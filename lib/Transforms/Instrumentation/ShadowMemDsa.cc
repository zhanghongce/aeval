#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"

#ifdef HAVE_DSA
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"

#include "avy/AvyDebug.h"
#include "boost/range.hpp"
#include "boost/range/algorithm/sort.hpp"
#include "boost/range/algorithm/set_algorithm.hpp"
#include "boost/range/algorithm/binary_search.hpp"

#include "dsa/Steensgaard.hh"

namespace seahorn
{
  using namespace llvm;
  
  template <typename Set>
  void markReachableNodes (const DSNode *n, Set &set)
  {
    if (!n) return;
    
    assert (!n->isForwarding () && "Cannot mark a forwarded node");
    if (set.insert (n).second)
      for (auto &edg : boost::make_iterator_range (n->edge_begin (), n->edge_end ()))
        markReachableNodes (edg.second.getNode (), set);
  }
  
  template <typename Set>
  void inputReachableNodes (const DSCallSite &cs, DSGraph &dsg, Set &set)
  {
    markReachableNodes (cs.getVAVal().getNode (), set);
    if (cs.isIndirectCall ()) markReachableNodes (cs.getCalleeNode (), set);
    for (unsigned i = 0, e = cs.getNumPtrArgs (); i != e; ++i)
      markReachableNodes (cs.getPtrArg (i).getNode (), set);
    
    // globals
    DSScalarMap &sm = dsg.getScalarMap ();
    for (auto &gv : boost::make_iterator_range (sm.global_begin(), sm.global_end ()))
      markReachableNodes (sm[gv].getNode (), set);
  }
  
  template <typename Set>
  void retReachableNodes (const DSCallSite &cs, Set &set) 
  {markReachableNodes (cs.getRetVal ().getNode (), set);}
  
  template <typename Set>
  void set_difference (Set &s1, Set &s2)
  {
    Set s3;
    boost::set_difference (s1, s2, std::inserter (s3, s3.end ()));
    std::swap (s3, s1);
  }
  
  template <typename Set>
  void set_union (Set &s1, Set &s2)
  {
    Set s3;
    boost::set_union (s1, s2, std::inserter (s3, s3.end ()));
    std::swap (s3, s1);
  }
  
  /// Computes DSNode reachable from the call arguments
  /// reach - all reachable nodes
  /// outReach - subset of reach that is only reachable from the return node
  template <typename Set1, typename Set2>
  void argReachableNodes (DSCallSite CS, DSGraph &dsg, 
                          Set1 &reach, Set2 &outReach)
  {
    inputReachableNodes (CS, dsg, reach);
    retReachableNodes (CS, outReach);
    set_difference (outReach, reach);
    set_union (reach, outReach);
  }
  
  
  
  AllocaInst* ShadowMemDsa::allocaForNode (const DSNode *n, const unsigned offset)
  {
    auto &offmap = m_shadows[n];
    
    auto it = offmap.find (offset);
    if (it != offmap.end ()) return it->second;
    
    AllocaInst *a = new AllocaInst (m_Int32Ty, 0);
    offmap [offset] = a;
    return a;
  }
    
  unsigned ShadowMemDsa::getId (const DSNode *n, unsigned offset)
  {
    auto it = m_node_ids.find (n);
    if (it != m_node_ids.end ()) return it->second + offset;
    
    unsigned id = m_max_id;
    m_node_ids[n] = id;

    // -- allocate enough ids for every byte of the object
    assert (n->getSize() > 0);
    m_max_id += n->getSize ();
    return id;
  }
    
    
  void ShadowMemDsa::declareFunctions (llvm::Module &M)
  {
    LLVMContext &ctx = M.getContext ();
    m_Int32Ty = Type::getInt32Ty (ctx);
    m_memLoadFn = M.getOrInsertFunction ("shadow.mem.load", 
                                         Type::getVoidTy (ctx),
                                         Type::getInt32Ty (ctx),
                                         Type::getInt32Ty (ctx),
                                         Type::getInt8PtrTy (ctx),
                                         (Type*) 0);
    
    
    m_memStoreFn = M.getOrInsertFunction ("shadow.mem.store", 
                                          Type::getInt32Ty (ctx),
                                          Type::getInt32Ty (ctx),
                                          Type::getInt32Ty (ctx),
                                          Type::getInt8PtrTy (ctx),
                                          (Type*) 0);
      
    m_memShadowInitFn = M.getOrInsertFunction ("shadow.mem.init",
                                               Type::getInt32Ty (ctx),
                                               Type::getInt32Ty (ctx),
                                               Type::getInt8PtrTy (ctx),
                                               (Type*) 0);
    
    m_memShadowArgInitFn = M.getOrInsertFunction ("shadow.mem.arg.init",
                                                  Type::getInt32Ty (ctx),
                                                  Type::getInt32Ty (ctx),
                                                  Type::getInt8PtrTy (ctx),
                                                  (Type*) 0);
    
    m_argRefFn = M.getOrInsertFunction ("shadow.mem.arg.ref",
                                        Type::getVoidTy (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt8PtrTy (ctx),
                                        (Type*) 0);
    
    m_argModFn = M.getOrInsertFunction ("shadow.mem.arg.mod",
                                        Type::getInt32Ty (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt8PtrTy (ctx),
                                        (Type*) 0);
    m_argNewFn = M.getOrInsertFunction ("shadow.mem.arg.new",
                                        Type::getInt32Ty (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt8PtrTy (ctx),
                                        (Type*) 0);
    
    m_markIn = M.getOrInsertFunction ("shadow.mem.in",
                                      Type::getVoidTy (ctx),
                                      Type::getInt32Ty (ctx),
                                      Type::getInt32Ty (ctx),
                                      Type::getInt32Ty (ctx),
                                      Type::getInt8PtrTy (ctx),
                                      (Type*) 0);
    m_markOut = M.getOrInsertFunction ("shadow.mem.out",
                                       Type::getVoidTy (ctx),
                                       Type::getInt32Ty (ctx),
                                       Type::getInt32Ty (ctx),
                                       Type::getInt32Ty (ctx),
                                       Type::getInt8PtrTy (ctx),
                                       (Type*) 0);
  }
  
  bool ShadowMemDsa::runOnModule (llvm::Module &M)
  {
    if (M.begin () == M.end ()) return false;
      
    //m_dsa = &getAnalysis<EQTDDataStructures> ();
    m_dsa = &getAnalysis<SteensgaardDataStructures> ();
    
    declareFunctions(M);
    m_node_ids.clear ();
    for (Function &f : M) runOnFunction (f);
      
    return false;
  }
  
  static Value *getUniqueScalar (LLVMContext &ctx, IRBuilder<> &B, const DSNodeHandle &nh)
  {
    DSNode* n = nh.getNode ();
    if (n && nh.getOffset () == 0)
    {
      Value *v = const_cast<Value*>(n->getUniqueScalar ());
    
      // -- a unique scalar is a single-cell global variable. We might be
      // -- able to extend this to single-cell local pointers, but these
      // -- are probably not very common.
      if (v)
        if (GlobalVariable *gv = dyn_cast<GlobalVariable> (v))
          if (gv->getType ()->getElementType ()->isSingleValueType ())
            return B.CreateBitCast (v, Type::getInt8PtrTy (ctx));
    }
    return ConstantPointerNull::get (Type::getInt8PtrTy (ctx));
  }

  static Value *getUniqueScalar (LLVMContext &ctx, IRBuilder<> &B, const DSNode *n)
  {
    DSNodeHandle nh (const_cast<DSNode*>(n), 0);
    return getUniqueScalar (ctx, B, nh);
  }
  
  unsigned ShadowMemDsa::getOffset (const DSNodeHandle &nh) { return 0; }
  
  bool ShadowMemDsa::runOnFunction (Function &F)
  {
    if (F.isDeclaration ()) return false;
      
    DSGraph* dsg = m_dsa->getDSGraph (F);
    if (!dsg) return false;
    DSGraph* gDsg = dsg->getGlobalsGraph ();
    
    DSScalarMap &SM = dsg->getScalarMap ();
    LOG ("shadow",
         errs () << "Looking into globals\n";
         for (const Value* v : boost::make_iterator_range (SM.global_begin (),
                                                           SM.global_end ()))
         {
           DSNodeHandle lN = SM[v];
           errs () << "Node for: " << *v << "\n";
           if (lN.getNode ()) lN.getNode ()->dump ();
           else errs () << "NULL\n";
         }
         errs () << "End of globals\n";);
    
    
    
    m_shadows.clear ();
    // -- preserve ids across functions m_node_ids.clear ();
      
    LLVMContext &ctx = F.getContext ();
    IRBuilder<> B (ctx);
      
    for (BasicBlock &bb : F)
      for (Instruction &inst : bb)
      {
        if (const LoadInst *load = dyn_cast<LoadInst> (&inst))
        {
          if (!dsg->hasNodeForValue (load->getOperand (0))) continue;
          DSNodeHandle &nh = dsg->getNodeForValue (load->getOperand (0));
          DSNode* n = nh.getNode ();
          if (!n) continue;
          
          B.SetInsertPoint (&inst);
          B.CreateCall3 (m_memLoadFn, B.getInt32 (getId (n)),
                         B.CreateLoad (allocaForNode (nh)),
                         getUniqueScalar (ctx, B, nh));
        }
        else if (const StoreInst *store = dyn_cast<StoreInst> (&inst))
        {
          if (!dsg->hasNodeForValue (store->getOperand (1))) continue;
          DSNodeHandle &nh = dsg->getNodeForValue (store->getOperand (1));
          DSNode *n = nh.getNode ();
          if (!n) continue;
          
          B.SetInsertPoint (&inst);
          AllocaInst *v = allocaForNode (nh);
          B.CreateStore (B.CreateCall3 (m_memStoreFn, 
                                        B.getInt32 (getId (nh)),
                                        B.CreateLoad (v),
                                        getUniqueScalar (ctx, B, nh)),
                         v);           
        }
        else if (CallInst *call = dyn_cast<CallInst> (&inst))
        {
          /// ignore inline assembly
          if (call->isInlineAsm ()) continue;
          
          /// skip intrinsics, except for memory-related ones
          if (isa<IntrinsicInst> (call) && !isa<MemIntrinsic> (call)) continue;

          /// skip sehaorn.* and verifier.* functions
          if (Function *fn = call->getCalledFunction ())
            if ((fn->getName ().startswith ("seahorn.") ||
                 fn->getName ().startswith ("verifier.")) &&
                /* seahorn.bounce should be treated as a regular function*/
                !(fn->getName ().startswith ("seahorn.bounce"))) 
              continue;
          

          LOG ("shadow_cs", errs () << "Call: " << *call << "\n";);
          DSCallSite CS = dsg->getDSCallSiteForCallSite (CallSite (call));
          if (!CS.isDirectCall ()) continue;

          if (!CS.getCalleeFunc ()) continue;
          
          if (CS.getCalleeFunc ()->getName ().equals ("calloc"))
          {
            DSNodeHandle &nh = dsg->getNodeForValue (call);
            DSNode* n = nh.getNode ();
            if (!n) continue;

            // TODO: handle multiple nodes
            assert (nh.getOffset () == 0 && "TODO");
            B.SetInsertPoint (call);
            AllocaInst *v = allocaForNode (nh);
            B.CreateStore (B.CreateCall3 (m_memStoreFn,
                                          B.getInt32 (getId (nh)),
                                          B.CreateLoad (v),
                                          getUniqueScalar (ctx, B, nh)),
                           v);
          }
          
          if (!m_dsa->hasDSGraph (*CS.getCalleeFunc ())) continue;
          
          
          const Function &CF = *CS.getCalleeFunc ();
          DSGraph *cdsg = m_dsa->getDSGraph (CF);
          if (!cdsg) continue;
          
          // -- compute callee nodes reachable from arguments and returns
          DSCallSite CCS = cdsg->getCallSiteForArguments (CF);
          std::set<const DSNode*> reach;
          std::set<const DSNode*> retReach;
          argReachableNodes (CCS, *cdsg, reach, retReach);
          
          DSGraph::NodeMapTy nodeMap;
          dsg->computeCalleeCallerMapping (CS, CF, *cdsg, nodeMap);
          
          /// generate mod, ref, new function, based on whether the
          /// remote node reads, writes, or creates the corresponding node.
          
          B.SetInsertPoint (&inst);
          unsigned idx = 0;
          for (const DSNode* n : reach)
          {
            LOG("global_shadow", n->print (errs (), n->getParentGraph ());
                errs () << "global: " << n->isGlobalNode () << "\n";
                errs () << "#globals: " << n->numGlobals () << "\n";
                svset<const GlobalValue*> gv;
                if (n->numGlobals () == 1) n->addFullGlobalsSet (gv);
                errs () << "gv-size: " << gv.size () << "\n";
                if (gv.size () == 1) errs () << "Global: " << *(*gv.begin ()) << "\n";
                const Value *v = n->getUniqueScalar ();
                if (v) 
                  errs () << "value: " << *n->getUniqueScalar () << "\n";
                else
                  errs () << "no unique scalar\n";
                );
            
            
            // skip nodes that are not read/written by the callee
            if (!n->isReadNode () && !n->isModifiedNode ()) continue;

            /// XXX: it seems that for some nodes in the caller graph
            /// we may be unable to find its corresponding node in the
            /// callee graph.
            ///
            /// Since the current DSA implementation enforces that the
            /// caller and callee graphs are actually the same we can
            /// return n. Note that this is a hook and needs to be
            /// properly fixed.
            const DSNode* m = n;
            auto nodeMapIt = nodeMap.find (n);
            if (nodeMapIt != nodeMap.end ())
              m = nodeMapIt->second.getNode ();
             
            // TODO: This must be done for every possible offset of m,
            // TODO: not just for offset 0
            DSNodeHandle mh (const_cast<DSNode*>(m), 0);
            AllocaInst *v = allocaForNode (mh);
            unsigned id = getId (mh);
            
            // -- read only node ignore nodes that are only reachable
            // -- from the return of the function
            if (n->isReadNode () && !n->isModifiedNode () && retReach.count(n) <= 0)
            {
              B.CreateCall4 (m_argRefFn, B.getInt32 (id),
                             B.CreateLoad (v),
                             B.getInt32 (idx), getUniqueScalar (ctx, B, mh));
            }
            // -- read/write or new node
            else if (n->isModifiedNode ())
            {
              // -- n is new node iff it is reachable only from the return node
              Constant* argFn = retReach.count (n) ? m_argNewFn : m_argModFn;
              B.CreateStore (B.CreateCall4 (argFn, 
                                            B.getInt32 (id),
                                            B.CreateLoad (v),
                                            B.getInt32 (idx),
                                            getUniqueScalar (ctx, B, mh)), v);
            }
            idx++;
          }
        }
        
      }
      
    DSCallSite CS = dsg->getCallSiteForArguments (F);
    
    // compute DSNodes that escape because they are either reachable
    // from the input arguments or from returns
    std::set<const DSNode*> reach;
    std::set<const DSNode*> retReach;
    argReachableNodes (CS, *dsg, reach, retReach);
    
    // -- create shadows for all nodes that are modified by this
    // -- function and escape to a parent function
    for (const DSNode *n : reach)
      if (n->isModifiedNode () || n->isReadNode ())
      {
        // TODO: allocate for all slices of n, not just offset 0
        allocaForNode (n, 0);
      }
    
    // allocate initial value for all used shadows
    DenseMap<const DSNode*, DenseMap<unsigned, Value*> > inits;
    B.SetInsertPoint (&*F.getEntryBlock ().begin ());
    for (auto it : m_shadows)
    {
      const DSNode *n = it.first;
      Constant *fn = reach.count (n) <= 0 ? m_memShadowInitFn : m_memShadowArgInitFn;
      
      for (auto jt : it.second)
      {
        DSNodeHandle nh (const_cast<DSNode*>(n), jt.first);
        AllocaInst *a = jt.second;
        B.Insert (a, "shadow.mem");
        CallInst *ci;
        ci = B.CreateCall2 (fn, B.getInt32 (getId (nh)), getUniqueScalar (ctx, B, nh));
        inits[nh.getNode()][getOffset(nh)] = ci;
        B.CreateStore (ci, a);
      }
    }
     
    UnifyFunctionExitNodes &ufe = getAnalysis<llvm::UnifyFunctionExitNodes> (F);
    BasicBlock *exit = ufe.getReturnBlock ();
    
    if (!exit) 
    {
      // XXX Need to think how to handle functions that do not return in 
      // XXX interprocedural encoding. For now, we print a warning and ignore this case.
      errs () << "WARNING: ShadowMem: function `" << F.getName () << "' never returns\n";
      return true;
    }
    
    assert (exit);
    TerminatorInst *ret = exit->getTerminator ();
    assert (ret);
    
    // split return basic block if it has more than just the return instruction
    if (exit->size () > 1)
    {
      exit = llvm::SplitBlock (exit, ret, this);
      ret = exit->getTerminator ();
    }
    
    B.SetInsertPoint (ret);
    unsigned idx = 0;
    for (const DSNode* n : reach)
    {
      // TODO: extend to work with all slices
      DSNodeHandle nh (const_cast<DSNode*>(n), 0);
      
      // n is read and is not only return-node reachable (for
      // return-only reachable nodes, there is no initial value
      // because they are created within this function)
      if ((n->isReadNode () || n->isModifiedNode ()) 
          && retReach.count (n) <= 0)
      {
        assert (!inits[n].empty());
        /// initial value
        B.CreateCall4 (m_markIn,
                       B.getInt32 (getId (nh)),
                       inits[n][0], 
                       B.getInt32 (idx),
                       getUniqueScalar (ctx, B, nh));
      }
      
      if (n->isModifiedNode ())
      {
        assert (!inits[n].empty());
        /// final value
        B.CreateCall4 (m_markOut, 
                       B.getInt32 (getId (nh)),
                       B.CreateLoad (allocaForNode (nh)),
                       B.getInt32 (idx),
                       getUniqueScalar (ctx, B, nh));
      }
      ++idx;
    }
      
    return true;
  }
    
  void ShadowMemDsa::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    // AU.addRequiredTransitive<llvm::EQTDDataStructures>();
    AU.addRequiredTransitive<llvm::SteensgaardDataStructures> ();
    AU.addRequired<llvm::DataLayoutPass>();
    AU.addRequired<llvm::UnifyFunctionExitNodes> ();
  } 
    

  class StripShadowMem : public ModulePass 
  {
  public:
    static char ID;
    StripShadowMem () : ModulePass (ID) {} 

    void getAnalysisUsage (AnalysisUsage &AU) const override
    {AU.setPreservesAll ();}
    
    bool runOnModule (Module &M) override
    {
      std::vector<std::string> voidFnNames = 
        {"shadow.mem.load", "shadow.mem.arg.ref",
         "shadow.mem.in", "shadow.mem.out" };
      
      for (auto &name : voidFnNames)
      {
        Function *fn = M.getFunction (name);
        if (!fn) continue;
        
        while (!fn->use_empty ())
        {
          CallInst *ci = cast<CallInst> (fn->user_back ());
          Value *last = ci->getArgOperand (ci->getNumArgOperands () - 1);
          ci->eraseFromParent ();
          RecursivelyDeleteTriviallyDeadInstructions (last);
        }
      }

      std::vector<std::string> intFnNames =
        { "shadow.mem.store", "shadow.mem.init",
          "shadow.mem.arg.init", "shadow.mem.arg.mod"};
      Value *zero = ConstantInt::get (Type::getInt32Ty(M.getContext ()), 0);
      
      for (auto &name : intFnNames)
      {
        Function *fn = M.getFunction (name);
        if (!fn) continue;
        
        while (!fn->use_empty ())
        {
          CallInst *ci = cast<CallInst> (fn->user_back ());
          Value *last = ci->getArgOperand (ci->getNumArgOperands () - 1);
          ci->replaceAllUsesWith (zero);
          ci->eraseFromParent ();
          RecursivelyDeleteTriviallyDeadInstructions (last);
        }
      }
      
      return true;
    }
    
  };    
}

#endif

namespace seahorn
{
  char ShadowMemDsa::ID = 0;
  char StripShadowMem::ID = 0;
  Pass * createShadowMemDsaPass () {return new ShadowMemDsa ();}
  Pass * createStripShadowMemPass () {return new StripShadowMem ();}
  
}

static llvm::RegisterPass<seahorn::ShadowMemDsa> X ("shadow-dsa", "Shadow DSA nodes");
static llvm::RegisterPass<seahorn::StripShadowMem> Y ("strip-shadow-dsa",
                                                      "Remove shadow.mem instrinsics");


