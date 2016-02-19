#include "seahorn/Transforms/Instrumentation/BufferBoundsCheck.hh"

#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"

static llvm::cl::opt<unsigned int>
TrackedDSNode("abc-dsa-node",
        llvm::cl::desc ("Only instrument pointers within this dsa node"),
        llvm::cl::init (0));

namespace seahorn
{
  // TODO: update the call graph for ABC1
  using namespace llvm;

  Value* ABC1::lookupSize (const Value* ptr)
  {
    auto it = m_sizes.find (ptr);
    if (it != m_sizes.end ()) return it->second;
    else return nullptr;
  }

  Value* ABC1::lookupOffset (const Value* ptr)
  {
    auto it = m_offsets.find (ptr);
    if (it != m_offsets.end ()) return it->second;
    else return nullptr;
  }

  ABC1::ValuePair ABC1::findShadowArg (Function *F, const Value *Arg) 
  {
    if (m_orig_arg_size.find (F) == m_orig_arg_size.end ()) {
      return ValuePair (nullptr,nullptr);
    }
      
    size_t shadow_idx = m_orig_arg_size [F];
    Function::arg_iterator AI = F->arg_begin();
    for (size_t idx = 0 ; idx < m_orig_arg_size [F] ; ++AI, idx++) {
      const Value* formalPar = &*AI;
      if (formalPar == Arg) {
        Value* shadowOffset = abc_helpers::getArgument (F, shadow_idx);
        Value* shadowSize   = abc_helpers::getArgument (F, shadow_idx+1);
        assert (shadowOffset && shadowSize);
        return ValuePair (shadowOffset, shadowSize);
      }
      
      if (IsShadowableType (formalPar->getType ()))
        shadow_idx += 2;
    }
    return ValuePair (nullptr,nullptr);
  }

  ABC1::StoreInstPair ABC1::findShadowRet (Function *F) {
    return m_ret_shadows [F];
  }

  bool ABC1::IsShadowableFunction (const Function &F) const  
  { 
    auto it = m_orig_arg_size.find (&F);
    if (it == m_orig_arg_size.end ()) return false;
    return (F.arg_size () > it->second);
    //return (m_orig_arg_size.find (&F) != m_orig_arg_size.end ());
  }

  bool ABC1::IsShadowableType (Type * ty) const 
  { return ty->isPointerTy (); } 
    
  // return the number of original arguments before the pass added
  // shadow parameters
  size_t ABC1::getOrigArgSize (const Function &F) {
    assert (IsShadowableFunction (F));
    return m_orig_arg_size [&F];
  }
    
  // For each function parameter for which we want to propagate its
  // offset and size we add two more *undefined* function parameters
  // for placeholding its offset and size which will be filled out
  // later.
  bool ABC1::addFunShadowParams (Function *F, LLVMContext &ctx) {  
    if (F->isDeclaration ()) return false;

    if (F->getName ().equals ("main")) return false;

    // TODO: relax this case
    if (F->hasAddressTaken ()) return false;
    // TODO: relax this case
    const FunctionType *FTy = F->getFunctionType ();
    if (FTy->isVarArg ()) return false;

    CanAccessMemory &CM = getAnalysis<CanAccessMemory> ();
    if (!CM.canAccess(F)) return false;

    // copy params
    std::vector<llvm::Type*> ParamsTy (FTy->param_begin (), FTy->param_end ());
    // XXX: I use string because StringRef and Twine should not be
    //      stored.
    std::vector<std::string> NewNames;
    Function::arg_iterator FAI = F->arg_begin();
    for(FunctionType::param_iterator I =  FTy->param_begin (),             
            E = FTy->param_end (); I!=E; ++I, ++FAI)  {
      Type *PTy = *I;
      if (IsShadowableType (PTy)) {
        ParamsTy.push_back (m_Int64Ty);
        Twine offset_name = FAI->getName () + ".shadow.offset";
        NewNames.push_back (offset_name.str ());
        ParamsTy.push_back (m_Int64Ty);
        Twine size_name = FAI->getName () + ".shadow.size";
        NewNames.push_back (size_name.str ());
      }
    }
    // create function type
    Type *RetTy = F->getReturnType ();
    FunctionType *NFTy = FunctionType::get (RetTy, 
                                            ArrayRef<llvm::Type*> (ParamsTy), 
                                            FTy->isVarArg ());

    // create new function 
    Function *NF = Function::Create (NFTy, F->getLinkage ());
    NF->copyAttributesFrom(F);
    F->getParent ()->getFunctionList ().insert(F, NF);
    NF->takeName (F);

    //m_orig_arg_size [NF] = F->arg_size ();
    assert (m_orig_arg_size.find (NF) == m_orig_arg_size.end ());
    m_orig_arg_size.insert (std::make_pair (NF, F->arg_size ()));

    // new parameter names
    unsigned idx=0;
    for(Function::arg_iterator I = NF->arg_begin(), E = NF->arg_end(); 
        I != E; ++I, idx++) {
      if (idx >= F->arg_size ()) {
        Value* newParam = &*I;
        newParam->setName (NewNames [idx - F->arg_size ()]);
      }
    }
    
    ValueToValueMapTy ValueMap;
    Function::arg_iterator DI = NF->arg_begin();
    for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end();
         I != E; ++I, ++DI)  {
      DI->setName(I->getName());  // Copy the name over.
      // Add a mapping to our mapping.
      ValueMap[I] = DI;
    }
    
    SmallVector<ReturnInst*, 8> Returns; // Ignore returns.
    CloneFunctionInto (NF, F, ValueMap, false, Returns);

    IRBuilder<> B (ctx);

    // placeholders for the variables that will feed the shadow
    // variables for the return instruction of the function
    if (IsShadowableType (RetTy)) {
      ReturnInst* ret = abc_helpers::getReturnInst (NF);   
      B.SetInsertPoint (ret);

      // StoreInst* SI_Off = 
      //     B.CreateAlignedStore (UndefValue::get (m_Int64Ty), 
      //                           m_ret_offset,
      //                           m_dl->getABITypeAlignment (m_ret_offset->getType ())); 

      // StoreInst* SI_Size = 
      //     B.CreateAlignedStore (UndefValue::get (m_Int64Ty), 
      //                           m_ret_size,
      //                           m_dl->getABITypeAlignment (m_ret_size->getType ())); 

      StoreInst* SI_Off =  B.CreateStore (UndefValue::get (m_Int64Ty), m_ret_offset); 
      StoreInst* SI_Size = B.CreateStore (UndefValue::get (m_Int64Ty), m_ret_size);

      m_ret_shadows [NF] = std::make_pair (SI_Off,SI_Size);
    }

    // Replace all callers
    while (!F->use_empty ()) {
      // here we know all uses are call instructions
      CallSite CS (cast<Value>(F->user_back ()));

      Instruction *Call = CS.getInstruction ();
      // Copy the existing arguments
      std::vector <Value*> Args;
      Args.reserve (CS.arg_size ());
      CallSite::arg_iterator AI = CS.arg_begin ();
      for (unsigned i=0, e=FTy->getNumParams (); i!=e ; ++i, ++AI)
        Args.push_back (*AI);

      B.SetInsertPoint (Call);

      // insert placeholders for new arguments
      unsigned added_new_args = NF->arg_size () - F->arg_size();
      for(unsigned i=0; i < added_new_args ; i++)
        Args.push_back (UndefValue::get (m_Int64Ty)); // for shadow formal parameters

      // create new call 
      Instruction *New = B.CreateCall (NF, ArrayRef<Value*> (Args));
      cast<CallInst>(New)->setCallingConv (CS.getCallingConv ());
      cast<CallInst>(New)->setAttributes (CS.getAttributes ());
      if (cast<CallInst>(Call)->isTailCall ())
        cast<CallInst>(New)->setTailCall ();
      
      if (Call->hasName ())
        New->takeName (Call);

      // Replace all the uses of the old call
      Call->replaceAllUsesWith (New);
      
      // Remove the old call
      Call->eraseFromParent ();

      // wire up shadow actual parameters of the call with the shadow
      // formal parameters of its parent.
      CallSite NCS (const_cast<CallInst*> (cast<CallInst>(New)));

      size_t  orig_arg_size = m_orig_arg_size [NCS.getCalledFunction ()];
      for (unsigned idx = 0, shadow_idx = orig_arg_size; 
           idx < orig_arg_size; idx++) {
        const Value* ArgPtr = NCS.getArgument (idx);
        if (IsShadowableType (ArgPtr->getType ())) {
          ValuePair shadow_pars = 
              findShadowArg (New->getParent ()->getParent(), ArgPtr);
          if (shadow_pars.first && shadow_pars.second) {
            NCS.setArgument(shadow_idx,   shadow_pars.first);
            NCS.setArgument(shadow_idx+1, shadow_pars.second); 
          }
          shadow_idx +=2;
        }
      }
    }

    // -- Do not try to remove because others could have a pointer to
    //    the function (e.g., callgraph).
    // F->eraseFromParent ();

    return true;
  } 
  
  void ABC1::resolvePHIUsers (const Value *v, 
                              DenseMap <const Value*, Value*>& m_table) {
    // resolve phi incoming values that were marked as undef
    for (Value::const_use_iterator it = v->use_begin(), et = v->use_end (); it!=et; ++it) {
      if (const PHINode *PHI = dyn_cast<PHINode> (*it)) {
        Value * ValShadow = m_table [*it];
        if (!ValShadow) continue;

        if (PHINode *PHIShadow = dyn_cast<PHINode> (ValShadow)) {
          for (unsigned i=0; i < PHI->getNumIncomingValues (); i++) {
            if (PHI->getIncomingValue (i) == v && 
                ( ( i >= PHIShadow->getNumIncomingValues ()) ||
                  PHIShadow->getIncomingValue (i) == UndefValue::get (m_Int64Ty))) {
              PHIShadow->setIncomingValue (i, m_table [v]);
            }
          }
        }        
      }
    }
  }

  void ABC1::instrumentGepOffset(IRBuilder<> B, Instruction* insertPoint,
                                 const GetElementPtrInst *gep) {
    SmallVector<const Value*, 4> ps;
    SmallVector<const Type*, 4> ts;
    gep_type_iterator typeIt = gep_type_begin (*gep);
    for (unsigned i = 1; i < gep->getNumOperands (); ++i, ++typeIt) {
      ps.push_back (gep->getOperand (i));
      ts.push_back (*typeIt);
    }

    const Value *base = gep->getPointerOperand ();    
    Value *gepBaseOff = m_offsets [base];

    if (!gepBaseOff)
      return;

    B.SetInsertPoint(insertPoint);
    Value* curVal = gepBaseOff;
    for (unsigned i = 0; i < ps.size (); ++i) {
      if (const StructType *st = dyn_cast<const StructType> (ts [i])) {
        if (const ConstantInt *ci = dyn_cast<const ConstantInt> (ps [i])) {
          unsigned off = abc_helpers::fieldOffset (m_dl, st, ci->getZExtValue ());
          curVal = abc_helpers::createAdd (B, curVal, 
                                           ConstantInt::get (m_Int64Ty, off));
        }
        else assert (false);
      }
      else if (const SequentialType *seqt = dyn_cast<const SequentialType> (ts [i])) {
        // arrays, pointers, and vectors
        unsigned sz = abc_helpers::storageSize (m_dl, seqt->getElementType ());
        Value *LHS = curVal;
        Value *RHS = abc_helpers::createMul(B, const_cast<Value*> (ps[i]), sz);
        curVal = abc_helpers::createAdd(B, LHS, RHS); 
      }
    } 
    m_offsets [gep] = curVal;                                   
    resolvePHIUsers (gep, m_offsets);
  }

  /*
    This instruments the offset and size of ptr by inserting
    arithmetic instructions. We instrument ptr as long as it follows a
    sequence of instructions with this grammar:

    Ptr = globalVariable | alloca | malloc | load | inttoptr | formal param | return |
          (getElementPtr (Ptr) | bitcast (Ptr) | phiNode (Ptr) ... (Ptr) )*  

   */
  void ABC1::instrumentSizeAndOffsetPtrRec (Function *F, IRBuilder<> B, 
                                            Instruction* insertPoint, 
                                            const Value * ptr,
                                            ValueSet &visited) {

    if (visited.find(ptr) != visited.end ())  return;
    visited.insert (ptr);
    
    /// recursive cases 

    if (const BitCastInst *Bc = dyn_cast<BitCastInst> (ptr)) {
      Instruction *insertPoint = const_cast<Instruction*> (cast<Instruction> (Bc));
      instrumentSizeAndOffsetPtrRec (F, B, insertPoint, 
                                     Bc->getOperand (0),
                                     visited);
      B.SetInsertPoint(insertPoint);
      if (Value* shadowBcOpOff = lookupOffset(Bc->getOperand (0)))
        m_offsets [ptr] = shadowBcOpOff;
      if (Value* shadowBcOpSize = lookupSize(Bc->getOperand (0)))
        m_sizes [ptr] = shadowBcOpSize;

      return;
    }

    if (const GetElementPtrInst *Gep = dyn_cast<GetElementPtrInst> (ptr)) {
      Instruction *insertPoint = const_cast<Instruction*> (cast<Instruction> (Gep));
      instrumentSizeAndOffsetPtrRec (F, B, insertPoint, 
                                     Gep->getPointerOperand (),
                                     visited);
      
      B.SetInsertPoint(insertPoint);
      instrumentGepOffset(B, insertPoint, Gep);
      if (Value* shadowGepOpSize = lookupSize(Gep->getPointerOperand ())) {
        m_sizes [ptr] = shadowGepOpSize;
        resolvePHIUsers (ptr, m_sizes);
      }
      return;
    }

    if (const PHINode *PHI = dyn_cast<PHINode> (ptr)) {
      Instruction *insertPoint = const_cast<Instruction*> (cast<Instruction> (PHI));
      PHINode* shadowPHINodeOff = 
          PHINode::Create (m_Int64Ty, PHI->getNumIncomingValues (), 
                           ((ptr->hasName ()) ? 
                            ptr->getName () + ".shadow.offset" : ""),
                           insertPoint);
      PHINode* shadowPHINodeSize = 
          PHINode::Create (m_Int64Ty, PHI->getNumIncomingValues (), 
                           ((ptr->hasName ()) ? 
                            ptr->getName () + ".shadow.size" : ""),
                           insertPoint);

      for (unsigned i=0; i < PHI->getNumIncomingValues (); i++) {
        // placeholder for now
        shadowPHINodeOff->addIncoming (UndefValue::get (m_Int64Ty), 
                                       PHI->getIncomingBlock (i));
        shadowPHINodeSize->addIncoming (UndefValue::get (m_Int64Ty), 
                                        PHI->getIncomingBlock (i));
      }

      
      m_offsets [ptr] = shadowPHINodeOff;
      m_sizes [ptr] = shadowPHINodeSize;

      for (unsigned i=0; i < PHI->getNumIncomingValues (); i++) {
        Instruction *insertPoint = 
            dyn_cast<Instruction> (PHI->getIncomingValue (i)); 
        if (!insertPoint)
          insertPoint = PHI->getIncomingBlock (i)->getFirstNonPHI ();
        instrumentSizeAndOffsetPtrRec (F, B, insertPoint, 
                                       PHI->getIncomingValue (i),
                                       visited);
        if (Value* shadowPHIValOff = lookupOffset(PHI->getIncomingValue (i)))
          shadowPHINodeOff->setIncomingValue (i, shadowPHIValOff);
        if (Value* shadowPHIValSize = lookupSize(PHI->getIncomingValue (i)))
          shadowPHINodeSize->setIncomingValue (i, shadowPHIValSize);
      }

      return;
    }

    /// base cases
    if (isa<AllocaInst> (ptr) || isa<GlobalVariable> (ptr) || 
        isa<LoadInst> (ptr) || isAllocationFn (ptr, m_tli, true)) {
      // Here we can handle the load instruction only for simple cases
      // (eg. if the pointer is a global variable)
      uint64_t Size;
      if (getObjectSize(ptr, Size, m_dl, m_tli, true)) {
        m_offsets [ptr] = ConstantInt::get (m_Int64Ty, 0);
        m_sizes [ptr] = ConstantInt::get (m_Int64Ty,Size);
        return;
      } 

      if (const AllocaInst *AI = dyn_cast<AllocaInst> (ptr))  {
        Value *nElems = const_cast<Value*> (AI->getArraySize ()); // number of elements
        const Type* ty = AI->getAllocatedType (); // size of the allocated type
        unsigned ty_size = abc_helpers::storageSize (m_dl, ty);
        Value* size = nullptr;
        B.SetInsertPoint (insertPoint);
        if (ty_size == 1) 
          size = nElems;
        else 
          size = abc_helpers::createMul (B, nElems, ty_size, "alloca_size");
        m_offsets [ptr] = ConstantInt::get (m_Int64Ty, 0);
        m_sizes [ptr] = B.CreateSExtOrTrunc (size, m_Int64Ty);
        return;
      }
      else if (const CallInst * MallocInst = extractMallocCall (ptr ,m_tli)) {
        if (MallocInst->getNumArgOperands () == 1) {
          Value *size = MallocInst->getArgOperand(0);
          if (size->getType ()->isIntegerTy ()) {
            B.SetInsertPoint(insertPoint);
            m_offsets [ptr] = ConstantInt::get (m_Int64Ty, 0);
            m_sizes [ptr] = B.CreateSExtOrTrunc (size, m_Int64Ty);
            return;
          }
        }
      }     
    }

    if (isa<IntToPtrInst> (ptr))
    { // TODO
      return;
    }
    
    if (isa<LoadInst> (ptr))
    { // TODO
      return;
    }
    
    /// ptr is the return value of a call site      
    if (const CallInst *CI = dyn_cast<CallInst> (ptr)) {
      CallSite CS (const_cast<CallInst*> (CI));
      Function *cf = CS.getCalledFunction ();      
      if (cf && IsShadowableFunction (*cf)) {
        B.SetInsertPoint(const_cast<CallInst*> (CI)); //just before CI
        auto it = B.GetInsertPoint ();
        ++it; // just after CI
        B.SetInsertPoint (const_cast<llvm::BasicBlock*>(CI->getParent ()), it);

        // m_offsets [ptr] = 
        //     B.CreateAlignedLoad (m_ret_offset,
        //                          m_dl->getABITypeAlignment (m_ret_offset->getType ())); 

        // m_sizes [ptr] = 
        //     B.CreateAlignedLoad (m_ret_size,
        //                          m_dl->getABITypeAlignment (m_ret_size->getType ())); 

        m_offsets [ptr] = B.CreateLoad (m_ret_offset); 
        m_sizes [ptr] = B.CreateLoad (m_ret_size); 
        return;
      }
    }
    
    /// if ptr is a function formal parameter
    auto p =  findShadowArg (F, ptr);
    Value* shadowPtrOff =  p.first;
    Value* shadowPtrSize = p.second;
    if (shadowPtrOff && shadowPtrSize) {
      m_offsets [ptr] = shadowPtrOff;
      m_sizes [ptr] = shadowPtrSize;      
      return;
    }
  }


  void ABC1::instrumentSizeAndOffsetPtr (Function *F, IRBuilder<> B, 
                                         Instruction* insertPoint, 
                                         const Value * ptr) {
    ValueSet visited;
    instrumentSizeAndOffsetPtrRec (F, B, insertPoint, ptr, visited);
  }

  //! Instrument check for memory accesses
  bool ABC1::instrumentCheck (Function& F, IRBuilder<> B, 
                              Instruction& inst, 
                              const Value& ptr, Value* len) {
    // Figure out offset and size
    instrumentSizeAndOffsetPtr (&F, B, &inst, &ptr);
    Value *ptrSize   = m_sizes [&ptr];
    Value *ptrOffset = m_offsets [&ptr];

    if (!ptrSize || !ptrOffset) {
      m_checks_unable++;
      return false;
    }

    // Create error blocks
    LLVMContext& ctx = B.getContext ();
    BasicBlock* err_under_bb = BasicBlock::Create(ctx, "underflow_bb", &F);
    BasicBlock* err_over_bb = BasicBlock::Create(ctx, "overflow_bb", &F);

    B.SetInsertPoint (err_under_bb);
    CallInst* ci_under = B.CreateCall (m_errorFn);
    ci_under->setDebugLoc (inst.getDebugLoc ());
    B.CreateUnreachable ();
    
    B.SetInsertPoint (err_over_bb);
    CallInst* ci_over = B.CreateCall (m_errorFn);
    ci_over->setDebugLoc (inst.getDebugLoc ());
    B.CreateUnreachable ();
    
    
    B.SetInsertPoint (&inst);    

    BasicBlock *OldBB0 = inst.getParent ();
    BasicBlock *Cont0 = OldBB0->splitBasicBlock(B.GetInsertPoint ());
    OldBB0->getTerminator ()->eraseFromParent ();
    BranchInst::Create (Cont0, OldBB0);
    
    B.SetInsertPoint (Cont0->getFirstNonPHI ());    

    /// --- Underflow: add check offset >= 0 
    Value* Cond_U = B.CreateICmpSGE (ptrOffset, 
                                     ConstantInt::get (m_Int64Ty, 0),
                                     "buffer_under");

    BasicBlock *OldBB1 = Cont0;
    BasicBlock *Cont1 = OldBB1->splitBasicBlock(B.GetInsertPoint ());
    OldBB1->getTerminator ()->eraseFromParent();
    BranchInst::Create (Cont1, err_under_bb, Cond_U, OldBB1);

    m_checks_added++;
    B.SetInsertPoint (Cont1->getFirstNonPHI ());    

    /// --- Overflow: add check 
    //      offset + align <= size or offset + len <= size 

    Value *range = nullptr;
    if (len) {
      range = abc_helpers::createAdd (B, ptrOffset, len);
    } else {
      int align = abc_helpers::getOffsetAlign (inst);
      if (align < 0) { // This should not happen ...
        errs () << "Error: cannot find align of offset for " << inst << "\n";
        return true;
      }
      range = abc_helpers::createAdd (B, ptrOffset, 
                                      ConstantInt::get (m_Int64Ty, align));
    }
    
    Value* Cond_O = B.CreateICmpSLE (range, ptrSize, "buffer_over");

    BasicBlock *OldBB2 = Cont1;
    BasicBlock *Cont2 = OldBB2->splitBasicBlock(B.GetInsertPoint ());
    OldBB2->getTerminator ()->eraseFromParent();
    BranchInst::Create (Cont2, err_over_bb, Cond_O, OldBB2);

    m_checks_added++;
    return true;
  }

  // Whether a pointer should be tracked based on DSA (if available)
  bool ABC1::ShouldBeTrackedPtr (Value* ptr, Function& F) {
     #ifndef HAVE_DSA
     return true;
     #else
     if (TrackedDSNode == 0)
       return true; 

     DSACount* m_dsa_count = &getAnalysis<DSACount> ();
     assert (m_dsa_count);
     
     DSGraph* dsg = nullptr;
     DSGraph* gDsg = nullptr;
     if (m_dsa_count->getDSA ()) {
       dsg = m_dsa_count->getDSA ()->getDSGraph (F);
       gDsg = m_dsa_count->getDSA ()->getGlobalsGraph (); 
     }
     
     const DSNode* n = dsg->getNodeForValue (ptr).getNode ();
     if (!n) n = gDsg->getNodeForValue (ptr).getNode ();
     if (!n) 
       return false; // DSA node not found. This should not happen.
     
     return (m_dsa_count->getId (n) == TrackedDSNode);
     #endif 
  }

  bool ABC1::runOnModule (llvm::Module &M)
  {
    if (M.begin () == M.end ()) return false;
      
    // Print statistics about DSA nodes
    DSACount* m_dsa_count = &getAnalysis<DSACount> ();    
    if (m_dsa_count)
      m_dsa_count->write (errs ());

    LLVMContext &ctx = M.getContext ();
    m_Int64Ty = Type::getInt64Ty (ctx);
    m_Int64PtrTy = m_Int64Ty->getPointerTo ();

    AttrBuilder AB;
    AB.addAttribute (Attribute::NoReturn);
    AttributeSet as = AttributeSet::get (ctx, 
                                         AttributeSet::FunctionIndex,
                                         AB);
    
    m_errorFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.error",
                                as,
                                Type::getVoidTy (ctx), nullptr));
        
    /* Shadow function parameters */
    std::vector<Function*> funcsToInstrument;
    funcsToInstrument.reserve (std::distance (M.begin (), M.end ()));
    for (Function &F : M) { 
      if (!F.isDeclaration ())
        funcsToInstrument.push_back (&F);
    }
    // Insert shadow global variables for function return values 
    m_ret_offset = abc_helpers::createGlobalInt (M, 0, "ret.offset");
    m_ret_size = abc_helpers::createGlobalInt (M, 0, "ret.size");
    for (auto F: funcsToInstrument) {
       addFunShadowParams (F, ctx);
    }

    // TODO: addFunShadowParams invalidates DSA information since it
    // adds shadow parameters by making new copies of the existing
    // functions and then removing those functions.
    if (TrackedDSNode != 0) {
      errs () << "Warning: DSA is invalidated so we cannot use DSA info ...\n";
      TrackedDSNode = 0;
    }
    
    /* Instrument load/store/memcpy/memmove/memset instructions */
    unsigned untracked_dsa_checks = 0;
    std::vector<Instruction*> WorkList;
    for (Function &F : M) {
      
      if (F.isDeclaration ()) continue;
      if (!F.hasName ()) continue; // skip old functions before instrumentation
      
      for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
        Instruction *I = &*i;
        if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
          Value* ptr = LI->getPointerOperand ();
          if (ptr == m_ret_offset || ptr == m_ret_size) continue;
            
          if (ShouldBeTrackedPtr (ptr, F))
            WorkList.push_back (I);
          else
            untracked_dsa_checks++; 
          
        } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
          Value* ptr = SI->getPointerOperand ();
          if (ptr == m_ret_offset || ptr == m_ret_size) continue;

          if (ShouldBeTrackedPtr (ptr, F))
            WorkList.push_back (I);
          else
            untracked_dsa_checks++; 
          
        } else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
          if (ShouldBeTrackedPtr (MTI->getDest (), F) || 
              ShouldBeTrackedPtr (MTI->getSource (), F))
            WorkList.push_back (I);
          else
            untracked_dsa_checks+=2;
        } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
          Value* ptr = MSI->getDest ();
          if (ShouldBeTrackedPtr (ptr, F))
            WorkList.push_back (I);            
          else
            untracked_dsa_checks++; 
          
        } else if (isa<CallInst> (I) || isa<ReturnInst> (I)) {
          WorkList.push_back(I);
        }
      }
    }

    m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
    m_tli = &getAnalysis<TargetLibraryInfo>();
    IRBuilder<> B (ctx);

    for (auto inst: WorkList) {
      Function* F = inst->getParent()->getParent();
      // make sure we do first these two cases before visiting
      // CallInst
      if (MemTransferInst *MTI = dyn_cast<MemTransferInst> (inst)) {
        m_mem_accesses+=2;
        Value* DestPtr = MTI->getDest ();
        Value* SrcPtr = MTI->getSource ();
        instrumentCheck (*F, B, *inst, *SrcPtr, MTI->getLength ());           
        instrumentCheck (*F, B, *inst, *DestPtr, MTI->getLength ());           
      }
      else if (MemSetInst *MSI = dyn_cast<MemSetInst> (inst)) {
        m_mem_accesses++;
        Value* DestPtr = MSI->getDest ();
        instrumentCheck (*F, B, *inst, *DestPtr, MSI->getLength ());           
      }
      else if (const CallInst *CI = dyn_cast<CallInst> (inst)) {
        CallSite CS (const_cast<CallInst*> (CI));
        const Function *cf = CS.getCalledFunction ();
        if (cf) {
          if (cf->isIntrinsic ()) continue;
          // Resolving the shadow offsets and sizes which are
          // actual parameters of a function call
          // At this point F has this form:
          //
          // q = foo (p,...,_,_,&q.off,&q.size);
          //
          // The placeholders are filled out with the shadow
          // variables corresponding to p.
          if (IsShadowableFunction (*cf)) {
            size_t orig_arg_size = getOrigArgSize (*cf);
            unsigned shadow_idx = orig_arg_size;
            for (size_t idx= 0; idx < orig_arg_size; idx++) {
              const Value* ArgPtr = CS.getArgument (idx);
              // this could be a symptom of a bug
              if (isa<UndefValue> (ArgPtr) || isa<ConstantPointerNull> (ArgPtr))
                continue;
              if (IsShadowableType (ArgPtr->getType ())) {
                instrumentSizeAndOffsetPtr (F, B, inst, ArgPtr);                  
                Value *ptrSize   = m_sizes [ArgPtr];
                Value *ptrOffset = m_offsets [ArgPtr];
                if (ptrSize && ptrOffset) {
                  CS.setArgument (shadow_idx, ptrOffset);
                  CS.setArgument (shadow_idx+1, ptrSize);
                }
                shadow_idx +=2;
              }
            }
          }
        }
      }
      else if (const ReturnInst *ret = dyn_cast<ReturnInst> (inst)) {
        if (const Value* retVal = ret->getReturnValue ()) {
          if (IsShadowableType (retVal->getType ())) {
            // Resolving the shadow offset and size of the return
            // value of a function. At this point, F has this form:
            //    ...
            //    g_ret.off = _;
            //    g_ret.size = _;
            //    return p;
            // 
            // The placeholders _ are filled out with the shadow
            // variables associated with the return variable.
            instrumentSizeAndOffsetPtr (F, B, inst, retVal);                  
            Value *ShadowOffset = m_offsets [retVal];
            Value *ShadowSize = m_sizes [retVal];
            if (ShadowOffset && ShadowSize) {
              auto p = findShadowRet (F);
              if (p.first) 
                p.first->setOperand (0, ShadowOffset);
              if (p.second) 
                p.second->setOperand (0, ShadowSize);
            }
          }
        }
      }
      else if (LoadInst *load = dyn_cast<LoadInst> (inst)) {
        Value * Ptr = load->getOperand (0);
        if (Ptr == m_ret_size || Ptr == m_ret_offset) continue;
        
        m_mem_accesses++;
        if (!abc_helpers::IsTrivialCheck (m_dl, m_tli, Ptr))  {
          instrumentCheck (*F, B, *inst, *Ptr, nullptr);           
        } else 
          m_trivial_checks++;
      }
      else if (StoreInst *store = dyn_cast<StoreInst> (inst)) {
        Value * Ptr = store->getOperand (1);
        if (Ptr == m_ret_size || Ptr == m_ret_offset) continue;

        m_mem_accesses++;
        if (!abc_helpers::IsTrivialCheck (m_dl, m_tli, Ptr)) {
          instrumentCheck (*F, B, *inst, *Ptr, nullptr);           
        } else 
          m_trivial_checks++;
      }
    }
    
    errs () << " ========== ABC  ==========\n";
    errs () << "-- " << m_mem_accesses    
            << " Total number of memory reads/writes\n" ;
    errs () << "-- " << m_mem_accesses - m_checks_unable  
            << " Total number of memory reads/writes instrumented\n";
    errs () << "-- " << m_checks_unable
            << " Total number of memory reads/writes NOT instrumented\n";
    errs () << "-- " << m_checks_added    
            << " Total number of added buffer overflow/underflow checks\n";

    if (TrackedDSNode != 0) {
      errs () << "-- " << untracked_dsa_checks 
              << " Total number of skipped checks because untracked DSA node\n";
    }

    return true;
  }
    
  void ABC1::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<seahorn::DSACount>();
    AU.addRequired<llvm::DataLayoutPass>();
    AU.addRequired<llvm::TargetLibraryInfo>();
    AU.addRequired<llvm::UnifyFunctionExitNodes> ();
    AU.addRequired<CanAccessMemory> ();
  } 

  char ABC1::ID = 0;

  static llvm::RegisterPass<ABC1> 
  X ("abc-1", "Insert array buffer checks");

} // end namespace


 
namespace seahorn {
    using namespace llvm;

    void ABC2::ABCInst::update_callgraph(Function* caller, 
                                         CallInst* callee) {
      if (m_cg) {
        (*m_cg)[caller]->addCalledFunction (CallSite (callee),
                                            (*m_cg)[callee->getCalledFunction ()]);
      }
    }

    //! extract offset from gep
    Value* ABC2::ABCInst::doGep(GetElementPtrInst *gep) {
      SmallVector<Value*, 4> ps;
      SmallVector<Type*, 4> ts;
      gep_type_iterator typeIt = gep_type_begin (*gep);
      for (unsigned i = 1; i < gep->getNumOperands (); ++i, ++typeIt) {
        ps.push_back (gep->getOperand (i));
        ts.push_back (*typeIt);
      }
      
      Value* base = abc_helpers::createIntCst (m_B.getContext (), 0);
      Value* curVal = base;
      
      for (unsigned i = 0; i < ps.size (); ++i) {
        if (const StructType *st = dyn_cast<StructType> (ts [i])) {
          if (const ConstantInt *ci = dyn_cast<ConstantInt> (ps [i])) {
            unsigned off = abc_helpers::fieldOffset (m_dl, st, ci->getZExtValue ());
            curVal = abc_helpers::createAdd(m_B, curVal, 
                                            abc_helpers::createIntCst (m_B.getContext (), off));
          }
          else assert (false);
        }
        else if (SequentialType *seqt = dyn_cast<SequentialType> (ts [i]))
        { // arrays, pointers, and vectors
          unsigned sz = abc_helpers::storageSize (m_dl, seqt->getElementType ());
          Value *lhs = curVal;
          Value *rhs = abc_helpers::createMul (m_B, ps[i], sz);
          curVal = abc_helpers::createAdd (m_B, lhs, rhs); 
        }
      } 
      return curVal;
    }

    //! Instrument pointer arithmetic
    //  lhs = rhs + n;
    void ABC2::ABCInst::doPtrArith (Value* lhs, Value* rhs, 
                                    GetElementPtrInst * gep, 
                                    Instruction* insertPt) {
      /* 
          if (nd () && tracked_ptr && rhs == tracked_ptr) {
             tracked_ptr = lhs;
             tracked_offset += n;
          }

          TODO:
            bool f = nd () tracked_ptr && rhs == tracked_ptr ? lhs: tracked_ptr;
            tracked_ptr = (f ? lhs: rhs);
            tracked_offset += (f ? n: 0);
      */

      // We do not need to instrument the gep instruction if all uses
      // are load and store instructions since when checking those
      // uses the offset can be extracted directly from the base
      // pointer of the instruction.
      if (std::all_of (gep->uses().begin (), gep->uses().end (), 
                       [](Use& u) { 
                         return (isa<LoadInst>(u.get()) || 
                                 isa<StoreInst>(u.get()));}))
        return;

      LLVMContext& ctx = m_B.getContext ();
      BasicBlock* bb = insertPt->getParent ();
      Function* F = bb->getParent ();
      BasicBlock* cont = bb->splitBasicBlock(insertPt);

      /// if (nd () && tracked_ptr && rhs == tracked_ptr)
      m_B.SetInsertPoint (bb->getTerminator ());
      CallInst *ci_nondet = m_B.CreateCall (m_nondetFn);
      Value *vtracked_ptr = abc_helpers::createLoad(m_B, m_tracked_ptr, m_dl);
      update_callgraph (insertPt->getParent()->getParent(), ci_nondet);
      Value* condA = m_B.CreateICmpSGE (ci_nondet, 
                                        abc_helpers::createIntCst (ctx, 0));
      Value* condB = m_B.CreateICmpSGT(vtracked_ptr,
                                       abc_helpers::createNullCst (ctx));
      Value* condC = m_B.CreateICmpEQ (m_B.CreateBitOrPointerCast (rhs, abc_helpers::voidPtr (ctx)),
                                       vtracked_ptr);
      Value* cond = m_B.CreateAnd (condA, m_B.CreateAnd (condB, condC));
      bb->getTerminator ()->eraseFromParent ();      
      BasicBlock* bb1 = BasicBlock::Create(ctx, "update_ptr_" + lhs->getName ()  + "_bb", F);
      BranchInst::Create (bb1, cont, cond, bb);      

      m_B.SetInsertPoint (bb1);
      /// tracked_ptr = lhs;
      abc_helpers::createStore (m_B, m_B.CreateBitOrPointerCast (lhs, abc_helpers::voidPtr (ctx)),
                                m_tracked_ptr, m_dl);
      /// tracked_offset += n;
      Value* gep_offset = doGep (gep);    
      abc_helpers::createStore (m_B, 
                                abc_helpers::createAdd(m_B, 
                                                       gep_offset, 
                                                       abc_helpers::createLoad(m_B, m_tracked_offset, m_dl)),
                                m_tracked_offset, m_dl);

      BranchInst::Create (cont, bb1);
    }

    //! Initialization of base, offset, and size.
    void ABC2::ABCInst::doInit (Module& M) {
      /*
         assume (tracked_base > 0);
         assume (tracked_size > 0);
         tracked_ptr = 0;
         tracked_offset = 0;
      */

      Function* main = M.getFunction ("main");
      assert (main);
      BasicBlock& main_entry = main->getEntryBlock ();
      m_B.SetInsertPoint (main->getEntryBlock ().getFirstInsertionPt ());
      LLVMContext& ctx = m_B.getContext ();      

      // p1 = nd ();
      // assume (p1 > 0);
      // m_tracked_base  = p1
      m_tracked_base = abc_helpers::createGlobalPtr (M, "tracked_base");
      CallInst* p1 = m_B.CreateCall (m_nondetPtrFn, "nd");
      update_callgraph (main, p1);
      CallInst* c_assume1 = 
          m_B.CreateCall (m_assumeFn,
                          m_B.CreateICmpSGT(p1, 
                                            m_B.CreateBitOrPointerCast (abc_helpers::createNullCst (ctx), 
                                                                        p1->getType ())));
      update_callgraph (main, c_assume1);
      abc_helpers::createStore (m_B, p1, m_tracked_base, m_dl);

      // x = nd ();
      // assume (x > 0);
      // m_tracked_size = x;
      m_tracked_size = abc_helpers::createGlobalInt (M, 0, "tracked_size");
      CallInst *x = m_B.CreateCall (m_nondetFn);
      update_callgraph (main, x);
      CallInst* c_assume2 = 
          m_B.CreateCall (m_assumeFn, 
                          m_B.CreateICmpSGT(x, abc_helpers::createIntCst(ctx, 0)));
      update_callgraph (main, c_assume2);
      abc_helpers::createStore (m_B, x, m_tracked_size, m_dl);
      // m_tracked_ptr = 0
      m_tracked_ptr  = abc_helpers::createGlobalPtr (M, "tracked_ptr");
      abc_helpers::createStore (m_B, abc_helpers::createNullCst (ctx), m_tracked_ptr, m_dl);

      // m_tracked_offset = 0;
      m_tracked_offset = abc_helpers::createGlobalInt (M, 0, "tracked_offset");

      Instruction * insertPt = m_B.GetInsertPoint ();
      /// Allocation of global variables
      for (auto &GV: M.globals ()) {

        // skip global variables that we just introduced
        if (&GV == m_tracked_base || &GV == m_tracked_ptr ||
            &GV == m_tracked_offset || &GV == m_tracked_size)
          continue;
        
        uint64_t size;
        if (getObjectSize(&GV, size, m_dl, m_tli, true)) {
          doAllocaSite (&GV,
                        abc_helpers::createIntCst (m_B.getContext (), size), 
                        insertPt);
        }
        else {
          // this should not happen ...
          errs () << "Warning: cannot infer statically the size of global " 
                  << GV << "\n";
        }
      }
    }

    //! Instrument any allocation site
    // p := alloca (n) or p:= malloc (n)
    void ABC2::ABCInst::doAllocaSite (Value* Ptr, Value* Size /* bytes*/, 
                                      Instruction* insertPt) {
      /*
           if (!tracked_ptr && p == tracked_base)
              tracked_ptr  = tracked_base
              assume (tracked_size == n)
              tracked_offset = 0
           else { 
              assume (tracked_base + m_tracked_size < p); 
           }
      */

      LLVMContext& ctx = m_B.getContext ();
      BasicBlock* bb = insertPt->getParent ();
      Function* F = bb->getParent ();
      BasicBlock *cont = bb->splitBasicBlock(insertPt);
      BasicBlock* alloca_then_bb = 
          BasicBlock::Create(ctx, "allocated_" + Ptr->getName () + "_bb", F);
      BasicBlock* alloca_else_bb = 
          BasicBlock::Create(ctx, "not_allocated_" + Ptr->getName () + "_bb", F);

      m_B.SetInsertPoint (bb->getTerminator ());
      Value* vtracked_size = abc_helpers::createLoad(m_B, m_tracked_size, m_dl);
      Value* vtracked_base = abc_helpers::createLoad(m_B, m_tracked_base, m_dl);
      Value* PtrX = m_B.CreateBitOrPointerCast (Ptr, abc_helpers::voidPtr (ctx));
      Value* cond = m_B.CreateAnd (m_B.CreateIsNull(abc_helpers::createLoad(m_B, m_tracked_ptr, m_dl)),
                                   m_B.CreateICmpEQ (PtrX, vtracked_base));

      bb->getTerminator ()->eraseFromParent ();      
      BranchInst::Create (alloca_then_bb, alloca_else_bb, cond, bb);      

      m_B.SetInsertPoint (alloca_then_bb);
      /// tracked_ptr = tracked_base
      abc_helpers::createStore (m_B, vtracked_base, m_tracked_ptr, m_dl);
      /// assume (tracked_size == n);
      CallInst* assume1 = m_B.CreateCall (m_assumeFn, 
                  m_B.CreateICmpEQ(vtracked_size,
                                   m_B.CreateSExtOrTrunc (Size, 
                                                          abc_helpers::createIntTy (ctx))));
      
      /// tracked_offset = 0
      abc_helpers::createStore (m_B, abc_helpers::createIntCst (ctx, 0), 
                                m_tracked_offset, m_dl);

      BranchInst::Create (cont, alloca_then_bb);

      // assume (tracked_base + tracked_size < p); 
      m_B.SetInsertPoint (alloca_else_bb);
      CallInst* assume2 = m_B.CreateCall (m_assumeFn, 
                                          m_B.CreateICmpSLT(m_B.CreateGEP(vtracked_base, vtracked_size),
                                                            PtrX));

      update_callgraph (insertPt->getParent()->getParent(), assume2);
      BranchInst::Create (cont, alloca_else_bb);
      
    }

    //! Instrument any read or write to a pointer and also memory
    //! intrinsics. If N is not null then the check corresponds to a
    //! memory intrinsic
    void ABC2::ABCInst::doChecks (Value* Ptr, Value* N /*bytes*/, Instruction* insertPt) {
      /*  
          if N is null then the check corresponds to a store or
          load. In that case, the added code is:

          if (tracked_ptr && p == tracked_ptr) {
              assert (tracked_offset + align < tracked_size);
              assert (tracked_offset >= 0);
          }
           
          otherwise, the check corresponds to a memory intrinsic
          (memcpy, memmove, or memset). The code differs slightly:

          if (tracked_ptr && p == tracked_ptr) {
              assert (tracked_offset + n < tracked_size);
              assert (tracked_offset >= 0);
          }
      */

      LLVMContext& ctx = m_B.getContext ();
      BasicBlock* bb = insertPt->getParent ();
      Function* F = bb->getParent ();

      BasicBlock* err_under_bb = BasicBlock::Create(ctx, "underflow_bb", F);
      BasicBlock* err_over_bb = BasicBlock::Create(ctx, "overflow_bb", F);
      BasicBlock* abc_under_bb = BasicBlock::Create(ctx, "under_check_bb", F);
      BasicBlock* abc_over_bb = BasicBlock::Create(ctx, "over_check_bb", F);

      // populate the error blocks
      m_B.SetInsertPoint (err_under_bb);
      CallInst* ci_under = m_B.CreateCall (m_errorFn);
      update_callgraph (insertPt->getParent()->getParent(), ci_under);
      ci_under->setDebugLoc (insertPt->getDebugLoc ());
      m_B.CreateUnreachable ();

      m_B.SetInsertPoint (err_over_bb);
      CallInst* ci_over = m_B.CreateCall (m_errorFn);
      update_callgraph (insertPt->getParent()->getParent(), ci_over);
      ci_over->setDebugLoc (insertPt->getDebugLoc ());
      m_B.CreateUnreachable ();

      BasicBlock *cont = bb->splitBasicBlock(insertPt);
      m_B.SetInsertPoint (bb->getTerminator ());

      // if (m_tracked_ptr && ptr == m_tracked_ptr)
      Value* vtracked_ptr = abc_helpers::createLoad(m_B, m_tracked_ptr, m_dl);
      Value* vtracked_base = abc_helpers::createLoad(m_B, m_tracked_base, m_dl);

      Value* condA = m_B.CreateICmpSGT(vtracked_ptr, 
                                       abc_helpers::createNullCst (ctx));
      Value* condB = m_B.CreateICmpEQ (vtracked_ptr,
                                       m_B.CreateBitOrPointerCast (Ptr, abc_helpers::voidPtr (ctx)));
      Value* cond = m_B.CreateAnd (condA, condB);
      bb->getTerminator ()->eraseFromParent ();      
      BranchInst::Create (abc_under_bb, cont, cond, bb);      
      m_B.SetInsertPoint (abc_under_bb);

      // In general, we can use tracked_offset and
      // tracked_size. However, in some cases (e.g., if the load/store
      // uses a gep instruction) we try to extract directly the offset
      // and size.

      Value* addr = nullptr;
      if (GetElementPtrInst * gep = dyn_cast<GetElementPtrInst> (Ptr))
        addr = gep->getPointerOperand ();
      if (!addr && isa<GlobalVariable>(Ptr))
        addr = Ptr;
      if (!addr && isa<AllocaInst>(Ptr))
        addr = Ptr;
      // TODO: malloc's and bitcast's

      Value* addrEqualToBase = nullptr;
      if (addr)
          addrEqualToBase = m_B.CreateICmpEQ (vtracked_base, 
                            m_B.CreateBitOrPointerCast (addr, abc_helpers::voidPtr (ctx)));

      Value* size = nullptr;
      if (addr) {
        uint64_t vsize;
        if (getObjectSize(addr, vsize, m_dl, m_tli, true)) {
          size = m_B.CreateSelect (addrEqualToBase,
                                   abc_helpers::createIntCst (m_B.getContext (), vsize), 
                                   abc_helpers::createLoad(m_B, m_tracked_size, m_dl));
        }
      }

      Value* offset = nullptr;
      if (addr) {
        Value* o = nullptr;
        if (GetElementPtrInst * gep = dyn_cast<GetElementPtrInst> (Ptr))
          o = doGep (gep);
        else
          o = abc_helpers::createIntCst (m_B.getContext (), 0); 
        
        offset = m_B.CreateSelect (addrEqualToBase, o, 
                                   abc_helpers::createLoad(m_B, m_tracked_offset, m_dl));
      }

      // if no optimization possible then use tracked_offset and
      // tracked_size
      if (!offset) {
        offset = abc_helpers::createLoad(m_B, m_tracked_offset, m_dl);
      }

      if (!size) { 
        size = abc_helpers::createLoad(m_B, m_tracked_size, m_dl); 
      }

      /////
      // underflow check: m_tracked_offset >= 0
      /////

      // abc_under_bb:
      //    if (m_tracked_offset >= 0) goto abc_over_bb else goto err_under_bb
      Value* under_cond = 
          m_B.CreateICmpSGE (offset,
                             abc_helpers::createIntCst (ctx, 0));
      BranchInst::Create (abc_over_bb, err_under_bb, under_cond, abc_under_bb);            
      m_checks_added++;

      /////
      // overflow check
      /////

      m_B.SetInsertPoint (abc_over_bb);
      // abc_over_bb:
      // We have two cases whether n is not null or not.
      // 
      // case a)
      //    if (m_tracked_offset + n <= m_tracked_size) 
      //        goto cont 
      //    else 
      //        goto err_over_bb
      // case b)
      //    if (m_tracked_offset + align <= m_tracked_size) 
      //        goto cont 
      //    else 
      //        goto err_over_bb
      if (N) {
        // both offset and N are in bytes
        offset = abc_helpers::createAdd (m_B, offset, N);
      } else {
        int align = abc_helpers::getOffsetAlign (*insertPt);
        if (align < 0) { // this should not happen
          errs () << "Error: cannot find align for " << *insertPt << "\n";
          return;
        }
        // both offset and align are in bytes
        offset = abc_helpers::createAdd (m_B, offset, 
                                         abc_helpers::createIntCst (ctx, align));
      }
      
      Value* over_cond = m_B.CreateICmpSLE (offset, size);
      BranchInst::Create (cont, err_over_bb, over_cond, abc_over_bb);            
      m_checks_added++;      
    }

    ABC2::ABCInst::ABCInst (Module& M, 
                            const DataLayout* dl, 
                            const TargetLibraryInfo* tli,
                            IRBuilder<> B, CallGraph* cg,
                            Function* errorFn, Function* nondetFn,
                            Function* nondetPtrFn, Function* assumeFn): 
        m_dl (dl), m_tli (tli), m_B (B), m_cg (cg),
        m_tracked_base (nullptr), m_tracked_ptr (nullptr),
        m_tracked_offset (nullptr), m_tracked_size (nullptr),        
        m_errorFn (errorFn), m_nondetFn (nondetFn), 
        m_nondetPtrFn (nondetPtrFn), m_assumeFn (assumeFn),
        m_checks_added (0), m_trivial_checks (0), m_mem_accesses (0)
    {     
      doInit (M);
    }
                  
    void ABC2::ABCInst::visit (GetElementPtrInst *I) {
      Value *lhs = I;
      if (!abc_helpers::IsTrivialCheck (m_dl, m_tli, lhs)) {
        Value *rhs = I->getPointerOperand ();            
        doPtrArith (lhs, rhs, I, abc_helpers::getNextInst (I));
      }
    }

    void ABC2::ABCInst::visit (LoadInst *I) {
      Value* ptr = I->getPointerOperand ();

      // skip our own global variables
      if (ptr == m_tracked_base || ptr == m_tracked_ptr ||
          ptr == m_tracked_offset || ptr == m_tracked_size)
        return;

      m_mem_accesses++;
      if (!abc_helpers::IsTrivialCheck (m_dl, m_tli, ptr)) {
        doChecks (ptr, nullptr, I);        
      }
      else
        m_trivial_checks++;
    }
    
    void ABC2::ABCInst::visit (StoreInst *I) {
      Value* ptr = I->getPointerOperand ();

      // skip our own global variables
      if (ptr == m_tracked_base || ptr == m_tracked_ptr ||
          ptr == m_tracked_offset || ptr == m_tracked_size)
        return;

      m_mem_accesses++;
      if (!abc_helpers::IsTrivialCheck (m_dl, m_tli, ptr)) {
        doChecks (ptr, nullptr, I);
      }
      else 
        m_trivial_checks++;
    }

    void ABC2::ABCInst::visit (MemTransferInst *MTI) {
      m_mem_accesses+=2;

      doChecks (MTI->getDest (), MTI->getLength (), MTI);
      doChecks (MTI->getSource (), MTI->getLength (), MTI);
    }

    void ABC2::ABCInst::visit (MemSetInst *MSI) {
      m_mem_accesses++;

      doChecks (MSI->getDest (), MSI->getLength (), MSI);
    }

    void ABC2::ABCInst::visit (AllocaInst *I) {
      // note that the frontend can promote malloc-like instructions
      // to alloca's.

      uint64_t size; //bytes
      if (getObjectSize(I, size, m_dl, m_tli, true)) {
        doAllocaSite (I, 
                      abc_helpers::createIntCst (m_B.getContext (), size), 
                      abc_helpers::getNextInst (I)); 
        return;
      } else {
        Value *nElems = I->getArraySize (); // number of elements
        Type* ty = I->getAllocatedType (); // size of the allocated type
        unsigned ty_size = abc_helpers::storageSize (m_dl, ty); // bytes
        Value* size = nullptr;
        if (ty_size == 1) 
          size = nElems;
        else {
          m_B.SetInsertPoint (I);
          size = abc_helpers::createMul (m_B, nElems, ty_size, "alloca_size");
        }
        doAllocaSite (I, size, abc_helpers::getNextInst (I)); 
        return;
      }
      errs () << "Warning: missing alloca site: " << *I << "\n";
    }

    void ABC2::ABCInst::visit (CallInst *I) {
      if (isMallocLikeFn (I, m_tli)) {
        if (I->getNumArgOperands () == 1) {
          Value *size = I->getArgOperand(0); // bytes
          doAllocaSite (I, size, abc_helpers::getNextInst (I)); 
          return;
        }
      }
      errs () << "Warning: missing alloca site: " << *I << "\n";
    }

   // Whether a pointer should be tracked based on DSA (if available)
   bool ABC2::ShouldBeTrackedPtr (Value* ptr, Function& F) {
     #ifndef HAVE_DSA
     return true;
     #else
     if (TrackedDSNode == 0)
       return true; 

     DSACount* m_dsa_count = &getAnalysis<DSACount> ();
     assert (m_dsa_count);
     
     DSGraph* dsg = nullptr;
     DSGraph* gDsg = nullptr;
     if (m_dsa_count->getDSA ()) {
       dsg = m_dsa_count->getDSA ()->getDSGraph (F);
       gDsg = m_dsa_count->getDSA ()->getGlobalsGraph (); 
     }
     
     const DSNode* n = dsg->getNodeForValue (ptr).getNode ();
     if (!n) n = gDsg->getNodeForValue (ptr).getNode ();
     if (!n) 
       return false; // DSA node not found. This should not happen.
     
     return (m_dsa_count->getId (n) == TrackedDSNode);
     #endif 
   }

  bool ABC2::runOnModule (llvm::Module &M)
  {
    if (M.begin () == M.end ()) return false;

    Function* main = M.getFunction ("main");
    if (!main) {
      errs () << "Main not found: no buffer overflow checks added\n";
      return false;
    }

    // Print statistics about DSA nodes
    DSACount* m_dsa_count = &getAnalysis<DSACount> ();    
    if (m_dsa_count)
      m_dsa_count->write (errs ());

    LLVMContext &ctx = M.getContext ();

    AttrBuilder AB;
    AB.addAttribute (Attribute::NoReturn);
    AttributeSet as = AttributeSet::get (ctx, AttributeSet::FunctionIndex, AB);
    Function* errorFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.error",
                                as,
                                Type::getVoidTy (ctx), NULL));

    AB.clear ();
    as = AttributeSet::get (ctx, AttributeSet::FunctionIndex, AB); 

    Function* nondetFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.nondet",
                                as,
                                Type::getInt64Ty (ctx), 
                                NULL));

    Function* nondetPtrFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.nondet_ptr",
                                as,
                                Type::getInt8Ty (ctx)->getPointerTo (), 
                                NULL));

    Function* assumeFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.assume", 
                                as,
                                Type::getVoidTy (ctx),
                                Type::getInt1Ty (ctx),
                                NULL));
    
    IRBuilder<> B (ctx);

    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
    CallGraph* cg = cgwp ? &cgwp->getCallGraph () : nullptr;
    if (cg)
    {
      cg->getOrInsertFunction (assumeFn);
      cg->getOrInsertFunction (errorFn);
      cg->getOrInsertFunction (nondetFn);
      cg->getOrInsertFunction (nondetPtrFn);
    }

    unsigned untracked_dsa_checks = 0;
    const TargetLibraryInfo * tli = &getAnalysis<TargetLibraryInfo>();
    std::vector<Instruction*> Worklist;
    for (Function &F : M) {
      if (F.isDeclaration ()) continue;
    
      for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i)  {
        Instruction *I = &*i;

        if (GetElementPtrInst * GEP  = dyn_cast<GetElementPtrInst> (I)) {
          Value *ptr = GEP->getPointerOperand ();            
          if (ShouldBeTrackedPtr (ptr, F))
            Worklist.push_back (I);
        } else if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
          Value* ptr = LI->getPointerOperand ();
          if (ShouldBeTrackedPtr (ptr, F)) 
            Worklist.push_back (I);
          else 
            untracked_dsa_checks++;
        } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
          Value* ptr = SI->getPointerOperand ();
           if (ShouldBeTrackedPtr (ptr, F)) 
             Worklist.push_back (I);
           else 
             untracked_dsa_checks++; 
        } else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
          if (ShouldBeTrackedPtr (MTI->getDest (), F) || 
              ShouldBeTrackedPtr (MTI->getSource (),F))
            Worklist.push_back (I);
          else 
            untracked_dsa_checks+=2; 
        } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
          Value* ptr = MSI->getDest ();
           if (ShouldBeTrackedPtr (ptr, F)) 
             Worklist.push_back (I);
           else 
             untracked_dsa_checks++; 
        } else if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {
          Value* ptr = AI;
          if (ShouldBeTrackedPtr (ptr, F)) 
            Worklist.push_back (I);
        } else if (CallInst *CI = extractMallocCall (I, tli)) {
          Value* ptr = CI;
          if (ShouldBeTrackedPtr (ptr, F))
            Worklist.push_back (CI);
        }
      }
    } 
      
    const DataLayout * dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
    ABCInst abc (M, dl, tli, B, cg, errorFn, nondetFn, nondetPtrFn, assumeFn);
    for (auto I: Worklist) {
      if (GetElementPtrInst * GEP  = dyn_cast<GetElementPtrInst> (I)) {
        abc.visit (GEP);
      } else if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
        abc.visit (LI);
      } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
        abc.visit (SI);
      } else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
        abc.visit (MTI);        
      } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
        abc.visit (MSI);        
      } else if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {
        abc.visit (AI);
      } else if (CallInst *CI = dyn_cast<CallInst>(I)) {
        abc.visit (CI);
      }
    }

    errs () << " ========== ABC  ==========\n";
    errs () << "-- " << abc.m_mem_accesses 
            << " Total number of memory reads/writes\n"
            << "-- " << abc.m_checks_added 
            << " Total number of added buffer overflow/underflow checks\n"; 

    if (TrackedDSNode != 0) {
      errs () << "-- " << untracked_dsa_checks 
              << " Total number of skipped checks because untracked DSA node\n";
    }

    return true;
  }
    
  void ABC2::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<seahorn::DSACount>();
    AU.addRequired<llvm::DataLayoutPass>();
    AU.addRequired<llvm::TargetLibraryInfo>();
    AU.addRequired<llvm::UnifyFunctionExitNodes> ();
    AU.addRequired<llvm::CallGraphWrapperPass>();
  } 

  char ABC2::ID = 0;

  static llvm::RegisterPass<ABC2> 
  Y ("abc-2", "Insert array buffer checks");


} // end namespace seahorn
  

