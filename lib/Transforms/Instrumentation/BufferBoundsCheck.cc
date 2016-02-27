#include "seahorn/Transforms/Instrumentation/BufferBoundsCheck.hh"

#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"

static llvm::cl::opt<unsigned int>
TrackedDSNode("abc-dsa-node",
        llvm::cl::desc ("Only instrument pointers within this dsa node"),
        llvm::cl::init (0));

static llvm::cl::opt<bool>
DisableUnderflow("abc-disable-underflow",
        llvm::cl::desc ("Disable underflow checks"),
        llvm::cl::init (false));

#define DEREFERENCEABLE_OPT
#define SIZE_OPT

namespace seahorn {

   // common helpers to all ABC encodings
   namespace abc {

    using namespace llvm;

    // Similar to ObjectSizeOffsetVisitor in MemoryBuiltins but using
    // the dereferenceable attribute
    class WrapperObjectSizeOffsetVisitor
        : public InstVisitor<WrapperObjectSizeOffsetVisitor, SizeOffsetType> {
      
      const DataLayout *DL;
      const TargetLibraryInfo *TLI;
      unsigned IntTyBits;
      APInt Zero;
      SmallPtrSet<Instruction *, 8> SeenInsts;     
      ObjectSizeOffsetVisitor vis;
      
      SizeOffsetType unknown() 
      { return std::make_pair(APInt(), APInt()); }
      
      APInt align(APInt Size, uint64_t Align) {
        const bool RoundToAlign = true; // always true
        if (RoundToAlign && Align)
          return APInt(IntTyBits, RoundUpToAlignment(Size.getZExtValue(), Align));
        return Size;
      }
      
     public:
      
      WrapperObjectSizeOffsetVisitor(const DataLayout *DL, 
                                     const TargetLibraryInfo *TLI,
                                     LLVMContext &Context) : 
          DL (DL), TLI (TLI), vis (DL, TLI, Context, true) { }
      
      bool knownSize(SizeOffsetType &SizeOffset)
      { return SizeOffset.first.getBitWidth() > 1; }
      
      bool knownOffset(SizeOffsetType &SizeOffset) 
      { return SizeOffset.second.getBitWidth() > 1; }
      
      bool bothKnown(SizeOffsetType &SizeOffset) 
      { return knownSize(SizeOffset) && knownOffset(SizeOffset); }
      
      SizeOffsetType compute(Value *V)  {
        IntTyBits = DL->getPointerTypeSizeInBits(V->getType());
        Zero = APInt::getNullValue(IntTyBits);
        V = V->stripPointerCasts();
        if (Instruction *I = dyn_cast<Instruction>(V)) {
          // If we have already seen this instruction, bail
          // out. Cycles can happen in unreachable code after constant
          // propagation.
          if (!SeenInsts.insert(I).second)
            return unknown();
          if (GEPOperator *GEP = dyn_cast<GEPOperator>(V))
            return visitGEPOperator(*GEP);
          if (CallInst* CI = dyn_cast<CallInst> (V)) {
            // return value of a callsite
            CallSite CS (CI);
            unsigned deref_bytes = CS.getDereferenceableBytes(0);
            if (deref_bytes > 0) {
              // the size is actually >= deref_bytes so we are
              // returning a lower bound as the actual size.
              APInt Size(IntTyBits, deref_bytes);
              return std::make_pair(align(Size, CS.getParamAlignment(0)), Zero);
            }
          }
          return vis.compute (V);
        }
        if (Argument *A = dyn_cast<Argument>(V))
          return visitArgument(*A);
        if (isa<ConstantPointerNull>(V))
          return vis.compute(V);
        if (isa<GlobalAlias>(V))
          return vis.compute (V);
        if (isa<GlobalVariable>(V))
          return vis.compute (V);
        if (isa<UndefValue>(V))
          return vis.compute (V);
        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(V)) {
          if (CE->getOpcode() == Instruction::IntToPtr)
            return unknown(); 
          if (CE->getOpcode() == Instruction::GetElementPtr)
            return visitGEPOperator(cast<GEPOperator>(*CE));
        }
        return unknown();
      }
      
      SizeOffsetType visitArgument(Argument &A) {
        // no interprocedural analysis is done at the moment
        if (A.hasByValOrInAllocaAttr()) {
          PointerType *PT = cast<PointerType>(A.getType());
          APInt Size(IntTyBits, DL->getTypeAllocSize(PT->getElementType()));
          return std::make_pair(align(Size, A.getParamAlignment()), Zero);
        }
        else {
          uint64_t deref_bytes = A.getDereferenceableBytes ();
          if (deref_bytes > 0) {
            // the size is actually >= deref_bytes so we are
            // returning a lower bound as the actual size.
            APInt Size(IntTyBits, deref_bytes);
            return std::make_pair(align(Size, A.getParamAlignment()), Zero);
          }
        } 
        return unknown ();
      }
            
      SizeOffsetType visitGEPOperator(GEPOperator &GEP) {
        SizeOffsetType PtrData = compute(GEP.getPointerOperand());
        APInt Offset(IntTyBits, 0);
        if (!bothKnown(PtrData) || !GEP.accumulateConstantOffset(*DL, Offset))
          return unknown();
        return std::make_pair(PtrData.first, PtrData.second + Offset);
      }
     
    }; 
   
    inline bool getObjectSize(const Value *Ptr, uint64_t &Size, const DataLayout *DL,
                              const TargetLibraryInfo *TLI, bool RoundToAlign) {
      if (!DL)
        return false;
#if 1
      WrapperObjectSizeOffsetVisitor Visitor(DL, TLI, Ptr->getContext());
      SizeOffsetType Data = Visitor.compute(const_cast<Value*>(Ptr));
      if (!Visitor.bothKnown(Data))
        return false;
      
      APInt ObjSize = Data.first, Offset = Data.second;
      if (Offset.slt(0) || ObjSize.ult(Offset))
        Size = 0; // overflow
      else
        Size = (ObjSize - Offset).getZExtValue();
      return true;
#else
      return llvm::getObjectSize(Ptr, Size, DL, TLI, RoundToAlign);
#endif 
   }

    inline Value* getArgument (Function *F, unsigned pos) {
      unsigned idx = 0;
      for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end(); I != E;
           ++I, idx++)
      {
        if (idx == pos) return &*I; 
      }
      return nullptr;
    }
  
    inline ReturnInst* getReturnInst (Function *F) {
      // Assume there is one single return instruction per function
      for (llvm::BasicBlock& bb : *F)
      {
        if (ReturnInst *ret = dyn_cast<ReturnInst> (bb.getTerminator ()))
          return ret;
      }
      return nullptr;
    }

    inline unsigned storageSize (const DataLayout* dl, const llvm::Type *t) {
      // getTypeStorageSize does not include aligment padding.
      return dl->getTypeAllocSize (const_cast<Type*> (t));
    }

    inline unsigned storageSize (const DataLayout* dl, llvm::Type *t) {
     // getTypeStorageSize does not include aligment padding.
      return dl->getTypeAllocSize (t);
    }

    inline int getAddrSize (const DataLayout* dl, const Instruction& I) {
      int size = -1; 
      if (const StoreInst * SI = dyn_cast<const StoreInst> (&I)) {
        size = (int) storageSize (dl, SI->getPointerOperand ()->getType ());
      }
      else if (const LoadInst * LI = dyn_cast<const LoadInst> (&I)) {
        size = (int) storageSize (dl, LI->getPointerOperand ()->getType ());
      }
      return size; 
    }
 
    // Return true iff the check can be determined as definitely safe
    // or unsafe statically.
    inline bool IsTrivialCheck (const DataLayout* dl, 
                                const TargetLibraryInfo* tli,
                                const Value* Ptr) {

      // Compute the size of the object pointed by Ptr. It also checks
      // for underflow and overflow.
      uint64_t Size;
      if (abc::getObjectSize (Ptr, Size, dl, tli, true)){
        // static check
        if (Size == 0) {
         // XXX: this is not true anymore if dereferenceable attribute is used
         errs () << "ArrayBoundsCheck: definite unsafe access to " << *Ptr << "\n";
        }
        return true;
      } 
      return false; 
    }
   
    bool canEscape (GetElementPtrInst* GEP) {
      for (Use& u: GEP->uses ()) {
        if (isa<ICmpInst> (u.getUser ()))
          continue;
        else if (isa<LoadInst> (u.getUser ()))
          continue;
        else if (StoreInst* SI = dyn_cast<StoreInst> (u.getUser ())) {
          if (SI->getValueOperand () == GEP)
            return true;
        } else {
          // TODO: any other case where it cannot escape
          return true;
        }
      }
      return false;
    }

    inline uint64_t fieldOffset (const DataLayout* dl, const StructType *t, 
                                 unsigned field) {
      return dl->getStructLayout (const_cast<StructType*>(t))->
          getElementOffset (field);
    }

    // Helper to return the next instruction to I
    inline Instruction* getNextInst (Instruction* I) {
      if (I->isTerminator ()) return I;
      return I->getParent ()->getInstList ().getNext (I);
    }
    
    inline Type* createIntTy (const DataLayout*dl, LLVMContext& ctx) {
      return dl->getIntPtrType (ctx, 0);
    }

    inline Type* geti8PtrTy (LLVMContext &ctx) {
      return Type::getInt8Ty (ctx)->getPointerTo ();
    }

    inline Value* createIntCst (Type* ty, int64_t val) {
      return ConstantInt::get (ty, val);
    }

    inline Value* createAdd (IRBuilder<> B, const DataLayout*dl,
                             Value *LHS, Value *RHS, 
                             const Twine &Name = "") {
      assert (LHS->getType ()->isIntegerTy () && 
              RHS->getType ()->isIntegerTy ());
      Type* IntTy = createIntTy (dl, B.getContext ());
      Value *LHS1 = B.CreateSExtOrBitCast (LHS, IntTy);
      Value *RHS1 = B.CreateSExtOrBitCast (RHS, IntTy);
      return  B.CreateAdd (LHS1, RHS1, Name);
    }

    inline Value* createMul (IRBuilder<> B, const DataLayout*dl, 
                             Value *LHS, unsigned RHS, 
                             const Twine &Name = "") {
      assert (LHS->getType ()->isIntegerTy ());
      Type* IntTy = createIntTy (dl, B.getContext ());
      Value* LHS1 = B.CreateSExtOrBitCast (LHS, IntTy );
      return  B.CreateMul (LHS1, 
                           createIntCst (IntTy, RHS),
                           Name);
    }

    inline Value* createLoad(IRBuilder<> B, Value *Ptr, 
                             const DataLayout* dl) {
      return B.CreateAlignedLoad (Ptr, 
                                  dl->getABITypeAlignment (Ptr->getType ()));
    }
  
    inline Value* createStore(IRBuilder<> B, Value* Val, Value *Ptr, 
                              const DataLayout* dl) {
      return B.CreateAlignedStore (Val, Ptr, 
                                   dl->getABITypeAlignment (Ptr->getType ()));
    }
                               
    inline Value* createNullCst (LLVMContext &ctx) {
      return ConstantPointerNull::get (cast<PointerType> (geti8PtrTy (ctx)));
    }

    inline Value* createGlobalInt (const DataLayout*dl, Module& M, 
                                   unsigned val, const Twine& Name ="") {
      IntegerType* intTy = cast<IntegerType>(createIntTy (dl, M.getContext ()));
      ConstantInt *Cst = ConstantInt::get(intTy, val);
      GlobalVariable *GV = new GlobalVariable (M, Cst->getType (), 
                                               false,  /*non-constant*/
                                               GlobalValue::InternalLinkage,
                                               Cst);
      GV->setName(Name);
      return GV;
    }

    inline Value* createGlobalPtr(Module& M, const Twine& Name ="") {
      auto NullPtr = cast<ConstantPointerNull>(createNullCst (M.getContext ()));
      GlobalVariable *GV = new GlobalVariable (M, geti8PtrTy (M.getContext ()), 
                                               false, /*non-constant*/
                                               GlobalValue::InternalLinkage,
                                               NullPtr);
      GV->setName(Name);
      return GV;
    }

    //! extract offset from gep using llvm machinery
    inline Value* computeGepOffset(const DataLayout* dl, IRBuilder<> B, 
                                   GetElementPtrInst *gep) {
      
      LLVMContext& ctx = B.getContext ();
      unsigned IntTyBits = dl->getPointerTypeSizeInBits(gep->getType());
      APInt offset(IntTyBits, 0);
      if (gep->accumulateConstantOffset (*dl, offset)){
        return createIntCst (createIntTy (dl, ctx), offset.getSExtValue ());       
      } else {
        return EmitGEPOffset (&B, *dl, gep, true);
      }
    }

    // //! extract offset from gep
    // inline Value* computeGepOffset(const DataLayout* dl, IRBuilder<> B, 
    //                                GetElementPtrInst *gep) {
    //   SmallVector<Value*, 4> ps;
    //   SmallVector<Type*, 4> ts;
    //   gep_type_iterator typeIt = gep_type_begin (*gep);
    //   for (unsigned i = 1; i < gep->getNumOperands (); ++i, ++typeIt) {
    //     ps.push_back (gep->getOperand (i));
    //     ts.push_back (*typeIt);
    //   }
      
    //   Type* IntTy = createIntTy (dl, B.getContext ());
    //   Value* base = abc::createIntCst (IntTy, 0);
    //   Value* curVal = base;
      
    //   for (unsigned i = 0; i < ps.size (); ++i) {
    //     if (const StructType *st = dyn_cast<StructType> (ts [i])) {
    //       if (const ConstantInt *ci = dyn_cast<ConstantInt> (ps [i])) {
    //         uint64_t off = abc::fieldOffset (dl, st, ci->getZExtValue ());
    //         curVal = abc::createAdd(B, dl, 
    //                                 curVal, 
    //                                 abc::createIntCst (IntTy, off));
    //       }
    //       else assert (false);
    //     }
    //     else if (SequentialType *seqt = dyn_cast<SequentialType> (ts [i]))
    //     { // arrays, pointers, and vectors
    //       unsigned sz = abc::storageSize (dl, seqt->getElementType ());
    //       Value *lhs = curVal;
    //       Value *rhs = abc::createMul (B, dl, ps[i], sz);
    //       curVal = abc::createAdd (B, dl, lhs, rhs); 
    //     }
    //   } 
    //   return curVal;
    // }

    // Whether a pointer should be tracked based on DSA (if available)
    bool ShouldBeTrackedPtr (Value* ptr, Function& F, DSACount* m_dsa_count) {
     #ifndef HAVE_DSA
     return true;
     #else
     
     DSGraph* dsg = nullptr;
     DSGraph* gDsg = nullptr;
     if (m_dsa_count->getDSA ()) {
       dsg = m_dsa_count->getDSA ()->getDSGraph (F);
       gDsg = m_dsa_count->getDSA ()->getGlobalsGraph (); 
     }
     
     const DSNode* n = dsg->getNodeForValue (ptr).getNode ();
     if (!n) n = gDsg->getNodeForValue (ptr).getNode ();
     if (!n) return true; // DSA node not found. This should not happen.
     
     if (!m_dsa_count->isAccessed (n))
       return false;
     else {
       if (TrackedDSNode != 0)
         return (m_dsa_count->getId (n) == TrackedDSNode);
       else 
         return true;
     }
     #endif 
   }

   inline void update_cg(CallGraph* cg, Function* caller, CallInst* callee) {
     if (cg) {
       (*cg)[caller]->addCalledFunction (CallSite (callee),
                                         (*cg)[callee->getCalledFunction ()]);
     }
   } 
  } // end namespace
} // end namespace

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
        Value* shadowOffset = abc::getArgument (F, shadow_idx);
        Value* shadowSize   = abc::getArgument (F, shadow_idx+1);
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
        ParamsTy.push_back (m_IntPtrTy);
        Twine offset_name = FAI->getName () + ".shadow.offset";
        NewNames.push_back (offset_name.str ());
        ParamsTy.push_back (m_IntPtrTy);
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
      ReturnInst* ret = abc::getReturnInst (NF);   
      B.SetInsertPoint (ret);

      // StoreInst* SI_Off = 
      //     B.CreateAlignedStore (UndefValue::get (m_IntPtrTy), 
      //                           m_ret_offset,
      //                           m_dl->getABITypeAlignment (m_ret_offset->getType ())); 

      // StoreInst* SI_Size = 
      //     B.CreateAlignedStore (UndefValue::get (m_IntPtrTy), 
      //                           m_ret_size,
      //                           m_dl->getABITypeAlignment (m_ret_size->getType ())); 

      StoreInst* SI_Off =  B.CreateStore (UndefValue::get (m_IntPtrTy), m_ret_offset); 
      StoreInst* SI_Size = B.CreateStore (UndefValue::get (m_IntPtrTy), m_ret_size);

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
        Args.push_back (UndefValue::get (m_IntPtrTy)); // for shadow formal parameters

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
                  PHIShadow->getIncomingValue (i) == UndefValue::get (m_IntPtrTy))) {
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
          uint64_t off = abc::fieldOffset (m_dl, st, ci->getZExtValue ());
          curVal = abc::createAdd (B, m_dl, curVal, 
                                   abc::createIntCst (m_IntPtrTy, off));
        }
        else assert (false);
      }
      else if (const SequentialType *seqt = dyn_cast<const SequentialType> (ts [i])) {
        // arrays, pointers, and vectors
        unsigned sz = abc::storageSize (m_dl, seqt->getElementType ());
        Value *LHS = curVal;
        Value *RHS = abc::createMul (B, m_dl, const_cast<Value*> (ps[i]), sz);
        curVal = abc::createAdd (B, m_dl, LHS, RHS); 
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
          PHINode::Create (m_IntPtrTy, PHI->getNumIncomingValues (), 
                           ((ptr->hasName ()) ? 
                            ptr->getName () + ".shadow.offset" : ""),
                           insertPoint);
      PHINode* shadowPHINodeSize = 
          PHINode::Create (m_IntPtrTy, PHI->getNumIncomingValues (), 
                           ((ptr->hasName ()) ? 
                            ptr->getName () + ".shadow.size" : ""),
                           insertPoint);

      for (unsigned i=0; i < PHI->getNumIncomingValues (); i++) {
        // placeholder for now
        shadowPHINodeOff->addIncoming (UndefValue::get (m_IntPtrTy), 
                                       PHI->getIncomingBlock (i));
        shadowPHINodeSize->addIncoming (UndefValue::get (m_IntPtrTy), 
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
      if (abc::getObjectSize(ptr, Size, m_dl, m_tli, true)) {
        m_offsets [ptr] = ConstantInt::get (m_IntPtrTy, 0);
        m_sizes [ptr] = ConstantInt::get (m_IntPtrTy, Size);
        return;
      } 

      if (const AllocaInst *AI = dyn_cast<AllocaInst> (ptr))  {
        Value *nElems = const_cast<Value*> (AI->getArraySize ()); // number of elements
        const Type* ty = AI->getAllocatedType (); // size of the allocated type
        unsigned ty_size = abc::storageSize (m_dl, ty);
        Value* size = nullptr;
        B.SetInsertPoint (insertPoint);
        if (ty_size == 1) 
          size = nElems;
        else 
          size = abc::createMul (B, m_dl, nElems, ty_size, "alloca_size");
        m_offsets [ptr] = ConstantInt::get (m_IntPtrTy, 0);
        m_sizes [ptr] = B.CreateZExtOrTrunc (size, m_IntPtrTy);
        return;
      }
      else if (const CallInst * MallocInst = extractMallocCall (ptr ,m_tli)) {
        if (MallocInst->getNumArgOperands () == 1) {
          Value *size = MallocInst->getArgOperand(0);
          if (size->getType ()->isIntegerTy ()) {
            B.SetInsertPoint(insertPoint);
            m_offsets [ptr] = ConstantInt::get (m_IntPtrTy, 0);
            m_sizes [ptr] = B.CreateZExtOrTrunc (size, m_IntPtrTy);
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
    BasicBlock* err_under_bb = BasicBlock::Create(ctx, "underflow_error_bb", &F);
    BasicBlock* err_over_bb = BasicBlock::Create(ctx, "overflow_error_bb", &F);

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
                                     ConstantInt::get (m_IntPtrTy, 0),
                                     "buffer_under");

    BasicBlock *OldBB1 = Cont0;
    BasicBlock *Cont1 = OldBB1->splitBasicBlock(B.GetInsertPoint ());
    OldBB1->getTerminator ()->eraseFromParent();
    BranchInst::Create (Cont1, err_under_bb, Cond_U, OldBB1);

    m_checks_added++;
    B.SetInsertPoint (Cont1->getFirstNonPHI ());    

    /// --- Overflow: add check 
    //      offset + addr_sz <= size or offset + len <= size 

    Value *range = nullptr;
    if (len) {
      range = abc::createAdd (B, m_dl, ptrOffset, len);
    } else {
      int addr_sz = abc::getAddrSize (m_dl, inst);
      if (addr_sz < 0) { // This should not happen ...
        errs () << "Error: cannot find size of the accessed address for " << inst << "\n";
        return true;
      }
      range = abc::createAdd (B, m_dl, ptrOffset, 
                              abc::createIntCst (m_IntPtrTy, addr_sz));
    }
    
    Value* Cond_O = B.CreateICmpSLE (range, ptrSize, "buffer_over");

    BasicBlock *OldBB2 = Cont1;
    BasicBlock *Cont2 = OldBB2->splitBasicBlock(B.GetInsertPoint ());
    OldBB2->getTerminator ()->eraseFromParent();
    BranchInst::Create (Cont2, err_over_bb, Cond_O, OldBB2);

    m_checks_added++;
    return true;
  }

  bool ABC1::runOnModule (llvm::Module &M)
  {
    if (M.begin () == M.end ()) return false;
      
    // Gather some statistics about DSA nodes
    DSACount* m_dsa_count = &getAnalysis<DSACount> ();    

    LLVMContext &ctx = M.getContext ();
    m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
    m_tli = &getAnalysis<TargetLibraryInfo>();

    m_IntPtrTy = m_dl->getIntPtrType (ctx, 0);
    errs () << "intPtrTy is " << *m_IntPtrTy << "\n";

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
    m_ret_offset = abc::createGlobalInt (m_dl, M, 0, "ret.offset");
    m_ret_size = abc::createGlobalInt (m_dl, M, 0, "ret.size");
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
            
          if (abc::ShouldBeTrackedPtr (ptr, F, m_dsa_count))
            WorkList.push_back (I);
          else
            untracked_dsa_checks++; 
          
        } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
          Value* ptr = SI->getPointerOperand ();
          if (ptr == m_ret_offset || ptr == m_ret_size) continue;

          if (abc::ShouldBeTrackedPtr (ptr, F, m_dsa_count))
            WorkList.push_back (I);
          else
            untracked_dsa_checks++; 
          
        } else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
          if (abc::ShouldBeTrackedPtr (MTI->getDest (), F, m_dsa_count) || 
              abc::ShouldBeTrackedPtr (MTI->getSource (), F, m_dsa_count))
            WorkList.push_back (I);
          else
            untracked_dsa_checks+=2;
        } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
          Value* ptr = MSI->getDest ();
          if (abc::ShouldBeTrackedPtr (ptr, F, m_dsa_count))
            WorkList.push_back (I);            
          else
            untracked_dsa_checks++; 
          
        } else if (isa<CallInst> (I) || isa<ReturnInst> (I)) {
          WorkList.push_back(I);
        }
      }
    }

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
        if (!abc::IsTrivialCheck (m_dl, m_tli, Ptr))  {
          instrumentCheck (*F, B, *inst, *Ptr, nullptr);           
        } else 
          m_trivial_checks++;
      }
      else if (StoreInst *store = dyn_cast<StoreInst> (inst)) {
        Value * Ptr = store->getOperand (1);
        if (Ptr == m_ret_size || Ptr == m_ret_offset) continue;

        m_mem_accesses++;
        if (!abc::IsTrivialCheck (m_dl, m_tli, Ptr)) {
          instrumentCheck (*F, B, *inst, *Ptr, nullptr);           
        } else 
          m_trivial_checks++;
      }
    }
    
    errs () << " ========== ABC  ==========\n"
            << "-- " << m_mem_accesses - m_trivial_checks   
            << " Total number of non-trivial memory reads/writes\n" 
            << "-- " << m_trivial_checks
            << " Total number of trivially safe memory reads/writes (not instrumented)\n"
            << "-- " << m_mem_accesses - m_trivial_checks - m_checks_unable  
            << " Total number of memory reads/writes instrumented\n"
            << "-- " << m_checks_unable
            << " Total number of memory reads/writes NOT instrumented\n"
            << "-- " << m_checks_added    
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

    void ABC2::ABCInst::Assume (Value* cond, Function* F) {
      CallInst* CI = m_B.CreateCall (m_assumeFn, cond);
      abc::update_cg (m_cg, F, CI);
    }

    CallInst* ABC2::ABCInst::NonDet (Function* F) {
      CallInst *CI = m_B.CreateCall (m_nondetFn, "nd");
      abc::update_cg (m_cg, F, CI);
      return CI;
    }
    
    CallInst* ABC2::ABCInst::NonDetPtr (Function* F) {
      CallInst* CI = m_B.CreateCall (m_nondetPtrFn, "nd_ptr");
      abc::update_cg (m_cg, F, CI);
      return CI;
    }

    //! Instrument pointer arithmetic
    //  lhs = rhs + n;
    void ABC2::ABCInst::doPtrArith (Value* lhs, Value* rhs, 
                                    GetElementPtrInst * gep, 
                                    Instruction* insertPt) {
      /* 
          if (nd () && tracked_ptr && rhs == tracked_ptr) {
             tracked_ptr = nd (); 
             assume (tracked_ptr == lhs);
             tracked_offset += n;
          }
      */

      LLVMContext& ctx = m_B.getContext ();
      BasicBlock* bb = insertPt->getParent ();
      Function* F = bb->getParent ();
      BasicBlock* cont = bb->splitBasicBlock(insertPt);

      /// if (nd () && tracked_ptr && rhs == tracked_ptr)
      m_B.SetInsertPoint (bb->getTerminator ());
      
      CallInst *nd = NonDet (insertPt->getParent()->getParent());
      Value *vtracked_ptr = abc::createLoad(m_B, m_tracked_ptr, m_dl);
      Value* condA = m_B.CreateICmpSGE (nd, abc::createIntCst (m_IntPtrTy, 0));
      Value* condB = m_B.CreateICmpSGT(vtracked_ptr,
                                       abc::createNullCst (ctx));
      Value* condC = m_B.CreateICmpEQ (m_B.CreateBitOrPointerCast (rhs, abc::geti8PtrTy (ctx)),
                                       vtracked_ptr);
      Value* cond = m_B.CreateAnd (condA, m_B.CreateAnd (condB, condC));
      bb->getTerminator ()->eraseFromParent ();      
      BasicBlock* bb1 = BasicBlock::Create(ctx, "update_ptr_" + lhs->getName ()  + "_bb", F);
      BranchInst::Create (bb1, cont, cond, bb);      

      m_B.SetInsertPoint (bb1);
      /// tracked_ptr = lhs;
      //abc::createStore (m_B, m_B.CreateBitOrPointerCast (lhs, abc::geti8PtrTy (ctx)),
      //                          m_tracked_ptr, m_dl);
      //// This code is equivalent to "tracked_ptr = lhs" but
      //// it will not force tracked_ptr and lhs to be in the
      //// same alias class since alias analyses ignore equalities:
      ///      tracked_ptr = nd ();
      ///      assume (tracked_ptr == lhs)
      CallInst* nd_ptr = NonDetPtr (insertPt->getParent()->getParent());
      abc::createStore (m_B, nd_ptr, m_tracked_ptr, m_dl);      
      Assume (m_B.CreateICmpEQ(nd_ptr, 
                               m_B.CreateBitOrPointerCast (lhs, abc::geti8PtrTy (ctx))),
              insertPt->getParent()->getParent());

      /// tracked_offset += n;
      Value* gep_offset = abc::computeGepOffset (m_dl, m_B, gep);    
      abc::createStore (m_B, 
                        abc::createAdd(m_B, m_dl,
                                       gep_offset, 
                                       abc::createLoad(m_B, m_tracked_offset, m_dl)),
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
      m_B.SetInsertPoint (main->getEntryBlock ().getFirstInsertionPt ());
      LLVMContext& ctx = m_B.getContext ();      

      // p1 = nd ();
      // assume (p1 > 0);
      // m_tracked_base  = p1
      m_tracked_base = abc::createGlobalPtr (M, "tracked_base");
      CallInst* p1 = NonDetPtr (main);
      Assume (m_B.CreateICmpSGT(p1, 
                                m_B.CreateBitOrPointerCast (abc::createNullCst (ctx), 
                                                            p1->getType ())), main);
      abc::createStore (m_B, p1, m_tracked_base, m_dl);

      // x = nd ();
      // assume (x > 0);
      // m_tracked_size = x;
      m_tracked_size = abc::createGlobalInt (m_dl, M, 0, "tracked_size");      
      CallInst *x = NonDet (main);
      Assume (m_B.CreateICmpSGT(x, abc::createIntCst (m_IntPtrTy, 0)), main);
      abc::createStore (m_B, x, m_tracked_size, m_dl);

      // m_tracked_ptr = 0
      m_tracked_ptr  = abc::createGlobalPtr ( M, "tracked_ptr");
      abc::createStore (m_B, abc::createNullCst (ctx), m_tracked_ptr, m_dl);

      // m_tracked_offset = 0;
      m_tracked_offset = abc::createGlobalInt (m_dl, M, 0, "tracked_offset");

      Instruction * insertPt = m_B.GetInsertPoint ();
      /// Allocation of global variables
      for (auto &GV: M.globals ()) {

        if (abc::IsTrivialCheck (m_dl, m_tli, &GV))
          continue;

        // skip global variables that we just introduced
        // IsTrivialCheck should have returned true before reaching
        // this point.
        if (&GV == m_tracked_base || &GV == m_tracked_ptr ||
            &GV == m_tracked_offset || &GV == m_tracked_size)
          continue;

        if (!abc::ShouldBeTrackedPtr (&GV, *main, m_dsa_count))
          continue;

        uint64_t size;
        if (abc::getObjectSize(&GV, size, m_dl, m_tli, true)) {
          doAllocaSite (&GV,
                        abc::createIntCst (m_IntPtrTy, size), 
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
    void ABC2::ABCInst::doAllocaSite (Value* Ptr, Value* Size /* bytes*/, 
                                      Instruction* insertPt) {
      /*
           if (!tracked_ptr && p == tracked_base)
              tracked_ptr = nd ();
              assume (tracked_ptr == tracked_base);
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
      Value* vtracked_size = abc::createLoad(m_B, m_tracked_size, m_dl);
      Value* vtracked_base = abc::createLoad(m_B, m_tracked_base, m_dl);
      Value* vtracked_ptr = abc::createLoad(m_B, m_tracked_ptr, m_dl);
      Value* PtrX = m_B.CreateBitOrPointerCast (Ptr, abc::geti8PtrTy (ctx));
      Value* cond = m_B.CreateAnd (m_B.CreateIsNull(vtracked_ptr),
                                   m_B.CreateICmpEQ (PtrX, vtracked_base));

      bb->getTerminator ()->eraseFromParent ();      
      BranchInst::Create (alloca_then_bb, alloca_else_bb, cond, bb);      

      m_B.SetInsertPoint (alloca_then_bb);
      //// tracked_ptr = tracked_base
      // abc::createStore (m_B, vtracked_base, m_tracked_ptr, m_dl);
      
      //// This code is equivalent to "tracked_ptr = tracked_base" but
      //// it will not force tracked_ptr and tracked_base to be in the
      //// same alias class since alias analyses ignore equalities:
      ///      tracked_ptr = nd ();
      ///      assume (tracked_ptr == tracked_base)
      CallInst* nd_ptr = NonDetPtr (insertPt->getParent()->getParent());
      abc::createStore (m_B, nd_ptr, m_tracked_ptr, m_dl);      
      Assume (m_B.CreateICmpEQ(nd_ptr, vtracked_base),
              insertPt->getParent()->getParent());
      
      /// assume (tracked_size == n);
      Assume (m_B.CreateICmpEQ(vtracked_size,
                               m_B.CreateZExtOrTrunc (Size, 
                                                      abc::createIntTy (m_dl, ctx))),
              insertPt->getParent()->getParent());

      /// tracked_offset = 0
      abc::createStore (m_B, abc::createIntCst (m_IntPtrTy, 0), 
                        m_tracked_offset, m_dl);

      BranchInst::Create (cont, alloca_then_bb);

      // assume (tracked_base + tracked_size < p); 
      m_B.SetInsertPoint (alloca_else_bb);
      Assume (m_B.CreateICmpSLT(m_B.CreateGEP(vtracked_base, vtracked_size), PtrX),
              insertPt->getParent()->getParent());
                          
      BranchInst::Create (cont, alloca_else_bb);
      
    }


     // Add in cur the instruction "br cond, then, error" where error is a
     // new block that contains a call to the error function.
     BasicBlock* ABC2::ABCInst::Assert (Value* cond, BasicBlock* then, BasicBlock* cur, 
                                        Instruction* instToBeChecked, 
                                        const Twine &errorBBName){
                  
       BasicBlock* err_bb = 
           BasicBlock::Create(m_B.getContext (), errorBBName, cur->getParent());

       m_B.SetInsertPoint (err_bb);
       CallInst* ci = m_B.CreateCall (m_errorFn);
       abc::update_cg (m_cg, cur->getParent (), ci);
       ci->setDebugLoc (instToBeChecked->getDebugLoc ());
       m_B.CreateUnreachable ();

       BranchInst::Create (then, err_bb, cond, cur);            

       return err_bb;
     }

     void ABC2::ABCInst::doGepOffsetCheck (GetElementPtrInst* gep, uint64_t size, 
                                           Instruction* insertPt) {
      /*
         Let gep be an instruction gep (b,o) and s the size of the
         object pointed by b

         for overflow:
           assert (o + addr_sz <= s);
         for underflow:
           if (b == tracked_base) {
              assert (o >= 0);
           }
           else if (b == tracked_ptr) {
              assert (tracked_offset + o >= 0);
           }
      */
      int addr_sz = abc::getAddrSize (m_dl, *insertPt);
      if (addr_sz < 0) { // this should not happen
        errs () << "Error: cannot find size of the accessed address for " 
                << *insertPt << "\n";
        return;
      }

      LLVMContext& ctx = m_B.getContext ();
      BasicBlock* bb = insertPt->getParent ();
      Function* F = bb->getParent ();
      BasicBlock *cont = bb->splitBasicBlock(insertPt);

      BasicBlock* bb1 = BasicBlock::Create(ctx, "over_check_bb", F);
      BasicBlock* bb2 = BasicBlock::Create(ctx, "under_check_bb", F);

      bb->getTerminator ()->eraseFromParent ();      
      BranchInst::Create (bb1, bb);      

      // assert (offset + addr_sz <= size);     
      m_B.SetInsertPoint (bb1);                                  
      Value* vsize = abc::createIntCst (m_IntPtrTy, size);
      Value* voffset = abc::computeGepOffset (m_dl, m_B, gep);
      Value* voffset_sz = abc::createAdd (m_B, m_dl, 
                                          voffset,
                                          abc::createIntCst (m_IntPtrTy, addr_sz));
      Assert (m_B.CreateICmpSLE (voffset_sz, vsize),
              bb2, bb1, insertPt, "overflow_error_bb");

      if (DisableUnderflow)  {
        BranchInst::Create (cont, bb2);
      } else {
        // underflow
        BasicBlock* bb2_then = BasicBlock::Create(ctx, "under_check_bb", F);
        BasicBlock* bb2_else = BasicBlock::Create(ctx, "under_check_bb", F);
        BasicBlock* bb3 = BasicBlock::Create(ctx, "under_check_bb", F);
        m_B.SetInsertPoint (bb2); 
        Value* base = gep->getPointerOperand ();
        Value* vtracked_base = abc::createLoad(m_B, m_tracked_base, m_dl);      
        Value* vbase = m_B.CreateBitOrPointerCast (base, abc::geti8PtrTy (ctx));
        BranchInst::Create (bb2_then, bb2_else, 
                            m_B.CreateICmpEQ (vtracked_base, vbase), bb2);            
        
        BasicBlock* abc_under_bb1 = BasicBlock::Create(ctx, "under_check_bb", F);
        BasicBlock* abc_under_bb2 = BasicBlock::Create(ctx, "under_check_bb", F);
        BranchInst::Create (abc_under_bb1, bb2_then);      
        // assert (offset >= 0);
        m_B.SetInsertPoint (abc_under_bb1);
        Assert (m_B.CreateICmpSGE (voffset, abc::createIntCst (m_IntPtrTy, 0)), 
                cont, abc_under_bb1, insertPt, "underflow_error_bb");
        
        m_B.SetInsertPoint (bb2_else); 
        Value* vtracked_ptr = abc::createLoad(m_B, m_tracked_ptr, m_dl);      
        BranchInst::Create (bb3, cont, 
                            m_B.CreateICmpEQ (vtracked_ptr, vbase), bb2_else);            
        
        m_B.SetInsertPoint (bb3); 
        Value* vtracked_offset = abc::createLoad(m_B, m_tracked_offset, m_dl);      
        BranchInst::Create (abc_under_bb2, bb3);      
        // assert (tracked_offset + offset >= 0);
        m_B.SetInsertPoint (abc_under_bb2);
        Assert (m_B.CreateICmpSGE (abc::createAdd (m_B, m_dl, voffset, vtracked_offset), 
                                   abc::createIntCst (m_IntPtrTy, 0)), 
                cont, abc_under_bb2, insertPt, "underflow_error_bb");

      }
     }
      
     void ABC2::ABCInst::doGepPtrCheck (GetElementPtrInst* gep, Instruction* insertPt) {

      int addr_sz = abc::getAddrSize (m_dl, *insertPt);
      if (addr_sz < 0) { // this should not happen
        errs () << "Error: cannot find size of the accessed address for " 
                << *insertPt << "\n";
        return;
      }

      LLVMContext& ctx = m_B.getContext ();
      BasicBlock* bb = insertPt->getParent ();
      Function* F = bb->getParent ();
      BasicBlock *cont = bb->splitBasicBlock(insertPt);
      m_B.SetInsertPoint (bb->getTerminator ());

      BasicBlock* bb1 = BasicBlock::Create(ctx, "check_gep_base_if", F);
      BasicBlock* bb1_then = BasicBlock::Create(ctx, "check_gep_base_base", F);
      BasicBlock* bb1_else = BasicBlock::Create(ctx, "check_gep_base_else", F);
      BasicBlock* bb2 = BasicBlock::Create(ctx, "check_gep_base_ptr", F);
      bb->getTerminator ()->eraseFromParent ();      
      BranchInst::Create (bb1, bb);      
      Value* base = gep->getPointerOperand ();

      /*
        bb1:
           if (base == tracked_base) goto bb1_then else goto bb1_else
        bb1_then:
           assert (offset >= 0);
           assert (offset + addr_sz <= tracked_size);
           goto cont;
        bb1_else:
           if (base == tracked_ptr) goto bb2 else goto cont
        bb2:
           assert (tracked_offset + offset >= 0);
           assert (tracked_offset + offset + addr_sz <= tracked_size);
           goto cont;
        cont:
           load or store
       */

      m_B.SetInsertPoint (bb1); 
      Value* vtracked_base = abc::createLoad(m_B, m_tracked_base, m_dl);      
#ifdef SIZE_OPT
      // use llvm machinery to figure out the size
      SizeOffsetEvalType Data = m_eval.compute (base);
      Value* vtracked_size = Data.first;
      if (vtracked_size)
        vtracked_size =  m_B.CreateZExtOrTrunc (vtracked_size, 
                                                abc::createIntTy (m_dl, ctx));
      else
        vtracked_size = abc::createLoad(m_B, m_tracked_size, m_dl);      
#else
      Value* vtracked_size = abc::createLoad(m_B, m_tracked_size, m_dl);      
#endif 
      Value* vbase = m_B.CreateBitOrPointerCast (base, abc::geti8PtrTy (ctx));
      Value* voffset = abc::computeGepOffset (m_dl, m_B, gep);
      BranchInst::Create (bb1_then, bb1_else, 
                          m_B.CreateICmpEQ (vtracked_base, vbase), bb1);            

      BasicBlock* abc_under_bb1 = BasicBlock::Create(ctx, "under_check_bb", F);
      BasicBlock* abc_over_bb1 = BasicBlock::Create(ctx, "over_check_bb", F);
      BranchInst::Create (abc_under_bb1, bb1_then);      

      // assert (offset >= 0);

      if (DisableUnderflow)  {
        BranchInst::Create (abc_over_bb1, abc_under_bb1);
      } else {
        m_B.SetInsertPoint (abc_under_bb1);
        Assert (m_B.CreateICmpSGE (voffset, abc::createIntCst (m_IntPtrTy, 0)), 
                abc_over_bb1, abc_under_bb1, insertPt, "underflow_error_bb");
      }

      // assert (offset + addr_sz <= tracked_size);
      m_B.SetInsertPoint (abc_over_bb1);
      Value* over_cond1 = m_B.CreateICmpSLE (
          abc::createAdd (m_B, m_dl, 
                          voffset, 
                          abc::createIntCst (m_IntPtrTy, addr_sz)),  
          vtracked_size);
          
      Assert (over_cond1, cont, abc_over_bb1, insertPt, "overflow_error_bb");

      m_B.SetInsertPoint (bb1_else); 
      Value* vtracked_ptr = abc::createLoad(m_B, m_tracked_ptr, m_dl);      
      BranchInst::Create (bb2, cont, 
                          m_B.CreateICmpEQ (vtracked_ptr, vbase), bb1_else);            

      m_B.SetInsertPoint (bb2); 
      Value* vtracked_offset = abc::createLoad(m_B, m_tracked_offset, m_dl);      
      BasicBlock* abc_under_bb2 = BasicBlock::Create(ctx, "under_check_bb", F);
      BasicBlock* abc_over_bb2 = BasicBlock::Create(ctx, "over_check_bb", F);
      BranchInst::Create (abc_under_bb2, bb2); 
     
      // assert (tracked_offset + offset >= 0);
      m_B.SetInsertPoint (abc_under_bb2);
      voffset = abc::createAdd (m_B, m_dl, voffset, vtracked_offset);

      if (DisableUnderflow)  {
        BranchInst::Create(abc_over_bb2, abc_under_bb2);
      } else {
        Assert (m_B.CreateICmpSGE (voffset, 
                                   abc::createIntCst (m_IntPtrTy, 0)), 
                abc_over_bb2, abc_under_bb2, insertPt, "underflow_error_bb");
      }

      // assert (tracked_offset + offset + addr_sz <= tracked_size);
      m_B.SetInsertPoint (abc_over_bb2);
      voffset = abc::createAdd (m_B, m_dl, 
                                voffset, 
                                abc::createIntCst (m_IntPtrTy, addr_sz));
      Assert (m_B.CreateICmpSLE (voffset, vtracked_size),
              cont, abc_over_bb2, insertPt, "overflow_error_bb");
     }


    //! Instrument any read or write to a pointer and also memory
    //! intrinsics. If N != null then the check corresponds to a
    //! memory intrinsic
    void ABC2::ABCInst::doPtrCheck (Value* Ptr, Value* N /*bytes*/, Instruction* insertPt) {
      /*  
          if N is null then the check corresponds to a store or
          load. In that case, the added code is:

          if (tracked_ptr && p == tracked_ptr) {
              assert (tracked_offset + addr_size <= tracked_size);
              assert (tracked_offset >= 0);
          }
           
          otherwise, the check corresponds to a memory intrinsic
          (memcpy, memmove, or memset). The code differs slightly:

          if (tracked_ptr && p == tracked_ptr) {
              assert (tracked_offset + n <= tracked_size);
              assert (tracked_offset >= 0);
          }
      */

      LLVMContext& ctx = m_B.getContext ();
      BasicBlock* bb = insertPt->getParent ();
      Function* F = bb->getParent ();

      BasicBlock* abc_under_bb = BasicBlock::Create(ctx, "under_check_bb", F);
      BasicBlock* abc_over_bb = BasicBlock::Create(ctx, "over_check_bb", F);


      BasicBlock *cont = bb->splitBasicBlock(insertPt);
      m_B.SetInsertPoint (bb->getTerminator ());

      // if (m_tracked_ptr && ptr == m_tracked_ptr)
      Value* vtracked_ptr = abc::createLoad(m_B, m_tracked_ptr, m_dl);
      Value* condA = m_B.CreateICmpSGT(vtracked_ptr, 
                                       abc::createNullCst (ctx));
      Value* condB = m_B.CreateICmpEQ (vtracked_ptr,
                                       m_B.CreateBitOrPointerCast (Ptr, abc::geti8PtrTy (ctx)));
      Value* cond = m_B.CreateAnd (condA, condB);
      bb->getTerminator ()->eraseFromParent ();      
      BranchInst::Create (abc_under_bb, cont, cond, bb);      
      m_B.SetInsertPoint (abc_under_bb);

      Value* offset = abc::createLoad(m_B, m_tracked_offset, m_dl);
#ifdef SIZE_OPT
      // use llvm machinery to figure out the size
      SizeOffsetEvalType Data = m_eval.compute (Ptr);
      Value* size = Data.first;
      if (size)
        size =  m_B.CreateZExtOrTrunc (size, abc::createIntTy (m_dl, ctx));
      else
        size = abc::createLoad(m_B, m_tracked_size, m_dl);      
#else
      Value* size = abc::createLoad(m_B, m_tracked_size, m_dl); 
#endif 

      /////
      // underflow check
      /////

      if (DisableUnderflow)  {
        BranchInst::Create (abc_over_bb, abc_under_bb);
      } else {
        // abc_under_bb:
        //    if (m_tracked_offset >= 0) goto abc_over_bb else goto err_under_bb
        
        Assert (m_B.CreateICmpSGE (offset, abc::createIntCst (m_IntPtrTy, 0)), 
                abc_over_bb, abc_under_bb, insertPt, "underflow_error_bb");
      }

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
      //    if (m_tracked_offset + addr_size <= m_tracked_size) 
      //        goto cont 
      //    else 
      //        goto err_over_bb
      if (N) {
        // both offset and N are in bytes
        offset = abc::createAdd (m_B, m_dl, offset, N);
      } else {
        int addr_sz = abc::getAddrSize (m_dl, *insertPt);
        if (addr_sz < 0) { // this should not happen
          errs () << "Error: cannot find size of the accessed address for " 
                  << *insertPt << "\n";
          return;
        }
        // both offset and addr_sz are in bytes
        offset = abc::createAdd (m_B, m_dl, 
                                 offset, 
                                 abc::createIntCst (m_IntPtrTy, addr_sz));
      }

      Assert (m_B.CreateICmpSLE (offset, size), cont, abc_over_bb, 
              insertPt, "overflow_error_bb");                
    }

    ABC2::ABCInst::ABCInst (Module& M, 
                            const DataLayout* dl, 
                            const TargetLibraryInfo* tli,
                            IRBuilder<> B, CallGraph* cg,
                            DSACount* dsa_count,
                            Function* errorFn, Function* nondetFn,
                            Function* nondetPtrFn, Function* assumeFn): 
        m_dl (dl), m_tli (tli), 
        m_B (B), m_cg (cg), m_dsa_count (dsa_count),
        m_eval (dl, tli, B.getContext (), true),             
        m_IntPtrTy (dl->getIntPtrType (M.getContext (), 0)),
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
      if (!abc::IsTrivialCheck (m_dl, m_tli, lhs)) {
        Value *rhs = I->getPointerOperand ();            
        doPtrArith (lhs, rhs, I, abc::getNextInst (I));
      }
    }

    void ABC2::ABCInst::visit (LoadInst *I) {
      Value* ptr = I->getPointerOperand ();
      
      // skip our own global variables. IsTrivialCheck should skip any
      // access to a the tracked variables but we keep it to avoid
      // incrementing m_mem_accesses counter.
      if (ptr == m_tracked_base || ptr == m_tracked_ptr ||
          ptr == m_tracked_offset || ptr == m_tracked_size)
        return;

      m_mem_accesses++;
      if (!abc::IsTrivialCheck (m_dl, m_tli, ptr)) {
        if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst> (ptr)) {
          uint64_t size; //bytes
          if (abc::getObjectSize(gep->getPointerOperand (), size, m_dl, m_tli, true))
            doGepOffsetCheck (gep, size, I);
          else 
            doGepPtrCheck (gep, I);
        }
        else 
          doPtrCheck (ptr, nullptr, I);
        // add one for overflow and another one for underflow
        m_checks_added+=(DisableUnderflow ? 1 : 2);
      }
      else
        m_trivial_checks++;
    }
    
    void ABC2::ABCInst::visit (StoreInst *I) {
      Value* ptr = I->getPointerOperand ();

      // skip our own global variables. IsTrivialCheck should skip
      // this access but we keep it to avoid incrementing
      // m_mem_accesses counter.
      if (ptr == m_tracked_base || ptr == m_tracked_ptr ||
          ptr == m_tracked_offset || ptr == m_tracked_size)
        return;

      m_mem_accesses++;
      if (!abc::IsTrivialCheck (m_dl, m_tli, ptr)) {
        if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst> (ptr)) {
          uint64_t size; // bytes
          if (abc::getObjectSize(gep->getPointerOperand (), size, m_dl, m_tli, true))
            doGepOffsetCheck (gep, size, I);
          else
            doGepPtrCheck (gep, I);
        }
        else 
          doPtrCheck (ptr, nullptr, I);
        m_checks_added+=(DisableUnderflow ? 1 : 2);
      }
      else 
        m_trivial_checks++;
    }

    void ABC2::ABCInst::visit (MemTransferInst *MTI) {
      m_mem_accesses+=2;

      doPtrCheck (MTI->getDest (), MTI->getLength (), MTI);
      m_checks_added+=(DisableUnderflow ? 1 : 2);

      doPtrCheck (MTI->getSource (), MTI->getLength (), MTI);
      m_checks_added+=(DisableUnderflow ? 1 : 2);
    }

    void ABC2::ABCInst::visit (MemSetInst *MSI) {
      m_mem_accesses++;

      doPtrCheck (MSI->getDest (), MSI->getLength (), MSI);
      m_checks_added++; 
      if (!DisableUnderflow) 
        m_checks_added++; 
    }

    void ABC2::ABCInst::visit (AllocaInst *I) {
      // note that the seahorn frontend can promote malloc-like instructions
      // to alloca's.

      SizeOffsetEvalType Data = m_eval.compute (I);
      if (Value* size = Data.first) 
        doAllocaSite (I, size, abc::getNextInst (I));
      else
        errs () << "Warning: missing allocation site: " << *I << "\n";

      // uint64_t size; //bytes
      // if (abc::getObjectSize(I, size, m_dl, m_tli, true)) {
      //   doAllocaSite (I, 
      //                 abc::createIntCst (m_IntPtrTy, size), 
      //                 abc::getNextInst (I)); 
      //   return;
      // } else {
      //   Value *nElems = I->getArraySize (); // number of elements
      //   Type* ty = I->getAllocatedType (); // size of the allocated type
      //   unsigned ty_size = abc::storageSize (m_dl, ty); // bytes
      //   Value* size = nullptr;
      //   if (ty_size == 1) 
      //     size = nElems;
      //   else {
      //     m_B.SetInsertPoint (I);
      //     size = abc::createMul (m_B, m_dl, nElems, ty_size, "alloca_size");
      //   }
      //   doAllocaSite (I, size, abc::getNextInst (I)); 
      //   return;
      // }
      // errs () << "Warning: missing alloca site: " << *I << "\n";
    }

    void ABC2::ABCInst::visit (CallInst *I) {

      if (isAllocationFn (I, m_tli, true)) {

        // new, malloc, calloc, realloc, and strdup.
        SizeOffsetEvalType Data = m_eval.compute (I);
        if (Value* size = Data.first) 
          doAllocaSite (I, size, abc::getNextInst (I));
        else
          errs () << "Warning: missing allocation site " << *I << "\n";
        
        // if (isMallocLikeFn(I, m_tli, true) || isOperatorNewLikeFn(I, m_tli, true)){
        //   if (I->getNumArgOperands () == 1) {
        //     Value *size = I->getArgOperand(0); // bytes
        //     doAllocaSite (I, size, abc::getNextInst (I)); 
        //     return;
        //   }
        // }
        // errs () << "Warning: missing " << *I << "\n";
        
        return;
      }

      #ifdef DEREFERENCEABLE_OPT
      Function* F = I->getParent()->getParent();

      if (!abc::ShouldBeTrackedPtr (I->getArgOperand (0), *F, m_dsa_count))
        return;

      if (!I->getArgOperand (0)->getType ()->isPointerTy ())
        return;
        
      uint64_t n = I->getDereferenceableBytes (0);
      if (n == 0)
        return;
            
      // if all uses are trivial then skip
      if (std::all_of (I->getArgOperand (0)->uses().begin (),
                       I->getArgOperand (0)->uses().end (), 
                       [&](Use& U) {
                          return abc::IsTrivialCheck (m_dl, m_tli, U.getUser());})) 
        return;
       
      m_B.SetInsertPoint (abc::getNextInst (I));
      
      Value* vtracked_base = abc::createLoad(m_B, m_tracked_base, m_dl);
      Value* vtracked_ptr = abc::createLoad(m_B, m_tracked_ptr, m_dl);
      Value* vtracked_size= abc::createLoad(m_B, m_tracked_size, m_dl);
      Value* vtracked_offset= abc::createLoad(m_B, m_tracked_offset, m_dl);

      Value* lhs = m_B.CreateBitOrPointerCast (I->getArgOperand (0), 
                                               abc::geti8PtrTy (m_B.getContext()));
      Value* N = abc::createIntCst (abc::createIntTy (m_dl, m_B.getContext ()), n);

      // assume (lhs == tracked_base -> tracked_size >= n);
      Assume (m_B.CreateOr (m_B.CreateICmpNE (lhs, vtracked_base),
                            m_B.CreateICmpSGE (vtracked_size, N)),  F);
      
      // assume (lhs == tracked_ptr -> tracked_size + tracked_offset >= n);
      Assume (m_B.CreateOr (m_B.CreateICmpNE (lhs, vtracked_ptr),
                            m_B.CreateICmpSGE (abc::createAdd (m_B, m_dl, 
                                                               vtracked_size, vtracked_offset),
                                               N), "deref_assumption"), F);
      #endif 
    }

    void ABC2::ABCInst::visit (iterator_range<Function::arg_iterator> Args) {
      #ifdef DEREFERENCEABLE_OPT
      // TODO: add this extra assumption only if there is an use of
      // Arg which is not trivial.

      if (Args.begin () == Args.end ()) return;
      
      Value *vtracked_base = nullptr;
      Value *vtracked_ptr = nullptr;
      Value *vtracked_size = nullptr;
      Value *vtracked_offset = nullptr;
      
      Function *F = (*(Args.begin())).getParent();
      m_B.SetInsertPoint (F->getEntryBlock ().getFirstInsertionPt ());
      for (Argument& A : Args) {

        if (!abc::ShouldBeTrackedPtr (&A, *F, m_dsa_count))
          continue;
        
        if (!A.getType ()->isPointerTy ())
          continue;
        
        uint64_t n = A.getDereferenceableBytes ();
        if (n == 0)
          continue;
        
        // if all uses are trivial we skip
        if (std::all_of (A.uses().begin (), A.uses().end (), 
                         [&](Use& U) {
                           return abc::IsTrivialCheck (m_dl, m_tli, U.getUser());})) 
          continue;

        if (!vtracked_base)
          vtracked_base = abc::createLoad(m_B, m_tracked_base, m_dl);
        if (!vtracked_ptr)
          vtracked_ptr = abc::createLoad(m_B, m_tracked_ptr, m_dl);
        if (!vtracked_size)
          vtracked_size= abc::createLoad(m_B, m_tracked_size, m_dl);
        if (!vtracked_offset)
          vtracked_offset= abc::createLoad(m_B, m_tracked_offset, m_dl);
        
        Value* vA = m_B.CreateBitOrPointerCast (&A, abc::geti8PtrTy (m_B.getContext()));
        Value* N = abc::createIntCst (abc::createIntTy (m_dl, m_B.getContext ()), n);
        
        // assume (arg == tracked_base -> tracked_size >= n);
        Assume (m_B.CreateOr (m_B.CreateICmpNE (vA, vtracked_base),
                              m_B.CreateICmpSGE (vtracked_size, N), "deref_assumption"),  F);
        
        // assume (arg == tracked_ptr -> tracked_size + tracked_offset >= n);
        Assume (m_B.CreateOr (m_B.CreateICmpNE (vA, vtracked_ptr),
                              m_B.CreateICmpSGE (abc::createAdd (m_B, m_dl, 
                                                                 vtracked_size, 
                                                                 vtracked_offset),
                                                 N), "deref_assumption"), F);
      }
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
      
      // Gather some statistics about DSA nodes
      DSACount* m_dsa_count = &getAnalysis<DSACount> ();    

      LLVMContext &ctx = M.getContext ();

      const TargetLibraryInfo * tli = &getAnalysis<TargetLibraryInfo>();
      const DataLayout * dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
      
      AttrBuilder AB;
      AB.addAttribute (Attribute::NoReturn);
      AttributeSet as = AttributeSet::get (ctx, AttributeSet::FunctionIndex, AB);
      Function* errorFn = dyn_cast<Function>
          (M.getOrInsertFunction ("verifier.error",
                                  as,
                                  Type::getVoidTy (ctx), NULL));
      
      AB.clear ();
      as = AttributeSet::get (ctx, AttributeSet::FunctionIndex, AB); 

      Type *intPtrTy = dl->getIntPtrType (ctx, 0);
      errs () << "intPtrTy is " << *intPtrTy << "\n";
      Type *i8PtrTy = Type::getInt8Ty (ctx)->getPointerTo ();
      
      Function* nondetFn = dyn_cast<Function>
          (M.getOrInsertFunction ("verifier.nondet",
                                  as,
                                  intPtrTy, 
                                  NULL));
      
      Function* nondetPtrFn = dyn_cast<Function>
          (M.getOrInsertFunction ("verifier.nondet_ptr",
                                  as,
                                  i8PtrTy, 
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
      std::vector<Instruction*> Worklist;
      for (Function &F : M) {
        if (F.isDeclaration ()) continue;
                
        for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i)  {
          Instruction *I = &*i;
          
          if (GetElementPtrInst* GEP  = dyn_cast<GetElementPtrInst> (I)) {
            Value *ptr = GEP->getPointerOperand ();            
            if (abc::ShouldBeTrackedPtr (ptr, F, m_dsa_count) && abc::canEscape (GEP))
              Worklist.push_back (I);
          } else if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
            Value* ptr = LI->getPointerOperand ();
            if (abc::ShouldBeTrackedPtr (ptr, F, m_dsa_count)) 
              Worklist.push_back (I);
            else 
              untracked_dsa_checks++;
          } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
            Value* ptr = SI->getPointerOperand ();
            if (abc::ShouldBeTrackedPtr (ptr, F, m_dsa_count)) 
             Worklist.push_back (I);
            else 
              untracked_dsa_checks++; 
          } else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
            if (abc::ShouldBeTrackedPtr (MTI->getDest (), F, m_dsa_count) || 
                abc::ShouldBeTrackedPtr (MTI->getSource (),F, m_dsa_count))
              Worklist.push_back (I);
            else 
              untracked_dsa_checks+=2; 
          } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
            Value* ptr = MSI->getDest ();
            if (abc::ShouldBeTrackedPtr (ptr, F, m_dsa_count)) 
              Worklist.push_back (I);
            else 
              untracked_dsa_checks++; 
          } else if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {
            Value* ptr = AI;
            if (abc::ShouldBeTrackedPtr (ptr, F, m_dsa_count)) 
              Worklist.push_back (I);
          } else if (CallInst* CI = dyn_cast<CallInst> (I)) {
            if (abc::ShouldBeTrackedPtr (I, F, m_dsa_count))
              Worklist.push_back (CI);
          }
        }
      } 
      
      ABCInst abc (M, dl, tli, B, cg, m_dsa_count, 
                   errorFn, nondetFn, nondetPtrFn, assumeFn);

      // instrument formal parameters of functions 
      for (Function &F : M) {
        if (F.isDeclaration ()) continue;
        abc.visit (F.args ());
      }

      // process the worklist
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
      errs () << "-- " << abc.m_mem_accesses - abc.m_trivial_checks
              << " Total number of non-trivial memory reads/writes\n"
              << "-- " << abc.m_trivial_checks
              << " Total number of trivially safe memory reads/writes (not instrumented)\n"
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


namespace seahorn {
    using namespace llvm;

    bool ABC3::runOnModule (llvm::Module &M)
    {
      if (M.begin () == M.end ()) return false;
      
      Function* main = M.getFunction ("main");
      if (!main) {
        errs () << "Main not found: no buffer overflow checks added\n";
        return false;
      }
      
      const TargetLibraryInfo * tli = &getAnalysis<TargetLibraryInfo>();
      const DataLayout* dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
      
      // Gather some statistics about DSA nodes
      DSACount* dsa_count = &getAnalysis<DSACount> ();    

      LLVMContext &ctx = M.getContext ();
      Type *voidTy = Type::getVoidTy (ctx);
      Type *intPtrTy = dl->getIntPtrType (ctx, 0);
      errs () << "intPtrTy is " << *intPtrTy << "\n";
      
      Type *i8PtrTy = Type::getInt8Ty (ctx)->getPointerTo ();
      
      
      AttrBuilder AB;
      AttributeSet as = AttributeSet::get (ctx, AttributeSet::FunctionIndex, AB); 

      Function* abc_init = dyn_cast<Function>
          (M.getOrInsertFunction ("sea_abc_init",
                                  as, voidTy, NULL));
      abc_init->addFnAttr(Attribute::AlwaysInline);

      Function* abc_alloc = dyn_cast<Function>
          (M.getOrInsertFunction ("sea_abc_alloc",
                                  as, voidTy, i8PtrTy, intPtrTy,
                                  NULL));
      abc_alloc->addFnAttr(Attribute::AlwaysInline);

      Function* abc_log_ptr = dyn_cast<Function>
          (M.getOrInsertFunction ("sea_abc_log_ptr",
                                  as, voidTy, i8PtrTy, intPtrTy,
                                  NULL));
      abc_log_ptr->addFnAttr(Attribute::AlwaysInline);
      
      Function* abc_assert_valid_ptr = dyn_cast<Function>
          (M.getOrInsertFunction ("sea_abc_assert_valid_ptr",
                                  as, voidTy, i8PtrTy, intPtrTy,
                                  NULL));
      abc_assert_valid_ptr->addFnAttr(Attribute::AlwaysInline);

      Function* abc_assert_valid_offset = dyn_cast<Function>
          (M.getOrInsertFunction ("sea_abc_assert_valid_offset",
                                  as, voidTy, intPtrTy, intPtrTy,
                                  NULL));
      abc_assert_valid_offset->addFnAttr(Attribute::AlwaysInline);

      std::vector<Function*> sea_funcs = 
          { abc_assert_valid_offset, abc_assert_valid_ptr, 
            abc_log_ptr, abc_alloc, abc_init };

      GlobalVariable *LLVMUsed = M.getGlobalVariable("llvm.used");
      std::vector<Constant*> MergedVars;
      if (LLVMUsed) {
        // Collect the existing members of llvm.used except sea
        // functions
        ConstantArray *Inits = cast<ConstantArray>(LLVMUsed->getInitializer());
        for (unsigned I = 0, E = Inits->getNumOperands(); I != E; ++I) {
          Value* V = Inits->getOperand(I)->stripPointerCasts();
          if (std::find (sea_funcs.begin (), sea_funcs.end (),
                         V) == sea_funcs.end ()) {
            MergedVars.push_back(Inits->getOperand(I));
          }
        }
        LLVMUsed->eraseFromParent();
      }

      // Recreate llvm.used.
      if (!MergedVars.empty ()) {
        ArrayType *ATy = ArrayType::get(abc::geti8PtrTy (ctx), MergedVars.size());
        LLVMUsed = new llvm::GlobalVariable(
            M, ATy, false, llvm::GlobalValue::AppendingLinkage,
            llvm::ConstantArray::get(ATy, MergedVars), "llvm.used");
        LLVMUsed->setSection("llvm.metadata");
      }

      IRBuilder<> B (ctx);
      
      CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
      CallGraph* cg = cgwp ? &cgwp->getCallGraph () : nullptr;
      if (cg) {
        cg->getOrInsertFunction (abc_init);
        cg->getOrInsertFunction (abc_alloc);
        cg->getOrInsertFunction (abc_log_ptr);
        cg->getOrInsertFunction (abc_assert_valid_ptr);
        cg->getOrInsertFunction (abc_assert_valid_offset);
      }
      
      unsigned untracked_dsa_checks = 0;
      unsigned checks_added = 0;
      unsigned trivial_checks = 0;
      unsigned mem_accesses = 0;
      DenseMap<GetElementPtrInst*, Value*> instrumented_gep;
      ObjectSizeOffsetEvaluator size_offset_eval (dl, tli, ctx, true);
      
      // do initialization
      B.SetInsertPoint (main->getEntryBlock ().getFirstInsertionPt ());
      abc::update_cg (cg, main, B.CreateCall (abc_init));

      // allocation of global variables
      for (auto &GV: M.globals ()) {

        if (abc::IsTrivialCheck (dl, tli, &GV))
          continue;

        // IsTrivialCheck should have skipped them but just in case.
        if (GV.getName ().startswith ("sea_"))
          continue;

        if (!abc::ShouldBeTrackedPtr (&GV, *main, dsa_count))
          continue;

        uint64_t size;
        if (abc::getObjectSize(&GV, size, dl, tli, true)) {
          abc::update_cg (cg, main,
               B.CreateCall2 (abc_alloc, 
                              B.CreateBitOrPointerCast (&GV,abc::geti8PtrTy (ctx)),
                              abc::createIntCst (intPtrTy, size)));
        }
        else {// this should not happen ...
          errs () << "Warning: cannot infer statically the size of global " 
                  << GV << "\n";
        }
      }
      
      for (Function &F : M) {
        if (F.isDeclaration ()) continue;

        // skip sea functions
        if (std::find (sea_funcs.begin (), 
                       sea_funcs.end (), &F) != sea_funcs.end ())  
          continue;
        
        for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i)  {
          Instruction *I = &*i;
          
          if (GetElementPtrInst* GEP  = dyn_cast<GetElementPtrInst> (I)) {
            Value *base = GEP->getPointerOperand ();            
            if (abc::ShouldBeTrackedPtr (base, F, dsa_count) && abc::canEscape (GEP)) 
            {
              B.SetInsertPoint (abc::getNextInst (I));
              Value* offset = abc::computeGepOffset (dl, B, GEP);                  
              instrumented_gep [GEP] = offset;
              abc::update_cg (cg, &F, 
                   B.CreateCall2 (abc_log_ptr, 
                                  B.CreateBitOrPointerCast (base,
                                                            abc::geti8PtrTy (ctx)),
                                  offset));
            }
          } else if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
            Value* ptr = LI->getPointerOperand ();
            // IsTrivialCheck should skip any access to a sea
            // global but we keep it to avoid incrementing
            // m_mem_accesses counter.
            if (ptr->getName ().startswith ("sea_"))
              continue;

            if (abc::ShouldBeTrackedPtr (ptr, F, dsa_count)) { 
              mem_accesses++;
              if (abc::IsTrivialCheck (dl, tli, ptr)) {
                trivial_checks++;
              } else {
                int addr_sz = abc::getAddrSize (dl, *I);
                if (addr_sz < 0) {
                  errs () << "Error: cannot find size of the accessed address for " 
                          << *I << "\n";
                  continue;
                }
 
                checks_added++;
                B.SetInsertPoint (LI);

                if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst> (ptr)) {
                  Value* offset = instrumented_gep [gep];
                  if (!offset) 
                    offset = abc::computeGepOffset (dl, B, gep);                  
                  offset = abc::createAdd (B, dl, 
                                           offset, 
                                           abc::createIntCst (intPtrTy, addr_sz));
                  Value* base = gep->getPointerOperand ();
                  uint64_t size; //bytes
                  if (abc::getObjectSize(base, size, dl, tli, true)) {
                    abc::update_cg (cg, &F, 
                         B.CreateCall2 (abc_assert_valid_offset, 
                                        offset, 
                                        abc::createIntCst (intPtrTy, size)));
                  }
                  else {
                    base = B.CreateBitOrPointerCast (base, abc::geti8PtrTy (ctx));
                    abc::update_cg (cg, &F, 
                         B.CreateCall2 (abc_assert_valid_ptr, base, offset));
                  }
                } else { // ptr is not a gep
                  Value* base = B.CreateBitOrPointerCast (ptr, abc::geti8PtrTy (ctx));
                  abc::update_cg (cg, &F, 
                       B.CreateCall2 (abc_assert_valid_ptr,
                                      base,
                                      abc::createIntCst (intPtrTy, addr_sz)));
                }
              }
            }
            else 
              untracked_dsa_checks++;
          } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
            Value* ptr = SI->getPointerOperand ();
            // IsTrivialCheck should skip any access to a sea
            // global but we keep it to avoid incrementing
            // m_mem_accesses counter.
            if (ptr->getName ().startswith ("sea_"))
              continue;

            if (abc::ShouldBeTrackedPtr (ptr, F, dsa_count))  {
              mem_accesses++;
              if (abc::IsTrivialCheck (dl, tli, ptr)) {
                trivial_checks++;
              } else {
                int addr_sz = abc::getAddrSize (dl, *I);
                if (addr_sz < 0) {
                  errs () << "Error: cannot find size of the accessed address for " 
                          << *I << "\n";
                  continue;
                }
                checks_added++;
                B.SetInsertPoint (SI);

                if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst> (ptr)) {
                  Value* offset = instrumented_gep [gep];
                  if (!offset) 
                    offset = abc::computeGepOffset (dl, B, gep);                  
                  offset = abc::createAdd (B, dl, 
                                           offset, 
                                           abc::createIntCst (intPtrTy, addr_sz));
                  Value* base = gep->getPointerOperand ();
                  uint64_t size; //bytes
                  if (abc::getObjectSize(base, size, dl, tli, true)) {
                    abc::update_cg (cg, &F, 
                         B.CreateCall2 (abc_assert_valid_offset, 
                                        offset, 
                                        abc::createIntCst (intPtrTy, size)));
                  }
                  else {
                    base = B.CreateBitOrPointerCast (base, abc::geti8PtrTy (ctx));
                    abc::update_cg (cg, &F, 
                         B.CreateCall2 (abc_assert_valid_ptr, base, offset));
                  }
                } else { // ptr is not a gep
                  Value* base = B.CreateBitOrPointerCast (ptr, abc::geti8PtrTy (ctx));
                  abc::update_cg (cg, &F, 
                       B.CreateCall2 (abc_assert_valid_ptr, 
                                      base,
                                      abc::createIntCst (intPtrTy, addr_sz)));
                }
              }
            }
            else 
              untracked_dsa_checks++; 
          } else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
            if (abc::ShouldBeTrackedPtr (MTI->getDest (), F, dsa_count) || 
                abc::ShouldBeTrackedPtr (MTI->getSource (),F, dsa_count)) {
              mem_accesses+=2;
              checks_added+=2; 
              Value *base1 = 
                  B.CreateBitOrPointerCast (MTI->getDest(), abc::geti8PtrTy(ctx));
              Value *base2 = 
                  B.CreateBitOrPointerCast (MTI->getSource(), abc::geti8PtrTy(ctx));
              Value *len = 
                  B.CreateZExtOrTrunc (MTI->getLength(), intPtrTy);
              abc::update_cg (cg, &F, 
                              B.CreateCall2 (abc_assert_valid_ptr, base1, len));
              abc::update_cg (cg, &F, 
                              B.CreateCall2 (abc_assert_valid_ptr, base2, len));
            }
            else 
              untracked_dsa_checks+=2; 
          } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
            Value* ptr = MSI->getDest ();
            if (abc::ShouldBeTrackedPtr (ptr, F, dsa_count))  {
              mem_accesses++;
              checks_added++; 
              Value *base = 
                  B.CreateBitOrPointerCast (MSI->getDest(), abc::geti8PtrTy(ctx));
              Value *len = 
                  B.CreateZExtOrTrunc (MSI->getLength(), intPtrTy);
              abc::update_cg (cg, &F, 
                              B.CreateCall2 (abc_assert_valid_ptr, base, len));
            }
            else 
              untracked_dsa_checks++; 
          } else if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {
            Value* ptr = AI;
            if (abc::ShouldBeTrackedPtr (ptr, F, dsa_count))  {
              B.SetInsertPoint (abc::getNextInst (I));

              SizeOffsetEvalType Data = size_offset_eval.compute (I);
              if (Value* size = Data.first) {
                abc::update_cg (cg, &F, 
                                B.CreateCall2 (abc_alloc, 
                                     B.CreateBitOrPointerCast (ptr, abc::geti8PtrTy (ctx)),
                                     B.CreateZExtOrTrunc (size, intPtrTy)));
              } else {
                errs () << "Warning: missing allocation site: " << *I << "\n";
              }
              
              // Value* vsize = nullptr;
              // uint64_t size; //bytes
              // if (abc::getObjectSize(I, size, dl, tli, true)) {
              //   vsize = abc::createIntCst (intPtrTy, size);
              // } else {
              //   Value *nElems = AI->getArraySize (); // number of elements
              //   Type* ty = AI->getAllocatedType (); // size of the allocated type
              //   unsigned ty_size = abc::storageSize (dl, ty); // bytes
              //   if (ty_size == 1) 
              //     vsize = nElems;
              //   else {
              //     vsize = abc::createMul (B, dl, nElems, ty_size, "alloca_size");
              //   }
              // }
              // if (!vsize) {
              //   errs () << "Warning: missing " << *I << "\n";
              //   continue;
              // }
              // abc::update_cg (cg, &F, 
              //      B.CreateCall2 (abc_alloc, 
              //                     B.CreateBitOrPointerCast (ptr, abc::geti8PtrTy (ctx)),
              //                     B.CreateZExtOrTrunc (vsize, intPtrTy)));
            }
          } 
          else if (isMallocLikeFn(I, tli, true) || isOperatorNewLikeFn(I, tli, true)){
            if (abc::ShouldBeTrackedPtr (I, F, dsa_count)) {

              SizeOffsetEvalType Data = size_offset_eval.compute (I);
              if (Value* size = Data.first) {
                B.SetInsertPoint (abc::getNextInst (I));
                abc::update_cg (cg, &F,
                                B.CreateCall2 (abc_alloc, 
                                   B.CreateBitOrPointerCast (I, abc::geti8PtrTy (ctx)),
                                   B.CreateZExtOrTrunc (size,intPtrTy)));
              } else {
                errs () << "Warning: missing allocation site " << *I << "\n";
              }

              // if (CallInst* CI = dyn_cast<CallInst> (I)) {
              //   B.SetInsertPoint (abc::getNextInst (I));
              //   Value* ptr = CI;
              //   Value *size = CI->getArgOperand(0); // bytes
              //   abc::update_cg (cg, &F,
              //                   B.CreateCall2 (abc_alloc, 
              //                      B.CreateBitOrPointerCast (ptr, abc::geti8PtrTy (ctx)),
              //                                  B.CreateZExtOrTrunc (size,intPtrTy)));
              // }
            }
          }
        }
      } 
      
      errs () << " ========== ABC  ==========\n";
      errs () << "-- " << mem_accesses - trivial_checks
              << " Total number of non-trivial memory reads/writes\n"
              << "-- " << trivial_checks
              << " Total number of trivially safe memory reads/writes (not instrumented)\n"
              << "-- " << checks_added 
              << " Total number of added buffer overflow/underflow checks\n"; 
      
      if (TrackedDSNode != 0) {
        errs () << "-- " << untracked_dsa_checks 
                << " Total number of skipped checks because untracked DSA node\n";
      }
      
      return true;
    }

    void ABC3::getAnalysisUsage (llvm::AnalysisUsage &AU) const
    {
     AU.setPreservesAll ();
     AU.addRequired<seahorn::DSACount>();
     AU.addRequired<llvm::DataLayoutPass>();
     AU.addRequired<llvm::TargetLibraryInfo>();
     AU.addRequired<llvm::UnifyFunctionExitNodes> ();
     AU.addRequired<llvm::CallGraphWrapperPass>();
    } 

    char ABC3::ID = 0;

    static llvm::RegisterPass<ABC3> 
    Z ("abc-3", "Insert array buffer checks");

} // end namespace seahorn
  

