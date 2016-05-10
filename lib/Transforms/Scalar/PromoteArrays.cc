#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/TypeFinder.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"

#include "avy/AvyDebug.h"

/*
  This pass rewrites a module by transforming sized arrays to packed
  structs.

  Currently, we handle two cases:

  - struct members of array type by replacing
  
    %struct.foo = type { i32, %struct.bar, [2 x i32] }

    with

    %struct.foo = type { i32, %struct.bar, <{i32, i32 }>}

  - allocas of arrays by replacing 

    %a = alloca [10 x i32]
  
    with 

    %a = alloca <{ i32, i32, i32, i32, i32, i32, i32, i32, i32, i32 }>

  TODO: Update CallGraph
  TODO: All the metadata is removed by this pass. See FIXME.
  
*/

using namespace llvm;

#define DEBUG_TYPE "promote-arrays"

namespace seahorn {

  class PromoteArrays : public ModulePass {

   public:

    static char ID; // Pass ID, replacement for typeid
    
    PromoteArrays() : ModulePass(ID) { }
    
    bool runOnModule(Module &M);

    bool runOnFunction(Function &F) {return false;}
    
    void getAnalysisUsage (AnalysisUsage &AU) const
    { 
      AU.setPreservesAll ();
      AU.addRequired<TargetLibraryInfo>();
      AU.addRequired<DataLayoutPass>();
      AU.addRequired<CallGraphWrapperPass>(); 
    }
    
    virtual const char* getPassName () const {
      return "Convert sized arrays to packed structs";
    }

  private:

    const DataLayout *DL;
    const TargetLibraryInfo *TLI;
    CallGraph *CG;
    DenseMap<Type*,Type*> TypeMap;
    DenseMap<GlobalValue*, GlobalValue*> GlobalValueMap;
    DenseMap<Constant*, Constant*> ConstantMap;

    SmallSet<Type*, 32> PromotedTypes;

    // Convert from the old type system to the new one. 
    Type* ConvertType (Type *T, bool hasStructAncestor);
    Constant* ConvertConstant (Constant *C);
    Value* ConvertValue (Value*V, DenseMap<Value*,Value*> &LocalValueMap);

    void RewriteFunctionBody(Function *F);
    void RewriteFunctionDecl(Function *F);

    SmallVector<Value*, 8> 
    RewriteGEPNonConstantIdx(GetElementPtrInst *GEPI,
                             DenseMap<Value*,Value*> &LocalValueMap);
    SmallVector<Instruction*, 4>
    RewriteGEP(GetElementPtrInst *GEPI, DenseMap<Value*,Value*> &LocalValueMap);

  };

  // ValuePlaceHolder - A temporary placeholder value.  It appears as
  // an instruction of type Instruction::UserOp1.
  struct ValuePlaceHolder : public Instruction {

    ValuePlaceHolder(Type *Ty, Instruction *InsertBefore = nullptr) 
        : Instruction(Ty, Instruction::UserOp1, nullptr, 0, InsertBefore) { }

    virtual Instruction *clone_impl() const { abort(); return nullptr; }

    //virtual const char *getOpcodeName() const { return "ValuePlaceHolder"; }

    void print(llvm::raw_ostream&OS) const {
      OS << "ValuePlaceHolder";
    }

    // Methods for support type inquiry through isa, cast, and dyn_cast:
    static inline bool classof(const ValuePlaceHolder *) { return true; }
    static inline bool classof(const Instruction *I) {
      return (I->getOpcode() == Instruction::UserOp1);
    }
    static inline bool classof(const Value *V) {
      return isa<Instruction>(V) && classof(cast<Instruction>(V));
    }
  };

  // Convert from the old type system to the new one. 
  Type* PromoteArrays::
  ConvertType (Type *T, bool hasStructAncestor=false) {   
    
    auto TMI = TypeMap.find(T);
    if (TMI != TypeMap.end ())
      return TMI->second;

    Type* NT = nullptr;

    if (PointerType *PT = dyn_cast<PointerType>(T)) {
      Type*NPET = ConvertType (PT->getElementType (), hasStructAncestor);
      NT = PointerType::get (NPET, PT->getAddressSpace());
      goto convert_type_end;
    }

    if (FunctionType *FT = dyn_cast<FunctionType>(T)) {
      std::vector<Type*> NParamsTy;
      NParamsTy.reserve (FT->getNumParams ());
      for (auto ParamTy: FT->params())
        NParamsTy.push_back (ConvertType (ParamTy, hasStructAncestor));
      Type* NRetTy = ConvertType (FT->getReturnType(), hasStructAncestor);
      NT = FunctionType::get (NRetTy, NParamsTy, FT->isVarArg());
      goto convert_type_end;
    }
    
    if (StructType *ST = dyn_cast<StructType>(T)) {

      if (ST->isOpaque ()) { // ignore opaque types. 
        NT = T;
        goto convert_type_end;
      }

      if (ST->isLiteral ()) {
        // The struct type cannot be recursive
        std::vector<Type*> NEs;
        NEs.reserve (ST->getNumContainedTypes());
        for (auto ETy: ST->elements())
          NEs.push_back (ConvertType (ETy, hasStructAncestor));
        NT = StructType::get (ST->getContext(), NEs, ST->isPacked());        
        goto convert_type_end;
      } else {
        // To build a potential recursive type the trick is to create an
        // indentified structure whose body can be specified after the
        // type has been created.
        NT = StructType::create (ST->getContext(), ST->getName());
        TypeMap[T] = NT; // insert here to break cycles

        std::vector<Type*> NEs;
        NEs.reserve (ST->getNumContainedTypes());
        for (auto ETy: ST->elements())
          NEs.push_back (ConvertType (ETy,true));
        cast<StructType>(NT)->setBody(NEs, ST->isPacked());
        return NT;
      }
    }

    if (ArrayType *AT = dyn_cast<ArrayType>(T)) {
      if (hasStructAncestor || PromotedTypes.count(AT) > 0) { 
        // --- Convert array to a packed struct 
        std::vector<Type*> StructElementTypes;
        StructElementTypes.reserve (AT->getNumElements ());
        Type* StructElementTy = ConvertType (AT->getElementType(), hasStructAncestor);
        for (unsigned j = 0; j < AT->getNumElements (); j++)
          StructElementTypes.push_back (StructElementTy);
        NT = StructType::get(T->getContext(), StructElementTypes, true/*isPacked*/);
        goto convert_type_end;
      } else {
        NT = ArrayType::get (ConvertType (AT->getElementType(), hasStructAncestor), 
                             AT->getNumElements());
        goto convert_type_end;

      }
    }

    if (VectorType *VT = dyn_cast<VectorType>(T)) {
      NT = VectorType::get (ConvertType (VT->getElementType(), hasStructAncestor), 
                            VT->getNumElements());
      goto convert_type_end;
    }

    NT=T;

 convert_type_end:
    return TypeMap[T]=NT;
  }

  // Convert from the old type system to the new one. 
  Constant* PromoteArrays::ConvertConstant (Constant *C) {

    if (isa<ConstantInt> (C)) return C;

    if (isa<ConstantFP> (C)) return C;

    auto It = ConstantMap.find(C);
    if (It != ConstantMap.end ())
      return It->second;

    if (ConstantAggregateZero* CAZ = dyn_cast<ConstantAggregateZero>(C)) {
      return ConstantMap[C] = ConstantAggregateZero::get(
          ConvertType(CAZ->getType()));
                      
    } 

    if (ConstantStruct* CS = dyn_cast<ConstantStruct>(C)) {
      std::vector<Constant*> NElems;
      NElems.reserve (CS->getType()->getNumElements());
      for (unsigned I = 0, N = CS->getType()->getNumElements(); I != N; ++I) {
        Constant *Elem = C->getAggregateElement(I);
        if (!Elem) return C;
        NElems.push_back (ConvertConstant(Elem));
      }
      return ConstantMap[C] = ConstantStruct::get(cast<StructType>(
          ConvertType(CS->getType())), NElems);
    } 

    if (ConstantArray* CA = dyn_cast<ConstantArray>(C)) {
      std::vector<Constant*> NElems;
      NElems.reserve (CA->getType()->getNumElements());
      for (unsigned I = 0, N = CA->getType()->getNumElements(); I != N; ++I) {
        Constant *Elem = C->getAggregateElement(I);
        if (!Elem) return C;
        NElems.push_back (ConvertConstant(Elem));
      }
      return ConstantMap[C] = ConstantArray::get(
          cast<ArrayType>(ConvertType(CA->getType())), NElems);
    } 


    if (ConstantVector* CV = dyn_cast<ConstantVector>(C)) {
      std::vector<Constant*> NElems;
      NElems.reserve (CV->getType()->getNumElements());
      for (unsigned I = 0, N = CV->getType()->getNumElements(); I != N; ++I) {
        Constant *Elem = C->getAggregateElement(I);
        if (!Elem) return C;
        NElems.push_back (ConvertConstant(Elem));
      }
      return ConstantMap[C] = ConstantVector::get(NElems);
    } 
    
    if (ConstantPointerNull* CNP = dyn_cast<ConstantPointerNull>(C)) {
      return ConstantMap[C] = ConstantPointerNull::get(
          cast<PointerType>(ConvertType(C->getType())));
    }

    if (UndefValue* Undef = dyn_cast<UndefValue>(C)) {
      return ConstantMap[C] = UndefValue::get(ConvertType(C->getType()));
    }
     
    // otherwise, we don not convert the constant
    return C;
  }


  Value* PromoteArrays::
  ConvertValue (Value*V, DenseMap<Value*,Value*> &LocalValueMap) {

    // Ignore null values and simple constants..
    if (!V) return nullptr;

    // Check to see if this is an out of function reference first...
    if (GlobalValue *GV = dyn_cast<GlobalValue>(V)) {
      // Check to see if the value is in the map...
      auto I = GlobalValueMap.find(GV);
      if (I == GlobalValueMap.end()) {
        return V;  // Not mapped, just return value itself
      }
      return I->second;
    }
  
    auto I = LocalValueMap.find(V);
    if (I != LocalValueMap.end()) {
      return I->second;
    }

    if (BasicBlock *BB = dyn_cast<BasicBlock>(V)) {
      // Create placeholder block to represent the basic block we
      // haven't seen yet. This will be used when the block gets
      // created.

      return LocalValueMap[V] = BasicBlock::Create(V->getContext(), BB->getName());
    }

    if (Constant *CPV = dyn_cast<Constant>(V)) {
      if (isa<ConstantExpr>(CPV))
        report_fatal_error("PromoteArrays does not support constant expressions!");

      return ConvertConstant (CPV);
    }

    // Otherwise make a value to represent it
    ValuePlaceHolder * VPH = ::new ValuePlaceHolder(ConvertType(V->getType())); 
    LocalValueMap[V] = VPH;
    return VPH;
  }

  // void removeTypedMetadata(Instruction* I) {  
  //   SmallVector<std::pair<unsigned, MDNode*>, 4> MDForInst;
  //   I->getAllMetadata(MDForInst);
  //   for(unsigned i = 0, e = MDForInst.size(); i!=e; ++i) {
  //     unsigned MDKind = MDForInst[i].first;
  //     switch (MDKind) {
  //       case Metadata::MDTupleKind:
  //       case Metadata::MDLocationKind:
  //       case Metadata::MDNodeFwdDeclKind:
  //       case Metadata::MDStringKind:
  //         break;
  //       case Metadata::ConstantAsMetadataKind:
  //       case Metadata::LocalAsMetadataKind:
  //       default:
  //         I->setMetadata(MDKind, nullptr);
  //     }
  //   }
  // }

  bool IsGEPConstantIdx (GetElementPtrInst *GEPI) {
    gep_type_iterator GEPIt = gep_type_begin(GEPI), E = gep_type_end(GEPI);
    if (GEPIt == E) return true;

    // Walk through the GEP type indices, checking the types that this
    // indexes into.
    for (; GEPIt != E; ++GEPIt) {
      // Ignore struct elements, no extra checking needed for these.
      if ((*GEPIt)->isStructTy())
        continue;      
      ConstantInt *IdxVal = dyn_cast<ConstantInt>(GEPIt.getOperand());
      if (!IdxVal) {
        return false;
      }
    }
    return true;
  }

  SmallVector<Value*, 8> RewriteGEPConstantIdx(GetElementPtrInst *GEPI) {
    
    SmallVector<Value*, 8> NewIndices;    
    gep_type_iterator GEPIt = gep_type_begin(GEPI), E = gep_type_end(GEPI);
    if (GEPIt == E) return NewIndices;

    assert (IsGEPConstantIdx (GEPI));

    // All struct member indices must be i32
    gep_type_iterator typeIt = gep_type_begin (*GEPI);
    for (unsigned i = 1; i < GEPI->getNumOperands (); ++i, ++typeIt) {
      if (ArrayType * AT = dyn_cast<ArrayType> (*typeIt)) {
        if (ConstantInt *CI = dyn_cast<ConstantInt> (GEPI->getOperand (i))) {
          if (CI->getBitWidth () != 32) { 
            NewIndices.push_back (
                ConstantInt::get(Type::getInt32Ty(GEPI->getContext ()),
                                 CI->getSExtValue()));
            continue;
          }
        }
      }
      NewIndices.push_back (GEPI->getOperand (i));
    }
    return NewIndices;
  }

  SmallVector<Value*, 8> PromoteArrays::
  RewriteGEPNonConstantIdx(GetElementPtrInst *GEPI,
                           DenseMap<Value*,Value*> &LocalValueMap) {
    SmallVector<Value*, 8> NewIndexes;
    Instruction::op_iterator I = GEPI->idx_begin();
    Instruction::op_iterator E = GEPI->idx_end();
    for (; I!=E; ++I)
      NewIndexes.push_back(ConvertValue(*I, LocalValueMap));
    return NewIndexes;
  }

  SmallVector<Instruction*, 4> PromoteArrays::
  RewriteGEP(GetElementPtrInst *GEPI, DenseMap<Value*,Value*> &LocalValueMap) {
    
    SmallVector<Instruction*, 4> NewIns;
    if (IsGEPConstantIdx (GEPI)) {
      GetElementPtrInst* NewI = 
          GetElementPtrInst::Create(ConvertValue(GEPI->getPointerOperand(), LocalValueMap),
                                    RewriteGEPConstantIdx (GEPI));
      NewI->setIsInBounds (GEPI->isInBounds());
      NewIns.push_back(NewI);
    } else {

      LOG ("promote-arrays",       
           errs () << *GEPI << "\n"
           //errs () << "Type " << *(GEPI->getPointerOperand()->getType()) 
                   << "  has a non-constant access\n";
           );

      Type* OldType = nullptr;
      auto LocalValueMapI = LocalValueMap.find (GEPI->getPointerOperand());
      if (LocalValueMapI != LocalValueMap.end ())
        OldType = LocalValueMapI->first->getType ();
      
      if (!OldType) {
        if (GlobalValue* GV = dyn_cast<GlobalValue>(GEPI->getPointerOperand())) {
          auto GlobalValueMapI = GlobalValueMap.find (GV);
          if (GlobalValueMapI != GlobalValueMap.end ())
            OldType = GlobalValueMapI->first->getType ();
        }
      }
      
      if (!OldType) { 
        errs () << *GEPI << "\n";
        report_fatal_error("PromoteArrays failed with non-constant GEP instruction!");
      }
      
      // converted base pointer to old system
      BitCastInst* OldGEPI = 
          new BitCastInst (ConvertValue(GEPI->getPointerOperand(), LocalValueMap), 
                           OldType);
      NewIns.push_back(OldGEPI);
      // perform pointer arithmetic in the old system
      GetElementPtrInst *NewGEPI = 
          GetElementPtrInst::Create(OldGEPI, RewriteGEPNonConstantIdx(GEPI,LocalValueMap));
      NewGEPI->setIsInBounds (GEPI->isInBounds());
      NewIns.push_back(NewGEPI);
      // translated back to the new system
      NewIns.push_back(new BitCastInst(NewGEPI, ConvertType(NewGEPI->getType())));
    }
    return NewIns;
  }
 
  bool DoesRewriteFunction (Function*F) {
    if (F->getName().startswith ("llvm.dbg")) 
      return false;
    return true;
    // FunctionType *FTy = F->getFunctionType();
    // return (!(FTy->getReturnType()->isVoidTy() && FTy->getNumParams () == 0));
  }

  bool DoesRewriteFunction (CallSite& CS) {
    if (isa<DbgInfoIntrinsic>(CS.getInstruction()))
      return false;
    return true;
    //return (!CS.arg_empty());
  }

  // Rewrite a function signature to convert from the old type system
  // to the new one.
  void PromoteArrays::RewriteFunctionDecl (Function *F) {
    if (!DoesRewriteFunction (F))
      return;

    // --- New function signature 
    FunctionType *FTy = F->getFunctionType();
    Type* NRetTy = ConvertType (FTy->getReturnType());
    std::vector<Type*> NParams;    
    for (auto Ty: FTy->params ())
      NParams.push_back(ConvertType (Ty));
    FunctionType *NFTy = FunctionType::get(NRetTy,  NParams, FTy->isVarArg());
    Function *NF = Function::Create(NFTy, F->getLinkage());
    NF->takeName(F);
    NF->copyAttributesFrom(F);
    F->getParent()->getFunctionList().insert(F, NF);
    GlobalValueMap[F] = NF;
  }

  // Rewrite a function body to convert from the old type system to
  // the new one. TypeMap contains the type conversion *but* the old
  // and new types must be equivalent memory-wise.
  void PromoteArrays::RewriteFunctionBody(Function *F) {

    if (F->isDeclaration ())
      return;

    Function* NF = nullptr;
    auto GlobalValueMapI = GlobalValueMap.find(F);
    if (GlobalValueMapI == GlobalValueMap.end ())
      return; // this should not happen
    else
      NF = cast<Function>(GlobalValueMapI->second);

    DenseMap<Value*,Value*> LocalValueMap; 
    // Loop over all of the basic blocks copying instructions over...
    for (auto &BB: *F) {
      
      // Create a new basic block and establish a mapping between the
      // old and new
      BasicBlock *NewBB = cast<BasicBlock>(ConvertValue(&BB, LocalValueMap));
      NF->getBasicBlockList().push_back(NewBB);  // Add block to function
      
      // Copy over all of the instructions in the basic block...
      for (auto &I : BB) {

        Instruction *NewI = nullptr;
        
        switch (I.getOpcode()) {
          // Terminator Instructions
          case Instruction::Ret:
            NewI = ReturnInst::Create(I.getContext(),
                                      ConvertValue(cast<ReturnInst>(I).getReturnValue(), 
                                                   LocalValueMap));
            break;
          case Instruction::Br: {
            const BranchInst &BI = cast<BranchInst>(I);
            if (BI.isConditional()) {
              NewI =
                  BranchInst::Create(cast<BasicBlock>(ConvertValue(BI.getSuccessor(0),LocalValueMap)),
                                     cast<BasicBlock>(ConvertValue(BI.getSuccessor(1),LocalValueMap)),
                                     ConvertValue(BI.getCondition(),LocalValueMap));
            } else {
              NewI = 
                  BranchInst::Create(cast<BasicBlock>(ConvertValue(BI.getSuccessor(0),LocalValueMap)));
            }
            break;
          }
          case Instruction::Unreachable:
            NewI = new UnreachableInst (F->getContext());
            break;
          case Instruction::Switch:
            report_fatal_error("PromoteArrays does not support switch instructions!");
          case Instruction::Invoke:
            report_fatal_error("PromoteArrays does not support invoke instructions!");
          case Instruction::Resume:
            report_fatal_error("PromoteArrays does not support resume instructions!");
            // Binary Instructions
          case Instruction::Add:
          case Instruction::FAdd:
          case Instruction::Sub:
          case Instruction::FSub:
          case Instruction::Mul:
          case Instruction::FMul:
          case Instruction::UDiv:
          case Instruction::SDiv:
          case Instruction::FDiv:
          case Instruction::URem:
          case Instruction::SRem:
          case Instruction::FRem:
            // Logical Operations
          case Instruction::And:
          case Instruction::Or:
          case Instruction::Xor:
          case Instruction::Shl:
          case Instruction::LShr:
          case Instruction::AShr:
            NewI = BinaryOperator::Create((Instruction::BinaryOps)I.getOpcode(),
                                          ConvertValue(I.getOperand(0),LocalValueMap),
                                          ConvertValue(I.getOperand(1),LocalValueMap));

            if (isa<PossiblyExactOperator> (I))  
              cast<BinaryOperator>(NewI)->setIsExact (cast<BinaryOperator>(I).isExact());

            if (isa<OverflowingBinaryOperator>(I)) {
              cast<BinaryOperator>(NewI)->setHasNoUnsignedWrap (cast<BinaryOperator>(I).hasNoUnsignedWrap());
              cast<BinaryOperator>(NewI)->setHasNoSignedWrap (cast<BinaryOperator>(I).hasNoSignedWrap());
            }
                
            break;
            // Comparison Instructions
          case Instruction::ICmp:
            NewI = new ICmpInst(cast<ICmpInst>(I).getPredicate(),
                                ConvertValue(cast<ICmpInst>(I).getOperand(0),LocalValueMap),
                                ConvertValue(cast<ICmpInst>(I).getOperand(1),LocalValueMap));
                                
            break;
          case Instruction::FCmp:
            NewI = new FCmpInst(cast<FCmpInst>(I).getPredicate(),
                                ConvertValue(cast<FCmpInst>(I).getOperand(0),LocalValueMap),
                                ConvertValue(cast<FCmpInst>(I).getOperand(1),LocalValueMap));
                                
            break;            
            // Memory Instructions
          case Instruction::Alloca:
            NewI = new AllocaInst(ConvertType(cast<AllocaInst>(I).getAllocatedType()),
                                  ConvertValue(cast<AllocaInst>(I).getOperand(0),
                                               LocalValueMap),
                                  cast<AllocaInst>(I).getAlignment());
            break;
          case Instruction::Load:
            NewI = new LoadInst(ConvertValue(I.getOperand(0),LocalValueMap));
            cast<LoadInst>(NewI)->setVolatile (cast<LoadInst>(I).isVolatile());
            cast<LoadInst>(NewI)->setAlignment (cast<LoadInst>(I).getAlignment());
            cast<LoadInst>(NewI)->setOrdering (cast<LoadInst>(I).getOrdering());
            cast<LoadInst>(NewI)->setSynchScope (cast<LoadInst>(I).getSynchScope());
            break;
          case Instruction::Store:
            NewI = new StoreInst(ConvertValue(I.getOperand(0),LocalValueMap),
                                 ConvertValue(I.getOperand(1),LocalValueMap));
            cast<StoreInst>(NewI)->setVolatile (cast<StoreInst>(I).isVolatile());
            cast<StoreInst>(NewI)->setAlignment (cast<StoreInst>(I).getAlignment());
            cast<StoreInst>(NewI)->setOrdering (cast<StoreInst>(I).getOrdering());
            cast<StoreInst>(NewI)->setSynchScope (cast<StoreInst>(I).getSynchScope());
            break;
          case Instruction::GetElementPtr: {
            GetElementPtrInst &GEPI = cast<GetElementPtrInst>(I);
            auto NewIns = RewriteGEP(&GEPI,LocalValueMap);
            if (NewIns.size () == 1) { // constant indexes 
              NewI = NewIns[0];
            } else if (NewIns.size () == 3) { // non-constant indexes
              NewBB->getInstList().push_back(NewIns[0]); // bitcast to old system             
              NewBB->getInstList().push_back(NewIns[1]); // gep in the old system             
              NewI = NewIns[2];                          // bitcast to the new sytem  
            } else 
              report_fatal_error ("PromoteArrays translation of GEP failed!");
            break;
          }
          // Miscellaneous Instructions
          case Instruction::PHI: {
            const PHINode &OldPN = cast<PHINode>(I);
            PHINode *PN = PHINode::Create(ConvertType(OldPN.getType()),
                                          OldPN.getNumIncomingValues());
            for (unsigned i = 0; i < OldPN.getNumIncomingValues(); ++i)
              PN->addIncoming(ConvertValue(OldPN.getIncomingValue(i),LocalValueMap),
                              cast<BasicBlock>(ConvertValue(OldPN.getIncomingBlock(i),
                                                            LocalValueMap)));
            NewI = PN;
            break;
          }
          case Instruction::InsertValue: {
            InsertValueInst &OldIVI = cast<InsertValueInst>(I);
            NewI = InsertValueInst::Create (ConvertValue(OldIVI.getAggregateOperand(), LocalValueMap),
                                            ConvertValue(OldIVI.getInsertedValueOperand(), LocalValueMap),
                                            OldIVI.getIndices());
            break;
          }          
          case Instruction::ExtractValue: {
            ExtractValueInst &OldEVI = cast<ExtractValueInst>(I);
            NewI = ExtractValueInst::Create (ConvertValue(OldEVI.getAggregateOperand(), LocalValueMap),
                                             OldEVI.getIndices());
            break;
          }          
          case Instruction::InsertElement: {
            InsertElementInst &OldIEI = cast<InsertElementInst>(I);
            NewI = InsertElementInst::Create (ConvertValue(OldIEI.getOperand(0), LocalValueMap),
                                              ConvertValue(OldIEI.getOperand(1), LocalValueMap),
                                              ConvertValue(OldIEI.getOperand(2), LocalValueMap));
            break;
          }          
          case Instruction::ExtractElement: {
            ExtractElementInst &OldEEI = cast<ExtractElementInst>(I);
            NewI = ExtractElementInst::Create (ConvertValue(OldEEI.getVectorOperand(), LocalValueMap),
                                               ConvertValue(OldEEI.getIndexOperand(), LocalValueMap));
            break;
          }          

          case Instruction::Select: {
            SelectInst &OldSelIns = cast<SelectInst>(I);
            NewI = SelectInst::Create (ConvertValue(OldSelIns.getCondition(), LocalValueMap),
                                       ConvertValue(OldSelIns.getTrueValue(), LocalValueMap),
                                       ConvertValue(OldSelIns.getFalseValue(), LocalValueMap));
            break;
          }
          case Instruction::Trunc:
          case Instruction::ZExt:
          case Instruction::SExt:
          case Instruction::FPToUI:
          case Instruction::FPToSI:
          case Instruction::UIToFP:
          case Instruction::SIToFP:
          case Instruction::FPTrunc:
          case Instruction::FPExt:
          case Instruction::PtrToInt:
          case Instruction::IntToPtr:
          case Instruction::BitCast:
            NewI = CastInst::Create((Instruction::CastOps) I.getOpcode(),
                                    ConvertValue(I.getOperand(0),LocalValueMap),
                                    ConvertType(I.getType()));
            break;
          case Instruction::Call: {
            CallSite CS (&I);
            if (!DoesRewriteFunction (CS))
              continue;
            std::vector<Value*> Args;
            Args.reserve(I.getNumOperands());
            for (unsigned i=0; i < CS.arg_size(); i++)
              Args.push_back(ConvertValue(CS.getArgument(i),LocalValueMap));
            NewI = CallInst::Create(ConvertValue(CS.getCalledValue(),
                                                 LocalValueMap), Args);
            cast<CallInst>(NewI)->setAttributes(CS.getAttributes());
            break;
          }
          default:
            errs () << I << "\n";
            report_fatal_error("PromoteArrays found unknown instruction!");
        }
        
        NewI->setName(I.getName());

        // FIXME: we do not propagate debug information because we
        // need to rename it to the new type system.
        // 
        //NewI->setDebugLoc(I.getDebugLoc());
                                        
        NewBB->getInstList().push_back(NewI);
        
        // Check to see if we had to make a placeholder for this value...
        auto LocalValueMapI = LocalValueMap.find(&I);
        if (LocalValueMapI != LocalValueMap.end()) {
          Instruction *I = cast<Instruction>(LocalValueMapI->second);
          // Replace all uses of the place holder with the final value.
          I->replaceAllUsesWith(NewI);
          if (isa<ValuePlaceHolder>(I))
            delete I;// free the placeholder
        }

        // Keep track of the fact the the local implementation of this
        // instruction is NewI.
        LocalValueMap[&I] = NewI;

        LOG ("promote-arrays-details",           
             errs () << "  Rewritten " << I  << "\n  with       " 
                     << *NewI << "\n";);
      }
    }

    // --- Replace formal parameters
    Function::arg_iterator AI = F->arg_begin();
    Function::arg_iterator AE = F->arg_end();
    Function::arg_iterator NAI = NF->arg_begin();
    while (AI != AE) {
      auto LocalValueMapI = LocalValueMap.find(AI);
      if (LocalValueMapI != LocalValueMap.end()) {
        // Replace all uses of the place holder with the final parameter.
        LocalValueMapI->second->replaceAllUsesWith(NAI);
        NAI->takeName(AI);
      }
      ++AI; ++NAI;
    }

    LocalValueMap.clear();
  }

  bool PromoteArrays::runOnModule(Module &M) {

    DL = &getAnalysis<DataLayoutPass>().getDataLayout ();
    TLI = &getAnalysis<TargetLibraryInfo>();
    CallGraphWrapperPass *cgwp = &getAnalysis<CallGraphWrapperPass> ();
    CG = &cgwp->getCallGraph ();

    // --- Walk through all the module types and identify struct types
    //     with array members
    TypeFinder StructTypes;
    StructTypes.run(M, false);
    bool Change = false;
    for (unsigned i = 0, e = StructTypes.size(); i != e; ++i) {
      StructType *STy = StructTypes[i];
      for (Type::subtype_iterator I = STy->subtype_begin(), E = STy->subtype_end();
           I != E; ++I) {

        if (ArrayType *ATy = dyn_cast<ArrayType> (*I)) {
          // ignore the struct if it has an unsized array member
          unsigned NumElements = ATy->getNumElements ();
          if (NumElements == 0)
            continue;

          Change = true;
          PromotedTypes.insert(STy);
        }
      }
    }

    // promote allocas of sized arrays
    for (auto &F: M) 
      for (inst_iterator II = inst_begin(&F), IE = inst_end(&F); II!=IE; ++II) {
        Instruction *I = &*II;
        if (AllocaInst* AI = dyn_cast<AllocaInst>(I)) {
          if (ArrayType *ATy = dyn_cast<ArrayType> (AI->getAllocatedType())) {
            if (ATy->getNumElements () > 0) {
              PromotedTypes.insert(ATy);
              Change = true;
            }
          }
        }
      }
    
    if (!Change) 
      return false;
    
    LOG ("promote-arrays", 
         errs () << PromotedTypes.size () << " types will be promoted: \n";
         for (auto T: PromotedTypes) { 
           if (isa<StructType>(T))
             errs () << "\t" << *T << " has a sized array member.\n";
           else if (isa<ArrayType>(T))
             errs () << "\t" << *T << " is a sized array.\n";
           else // this case should not happen
             errs () << "\t" << *T << "\n";
         }
         );
         
    // FIXME: remove all the metadata!
    //        We need to rename to the new type system all the metadata
    if (NamedMDNode* CU = M.getNamedMetadata("llvm.dbg.cu"))
      CU->eraseFromParent();

    // --- Create conversion map for globals from old system to new one 
    std::vector<GlobalVariable*> Globals;
    Globals.reserve (std::distance(M.global_begin(), M.global_end()));
    for (auto &GV: M.globals()) { 
      Globals.push_back (&GV);
    }
    for (auto GV: Globals) {
      // FIXME: llvm.global_ctors defines the initialization order
      // between static objects in different translation units. If the
      // analysis depends on it we need to properly rename to the new
      // type system rather than remove it.
      if (GV->getName().startswith("llvm.global_ctors")) {
        GV->eraseFromParent();
        continue;
      }

      Constant *In = nullptr;
      Type *GlobalType = nullptr;

      if (GV->hasInitializer()) {
        In = ConvertConstant(GV->getInitializer());
        GlobalType = In->getType();
      } 
      else { 
        GlobalType = ConvertType(cast<PointerType>(GV->getType())->getElementType()); 
      }

      GlobalVariable* NGV = new llvm::GlobalVariable (M, GlobalType,
                                                      GV->isConstant(), 
                                                      GV->getLinkage(), 
                                                      In, GV->getName()); 
      
      NGV->copyAttributesFrom(GV);
      GlobalValueMap[GV] = NGV;
    }
    Globals.clear();

    // --- Create conversion map for aliases from old system to new one 
    std::vector<GlobalAlias*> Aliases;
    Aliases.reserve (std::distance(M.alias_begin(), M.alias_end()));
    for (auto &Alias: M.aliases())
      Aliases.push_back (&Alias);
    for (auto Alias: Aliases) {
      Type *AliasType = ConvertType(Alias->getType());
      Constant *NAliasee = ConvertConstant(Alias->getAliasee());
      GlobalAlias* NAlias = GlobalAlias::create (AliasType, 
                                                 cast<PointerType>(AliasType)->getAddressSpace(),
                                                 Alias->getLinkage(), Alias->getName(), 
                                                 NAliasee, &M);
      NAlias->setVisibility(Alias->getVisibility());
      GlobalValueMap[Alias] = NAlias;
    }
    Aliases.clear();
    
    // --- Create conversion map from old type system to the new one
    //     for each function
    for (auto &F: M)
      RewriteFunctionDecl(&F);
    for (auto &F: M)
      RewriteFunctionBody(&F);

    // --- Cleanup of the old type system

    // collect all the call graph nodes and the nodes to be removed.
    std::vector<CallGraphNode*> CGNodes; 
    std::vector<CallGraphNode*> CGNToRemove; 
    for (scc_iterator<CallGraph *> I = scc_begin(CG), E = scc_end(CG);
         I != E; ++I) {
      for (auto CGN: *I)  {
        CGNodes.push_back (CGN);
        if (CGN->getFunction() && 
            GlobalValueMap.find(CGN->getFunction()) != GlobalValueMap.end())
          CGNToRemove.push_back(CGN);
      }
    }

    // remove all outgoing edges in CGNToRemove
    for (auto CGN: CGNToRemove) {
      CGN->removeAllCalledFunctions();
    }

    // remove any incoming edge outside CGNToRemove (specially from the
    // root node)
    for (auto CGN: CGNodes) {
      for (auto Callee: CGNToRemove) {
        CGN->removeAnyCallEdgeTo(Callee);
      }
    }

    while (!CGNToRemove.empty()) {
      CallGraphNode *CGN = CGNToRemove.back();
      CGNToRemove.pop_back();
      CGN->getFunction()->dropAllReferences ();
      CG->removeFunctionFromModule(CGN);
    }

    return Change;
  }

  char PromoteArrays::ID = 0;

  Pass* createPromoteArraysPass () 
  { return new PromoteArrays (); }

} // end seahorn namespace
