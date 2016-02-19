#ifndef __ARRAY_BOUNDS_CHECK__HH__
#define __ARRAY_BOUNDS_CHECK__HH__

/*
  Encodings to instrument a program for Array Bounds Check (ABC).
 */ 

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Debug.h"

#include "seahorn/config.h"
#include "seahorn/Analysis/CanAccessMemory.hh"
#include "seahorn/Support/DSACount.hh"


#include "boost/unordered_set.hpp"

namespace seahorn
{
  using namespace llvm;

  // common helpers to all ABC encodings
  namespace abc_helpers {

    inline Value* getArgument (Function *F, unsigned pos)
    {
      unsigned idx = 0;
      for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end(); I != E;
           ++I, idx++)
      {
        if (idx == pos) return &*I; 
      }
      return nullptr;
    }
  
    inline ReturnInst* getReturnInst (Function *F)
    {
      // Assume there is one single return instruction per function
      for (llvm::BasicBlock& bb : *F)
      {
        if (ReturnInst *ret = dyn_cast<ReturnInst> (bb.getTerminator ()))
          return ret;
      }
      return nullptr;
    }

    inline int getOffsetAlign (const Instruction& I) {
      int res = -1; // initially no align found
      
      if (const StoreInst * SI = dyn_cast<const StoreInst> (&I)) {
        res = SI->getAlignment ();
      }
      else if (const LoadInst * LI = dyn_cast<const LoadInst> (&I)) {
        res = LI->getAlignment ();
      }
      else if (const MemTransferInst *MTI = dyn_cast<const MemTransferInst> (&I)) {
        res = MTI->getAlignment ();
      } 
      else if (const MemSetInst *MSI = dyn_cast<const MemSetInst> (&I)) {
        res = MSI->getAlignment ();
      } 
      return res; 
    }
 
    // Return true iff the check can be determined as definitely safe
    // or unsafe statically.
    inline bool IsTrivialCheck (const DataLayout* dl, 
                                const TargetLibraryInfo* tli,
                                const Value* Ptr) {
      // if (const GlobalVariable *GV = dyn_cast<GlobalVariable>(Ptr))  {
      //   if (GV->getType ()->getContainedType (0)->isFloatingPointTy() ||
      //       GV->getType ()->getContainedType (0)->isIntegerTy ()) {
      //     return true;
      //   } 
      // }
      if (const GetElementPtrInst * GEP = dyn_cast<GetElementPtrInst> (Ptr)) {
        
        if (!(isa<AllocaInst>(GEP->getPointerOperand()) || 
              isa<GlobalVariable>(GEP->getPointerOperand())))
          return false;

        // figure out statically the offset of the pointer
        unsigned BitWidth = dl->getPointerTypeSizeInBits(GEP->getType());
        APInt Offset (BitWidth, 0);
        if (GEP->accumulateConstantOffset (*dl, Offset)) {          
          if (Offset.isNegative ()) {
            errs () << "Definitely underflow while accessing memory: " 
                    << *GEP << "\n";
            return true;
          }
          // figure out statically the size of the memory object
          uint64_t Size;
          if (getObjectSize (GEP->getPointerOperand (), Size, dl, tli, true)) {
            int64_t Offset_val = Offset.getSExtValue ();
            int align = getOffsetAlign (*GEP);
            if (align < 0) return false; // no align found
            if ((Offset_val + align) > (int64_t) Size) {
              errs () << "Definitely overflow while accessing memory: "
                      << *GEP << "\n";
            }
            return true;
          }
        }
      }
      return false;
    }
 
    inline unsigned storageSize (const DataLayout* dl, const llvm::Type *t) 
    { // getTypeStorageSize does not include aligment padding.
      return dl->getTypeAllocSize (const_cast<Type*> (t));
    }

    inline unsigned storageSize (const DataLayout* dl, llvm::Type *t) 
    { // getTypeStorageSize does not include aligment padding.
      return dl->getTypeAllocSize (t);
    }

    inline unsigned fieldOffset (const DataLayout* dl, const StructType *t, unsigned field)
    {
      return dl->getStructLayout (const_cast<StructType*>(t))->
          getElementOffset (field);
    }

    // Helper to return the next instruction to I
    inline Instruction* getNextInst (Instruction* I) {
      if (I->isTerminator ()) return I;
      return I->getParent ()->getInstList ().getNext (I);
    }
    
    inline Type* createIntTy (LLVMContext& ctx) {
      return Type::getInt64Ty (ctx);
    }

    inline Value* createAdd(IRBuilder<> B, Value *LHS, Value *RHS, 
                            const Twine &Name = "") {
      assert (LHS->getType ()->isIntegerTy () && 
              RHS->getType ()->isIntegerTy ());

      Type* IntTy = createIntTy (B.getContext ());
      Value *LHS1 = B.CreateSExtOrBitCast (LHS, IntTy);
      Value *RHS1 = B.CreateSExtOrBitCast (RHS, IntTy);
      return  B.CreateAdd (LHS1, RHS1, Name);
    }

    inline Value* createMul(IRBuilder<> B, Value *LHS, unsigned RHS, 
                            const Twine &Name = "") {
      assert (LHS->getType ()->isIntegerTy ());
      Type* IntTy = createIntTy (B.getContext ());
      Value* LHS1 = B.CreateSExtOrBitCast (LHS, IntTy );
      return  B.CreateMul (LHS1, 
                           ConstantInt::get (IntTy, RHS), 
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
                               
    // Helper to create a integer constant
    inline Value* createIntCst (LLVMContext &ctx, uint64_t val) {
      return ConstantInt::get (createIntTy (ctx), val);
    }

    // Helper to create a null constant
    inline Type* voidPtr (LLVMContext &ctx) {
      return Type::getInt8Ty (ctx)->getPointerTo ();
    }

    // Helper to create a null constant
    inline Value* createNullCst (LLVMContext &ctx) {
      return ConstantPointerNull::get (Type::getInt8Ty (ctx)->getPointerTo ());
    }

    inline Value* createGlobalInt(Module& M, unsigned val, const Twine& Name ="") {
      IntegerType* intTy = cast<IntegerType>(createIntTy (M.getContext ()));
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
      GlobalVariable *GV = new GlobalVariable (M, voidPtr (M.getContext ()), 
                                               false, /*non-constant*/
                                               GlobalValue::InternalLinkage,
                                               NullPtr);
      GV->setName(Name);
      return GV;
    }

  } //end namespace abc_helpers



  /* 
     First encoding.

     For each pointer dereference *p we add two shadow registers:
     p.offset and p.size. p.offset is the distance from the base address
     of the object that contains p to actual p and p.size is the actual
     size of the allocated memory for p (including padding). Note that
     for stack and static allocations p.size is always know but for
     malloc-like allocations p.size may be unknown.

     Then, for each pointer dereference *p we add two assertions:
       [underflow]  assert (p.offset >= 0)
       [overflow ]  assert (p.offset + p.align <= p.size)
       where p.align is statically known by llvm.

     For instrumenting a function f we add for each dereferenceable
     formal parameter x two more shadow formal parameters x.offset and
     x.size. Then, at a call site of f and for a dereferenceable actual
     parameter y we add its corresponding y.offset and y.size. To
     instrument the return value of a function we just keep of two
     shadow global variables ret.offset and ret.size so that the callee
     updates them before it returns to the caller.

     If the instrumented program does not violate any of the assertions
     then the original program is free of buffer overflows/underflows.

     TODO: 
       - instrument pointers originated from loads.
       - instrument intToPtr instructions
  */
  class ABC1 : public llvm::ModulePass
  {
    typedef boost::unordered_set< const Value *> ValueSet;

    const DataLayout *m_dl;
    TargetLibraryInfo *m_tli;

    Type *m_Int64Ty;    
    Type *m_Int64PtrTy;    

    Function * m_errorFn;

    Value* m_ret_offset;
    Value* m_ret_size;

    unsigned m_mem_accesses;   //! total number of instrumented mem accesses
    unsigned m_checks_added;   //! checks added
    unsigned m_trivial_checks; //! checks ignored because they are safe
    unsigned m_checks_unable;  //! checks unable to add

    DenseMap <const Value*, Value*> m_offsets;
    DenseMap <const Value*, Value*> m_sizes;

   private:

    Value* lookupSize (const Value* ptr);
    Value* lookupOffset (const Value* ptr);

    bool ShouldBeTrackedPtr (Value* ptr, Function& F);
    
    /* To instrument accesses */

    void resolvePHIUsers (const Value *v, 
                          DenseMap <const Value*, Value*>& m_table);
                     
    void instrumentGepOffset(IRBuilder<> B, Instruction* insertPoint,
                             const GetElementPtrInst *gep);

    void instrumentSizeAndOffsetPtrRec (Function* F, IRBuilder<> B, 
                                        Instruction* insertPoint, 
                                        const Value * ptr, ValueSet & visited);
    
    void instrumentSizeAndOffsetPtr (Function* F, IRBuilder<> B, 
                                     Instruction* insertPoint, const Value * ptr);
      
    bool instrumentCheck (Function& F, IRBuilder<> B, Instruction& inst, 
                          const Value& ptr, Value* len);
    
    /*   To shadow function parameters  */

    DenseMap <const Function *, size_t > m_orig_arg_size;
    // keep track of the store instructions for returning the shadow
    // offset and size return parameters.
    typedef std::pair<StoreInst*,StoreInst* > StoreInstPair;
    typedef std::pair<Value*,Value*> ValuePair;
    DenseMap <const Function*,  StoreInstPair> m_ret_shadows;

    bool addFunShadowParams (Function *F, LLVMContext &ctx);  

    bool IsShadowableFunction (const Function &F) const;  
    bool IsShadowableType (Type * ty) const;
    // return the number of original arguments before adding shadow
    // parameters
    size_t getOrigArgSize (const Function &F) ;
    
    // Formal parameters of F are x1 x2 ... xn y1 ... ym where x1...xn
    // are the original formal parameters and y1...ym are the shadow
    // parameters to propagate offset and size. y1...ym is a sequence
    // of offset,size,...,offset,size. 
    //
    // This function returns the pair of shadow variables
    // <offset,size> corresponding to Arg if there exists, otherwise
    // returns a pair of null pointers.
    ValuePair findShadowArg (Function *F, const Value *Arg);
    StoreInstPair findShadowRet (Function *F);

  public:

    static char ID;

    ABC1 () : llvm::ModulePass (ID), 
              m_dl (nullptr), m_tli (nullptr),
              m_Int64Ty (nullptr), m_Int64PtrTy (nullptr),
              m_errorFn (nullptr), 
              m_mem_accesses (0), m_checks_added (0), 
              m_trivial_checks (0), m_checks_unable (0) { }
    
    virtual bool runOnModule (llvm::Module &M);
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "ArrayBoundsCheck1";}
  };


  /* 
     Second encoding.

     The encoding keeps track only of four global variables: 

     - g_base (pointer), 
     - g_ptr (pointer), 
     - g_size (integer), and
     - g_offset (integer) 

     where g_ptr is some address between [g_base,..., g_base + g_size - align] 
     and g_offset is g_ptr - g_base

     Initially:
        assume (g_base > 0);
        g_ptr = null;
        g_size = 0;
        g_offset = 0;
   
     For each allocation site p := alloc (n):
        if (!g_ptr && p == g_base) {
          g_ptr = g_base;
          g_size = n;
          g_offset = 0;
        }
        else {
         assume (g_base + g_size < p);
        }
    
     For each p := q + n:
        if (nd () && g_ptr && q == g_base) {
          g_ptr = p;
          g_offset = n;
        }

     For each memory access *p := rhs or lhs := *p:
        if (g_ptr && p == g_ptr) {
          assert (g_offset + align <= g_size);
          assert (g_offset >= 0);
        }
  */
  class ABC2 : public llvm::ModulePass
  {
    class ABCInst {
      
      const DataLayout*  m_dl;
      const TargetLibraryInfo* m_tli;
      IRBuilder<> m_B;
      CallGraph* m_cg;
      /// tracked_ptr is some aligned address between 
      ///    [tracked_base, ... , tracked_base + tracked_size - align (tracked_ptr)]
      /// m_tracked_offset = m_tracked_ptr - m_tracked_base
      Value* m_tracked_base; 
      Value* m_tracked_ptr;
      Value* m_tracked_offset;
      Value* m_tracked_size;
      
      Function* m_errorFn;
      Function* m_nondetFn;
      Function* m_nondetPtrFn;
      Function* m_assumeFn;
      
     public: // counters for stats
      
      unsigned m_checks_added;   
      unsigned m_trivial_checks; 
      unsigned m_mem_accesses;
      
     private:
      
      void update_callgraph(Function* caller, CallInst* callee);

     private:
      
      //! Extract offset from gep instruction
      Value* doGep(GetElementPtrInst *gep);
      
      //! Instrument pointer arithmetic
      void doPtrArith (Value* lhs, Value* rhs, GetElementPtrInst * gep, 
                       Instruction* insertPt);
      
      //! Initialization of base, offset, and size.
      void doInit (Module& M);
      
      //! Instrument any allocation site
      void doAllocaSite (Value* Ptr, Value* Size, Instruction* insertPt);
      
      //! Instrument any read or write to a pointer
      void doChecks (Value* Ptr, Value* N, Instruction* insertPt);
      
     public:
      
      ABCInst (Module& M, 
               const DataLayout* dl, const TargetLibraryInfo* tli,
               IRBuilder<> B, CallGraph* cg,
               Function* errorFn, Function* nondetFn,
               Function* nondetPtrFn, Function* assumeFn);
      
      void visit (GetElementPtrInst *I);
      void visit (LoadInst *I);
      void visit (StoreInst *I);
      void visit (MemTransferInst *MTI);
      void visit (MemSetInst *MSI);
      void visit (AllocaInst *I);
      void visit (CallInst *I);
    }; // end class
    
    bool ShouldBeTrackedPtr (Value* ptr, Function& F);

   public:

    static char ID;
    ABC2 (): llvm::ModulePass (ID) { }
    virtual bool runOnModule (llvm::Module &M);
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "ArrayBoundsCheck2";}
    
  };

}

#endif
