#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/raw_ostream.h"

#include "boost/range.hpp"
#include "avy/AvyDebug.h"

using namespace llvm;

#define DEBUG_TYPE "symbolize-bounds"

STATISTIC(SymbolizedLoops, 
         "Number of constant loop bounds converted to symbolic bounds");

namespace 
{
  /*
     Transform loops with constant bounds 

     foo (...) {
       ...
       for (int i=start ;i < 500; i+=k) 
       { ... }
     }

     into symbolic loops of this form

     foo (...) {
       int n = nd ();
       assume (n == 500);
       ....
       for (int i=start ;i < n; i+=k) 
       { ... }
     }
   */
  class SymbolizeConstantLoopBounds : public FunctionPass
  {
   public:
    
    static char ID;
    
   private:
    
    void updateCallGraph (CallGraph* cg, Function* caller, CallInst* callee) {
      if (cg) {
        (*cg)[caller]->addCalledFunction (CallSite (callee),
                                          (*cg)[callee->getCalledFunction ()]);
      }
    }

    CmpInst* getLoopExitCond (BasicBlock* ExitingLoop) {
      TerminatorInst* TI = ExitingLoop->getTerminator ();
      if (BranchInst* BI = dyn_cast<BranchInst> (TI)) {
        if (BI->isConditional ()) {
          return dyn_cast<CmpInst> (BI->getCondition ());
        }
      }
      return nullptr;
    }

   public:

    SymbolizeConstantLoopBounds () : FunctionPass (ID) {} 

    bool runOnFunction (Function &F)
    {
      if (F.isDeclaration () || F.empty ()) return false;

      Module* M = F.getParent ();
      LLVMContext& ctx = M->getContext ();
      Type* voidTy = Type::getVoidTy (ctx);
      Type* boolTy = Type::getInt1Ty (ctx);

      const DataLayout* dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
      Type* intTy = dl->getIntPtrType (ctx, 0);

      IRBuilder<> B (ctx);
      B.SetInsertPoint (F.getEntryBlock ().getFirstInsertionPt ());      

      AttrBuilder AB;        
      AttributeSet as = AttributeSet::get (ctx, AttributeSet::FunctionIndex, AB);

      Function* assumeFn = dyn_cast<Function>
          (M->getOrInsertFunction ("verifier.assume", as, voidTy, boolTy, NULL));                                 

      Function* nondetFn = dyn_cast<Function>
          (M->getOrInsertFunction ("verifier.nondet", as, intTy, NULL));
                                   
      // XXX: I'm not sure the pass needs to a Module pass
      CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
      CallGraph* cg = cgwp ? &cgwp->getCallGraph () : nullptr;
      if (cg) { 
        cg->getOrInsertFunction (assumeFn);
        cg->getOrInsertFunction (nondetFn);
      }
        
      LoopInfo* LI = &getAnalysis<LoopInfo>();      
      bool Change = false;
      for (auto L : boost::make_iterator_range (LI->begin (), LI->end ())) {
        LOG ("sym-bound", errs () << *L << "\n");

        SmallVector<BasicBlock*, 16> ExitingBlocks;
        L->getExitingBlocks (ExitingBlocks);
        for (BasicBlock* ExitingBlock : ExitingBlocks) {

          // We could consider the exiting block only if an induction
          // variable is involved.

          CmpInst* ExitCond = getLoopExitCond (ExitingBlock);
          if (!ExitCond) { 
            LOG ("sym-bound", 
                 errs () << "STC: Skipped exiting block because no condition found\n");            
            continue;
          }
          
          // Assume that only one operand is constant
          Value* CstBound = nullptr;
          if (isa<ConstantInt> (ExitCond->getOperand (0))) 
            CstBound = ExitCond->getOperand (0);
          else if (isa<ConstantInt> (ExitCond->getOperand (1))) 
            CstBound = ExitCond->getOperand (1);

          if (!CstBound) {
            LOG ("sym-bound", 
                 errs () 
                 << "STC: Skipped exiting block because no constant bound found\n";);
            continue;
          }
                      
          LOG ("sym-bound", 
               errs () << "STC: Found loop with constant bound=" << *CstBound << "\n";); 
               
          CallInst* nd = B.CreateCall (nondetFn, "sym_bound");
          Value* symBound = B.CreateSExtOrTrunc (nd, CstBound->getType ()); 
          updateCallGraph (cg, &F, nd);
          CallInst* assumption = B.CreateCall (assumeFn, 
                                               B.CreateICmpEQ (symBound, CstBound));
          updateCallGraph (cg, &F, assumption);

          // --- replace the constant bound with the symbolic one.
          //     We could replace any occurrence of the constant bound
          //     inside the loop or even the function.
          if (ExitCond->getOperand (0) == CstBound) {
            ExitCond->setOperand (0, symBound);
          } else {
            ExitCond->setOperand (1, symBound);
          }

          SymbolizedLoops++;
          Change = true;
        } 
      } 
      
      return Change;
    }

    void getAnalysisUsage (AnalysisUsage &AU) const {
      AU.setPreservesAll();
      AU.addRequired<LoopInfo>();
      AU.addRequired<llvm::DataLayoutPass>();
      AU.addRequired<llvm::CallGraphWrapperPass>();
    }
    
    virtual const char *getPassName () const 
    {return "Convert constant loop bounds into symbolic bounds";}
    
  };

  char SymbolizeConstantLoopBounds::ID = 0;
}

namespace seahorn
{
  Pass *createSymbolizeConstantLoopBoundsPass () 
  {return new SymbolizeConstantLoopBounds ();} 
}

static llvm::RegisterPass<SymbolizeConstantLoopBounds> 
X ("symbolize-constant-loop-bounds", 
   "Convert constant loop bounds into symbolic");
