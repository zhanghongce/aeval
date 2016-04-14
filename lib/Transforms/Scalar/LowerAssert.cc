#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/CallGraph.h"

#include "llvm/Support/raw_ostream.h"
#include "avy/AvyDebug.h"

using namespace llvm;

/* Replace assertions to calls to assume */

namespace seahorn
{

  struct LowerAssert : public ModulePass
  {
    static char ID;
    
    Function *assumeFn;
    
    LowerAssert () : ModulePass (ID) {}
      
    bool runOnModule (Module &M);
    
    bool runOnFunction (Function &F);
    
    void getAnalysisUsage (AnalysisUsage &AU) const
    {AU.setPreservesAll ();}
    
    virtual const char* getPassName () const 
    {return "LowerAssert";}
  };

  bool LowerAssert::runOnModule (Module &M)
  {

    LLVMContext &Context = M.getContext ();
    
    AttrBuilder B;
    
    AttributeSet as = AttributeSet::get (Context, 
                                         AttributeSet::FunctionIndex,
                                         B);
    
    assumeFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.assume", 
                                as,
                                Type::getVoidTy (Context),
                                Type::getInt1Ty (Context),
                                NULL));
    
    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
    if (CallGraph *cg = cgwp ? &cgwp->getCallGraph () : nullptr) {
      cg->getOrInsertFunction (assumeFn);
    }
    
    bool Changed = false;
    for (auto &F : M) 
      Changed |= runOnFunction (F);
    return Changed;
  }


  // // Return the Value that only when evaluated to true then I is
  // // executed. Otherwise, it return null.
  // Value* getDominantCondition (Instruction *I) {
  //   if (BasicBlock* PB = I->getParent()->getSinglePredecessor ()) {
  //     TerminatorInst* TI = PB->getTerminator ();
  //     if (BranchInst* BI = dyn_cast<BranchInst> (TI)) {
  //       if (BI->isConditional ())
  //         return BI->getCondition ();
  //     }
  //   }
  //   return nullptr;
  // }
            
  bool LowerAssert::runOnFunction (Function &F)
  {
    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
    CallGraph* cg = cgwp ? &cgwp->getCallGraph () : nullptr;
    IRBuilder<> B (F.getContext()); 
   
    std::vector<CallInst*> Worklist;
    for (auto &BB : F)
      for (auto &I : BB)
      {
        CallInst *CI = dyn_cast<CallInst> (&I);
        if (!CI) continue;
        Function* CF = CI->getCalledFunction ();
        if (!CF) continue;
        
        if (CF->getName ().equals ("verifier.assert")) {
          // verifier assert
          Worklist.push_back (CI);
        }
        else if (CF->getName ().equals ("__assert_fail")) {
          // assert from assert.h is translated to __assert_fail
          Worklist.push_back (CI);
        } else if (CF->getName ().equals ("verifier.error")) {
          // verifier error
          Worklist.push_back (CI);
        }
      }    
        
    if (Worklist.empty ()) return true;
      
    while (!Worklist.empty()) 
    {
      CallInst* CI = Worklist.back();
      Worklist.pop_back();

      Function* CF = CI->getCalledFunction ();
      
      if (CF->getName ().equals ("verifier.assert")) 
      {
        CallSite CS (CI);
        Value* Cond = CS.getArgument(0);
        CallInst* NCI = CallInst::Create (assumeFn, 
                                          B.CreateZExtOrTrunc (Cond, 
                                                               Type::getInt1Ty (F.getContext())));
        NCI->setDebugLoc (CI->getDebugLoc ());

        LOG ("lower-assert",
             errs () << "Replaced " << *CI << " with " << *NCI << "\n");
        
        ReplaceInstWithInst (CI,  NCI);

        if (cg)
          (*cg)[&F]->addCalledFunction (CallSite (NCI),
                                        (*cg)[NCI->getCalledFunction ()]);
      }
      else if (CF->getName ().equals ("__assert_fail") || 
               CF->getName ().equals ("verifier.error")) 
      {
        CallInst* NCI = CallInst::Create (assumeFn, ConstantInt::getFalse(F.getContext()));
        NCI->setDebugLoc (CI->getDebugLoc ());

        LOG ("lower-assert",
             errs () << "Replaced " << *CI << " with " << *NCI << "\n");

        ReplaceInstWithInst (CI,  NCI);

        if (cg)
          (*cg)[&F]->addCalledFunction (CallSite (NCI),
                                        (*cg)[NCI->getCalledFunction ()]);
      }
    }

    return true;
  }


  char LowerAssert::ID = 0;

  Pass* createLowerAssertPass ()
  { return new LowerAssert (); }

}

