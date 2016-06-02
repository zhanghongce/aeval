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

  // Return a pair of a branch B and a Boolean V such that I is
  // reachable if the condition of B evaluates to V.
  //
  // Post: the branch is conditional and its condition is either
  // CmpInst or ConstantInt
  std::pair<BranchInst*, bool> getDominantBranch(BasicBlock *B) {
    // Skip all the single predecessors to find the branch that
    // dominates B
    BasicBlock *Parent = B->getSinglePredecessor();
    if (Parent && Parent->getSinglePredecessor()) {
      TerminatorInst* TI = Parent->getTerminator ();
      if (BranchInst* BI = dyn_cast<BranchInst> (TI)) {
        if (!BI->isConditional ())
          return getDominantBranch(Parent);
      }
    }
    
    if (Parent) { 
      TerminatorInst* TI = Parent->getTerminator ();
      if (BranchInst* BI = dyn_cast<BranchInst> (TI)) {
        if (BI->isConditional ()) {
          Value* BICond = BI->getCondition();
          if (isa<CmpInst>(BICond) || isa<ConstantInt>(BICond))
            return std::make_pair(BI, (BI->getSuccessor(0)==B));
        }
      }
    }
    return std::make_pair(nullptr, false);
  }

  CmpInst* inverseCmpInst (CmpInst* CI) {
    return CmpInst::Create(CI->getOpcode(), CI->getInversePredicate(), 
                           CI->getOperand(0), CI->getOperand(1), "", CI);
  }
            
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

        auto p = getDominantBranch(CI->getParent());
        if (!(p.first)) {
          llvm::errs () << "lower-assert: " << *CI 
                        << " could not be lowered to an assume instruction.\n";
          continue;
        }

        if (const ConstantInt *CI = dyn_cast<const ConstantInt>(p.first->getCondition())) {
          if ((CI->isOne() && p.second) || (CI->isZero() && !p.second)) { 
            // error is definitely reachable
            llvm::errs () << "lower-assert: " << *CI 
                          << " could not be lowered to an assume instruction.\n";
            llvm::errs () << "Moreover, an error location seems to be reachable!\n";
          } 
          // otherwise the call to verifier.error is dead code.
          continue;
        }

        Value* assumeCond = p.first->getCondition();
        if (p.second) { 
          // here error is reachable if the branch condition is true.
          // Replace with assume(not condition)
          assumeCond = inverseCmpInst(cast<CmpInst>(p.first->getCondition()));
          assumeCond->setName(p.first->getCondition()->getName());
        } 

        // convert the conditional branch into an unconditional one
        if (p.second) // error is reachable if the branch condition is true
          p.first->setCondition(ConstantInt::getFalse(F.getContext()));
        else // error is reachable if the branch condition is false
          p.first->setCondition(ConstantInt::getTrue(F.getContext()));
 
        
        CallInst* NCI = CallInst::Create(assumeFn, assumeCond, "", p.first);
        NCI->setDebugLoc (p.first->getDebugLoc ());

        LOG ("lower-assert",
             errs () << "Replaced " << *CI << " with " << *NCI << "\n");

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

