#ifndef SLICE_FUNCTIONS_H
#define SLICE_FUNCTIONS_H

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"

namespace seahorn
{
  using namespace llvm;
  
  struct SliceFunctions : public ModulePass
  {
    static char ID;

    SliceFunctions (): ModulePass (ID) {}
    
    bool runOnModule (Module &M);

    void getAnalysisUsage (AnalysisUsage &AU)
    {AU.setPreservesAll ();}

  };
}

#endif 
