#ifndef SLICE_FUNCTIONS_H
#define SLICE_FUNCTIONS_H

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"

namespace seahorn
{
  using namespace llvm;
  
  class SliceFunctions : public ModulePass
  {
    void printFunctionsInfo (Module& M);

   public:

    static char ID;

    SliceFunctions (): ModulePass (ID) {}
    
    virtual bool runOnModule (Module &M);

    virtual void getAnalysisUsage (AnalysisUsage &AU);

    virtual const char* getPassName () const override 
    {return "SliceFunctions";}  

  };
}

#endif 
