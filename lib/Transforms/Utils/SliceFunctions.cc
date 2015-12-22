#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

#include <boost/range.hpp>

#include "seahorn/Transforms/Utils/SliceFunctions.hh"

#include <set>
#include <vector>

static llvm::cl::list<std::string> 
FunctionNames("slice-functions", 
               llvm::cl::desc ("Slice the whole program onto wrt to these functions"),
               llvm::cl::ZeroOrMore);

namespace seahorn
{
    using namespace llvm;

    bool SliceFunctions::runOnModule (Module &M)
    {
      // sanity check
      for (auto f: boost::make_iterator_range (FunctionNames.begin (),
                                               FunctionNames.end ())) {
        if (!M.getFunction (f)) {
          errs () << "Function " << f << " not found in module."
                  << " No functions will be removed.\n";
          errs () << "These are the (non-declaration) module's functions: \n";
          for (auto &F : M) {
            if (!F.isDeclaration ())
              errs () << F.getName () << "\n";
          }
          return false;
        }
      }
      
      if (FunctionNames.begin () == FunctionNames.end ())
        return false;
      
      std::set <std::string> funcs (FunctionNames.begin (), FunctionNames.end ());
      
      // Find the set of functions to be removed 
      std::vector<Function*> Worklist;
      for (Function &F : M) {
        if (F.isDeclaration ()) continue;
        
        if (!(funcs.count (F.getName ()) > 0))
          Worklist.push_back (&F);
      }
      
      // Collect the function declarations from the functions that can
      // be called by the slice callee functions by the slice.
      typedef std::pair <StringRef, FunctionType*> FunctionInfo;
      std::vector< FunctionInfo > callee_decls;
      for (auto F: Worklist) {
        for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
          // only direct calls
          if (CallInst *CI = dyn_cast <CallInst> (&*I)) {
            CallSite CS (CI);
            if (Function* Callee = CS.getCalledFunction ()) {
              callee_decls.push_back ( FunctionInfo (Callee->getName (), 
                                                     Callee->getFunctionType ()));
            }
          }
        }
      }

      // Remove the functions. During this the bitecode won't be well formed.
      for (auto F: Worklist) 
        F->eraseFromParent ();
      
      // Finally, add the declarations to make the bitecode well formed.
      for (auto decl : callee_decls)
        M.getOrInsertFunction (decl.first, decl.second);

      return true;
    }

    char SliceFunctions::ID = 0;
}
