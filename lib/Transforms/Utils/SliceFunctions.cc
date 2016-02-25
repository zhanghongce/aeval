#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

#include <boost/range.hpp>

#include "seahorn/Transforms/Utils/SliceFunctions.hh"

#include <set>
#include <vector>

static llvm::cl::list<std::string> 
FunctionNames("slice-functions", 
               llvm::cl::desc ("Set of functions to be kept"),
               llvm::cl::ZeroOrMore);

namespace seahorn
{
    using namespace llvm;

    void SliceFunctions::printModuleInfo (Module& M){

      CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
      CallGraph* CG = cgwp ? &cgwp->getCallGraph () : nullptr;

      if (CG) {
        errs () << "--- Recursive functions \n";
        bool has_rec_func = false;
        for (auto it = scc_begin (CG); !it.isAtEnd (); ++it) {
          auto &scc = *it;
          if (std::distance (scc.begin (), scc.end ()) > 1) {
            has_rec_func = true;
            errs () << "SCC={";
            for (CallGraphNode *cgn : scc) {
              if (cgn->getFunction ())
                errs () << cgn->getFunction ()->getName () << ";";
            }
          }
        }
        if (!has_rec_func) errs () << "None\n";
        
        typedef std::pair <Function*, std::pair <unsigned, unsigned> > func_ty;
        std::vector<func_ty> funcs;
        errs () << "--- Call graph information \n";
        for (auto it = scc_begin (CG); !it.isAtEnd (); ++it) {
          auto &scc = *it;
          for (CallGraphNode *cgn : scc) {
            if (cgn->getFunction () && !cgn->getFunction ()->isDeclaration ()) {
              funcs.push_back (std::make_pair (cgn->getFunction (), 
                                    std::make_pair (cgn->getNumReferences (), 
                                                    std::distance (cgn->begin (), cgn->end ()))));
            }
          }
        }
        
        std::sort (funcs.begin(), funcs.end (), 
                   [](func_ty p1, func_ty p2) { 
                     return   (p1.second.first + p1.second.second) > 
                         (p2.second.first + p2.second.second);
                   });
        
        for (auto&p: funcs){
          Function* F = p.first;
          unsigned numInsts = std::distance (inst_begin(F), inst_end(F));
          errs () << F->getName () 
                  << " num of insts=" << numInsts
                  << " callers=" << p.second.first 
                << " callees=" << p.second.second << "\n";
        }                                   
      } else {
        errs () << "Call graph not found.\n";
        for (auto &F: M){
          unsigned numInsts = std::distance (inst_begin(&F), inst_end(&F));
          errs () << F.getName () << " num of insts=" << numInsts << "\n";
        }
      }
    }


    bool SliceFunctions::runOnModule (Module &M)
    {

      printModuleInfo (M);

      // sanity check
      for (auto f: boost::make_iterator_range (FunctionNames.begin (),
                                               FunctionNames.end ())) {
        if (!M.getFunction (f)) {
          errs () << "Function " << f << " not found in module."
                  << " No functions will be removed.\n";
          // errs () << "These are the (non-declaration) module's functions: \n";
          // for (auto &F : M) 
          //   if (!F.isDeclaration ()) 
          //     errs () << F.getName () << "\n";
          return false;
        }
      }
      
      if (FunctionNames.begin () == FunctionNames.end ())
        return false;
      
      std::set <std::string> funcs (FunctionNames.begin (), 
                                    FunctionNames.end ());

      // Delete bodies
      for (Function &F : M) {
        if (F.isDeclaration ()) continue;
        if (funcs.count (F.getName ()) > 0) continue;
        
        F.deleteBody ();
      }

      // Remove main if user says so. This means that DummyMain
      // function must be run later otherwise the whole module will be
      // empty.
      if (!(funcs.count ("main") > 0)) {
        Function* main = M.getFunction ("main");
        main->dropAllReferences ();
        main->eraseFromParent ();
      }
      
      return true;
    }

    void SliceFunctions::getAnalysisUsage (AnalysisUsage &AU) 
    { 
      AU.setPreservesAll (); 
      AU.addRequired<llvm::CallGraphWrapperPass>();
    }

    char SliceFunctions::ID = 0;
}
