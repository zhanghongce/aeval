#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

#include "seahorn/Transforms/Utils/SliceFunctions.hh"

#include <set>
#include <vector>

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>

using namespace std;

static llvm::cl::list<std::string>
    FunctionNames("slice-function-names",
                  llvm::cl::desc("Slice program onto these functions"),
                  llvm::cl::ZeroOrMore);

namespace seahorn {
using namespace llvm;

bool SliceFunctions::runOnModule(Module &M) {

  std::set<Function *> funcs;
  for (std::string fname : FunctionNames) {
    Function *F = M.getFunction(fname);
    if (!F) {
      // errs() << "Warning: " << fname
      //        << " not found. No functions will be removed.\n";
      errs() << "INC_INFO";
      printFunctionsInfo(M, fname);
      return false;
    }
    funcs.insert(F);
  }

  if (funcs.empty ())
    return false;

  bool Change = false;
  // Delete function bodies and set external linkage
  for (Function &F : M) {
    if (F.isDeclaration())
      continue;
    if (funcs.count(&F) > 0)
      continue;

    F.deleteBody();
    Change = true;
  }

  // Delete global aliases
  // Aliases cannot point to a function declaration so if there is
  // an alias to a removed function we also need to remove all its
  // aliases.
  std::vector<GlobalAlias *> aliases;
  for (GlobalAlias &GA : M.aliases()) {
    aliases.push_back(&GA);
  }

  for (GlobalAlias *GA : aliases) {
    if (Function *aliasee = dyn_cast<Function>(GA->getAliasee())) {
      if (!(funcs.count(aliasee) > 0)) {
        GA->replaceAllUsesWith(aliasee);
        M.getAliasList().erase(GA);
        Change = true;
      }
    }
  }

  // Remove main if user says so. This means that DummyMain
  // function must be run later otherwise the whole module will be
  // empty.
  Function *main = M.getFunction("main");
  if (main && !(funcs.count(main) > 0)) {
    main->dropAllReferences();
    main->eraseFromParent();
    Change = true;
  }

  return Change;
}

void SliceFunctions::getAnalysisUsage(AnalysisUsage &AU) {
  AU.setPreservesAll();
  AU.addRequired<llvm::CallGraphWrapperPass>();
}

void SliceFunctions::printFunctionsInfo(Module &M, string fname) {

  CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass>();
  CallGraph *CG = cgwp ? &cgwp->getCallGraph() : nullptr;
  ofstream file_out;
  // file_out.open(fname+"_info.txt");
  std::stringstream info;

  if (CG) {
    // errs () << "==== Recursive functions ==== \n";
    // bool has_rec_func = false;
    // for (auto it = scc_begin (CG); !it.isAtEnd (); ++it) {
    //   auto &scc = *it;
    //   if (std::distance (scc.begin (), scc.end ()) > 1) {
    //     has_rec_func = true;
    //     errs () << "SCC={";
    //     for (CallGraphNode *cgn : scc) {
    //       if (cgn->getFunction ())
    //         errs () << cgn->getFunction ()->getName () << ";";
    //     }
    //   }
    // }
    // if (!has_rec_func) errs () << "None\n";

    typedef std::pair<Function *, std::pair<unsigned, unsigned>> func_ty;
    std::vector<func_ty> funcs;
    // errs() << "=== Call graph and function information === \n";
    // errs() << "TOTAL NUM of FUNCTIONS=" << std::distance(M.begin(), M.end())
    //        << "\n";
    info << "FUNS_INFO :  \n\t{";
    info << "\t NUM_FUNCS: " << std::to_string(std::distance(M.begin(), M.end())) << ",";
    for (auto it = scc_begin(CG); !it.isAtEnd(); ++it) {
      auto &scc = *it;
      for (CallGraphNode *cgn : scc) {
        if (cgn->getFunction() && !cgn->getFunction()->isDeclaration()) {
          funcs.push_back(std::make_pair(
              cgn->getFunction(),
              std::make_pair(cgn->getNumReferences(),
                             std::distance(cgn->begin(), cgn->end()))));
        }
      }
    }

    std::sort(funcs.begin(), funcs.end(), [](func_ty p1, func_ty p2) {
      return (p1.second.first + p1.second.second) >
             (p2.second.first + p2.second.second);
    });

    for (auto &p : funcs) {
      Function *F = p.first;
      unsigned numInsts = std::distance(inst_begin(F), inst_end(F));
      // errs() << "\t" << F->getName() << " --- NUM INST=" << numInsts
      //        << " CALLERS=" << p.second.first << " CALLEES=" << p.second.second
      //        << "\n";
      std::string fn = F->getName();
      info << "\t" << fn << ": {INST: " + std::to_string(numInsts)
             << ", CALLERS: " << std::to_string(p.second.first)
             << ", CALLEES:" << std::to_string(p.second.second)
             << "},\n";
    }
  } else {
    // errs () << "Call graph not found.\n";
    info << "{FUNCS_INFO : \n\t{";
    // errs() << "=== Function information === \n";
    // errs() << "TOTAL NUM of FUNCTIONS=" << std::distance(M.begin(), M.end())
    //        << "\n";
    info << "\t NUM_FUNCS: " << std::to_string(std::distance(M.begin(), M.end())) << ",\n";
    for (auto &F : M) {
      unsigned numInsts = std::distance(inst_begin(&F), inst_end(&F));
      std::string fn = F.getName();
      errs() << "INC | " << F.getName()
             << " | " << std::distance(F.begin(), F.end())
             << " | " << numInsts << "\n";
      info << "\t" << fn
           << ":{ BLOCKS: " << std::to_string(std::distance(F.begin(), F.end()))
           << ", INST: " << std::to_string(numInsts) + "},\n";
    }
  }
  // info << "\t}\n}";
  // std::string info_s = info.str();
  // file_out << info_s;
  // file_out.close();

}

char SliceFunctions::ID = 0;

static llvm::RegisterPass<SliceFunctions>
    X("slice-functions", "Slice program onto some selected functions");
}
