#include "deep/TermCheck.hpp"

using namespace ufo;
using namespace std;

bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return atoi(argv[i+1]);
    }
  }
  return defValue;
}

int main (int argc, char ** argv)
{
  if (getBoolValue("--help", false, argc, argv) || argc < 2){
    outs () <<
    "* * *                         FreqTerm v.0.1 - Copyright (C) 2017                         * * *\n" <<
    "                                      Grigory Fedyukovich                                      \n\n" <<
    "Usage:                              Purpose:\n" <<
    " term [--help]                        show help\n" <<
    " term <chc.smt2>                      prove (non-)termination, where\n" <<
    "                                      `chc.smt2` - system of CHCs\n\n" <<
    "Options:\n" <<
    " --nonterm <NUM>                      level of search for nonterminating refinements:\n" <<
    "                                      the higher level, the deeper search\n" <<
    " --rank <0|1|2|3>                     level of search for ranking functions:\n" <<
    "                                      0 - none, 1 - counter, 2 - lexicographic, 3 - both\n" <<
    " --solver <spacer|freqhorn>           solver to confirm ranking function\n" <<  // GF: kind is disabled for now
    "                                      or universal nontermination\n" <<
    " --transform <NUM>                    pre-transform the inductive rule by grouping `NUM` bodies\n" <<
    " --lightweight                        sacrifice deep preprocessing (for big programs)\n";

    return 0;
  }

  int nonterm = getIntValue("--nonterm", 3, argc, argv);
  int rank = getIntValue("--rank", 3, argc, argv);
  int mrg = getIntValue("--transform", 0, argc, argv);
  int lw = getBoolValue("--lightweight", false, argc, argv);

  int sp = getBoolValue("spacer", false, argc, argv);
  int fr = getBoolValue("freqhorn", false, argc, argv);
  int ki = getBoolValue("kind", false, argc, argv);

  if (sp + fr + ki > 1)
  {
    outs() << "Only one solver could be chosen\n";
    return 0;
  }

  if (sp + fr + ki == 0) fr = 1;

  solver slv;
  if (sp > 0) slv = spacer;
  else if (fr > 0) slv = freqhorn;
  else slv = kind;

  if (nonterm == 0 && rank == 0)
  {
    outs() << "All fun is skipped\n";
    return 0;
  }

  terminationAnalysis(string(argv[argc-1]), nonterm, rank, mrg, slv, lw);

  return 0;
}
