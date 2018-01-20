#include "deep/TermCheck.hpp"

using namespace ufo;
using namespace std;

bool getBoolValue(const char * opt, bool defValue, int * argc, char ** argv)
{
  for (int i = 1; i < *argc; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      std::copy(argv + i + 1, argv + *argc, argv + i);
      (*argc)--;
      return true;
    }
  }
  return defValue;
}

bool getBoolValue(const char * opt, const char * opt2, bool defValue, int * argc, char ** argv)
{
  for (int i = 1; i < *argc - 1; i++)
  {
    if (strcmp(argv[i], opt) == 0 && strcmp(argv[i+1], opt2) == 0)
    {
      std::copy(argv + i + 2, argv + *argc, argv + i);
      *argc = *argc - 2;
      return true;
    }
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int * argc, char ** argv)
{
  for (int i = 1; i < *argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      int res = atoi(argv[i+1]);
      std::copy(argv + i + 2, argv + *argc, argv + i);
      *argc = *argc - 2;
      return res;
    }
  }
  return defValue;
}

int main (int argc, char ** argv)
{
  if (getBoolValue("--help", false, &argc, argv) || argc < 2){
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
    " --solver <spacer|freqhorn|muz>       solver to confirm ranking function\n" <<  // GF: kind is disabled for now
    "                                      or universal nontermination\n" <<
    " --transform <NUM>                    pre-transform the inductive rule by grouping `NUM` bodies\n" <<
    " --lightweight                        sacrifice deep preprocessing (for big programs)\n" <<
    "                                      and check candidates one-by-one\n" <<
    " --cex                                use counter-examples to accelerate the search\n";

    return 0;
  }

  int nonterm = getIntValue("--nonterm", 3, &argc, argv);
  int rank = getIntValue("--rank", 3, &argc, argv);
  int mrg = getIntValue("--transform", 0, &argc, argv);
  int lw = getBoolValue("--lightweight", false, &argc, argv);
  int cex = getBoolValue("--cex", false, &argc, argv);

  int sp = getBoolValue("--solver", "spacer", false, &argc, argv);
  int mu = getBoolValue("--solver", "muz", false, &argc, argv);
  int fr = getBoolValue("--solver", "freqhorn", false, &argc, argv);
  int ki = getBoolValue("--solver", "kind", false, &argc, argv);

  if (sp + fr + ki + mu > 1)
  {
    outs() << "Only one solver could be chosen\n";
    return 0;
  }

  if (sp + fr + ki == 0) fr = 1;

  solver slv;
  if (sp > 0) slv = spacer;
  else if (mu > 0) slv = muz;
  else if (fr > 0) slv = freqhorn;
  else slv = kind;

  if (argc > 2)
  {
    outs () << "Could not parse some of the following options: ";
    for (int i = 1; i < argc; i++) outs () << "\"" << argv[i] << "\", ";
    outs () << "\n";
    return 0;
  }

  if (nonterm == 0 && rank == 0)
  {
    outs() << "All fun is skipped\n";
    return 0;
  }

  std::ifstream infile(argv[argc-1]);
  if (!infile.good())
  {
    outs() << "Could not read file \"" << argv[argc-1] << "\"\n";
    return 0;
  }

  terminationAnalysis(string(argv[argc-1]), nonterm, rank, mrg, slv, lw, cex);

  return 0;
}
