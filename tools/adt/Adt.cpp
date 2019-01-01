#include "adt/ADTSolver.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace ufo;

char * getStrValue(const char * opt, const char * defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return argv[i+1];
    }
  }
  return (char *)defValue;
}

char * getSmtFileName(int num, int argc, char ** argv)
{
  int num1 = 1;
  for (int i = 1; i < argc; i++)
  {
    int len = strlen(argv[i]);
    if (len >= 5 && strcmp(argv[i] + len - 5, ".smt2") == 0)
    {
      if (num1 == num) return argv[i];
      else num1++;
    }
  }
  return NULL;
}


bool PrintExpr(Expr e)
{
  outs()<<*e;
  return false;
}

int main (int argc, char ** argv)
{
  ExprFactory efac;
  EZ3 z3(efac);
  char *infile = getSmtFileName(1, argc, argv);
  char *basecheck = getStrValue("--base", NULL, argc, argv);
  char *indcheck = getStrValue("--ind", NULL, argc, argv);
  
  Config cfg(argc, argv);
  
  Expr e = z3_from_smtlib_file (z3, infile);
  adtSolve(z3, e, basecheck, indcheck, cfg);

  return 0;
}
