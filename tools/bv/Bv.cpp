#include "deep/CandChecker.hpp"


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

std::string getStringValue(const char * opt, const std::string & defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return (argv[i+1]);
    }
  }
  return defValue;
}

bool loadVariableNamesFromFile(const std::string fname, std::set<std::string> & var_set) {
  std::ifstream fin(fname);
  if (!fin.is_open()) {
    return false;
  }
  std::string line;
  while(getline(fin,line)) {
    var_set.insert("S_" + line);
  }
}

// unsigned bw_bound = 128, unsigned bval_bound = 2, bool enable_eqs = 1, bool enable_adds = 1, bool enable_bvnot = 0, bool enable_extract = 1, bool enable_concr = 1, bool enable_concr_impl = 0, bool enable_or = 1

int main (int argc, char ** argv)
{
  std::set<std::string> variable_name_set;

  { // load variable name if it is specified
    std::string fname;
    fname = getStringValue("--vnames-file", "", argc,argv);
    if (!fname.empty() )
      loadVariableNamesFromFile(fname, variable_name_set);
  }

  simpleCheck(argv[argc-1], getIntValue("--bw", 128, argc, argv),
              getIntValue("--ante-size", 4, argc, argv),
              getIntValue("--conseq-size", 4, argc, argv),
              getStringValue("--cnf", "", argc, argv),
              getBoolValue("--skip-cnf", false, argc, argv),
              getBoolValue("--skip-const-check", false, argc, argv),
              getBoolValue("--shift-extract", false, argc, argv),
              getBoolValue("--use-arith-add-sub", false, argc, argv),


              getBoolValue("--debug", false, argc, argv)
              );
  return 0;
}
