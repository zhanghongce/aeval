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

int main (int argc, char ** argv)
{
  simpleCheck(argv[1]);
  return 0;
}
