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


std::vector<std::string> Split(const std::string& str,
                               const std::string& delim) {
  std::vector<std::string> tokens;
  size_t prev = 0, pos = 0;
  do {
    pos = str.find(delim, prev);
    if (pos == std::string::npos)
      pos = str.length();
    std::string token = str.substr(prev, pos - prev);
    if (!token.empty())
      tokens.push_back(token);
    prev = pos + delim.length();
  } while (pos < str.length() && prev < str.length());
  return tokens;
}

std::vector<std::string> SplitSpaceTabEnter(const std::string& str) {
  std::vector<std::string> result;
  std::istringstream iss(str);
  for (std::string s; iss >> s;)
    result.push_back(s);
  return result;
}

std::string Join(const std::vector<std::string>& in, const std::string& delim) {
  std::string ret;
  std::string d = "";
  for (auto&& s : in) {
    ret += (d + s);
    d = delim;
  }
  return ret;
}


// unsigned bw_bound = 128, unsigned bval_bound = 2, bool enable_eqs = 1, bool enable_adds = 1, bool enable_bvnot = 0, bool enable_extract = 1, bool enable_concr = 1, bool enable_concr_impl = 0, bool enable_or = 1

int main (int argc, char ** argv)
{
  std::set<std::string> no_enum_variable_name;
  cross_bw_hints_t bit_select_hints;

  { // load variable name if it is specified
    std::string vnames;
    vnames = getStringValue("--no-const-enum-vars-on", "", argc,argv);
    if (!vnames.empty() ) {
      auto no_enum_var_vec = Split(vnames,",");
      for (const auto & p : no_enum_var_vec)
        no_enum_variable_name.insert(p);
    }
  }

  { // load variable name if it is specified
    std::string bitselect;
    bitselect = getStringValue("--bit-select-hints", "", argc,argv);
    if (!bitselect.empty() ) {
      auto bitsels = Split(bitselect,",");
      for (auto pos = bitsels.begin(); pos < bitsels.end(); pos += 2) {
        unsigned width = stoi(*(pos)), lsb = stoi(*(pos+1));
        if (bit_select_hints.find(width) == bit_select_hints.end())
          bit_select_hints.insert(std::make_pair(width, std::set<unsigned>()));
        bit_select_hints.at(width).insert(lsb);
      }
    }
  }

  std::vector<std::string> forced_states;
  { // state file
    auto state_list = getStringValue("--force-state-list", "", argc,argv);
    if (!state_list.empty()) 
      forced_states = Split(state_list,",");

    auto state_list_file = getStringValue("--force-state-file", "", argc,argv);
    if (!state_list_file.empty()){
      std::ifstream fin(state_list_file);
      if (fin.is_open()) {
        std::string line;
        while(std::getline(fin,line)) {
          forced_states.push_back(line);
        }
      } else {
        outs () << "unable to read from " << state_list_file <<"\n";
      }
    }
  }

  std::map<std::string, std::set<unsigned> > var_s_const;
  { // var to const
    auto var_const_fn = getStringValue("--var-const-file", "", argc,argv);
    if (!var_const_fn.empty()) {
      std::ifstream fin(var_const_fn);
      if (fin.is_open()) {
        unsigned nvars;
        fin >> nvars;
        for (unsigned idx = 0; idx < nvars; ++ idx) {
          std::string sname; unsigned const_num;
          fin >> sname >> const_num;
          if (var_s_const.find(sname) == var_s_const.end())
            var_s_const.insert(std::make_pair(sname, std::set<unsigned>()));
          for (unsigned cidx = 0; cidx < const_num; ++ cidx) {
            unsigned c; fin >> c; var_s_const[sname].insert(c);
          }
        }
      }else {
        outs () << "unable to read from " << var_const_fn <<"\n";
      }
    }
  }

  
  


  simpleCheck(argv[argc-1], getIntValue("--bw", 128, argc, argv),
              getIntValue("--cw", 16, argc, argv),
              getIntValue("--ante-size", 4, argc, argv),
              getIntValue("--conseq-size", 4, argc, argv),
              getStringValue("--cnf", "", argc, argv),
              getBoolValue("--skip-cnf", false, argc, argv),
              getBoolValue("--skip-const-check", false, argc, argv),
              getBoolValue("--shift-extract", false, argc, argv),
              getBoolValue("--use-arith-add-sub", false, argc, argv),
              getBoolValue("--cross-bw", false, argc, argv),
              getBoolValue("--skip-stat-collect", false, argc, argv),
              getBoolValue("--gen-spec-only", false, argc, argv), // only use generalization/specification candidates
              getBoolValue("--force-bit-select-hint", false, argc, argv),
              getIntValue("--check-cand-per-cl-max", 0, argc, argv),
              var_s_const,
              forced_states,
              
              no_enum_variable_name,
              bit_select_hints,
              getBoolValue("--debug", false, argc, argv)
              );
  return 0;
}
