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


std::set<std::string> Split2Set(const std::string& str,
                               const std::string& delim) {
  std::set<std::string> tokens;
  size_t prev = 0, pos = 0;
  do {
    pos = str.find(delim, prev);
    if (pos == std::string::npos)
      pos = str.length();
    std::string token = str.substr(prev, pos - prev);
    if (!token.empty())
      tokens.insert(token);
    prev = pos + delim.length();
  } while (pos < str.length() && prev < str.length());
  return tokens;
}


/// Replace all occurrance of substring a by substring b
std::string ReplaceAll(const std::string& str, const std::string& a,
                       const std::string& b) {
  std::string result;
  size_t find_len = a.size();
  size_t pos, from = 0;
  while (std::string::npos != (pos = str.find(a, from))) {
    result.append(str, from, pos - from);
    result.append(b);
    from = pos + find_len;
  }
  result.append(str, from, std::string::npos);
  return result;
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
  std::map<std::string, std::set<unsigned> > var_s_const;

  // ----------------------- LOADING UNITFIED CONFIGS ---------------------- //
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
  // ----------------------- LOADING CTRL CONFIGS ---------------------- //

  std::set<std::string> ctrl_no_enum_variable_name;
  cross_bw_hints_t ctrl_bit_select_hints;
  std::map<std::string, std::set<unsigned> > ctrl_var_s_const;
  { // load variable name if it is specified
    std::string vnames;
    vnames = getStringValue("--ctrl-no-const-enum-vars-on", "", argc,argv);
    if (!vnames.empty() ) {
      auto no_enum_var_vec = Split(vnames,",");
      for (const auto & p : no_enum_var_vec)
        ctrl_no_enum_variable_name.insert(p);
    }
  }

  { // load variable name if it is specified
    std::string bitselect;
    bitselect = getStringValue("--ctrl-bit-select-hints", "", argc,argv);
    if (!bitselect.empty() ) {
      auto bitsels = Split(bitselect,",");
      for (auto pos = bitsels.begin(); pos < bitsels.end(); pos += 2) {
        unsigned width = stoi(*(pos)), lsb = stoi(*(pos+1));
        if (ctrl_bit_select_hints.find(width) == ctrl_bit_select_hints.end())
          ctrl_bit_select_hints.insert(std::make_pair(width, std::set<unsigned>()));
        ctrl_bit_select_hints.at(width).insert(lsb);
      }
    }
  }
  { // var to const
    auto var_const_fn = getStringValue("--ctrl-var-const-file", "", argc,argv);
    if (!var_const_fn.empty()) {
      std::ifstream fin(var_const_fn);
      if (fin.is_open()) {
        unsigned nvars;
        fin >> nvars;
        for (unsigned idx = 0; idx < nvars; ++ idx) {
          std::string sname; unsigned const_num;
          fin >> sname >> const_num;
          if (ctrl_var_s_const.find(sname) == ctrl_var_s_const.end())
            ctrl_var_s_const.insert(std::make_pair(sname, std::set<unsigned>()));
          for (unsigned cidx = 0; cidx < const_num; ++ cidx) {
            unsigned c; fin >> c; ctrl_var_s_const[sname].insert(c);
          }
        }
      }else {
        outs () << "unable to read from " << var_const_fn <<"\n";
      }
    }
  }

  // ----------------------- LOADING GRAMMARS ---------------------- //

  std::set<std::string> CSvar, COvar, DIvar, DOvar;
  std::vector<std::set<std::string>> Groupings;
  { // load grammar
    auto grammar_file = getStringValue("--grammar", "", argc,argv);
    vector<string> ConseqPredNames, AntePredNames;
    std::string CSnames, CInames, COnames, DInames, DOnames;
    std::string Group;
    if (!grammar_file.empty())
    {
      string buf;
      ifstream gf(grammar_file);
      while (gf.good())
      {
        getline(gf, buf);
        if (buf.substr(0, 12) == "CTRL-STATE: ") CSnames += buf.substr(12);
        else if (buf.substr(0, 9) == "CTRL-IN: ") CInames += buf.substr(9);
        else if (buf.substr(0, 10) == "CTRL-OUT: ") COnames += buf.substr(10);
        else if (buf.substr(0, 9) == "DATA-IN: ") DInames += buf.substr(9);
        else if (buf.substr(0, 10) == "DATA-OUT: ") DOnames += buf.substr(10);
        else if (buf.substr(0, 11) == "CONS-PRED: ") ConseqPredNames.push_back(buf.substr(11));
        else if (buf.substr(0, 11) == "ANTE-PRED: ") AntePredNames.push_back(buf.substr(11));
        else if (buf.substr(0, 11) == "VAR-GROUP: ") Groupings.push_back( Split2Set(ReplaceAll(buf.substr(11)," ", ""), ",") );
      }
    }
    CSvar = Split2Set(ReplaceAll(CSnames," ", ""), ",");
    COvar = Split2Set(ReplaceAll(COnames," ", ""), ",");
    DIvar = Split2Set(ReplaceAll(DInames," ", ""), ",");
    DOvar = Split2Set(ReplaceAll(DOnames," ", ""), ",");
  } // end -- load grammar ile
  
  
  CDParameters DParam;
  {
    DParam.bw_bound =     getIntValue( "--bw", 128, argc, argv);
    DParam.cw_bound =     getIntValue( "--cw", 16, argc, argv);
    DParam.shift_ranges = getBoolValue("--shift-extract", false, argc, argv);
    DParam.use_add_sub =  getBoolValue("--use-arith-add-sub", false, argc, argv);
    DParam.cross_bw =     getBoolValue("--cross-bw", false, argc, argv);
    DParam.force_bitselect_hint_on_every_var = getBoolValue("--force-bit-select-hint", false, argc, argv);
    DParam.var_s_const = var_s_const;
    DParam.no_enum_num_name = no_enum_variable_name;
    DParam.bit_select_hints = bit_select_hints;
    DParam.use_bv_not = getBoolValue("--use-arith-bvnot", false, argc, argv);
    DParam.cross_var_eq = true;
  }
  CDParameters CParam(DParam); // by default almost the same
  {
    CParam.shift_ranges = false;
    CParam.use_add_sub = false;
    CParam.cross_bw = false;
    CParam.force_bitselect_hint_on_every_var = false;
    CParam.use_bv_not = false;
  } // with some exceptions
  { // will use DParam's unless override
    CParam.bw_bound =     getIntValue( "--ctrl-bw", CParam.bw_bound, argc, argv);
    CParam.cw_bound =     getIntValue( "--ctrl-cw", CParam.cw_bound, argc, argv);
    CParam.shift_ranges = getBoolValue("--ctrl-shift-extract", CParam.shift_ranges, argc, argv);
    CParam.use_add_sub =  getBoolValue("--ctrl-use-arith-add-sub", CParam.use_add_sub, argc, argv);
    CParam.cross_bw =     getBoolValue("--ctrl-cross-bw", CParam.cross_bw, argc, argv);
    CParam.force_bitselect_hint_on_every_var = getBoolValue("--ctrl-force-bit-select-hint", CParam.force_bitselect_hint_on_every_var, argc, argv);
    CParam.cross_var_eq = !getBoolValue("--ctrl-no-cross-var-eq", false, argc, argv);
    if (!ctrl_var_s_const.empty())
      CParam.var_s_const = ctrl_var_s_const;
    if (!ctrl_no_enum_variable_name.empty())
      CParam.no_enum_num_name = ctrl_no_enum_variable_name;
    if (!ctrl_bit_select_hints.empty())
      CParam.bit_select_hints = ctrl_bit_select_hints;
    CParam.use_bv_not = getBoolValue("--ctrl-use-arith-bvnot", CParam.use_bv_not, argc, argv);
  }




  simpleCheck(argv[argc-1],
              getIntValue("--ante-size", 4, argc, argv),
              getIntValue("--conseq-size", 4, argc, argv),
              getStringValue("--cnf", "", argc, argv),
              getBoolValue("--skip-cnf", false, argc, argv),
              getBoolValue("--skip-const-check", false, argc, argv),
              getBoolValue("--skip-stat-collect", false, argc, argv),
              getBoolValue("--gen-spec-only", false, argc, argv), // only use generalization/specification candidates
              getIntValue("--check-cand-per-cl-max", 0, argc, argv),
              getBoolValue("--cti-prune", false, argc, argv),
              getBoolValue("--force-cti-prune", false, argc, argv),
              getBoolValue("--find-one", false, argc, argv),
              getBoolValue("--find-one-clause", false, argc, argv),
              getBoolValue("--cti-wait-till-stable", false, argc, argv),

              getBoolValue("--no-merge-cti", false, argc, argv),
              getBoolValue("--no-add-cand-after-cti", false, argc, argv),
              getBoolValue("--2-chance", false, argc, argv),

              CParam, DParam,
              CSvar, COvar, DIvar, DOvar,Groupings,

              getBoolValue("--debug-print-lemma", false, argc, argv),
              getBoolValue("--debug", false, argc, argv)
              );
  return 0;
}



  /*
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
  }*/
