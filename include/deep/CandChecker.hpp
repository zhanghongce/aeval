#ifndef CANDCHECKER__HPP__
#define CANDCHECKER__HPP__

#include "ae/SMTUtils.hpp"
#include "Horn.hpp"

#include <fstream>
#include <map>
#include <unordered_map>

using namespace std;
using namespace boost;
namespace ufo
{

  // ---------------------- UTILITIES ---------------- //

  static int OP_CONJ = 1;
  static int OP_DISJ = 2;


  Expr combineListExpr(ExprVector selection, int op){
    Expr e;
    if (selection.size() == 1) e = selection[0];
    else if (selection.size() == 2){
      if (op == OP_CONJ) e = mk<AND>(selection[0], selection[1]);
      else if (op == OP_DISJ) e = mk<OR>(selection[0], selection[1]);
    }
    else{
      if (op == OP_CONJ) e = mknary<AND>(selection);
      else if (op == OP_DISJ) e = mknary<OR>(selection);
    }
    return e;
  }
  
  // ---------------------- END OF UTILITIES ---------------- //

  /// \brief Class of CNF
  struct InvariantInCnf {
  public:
    // Type definitions
    /// literal : complement, var, bit-idx
    typedef std::tuple<std::string, unsigned, bool> literal;
    /// clause : string(state name) -> literals
    typedef std::map<std::string, std::vector<literal>> clause;
    /// the var names need to collect
    typedef std::unordered_set<std::string> vars_t;
    /// inv : clauses ~(c1 | c2 | c3) : clause_hash -> clause
    typedef std::vector<clause> clauses;
    /// the var -> z3var map
    typedef std::unordered_map<std::string, Expr> named_vars_t;

  public:
    // members
    /// the invariant in CNF form
    clauses _cnf_;
    vars_t _vars_;

    void LoadFromFile(const std::string & fn) {
      std::ifstream fin(fn);
      if (!fin.is_open()) {
        outs () << "Error reading " << fn << "\n";
        return;
      }
      unsigned num_clause;
      fin >> num_clause;
      for (unsigned idx = 0; idx < num_clause; ++ idx) {
        unsigned num_literal;
        fin >> num_literal;
        _cnf_.push_back(clause()); // put a clause
        auto & back = _cnf_.back();
        for (unsigned lidx = 0; lidx < num_literal; ++ lidx){
          std::string s_name;
          unsigned bitslice;
          bool complemented;
          fin >> s_name >> bitslice >> complemented;
          back[s_name].push_back(
            std::make_tuple(s_name, bitslice, complemented));
          _vars_.insert(s_name);
        } // for each literal
      } // for each clause
    } // LoadFromFile

    template <class T>
    void FromVnameContainer(const T & ctr) {
      if (_cnf_.empty())
        _cnf_.push_back(clause()); // put a clause

      auto & back = _cnf_.back();
      for (auto pos = ctr.begin(); pos != ctr.end() ; ++pos) {
        const auto & s_name = *pos;
        back[s_name].push_back(
          std::make_tuple(s_name, 0, false));
        _vars_.insert(s_name);

      }
    } // FromVnameContainer

    static Expr clause_to_expression(const clause & cl, const named_vars_t & vars) {
      ExprVector z3_lits;
      for (auto && vn_liters : cl) { // for each
        for (auto && l : vn_liters.second) {
          const auto & name = std::get<0>(l);
          unsigned bitslice = std::get<1>(l);
          bool complemented = std::get<2>(l);
          auto pos = vars.find(name);
          if (pos == vars.end()) {
            outs() << "clause_to_expression: Vars: " << name << " not found.\n";
            continue;
          }
          // assert(pos != vars.end());
          int n = complemented ? 0 : 1;
          auto ltexp = 
            mk<EQ>(bv::extract(bitslice,bitslice,pos->second), bv::bvnum(n, 1, pos->second->efac()) );
          z3_lits.push_back(ltexp);
        } // for each literal in that name
      } // for each name
      return combineListExpr(z3_lits, OP_CONJ );
    } // clause_to_expression

    static std::string clause_vars_to_string (const clause & cl) {
      string ret;
      for (auto && vn_liters : cl)
        ret += "||" + vn_liters.first;
      return ret;
    }
  }; // class InvariantInCnf

  class CandChecker
  {
    private:

    ExprFactory &efac;
    EZ3 z3;
    ufo::ZSolver<ufo::EZ3> smt_solver;

    HornRuleExt* tr;
    HornRuleExt* fc;
    HornRuleExt* qr;

    ExprVector& vars;
    ExprSet learnedExprs;

    public:
    
    CandChecker (ExprFactory &_efac, HornRuleExt* _fc, HornRuleExt* _tr, HornRuleExt* _qr) :
      efac(_efac), z3(efac), smt_solver (z3), fc(_fc), tr(_tr), qr(_qr), vars(qr->srcVars)
    {
      // sanity checks:
      assert (fc != NULL);
      assert (tr != NULL);
      assert (qr != NULL);
      for (int i = 0; i < tr->srcVars.size(); i++)
        assert (tr->srcVars[i] == vars[i]);
      for (int i = 0; i < tr->dstVars.size(); i++)
        assert (tr->dstVars[i] == fc->dstVars[i]);
    }

    // Expr getModel(ExprVector& vars)
    Expr getModel()
    {
      // used to explain the reason why some of the check failed
      // i.e., it is supposed to be called after "smt_solver.solve()" returned SAT

      ExprVector eqs;
      ZSolver<EZ3>::Model m = smt_solver.getModel();
      for (auto & v : vars)
        if (v != m.eval(v))
            eqs.push_back(mk<EQ>(v, m.eval(v)));
      return conjoin (eqs, efac);
    }

    Expr getlearnedLemmas()
    {
      return conjoin (learnedExprs, efac);
    }

    bool checkInitiation(Expr cand)
    {
      for (int j = 0; j < fc->dstVars.size(); j++)
      {
        cand = replaceAll(cand, vars[j], fc->dstVars[j]);
      }

      smt_solver.reset ();
      smt_solver.assertExpr (fc->body);
      smt_solver.assertExpr (mk<NEG>(cand));

      return (!smt_solver.solve ());
    }

    bool checkInductiveness(Expr cand)
    {
      // supposed to be called after checkInitiation

      Expr candPrime = cand;

      for (int j = 0; j < fc->dstVars.size(); j++)
      {
        candPrime = replaceAll(candPrime, vars[j], tr->dstVars[j]);
      }

      smt_solver.reset ();
      smt_solver.assertExpr (tr->body);
      smt_solver.assertExpr (cand);
      smt_solver.assertExpr (getlearnedLemmas()); // IMPORTANT: use all lemmas learned so far
      smt_solver.assertExpr (mk<NEG>(candPrime));

      bool res = !smt_solver.solve ();
      if (res) learnedExprs.insert (cand);  // inductiveness check passed; so add a new lemma

      return res;
    }


    bool hasThisCTI(Expr cand, Expr cti)
    {
      // supposed to be called after checkInitiation

      Expr candPrime = cand;

      for (int j = 0; j < fc->dstVars.size(); j++)
      {
        candPrime = replaceAll(candPrime, vars[j], tr->dstVars[j]);
      }

      smt_solver.reset ();
      smt_solver.assertExpr (tr->body);
      smt_solver.assertExpr (cand);
      smt_solver.assertExpr (cti);
      smt_solver.assertExpr (getlearnedLemmas()); // IMPORTANT: use all lemmas learned so far
      smt_solver.assertExpr (mk<NEG>(candPrime));

      // outs()<<"*************begin IND check**************\n";
      // smt_solver.toSmtLib(outs());
      // outs()<<"*************end IND check**************\n";

      bool res = smt_solver.solve ();

      return res; // if true then it also has this cti
    }

    bool checkBlockCTI(Expr model)
    {
      // supposed to be called after checkInductiveness
      // but it does not take a candidate as input since it is already in learnedExprs

      smt_solver.reset();
      smt_solver.assertExpr (model);
      smt_solver.assertExpr (getlearnedLemmas());

      return !smt_solver.solve ();
    }

    bool checkSafety()
    {
      // supposed to be called after checkInductiveness
      // but it does not take a candidate as input since it is already in learnedExprs

      smt_solver.reset();
      smt_solver.assertExpr (qr->body);
      smt_solver.assertExpr (getlearnedLemmas());

      return !smt_solver.solve ();
    }

    bool isSimplifyToConst(Expr c) {
      smt_solver.reset();
      smt_solver.assertExpr(c);
      bool possible_to_be_true = smt_solver.solve ();

      smt_solver.reset();
      smt_solver.assertExpr(mk<NEG>(c));
      bool possible_to_be_false = smt_solver.solve ();
      if (! (possible_to_be_true && possible_to_be_false) )
        return true; // if it cannot be true or cannot be false then it is const
      return false;
    }

    bool isAimpliesB(Expr a, Expr b) {
      smt_solver.reset();
      smt_solver.assertExpr(a);
      smt_solver.assertExpr(mk<NEG>(b));
      bool possible_to_be_true = smt_solver.solve ();
      return !possible_to_be_true;
    }

    void serializeInvars()
    {
      Expr lms = getlearnedLemmas();
      for (auto & a : qr->origNames) lms = replaceAll(lms, a.first, a.second);

      smt_solver.reset();
      smt_solver.assertExpr(lms);

      smt_solver.toSmtLib (errs());
      errs().flush ();
    }

    size_t getLearnedLemmansSize() const { return learnedExprs.size(); }

    string printExpr(Expr e)
    {
      for (auto & a : qr->origNames) e = replaceAll(e, a.first, a.second);
      std::stringstream sbuf;
      sbuf << e;
      return sbuf.str();
    }

  };
  


  // ------------------------------------ GRAMMAR PART ----------------------------------------- //

  void enumConstPredForEachVar(ExprVector& vars, unsigned bw_bound, vector<ExprVector>& lol, bool shift_extract){
    for (Expr v : vars){
      ExprVector preds;
      
      unsigned bw = bv::width(v->first()->arg(1));
      // std::stringstream sbuf;
      // sbuf<<"BV name: "<<v<<" width:"<<real_bw<<"\n";
      // outs() <<sbuf.str();
      // unsigned bw = real_bw;
      ExprVector evs;
      if (bw > bw_bound)
      {
        if (shift_extract) {
          for (unsigned l = 0; l <= bw - bw_bound; ++l )
            evs.push_back(bv::extract(bw_bound-1 + l,l, v));
        }
        else
          evs.push_back(bv::extract(bw_bound-1, 0, v));
        bw = bw_bound;
      } else
        evs.push_back(v);

      for (Expr & ev : evs)
        for (unsigned i = 0; i < (1ul<<bw); i++){
          Expr pred = mk<EQ>(ev, bv::bvnum(i, bw, v->efac()));
          preds.push_back(pred);
          if (bw > 1){
            pred = mk<NEQ>(ev, bv::bvnum(i, bw, v->efac()));
            preds.push_back(pred);
          }
        }
      lol.push_back(preds);
    }
  }

  // width -> starting location bound
  typedef map<unsigned, set<unsigned>> cross_bw_hints_t;

  void enumDataPredForEachVar(ExprVector& vars,  const vector<string> & var_names,
      unsigned bw_bound, unsigned cw_bound, /* constant-bound */
      const std::map<std::string, std::set<unsigned>>  & var_const,
      // no enumerate
      const set<string> & no_const_enumerate_vars,
      vector<ExprVector>& lol, bool shift_extract, bool use_add, CandChecker & cc, bool cross_bw,
      const cross_bw_hints_t & cross_bw_hints, bool force_cut_bit,
      bool bvnot,
      bool cross_var_eq
      ){
    for (int lidx = 0; lidx < vars.size() ; ++ lidx ) {
      ExprVector preds;
      Expr v = vars[lidx];
      unsigned bw = bv::width(v->first()->arg(1));

      if (force_cut_bit && bw <= bw_bound)
        continue;

      ExprVector evs;
      if (bw > bw_bound) {
        bw = bw_bound;
        
        if (shift_extract) {
          if (!cross_bw_hints.empty() && cross_bw_hints.find(bw_bound) != cross_bw_hints.end()) {
            for (unsigned l : cross_bw_hints.at(bw_bound))
              if (l <= bw - bw_bound)
                evs.push_back(bv::extract(bw_bound-1 + l,l, v));
          } else {
            for (unsigned l = 0; l <= bw - bw_bound; ++l )
              evs.push_back(bv::extract(bw_bound-1 + l,l, v));
          }
        }
        else
          evs.push_back(bv::extract(bw_bound-1, 0, v));
        bw = bw_bound;
      }else
        evs.push_back(v);

      bool skip_enum_const_for_current_var = false; 
      if (!no_const_enumerate_vars.empty() && !var_names.empty()) {
        skip_enum_const_for_current_var = 
          no_const_enumerate_vars.find(var_names[lidx]) != no_const_enumerate_vars.end();
      }

      if (bw <= cw_bound && !skip_enum_const_for_current_var) {
        for (auto && ev : evs) {
          if(var_const.find(var_names[lidx] ) != var_const.end() ) {
            // enum some of them
            for (unsigned i : var_const.at(var_names[lidx]) ){
              Expr pred = mk<EQ>(ev, bv::bvnum(i, bw, v->efac()));
              preds.push_back(pred);
              if (bw > 1){
                pred = mk<NEQ>(ev, bv::bvnum(i, bw, v->efac()));
                preds.push_back(pred);
              }
            }

          } else {
            for (unsigned i = 0; i < (1ul<<bw); i++){
              Expr pred = mk<EQ>(ev, bv::bvnum(i, bw, v->efac()));
              preds.push_back(pred);
              if (bw > 1){
                pred = mk<NEQ>(ev, bv::bvnum(i, bw, v->efac()));
                preds.push_back(pred);
              }
            }
          } // end of enum all
        } // evs
      } // only enumerate numbers based on cw_bound

      // X = Y
      if (cross_var_eq) {
        auto lhs_string = cc.printExpr(v);
        bw = bv::width(v->first()->arg(1));
        for (int ridx = lidx + 1; ridx < vars.size(); ++ ridx) {
          Expr rhs = vars[ridx];
          if ( cc.printExpr(rhs) == lhs_string )
            continue;
          unsigned rbw = bv::width(rhs->first()->arg(1));
          if (bw == rbw) {
              if(bvnot)
                preds.push_back(mk<EQ>(v, mk<BNOT>(rhs)));
              preds.push_back(mk<EQ>(v, rhs));
          }
          else if (cross_bw) {
            if (bw > rbw) {
              if (shift_extract) {
                if (!cross_bw_hints.empty() && cross_bw_hints.find(bw_bound) != cross_bw_hints.end()) {
                  for (unsigned l : cross_bw_hints.at(bw_bound))
                    if (l <= bw - rbw)
                      evs.push_back(bv::extract(bw_bound-1 + l,l, v));
                } else {
                  for (unsigned l = 0; l <= bw - rbw; ++l )
                    preds.push_back(mk<EQ>(bv::extract(rbw-1 + l,l, v), rhs));
                }
              } else // end of shift extract
                preds.push_back(mk<EQ>(bv::extract(rbw-1, 0, v), rhs));
            }
            else if (bw < rbw) {
              if (shift_extract) {
                if (!cross_bw_hints.empty() && cross_bw_hints.find(bw_bound) != cross_bw_hints.end()) {
                  for (unsigned l : cross_bw_hints.at(bw_bound))
                    if (l <= rbw - bw)
                      evs.push_back(bv::extract(bw_bound-1 + l,l, v));
                } else {
                  for (unsigned l = 0; l <= rbw - bw; ++l )
                    preds.push_back(mk<EQ>(v, bv::extract(bw-1 + l, l, rhs)));
                }
              } else
              preds.push_back(mk<EQ>(v, bv::extract(bw-1, 0, rhs)));
            }
          } // cross_bw
        } // for ridx ...
      } // cross_var_eq
      // X = Y1 ADD Y2
      if (use_add) {
        for (int i = 0; i < vars.size(); i++){
          unsigned rbw1 = bv::width(vars[i]->first()->arg(1));
          for (int j = i + 1; j < vars.size(); j++){
            
            unsigned min_bw = bw; if (min_bw > rbw1) min_bw = rbw1;
            
            unsigned rbw2 = bv::width(vars[j]->first()->arg(1));
            if (min_bw > rbw2) min_bw = rbw2;

            Expr X = bw == min_bw? v: bv::extract(min_bw-1, 0, v);
            Expr Y1 = rbw1 == min_bw? vars[i]: bv::extract(min_bw-1, 0, vars[i]);
            Expr Y2 = rbw2 == min_bw? vars[j]: bv::extract(min_bw-1, 0, vars[j]);

            preds.push_back(mk<EQ>(X, mk<BADD>(Y1, Y2)));
            preds.push_back(mk<EQ>(X, mk<BSUB>(Y1, Y2)));
          }
        }
      }
      // can have more operations

      lol.push_back(preds);
    }
  } // enumDataPredForEachVar


  void enumSelectFromLoLImplPart2(vector<ExprVector>& lol, int start, vector<int>& list_selection, ExprVector& selection, ExprVector& output, int op, 
    std::vector<std::set<int>> & per_output_selection_idxs)
  {
    if (start == list_selection.size()){
      assert(selection.size() == list_selection.size());
      
      output.push_back(combineListExpr(selection, op));
      
      per_output_selection_idxs.push_back(std::set<int>());
      for (auto idx : list_selection)
        per_output_selection_idxs.back().insert(idx);
      return;
    }
    for (Expr e: lol[list_selection[start]]) {
      selection.push_back(e);
      enumSelectFromLoLImplPart2(lol, start+1, list_selection, selection, output, op, per_output_selection_idxs);
      selection.pop_back();
    }
  } // enumSelectFromLoLImplPart2

  void enumSelectFromLoLImpl(vector<ExprVector>& lol, int start, unsigned k, vector<int>& list_selection, ExprVector& output, int op, 
    std::vector<std::set<int>> & per_output_selection_idxs, const std::set<int> & skip_lol_idxs)
  {
    if (k == 0){
      ExprVector selection;
      enumSelectFromLoLImplPart2(lol, 0, list_selection, selection, output, op, per_output_selection_idxs);
      return;
    }
    for (int i = start; i <= (signed long long)(lol.size()) -  (signed long long)(k); ++i) {
      if (skip_lol_idxs.find(i) != skip_lol_idxs.end())
        continue;
      list_selection.push_back(i);
      enumSelectFromLoLImpl(lol, i+1, k-1, list_selection, output, op, per_output_selection_idxs, skip_lol_idxs);
      list_selection.pop_back();
    }
  } // enumSelectFromLoLImpl
  
  void enumSelectKFromListofList(vector<ExprVector>& lol, unsigned k, ExprVector& output, int op, 
      std::vector<std::set<int>> & per_output_selection_idxs, const std::set<int> & skip_lol_idxs)
  {
    vector<int> list_selection;
    for (int i = 1; i <= k; i++)
      enumSelectFromLoLImpl(lol, 0, i, list_selection, output, op, per_output_selection_idxs, skip_lol_idxs);
  }

  void enumSelectFromListImpl(ExprVector& list, int start, unsigned k, ExprVector& selection, ExprVector& output, int op){
    if (k == 0){
      output.push_back(combineListExpr(selection, op));
      return;
    }
    for (int i = start; i <= (signed long long)(list.size()) - (signed long long)(k); ++i) {
      selection.push_back(list[i]);
      enumSelectFromListImpl(list, i+1, k-1, selection, output, op);
      selection.pop_back();
    }
  }

  void enumSelectKFromList(ExprVector& list, unsigned k, ExprVector& output, int op) {
    ExprVector selection;
    for (int i = 1; i <= k; i++)
      enumSelectFromListImpl(list, 0, i, selection, output, op);
  }

 //------------------------------------------ ENUM idxs ------------------------------------------ //

  void enumIdxSelectFromLoLImpl(const vector<int> & listOfIdxs, int start, unsigned k, vector<int>& list_selection,
    std::vector<std::vector<int>> & combination_of_idxs, const std::set<int> & skip_lol_idxs)
  {
    if (k == 0){
      combination_of_idxs.push_back(std::vector<int>());
      for (auto idx : list_selection)
        combination_of_idxs.back().push_back( listOfIdxs.at(idx) );
      //enumSelectFromLoLImplPart2(lol, 0, list_selection, selection, output, op);
      return;
    }
    for (int i = start; i <= ( (signed long long)(listOfIdxs.size()) - k ); ++i) {
      if (skip_lol_idxs.find(i) != skip_lol_idxs.end())
        continue;
      list_selection.push_back(i);
      enumIdxSelectFromLoLImpl(listOfIdxs, i+1, k-1, list_selection, combination_of_idxs, skip_lol_idxs);
      list_selection.pop_back();
    }
  }
  
  void enumIdxSelectKFromListofList(const vector<int>& listOfIdxs, unsigned k,
    std::vector<std::vector<int>> & combination_of_idxs, const std::set<int> & skip_lol_idxs)
  {
    vector<int> list_selection;
    for (int i = 1; i <= k; i++)
      enumIdxSelectFromLoLImpl(listOfIdxs, 0, i, list_selection, combination_of_idxs, skip_lol_idxs);
  }
  // ------------------------------------ END OF GRAMMAR PART ----------------------------------------- //

class CTI_manager {
  public:
    CandChecker & cc;
    int indfailcnt;
    bool no_merge_cti;

  public:
    map<Expr, ExprVector> CTImap;
    
    CTI_manager(CandChecker & _cc, bool _no_merge_cti) : cc(_cc), indfailcnt(0), no_merge_cti(_no_merge_cti) {}

    void InsertCTIFailedCand(Expr & cand) { // right after ind check!!!
      // for existing cti's test if it is also failing on that 
      indfailcnt ++;

      Expr cti = cc.getModel();
      if (!no_merge_cti)
        for (auto && model_vec_pair : CTImap) {
          if (cc.hasThisCTI(cand, model_vec_pair.first) ) {
            model_vec_pair.second.push_back(cand);
            return;
          }
        }
      // not found, new CTI 
      CTImap[cti].push_back(cand);
    } // InsertCTIFailedCand

}; // class CTI_manager

struct CDParameters{
    unsigned bw_bound;
    unsigned cw_bound;
    bool shift_ranges;
    bool use_add_sub;
    bool cross_bw;
    bool force_bitselect_hint_on_every_var;
    std::map<std::string, std::set<unsigned>> var_s_const;
    std::set<std::string>  no_enum_num_name;
    cross_bw_hints_t bit_select_hints;
    bool use_bv_not;
    bool cross_var_eq;

    void Print (raw_ostream & os) const {
      os  << "Max bitwidth considered: " << bw_bound << "\n"
          << "Max bitwidth of constant: " << cw_bound << "\n"
          << "Shift extraction: "  <<  shift_ranges  << "\n"
          << "Add/sub: "  <<  use_add_sub  << "\n"
          << "bvnot: "  <<  use_bv_not  << "\n"
          << "EQ/NEQ across bitwidth: "  <<  cross_bw  << "\n"
          << "Force bitselection hints on every var: " << force_bitselect_hint_on_every_var << "\n"
          ;
    }
};


  inline void simpleCheck(const char * chcfile, 
    int ANTE_Size, int CONSQ_Size,
    const std::string &clauses_fn, bool skip_original, bool skip_const_check,
    bool skip_stat_check, bool gen_spec_only,
    int check_cand_max,
    // hints
    bool cti_prune,
    bool force_cti_prune,
    bool find_one,
    bool find_on_one_clause,
    bool cti_till_stable,
    bool no_merge_cti,
    bool no_add_cand_after_cti,
    bool repeated_search,

    const CDParameters & CParam,
    const CDParameters & DParam,

    const std::set<std::string> & CSvar,
    const std::set<std::string> & COvar,
    const std::set<std::string> & DIvar,
    const std::set<std::string> & DOvar,
    const std::vector<std::set<std::string>> & Groupings,

    bool debug_print_lemma,
    bool debug)
  {

    if (force_cti_prune)
      cti_prune = true;

    outs () << "=========== GLOBAL CONFIG =============\n"
            << "Find one and stop: " << find_one << "\n"
            << "Find one clause and stop: " << find_on_one_clause << "\n"
            << "CTI till stable: " << cti_till_stable << "\n"
            << "(" << ANTE_Size << ") ==> (" << CONSQ_Size << ")"  << "\n"
            << "Skip original cnf: " <<  skip_original  << "\n"
            << "Skip const check: "  <<  skip_const_check  << "\n"
            << "CTI Prune: "  <<  cti_prune <<  (force_cti_prune ? " (forced)" : "")  << "\n"
            << "No merge cti: "  <<  no_merge_cti  << "\n"
            << "Not adding cand after cti: "  <<  no_add_cand_after_cti  << "\n"
            << "2nd chance: "  <<  repeated_search  << "\n"
            ;
    outs () << "----------- CONTROL CONFIG -----------\n";
    CParam.Print(outs());
    outs () << "----------- DATA CONFIG --------------\n";
    DParam.Print(outs());

    // let's load clauses
    InvariantInCnf cnf;

    if (!clauses_fn.empty()) {
      cnf.LoadFromFile(clauses_fn); // will print err msg
      if (cnf._cnf_.empty()) {
        outs () << "Error reading " << clauses_fn << "\n";
        return; // read error
      }
    } else {
      if (CSvar.empty()) {
        outs () << "Empty cnf and empty CSvar\n";
        return; // read error
      }
      cnf.FromVnameContainer(CSvar);
      cnf.FromVnameContainer(COvar);
      cnf.FromVnameContainer(DIvar);
      cnf.FromVnameContainer(DOvar);
    }

    outs () << "----------- GRAMMAR --------------\n";
    outs () << "CSvar.size = " << CSvar.size() << "\n"
            << "COvar.size = " << COvar.size() << "\n"
            << "DIvar.size = " << DIvar.size() << "\n"
            << "DOvar.size = " << DOvar.size() << "\n"
            << "Grouping.size = " << Groupings.size() << "\n";
    outs () << "=========== END CONFIG =============\n";

    ExprFactory efac;
    EZ3 z3(efac);
    CHCs ruleManager(efac, z3);
    ruleManager.parse(string(chcfile));

    // create a map : cnf's state_name -> var

    HornRuleExt* tr;
    HornRuleExt* fc;
    HornRuleExt* qr;

    for (auto & a : ruleManager.chcs)
      if (a.isInductive) tr = &a;
      else if (a.isFact) fc = &a;
      else if (a.isQuery) qr = &a;

    CandChecker cc(efac, fc, tr, qr);
    CTI_manager cti_manager (cc, no_merge_cti);

    // get inv vars
    InvariantInCnf::named_vars_t named_vars;
    for (auto & a: tr->srcVars) {
      if (!bv::is_bvconst(a)) 
      {
      //  outs()<<"not a bv var: "<<*a<<" name: "<<*qr->origNames[a]<<" \n";
          continue;
      } 
      // else 
      //  outs()<<"is a bv var: "<<*a<<" name: "<<*qr->origNames[a]<<" \n";

      std::stringstream sbuf;
      sbuf << *qr->origNames[a];
      const std::string & state_name = sbuf.str();
      if (state_name.length()<3)
        continue; // too short
      if (state_name.substr(0,2) != "S_")
        continue;
      std::string sn = state_name.substr(2); // S_...
      //if (cnf._vars_.find(sn) != cnf._vars_.end())
      named_vars.insert(std::make_pair(sn,a));
    }

    
    ExprVector cls_list;
    for (auto && cl : cnf._cnf_)
      cls_list.push_back ( InvariantInCnf::clause_to_expression(cl,named_vars) );

    Expr InputIndInv = mk<NEG>(combineListExpr(cls_list, OP_DISJ));
    if (skip_original) 
      outs()  << "Skip sanity check\n";
    else{
      outs() <<"Testing Candidate: "<<cc.printExpr(InputIndInv) << "\n";

      if (!(cc.checkInitiation(InputIndInv) &&
            cc.checkInductiveness(InputIndInv) &&
            cc.checkSafety())) {
        outs() << "The provided CNF is not inductive invariant!\n";
        return;
      }
      outs() << "Sanity check passed!\n";
    }
    outs().flush();
    // ------------ let's try enhancement here --------------- //
    

    // 1. test the cnf is truly a solution
    // 2. for each clause, try enhance it
    // 3. output clauses that get extended (for on clause, they could be more than one)
    //          clause idx, results :n
    //          (define-fun ?) ... for every? (end with (check-sat), so search and clip

    int iter = 0;
    int found = 0;
    int clause_no = 0;
    int num_generalizion = 0;
    int num_specification = 0;
    std::unordered_set<std::string> handled_clauses;
    for (auto && cl : cnf._cnf_) {
      // check if we want to skip this clause
      auto clause_signature = InvariantInCnf::clause_vars_to_string(cl);
      if (handled_clauses.find(clause_signature) != handled_clauses.end())
        continue; // skip this clause
      handled_clauses.insert(clause_signature);

      ExprVector cands;

      // find the variable in this clause
      ExprVector vars_in_this_clause;
      vector<string> varnames;
      for (auto && var_name : cl) {
        assert (named_vars.find(var_name.first) != named_vars.end());
        vars_in_this_clause.push_back( named_vars[ var_name.first ] );
        varnames.push_back(var_name.first);
      }
      
      int this_clause_ANTE_Size, this_clause_CONSQ_Size;
      if (vars_in_this_clause.size() > 1) {
        this_clause_ANTE_Size = vars_in_this_clause.size() - 1;
        this_clause_CONSQ_Size = 1;
      } else {
        this_clause_ANTE_Size = 1;
        this_clause_CONSQ_Size = 0;
      }
      if (ANTE_Size != 0)
        this_clause_ANTE_Size = min(this_clause_ANTE_Size, ANTE_Size);

      this_clause_CONSQ_Size = vars_in_this_clause.size() - this_clause_ANTE_Size;
      if (CONSQ_Size != 0)
        this_clause_CONSQ_Size = min(this_clause_CONSQ_Size, CONSQ_Size);

      // build an expression without current clause 
      Expr LocalInputIndInv = NULL;
      if (!skip_stat_check) {
        ExprVector local_cls_list;
        for (auto pos = cnf._cnf_.begin(); pos != cnf._cnf_.end(); ++ pos) {
          if (pos - cnf._cnf_.begin() == clause_no)
            continue;
          local_cls_list.push_back ( InvariantInCnf::clause_to_expression(*pos,named_vars) );
        }
        if (!local_cls_list.empty())
          LocalInputIndInv = mk<NEG>(combineListExpr(local_cls_list, OP_DISJ));
      } // 

      // -------------------------- CANDIDATE GENERATION STAGE -------------------------------- //

      // filter names according to the grammar
      if (!CSvar.empty()) {
        ExprVector vars_ante;
        vector<string> varnames_ante;
        ExprVector vars_conseq;
        vector<string> varnames_conseq;
        assert (vars_in_this_clause.size() == varnames.size());
        for (size_t idx = 0 ; idx < varnames.size() ; ++ idx){
          const auto & vn = varnames.at(idx);
          if (CSvar.find(vn) != CSvar.end()) {
            vars_ante.push_back(vars_in_this_clause.at(idx));
            varnames_ante.push_back(varnames.at(idx));
          }
          if (COvar.find(vn) != COvar.end() ||
              DIvar.find(vn) != DIvar.end() ||
              DOvar.find(vn) != DOvar.end()
              ) {
            vars_conseq.push_back(vars_in_this_clause.at(idx));
            varnames_conseq.push_back(varnames.at(idx));
          }
        }
        // will have two sets of preds

        vector<ExprVector> CSpredList; // {cs1: [cs1=0, cs1=1 , cs1=2 ...], cs2: [cs2=0, cs2=1 ...]}
        vector<ExprVector> CODIDOpredList;

        assert (vars_ante.size() == varnames_ante.size() &&
                vars_conseq.size() ==  varnames_conseq.size()
          );

        enumDataPredForEachVar(vars_ante,  varnames_ante, 
          CParam.bw_bound, CParam.cw_bound, 
          CParam.var_s_const, CParam.no_enum_num_name, 
          CSpredList, 
          CParam.shift_ranges, CParam.use_add_sub, cc, 
          CParam.cross_bw, CParam.bit_select_hints, false, CParam.use_bv_not,
          CParam.cross_var_eq );
        
        enumDataPredForEachVar(vars_conseq,  varnames_conseq, 
          DParam.bw_bound, DParam.cw_bound, 
          DParam.var_s_const, DParam.no_enum_num_name, 
          CODIDOpredList, 
          DParam.shift_ranges, DParam.use_add_sub, cc, 
          DParam.cross_bw, DParam.bit_select_hints, false, DParam.use_bv_not,
          DParam.cross_var_eq );
        

        outs () << "CSpred set size: " << CSpredList.size() << "\n";
        outs () << "CODIDOpredList set size: " << CODIDOpredList.size() << "\n";

        std::vector<std::set<int>> per_ante_selection_idxs; 
        ExprVector Ante;

        enumSelectKFromListofList(CSpredList, this_clause_ANTE_Size, Ante, OP_CONJ, per_ante_selection_idxs, {} ); // --> get a list of selection
        outs () << "Ante set size: " << Ante.size() << "\n";

        size_t ante_idx = 0;
        size_t current_cand_incr_count = 0;
        for (Expr a : Ante) {
          assert (ante_idx < per_ante_selection_idxs.size());

          if (check_cand_max != 0 && current_cand_incr_count > check_cand_max) {
            outs () << "Skipped, " << current_cand_incr_count << " exceed cand max.\n";
            break;
          }

          if (skip_const_check || !cc.isSimplifyToConst(a)) {
            current_cand_incr_count ++;
            cands.push_back(a);
          }

          const std::set<int> & this_ante_select =  per_ante_selection_idxs.at(ante_idx);
          std::set<int> conseq_should_avoid;
          for (auto idx : this_ante_select) {
            const auto & vn = varnames_ante.at(idx);
            auto conseq_idx = 
              std::find(varnames_conseq.begin() , varnames_conseq.end(), vn);
            if ( conseq_idx != varnames_conseq.end() ){
              conseq_should_avoid.insert( conseq_idx - varnames_conseq.begin() );
            }
          } // translate avoid set


        // -------------------------- MAP GROUPS to idxs -------------------------------- //
        // not the group can be larger than those appear in the varnames

        std::vector<std::vector<int>> GroupingsListofIdxs;
        for (auto && group : Groupings) {
          std::vector<int> idxs;
          for (auto && vname : group) {
            auto pos = std::find(varnames_conseq.begin(), varnames_conseq.end(), vname);
            if (pos != varnames_conseq.end())
              idxs.push_back(pos - varnames_conseq.begin());
          } // for each var in the group
          if (!idxs.empty())
            GroupingsListofIdxs.push_back(idxs);
        } // for groupings

        // -------------------------- END of MAP GROUPS to idxs -------------------------------- //

          std::vector<std::set<int>> no_use;
          ExprVector Conseq;
          // select from grouping
          if (GroupingsListofIdxs.empty())
            enumSelectKFromListofList(CODIDOpredList, this_clause_CONSQ_Size, Conseq, OP_DISJ, no_use ,  conseq_should_avoid );
          else {
            // to conseq 
            std::vector<std::vector<int>> combination_of_idxs;
            for (auto && group : GroupingsListofIdxs) {
              int K = min(group.size(), (size_t)(this_clause_CONSQ_Size) );
              if (K <= 1)
                continue;
              vector<int> list_selection;
              enumIdxSelectFromLoLImpl(group,0, K, list_selection, combination_of_idxs, conseq_should_avoid); 
              // select exactly K elements
            }
            for (auto && listOfVarIdx : combination_of_idxs) {
              vector<int> list_selection;
              ExprVector selection; // no use
              enumSelectFromLoLImplPart2(CODIDOpredList, 0, listOfVarIdx, selection, Conseq, OP_DISJ, no_use);
            }
            if (this_clause_CONSQ_Size >= 1)
              enumSelectKFromListofList(CODIDOpredList, 1, Conseq, OP_DISJ, no_use ,  conseq_should_avoid );
          }

          for (Expr b: Conseq) {
            auto cand = mk<IMPL>(a, b);
            if (skip_const_check || !cc.isSimplifyToConst(cand)) {
              current_cand_incr_count ++;
              cands.push_back(cand);
            }
          } // for conseq
          ante_idx ++;
        } // for each Ante


      } else { // enumerate the whole
        ExprVector Ante;
        vector<ExprVector> CSpredList; // {cs1: [cs1=0, cs1=1 , cs1=2 ...], cs2: [cs2=0, cs2=1 ...]}

        //enumConstPredForEachVar(vars_in_this_clause, bw_bound, CSpredList, shift_ranges);
        enumDataPredForEachVar(vars_in_this_clause,  varnames, 
          DParam.bw_bound, DParam.cw_bound, 
          DParam.var_s_const, DParam.no_enum_num_name, 
          CSpredList, 
          DParam.shift_ranges, DParam.use_add_sub, cc, 
          DParam.cross_bw, DParam.bit_select_hints, false, DParam.use_bv_not,
          DParam.cross_var_eq );
      
        if (DParam.force_bitselect_hint_on_every_var) {
          for (auto && bitwidth_lsb_pair : DParam.bit_select_hints)
            enumDataPredForEachVar(vars_in_this_clause, varnames, bitwidth_lsb_pair.first, 
              DParam.cw_bound, DParam.var_s_const, DParam.no_enum_num_name, 
              CSpredList, 
              DParam.shift_ranges, DParam.use_add_sub, cc, DParam.cross_bw, 
              DParam.bit_select_hints, true, DParam.use_bv_not,
              DParam.cross_var_eq );
        } // force_bitselect_hint_on_every_var

        outs () << "Base selection set size: " << CSpredList.size() << "\n";

        std::vector<std::set<int>> per_ante_selection_idxs; 
        enumSelectKFromListofList(CSpredList, this_clause_ANTE_Size, Ante, OP_CONJ, per_ante_selection_idxs, {} ); // --> get a list of selection
        outs () << "Ante set size: " << Ante.size() << "\n";

        size_t ante_idx = 0;
        size_t current_cand_incr_count = 0;
        for (Expr a : Ante) {
          assert (ante_idx < per_ante_selection_idxs.size());

          if (check_cand_max != 0 && current_cand_incr_count > check_cand_max) {
            outs () << "Skipped, " << current_cand_incr_count << " exceed cand max.\n";
            break;
          }

          if (skip_const_check || !cc.isSimplifyToConst(a)) {
            current_cand_incr_count ++;
            cands.push_back(a);
          }

          std::vector<std::set<int>> no_use;
          ExprVector Conseq;
          enumSelectKFromListofList(CSpredList, this_clause_CONSQ_Size, Conseq, OP_DISJ, no_use , per_ante_selection_idxs.at(ante_idx) );

          for (Expr b: Conseq) {
            auto cand = mk<IMPL>(a, b);
            if (skip_const_check || !cc.isSimplifyToConst(cand)) {
              current_cand_incr_count ++;
              cands.push_back(cand);
            }
          } // for conseq
          ante_idx ++;
        } // for each Ante
      } // Enumerate as a whole

      // -------------------------- ENUMERATION STAGE -------------------------------- //
      
      outs() << "Cands : " << cands.size() << "\n";
      outs() .flush();

      unsigned old_learned_lemmas = cc.getLearnedLemmansSize();
      unsigned new_learned_lemmas;
      bool first_round = true;

      do{
        for (auto & cand : cands)
        {
          iter++;
          if (debug)
            outs() <<"Testing Candidate: "<<cc.printExpr(cand) ;

          bool is_specialization, is_generalization;
          if (gen_spec_only) {
              Expr new_cnf = LocalInputIndInv ? mk<AND> (cand, LocalInputIndInv) : cand;
              is_specialization = cc.isAimpliesB( new_cnf , InputIndInv);
              is_generalization = cc.isAimpliesB( InputIndInv, new_cnf );
              if (!is_specialization && !is_generalization)
                continue; // skip
          }

          if (cc.checkInitiation(cand) ) {

            if (cc.checkInductiveness(cand) ) {
              if (cc.checkSafety())
              {
                if (debug)
                  outs() <<" @@@@ safe\n";
                found ++;
                if (!skip_stat_check) {
                  Expr new_cnf = LocalInputIndInv ? mk<AND> (cand, LocalInputIndInv) : cand;

                  if ( ( gen_spec_only &&  is_generalization ) || cc.isAimpliesB( InputIndInv, new_cnf ) )
                    num_generalizion ++;
                  if ( ( gen_spec_only &&  is_specialization ) || cc.isAimpliesB( new_cnf , InputIndInv) )
                    num_specification ++;
                }

                if (find_one)
                  goto end_check;
              } // safety check
              else {
                if (debug)
                  outs() <<" +++ ind\n";
              }
            } // ind check check
            else {
              if (cti_prune && first_round)
                cti_manager.InsertCTIFailedCand(cand);
              if (debug)
                  outs() <<" -- CTI\n";
            }
          } // init check
          else {
              if (debug)
                  outs() <<"\n";
          }
        } // for each cand
        new_learned_lemmas = cc.getLearnedLemmansSize();
        if (new_learned_lemmas == old_learned_lemmas)
          break;
        if (!repeated_search)
         break;
        old_learned_lemmas = new_learned_lemmas;
        first_round = false;
        outs () << "--- R --- Learned lemmas : " << new_learned_lemmas << "\n";
      }while(true);

      outs () << "Status @ iter: " << iter << " @ clause " << clause_no << " found :" << found << "\n";
      outs () << "Generalizaion:" << num_generalizion << "\n";
      outs () << "Specialization:" << num_specification << "\n";
      outs () .flush();
      clause_no ++;

      if (found > 0 && find_on_one_clause)
        goto end_check;
    } // for each clause

end_check:
    outs() << "Total iter:" << iter << ", found: " << found  << " learned lemmas: " << cc.getLearnedLemmansSize() << "\n";
    outs() << "TotalGen: "<< num_generalizion << "\n";
    outs() << "TotalSpec: " << num_specification << "\n";

    // finally print out what we learned (at least the one given)
    if (found > 0  && !force_cti_prune) {
      cc.serializeInvars();
      outs() << "proved\n";
      return;
    }

    if (found == 0 && !cti_prune) {
      if (debug_print_lemma)
        cc.serializeInvars();
      outs() << "unknown\n";
      return;
    }

    outs()<<" Found CTIs # "<<cti_manager.CTImap.size()<<" covering # "<<cti_manager.indfailcnt<< "candidates\n";

    while (1){
      ExprVector ctisToRemove;
      for (auto& iter: cti_manager.CTImap){
        if (cc.checkBlockCTI(iter.first)){
          ctisToRemove.push_back(iter.first);
          outs()<<"new CTI blocked\n";
        }
      }
      if (ctisToRemove.empty()) break; // fail to change anything

      for (auto && model : ctisToRemove) {
        if (cc.checkInductiveness(conjoin(cti_manager.CTImap.at(model), efac))){
          cti_manager.CTImap.erase(model);
          outs()<<"new cands added\n";
          if (cc.checkSafety()){
            found ++;
            if (!cti_till_stable) {
              outs()<<"proved\n";
              outs().flush();
              cc.serializeInvars();
              return;
            }
          }
        } else {
          auto cands = cti_manager.CTImap.at(model);
          cti_manager.CTImap.erase(model);
          if(!no_add_cand_after_cti)
            for (auto && cand : cands) {
              if (!cc.checkInductiveness(cand))
                cti_manager.InsertCTIFailedCand(cand);
            }
        }
      } // for each of ctisToRemove
    } // the cti block loop

    if (found > 0) {
      outs()<<"proved\n";
      outs().flush();
      cc.serializeInvars();
      return;
    } else {
      if (debug_print_lemma)
        cc.serializeInvars();
      outs() << "unknown\n";
    }
    // the end

  } // function simpleCheck
} // namespace ufo

#endif
