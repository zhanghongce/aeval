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


  // ------------------------------------ GRAMMAR PART ----------------------------------------- //


  static int OP_CONJ = 1;
  static int OP_DISJ = 2;

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
  void enumDataPredForEachVar(ExprVector& LHSvars, unsigned bw_bound, ExprVector& RHSvars, vector<ExprVector>& lol, bool shift_extract, bool use_add){
    for (Expr v : LHSvars){
      ExprVector preds;
      Expr ev = v;
      unsigned bw = bv::width(v->first()->arg(1));

      ExprVector evs;
      if (bw > bw_bound) {
        bw = bw_bound;
        
        if (shift_extract) {
          for (unsigned l = 0; l <= bw - bw_bound; ++l )
            evs.push_back(bv::extract(bw_bound-1 + l,l, v));
        }
        else
          evs.push_back(bv::extract(bw_bound-1, 0, v));
        bw = bw_bound;
      }else
        evs.push_back(v);

      for (auto && ev : evs)
        for (unsigned i = 0; i < (1ul<<bw); i++){
          Expr pred = mk<EQ>(ev, bv::bvnum(i, bw, v->efac()));
          preds.push_back(pred);
          if (bw > 1){
            pred = mk<NEQ>(ev, bv::bvnum(i, bw, v->efac()));
            preds.push_back(pred);
          }
        }
      // X = Y
      bw = bv::width(v->first()->arg(1));
      for (Expr rhs: RHSvars) {
        unsigned rbw = bv::width(rhs->first()->arg(1));
        if (bw == rbw)
          preds.push_back(mk<EQ>(v, rhs));
        else if (bw > rbw) {
          if (shift_extract) {
            for (unsigned l = 0; l <= bw - rbw; ++l )
              preds.push_back(mk<EQ>(bv::extract(rbw-1 + l,l, v), rhs));
          } else
            preds.push_back(mk<EQ>(bv::extract(rbw-1, 0, v), rhs));
        }
        else if (bw < rbw) {
          if (shift_extract) {
            for (unsigned l = 0; l <= rbw - bw; ++l )
              preds.push_back(mk<EQ>(v, bv::extract(bw-1 + l, l, rhs)));
          } else
          preds.push_back(mk<EQ>(v, bv::extract(bw-1, 0, rhs)));
        }
      }
      // X = Y1 ADD Y2
      if (use_add) {
        for (int i = 0; i < RHSvars.size(); i++){
          unsigned rbw1 = bv::width(RHSvars[i]->first()->arg(1));
          for (int j = i + 1; j < RHSvars.size(); j++){
            
            unsigned min_bw = bw; if (min_bw > rbw1) min_bw = rbw1;
            
            unsigned rbw2 = bv::width(RHSvars[j]->first()->arg(1));
            if (min_bw > rbw2) min_bw = rbw2;

            Expr X = bw == min_bw? v: bv::extract(min_bw-1, 0, v);
            Expr Y1 = rbw1 == min_bw? RHSvars[i]: bv::extract(min_bw-1, 0, RHSvars[i]);
            Expr Y2 = rbw2 == min_bw? RHSvars[j]: bv::extract(min_bw-1, 0, RHSvars[j]);

            preds.push_back(mk<EQ>(X, mk<BADD>(Y1, Y2)));
            preds.push_back(mk<EQ>(X, mk<BSUB>(Y1, Y2)));
          }
        }
      }
      // can have more operations

      lol.push_back(preds);
    }
  }
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
  

  void enumSelectFromLoLImplPart2(vector<ExprVector>& lol, int start, vector<int>& list_selection, ExprVector& selection, ExprVector& output, int op)
  {
    if (start == list_selection.size()){
      assert(selection.size() == list_selection.size());
      
      output.push_back(combineListExpr(selection, op));
      return;
    }
    for (Expr e: lol[list_selection[start]]) {
      selection.push_back(e);
      enumSelectFromLoLImplPart2(lol, start+1, list_selection, selection, output, op);
      selection.pop_back();
    }
  }

  void enumSelectFromLoLImpl(vector<ExprVector>& lol, int start, unsigned k, vector<int>& list_selection, ExprVector& output, int op)
  {
    if (k == 0){
      ExprVector selection;
      enumSelectFromLoLImplPart2(lol, 0, list_selection, selection, output, op);
      return;
    }
    for (int i = start; i <= lol.size() - k; ++i) {
      list_selection.push_back(i);
      enumSelectFromLoLImpl(lol, i+1, k-1, list_selection, output, op);
      list_selection.pop_back();
    }
  }
  
  void enumSelectKFromListofList(vector<ExprVector>& lol, unsigned k, ExprVector& output, int op){
    vector<int> list_selection;
    for (int i = 1; i <= k; i++)
      enumSelectFromLoLImpl(lol, 0, i, list_selection, output, op);
  }

  void enumSelectFromListImpl(ExprVector& list, int start, unsigned k, ExprVector& selection, ExprVector& output, int op){
    if (k == 0){
      output.push_back(combineListExpr(selection, op));
      return;
    }
    for (int i = start; i <= list.size() - k; ++i) {
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

  // ------------------------------------ END OF GRAMMAR PART ----------------------------------------- //


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

    static Expr clause_to_expression(const clause & cl, const named_vars_t & vars) {
      ExprVector z3_lits;
      for (auto && vn_liters : cl) { // for each
        for (auto && l : vn_liters.second) {
          const auto & name = std::get<0>(l);
          unsigned bitslice = std::get<1>(l);
          bool complemented = std::get<2>(l);
          auto pos = vars.find(name);
          assert(pos != vars.end());
          int n = complemented ? 0 : 1;
          auto ltexp = 
            mk<EQ>(bv::extract(bitslice,bitslice,pos->second), bv::bvnum(n, 1, pos->second->efac()) );
          z3_lits.push_back(ltexp);
        } // for each literal in that name
      } // for each name
      return combineListExpr(z3_lits, OP_CONJ );
    } // clause_to_expression
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

    Expr getModel(ExprVector& vars)
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
  

  inline void simpleCheck(const char * chcfile, unsigned bw_bound, int ANTE_Size, int CONSQ_Size,
    const std::string &clauses_fn, bool skip_original, bool skip_const_check, bool shift_ranges,
    bool use_add_sub,
    bool debug)
  {

    outs () << "Max bitwidth considered: " << bw_bound << "\n"
            << "(" << ANTE_Size << ") ==> (" << CONSQ_Size << ")"  << "\n"
            << "Skip original cnf: " <<  skip_original  << "\n"
            << "Skip const check: "  <<  skip_const_check  << "\n"
            << "Shift extraction: "  <<  shift_ranges  << "\n"
            << "Add/sub: "  <<  use_add_sub  << "\n"
            ;

    // let's load clauses
    InvariantInCnf cnf;
    cnf.LoadFromFile(clauses_fn); // will print err msg
    if (cnf._cnf_.empty())
      return; // read error

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

    // get inv vars
    InvariantInCnf::named_vars_t named_vars;
    for (auto & a: tr->srcVars) {
      if (!bv::is_bvconst(a))
        continue;
      std::stringstream sbuf;
      sbuf << *qr->origNames[a];
      const std::string & state_name = sbuf.str();
      if (state_name.length()<3)
        continue; // too short
      if (state_name.substr(0,2) != "S_")
        continue;
      std::string sn = state_name.substr(2); // S_...
      if (cnf._vars_.find(sn) != cnf._vars_.end())
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

    // ------------ let's try enhancement here --------------- //
    

    // 1. test the cnf is truly a solution
    // 2. for each clause, try enhance it
    // 3. output clauses that get extended (for on clause, they could be more than one)
    //          clause idx, results :n
    //          (define-fun ?) ... for every? (end with (check-sat), so search and clip

    int iter = 0;
    int found = 0;
    int clause_no = 0;
    for (auto && cl : cnf._cnf_) {
      ExprVector cands;
      ExprVector vars_in_this_clause;
      for (auto && var_name : cl) {
        assert (named_vars.find(var_name.first) != named_vars.end());
        vars_in_this_clause.push_back( named_vars[ var_name.first ] );
      }

      ExprVector Ante;
      ExprVector Conseq;
      vector<ExprVector> CSpredList; // {cs1: [cs1=0, cs1=1 , cs1=2 ...], cs2: [cs2=0, cs2=1 ...]}
      //enumConstPredForEachVar(vars_in_this_clause, bw_bound, CSpredList, shift_ranges);
      enumDataPredForEachVar(vars_in_this_clause, bw_bound, vars_in_this_clause, CSpredList, shift_ranges, use_add_sub);

      enumSelectKFromListofList(CSpredList, ANTE_Size, Ante, OP_CONJ);
      enumSelectKFromListofList(CSpredList, CONSQ_Size, Conseq, OP_DISJ);

      for (Expr a : Ante) {
        if (skip_const_check || !cc.isSimplifyToConst(a))
          cands.push_back(a);
        for (Expr b: Conseq) {
          auto cand = mk<IMPL>(a, b);
          if (skip_const_check || !cc.isSimplifyToConst(cand))
            cands.push_back(cand);
        }
      }
      
      outs() << "Cands : " << cands.size() << "\n";
      for (auto & cand : cands)
      {
        iter++;
        if (debug)
          outs() <<"Testing Candidate: "<<cc.printExpr(cand) << "\n";
        if (cc.checkInitiation(cand) &&
            cc.checkInductiveness(cand) &&
            cc.checkSafety())
        {
          found ++;
        }
      }
      outs () << "Status @ iter: " << iter << " @ clause " << clause_no << " found :" << found << "\n";
      clause_no ++;
    }

    outs() << "Total iter:" << iter << ", found: " << found  << " learned lemmas: " << cc.getLearnedLemmansSize() << "\n";
    // finally print out what we learned (at least the one given)
    cc.serializeInvars();
  }
}

#endif
