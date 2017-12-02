#ifndef TERMCHECK__HPP__
#define TERMCHECK__HPP__

#include "Horn.hpp"
#include "RndLearnerV2.hpp"
#include "ae/SMTUtils.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  
  typedef enum {kind, freqhorn, spacer} solver;

  class TermCheck
  {
    private:

    ExprFactory& efac;
    EZ3& z3;
    SMTUtils u;
    solver slv;

    HornRuleExt* tr;
    HornRuleExt* fc;
    HornRuleExt* qr;

    Expr lemmas2add;
    Expr invDecl;
    ExprVector invVars;
    ExprVector invVarsPr;
    Expr maxInt;
    int invVarsSz;

    string ghostVar_pref = "gh_";
    CHCs* cand;
    ExprVector ghostVars;
    ExprVector ghostVarsPr;
    Expr decGhost0;
    Expr decGhost1;
    Expr ghost0Minus1;
    Expr ghost1Minus1;
    Expr ghostAss;
    Expr ghostGuard;

    ExprSet elements;
    ExprSet seeds;
    ExprSet seedsPrepped;
    ExprSet mutants;
    ExprSet mutantsPrepped;
    Expr loopGuard;

    ExprSet candConds;
    ExprSet jumpConds;
    RndLearnerV2* exprsmpl;       // for samples used in various pieces of termination analysis

    int nontlevel;

    public:

    TermCheck (ExprFactory& _efac, EZ3& _z3, solver _slv, int _n) :
      efac(_efac), z3(_z3), u(efac), slv(_slv), nontlevel(_n)
    {
      for (int i = 0; i < 2; i++)
      {
        Expr new_name = mkTerm<string> (ghostVar_pref + to_string(i), efac);
        Expr var = bind::intConst(new_name);
        ghostVars.push_back(var);

        new_name = mkTerm<string> (ghostVar_pref + to_string(i) + "'", efac);
        var = bind::intConst(new_name);
        ghostVarsPr.push_back(var);
      }

      ghost0Minus1 = mk<MINUS>(ghostVars[0], mkTerm (mpz_class (1), efac));
      ghost1Minus1 = mk<MINUS>(ghostVars[1], mkTerm (mpz_class (1), efac));
      decGhost0 = mk<EQ>(ghostVarsPr[0], ghost0Minus1);
      decGhost1 = mk<EQ>(ghostVarsPr[1], ghost1Minus1);
      ghostAss = mk<LT>(ghostVars[0], mkTerm (mpz_class (0), efac));
      ghostGuard = mk<GT>(ghostVars[1], mkTerm (mpz_class (0), efac)); // for lexicographic only
    }

    void checkPrerequisites (CHCs& r)
    {
      if (r.decls.size() > 1)
      {
        outs() << "Nested loops not supported\n";
        exit(0);
      }

      if (r.chcs.size() < 2 || r.chcs.size() > 3)
      {
        outs() << "Please provide a file with two or three rules\n";
        exit(0);
      }

      for (auto & a : r.chcs)
        if (a.isInductive) tr = &a;
        else if (a.isFact) fc = &a;
        else if (a.isQuery) qr = &a;

      invDecl = tr->srcRelation;
      invVars = tr->srcVars;
      invVarsPr = tr->dstVars;
      invVarsSz = invVars.size();

      if (tr == NULL)
      {
        outs() << "TR is missing\n";
        exit(0);
      }

      if (fc == NULL)
      {
        outs() << "INIT is missing\n";
        exit(0);
      }

      loopGuard = r.getPrecondition(*r.decls.begin());
      if (qr == NULL)
      {
        qr = new HornRuleExt();
        qr->srcRelation = invDecl;
        qr->srcVars = invVars;
        qr->body = loopGuard;
        qr->dstRelation = mkTerm<string> ("err", efac);
        qr->head = bind::boolConstDecl(qr->dstRelation);
        qr->isQuery = true;

        r.addFailDecl(qr->dstRelation);
        r.addRule(qr);

        for (auto & a : r.chcs)       // r.chcs changed by r.addRule, so pointers to its elements are broken
          if (a.isInductive) tr = &a;
          else if (a.isFact) fc = &a;
      }
      else
      {
        // requirement in the old input format
        assert(u.isEquiv(qr->body, loopGuard));
      }

      /* Preps for syntax-guided synthesis of ranking functions and program refinements */

      exprsmpl = new RndLearnerV2(efac, z3, r, false, true);

      for (auto& dcl: r.decls)
      {
        // actually, should be one iter here
        exprsmpl->initializeDecl(dcl);
        exprsmpl->doSeedMining(dcl->arg(0), seeds);
      }

      exprsmpl->calculateStatistics();
      exprsmpl->categorizeCHCs();
      exprsmpl->houdini(seeds, true, false);
      lemmas2add = conjoin(exprsmpl->getlearnedLemmas(0), efac);

      vector<int> consts = exprsmpl->getAllConsts();
      auto rit = consts.rbegin();
      maxInt = mkTerm (mpz_class (*rit + 1), efac); // GF: hacked (+1)

      elements.insert(maxInt);      // in some cases, it helps, in some other cases it hurts...
      for (auto & v : invVars) elements.insert(mult(v));

      for (auto s : seeds)
      {
        s = convertToTerm(s);
        if (s == NULL) continue;
        if (find(std::begin(elements), std::end (elements), s) == std::end(elements))
          seedsPrepped.insert(s);
      }

      for (int i = 0; i < 100; i++) // could consider more than 100 mutants as well
        mutants.insert(exprsmpl->getFreshCand());

      for (auto m : mutants)
      {
        m = convertToTerm(m);
        if (m == NULL) continue;
        if (find(std::begin(elements), std::end (elements), m) == std::end(elements) &&
            find(std::begin(seedsPrepped), std::end (seedsPrepped), m) == std::end(seedsPrepped))
          mutantsPrepped.insert(m);
      }

      // optimize a little bit
      ExprSet mutantsPreppedTmp;
      for (auto a : mutantsPrepped)
      {
        mutantsPreppedTmp.insert(mk<GEQ>(ghostVars[0], a));
      }

      u.removeRedundantConjuncts(mutantsPreppedTmp);

      mutantsPrepped.clear();
      for (auto a : mutantsPreppedTmp)
      {
        mutantsPrepped.insert(a->right());
      }
    }

    Expr convertToTerm(Expr e)
    {
      if (isOpX<OR>(e)) return NULL;

      assert(isOp<ComparissonOp>(e));
      int cnst = lexical_cast<int>(e->right());
      if (cnst < 0) return NULL;
      else if (cnst == 0) return e->left();
      else return mk<PLUS>(e->left(), e->right());
    }

    bool assembleCand(ExprSet& initConds)
    {
      // assemble an initCond-part for the base rule
      int cnt = 0;

      for (auto e : initConds)
      {
        for (int i = 0; i < invVarsSz; i++) e = replaceAll(e, invVars[i], invVarsPr[i]);
        Expr newGeq = mk<GEQ>(ghostVarsPr[0], e);
        if (!u.implies(conjoin(candConds, efac), newGeq))
        {
          cnt++;
          candConds.insert(newGeq);
        }
      }
      if (cnt == 0) return false;

      // now, preparing the new rules (same for every attempt)

      cand = new CHCs(efac, z3);

      HornRuleExt fc_new = *fc;
      HornRuleExt tr_new = *tr;
      HornRuleExt qr_new = *qr;

      ExprVector vars = invVars;
      vars.push_back(ghostVars[0]);
      ExprVector varsPr = invVarsPr;
      varsPr.push_back(ghostVarsPr[0]);
      cand->addDecl(invDecl, vars);

      tr_new.srcVars = vars;
      qr_new.srcVars = vars;
      fc_new.dstVars = varsPr;
      tr_new.dstVars = varsPr;

      ExprSet tmp;
      getConj(fc_new.body, tmp);
      tmp.insert(candConds.begin(), candConds.end());
      fc_new.body = conjoin(tmp, efac);

      tmp.clear();
      getConj(tr_new.body, tmp);
      tmp.insert(decGhost0);
      tr_new.body = conjoin(tmp, efac);

      tmp.clear();
      getConj(qr_new.body, tmp);
      tmp.insert(ghostAss);
      qr_new.body = conjoin(tmp, efac);

      cand->addRule(&fc_new);
      cand->addRule(&tr_new);
      cand->addRule(&qr_new);

      cand->addFailDecl(qr->dstRelation);

      return true;
    }

    bool tryLexRankingFunctionCandidates(ExprSet& initConds0, ExprSet& initConds1, ExprSet& iteConds)
    {
      // TODO: any of these loops could be removed, and sets of candidates could be checked at once
      for (auto & a : initConds0)
        for (auto & b : initConds1)
          for (auto & c : iteConds)
          {
            ExprSet a1;
            ExprSet b1;
            ExprSet c1;
            a1.insert(a);
            b1.insert(b);
            c1.insert(c);
            //  a1 = initConds0;
            //  b1 = initConds1;
            //  c1 = iteConds;
            assembleLexCand(a1, b1, c1);
            outs () << "< " << *conjoin(a1, efac) << "; "
                            << *conjoin(b1, efac) << "; "
                            << *conjoin(c1, efac) << " >";
            if (checkCand()) return true;
          }
      return false;
    }

    void assembleLexCand(ExprSet& initConds0, ExprSet& initConds1, ExprSet& iteConds)
    {
      candConds.clear();     // ideally, it should work w/o clearing,..
      jumpConds.clear();     // but in reality the CHC systems become too complex for solving

      // assemble an initCond-part for the base rule

      for (auto e : initConds0)
      {
        for (int i = 0; i < invVarsSz; i++) e = replaceAll(e, invVars[i], invVarsPr[i]);
        candConds.insert(mk<GEQ>(ghostVarsPr[0], e));
      }
      for (auto e : initConds1)
      {
        for (int i = 0; i < invVarsSz; i++) e = replaceAll(e, invVars[i], invVarsPr[i]);
        candConds.insert(mk<GEQ>(ghostVarsPr[1], e));
      }
      for (auto e : iteConds)
      {
        for (int i = 0; i < invVarsSz; i++) e = replaceAll(e, invVars[i], invVarsPr[i]);
        jumpConds.insert(mk<GEQ>(ghostVarsPr[1], e));
      }

      // then, assemble decrements for the tr rule

      ExprSet e1;
      e1.insert(ghostGuard);
      e1.insert(mk<EQ>(ghostVarsPr[0], ghostVars[0]));
      e1.insert(mk<EQ>(ghostVarsPr[1], ghost1Minus1));

      ExprSet e2;
      e2.insert(mkNeg(ghostGuard));
      e2.insert(mk<EQ>(ghostVarsPr[0], ghost0Minus1));
      e2.insert(jumpConds.begin(), jumpConds.end());

      // now, preparing the new rules (same for every attempt)

      cand = new CHCs(efac, z3);

      HornRuleExt fc_new = *fc;
      HornRuleExt tr_new = *tr;
      HornRuleExt qr_new = *qr;

      ExprVector vars = invVars;
      vars.push_back(ghostVars[0]);
      vars.push_back(ghostVars[1]);
      ExprVector varsPr = invVarsPr;
      varsPr.push_back(ghostVarsPr[0]);
      varsPr.push_back(ghostVarsPr[1]);
      cand->addDecl(invDecl, vars);

      tr_new.srcVars = vars;
      qr_new.srcVars = vars;
      fc_new.dstVars = varsPr;
      tr_new.dstVars = varsPr;

      ExprSet tmp;
      getConj(fc_new.body, tmp);
      tmp.insert(candConds.begin(), candConds.end());
      fc_new.body = conjoin(tmp, efac);

      tmp.clear();
      getConj(tr_new.body, tmp);
      tmp.insert(mk<OR>(conjoin(e1, efac), conjoin(e2, efac)));
      tr_new.body = conjoin(tmp, efac);

      tmp.clear();
      getConj(qr_new.body, tmp);
      tmp.insert(ghostAss);
      qr_new.body = conjoin(tmp, efac);

      cand->addRule(&fc_new);
      cand->addRule(&tr_new);
      cand->addRule(&qr_new);

      cand->addFailDecl(qr->dstRelation);
    }

    bool checkCand(bool goodtogo = true)
    {
      if (!goodtogo)
      {
        outs () << "  ---> skip checking\n";
        return false;
      }

      // cand->print();
      bool res;

      switch(slv)
      {
        case kind: res = checkCandWithKind(); break;
        case freqhorn: res = checkCandWithFreqhorn(); break;
        case spacer: res = checkCandWithSpacer(); break;
      }

      if (res)
      {
        outs () << "  ---> Terminates!\n";
      }
      else
      {
        outs () << "  ---> not a good candidate\n";
      }
      return res;
    }

    bool checkCandWithKind(int bnd = 100)
    {
      BndExpl be(*cand, lemmas2add);
      bool success = false;
      int i;
      for (i = 2; i < bnd; i++)
      {
        if (!be.kIndIterBase(i, i))
        {
          break;
        }
        if (be.kIndIter(i, i))
        {
          success = true;
          break;
        }
      }
      return success;
    }

    bool checkCandWithFreqhorn(int bnd = 20)
    {
      // TODO: try reusing learnedLemmas between runs
      BndExpl be(*cand);
      bool bug = !(be.exploreTraces(2, bnd, false));
      if (bug) return false;
      else
      {
        outs () << "  keep proving.. ";
        RndLearnerV2 ds(efac, z3, *cand, true, true);
        ds.categorizeCHCs();

        for (auto& dcl: cand->decls) ds.initializeDecl(dcl);

        ExprSet cands;
        for (auto& dcl: cand->decls) ds.doSeedMining (dcl->arg(0), cands);

        bool success = ds.houdini(cands, true, false);
        if (!success)
        {
          outs () << "  keep proving.. ";
          ds.calculateStatistics();
          ds.prioritiesDeferred();

          success = ds.synthesize(100, 3, 3);
        }
        return success;
      }
    }

    bool checkCandWithSpacer()
    {
      // experimentally augment encoding:
      for (auto & r : cand->chcs)
        if (r.srcRelation == invDecl)
          r.body = mk<AND>(r.body, lemmas2add);

      return cand->checkWithSpacer();
    }

    bool synthesizeRankingFunction()
    {
      bool res = false;

      // check all elements first:
      // TODO: could be done one-by-one
      outs() << "element #" << candConds.size() << ": " << *conjoin(elements, efac);
      res = checkCand(assembleCand(elements));
      if (res) return res;

      // otherwise check seeds:
      // TODO: could be done one-by-one
      outs() << "seed #" << candConds.size() << ": " << *conjoin(seedsPrepped, efac);
      res = checkCand(assembleCand(seedsPrepped));
      if (res) return res;

      // otherwise check mutants in a loop:
      for (auto initCond : mutantsPrepped)
      {
        // TODO: could be done in batches
        ExprSet a; a.insert(initCond);
        outs() << "mutant #" << candConds.size() << ": " << *initCond;
        res = checkCand(assembleCand(a));
        if (res) break;
      }

      // if !res, need to try lexicographic ranking function
      return res;
    }

    bool synthesizeLexRankingFunction()
    {
      bool res;

      // gradual brute force.. needs more optimizations
      res = tryLexRankingFunctionCandidates(elements, elements, elements);

      if (res) return res;
      res = tryLexRankingFunctionCandidates(seedsPrepped, seedsPrepped, seedsPrepped);

      if (res) return res;
      res = tryLexRankingFunctionCandidates(mutantsPrepped, mutantsPrepped, mutantsPrepped);

      return res;
    }

    bool checkNonterm()
    {
      Expr loopGuardEnhanced = mk<AND>(lemmas2add, loopGuard);
      Expr renamedLoopGuard = loopGuardEnhanced;
      for (int i = 0; i < invVarsSz; i++)
        renamedLoopGuard = replaceAll(renamedLoopGuard, invVars[i], invVarsPr[i]);

      Expr trBody = mk<AND>(tr->body, lemmas2add);

      // Initially, check if the given restrictions in init are enough for non-terminating

      if (!resolveTrNondeterminism(loopGuardEnhanced)) return false;

      // Otherwise, try to resolve nondeterminism in init

      bool nondeterministicIn = false;

      // check if there is a nondeterminism in init

      for (int i = 0; i < invVarsSz; i++)
      {
        Expr v = invVarsPr[i];
        nondeterministicIn = !u.hasOneModel(v, fc->body);
        if (nondeterministicIn) break;
      }

      // try to refine the init conditions gradually:

      bool res = resolveInNondeterminism(seeds, loopGuardEnhanced, 1);
      if (res) res = resolveInNondeterminism(mutants, loopGuardEnhanced, 1);
      return res;
    }

    bool resolveInNondeterminism(ExprSet& refineCands, Expr loopGuardEnhanced, int depth)
    {
      if (depth > nontlevel) return true;    // refinement becomes too complex

      for (auto & refinee : refineCands)     // TODO: optimize
      {
        if (u.implies(loopGuardEnhanced, refinee)) continue;

        Expr loopGuardEnhancedTry = mk<AND>(refinee, loopGuardEnhanced);
        Expr loopGuardEnhancedTryPr = loopGuardEnhancedTry;

        if (!u.isSat(loopGuardEnhancedTry)) continue;
        Expr refineePr = refinee;
        for (int j = 0; j < invVarsSz; j++)
        {
          refineePr = replaceAll(refineePr, invVars[j], invVarsPr[j]);
          loopGuardEnhancedTryPr = replaceAll(loopGuardEnhancedTryPr, invVars[j], invVarsPr[j]);
        }

        if (!u.isSat (loopGuardEnhancedTryPr, fc->body)) continue;

        bool res = resolveTrNondeterminism(loopGuardEnhancedTry);
        if (! res)
        {
          return res;
        }
        else res = resolveInNondeterminism(refineCands, loopGuardEnhancedTry, depth+1);

        if (! res)
        {
          return res;
        }
      }
      return true;
    }

    bool resolveTrNondeterminism(Expr refinedGuard)
    {
      Expr trBody = mk<AND>(tr->body, lemmas2add);
      Expr renamedLoopGuard = refinedGuard;
      for (int i = 0; i < invVarsSz; i++)
        renamedLoopGuard = replaceAll(renamedLoopGuard, invVars[i], invVarsPr[i]);

      // for some cases with MOD, DIV, and nonlinear arithmetic
      // we do not have a support in AE-VAL
      // so try a simple quantifer-free check
      if (u.implies(mk<AND>(refinedGuard, trBody), renamedLoopGuard)) return false;

      ExprSet quantified;
      quantified.insert(tr->locVars.begin(), tr->locVars.end());
      quantified.insert(invVarsPr.begin(), invVarsPr.end());

      Expr refinedTrBody = mk<AND>(trBody, renamedLoopGuard);
      AeValSolver ae(refinedGuard, refinedTrBody, quantified);
      return ae.solve();
    }
  };

  inline void terminationAnalysis(string chcfile, int nonterm, int rank, solver slv)
  {
    std::srand(std::time(0));

    ExprFactory efac;
    EZ3 z3(efac);
    CHCs ruleManager(efac, z3);
    ruleManager.parse(chcfile);
    TermCheck a(efac, z3, slv, nonterm);
    a.checkPrerequisites(ruleManager);

    //    outs () << "Sketch encoding:\n";
    //    ruleManager.print();

    if (nonterm == 0)
    {
      outs () << "Skipping non-termination proving\n";
    }
    else
    {
      if (!a.checkNonterm())
      {
        outs () << "Does not terminate\n";
        return;
      }
    }

    if (rank == 0)
    {
      outs () << "Skipping ranking function synthesis\n";
    }
    else if (rank == 1)
    {
      a.synthesizeRankingFunction();
    }
    else if (rank == 2)
    {
      a.synthesizeLexRankingFunction();
    }
    else if (rank == 3)
    {
      bool res = a.synthesizeRankingFunction();
      if (! res) a.synthesizeLexRankingFunction();
    }
  }
}

#endif
