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
    CHCs& r;
    solver slv;

    HornRuleExt* tr;
    HornRuleExt* fc;
    HornRuleExt* qr;

    Expr lemmas2add;
    Expr invDecl;
    ExprVector invVars;
    ExprVector invVarsPr;
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

    std::map<Expr, ExprSet> trNondets;

    ExprSet candConds;
    ExprSet jumpConds;
    RndLearnerV2* exprsmpl;       // for samples used in various pieces of termination analysis

    int nontlevel;
    bool lightweight;

    public:

    TermCheck (ExprFactory& _efac, EZ3& _z3, CHCs& _r, solver _slv, int _n, bool _l) :
      efac(_efac), z3(_z3), u(efac), r(_r), slv(_slv), nontlevel(_n), lightweight(_l),
      tr(NULL), fc(NULL), qr(NULL)
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

    void checkPrerequisites ()
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
      outs () << "loopGuard = " << *loopGuard << "\n";
      ExprSet lg_vars;
      expr::filter (loopGuard, bind::IsConst(), std::inserter (lg_vars, lg_vars.begin ()));

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
      for (auto & v : invVars) if (bind::isIntConst(v))
      {
        elements.insert(v);
        elements.insert(additiveInverse(v));
      }
    }

    /* Preps for syntax-guided synthesis of ranking functions and program refinements */
    void getSampleExprs()
    {
      exprsmpl = new RndLearnerV2(efac, z3, r, false, true, lightweight);
      for (auto& dcl: r.decls)
      {
        // actually, should be one iter here
        exprsmpl->initializeDecl(dcl);
        exprsmpl->doSeedMining(dcl->arg(0), seeds);
      }

      exprsmpl->calculateStatistics();
      exprsmpl->categorizeCHCs();
      if (lightweight)
      {
        lemmas2add = mk<TRUE>(efac);
      }
      else
      {
        exprsmpl->houdini(seeds, true, false);
        lemmas2add = conjoin(exprsmpl->getlearnedLemmas(0), efac);
      }

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
        mutantsPreppedTmp.insert(mk<GT>(ghostVars[0], a));
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
      if (!isOp<ComparissonOp>(e)) return NULL;

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
        e = replaceAll(e, invVars, invVarsPr);
        Expr newGeq = mk<GT>(ghostVarsPr[0], e);
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
      if (lightweight)
      {
        for (auto & a : initConds0)
          for (auto & b : initConds1)
            for (auto & c : iteConds)
            {
              ExprSet a1; a1.insert(a);
              ExprSet b1; b1.insert(b);
              ExprSet c1; c1.insert(c);

              if (!assembleLexCand(a1, b1, c1)) continue;
              if (checkCand()) return true;
            }
      }
      else
      {
        assembleLexCand(initConds0, initConds1, iteConds);
        if (checkCand()) return true;
      }
      return false;
    }

    bool assembleLexCand(ExprSet& initConds0, ExprSet& initConds1, ExprSet& iteConds)
    {
      outs () << "< " << *conjoin(initConds0, efac) << "; "
                      << *conjoin(initConds1, efac) << "; "
                      << *conjoin(iteConds, efac)   << " >";

      // assemble an initCond-part for the base rule
      int cnt = 0;
      for (auto e : initConds0)
      {
        e = replaceAll(e, invVars, invVarsPr);
        Expr newGeq = mk<GT>(ghostVarsPr[0], e);
        if (!u.implies(conjoin(candConds, efac), newGeq))
        {
          cnt++;
          candConds.insert(newGeq);
        }
      }
      for (auto e : initConds1)
      {
        e = replaceAll(e, invVars, invVarsPr);
        Expr newGeq = mk<GT>(ghostVarsPr[1], e);
        if (!u.implies(conjoin(candConds, efac), newGeq))
        {
          cnt++;
          candConds.insert(newGeq);
        }
      }
      for (auto e : iteConds)
      {
        e = replaceAll(e, invVars, invVarsPr);
        Expr newGeq = mk<GT>(ghostVarsPr[1], e);
        if (!u.implies(conjoin(jumpConds, efac), newGeq))
        {
          cnt++;
          jumpConds.insert(newGeq);
        }
      }
      if (cnt == 0) return false;

      // then, assemble decrements for the tr rule

      ExprSet e1;
      e1.insert(ghostGuard);
      e1.insert(mk<EQ>(ghostVarsPr[0], ghostVars[0]));
      e1.insert(decGhost1);

      ExprSet e2;
      e2.insert(mkNeg(ghostGuard));
      e2.insert(decGhost0);
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
      return true;
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
        RndLearnerV2 ds(efac, z3, *cand, true, true, false);
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

      getSampleExprs();

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
      if (lemmas2add == NULL) getSampleExprs();
      bool res;

      // gradual brute force.. needs more optimizations
      res = tryLexRankingFunctionCandidates(elements, elements, elements);

      if (res) return res;
      res = tryLexRankingFunctionCandidates(elements, elements, seedsPrepped);

      if (res) return res;
      res = tryLexRankingFunctionCandidates(seedsPrepped, elements, seedsPrepped);

      if (res) return res;
      res = tryLexRankingFunctionCandidates(seedsPrepped, seedsPrepped, seedsPrepped);

      if (res) return res;
      res = tryLexRankingFunctionCandidates(seedsPrepped, seedsPrepped, mutantsPrepped);

      if (res) return res;
      res = tryLexRankingFunctionCandidates(mutantsPrepped, seedsPrepped, mutantsPrepped);

      if (res) return res;
      res = tryLexRankingFunctionCandidates(mutantsPrepped, mutantsPrepped, mutantsPrepped);

      return res;
    }

    bool checkNonterm()
    {
      // Initially, check if we can enter the loop from the initial state
      Expr initCheck = mk<AND>(loopGuard, fc->body);
      initCheck = replaceAll(initCheck, invVarsPr, invVars);
      if (!u.isSat(initCheck))
      {
        outs() << "\nLoop body is unreachable\nTerminates!\n";
        exit(0);
      }

      if (slv == spacer) getNondets(tr->body, trNondets);

      // Then, check if starting from a state satisfying the loop guard
      // we can reach state also satisfying the loop guard
      if (!resolveTrNondeterminism(loopGuard)) return false;

      // Then, get some invariants and repeat
      if (lemmas2add == NULL) getSampleExprs();

      Expr loopGuardEnhanced = mk<AND>(lemmas2add, loopGuard);
      Expr renamedLoopGuard = replaceAll(loopGuardEnhanced, invVars, invVarsPr);

      Expr trBody = mk<AND>(tr->body, lemmas2add);
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
        Expr initCheck = mk<AND>(refinee, fc->body);
        initCheck = replaceAll(initCheck, invVarsPr, invVars);

        if (!u.isSat(initCheck)) continue;

        if (u.implies(loopGuardEnhanced, refinee)) continue;

        Expr loopGuardEnhancedTry = mk<AND>(refinee, loopGuardEnhanced);

        if (!u.isSat(loopGuardEnhancedTry)) continue;
        Expr refineePr = replaceAll(refinee, invVars, invVarsPr);
        Expr loopGuardEnhancedTryPr = replaceAll(loopGuardEnhancedTry, invVars, invVarsPr);

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
      Expr trBody = tr->body;
      if (lemmas2add != NULL) trBody = mk<AND>(trBody, lemmas2add);

      Expr updTrBody = mk<AND>(refinedGuard, trBody);
      Expr renamedLoopGuard = replaceAll(refinedGuard, invVars, invVarsPr);

      // try to prove universal non-termination
      if (slv == spacer)
      {
        CHCs r1 = r;
        for (auto & a : r1.chcs)
          if (a.isFact) a.body = mk<AND>(renamedLoopGuard, a.body);
          else if (a.isInductive) a.body = updTrBody;
          else if (a.isQuery) a.body = mk<NEG>(refinedGuard);

        if (!lightweight)
        {
          bool res = r1.checkWithSpacer();
          if (res && refinedGuard == loopGuard) outs () << "Trully universal\n";

          if (res)
          {
            outs () << "refined with " << *refinedGuard << "\n";
            return false;
          }
        }

        // very naive method to eliminate nondeterminism in Tr witout expensive AE-solving
        for (auto & a : trNondets)
        {
          for (auto & b : a.second)
          {
            if (!u.isSat(updTrBody, b)) continue;
            for (auto & r : r1.chcs) if (r.isInductive) r.body = mk<AND>(updTrBody, b);
            bool res = r1.checkWithSpacer();
            if (res)
            {
              outs () << "refined with " << *refinedGuard << " and " << *b << "\n";
              return false;
            }
          }
        }

        return true;
      }
      else
      {
        bool res = u.implies(updTrBody, renamedLoopGuard);
        if (res && refinedGuard == loopGuard) outs () << "Trully universal\n";
        if (res) return false;

        // for some cases with MOD, DIV, and nonlinear arithmetic
        // we do not have a support in AE-VAL
        if (findNonlin(refinedGuard) || findNonlin(trBody)) return true;

        ExprSet quantified;
        quantified.insert(tr->locVars.begin(), tr->locVars.end());
        quantified.insert(invVarsPr.begin(), invVarsPr.end());

        Expr refinedTrBody = mk<AND>(trBody, renamedLoopGuard);

        // finally, try to prove existential non-termination
        AeValSolver ae(refinedGuard, refinedTrBody, quantified);
        return ae.solve();
      }
    }
  };

  inline void terminationAnalysis(string chcfile, int nonterm, int rank, int mrg, solver slv, bool lw)
  {
    std::srand(std::time(0));

    ExprFactory efac;
    EZ3 z3(efac);
    CHCs ruleManager(efac, z3);
    ruleManager.parse(chcfile);
    if (mrg > 1)
    {
      outs() << "Transforming program such that each new iteration "
             << "corresponds to " << mrg << " original iterations\n";
      ruleManager.mergeIterations(*ruleManager.decls.begin(), mrg);
    }
    TermCheck a(efac, z3, ruleManager, slv, nonterm, lw);
    a.checkPrerequisites();

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
