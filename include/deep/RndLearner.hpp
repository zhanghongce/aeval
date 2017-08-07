#ifndef RNDLEARNER__HPP__
#define RNDLEARNER__HPP__

#include <chrono>
#include "Horn.hpp"
#include "CodeSampler.hpp"
#include "Distribution.hpp"
#include "LinCom.hpp"
#include "Distributed.hpp"
#include "ae/SMTUtils.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class RndLearner
  {
  private:

    ExprFactory &m_efac;
    EZ3 &m_z3;
    SMTUtils u;
    ufo::ZSolver<ufo::EZ3> m_smt_solver;
    vector<ufo::ZSolver<ufo::EZ3>> m_smt_safety_solvers;
    map<int, bool> safety_progress;

    CHCs& ruleManager;
    vector<Expr> decls;          //  container only mutated by `initializeDecl`
    vector<LAfactory> lfs;       // zips with `decls`; container only mutated by `initializeDecl`
    vector<Expr> curCandidates;
    map<int, int> incomNum;
    int numOfSMTChecks;

    const bool densecode;           // catch various statistics about the code (mostly, frequences) and setup the prob.distribution based on them
    const bool shrink;              // consider only a small subset of int constants and samples from the code
    const bool aggressivepruning;   // aggressive pruning of the search space based on SAT/UNSAT (WARNING: may miss some invariants)

    void reportLemma(boost::mpi::communicator world, unsigned declIdx, LAdisj& disj) {
      WorkerResult result { WorkerResultKindLemma, declIdx, unique_ptr<LAdisj>(new LAdisj(disj)) };
      world.send(0, MSG_TAG_NORMAL, std::shared_ptr<WorkerResult>(&result, [](WorkerResult*){}));
    }

    void reportFailure(boost::mpi::communicator world, unsigned declIdx, LAdisj& disj) {
      WorkerResult result { WorkerResultKindFailure, declIdx, unique_ptr<LAdisj>(new LAdisj(disj)) };
      world.send(0, MSG_TAG_NORMAL, std::shared_ptr<WorkerResult>(&result, [](WorkerResult*){}));
    }

  public:

    RndLearner (ExprFactory &efac, EZ3 &z3, CHCs& r, bool b1, bool b2, bool b3) :
      m_efac(efac), m_z3(z3), ruleManager(r), m_smt_solver (z3),
      u(efac), densecode(b1), shrink(b2),
      aggressivepruning(b3) {}

    inline int invNumber() { return decls.size(); }

    inline LAfactory& getLAFactory(unsigned inv) { return lfs[inv]; }

    inline bool isSMTSat(Expr a) { return u.isSat(a); }

    void printCandidates() {
      for (size_t i = 0; i < invNumber(); i++) {
        outs() << "candidate for " << *(decls[i]) << ": "
               << *(curCandidates[i]) << "\n";
      }
    }

    Expr convertDisjToExpr(int dIdx, LAdisj& disj) {
      return lfs[dIdx].toExpr(disj);
    }

    bool isTautology (Expr a)     // adjusted for big disjunctions
    {
      if (isOpX<TRUE>(a)) return true;

      ExprSet disjs;
      getDisj(a, disjs);
      if (disjs.size() == 1) return false;

      map<ExprSet, ExprSet> varComb;
      for (auto &a : disjs)
      {
        ExprSet avars;
        expr::filter (a, bind::IsConst(), std::inserter (avars, avars.begin ()));
        varComb[avars].insert(mkNeg(a));
      }

      m_smt_solver.reset();

      bool res = false;
      for (auto &v : varComb )
      {
        m_smt_solver.assertExpr(conjoin(v.second, m_efac));
        if (!m_smt_solver.solve ())
        {
          res = true; break;
        }
      }
      return res;
    }

    bool checkCandidates(boost::mpi::communicator world)
    {
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isQuery) continue;

        m_smt_solver.reset();

        int ind1;  // to be identified later
        int ind2 = getVarIndex(hr.dstRelation, decls);

        // pushing body
        m_smt_solver.assertExpr (hr.body);

        Expr cand1;
        Expr cand2;
        Expr lmApp;

        // pushing src relation
        if (!isOpX<TRUE>(hr.srcRelation))
        {
          ind1 = getVarIndex(hr.srcRelation, decls);
          LAfactory& lf1 = lfs[ind1];

          cand1 = curCandidates[ind1];
          for (int i = 0; i < hr.srcVars.size(); i++)
          {
            cand1 = replaceAll(cand1, lf1.getVarE(i), hr.srcVars[i]);
          }
          m_smt_solver.assertExpr(cand1);

          lmApp = conjoin(lf1.learntExprs, m_efac);
          for (int i = 0; i < hr.srcVars.size(); i++)
          {
            lmApp = replaceAll(lmApp, lf1.getVarE(i), hr.srcVars[i]);
          }
          m_smt_solver.assertExpr(lmApp);
        }

        // pushing dst relation
        cand2 = curCandidates[ind2];
        LAfactory& lf2 = lfs[ind2];

        for (int i = 0; i < hr.dstVars.size(); i++)
        {
          cand2 = replaceAll(cand2, lf2.getVarE(i), hr.dstVars[i]);
        }

        auto neggedInvApp2 = mk<NEG>(cand2);
        m_smt_solver.assertExpr(neggedInvApp2);

        boost::tribool res = m_smt_solver.solve ();
        if (res)    // SAT   == candidate failed
        {
          curCandidates[ind2] = mk<TRUE>(m_efac);
          return checkCandidates(world);
        }
      }

      bool res = false;
      for (int ind2 = 0; ind2 < curCandidates.size(); ind2++)
      {
        Expr cand2 = curCandidates[ind2];
        LAfactory& lf2 = lfs[ind2];
        if (isOpX<TRUE>(cand2))
        {
          outs () << "    => bad candidate for " << *decls[ind2] << "\n";
          if (aggressivepruning) {
            LAdisj& failedDisj = lf2.samples.back();
            reportFailure(world, ind2, failedDisj);
            lf2.assignPrioritiesForFailed(failedDisj);
          }
        }
        else
        {
          outs () << "    => learnt lemma for " << *decls[ind2] << "\n";
          res = true;
          LAdisj& learntDisj = lf2.samples.back();
          lf2.assignPrioritiesForLearnt(learntDisj);
          lf2.learntExprs.insert(cand2);
          lf2.learntLemmas.push_back(lf2.samples.size() - 1);
          reportLemma(world, ind2, learntDisj);
        }
      }
      return res;
    }

    bool checkSafety()
    {
      int num = 0;
      for (auto &hr: ruleManager.chcs)
      {
        if (!hr.isQuery) continue;
        num++;

        int ind = getVarIndex(hr.srcRelation, decls);
        Expr invApp = curCandidates[ind];
        if (safety_progress[num-1] == true) continue;

        LAfactory& lf = lfs[ind];
        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          invApp = replaceAll(invApp, lf.getVarE(i), hr.srcVars[i]);
        }

        m_smt_safety_solvers[num-1].assertExpr(invApp);
        safety_progress[num-1] = !m_smt_safety_solvers[num-1].solve ();
      }

      for (auto a : safety_progress) if (a.second == false) return false;
      return true;
    }

    void setupSafetySolver()
    {
      // setup the safety solver
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isQuery)
        {
          m_smt_safety_solvers.push_back(ufo::ZSolver<ufo::EZ3>(m_z3));
          m_smt_safety_solvers.back().assertExpr (hr.body);
          safety_progress[safety_progress.size()] = false;
        }
      }
    }

    void initializeDecl(Expr invDecl)
    {
      assert (invDecl->arity() > 2);

      decls.push_back(invDecl->arg(0));
      lfs.push_back(LAfactory(m_efac, densecode, aggressivepruning));  // indeces at decls, lfs, and curCandidates should be the same
      curCandidates.push_back(NULL);

      LAfactory& lf = lfs.back();

      // collect how many rules has invDecl on the right side
      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation == decls.back())
          incomNum[invNumber()-1]++;
      }

      for (int i = 1; i < invDecl->arity()-1; i++)
      {
        Expr new_name = mkTerm<string> ("__v__" + to_string(i - 1), m_efac);
        Expr var = bind::mkConst(new_name, invDecl->arg(i));
        lf.addVar(var);
      }

      vector<CodeSampler> css;
      set<int> orArities;
      set<int> progConstsTmp;
      set<int> progConsts;
      set<int> intCoefs;

      // analize each rule separately:
      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation != decls.back() && hr.srcRelation != decls.back()) continue;

        css.push_back(CodeSampler(hr, invDecl, lf.getVars(), lf.nonlinVars));
        css.back().analyzeCode(densecode, shrink);

        // convert intConsts to progConsts and add additive inverses (if applicable):
        for (auto &a : css.back().intConsts)
        {
          progConstsTmp.insert( a);
          progConstsTmp.insert(-a);
        }

        // same for intCoefs
        for (auto &a : css.back().intCoefs)
        {
          intCoefs.insert( a);
          intCoefs.insert(-a);
        }
      }

      outs() << "Multed vars: ";
      for (auto &a : lf.nonlinVars)
      {
        outs() << *a.first << " = " << *a.second << "\n";
        lf.addVar(a.second);
      }

      for (auto &a : intCoefs) if (a != 0) lf.addIntCoef(a);

      for (auto &a : intCoefs)
      {
        for (auto &b : progConstsTmp)
        {
          progConsts.insert(a*b);
        }
      }

      // sort progConsts and push to vector:
      while (progConsts.size() > 0)
      {
        int min = INT_MAX;
        for (auto c : progConsts)
        {
          if (c < min)
          {
            min = c;
          }
        }
        progConsts.erase(min);
        lf.addConst(min);
      }

      lf.initialize();

      // normalize samples obtained from CHCs and calculate various statistics:
      vector<LAdisj> lcss;
      for (auto &cs : css)
      {
        for (auto &cand : cs.candidates)
        {
          lcss.push_back(LAdisj());
          LAdisj& lcs = lcss.back();
          if (lf.exprToLAdisj(cand, lcs))
          {
            lcs.normalizePlus();
            orArities.insert(lcs.arity);
          }
          else
          {
            lcss.pop_back();
          }
        }
      }

      if (orArities.size() == 0)                // default, if no samples were obtained from the code
      {
        for (int i = 1; i <= DEFAULTARITY; i++) orArities.insert(i);
      }

      lf.initDensities(orArities);

      if (densecode)
      {
        int multip = PRIORSTEP;                 // will add +PRIORSTEP to every occurrence

        // or, alternatively multip can depend on the type of CHC:
        //        if (cs.hr.isFact) multip = 1;
        //        else if (cs.hr.isQuery) multip = 2 * PRIORSTEP;
        //        else multip = PRIORSTEP;
        for (auto &lcs : lcss)
        {
          int ar = lcs.arity;
          // specify weights for OR arity
          lf.orAritiesDensity[ar] += multip;

          for (int i = 0; i < ar; i++)
          {
            LAterm& lc = lcs.dstate[i];

            // specify weights for PLUS arity
            lf.plusAritiesDensity[ar][lc.arity] += multip;

            // specify weights for const
            lf.intConstDensity[ar][lc.intconst] += multip;

            // specify weights for comparison operation
            lf.cmpOpDensity[ar][lc.cmpop] += multip;

            // specify weights for var combinations
            set<int> vars;
            int vars_id = -1;
            for (int j = 0; j < lc.vcs.size(); j = j+2) vars.insert(lc.vcs[j]);
            for (int j = 0; j < lf.varCombinations[ar][lc.arity].size(); j++)
            {
              if (lf.varCombinations[ar][lc.arity][j] == vars)
              {
                vars_id = j;
                break;
              }
            }
            assert(vars_id >= 0);
            lf.varDensity[ar][lc.arity][vars_id] += multip;

            for (int j = 1; j < lc.vcs.size(); j = j+2)
            {
              lf.coefDensity[ ar ][ lc.vcs [j-1] ] [lc.vcs [j] ] += multip;
            }
          }
        }

        outs() << "\nStatistics for " << *decls.back() << ":\n";
        lf.printCodeStatistics(orArities);
      }
    }

    void integrateWorkerResult(WorkerResult& d) {
      LAfactory& laf = lfs[d.declIdx];
      laf.samples.push_back(*(d.disj));
      LAdisj& disj = laf.samples.back();
      disj.normalizePlus();  // should be normalized already, but: safety
      switch (d.kind) {
      case WorkerResultKindLemma:
        laf.assignPrioritiesForLearnt(disj);
        laf.learntExprs.insert(laf.toExpr(disj));
        laf.learntLemmas.push_back(laf.samples.size() - 1);
        break;
      case WorkerResultKindFailure:
        laf.assignPrioritiesForFailed(disj);
        break;
      case WorkerResultKindGarbage:
        laf.assignPrioritiesForGarbage(disj);
        break;
      default:
        break;
      }
    }

    void workerMain(boost::mpi::communicator world) {
      std::chrono::duration<double, std::milli> waitElapsed;

      while (1) {
        const auto start = std::chrono::steady_clock::now();
        ReceivedWorkerJob job = recvWorkerJob(world, invNumber());
        waitElapsed += (std::chrono::steady_clock::now() - start);

        if (job.shouldStop())
          break;

        // TODO: Is adding samples to LAfactory's needed too?

        // Integrate new lemmas
        for (auto it = job.newLemmas.cbegin();
             it != job.newLemmas.cend(); it++)
        {
          const std::pair<unsigned, LAdisj>& d = *it;
          LAfactory& laf = lfs[d.first];
          laf.samples.push_back(d.second);
          LAdisj& disj = laf.samples.back();
          disj.normalizePlus();  // should be normalized already, but: safety
          laf.assignPrioritiesForLearnt(disj);
          Expr lafExpr = laf.toExpr(disj);
          laf.learntExprs.insert(lafExpr);
          laf.learntLemmas.push_back(laf.samples.size() - 1);

          Expr invApp = lafExpr;
          for (auto& hr : ruleManager.chcs) {
            for (int i = 0; i < hr.srcVars.size(); i++)
              invApp = replaceAll(invApp, laf.getVarE(i), hr.srcVars[i]);
          }

          // Determine safety solver from declIdx (d.first) and add lemma
          unsigned ssIdx = 0;
          for (auto &hr: ruleManager.chcs) {
            if (hr.isQuery) {
              if (d.first == getVarIndex(hr.srcRelation, decls)) {
                m_smt_safety_solvers[ssIdx].assertExpr(invApp);
              }
              ssIdx++;
            }
          }
        }

        // Check for tautologies etc. while converting to Expr and adding to
        // curCandidates
        bool skipIter = false;
        for (size_t j = 0; j < job.curCandDisjs.size(); j++) {
          LAfactory& lf = lfs[j];
          auto& jo = job.curCandDisjs[j];
          Expr cand = lf.toExpr(jo);

          if (isTautology(cand)) {  // keep searching
            reportLemma(world, j, jo);
            skipIter = true;
            break;
          }

          if (lf.nonlinVars.size() > 0 && !u.isSat(cand)) { // keep searching
            reportFailure(world, j, jo);
            skipIter = true;
            break;
          }

          lf.samples.push_back(jo);
          curCandidates[j] = cand;
        }

        if (!skipIter) {
          outs() << "\n  ---- new iteration " << job.globalIter <<  " ----\n";
          printCandidates();
          if (checkCandidates(world) && checkSafety()) {
            WorkerResult succMsg { WorkerResultKindFoundInvariants, 0, nullptr };
            world.send(0, MSG_TAG_NORMAL, std::shared_ptr<WorkerResult>(&succMsg, [](WorkerResult*){}));
            break;
          }
        }

        WorkerResult iterDoneMsg { WorkerResultKindDone, 0, nullptr };
        world.send(0, MSG_TAG_NORMAL, std::shared_ptr<WorkerResult>(&iterDoneMsg, [](WorkerResult*){}));
      }

      stringstream waitStream;
      waitStream << fixed << setprecision(2) << waitElapsed.count()/1000.0;
      outs() << "time spent waiting for jobs: " << waitStream.str() << "s\n";
    }
  };
}

#endif
