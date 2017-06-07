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
    ufo::ZSolver<ufo::EZ3> m_smt_safety_solver;

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
      world.send(0, MSG_TAG_NORMAL, result);
    }

    void reportFailure(boost::mpi::communicator world, unsigned declIdx, LAdisj& disj) {
      WorkerResult result { WorkerResultKindFailure, declIdx, unique_ptr<LAdisj>(new LAdisj(disj)) };
      world.send(0, MSG_TAG_NORMAL, result);
    }

  public:

    RndLearner (ExprFactory &efac, EZ3 &z3, CHCs& r, bool b1, bool b2, bool b3) :
      m_efac(efac), m_z3(z3), ruleManager(r), m_smt_solver (z3),
      m_smt_safety_solver(z3), u(efac), numOfSMTChecks(0), densecode(b1),
      shrink(b2), aggressivepruning(b3) {}

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
      map<int, int> localNum = incomNum; // for local status
      map<int, bool> candsFailed;        // -||-
      int candsTried = invNumber();        // -||-

      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isQuery) continue;

        m_smt_solver.reset();

        int ind1;  // to be identified later
        int ind2 = getVarIndex(hr.dstRelation, decls);

        if (candsFailed[ind2]) continue;  // exit if cand2 is already a failure

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

          if (localNum[ind1] > 0)
          {
            cand1 = curCandidates[ind1];
            for (int i = 0; i < hr.srcVars.size(); i++)
            {
              cand1 = replaceAll(cand1, lf1.getVarE(i), hr.srcVars[i]);
            }
            m_smt_solver.assertExpr(cand1);
          }

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

        numOfSMTChecks++;
        boost::tribool res = m_smt_solver.solve ();
        if (res)    // SAT   == candidate failed
        {
          outs () << "   => bad candidate for " << *hr.dstRelation << "\n";
          assert(!lf2.samples.empty());
          LAdisj& failedDisj = lf2.samples.back();
          if (aggressivepruning) reportFailure(world, ind2, failedDisj);
          candsTried--;
          candsFailed[ind2] = true;
          if (candsTried == 0) return false;
        }
        else        // UNSAT == candadate is OK for now; keep checking
        {
          localNum[ind2]--;
          if (!res && localNum[ind2] == 0) // something inductive found
          {
            outs () << "   => learnt lemma for " << *hr.dstRelation << "\n";
            assert(!lf2.samples.empty());
            LAdisj& learntDisj = lf2.samples.back();
            lf2.learntExprs.insert(curCandidates[ind2]);
            lf2.learntLemmas.push_back(lf2.samples.size() - 1);
            candsTried--;
            reportLemma(world, ind2, learntDisj);
          }
        }
      }
      return true;
    }

    bool checkSafety()
    {
      for (auto &hr: ruleManager.chcs)
      {
        if (!hr.isQuery) continue;

        int ind = getVarIndex(hr.srcRelation, decls);
        Expr invApp = curCandidates[ind];
        if (invApp == NULL) continue;

        LAfactory& lf = lfs[ind];
        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          invApp = replaceAll(invApp, lf.getVarE(i), hr.srcVars[i]);
        }

        m_smt_safety_solver.assertExpr(invApp);

        numOfSMTChecks++;
        boost::tribool res = m_smt_safety_solver.solve ();
        if (!res) return true;
      }
      return false;
    }

    void setupSafetySolver()
    {
      // setup the safety solver
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isQuery)
        {
          m_smt_safety_solver.assertExpr (hr.body);
          break;
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

    std::pair<unsigned, vector<LAdisj>> recvWorkerJob(boost::mpi::communicator world) {
      // Receive either a job start or stop message
      StartIterMsg startMsg;
      world.recv(0, MSG_TAG_NORMAL, startMsg);
      if (startMsg.shouldStop)
        return make_pair(startMsg.globalIter, vector<LAdisj>());

      // Recv candidates, filling curCandidates÷
      vector<LAdisj> newCurCandsDisjs;
      for (size_t i = 0; i < invNumber(); i++) {
        newCurCandsDisjs.emplace_back();
        LAdisj& disj = newCurCandsDisjs.back();
        world.recv(0, MSG_TAG_NORMAL, disj);
      }
      return make_pair(startMsg.globalIter, newCurCandsDisjs);
    }

    void workerMain(boost::mpi::communicator world) {
      while (1) {
        std::pair<unsigned, vector<LAdisj>> job = recvWorkerJob(world);
        unsigned globalIter = job.first;
        vector<LAdisj>& jobDisjs = job.second;
        if (jobDisjs.empty()) {
          // empty vector means stop
          break;
        }

        // TODO: Is adding samples to LAfactory's needed too?

        // Check for tautologies etc. while converting to Expr and adding to
        // curCandidates
        bool skipIter = false;
        for (size_t j = 0; j < jobDisjs.size(); j++) {
          LAfactory& lf = lfs[j];
          Expr cand = lf.toExpr(jobDisjs[j]);

          if (isTautology(cand)) {  // keep searching
            reportLemma(world, j, jobDisjs[j]);
            skipIter = true;
            break;
          }

          if (lf.nonlinVars.size() > 0 && !u.isSat(cand)) { // keep searching
            reportFailure(world, j, jobDisjs[j]);
            skipIter = true;
            break;
          }

          lf.samples.push_back(jobDisjs[j]);
          curCandidates[j] = cand;
        }

        if (!skipIter) {
          outs() << "\n  ---- new iteration " << globalIter <<  " ----\n";
          printCandidates();
          if (checkCandidates(world) && checkSafety()) {
            WorkerResult succMsg { WorkerResultKindFoundInvariants, 0, nullptr };
            world.send(0, MSG_TAG_NORMAL, succMsg);
            break;
          }
        }

        WorkerResult iterDoneMsg { WorkerResultKindDone, 0, nullptr };
        world.send(0, MSG_TAG_NORMAL, iterDoneMsg);
      }
    }
  };
}

#endif
