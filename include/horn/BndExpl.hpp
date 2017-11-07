#ifndef BNDEXPL__HPP__
#define BNDEXPL__HPP__

#include "Horn.hpp"
#include "CandChecker.hpp"
#include "ae/SMTUtils.hpp"

/* Template for P1 and P2. Could also be used in P7 */

using namespace std;
using namespace boost;
namespace ufo
{
  class BndExpl
  {
    private:

    ExprFactory &efac;
    SMTUtils u;
    CHCs& ruleManager;

    vector<ExprVector> bindVars; // helper vars
    ExprVector bindVars1;

    HornRuleExt* tr;             // we assume CHC system has just three rules
    HornRuleExt* fc;             // but in principle, it can have many...
    HornRuleExt* qr;

    CandChecker* cc;             // invariant checker

    public:

    BndExpl (CHCs& r) : efac(r.m_efac), ruleManager(r), u(efac) {}

    void checkPrerequisites ()
    {
      if (ruleManager.decls.size() > 1)
      {
        outs() << "Nested loops not supported\n";
        exit(0);
      }

      if (ruleManager.chcs.size() != 3)
      {
        outs() << "Please provide a file with exactly three rules\n";
        exit(0);
      }

      for (auto & a : ruleManager.chcs)
        if (a.isInductive) tr = &a;
        else if (a.isFact) fc = &a;
        else if (a.isQuery) qr = &a;

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

      if (qr == NULL)
      {
        outs() << "BAD is missing\n";
        exit(0);
      }
      cc = new CandChecker(efac, fc, tr, qr);
    }

    Expr toExpr(vector<HornRuleExt*>& trace)
    {
      ExprVector ssa;

      ExprVector bindVars2;
      bindVars.clear();
      ExprVector bindVars1 = trace[0]->srcVars;
      int bindVar_index = 0;
      int locVar_index = 0;

      for (int s = 0; s < trace.size(); s++)
      {
        bindVars2.clear();
        HornRuleExt& hr = *trace[s];
        Expr body = hr.body;

        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          body = replaceAll(body, hr.srcVars[i], bindVars1[i]);
        }

        for (int i = 0; i < hr.dstVars.size(); i++)
        {
          bool kept = false;
          for (int j = 0; j < hr.srcVars.size(); j++)
          {
            if (hr.dstVars[i] == hr.srcVars[j])
            {
              bindVars2.push_back(bindVars1[i]);
              kept = true;
            }
          }
          if (!kept)
          {
            Expr new_name = mkTerm<string> ("__bnd_var_" + to_string(bindVar_index++), efac);
            bindVars2.push_back(cloneVar(hr.dstVars[i],new_name));
          }

          body = replaceAll(body, hr.dstVars[i], bindVars2[i]);
        }

        for (int i = 0; i < hr.locVars.size(); i++)
        {
          Expr new_name = mkTerm<string> ("__loc_var_" + to_string(locVar_index++), efac);
          Expr var = cloneVar(hr.locVars[i], new_name);

          body = replaceAll(body, hr.locVars[i], var);
        }

        ssa.push_back(body);
        bindVars.push_back(bindVars2);
        bindVars1 = bindVars2;
      }

      return conjoin(ssa, efac);
    }

    bool checkBMCformula(int k)
    {
      assert(k >= 0);

      Expr prop = qr->body;
      Expr init = fc->body;
      for (int i = 0; i < tr->srcVars.size(); i++)
      {
        init = replaceAll(init, tr->dstVars[i],  tr->srcVars[i]);
      }

      Expr unr = mk<TRUE>(efac);
      if (k > 0)
      {
        vector<HornRuleExt*> trace;
        for (int i = 0; i < k; i++) trace.push_back(tr);

        // TODO [P2]:
        // optimize such that unr is not constructed from scratch for each k:
        unr = toExpr(trace);

        for (int i = 0; i < qr->srcVars.size(); i++)
        {
          prop = replaceAll(prop, qr->srcVars[i], bindVars.back()[i]);
        }
      }

      // TODO [P2]:
      // optimize such that the formula is not solved from scratch for each k:
      return u.isSat(mk<AND>(mk<AND>(init, unr), prop));
    }

    // similar to checkBMCformula, but uses interpolation, thus is more expensive
    Expr getBoundedItp(int k)
    {
      assert(k >= 0);

      Expr prop = qr->body;
      Expr init = fc->body;
      for (int i = 0; i < tr->srcVars.size(); i++)
      {
        init = replaceAll(init, tr->dstVars[i],  tr->srcVars[i]);
      }

      Expr itp;

      Expr unr = mk<TRUE>(efac);
      if (k > 0)
      {
        vector<HornRuleExt*> trace;
        for (int i = 0; i < k; i++) trace.push_back(tr);

        unr = toExpr(trace);

        for (int i = 0; i < qr->srcVars.size(); i++)
        {
          prop = replaceAll(prop, qr->srcVars[i], bindVars.back()[i]);
        }
      }

      // TODO [P1]:
      // try various partitionings of formula (i.e., arguments of getItp):
      return getItp(init, mk<AND>(unr, prop));
    }

    bool checkInvariant (Expr cand)
    {
      bool res;

      // in fact, cc->checkInitiation could be here as well,
      // but it is not needed when dealing with interpolants

      res = cc->checkInductiveness(cand);
      if (!res) return false;

      return cc->checkSafety();
    }
  };

  inline void unrollAndCheck(string smt, int bnd, int bnd2)
  {
    ExprFactory efac;
    EZ3 z3(efac);
    CHCs ruleManager(efac, z3);
    ruleManager.parse(smt);
    BndExpl be(ruleManager);
    be.checkPrerequisites();

    int i = bnd;
    while (i < bnd2)
    {
      if (be.checkBMCformula(i))
      {
        outs() << "Counterexample of length " << i << " is found.\n";
        exit(0);
      }
      i++;
    }
    outs () << "Traces of size " << bnd << " ... " << bnd2 << " explored and are free of bugs\n";
  }

  inline void getItpsAndCheck(string smt, int bnd, int bnd2)
  {
    ExprFactory efac;
    EZ3 z3(efac);
    CHCs ruleManager(efac, z3);
    ruleManager.parse(smt);
    BndExpl be(ruleManager);
    be.checkPrerequisites();
    Expr cand;
    int i = bnd;
    bool invariantFound = false;
    while (i < bnd2 && !invariantFound)
    {
      cand = be.getBoundedItp(i);
      if (cand == NULL)
      {
        outs() << "Counterexample of length " << i << " is found.\n";
        exit(0);
      }
      invariantFound = be.checkInvariant(cand);

      i++;
    }

    if (invariantFound)
    {
      outs () << "Invariant found at step " << i << "\n";
    }
    else
    {
      outs () << "Invariant not found\nTraces of size " << bnd << " ... " << bnd2 << " explored and are free of bugs\n";
    }
  }
}

#endif
