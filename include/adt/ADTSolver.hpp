#ifndef ADTSOLVER__HPP__
#define ADTSOLVER__HPP__
#include <assert.h>
#include <string.h>

#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{
  class ADTSolver
  {
    private:

    Expr goal;
    ExprVector& assumptions;
    ExprVector& constructors;

    map<Expr, Expr> baseConstructors;
    map<Expr, Expr> indConstructors;

    ExprFactory &efac;
    SMTUtils u;

    ExprVector rewriteHistory;
    vector<int> rewriteSequence;
    int maxDepth;
    int maxSameAssm;
    public:

    ADTSolver(Expr _goal, ExprVector& _assumptions, ExprVector& _constructors, int _maxDepth, int _maxSameAssm) :
        goal(_goal), assumptions(_assumptions), constructors(_constructors),
        efac(_goal->getFactory()), u(_goal->getFactory()), maxDepth(_maxDepth), maxSameAssm(_maxSameAssm)
    {
      assert(isOpX<FORALL>(goal));
    }

    bool simplifyGoal()
    {
      Expr goalQF = goal->last();
      for (auto & a : assumptions)
      {
        Expr goalSimpl = useAssumption(goalQF, a);
        if (goalSimpl != NULL) goalQF = goalSimpl;
      }
      goalQF = liftITEs(goalQF); // TODO: more simplification passes
      goalQF = u.simplifyITE(goalQF);
      if (u.isEquiv(goalQF, mk<TRUE>(efac))) return true;

      ExprVector args;
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        if (contains(goal->last(), goal->arg(i))) args.push_back(goal->arg(i));
      }
      if (args.size() == 0) goal = goalQF;
      else
      {
        args.push_back(goalQF);
        goal = mknary<FORALL>(args);
      }
      rewriteHistory.push_back(goal);
      return false;
    }

    // main method to do rewriting
    Expr useAssumption(Expr subgoal, Expr assm)
    {
      subgoal = liftITEs(subgoal);
      if (isOpX<FORALL>(assm))
      {
        ExprMap matching;
        ExprVector args;
        for (int i = 0; i < assm->arity() - 1; i++) args.push_back(bind::fapp(assm->arg(i)));
        Expr assmQF = assm->last();
        Expr repl = assmQF;

        // we first search for a matching of the entire assumption (usually some inequality)
        if (findMatchingSubexpr (assmQF, subgoal, args, matching))
        {
          for (auto & a : matching) repl = replaceAll(repl, a.first, a.second);
          Expr replaced = replaceAll(subgoal, repl, mk<TRUE>(efac));
          if (subgoal != replaced) return replaced;
        }
        if (isOpX<EQ>(assmQF))
        {
          matching.clear();

          // if the assumption is equality, the we search for a matching of its LHS
          // (we can try matching the RHS as well, but it will likely give us infinite loops)
          if (findMatchingSubexpr (assmQF->left(), subgoal, args, matching))
          {
            for (auto & a : matching) repl = replaceAll(repl, a.first, a.second);
            return replaceAll(subgoal, repl->left(), repl->right());
          }
        }
        if ((isOpX<LEQ>(assmQF) && isOpX<LEQ>(subgoal)) ||
            (isOpX<GEQ>(assmQF) && isOpX<GEQ>(subgoal)) ||
            (isOpX<LT>(assmQF) && isOpX<LT>(subgoal)) ||
            (isOpX<GT>(assmQF) && isOpX<GT>(subgoal)))
        {
          if (findMatchingSubexpr (assmQF->left(), subgoal->left(), args, matching))
          {
            for (auto & a : matching) repl = replaceAll(repl, a.first, a.second);
            if (u.implies(repl, subgoal)) return mk<TRUE>(efac);
          }
        }
      }
      else
      {
        // for a quantifier-free assumption (e.g., inductive hypotheses),
        // we create an SMT query and check with Z3
        // TODO: we can do so for ALL constistent quantifier-free assumptions at once
        if (u.implies(assm, subgoal)) return mk<TRUE>(efac);
        if (isOpX<EQ>(assm))
        {
          Expr res = replaceAll(subgoal, assm->left(), assm->right());
          if (res != subgoal)
          {
            return res;
          }
        }
      }
      // if nothing helped, return NULL -- it will be used for backtracking
      return NULL;
    }

    // this method is used when a strategy is specified from the command line
    bool tryStrategy(Expr subgoal, vector<int>& strat)
    {
      Expr subgoal_copy = subgoal;
      for (int i : strat)
      {
        assert (i < assumptions.size());
        subgoal_copy = useAssumption(subgoal_copy, assumptions[i]);
        if (subgoal_copy == NULL || subgoal_copy == subgoal) break;

        outs () << "rewritten [" << i << "]:   " << *subgoal_copy << "\n";
        if (u.isEquiv(subgoal_copy, mk<TRUE>(efac))) return true;
      }
      return false;
    }

    // this recursive method performs a naive search for a strategy
    bool rewriteAssumptions(Expr subgoal)
    {
      if (u.isEquiv(subgoal, mk<TRUE>(efac))) return true;

      // check recursion depth
      if (rewriteSequence.size() >= maxDepth)
      {
        outs() << "Maximum recursion depth reached\n";
        return false;
      }

      // check consecutive applications of the same assumption
      if (rewriteSequence.size() >= maxSameAssm)
      {
        int assmId = rewriteSequence.back();
        int offset = rewriteSequence.size() - maxSameAssm - 1;
        int i = 0;
        for (; i < maxSameAssm; i++)
          if (rewriteSequence[i + offset] != assmId)
            break;

        if (i == maxSameAssm)
        {
          outs() << "Maximum use of assumption #" << assmId << " reached\n";
          return false;
        }
      }

      for (int i = 0; i < assumptions.size(); i++)
      {
        Expr a = assumptions[i];
        Expr res = useAssumption(subgoal, a);
        if (res != NULL)
        {
          outs () << "rewritten [" << i << "]:   " << *res << "\n";
          // save history
          rewriteHistory.push_back(res);
          rewriteSequence.push_back(i);

          if  (rewriteAssumptions(res))
            return true;
          else {
            // failed attempt, remove history
            rewriteHistory.pop_back();
            rewriteSequence.pop_back();
          }

          // backtrack:
          outs () << "backtrack to:    " << *subgoal << "\n";
        }
      }

      return false;
    }

    // preprocessing of the main goal:
    //   - classify constructors for all ADTs that appear in the goal
    //   - replace all non-inductive ADTs
    void unfoldGoal()
    {
      ExprVector goalArgs;
      Expr unfoldedGoalQF = goal->last();
      bool toRebuild = false;
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        Expr type = goal->arg(i)->last();
        for (auto & a : constructors)
        {
          if (a->last() == type)
          {
            bool ind = false;
            for (int i = 0; i < a->arity() - 1; i++)
            {
              if (a->last() == a->arg(i))
              {
                ind = true;
                if (indConstructors[type] != NULL && indConstructors[type] != a)
                {
                  outs () << "Several inductive constructors are not supported\n";
                  exit(0);
                }
                indConstructors[type] = a;
              }
            }
            if (!ind)
            {
              if (baseConstructors[type] != NULL && baseConstructors[type] != a)
              {
                outs () << "Several base constructors are not supported\n";
                exit(0);
              }
              baseConstructors[type] = a;
            }
          }
        }
        if (baseConstructors[type] != NULL && indConstructors[type] == NULL)
        {
          toRebuild = true;
          ExprVector args;
          args.push_back(baseConstructors[type]);
          for (int i = 1; i < baseConstructors[type]->arity() - 1; i++)
          {
            // TODO: make sure the name is unique
            Expr s = bind::mkConst(mkTerm<string>
                         ("_b_" + to_string(goalArgs.size()), efac),
                         baseConstructors[type]->arg(i));
            goalArgs.push_back(s->last());
            args.push_back(s);
          }
          Expr newApp = mknary<FAPP>(args);
          unfoldedGoalQF = replaceAll(unfoldedGoalQF, bind::fapp(goal->arg(i)), newApp);
        }
        else
        {
          goalArgs.push_back(goal->arg(i));
        }
      }

      if (toRebuild)
      {
        goalArgs.push_back(unfoldedGoalQF);
        goal = mknary<FORALL>(goalArgs);

        // continue recursively, because newly introduced vars may again need unfolding
        unfoldGoal();
      }
    }

    // this method can be (but not used currently) to add symmetric assumptions
    // and to enable searching for RHS of assumptions
    void insertSymmetricAssumption(Expr assm)
    {
      if (isOpX<EQ>(assm))
      {
        assumptions.push_back(mk<EQ>(assm->right(), assm->left()));
      }
      else if (isOpX<FORALL>(assm) && isOpX<EQ>(assm->last()))
      {
        ExprVector args;
        for (int i = 0; i < assm->arity() - 1; i++) args.push_back(assm->arg(i));
        args.push_back(mk<EQ>(assm->last()->right(), assm->last()->left()));
        assumptions.push_back(mknary<FORALL>(args));
      }
    }

    void printAssumptions()
    {
      outs () << "=========================\n";
      for (int i = 0; i < assumptions.size(); i++)
      {
        outs () << "Assumptions [" << i << "]: " << *assumptions[i] << "\n";
      }
    }

    bool induction(int num, vector<int>& basenums, vector<int>& indnums)
    {
      assert(num < goal->arity() - 1);
      Expr typeDecl = goal->arg(num);
      Expr type = goal->arg(num)->last();

      Expr baseConstructor = baseConstructors[type];
      Expr indConstructor = indConstructors[type];

      // instantiate every quantified variable (except the inductive one) in the goal
      Expr goalQF = goal->last();
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        if (i == num) continue;
        // TODO: make sure the name is unique
        Expr s = bind::mkConst(mkTerm<string> ("_v_" + to_string(i), efac), goal->arg(i)->last());
        goalQF = replaceAll(goalQF, bind::fapp(goal->arg(i)), s);
      }

      // prove the base case
      Expr baseSubgoal = replaceAll(goalQF, typeDecl, baseConstructor);
      printAssumptions();
      outs() << "\nBase case:       " << *baseSubgoal << "\n";

      rewriteHistory.clear();
      rewriteSequence.clear();

      bool baseres = basenums.empty() ?
              rewriteAssumptions(baseSubgoal) :
              tryStrategy(baseSubgoal, basenums);

      if (!baseres)
      {
        ExprVector newArgs;
        for (int i = 0; i < goal->arity() - 1; i++)
        {
          if (i == num) continue;
          newArgs.push_back(goal->arg(i));
        }
        if (newArgs.size() > 0)
        {
          outs () << "\nProceeding to nested induction\n";
          newArgs.push_back(replaceAll(goal->last(), typeDecl, baseConstructor));
          Expr newGoal = mknary<FORALL>(newArgs);
          ADTSolver sol (newGoal, assumptions, constructors, maxDepth, maxSameAssm);
          if (!sol.solve (basenums, indnums)) return false;
          outs () << "\nReturning to the outer induction\n\n";
        }
        else
        {
          return false;
        }
      }

      // generate inductive hypotheses
      ExprVector args;
      ExprVector indHypotheses;
      bool allQF = true;
      for (int i = 1; i < indConstructor->arity() - 1; i++)
      {
        // TODO: make sure the name is unique
        Expr s = bind::mkConst(mkTerm<string> ("_t_" + to_string(i), efac), indConstructor->arg(i));
        args.push_back(s);

        if (type == indConstructor->arg(i)) // type check
        {
          ExprVector argsIH;
          for (int j = 0; j < goal->arity() - 1; j++)
          {
            if (j != num) argsIH.push_back(goal->arg(j));
          }
          argsIH.push_back(replaceAll(goal->last(), bind::fapp(typeDecl), s));
          if (argsIH.size() == 1)
          {
            indHypotheses.push_back(argsIH.back());
          }
          else
          {
            allQF = false;
            indHypotheses.push_back(mknary<FORALL>(argsIH));
          }
        }
      }
      for (auto & a : indHypotheses)
      {
        assumptions.push_back(a);
        // always add symmetric IH?
        insertSymmetricAssumption(a);
      }
      // for simplicity, add conjunction of hypotheses as a single hypothesis
      // should be removed in the future (when all QF-assumptions are used at the same time)
      if (indHypotheses.size() > 1 && allQF) assumptions.push_back(conjoin(indHypotheses, efac));

      // prove the inductive step
      Expr indConsApp = bind::fapp(indConstructor, args);
      Expr indSubgoal = replaceAll(goalQF, bind::fapp(typeDecl), indConsApp);
      printAssumptions();
      outs() << "\nInductive step:  " << * indSubgoal << "\n";

      rewriteHistory.clear();
      rewriteSequence.clear();

      bool indres = indnums.empty() ?
               rewriteAssumptions(indSubgoal) :
               tryStrategy(indSubgoal, indnums);

      if (indres) return true;
      else
      {
        ExprVector newArgs;
        for (int i = 0; i < goal->arity() - 1; i++)
        {
          if (i == num) continue;
          newArgs.push_back(goal->arg(i));
        }
        if (newArgs.size() > 0)
        {
          outs () << "\nProceeding to nested induction\n";
          newArgs.push_back(replaceAll(goal->last(), bind::fapp(typeDecl), indConsApp));
          Expr newGoal = mknary<FORALL>(newArgs);
          ADTSolver sol (newGoal, assumptions, constructors, maxDepth, maxSameAssm);
          return sol.solve (basenums, indnums);
        }
        return false;
      }
    }

    bool solve(vector<int>& basenums, vector<int>& indnums)
    {
      unfoldGoal();
      rewriteHistory.push_back(goal);
      for (int i = 0; i < 5; i++)
      {
        if (simplifyGoal())
        {
          outs () << "Trivially Proved\n";
          return true;
        }
      }

      // simple heuristic: if the result of every rewriting made the goal larger, we rollback
      bool toRollback = true;
      for (int i = 1; i < rewriteHistory.size(); i++)
      {
        toRollback = toRollback &&
            (treeSize(rewriteHistory[i-1]) < treeSize(rewriteHistory[i]));
      }

      if (toRollback) goal = rewriteHistory[0];

      outs () << "Simplified goal: " << *goal << "\n\n";
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        Expr type = goal->arg(i)->last();
        if (baseConstructors[type] != NULL && indConstructors[type] != NULL)
        {
          if (induction(i, basenums, indnums))
          {
            outs () << "                 Proved\n";
            return true;
          }
          else
          {
            outs () << "                 Failed\n";
            return false;
          }
        }
      }
      return false;
    }
  };

  static inline void getNums(vector<int>& nums, char * str)
  {
    if (str == NULL) return;
    int len = strlen(str);
    char* pch = strchr(str, ',');
    int pos1 = 0;
    int pos2 = 0;
    while (pch != NULL)
    {
      pos2 = pch - str;
      char* substr = (char*)malloc(pos2 - pos1);
      strncpy(substr, str + pos1, pos2 - pos1);
      nums.push_back(atoi(substr));
      pch = strchr(pch + 1, ',');
      pos1 = pos2 + 1;
    }
    if (pos1 == len) return;
    char* substr = (char*)malloc(len - pos1);
    strncpy(substr, str + pos1, len - pos1);
    nums.push_back(atoi(substr));
  }

  void adtSolve(EZ3& z3, Expr s, char* basecheck, char *indcheck, int maxDepth, int maxSameAssm)
  {
    vector<int> basenums;
    vector<int> indnums;
    getNums(basenums, basecheck);
    getNums(indnums, indcheck);
    ExprVector constructors;
    for (auto & a : z3.getAdtConstructors()) constructors.push_back(regularizeQF(a));

    ExprVector assumptions;
    Expr goal;

    if (isOpX<AND>(s))
    {
      for (int i = 0; i < s->arity(); i++)
      {
        Expr a = s->arg(i);
        if (isOpX<NEG>(a))
        {
          goal = regularizeQF(a->left());
        }
        else
        {
          assumptions.push_back(regularizeQF(a));
        }
      }
    }
    else if (isOpX<NEG>(s))
    {
      goal = regularizeQF(s->left());
    }

    if (goal == NULL)
    {
      outs () << "Unable to parse the query\n";
      return;
    }
    ADTSolver sol (goal, assumptions, constructors, maxDepth, maxSameAssm);
    sol.solve (basenums, indnums);
  }
}

#endif
