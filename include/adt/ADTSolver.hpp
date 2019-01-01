#ifndef ADTSOLVER__HPP__
#define ADTSOLVER__HPP__
#include <assert.h>
#include <string.h>
#include <chrono>
#include <iterator>

#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"
#include <algorithm>

#include <iostream>

using namespace std;
using namespace boost;
namespace ufo
{
  struct SimplifyAdd0
  { 
    Expr operator()(Expr e) const{
      bind::IsHardIntConst isInt;
      if (!isOpX<PLUS>(e) || e->arity() != 2) return NULL;
      if (isInt(e->left()) && getTerm<mpz_class>(e->left()) == 0)
        return e->right();
      if (isInt(e->right()) && getTerm<mpz_class>(e->right()) == 0)
        return e->left();
      else return NULL;
    }
  };

  Expr makeAddExpr(ExprVector ev){
    if (ev.size()>1) return mknary<PLUS>(ev);
    else if (ev.size() == 1) return ev[0];
    else return NULL;
  }
  Expr simplifyAdd(Expr e){
    if (!(isOpX<EQ>(e) && isOpX<PLUS>(e->left()) && isOpX<PLUS>(e->right()))) return e;
    bind::IsHardIntConst isInt;
    mpz_class lhsConst = 0;
    mpz_class rhsConst = 0;
    ExprVector lhsInts;
    ExprVector rhsInts;
    for (Expr lhsArg : boost::make_iterator_range(e->left()->args_begin (), e->left()->args_end ()))
      if (isInt(lhsArg))
        lhsConst += getTerm<mpz_class>(lhsArg);
      else lhsInts.push_back(lhsArg);
    for (Expr rhsArg : boost::make_iterator_range(e->right()->args_begin (), e->right()->args_end()))
      if (isInt(rhsArg))
        rhsConst += getTerm<mpz_class>(rhsArg);
      else rhsInts.push_back(rhsArg);

    if (lhsConst != rhsConst)
      lhsInts.push_back(mkTerm<mpz_class>(lhsConst - rhsConst, e->efac()));
    return mk<EQ>(makeAddExpr(lhsInts), makeAddExpr(rhsInts));
  }
  class TermEnumerator
  {
  private:
    ExprMap baseCtors;
    ExprMap indCtors;
    ExprSet vars;
    ExprSet funcs;
    int maxDepth;
    vector<size_t> depthIdx;
    bool isVarFn(Expr e){
      if (isOpX<FAPP> (e) && e->arity () == 1 && isOpX<FDECL> (e->first())) {
        Expr baseCtor = baseCtors[bind::typeOf(e)];
        // exclude base constructors (e.g. nil:Lst)
        return (baseCtor == NULL || e != bind::fapp(baseCtor));
      } else return false;
    }
    bool isBaseCtor(Expr e){
      if (isOpX<FAPP> (e) && e->arity () == 1 && isOpX<FDECL> (e->first())
        && (e->first() == baseCtors[bind::typeOf(e)])) return true;
        else return false;
    }
    bool isFuncFn(Expr e){
      // fdecl [name fromTy ... toTy]
      if (isOpX<FDECL> (e) && e->arity () >= 3) {
        return true;
      } else return false;
    }
    // bool isIndCtorFn(Expr e){
    //   if (isOpX<FAPP> (e) && isOpX<FDECL> (e->first())){
    //     if (find(indCtorDecls.begin(), indCtorDecls.end(), e->first()) != indCtorDecls.end())
    //       return true;
    //   }
    //   return false;
    // }
  public:
    map<Expr, ExprVector> allTerms;
    TermEnumerator(Expr expr, ExprMap _baseCtors, ExprMap _indCtors, int _maxDepth = 3) :
      baseCtors(_baseCtors), indCtors(_indCtors), maxDepth(_maxDepth)
    {
      outs()<<"expr: "<<*expr;
      filter(expr, [this](Expr e){return isVarFn(e);}, inserter(vars, vars.end()));
      // outs()<<"\nvars:";
      // for (Expr v: vars) outs()<<" "<<*v;
      filter(expr, [this](Expr e){return isFuncFn(e);}, inserter(funcs, funcs.end()));

      for(auto p: indCtors)
      {
        if (p.second)
          funcs.insert(p.second);
      }
      // outs()<<"Please input max depth:";
      // cin>>maxDepth;
      // outs()<<"max depth is "<<maxDepth<<"\n";
    }
    void addFunctions(Expr axiom){
      filter(axiom, [this](Expr e){return isFuncFn(e);}, inserter(funcs, funcs.end()));
    }
    bool isOk()
    {
      getTerms();
      return true;
    }
    int depth(Expr e)
    {
      bind::IsConst isConst;
      int maxD = 0;
      if (isConst(e)) return 1;
      if (isOpX<FAPP>(e))
      {
        for (int i = 0; i < bind::domainSz(e->first()); i++)
        {
          int d = depth(e->arg(i+1));
          if (d > maxD) maxD = d;
        }
      }
      return maxD + 1;
    }
    void getTerms()
    {
      outs()<<"=======Base terms:\n";
      for (Expr v: vars)
      {
        allTerms[bind::typeOf(v)].push_back(v);
        outs()<<"Variable "<<*v<<" of type: "<<*bind::typeOf(v)<<"\n";
      }
      for (auto p: baseCtors)
      {
        if (!p.second || (p.second)->arity() != 2) continue;
        allTerms[p.first].push_back(bind::fapp(p.second));
        outs()<<"Ctor "<<*bind::fapp(p.second)<<" of type: "<<*(p.first)<<"\n";
      }

      outs()<<"\nfuncs:";
      for (Expr f: funcs) outs()<<" "<<*f;
      outs()<<"\n\n";

      int i, d;
      for (d = 1; d < maxDepth; d++)
      {
        ExprVector newTerms;
        for (Expr fdecl : funcs)
        {
          Expr ty = fdecl->last();
          int nArgs = bind::domainSz(fdecl);
          ExprVector conArgs(nArgs, NULL); // concrete args
          // check required type terms exist
          bool termsExist = true;
          for (i = 0; i < nArgs; i++)
            if (allTerms.count(bind::domainTy(fdecl, i)) == 0){
              termsExist = false;
              break;
            }
          // chose another function
          if (!termsExist) continue;

          // stack
          vector<int> stk(nArgs, 0);
          while (true)
          {
            bool allBaseCtor = true;
            for (i = 0; i < nArgs; i++)
            {
              int choice = stk[i];
              conArgs[i] = allTerms[bind::domainTy(fdecl, i)][choice];
              if (!isBaseCtor(conArgs[i])) allBaseCtor = false;
            }
            // ok to have len(nil) and such
            if (nArgs == 1) allBaseCtor = false;

            Expr term = bind::fapp(fdecl, conArgs);
            if (depth(term) == d+1 && !allBaseCtor) // at least d+1, not OK to have (append nil nil)
              newTerms.push_back(term);

            for (i = 0; i < nArgs; i++)
            {
              stk[i] ++;
              if (stk[i] < allTerms[bind::domainTy(fdecl, i)].size()) break;
              else stk[i] = 0;
            }
            if (i == nArgs) break;
          }
        }
        outs()<<"======Depth "<<d<<" terms ("<<newTerms.size()<<"):\n";
        for (Expr t : newTerms)
        {
          // TODO check depth
          Expr ty = bind::typeOf(t);
          allTerms[ty].push_back(t);
          outs()<<"  "<<*t<<" of type: "<<*ty<<"\n";
        }
      }
    }
    // void getTerms(Expr ty, int d) {
    //   if (d < maxDepth)
    //   {
    //     for (Expr fdecl : funcs) {
    //       if (!ty || ty == bind::typeOf(fdecl))
    //         select fdecl
    //     }
    //   }
    //   else if (d == maxDepth)
    //   {
    //     for (Expr v : vars) {
    //       if (!ty || ty == bind::typeOf(v))
    //         yield v
    //     }
    //   }
    // }
    ~TermEnumerator(){}
    
  };
  class ADTSolver
  {
    private:
    static int cntr;
    Expr goal;
    // assumptions should be copied, prevents changes propagating
    ExprVector assumptions;
    ExprVector constructors;

    ExprMap baseConstructors;
    ExprMap indConstructors;

    ExprFactory &efac;
    SMTUtils u;

    ExprVector rewriteHistory;
    vector<int> rewriteSequence;
    ExprSet rewriteSet;
    int maxDepth;
    int maxSameAssm;
    bool assertIHPrime;
    bool baseOrInd;


    int maxDepthCnt;
    int failureCnt;

    ExprSet failures;
    bool synthLemmas;

    ExprVector indCtorDecls;
    ExprMap valueMap;


    int nextInt;
    std::chrono::duration<int> maxTime;
    std::chrono::system_clock::time_point begin;
    public:
    int maxTermDepth;
    ADTSolver(Expr _goal, ExprVector& _assumptions, ExprVector& _constructors, int _maxDepth, int _maxSameAssm, bool flipIH) :
        goal(_goal), assumptions(_assumptions), constructors(_constructors),
        efac(_goal->getFactory()), u(_goal->getFactory()), maxDepth(_maxDepth), maxSameAssm(_maxSameAssm), assertIHPrime(flipIH),
        maxTime(5) // wait for 10 secs at most
    {
      // assertIHPrime = true;
      assert(isOpX<FORALL>(goal));
      // bind::IsConst isVar;
      outs()<<"goal: "<<*goal<<"\n";
      // outs()<<"===== quantified vars: ";
      // for (int i = 0; i < goal->arity() - 1; i++)
      // {

      //   outs()<<" "<<* (goal->arg(i));
      //   if (isOpX<FDECL>(goal->arg(i))) outs()<<"[is fdecl]";
      // }
      // outs()<<"\n";


      // default : no synth
      synthLemmas = false;
      cntr ++;
      nextInt = 0;
    }

    // bool p(Expr e){
    //   auto f = [this](){return this->cntr > 0;};
    //   outs()<<*e;
    //   return f();
    // }

    bool simplifyGoal()
    {
      // outs()<<"hello simplifyGoal\n";
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

    bool refuteGoal(Expr goalQF, int nTimes)
    {

      outs()<<"???? try to invalidate :"<<*goalQF<<"\n";

      for (int i = 0; i < nTimes; ++i)
      {
        for (auto & a : assumptions) {
          Expr goalSimpl = useAssumption(goalQF, a);
          if (goalSimpl != NULL) goalQF = goalSimpl;
        }
      }
      if (u.isEquiv(goalQF, mk<FALSE>(efac))){
        outs()<<"===*** REFUTED!!!\n";
        return false;
      } 
      if (u.isEquiv(goalQF, mk<TRUE>(efac))){
        outs()<<"===*** Valid!!!\n";
        return true;
      }
      return true;
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

    void useAssumptionMulti(Expr subgoal, Expr assm, ExprVector& results)
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
          if (subgoal != replaced)
          {
            results.push_back(replaced);
            return;
          }
        }
        if (isOpX<EQ>(assmQF))
        {
          vector<ExprMap> matchings;
          findMultiMatchingSubexpr (assmQF->left(), subgoal, args, matchings);
          for (ExprMap &match: matchings)
          {
            repl = assmQF;
            for (auto & a : match) repl = replaceAll(repl, a.first, a.second);
            results.push_back(replaceAll(subgoal, repl->left(), repl->right()));
          }
        }
        if ((isOpX<LEQ>(assmQF) && isOpX<LEQ>(subgoal)) ||
            (isOpX<GEQ>(assmQF) && isOpX<GEQ>(subgoal)) ||
            (isOpX<LT>(assmQF) && isOpX<LT>(subgoal)) ||
            (isOpX<GT>(assmQF) && isOpX<GT>(subgoal)))
        {
          vector<ExprMap> matchings;
          findMultiMatchingSubexpr (assmQF->left(), subgoal, args, matchings);
          for (ExprMap &match: matchings)
          {
            repl = assmQF;
            for (auto & a : match) repl = replaceAll(repl, a.first, a.second);
            if (u.implies(repl, subgoal)) results.push_back(mk<TRUE>(efac));
          }
        }
      }
      else
      {
        // for a quantifier-free assumption (e.g., inductive hypotheses),
        // we create an SMT query and check with Z3
        // TODO: we can do so for ALL constistent quantifier-free assumptions at once
        if (u.implies(assm, subgoal)) results.push_back(mk<TRUE>(efac));
        if (isOpX<EQ>(assm))
        {
          Expr res = replaceAll(subgoal, assm->left(), assm->right());
          if (res != subgoal)
          {
            results.push_back(res);
          }
        }
      }
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
      subgoal = replace(subgoal, mk_fn_map(SimplifyAdd0()));
      Expr newGoal = rewriteITE(subgoal);
      if (newGoal) subgoal = newGoal;

      if (u.isEquiv(subgoal, mk<TRUE>(efac))) {
        outs()<<"Proof sequence:";
        for (int a : rewriteSequence)
          outs()<<" "<<a;
        outs()<<"\n";
        return true;
      }

      // check recursion depth
      if (rewriteSequence.size() >= maxDepth) 
      {
        // outs() << "reached max recursion depth! \n";
        maxDepthCnt ++;
        return false;
      }
      
      // check consecutive applications of the same assumption
      if (rewriteSequence.size() >= maxSameAssm){
        int assmId = rewriteSequence.back();
        int offset = rewriteSequence.size() - maxSameAssm - 1;
        int i = 0;
        for (; i < maxSameAssm; i++)
          if (rewriteSequence[i + offset] != assmId)
            break;
        // test here
        if (i == maxSameAssm){
          // outs() << "same assm["<<assmId<<"] applied too many times! \n";
          return false;
        }
      }



      auto elapsed = std::chrono::system_clock::now() - begin;
      if (elapsed > maxTime){
        outs()<<"TIME OUT!!!!\n";
        return false;
      }

      bool noMoreRewriting = true;
      for (int i = 0; i < assumptions.size(); i++)
      {
        // only apply this rule when proving inductive case
        if (baseOrInd && assertIHPrime && rewriteSequence.size()){
          int assmId = rewriteSequence.back();

          // IH and IH' cannot be applied back-to-back
          if ( ((assmId == assumptions.size() - 1) && (i == assmId - 1))
            || ((assmId == assumptions.size() - 2) && (i == assmId + 1)))
            continue;
          // TODO: IH and IH' can be applied to different part of the expression
        }
        Expr a = assumptions[i];
        // Expr res = useAssumption(subgoal, a);
        ExprVector results;
        useAssumptionMulti(subgoal, a, results);
        for (Expr res : results)
        {
          if (res != NULL)
          {
            noMoreRewriting = false;
            if (rewriteSet.find(res) != rewriteSet.end()){
              // outs()<<"revisit bt\n";
              continue;
            }
            rewriteSet.insert(res);
            //outs () << "rewritten [" << i << "]:   " << *res << "\n";
            // save history
            rewriteHistory.push_back(res);
            rewriteSequence.push_back(i);

            if  (rewriteAssumptions(res))
              return true;
            else {
              // failed attempt, remove history
              rewriteHistory.pop_back();
              rewriteSequence.pop_back();
              // backtrack:
              // outs()<<"bt\n";
              // outs () << "backtrack to:    " << *subgoal << "\n";
            }
          }
        }
      }
      // failure node, stuck here, have to backtrack

      if (noMoreRewriting){
        int fcnt = failures.size();
        failures.insert(subgoal);
        if (fcnt < failures.size())
        {
          outs()<<"***new failure== "<< *subgoal<<"\nreached by: \n";
          for (int k = 0; k < rewriteSequence.size(); k ++)
            outs()<<"["<<rewriteSequence[k]<<"] "<<*(rewriteHistory[k])<<"\n";

        }
        failureCnt ++;
      }
      // TODO: collect failure node "subgoal, rewriteHistory, rewriteSequence, [assumptions]" 
      // generalize "subgoal" (replace () )
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
        Expr s = bind::mkConst(mkTerm<string> ("_v_" + to_string(i) + "_sn" + to_string(cntr), efac), goal->arg(i)->last());
        goalQF = replaceAll(goalQF, bind::fapp(goal->arg(i)), s);
      }

      // prove the base case
      Expr baseSubgoal = replaceAll(goalQF, typeDecl, baseConstructor);
      printAssumptions();
      outs() << "\nBase case:       " << *baseSubgoal << "\n";
      rewriteSet.clear();
      rewriteSequence.clear();
      rewriteHistory.clear();
      maxDepthCnt = 0;
      failureCnt = 0;
      failures.clear();

      baseOrInd = false;

      begin = std::chrono::system_clock::now();
      bool baseres = basenums.empty() ?
              rewriteAssumptions(baseSubgoal) :
              tryStrategy(baseSubgoal, basenums);
      
      outs()<<"======== base # of leaves at max depth: "<<maxDepthCnt<<"\n";
      outs()<<"======== base # of failure nodes: "<<failureCnt<<"\n";

      // remove baseSubgoal
      failures.erase(baseSubgoal);
      outs()<<"======== base # of unique failure nodes: "<<failures.size()<<"\n";
      
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
          outs () << "\nProceeding to nested induction for base case\n";
          newArgs.push_back(replaceAll(goal->last(), typeDecl, baseConstructor));
          Expr newGoal = mknary<FORALL>(newArgs);
          ADTSolver sol (newGoal, assumptions, constructors, maxDepth, maxSameAssm, assertIHPrime);
          if (!sol.solve (basenums, indnums)) 
          {
            outs () << "\nNested induction for base case failed!!!\n";
            return false;
          }
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
        Expr s = bind::mkConst(mkTerm<string> ("_t_" + to_string(i) + "_sn" + to_string(cntr), efac), indConstructor->arg(i));
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
      for (auto & a : indHypotheses) {
        assumptions.push_back(a);
        // always add symmetric IH?
        if (assertIHPrime)
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

      rewriteSet.clear();
      rewriteSequence.clear();
      rewriteHistory.clear(); // TODO: use it during the base case proving
      maxDepthCnt = 0;
      failureCnt = 0;
      failures.clear();
      baseOrInd = true;
      begin = std::chrono::system_clock::now();
      bool indres = indnums.empty() ?
               rewriteAssumptions(indSubgoal) : // TODO: apply DFS, rank the failure nodes, synthesis of new lemma
               tryStrategy(indSubgoal, indnums);
      
      outs()<<"======== ind # of leaves at max depth: "<<maxDepthCnt<<"\n";
      outs()<<"======== ind # of failure nodes: "<<failureCnt<<"\n";
      failures.erase(indSubgoal);
      outs()<<"======== ind # of unique failure nodes: "<<failures.size()<<"\n";

      // for (Expr f : failures) outs()<<"     "<<*f<<"\n";
      /*for (Expr f: failures)
      {
        outs()<<";      "<<*f<<"\n";
        
        // (f->arg(0)->arg(1)) ->Print(cout);

        // if (bind::isConst<AD_TY>((f->arg(0)->arg(1))))
        //   cout<<" is Const";
        bind::IsConst isVar;
        // if (isVar((f->arg(0)->arg(1))))
        //   cout<<" is Var";


        ExprVector args;
        filter(f, isVar, back_inserter(args));
        for (Expr e : args)
        {
          outs()<<"                "<<*e<<" of Type ";
          Expr typeDecl = bind::typeOf(e);
          outs()<<*typeDecl;

          // YES isOpX<FAPP>(e)
          // YES isOpX<AD_TY>(typeDecl)

          Expr baseCtor = baseConstructors[typeDecl];
          if (baseCtor != NULL && e == bind::fapp(baseCtor))
              outs()<<" is base ctor";

          outs()<<"\n";
        }

        // 1. 
        // ADTSolver newSolver()
      }
      */
      // outs()<<"# of baseCtors: "<<baseConstructors.size()<<"\n";
      // for (auto p : baseConstructors)
      // {
      //   outs()<<"======== typename: "<<*(p.first);
      //   if (isOpX<AD_TY>(p.first)) outs()<<" [is AD_TY] ";
      //   if (p.second)
      //     outs()<<*(p.second);
      //   outs()<<"\n";
      // }

      // outs()<<"# of indCtors: "<<indConstructors.size()<<"\n";
      // for (auto p : indConstructors)
      // {
      //   outs()<<"======== typename: "<<*(p.first);
      //   if (isOpX<AD_TY>(p.first)) outs()<<" [is AD_TY] ";
      //   if (p.second)
      //     outs()<<*(p.second);
      //   outs()<<"\n";
      // }

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
          outs () << "\nProceeding to nested induction for ind case\n";
          newArgs.push_back(replaceAll(goal->last(), bind::fapp(typeDecl), indConsApp));
          Expr newGoal = mknary<FORALL>(newArgs);
          ADTSolver sol (newGoal, assumptions, constructors, maxDepth, maxSameAssm, assertIHPrime);
          return sol.solve (basenums, indnums);
        }
        return false;
      }

    }

    bool isVarFn(Expr e){
      if (isOpX<FAPP> (e) && e->arity () == 1 && isOpX<FDECL> (e->first())) {
        Expr baseCtor = baseConstructors[bind::typeOf(e)];
        // exclude base constructors (e.g. nil:Lst)
        return (baseCtor == NULL || e != bind::fapp(baseCtor));
      } else return false;
    }
    bool isBaseCtorFn(Expr e){
      if (isOpX<FAPP> (e) && e->arity () == 1 && isOpX<FDECL> (e->first())
        && (e->first() == baseConstructors[bind::typeOf(e)])) return true;
        else return false;
    }
    bool isIndCtorFn(Expr e){
      if (isOpX<FAPP> (e) && isOpX<FDECL> (e->first())){
        if (find(indCtorDecls.begin(), indCtorDecls.end(), e->first()) != indCtorDecls.end())
          return true;
      }
      return false;
    }
    void insertUniqueGoal(Expr goalQF, ExprVector& candidates) {
      goalQF = simplifyAdd(goalQF);
      ExprVector vars;
      filter(goalQF, [this](Expr e){return isVarFn(e);}, back_inserter(vars));
      // remove fapp for quantified vars
      for (Expr &v : vars) v = v->first();
      vars.push_back(goalQF);
      Expr newGoal = mknary<FORALL>(vars);
      if (find(candidates.begin(), candidates.end(), newGoal) == candidates.end())
      {
        candidates.push_back(newGoal);
        outs()<<"****===*** new goal:  "<<*newGoal<<"\n";
      }
    }
    Expr rewriteITE(Expr e)
    {
      if (!isOpX<EQ>(e) || e->arity() != 2) return NULL;
      Expr ite;
      if (isOpX<ITE>(e->left()))
      {
        ite = e->left();
        e = e->right();
      }else if (isOpX<ITE>(e->right())){
        ite = e->right();
        e = e->left();
      }else return NULL;

      // Expr thenBr = boolop::limp(ite->left(), mk<EQ>(e, ite->arg(1)));
      // Expr elseBr = boolop::limp(boolop::lneg(ite->left()), mk<EQ>(e, ite->arg(2)));
      Expr thenBr = mk<EQ>(ite->arg(1), e);
      Expr elseBr = mk<EQ>(ite->arg(2), e);
      if (u.isEquiv(thenBr, mk<TRUE>(efac))) return elseBr;
      if (u.isEquiv(elseBr, mk<TRUE>(efac))) return thenBr;
      else return NULL;
    }
    void generalize(Expr goalQF, ExprVector &qVars, ExprVector &candidates)
    {
      ExprVector ctorApps;
      filter(goalQF, [this](Expr e){return isIndCtorFn(e);}, back_inserter(ctorApps));
      for (Expr ctor: ctorApps){
        outs()<<"**** found ind ctor: "<<*ctor;
        ExprVector ctorArgs;
        filter(ctor, [this](Expr e){return isVarFn(e);}, back_inserter(ctorArgs));
        Expr ty = bind::typeOf(ctor);
        auto tyStr = getTerm<string>(ty->first());
        Expr newVar = bind::mkConst(mkTerm<string>("_lm_ind_" + tyStr, ctor->efac()), ty);
        outs()<<" replaced by newVar: "<<*newVar<<"\n";
        Expr newGoalQF = replaceAll(goalQF, ctor, newVar);

        bool replaceSuccess = true;
        if (isOpX<EQ>(goalQF))
        {
          bool ctorOnLHS = contains(goalQF->left(), ctor);
          bool ctorOnRHS = contains(goalQF->right(), ctor);
          if (!(ctorOnLHS && ctorOnRHS)) replaceSuccess = false;
        }
        if (replaceSuccess){
          for (Expr arg: ctorArgs)
          if (contains(newGoalQF, arg)){
            replaceSuccess = false;
            break;
          } 
        }
        if (replaceSuccess)
          insertUniqueGoal(newGoalQF, candidates);
        else
        {
          outs()<<"(*************Term Enum preparations***********)\n\n";
          Expr LHS = newGoalQF->first();

          // replace base ctor
          ExprVector baseCtors;
          filter(LHS, [this](Expr e){return isBaseCtorFn(e);}, back_inserter(baseCtors));
          if (!baseCtors.empty()) {
            Expr baseCtor = baseCtors[0];
            Expr ty = bind::typeOf(baseCtor);
            auto tyStr = getTerm<string>(ty->first());
            Expr newVar = bind::mkConst(mkTerm<string>("_lm_base_" + tyStr, baseCtor->efac()), ty);
            LHS = replaceAll(LHS, baseCtor, newVar);
          }
          // generalize Function calls
          ExprSet fnApps;
          recFilter(LHS, [this](Expr e){return isOpX<FAPP>(e) && e->arity() > 1;}, inserter(fnApps, fnApps.end()));
          vector<pair<int, Expr>> sortedFnApps;
          for (Expr e: fnApps){
            int sz = dagSize(e);
            outs()<<"found function application size "<<sz<<" "<<*e<<"\n";
            sortedFnApps.emplace_back(sz, e);
          } 
          std::sort(sortedFnApps.begin(), sortedFnApps.end(), 
            [](pair<int, Expr>& x, pair<int, Expr>& y){return x.first < y.first;});

          ExprVector LHSchoices;
          for (auto p : sortedFnApps)
          {
            Expr fapp = p.second;
            Expr ty = bind::typeOf(fapp);
            string tyStr;
            if (isOpX<INT_TY>(ty)) tyStr = "INT";
            else tyStr = getTerm<string>(ty->first());
            Expr newVar = bind::mkConst(mkTerm<string>("_lm_fapp_" + tyStr, fapp->efac()), ty);
            LHSchoices.push_back(replaceAll(LHS, fapp, newVar));
          }
          LHS = LHSchoices[0];

          outs()<<"template LHS: "<<*LHS<<"\n";
          Expr lhsTy = bind::typeOf(LHS);
          ExprSet lhsVars;
          filter(LHS, [this](Expr e){return isVarFn(e);}, inserter(lhsVars, lhsVars.end()));

          TermEnumerator tEnum(LHS, baseConstructors, indConstructors, maxTermDepth);
          // MAYBE collect all functions
          // for (Expr assm : assumptions)
          //   tEnum.addFunctions(assm);
          tEnum.getTerms();
          ExprVector &tList = tEnum.allTerms[lhsTy];
          int validCnt = tList.size();
          /*for (Expr t: tEnum.allTerms[lhsTy])
          {
            // if (bind::typeOf(t) != lhsTy) continue;
            ExprVector rhsVars;
            filter(t, [this](Expr e){return isVarFn(e);}, back_inserter(rhsVars));
            if (rhsVars == lhsVars) {
              insertUniqueGoal(mk<EQ>(LHS, t), candidates);
              tList.push_back(t);
              validCnt++;
            }
          }*/
          // return;
          outs()<<"==== # terms "<<validCnt<<"\n";

          /* TEMPLATE 1
           * LHS fixed = <???>
           * fill RHS
           */
          /*for (int i = 0; i < validCnt; i ++)
          {
            ExprVector rhsVars;
            filter(tList[i], [this](Expr e){return isVarFn(e);}, back_inserter(rhsVars));
            if (rhsVars == lhsVars)
              insertUniqueGoal(mk<EQ>(LHS, tList[i]), candidates);
          }*/
          /* TEMPLATE 2
           * LHS fixed = <???> + <???> for Int
           * fill RHS x 2
           */
          
          for (int i = 0; i < validCnt; i ++)
            for (int j = i; j < validCnt; j++)
            {
              Expr RHS = mk<PLUS>(tList[i], tList[j]);
              ExprSet rhsVars;
              filter(RHS, [this](Expr e){return isVarFn(e);}, inserter(rhsVars, rhsVars.end()));
              if (rhsVars == lhsVars)
                insertUniqueGoal(mk<EQ>(LHS, RHS), candidates);
            }
        }
      }
      
      if (ctorApps.empty()) {
        outs()<<"*** attempt rewrite ITE and simplify arithmetic\n";
        goalQF = replace(goalQF, mk_fn_map(SimplifyAdd0()));
        Expr simplGoal = rewriteITE(goalQF);
        if (simplGoal) insertUniqueGoal(simplGoal, candidates);
        else insertUniqueGoal(goalQF, candidates);
      }
    }
    int cntFuncFn(Expr e){
      auto isFuncFn = [](Expr e){return isOpX<FDECL> (e) && e->arity () >= 3;};
      ExprSet funcs;
      filter(e, [](Expr e){return isOpX<FDECL> (e) && e->arity () >= 3;}, 
        inserter(funcs, funcs.end()));
      return funcs.size();
    }

    void resetValues(){
      nextInt = 0;
      valueMap.clear();
    }
    Expr getNextValue(Expr ty)
    {
      if (isOpX<INT_TY>(ty))
        return mkTerm<mpz_class>(++nextInt, efac);
      else {
        if (valueMap.count(ty) == 0){
          valueMap[ty] = bind::fapp(baseConstructors[ty]);
        }
        Expr currentValue = valueMap[ty];
        Expr indCtorDecl = indConstructors[ty];

        ExprVector args;
        args.push_back(indCtorDecl);
        for (int i = 1; i < indCtorDecl->arity() - 1; ++i)
        {
          Expr argTy = indCtorDecl->arg(i);
          if (argTy == ty) args.push_back(currentValue);
          else args.push_back(getNextValue(argTy));
        }
        currentValue = mknary<FAPP>(args);
        valueMap[ty] = currentValue;
        return currentValue;
      }
    }

    bool tryLemmas(Expr originaGoal, ExprVector assm, bool tryAgain = true)
    {
      if (failures.empty()) {
        outs()<<"ATTENTION!!! max search depth not enough to reach failure points!!\n";
        return false;
      }
      ExprVector candidates;

      // rank failures. less functions the better
      vector<pair<int, Expr>> sortedF;
      for (Expr f : failures){
        sortedF.emplace_back(cntFuncFn(f), f);
      }
      std::sort(sortedF.begin(),sortedF.end(), 
        [](pair<int, Expr>& x, pair<int, Expr>& y){return x.first < y.first;});
      for (auto x : sortedF)
      {
        Expr f = x.second;
        outs()<<";failure      "<<*f<<"\n";
        ExprVector vars;
        ExprVector renamedVars;
        filter(f, [this](Expr e){return isVarFn(e);}, back_inserter(vars));
        for (Expr v: vars)
        {
          outs()<<" "<<*v;
          Expr varDecl = v->left();
          auto nameStr = "_lm" + getTerm<string>(varDecl->left());
          Expr newName = mkTerm<string>(nameStr, v->efac());
          renamedVars.push_back(bind::fapp(bind::rename(varDecl, newName)));
        }
        Expr goalQF = replaceAll(f, vars, renamedVars);
        generalize(goalQF, renamedVars, candidates);
        //break;
        outs()<<"\n";
      }
      vector<int> basenums;
      vector<int> indnums;
      bool res;
      outs()<<"\n\n======== # of lemma candidates"<<candidates.size()<< "\n\n";

      ExprVector filteredCandidates;

      for (Expr lemma: candidates){
        int nQVars = lemma->arity() - 1;
        int nTest = 3;
        resetValues();
        while (nTest--)
        {
          Expr lemmaQF = lemma->last();
          for (int i = 0; i < nQVars; i++)
          {
            Expr qVar = bind::fapp(lemma->arg(i));
            Expr ty = bind::typeOf(qVar);
            lemmaQF = replaceAll(lemmaQF, qVar, getNextValue(ty));
          }
          
          // bad lemma
          
          if (refuteGoal(lemmaQF, 20) == false)  break;  
        }

        // some test failed
        if (nTest != -1) continue;
        outs()<<"\nlemma is prolly good:"<<*lemma<<"\n";
        filteredCandidates.push_back(lemma);

        // jsut try 20 
        if (filteredCandidates.size() > 20) break;
      }

      outs()<<"\n\n======== # of FILTERED lemma candidates"<<filteredCandidates.size()<< "\n\n";

      for (Expr lemma: filteredCandidates)
      {
        outs()<<"\n\n======={ try proving lemma\n\n";
        ADTSolver solLemma (lemma, assm, constructors, maxDepth, maxSameAssm, assertIHPrime);
        res = solLemma.solve (basenums, indnums);
        if (!res) {

          outs()<<" ****** not solved. attempt lemma synth on proposed lemma\n***\n***\n";
          solLemma.tryLemmas(lemma, assumptions, true);

          outs()<<"\n\n======= lemma is invalid / not proved }\n\n";
          continue;
        }

        
        outs()<<"\n\n========lemma is valid and proved}\n\n";
        assm.push_back(lemma);
        ADTSolver sol (originaGoal, assm, constructors, maxDepth, maxSameAssm, assertIHPrime);
        outs()<<"\n\n======={ try original goal with lemma\n\n";
        res = sol.solve (basenums, indnums);
        if (res) {
          outs()<<"===========Solved with new lemma: "<< *lemma <<"}\n";
          return true;
        }else {
          outs()<<"===========Not solved with new lemma: "<< *lemma <<"}\n";
          if (tryAgain){
            outs()<<"===========tryLemmas 2nd attempt begin{\n";
            res = sol.tryLemmas(originaGoal, assm, false);
            outs()<<"===========tryLemmas 2nd attempt end}\n";
            if (res) return true;
          }
        }
        // outs()<<"\n\n=======================\n\n";
        assm.pop_back();
      }
      return false;
    }
    bool solve(vector<int>& basenums, vector<int>& indnums)
    {
      unfoldGoal();
      rewriteHistory.push_back(goal);
      for (int i = 0; i < 8; i++)
      {
        if (simplifyGoal())
        {
          outs () << "Trivially Proved\n";
          return true;
        }
      }

      for (auto p : indConstructors)
      {
        if (isOpX<AD_TY>(p.first) && p.second != NULL)
          indCtorDecls.push_back(p.second);
      }

      // simple heuristic: if the result of every rewriting made the goal larger, we rollback
      /*bool toRollback = true;
      for (int i = 1; i < rewriteHistory.size(); i++)
      {
        toRollback = toRollback &&
            (treeSize(rewriteHistory[i-1]) < treeSize(rewriteHistory[i]));
      }

      if (toRollback) goal = rewriteHistory[0];*/
      if (treeSize(goal) >= treeSize(rewriteHistory[0])) goal = rewriteHistory[0];

      outs () << "Simplified goal: " << *goal << "\n\n";
      
      // Expr LHS = goal->arg(2)->first();

      //     Expr lhsTy = bind::typeOf(LHS);
      //     ExprVector lhsVars;
      //     filter(LHS, [this](Expr e){return isVarFn(e);}, back_inserter(lhsVars));
      // TermEnumerator tEnum(LHS, baseConstructors, indConstructors, maxTermDepth);
      // tEnum.isOk();

      // ExprVector &tList = tEnum.allTerms[lhsTy];
      //     int validCnt = tList.size();
                   // return;
      //     outs()<<"==== # terms "<<validCnt<<"\n";
      //     ExprVector lemmaCandidates;
      //     for (int i = 0; i < validCnt; i ++)
      //       {
      //         Expr cand = tList[i];
      //         ExprVector rhsVars;
      //         filter(cand, [this](Expr e){return isVarFn(e);}, back_inserter(rhsVars));
      //         if (rhsVars == lhsVars){
      //           insertUniqueGoal(cand, lemmaCandidates);
      //         }
      //       }
      //   outs()<<"==== # lemmas "<<lemmaCandidates.size()<<"\n";
      // return false;
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

  int ADTSolver::cntr = 0;
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

  void adtSolve(EZ3& z3, Expr s, char* basecheck, char *indcheck, int maxDepth, int maxSameAssm, bool flipIH, int maxTermDepth)
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
    ADTSolver sol (goal, assumptions, constructors, maxDepth, maxSameAssm, flipIH);
    sol.maxTermDepth = maxTermDepth;
    bool res = sol.solve (basenums, indnums);
    if (!res){
      outs()<<" *** not solved. attempt lemma synth\n";
      sol.tryLemmas(goal, assumptions, true);
    }
  }
}

#endif
