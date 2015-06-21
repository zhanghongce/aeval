#!/usr/bin/env python

import z3
import z3core
import stats

from z3_utils import *
from LogManager import LoggingManager
import os,subprocess,sys
import shutil
import stats


root = os.path.dirname (os.path.dirname (os.path.realpath (__file__)))
verbose=False
xml=False

class Feas(object):
    def __init__(self, args, ctx, fp):
        self.log = LoggingManager.get_logger(__name__)
        self.args = args
        self.fp = fp
        self.ctx = ctx
        self.preds = []
        return

    def solve(self, smt2_file):
        """
        Start solving
        """
        self.log.info("Start solving...")
        self.fp.set (engine='spacer')
        if self.args.stat:
            self.fp.set('print.statistics',True)
        self.fp.set('use_heavy_mev',True)
        self.fp.set('pdr.flexible_trace',True)
        self.fp.set('reset_obligation_queue',False)
        self.fp.set('spacer.elim_aux',False)
        if not self.args.pp:
            self.log.info("No pre-processing")
            self.fp.set ('xform.slice', False)
            self.fp.set ('xform.inline_linear',False)
            self.fp.set ('xform.inline_eager',False)
        with stats.timer ('Parse'):
            self.log.info('Parsing  ... ' + str(smt2_file))
            q = self.fp.parse_file (smt2_file)
            self.preds = get_preds(self.fp)
            self.checkFeasibility(q[0])


    def checkFeasibility(self, expr_query):
        self.log.info("Check Feasibility .... ")
        done = False
        while not done:
            with stats.timer ('Query'):
                res = self.fp.query (expr_query)
                if res == z3.sat:
                    self.log.info("CEX: More work")
                    expr_query = self.cex(expr_query)
                elif res == z3.unsat:
                    self.log.info("UNSAT: Set of Invariants:")
                    for p in self.preds:
                        lemmas = fp_get_cover_delta (self.fp, p)
                        print "Predicate: ", p.decl()
                        print "Invariant: ", lemmas
                        print "-----------"
                    done = True


    def cex(self, qr):
        """ Create a new query """
        self.log.info("Creating a new query ...")
        raw_cex = self.fp.get_ground_sat_answer()
        ground_sat = get_conjuncts(raw_cex)
        if verbose: print "RAW CEX:", ground_sat
        var_flags = self.getFlags(ground_sat[1])
        failing_flag_idx = self.getIndexFlag(ground_sat[1], len(var_flags)+1) # get the index of the failing flag
        self.log.info("Failing Flag index is : " + str(var_flags[failing_flag_idx]))
        new_query = self.mkNewQuery(qr,failing_flag_idx)
        return new_query


    def getIndexFlag(self, pred, flags_len):
        """
        return the index of the flag to be changed
        """
        ch = pred.children()
        i=0
        for val in ch[0:flags_len]:
            if z3.is_false(val):
                return i
            i+=1
        self.log.error("No Index found Failing Flag")
        return None

    def getFlags(self, pred):
        """
        Return a list of the flags variable
        """
        #STUPID HACK, Not correct yet, CORRECT ME
        flags = []
        for p in self.preds:
            if str(p.decl()) == str(pred.decl()):
                for var in p.children():
                    p_split = str(var).split('_')
                    if "__" in str(var):
                        flags.append(var)
        return flags


    def mkNewQuery(self,expr,index):
        """
        assign True to the variables at position index of expr
        return an expr
        """
        z3ctx = expr.ctx
        new_value = z3.BoolVal(True, z3ctx)
        body = expr.body()
        pred_name = body.decl()
        sub = []
        for i in range (0, body.num_args ()):
            arg = body.arg (i)
            if i != index: sub.append ((arg, arg))
            else: sub.append((arg,new_value))
        new_body = z3.substitute(body, sub)
        if verbose: print 'Original Body: ', body, '\n Modified Body:', new_body
        exists_var = []
        for i in range (0, new_body.num_args ()):
            arg = new_body.arg (i)
            if z3.is_var(arg):
                v_name = z3.Const("__n"+str(i), z3.BoolSort())
                exists_var.append(v_name)
        return z3.Exists(exists_var, new_body)






def split_body (body):
  """ Splits body into Pred and Tail, where Pred is the only
  uninterpreted predicate (instance), and tail is all interpreted"""
  pred = getFirstConjunct (body)
  if pred.decl ().kind () != z3.Z3_OP_UNINTERPRETED:
    pred = None
    tail = body.children ()
  else:
    assert body.num_args () > 0
    tail = []
    if z3.is_and (body):
      tail.extend (body.children ()[1:])
  return pred, tail


def fp_add_cover (fp, pred, lemma, level=-1):
    # no trivial lemmas
    if z3.is_true (lemma): return

    assert (z3.is_app (pred))
    sub = []
    for i in range (0, pred.num_args ()):
        arg = pred.arg (i)
        sub.append ((arg,
                     z3.Var (i, arg.decl ().range ())))

    tlemma = z3.substitute (lemma, sub)
    if verbose:
        print "Lemma for ", pred.decl (), ": ", tlemma
    fp.add_cover (level, pred.decl (), tlemma)


def fp_get_cover_delta (fp, pred, level=-1):
    sub = []
    for i in range (0, pred.num_args ()):
        sub.append (pred.arg (i))
    lemma = fp.get_cover_delta (level, pred.decl ())
    if z3core.Z3_get_bool_value (fp.ctx.ctx, lemma.as_ast ()) != z3.unsat:
        lemma = z3.substitute_vars (lemma, *sub)
    return lemma


def get_preds (fp):
    seen = set ()
    res = list ()
    for rule in fp.get_rules ():
        pred = rule
        # A rule is of the form
        # FORALL? (BODY IMPLIES)? PRED
        if z3.is_quantifier (pred): pred = pred.body ()
        if is_implies (pred): pred = pred.arg (1)

        decl = pred.decl ()
        assert is_uninterpreted (decl)
        if z3key (decl) in seen: continue
        seen.add (z3key (decl))

        # if the rule contains a universal quantifier, replace
        # variables by properly named constants
        if z3.is_quantifier (rule):
            sub = [ z3.Const (bound_var_name (rule, i),
                              bound_var_sort (rule, i))
                    for i in range (0, rule.num_vars ()) ]
            pred = substitute_vars (pred, *sub)
        res.append (pred)
    return res




def parseArgs (argv):
    import argparse as a
    p = a.ArgumentParser (description='Feasibility check with SeaHorn')

    p.add_argument ('file', metavar='BENCHMARK', help='Benchmark file')
    p.add_argument ('--pp',
                    help='Enable default pre-processing',
                    action='store_true', default=False)


    p.add_argument ('--stat', help='Print statistics', dest="stat",
                    default=False, action='store_true')
    p.add_argument ('--verbose', help='Verbose', action='store_true',
                    default=False, dest="verbose")
    pars = p.parse_args (argv)
    global verbose
    verbose = pars.verbose
    return pars


def stat (key, val): stats.put (key, val)

def main (argv):
    args = parseArgs (argv[1:])
    stat ('Result', 'UNKNOWN')
    ctx = z3.Context ()
    fp = z3.Fixedpoint (ctx=ctx)
    feas = Feas(args,ctx,fp)
    feas.solve(args.file)


if __name__ == '__main__':
    res = None
    try:
        main (sys.argv)
    except Exception as e:
        print str(e)
    sys.exit (res)
