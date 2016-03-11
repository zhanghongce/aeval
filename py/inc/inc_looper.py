#!/usr/bin/env python

import sys
import os
import os.path
import atexit
import tempfile
import shutil
import subprocess as sub
import threading
import signal
import itertools
import re
import fileinput
import shutil
import itertools


root = os.path.dirname (os.path.dirname (os.path.realpath (__file__)))
verbose = True

def isexec (fpath):
    if fpath == None: return False
    return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

def parseOpt (argv):
    from optparse import OptionParser

    parser = OptionParser ()
    parser.add_option ("--save-temps", dest="save_temps",
                       help="Do not delete temporary files",
                       action="store_true",
                       default=False)
    parser.add_option ("--temp-dir", dest="temp_dir",
                       help="Temporary directory",
                       default=None)
    parser.add_option ('--finfo', dest='finfo', help='Funcs Info file', default='finfo_inc')
    parser.add_option ('--num_blks', dest='num_blks', help='Number of Basic Blocks', default=3, type=int)

    (options, args) = parser.parse_args (argv)
    return (options, args)

def createWorkDir (dname = None, save = False):
    if dname == None:
        workdir = tempfile.mkdtemp (prefix='seahornpar-')
    else:
        workdir = dname

    if verbose: print "Working directory", workdir

    if not save: atexit.register (shutil.rmtree, path=workdir)
    return workdir

def getSea ():
    seahorn = os.path.join (root, "../../bin/sea")
    if not isexec (seahorn):
        raise IOError ("Cannot find sea")
    return seahorn


def cat (in_file, out_file): out_file.write (in_file.read ())

running = list()

def runSeahorn (args, fname, stdout, stderr):

    args = args + [fname]
    if verbose: print ' '.join (args)
    return sub.Popen (args,
                      stdout=open (stdout, 'w'),
                      stderr=open (stderr, 'w'))



def getAnswer(out_file):
    output = open(out_file).read()
    if "BRUNCH_STAT Result TRUE" in output:
        return True
    elif "BRUNCH_STAT Result FALSE" in output:
        return False
    else:
        return None


def run (workdir, fname, finfo, num_blks):
    sea_cmd = getSea()
    name = os.path.splitext (os.path.basename (fname))[0]
    info = '--slice-function=\"' + finfo + '"'
    getInfo_cmd = [sea_cmd, 'finfo', info, fname]
    p = sub.Popen(getInfo_cmd, shell=False, stdout=sub.PIPE, stderr=sub.STDOUT)
    result_info, _ = p.communicate()
    all_funcs = {}
    if "INC_INFO" in result_info:

        print 'Functions info ...  OK'
        for info in result_info.split('\n'):
            if "INC_INFO" in info: continue
            elif "INC" in info:
                raw = info.split('|')
                f = {raw[1] : {'blks': raw[2], 'instr':raw[3]}}
                all_funcs.update(f)
        print 'Total number of functions ... ' + str(len(all_funcs))
        run_inc(all_funcs, fname, num_blks)
    else:
        print 'Functions info ... KO'
    return

def run_inc(all_funcs, fname, num_blks):
    sea_cmd = getSea()
    name = os.path.splitext (os.path.basename (fname))[0]
    analyzed = {}
    bash_script = ""
    f_script = open (fname+"_script.sh", "w")
    f_result = open (fname+"_result.txt", "w")
    all_result = "FUNCTION, NUM_BLKS, RESULT, FEASIBLE, INFEASIBLE, ROUNDS, QUERY_TIME\n"
    for func,v in all_funcs.iteritems():
        if int(v['blks']) > num_blks:
            print 'Running Function ... ' + func + '| BLK ...' + v['blks']
            info = '--slice-function=' + func.strip()
            cmd = [sea_cmd, 'inc', info, '--horn-no-verif', '--lower-invoke',
                   '--devirt-functions', '--step=incsmall', '--inc_verbose',
                   '--save', '--timeout=60.0', fname]
            cmd_sc = [sea_cmd, ' inc ', info, ' --horn-no-verif ', '--lower-invoke ',
                   '--devirt-functions ', '--step=incsmall ', '--inc_verbose ',
                   '--save ', '--timeout=60.0 ', fname]
            analyzed.update({func:v})
            bash_script += ''.join(cmd_sc) + '\n'
            f_script.write(bash_script)
            p = sub.Popen(cmd, shell=False, stdout=sub.PIPE, stderr=sub.STDOUT)
            result, _ = p.communicate()
            func_res = ""
            for r in result.split('\n'):
                if 'INC_STAT' in r: func_res += r + "\n"
            tmp_split = func_res.split("\n")
            res = (tmp_split[0]).split('|')[2]
            cons = (tmp_split[1]).split('|')[2]
            incs = (tmp_split[2]).split('|')[2]
            rounds = (tmp_split[3]).split('|')[2]
            query = (tmp_split[4]).split('|')[2]
            new_result = func + " , " + v['blks'] + " , " + res + " , " + cons + " , " + incs + " , " + rounds + " , " + query + "\n"
            all_result += new_result
            print new_result
    f_result.write(all_result)
    f_result.close()
    print 'Analyzed functions ... ' + str(len(analyzed))
    return


def main (argv):
    (opt, args) = parseOpt (argv)

    workdir = createWorkDir (opt.temp_dir, opt.save_temps)
    returnvalue = 0
    fname = args[1]
    finfo = opt.finfo
    num_blks = opt.num_blks
    run(workdir, fname, finfo, num_blks)
    return returnvalue


# if __name__ == '__main__':
#     # unbuffered output
#     sys.stdout = os.fdopen (sys.stdout.fileno (), 'w', 0)
#     try:
#         sys.exit (main (sys.argv))
#     except KeyboardInterrupt:
#         pass
#     except Exception as e:
#         print 'here'
#     finally:
#         sys.exit(0)

if __name__ == '__main__':
    res = None
    try:
        res = main (sys.argv)
    finally:
        print '\n ... DONE ...'
    sys.exit (res)
