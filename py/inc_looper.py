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
    seahorn = os.path.join (root, "inc_build/run/bin/sea")
    print seahorn
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

        print 'Generated Functions info ... '
        for info in result_info.split('\n'):
            if "INC_INFO" in info: continue
            elif "INC" in info:
                raw = info.split('|')
                f = {raw[1] : {'blks': raw[2], 'instr':raw[3]}}
                all_funcs.update(f)
        run_inc(all_funcs, fname, num_blks)
    else:
        print 'No generated functions info ...'
    return

def run_inc(all_funcs, fname, num_blks):
    sea_cmd = getSea()
    name = os.path.splitext (os.path.basename (fname))[0]
    for func,v in all_funcs.iteritems():
        if int(v['blks']) > num_blks:
            print 'Running Function ... ' + func
            info = '--slice-function=\"' + func.strip() + '"'
            cmd = [sea_cmd, 'inc', info, '--horn-no-verif', '--step=incsmall', fname]
            p = sub.Popen(cmd, shell=False, stdout=sub.PIPE, stderr=sub.STDOUT)
            result, _ = p.communicate()
            print result
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
