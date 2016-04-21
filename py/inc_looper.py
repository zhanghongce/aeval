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
verbose = False
f_result = None

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
    parser.add_option ('--save', dest='save', help='Save results into file', default='save')

    parser.add_option ('--num_blks', dest='num_blks', help='Number of Basic Blocks', default=0, type=int)
    parser.add_option ('--timeout', dest='timeout', help='Timeout per function', default=10.00, type=float)
    parser.add_option ('--verbose', help='', action='store_true', default=False, dest="verbose")
    parser.add_option ('--boa', help='Add buffer overflow', action='store_true', default=False, dest="boa")
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
    path = os.path.abspath (sys.argv[0])
    path = os.path.dirname(path)
    seahorn = os.path.join(path,'sea')
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


def run (workdir, fname, finfo, num_blks, opt):
    print "Getting functions information ..."
    sea_cmd = getSea()
    name = os.path.splitext (os.path.basename (fname))[0]
    info = '--slice-function=\"' + finfo + '"'
    getInfo_cmd = [sea_cmd, 'finfo', info, '-O0', fname]
    p = sub.Popen(getInfo_cmd, shell=False, stdout=sub.PIPE, stderr=sub.STDOUT)
    result_info, _ = p.communicate()
    if verbose: print "Function infos:\n" + result_info
    all_funcs = {}
    for info in result_info.split('\n'):
        if 'INC' in info:
            raw = info.split('|')
            f = {raw[1] : {'blks': raw[2], 'instr':raw[3]}}
            all_funcs.update(f)
    if len(all_funcs) > 0:
        print 'Functions infos ...  OK'
        print 'Total number of functions ... ' + str(len(all_funcs))
        run_inc(all_funcs, fname, num_blks, opt)
    else:
        print 'Functions info ...  KO'
    return

def run_inc(all_funcs, fname, num_blks, opt):
    sea_cmd = getSea()
    name = os.path.splitext (os.path.basename (fname))[0]
    analyzed = {}
    bash_script = ""
    f_script = open (fname+"_script.sh", "w")
    global f_result
    f_result = open (fname+"_result.txt", "w")
    all_result = "FUNCTION, NUM_BLKS, RESULT, LINE_NUMBER(S), ROUNDS, QUERY_TIME\n"
    f_result.write(all_result)
    for func,v in all_funcs.iteritems():
        if int(v['blks']) >= num_blks:
            print 'Checking Inconsistency ... ' + func + '| BLK ...' + v['blks']
            info = '--slice-function=' + func.strip()
            my_timeout = '--timeout=' + str(opt.timeout)
            boa = '--boa=2' if opt.boa else ''
            cmd = [sea_cmd, 'inc', info, '--horn-no-verif', '--lower-invoke', boa,
                   '--devirt-functions', '--step=incsmall', '--inc_verbose', '--horn-df=bla.txt',
                   my_timeout, '-g', '-O0', '--null-check', '--lower-assert', fname]
            cmd_sc = [sea_cmd, ' inc ', info, ' --horn-no-verif ', '--lower-invoke ',
                   '--devirt-functions ', '--step=incsmall ', '--inc_verbose ' ,
                   my_timeout, fname]
            analyzed.update({func:v})
            bash_script += ''.join(cmd_sc) + '\n'
            f_script.write(bash_script)
            p = sub.Popen(cmd, shell=False, stdout=sub.PIPE, stderr=sub.STDOUT)
            result, _ = p.communicate()
            if verbose: print result
            func_res = ""
            debug_info = {}
            for r in result.split('\n'):
                if 'INC_STAT' in r:
                    func_res += r + "\n"
                if 'DINFO' in r:
                    tmp = r.split(":")
                    debug_info.update({tmp[1].strip():tmp[2]})
            res, incs, rounds, query = "", "","",""
            tmp_split = func_res.split("\n")
            try:
                res = (tmp_split[0]).split('|')[2]
                incs = (tmp_split[2]).split('|')[2]
                rounds = (tmp_split[3]).split('|')[2]
                query = (tmp_split[4]).split('|')[2]
            except Exception as e:
                print 'WARNING: wrong format \n' + func_res
            line_numbers = getLines(debug_info, incs)
            new_result = func + " , " + v['blks'] + " , " + res + " , " + line_numbers + " , " + rounds + " , " + query + "\n"
            all_result += new_result
            print new_result
            f_result.write(new_result)
    f_result.close()
    print 'Analyzed functions ... ' + str(len(analyzed))
    return

def getLines (lines_dict, incs):
    if incs == "": return "--"
    inc_lines = incs.split(";")
    line = ""
    for i in inc_lines:
        try:
            tmp = '-'.join([x.strip() for x in list((set((lines_dict[i]).split("|"))))])
            line += tmp
        except:
            continue
    return line

def main (argv):
    (opt, args) = parseOpt (argv)
    workdir = createWorkDir (opt.temp_dir, opt.save_temps)
    returnvalue = 0
    fname = args[1]
    finfo = opt.finfo
    num_blks = opt.num_blks
    timeout= opt.timeout
    global verbose
    verbose = opt.verbose
    run(workdir, fname, finfo, num_blks, opt)
    return returnvalue


if __name__ == '__main__':
    res = None
    try:
        res = main (sys.argv)
    except Exception as e:
        str(e)
        f_result.close()
    except KeyboardInterrupt:
        f_result.close()
    finally:
        print '\nDONE ...'
    sys.exit (res)
