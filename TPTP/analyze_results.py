#!/usr/bin/env python2

import sys, os

import subprocess, time, signal

import cPickle as pickle
import gzip
import math, random
from collections import defaultdict

def normalize_names(dict):
  res = {}
  for name,val in dict.items():
    if name.startswith("./"):
      name = name[2:]
    elif name.startswith("/"):
      name = name[1:]
    res[name] = val
  return res

if __name__ == "__main__":

  hist = defaultdict(int) # how many times has this benchmark been solved?
  
  confs = [] # to have solvers in order
  
  results = {} # conf -> (bechmarm -> time)
  solveds = {} # conf -> set_of_solved
  
  '''
  with open("/nfs/sudamar2/TPTP-v7.3.0/probinfo7.3.0.pkl",'rb') as f:
    probinfo = pickle.load(f)
  '''

  for filename in sys.argv[1:]:
    with open(filename,'rb') as f:
      confs.append(filename)
      result = normalize_names(pickle.load(f))
      results[filename] = result
      solveds[filename] = set([bench.split("/")[-1] for bench in result]) # just the short TPTP names
      for benchmark in result:
        hist[benchmark] += 1

  '''
  stras_with_scores = []
  for strat, solved in solveds.iteritems():
    score = sum([1.0/hist[benchmark] for benchmark in solved])
    stras_with_scores.append((strat,len(solved),score))

  for strat, total, score in sorted(stras_with_scores,key = lambda x : x[2]):
    print strat, total, score
  '''
  '''
  masters = []
  subdems = []
  touches = []
  
  for name, result in results.items():
    if "master" in name:
      masters.append(set(result))
    if "subdem" in name:
      subdems.append(set(result))
    if "touches" in name:
      touches.append(set(result))

  print "masters_inter", len(set.intersection(*masters))
  print "subdems_inter", len(set.intersection(*subdems))
  print "touches_inter", len(set.intersection(*touches))

  print "all subdems and no master:"
  for benchmark in set.intersection(*subdems) - set.union(*masters):
    print benchmark,
    for name, result in results.items():
      if "subdem" in name:
        print result[benchmark],
    print
  print
  print
  '''

  '''
  base = results[confs[0]]
  other = results[confs[1]]

  base_total = 0.0
  other_total = 0.0
  common_cnt = 0

  base_under_3 = 0

  for benchmark in hist:
    if benchmark in base and base[benchmark] <= 3.0:
      base_under_3 += 1
    
  
    # print benchmark
    if benchmark in base and benchmark in other:
      common_cnt += 1
      base_total += base[benchmark]
      other_total += other[benchmark]

  print "common_cnt", common_cnt
  print "base_total", base_total
  print "other_total", other_total

  print
  print "base_under_3", base_under_3

  exit(0)
  '''
  
  '''
  base = results[confs[0]]
  other = results[confs[1]]

  base_minus_other = sorted([ (bench, time) for bench, time in base.items() if bench not in other ], key = lambda x : x[1])
  other_minus_base = sorted([ (bench, time) for bench, time in other.items() if bench not in base ], key = lambda x : x[1])

  print "base_minus_other"
  for bench, time in base_minus_other:
    print bench, time

  print
  print "other_minus_base"
  for bench, time in other_minus_base:
    print bench, time

  exit(0)
  '''

  # base = None # --> initilize by the first in table
  base = len(solveds[confs[0]]) # --> initilize by the first one read
  
  for conf, set_of_solved in sorted(solveds.items(),key = lambda x : len(x[1])):
    if base is None:
      base = len(set_of_solved)
    # rated_benches = sorted([(bench, probinfo[bench][0]) for bench in set_of_solved], key = lambda x : -x[1] )
    print conf, len(set_of_solved), len(set_of_solved) - base
    # print rated_benches[:5]
  
  '''
  base_val = None
  last_dashcount = 0
  for conf, set_of_solved in sorted(solveds.items(),key = lambda x : x[0].count("-")*10000 + len(x[1])):
    if base_val is None:
      base_val = len(set_of_solved)
    dashcount = conf.count("-")
    if dashcount > last_dashcount:
      last_dashcount = dashcount
      print
    print conf, len(set_of_solved), len(set_of_solved) - base_val, 100.0*(len(set_of_solved) - base_val) / base_val
  '''


  print 
  print "Greedy cover:"
  covered = set()
  while True:
    best_val = 0
    for strat, solved in solveds.iteritems():
      val = len(solved - covered)
      if val > best_val:
        best_val = val
        best_strat = strat
    if best_val > 0:
      best_solved = solveds[best_strat].copy()
      print best_strat, "contributes", best_val, "total", len(best_solved),
      for strat, solved in solveds.iteritems():
        if strat != best_strat:
          best_solved = best_solved - solved
      print "uniques", len(best_solved)
      covered = covered | solveds[best_strat]
    else:
      break
  print "Total", len(covered)



