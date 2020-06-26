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
  
  with open("/nfs/sudamar2/TPTP-v7.3.0/probinfo7.3.0.pkl",'rb') as f:
    probinfo = pickle.load(f)

  nonsolvedsets = []

  for filename in sys.argv[1:]:
    with open(filename,'rb') as f:
      confs.append(filename)
      result = normalize_names(pickle.load(f))
      results[filename] = result
      nonsolvedsets.append(set(result))

  intersect = set.intersection(*nonsolvedsets)

  sums = [0.0]*len(confs)

  for bench in intersect:
    for i,conf in enumerate(confs):
      sums[i] += results[conf][bench] if results[conf][bench] is not None else 0.0

  total = len(intersect)
  print total
  for conf,sum in zip(confs,sums):
    print conf, sum/total
