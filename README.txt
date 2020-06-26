These are supplementary files for reproducing experiments described in the paper 
Layered Clause Selection for Saturation-based Theorem Proving (B. Gleiss and M. Suda), PAAR 2020.

The repo is organised into three subfolders corresponding to the three benchmark sets (TPTP, SMTLIB, and RAPID for Experiment 4).
The structure of the TPTP and SMTLIB folders is similar (benchmarks are not present, since they are publicly available, 
but their list is provided; the vampire executable, which can be obtained via a public git repo, is also omitted).
The RAPID folder is different (the benchmarks are included and statically linked executable of a custom vampire branch is provided).
We describe the content of each of the three folders separately.

TPTP:
-----

- We used the version 7.3.0 of the library which is available from http://www.tptp.org/TPTP/Distribution/TPTP-v7.3.0.tgz
- The list of actually used problems can be found in the file problemsFOL.txt

- to obtain the version of Vampire used for these experiments checkout the commit

commit d016bfb2fd6f1972a96414a952c4b526e624c0d9
Author: Martin Suda <sudam@cs.man.ac.uk>
Date:   Tue May 26 14:56:29 2020 +0200

(on the master branch)

of git@github.com:vprover/vampire.git

- to compile that version of vampire use

make vampire_rel

in the top level directory using a recent version of a c++ compiler should give the executable

vampire_rel_detached_4343

- the following support scripts were used to run the experiment:

run_in_parallel_plus.sh
run_vampire10s.sh
filenamify_path.sh

- the top level command to run a single strategy over the TPTP library looks like

./run_in_parallel_plus.sh 30 problemsFOL.txt ./run_vampire10s.sh ./vampire_rel_detached_4343 "-sa discount -awr 10" <target_folder_for_the_logs>

where 30 is the number of parallel cores, and "-sa discount -awr 10" defines the base strategy

- to run a split heuristic with default ratio, cutoffs and mode, one can simply add "-thsq on", "-slsq on", "-avsq on", or "-plsq on"

- the options to change the ratio, cutoffs and mode, by an example, look like "-slsq on -slsqc 0,1 -slsqr 1,4,1 -slsql off"
where "-slsq on" turns on the split heuristic for sine levels, "-slsqc 0,1" spicifies the two non-trivial cutoff values, "-slsqr 1,4,1" the three values of the corresponding ratio,
and "-slsql off" stands for the disjoint mode of split ("-slsql on" would mean the monotone mode)

- After a strategy is run, the <target_folder_for_the_logs> must be scanned to extract the relevant information by calling

./scan_and_store_one.py problemsFOL.txt <target_folder_for_the_logs>

which creates a python pickle file <target_folder_for_the_logs>.pkl

- In the end, all the strategies can be compared by calling

./analyze_results.py *.pkl 

where *.pkl should be expanded by the shell to all the pkl files in the current directory.

- Analogous scrips ./scan_and_store_time.py and ./analyze_times.py were used to extract information about time spent in the split heuristic code 
as reported on in Experiment 2.

SMTLIB:
-------

- the file problemsSMTLIB.txt contains the list of selected problems
- these should be matched against a git repo checkout from 
  https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks,
  from the respective sub-logic sub-projects, 
  with commits not younger than January 2020.

- for an info on how to obtain vampire executable of the right version, see TPTP above

- the scripts to run the experiment work the same as those for TPTP

- to scan the <target_folder_for_the_logs> here, run

./scan_and_store_one.py problemsSMTLIB.txt <target_folder_for_the_logs>

which creates a python pickle file <target_folder_for_the_logs>.pkl

- As above, all the strategies can be compared by calling

./analyze_results.py *.pkl 

where *.pkl should be expanded by the shell to all the pkl files in the current directory.

RAPID:
------

- the corresponding folder contains all the data necessary to reproduce this experiment (Experiment 4 in the paper)
- the entry points are 
  "evaluate-rapid.py" for the "split-heuristics" run, and
  "evaluate-rapid-no-layered-cs.py" for the "aw" run (cf. Table 4 in the paper)

