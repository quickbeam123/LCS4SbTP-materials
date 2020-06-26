import os
import subprocess
import argparse
from timeit import default_timer as timer

import sqlite3
from datetime import datetime
import uuid
import sys
if sys.version_info < (3,0,0):
    raise Exception("User error: This application does not support Python 2. You probably need to use python3 instead of python.")
if sys.version_info < (3,6,0):
    raise Exception("User error: This application requires Python 3.6 or higher!")

def run_vampire(vampire_exec, inputFile, userOptions):

	args = [vampire_exec]
	for keyValuePair in userOptions:
		args.append(keyValuePair[0])
		args.append(keyValuePair[1])
	args.append(inputFile)

	output = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, universal_newlines=True).stdout
	lines = output.replace('\r\n', '\n').replace('\r', '\n').split('\n')

	for line in lines:
		if line.startswith("% Refutation found. Thanks to"): # TODO: use SZS status instead?
			return True
		# Note:
		# Vampire reports Satisfiable, if it saturates on a problem without conjecture
		# Vampire reports CounterSatisfiable, if it saturates on a problem with conjecture
		elif line.startswith("% SZS status Satisfiable") or line.startswith("% SZS status CounterSatisfiable"):
			print("Warning: Vampire saturated on " + " ".join(args))
			return False
		elif line.startswith("User error: "):
			print("Warning: User error on " + " ".join(args))
			return False
		elif line.startswith("% Termination reason: Refutation not found, non-redundant clauses discarded"):
			return False
		elif line.startswith("% Termination reason: Time limit"):
			return False
	print("Warning: Unknown error on " + " ".join(args))
	return False

def run_vampire_portfolio(vampire_exec, inputFile, userOptionsList, verbose, continueAfterSuccess, database, evaluationId=0):
	name = inputFile.split("/")[-1]
	if database != "":
		conn = sqlite3.connect(database)
		cursor = conn.cursor()
	if verbose:
		print("Evaluating benchmark: " + inputFile)

	successExists = False
	for userOptions in userOptionsList:
		userOptionToString = lambda userOption: str(userOption[0]) + " " + str(userOption[1])
		userOptionString = " ".join(map(userOptionToString, userOptions))

		start = timer()
		result = run_vampire(vampire_exec, inputFile, userOptions)
		timeNeeded = timer()-start

		if database != "":
			if result:
				cursor.execute("INSERT INTO run (evaluation_id, name, option_string, result, time) VALUES (?, ?, ?, ?, ?)", (evaluationId, name, userOptionString, "success", "{0:.2f}".format(timeNeeded) + "s") )
			else:
				cursor.execute("INSERT INTO run (evaluation_id, name, option_string, result) VALUES (?, ?, ?, ?)", (evaluationId, name, userOptionString, "failed"))
			runId = cursor.lastrowid
			for userOption in userOptions:
				cursor.execute("INSERT INTO options (run_id, key, value) VALUES (?, ?, ?)", (runId, str(userOption[0]), str(userOption[1])))
			conn.commit()

		if result:
			successExists = True
			if verbose:
				print("   Success (in " + "{0:.2f}".format(timeNeeded) + "s): " + userOptionString,flush=True)
			else:
				print("   Success (in " + "{0:.2f}".format(timeNeeded) + "s): " + inputFile,flush=True)
			if not continueAfterSuccess and not database != "":
				return True
		else:
			if verbose:
				print("   Failed: " + userOptionString,flush=True)

	if database != "":
		conn.commit()
		conn.close()
	if not successExists and not verbose:
		print("Failed: " + inputFile)

	return successExists

def run_vampire_portfolio_on_dir(vampire_exec, benchmark_dir, userOptionsList, verbose, database=""):
	evaluationId = 0
	if database != "":

		conn = sqlite3.connect(database)
		cursor = conn.cursor()
		nowString = datetime.now().strftime("%d/%m/%Y %H:%M:%S")
		cursor.execute("INSERT INTO evaluation (vampire_version, date) VALUES (?, ?)", (vampire_exec, nowString))
		evaluationId = cursor.lastrowid
		conn.commit()
		conn.close()
	successCounter = 0
	overallCounter = 0
	with os.scandir(benchmark_dir) as entries:
		for entry in sorted(entries, key=lambda e: e.name):
				if entry.is_file():
					if(not entry.name.startswith(".DS_Store")):
						file_path = benchmark_dir + "/" + entry.name
						result = run_vampire_portfolio(vampire_exec, file_path, userOptionsList, verbose, database != "", database, evaluationId)
						if result:
							successCounter = successCounter + 1
						overallCounter = overallCounter + 1
	print("\nOVERALL STATISTICS:\nSolved " + str(successCounter) + " out of " + str(overallCounter) + " benchmarks!\n")

