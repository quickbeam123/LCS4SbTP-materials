import os
import subprocess
import argparse
import tempfile
import shutil
import shlex
import sys
import datetime

if sys.version_info < (3,0,0):
    raise Exception("User error: This application does not support Python 2. You probably need to use python3 instead of python.")
if sys.version_info < (3,6,0):
    raise Exception("User error: This application requires Python 3.6 or higher!")


########################################################
# GENERATING BENCHMARKS
########################################################

# run rapid on 'filename' in directory 'example_dir/subdir', and save resulting conjectures in out_dir
def process(rapid_exec, example_dir, subdir, filename, out_dir, rapidArgs, generateConjectures):
	assert(filename.endswith(".spec")), "Wrong file ending, needs to be .spec!"

	print("processing benchmark " + filename[:-5])
	numberOfReasoningTasks = 0

	with tempfile.TemporaryDirectory() as temp_dir_name:

		example_file_path = os.path.join(example_dir, subdir, filename)
		assert(os.path.exists(example_file_path)), (example_file_path + " doesn't exist!")

		# run rapid on example_file_path and create resulting files in the temporary directory
		call_string = rapid_exec + " -dir " + temp_dir_name + "/" + " " + rapidArgs + " " + example_file_path
		subprocess.run(shlex.split(call_string), stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

		# copy each resulting user-conjecture into out_dir
		with os.scandir(temp_dir_name) as entries:
			for entry in entries:
					if entry.is_file():
						if generateConjectures:
							if entry.name.startswith("user-conjecture-"):
								new_file_path = out_dir + "/" + filename[:-5] + "-" + entry.name[16:]
								shutil.copyfile(temp_dir_name + "/" + entry.name, new_file_path)
								numberOfReasoningTasks = numberOfReasoningTasks + 1
						else:
							if not entry.name.startswith("user-conjecture-"):
								new_file_path = out_dir + "/" + filename[:-5] + "-" + entry.name
								shutil.copyfile(temp_dir_name + "/" + entry.name, new_file_path)
								numberOfReasoningTasks = numberOfReasoningTasks + 1

	return numberOfReasoningTasks

def generateBenchmarks(rapid_exec, rapid_args, example_dir, out_dir, generateConjectures):
	print("\n================================================================")
	print("RAPID: Generating benchmarks")
	print("RAPID: input directory: " + example_dir)
	print("RAPID: output directory: " + out_dir)
	print("RAPID: rapid arguments: " + rapid_args)
	print("================================================================")
	numberOfReasoningTasks = 0

	# test each file in example_dir(recursively)
	for root, _, filenames in os.walk(example_dir):
		print("\nRAPID: Scanning folder " + root)

		subdir = os.path.relpath(root, example_dir)
		for filename in sorted(filenames):
			if filename == ".DS_Store":
				continue

			numberOfNewReasoningTasks = process(rapid_exec, example_dir, subdir, filename, out_dir, rapid_args, generateConjectures)
			numberOfReasoningTasks = numberOfReasoningTasks + numberOfNewReasoningTasks

	print("RAPID: Generated " + str(numberOfReasoningTasks) + " benchmarks")


########################################################
# CUSTOM PORTFOLIO MODE
########################################################
def printPortfolioStats(user_options_list, timeout, numberOfBenchmarks):
	secondsPerExample = len(user_options_list) * timeout
	overallSeconds = secondsPerExample * numberOfBenchmarks
	print("Will run " + str(len(user_options_list)) + " configurations, with a timeout of " + str(timeout) + " seconds.")
	print("Expected duration per benchmark: " + str(datetime.timedelta(seconds=secondsPerExample)))
	print("Number of benchmarks: " + str(numberOfBenchmarks))
	print("Overall expected duration: " + str(datetime.timedelta(seconds=overallSeconds)))

# def getPortfolioConfigurationsAll(timeout):
# 	user_options_list = []

# 	for av in ["off", "on"]:
# 		for sa in ["lrs", "discount"]:
# 			for urr in ["on", "off"]:
# 				for bsd in ["off", "on"]:
# 					for bs in ["off", "on"]:
# 						for bsr in ["off", "on"]:
# 							for fsd in ["off", "on"]:
# 								for s in ["10", "11", "1010", "1011"]:
# 									if av == "off" and urr == "on":
# 										for thsq_args in ["-thsqd 7 -thsqc 0,7 -thsqr 20,10,1 ", "-thsqd 6 -thsqc 0,6,18 ", "-thsqd 7 -thsqc 0,7,21 ", "-thsqd 8 -thsqc 0,8,24 "]:
# 											for lls in ["on", "off"]:
# 												user_options_list.append("--input_syntax smtlib2 -nwc 2 --newcnf on -thsq on -sa " + sa + " -t " + str(timeout) + " " + thsq_args + " -av " + av + " -bs " + bs + " -bsr " + bsr + " -fsd " + fsd + " -bsd " + bsd + " -s " + s + " -urr " + urr + " -lls " + lls + " ")
# 									if av == "on": 
# 										for thsq_args in ["-thsqd 20 -thsqc 0,20,60 ", "-thsqd 28 -thsqc 0,28,84 "]:
# 											for lls in ["on", "off"]:
# 												user_options_list.append("--input_syntax smtlib2 -nwc 2 --newcnf on -thsq on -sa " + sa + " -t " + str(timeout) + " " + thsq_args + " -av " + av + " -bs " + bs + " -bsr " + bsr + " -fsd " + fsd + " -bsd " + bsd + " -s " + s + " -urr " + urr + " -lls " + lls + " ")

# 	return user_options_list

def getPortfolioConfigurationsSmallNoAvatar(timeout):
	user_options_list = []

	for av in ["off"]:
		for sa in ["lrs"]:
			# for lls in ["on", "off"]:
			for lls in ["on"]:
				# for urr in ["on", "off"]:
				for urr in ["on"]:
					# for fsd in ["on", "off"]:
					for fsd in ["on"]:
						# for bsd in ["on", "off"]:
						for bsd in ["on"]:
							for tha in ["some", "on"]:
								for s in ["1010", "10", "1011", "11"]:
								# for s in ["1010", "1011"]:
									thsq_configs = [
										[
											("-thsqd", "6"),
											("-thsqc", "0,6"),
											("-thsqr", "20,10,1")
										],
										[
											("-thsqd", "7"),
											("-thsqc", "0,7"),
											("-thsqr", "20,10,1")
										],
										[
											("-thsqd", "8"),
											("-thsqc", "0,8"),
											("-thsqr", "20,10,1")
										],
										[
											("-thsqd", "9"),
											("-thsqc", "0,9"),
											("-thsqr", "20,10,1")
										],
										[
											("-thsqd", "6"),
											("-thsqc", "0,6,18"),
											("-thsqr", "20,10,10,1")
										],
										[
											("-thsqd", "7"),
											("-thsqc", "0,7,21"),
											("-thsqr", "20,10,10,1")
										],
										[
											("-thsqd", "8"),
											("-thsqc", "0,8,24"),
											("-thsqr", "20,10,10,1")
										]
									]
									for thsq_args in thsq_configs:
										if fsd == bsd:
											user_options = [
												("--input_syntax", "smtlib2"),
												("-nwc", "2"),
												("--newcnf", "on"),
												("-thsq", "on"),
												("-bs", "on"),
												("-bsr", "on"),
												("-av", av),
												("-sa", sa),
												("-urr", urr),
												("-lls", lls),
												("-t", str(timeout)),
												("-fsd", fsd),
												("-bsd", bsd),
												("-s", s),
												("-tha", tha)
											]
											user_options.extend(thsq_args)
											user_options_list.append(user_options)

	return user_options_list

def getPortfolioConfigurationsTinyNoAvatar(timeout):
	user_options_list = []

	for av in ["off"]:
		for sa in ["lrs", "discount"]:
			for lls in ["on"]:
				for urr in ["on"]:
					for fsd in ["on"]:
						for bsd in ["on"]:
							for tha in ["on", "some"]:
								for s in ["1010", "10"]:
									thsq_configs = [
										[
											("-thsqd", "8"),
											("-thsqc", "0,8"),
											("-thsqr", "20,10,1")
										],
										[
											("-thsqd", "8"),
											("-thsqc", "0,8,16,24"),
											("-thsqr", "20,10,10,10,1")
										],
										[
											("-thsqd", "4"),
											("-thsqc", "0,4"),
											("-thsqr", "20,10,1")
										],
										[
											("-thsqd", "4"),
											("-thsqc", "0,4,8,12"),
											("-thsqr", "20,10,10,10,1")
										]
									]
									for thsq_args in thsq_configs:
										if fsd == bsd:
											user_options = [
												("--input_syntax", "smtlib2"),
												("-nwc", "2"),
												("--newcnf", "on"),
												("-thsq", "on"),
												("-bs", "on"),
												("-bsr", "on"),
												("-av", av),
												("-sa", sa),
												("-urr", urr),
												("-lls", lls),
												("-t", str(timeout)),
												("-fsd", fsd),
												("-bsd", bsd),
												("-s", s),
												("-tha", tha)
											]
											user_options.extend(thsq_args)
											if sa == "discount":
												user_options.append(("-awr", "1:10"))
											user_options_list.append(user_options)

	return user_options_list


def getPortfolioConfigurationsSLSQ(timeout):
	user_options_list = []

	for av in ["off"]:
		for sa in ["lrs"]:
			for lls in ["on"]:
				for urr in ["on"]:
					for fsd in ["on"]:
						for bsd in ["on"]:
							for tha in ["on"]:
								for s in ["1010"]:
									thsq_configs = [
										[
											("-thsqd", "8"),
											("-thsqc", "0,8"),
											("-thsqr", "20,10,1")
										],
										[
											("-thsqd", "8"),
											("-thsqc", "0,8,16,24"),
											("-thsqr", "20,10,10,10,1")
										],
										[
											("-thsqd", "4"),
											("-thsqc", "0,4"),
											("-thsqr", "20,10,1")
										],
										[
											("-thsqd", "4"),
											("-thsqc", "0,4,8,12"),
											("-thsqr", "20,10,10,10,1")
										]
									]
									slsq_configs = [
										[
											("-slsq", "on"),
											("-slsqc", "0"),
											("-slsqr", "30,1")
										],
										[
											("-slsq", "on"),
											("-slsqc", "0"),
											("-slsqr", "50,1")
										],
										[
											("-slsq", "off")
										],
										[
											("-slsq", "on"),
											("-slsqc", "0"),
											("-slsqr", "1,1")
										],
										[
											("-slsq", "on"),
											("-slsqc", "0"),
											("-slsqr", "10,1")
										],
									]
									for thsq_args in thsq_configs:
										for slsq_args in slsq_configs:
											user_options = [
												("--input_syntax", "smtlib2"),
												("-nwc", "2"),
												("--newcnf", "on"),
												("-thsq", "on"),
												("-bs", "on"),
												("-bsr", "on"),
												("-av", av),
												("-sa", sa),
												("-urr", urr),
												("-lls", lls),
												("-t", str(timeout)),
												("-fsd", fsd),
												("-bsd", bsd),
												("-s", s),
												("-tha", tha)
											]
											user_options.extend(thsq_args)
											user_options.extend(slsq_args)
											user_options_list.append(user_options)

	return user_options_list

def getPortfolioConfigurationsPLSQ(timeout):
	return getPortfolioConfigurationsRapid(timeout)

def getPortfolioConfigurationsRapid(timeout):
	user_options_list = []
	for vtimeout in ["1", "10", str(timeout)]:
		for av in ["off"]:
			for sa in ["lrs"]:
				for lls in ["on"]:
					for urr in ["on"]:
						for fsd in ["on"]:
							for bsd in ["on"]:
								for tha in ["on"]:
									for s in ["1010"]:
										thsq_configs = [
											[
												("-thsqd", "8"),
												("-thsqc", "0,8"),
												("-thsqr", "20,10,1")
											],
											[
												("-thsqd", "8"),
												("-thsqc", "0,8,16,24"),
												("-thsqr", "20,10,10,10,1")
											]
										]
										slsq_configs = [
											[
												("-slsq", "on"),
												("-slsqc", "0"),
												("-slsqr", "30,1")
											],
											[
												("-slsq", "off")
											],
											[
												("-slsq", "on"),
												("-slsqc", "0"),
												("-slsqr", "1,1")
											],
										]
										plsq_configs = [
											[
												("-plsq", "on"),
												("-plsqc", "1,2"),
												("-plsqr", "5,5,1")
											],
											[
												("-plsq", "on"),
												("-plsqc", "1,2"),
												("-plsqr", "10,10,1")
											],
											[
												("-plsq", "on"),
												("-plsqc", "1,2"),
												("-plsqr", "20,20,1")
											],
											[
												("-plsq", "on"),
												("-plsqc", "1,2"),
												("-plsqr", "1,1,1")
											],
											[
												("-plsq", "off")
											],
										]
										for thsq_args in thsq_configs:
											for slsq_args in slsq_configs:
												for plsq_args in plsq_configs:
													user_options = [
														("--input_syntax", "smtlib2"),
														("-nwc", "2"),
														("--newcnf", "on"),
														("-thsq", "on"),
														("-bs", "on"),
														("-bsr", "on"),
														("-av", av),
														("-sa", sa),
														("-urr", urr),
														("-lls", lls),
														("-t", vtimeout),
														("-fsd", fsd),
														("-bsd", bsd),
														("-s", s),
														("-tha", tha)
													]
													user_options.extend(thsq_args)
													user_options.extend(slsq_args)
													user_options.extend(plsq_args)
													user_options_list.append(user_options)

	return user_options_list

def getPortfolioConfigurationsRapidNoLayeredCS(timeout):
	user_options_list = []
	for vtimeout in ["1", "10", str(timeout)]:
		for av in ["off"]:
			for sa in ["lrs"]:
				for lls in ["on"]:
					for urr in ["on"]:
						for fsd in ["on"]:
							for bsd in ["on"]:
								for tha in ["on"]:
									for s in ["1010"]:
										user_options = [
											("--input_syntax", "smtlib2"),
											("-nwc", "2"),
											("--newcnf", "on"),
											("-thsq", "off"),
											("-slsq", "off"),
											("-avsq", "off"),
											("-plsq", "off"),
											("-bs", "on"),
											("-bsr", "on"),
											("-av", av),
											("-sa", sa),
											("-urr", urr),
											("-lls", lls),
											("-t", vtimeout),
											("-fsd", fsd),
											("-bsd", bsd),
											("-s", s),
											("-tha", tha)
										]
										user_options_list.append(user_options)

	return user_options_list

def getPortfolioConfigurationsRapidNoLayeredCSNoSD(timeout):
	user_options_list = []
	for vtimeout in ["1", "10", str(timeout)]:
		for av in ["off"]:
			for sa in ["lrs"]:
				for lls in ["on"]:
					for urr in ["on"]:
						for fsd in ["off"]:
							for bsd in ["off"]:
								for tha in ["on"]:
									for s in ["1010"]:
										user_options = [
											("--input_syntax", "smtlib2"),
											("-nwc", "2"),
											("--newcnf", "on"),
											("-thsq", "off"),
											("-slsq", "off"),
											("-avsq", "off"),
											("-plsq", "off"),
											("-bs", "on"),
											("-bsr", "on"),
											("-av", av),
											("-sa", sa),
											("-urr", urr),
											("-lls", lls),
											("-t", vtimeout),
											("-fsd", fsd),
											("-bsd", bsd),
											("-s", s),
											("-tha", tha)
										]
										user_options_list.append(user_options)

	return user_options_list


def getPortfolioConfigurationsPLSQEq1(timeout):
	user_options_list = []
	for vtimeout in ["1", "10", str(timeout)]:
		for av in ["off"]:
			for sa in ["lrs"]:
				for lls in ["on"]:
					for urr in ["on"]:
						for fsd in ["on"]:
							for bsd in ["on"]:
								for tha in ["on"]:
									for s in ["10"]:
										thsq_configs = [
											[
												("-thsqd", "8"),
												("-thsqc", "0,8"),
												("-thsqr", "20,10,1")
											],
											[
												("-thsqd", "8"),
												("-thsqc", "0,8,16,24"),
												("-thsqr", "20,10,10,10,1")
											]
										]
										slsq_configs = [
											[
												("-slsq", "on"),
												("-slsqc", "0"),
												("-slsqr", "30,1")
											],
											[
												("-slsq", "off")
											],
											[
												("-slsq", "on"),
												("-slsqc", "0"),
												("-slsqr", "1,1")
											],
										]
										plsq_configs = [
											[
												("-plsq", "on"),
												("-plsqc", "1,2"),
												("-plsqr", "5,5,1")
											],
											[
												("-plsq", "on"),
												("-plsqc", "1,2"),
												("-plsqr", "10,10,1")
											],
											[
												("-plsq", "on"),
												("-plsqc", "1,2"),
												("-plsqr", "20,20,1")
											],
											[
												("-plsq", "on"),
												("-plsqc", "1,2"),
												("-plsqr", "1,1,1")
											],
											[
												("-plsq", "off")
											],
										]
										for thsq_args in thsq_configs:
											for slsq_args in slsq_configs:
												for plsq_args in plsq_configs:
													user_options = [
														("--input_syntax", "smtlib2"),
														("-nwc", "2"),
														("--newcnf", "on"),
														("-thsq", "on"),
														("-bs", "on"),
														("-bsr", "on"),
														("-av", av),
														("-sa", sa),
														("-urr", urr),
														("-lls", lls),
														("-t", vtimeout),
														("-fsd", fsd),
														("-bsd", bsd),
														("-s", s),
														("-tha", tha),
														("-lma", "on")
													]
													user_options.extend(thsq_args)
													user_options.extend(slsq_args)
													user_options.extend(plsq_args)
													user_options_list.append(user_options)

	return user_options_list

def getPortfolioConfigurationsPLSQRelational(timeout):
	user_options_list = []
	for vtimeout in ["1", "10", str(timeout)]:
		for av in ["off"]:
			for sa in ["lrs"]:
				for lls in ["on"]:
					for urr in ["on"]:
						for fsd in ["on"]:
							for bsd in ["on"]:
								for tha in ["on"]:
									for s in ["1010", "10"]:
										thsq_configs = [
											[
												("-thsqd", "8"),
												("-thsqc", "0,8"),
												("-thsqr", "20,10,1")
											],
											[
												("-thsqd", "8"),
												("-thsqc", "0,8,16,24"),
												("-thsqr", "20,10,10,10,1")
											]
										]
										slsq_configs = [
											[
												("-slsq", "on"),
												("-slsqc", "0"),
												("-slsqr", "30,1")
											],
											[
												("-slsq", "off")
											],
											[
												("-slsq", "on"),
												("-slsqc", "0"),
												("-slsqr", "1,1")
											],
										]
										plsq_configs = [
											[
												("-plsq", "on"),
												("-plsqc", "1,2"),
												("-plsqr", "5,5,1")
											],
											[
												("-plsq", "on"),
												("-plsqc", "1,2"),
												("-plsqr", "10,10,1")
											],
											[
												("-plsq", "on"),
												("-plsqc", "1,2"),
												("-plsqr", "20,20,1")
											],
											[
												("-plsq", "on"),
												("-plsqc", "1,2"),
												("-plsqr", "1,1,1")
											],
											[
												("-plsq", "off")
											],
										]
										for thsq_args in thsq_configs:
											for slsq_args in slsq_configs:
												for plsq_args in plsq_configs:
													user_options = [
														("--input_syntax", "smtlib2"),
														("-nwc", "2"),
														("--newcnf", "on"),
														("-thsq", "on"),
														("-bs", "on"),
														("-bsr", "on"),
														("-av", av),
														("-sa", sa),
														("-urr", urr),
														("-lls", lls),
														("-t", vtimeout),
														("-fsd", fsd),
														("-bsd", bsd),
														("-s", s),
														("-tha", tha)
													]
													user_options.extend(thsq_args)
													user_options.extend(slsq_args)
													user_options.extend(plsq_args)
													user_options_list.append(user_options)

	return user_options_list

def getPortfolioConfigurationsExp(timeout):
	user_options_list = []

	for av in ["off"]:
		for sa in ["lrs"]:
			for lls in ["on"]:
				for s in ["1010", "10"]:
					for fsd in ["on"]:
						for bsd in ["on"]:
							for tha in ["on"]:
								for urr in ["on", "off"]:
									thsq_configs = [
										[
											("-thsqd", "8"),
											("-thsqc", "0,8"),
											("-thsqr", "20,10,1")
										],
										[
											("-thsqd", "8"),
											("-thsqc", "0,8,16,24"),
											("-thsqr", "20,10,10,10,1")
										]
									]
									slsq_configs = [
										[
											("-slsq", "on"),
											("-slsqc", "0"),
											("-slsqr", "30,1")
										],
										[
											("-slsq", "off")
										],
										[
											("-slsq", "on"),
											("-slsqc", "0"),
											("-slsqr", "1,1")
										]
									]
									plsq_configs = [
										[
											("-plsq", "on"),
											("-plsqc", "1,2"),
											("-plsqr", "5,5,1")
										],
										[
											("-plsq", "on"),
											("-plsqc", "1,2"),
											("-plsqr", "10,10,1")
										],
										[
											("-plsq", "on"),
											("-plsqc", "1,2"),
											("-plsqr", "20,20,1")
										],
										[
											("-plsq", "on"),
											("-plsqc", "1,2,3"),
											("-plsqr", "5,5,5,1")
										],
										[
											("-plsq", "on"),
											("-plsqc", "1,2"),
											("-plsqr", "1,1,1")
										],
										[
											("-plsq", "off")
										],
									]
									for thsq_args in thsq_configs:
										for slsq_args in slsq_configs:
											for plsq_args in plsq_configs:
												user_options = [
													("--input_syntax", "smtlib2"),
													("-nwc", "2"),
													("--newcnf", "on"),
													("-thsq", "on"),
													("-bs", "on"),
													("-bsr", "on"),
													("-av", av),
													("-sa", sa),
													("-urr", urr),
													("-lls", lls),
													("-t", str(timeout)),
													("-fsd", fsd),
													("-bsd", bsd),
													("-s", s),
													("-tha", tha)
												]
												user_options.extend(thsq_args)
												user_options.extend(slsq_args)
												user_options.extend(plsq_args)
												user_options_list.append(user_options)

	return user_options_list

def getPortfolioConfigurationsLemmas(timeout):
	user_options_list = []

	for av in ["off"]:
		for sa in ["lrs"]:
			for lls in ["on"]:
				for urr in ["on"]:
					for fsd in ["on"]:
						for bsd in ["on"]:
							for tha in ["on"]:
								for s in ["10", "1010"]:
									thsq_configs = [
										[
											("-thsqd", "8"),
											("-thsqc", "0,8,16,24"),
											("-thsqr", "20,10,10,10,1")
										],
										[
											("-thsqd", "8"),
											("-thsqc", "0,8"),
											("-thsqr", "20,10,1")
										],
										[
											("-thsqd", "4"),
											("-thsqc", "0,4"),
											("-thsqr", "20,10,1")
										],
										[
											("-thsqd", "4"),
											("-thsqc", "0,4,8,12"),
											("-thsqr", "20,10,10,10,1")
										]
									]
									slsq_configs = [
										[
											("-slsq", "off")
										],
										[
											("-slsq", "on"),
											("-slsqc", "0"),
											("-slsqr", "50,1")
										],
										[
											("-slsq", "on"),
											("-slsqc", "0"),
											("-slsqr", "1,1")
										],
										[
											("-slsq", "on"),
											("-slsqc", "0"),
											("-slsqr", "10,1")
										],
										[
											("-slsq", "on"),
											("-slsqc", "0"),
											("-slsqr", "30,1")
										],
									]
									for thsq_args in thsq_configs:
										for slsq_args in slsq_configs:
											user_options = [
												("--input_syntax", "smtlib2"),
												("-nwc", "2"),
												("--newcnf", "on"),
												("-thsq", "on"),
												("-bs", "on"),
												("-bsr", "on"),
												("-av", av),
												("-sa", sa),
												("-urr", urr),
												("-lls", lls),
												("-t", str(timeout)),
												("-fsd", fsd),
												("-bsd", bsd),
												("-s", s),
												("-tha", tha)
											]
											user_options.extend(thsq_args)
											user_options.extend(slsq_args)
											user_options_list.append(user_options)

	return user_options_list

def getPortfolioConfigurationsAvatar(timeout):
	user_options_list = []

	for av in ["on"]:
		for sa in ["lrs", "discount"]:
			for lls in ["on"]:
				for urr in ["on", "off"]:
					for bs in ["on", "off"]:
						for bsr in ["on", "off"]:
							for fsd in ["on", "off"]:
								for bsd in ["on", "off"]:
									for tha in ["on", "some"]:
										for s in ["1010", "10", "11", "1011"]:
											for sas in ["minisat", "z3"]:
												thsq_configs = [
													[
														("-thsqd", "8"),
														("-thsqc", "0,8"),
														("-thsqr", "20,10,1")
													],
													[
														("-thsqd", "8"),
														("-thsqc", "0,8,16,24"),
														("-thsqr", "20,10,10,10,1")
													],
													[
														("-thsqd", "4"),
														("-thsqc", "0,4"),
														("-thsqr", "20,10,1")
													],
													[
														("-thsqd", "4"),
														("-thsqc", "0,4,8,12"),
														("-thsqr", "20,10,10,10,1")
													],
													[
														("-thsqd", "16"),
														("-thsqc", "0,16"),
														("-thsqr", "20,10,1")
													],
													[
														("-thsqd", "16"),
														("-thsqc", "0,16,32"),
														("-thsqr", "20,10,10,1")
													],
													[
														("-thsqd", "16"),
														("-thsqc", "0,16,32,38"),
														("-thsqr", "20,10,10,10,1")
													],
													[
														("-thsqd", "20"),
														("-thsqc", "0,20"),
														("-thsqr", "20,10,1")
													],
													[
														("-thsqd", "20"),
														("-thsqc", "0,20,40"),
														("-thsqr", "20,10,10,1")
													],
													[
														("-thsqd", "20"),
														("-thsqc", "0,20,40,60"),
														("-thsqr", "20,10,10,10,1")
													],
													[
														("-thsqd", "28"),
														("-thsqc", "0,28"),
														("-thsqr", "20,10,1")
													],
													[
														("-thsqd", "28"),
														("-thsqc", "0,28,56"),
														("-thsqr", "20,10,10,1")
													],
													[
														("-thsqd", "28"),
														("-thsqc", "0,28,56,84"),
														("-thsqr", "20,10,10,10,1")
													]
												]
												for thsq_args in thsq_configs:
													if fsd == bsd:
														if bs == bsr:
															user_options = [
																("--input_syntax", "smtlib2"),
																("-nwc", "2"),
																("--newcnf", "on"),
																("-thsq", "on"),
																("-bs", bs),
																("-bsr", bsr),
																("-av", av),
																("-sa", sa),
																("-urr", urr),
																("-lls", lls),
																("-t", str(timeout)),
																("-fsd", fsd),
																("-bsd", bsd),
																("-s", s),
																("-tha", tha),
																("-sas", sas)
															]
															user_options.extend(thsq_args)
															if sa == "discount":
																user_options.append(("-awr", "1:10"))
															user_options_list.append(user_options)

	return user_options_list


def getPortfolioConfigurationsAvatarSmall(timeout):
	user_options_list = []

	for av in ["on"]:
		for lls in ["on"]:
			for bs in ["on"]:
				for bsr in ["on"]:
					for fsd in ["on"]:
						for bsd in ["on"]:
							for urr in ["on"]:
								for tha in ["on"]:
									for sa in ["lrs"]:
										for s in ["1010"]:
											for sas in ["z3"]:
												for gs in ["off","on"]:
													thsq_configs = [
														# [
														# 	("-thsqd", "16"),
														# 	("-thsqc", "0,16"),
														# 	("-thsqr", "20,10,1")
														# ],
														# [
														# 	("-thsqd", "16"),
														# 	("-thsqc", "0,16,32"),
														# 	("-thsqr", "20,10,10,1")
														# ],
														# [
														# 	("-thsqd", "16"),
														# 	("-thsqc", "0,16,32,48"),
														# 	("-thsqr", "20,10,10,10,1")
														# ],
														[
															("-thsqd", "18"),
															("-thsqc", "0,18"),
															("-thsqr", "20,10,1")
														],
														[
															("-thsqd", "18"),
															("-thsqc", "0,18,36"),
															("-thsqr", "20,10,10,1")
														],
														[
															("-thsqd", "18"),
															("-thsqc", "0,18,36,54"),
															("-thsqr", "20,10,10,10,1")
														],
														# [
														# 	("-thsqd", "20"),
														# 	("-thsqc", "0,20"),
														# 	("-thsqr", "20,10,1")
														# ],
														# [
														# 	("-thsqd", "20"),
														# 	("-thsqc", "0,20,40"),
														# 	("-thsqr", "20,10,10,1")
														# ],
														# [
														# 	("-thsqd", "20"),
														# 	("-thsqc", "0,20,40,60"),
														# 	("-thsqr", "20,10,10,10,1")
														# ],
														[
															("-thsqd", "24"),
															("-thsqc", "0,24"),
															("-thsqr", "20,10,1")
														],
														[
															("-thsqd", "24"),
															("-thsqc", "0,24,48"),
															("-thsqr", "20,10,10,1")
														],
														[
															("-thsqd", "24"),
															("-thsqc", "0,24,48,72"),
															("-thsqr", "20,10,10,10,1")
														]
													]
													for thsq_args in thsq_configs:
														if fsd == bsd:
															if bs == bsr:
																user_options = [
																	("--input_syntax", "smtlib2"),
																	("-nwc", "2"),
																	("--newcnf", "on"),
																	("-thsq", "on"),
																	("-bs", bs),
																	("-bsr", bsr),
																	("-av", av),
																	("-sa", sa),
																	("-urr", urr),
																	("-lls", lls),
																	("-t", str(timeout)),
																	("-fsd", fsd),
																	("-bsd", bsd),
																	("-s", s),
																	("-tha", tha),
																	("-sas", sas),
																	("-gs", gs)
																]
																user_options.extend(thsq_args)
																if sa == "discount":
																	user_options.append(("-awr", "1:10"))
																user_options_list.append(user_options)

	return user_options_list



def testDiscott(timeout):
	user_options_list = []
	for vtimeout in ["3"]:
		for av in ["off"]:
			for lls in ["on"]:
				for urr in ["on"]:
					for fsd in ["on"]:
						for bsd in ["on"]:
							for tha in ["on"]:
								for s in ["10", "1010"]:
									thsq_configs = [
										[
											("-thsqd", "8"),
											("-thsqc", "0,8"),
											("-thsqr", "20,10,1")
										],
										[
											("-thsqd", "8"),
											("-thsqc", "0,8,16,24"),
											("-thsqr", "20,10,10,10,1")
										]
									]
									slsq_configs = [
										[
											("-slsq", "on"),
											("-slsqc", "0"),
											("-slsqr", "30,1")
										],
										[
											("-slsq", "off")
										],
										[
											("-slsq", "on"),
											("-slsqc", "0"),
											("-slsqr", "1,1")
										],
									]
									plsq_configs = [
										[
											("-plsq", "on"),
											("-plsqc", "1,2"),
											("-plsqr", "5,5,1")
										],
										[
											("-plsq", "on"),
											("-plsqc", "1,2"),
											("-plsqr", "20,20,1")
										],
										[
											("-plsq", "on"),
											("-plsqc", "1,2"),
											("-plsqr", "1,1,1")
										],
									]
									for thsq_args in thsq_configs:
										for slsq_args in slsq_configs:
											for plsq_args in plsq_configs:
												for sa in ["discott"]:
													for awr in ["1:1", "3:4", "2:3", "1:2","1:3","1:5","1:10"]:
													# for sa in ["discott","lrs", "discount"]:
														user_options = [
															("--input_syntax", "smtlib2"),
															("-nwc", "2"),
															("--newcnf", "on"),
															("-thsq", "on"),
															("-bs", "on"),
															("-bsr", "on"),
															("-av", av),
															("-sa", sa),
															("-urr", urr),
															("-lls", lls),
															("-t", vtimeout),
															("-fsd", fsd),
															("-bsd", bsd),
															("-s", s),
															("-tha", tha),
															("-awr", awr)
														]
														user_options.extend(thsq_args)
														user_options.extend(slsq_args)
														user_options.extend(plsq_args)
														user_options_list.append(user_options)

	return user_options_list
