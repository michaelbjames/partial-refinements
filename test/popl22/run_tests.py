#!/usr/bin/python3

import os
import subprocess
from multiprocessing import Pool, Manager
import sys
import csv

'''
Run all benchmarks, collect results, output csv and tex files

TODO:
record time
record AST size
other stats?
output csv
output tex
write all output to a log
'''

RUN_SYNQUID = "stack run -- synquid"
DEFAULT_ARGS = ["-c=False"]

TIMEOUT_SEC = 15

BASE_TEST_PATH = "./test/intersection/intersection/"

DEFAULT_CSV_NAME = "benchmark_status.csv"

OLD_DIR = 'old_dir'
NEW_DIR = 'new_dir'
STATUS = 'status'

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

SUCCESS_STATUS = bcolors.OKGREEN + 'success' + bcolors.ENDC
TIMEOUT_STATUS = bcolors.WARNING + 'timeout' + bcolors.ENDC
FAILED_STATUS = bcolors.FAIL + 'failed' + bcolors.ENDC


FNULL = open(os.devnull, 'w')

class Benchmark:
    def __init__(self, name, description, components='', options=[]):
        self.name = name
        self.description = description
        self.components = components
        self.options = options
    
    def str(self):
        return f"{self.name}: {self.description} {str(self.options)}"

BENCHMARKS = [
    Benchmark("List-Inc", "increment list"),
    Benchmark("List-Sum", "sum list")
]

def run_file(filepath, args):
    cmd = " ".join([RUN_SYNQUID] + args + [filepath])
    print(cmd)
    try:
        subprocess.run(cmd, timeout=TIMEOUT_SEC,
            check=True, shell=True,
            stderr=FNULL, stdout=FNULL)
        return SUCCESS_STATUS
    except subprocess.TimeoutExpired as e:
        return TIMEOUT_STATUS
    except subprocess.CalledProcessError as e:
        return FAILED_STATUS

def sort_dir(original_dir, status):
    if status == SUCCESS_STATUS:
        if original_dir == SYNTH_DIR:
            return SYNTH_DIR
        else:
            return CHECKS_DIR
    if status == TIMEOUT_STATUS:
        print("timeout")
        return WIP_DIR
    if status == FAILED_STATUS:
        return FAILS_DIR

def is_synquid_file(filename):
    filename[-3:] == ".sq"


def worker(bench, return_dict):
    filename = bench.name
    filepath = filename + ".sq" # os.path.join(BASE_TEST_PATH, subdir, filename)
    status = run_file(filepath, bench.options)
    #new_dir = sort_dir(subdir, status)

    if return_dict is not None:
        return_dict[filename] = {
            # OLD_DIR: subdir,
            #NEW_DIR: new_dir,
            STATUS: status}

#def print_status(status):
#    for (filename, st) in status:
#        new_dir = st[NEW_DIR]
#        old_dir = st[OLD_DIR]
#        new_dir_str = new_dir
#        if new_dir == CHECKS_DIR:
#            new_dir_str = f"{bcolors.OKGREEN}{new_dir}"
#        if new_dir != old_dir:
#            print(f"{filename}: {bcolors.WARNING}{old_dir} -> {new_dir_str}{bcolors.ENDC}")
#        else:
#            print(f"{filename}: {old_dir} | No change.")

def print_results(status):
    for (filename, res) in status:
        s = res[STATUS]
        print(f"{filename}: {s}")


# def write_status_csv(statuses, filename):
#    with open(filename, 'w', newline='') as csvfile:
#        writer = csv.writer(csvfile, quoting=csv.QUOTE_MINIMAL)
#        writer.writerow(["Filename", "Status"])
#        for (filename, st) in statuses:
#            status = st[STATUS]
#            writer.writerow([filename, status])


def main():
    # extra_args = sys.argv[1:]
    # args = DEFAULT_ARGS + extra_args
    # args = f"{BASE_ARGS} {' '.join(extra_args)}"
    worklist = []
    manager = Manager()
    return_dict = manager.dict()

    print("building project...", end="")
    subprocess.run("stack build", shell=True)
    print("done")

    for b in BENCHMARKS:
        worklist.append((b, return_dict))

    # print(f"Running with: synquid {args}")
    print("running testing benchmarks...", end="")
    with Pool() as pool:
        pool.starmap(worker, worklist)
    print("done")

    statuses = sorted(return_dict.items())
    print_results(statuses)
    #print_status(statuses)
    #write_status_csv(statuses, DEFAULT_CSV_NAME)

if __name__ == '__main__':
    main()