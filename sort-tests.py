#!/usr/bin/python3

import os
import subprocess
from multiprocessing import Pool, Manager
import sys
import csv

'''
Show the changes among our existing benchmarks.
This does not perform the acutal moves.

Example usage:

$ ./sort-tests.py
All-Neg.sq: 02-wip -> 05-impossible
List-Compress.sq: 02-wip -> 05-impossible
List-Even-Parity.sq: 02-wip -> 03-checks
Tree-Fold.sq: 05-impossible | No change.

[Usage]:

sort-tests.py <synquid args>
'''

SYNQUID = "stack run -- synquid"
BASE_ARGS = "-c=False"

TIMEOUT_SEC = 15

BASE_TEST_PATH = "./test/intersection/intersection/"

WIP_DIR = "02-wip"
CHECKS_DIR = "03-checks"
SYNTH_DIR = "04-synthesizes"
FAILS_DIR = "05-impossible"

WORKING_DIRS = [WIP_DIR, CHECKS_DIR, SYNTH_DIR, FAILS_DIR]

SUCCESS_STATUS = 'success'
TIMEOUT_STATUS = 'timeout'
FAILED_STATUS = 'failed'

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

FNULL = open(os.devnull, 'w')

def run_file(filepath, args):
    cmd = ' '.join([SYNQUID, args, filepath])
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


def worker(subdir, filename, return_dict, args):
    filepath = os.path.join(BASE_TEST_PATH, subdir, filename)
    status = run_file(filepath, args)
    new_dir = sort_dir(subdir, status)

    if return_dict is not None:
        return_dict[filename] = {
            OLD_DIR: subdir,
            NEW_DIR: new_dir,
            STATUS: status}

def print_status(status):
    for (filename, st) in status:
        new_dir = st[NEW_DIR]
        old_dir = st[OLD_DIR]
        new_dir_str = new_dir
        if new_dir == CHECKS_DIR:
            new_dir_str = f"{bcolors.OKGREEN}{new_dir}"
        if new_dir != old_dir:
            print(f"{filename}: {bcolors.WARNING}{old_dir} -> {new_dir_str}{bcolors.ENDC}")
        else:
            print(f"{filename}: {old_dir} | No change.")


def write_status_csv(statuses, filename):
    with open(filename, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile, quoting=csv.QUOTE_MINIMAL)
        writer.writerow(["Filename", "Status"])
        for (filename, st) in statuses:
            status = st[STATUS]
            writer.writerow([filename, status])


def main():
    extra_args = sys.argv[1:]
    args = f"{BASE_ARGS} {' '.join(extra_args)}"
    worklist = []
    manager = Manager()
    return_dict = manager.dict()

    print("building project...", end="")
    subprocess.run("stack build", shell=True)
    print("done")

    for subdir in WORKING_DIRS:
        for filename in os.listdir(os.path.join(BASE_TEST_PATH, subdir)):
            worklist.append((subdir, filename, return_dict, args))

    print(f"Running with: synquid {args}")
    print("running testing benchmarks...", end="")
    with Pool() as pool:
        pool.starmap(worker, worklist)
    print("done")

    statuses = sorted(return_dict.items())
    print_status(statuses)
    write_status_csv(statuses, DEFAULT_CSV_NAME)

if __name__ == '__main__':
    main()