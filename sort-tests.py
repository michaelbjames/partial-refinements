#!/usr/bin/python3

import os
import subprocess
from multiprocessing import Pool, Manager

'''
Show the changes among our existing benchmarks.
This does not perform the acutal moves.

Example usage:

$ ./sort-tests.py
All-Neg.sq: 02-wip -> 05-impossible
List-Compress.sq: 02-wip -> 05-impossible
List-Even-Parity.sq: 02-wip -> 03-checks
Tree-Fold.sq: 05-impossible | No change.
'''

SYNQUID = "stack run -- synquid"
BASE_ARGS = "-c=False -f nonterminating"

TIMEOUT_SEC = 10

BASE_TEST_PATH = "test/intersection/intersection/"

WIP_DIR = "02-wip"
CHECKS_DIR = "03-checks"
SYNTH_DIR = "04-synthesizes"
FAILS_DIR = "05-impossible"

WORKING_DIRS = [WIP_DIR, CHECKS_DIR, SYNTH_DIR, FAILS_DIR]

SUCCESS_STATUS = 'success_STATUS'
TIMEOUT_STATUS = 'timeout'
FAILED_STATUS = 'failed'

FNULL = open(os.devnull, 'w')

def run_file(filepath):
    cmd = ' '.join([SYNQUID, BASE_ARGS, filepath])
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


def worker(subdir, filename, return_dict=None):
    filepath = os.path.join(BASE_TEST_PATH, subdir, filename)
    status = run_file(filepath)
    new_dir = sort_dir(subdir, status)

    if return_dict is not None:
        return_dict[filename] = (subdir, new_dir)

def print_status(status):
    for (filename, (old_dir, new_dir)) in status:
        if new_dir != old_dir:
            print(f"{filename}: {old_dir} -> {new_dir}")
        else:
            print(f"{filename}: {old_dir} | No change.")


def main():
    worklist = []
    manager = Manager()
    return_dict = manager.dict()

    for subdir in WORKING_DIRS:
        for filename in os.listdir(os.path.join(BASE_TEST_PATH, subdir)):
            worklist.append((subdir, filename, return_dict))

    with Pool() as pool:
        pool.starmap(worker, worklist)

    print_status(sorted(return_dict.items()))

if __name__ == '__main__':
    main()