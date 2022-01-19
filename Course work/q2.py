#!/usr/bin/env python3
"""
CSC410 Assignment 2 - SAT and SMT.
Problem 2: Solving Hidato with a SMT Solver.
by Victor Nicolet
"""
# You cannot import any other modules. Put all your helper functions in this file
# You cannot use Bool from z3, only these functions
from z3 import Solver, Int, Xor, And, Or, Not, BoolRef, ArithRef
from itertools import combinations
from typing import *
from time import time
import sys

from z3.z3 import Bool

# ================================================================================
#  ⚠️ Do not modify above!
# ================================================================================
def mapGameRow(ele, name):
    if ele == "*":
        return None
    if ele == "-":
        return Int(name)
    return ele

def is_in(arr, i, j):
    n = len(arr)
    m = len(arr[0])

    return i < n and i >= 0 and j < m and j >= 0 and arr[i][j] != None

def solve(grid: List[List[Union[str, int]]]) -> List[List[Union[str, int]]]:
    """
    This function solves the Hidato puzzle with the initial configuration stored in grid.
    You should ouput a grid in the same format, but where all the '-' have been replaced
    by numbers.
    """
    # TODO : solve the Hidato puzzle using Z3. grid[i][j] is either "-", "*" or an integer.
    # You must use SMT. The import forces you to use integers (Int(..))
    # IMPORTANT:
    # - You are not allowed to create more variables than there are cells on the grid.
    # - Your python code should be at most O(n^4) where n is the length of the longest
    # side of the grid.
    # Return the completed grid if a solution exists. Otherwise, return None.
    # raise Exception("Solve function not implemented.")
    solver = Solver()
    n = len(grid)
    dirs = ((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1))
    adj_dirs = ((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1))
    parsed_lst = [[]] * n
    max_v = 0
    for lst in grid:
        for item in lst:
            if isinstance(item, int):
                max_v = max(max_v, item)
    for i in range(n):
        m = len(grid[i])
        parsed_lst[i] = [None] * m
        for j in range(m):
            parsed_lst[i][j] = mapGameRow(grid[i][j], str(i) + "-" + str(j))
    
    flattened_parsed_lst = [item for sub in parsed_lst for item in sub if item != None]
    for i in range(len(flattened_parsed_lst)):
        for j in range(i + 1, len(flattened_parsed_lst)):
            solver.add(flattened_parsed_lst[i] != flattened_parsed_lst[j])
    for i in range(n):
        m = len(grid[i])
        for j in range(m):
            if parsed_lst[i][j] == None:
                continue
            if parsed_lst[i][j] == max_v:
                continue
            solver.add(parsed_lst[i][j] > 0)
            solver.add(parsed_lst[i][j] <= max_v)
            at_last_one_follow = []
            for adj in adj_dirs:
                dx, dy = adj
                x1, y1 = j + dx, i + dy
                if (is_in(parsed_lst, y1, x1)):
                    at_last_one_follow.append(parsed_lst[y1][x1] == parsed_lst[i][j] + 1)
            solver.add(Or(*at_last_one_follow))
            # print(And(*non_repeat_constraint))
            # print(Or(*at_last_one_follow))
    resp = solver.check()
    ret = [[]] * n
    # print(solver.check())
    # print(solver.assertions())
    if (str(resp) == "sat"):
        model = solver.model()
        for i in range(len(parsed_lst)):
            ret[i] = [None] * len(parsed_lst[i])
            for j in range(len(ret[i])):
                if parsed_lst[i][j] == None:
                    ret[i][j] = "*"
                elif isinstance(parsed_lst[i][j], int):
                    ret[i][j] = parsed_lst[i][j]
                else:
                    ret[i][j] = model.evaluate(parsed_lst[i][j])
        return ret
    return None


# ================================================================================
#  ⚠️ Do not modify below!
# ================================================================================

def check(raw_grid: List[List[str]]) -> List[List[Union[str, int]]]:
    """
    Check that the grid is well defined.
    It return a grid with integers or the strings "*" or "-",
    or None if the grid is not well defined.
    """
    n = len(raw_grid)
    assert n > 1
    m = len(raw_grid[0])
    assert m > 1

    grid = []
    # Compute min and max in the grid
    max_value = 1
    min_value = 1
    # Compute the number of blocked cells
    blocked_cells = 0
    for i in range(n):
        grid.append([])
        if not len(raw_grid[i]) == m:
            print(
                f"Line {i+1} has only {len(raw_grid[i])} cells, it should have {m}.")
            return None

        for j, elt in enumerate(raw_grid[i]):
            if elt == '*':
                blocked_cells += 1
                grid[i].append(elt)
            elif elt == '-':
                grid[i].append(elt)
            else:
                try:
                    value = int(elt)
                    max_value = max(value, max_value)
                    min_value = min(value, min_value)
                    grid[i].append(int(elt))
                except:
                    print(
                        f"Cell {i+1},{j+1} is {elt}: this is not the right format.")
                    return None

    # Check the min and max values w.r.t to then number of blocked cells
    if min_value < 1:
        print("The smallest value allowed, which is 1, should appear on the grid.")
        return None

    largest_value_allowed = (n * m - blocked_cells)
    if max_value != largest_value_allowed:
        print(
            f"The largest value should be {largest_value_allowed}, but the max value on the grid is {max_value}.")
        return None

    return grid


def print_solution(grid: List[List[Union[str, int]]]) -> None:
    for line in grid:
        if '-' not in line:
            print(" ".join([f"{str(x):>3s}" for x in line]))
        else:
            print(" ".join([f"{str(x):>3s}" for x in line]))
            print("Solution incomplete!")

def test_print(grid):
     for line in grid:
         print(" ".join([f"{str(x):>3s}" for x in line]))

def main(argv: List[str]) -> None:
    if len(argv) < 2:
        print("Usage: python3 q2.py INPUT_FILE")
        print("\tHint: test_input contains valid input files for Hidato.")
        print("\tThe inputs that are unsat are suffixed _unsat.txt, the others are sat.")
        exit(1)

    raw_grid = []
    with open(argv[1], 'r') as input_grid:
        for line in input_grid.readlines():
            if not line.startswith("#"):
                raw_grid.append(line.strip().split())
        # print(raw_grid)
        # test_print(raw_grid)
        grid = check(raw_grid)
        if grid:
            # Call the encoding function on the input.
            start = time()
            solution = solve(grid)
            elapsed = time() - start
            if solution:
                print_solution(solution)

            print(f"ELAPSED: {elapsed: 4.4f} seconds.")

            exit(0)
        else:
            # Grid is none: this means there is no solution!
            print("The input file does not define a valid problem.")
            exit(1)


if __name__ == '__main__':
    main(sys.argv)
