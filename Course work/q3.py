#!/usr/bin/env python3
"""
CSC410 Assignment 2 - SAT and SMT.
Problem 2: Solving Hidato with a SMT Solver.
by Victor Nicolet
"""
# You cannot import any other modules. Put all your helper functions in this file
# You can only use Bool and propositional logic
from z3 import Solver, Bool, And, Xor, Or, Not, BoolRef
from itertools import combinations
from typing import *
from time import time
from math import log
import sys


# ================================================================================
#  ⚠️ Do not modify above!
# ================================================================================
def largest(grid: List[List[Union[str, int]]]) -> Tuple[int, set]:
    max_v = 0
    int_set = set()
    for lst in grid:
        for item in lst:
            if isinstance(item, int):
                int_set.add(item)
                max_v = max(max_v, item)
    whole_set = set(range(1, max_v + 1)) - int_set
    return max_v, whole_set

def build_ref_list(height, width, max_v):
    ret = [[]] * height
    for i in range(height):
        ret[i] = [[]] * width
        for j in range(width):
            ret[i][j] = [Bool(mapToName(i, j, t)) for t in range(max_v + 1)]

    return ret

def is_in(arr, i, j):
    n = len(arr)
    m = len(arr[0])

    return i < n and i >= 0 and j < m and j >= 0 and arr[i][j] != None

def test_print(grid):
     for line in grid:
         print(" ".join([f"{str(x):>3s}" for x in line]))
     print("----------------")

def mapToName(i, j, selected_num):
    return str(i) + "-" + str(j) + "-" + str(selected_num)

def getBoolRef(ref_list, name):
    y, x, n = name.split("-")
    return ref_list[int(y)][int(x)][int(n)]

def solve(grid: List[List[Union[str, int]]]) -> List[List[Union[str, int]]]:
    """
    This function solves the Hidato puzzle with the initial configuration stored in grid.
    You should ouput a grid in the same format, but where all the '-' have been replaced
    by numbers.
    """
    # TODO : solve the Hidato puzzle using Z3. grid[i][j] is either "-", "*" or an integer.
    # You must use SAT, i.e. only booleans and propositional logic!
    # IMPORTANT:
    # - Your python code should be polynomial in the size of the grid.
    #   You cannot use any search algorithm or backtracking.

    # Return the completed grid if a solution exists. Otherwise, return None.
    width = len(grid[0])
    height = len(grid)
    solver = Solver()
    # whole set is the number of available elements to select
    max_v, whole_set = largest(grid)
    adj_dirs = ((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1))
    ref_list = build_ref_list(height, width, max_v)
    unset_set = []
    existing_set = []
    for i in range(height):
        for j in range(width):
            if grid[i][j] == "-":
                unset_set.append((i, j))
            elif isinstance(grid[i][j], int):
                existing_set.append((i, j))
    unique_constraint = []
    at_least_one_constraint = []
    h1 = set(whole_set)
    for y, x in unset_set:
        n_const = []
        at_least_one_constraint = []
        for n in whole_set:
            h2 = h1 - set([n])
            n_const = [Not(getBoolRef(ref_list, mapToName(y, x, t))) for t in h2]
            n_const += [getBoolRef(ref_list, mapToName(y, x, n))]
            at_least_one_constraint.append(And(*n_const))
        solver.add(Or(*at_least_one_constraint))
    for to_select in whole_set:
        for i in range(len(unset_set)):
            y1, x1 = unset_set[i]
            for j in range(i + 1, len(unset_set)):
                y2, x2 = unset_set[j]
                unique_constraint.append(And(getBoolRef(ref_list, mapToName(y1, x1, to_select)), getBoolRef(ref_list, mapToName(y2, x2, to_select))))
    solver.add(Not(Or(*unique_constraint)))
    ret = [[]] * height
    for i in range(height):
        ret[i] = [None] * len(grid[i])
        for j in range(width):
            if grid[i][j] != "-":
                ret[i][j] = grid[i][j]
    # print(solver.check())
    # get consecutive point now
    for y, x in existing_set:
        v = grid[y][x]
        if v == max_v:
            continue
        n_statement = []
        for adj in adj_dirs:
            dx, dy = adj
            x1, y1 = x + dx, y + dy
            if is_in(grid, y1, x1):
                if grid[y1][x1] == "-":
                    n_statement.append(getBoolRef(ref_list, mapToName(y1, x1, v + 1)))
                elif isinstance(grid[y1][x1], int):
                    if grid[y1][x1] == v + 1:
                        n_statement.append(True)
                    else:
                        n_statement.append(False)
        if n_statement:
            solver.add(Or(*n_statement))
    
    for y, x in existing_set:
        v = grid[y][x]
        if v == 1:
            continue
        n_statement = []
        for adj in adj_dirs:
            dx, dy = adj
            x1, y1 = x + dx, y + dy
            if is_in(grid, y1, x1):
                if grid[y1][x1] == "-":
                    n_statement.append(getBoolRef(ref_list, mapToName(y1, x1, v - 1)))
                elif isinstance(grid[y1][x1], int):
                    if grid[y1][x1] == v - 1:
                        n_statement.append(True)
                    else:
                        n_statement.append(False)
        if n_statement:
            solver.add(Or(*n_statement))

    remaining_max_v = set()
    # doing the same for unset set to get consecutive numbers
    statement = []
    for y, x in unset_set:
        statement = []
        for n in whole_set:
            n_statement = []
            b = getBoolRef(ref_list, mapToName(y, x, n))
            for adj in adj_dirs:
                dx, dy = adj
                x1, y1 = x + dx, y + dy
                if is_in(grid, y1, x1):
                    if grid[y1][x1] == "-":
                        if n < max_v - 1:
                            b1 = getBoolRef(ref_list, mapToName(y1, x1, n + 1))
                            n_statement.append(b1)
                    elif isinstance(grid[y1][x1], int):
                        if grid[y1][x1] == n + 1:
                            if grid[y1][x1] == max_v:
                                remaining_max_v.add(getBoolRef(ref_list, mapToName(y, x, n)))
                            n_statement.append(True)
                        else:
                            n_statement.append(False)
            if n_statement:
                statement.append(And(b, Or(*n_statement)))
        if statement:
            solver.add(Or(*statement))
    if remaining_max_v:
        solver.add(Or(*list(remaining_max_v)))

    remaining_max_v = set()
    # doing the same for unset set to get consecutive numbers n - 1
    statement = []
    for y, x in unset_set:
        statement = []
        for n in whole_set:
            n_statement = []
            b = getBoolRef(ref_list, mapToName(y, x, n))
            for adj in adj_dirs:
                dx, dy = adj
                x1, y1 = x + dx, y + dy
                if is_in(grid, y1, x1):
                    if grid[y1][x1] == "-":
                        if n > 2:
                            b1 = getBoolRef(ref_list, mapToName(y1, x1, n - 1))
                            n_statement.append(b1)
                    elif isinstance(grid[y1][x1], int):
                        if grid[y1][x1] == n - 1:
                            if grid[y1][x1] == 1:
                                remaining_max_v.add(getBoolRef(ref_list, mapToName(y, x, n)))
                            n_statement.append(True)
                        else:
                            n_statement.append(False)
            if n_statement:
                statement.append(And(b, Or(*n_statement)))
        if statement:
            solver.add(Or(*statement))
    if remaining_max_v:
        solver.add(Or(*list(remaining_max_v)))

    if (str(solver.check()) == "sat"):
        model = solver.model()
        for i, j in unset_set:
            for n in whole_set:
                # print(getBoolRef(ref_list, mapToName(i, j, n)))
                if model.evaluate(getBoolRef(ref_list, mapToName(i, j, n))):
                    y, x, cur = mapToName(i, j, n).split("-")
                    ret[int(y)][int(x)] = int(cur)
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
            print("Solution incomplete!")
            break


def main(argv: List[str]) -> None:
    if len(argv) < 2:
        print("Usage: python3 q3.py INPUT_FILE")
        print("\tHint: test_input contains valid input files for Hidato.")
        print("\tThe inputs that are unsat are suffixed _unsat.txt, the others are sat.")
        exit(1)

    raw_grid = []
    with open(argv[1], 'r') as input_grid:
        for line in input_grid.readlines():
            if not line.startswith("#"):
                raw_grid.append(line.strip().split())

        grid = check(raw_grid)
        # test_print(raw_grid)
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
