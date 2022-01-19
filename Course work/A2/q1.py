#!/usr/bin/env python3
"""
CSC410 Assignment 2 - SAT and SMT.
Problem 1: Encodings of At-Most-k
by Victor Nicolet
"""
# You cannot import any other modules. Put all your helper functions in this file
import time
from z3 import *
import itertools
import sys
from typing import *

# ================================================================================
# ⚠️ Do not modify above!
# Your task is to write the functions 'naive' and 'sequential_counter' below.
# Also, don't forget to add your performance comparison in the comments.
# If you want to write your own automated tests, you can import this file into
# another file.
# Good luck!
# ================================================================================


def naive(literals: List[BoolRef], k: int, c: int = 0) -> List[BoolRef]:
    """
    Design your naive encoding of the at-most-k constraint.
    You are not allowed to create new variables for this encoding.
    The function returns the list of clauses that encode the at-most-k contraint.
    NOTE:
    The parameter c can be used to store temporary information that needs to be
    passed onto the next call of sequential_counter (see the test function.)
    Using it is not mandatory. c can only be an integer.
    """
    n = len(literals)
    lumi = itertools.combinations(literals, n - k)
    r = []
    for l in lumi:
        r.append(And(*[Not(ll) for ll in l]))
    so = [Or(*r)]
    return so, c


def sequential_counter(literals: List[BoolRef], k: int, c: int = 0) -> List[BoolRef]:
    """
    Implement the sequential counter encoding of the at-most-k constraint.
    You have to create new variables for this encoding.
    The function returns the list of clauses that encode the at-most-k constraint.
    NOTE:
    The parameter c can be used to store temporary information that needs to be
    passed onto the next call of sequential_counter (see the test function).
    Using it is not mandatory. c can only be an integer.
    """
    clauses = []
    X = [1] + literals
    n = len(literals)
    R = [[1]]

    for i in range(0, n):
        R.append([Bool("R%d-%d-%d" % (c, i + 1, j)) for j in range(k + 1)])
    # TODO: remove statement below and implement the encoding.
    clauses.append(Or(Not(X[1]), R[1][1]))
    for j in range(2, k + 1):
        clauses.append(Not(R[1][j]))
    for i in range(2, n):
        clauses.append(And(Or(Not(X[i]), R[i][1]), Or(Not(R[i - 1][1]), R[i][1])))
    
    for i in range(2, n):
        for j in range(2, k + 1):
            clauses.append(And(Or(Not(X[i]), Not(R[i - 1][j - 1]), R[i][j]), Or(Not(R[i - 1][j]), R[i][j])))
    
    for i in range(2, n):
        clauses.append(Or(Not(X[i]), Not(R[i - 1][k])))
    clauses.append(Or(Not(X[n]), Not(R[n - 1][k])))
    return clauses, c + 1

# ===
# - Is the performance difference between the two encodings significant?
# TODO : your response in comments here.
# Our naive encoding takes a combination function and makes at least N-K variable to be False.
# the number of combination is small when k is either to 0 or close to N as a result 
# there are less clauses to add in the test of both at most k and at least k
# The algorithm complexity for naive is O(n^(min(k,n-k)))) as the combination algorithm  
# The time difference was trivial when N value is small 
# With large N value, as we increases K, naive encoding gets worse and is significantly slower than 
# the sequential counter encoding.
# For naive encoding, we'll get the worst performance with a fixed N when we increases K value to somewhere around middle (e.g.(2+N)/2)
# As we keep increaseing K and getting closer to N, the performance gets better for naive encoding
# The time complexity for sequential counter encoding is O(NK) as N and K value pair increases, the algorithm will
# will take more time
# In reality, due to the cash line, sometimes we have a faster running time feedback with larger K value, but overall performance follows the O(NK) time complexity
# that is, when K and N increases, the time consumed will be higher
# Conclusion: When we take a bigger N, K value, the sequential counter encodeing give a much better overall performance
# than the naive approach       

# ===

# ================================================================================
#  ⚠️ Do not modify below!
# ================================================================================


def test(encoding_function, n: int, k: int) -> None:
    """
    The following test encodes the constraint of having exactly k variables true by
    encoding at-most-k over (X_1, .., X_n) and at-least-k:
    - at-most-k is encoded by the encoding function given as argument.
    - at-least-k is encoded by encoding at-most-(n-k) on the negation of the variables.
    """
    X = []
    for i in range(n):
        X += [Bool("b%d" % i)]
    s = Solver()
    at_most_k, c = encoding_function(X, k)
    # Parameter c returned in previous call is passed as argument in next call.
    # Use it if you need it - but you cannot modify this code.
    at_least_k, c = encoding_function([Not(x) for x in X], n - k, c)
    # Add all the clauses to the solver
    for clause in at_most_k + at_least_k:
        s.add(clause)
    # Should print sat
    start = time.time()
    resp = s.check()
    end = time.time()
    if str(resp) == "sat":
        m = s.model()
        count_true = 0
        for x in X:
            try:
                if m.evaluate(x):
                    count_true += 1
            except Z3Exception:
                pass
        if count_true == k:
            print("PASSED in %fs" % (end - start))
        else:
            print("FAILED")
    else:
        print("FAILED")


def usage():
    print("Usage: python3 q1.py E N K")
    print("      - E is 0 to use naive encoding or 1 to use sequential counter encoding.")
    print("      - K and N two integers such that N >= K > 2.")


def main(argv):
    if len(argv) < 4:
        usage()
        exit(1)
    e, n, k = int(argv[1]) == 0, int(argv[2]), int(argv[3])
    if not (n >= k > 2):
        usage()
        exit(1)
    if e:
        test(naive, n, k)
    else:
        test(sequential_counter, n, k)


if __name__ == '__main__':
    main(sys.argv)
