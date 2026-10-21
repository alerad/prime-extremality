"""Exact check of the large-k failure recorded in Open Problem 2.

For N = 9 and A_9 = {4,5,6,7,9} (Proposition 1.3), compares
E Z_A^k = int_0^1 k u^{k-1} P_A(u) du  in exact rational arithmetic
for A = P_9 = {2,3,5,7} and A = A_9, and reports the least k >= 1 from
which A_9 beats the primes, and that no primitive subset of {2..9}
beats the primes for k in {1, 2}.  Exit status nonzero on failure.
"""
from fractions import Fraction as Fr
from itertools import combinations
import sys


def primitive(A):
    return all(not (a != b and b % a == 0) for a in A for b in A)


def poly(A):
    p = {0: 1}
    for a in A:
        q = dict(p)
        for j, c in p.items():
            q[j + a] = q.get(j + a, 0) - c
        p = q
    return p


def moment(A, k):
    """int_0^1 k u^{k-1} prod_{a in A}(1-u^a) du, exactly."""
    return sum(Fr(k * c, k + j) for j, c in poly(A).items())


def main():
    P9 = (2, 3, 5, 7)
    A9 = (4, 5, 6, 7, 9)
    assert primitive(A9)
    first = next(k for k in range(1, 2000) if moment(A9, k) < moment(P9, k))
    print(f"least k with E Z_{{A_9}}^k < E Z_{{P_9}}^k : k = {first}")
    assert first == 126, first
    assert moment(A9, 125) > moment(P9, 125)
    S = range(2, 10)
    cands = [c for r in range(1, 9) for c in combinations(S, r)
             if primitive(c) and set(c) != set(P9)]
    for k in (1, 2):
        base = moment(P9, k)
        assert all(moment(c, k) > base for c in cands), k
    print("k = 1, 2: primes strictly minimal over all primitive subsets of {2..9}")
    print("all checks passed")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as e:
        sys.exit(f"FAIL: {e}")
