#!/usr/bin/env python3
"""Simulate the descent of the proof of Theorem thm:k9 on random primitive sets and assert every
bookkeeping claim: p-smoothness at stage p, addability of the primes in (p,N], p*max T <= N,
B_0 = P cap (p, p max T] subset B, coverage of every block T / final set S by a certified case,
and the claim 'A contains P cap [11,N]' at step (iii) (counted, not asserted)."""
import json, os, random, sys, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rv_common import is_prime, largest_prime_factor, is_antichain, smooth_list

HERE = os.path.dirname(os.path.abspath(__file__))
cases = json.load(open(os.path.join(HERE, "rv_cases.json")))
SINGLE = {11: (30, 24), 13: (24, 20), 17: (20, 16), 19: (16, 14), 23: (14, 12), 29: (12, 10),
          31: (10, 9), 37: (9, 8), 41: (8, 7), 43: (8, 7), 47: (6, 6), 53: (6, 6), 59: (5, 5)}
EXPL_T = {(p, tuple(T)) for p, T in cases["single_explicit"]}
TAIL_T = {}
for p, mp, B, M in cases["single_tail"]:
    TAIL_T.setdefault(p, []).append(set(M))
EXPL_S = [set(S) for S in cases["merged_explicit"]]
TAIL_S = {(tuple(Rp), tuple(A0)) for Rp, A0 in cases["merged_tail"]}


def smooth_upto(n, p):
    return largest_prime_factor(n) <= p


def covered_T(p, T):
    mp, Bp = SINGLE[p]
    if max(T) < mp:
        m = max(T)
        return any(q == p and set(T) <= set(Tm) and max(Tm) == m for (q, Tm) in EXPL_T)
    small = {t for t in T if t < Bp}
    return any(small <= M for M in TAIL_T[p])


def covered_S(S):
    if max(S) < 64:
        return any(set(S) <= Sm and max(Sm) == max(S) for Sm in EXPL_S)
    R0 = tuple(r for r in (2, 3, 5, 7) if r in S)
    Rp = tuple(r for r in (2, 3, 5, 7) if r not in S)
    A0 = tuple(sorted(s for s in S if s not in R0 and s < 24))
    return (Rp, A0) in TAIL_S


def descent(A, N, stats):
    A = set(A)
    comp = lambda: [a for a in A if not is_prime(a)]
    # (i)
    while True:
        big = [a for a in comp() if largest_prime_factor(a) >= 61]
        if not big:
            break
        p = largest_prime_factor(big[0])
        A = {a for a in A if a % p} | {p}
    # (ii)
    for p in [q for q in range(59, 10, -1) if is_prime(q)]:
        assert all(smooth_upto(a, p) for a in comp()), "composite not p-smooth"
        for q in range(p + 1, N + 1):
            if is_prime(q) and q not in A:
                assert all(a % q for a in A), "prime not addable"
                A.add(q)
        if any(a % p == 0 for a in comp()):
            T = sorted(a // p for a in A if a % p == 0)
            B = {a for a in A if a % p}
            assert is_antichain(T) and min(T) >= 2 and all(smooth_upto(t, p) for t in T)
            assert p * max(T) <= N
            assert all(q in B for q in range(p + 1, p * max(T) + 1) if is_prime(q)), "B0 not in B"
            if not covered_T(p, T):
                stats["uncovered_T"].append((p, T))
            stats["compressions"] += 1
            A = B | {p}
    # (iii)
    assert all(smooth_upto(a, 7) for a in comp())
    missing = [q for q in range(11, N + 1) if is_prime(q) and q not in A]
    if missing:
        stats["missing_ge11_at_iii"] += 1
        stats["missing_examples"].append(sorted(missing))
        for q in missing:
            assert all(a % q for a in A)
            A.add(q)
    for r in (2, 3, 5, 7):
        if r <= N and all(a % r for a in A):
            A.add(r)
    if N >= 7:
        S = sorted(a for a in A if a < 11 or not is_prime(a))
        assert all(any(s % r == 0 for s in S) for r in (2, 3, 5, 7))
        if not covered_S(S):
            stats["uncovered_S"].append(S)
    stats["runs"] += 1


def random_primitive(N, rng):
    nums = list(range(2, N + 1))
    # bias toward small composites to exercise the descent
    nums.sort(key=lambda n: (rng.random() * (3 if is_prime(n) else 1)) * n ** 0.5)
    A = []
    for x in nums:
        if rng.random() < 0.7 and all(x % a and a % x for a in A):
            A.append(x)
    return A


if __name__ == "__main__":
    rng = random.Random(2026)
    stats = {"runs": 0, "compressions": 0, "missing_ge11_at_iii": 0, "missing_examples": [],
             "uncovered_T": [], "uncovered_S": []}
    for trial in range(20000):
        N = rng.choice([7, 8, 9, 10, 11, 12, 15, 20, 25, 30, 40, 50, 64, 80, 100, 130, 160, 200, 260])
        descent(random_primitive(N, rng), N, stats)
    print("runs", stats["runs"], "compressions at p in [11,59]", stats["compressions"])
    print("uncovered blocks T:", len(stats["uncovered_T"]), stats["uncovered_T"][:5])
    print("uncovered final sets S:", len(stats["uncovered_S"]), stats["uncovered_S"][:5])
    print("runs where some prime >= 11 was missing at step (iii):", stats["missing_ge11_at_iii"],
          "examples:", stats["missing_examples"][:5])
    print("of which missing set == [11]:", sum(1 for m in stats["missing_examples"] if m == [11]))
