#!/usr/bin/env python3
"""Independent enumeration of every finite case of Proposition prop:cert, and comparison with the
task lists recorded in the logs.  Writes rv_cases.json (my own case list) for later scripts."""
import itertools, json, os, sys
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rv_common import (smooth_list, maximal_antichains, all_antichains, is_antichain, is_prime,
                       RSET)

HERE = os.path.dirname(os.path.abspath(__file__))
LOGDIR = os.path.join(HERE, "..", "stage1")

SINGLE = {11: (30, 24), 13: (24, 20), 17: (20, 16), 19: (16, 14), 23: (14, 12), 29: (12, 10),
          31: (10, 9), 37: (9, 8), 41: (8, 7), 43: (8, 7), 47: (6, 6), 53: (6, 6), 59: (5, 5)}
MCUT, BSMALL = 64, 24


def primes_upto(p):
    return [q for q in range(2, p + 1) if is_prime(q)]


cases = {}

# (b) explicit: maximal antichains of 7-smooth numbers in [2,m] containing m, m < 64, covering R.
X7 = smooth_list(RSET, 2, MCUT - 1)
merged = []
for m in X7:
    V = [x for x in X7 if x <= m]
    for S in maximal_antichains(V):
        if m in S and all(any(s % r == 0 for s in S) for r in RSET):
            merged.append(S)
cases["merged_explicit"] = merged

# (a) explicit: maximal antichains of p-smooth numbers in [2,m] containing m, m < m_p.
single = []
for p, (mp, Bp) in SINGLE.items():
    Xp = smooth_list(primes_upto(p), 2, mp - 1)
    for m in Xp:
        V = [x for x in Xp if x <= m]
        for T in maximal_antichains(V):
            if m in T:
                single.append((p, T))
cases["single_explicit"] = single

# (a) tails: maximal antichains of p-smooth numbers in [2, B_p).
stails = []
for p, (mp, Bp) in SINGLE.items():
    V = smooth_list(primes_upto(p), 2, Bp - 1)
    for M in maximal_antichains(V):
        stails.append((p, mp, Bp, M))
cases["single_tail"] = stails

# (b) tails: R' nonempty subset of R, A0 any antichain of composites of <R'> in [4,24).
mtails = []
for r in range(1, 5):
    for Rp in itertools.combinations(RSET, r):
        comps = [n for n in smooth_list(Rp, 4, BSMALL - 1) if not is_prime(n)]
        for A0 in all_antichains(comps):
            mtails.append((Rp, A0))
cases["merged_tail"] = mtails

# (c) small N: nonempty primitive subsets of [2,N], N <= 6.
small = []
for N in range(2, 7):
    nums = list(range(2, N + 1))
    for r in range(1, len(nums) + 1):
        for A in itertools.combinations(nums, r):
            if is_antichain(A):
                small.append((N, A))
cases["small_N"] = small

print({k: len(v) for k, v in cases.items()})
print("single explicit per p:", dict(Counter(p for p, _ in single)))
print("single tails per p:", dict(Counter(t[0] for t in stails)))
print("merged explicit per max:", dict(sorted(Counter(max(S) for S in merged).items())))

# ------------------------------------------------------------ compare with the logged task lists
logs = [json.loads(l) for f in ("cert_part1_log.jsonl", "cert_part2_log.jsonl")
        for l in open(os.path.join(LOGDIR, f))]
lt = Counter(r["task"][0] for r in logs)
print("logged kinds:", dict(lt))


def norm(kind, t):
    if kind == "merged_explicit":
        return tuple(sorted(t[1]))
    if kind == "single_explicit":
        return (t[1], tuple(sorted(t[2])))
    if kind == "single_tail":
        return (t[1], t[2], t[3], tuple(sorted(t[4])))
    if kind == "merged_tail_compat":
        return (tuple(t[1]), tuple(sorted(t[2])))
    if kind == "small_N":
        return (t[1], tuple(sorted(t[2])))


mine = {
    "merged_explicit": {tuple(sorted(S)) for S in merged},
    "single_explicit": {(p, tuple(sorted(T))) for p, T in single},
    "single_tail": {(p, mp, B, tuple(sorted(M))) for p, mp, B, M in stails},
    "merged_tail_compat": {(tuple(Rp), tuple(sorted(A))) for Rp, A in mtails},
    "small_N": {(N, tuple(sorted(A))) for N, A in small},
}
for kind, S in mine.items():
    logged = [norm(kind, r["task"]) for r in logs if r["task"][0] == kind]
    L = set(logged)
    print(f"{kind}: mine {len(S)}, logged {len(logged)} (distinct {len(L)}), "
          f"missing-from-log {len(S - L)}, extra-in-log {len(L - S)}")
    if S - L:
        print("   missing examples:", sorted(S - L)[:5])
    if L - S:
        print("   extra examples:", sorted(L - S)[:5])

# vacuity of merged tails: C(A0) = composites of <R'> >= 24, divisible by no element of A0;
# vacuous iff no element >= 64.  Every element of C(A0) above 448 has a divisor in C(A0) in [64,448)
# (divide by primes <= 7), so checking up to 448 decides it.
vac = []
for Rp, A0 in mtails:
    C = [n for n in smooth_list(Rp, BSMALL, 448) if not is_prime(n) and not any(n % a == 0 for a in A0)]
    if not any(n >= MCUT for n in C):
        vac.append((Rp, A0))
print("vacuous merged tails:", len(vac), vac)
logged_vac = {norm("merged_tail_compat", r["task"]) for r in logs
              if r["task"][0] == "merged_tail_compat" and r.get("type") == "vacuous"}
print("vacuous sets agree with log:", {(tuple(a), tuple(sorted(b))) for a, b in vac} == logged_vac)

with open(os.path.join(HERE, "rv_cases.json"), "w") as f:
    json.dump({k: v for k, v in cases.items()}, f)
print("wrote rv_cases.json")
