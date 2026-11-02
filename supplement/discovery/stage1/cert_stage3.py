#!/usr/bin/env python3
"""Exact certification of the weighted ordered descent up to k_9 (Stage 3).

Claim certified: Proposition 3.10 of the notes (section 3.3): for every 0 < k <= k_9 the
running-integral conditions of every step of the weighted descent hold, where
k_9 = 125.8404540694... is the root of E Z^k_{4,5,6,7,9} = E Z^k_{2,3,5,7}.

Certificates (all exact; see cert_lib.py):
  merged_explicit  every 7-smooth antichain S covering {2,3,5,7} with max S < MCUT,
                   integrand prod_{11<=q<=max S}(1-u^q) (P_S - P_{2,3,5,7})
  merged_tail_compat  S = R0 u S' (S' composites of <R'>, R' = R \\ R0) with max S' >= MCUT,
                   small part A0 = S' cap [4,24) (any antichain), large part in the composites
                   >= 24 divisible by no element of A0 (vacuous if none is >= MCUT)
  single_explicit  compression at p in [11,59] with block T (p-smooth antichain, max T < m_p),
                   integrand prod_{p<q<=p max T}(1-u^q) (P_T(u^p) - (1-u^p))
  single_tail      blocks with max T >= m_p
  small_N          every primitive A in [2,N] for N <= 6 (target P_{P_N})
  A_9              the tight case: single crossing and k_9 in (125.84, 125.85)
All non-tight certificates are checked at K = 126 > k_9; by monotonicity in k they hold for
every k <= 126.
"""
import sys, json, time, itertools, os
from fractions import Fraction as Fr
from multiprocessing import Pool
import numpy as np
from sympy import primerange, isprime
from cert_lib import P_of, padd, pmul, crossing_type, R1, v1_certificate

K = 126
R = (2, 3, 5, 7)
MCUT = 64
B_SMALL = 24
SINGLE = [(11, 30, 24), (13, 24, 20), (17, 20, 16), (19, 16, 14), (23, 14, 12), (29, 12, 10),
          (31, 10, 9), (37, 9, 8), (41, 8, 7), (43, 8, 7), (47, 6, 6), (53, 6, 6), (59, 5, 5)]
A9 = (4, 5, 6, 7, 9)


def progress(done, total=None, **f):
    print("ANVIL_PROGRESS " + json.dumps({"done": done, "total": total, **f}), flush=True)


def smooth(primes, lo, hi):
    out = {1}
    for p in primes:
        new = set()
        for x in out:
            y = x
            while y <= hi:
                new.add(y); y *= p
        out = new
    return sorted(n for n in out if lo <= n <= hi)


def maximal_antichains_with_max(Xs, m):
    Xm = [x for x in Xs if x <= m]
    res = []
    def rec(i, chosen):
        if i == len(Xm):
            if m not in chosen:
                return
            for x in Xm:
                if x not in chosen and not any(x % a == 0 or a % x == 0 for a in chosen):
                    return
            res.append(tuple(chosen)); return
        x = Xm[i]
        if x == m:
            if not any(x % a == 0 for a in chosen):
                rec(i + 1, chosen + [x])
            return
        if not any(x % a == 0 for a in chosen) and m % x != 0:
            rec(i + 1, chosen + [x])
        rec(i + 1, chosen)
    rec(0, [])
    return res


def all_maximal_antichains(Xf):
    res = []
    def rec(i, chosen):
        if i == len(Xf):
            for x in Xf:
                if x not in chosen and not any(x % a == 0 or a % x == 0 for a in chosen):
                    return
            res.append(tuple(chosen)); return
        x = Xf[i]
        if not any(x % a == 0 for a in chosen):
            rec(i + 1, chosen + [x])
        rec(i + 1, chosen)
    rec(0, [])
    return res


def all_antichains(Xf):
    res = []
    def rec(i, chosen):
        if i == len(Xf):
            res.append(tuple(chosen)); return
        x = Xf[i]
        if not any(x % a == 0 for a in chosen):
            rec(i + 1, chosen + [x])
        rec(i + 1, chosen)
    rec(0, [])
    return res


def primes_in(lo, hi):          # primes q with lo < q <= hi
    return list(primerange(lo + 1, hi + 1))


U1_CANDIDATES = [Fr(n, 1000) for n in range(990, 600, -5)]
U0_CANDIDATES = [Fr(1, 2), Fr(2, 5), Fr(1, 3), Fr(1, 4)]


def try_v1(W, M, Bcut, target, p):
    """search u1 (descending) and u0 for a passing V1 certificate"""
    last = None
    for u1 in U1_CANDIDATES:
        for u0 in U0_CANDIDATES:
            if u0 >= u1:
                continue
            ok, info = v1_certificate(W, list(M), Bcut, target, p, K, u1, u0)
            last = (u1, u0, info)
            if ok:
                return True, {'u1': str(u1), 'u0': str(u0), **info}
            if info.get('reason', '').startswith('psi'):
                continue            # try smaller u0
            break                   # partition/integral failure: try smaller u1
    return False, {'last': str(last)}


def work(task):
    kind = task[0]
    t0 = time.time()
    try:
        if kind == 'merged_explicit':
            S = task[1]
            D = padd(P_of(S), P_of(R), 1, -1)
            ct = crossing_type(D)
            if ct in ('zero', 'nonneg'):
                return {'task': task, 'ok': True, 'type': ct}
            if ct != 'single':
                return {'task': task, 'ok': False, 'type': ct}
            g = pmul(P_of(primes_in(10, max(S))), D)
            if tuple(S) == A9:
                lo, hi = R1(g, Fr(12584, 100)), R1(g, Fr(12585, 100))
                return {'task': task, 'ok': lo > 0 and hi < 0, 'type': 'single (tight)',
                        'R(125.84)': float(lo), 'R(125.85)': float(hi)}
            val = R1(g, K)
            return {'task': task, 'ok': val > 0, 'type': ct, 'R_K(1)': float(val)}
        if kind == 'merged_tail_compat':
            # S = R0 u S', S' composites of <R'> with max S' >= MCUT and small part exactly A
            Rp, A = task[1], task[2]
            R0 = [r for r in R if r not in Rp]
            comps = [n for n in smooth(Rp, 4, 10 ** 6) if n not in Rp]
            C = [n for n in comps if n >= B_SMALL and not any(n % a == 0 for a in A)]
            if not [n for n in C if n >= MCUT]:
                return {'task': task, 'ok': True, 'type': 'vacuous'}
            W = P_of(R0 + list(primerange(11, MCUT + 1)))
            for N2 in (120, 200, 320):
                M = list(A) + [n for n in C if n < N2]
                ok, info = try_v1(W, M, N2, list(Rp), 1)
                if ok:
                    return {'task': task, 'ok': True, 'type': 'V1', 'N2': N2, **info}
            return {'task': task, 'ok': False, 'type': 'V1', **info}
        if kind == 'single_explicit':
            p, T = task[1], task[2]
            ET = padd(P_of(T), np.array([1, -1], dtype=object), 1, -1)     # P_T(v) - (1 - v)
            ct = crossing_type(ET)
            if ct == 'nonneg':
                return {'task': task, 'ok': True, 'type': ct}
            if ct != 'single':
                return {'task': task, 'ok': False, 'type': ct}
            D = padd(P_of(T, scale=p), P_of([p]), 1, -1)                 # P_T(u^p) - (1 - u^p)
            for cap in (3 * p, 6 * p, 12 * p, 10 ** 9):
                Wp = primes_in(p, min(p * max(T), cap))
                val = R1(pmul(P_of(Wp), D), K)
                if val > 0:
                    return {'task': task, 'ok': True, 'type': ct, 'R_K(1)': float(val),
                            'weight_primes': len(Wp)}
            return {'task': task, 'ok': False, 'type': ct, 'R_K(1)': float(val)}
        if kind == 'single_tail':
            p, mp, B, M = task[1], task[2], task[3], task[4]
            for cap in (4 * p, 8 * p, 10 ** 9):
                W = P_of(primes_in(p, min(p * mp, cap)))
                ok, info = try_v1(W, M, B, [p], p)
                if ok:
                    return {'task': task, 'ok': True, 'type': 'V1', 'cap': cap, **info}
            return {'task': task, 'ok': False, 'type': 'V1', **info}
        if kind == 'small_N':
            N, A = task[1], task[2]
            PN = [q for q in range(2, N + 1) if isprime(q)]
            D = padd(P_of(A), P_of(PN), 1, -1)
            ct = crossing_type(D)
            if ct in ('zero', 'nonneg'):
                return {'task': task, 'ok': True, 'type': ct}
            if ct != 'single':
                return {'task': task, 'ok': False, 'type': ct}
            val = R1(D, K)
            return {'task': task, 'ok': val > 0, 'type': ct, 'R_K(1)': float(val)}
    except Exception as e:                                   # never hide a failure
        return {'task': task, 'ok': False, 'error': repr(e)}
    finally:
        pass


def primitive_subsets(N):
    nums = list(range(2, N + 1))
    out = []
    for r in range(1, len(nums) + 1):
        for A in itertools.combinations(nums, r):
            if all(not (b % a == 0) for a, b in itertools.combinations(A, 2)):
                out.append(A)
    return out


def build_tasks():
    tasks = []
    X7 = smooth(R, 2, 10 ** 7)
    for m in [x for x in X7 if x < MCUT]:
        for S in maximal_antichains_with_max(X7, m):
            if all(any(s % r == 0 for s in S) for r in R):
                tasks.append(('merged_explicit', S))
    for r in range(1, 5):
        for Rp in itertools.combinations(R, r):
            comps = [n for n in smooth(Rp, 4, 10 ** 7) if n not in Rp]
            for A in all_antichains([n for n in comps if n < B_SMALL]):
                tasks.append(('merged_tail_compat', Rp, A))
    for p, mp, B in SINGLE:
        Xp = smooth(list(primerange(2, p + 1)), 2, 10 ** 7)
        for m in [x for x in Xp if x < mp]:
            for T in maximal_antichains_with_max(Xp, m):
                tasks.append(('single_explicit', p, T))
        for M in all_maximal_antichains([x for x in Xp if x < B]):
            tasks.append(('single_tail', p, mp, B, M))
    for N in range(2, 7):
        for A in primitive_subsets(N):
            tasks.append(('small_N', N, A))
    return tasks


if __name__ == "__main__":
    tasks = build_tasks()
    only = os.environ.get("KINDS")
    if only:
        tasks = [t for t in tasks if t[0] in only.split(",")]
    kinds = {}
    for t in tasks:
        kinds[t[0]] = kinds.get(t[0], 0) + 1
    print("tasks:", kinds, flush=True)
    t0 = time.time()
    results = []
    progress(0, len(tasks), phase="certify", unit="certificate")
    with Pool(int(os.environ.get("JOBS", 14))) as pool:
        for i, res in enumerate(pool.imap_unordered(work, tasks, chunksize=4)):
            results.append(res)
            if not res['ok']:
                print("FAIL:", json.dumps(res, default=str), flush=True)
            if i % 25 == 0:
                progress(i + 1, len(tasks), phase="certify", unit="certificate")
    progress(len(tasks), len(tasks), phase="certify", unit="certificate")
    with open(os.environ.get("LOG", "cert_stage3_log.jsonl"), "w") as f:
        for r in results:
            f.write(json.dumps(r, default=str) + "\n")
    bad = [r for r in results if not r['ok']]
    print(f"{len(results)} certificates, {len(bad)} failures, {time.time() - t0:.0f}s", flush=True)
    for kind in kinds:
        rs = [r for r in results if r['task'][0] == kind]
        vals = [r.get('R_K(1)') for r in rs if r.get('R_K(1)') is not None]
        print(f"  {kind}: {len(rs)} certificates, {sum(r['ok'] for r in rs)} ok"
              + (f", min R_K(1) = {min(vals):.3e}" if vals else ""), flush=True)
    a9 = [r for r in results if r['task'][0] == 'merged_explicit' and tuple(r['task'][1]) == A9]
    print("A_9:", a9, flush=True)
    sys.exit(1 if bad else 0)
