#!/usr/bin/env python3
"""Local search (simulated annealing) for counterexamples beyond the exhaustive range.

State: an antichain F of composites, all of whose prime factors are <= PMAX, with max F <= X.
Competitor: A_F = F u (P_N minus primes dividing F), N = max F (lightest weight = worst case:
extra primes only add a nonincreasing factor).  Objective: k*(A_F, N) over ALL truncations c.
Floating point; evidence only.
"""
import json, os, sys, time, random
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rv_common import is_prime, progress
import rv_cex as C


def smooth_composites(pmax, X):
    ps = [q for q in range(2, pmax + 1) if is_prime(q)]
    out = []
    for n in range(4, X + 1):
        if is_prime(n):
            continue
        m = n
        for q in ps:
            while m % q == 0:
                m //= q
        if m == 1:
            out.append(n)
    return out


def comp_set(F):
    ps = set()
    for f in F:
        m, d = f, 2
        while d * d <= m:
            while m % d == 0:
                ps.add(d); m //= d
            d += 1
        if m > 1:
            ps.add(m)
    return ps


def competitor(F):
    N = max(F)
    ps = comp_set(F)
    return tuple(sorted(set(F) | {q for q in range(2, N + 1) if is_prime(q) and q not in ps})), N


def kstar_many(Fs):
    """thresholds for a list of F (grouped by N)."""
    out = [None] * len(Fs)
    byN = {}
    for i, F in enumerate(Fs):
        A, N = competitor(F)
        byN.setdefault(N, []).append((i, A))
    for N, lst in byN.items():
        D = C.D_matrix([A for _, A in lst], N)
        ks = C.thresholds(D)
        for (i, _), k in zip(lst, ks):
            out[i] = float(k) if np.isfinite(k) else 500.0
    return out


def maximize(F, pool, rng):
    F = set(F)
    cand = pool[:]
    rng.shuffle(cand)
    for x in cand:
        if x not in F and all(x % a and a % x for a in F):
            F.add(x)
    return F


def neighbor(F, pool, rng):
    r = rng.random()
    if r < 0.15 and len(F) > 1:                     # drop an element
        G = set(F); G.discard(rng.choice(sorted(G)))
    else:                                           # insert x, remove comparables
        near = [y for y in pool if y <= 2 * max(F) + 10]
        x = rng.choice(near)
        G = {a for a in F if a % x and x % a}
        G.add(x)
    if rng.random() < 0.5:
        G = maximize(G, [y for y in pool if y <= max(G)], rng)   # keep the max (lighter weight)
    return G


def anneal(args):
    pmax, X, seed, steps = args
    rng = random.Random(seed)
    pool = smooth_composites(pmax, X)
    # start: half the runs from known dangerous sets, half from random small maximal antichains
    seeds = [{4, 6, 9}, {4, 6, 9, 10, 15, 25}, {4, 6, 9, 10, 14, 15, 21, 25, 35, 49}, {4, 6, 9, 10, 15},
             {4, 6, 9, 14, 21, 49}, {4, 6, 9, 10, 14, 15, 21, 22, 33, 25, 35, 49, 55, 77, 121}]
    seeds = [S for S in seeds if all(x in pool for x in S)]
    if seed % 2 == 0 and seeds:
        F = set(rng.choice(seeds))
    else:
        top = rng.choice([x for x in pool if 9 <= x <= max(12, X // 3)])
        F = maximize(set(), [y for y in pool if y <= top], rng)
    k = kstar_many([F])[0]
    isA9 = lambda G: competitor(G)[0] == (4, 5, 6, 7, 9)
    best = (k, sorted(F)) if not isA9(F) else (np.inf, None)
    T0 = 6.0
    for s in range(steps):
        nb = [neighbor(F, pool, rng) for _ in range(24)]
        ks = kstar_many(nb)
        j = int(np.argmin(ks))
        T = T0 * (1 - s / steps) + 0.05
        if ks[j] < k or rng.random() < np.exp(-(ks[j] - k) / T):
            F, k = nb[j], ks[j]
        for G, kg in zip(nb, ks):                   # best non-A_9 competitor seen
            if kg < best[0] and not isA9(G):
                best = (kg, sorted(G))
    return {"pmax": pmax, "X": X, "seed": seed, "best_k": best[0], "best_F": best[1],
            "N": max(best[1]) if best[1] else None}


if __name__ == "__main__":
    from multiprocessing import Pool
    configs = []
    seed = 0
    for pmax, X in [(3, 400), (5, 200), (7, 120), (7, 200), (7, 400), (11, 150), (11, 300), (13, 200)]:
        for r in range(int(os.environ.get("RESTARTS", 8))):
            configs.append((pmax, X, seed, int(os.environ.get("STEPS", 60)))); seed += 1
    res = []
    t0 = time.time()
    with Pool(int(os.environ.get("JOBS", 16))) as pool:
        for i, r in enumerate(pool.imap_unordered(anneal, configs)):
            res.append(r)
            print(json.dumps(r), flush=True)
            progress(i + 1, len(configs), "anneal", "run")
    res.sort(key=lambda r: r["best_k"])
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "rv_cex_local.json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"done in {time.time()-t0:.0f}s; best thresholds:")
    for r in res[:12]:
        print(round(r["best_k"], 3), "pmax", r["pmax"], "X", r["X"], "N", r["N"], r["best_F"])
    print("any below k_9:", any(r["best_k"] < 125.8404540694 - 1e-6 for r in res))
