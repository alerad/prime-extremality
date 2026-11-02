#!/usr/bin/env python3
"""Referee spot-check of the 'exhaustive N <= 46' evidence for Conjecture 3.7, for small N.

For each N, all maximal primitive A in {2..N}, A != P_N: first k in (0, 400] where
D_A(k) = E Z_A^k - E Z_{P_N}^k = k * sum_n d_n/(k+n) changes sign, using arb ball arithmetic on a grid
(signs certified at grid points) and certified bisection.  Reports min over A per N.
"""
import json, sys, time
import flint
flint.ctx.prec = 400

def progress(done, total, phase, unit, _s={"t": 0.0}):
    if time.time() - _s["t"] >= 1.0 or done == total:
        _s["t"] = time.time()
        print("ANVIL_PROGRESS " + json.dumps({"done": done, "total": total, "phase": phase, "unit": unit}, separators=(",", ":")), flush=True)

def primes_upto(n):
    return [p for p in range(2, n + 1) if all(p % d for d in range(2, int(p ** 0.5) + 1))]

def maximal_antichains(N):
    U = list(range(N, 1, -1))           # decreasing order
    comp = {a: {b for b in range(2, N + 1) if b != a and (a % b == 0 or b % a == 0)} for a in range(2, N + 1)}
    out = []
    def rec(i, chosen, blocked):
        if i == len(U):
            # maximal iff every element is chosen or comparable to a chosen one
            if all(x in chosen or (comp[x] & chosen) for x in U):
                out.append(tuple(sorted(chosen)))
            return
        x = U[i]
        if x not in blocked:
            rec(i + 1, chosen | {x}, blocked | comp[x])
        # exclude x: allowed only if it can still be covered (some comparable element chosen or choosable later)
        if (comp[x] & chosen) or any(y not in blocked for y in comp[x] if U.index(y) > i):
            rec(i + 1, chosen, blocked)
    rec(0, frozenset(), frozenset())
    return out

def coeffs(A):
    c = {0: 1}
    for a in A:
        new = dict(c)
        for e, v in c.items():
            new[e + a] = new.get(e + a, 0) - v
        c = {e: v for e, v in new.items() if v}
    return c

def make_D(A, P):
    ca, cp = coeffs(A), coeffs(P)
    d = [(n, ca.get(n, 0) - cp.get(n, 0)) for n in set(ca) | set(cp)]
    d = [(n, v) for n, v in d if v]
    def f(k):                       # arb: sum d_n/(k+n), same sign as D_A(k) for k > 0
        kk = flint.arb(k)
        return sum((flint.arb(v) / (kk + n) for n, v in d), flint.arb(0))
    return f

def sign(x):
    if x > 0: return 1
    if x < 0: return -1
    return 0                         # undecided ball (never happened at prec 400)

def first_crossing(f, kmax=400.0, step=0.25):
    k = step; s0 = sign(f(k))
    if s0 <= 0:
        return ("nonpositive near 0", k)
    while k < kmax:
        k2 = k + step; s = sign(f(k2))
        if s == 0:
            return ("undecided", k2)
        if s < 0:
            lo, hi = k, k2
            for _ in range(45):
                m = 0.5 * (lo + hi)
                if sign(f(m)) > 0: lo = m
                else: hi = m
            return ("ok", lo)
        k = k2
    return ("none<=400", None)

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20
glob = []
for N in range(9, NMAX + 1):
    P = tuple(primes_upto(N))
    As = [A for A in maximal_antichains(N) if A != P]
    best = (1e9, None); flags = []
    for i, A in enumerate(As):
        st, k = first_crossing(make_D(A, P))
        if st == "ok" and k < best[0]:
            best = (k, A)
        elif st not in ("ok", "none<=400"):
            flags.append((A, st, k))
        progress(i + 1, len(As), f"N={N}", "antichain")
    glob.append((N, len(As) + 1, best))
    print(f"N={N}: {len(As)+1} maximal antichains; min first crossing = {best[0]:.6f} at A={best[1]}"
          + (f"; FLAGS {flags}" if flags else ""), flush=True)
