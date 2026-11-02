#!/usr/bin/env python3
"""Referee: k_9 and the N = 9 exhaustive check (independent of op2_*.py).

E Z_A^k = int_0^1 k u^(k-1) P_A(u) du = sum_n c_n k/(k+n),  P_A(u) = sum_n c_n u^n.
D_A(k) := E Z_A^k - E Z_P^k = k * sum_n d_n/(k+n).  For k > 0 the sign of D_A is the sign of
N_A(k) = sum_n d_n prod_{m != n}(k+m)  (integer polynomial), whose positive roots are isolated
with certified ball arithmetic (python-flint / arb).
"""
from fractions import Fraction as Fr
from itertools import combinations
import flint, mpmath as mp

def poly_of(A):
    c = {0: 1}
    for a in A:
        new = dict(c)
        for e, v in c.items():
            new[e + a] = new.get(e + a, 0) - v
        c = {e: v for e, v in new.items() if v}
    return c

def diff_coeffs(A, B):
    pa, pb = poly_of(A), poly_of(B)
    d = {e: pa.get(e, 0) - pb.get(e, 0) for e in set(pa) | set(pb)}
    return {e: v for e, v in d.items() if v}

def numer_poly(d):
    """N(k) = sum_n d_n prod_{m != n}(k + m) as fmpz_poly"""
    ns = sorted(d)
    assert 0 not in ns
    x = flint.fmpz_poly([0, 1])
    N = flint.fmpz_poly([0])
    for n in ns:
        term = flint.fmpz_poly([d[n]])
        for m in ns:
            if m != n:
                term *= (x + m)
        N += term
    return N

def positive_roots(N):
    out = []
    for z, mult in N.complex_roots():
        if z.imag.contains(0):
            if z.real > 0:
                out.append((z.real, mult))
            elif not (z.real < 0):
                out.append(("ambiguous", z))
    return sorted(out, key=lambda r: float(r[0].mid()) if not isinstance(r[0], str) else -1)

def DZ(d, k):
    return k * sum(Fr(v) / (k + n) for n, v in d.items())

# ---------------- k_9
A9, P9 = (4, 5, 6, 7, 9), (2, 3, 5, 7)
d9 = diff_coeffs(A9, P9)
N9 = numer_poly(d9)
flint.ctx.prec = 300
roots9 = positive_roots(N9)
print("positive real roots of E Z^k_{4,5,6,7,9} - E Z^k_{2,3,5,7} (certified arb enclosures):")
for r, m in roots9:
    print("   ", r, "mult", m)
# independent: exact-rational bisection on D(k) with Fractions
lo, hi = Fr(125), Fr(126)
assert DZ(d9, lo) > 0 and DZ(d9, hi) < 0
for _ in range(80):
    mid = (lo + hi) / 2
    if DZ(d9, mid) > 0: lo = mid
    else: hi = mid
mp.mp.dps = 40
print("exact bisection bracket: [", mp.nstr(mp.mpf(lo.numerator) / lo.denominator, 25), ",",
      mp.nstr(mp.mpf(hi.numerator) / hi.denominator, 25), "]")
print("claimed k_9 = 125.84045406944565748...")
print("sign at k=3146/25 (Lean bound):", "D>0" if DZ(d9, Fr(3146, 25)) > 0 else "D<=0",
      "; at k=126:", "D>0" if DZ(d9, Fr(126)) > 0 else "D<=0")

# ---------------- N = 9: all maximal primitive subsets of {2..9}
U = list(range(2, 10))
def primitive(S):
    return all(not (a != b and b % a == 0) for a in S for b in S)
anti = [S for r in range(1, len(U) + 1) for S in combinations(U, r) if primitive(S)]
maximal = [S for S in anti if not any(primitive(S + (x,)) for x in U if x not in S)]
print(f"\nN=9: {len(anti)} nonempty primitive subsets, {len(maximal)} maximal:")
res = []
for S in maximal:
    if S == P9:
        continue
    d = diff_coeffs(S, P9)
    N = numer_poly(d)
    pr = positive_roots(N)
    # sign of D at small k (k = 1/100) and first positive root
    sgn_small = DZ(d, Fr(1, 100)) > 0
    first = pr[0][0] if pr else None
    res.append((S, sgn_small, first, [str(r[0]) for r in pr]))
for S, sg, first, allr in sorted(res, key=lambda t: float(t[2].mid()) if t[2] is not None else 1e9):
    print(f"   A={S}: D(0.01)>0: {sg}; positive roots of D: {allr if allr else 'none'}")
ok = all(sg for _, sg, _, _ in res) and all((first is None) or (first > 125) for _, _, first, _ in res)
mins = min(float(f.mid()) for _, _, f, _ in res if f is not None)
print("\nNo maximal primitive A != P_9 has E Z_A^k <= E Z_P9^k for 0 < k <= 125:", ok,
      f"(smallest crossing = {mins:.12f})")
