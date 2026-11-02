#!/usr/bin/env python3
"""Exact certificates for the ordered-compression proof that the primes minimise
E min(Z_A^k, c^k) for all 0 < k < 3 + 6*sqrt(3) (= 13.3923...).

Exact rational arithmetic only (Python fractions; sympy Sturm counts for small polynomials).
Exit status 1 on any failure.

For an envelope E (a pointwise lower bound for P_T over the admissible blocks T) and an
exponent s put  g(v) = E(v) - (1 - v)  and  R_s(Z) = int_0^Z v^(s-1) g(v) dv.  The
compression at the prime p is admissible at k = p s when R_s(Z) > 0 for all Z in (0,1].

[SC]  E is an explicit polynomial and g = v (1-v) h(v) where h has exactly one root in (0,1),
      h(0) > 0 > h(1) (Sturm).  Then R_s(Z) >= min(R_s(0+), R_s(1)), so R_s(1) > 0
      suffices; and R_s(1) > 0 implies R_{s'}(1) > 0 for s' <= s (variation diminishing:
      v^(s'-s) decreases).  R_s(1) = sum_n c_n/(s+n) is computed exactly.

[V1]  For a cut v1 < 1 and a polynomial L <= E on [0, v1]:
        (i)  f = L - (1 - v) >= 0 on [0, v1]:  on [0, v0] by Weierstrass,
             L >= 1 - sum x_i, so f >= v phi(v) with phi decreasing, checked at v0;
             on [v0, v1] by a partition a_0 < ... < a_m: L decreasing gives
             f >= L(a_{j+1}) - (1 - a_j) on [a_j, a_{j+1}];
        (ii) int_0^v1 v^(s-1) f  >  int_v1^1 v^(s-1)(1 - v).
      Since E >= 0 this gives R_s(Z) > 0 for all Z; (ii) at s implies (ii) at every s' <= s,
      so one integer s suffices.  Tails: prod_{n>M}(1 - v^n) >= 1 - v^(M+1)/(1 - v1) on [0,v1].
"""
import sys
from fractions import Fraction as Fr
import sympy as sp

FAIL = []


def check(name, ok, detail=""):
    print(f"[{'ok' if ok else 'FAIL'}] {name} {detail}", flush=True)
    if not ok:
        FAIL.append(name)


def smooth(primes, lo, hi):
    out = {1}
    for p in primes:
        new = set()
        for x in out:
            y = x
            while y <= hi:
                new.add(y)
                y *= p
        out = new
    return sorted(n for n in out if lo <= n <= hi)


# ---------- polynomials as {exponent: coefficient} ----------
def pmul_binom(P, n, c=1):
    """P * (1 - c v^n)"""
    Q = dict(P)
    for e, a in P.items():
        Q[e + n] = Q.get(e + n, 0) - c * a
    return {e: a for e, a in Q.items() if a != 0}


def poly(exps):
    P = {0: 1}
    for n in exps:
        P = pmul_binom(P, n)
    return P


def minus_one_minus_v(P):
    Q = dict(P)
    Q[0] = Q.get(0, 0) - 1
    Q[1] = Q.get(1, 0) + 1
    return {e: a for e, a in Q.items() if a != 0}


def Rs1(P, s):
    g = minus_one_minus_v(P)
    return sum(Fr(a) / (s + e) for e, a in g.items())


def single_crossing(P):
    vv = sp.symbols('v')
    g = minus_one_minus_v(P)
    assert g.get(0, 0) == 0
    gp = sp.Poly(sum(sp.Integer(a) * vv**e for e, a in g.items()), vv)
    h, rem = sp.div(gp, sp.Poly(vv * (1 - vv), vv))      # g = v (1 - v) h  (g(0) = g(1) = 0)
    assert rem.is_zero
    return h.count_roots(0, 1) == 1 and h.eval(0) > 0 and h.eval(1) < 0


def int_poly(P, s, a, b):
    """int_a^b v^(s-1) P(v) dv, integer s >= 1, exact."""
    return sum(Fr(c) * (Fr(b)**(s + e) - Fr(a)**(s + e)) / (s + e) for e, c in P.items())


def v1_certificate(name, exps, M, v1, s, v0=Fr(1, 2), pieces=400):
    """[V1] for E = prod_{n in exps}(1 - v^n), exps possibly infinite: uses the n <= M."""
    fin = [n for n in exps if n <= M]
    c = 1 / (1 - Fr(v1))
    assert c * Fr(v1) ** (M + 1) < 1, "tail factor 1 - c v^(M+1) must stay positive on [0, v1]"
    # (i) on [0, v0]: phi(v0) = 1 - sum_{n in fin} v0^(n-1) - c v0^M >= 0
    phi = 1 - sum(Fr(v0)**(n - 1) for n in fin) - c * Fr(v0)**M
    ok0 = phi >= 0 and min(fin) >= 2
    # (i) on [v0, v1]: L(b) >= 1 - a on each piece
    def L(x):
        val = Fr(1)
        for n in fin:
            val *= 1 - x**n
        return val * (1 - c * x**(M + 1))
    grid = [Fr(v0) + (Fr(v1) - Fr(v0)) * j / pieces for j in range(pieces + 1)]
    ok1 = all(L(b) >= 1 - a for a, b in zip(grid[:-1], grid[1:]))
    # (ii)
    Lp = poly(fin)
    Lp = pmul_binom(Lp, M + 1, c)
    f = minus_one_minus_v(Lp)
    lhs = int_poly(f, s, 0, v1)
    rhs = int_poly({0: 1, 1: -1}, s, v1, 1)
    check(name, ok0 and ok1 and lhs > rhs,
          f"(s={s}, v0={v0}, v1={v1}, M={M}: phi(v0)={float(phi):.3g}, pieces ok={ok1}, "
          f"lhs={float(lhs):.6g} > rhs={float(rhs):.6g})")


print("=== compression at p = 3 (blocks T in <2,3>): needs s <= 1 + 2 sqrt 3 = 4.4641 ===")
s = sp.symbols('s')
expr = 1/(s+1) - 1/(s+2) - 1/(s+3) + 1/(s+5)
check("p=3, 2 or 3 in T, E=(1-v^2)(1-v^3): R_s(1) = (11+2s-s^2)/((s+1)(s+2)(s+3)(s+5))",
      sp.simplify(sp.together(expr) - (11 + 2*s - s**2)/((s+1)*(s+2)*(s+3)*(s+5))) == 0,
      "-> R_s(1) >= 0 iff s <= 1 + 2 sqrt 3")
check("p=3, 2 or 3 in T: single crossing of (1-v^2)(1-v^3) - (1-v)", single_crossing(poly([2, 3])))
S23 = smooth([2, 3], 4, 10**4)
v1_certificate("p=3, 2,3 not in T, E=H23=prod_{n in <2,3>, n>=4}(1-v^n)", S23, 60, Fr(4, 5), 5)

print("=== compression at p = 5 (blocks T in <2,3,5>): needs s <= (3+6 sqrt 3)/5 = 2.67846 ===")
s5 = Fr(75, 28)
assert 3 + 6 * 3**0.5 < 5 * s5
r = Rs1(poly([2, 3, 5]), s5)
check("p=5, T={2,3,5}, E=(1-v^2)(1-v^3)(1-v^5): R_{75/28}(1) > 0", r > 0, f"(= {float(r):.4e})")
check("p=5, T={2,3,5}: single crossing", single_crossing(poly([2, 3, 5])))
for R0, extra in (((2, 3), 25), ((2, 5), 9), ((3, 5), 4)):
    P = poly(list(R0) + [extra])
    r = Rs1(P, Fr(3))
    check(f"p=5, T cap {{2,3,5}} = {set(R0)}, E=prod(1-v^r)*(1-v^{extra}): R_3(1) > 0", r > 0,
          f"(= {float(r):.4g})")
    check(f"p=5, T cap {{2,3,5}} = {set(R0)}: single crossing", single_crossing(P))
S235 = smooth([2, 3, 5], 4, 10**4)
envs = {
    "{2}": [2] + [n for n in S235 if n % 2 and n not in (3, 5)],
    "{3}": [3] + [n for n in S235 if n % 3 and n != 5],
    "{5}": [5] + [n for n in S235 if n % 5],
    "{}": [n for n in S235 if n not in (2, 3, 5)],
}
for R0, exps in envs.items():
    v1_certificate(f"p=5, T cap {{2,3,5}} = {R0}: infinite envelope", sorted(exps), 60, Fr(3, 4), 3)

print("=== compressions at p >= 7: J-split, needs k/7 <= 17/8 (paper's certificate) ===")
check("(3 + 6 sqrt 3)/7 < 17/8", (3 + 6 * 3**0.5) / 7 < 17 / 8, f"({(3 + 6*3**0.5)/7:.5f} < 2.125)")

if FAIL:
    print("FAILED:", FAIL)
    sys.exit(1)
print("all certificates verified")
