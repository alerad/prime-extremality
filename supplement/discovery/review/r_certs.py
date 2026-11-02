#!/usr/bin/env python3
"""Referee re-verification of the certificates behind notes Theorem 3.6 (k < 3 + 6 sqrt 3).

Written independently of envelope_certificate.py.  Three layers:
  (1) exact rational arithmetic (own polynomial + own Sturm-sequence code, Fractions),
      cross-checked with python-flint certified root isolation;
  (2) high-resolution floating-point running integrals R_s(z) for every envelope,
      including the infinite ones, plus the true threshold s* of each envelope;
  (3) an independent exact re-run of the (V1) inequalities with a different cut/partition.
"""
import sys, math
from fractions import Fraction as Fr
import numpy as np
import flint

FAIL = []
def report(name, ok, detail=""):
    print(f"[{'ok' if ok else 'FAIL'}] {name} {detail}", flush=True)
    if not ok:
        FAIL.append(name)

# ---------------------------------------------------------------- exact polynomials (lists, low->high)
def pnorm(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a
def padd(a, b):
    n = max(len(a), len(b)); return pnorm([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])
def pneg(a): return [-x for x in a]
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return pnorm(r)
def pdivmod(a, b):
    a = [Fr(x) for x in a]; b = [Fr(x) for x in pnorm(b)]
    q = [Fr(0)] * max(1, len(a) - len(b) + 1)
    while len(pnorm(a)) >= len(b) and any(a):
        a = pnorm(a)
        if len(a) < len(b): break
        c = a[-1] / b[-1]; d = len(a) - len(b); q[d] = c
        for i, y in enumerate(b):
            a[i + d] -= c * y
        a = pnorm(a)
        if len(a) == 1 and a[0] == 0: break
    return pnorm(q), pnorm(a)
def pder(a): return pnorm([i * a[i] for i in range(1, len(a))]) if len(a) > 1 else [0]
def peval(a, x):
    r = 0
    for c in reversed(a): r = r * x + c
    return r
def one_minus_pow(n):
    a = [0] * (n + 1); a[0] = 1; a[n] = -1; return a
def prod_env(exps):
    P = [1]
    for n in exps: P = pmul(P, one_minus_pow(n))
    return P

def sturm_count(h, a, b):
    """number of distinct real roots of h in (a, b], own Sturm chain in exact arithmetic"""
    chain = [[Fr(x) for x in h], [Fr(x) for x in pder(h)]]
    while True:
        _, r = pdivmod(chain[-2], chain[-1])
        if len(r) == 1 and r[0] == 0: break
        chain.append(pneg(r))
    def var(x):
        s = [peval(p, x) for p in chain]; s = [v for v in s if v != 0]
        return sum(1 for u, v in zip(s, s[1:]) if (u > 0) != (v > 0))
    return var(a) - var(b)

def Rs1(E, s):
    """exact int_0^1 v^(s-1) (E(v) - (1-v)) dv for rational s > 0"""
    g = padd(E, [-1, 1])
    return sum(Fr(c) / (s + n) for n, c in enumerate(g) if c)

def to_fmpz_poly(h):
    P = flint.fmpq_poly([flint.fmpq(Fr(c).numerator, Fr(c).denominator) for c in h])
    return P.numer()

def flint_real_roots_in(h, lo, hi):
    """certified: list of (enclosure, mult) of real roots in (lo, hi); 'ambiguous' if undecidable"""
    out = []
    for z, mult in to_fmpz_poly(h).complex_roots():
        re, im = z.real, z.imag
        if not im.contains(0):
            continue                      # certainly non-real
        if (re > lo) and (re < hi):
            out.append((re, mult))
        elif (re < lo) or (re > hi) or (re <= lo) or (re >= hi):
            continue                      # certainly outside
        else:
            out.append(("ambiguous " + str(re), mult))
    return out

def flint_roots_01(h):
    return flint_real_roots_in(h, 0, 1)

print("=== (1) exact checks ===")
s = None
# closed form for (1-v^2)(1-v^3): R_s(1) = 1/(s+1) - 1/(s+2) - 1/(s+3) + 1/(s+5)
E23 = prod_env([2, 3])
g23 = padd(E23, [-1, 1])
report("g23 = v - v^2 - v^3 + v^5", g23 == [0, 1, -1, -1, 0, 1], str(g23))
# identity: (s+2)(s+3)(s+5) - (s+1)(s+3)(s+5) - (s+1)(s+2)(s+5) + (s+1)(s+2)(s+3) == 11 + 2s - s^2
L = lambda c: [c, 1]
lhs = padd(padd(pmul(pmul(L(2), L(3)), L(5)), pneg(pmul(pmul(L(1), L(3)), L(5)))),
           padd(pneg(pmul(pmul(L(1), L(2)), L(5))), pmul(pmul(L(1), L(2)), L(3))))
report("closed form numerator == 11 + 2s - s^2", lhs == [11, 2, -1], str(lhs))
r1 = 1 + 2 * math.sqrt(3)
report("root of 11+2s-s^2 is 1+2sqrt3", abs(11 + 2 * r1 - r1 * r1) < 1e-12, f"(1+2sqrt3 = {r1:.10f}, 3*(1+2sqrt3) = {3*r1:.10f})")
# spot check of closed form vs exact sum at a few rationals
for sv in (Fr(1), Fr(7, 2), Fr(4), Fr(9, 2)):
    a = Rs1(E23, sv); b = (11 + 2 * sv - sv * sv) / ((sv + 1) * (sv + 2) * (sv + 3) * (sv + 5))
    report(f"  closed form at s={sv}", a == b, f"R={float(a):.6e}")

envs_poly = {
    "(1-v^2)(1-v^3)": [2, 3],
    "E_{2,3,5}=(1-v^2)(1-v^3)(1-v^5)": [2, 3, 5],
    "E_{2,3}=(1-v^2)(1-v^3)(1-v^25)": [2, 3, 25],
    "E_{2,5}=(1-v^2)(1-v^5)(1-v^9)": [2, 5, 9],
    "E_{3,5}=(1-v^3)(1-v^4)(1-v^5)": [3, 4, 5],
}
for name, ex in envs_poly.items():
    E = prod_env(ex)
    g = padd(E, [-1, 1])
    q, r = pdivmod(g, pmul([0, 1], [1, -1]))       # g = v(1-v) h
    ok_div = (len(r) == 1 and r[0] == 0)
    h = q
    n_st = sturm_count(h, Fr(0), Fr(1))
    fr = flint_roots_01(h)
    report(f"{name}: g = v(1-v)h, h(0)={peval(h,0)}, h(1)={peval(h,1)}, #roots of h in (0,1] (own Sturm) = {n_st}, flint roots in (0,1) = {[(str(x), m) for x, m in fr]}",
           ok_div and n_st == 1 and peval(h, 0) > 0 and peval(h, 1) < 0 and len(fr) == 1 and fr[0][1] == 1)

s75 = Fr(75, 28)
R75 = Rs1(prod_env([2, 3, 5]), s75)
report("E_{2,3,5}: exact R_{75/28}(1) > 0", R75 > 0, f"= {R75} = {float(R75):.6e}")
report("75/28 > (3+6sqrt3)/5", Fr(75, 28) > Fr(0) and float(s75) > (3 + 6 * math.sqrt(3)) / 5,
       f"({float(s75):.8f} vs {(3+6*math.sqrt(3))/5:.8f}); exact: (5*75/28-3)^2 = {(5*s75-3)**2} > 108 <=> {(5*s75-3)**2 > 108}")
for name, ex in list(envs_poly.items())[2:]:
    r3 = Rs1(prod_env(ex), Fr(3))
    report(f"{name}: exact R_3(1) > 0", r3 > 0, f"= {float(r3):.6e}")

# threshold s* of each polynomial envelope: root of R_s(1) (decreasing sign change) via mpmath
import mpmath as mp
mp.mp.dps = 30
print("thresholds s* (R_{s*}(1) = 0) of the polynomial envelopes:")
for name, ex in envs_poly.items():
    g = padd(prod_env(ex), [-1, 1])
    f = lambda sv: mp.fsum(mp.mpf(c) / (sv + n) for n, c in enumerate(g) if c)
    # bracket
    lo, hi = mp.mpf('0.5'), mp.mpf('0.5')
    while f(hi) > 0: hi += mp.mpf('0.25')
    lo = hi - mp.mpf('0.25')
    root = mp.findroot(f, (lo, hi), solver='anderson')
    print(f"   {name:36s} s* = {mp.nstr(root, 15)}   (p=3: k<{mp.nstr(3*root, 10)}, p=5: k<{mp.nstr(5*root, 10)})", flush=True)

print("=== (2) floating-point running integrals, all envelopes incl. infinite ===")
def smooth(primes, hi):
    out = {1}
    for p in primes:
        new = set()
        for x in out:
            y = x
            while y <= hi:
                new.add(y); y *= p
        out = new
    return sorted(out)
S23 = [n for n in smooth([2, 3], 20000) if n >= 4]
S235 = [n for n in smooth([2, 3, 5], 20000) if n >= 4]
inf_envs = {
    "H23 (2,3 notin T, p=3)": S23,
    "E_{2} (p=5)": [2] + [n for n in S235 if n % 2 and n != 5],
    "E_{3} (p=5)": [3] + [n for n in S235 if n % 3 and n != 5],
    "E_{5} (p=5)": [5] + [n for n in S235 if n % 5],
    "E_{} (p=5, exact: 5 excluded)": [n for n in S235 if n != 5],
    "E_{} (p=5, as in script: 5 included)": list(S235),
}
# grid: Gauss-Legendre on many panels -> cumulative running integral at panel ends
NP = 40000
xg, wg = np.polynomial.legendre.leggauss(8)
edges = np.linspace(0.0, 1.0, NP + 1)
mid = 0.5 * (edges[1:] + edges[:-1]); half = 0.5 * (edges[1:] - edges[:-1])
V = (mid[:, None] + half[:, None] * xg[None, :])          # NP x 8 nodes
W = (half[:, None] * wg[None, :])
logV = np.log(V)
def env_vals(exps):
    """returns g = E - (1-v) computed as v + expm1(log E) (no cancellation near v = 0)"""
    le = np.zeros_like(V)
    for n in exps:
        t = V ** n
        if t.max() < 1e-300: break
        le += np.log1p(-np.minimum(t, 1 - 1e-300))
    return V + np.expm1(le)
def run_int(Evals, s):
    integrand = np.exp((s - 1) * logV) * Evals
    cell = (integrand * W).sum(1)
    return edges[1:], np.cumsum(cell)
def min_run(Evals, s, zmin=1e-2):
    z, R = run_int(Evals, s)
    m = z >= zmin
    i = np.argmin(R[m])
    return R[m][i], z[m][i], R[-1]
def threshold(Evals, lo, hi):
    # largest s with min_z R_s(z) > 0 (R near 0 is ~ z^(s+1)/(s+1) > 0)
    for _ in range(60):
        mdl = 0.5 * (lo + hi)
        if min_run(Evals, mdl)[0] > 0: lo = mdl
        else: hi = mdl
    return lo
allE = {name: env_vals(ex) for name, ex in envs_poly.items()}
allE.update({name: env_vals(ex) for name, ex in inf_envs.items()})
for name, Ev in allE.items():
    srt = threshold(Ev, 0.5, 12.0)
    print(f"   {name:40s} threshold s* = {srt:.10f}", flush=True)
need = {
    "(1-v^2)(1-v^3)": (1 + 2 * math.sqrt(3)) - 1e-9,
    "H23 (2,3 notin T, p=3)": 1 + 2 * math.sqrt(3),
    "E_{2,3,5}=(1-v^2)(1-v^3)(1-v^5)": (3 + 6 * math.sqrt(3)) / 5,
}
for name, Ev in allE.items():
    sneed = need.get(name, (3 + 6 * math.sqrt(3)) / 5)
    m, zm, R1 = min_run(Ev, sneed)
    report(f"float: {name} at s={sneed:.6f}: min_(z>=0.01) R_s(z) = {m:.4e} at z={zm:.4f}, R_s(1)={R1:.4e}", m > 0)
    if name in inf_envs or name.startswith("H23"):
        scert = 5 if name.startswith("H23") else 3
        m2, zm2, R12 = min_run(Ev, scert)
        report(f"float: {name} at certificate s={scert}: min R = {m2:.4e} at z={zm2:.4f}", m2 > 0)

print("=== (3) independent exact re-run of the (V1) inequalities (different cut/partition) ===")
def v1_check(name, exps, M, v1, s, pieces):
    fin = [n for n in exps if n <= M]
    c = 1 / (1 - v1)
    Lp = pmul(prod_env(fin), [1] + [0] * M + [-c])            # L = prod(1-v^n) * (1 - c v^(M+1))
    f = padd(Lp, [-1, 1])
    # (i) f >= 0 on [0, v1]: exact Sturm count of roots of f/v on (0, v1] + sign at v1/2 and v1
    fv, r = pdivmod(f, [0, 1]); assert len(r) == 1 and r[0] == 0
    # condition for monotonicity argument and the Weierstrass factor: c v1^(M+1) <= 1
    ok_tail = c * v1 ** (M + 1) <= 1
    # f = v*fv with fv(0) = 1 > 0; certified (flint/arb) absence of real roots of fv in (0, v1]
    rts = flint_real_roots_in(fv, 0, float(v1) + 1e-12)
    v1a = flint.arb(flint.fmpq(v1.numerator, v1.denominator))
    rts = [r for r in rts if not (isinstance(r[0], flint.arb) and (r[0] > v1a))]
    nst = len(rts)
    a1 = v1
    ok_i = ok_tail and nst == 0 and peval(fv, 0) > 0 and peval(fv, v1) > 0
    # (ii) int_0^v1 v^(s-1) f  >  int_v1^1 v^(s-1)(1-v)
    lhs = sum(Fr(cf) * v1 ** (s + n) / (s + n) for n, cf in enumerate(f) if cf)
    rhs = (Fr(1) / s - Fr(1) / (s + 1)) - (v1 ** s / s - v1 ** (s + 1) / (s + 1))
    ok = ok_i and lhs > rhs
    print(f"    V1 {name}: v1={v1}, M={M}, s={s}: c*v1^(M+1)<=1:{ok_tail}, certified real roots of f/v in (0,{a1}]={nst}, (i) ok:{ok_i}, (ii) lhs={float(lhs):.6g} vs rhs={float(rhs):.6g} -> {'certificate' if ok else 'no certificate at this cut'}", flush=True)
    return ok
for name, exps, s in (("H23", S23, 5),
                      ("E_{2}", inf_envs["E_{2} (p=5)"], 3),
                      ("E_{3}", inf_envs["E_{3} (p=5)"], 3),
                      ("E_{5}", inf_envs["E_{5} (p=5)"], 3),
                      ("E_{} (5 included)", inf_envs["E_{} (p=5, as in script: 5 included)"], 3)):
    oks = [v1_check(name, exps, 50, v1, s, 300) for v1 in (Fr(7, 10), Fr(3, 4), Fr(4, 5))]
    report(f"V1 (independent exact re-run) {name} at s={s}: some cut certifies", any(oks))

print("FAILED:" if FAIL else "all referee checks passed", FAIL if FAIL else "")
sys.exit(1 if FAIL else 0)
