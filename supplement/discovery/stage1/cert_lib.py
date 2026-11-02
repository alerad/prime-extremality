"""Exact certificate primitives for the weighted ordered descent (k_9 theorem).

All arithmetic is exact: integer polynomials (numpy object arrays of Python ints), rational
endpoints (fractions.Fraction), exact real-root isolation (sympy Poly.intervals, which works
in exact integer arithmetic).  Nothing here uses floating point for a decision.

Running integral at exponent K:  R_K(y) = int_0^y K u^(K-1) g(u) du.

* SC certificate (explicit polynomial g = W * D with W > 0 on (0,1)):
    D has no root in (0,1) and D > 0 there                      -> R_K(y) >= 0 for all y, K;
    or D = u^a (1-u)^b h with h having exactly one root in (0,1), h(0) > 0 > h(1)
    (one sign change, + to -), and R_K(1) > 0                    -> R_K(y) > 0 for y in (0,1],
    and R_k(1) > 0 for every k <= K (variation diminishing: u^(k-K) is decreasing).
* V1 certificate (g = W * (E - target), E an infinite-product envelope >= 0):
    a polynomial L <= E on [0, u1] with L - target >= 0 on [0, u1], and
    int_0^u1 K u^(K-1) W (L - target) > int_u1^1 K u^(K-1) W target.
    Then R_K(y) > 0 for all y, and the same holds for every k <= K (the ratio of the two sides
    decreases in k because both integrands are >= 0 on their ranges).
"""
from fractions import Fraction as Fr
from math import lcm, gcd
from functools import reduce
import numpy as np
import sympy as sp

U = sp.symbols('u')


def P_of(exps, scale=1):
    """prod_{e in exps} (1 - u^(scale*e)) as an object array of ints."""
    c = np.array([1], dtype=object)
    for e in exps:
        e = e * scale
        out = np.zeros(len(c) + e, dtype=object)
        out[:len(c)] += c
        out[e:] -= c
        c = out
    return c


def padd(a, b, sa=1, sb=1):
    n = max(len(a), len(b))
    out = np.zeros(n, dtype=object)
    out[:len(a)] += sa * a
    out[:len(b)] += sb * b
    return out


def pmul(a, b):
    return np.convolve(a, b)


def trim(c):
    nz = np.nonzero(c != 0)[0]
    return c[:nz[-1] + 1] if len(nz) else np.array([0], dtype=object)


def strip_u_and_one_minus_u(c):
    """c = u^a (1-u)^b h with h(0) != 0, h(1) != 0.  Returns (a, b, h)."""
    c = trim(c)
    nz = np.nonzero(c != 0)[0]
    if len(nz) == 0:
        return None
    a = int(nz[0])
    h = [int(x) for x in c[a:]]
    b = 0
    while sum(h) == 0:                      # divisible by (1 - u): synthetic division
        q = []
        acc = 0
        for coef in h[:-1]:                 # h = (1-u) q  <=>  q_i = sum_{j<=i} h_j
            acc += coef
            q.append(acc)
        h = q
        b += 1
    return a, b, h


def roots_in_unit_interval(h):
    """number of distinct real roots of the integer polynomial h in [0,1] (exact)."""
    poly = sp.Poly(list(reversed(h)), U)
    return len(poly.intervals(inf=0, sup=1))


def crossing_type(D):
    """'zero', 'nonneg' (D > 0 on (0,1)), 'single' (one sign change + to -), or 'other'."""
    r = strip_u_and_one_minus_u(D)
    if r is None:
        return 'zero'
    a, b, h = r
    h0, h1 = h[0], sum(h)
    n = roots_in_unit_interval(h)
    if n == 0 and h0 > 0 and h1 > 0:
        return 'nonneg'
    if n == 1 and h0 > 0 and h1 < 0:
        return 'single'
    return 'other'


def R1(g, K):
    """exact R_K(1) = sum_n g_n K/(K+n) as a Fraction; K a positive Fraction or int."""
    K = Fr(K)
    Kn, Kd = K.numerator, K.denominator
    idx = [n for n in range(len(g)) if g[n] != 0]
    dens = [Kn + n * Kd for n in idx]
    L = reduce(lcm, dens, 1)
    num = sum(int(g[n]) * (L // d) for n, d in zip(idx, dens))
    return Fr(num * Kn, L)


def partial_integrals(g, K, x):
    """exact (int_0^x K u^(K-1) g, int_x^1 K u^(K-1) g) for integer K >= 1, rational x in (0,1)."""
    x = Fr(x)
    a, b = x.numerator, x.denominator
    idx = [n for n in range(len(g)) if g[n] != 0]
    if not idx:
        return Fr(0), Fr(0)
    top = K + idx[-1]
    dens = [K + n for n in idx]
    L = reduce(lcm, dens, 1)
    # int_0^x u^(K+n-1) du * K = K x^(K+n)/(K+n)
    lo = 0
    tot = 0
    for n, d in zip(idx, dens):
        e = K + n
        lo += int(g[n]) * (a ** e) * (b ** (top - e)) * (L // d)
        tot += int(g[n]) * (L // d)
    lo_f = Fr(lo * K, L * b ** top)
    tot_f = Fr(tot * K, L)
    return lo_f, tot_f - lo_f


def eval_P(exps, x):
    v = Fr(1)
    for e in exps:
        v *= 1 - x ** e
    return v


def v1_certificate(W, M, Bcut, target_exps, p, K, u1, u0, pieces=64, max_depth=12):
    """V1 certificate for  g = W(u) * [E(u^p) - T(u)]  where
         E(v) = P_M(v) * prod_{n >= Bcut}(1 - v^n)   (envelope, n over a subset of integers >= Bcut),
         T(u) = prod_{r in target_exps} (1 - u^r)    (target; T = 1 - u^p for single steps).
    Lower bound on [0, v1] (v1 = u1^p): E(v) >= L(v) := P_M(v) * (1 - c v^Bcut), c = 1/(1-v1).
    Returns (ok, info)."""
    u1, u0 = Fr(u1), Fr(u0)
    v1 = u1 ** p
    c = 1 / (1 - v1)
    info = {}
    if not c * v1 ** Bcut < 1:
        return False, {'reason': 'c v1^B >= 1'}
    # (i-a) near 0: Weierstrass for L, Bonferroni for T.
    #   single step (T = 1 - u^p):  D_L >= v (1 - sum_m v^(m-1) - c v^(B-1)),   v = u^p
    #   merged      (T = P_R'):     D_L >= u^r0 (1 - sum_{r<r'} u^(r+r'-r0) - sum_m u^(p m - r0)
    #                                             - c u^(p B - r0))
    if target_exps == [p]:
        v0 = u0 ** p
        psi = 1 - sum(v0 ** (m - 1) for m in M) - c * v0 ** (Bcut - 1)
    else:
        r0 = min(target_exps)
        psi = 1 - sum(u0 ** (r + s - r0) for r, s in __import__('itertools').combinations(target_exps, 2)) \
                - sum(u0 ** (p * m - r0) for m in M) - c * u0 ** (p * Bcut - r0)
        if min([p * m for m in M] + [p * Bcut]) <= r0:
            return False, {'reason': 'envelope exponent <= r0'}
    info['psi(u0)'] = float(psi)
    if psi < 0:
        return False, {'reason': 'psi(u0) < 0', **info}

    # (i-b) partition of [u0, u1]: L(b^p) - T(a) >= 0 on [a, b] (L, T decreasing)
    def L_of(x):
        return eval_P(M, x) * (1 - c * x ** Bcut)

    def T_of(x):
        return eval_P(target_exps, x)

    stack = [(u0 + (u1 - u0) * j / pieces, u0 + (u1 - u0) * (j + 1) / pieces, 0) for j in range(pieces)]
    checked = 0
    while stack:
        a, b, dpt = stack.pop()
        checked += 1
        if L_of(b ** p) - T_of(a) >= 0:
            continue
        if dpt >= max_depth:
            return False, {'reason': f'partition fails near [{float(a):.6f},{float(b):.6f}]', **info}
        mid = (a + b) / 2
        stack += [(a, mid, dpt + 1), (mid, b, dpt + 1)]
    info['pieces'] = checked

    # (ii) exact integrals.  Scale by d = (1 - v1) > 0 to keep integer coefficients:
    #      d * L(u^p) = P_M(u^p) * (d - u^(p B)) with d = 1 - v1 = (den^p - num^p)/den^p.
    num, den = u1.numerator, u1.denominator
    dn = den ** p - num ** p            # (1 - v1) * den^p
    dd = den ** p
    PM = P_of(M, scale=p)
    Lscaled = pmul(PM, padd(np.array([dn], dtype=object), np.array([0] * (p * Bcut) + [dd], dtype=object),
                            1, -1))          # = dd * (1 - v1) * L(u^p) ... (see below)
    # Lscaled = P_M(u^p) * (dn - dd u^(pB)) = dd * P_M(u^p) * ((1-v1) - u^(pB)) = dd*(1-v1)*L(u^p)
    T = P_of(target_exps)
    scale = dn                           # dd*(1-v1) = dn
    Dl = padd(Lscaled, T, 1, -scale)     # = dn * (L(u^p) - T(u))
    gL = pmul(W, Dl)
    gT = pmul(W, T)
    lo, _ = partial_integrals(gL, K, u1)          # dn * int_0^u1 K u^(K-1) W (L - T)
    _, hi = partial_integrals(gT, K, u1)          # int_u1^1 K u^(K-1) W T
    lhs, rhs = lo / scale, hi
    info['lhs'] = float(lhs)
    info['rhs'] = float(rhs)
    return lhs > rhs, info
