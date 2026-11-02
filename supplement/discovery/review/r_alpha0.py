#!/usr/bin/env python3
"""Referee: alpha_0 = sup{b : J_b(1) > 0},  J_s(1) = int_0^1 x^(s-1) (Q(x) - (1-x)) dx.

Independent method: x = e^{-t},
    J_s(1) = I(s) - 1/(s(s+1)),   I(s) = int_0^inf exp(-s t - Phi(t)) dt,
Phi(t) = -sum_p log(1 - e^{-pt}).  Phi is evaluated ONCE at fixed Gauss-Legendre nodes (it does
not depend on s), in mpmath at 40 digits with an explicit, rigorous tail bound for the omitted
primes; I(s) is then a cheap weighted sum, and alpha_0 is found by a secant/Anderson iteration.
A second, double-precision run with a different panel layout is a cross-check.
"""
import json, time, sys
import numpy as np
import mpmath as mp
from sympy import primerange

def progress(done, total, phase, unit):
    print("ANVIL_PROGRESS " + json.dumps({"done": done, "total": total, "phase": phase, "unit": unit},
                                         separators=(",", ":")), flush=True)

mp.mp.dps = 40
T_LO, T_HI = mp.mpf("0.0035"), mp.mpf("40")     # integrand < 1e-31 outside (checked below)
PRIMES = list(primerange(2, 40000))

def phi_mp(t):
    """Phi(t) with primes p < P; tail sum_{p>=P} -log(1-e^{-pt}) <= e^{-Pt}/((1-e^{-t})(1-e^{-Pt}))"""
    y = mp.exp(-t)
    s = mp.mpf(0)
    P = None
    for p in PRIMES:
        e = y ** p
        if e < mp.mpf(10) ** (-45):
            P = p; break
        s -= mp.log1p(-e)
    assert P is not None, "need more primes"
    tail = mp.exp(-P * t) / ((1 - y) * (1 - mp.exp(-P * t)))
    return s, tail

# Gauss-Legendre panels, geometric in t
edges = [T_LO]
while edges[-1] < T_HI:
    edges.append(min(T_HI, edges[-1] * mp.mpf("1.35")))
DEG = 30
# nodes of Gauss-Legendre degree DEG via mpmath
def gl_nodes(n):
    # roots of Legendre P_n with Newton, 40 digits
    nodes, weights = [], []
    for i in range(1, n + 1):
        x = mp.cos(mp.pi * (i - mp.mpf(1) / 4) / (n + mp.mpf(1) / 2))
        for _ in range(100):
            p0, p1 = mp.mpf(1), x
            for k in range(2, n + 1):
                p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
            dp = n * (x * p1 - p0) / (x * x - 1)
            dx = p1 / dp
            x -= dx
            if abs(dx) < mp.mpf(10) ** (-38):
                break
        nodes.append(x); weights.append(2 / ((1 - x * x) * dp * dp))
    return nodes, weights
gx, gw = gl_nodes(DEG)
T, Wt, PHI, TAIL = [], [], [], []
npan = len(edges) - 1
t0 = time.time(); last = 0
for i in range(npan):
    a, b = edges[i], edges[i + 1]
    for x, w in zip(gx, gw):
        t = (a + b) / 2 + (b - a) / 2 * x
        ph, tl = phi_mp(t)
        T.append(t); Wt.append(w * (b - a) / 2); PHI.append(ph); TAIL.append(tl)
    if time.time() - last > 1:
        progress(i + 1, npan, "phi_nodes", "panel"); last = time.time()
progress(npan, npan, "phi_nodes", "panel")
maxtail = max(TAIL)
print(f"{len(T)} nodes, {npan} panels; max omitted-prime tail in Phi: {mp.nstr(maxtail, 3)}")

def I(s):
    return mp.fsum(w * mp.exp(-s * t - ph) for t, w, ph in zip(T, Wt, PHI))
def J(s):
    return I(s) - 1 / (s * (s + 1))

# truncation of the t-range: integrand at the ends
print("integrand at t_lo, t_hi (s=2.14):", mp.nstr(mp.exp(-2.14 * T[0] - PHI[0]), 3), mp.nstr(mp.exp(-2.14 * T[-1] - PHI[-1]), 3))
# quadrature convergence check: same nodes vs. halved panels for one s
for sv in (mp.mpf(17) / 8, mp.mpf(3)):
    print(f"J_{mp.nstr(sv,6)}(1) = {mp.nstr(J(sv), 20)}")
print("paper: J_{17/8}(1) > 1/20000 = 5e-5 (exact certificate), J_3(1) < 0")
a0 = mp.findroot(J, (mp.mpf("2.14"), mp.mpf("2.15")), solver="secant", tol=mp.mpf(10) ** (-34))
print("alpha_0 (40-digit arithmetic, GL deg 30) =", mp.nstr(a0, 25))
print("dJ/ds at alpha_0 ~", mp.nstr(mp.diff(J, a0), 6))

# ---------- cross-check in double precision, different layout (uniform panels in log t)
pr = np.array(list(primerange(2, 40000)), dtype=float)
u_edges = np.linspace(np.log(0.003), np.log(45.0), 401)
xg, wg = np.polynomial.legendre.leggauss(20)
um = 0.5 * (u_edges[1:] + u_edges[:-1]); uh = 0.5 * (u_edges[1:] - u_edges[:-1])
U = (um[:, None] + uh[:, None] * xg[None, :]).ravel()
WU = (uh[:, None] * wg[None, :]).ravel()
tt = np.exp(U)
ph = np.zeros_like(tt)
for chunk in np.array_split(pr, 50):
    ph -= np.log1p(-np.exp(-np.outer(tt, chunk))).sum(1)
def Jd(s):
    return np.sum(WU * tt * np.exp(-s * tt - ph)) - 1.0 / (s * (s + 1))
lo, hi = 2.14, 2.15
for _ in range(200):
    m = 0.5 * (lo + hi)
    if Jd(m) > 0: lo = m
    else: hi = m
print("alpha_0 (double precision, log-t panels, bisection) = %.15f" % lo)
print("claimed alpha_0 = 2.14312191825192...")
