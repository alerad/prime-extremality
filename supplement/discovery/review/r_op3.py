#!/usr/bin/env python3
"""Referee recomputation for notes Section 2 (Theorem 2.4, Table 1, Prop. 2.3 numerics).

Written independently of op3_local.py / op3_check_thmA.py / op3_tables.py.

Method 1 (no telescoping):  I_N - Lambda = int_0^1 (P_N - Q) dx
      = int_0^inf e^{-t} P_N(e^{-t}) [1 - prod_{p>N}(1 - e^{-pt})] dt,
  evaluated in log space on Gauss-Legendre panels in u = log t; the bracket is -expm1(sum log1p(-e^{-pt})).
Method 2 (telescoping, different quadrature from the authors): delta(p) = int_0^inf e^{-(p+1)t} prod_{r<p}(1-e^{-rt}) dt
  on a fixed Gauss-Legendre node set in u = log t, the product updated prime by prime;
  I_N - Lambda = sum_{p>N} delta(p) by log-space suffix sums.
Main term of Theorem 2.4:  -log( sqrt(2 pi/Phi''(t_q)) e^{-M_q} Sigma_q ),  Sigma_q = sum_{p>=q} e^{-(p-q) t_q}.
"""
import json, time, math, sys
import numpy as np

def progress(done, total, phase, unit, _state={"t": 0.0}):
    now = time.time()
    if now - _state["t"] >= 1.0 or done == total:
        _state["t"] = now
        print("ANVIL_PROGRESS " + json.dumps({"done": done, "total": total, "phase": phase, "unit": unit},
                                             separators=(",", ":")), flush=True)

def sieve(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]

PR = sieve(700000).astype(np.float64)
a = math.pi ** 2 / 6

# ------------------------------------------------------------------ saddle quantities
def phi_derivs(t, pmax_factor=60.0):
    """Phi, Phi', Phi'' at scalar t, all primes with p t <= pmax_factor (rest < e^-60 relative)"""
    P = PR[PR <= pmax_factor / t + 10]
    x = P * t
    em = -np.expm1(-x)                     # 1 - e^{-pt}
    y = np.exp(-x)
    phi = -np.sum(np.log1p(-y))
    d1 = -np.sum(P * y / em)
    d2 = np.sum(P * P * y / (em * em))
    return phi, d1, d2

def saddle(n):
    t = math.sqrt(2 * a / (n * math.log(n)))
    for _ in range(60):
        _, d1, d2 = phi_derivs(t)
        dt = (d1 + n) / d2
        t -= dt
        if abs(dt) < 1e-15 * t:
            break
    phi, d1, d2 = phi_derivs(t)
    assert abs(d1 + n) < 1e-9 * n, (n, d1)
    return t, n * t + phi, d2              # t_n, M_n, Phi''(t_n)

def Sigma(q, tq):
    P = PR[(PR >= q) & (PR <= q + 80.0 / tq)]
    return np.sum(np.exp(-(P - q) * tq))

def gl_panels(u0, u1, npan, deg=16):
    xg, wg = np.polynomial.legendre.leggauss(deg)
    e = np.linspace(u0, u1, npan + 1)
    m = 0.5 * (e[1:] + e[:-1]); h = 0.5 * (e[1:] - e[:-1])
    return (m[:, None] + h[:, None] * xg).ravel(), (h[:, None] * wg).ravel()

def logsumexp(v, w):
    m = np.max(v)
    return m + math.log(np.sum(w * np.exp(v - m)))

# ------------------------------------------------------------------ Method 1
def method1(N, span=3.0, npan=160):
    q = int(PR[np.searchsorted(PR, N, side="right")])
    tq, Mq, d2 = saddle(q)
    U, W = gl_panels(math.log(tq) - span, math.log(tq) + span, npan)
    t = np.exp(U)
    A = np.zeros_like(t)                   # log P_N(e^{-t})
    for chunk in np.array_split(PR[PR <= N], 20):
        A += np.log1p(-np.exp(-np.outer(t, chunk))).sum(1)
    S = np.zeros_like(t)                   # sum_{p>N} log1p(-e^{-pt})
    hi = N + 900.0 / tq
    big = PR[(PR > N) & (PR <= hi)]
    assert PR[-1] > hi
    for chunk in np.array_split(big, max(1, len(big) // 2000)):
        S += np.log1p(-np.exp(-np.outer(t, chunk))).sum(1)
    B = -np.expm1(S)
    with np.errstate(divide="ignore"):
        ell = -t + A + np.log(B) + U       # + U: dt = t du
    ok = np.isfinite(ell)
    val = logsumexp(ell[ok], W[ok])
    edge = max(ell[0], ell[-1]) - np.max(ell[ok])
    return q, -val, edge, (tq, Mq, d2)

# ------------------------------------------------------------------ Method 2 (incremental delta(p))
def method2(p_first, p_last, t_lo, t_hi, npan, deg=16):
    U, W = gl_panels(math.log(t_lo), math.log(t_hi), npan, deg)
    t = np.exp(U)
    Lsum = np.zeros_like(t)
    for chunk in np.array_split(PR[PR < p_first], 40):
        Lsum += np.log1p(-np.exp(-np.outer(t, chunk))).sum(1)
    ps = PR[(PR >= p_first) & (PR <= p_last)]
    logd = np.empty(len(ps)); edge = np.empty(len(ps))
    for i, p in enumerate(ps):
        ell = -(p + 1) * t + Lsum + U
        m = ell.max()
        logd[i] = m + math.log(np.sum(W * np.exp(ell - m)))
        edge[i] = max(ell[0], ell[-1]) - m
        Lsum += np.log1p(-np.exp(-p * t))
        progress(i + 1, len(ps), "delta_p", "prime")
    return ps, logd, edge

if __name__ == "__main__":
    C0 = -0.5 * math.log(math.pi) + 0.25 * math.log(2 * a)
    TABLE = [1009, 10007, 19609, 31397, 50021, 89689, 99989]
    claims = {1009: (4, 47.953, -0.252, -0.187, 0.0227), 10007: (2, 130.735, -0.056, 0.006, 0.0072),
              19609: (52, 175.991, -0.116, -0.055, 0.0048), 31397: (72, 216.825, -0.083, -0.023, 0.0034),
              50021: (2, 266.497, -0.095, -0.036, 0.0027), 89689: (64, 346.084, -0.153, -0.096, 0.0020),
              99989: (2, 363.416, -0.010, 0.046, 0.0020)}
    print("=== Method 1 (direct integral of P_N - Q) ===", flush=True)
    m1 = {}
    for N in TABLE:
        q, val, edge, (tq, Mq, d2) = method1(N)
        q2, val2, _, _ = method1(N, span=3.5, npan=260)          # convergence check
        m1[N] = (q, val, tq, Mq, d2)
        print(f"N={N}: q={q}, -log(I_N-Lambda) = {val:.10f} (refined grid: {val2:.10f}, diff {val-val2:+.1e}); "
              f"log(integrand at ends / max) = {edge:.1f}", flush=True)

    print("=== Method 2 (sum of delta(p), GL panels in log t) ===", flush=True)
    p_last = 160000
    t_hi = 20 * saddle(1013)[0]
    t_lo = saddle(p_last)[0] / 20
    ps, logd, edge2 = method2(1013, p_last, t_lo, t_hi, npan=220)
    print(f"{len(ps)} primes p in [1013,{p_last}]; worst log(integrand at ends / max) = {edge2.max():.1f}", flush=True)
    # suffix log-sums: logT[i] = log sum_{j>=i} delta(p_j)
    logT = np.logaddexp.accumulate(logd[::-1])[::-1]
    idx = {int(p): i for i, p in enumerate(ps)}

    # mpmath spot check of one delta(p)
    import mpmath as mp
    mp.mp.dps = 30
    def delta_mp(p):
        rs = [int(r) for r in PR[PR < p]]
        f = lambda t: mp.exp(-(p + 1) * t + mp.fsum(mp.log1p(-mp.exp(-r * t)) for r in rs))
        tp = saddle(p)[0]
        pts = [mp.mpf(tp) * c for c in (0.05, 0.3, 0.6, 0.8, 0.9, 1.0, 1.1, 1.25, 1.5, 2.0, 4.0, 20.0)]
        return mp.log(mp.quad(f, pts))
    for p in (1013, 10009):
        lm = delta_mp(p)
        print(f"mpmath check: log delta({p}) = {mp.nstr(lm, 15)}  vs method 2: {logd[idx[p]]:.12f}  (diff {float(lm) - logd[idx[p]]:+.2e})", flush=True)

    print("=== Table 1 (notes) recomputed ===")
    print(f"{'N':>6} {'q-N':>4} {'-log(I-L) m1':>14} {'m2':>14} {'claimed':>9} | {'res heur':>9} {'cl':>7} | {'-log(tq lq S)':>13} {'cl':>7} | {'res Thm2.4':>10} {'cl':>7}")
    rows_out = []
    for N in TABLE:
        q, v1, tq, Mq, d2 = m1[N]
        v2 = -logT[idx[q]]
        S = Sigma(q, tq)
        main = Mq + 0.5 * math.log(d2 / (2 * math.pi)) - math.log(S)
        heur = Mq + 0.25 * math.log(q) + 0.75 * math.log(math.log(q)) + C0
        loc = -math.log(tq * math.log(q) * S)
        cl = claims[N]
        rows_out.append((N, q - N, v1, v2, v1 - heur, loc, v1 - main))
        print(f"{N:>6} {q-N:>4} {v1:>14.6f} {v2:>14.6f} {cl[1]:>9.3f} | {v1-heur:>+9.4f} {cl[2]:>+7.3f} | {loc:>+13.4f} {cl[3]:>+7.3f} | {v1-main:>+10.5f} {cl[4]:>+7.4f}")

    print("=== Prop. 2.3 numerics: log(delta(p) / (sqrt(2pi/Phi''(t_p)) e^{-M_p - t_p})) ===")
    # p = 101 separately (method-2 style, standalone)
    tp101 = saddle(101)[0]
    ps101, ld101, _ = method2(101, 101, tp101 / 30, tp101 * 30, npan=200)
    vals = {101: ld101[0]}
    for p in (1009 + 4, 10007, 100003):
        pp = int(PR[np.searchsorted(PR, p)])
        vals[pp] = logd[idx[pp]] if pp in idx else None
    claimed23 = {101: 0.0211, 1013: 0.0073, 10007: 0.0029, 100003: 0.0011}
    for p, ld in vals.items():
        tp, Mp, d2p = saddle(p)
        r = ld - (0.5 * math.log(2 * math.pi / d2p) - Mp - tp)
        print(f"   p={p}: {r:+.5f}   (notes: {claimed23.get(p, float('nan')):+.4f}; notes use p=1009 for '10^3')")
    # p = 1009 itself (needs primes < 1009 only): standalone
    tp1009 = saddle(1009)[0]
    _, ld1009, _ = method2(1009, 1009, tp1009 / 30, tp1009 * 30, npan=200)
    tp, Mp, d2p = saddle(1009)
    print(f"   p=1009: {ld1009[0] - (0.5*math.log(2*math.pi/d2p) - Mp - tp):+.5f}   (notes: +0.0073)")

    print("=== Ranges over N = p_n in (20000, 10^5] (notes: Thm 2.4 residual in [0.0019,0.0048]; heur residual in [-0.25,0.16], sd 0.057; regression slope 1.0009, intercept -0.058, corr 0.9995) ===", flush=True)
    Ns = PR[(PR > 20000) & (PR <= 100000)]
    qs = PR[np.searchsorted(PR, Ns, side="right")]
    # vectorized Newton for all q
    tq = np.sqrt(2 * a / (qs * np.log(qs)))
    Pphi = PR[PR <= 60.0 / tq.min() + 10]
    def derivs(tv):
        f0 = np.zeros_like(tv); f1 = np.zeros_like(tv); f2 = np.zeros_like(tv)
        for chunk in np.array_split(Pphi, 60):
            x = np.outer(tv, chunk); y = np.exp(-x); em = -np.expm1(-x)
            f0 -= np.log1p(-y).sum(1); f1 -= (chunk * y / em).sum(1); f2 += (chunk * chunk * y / (em * em)).sum(1)
        return f0, f1, f2
    for it in range(8):
        f0, f1, f2 = derivs(tq)
        tq = tq - (f1 + qs) / f2
        progress(it + 1, 8, "newton_all_q", "iteration")
    f0, f1, f2 = derivs(tq)
    assert np.max(np.abs(f1 + qs) / qs) < 1e-9
    Mq = qs * tq + f0
    Sig = np.array([Sigma(q, t) for q, t in zip(qs, tq)])
    meas = np.array([-logT[idx[int(q)]] for q in qs])
    main = Mq + 0.5 * np.log(f2 / (2 * np.pi)) - np.log(Sig)
    heur = Mq + 0.25 * np.log(qs) + 0.75 * np.log(np.log(qs)) + C0
    loc = -np.log(tq * np.log(qs) * Sig)
    rT = meas - main; rH = meas - heur
    slope, icpt = np.polyfit(loc, rH, 1)
    corr = np.corrcoef(loc, rH)[0, 1]
    print(f"   {len(Ns)} values of N; Thm 2.4 residual in [{rT.min():+.5f}, {rT.max():+.5f}]; heur residual in [{rH.min():+.4f}, {rH.max():+.4f}], sd {rH.std():.4f}")
    print(f"   regression of heur residual on -log(t_q log q Sigma_q): slope {slope:.4f}, intercept {icpt:+.4f}, corr {corr:.5f}")
    big = qs > 70000
    print(f"   sd of log(t_q log q Sigma_q) over q in [70000,1e5]: {loc[big].std():.4f} (notes 0.050); mean {(-loc[big]).mean():+.4f} (notes +0.0128)")
    np.savez("r_op3_data.npz", ps=ps, logd=logd, Ns=Ns, qs=qs, meas=meas, main=main, heur=heur, loc=loc)
