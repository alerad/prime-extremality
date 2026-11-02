#!/usr/bin/env python3
"""Independent exact re-check of every LOGGED V1 certificate (single_tail, merged_tail_compat).

From the log entry only (u1, N2 or cap) the certificate data are rebuilt with my own code and:
 (1) c u1^(p B) < 1 with c = 1/(1-u1^p);
 (2) H(u) = L(u^p) - T(u) >= 0 on [0,u1], L(v) = P_M(v)(1 - c v^B), proven by exact root counting
     of the stripped polynomial on (0,u1) (instead of the psi bound + monotone partition);
 (3) lhs = int_0^u1 K u^(K-1) W H  >  rhs = int_u1^1 K u^(K-1) W T, exact Fractions; compared with
     the logged floats.
"""
import json, os, sys, time
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import flint
from rv_common import (P_poly, coeffs, count_roots_01, smooth_list, is_prime, primes_open_closed,
                       RSET, progress)

HERE = os.path.dirname(os.path.abspath(__file__))
K = 126


def exact_partial(poly_c, x):
    """(int_0^x K u^(K-1) f, int_0^1 K u^(K-1) f) for integer coefficient list poly_c, x rational.
    F(u) = sum_n c_n K/(K+n) u^n as flint fmpq_poly; int_0^x = x^K F(x)."""
    F = flint.fmpq_poly([flint.fmpq(c * K, K + n) for n, c in enumerate(poly_c)])
    xq = flint.fmpq(x.numerator, x.denominator)
    lo = (xq ** K) * F(xq)
    tot = F(flint.fmpq(1))
    return Fr(int(lo.p), int(lo.q)), Fr(int(tot.p), int(tot.q))


def nonneg_on_0_x(H, x):
    """exact: H >= 0 on [0,x] (x rational in (0,1))."""
    c = coeffs(H)
    a = next(i for i, v in enumerate(c) if v)
    h = c[a:]
    if h[0] <= 0:
        return False
    num, den = x.numerator, x.denominator
    deg = len(h) - 1
    ht = flint.fmpz_poly([h[j] * num ** j * den ** (deg - j) for j in range(deg + 1)])   # den^deg h(x t)
    if int(ht(1)) < 0:
        return False
    if int(ht(1)) == 0:
        return False      # conservative
    return count_roots_01(ht) == 0


def work(rec):
    task = rec["task"]
    kind = task[0]
    u1 = Fr(rec["u1"])
    if kind == "merged_tail_compat":
        Rp, A0 = tuple(task[1]), tuple(task[2])
        R0 = [r for r in RSET if r not in Rp]
        N2 = rec["N2"]
        Cs = [n for n in smooth_list(Rp, 24, N2 - 1) if not is_prime(n) and not any(n % a == 0 for a in A0)]
        M = list(A0) + Cs
        B, p, target = N2, 1, list(Rp)
        W = P_poly(R0 + [q for q in range(11, 65) if is_prime(q)])
    else:
        p, mp, B, M = task[1], task[2], task[3], list(task[4])
        cap = rec["cap"]
        target = [p]
        W = P_poly(primes_open_closed(p, min(p * mp, cap)))
    v1 = u1 ** p
    c = 1 / (1 - v1)
    ok1 = c * v1 ** B < 1
    # integer form: dn*H = P_M(u^p) (dn - dd u^(pB)) - dn T(u), dn/dd = 1 - v1
    dn = u1.denominator ** p - u1.numerator ** p
    dd = u1.denominator ** p
    PM = P_poly(M, scale=p)
    Lpart = PM * flint.fmpz_poly([dn] + [0] * (p * B - 1) + [-dd])
    T = P_poly(target)
    Hs = Lpart - dn * T                    # = dn * H
    ok2 = nonneg_on_0_x(Hs, u1)
    lo, _ = exact_partial(coeffs(W * Hs), u1)
    lhs = lo / dn
    loT, totT = exact_partial(coeffs(W * T), u1)
    rhs = totT - loT
    ok3 = lhs > rhs
    return {"task": task, "ok": bool(ok1 and ok2 and ok3), "ok1": ok1, "ok2": ok2, "ok3": ok3,
            "lhs": float(lhs), "rhs": float(rhs), "log_lhs": rec["lhs"], "log_rhs": rec["rhs"]}


if __name__ == "__main__":
    from multiprocessing import Pool
    logs = [json.loads(l) for f in ("cert_part1_log.jsonl", "cert_part2_log.jsonl")
            for l in open(os.path.join(HERE, "..", "stage1", f))]
    recs = [r for r in logs if r.get("type") == "V1"]
    if len(sys.argv) > 1:
        recs = recs[:int(sys.argv[1])]
    print("V1 certificates:", len(recs), flush=True)
    res = []
    t0 = time.time()
    with Pool(int(os.environ.get("JOBS", 16))) as pool:
        for i, r in enumerate(pool.imap_unordered(work, recs, chunksize=1)):
            res.append(r)
            if not r["ok"]:
                print("FAIL:", r, flush=True)
            progress(i + 1, len(recs), "v1-recheck", "certificate")
    with open(os.path.join(HERE, "rv_v1_recheck.jsonl"), "w") as f:
        for r in res:
            f.write(json.dumps(r) + "\n")
    dev = max(max(abs(r["lhs"] - r["log_lhs"]) / abs(r["lhs"]), abs(r["rhs"] - r["log_rhs"]) / abs(r["rhs"]))
              for r in res)
    print(f"done in {time.time()-t0:.0f}s: {sum(r['ok'] for r in res)}/{len(res)} ok; "
          f"max rel deviation from logged lhs/rhs = {dev:.2e}")
