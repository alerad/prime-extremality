#!/usr/bin/env python3
"""Exact re-verification of ALL explicit cases of Proposition prop:cert with my own code.

For every case two independent criteria are evaluated (both exact):
 (A) sign pattern of D on (0,1) (own Descartes/VCA isolation) and exact R_126(1) of g = W*D
     (Fraction summation) -- the paper's SC certificate;
 (B) direct decision that R_126(y) = int_0^y 126 u^125 g du > 0 for EVERY y in (0,1]
     (root-freeness of the running-integral polynomial).  By [P, Lemma 3.1] with the
     nonincreasing weight (k/126) u^(k-126) this gives the condition for every 0 < k <= 126
     without any single-crossing argument.
Weights: merged S: primes in [11, max S]; single T: primes in (p, min(p max T, cap)],
caps tried 2p, 3p, 6p, 12p, full (any subset of (p, p max T] is allowed by Lemma lem:wexch).
"""
import json, os, sys, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rv_common import (P_poly, primes_open_closed, sign_pattern, RK1_exact, running_integral_positive,
                       is_prime, RSET, A9, progress)
import flint

HERE = os.path.dirname(os.path.abspath(__file__))
K = 126


def work(task):
    kind = task[0]
    t0 = time.time()
    if kind == "merged":
        S = tuple(task[1])
        D = P_poly(S) - P_poly(RSET)
        sp_ = sign_pattern(D)
        W = P_poly(primes_open_closed(10, max(S)))
        g = W * D
        out = {"kind": kind, "S": S, "sign": sp_}
        if S == A9:
            out["A9"] = True
            out["R(125.84)"] = float(RK1_exact(g, __import__("fractions").Fraction(12584, 100)))
            out["R(125.85)"] = float(RK1_exact(g, __import__("fractions").Fraction(12585, 100)))
            return out
        r1 = RK1_exact(g, K)
        okB, r1b = running_integral_positive(g, K)
        assert r1 == r1b
        out.update({"R1": float(r1), "A_ok": sp_ == "pos" or (sp_ == "single+-" and r1 > 0) or sp_ == "zero",
                    "B_ok": okB or sp_ == "zero", "t": time.time() - t0})
        return out
    if kind == "single":
        p, T = task[1], tuple(task[2])
        ET = P_poly(T) - flint.fmpz_poly([1, -1])          # P_T(v) - (1 - v)
        spv = sign_pattern(ET)
        D = P_poly(T, scale=p) - P_poly([p])               # P_T(u^p) - (1 - u^p)
        spu = sign_pattern(D)
        out = {"kind": kind, "p": p, "T": T, "sign_v": spv, "sign_u": spu}
        for cap in (2 * p, 3 * p, 6 * p, 12 * p, 10 ** 9):
            Q = primes_open_closed(p, min(p * max(T), cap))
            g = P_poly(Q) * D
            okB, r1 = running_integral_positive(g, K)
            if okB:
                break
        out.update({"cap": cap, "nQ": len(Q), "Qmax": max(Q) if Q else None, "R1": float(r1),
                    "A_ok": spu == "pos" or (spu == "single+-" and r1 > 0), "B_ok": okB,
                    "Q_valid": all(p < q <= p * max(T) and is_prime(q) for q in Q),
                    "t": time.time() - t0})
        return out
    if kind == "small":
        N, A = task[1], tuple(task[2])
        PN = [q for q in range(2, N + 1) if is_prime(q)]
        D = P_poly(A) - P_poly(PN)
        sp_ = sign_pattern(D)
        if sp_ == "zero":
            return {"kind": kind, "N": N, "A": A, "sign": sp_, "A_ok": True, "B_ok": True}
        r1 = RK1_exact(D, K)
        okB, _ = running_integral_positive(D, K)
        return {"kind": kind, "N": N, "A": A, "sign": sp_, "R1": float(r1),
                "A_ok": sp_ == "pos" or (sp_ == "single+-" and r1 > 0), "B_ok": okB}


if __name__ == "__main__":
    cases = json.load(open(os.path.join(HERE, "rv_cases.json")))
    tasks = [("merged", S) for S in cases["merged_explicit"]] + \
            [("single", p, T) for p, T in cases["single_explicit"]] + \
            [("small", N, A) for N, A in cases["small_N"]]
    print("tasks:", len(tasks), flush=True)
    res = []
    t0 = time.time()
    with Pool(16) as pool:
        for i, r in enumerate(pool.imap_unordered(work, tasks, chunksize=2)):
            res.append(r)
            progress(i + 1, len(tasks), "explicit", "case")
    with open(os.path.join(HERE, "rv_explicit_results.jsonl"), "w") as f:
        for r in res:
            f.write(json.dumps(r) + "\n")
    print(f"done in {time.time() - t0:.0f}s")
    for kind in ("merged", "single", "small"):
        rs = [r for r in res if r["kind"] == kind and not r.get("A9")]
        from collections import Counter
        print(kind, len(rs), "A_ok:", sum(r["A_ok"] for r in rs), "B_ok:", sum(r["B_ok"] for r in rs),
              "signs:", dict(Counter(r.get("sign", r.get("sign_u")) for r in rs)))
        vals = [r["R1"] for r in rs if "R1" in r and r.get("sign", r.get("sign_u")) != "pos"]
        if vals:
            m = min(vals)
            arg = [r for r in rs if r.get("R1") == m][0]
            print("   min R_126(1) over single-crossing cases:", m, {k: arg[k] for k in arg if k in ("S", "T", "p", "A", "N")})
        bad = [r for r in rs if not (r["A_ok"] and r["B_ok"])]
        for r in bad[:20]:
            print("   FAIL:", r)
    singles = [r for r in res if r["kind"] == "single"]
    print("single: sign_v == sign_u for all:", all(r["sign_v"] == r["sign_u"] for r in singles),
          " Q valid for all:", all(r["Q_valid"] for r in singles))
    from collections import Counter
    print("single caps used:", dict(Counter(r["cap"] for r in singles)))
    a9 = [r for r in res if r.get("A9")]
    print("A9:", a9)
