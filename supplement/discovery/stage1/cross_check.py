#!/usr/bin/env python3
"""Independent cross-check of logged exact certificate values by mpmath quadrature.
The integrands are rebuilt here from the task description only (products evaluated directly)."""
import json, random
import mpmath as mp
from sympy import primerange
mp.mp.dps = 40
K = 126
R = (2, 3, 5, 7)
def P(exps, x):
    v = mp.mpf(1)
    for e in exps:
        v *= 1 - x**e
    return v
def quad01(f, a=0, b=1):
    pts = [a] + [a + (b - a) * t for t in (0.5, 0.8, 0.9, 0.95, 0.97, 0.98, 0.99, 0.995, 0.999)] + [b]
    return mp.quad(f, pts)
logs = [json.loads(l) for l in open("cert_part1_log.jsonl")] + [json.loads(l) for l in open("cert_part2_log.jsonl")]
random.seed(1)
me = [r for r in logs if r['task'][0] == 'merged_explicit' and 'R_K(1)' in r]
se = [r for r in logs if r['task'][0] == 'single_explicit' and 'R_K(1)' in r]
worst = 0
for r in random.sample(me, 25) + sorted(me, key=lambda r: r['R_K(1)'])[:5]:
    S = r['task'][1]
    W = list(primerange(11, max(S) + 1))
    val = quad01(lambda u: K * u**(K - 1) * P(W, u) * (P(S, u) - P(R, u)))
    rel = abs(val - r['R_K(1)']) / abs(r['R_K(1)'])
    worst = max(worst, rel)
print(f"merged_explicit: 30 values, max relative deviation exact vs quadrature = {float(worst):.2e}")
worst = 0
for r in random.sample(se, 25):
    p, T = r['task'][1], r['task'][2]
    Wp = list(primerange(p + 1, 10**6))[:r['weight_primes']]
    val = quad01(lambda u: K * u**(K - 1) * P(Wp, u) * (P(T, u**p) - (1 - u**p)))
    rel = abs(val - r['R_K(1)']) / abs(r['R_K(1)'])
    worst = max(worst, rel)
print(f"single_explicit: 25 values, max relative deviation = {float(worst):.2e}")
# V1 tails: recompute lhs = int_0^u1 K u^(K-1) W (L - T) and rhs = int_u1^1 K u^(K-1) W T
from fractions import Fraction as Fr
import cert_stage3 as cs
mt = [r for r in logs if r['task'][0] == 'merged_tail_compat']
kinds = {}
for r in mt: kinds[r['type']] = kinds.get(r['type'], 0) + 1
print("merged_tail_compat types:", kinds)
worst = 0
v1s = [r for r in mt if r['type'] == 'V1']
for r in random.sample(v1s, min(15, len(v1s))):
    Rp, A = tuple(r['task'][1]), tuple(r['task'][2])
    R0 = [x for x in R if x not in Rp]
    comps = [n for n in cs.smooth(Rp, 4, 10**6) if n not in Rp]
    C = [n for n in comps if n >= 24 and not any(n % a == 0 for a in A)]
    N2 = r['N2']; u1 = mp.mpf(Fr(r['u1']).numerator) / Fr(r['u1']).denominator
    M = list(A) + [n for n in C if n < N2]
    W = R0 + list(primerange(11, 65))
    c = 1 / (1 - u1)
    lhs = quad01(lambda u: K * u**(K-1) * P(W, u) * (P(M, u) * (1 - c * u**N2) - P(Rp, u)), 0, u1)
    rhs = mp.quad(lambda u: K * u**(K-1) * P(W, u) * P(Rp, u), [u1, (1 + u1) / 2, 1])
    worst = max(worst, abs(lhs - r['lhs']) / abs(r['lhs']), abs(rhs - r['rhs']) / abs(r['rhs']))
print(f"merged V1 tails: 15 certificates, max relative deviation of lhs/rhs = {float(worst):.2e}")
st = [r for r in logs if r['task'][0] == 'single_tail']
worst = 0
for r in random.sample(st, 12):
    p, mp_, B, Msm = r['task'][1], r['task'][2], r['task'][3], r['task'][4]
    cap = r['cap']; u1 = mp.mpf(Fr(r['u1']).numerator) / Fr(r['u1']).denominator
    Wp = list(primerange(p + 1, min(p * mp_, cap) + 1))
    v1 = u1**p; c = 1 / (1 - v1)
    lhs = quad01(lambda u: K * u**(K-1) * P(Wp, u) * (P(Msm, u**p) * (1 - c * u**(p * B)) - (1 - u**p)), 0, u1)
    rhs = mp.quad(lambda u: K * u**(K-1) * P(Wp, u) * (1 - u**p), [u1, (1 + u1) / 2, 1])
    worst = max(worst, abs(lhs - r['lhs']) / abs(r['lhs']), abs(rhs - r['rhs']) / abs(r['rhs']))
print(f"single V1 tails: 12 certificates, max relative deviation of lhs/rhs = {float(worst):.2e}")
