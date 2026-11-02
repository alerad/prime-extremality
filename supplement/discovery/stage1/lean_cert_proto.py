#!/usr/bin/env python3
"""Prototype of the Lean-checkable sign-pattern certificate (cost estimate only).

For h with h(0) > 0 > h(1) and one root in (0,1): find rationals a < b with
  h > 0 on [0,a],  h < 0 on [b,1],  h' < 0 on [a,b]
each proved by the Taylor-bound bisection test:
  on [l, r] write p(l + (r-l) t) = sum c_i t^i (t in [0,1]); positive if c_0 + sum_{c_i<0} c_i > 0.
Integer arithmetic: scaled coefficients, bisection by t -> t/2 and t -> (1+t)/2.
"""
import json, sys, time
from math import gcd
from functools import reduce
from fractions import Fraction as Fr
import numpy as np
sys.path.insert(0, '.')
from cert_lib import P_of, padd, strip_u_and_one_minus_u


def content_div(c):
    g = reduce(gcd, (abs(x) for x in c if x), 0)
    return [x // g for x in c] if g > 1 else c


def taylor1(c):
    """coefficients of p(1 + t) from those of p(t) (additions only)."""
    c = list(c)
    n = len(c)
    for i in range(n - 1):
        for j in range(n - 2, i - 1, -1):
            c[j] += c[j + 1]
    return c


def halves(c):
    n = len(c) - 1
    left = [x * (1 << (n - i)) for i, x in enumerate(c)]       # 2^n p(t/2)
    right = taylor1(left)                                       # 2^n p((1+t)/2)
    return content_div(left), content_div(right)


def pos_unit(c, depth, stats):
    """p(t) > 0 on [0,1]?  c integer coefficients of p on the current subinterval."""
    stats['nodes'] += 1
    if c[0] + sum(x for x in c[1:] if x < 0) > 0:
        return True
    if depth == 0:
        return False
    l, r = halves(c)
    return pos_unit(l, depth - 1, stats) and pos_unit(r, depth - 1, stats)


def restrict(h, a, b):
    """integer coefficients (up to a positive factor) of h(a + (b-a) t), a,b rational."""
    # p(x) with x = a + w t: Taylor shift by a then scale by w; do it in Fractions then clear
    n = len(h) - 1
    c = [Fr(x) for x in h]
    for i in range(n):                      # shift by a
        for j in range(n - 1, i - 1, -1):
            c[j] += a * c[j + 1]
    w = b - a
    c = [x * w ** i for i, x in enumerate(c)]
    L = reduce(lambda x, y: x * y // gcd(x, y), (x.denominator for x in c), 1)
    return content_div([int(x * L) for x in c])


def deriv(h):
    return [i * h[i] for i in range(1, len(h))]


def sign_pattern_cert(h, depth=40):
    hf = np.array([float(x) for x in h])
    roots = np.roots(hf[::-1])
    rr = sorted(r.real for r in roots if abs(r.imag) < 1e-9 and 0 < r.real < 1)
    st = {'nodes': 0}
    if not rr:
        ok = pos_unit(content_div(list(h)), depth, st)
        return ok, st['nodes'], None
    x = rr[0]
    for delta in (1e-3, 1e-4, 1e-5, 1e-6):
        a = Fr(x - delta).limit_denominator(10 ** 9)
        b = Fr(x + delta).limit_denominator(10 ** 9)
        st = {'nodes': 0}
        ok1 = pos_unit(restrict(h, Fr(0), a), depth, st)
        ok2 = pos_unit([-v for v in restrict(h, b, Fr(1))], depth, st)
        ok3 = pos_unit([-v for v in restrict(deriv(h), a, b)], depth, st)
        if ok1 and ok2 and ok3:
            return True, st['nodes'], (float(a), float(b))
    return False, st['nodes'], None


if __name__ == "__main__":
    R = (2, 3, 5, 7)
    lim = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 9
    t0 = time.time()
    tot = 0; worst = 0; fails = []
    n = 0
    for line in open('cert_stage3_log.jsonl'):
        r = json.loads(line)
        kind = r['task'][0]
        if kind == 'merged_explicit':
            D = padd(P_of(r['task'][1]), P_of(R), 1, -1)
        elif kind == 'single_explicit':
            D = padd(P_of(r['task'][2]), np.array([1, -1], dtype=object), 1, -1)
        elif kind == 'small_N':
            N, A = r['task'][1], r['task'][2]
            D = padd(P_of(A), P_of([q for q in (2, 3, 5) if q <= N]), 1, -1)
        else:
            continue
        s = strip_u_and_one_minus_u(D)
        if s is None:
            continue
        a, b, h = s
        ok, nodes, br = sign_pattern_cert(h)
        n += 1
        tot += nodes; worst = max(worst, nodes)
        if not ok:
            fails.append(r['task'])
        if n >= lim:
            break
    print(f"cases {n}, total nodes {tot}, worst {worst}, fails {len(fails)}, {time.time()-t0:.1f}s")
    print(fails[:5])
