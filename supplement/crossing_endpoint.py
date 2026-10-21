"""Exact rational checks for Section 2 of the paper (the elementary proof
of the universal product inequality) and for Remark 2.4.

Checks, all in exact arithmetic (pure Python, no dependencies):

  * P5(x) = prod_{n=2}^{5} (1-x^n) has the stated monomial expansion, and
    P5(x)/(1-x) = (1+x)(1-x^3)(1-x^4)(1-x^5) likewise.
  * int_0^1 P5 = 96601/180180,  int_0^1 x^6 P5/(1-x) = 275501/9699690,
    hence int_0^1 H - 1/2 >= 34619/4476780 > 0  (Lemma 2.2).
  * Remark 2.4: D~(c) = int_0^c P5 (1 - x^6/(1-x)) dx - (c - c^2/2)
    equals c^2 Q~(c) with deg Q~ = 18 and all 19 Bernstein coefficients
    of Q~ on [0,1] positive, the least being 34619/4476780.

Exit status is nonzero if any check fails.
"""
from fractions import Fraction as Fr
from math import comb
import sys


def mul(a, b):
    r = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def poly(d):
    r = [Fr(0)] * (max(d) + 1)
    for k, v in d.items():
        r[k] = Fr(v)
    return r


def integral01(p, shift=0):
    """int_0^1 x^shift p(x) dx"""
    return sum(c / (k + shift + 1) for k, c in enumerate(p))


def main():
    P5 = poly({0: 1})
    for n in (2, 3, 4, 5):
        P5 = mul(P5, poly({0: 1, n: -1}))
    expected = {0: 1, 2: -1, 3: -1, 4: -1, 6: 1, 7: 2, 8: 1,
                10: -1, 11: -1, 12: -1, 14: 1}
    assert {k: int(c) for k, c in enumerate(P5) if c} == expected, "P5 expansion"

    R = poly({0: 1, 1: 1})  # (1+x)(1-x^3)(1-x^4)(1-x^5) = P5/(1-x)
    for n in (3, 4, 5):
        R = mul(R, poly({0: 1, n: -1}))
    assert mul(R, poly({0: 1, 1: -1})) == P5 + [Fr(0)] * (len(R) + 1 - len(P5)), "P5/(1-x)"
    expR = {0: 1, 1: 1, 3: -1, 4: -2, 5: -2, 6: -1, 7: 1, 8: 2, 9: 2,
            10: 1, 12: -1, 13: -1}
    assert {k: int(c) for k, c in enumerate(R) if c} == expR, "R expansion"

    I1 = integral01(P5)
    I2 = integral01(R, shift=6)
    assert I1 == Fr(96601, 180180), I1
    assert I2 == Fr(275501, 9699690), I2
    margin = I1 - I2 - Fr(1, 2)
    assert margin == Fr(34619, 4476780), margin
    print(f"int_0^1 P5           = {I1}")
    print(f"int_0^1 x^6 P5/(1-x) = {I2}")
    print(f"endpoint margin      = {margin} = {float(margin):.6e} > 0: {margin > 0}")

    # Remark 2.4: degree-18 Bernstein certificate
    bound = mul(R, poly({0: 1, 1: -1, 6: -1}))  # (1+x)(1-x^3)(1-x^4)(1-x^5)(1-x-x^6)
    D = [Fr(0)] * (len(bound) + 1)
    for k, c in enumerate(bound):
        D[k + 1] += c / (k + 1)
    D[1] -= 1
    D[2] += Fr(1, 2)
    assert D[0] == 0 and D[1] == 0, "c^2 does not divide D~"
    Q = D[2:]
    m = len(Q) - 1
    assert m == 18, m
    betas = [sum(Fr(comb(k, j), comb(m, j)) * Q[j] for j in range(k + 1))
             for k in range(m + 1)]
    assert all(b > 0 for b in betas), "Bernstein certificate FAILS"
    assert min(betas) == Fr(34619, 4476780)
    print(f"deg Q~ = {m}; all {m+1} Bernstein coefficients positive; "
          f"min = {min(betas)}")
    print("all checks passed")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as e:
        sys.exit(f"FAIL: {e}")
