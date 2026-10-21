"""Self-contained verification of the running-positivity certificate.

Claim (Proposition `running positivity', key inequality): with
T0 = {2,...,16},

  D(c) := int_0^c prod_{n=2}^{16}(1-v^n) dv - Err16(c) - (c - c^2/2) > 0
  for 0 < c <= 1,  where
  Err16(c) = c^18/18 + c^19/19 - c^21/21 - c^22/22.

Certificate: D(c) = c^2 * Q(c) with deg Q = 134, and all 135 Bernstein
coefficients of Q on [0,1] are strictly positive; since the Bernstein
basis polynomials are nonnegative on [0,1] and positive on (0,1), this
proves Q > 0 on (0,1] (and Q(0) = beta_0 > 0), hence D > 0 on (0,1].

This script recomputes everything from scratch in exact rational
arithmetic (pure Python, no dependencies) and compares against the
shipped coefficient list q16_bernstein.txt, exiting with nonzero status
on any disagreement.  Pass --write to (re)generate the file instead.

Facts printed:
  * D = c^2 Q exactly, deg Q = 134
  * min Bernstein coefficient (exact and float) -- it equals D(1),
    i.e. the binding margin of the certificate is the endpoint c = 1
  * cutoff minimality: the same scheme with T0 = {2,...,15} FAILS at
    c = 1 (D_15(1) < 0), so 16 is the least admissible cutoff
"""
from fractions import Fraction
from math import comb
import hashlib
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CERT = os.path.join(HERE, "q16_bernstein.txt")


def mul_1_minus_xn(a, n):
    out = a + [Fraction(0)] * n
    for i in range(len(a) - 1, -1, -1):
        out[i + n] -= a[i]
    return out


def D_coeffs(K):
    P = [Fraction(1)]
    for n in range(2, K + 1):
        P = mul_1_minus_xn(P, n)
    D = [Fraction(0)] * (len(P) + K + 8)
    for j, cf in enumerate(P):
        D[j + 1] += Fraction(cf, j + 1)
    for e, s in ((K + 2, -1), (K + 3, -1), (K + 5, 1), (K + 6, 1)):
        D[e] += Fraction(s, e)
    D[1] -= 1
    D[2] += Fraction(1, 2)
    while D and D[-1] == 0:
        D.pop()
    return D


def main():
    # cutoff minimality
    D15 = D_coeffs(15)
    v15 = sum(D15)
    print(f"cutoff 15: D_15(1) = {float(v15):+.6e}  (fails: {v15 < 0})")

    D = D_coeffs(16)
    assert D[0] == 0 and D[1] == 0, "c^2 does not divide D"
    Q = D[2:]
    m = len(Q) - 1
    assert m == 134, m
    print(f"cutoff 16: D = c^2 Q, deg Q = {m}")

    betas = [sum(Fraction(comb(k, j), comb(m, j)) * Q[j]
                 for j in range(k + 1)) for k in range(m + 1)]
    assert all(b > 0 for b in betas), "certificate FAILS"
    mn = min(betas)
    print(f"all {m+1} Bernstein coefficients positive")
    print(f"min coefficient = {mn}")
    print(f"                = {float(mn):.12e}")
    print(f"min is attained at k = {betas.index(mn)} (endpoint c = 1):",
          mn == sum(D))

    payload = "\n".join(f"{b.numerator}/{b.denominator}" for b in betas) + "\n"
    if "--write" in sys.argv:
        with open(CERT, "w") as f:
            f.write(payload)
        print("wrote q16_bernstein.txt")
    else:
        with open(CERT, "rb") as f:
            shipped = f.read()
        ok = shipped == payload.encode()
        print("matches shipped q16_bernstein.txt:", ok)
        if not ok:
            sys.exit("FAIL: shipped coefficient list disagrees with recomputation")
    # canonical checksum: SHA-256 of the distributed file's exact bytes
    with open(CERT, "rb") as f:
        sha = hashlib.sha256(f.read()).hexdigest()
    print(f"sha256(q16_bernstein.txt) = {sha}")


if __name__ == "__main__":
    main()
