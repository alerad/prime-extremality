"""Independent helpers for the second review (do NOT import cert_lib / cert_stage3).

Number theory by trial division / sieve, antichain enumeration by Bron-Kerbosch on the
incomparability graph (bitsets), exact polynomials via python-flint fmpz_poly.
"""
import json, sys, time
from fractions import Fraction as Fr

import flint

K126 = 126
RSET = (2, 3, 5, 7)
A9 = (4, 5, 6, 7, 9)


# ---------------------------------------------------------------- number theory
def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


_PR = sieve(200000)
_PRSET = set(_PR)


def is_prime(n):
    return n in _PRSET


def primes_open_closed(lo, hi):
    """primes q with lo < q <= hi"""
    return [q for q in _PR if lo < q <= hi]


def largest_prime_factor(n):
    best, m, d = 1, n, 2
    while d * d <= m:
        while m % d == 0:
            best, m = d, m // d
        d += 1
    if m > 1:
        best = max(best, m)
    return best


def is_smooth_by(n, primes):
    for q in primes:
        while n % q == 0:
            n //= q
    return n == 1


def smooth_list(primes, lo, hi):
    """integers in [lo,hi] all of whose prime factors lie in `primes` (trial division)."""
    return [n for n in range(max(lo, 2), hi + 1) if is_smooth_by(n, primes)]


# ---------------------------------------------------------------- antichains (Bron-Kerbosch)
def _incomp_masks(V):
    n = len(V)
    nb = [0] * n
    for i in range(n):
        for j in range(n):
            if i != j and V[i] % V[j] != 0 and V[j] % V[i] != 0:
                nb[i] |= 1 << j
    return nb


def maximal_antichains(V):
    """all maximal antichains (divisibility) of the finite set V, as sorted tuples."""
    V = sorted(V)
    nb = _incomp_masks(V)
    out = []

    def bk(Rm, Pm, Xm):
        if Pm == 0 and Xm == 0:
            out.append(tuple(V[i] for i in range(len(V)) if Rm >> i & 1))
            return
        # pivot maximizing |P & N(u)|
        PX = Pm | Xm
        best, bu = -1, None
        t = PX
        while t:
            b = t & -t
            i = b.bit_length() - 1
            c = bin(Pm & nb[i]).count("1")
            if c > best:
                best, bu = c, i
            t ^= b
        cand = Pm & ~nb[bu]
        while cand:
            b = cand & -cand
            i = b.bit_length() - 1
            bk(Rm | b, Pm & nb[i], Xm & nb[i])
            Pm &= ~b
            Xm |= b
            cand ^= b

    bk(0, (1 << len(V)) - 1, 0)
    return out


def all_antichains(V):
    """all antichains of V including the empty one."""
    V = sorted(V)
    nb = _incomp_masks(V)
    out = []

    def rec(start, Rm, Pm):
        out.append(tuple(V[i] for i in range(len(V)) if Rm >> i & 1))
        for i in range(start, len(V)):
            if Pm >> i & 1:
                rec(i + 1, Rm | (1 << i), Pm & nb[i])

    rec(0, 0, (1 << len(V)) - 1)
    return out


def is_antichain(S):
    S = list(S)
    return all(not (a % b == 0 or b % a == 0) for i, a in enumerate(S) for b in S[i + 1:])


# ---------------------------------------------------------------- exact polynomials (flint)
X = flint.fmpz_poly([0, 1])
ONE = flint.fmpz_poly([1])


def one_minus_pow(e):
    c = [0] * (e + 1)
    c[0] = 1
    c[e] = -1
    return flint.fmpz_poly(c)


def P_poly(exps, scale=1):
    """prod (1 - u^(scale*e)) as fmpz_poly (product tree for speed)."""
    fs = [one_minus_pow(scale * e) for e in exps]
    if not fs:
        return ONE
    while len(fs) > 1:
        nxt = []
        for i in range(0, len(fs), 2):
            nxt.append(fs[i] * fs[i + 1] if i + 1 < len(fs) else fs[i])
        fs = nxt
    return fs[0]


def coeffs(p):
    return [int(c) for c in p.coeffs()]


def strip_u_1mu(p):
    """p = u^a (1-u)^b h with h(0) != 0 != h(1).  Returns (a, b, h) or None if p == 0."""
    if p == 0:
        return None
    c = coeffs(p)
    a = next(i for i, x in enumerate(c) if x != 0)
    h = flint.fmpz_poly(c[a:])
    b = 0
    om = flint.fmpz_poly([1, -1])
    while int(h(1)) == 0:
        q, r = divmod(h, om)
        assert r == 0
        h = q
        b += 1
    return a, b, h


def _variations(cs):
    s = [c for c in cs if c != 0]
    return sum(1 for i in range(len(s) - 1) if (s[i] > 0) != (s[i + 1] > 0))


def descartes_01(h):
    """sign variations of (1+x)^n h(1/(1+x)): bound (same parity) on #roots of h in (0,1)."""
    c = coeffs(h)
    n = len(c) - 1
    rev = flint.fmpz_poly(list(reversed(c)))       # u^n h(1/u)
    shifted = rev(flint.fmpz_poly([1, 1]))          # rev(1+x)
    return _variations(coeffs(shifted))


def count_roots_01(h, depth=0, maxdepth=60):
    """exact number of DISTINCT roots of integer poly h in the open interval (0,1).
    Square-free part, then Descartes bisection (Vincent-Collins-Akritas)."""
    if h.degree() <= 0:
        return 0
    g = flint.fmpz_poly.gcd(h, h.derivative())
    if g.degree() > 0:
        h = h // g
    return _vca(h, 0, maxdepth)


def _vca(h, depth, maxdepth):
    if h.degree() <= 0:
        return 0
    v = descartes_01(h)
    if v == 0:
        return 0
    if v == 1:
        return 1
    if depth >= maxdepth:
        raise RuntimeError("VCA depth exceeded")
    n = h.degree()
    c = coeffs(h)
    # left half: H_L(u) = 2^n h(u/2) ; right half: H_R(u) = 2^n h((u+1)/2)
    HL = flint.fmpz_poly([c[j] * (1 << (n - j)) for j in range(n + 1)])
    HR = HL(flint.fmpz_poly([1, 1]))
    mid = 1 if int(HL(1)) == 0 else 0           # h(1/2) == 0 ?
    return _vca(HL, depth + 1, maxdepth) + _vca(HR, depth + 1, maxdepth) + mid


def sign_pattern(p):
    """classify a polynomial on (0,1): 'zero', 'pos' (>0 on (0,1)), 'single+-' (exactly one sign
    change, from + to -), or 'other:<n roots>,<h0>,<h1>'.  Exact."""
    r = strip_u_1mu(p)
    if r is None:
        return "zero"
    a, b, h = r
    h0, h1 = int(h(0)), int(h(1))
    n = count_roots_01(h)
    if n == 0 and h0 > 0 and h1 > 0:
        return "pos"
    if n == 1 and h0 > 0 and h1 < 0:
        return "single+-"
    return f"other:{n},{h0 > 0},{h1 > 0}"


def RK1_exact(g, K):
    """exact sum_n g_n K/(K+n) as a Fraction (Fraction arithmetic, independent of the lcm trick)."""
    K = Fr(K)
    tot = Fr(0)
    for n, gn in enumerate(coeffs(g)):
        if gn:
            tot += Fr(gn) * K / (K + n)
    return tot


def running_integral_positive(g, K):
    """Decide exactly whether R_K(y) = int_0^y K u^(K-1) g(u) du > 0 for ALL y in (0,1], integer K.
    R_K(y) = y^K * r(y), r(y) = sum g_n K/(K+n) y^n.  Strip y^a, check r(1) > 0, leading coeff > 0
    and that r has no root in (0,1).  Returns (bool, r(1) as Fraction)."""
    c = coeffs(g)
    idx = [n for n, x in enumerate(c) if x]
    if not idx:
        return False, Fr(0)
    from math import lcm
    from functools import reduce
    L = reduce(lcm, [K + n for n in idx], 1)
    rc = [0] * (idx[-1] + 1)
    for n in idx:
        rc[n] = c[n] * (L // (K + n))          # r(y) * L / K, integer coefficients
    a = idx[0]
    s = flint.fmpz_poly(rc[a:])                  # r(y) = (K/L) y^a s(y)
    s0, s1 = int(s(0)), int(s(1))
    r1 = Fr(s1 * K, L)
    if s0 <= 0 or s1 <= 0:
        return False, r1
    n = count_roots_01(s)
    return n == 0, r1


def progress(done, total, phase, unit, _state={"t": 0.0}):
    t = time.time()
    if t - _state["t"] >= 1.0 or done == total:
        _state["t"] = t
        print("ANVIL_PROGRESS " + json.dumps({"done": done, "total": total, "phase": phase,
                                               "unit": unit}, separators=(",", ":")), flush=True)
