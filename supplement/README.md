# Supplementary computations

Computational checks accompanying the paper. `crossing_endpoint.py`,
`powers_check.py`, `bernstein_certificate.py` and the exact part of
`moment_certificate.py` are pure Python (exact rational arithmetic) and exit with
nonzero status on failure; the others are floating-point or high-precision
illustrations.

## `crossing_endpoint.py` — the elementary proof (Section 2)

Verifies the rational identities behind Lemma 2.2 (endpoint estimate),

    int_0^1 prod_{n=2}^5 (1-x^n) dx = 96601/180180
    int_0^1 x^6 prod_{n=2}^5 (1-x^n)/(1-x) dx = 275501/9699690
    => int_0^1 H - 1/2 >= 34619/4476780 > 0,

and the degree-18 Bernstein certificate (an alternative to Lemma 2.1, no longer
discussed in the paper).

    python3 crossing_endpoint.py

## `powers_check.py` — large-k failure (Open Problem 2)

Exact computation showing that for N = 9 the set A_9 = {4,5,6,7,9} has
smaller E Z^k than the primes for every k >= 126 (and not for k = 125),
while the primes are strictly minimal for k = 1, 2.

    python3 powers_check.py

## `bernstein_certificate.py` + `q16_bernstein.txt` — the cutoff-16 certificate (earlier version)

The computational route of an earlier version of the paper and of the earlier
`productinvariants` Lean artifact; no longer cited in the paper. `q16_bernstein.txt`
holds the 135 Bernstein coefficients of Q16 on [0,1], one exact rational
per line, lowest index first.
SHA-256: `29620d13046d5bb52a55d3d5d5f8c1b6adcb9d1a240eed08d4dd1b8ebe485bc6`

    python3 bernstein_certificate.py            # verify against shipped file
    python3 bernstein_certificate.py --write    # regenerate the file

Expected output ends with:

    all 135 Bernstein coefficients positive
    ...
    matches shipped q16_bernstein.txt: True
    sha256(q16_bernstein.txt) = 29620d13046d5bb52a55d3d5d5f8c1b6adcb9d1a240eed08d4dd1b8ebe485bc6

## `moment_certificate.py` — the moment certificate (Remark 4.4)

Exact: with R(x) = prod_{p in {3,5,7,11,13,17}} (1 - x^p),

    J_{17/8}(1) >= int_0^1 x^{9/8} R(x)(1 - x^2 - x^19) dx - 64/425 = 5.92057e-5 > 1/20000,
    J_3(1) <= -23/8580.

Floating point (numpy, optional): alpha_0 = 2.1431219183..., the threshold of the
bootstrap (prime minimality of E Z^k for k < 2 alpha_0).

    python3 moment_certificate.py

## `moments_search.py` — open problem 2, numerical evidence

Every maximal primitive subset of {2,...,N} (N = 12, 18, 24) against the primes, for
E min(Z^k, c^k) with k up to 20, in 40-digit arithmetic (requires mpmath). The primes win
in every case; this is evidence, not a proof.

    python3 moments_search.py [N ...]

## `tail_asymptotic_check.py` — tail asymptotics (Theorem 1.5, Open Problem 3)

Floating-point illustration, not a certificate (requires numpy, sympy).
Computes -log(J_n - Lambda) through the telescoped tail
J_n - Lambda = sum_{k>n} int_0^1 x^{p_k} prod_{q<p_k}(1-x^q) dx in log
space, and compares it with (2 pi/sqrt 3) sqrt n, 2 pi sqrt(N/(3 log N)) and
the Laplace value M_N = min_t [N t + Phi(t)] at N = p_n.

    python3 tail_asymptotic_check.py

## `next_prime_check.py` — next-prime form of the truncation error (Section 5.3, Open Problem 3)

Floating-point illustration, not a certificate (requires numpy, sympy).
For N = p_n, 20 <= n <= 9000, including the maximal gaps after 19609 and 31397,
it compares -log(J_n - Lambda) with M_N and with M_q, where q = p_{n+1}.
It reports the residual against the heuristic
M_q + 1/4 log q + 3/4 log log q - 1/2 log pi + 1/4 log(2 zeta(2)).
The residual lies in [-0.230, 0.105].

    python3 next_prime_check.py

All scripts may be run from any working directory; runtime is seconds.
