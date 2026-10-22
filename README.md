# Prime extremality for product integrals over primitive sets

[![Lean build](https://github.com/alerad/prime-extremality/actions/workflows/lean.yml/badge.svg)](https://github.com/alerad/prime-extremality/actions/workflows/lean.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23537235.svg)](https://doi.org/10.5281/zenodo.23537235)

Paper ([`main.tex`](main.tex), [`main.pdf`](main.pdf)) and its Lean 4 formalization
([`lean/`](lean)) by Alejandro Radisic
([ORCID 0009-0001-7612-1082](https://orcid.org/0009-0001-7612-1082)).

Among primitive sets `A ⊆ {2, 3, …}`, the primes uniquely minimize
`F_c(A) = ∫₀ᶜ ∏_{n∈A} (1 − xⁿ) dx` for every `c ∈ (0, 1]`. The paper also gives the
limiting value `Λ = 0.5506530112…` and the asymptotics of the truncation error.

## Formal verification

On every push, CI builds the whole development from scratch against pinned public
dependencies and then runs [`lean/scripts/check-axioms.sh`](lean/scripts/check-axioms.sh).
The check fails if

- any declaration in `RntPaper.*` depends on `sorryAx`,
- the development declares an axiom of its own, or
- a paper result uses an axiom other than `propext`, `Classical.choice` and `Quot.sound`.
  The two finite computations done with `native_decide` (the digits of `Λ` and the
  `k = 126` comparison) are the exceptions and may also use `Lean.ofReduceBool` and
  `Lean.trustCompiler`.

The PrimeNumberTheoremAnd dependency contains `sorry`s in parts the development does not
use. The audit checks every declaration, so it shows that none of them reach these results.

Dependencies: Lean `v4.35.0`, Mathlib `56a00585`,
[LeanCert](https://github.com/alerad/leancert) `d3e7f686`,
[leancert-qproduct](https://github.com/alerad/leancert-qproduct) `4ce87955`, and
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
`127b50e3` (unmodified).

To reproduce:

```sh
cd lean
lake exe cache get        # prebuilt Mathlib
lake build                # every module, including the PNT bridges
./scripts/check-axioms.sh
```

[`lean/README.md`](lean/README.md) maps every paper result to its Lean declaration.
The numerical scripts cited in the paper are in [`supplement/`](supplement).
