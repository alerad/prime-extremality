import RntPaper.Basic
import LeanCert.Validity

/-!
# The constant `Λ` (paper §5.2, Appendix A.2)

`Λ = 𝓛(1) = primeLambda` (`Lfun_one_eq_primeLambda`).  LeanCert already
provides the qualitative facts and a directed-limit certificate; the 26-digit
sandwich is evaluated by LeanCert's sparse `QPoly` product integrals
(`QProduct.LeanCert.Sparse`), the linear-time replacement for the powerset
`finiteIntegralRat`.
-/

namespace RntPaper

open QProduct

/-- `Λ > 1/2` (LeanCert). -/
theorem primeLambda_gt_half' : (1 : ℝ) / 2 < primeLambda := primeLambda_gt_half

/-- A coarse machine-checked enclosure from LeanCert's directed-limit certificate. -/
theorem primeLambda_coarse :
    ((19 / 36 : ℚ) : ℝ) ≤ primeLambda ∧ primeLambda ≤ ((7 / 12 : ℚ) : ℝ) :=
  LeanCert.Validity.verify_limit_interval
    primeLambda_le_shiftedTrunc shiftedTrunc_sub_tail_le_primeLambda
    1 (19 / 36) (7 / 12) (by native_decide)

/-- A tighter enclosure with primes up to `22` (powerset of 8 primes). -/
theorem primeLambda_tighter :
    ((54 / 100 : ℚ) : ℝ) ≤ primeLambda ∧ primeLambda ≤ ((56 / 100 : ℚ) : ℝ) :=
  LeanCert.Validity.verify_limit_interval
    primeLambda_le_shiftedTrunc shiftedTrunc_sub_tail_le_primeLambda
    20 (54 / 100) (56 / 100) (by native_decide)

set_option maxRecDepth 100000 in
/-- **26 certified digits** (paper §5.2, Appendix A.2): primes up to `2003`
with the odd-tail majorant at exponent `2005`, evaluated exactly by LeanCert's
sparse product-integral certificate (`primeFRatSparse`,
`primeSandwichErrorRatSparse`) and lifted by `verify_limit_interval`.
One `native_decide`, about two minutes. -/
theorem primeLambda_digits26 :
    ((5506530112728429635779717568 / 10 ^ 28 : ℚ) : ℝ) ≤ primeLambda ∧
      primeLambda ≤ ((5506530112728429635779717572 / 10 ^ 28 : ℚ) : ℝ) :=
  LeanCert.Validity.verify_limit_interval primeLambda_le_shiftedTruncSparse
    shiftedTruncSparse_sub_tail_le_primeLambda 2001
    (5506530112728429635779717568 / 10 ^ 28) (5506530112728429635779717572 / 10 ^ 28)
    (by native_decide)

end RntPaper
