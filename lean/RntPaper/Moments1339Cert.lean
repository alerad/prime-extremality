import RntPaper.CertV1

/-!
# Exact certificates for the envelopes of `Moments1339`

All checks are exact rational computations, evaluated by the kernel (`decide +kernel`).

* SC: `E - (1 - v)` has one sign change on `(0,1)` and a positive endpoint moment, for the
  polynomial envelopes `(1-v²)(1-v³)(1-v⁵)` (at `s = 75/28`), `(1-v²)(1-v³)(1-v²⁵)`,
  `(1-v²)(1-v⁵)(1-v⁹)`, `(1-v³)(1-v⁴)(1-v⁵)` (at `s = 3`).
* V1: the envelopes `∏_{m ∈ M}(1 - vᵐ) ∏_{n ≥ 61}(1 - vⁿ)` for the five exponent lists `M`
  below (at `s = 3`, resp. `s = 5` for `H₂₃`).
-/

namespace RntPaper.M1339

open RntPaper.CP

/-- `∏_{n ∈ l}(1 - vⁿ) - (1 - v)` as a coefficient list. -/
def envD (l : List ℕ) : List ℚ := sub (prodOneSub l) [1, -1]

theorem sc235 : scCheck 40 (envD [2, 3, 5]) (mul [1] (compPow 1 (envD [2, 3, 5]))) (75 / 28)
    = true := by decide +kernel

theorem sc23 : scCheck 40 (envD [2, 3, 25]) (mul [1] (compPow 1 (envD [2, 3, 25]))) 3
    = true := by decide +kernel

theorem sc25 : scCheck 40 (envD [2, 5, 9]) (mul [1] (compPow 1 (envD [2, 5, 9]))) 3
    = true := by decide +kernel

theorem sc35 : scCheck 40 (envD [3, 4, 5]) (mul [1] (compPow 1 (envD [3, 4, 5]))) 3
    = true := by decide +kernel

/-- `3`-smooth numbers in `[4, 60]`. -/
def M23 : List ℕ := [4, 6, 8, 9, 12, 16, 18, 24, 27, 32, 36, 48, 54]
/-- `R₀ = {2}`: `2` and the odd `5`-smooth numbers in `[4, 60]`. -/
def M5two : List ℕ := [2, 9, 15, 25, 27, 45]
/-- `R₀ = {3}`. -/
def M5three : List ℕ := [3, 4, 8, 10, 16, 20, 25, 32, 40, 50]
/-- `R₀ = {5}`. -/
def M5five : List ℕ := [5, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32, 36, 48, 54]
/-- `R₀ = ∅`. -/
def M5none : List ℕ :=
  [4, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30, 32, 36, 40, 45, 48, 50, 54, 60]

theorem v1_23 : v1Check 12 [1] M23 61 [1] 1 5 (4 / 5) (1 / 2) = true := by decide +kernel
theorem v1_5two : v1Check 12 [1] M5two 61 [1] 1 3 (3 / 4) (1 / 2) = true := by decide +kernel
theorem v1_5three : v1Check 12 [1] M5three 61 [1] 1 3 (3 / 4) (1 / 2) = true := by decide +kernel
theorem v1_5five : v1Check 12 [1] M5five 61 [1] 1 3 (3 / 4) (1 / 2) = true := by decide +kernel
theorem v1_5none : v1Check 12 [1] M5none 61 [1] 1 3 (3 / 4) (1 / 2) = true := by decide +kernel

end RntPaper.M1339
