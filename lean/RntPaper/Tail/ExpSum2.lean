import RntPaper.Tail.Defs2
import RntPaper.Tail.Phi
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Int
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Second-order expansion of `S(u) = ∑_p e^{-pu}` (blueprint `TAIL2_PLAN.md`, §B)

Under `ThetaErrLog2` we prove `S(u) = (1 + γ/L)/(uL) + O(1/(uL³))`, `L = -log u`.

The proof is entirely discrete (no integrals). With `x = e^{-u}` and `g(n) = x^n / log n`
(which is `0` for `n ≤ 1` by Lean's conventions):

* Abel summation: `S(u) - ∑ g(n) = ∑ E(n) (g(n) - g(n+1))`, `E(n) = θ(n) - n`.
* Expansion `1/log n = 1/L - (log n - L)/L² + (log n - L)²/(L² log n)`.
* `∑ x^n log n` is computed through harmonic numbers: `∑ H_n x^n = -log(1-x)/(1-x)` and
  `H_n - log n - γ ∈ [0, 1/n]`; this is where Euler's constant enters.
* All remainders are dominated termwise by `C · D(n) / L³` (or `/L`), where
  `D(n) = x^n · nu + [nu ≤ 1] (nu)^{-1/2}` has `∑ D(n) ≤ 4/u`.
-/

namespace RntPaper

open Real Filter Topology

/-! ### Elementary inequalities -/

private lemma es2_log_two_gt : (1 : ℝ) / 2 < Real.log 2 := by
  have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

private lemma es2_log_sq_le_of_le_one {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    Real.log y ^ 2 ≤ 16 * (√y)⁻¹ := by
  have hs0 : 0 < √y := Real.sqrt_pos.2 hy0
  set r := √(√y) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hs0
  have hr2 : r ^ 2 = √y := Real.sq_sqrt hs0.le
  have hy4 : y = r ^ 4 := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2, Real.sq_sqrt hy0.le]
  have hr1 : r ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < r ^ 4 := one_lt_pow₀ h (by norm_num)
    linarith
  have hlog : Real.log y = 4 * Real.log r := by
    rw [hy4, Real.log_pow]; push_cast; ring
  have h1 : Real.log r ≤ 0 := Real.log_nonpos hr0.le hr1
  have h2 : -Real.log r ≤ r⁻¹ := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hr0)
    rw [Real.log_inv] at this; linarith
  have h3 : Real.log r ^ 2 ≤ (r⁻¹) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith [inv_pos.2 hr0])
  calc Real.log y ^ 2 = 16 * Real.log r ^ 2 := by rw [hlog]; ring
    _ ≤ 16 * (r⁻¹) ^ 2 := by linarith
    _ = 16 * (√y)⁻¹ := by rw [inv_pow, hr2]

private lemma es2_log_sq_le_of_one_le {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 2 ≤ 4 * y := by
  have hy0 : 0 < y := by linarith
  set t := √y with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 hy0
  have ht2 : t ^ 2 = y := Real.sq_sqrt hy0.le
  have hlog : Real.log y = 2 * Real.log t := by
    rw [← ht2, Real.log_pow]; push_cast; ring
  have h1 : 0 ≤ Real.log y := Real.log_nonneg hy
  have h2 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht0
  have h3 : 0 ≤ Real.log t := by linarith
  calc Real.log y ^ 2 = 4 * Real.log t ^ 2 := by rw [hlog]; ring
    _ ≤ 4 * t ^ 2 := by nlinarith
    _ = 4 * y := by rw [ht2]

private lemma es2_sum_inv_sqrt (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (√(n : ℝ))⁻¹ ≤ 2 * √(N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have ha := Real.sqrt_nonneg (N : ℝ)
    have hb : 0 < √((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have ha2 : √(N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
    have hb2 : √((N + 1 : ℕ) : ℝ) ^ 2 = N + 1 := by
      rw [Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; ring
    have key : (√((N + 1 : ℕ) : ℝ))⁻¹ ≤ 2 * √((N + 1 : ℕ) : ℝ) - 2 * √(N : ℝ) := by
      rw [inv_eq_one_div, div_le_iff₀ hb]
      nlinarith [sq_nonneg (√((N + 1 : ℕ) : ℝ) - √(N : ℝ))]
    linarith

private lemma es2_cube_mul_exp_le {L : ℝ} (hL : 0 ≤ L) : L ^ 3 * rexp (-(3 * L / 8)) ≤ 512 := by
  have h1 : L / 8 + 1 ≤ rexp (L / 8) := Real.add_one_le_exp _
  have h3 : L ^ 3 ≤ (8 * rexp (L / 8)) ^ 3 := pow_le_pow_left₀ hL (by linarith) 3
  have h4 : rexp (L / 8) ^ 3 * rexp (-(3 * L / 8)) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add,
      show ((3 : ℕ) : ℝ) * (L / 8) + -(3 * L / 8) = 0 by push_cast; ring, Real.exp_zero]
  calc L ^ 3 * rexp (-(3 * L / 8)) ≤ (8 * rexp (L / 8)) ^ 3 * rexp (-(3 * L / 8)) :=
        mul_le_mul_of_nonneg_right h3 (exp_pos _).le
    _ = 512 * (rexp (L / 8) ^ 3 * rexp (-(3 * L / 8))) := by ring
    _ = 512 := by rw [h4, mul_one]

private lemma es2_cube_mul_exp_le' {L : ℝ} (hL : 0 ≤ L) : L ^ 3 * rexp (-L) ≤ 27 := by
  have h1 : L / 3 + 1 ≤ rexp (L / 3) := Real.add_one_le_exp _
  have h3 : L ^ 3 ≤ (3 * rexp (L / 3)) ^ 3 := pow_le_pow_left₀ hL (by linarith) 3
  have h4 : rexp (L / 3) ^ 3 * rexp (-L) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add,
      show ((3 : ℕ) : ℝ) * (L / 3) + -L = 0 by push_cast; ring, Real.exp_zero]
  calc L ^ 3 * rexp (-L) ≤ (3 * rexp (L / 3)) ^ 3 * rexp (-L) :=
        mul_le_mul_of_nonneg_right h3 (exp_pos _).le
    _ = 27 * (rexp (L / 3) ^ 3 * rexp (-L)) := by ring
    _ = 27 := by rw [h4, mul_one]

/-- `log (n u) = log n - L` when `u = e^{-L}`. -/
private lemma es2_log_nu {u L : ℝ} (huL : u = rexp (-L)) {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n * u) = Real.log n - L := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_mul hn0.ne' (by rw [huL]; exact (exp_pos _).ne'), huL, Real.log_exp]; ring

/-- Small `n` (`log n < L/4`): `n u < 1` and `L³ ≤ 512 (nu)^{-1/2}`. -/
private lemma es2_small {u L : ℝ} (hL : 0 ≤ L) (huL : u = rexp (-L)) {n : ℕ} (hn : 1 ≤ n)
    (h : Real.log n < L / 4) :
    (n : ℝ) * u < 1 ∧ L ^ 3 ≤ 512 * (√((n : ℝ) * u))⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnu : (n : ℝ) * u = rexp (Real.log n - L) := by
    rw [Real.exp_sub, Real.exp_log hn0, huL, Real.exp_neg, div_eq_mul_inv]
  have hsq : √((n : ℝ) * u) = rexp ((Real.log n - L) / 2) := by
    rw [hnu, Real.sqrt_eq_iff_mul_self_eq_of_pos (exp_pos _), ← Real.exp_add]; ring_nf
  have hle : √((n : ℝ) * u) ≤ rexp (-(3 * L / 8)) := by
    rw [hsq]; exact Real.exp_le_exp.2 (by linarith)
  have hpos : 0 < √((n : ℝ) * u) := by rw [hsq]; exact exp_pos _
  refine ⟨?_, ?_⟩
  · rw [hnu]; exact Real.exp_lt_one_iff.2 (by linarith)
  · have := es2_cube_mul_exp_le hL
    have h2 : L ^ 3 * √((n : ℝ) * u) ≤ 512 :=
      (mul_le_mul_of_nonneg_left hle (pow_nonneg hL 3)).trans this
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact h2

/-! ### The kernel `g`, the dominating sequence `D` -/

/-- `g(n) = e^{-nu} / log n` (`= 0` for `n ≤ 1`). -/
private noncomputable def es2_g (u : ℝ) (n : ℕ) : ℝ := rexp (-u) ^ n / Real.log n

/-- `D(n) = x^n · nu + [nu ≤ 1] (nu)^{-1/2}`. -/
private noncomputable def es2_D (u : ℝ) (n : ℕ) : ℝ :=
  rexp (-u) ^ n * (n * u) + (if (n : ℝ) * u ≤ 1 then (√((n : ℝ) * u))⁻¹ else 0)

private lemma es2_D2_nonneg (u : ℝ) (n : ℕ) :
    0 ≤ (if (n : ℝ) * u ≤ 1 then (√((n : ℝ) * u))⁻¹ else 0) := by
  split_ifs
  · exact inv_nonneg.2 (Real.sqrt_nonneg _)
  · exact le_rfl

private lemma es2_D_ge_lin {u : ℝ} (hu : 0 < u) (n : ℕ) :
    rexp (-u) ^ n * (n * u) ≤ es2_D u n := by
  unfold es2_D; linarith [es2_D2_nonneg u n]

private lemma es2_D_ge_sqrt {u : ℝ} (hu : 0 < u) {n : ℕ} (h : (n : ℝ) * u ≤ 1) :
    (√((n : ℝ) * u))⁻¹ ≤ es2_D u n := by
  unfold es2_D
  rw [if_pos h]
  have : 0 ≤ rexp (-u) ^ n * (n * u) := by positivity
  linarith

private lemma es2_D_nonneg {u : ℝ} (hu : 0 < u) (n : ℕ) : 0 ≤ es2_D u n :=
  le_trans (by positivity) (es2_D_ge_lin hu n)

private lemma es2_x_facts {u : ℝ} (hu : 0 < u) :
    0 < rexp (-u) ∧ rexp (-u) < 1 ∧ 1 - rexp (-u) ≤ u ∧ u * rexp (-u) ≤ 1 - rexp (-u) ∧
      rexp (-u) * (1 + u) ≤ 1 := by
  have hx0 := exp_pos (-u)
  have hx1 : rexp (-u) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h1 : -u + 1 ≤ rexp (-u) := Real.add_one_le_exp _
  have h2 : u + 1 ≤ rexp u := Real.add_one_le_exp _
  have h3 : rexp (-u) * rexp u = 1 := by rw [← exp_add]; simp
  refine ⟨hx0, hx1, by linarith, by nlinarith, by nlinarith⟩

private lemma es2_hasSum_D1 {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => rexp (-u) ^ n * (n * u)) (u * (rexp (-u) / (1 - rexp (-u)) ^ 2)) := by
  obtain ⟨hx0, hx1, -⟩ := es2_x_facts hu
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one
    (r := rexp (-u)) (by rw [Real.norm_of_nonneg hx0.le]; exact hx1)).mul_left u
  convert h using 1
  ext n; ring

private lemma es2_D2_sum {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => if (n : ℝ) * u ≤ 1 then (√((n : ℝ) * u))⁻¹ else 0) ∧
    ∑' n : ℕ, (if (n : ℝ) * u ≤ 1 then (√((n : ℝ) * u))⁻¹ else 0) ≤ 2 / u := by
  set N := ⌊u⁻¹⌋₊ with hN
  have hzero : ∀ n ∉ Finset.range (N + 1),
      (if (n : ℝ) * u ≤ 1 then (√((n : ℝ) * u))⁻¹ else 0) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have h1 : u⁻¹ < n := by
      have := Nat.lt_floor_add_one u⁻¹
      have h2 : ((N + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2; linarith
    have h2 : 1 < (n : ℝ) * u := by
      have := mul_lt_mul_of_pos_right h1 hu
      rwa [inv_mul_cancel₀ hu.ne'] at this
    rw [if_neg (not_le.2 h2)]
  refine ⟨summable_of_ne_finset_zero hzero, ?_⟩
  rw [tsum_eq_sum hzero]
  have hsu : 0 < √u := Real.sqrt_pos.2 hu
  calc ∑ n ∈ Finset.range (N + 1), (if (n : ℝ) * u ≤ 1 then (√((n : ℝ) * u))⁻¹ else 0)
      ≤ ∑ n ∈ Finset.range (N + 1), (√u)⁻¹ * (√(n : ℝ))⁻¹ := by
        apply Finset.sum_le_sum; intro n _
        split_ifs
        · rw [Real.sqrt_mul (Nat.cast_nonneg _), mul_inv, mul_comm]
        · positivity
    _ = (√u)⁻¹ * ∑ n ∈ Finset.range (N + 1), (√(n : ℝ))⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (√u)⁻¹ * (2 * √(N : ℝ)) :=
        mul_le_mul_of_nonneg_left (es2_sum_inv_sqrt N) (by positivity)
    _ ≤ (√u)⁻¹ * (2 * (√u)⁻¹) := by
        gcongr
        rw [← Real.sqrt_inv]; exact Real.sqrt_le_sqrt (Nat.floor_le (by positivity))
    _ = 2 / u := by
        have : (√u)⁻¹ * (√u)⁻¹ = u⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt hu.le]
        rw [div_eq_mul_inv, ← this]; ring

private lemma es2_D_sum {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    Summable (es2_D u) ∧ ∑' n, es2_D u n ≤ 4 / u := by
  obtain ⟨hx0, hx1, h1x, hux, hxu⟩ := es2_x_facts hu
  obtain ⟨hs2, hb2⟩ := es2_D2_sum hu
  have h1 := es2_hasSum_D1 hu
  have hsum : HasSum (es2_D u) (u * (rexp (-u) / (1 - rexp (-u)) ^ 2) +
      ∑' n : ℕ, (if (n : ℝ) * u ≤ 1 then (√((n : ℝ) * u))⁻¹ else 0)) :=
    h1.add hs2.hasSum
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq]
  set x := rexp (-u)
  have hpos : 0 < 1 - x := by linarith
  have hb1 : u * (x / (1 - x) ^ 2) ≤ 2 / u := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hu]
    -- u x u ≤ 2 (1-x)^2, from u x ≤ 1 - x and u ≤ 2 (1 - x)
    have : u ≤ 2 * (1 - x) := by nlinarith
    nlinarith
  have : 4 / u = 2 / u + 2 / u := by ring
  linarith

/-! ### Termwise estimates -/

private lemma es2_gdiff {u : ℝ} (hu : 0 < u) {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ es2_g u n - es2_g u (n + 1) ∧
    es2_g u n - es2_g u (n + 1) ≤
      rexp (-u) ^ n / (n * Real.log n ^ 2) + u * rexp (-u) ^ n / Real.log n := by
  obtain ⟨hx0, hx1, h1x, -, -⟩ := es2_x_facts hu
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hg0 : es2_g u n - es2_g u (n + 1) = rexp (-u) ^ n / Real.log n -
      rexp (-u) ^ n * rexp (-u) / Real.log ((n : ℝ) + 1) := by
    unfold es2_g; push_cast; ring
  rw [hg0]
  set x := rexp (-u)
  set X := x ^ n with hX
  have hX0 : 0 < X := pow_pos hx0 n
  set a := Real.log n with ha
  set b := Real.log ((n : ℝ) + 1) with hb
  have ha0 : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log hn0 (by linarith)
  have hba : (b - a) * n ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / n by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at h
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    rw [e] at h
    have := mul_le_mul_of_nonneg_right h hn0.le
    rwa [one_div_mul_cancel hn0.ne'] at this
  have hb0 : 0 < b := by linarith
  have e : X / a - X * x / b = X * (b - a) / (a * b) + X * (1 - x) / b := by
    field_simp; ring
  rw [e]
  constructor
  · have : 0 ≤ X * (b - a) / (a * b) :=
      div_nonneg (mul_nonneg hX0.le (by linarith)) (by positivity)
    have : 0 ≤ X * (1 - x) / b := div_nonneg (mul_nonneg hX0.le (by linarith)) hb0.le
    linarith
  · have t1 : X * (b - a) / (a * b) ≤ X / (n * a ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc X * (b - a) * (n * a ^ 2) = (X * a ^ 2) * ((b - a) * n) := by ring
        _ ≤ (X * a ^ 2) * 1 := mul_le_mul_of_nonneg_left hba (by positivity)
        _ ≤ X * (a * b) := by
          nlinarith [mul_nonneg (mul_nonneg hX0.le ha0.le) (sub_nonneg.2 hab)]
    have t2 : X * (1 - x) / b ≤ u * X / a := by
      rw [div_le_div_iff₀ hb0 ha0]
      have h1 : X * (1 - x) * a ≤ X * u * a := by
        apply mul_le_mul_of_nonneg_right _ ha0.le
        exact mul_le_mul_of_nonneg_left h1x hX0.le
      have h2 : X * u * a ≤ X * u * b := mul_le_mul_of_nonneg_left hab (by positivity)
      linarith
    linarith

private lemma es2_sqrt_inv_ge_one {u : ℝ} (hu : 0 < u) {n : ℕ} (hn : 1 ≤ n)
    (h : (n : ℝ) * u ≤ 1) : 1 ≤ (√((n : ℝ) * u))⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √((n : ℝ) * u) := Real.sqrt_pos.2 (by positivity)
  rw [one_le_inv₀ hs]
  calc √((n : ℝ) * u) ≤ √1 := Real.sqrt_le_sqrt h
    _ = 1 := Real.sqrt_one

/-- Error-part kernel: `x^n/log⁴ n + nu x^n/log³ n ≤ 12288 D(n)/L³` for `n ≥ 2`. -/
private lemma es2_err_core {u L : ℝ} (hu : 0 < u) (hL : 1 ≤ L) (huL : u = rexp (-L))
    {n : ℕ} (hn : 2 ≤ n) :
    rexp (-u) ^ n / Real.log n ^ 4 + n * u * rexp (-u) ^ n / Real.log n ^ 3 ≤
      12288 * es2_D u n / L ^ 3 := by
  obtain ⟨hx0, hx1, -⟩ := es2_x_facts hu
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog2 := es2_log_two_gt
  have hlognu := es2_log_nu huL (by omega : 1 ≤ n)
  set X := rexp (-u) ^ n with hX
  have hX0 : 0 < X := pow_pos hx0 n
  have hX1 : X ≤ 1 := pow_le_one₀ hx0.le hx1.le
  set a := Real.log n with ha
  have ha2 : Real.log 2 ≤ a := Real.log_le_log two_pos hn2
  have ha0 : 0 < a := by linarith
  have hD := es2_D_nonneg hu n
  have hL0 : 0 < L := by linarith
  have hnu0 : 0 < (n : ℝ) * u := by positivity
  have key : (X + n * u * X * a) * L ^ 3 ≤ 12288 * es2_D u n * a ^ 4 := by
    by_cases h1 : 1 < (n : ℝ) * u
    · have haL : L < a := by
        have := Real.log_pos h1; rw [hlognu] at this; linarith
      have hlin := es2_D_ge_lin hu n
      have hL3 : L ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hL0.le haL.le 3
      have ha1 : 1 ≤ a := by linarith
      have ha34 : a ^ 3 ≤ a ^ 4 := pow_le_pow_right₀ ha1 (by norm_num)
      have hnuX : 0 ≤ (n : ℝ) * u * X := by positivity
      have e1 : X * L ^ 3 ≤ X * (n * u) * a ^ 4 := by
        have : L ^ 3 ≤ (n * u) * a ^ 4 :=
          calc L ^ 3 ≤ a ^ 4 := hL3.trans ha34
            _ = 1 * a ^ 4 := by ring
            _ ≤ (n * u) * a ^ 4 := mul_le_mul_of_nonneg_right h1.le (by positivity)
        calc X * L ^ 3 ≤ X * ((n * u) * a ^ 4) := mul_le_mul_of_nonneg_left this hX0.le
          _ = _ := by ring
      have e2 : n * u * X * a * L ^ 3 ≤ X * (n * u) * a ^ 4 := by
        have : a * L ^ 3 ≤ a ^ 4 := by nlinarith
        calc n * u * X * a * L ^ 3 = (n * u * X) * (a * L ^ 3) := by ring
          _ ≤ (n * u * X) * a ^ 4 := mul_le_mul_of_nonneg_left this hnuX
          _ = _ := by ring
      have e3 : X * (n * u) * a ^ 4 ≤ es2_D u n * a ^ 4 :=
        mul_le_mul_of_nonneg_right hlin (by positivity)
      calc (X + n * u * X * a) * L ^ 3 = X * L ^ 3 + n * u * X * a * L ^ 3 := by ring
        _ ≤ X * (n * u) * a ^ 4 + X * (n * u) * a ^ 4 := add_le_add e1 e2
        _ ≤ es2_D u n * a ^ 4 + es2_D u n * a ^ 4 := add_le_add e3 e3
        _ ≤ 12288 * es2_D u n * a ^ 4 := by nlinarith [mul_nonneg hD (pow_pos ha0 4).le]
    · push Not at h1
      have hsq := es2_D_ge_sqrt hu h1
      have hs1 := es2_sqrt_inv_ge_one hu (by omega : 1 ≤ n) h1
      have hD1 : 1 ≤ es2_D u n := hs1.trans hsq
      have hnuX : n * u * X ≤ 1 := by
        calc (n : ℝ) * u * X ≤ 1 * 1 := mul_le_mul h1 hX1 hX0.le zero_le_one
          _ = 1 := by ring
      have hsum : (X + n * u * X * a) * L ^ 3 ≤ (1 + a) * L ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      by_cases h2 : L / 4 ≤ a
      · have hL4a : L ≤ 4 * a := by linarith
        have hL3 : L ^ 3 ≤ 64 * a ^ 3 := by
          have := pow_le_pow_left₀ hL0.le hL4a 3
          calc L ^ 3 ≤ (4 * a) ^ 3 := this
            _ = 64 * a ^ 3 := by ring
        have hL4 : L ^ 4 ≤ 256 * a ^ 4 := by
          have := pow_le_pow_left₀ hL0.le hL4a 4
          calc L ^ 4 ≤ (4 * a) ^ 4 := this
            _ = 256 * a ^ 4 := by ring
        have hL34 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
        have : (1 + a) * L ^ 3 ≤ 320 * a ^ 4 := by
          have : a * L ^ 3 ≤ a * (64 * a ^ 3) := mul_le_mul_of_nonneg_left hL3 ha0.le
          nlinarith
        have : 320 * a ^ 4 ≤ 12288 * es2_D u n * a ^ 4 := by
          have := pow_pos ha0 4
          nlinarith
        linarith
      · push Not at h2
        obtain ⟨-, hsm⟩ := es2_small hL0.le huL (by omega : 1 ≤ n) h2
        have hL3 : L ^ 3 ≤ 512 * es2_D u n := by linarith
        have ha1 : 1 ≤ 2 * a := by linarith
        have ha3 : 1 ≤ 8 * a ^ 3 :=
          calc (1 : ℝ) = 1 ^ 3 := by norm_num
            _ ≤ (2 * a) ^ 3 := pow_le_pow_left₀ zero_le_one ha1 3
            _ = 8 * a ^ 3 := by ring
        have : (1 + a) * L ^ 3 ≤ 3 * a * (512 * es2_D u n) := by
          have h3 : 1 + a ≤ 3 * a := by linarith
          calc (1 + a) * L ^ 3 ≤ 3 * a * L ^ 3 :=
                mul_le_mul_of_nonneg_right h3 (by positivity)
            _ ≤ 3 * a * (512 * es2_D u n) := mul_le_mul_of_nonneg_left hL3 (by positivity)
        have : 3 * a * (512 * es2_D u n) ≤ 12288 * es2_D u n * a ^ 4 := by
          have h4 : 0 ≤ a * es2_D u n := by positivity
          nlinarith
        linarith
  rw [show X / a ^ 4 + n * u * X / a ^ 3 = (X + n * u * X * a) / a ^ 4 by field_simp]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact key

/-- Main-part remainder kernel: `x^n (log n - L)²/(L² log n) ≤ 1024 D(n)/L³` for `n ≥ 2`. -/
private lemma es2_r_core {u L : ℝ} (hu : 0 < u) (hL : 1 ≤ L) (huL : u = rexp (-L))
    {n : ℕ} (hn : 2 ≤ n) :
    rexp (-u) ^ n * (Real.log n - L) ^ 2 / (L ^ 2 * Real.log n) ≤
      1024 * es2_D u n / L ^ 3 := by
  obtain ⟨hx0, hx1, -⟩ := es2_x_facts hu
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog2 := es2_log_two_gt
  have hlognu := es2_log_nu huL (by omega : 1 ≤ n)
  set X := rexp (-u) ^ n with hX
  have hX0 : 0 < X := pow_pos hx0 n
  have hX1 : X ≤ 1 := pow_le_one₀ hx0.le hx1.le
  set a := Real.log n with ha
  have ha2 : Real.log 2 ≤ a := Real.log_le_log two_pos hn2
  have ha0 : 0 < a := by linarith
  have hD := es2_D_nonneg hu n
  have hL0 : 0 < L := by linarith
  have hnu0 : 0 < (n : ℝ) * u := by positivity
  have key : X * (a - L) ^ 2 * L ≤ 1024 * es2_D u n * a := by
    by_cases h1 : 1 < (n : ℝ) * u
    · have haL : L < a := by
        have := Real.log_pos h1; rw [hlognu] at this; linarith
      have hlin := es2_D_ge_lin hu n
      have hl2 : (a - L) ^ 2 ≤ 4 * (n * u) := by
        rw [← hlognu]; exact es2_log_sq_le_of_one_le h1.le
      calc X * (a - L) ^ 2 * L ≤ X * (4 * (n * u)) * a := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hl2 hX0.le) haL.le hL0.le
            positivity
        _ = 4 * (X * (n * u)) * a := by ring
        _ ≤ 4 * es2_D u n * a := by
            apply mul_le_mul_of_nonneg_right _ ha0.le; linarith
        _ ≤ 1024 * es2_D u n * a := by nlinarith [mul_nonneg hD ha0.le]
    · push Not at h1
      have hsq := es2_D_ge_sqrt hu h1
      by_cases h2 : L / 4 ≤ a
      · have hl2 : (a - L) ^ 2 ≤ 16 * (√((n : ℝ) * u))⁻¹ := by
          rw [← hlognu]; exact es2_log_sq_le_of_le_one hnu0 h1
        have hs0 : 0 ≤ (√((n : ℝ) * u))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
        calc X * (a - L) ^ 2 * L ≤ 1 * (16 * (√((n : ℝ) * u))⁻¹) * (4 * a) := by
              apply mul_le_mul (mul_le_mul hX1 hl2 (sq_nonneg _) zero_le_one) (by linarith)
                hL0.le (by positivity)
          _ = 64 * (√((n : ℝ) * u))⁻¹ * a := by ring
          _ ≤ 64 * es2_D u n * a := by
              apply mul_le_mul_of_nonneg_right _ ha0.le; linarith
          _ ≤ 1024 * es2_D u n * a := by nlinarith [mul_nonneg hD ha0.le]
      · push Not at h2
        obtain ⟨-, hsm⟩ := es2_small hL0.le huL (by omega : 1 ≤ n) h2
        have hl2 : (a - L) ^ 2 ≤ L ^ 2 := by nlinarith
        calc X * (a - L) ^ 2 * L ≤ 1 * L ^ 2 * L := by
              apply mul_le_mul_of_nonneg_right _ hL0.le
              exact mul_le_mul hX1 hl2 (sq_nonneg _) zero_le_one
          _ = L ^ 3 := by ring
          _ ≤ 512 * es2_D u n := by linarith
          _ ≤ 1024 * es2_D u n * a := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc X * (a - L) ^ 2 * L ^ 3 = L ^ 2 * (X * (a - L) ^ 2 * L) := by ring
    _ ≤ L ^ 2 * (1024 * es2_D u n * a) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = 1024 * es2_D u n * (L ^ 2 * a) := by ring

/-! ### Termwise bounds for all `n` -/

/-- `E(n) = θ(n) - n`. -/
private noncomputable def es2_E (n : ℕ) : ℝ := Chebyshev.theta n - n

private lemma es2_g_zero (u : ℝ) : es2_g u 0 = 0 := by simp [es2_g]

private lemma es2_g_one (u : ℝ) : es2_g u 1 = 0 := by simp [es2_g]

private lemma es2_err_term {u L K : ℝ} (hu : 0 < u) (hL : 1 ≤ L) (huL : u = rexp (-L))
    (hK : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ K * x / Real.log x ^ 2) (n : ℕ) :
    |es2_E n * (es2_g u n - es2_g u (n + 1))| ≤ (12288 * |K| + 1024) * es2_D u n / L ^ 3 := by
  have hL0 : 0 < L := by linarith
  have hD := es2_D_nonneg hu n
  have hC : 0 ≤ (12288 * |K| + 1024) * es2_D u n / L ^ 3 := by positivity
  obtain ⟨hx0, hx1, -⟩ := es2_x_facts hu
  have hlog2 := es2_log_two_gt
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp [es2_g_zero, es2_g_one]; exact hC
    · have hE1 : es2_E 1 = -1 := by simp [es2_E, Chebyshev.theta_one]
      rw [hE1, es2_g_one]
      have hg2 : es2_g u (1 + 1) = rexp (-u) ^ 2 / Real.log 2 := by
        simp [es2_g]
      rw [hg2]
      have hx2 : rexp (-u) ^ 2 ≤ 1 := pow_le_one₀ hx0.le hx1.le
      have h1 : |(-1 : ℝ) * (0 - rexp (-u) ^ 2 / Real.log 2)| ≤ 2 := by
        rw [show (-1 : ℝ) * (0 - rexp (-u) ^ 2 / Real.log 2) = rexp (-u) ^ 2 / Real.log 2 by ring,
          abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
        linarith
      obtain ⟨hu1, hsm⟩ := es2_small hL0.le huL (n := 1) le_rfl (by simp; linarith)
      have hsq := es2_D_ge_sqrt hu (n := 1) hu1.le
      refine h1.trans ?_
      rw [le_div_iff₀ (by positivity)]
      have : 0 ≤ |K| * es2_D u 1 := by positivity
      nlinarith
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    obtain ⟨hd0, hd1⟩ := es2_gdiff hu hn
    have ha2 : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos hn2
    have ha0 : 0 < Real.log n := by linarith
    have hEb : |es2_E n| ≤ |K| * n / Real.log n ^ 2 := by
      refine (hK n hn2).trans ?_
      gcongr
      exact le_abs_self K
    have hcore := es2_err_core hu hL huL hn
    rw [abs_mul, abs_of_nonneg hd0]
    calc |es2_E n| * (es2_g u n - es2_g u (n + 1))
        ≤ (|K| * n / Real.log n ^ 2) *
          (rexp (-u) ^ n / (n * Real.log n ^ 2) + u * rexp (-u) ^ n / Real.log n) :=
          mul_le_mul hEb hd1 hd0 (by positivity)
      _ = |K| * (rexp (-u) ^ n / Real.log n ^ 4 + n * u * rexp (-u) ^ n / Real.log n ^ 3) := by
          field_simp
      _ ≤ |K| * (12288 * es2_D u n / L ^ 3) := mul_le_mul_of_nonneg_left hcore (abs_nonneg K)
      _ ≤ (12288 * |K| + 1024) * es2_D u n / L ^ 3 := by
          rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
          nlinarith

private lemma es2_r_term {u L : ℝ} (hu : 0 < u) (hL : 1 ≤ L) (huL : u = rexp (-L)) (n : ℕ) :
    |es2_g u n - rexp (-u) ^ n / L + (rexp (-u) ^ n * Real.log n - L * rexp (-u) ^ n) / L ^ 2|
      ≤ 1024 * es2_D u n / L ^ 3 + (if n = 0 then 2 else 0) := by
  have hL0 : 0 < L := by linarith
  have hD := es2_D_nonneg hu n
  have hC : 0 ≤ 1024 * es2_D u n / L ^ 3 := by positivity
  obtain ⟨hx0, hx1, -⟩ := es2_x_facts hu
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · have e : es2_g u 0 - rexp (-u) ^ 0 / L +
          (rexp (-u) ^ 0 * Real.log ((0 : ℕ) : ℝ) - L * rexp (-u) ^ 0) / L ^ 2 = -(2 / L) := by
        rw [es2_g_zero]; simp; field_simp; ring
      rw [e, abs_neg, abs_of_nonneg (by positivity), if_pos rfl]
      have : 2 / L ≤ 2 := div_le_self (by norm_num) hL
      linarith
    · have e : es2_g u 1 - rexp (-u) ^ 1 / L +
          (rexp (-u) ^ 1 * Real.log ((1 : ℕ) : ℝ) - L * rexp (-u) ^ 1) / L ^ 2 =
            -(2 * rexp (-u) / L) := by
        rw [es2_g_one]; simp; field_simp; ring
      rw [e, abs_neg, abs_of_nonneg (by positivity), if_neg (by norm_num), add_zero]
      obtain ⟨hu1, hsm⟩ := es2_small hL0.le huL (n := 1) le_rfl (by simp; linarith)
      have hsq := es2_D_ge_sqrt hu (n := 1) hu1.le
      rw [div_le_div_iff₀ hL0 (by positivity)]
      have hL23 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL (by norm_num)
      push_cast at hsm hsq
      nlinarith
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have ha0 : 0 < Real.log n := Real.log_pos (by linarith)
    have e : es2_g u n - rexp (-u) ^ n / L +
        (rexp (-u) ^ n * Real.log n - L * rexp (-u) ^ n) / L ^ 2 =
          rexp (-u) ^ n * (Real.log n - L) ^ 2 / (L ^ 2 * Real.log n) := by
      unfold es2_g; field_simp; ring
    rw [e, abs_of_nonneg (by positivity), if_neg (by omega), add_zero]
    exact es2_r_core hu hL huL hn

/-! ### Abel summation -/

/-- `log n` on primes, `0` elsewhere. -/
private noncomputable def es2_plog (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

private lemma es2_theta_nat (n : ℕ) :
    Chebyshev.theta n = ∑ k ∈ Finset.Ioc 0 n, es2_plog k := by
  rw [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]; rfl

private lemma es2_theta_succ (n : ℕ) :
    Chebyshev.theta ((n : ℝ) + 1) = Chebyshev.theta n + es2_plog (n + 1) := by
  have := es2_theta_nat (n + 1)
  push_cast at this
  rw [this, es2_theta_nat, Finset.sum_Ioc_succ_top (Nat.zero_le n)]

private lemma es2_S_eq (u : ℝ) : primeExpSum u = ∑' n : ℕ, es2_plog n * es2_g u n := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := fun _ _ h => Subtype.ext h
  unfold primeExpSum
  rw [← hinj.tsum_eq (f := fun n : ℕ => es2_plog n * es2_g u n)]
  · congr 1; ext p
    have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
    have hl : Real.log ((p : ℕ) : ℝ) ≠ 0 := (Real.log_pos hp).ne'
    simp only [es2_plog, es2_g, if_pos p.2]
    rw [mul_div_cancel₀ _ hl, ← Real.exp_nat_mul]
    ring_nf
  · intro n hn
    by_cases h : n.Prime
    · exact ⟨⟨n, h⟩, rfl⟩
    · exact absurd (by simp [es2_plog, h]) hn

private lemma es2_g_bounds {u : ℝ} (hu : 0 < u) (n : ℕ) :
    0 ≤ es2_g u n ∧ es2_g u n ≤ 2 * rexp (-u) ^ n := by
  obtain ⟨hx0, -⟩ := es2_x_facts hu
  have hX := pow_pos hx0 n
  have hl := Real.log_natCast_nonneg n
  refine ⟨div_nonneg hX.le hl, ?_⟩
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp [es2_g] <;> positivity
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have ha2 : 1 / 2 < Real.log n :=
      es2_log_two_gt.trans_le (Real.log_le_log two_pos hn2)
    unfold es2_g
    rw [div_le_iff₀ (by linarith)]
    nlinarith

private lemma es2_E_bound (n : ℕ) : |es2_E n| ≤ 4 * n := by
  have h1 := Chebyshev.theta_nonneg (n : ℝ)
  have h2 := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) n)
  have h3 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : Real.log 4 * n ≤ 3 * n := mul_le_mul_of_nonneg_right h3 hn
  unfold es2_E
  rw [abs_le]; constructor <;> linarith

private lemma es2_abel {u : ℝ} (hu : 0 < u) :
    Summable (fun n => es2_E n * (es2_g u n - es2_g u (n + 1))) ∧
    primeExpSum u - ∑' n, es2_g u n =
      ∑' n, es2_E n * (es2_g u n - es2_g u (n + 1)) := by
  obtain ⟨hx0, hx1, -⟩ := es2_x_facts hu
  set x := rexp (-u) with hx
  have hgeo : Summable (fun n : ℕ => (n : ℝ) * x ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      (by rw [Real.norm_of_nonneg hx0.le]; exact hx1)).summable
  have hgeo8 : Summable (fun n : ℕ => 8 * ((n : ℝ) * x ^ n)) := hgeo.mul_left 8
  have hG : Summable (es2_g u) := by
    refine Summable.of_nonneg_of_le (fun n => (es2_g_bounds hu n).1)
      (fun n => (es2_g_bounds hu n).2) ?_
    exact (summable_geometric_of_lt_one hx0.le hx1).mul_left 2
  have hEG : Summable (fun n => es2_E n * es2_g u n) := by
    refine Summable.of_norm_bounded hgeo8 (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (es2_g_bounds hu n).1]
    have := es2_E_bound n
    have := es2_g_bounds hu n
    have : 0 ≤ x ^ n := by positivity
    nlinarith [abs_nonneg (es2_E n)]
  have hEG1 : Summable (fun n => es2_E n * es2_g u (n + 1)) := by
    refine Summable.of_norm_bounded hgeo8 (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (es2_g_bounds hu (n + 1)).1]
    have := es2_E_bound n
    have := es2_g_bounds hu (n + 1)
    have : x ^ (n + 1) ≤ x ^ n := pow_le_pow_of_le_one hx0.le hx1.le (by omega)
    have : 0 ≤ x ^ (n + 1) := by positivity
    nlinarith [abs_nonneg (es2_E n)]
  have hPG : Summable (fun n => es2_plog n * es2_g u n) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeo8
    · unfold es2_plog; split_ifs
      · exact mul_nonneg (Real.log_natCast_nonneg n) (es2_g_bounds hu n).1
      · simp
    · have hp : es2_plog n ≤ n := by
        unfold es2_plog; split_ifs
        · exact Real.log_le_self (Nat.cast_nonneg n)
        · exact Nat.cast_nonneg n
      have hp0 : 0 ≤ es2_plog n := by
        unfold es2_plog; split_ifs
        · exact Real.log_natCast_nonneg n
        · exact le_rfl
      have := es2_g_bounds hu n
      have : 0 ≤ x ^ n := by positivity
      nlinarith
  refine ⟨hEG.sub hEG1 |>.congr (fun n => by ring), ?_⟩
  have hF := hPG.sub hG
  have hEGs : Summable (fun n => es2_E (n + 1) * es2_g u (n + 1)) :=
    (summable_nat_add_iff 1).2 hEG
  rw [es2_S_eq, ← hPG.tsum_sub hG, hF.tsum_eq_zero_add]
  have h0 : es2_plog 0 * es2_g u 0 - es2_g u 0 = 0 := by simp [es2_g_zero]
  have hstep : ∀ n : ℕ, es2_plog (n + 1) * es2_g u (n + 1) - es2_g u (n + 1) =
      es2_E (n + 1) * es2_g u (n + 1) - es2_E n * es2_g u (n + 1) := by
    intro n
    have := es2_theta_succ n
    simp only [es2_E]
    push_cast
    rw [this]; ring
  rw [h0, zero_add, tsum_congr hstep, hEGs.tsum_sub hEG1]
  have hz : ∑' n, es2_E n * es2_g u n = ∑' n, es2_E (n + 1) * es2_g u (n + 1) := by
    rw [hEG.tsum_eq_zero_add]; simp [es2_g_zero]
  rw [← hz, ← hEG.tsum_sub hEG1]
  exact tsum_congr (fun n => by ring)

/-! ### Harmonic numbers and Euler's constant -/

private lemma es2_harmonic_bounds (n : ℕ) : 0 ≤ (harmonic n : ℝ) ∧ (harmonic n : ℝ) ≤ n := by
  constructor
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact_mod_cast (harmonic_pos hn.ne').le
  · induction n with
    | zero => simp
    | succ n ih =>
      rw [harmonic_succ]; push_cast
      have : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
      linarith

private lemma es2_hasSum_harmonic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => (harmonic n : ℝ) * x ^ n) (-Real.log (1 - x) / (1 - x)) := by
  have hgeo : Summable (fun n : ℕ => (n : ℝ) * x ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      (by rw [Real.norm_of_nonneg hx0]; exact hx1)).summable
  have hA : Summable (fun n : ℕ => (harmonic n : ℝ) * x ^ n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (es2_harmonic_bounds n).1 (pow_nonneg hx0 n))
      (fun n => mul_le_mul_of_nonneg_right (es2_harmonic_bounds n).2 (pow_nonneg hx0 n)) hgeo
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rw [abs_lt]; constructor <;> linarith)
  have h1 : HasSum (fun n : ℕ => (harmonic (n + 1) : ℝ) * x ^ (n + 1))
      (x * ∑' n : ℕ, (harmonic n : ℝ) * x ^ n + -Real.log (1 - x)) := by
    convert (hA.hasSum.mul_left x).add hlog using 1
    ext n; rw [harmonic_succ]; push_cast; ring
  have h2 : ∑' n : ℕ, (harmonic n : ℝ) * x ^ n =
      x * ∑' n : ℕ, (harmonic n : ℝ) * x ^ n + -Real.log (1 - x) := by
    conv_lhs => rw [hA.tsum_eq_zero_add]
    rw [h1.tsum_eq]; simp
  have hpos : 0 < 1 - x := by linarith
  have h3 : ∑' n : ℕ, (harmonic n : ℝ) * x ^ n = -Real.log (1 - x) / (1 - x) := by
    rw [eq_div_iff hpos.ne']; linarith
  rw [← h3]; exact hA.hasSum

private lemma es2_delta_bound {n : ℕ} (hn : 1 ≤ n) :
    |Real.log n - harmonic n + eulerMascheroniConstant| ≤ 1 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have h2 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  simp only [Real.eulerMascheroniSeq', Real.eulerMascheroniSeq, if_neg (by omega : n ≠ 0)] at h1 h2
  have h3 : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / n by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at h
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  rw [abs_le]; constructor <;> linarith

/-- `∑ x^n log n = (-log(1-x) - γ)/(1-x) + Δ` with `|Δ| ≤ -log(1-x) + γ`. -/
private lemma es2_B {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun n : ℕ => x ^ n * Real.log n) ∧
    |∑' n : ℕ, x ^ n * Real.log n -
        (-Real.log (1 - x) / (1 - x) - eulerMascheroniConstant * (1 - x)⁻¹)|
      ≤ -Real.log (1 - x) + eulerMascheroniConstant := by
  have hgeo : Summable (fun n : ℕ => (n : ℝ) * x ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      (by rw [Real.norm_of_nonneg hx0]; exact hx1)).summable
  have hBs : Summable (fun n : ℕ => x ^ n * Real.log n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hx0 n) (Real.log_natCast_nonneg n))
      (fun n => by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (Real.log_le_self (Nat.cast_nonneg n)) (pow_nonneg hx0 n))
      hgeo
  refine ⟨hBs, ?_⟩
  have hA := es2_hasSum_harmonic hx0 hx1
  have hQ := hasSum_geometric_of_lt_one hx0 hx1
  have hΔ := (hBs.hasSum.sub hA).add (hQ.mul_left eulerMascheroniConstant)
  have hbound := (hasSum_neg_log_one_sub hx0 hx1).add (hasSum_ite_eq 0 eulerMascheroniConstant)
  have hγ : 0 < eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  have hb : ∀ n : ℕ, ‖x ^ n * Real.log n - (harmonic n : ℝ) * x ^ n +
      eulerMascheroniConstant * x ^ n‖ ≤
        x ^ n / n + (if n = 0 then eulerMascheroniConstant else 0) := by
    intro n
    rw [Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [abs_of_pos hγ]
    · rw [if_neg (by omega), add_zero]
      have hδ := es2_delta_bound (n := n) hn
      calc |x ^ n * Real.log n - (harmonic n : ℝ) * x ^ n + eulerMascheroniConstant * x ^ n|
          = |x ^ n| * |Real.log n - harmonic n + eulerMascheroniConstant| := by
            rw [← abs_mul]; ring_nf
        _ = x ^ n * |Real.log n - harmonic n + eulerMascheroniConstant| := by
            rw [abs_of_nonneg (pow_nonneg hx0 n)]
        _ ≤ x ^ n * (1 / n) := mul_le_mul_of_nonneg_left hδ (pow_nonneg hx0 n)
        _ = x ^ n / n := by ring
  have := tsum_of_norm_bounded hbound hb
  rw [hΔ.tsum_eq, Real.norm_eq_abs] at this
  calc _ = |∑' n : ℕ, x ^ n * Real.log n - -Real.log (1 - x) / (1 - x) +
        eulerMascheroniConstant * (1 - x)⁻¹| := by ring_nf
    _ ≤ _ := this

/-! ### Assembly -/

private lemma es2_g_summable {u : ℝ} (hu : 0 < u) : Summable (es2_g u) := by
  obtain ⟨hx0, hx1, -⟩ := es2_x_facts hu
  exact Summable.of_nonneg_of_le (fun n => (es2_g_bounds hu n).1)
    (fun n => (es2_g_bounds hu n).2) ((summable_geometric_of_lt_one hx0.le hx1).mul_left 2)

/-- **Second-order expansion of `S(u)`** under `θ(x) = x + O(x/log² x)`:
`S(u) = (1 + γ/L)/(uL) + O(1/(uL³))`, `L = -log u`. -/
theorem primeExpSum_expansion (hθ : ThetaErrLog2) :
    ExpSumExpansion Real.eulerMascheroniConstant := by
  obtain ⟨K, hK⟩ := hθ
  set CE := 12288 * |K| + 1024 with hCE
  have hCE0 : 0 ≤ CE := by positivity
  refine ⟨4 * CE + 4096 + 243, rexp (-1), exp_pos _, Real.exp_lt_one_iff.2 (by norm_num), ?_⟩
  intro u hu hu1
  have hlogu : Real.log u < -1 := by
    have := Real.log_lt_log hu hu1; rwa [Real.log_exp] at this
  have hu1' : u ≤ 1 := by
    have : rexp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    linarith
  set γ := eulerMascheroniConstant with hγdef
  have hγ0 : 0 < γ := lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  have hγ1 : γ < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  set L := -Real.log u with hLdef
  have hL : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have huL : u = rexp (-L) := by rw [hLdef, neg_neg, Real.exp_log hu]
  obtain ⟨hx0, hx1, h1x, hux, hxu⟩ := es2_x_facts hu
  set x := rexp (-u) with hx
  obtain ⟨hDs, hDb⟩ := es2_D_sum hu hu1'
  have huL3 : u * L ^ 3 ≤ 27 := by
    have := es2_cube_mul_exp_le' hL0.le
    rw [huL]; linarith [mul_comm (L ^ 3) (rexp (-L))]
  have hW0 : 0 < 1 / (u * L ^ 3) := by positivity
  have h1W : 1 ≤ 27 * (1 / (u * L ^ 3)) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
  have h4u : 4 / u / L ^ 3 = 4 * (1 / (u * L ^ 3)) := by field_simp
  -- the error part `S - M`
  obtain ⟨hEs, hSM⟩ := es2_abel hu
  have hErr : |primeExpSum u - ∑' n, es2_g u n| ≤ 4 * CE * (1 / (u * L ^ 3)) := by
    rw [hSM]
    have hb := (hDs.hasSum.mul_left CE).div_const (L ^ 3)
    have := tsum_of_norm_bounded (f := fun n => es2_E n * (es2_g u n - es2_g u (n + 1))) hb
      (fun n => by rw [Real.norm_eq_abs]; exact es2_err_term hu hL huL hK n)
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    calc (CE * ∑' n, es2_D u n) / L ^ 3 ≤ CE * (4 / u) / L ^ 3 := by gcongr
      _ = 4 * CE * (1 / (u * L ^ 3)) := by field_simp
  -- the main part `M`
  have hGs := es2_g_summable hu
  obtain ⟨hBs, hBb⟩ := es2_B hx0.le hx1
  have hQ := hasSum_geometric_of_lt_one hx0.le hx1
  have hr := (hGs.hasSum.sub (hQ.div_const L)).add
    ((hBs.hasSum.sub (hQ.mul_left L)).div_const (L ^ 2))
  have hrb := ((hDs.hasSum.mul_left 1024).div_const (L ^ 3)).add (hasSum_ite_eq 0 (2 : ℝ))
  have hP := tsum_of_norm_bounded
    (f := fun n => es2_g u n - x ^ n / L + (x ^ n * Real.log n - L * x ^ n) / L ^ 2) hrb
    (fun n => by rw [Real.norm_eq_abs]; exact es2_r_term hu hL huL n)
  have hPeq : ∑' n, (es2_g u n - x ^ n / L + (x ^ n * Real.log n - L * x ^ n) / L ^ 2) =
      ∑' n, es2_g u n - (1 - x)⁻¹ / L +
        (∑' n : ℕ, x ^ n * Real.log n - L * (1 - x)⁻¹) / L ^ 2 := hr.tsum_eq
  rw [hPeq, Real.norm_eq_abs] at hP
  have hP' : |∑' n, es2_g u n - (1 - x)⁻¹ / L +
      (∑' n : ℕ, x ^ n * Real.log n - L * (1 - x)⁻¹) / L ^ 2| ≤
        4096 * (1 / (u * L ^ 3)) + 2 := by
    refine hP.trans ?_
    have : (1024 * ∑' n, es2_D u n) / L ^ 3 ≤ 1024 * (4 / u) / L ^ 3 := by gcongr
    have e : 1024 * (4 / u) / L ^ 3 = 4096 * (1 / (u * L ^ 3)) := by field_simp; norm_num
    linarith
  -- facts on `Q = (1-x)⁻¹` and `L' = -log(1-x)`
  have hpos : 0 < 1 - x := by linarith
  have hQ1 : 1 / u ≤ (1 - x)⁻¹ := by
    rw [← one_div]; exact one_div_le_one_div_of_le hpos h1x
  have hQ2 : (1 - x)⁻¹ ≤ 1 / u + 1 := by
    rw [show 1 / u + 1 = (1 + u) / u by field_simp, ← one_div,
      div_le_div_iff₀ hpos hu]
    have : (1 + u) * (1 - x) = 1 + u - x * (1 + u) := by ring
    linarith
  have hQ0 : 0 < (1 - x)⁻¹ := inv_pos.2 hpos
  have huQ1 : 1 ≤ u * (1 - x)⁻¹ := by
    have := mul_le_mul_of_nonneg_left hQ1 hu.le
    rwa [mul_one_div_cancel hu.ne'] at this
  have huQ2 : u * (1 - x)⁻¹ ≤ 1 + u := by
    have := mul_le_mul_of_nonneg_left hQ2 hu.le
    rwa [mul_add, mul_one_div_cancel hu.ne', mul_one] at this
  have hLL : -Real.log (1 - x) - L = Real.log (u * (1 - x)⁻¹) := by
    rw [Real.log_mul hu.ne' hQ0.ne', Real.log_inv, hLdef]; ring
  have hLL0 : 0 ≤ -Real.log (1 - x) - L := by rw [hLL]; exact Real.log_nonneg huQ1
  have hLL1 : -Real.log (1 - x) - L ≤ u := by
    rw [hLL]; have := Real.log_le_sub_one_of_pos (by positivity : 0 < u * (1 - x)⁻¹); linarith
  -- the pieces
  set M := ∑' n, es2_g u n
  set B := ∑' n : ℕ, x ^ n * Real.log n
  set Q := (1 - x)⁻¹ with hQdef
  set L' := -Real.log (1 - x) with hL'def
  have t1a : 0 ≤ (Q - 1 / u) / L := div_nonneg (by linarith) hL0.le
  have t1b : (Q - 1 / u) / L ≤ 1 := (div_le_self (by linarith) hL).trans (by linarith)
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hγQ : 0 ≤ γ * (Q - 1 / u) := mul_nonneg hγ0.le (by linarith)
  have t2a : 0 ≤ γ * (Q - 1 / u) / L ^ 2 := div_nonneg hγQ (by positivity)
  have t2b : γ * (Q - 1 / u) / L ^ 2 ≤ 1 := by
    refine (div_le_self hγQ hL2).trans ?_
    have := mul_le_of_le_one_right hγ0.le (show Q - 1 / u ≤ 1 by linarith)
    linarith
  have t3a : 0 ≤ (L' - L) * Q / L ^ 2 := div_nonneg (by positivity) (by positivity)
  have t3b : (L' - L) * Q / L ^ 2 ≤ 2 := by
    refine (div_le_self (by positivity) hL2).trans ?_
    have : (L' - L) * Q ≤ u * Q := mul_le_mul_of_nonneg_right hLL1 hQ0.le
    linarith
  have t4 : |(B - (L' / (1 - x) - γ * Q)) / L ^ 2| ≤ 3 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < L ^ 2), div_le_iff₀ (by positivity)]
    refine hBb.trans ?_
    have : L ≤ L ^ 2 := le_self_pow₀ hL (by norm_num)
    linarith
  have key : primeExpSum u - (1 + γ / L) / (u * L) =
      (primeExpSum u - M) + (M - Q / L + (B - L * Q) / L ^ 2) + (Q - 1 / u) / L +
        γ * (Q - 1 / u) / L ^ 2 - (L' - L) * Q / L ^ 2 -
        (B - (L' / (1 - x) - γ * Q)) / L ^ 2 := by
    rw [hQdef]; field_simp; ring
  rw [key, div_eq_mul_one_div (4 * CE + 4096 + 243)]
  have a1 := abs_le.1 hErr
  have a2 := abs_le.1 hP'
  have a4 := abs_le.1 t4
  rw [abs_le]; constructor <;> linarith

end RntPaper
