import RntPaper.Tail.Phi
import RntPaper.Tail.Laplace
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Tail asymptotics of `Λ` (paper Theorem 1.6, §5.4)

Under the prime number theorem in the form `θ ~ id`,

  `-log(I_N - Λ) ~ 2π √(N / (3 log N))`,   `I_N = F (primesLE N)`,

and, if moreover `p_n ~ n log n`, `-log(I_{p_n} - Λ) ~ (2π/√3) √n`.
The PNT is a hypothesis here; `RntPaper.PNT` discharges it with
PrimeNumberTheoremAnd. Lemmas A–C are in `RntPaper/Tail/`, the unconditional
sandwich (paper Lemma 5.5) in `RntPaper/Tail/Laplace.lean`.

Write `c = 2π/√3`, `a = ζ(2) = π²/6` (so `c² = 8a`), `ℓ = log N`, `r_N = √(N/ℓ)`,
`X = e^{ℓ/2} = √N`. Then `λ_N = c r_N`, and:

* `tail_upper_bound`: for `κ < 1`, eventually `I_N - Λ ≤ exp(-κ c r_N)`, from
  `tail_le_of_primePhi` and `N t + Φ(t) ≥ κ c r_N + 2ℓ + 1` for all `t > 0`;
* `tail_lower_bound`: for `κ > 1`, eventually `exp(-κ c r_N) ≤ I_N - Λ`, from
  `tail_ge_of_window` on the window `[τ, (1+ε)τ]`, `τ = √(2a/(Nℓ))`.
-/

namespace RntPaper

open QProduct Real Filter Topology Asymptotics MeasureTheory Set

/-! ## Elementary growth facts -/

/-- `ℓ² ≤ K e^{γℓ}` for all large `ℓ`. -/
theorem eventually_sq_le_exp {γ K : ℝ} (hγ : 0 < γ) (hK : 0 < K) :
    ∀ᶠ ℓ : ℝ in atTop, ℓ ^ 2 ≤ K * rexp (γ * ℓ) := by
  have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp (tendsto_id.const_mul_atTop hγ)
  have hγ2 : 0 < γ ^ 2 := by positivity
  filter_upwards [h.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < γ ^ 2 * K))] with ℓ hℓ
  simp only [Function.comp, id] at hℓ
  have he : rexp (-(γ * ℓ)) * rexp (γ * ℓ) = 1 := by rw [← exp_add]; simp
  have hpos := exp_pos (γ * ℓ)
  have h1 : γ ^ 2 * ℓ ^ 2 < γ ^ 2 * (K * rexp (γ * ℓ)) := by
    have := mul_lt_mul_of_pos_right hℓ hpos
    calc γ ^ 2 * ℓ ^ 2 = (γ * ℓ) ^ 2 * rexp (-(γ * ℓ)) * rexp (γ * ℓ) := by
          rw [mul_assoc, he, mul_one, mul_pow]
      _ < γ ^ 2 * K * rexp (γ * ℓ) := this
      _ = _ := by ring
  exact ((mul_lt_mul_iff_right₀ hγ2).mp h1).le

theorem tendsto_log_natCast : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `c² = 8 ζ(2)` for `c = 2π/√3`. -/
theorem c_sq : (2 * π / √3) ^ 2 = 8 * (π ^ 2 / 6) := by
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring

/-- For `N ≥ 3`, with `ℓ = log N` and `X = e^{ℓ/2}`: `N = X²`, `X ≥ 1`, and
`X/ℓ ≤ √(N/ℓ) ≤ X`. -/
theorem sqrt_div_log_bounds {N : ℕ} (hN : 3 ≤ N) :
    (N : ℝ) = rexp (Real.log N / 2) ^ 2 ∧ 1 ≤ rexp (Real.log N / 2) ∧
      rexp (Real.log N / 2) / Real.log N ≤ √(N / Real.log N) ∧
      √(N / Real.log N) ≤ rexp (Real.log N / 2) ∧
      √(N / Real.log N) ^ 2 = N / Real.log N := by
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hℓ := one_le_log_of_three_le hN
  set ℓ := Real.log N
  set X := rexp (ℓ / 2)
  have hX2 : (N : ℝ) = X ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast; rw [show 2 * (ℓ / 2) = ℓ by ring, exp_log hN0]
  have hX1 : 1 ≤ X := Real.one_le_exp (by linarith)
  refine ⟨hX2, hX1, ?_, ?_, Real.sq_sqrt (by positivity)⟩
  · calc X / ℓ = √((X / ℓ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(N / ℓ) := by
          apply Real.sqrt_le_sqrt
          rw [div_pow, hX2]
          exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by nlinarith)
  · calc √(N / ℓ) ≤ √(N : ℝ) := Real.sqrt_le_sqrt (div_le_self hN0.le hℓ)
      _ = X := by rw [hX2, Real.sqrt_sq (by positivity)]

/-- The saddle-point estimate behind `tail_upper_bound`, for fixed parameters: every
`t > 0` has `N t + Φ(t) ≥ κ₁ c r + 2ℓ + 1`. -/
theorem saddle_lower {N : ℕ} (hN : 3 ≤ N) {c a κ₁ κ' ε t₀' d : ℝ}
    (hc0 : 0 < c) (hc2 : c ^ 2 = 8 * a) (ha0 : 0 < a) (hκ₁0 : 0 < κ₁) (hκ₁κ' : κ₁ < κ')
    (hε0 : 0 < ε) (hε1 : ε < 1 / 3) (hκ'ε : κ' ^ 2 * (1 + 2 * ε) ≤ 1 - ε)
    (ht₀'0 : 0 < t₀') (hd : d = (κ' - κ₁) * c)
    (hPt : ∀ t, 0 < t → t < t₀' → (1 - ε) * a < t * Real.log t⁻¹ * primePhi t)
    (hXa : Real.log N ^ 2 ≤ t₀' / (2 * κ₁ * c) * rexp (Real.log N / 2))
    (hXb : Real.log N ^ 2 ≤ t₀' / 6 * rexp (Real.log N / 2))
    (hXc : Real.log N ^ 2 ≤ d / 3 * rexp (Real.log N / 2))
    (hXd : Real.log N ^ 2 ≤ rexp (Real.log N / 2))
    (hYa : Real.log N ^ 2 ≤ (1 - ε) * a / (2 * κ₁ * c) * rexp (ε * Real.log N))
    (hYb : Real.log N ^ 2 ≤ (1 - ε) * a / 6 * rexp (ε * Real.log N)) :
    ∀ t : ℝ, 0 < t →
      κ₁ * (c * √(N / Real.log N)) + 2 * Real.log N + 1 ≤ N * t + primePhi t := by
  obtain ⟨hX2, hX1, hrlo, hrhi, hrsq⟩ := sqrt_div_log_bounds hN
  have hℓ := one_le_log_of_three_le hN
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set ℓ := Real.log N with hℓdef
  set X := rexp (ℓ / 2) with hXdef
  set Y := rexp (ε * ℓ) with hYdef
  set r := √(N / ℓ) with hrdef
  have hY1 : 1 ≤ Y := Real.one_le_exp (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have ht₁XY : rexp (-((1 / 2 + ε) * ℓ)) * (X * Y) = 1 := by
    rw [hXdef, hYdef, ← exp_add, ← exp_add]; ring_nf; simp
  clear_value ℓ X Y r
  have hd0 : 0 < d := by rw [hd]; exact mul_pos (by linarith) hc0
  have hℓ2 : ℓ ≤ ℓ ^ 2 := by nlinarith only [hℓ]
  have hℓ21 : 1 ≤ ℓ ^ 2 := one_le_pow₀ hℓ
  have hκc : 0 < κ₁ * c := mul_pos hκ₁0 hc0
  have h1ε : 0 < (1 - ε) * a := mul_pos (by linarith) ha0
  set B := κ₁ * (c * r) + 2 * ℓ + 1 with hBdef
  have hBle : B ≤ κ₁ * c * X + 3 * ℓ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hrhi hκc.le
    rw [hBdef]; linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  clear_value B
  -- C1: `B ≤ N t₀'`
  have hC1 : B ≤ N * t₀' := by
    have e1 : κ₁ * c ≤ t₀' / 2 * X := by
      have h := mul_le_mul_of_nonneg_left (hℓ21.trans hXa) hκc.le
      have he : κ₁ * c * (t₀' / (2 * κ₁ * c) * X) = t₀' / 2 * X := by field_simp
      linarith
    have e2 : 3 * ℓ ^ 2 ≤ t₀' / 2 * X := by linarith
    have e3 := mul_le_mul_of_nonneg_right e1 (by positivity : (0 : ℝ) ≤ X)
    have e4 : t₀' / 2 * X ≤ t₀' / 2 * X * X :=
      le_mul_of_one_le_right (by positivity) hX1
    rw [hX2]
    nlinarith only [hBle, e2, e3, e4]
  -- C2: `2ℓ + 1 ≤ d r`
  have hC2 : 2 * ℓ + 1 ≤ d * r := by
    have h3 : 3 * ℓ * ℓ ≤ d * X := by linarith
    have h4 : 3 * ℓ ≤ d * (X / ℓ) := by
      rw [mul_div_assoc', le_div_iff₀ (by linarith)]; exact h3
    have := mul_le_mul_of_nonneg_left hrlo hd0.le
    linarith
  set t₁ := rexp (-((1 / 2 + ε) * ℓ)) with ht₁def
  have ht₁0 : 0 < t₁ := exp_pos _
  have hL1 : Real.log t₁⁻¹ = (1 / 2 + ε) * ℓ := by
    rw [ht₁def, Real.log_inv, Real.log_exp]; ring
  clear_value t₁
  -- C3: `t₁ < t₀'`
  have hC3 : t₁ < t₀' := by
    have hX : 2 ≤ X * t₀' := by
      have h := hℓ21.trans hXb
      have : t₀' / 6 * X = X * t₀' / 6 := by ring
      linarith
    have hXY : X ≤ X * Y := le_mul_of_one_le_right (by positivity) hY1
    have h5 : t₁ * (X * t₀') ≤ t₁ * (X * Y) * t₀' := by
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXY ht₀'0.le) ht₁0.le
      linarith
    rw [ht₁XY, one_mul] at h5
    have h6 := mul_le_mul_of_nonneg_left hX ht₁0.le
    linarith
  -- C4: `B t₁ (1/2+ε) ℓ ≤ (1-ε) a`
  have hC4 : B * (t₁ * ((1 / 2 + ε) * ℓ)) ≤ (1 - ε) * a := by
    have k1 : κ₁ * c * X * ℓ ≤ (1 - ε) * a / 2 * (X * Y) := by
      have h := mul_le_mul_of_nonneg_left (hℓ2.trans hYa) hκc.le
      have he : κ₁ * c * ((1 - ε) * a / (2 * κ₁ * c) * Y) = (1 - ε) * a / 2 * Y := by
        field_simp
      have := mul_le_mul_of_nonneg_left (h.trans he.le) (by positivity : (0 : ℝ) ≤ X)
      linarith
    have k2 : 3 * ℓ ^ 2 * ℓ ≤ (1 - ε) * a / 2 * (X * Y) := by
      have h3 : ℓ ^ 2 * ℓ ≤ ℓ ^ 2 * ℓ ^ 2 := mul_le_mul_of_nonneg_left hℓ2 (by positivity)
      have h4 : ℓ ^ 2 * ℓ ^ 2 ≤ X * ((1 - ε) * a / 6 * Y) :=
        mul_le_mul hXd hYb (by positivity) (by positivity)
      linarith
    have hBℓ : B * ((1 / 2 + ε) * ℓ) ≤ (1 - ε) * a * (X * Y) := by
      have hm : (1 / 2 + ε) * ℓ ≤ ℓ := by nlinarith only [hε1, hℓ]
      have e1 := mul_le_mul_of_nonneg_left hm hB0
      have e2 := mul_le_mul_of_nonneg_right hBle (by linarith : (0 : ℝ) ≤ ℓ)
      linarith
    have := mul_le_mul_of_nonneg_left hBℓ ht₁0.le
    have he : t₁ * ((1 - ε) * a * (X * Y)) = (1 - ε) * a * (t₁ * (X * Y)) := by ring
    rw [he, ht₁XY, mul_one] at this
    linarith
  intro t ht
  have hΦ0 := primePhi_nonneg ht
  rcases le_or_gt t₀' t with h | h
  · have : (N : ℝ) * t₀' ≤ N * t := mul_le_mul_of_nonneg_left h hN0.le
    linarith
  have hPt' := hPt t ht h
  rcases le_or_gt (Real.log t⁻¹) ((1 / 2 + ε) * ℓ) with hL | hL
  · -- saddle region: `(N t + Φ)² ≥ 4 N t Φ ≥ (κ' c r)²`
    have htΦ : (1 - ε) * a < t * primePhi t * ((1 / 2 + ε) * ℓ) := by
      have := mul_le_mul_of_nonneg_left hL (mul_nonneg ht.le hΦ0)
      have he : t * Real.log t⁻¹ * primePhi t = t * primePhi t * Real.log t⁻¹ := by ring
      linarith
    have hm0 : 0 < (1 / 2 + ε) * ℓ := by positivity
    have e3 : κ' ^ 2 * (8 * a) * (N / ℓ) ≤ 4 * (N * (t * primePhi t)) := by
      have h_eq : κ' ^ 2 * (8 * a) * (N / ℓ) * ((1 / 2 + ε) * ℓ) =
          4 * a * N * (κ' ^ 2 * (1 + 2 * ε)) := by
        field_simp; ring
      have h_le := mul_le_mul_of_nonneg_left hκ'ε (by positivity : (0 : ℝ) ≤ 4 * a * N)
      have h_lt := mul_lt_mul_of_pos_left htΦ (by positivity : (0 : ℝ) < 4 * N)
      refine le_of_mul_le_mul_right ?_ hm0
      linarith
    have e2 : 4 * (N * (t * primePhi t)) ≤ (N * t + primePhi t) ^ 2 := by
      nlinarith only [sq_nonneg (N * t - primePhi t)]
    have e1 : (κ' * (c * r)) ^ 2 = κ' ^ 2 * (8 * a) * (N / ℓ) := by
      rw [mul_pow, mul_pow, hc2, hrsq]; ring
    have hsq : (κ' * (c * r)) ^ 2 ≤ (N * t + primePhi t) ^ 2 := by linarith
    have hκ'0 : 0 < κ' := by linarith
    have hZ := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    have : κ₁ * (c * r) + d * r = κ' * (c * r) := by rw [hd]; ring
    linarith
  · -- small `t`: `Φ(t) ≥ Φ(t₁) ≥ B`
    have htt₁ : t ≤ t₁ := by
      rw [Real.log_inv] at hL
      have hlt : Real.log t < -((1 / 2 + ε) * ℓ) := by linarith
      have := Real.exp_lt_exp.mpr hlt
      rw [exp_log ht] at this
      rw [ht₁def]
      exact this.le
    have hΦ1 := primePhi_anti ht htt₁
    have hPt₁ := hPt t₁ ht₁0 hC3
    rw [hL1] at hPt₁
    have hB1 : B ≤ primePhi t₁ := by
      by_contra hcon
      push Not at hcon
      have hm : 0 < t₁ * ((1 / 2 + ε) * ℓ) := by positivity
      have := mul_lt_mul_of_pos_left hcon hm
      have he : t₁ * ((1 / 2 + ε) * ℓ) * primePhi t₁ = t₁ * ((1 / 2 + ε) * ℓ) * primePhi t₁ := rfl
      linarith
    have : 0 ≤ (N : ℝ) * t := by positivity
    linarith

/-- The window estimate behind `tail_lower_bound`, for fixed parameters. -/
theorem window_lower {N q : ℕ} (hN : 3 ≤ N) (hq : q.Prime) (hNq : N < q) {c a κ κ' ε t₀ : ℝ}
    (hc0 : 0 < c) (hc2 : c ^ 2 = 8 * a) (ha1 : 1 ≤ a) (hε0 : 0 < ε) (hε12 : ε ≤ 1 / 2)
    (hκκ' : κ' < κ) (hεK : (1 + ε) / (1 - ε) + (1 + ε) ^ 2 ≤ 2 * κ')
    (ht₀0 : 0 < t₀) (ht₀h : t₀ ≤ 1 / 2)
    (hPt : ∀ t, 0 < t → t < t₀ → t * Real.log t⁻¹ * primePhi t < (1 + ε) * a)
    (hq1 : (q : ℝ) ≤ (1 + ε) * N)
    (hG2 : Real.log N ^ 2 ≤ t₀ ^ 2 / (4 * (1 + ε) ^ 2 * a) * rexp (Real.log N / 2))
    (hG3 : 2 + Real.log (2 * a) / ε ≤ Real.log N)
    (hG4a : Real.log (6 / ε) ≤ Real.log N)
    (hG4 : Real.log N ^ 2 ≤ (κ - κ') * c / 2 * rexp (Real.log N / 2)) :
    rexp (-(κ * (c * √(N / Real.log N)))) ≤ F (primesLE N) - primeLambda := by
  obtain ⟨hX2, hX1, hrlo, _, hrsq⟩ := sqrt_div_log_bounds hN
  have hℓ := one_le_log_of_three_le hN
  have hN0 : (0 : ℝ) < N := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hℓN : Real.log N ≤ N := by
    have := Real.log_le_sub_one_of_pos hN0; linarith
  have hlogℓ : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hℓ
  have hlogNℓ : Real.log (N * Real.log N) = Real.log N + Real.log (Real.log N) :=
    Real.log_mul hN0.ne' (by linarith)
  set ℓ := Real.log N with hℓdef
  set X := rexp (ℓ / 2) with hXdef
  set r := √(N / ℓ) with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hXℓ : rexp ℓ = X ^ 2 := by
    rw [hXdef, ← Real.exp_nat_mul]; push_cast; ring_nf
  clear_value ℓ X r
  have ha0 : 0 < a := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hκκ'c : 0 < (κ - κ') * c := mul_pos (by linarith) hc0
  -- `τ`
  set τ := √(2 * a / (N * ℓ)) with hτdef
  have hτ0 : 0 < τ := Real.sqrt_pos.2 (by positivity)
  have hτsq : τ ^ 2 = 2 * a / (N * ℓ) := Real.sq_sqrt (by positivity)
  have hlogτ : Real.log τ = (Real.log (2 * a) - ℓ - Real.log ℓ) / 2 := by
    rw [hτdef, Real.log_sqrt (by positivity), Real.log_div (by positivity) (by positivity),
      hlogNℓ]
    ring
  clear_value τ
  have hτNℓ : τ ^ 2 * (N * ℓ) = 2 * a := by rw [hτsq]; field_simp
  -- `N τ = (c/2) r`
  have hNτ : N * τ = c / 2 * r := by
    have h1 : (N * τ) ^ 2 = (c / 2 * r) ^ 2 := by
      rw [mul_pow, mul_pow, div_pow, hc2, hrsq, hτsq]; field_simp; ring
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1
  -- `(1+ε)τ < t₀`
  have hτt₀ : (1 + ε) * τ < t₀ := by
    have hK : 4 * (1 + ε) ^ 2 * a ≤ t₀ ^ 2 * X := by
      have h := hG2.trans' (one_le_pow₀ hℓ)
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h
      linarith
    have hXX : t₀ ^ 2 * X ≤ t₀ ^ 2 * X ^ 2 := by
      have : X ≤ X ^ 2 := by nlinarith only [hX1]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hsq : ((1 + ε) * τ) ^ 2 < t₀ ^ 2 := by
      rw [mul_pow, hτsq]
      have hNℓ : N ≤ (N : ℝ) * ℓ := le_mul_of_one_le_right hN0.le hℓ
      have h1 : (1 + ε) ^ 2 * (2 * a / (N * ℓ)) ≤ (1 + ε) ^ 2 * (2 * a / N) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hN0 hNℓ)
          (by positivity)
      have h2 : (1 + ε) ^ 2 * (2 * a / N) < t₀ ^ 2 := by
        rw [hX2, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
        have hpos : 0 < (1 + ε) ^ 2 * a := by positivity
        nlinarith only [hK, hXX, hpos]
      linarith
    exact (pow_lt_pow_iff_left₀ (by positivity) ht₀0.le two_ne_zero).mp hsq
  have hτ1 : τ ≤ 1 := by nlinarith only [hτt₀, ht₀h, hε0, hτ0]
  -- `log(1/t) ≥ (1-ε)ℓ/2` on the window
  have hL : ∀ t ∈ Icc τ ((1 + ε) * τ), (1 - ε) * ℓ / 2 ≤ Real.log t⁻¹ := by
    intro t ht
    have ht0 : 0 < t := hτ0.trans_le ht.1
    have h1 : Real.log t ≤ Real.log (1 + ε) + Real.log τ := by
      rw [← Real.log_mul (by linarith) hτ0.ne']
      exact Real.log_le_log ht0 ht.2
    have h2 : Real.log (1 + ε) ≤ ε := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + ε); linarith
    have h3 : ε * (2 + Real.log (2 * a) / ε) = 2 * ε + Real.log (2 * a) := by
      field_simp
    have h4 := mul_le_mul_of_nonneg_left hG3 hε0.le
    rw [Real.log_inv, hlogτ] at *
    linarith
  -- `Φ ≤ A` on the window
  set A := (1 + ε) / (1 - ε) * (N * τ) with hAdef
  have hΦA : ∀ t ∈ Icc τ ((1 + ε) * τ), primePhi t ≤ A := by
    intro t ht
    have ht0 : 0 < t := hτ0.trans_le ht.1
    have hP := hPt t ht0 (ht.2.trans_lt hτt₀)
    have hΦ0 := primePhi_nonneg ht0
    have hLt := hL t ht
    have e1 : τ * ((1 - ε) * ℓ / 2) * primePhi t ≤ t * Real.log t⁻¹ * primePhi t :=
      mul_le_mul_of_nonneg_right (mul_le_mul ht.1 hLt (by nlinarith only [hε12, hℓ0])
        ht0.le) hΦ0
    have e2 : (1 + ε) * a = (1 + ε) * (τ ^ 2 * (N * ℓ)) / 2 := by rw [hτNℓ]; ring
    -- `(1-ε) Φ < (1+ε) N τ`, after dividing by `τ ℓ / 2`
    have e3 : τ * ℓ / 2 * ((1 - ε) * primePhi t) < τ * ℓ / 2 * ((1 + ε) * (N * τ)) := by
      have : τ * ((1 - ε) * ℓ / 2) * primePhi t = τ * ℓ / 2 * ((1 - ε) * primePhi t) := by ring
      have : (1 + ε) * (τ ^ 2 * (N * ℓ)) / 2 = τ * ℓ / 2 * ((1 + ε) * (N * τ)) := by ring
      linarith
    have e4 := lt_of_mul_lt_mul_left e3 (by positivity)
    rw [hAdef, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    linarith
  have hwin := tail_ge_of_window N q hq hNq hτ0 hε0 hΦA
  -- exponent bound: `A + q(1+ε)τ ≤ κ' c r`
  have hexp : A + q * ((1 + ε) * τ) ≤ κ' * (c * r) := by
    have h1 : (q : ℝ) * ((1 + ε) * τ) ≤ (1 + ε) ^ 2 * (N * τ) := by
      have := mul_le_mul_of_nonneg_right hq1 (by positivity : (0 : ℝ) ≤ (1 + ε) * τ)
      linarith
    have h2 : ((1 + ε) / (1 - ε) + (1 + ε) ^ 2) * (N * τ) ≤ 2 * κ' * (N * τ) :=
      mul_le_mul_of_nonneg_right hεK (by positivity)
    rw [hAdef]
    have : 2 * κ' * (N * τ) = κ' * (c * r) := by rw [hNτ]; ring
    linarith
  -- prefactor bound: `e^{-(κ-κ') c r} ≤ e^{-τ} ετ/(1+ετ)`
  have hpre : rexp (-((κ - κ') * (c * r))) ≤ rexp (-τ) * (ε * τ / (1 + ε * τ)) := by
    -- right side `≥ ε τ / 6 ≥ ε / (6 X²)`
    have hτN : 1 / (N : ℝ) ≤ τ := by
      have hs : (1 / (N : ℝ)) ^ 2 ≤ τ ^ 2 := by
        rw [hτsq, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        have e1 := mul_le_mul_of_nonneg_left hℓN hN0.le
        have e2 := mul_le_mul_of_nonneg_right ha1 (sq_nonneg (N : ℝ))
        nlinarith only [e1, e2, sq_nonneg (N : ℝ)]
      exact (pow_le_pow_iff_left₀ (by positivity) hτ0.le two_ne_zero).mp hs
    have he1 : 1 / 3 ≤ rexp (-τ) := by
      have hτ12 : τ ≤ 1 / 2 := by nlinarith only [hτt₀, ht₀h, hε0, hτ0]
      have := Real.add_one_le_exp (-τ); linarith
    have hετ : ε * τ / 2 ≤ ε * τ / (1 + ε * τ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith only [hε12, hτ1, hε0, hτ0])
    have hR : ε / (6 * X ^ 2) ≤ rexp (-τ) * (ε * τ / (1 + ε * τ)) := by
      have h1 : ε / (6 * X ^ 2) = 1 / 3 * (ε * (1 / N) / 2) := by rw [hX2]; field_simp; ring
      rw [h1]
      refine mul_le_mul he1 (hετ.trans' ?_) (by positivity) (exp_pos _).le
      have := mul_le_mul_of_nonneg_left hτN hε0.le
      linarith
    -- left side
    have hG : (Real.log (6 / ε) + ℓ) * ℓ ≤ (κ - κ') * c * X := by
      have : (Real.log (6 / ε) + ℓ) * ℓ ≤ 2 * ℓ ^ 2 := by nlinarith only [hG4a, hℓ0]
      linarith
    have hL1 : Real.log (6 / ε) + ℓ ≤ (κ - κ') * (c * r) := by
      have h1 : Real.log (6 / ε) + ℓ ≤ (κ - κ') * c * (X / ℓ) := by
        rw [mul_div_assoc', le_div_iff₀ hℓ0]; exact hG
      have := mul_le_mul_of_nonneg_left hrlo hκκ'c.le
      linarith
    have hL2 : rexp (-((κ - κ') * (c * r))) ≤ ε / (6 * X ^ 2) := by
      have h6 : rexp (Real.log (6 / ε) + ℓ) = 6 * X ^ 2 / ε := by
        rw [exp_add, exp_log (by positivity), hXℓ]; ring
      have := Real.exp_le_exp.mpr (neg_le_neg hL1)
      rw [exp_neg (Real.log (6 / ε) + ℓ), h6, inv_div] at this
      exact this
    exact hL2.trans hR
  calc rexp (-(κ * (c * r)))
      = rexp (-((κ - κ') * (c * r))) * rexp (-(κ' * (c * r))) := by rw [← exp_add]; ring_nf
    _ ≤ rexp (-τ) * (ε * τ / (1 + ε * τ)) * rexp (-(A + q * ((1 + ε) * τ))) :=
        mul_le_mul hpre (Real.exp_le_exp.mpr (neg_le_neg hexp)) (exp_pos _).le
          (by positivity)
    _ ≤ _ := hwin

section PNT

variable (hθ : Chebyshev.theta ~[atTop] id)
include hθ

/-! ## Upper bound for `I_N - Λ` -/

/-- For `κ < 1`, eventually `I_N - Λ ≤ exp(-κ (2π/√3) √(N/log N))`. -/
theorem tail_upper_bound {κ : ℝ} (hκ : κ < 1) :
    ∀ᶠ N : ℕ in atTop, F (primesLE N) - primeLambda ≤
      rexp (-(κ * (2 * π / √3 * √(N / Real.log N)))) := by
  have hc0 : 0 < 2 * π / √3 := by positivity
  have ha0 : 0 < π ^ 2 / 6 := by positivity
  set κ₁ := max κ (1 / 2) with hκ₁def
  have hκ₁ : κ₁ < 1 := max_lt hκ (by norm_num)
  have hκ₁0 : 0 < κ₁ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hκκ₁ : κ ≤ κ₁ := le_max_left _ _
  set κ' := (1 + κ₁) / 2 with hκ'def
  have hκ₁κ' : κ₁ < κ' := by rw [hκ'def]; linarith
  have hκ'1 : κ' < 1 := by rw [hκ'def]; linarith
  have hκ'0 : 0 < κ' := by linarith
  have hκ'sq : κ' ^ 2 < 1 := by nlinarith only [hκ'0, hκ'1]
  set ε := (1 - κ' ^ 2) / 3 with hεdef
  have hε0 : 0 < ε := by rw [hεdef]; linarith
  have hε1 : ε < 1 / 3 := by rw [hεdef]; nlinarith only [hκ'0]
  have hκ'ε : κ' ^ 2 * (1 + 2 * ε) ≤ 1 - ε := by
    rw [hεdef]; nlinarith only [hκ'sq, hκ'0]
  obtain ⟨t₀, ht₀, hP⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1
    ((primePhi_asymp hθ).eventually
      (lt_mem_nhds (show (1 - ε) * (π ^ 2 / 6) < π ^ 2 / 6 by nlinarith only [hε0, ha0])))
  set t₀' := min t₀ (1 / 2) with ht₀'def
  have ht₀'0 : 0 < t₀' := lt_min ht₀ (by norm_num)
  have hPt : ∀ t, 0 < t → t < t₀' →
      (1 - ε) * (π ^ 2 / 6) < t * Real.log t⁻¹ * primePhi t :=
    fun t h0 h1 => hP ⟨h0, h1.trans_le (min_le_left _ _)⟩
  set c := 2 * π / √3 with hc
  set a := π ^ 2 / 6 with ha
  have hc2 : c ^ 2 = 8 * a := c_sq
  set d := (κ' - κ₁) * c with hddef
  have hd0 : 0 < d := mul_pos (by linarith) hc0
  have h1ε : 0 < (1 - ε) * a := mul_pos (by linarith) ha0
  clear_value c a κ₁ κ' ε t₀' d
  filter_upwards [eventually_ge_atTop 3,
    tendsto_log_natCast.eventually (eventually_sq_le_exp (γ := 1 / 2)
      (K := min (min (t₀' / (2 * κ₁ * c)) (t₀' / 6)) (min (d / 3) 1)) (by norm_num)
      (by positivity)),
    tendsto_log_natCast.eventually (eventually_sq_le_exp (γ := ε)
      (K := min ((1 - ε) * a / (2 * κ₁ * c)) ((1 - ε) * a / 6)) hε0 (by positivity))]
    with N hN hXe hYe
  have hX0 : 0 ≤ rexp (Real.log N / 2) := (exp_pos _).le
  have hY0 : 0 ≤ rexp (ε * Real.log N) := (exp_pos _).le
  have hXe' : Real.log N ^ 2 ≤ min (min (t₀' / (2 * κ₁ * c)) (t₀' / 6)) (min (d / 3) 1) *
      rexp (Real.log N / 2) := by
    rw [show Real.log N / 2 = 1 / 2 * Real.log N by ring]; exact hXe
  have hsad := saddle_lower hN hc0 hc2 ha0 hκ₁0 hκ₁κ' hε0 hε1 hκ'ε ht₀'0 hddef hPt
    (hXe'.trans (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) hX0))
    (hXe'.trans (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) hX0))
    (hXe'.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hX0))
    (hXe'.trans (by
      have := mul_le_mul_of_nonneg_right
        ((min_le_right (min (t₀' / (2 * κ₁ * c)) (t₀' / 6)) _).trans (min_le_right (d / 3) 1)) hX0
      linarith))
    (hYe.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hY0))
    (hYe.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hY0))
  have hmain := tail_le_of_primePhi N hN hsad
  have hcr : 0 ≤ c * √(N / Real.log N) := mul_nonneg hc0.le (Real.sqrt_nonneg _)
  refine hmain.trans (Real.exp_le_exp.mpr ?_)
  have := mul_le_mul_of_nonneg_right hκκ₁ hcr
  linarith

/-! ## Lower bound for `I_N - Λ` -/

/-- For `κ > 1`, eventually `exp(-κ (2π/√3) √(N/log N)) ≤ I_N - Λ`. -/
theorem tail_lower_bound {κ : ℝ} (hκ : 1 < κ) :
    ∀ᶠ N : ℕ in atTop, rexp (-(κ * (2 * π / √3 * √(N / Real.log N)))) ≤
      F (primesLE N) - primeLambda := by
  have hc0 : 0 < 2 * π / √3 := by positivity
  have ha1 : 1 ≤ π ^ 2 / 6 := by nlinarith only [Real.pi_gt_three]
  set κ' := (1 + κ) / 2 with hκ'def
  have hκ'1 : 1 < κ' := by rw [hκ'def]; linarith
  have hκκ' : κ' < κ := by rw [hκ'def]; linarith
  set ε := min (1 / 2) ((κ' - 1) * 2 / 7) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε12 : ε ≤ 1 / 2 := min_le_left _ _
  have hε7 : 7 * ε ≤ 2 * (κ' - 1) := by
    have := min_le_right (1 / 2 : ℝ) ((κ' - 1) * 2 / 7); rw [← hεdef] at this; linarith
  have hεK : (1 + ε) / (1 - ε) + (1 + ε) ^ 2 ≤ 2 * κ' := by
    have h1 : (1 + ε) / (1 - ε) ≤ 1 + 4 * ε := by
      rw [div_le_iff₀ (by linarith)]; nlinarith only [hε0, hε12]
    have h2 : (1 + ε) ^ 2 ≤ 1 + 3 * ε := by nlinarith only [hε0, hε12]
    linarith
  obtain ⟨t₀, ht₀, hP⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1
    ((primePhi_asymp hθ).eventually
      (gt_mem_nhds (show π ^ 2 / 6 < (1 + ε) * (π ^ 2 / 6) by nlinarith only [hε0, ha1])))
  set t₀' := min t₀ (1 / 2) with ht₀'def
  have ht₀'0 : 0 < t₀' := lt_min ht₀ (by norm_num)
  have ht₀'h : t₀' ≤ 1 / 2 := min_le_right _ _
  have hPt : ∀ t, 0 < t → t < t₀' →
      t * Real.log t⁻¹ * primePhi t < (1 + ε) * (π ^ 2 / 6) :=
    fun t h0 h1 => hP ⟨h0, h1.trans_le (min_le_left _ _)⟩
  set c := 2 * π / √3 with hc
  set a := π ^ 2 / 6 with ha
  have hc2 : c ^ 2 = 8 * a := c_sq
  have ha0 : 0 < a := by linarith
  have hκκ'c : 0 < (κ - κ') * c := mul_pos (by linarith) hc0
  clear_value c a κ' ε t₀'
  filter_upwards [eventually_ge_atTop 3, exists_prime_between hθ hε0,
    tendsto_log_natCast.eventually (eventually_sq_le_exp (γ := 1 / 2)
      (K := min (t₀' ^ 2 / (4 * (1 + ε) ^ 2 * a)) ((κ - κ') * c / 2)) (by norm_num)
      (by positivity)),
    tendsto_log_natCast.eventually (eventually_ge_atTop (2 + Real.log (2 * a) / ε)),
    tendsto_log_natCast.eventually (eventually_ge_atTop (Real.log (6 / ε)))]
    with N hN hq hXe hG3 hG4a
  obtain ⟨q, hqp, hNq, hq1⟩ := hq
  have hX0 : 0 ≤ rexp (Real.log N / 2) := (exp_pos _).le
  have hXe' : Real.log N ^ 2 ≤ min (t₀' ^ 2 / (4 * (1 + ε) ^ 2 * a)) ((κ - κ') * c / 2) *
      rexp (Real.log N / 2) := by
    rw [show Real.log N / 2 = 1 / 2 * Real.log N by ring]; exact hXe
  exact window_lower hN hqp hNq hc0 hc2 ha1 hε0 hε12 hκκ' hεK ht₀'0 ht₀'h hPt hq1
    (hXe'.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hX0)) hG3 hG4a
    (hXe'.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hX0))

/-! ## The asymptotics -/

/-- **Theorem 1.6, `N`-form.** Under `θ ~ id`,
`-log(I_N - Λ) / √(N / log N) → 2π/√3`. -/
theorem tail_asymptotic :
    Tendsto (fun N : ℕ => -Real.log (F (primesLE N) - primeLambda) / √(N / Real.log N))
      atTop (𝓝 (2 * π / √3)) := by
  have hc0 : 0 < 2 * π / √3 := by positivity
  set c := 2 * π / √3 with hc
  -- common facts for large `N`
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < √(N / Real.log N) ∧ 0 < F (primesLE N) - primeLambda := by
    filter_upwards [eventually_ge_atTop 3, tail_lower_bound hθ (κ := 2) (by norm_num)]
      with N hN hL
    have hN0 : (0 : ℝ) < N := by
      have : (3 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hℓ := one_le_log_of_three_le hN
    exact ⟨Real.sqrt_pos.2 (by positivity), (exp_pos _).trans_le hL⟩
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- `b < c`
    set κ := max (1 / 2) ((b / c + 1) / 2) with hκdef
    have hbc : b / c < 1 := by rw [div_lt_one hc0]; exact hb
    have hκ1 : κ < 1 := max_lt (by norm_num) (by linarith)
    have hκb : b < κ * c := by
      have : b / c < κ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      rwa [div_lt_iff₀ hc0] at this
    filter_upwards [hpos, tail_upper_bound hθ hκ1] with N ⟨hr, hI⟩ hU
    have hlog := Real.log_le_log hI hU
    rw [Real.log_exp] at hlog
    rw [lt_div_iff₀ hr]
    have := mul_lt_mul_of_pos_right hκb hr
    linarith
  · -- `c < b`
    set κ := (b / c + 1) / 2 with hκdef
    have hbc : 1 < b / c := by rw [one_lt_div hc0]; exact hb
    have hκ1 : 1 < κ := by rw [hκdef]; linarith
    have hκb : κ * c < b := by
      have : κ < b / c := by rw [hκdef]; linarith
      rwa [lt_div_iff₀ hc0] at this
    filter_upwards [hpos, tail_lower_bound hθ hκ1] with N ⟨hr, hI⟩ hL
    have hlog := Real.log_le_log (exp_pos _) hL
    rw [Real.log_exp] at hlog
    rw [div_lt_iff₀ hr]
    have := mul_lt_mul_of_pos_right hκb hr
    linarith

omit hθ in
/-- `p_n ~ n log n` implies `p_n / log p_n ~ n`. -/
theorem nth_prime_div_log_tendsto
    (hpn : (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) ~[atTop] fun n => n * Real.log n) :
    Tendsto (fun n : ℕ => ((Nat.nth Nat.Prime n : ℝ) / Real.log (Nat.nth Nat.Prime n)) / n)
      atTop (𝓝 1) := by
  have hnlog : Tendsto (fun n : ℕ => (n : ℝ) * Real.log n) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ tendsto_log_natCast
  -- `log p_n ~ log n`
  have h1 : (fun n : ℕ => Real.log (Nat.nth Nat.Prime n)) ~[atTop]
      fun n : ℕ => Real.log ((n : ℝ) * Real.log n) := hpn.log hnlog
  have h2 : (fun n : ℕ => Real.log ((n : ℝ) * Real.log n)) ~[atTop]
      fun n : ℕ => Real.log n := by
    have ho : (fun n : ℕ => Real.log (Real.log n)) =o[atTop] fun n : ℕ => Real.log n :=
      Real.isLittleO_log_id_atTop.comp_tendsto tendsto_log_natCast
    refine IsLittleO.isEquivalent (ho.congr' ?_ EventuallyEq.rfl)
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn0 : (0 : ℝ) < n := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hℓ := one_le_log_of_three_le hn
    simp only [Pi.sub_apply]
    rw [Real.log_mul hn0.ne' (by linarith)]
    ring
  have h3 := hpn.div (h1.trans h2)
  have h4 : (fun n : ℕ => (n : ℝ) * Real.log n / Real.log n) ~[atTop] fun n : ℕ => (n : ℝ) := by
    refine IsEquivalent.congr_left (IsEquivalent.refl) ?_
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hℓ := one_le_log_of_three_le hn
    field_simp
  have h5 := h3.trans h4
  have h6 := (isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity)).1 h5
  refine h6.congr' ?_
  filter_upwards with n
  simp only [Pi.div_apply]

/-- **Theorem 1.6, as stated.** Under `θ ~ id` and `p_n ~ n log n`,
`-log(J_n - Λ) / √n → 2π/√3` with `J_n = I_{p_n}`. -/
theorem tail_asymptotic_nth
    (hpn : (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) ~[atTop] fun n => n * Real.log n) :
    Tendsto (fun n : ℕ => -Real.log (F (primesLE (Nat.nth Nat.Prime n)) - primeLambda) / √n)
      atTop (𝓝 (2 * π / √3)) := by
  have hp : Tendsto (fun n : ℕ => Nat.nth Nat.Prime n) atTop atTop :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  have h1 := (tail_asymptotic hθ).comp hp
  have h2 : Tendsto (fun n : ℕ => √(((Nat.nth Nat.Prime n : ℝ) /
      Real.log (Nat.nth Nat.Prime n)) / n)) atTop (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp (nth_prime_div_log_tendsto hpn)
    rwa [Real.sqrt_one] at this
  have h3 := h1.mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp2 : 2 ≤ Nat.nth Nat.Prime n := (Nat.prime_nth_prime n).two_le
  have hp0 : (0 : ℝ) < Nat.nth Nat.Prime n := by exact_mod_cast (by omega : 0 < Nat.nth Nat.Prime n)
  have hlp : 0 < Real.log (Nat.nth Nat.Prime n) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Nat.nth Nat.Prime n))
  simp only [Function.comp_apply]
  rw [Real.sqrt_div' _ hn0.le]
  have hr : 0 < √((Nat.nth Nat.Prime n : ℝ) / Real.log (Nat.nth Nat.Prime n)) :=
    Real.sqrt_pos.2 (div_pos hp0 hlp)
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  field_simp

end PNT

end RntPaper
