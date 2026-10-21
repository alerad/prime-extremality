import RntPaper.Tail.Defs2
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Second-order saddle analysis (paper §5.5, part D)

For an antitone nonnegative `Φ` with `Φ(t) = a(1 + κ/L)/(tL) + O(1/(tL³))`, `L = -log t`,
the infimum of `N t + Φ(t)` over `t > 0` is `λ_N [1 - log ℓ/(2ℓ) + (κ + ½ log 2a)/ℓ]`
up to a relative error `O((log ℓ/ℓ)²)`, `ℓ = log N`, and the upper bound is attained at
`τ = e^{-u₀}`, `u₀ = ½(ℓ + log ℓ - log 2a)`.

Write `t = e^{-u}`, `X = e^{u₀}` (so `X² = Nℓ/(2a)`), `A = 2aX/ℓ = N/X` (so `λ_N = 2A`),
`h(u) = 1/u + κ/u² - K'/u³`, and `v = u - u₀`. Then `N t + Φ(t) ≥ A (e^{-v} + (ℓ/2) e^v h(u))`,
and the cases are: `t` bounded below (trivial), `v ≤ 0` (`h` is decreasing),
`0 ≤ v ≤ 1` (first-order Taylor bound for `h`), both via `e^{-v} + e^v ≥ 2 + v²/2`, and
`v ≥ 1` (antitonicity of `Φ`).
-/

namespace RntPaper

open Real Filter Topology

/-! ## Elementary inequalities -/

private lemma sad2_cosh (v : ℝ) : 2 + v ^ 2 / 2 ≤ rexp (-v) + rexp v := by
  rcases le_total 0 v with hv | hv
  · have h1 := Real.quadratic_le_exp_of_nonneg hv
    have h2 := Real.add_one_le_exp (-v)
    linarith
  · have h1 := Real.quadratic_le_exp_of_nonneg (neg_nonneg.mpr hv)
    have h2 := Real.add_one_le_exp v
    have h3 : (-v) ^ 2 = v ^ 2 := by ring
    linarith

private lemma sad2_exp_sub_one {v : ℝ} (hv : v ≤ 1) : |rexp v - 1| ≤ 2 * |v| := by
  rcases le_total (-1) v with h | h
  · exact Real.abs_exp_sub_one_le (abs_le.mpr ⟨h, hv⟩)
  · have h0 : 0 < rexp v := exp_pos v
    have h1 : rexp v ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
    linarith

/-- The quadratic lower bound: `e^{-v} + (1+δ)e^v - B v⁺ ≥ 2 + δ - (2|δ| + B)²/2` for `v ≤ 1`. -/
private lemma sad2_quad {v δ B : ℝ} (hv : v ≤ 1) (hB : 0 ≤ B) :
    2 + δ - (2 * |δ| + B) ^ 2 / 2 ≤ rexp (-v) + (1 + δ) * rexp v - B * max v 0 := by
  have h1 := sad2_cosh v
  have h2 := sad2_exp_sub_one hv
  have h3 : -(|δ| * (2 * |v|)) ≤ δ * (rexp v - 1) := by
    have e1 : |δ * (rexp v - 1)| = |δ| * |rexp v - 1| := abs_mul _ _
    have e2 := neg_abs_le (δ * (rexp v - 1))
    have e3 : |δ| * |rexp v - 1| ≤ |δ| * (2 * |v|) :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    linarith
  have h4 : B * max v 0 ≤ B * |v| :=
    mul_le_mul_of_nonneg_left (max_le (le_abs_self v) (abs_nonneg v)) hB
  have h5 : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
  nlinarith [sq_nonneg (|v| - (2 * |δ| + B))]

private lemma sad2_abs_mul_le {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x * y| ≤ X * Y := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-! ## The comparison function `h` -/

/-- `h(u) = (1/u)(1 + κ/u) - K'/u³`. -/
private noncomputable def sad2_h (κ K' u : ℝ) : ℝ := 1 / u + κ / u ^ 2 - K' / u ^ 3

/-- `h` is decreasing on `[2|κ| + 3K', ∞) ∩ [1, ∞)`. -/
private lemma sad2_h_anti {κ K' u u0 : ℝ} (hK' : 0 ≤ K') (hu1 : 1 ≤ u) (huu : u ≤ u0)
    (hU : 2 * |κ| + 3 * K' ≤ u) : sad2_h κ K' u0 ≤ sad2_h κ K' u := by
  have hu0 : 0 < u := by linarith
  have hu00 : 0 < u0 := by linarith
  obtain ⟨p, hp⟩ : ∃ p, p = 1 / u := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = 1 / u0 := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hp]; positivity
  have hq0 : 0 < q := by rw [hq]; positivity
  have hqp : q ≤ p := by rw [hp, hq]; exact one_div_le_one_div_of_le hu0 huu
  have hp1 : p ≤ 1 := by rw [hp]; exact (div_le_one hu0).mpr hu1
  have hpU : (2 * |κ| + 3 * K') * p ≤ 1 := by
    rw [hp, mul_one_div, div_le_one hu0]; exact hU
  have eu : sad2_h κ K' u = p + κ * p ^ 2 - K' * p ^ 3 := by rw [sad2_h, hp]; ring
  have eu0 : sad2_h κ K' u0 = q + κ * q ^ 2 - K' * q ^ 3 := by rw [sad2_h, hq]; ring
  rw [eu, eu0]
  have hκ := abs_nonneg κ
  have e1 : -(|κ| * (p + q)) ≤ κ * (p + q) := by
    have := mul_nonneg (by linarith [neg_abs_le κ] : 0 ≤ κ + |κ|) (by linarith : 0 ≤ p + q)
    linarith
  have e2 : |κ| * (p + q) ≤ 2 * |κ| * p := by
    have := mul_le_mul_of_nonneg_left hqp hκ
    linarith
  have e3 : K' * (p ^ 2 + p * q + q ^ 2) ≤ 3 * K' * p := by
    have f1 : p ^ 2 ≤ p := by nlinarith
    have f2 : p * q ≤ p := by nlinarith
    have f3 : q ^ 2 ≤ p := by nlinarith
    have := mul_le_mul_of_nonneg_left (by linarith : p ^ 2 + p * q + q ^ 2 ≤ 3 * p) hK'
    linarith
  have hbr : 0 ≤ 1 + κ * (p + q) - K' * (p ^ 2 + p * q + q ^ 2) := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hqp) hbr]

/-- First-order lower bound for `h` to the right of `u0`. -/
private lemma sad2_h_step {κ K' u0 v : ℝ} (hK' : 0 ≤ K') (hu0 : 0 < u0) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) :
    sad2_h κ K' u0 - (v / u0 ^ 2 + 2 * |κ| / u0 ^ 3) ≤ sad2_h κ K' (u0 + v) := by
  have hu : 0 < u0 + v := by linarith
  obtain ⟨p, hp⟩ : ∃ p, p = 1 / (u0 + v) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = 1 / u0 := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hp]; positivity
  have hq0 : 0 < q := by rw [hq]; positivity
  have hd : q - p = v * p * q := by rw [hp, hq]; field_simp; ring
  have hpq : p ≤ q := by nlinarith [mul_nonneg (mul_nonneg hv0 hp0.le) hq0.le]
  have eu : sad2_h κ K' (u0 + v) = p + κ * p ^ 2 - K' * p ^ 3 := by
    rw [sad2_h, hp]; generalize u0 + v = w; ring
  have eu0 : sad2_h κ K' u0 = q + κ * q ^ 2 - K' * q ^ 3 := by rw [sad2_h, hq]; ring
  have ev : v / u0 ^ 2 + 2 * |κ| / u0 ^ 3 = v * q ^ 2 + 2 * |κ| * q ^ 3 := by rw [hq]; ring
  rw [eu, eu0, ev]
  have a1 : v * p * q ≤ v * q ^ 2 := by
    have := mul_le_mul_of_nonneg_left hpq (mul_nonneg hv0 hq0.le)
    nlinarith
  have b1 : v * p * q ≤ q ^ 2 := by
    have : v * q ^ 2 ≤ q ^ 2 := mul_le_of_le_one_left (sq_nonneg q) hv1
    linarith
  have a2 : q ^ 2 - p ^ 2 ≤ 2 * q ^ 3 := by
    have e : q ^ 2 - p ^ 2 = v * p * q * (q + p) := by rw [← hd]; ring
    rw [e]
    calc v * p * q * (q + p) ≤ q ^ 2 * (2 * q) :=
          mul_le_mul b1 (by linarith) (by positivity) (by positivity)
      _ = 2 * q ^ 3 := by ring
  have a2' : 0 ≤ q ^ 2 - p ^ 2 := by nlinarith
  have a3 : -(|κ| * (q ^ 2 - p ^ 2)) ≤ κ * (p ^ 2 - q ^ 2) := by
    have := mul_nonneg (sub_nonneg.2 (le_abs_self κ)) a2'
    linarith
  have a3' : |κ| * (q ^ 2 - p ^ 2) ≤ |κ| * (2 * q ^ 3) :=
    mul_le_mul_of_nonneg_left a2 (abs_nonneg κ)
  have a4 : K' * p ^ 3 ≤ K' * q ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0.le hpq 3) hK'
  nlinarith

/-- The expansion of `Φ` in the variable `u = -log t`. -/
private lemma sad2_phi_bounds {Φ : ℝ → ℝ} {a κ K₁ t₀ : ℝ} (ha : 0 < a) (ht₀1 : t₀ < 1)
    (hexp : ∀ t : ℝ, 0 < t → t < t₀ →
      |Φ t - a * (1 + κ / (-Real.log t)) / (t * (-Real.log t))| ≤
        K₁ / (t * (-Real.log t) ^ 3))
    {u : ℝ} (hu : rexp (-u) < t₀) :
    a * rexp u * sad2_h κ (|K₁| / a) u ≤ Φ (rexp (-u)) ∧
      Φ (rexp (-u)) ≤ a * rexp u * (1 / u + κ / u ^ 2 + |K₁| / a / u ^ 3) := by
  have hu0 : 0 < u := by
    by_contra h
    push Not at h
    have : 1 ≤ rexp (-u) := Real.one_le_exp (by linarith)
    linarith
  have h := hexp (rexp (-u)) (exp_pos _) hu
  rw [Real.log_exp, neg_neg] at h
  have hE := (exp_pos u).ne'
  have e1 : a * (1 + κ / u) / (rexp (-u) * u) = a * rexp u * (1 / u + κ / u ^ 2) := by
    rw [Real.exp_neg]; field_simp
  have e2 : K₁ / (rexp (-u) * u ^ 3) = a * rexp u * (K₁ / a / u ^ 3) := by
    rw [Real.exp_neg]; field_simp
  rw [e1, e2] at h
  have h3 : a * rexp u * (K₁ / a / u ^ 3) ≤ a * rexp u * (|K₁| / a / u ^ 3) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right (le_abs_self K₁) ha.le
  obtain ⟨hl, hr⟩ := abs_le.mp h
  constructor
  · have : a * rexp u * sad2_h κ (|K₁| / a) u =
        a * rexp u * (1 / u + κ / u ^ 2) - a * rexp u * (|K₁| / a / u ^ 3) := by
      rw [sad2_h]; ring
    linarith
  · have : a * rexp u * (1 / u + κ / u ^ 2 + |K₁| / a / u ^ 3) =
        a * rexp u * (1 / u + κ / u ^ 2) + a * rexp u * (|K₁| / a / u ^ 3) := by ring
    linarith

/-! ## The algebraic core -/

/-- The error constant. -/
private noncomputable def sad2_K (D κ K' : ℝ) : ℝ :=
  D ^ 2 + 6 * |κ| * D + 16 * K' + (4 * D + 16 * |κ| + 64 * K' + 24) ^ 2 / 4 + 96 * |κ|

private lemma sad2_K_nonneg {D κ K' : ℝ} (hD : 0 ≤ D) (hK' : 0 ≤ K') : 0 ≤ sad2_K D κ K' := by
  rw [sad2_K]; have := abs_nonneg κ; positivity

/-- With `x = (2u₀ - ℓ)/ℓ = O(r)`, `1/ℓ ≤ r` and `r` small: the second-order comparison of
`(ℓ/2) h(u₀)` with the shape `S = 1 - x/2 + κ/ℓ`. -/
private lemma sad2_alg {ℓ u0 κ K' D r : ℝ} (hℓ : 0 < ℓ) (hD : 0 ≤ D) (hK' : 0 ≤ K')
    (hzr : 1 / ℓ ≤ r) (hd : |2 * u0 - ℓ| ≤ D * r * ℓ)
    (hsmall : (D + |κ| + 2) * r ≤ 1 / 40) :
    0 < u0 ∧ 19 / 20 ≤ ℓ / (2 * (u0 + 1)) ∧
    1 - (2 * u0 - ℓ) / (2 * ℓ) + κ / ℓ ≤ 6 / 5 ∧
    2 * ((1 - (2 * u0 - ℓ) / (2 * ℓ) + κ / ℓ) - sad2_K D κ K' * r ^ 2) ≤
      2 + (ℓ / 2 * sad2_h κ K' u0 - 1)
        - (2 * |ℓ / 2 * sad2_h κ K' u0 - 1| + 3 * ℓ / (2 * u0 ^ 2)) ^ 2 / 2
        - 3 * |κ| * ℓ / u0 ^ 3 ∧
    1 + ℓ / 2 * (1 / u0 + κ / u0 ^ 2 + K' / u0 ^ 3) ≤
      2 * ((1 - (2 * u0 - ℓ) / (2 * ℓ) + κ / ℓ) + sad2_K D κ K' * r ^ 2) := by
  have hz0 : 0 < 1 / ℓ := by positivity
  have hr0 : 0 < r := lt_of_lt_of_le hz0 hzr
  have hκ0 := abs_nonneg κ
  have hκr0 := mul_nonneg hκ0 hr0.le
  have hDr0 := mul_nonneg hD hr0.le
  have hDr : D * r ≤ 1 / 40 := by linarith
  have hr1 : r ≤ 1 / 80 := by linarith
  have hκr : |κ| * r ≤ 1 / 40 := by linarith
  have hrℓ : 1 ≤ r * ℓ := by rw [div_le_iff₀ hℓ] at hzr; linarith
  have hrℓ' : r * ℓ ≤ ℓ / 80 := by
    have := mul_le_mul_of_nonneg_right hr1 hℓ.le; linarith
  have hd' := abs_le.mp hd
  have hDrℓ : D * r * ℓ ≤ ℓ / 40 := by
    have := mul_le_mul_of_nonneg_right hDr hℓ.le; linarith
  have hu0 : 0 < u0 := by linarith
  have h1920 : 19 / 20 ≤ ℓ / (2 * (u0 + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  obtain ⟨x, hx⟩ : ∃ x, x = (2 * u0 - ℓ) / ℓ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = 1 / ℓ := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = ℓ / (2 * u0) := ⟨_, rfl⟩
  have hxb : |x| ≤ D * r := by
    rw [hx, abs_div, abs_of_pos hℓ, div_le_iff₀ hℓ]; exact hd
  have hxb' := abs_le.mp hxb
  have hzpos : 0 < z := by rw [hz]; exact hz0
  have hzr' : z ≤ r := by rw [hz]; exact hzr
  have hp0 : 0 < p := by rw [hp]; positivity
  have hpx : p * (1 + x) = 1 := by rw [hp, hx]; field_simp; ring
  have hp2 : p ≤ 2 := by
    have := mul_nonneg hp0.le (by linarith : 0 ≤ x + 1 / 40)
    linarith
  have hp4 : p ^ 2 ≤ 4 := by
    have := pow_le_pow_left₀ hp0.le hp2 2; norm_num at this; linarith
  have hp8 : p ^ 3 ≤ 8 := by
    have := pow_le_pow_left₀ hp0.le hp2 3; norm_num at this; linarith
  have hpm : p - 1 = -(x * p) := by linarith
  have hS : 1 - (2 * u0 - ℓ) / (2 * ℓ) + κ / ℓ = 1 - x / 2 + κ * z := by rw [hx, hz]; ring
  have hP : ℓ / 2 * sad2_h κ K' u0 - 1 =
      (p - 1) + 2 * (κ * z) * p ^ 2 - 4 * K' * z ^ 2 * p ^ 3 := by
    rw [sad2_h, hp, hz]; field_simp; ring
  have hP' : ℓ / 2 * (1 / u0 + κ / u0 ^ 2 + K' / u0 ^ 3) =
      p + 2 * (κ * z) * p ^ 2 + 4 * K' * z ^ 2 * p ^ 3 := by
    rw [hp, hz]; field_simp; ring
  have hB : 3 * ℓ / (2 * u0 ^ 2) = 6 * z * p ^ 2 := by rw [hp, hz]; field_simp; ring
  have hC : 3 * |κ| * ℓ / u0 ^ 3 = 24 * |κ| * z ^ 2 * p ^ 3 := by
    rw [hp, hz]; field_simp; ring
  -- common bounds
  have hzb : |z| ≤ r := by rw [abs_of_pos hzpos]; exact hzr'
  have hκz : |κ * z| ≤ |κ| * r := sad2_abs_mul_le le_rfl hzb
  have hκz' := abs_le.mp hκz
  have hS65 : 1 - (2 * u0 - ℓ) / (2 * ℓ) + κ / ℓ ≤ 6 / 5 := by rw [hS]; linarith
  have hT1 : 0 ≤ p - 1 + x ∧ p - 1 + x ≤ 2 * (D * r) ^ 2 := by
    have e : p - 1 + x = x ^ 2 * p := by linear_combination (-x) * hpx + hpm
    have hx2 : x ^ 2 ≤ (D * r) ^ 2 := sq_le_sq' hxb'.1 hxb'.2
    rw [e]
    constructor
    · positivity
    · have := mul_le_mul hx2 hp2 hp0.le (sq_nonneg _)
      linarith
  have hT2 : |κ * z * (p ^ 2 - 1)| ≤ |κ| * r * (D * r * 6) := by
    have e : κ * z * (p ^ 2 - 1) = (κ * z) * (x * (p * (p + 1))) * (-1) := by
      linear_combination (κ * z * (p + 1)) * hpm
    rw [e, abs_mul, abs_neg, abs_one, mul_one]
    apply sad2_abs_mul_le hκz (sad2_abs_mul_le hxb _)
    rw [abs_of_pos (by positivity)]
    have := mul_le_mul hp2 (by linarith : p + 1 ≤ 3) (by positivity) (by norm_num)
    linarith
  have hT2' := abs_le.mp hT2
  have hT3 : 0 ≤ K' * z ^ 2 * p ^ 3 ∧ K' * z ^ 2 * p ^ 3 ≤ K' * r ^ 2 * 8 := by
    constructor
    · positivity
    · have f1 : z ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hzpos.le hzr' 2
      have f3 : z ^ 2 * p ^ 3 ≤ r ^ 2 * 8 :=
        mul_le_mul f1 hp8 (by positivity) (by positivity)
      have := mul_le_mul_of_nonneg_left f3 hK'
      linarith
  -- `|δ| ≤ (2D + 8|κ| + 32K') r`
  have hp1b : |p - 1| ≤ D * r * 2 := by
    rw [hpm, abs_neg]
    exact sad2_abs_mul_le hxb (by rw [abs_of_pos hp0]; exact hp2)
  have hp1b' := abs_le.mp hp1b
  have hκzp : |κ * z * p ^ 2| ≤ |κ| * r * 4 :=
    sad2_abs_mul_le hκz (by rw [abs_of_nonneg (by positivity)]; exact hp4)
  have hκzp' := abs_le.mp hκzp
  have hr2 : r ^ 2 ≤ r := by
    rw [sq]; exact mul_le_of_le_one_right hr0.le (by linarith)
  have hKr : K' * r ^ 2 ≤ K' * r := mul_le_mul_of_nonneg_left hr2 hK'
  have hδ : |(p - 1) + 2 * (κ * z) * p ^ 2 - 4 * K' * z ^ 2 * p ^ 3| ≤
      (2 * D + 8 * |κ| + 32 * K') * r := by
    rw [abs_le]; constructor <;> linarith
  have hBb : 0 ≤ 6 * z * p ^ 2 ∧ 6 * z * p ^ 2 ≤ 24 * r := by
    constructor
    · positivity
    · have : z * p ^ 2 ≤ r * 4 := mul_le_mul hzr' hp4 (by positivity) hr0.le
      linarith
  have hCb : 24 * |κ| * z ^ 2 * p ^ 3 ≤ 192 * |κ| * r ^ 2 := by
    have f1 : z ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hzpos.le hzr' 2
    have f3 : z ^ 2 * p ^ 3 ≤ r ^ 2 * 8 := mul_le_mul f1 hp8 (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left f3 hκ0
    linarith
  have hsq : (2 * |(p - 1) + 2 * (κ * z) * p ^ 2 - 4 * K' * z ^ 2 * p ^ 3| + 6 * z * p ^ 2) ^ 2
      ≤ ((4 * D + 16 * |κ| + 64 * K' + 24) * r) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hlow : 2 * ((1 - (2 * u0 - ℓ) / (2 * ℓ) + κ / ℓ) - sad2_K D κ K' * r ^ 2) ≤
      2 + (ℓ / 2 * sad2_h κ K' u0 - 1)
        - (2 * |ℓ / 2 * sad2_h κ K' u0 - 1| + 3 * ℓ / (2 * u0 ^ 2)) ^ 2 / 2
        - 3 * |κ| * ℓ / u0 ^ 3 := by
    rw [hS, hP, hB, hC, sad2_K]
    have := sq_nonneg (D * r)
    linarith
  have hup : 1 + ℓ / 2 * (1 / u0 + κ / u0 ^ 2 + K' / u0 ^ 3) ≤
      2 * ((1 - (2 * u0 - ℓ) / (2 * ℓ) + κ / ℓ) + sad2_K D κ K' * r ^ 2) := by
    rw [hS, hP', sad2_K]
    have := sq_nonneg ((4 * D + 16 * |κ| + 64 * K' + 24) * r)
    have := mul_nonneg hκ0 (sq_nonneg r)
    have := mul_nonneg hK' (sq_nonneg r)
    have := mul_nonneg (mul_nonneg hκ0 hD) (sq_nonneg r)
    linarith
  exact ⟨hu0, h1920, hS65, hlow, hup⟩

/-! ## Large-`N` facts -/

private lemma sad2_log_div_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ℓ : ℝ in atTop, Real.log ℓ / ℓ ≤ ε := by
  filter_upwards [Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.eventually
    (Iic_mem_nhds hε)] with ℓ hℓ
  exact hℓ

private lemma sad2_log_le_eventually {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℝ in atTop, Real.log N ≤ c * N := by
  filter_upwards [Real.isLittleO_log_id_atTop.def hc, eventually_gt_atTop 0] with N hN hN0
  simp only [Real.norm_eq_abs, id] at hN
  rw [abs_of_pos hN0] at hN
  exact (le_abs_self _).trans hN

/-! ## The saddle estimate -/

set_option maxHeartbeats 1000000 in
theorem saddle_second_order {Φ : ℝ → ℝ} {a κ : ℝ} (ha : 0 < a)
    (hanti : ∀ s t, 0 < s → s ≤ t → Φ t ≤ Φ s) (hnonneg : ∀ t, 0 < t → 0 ≤ Φ t)
    (hΦ : PhiExpansion Φ a κ) :
    ∃ K : ℝ, ∀ᶠ N : ℝ in Filter.atTop,
      (∀ t : ℝ, 0 < t → tailLam a N * (tailShape a κ N - K * tailErr N) ≤ N * t + Φ t) ∧
      ∃ τ : ℝ, 1 / N ≤ τ ∧ τ ≤ 1 ∧ N * τ ≤ tailLam a N ∧
        N * τ + Φ τ ≤ tailLam a N * (tailShape a κ N + K * tailErr N) := by
  obtain ⟨K₁, t₀, ht₀, ht₀1, hexp⟩ := hΦ
  obtain ⟨K', hK'def⟩ : ∃ K', K' = |K₁| / a := ⟨_, rfl⟩
  have hK' : 0 ≤ K' := by rw [hK'def]; positivity
  obtain ⟨D, hDdef⟩ : ∃ D, D = 1 + |Real.log (2 * a)| := ⟨_, rfl⟩
  have hD : 0 ≤ D := by rw [hDdef]; positivity
  obtain ⟨U₁, hU₁⟩ : ∃ U, U = 20 * (|κ| + K') + 1 := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = min t₀ (rexp (-U₁)) := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hTdef]; exact lt_min ht₀ (exp_pos _)
  have hTt₀ : T ≤ t₀ := by rw [hTdef]; exact min_le_left _ _
  have hTU : T ≤ rexp (-U₁) := by rw [hTdef]; exact min_le_right _ _
  have hκ0 := abs_nonneg κ
  have hlog2a := abs_nonneg (Real.log (2 * a))
  have hKK := sad2_K_nonneg (κ := κ) hD hK'
  refine ⟨sad2_K D κ K', ?_⟩
  filter_upwards [eventually_gt_atTop 1, sad2_log_le_eventually (by positivity : 0 < 2 * a),
    tendsto_log_atTop.eventually (sad2_log_div_eventually
      (by positivity : (0 : ℝ) < 1 / (40 * (D + |κ| + 2)))),
    tendsto_log_atTop.eventually (eventually_ge_atTop (rexp 1)),
    tendsto_log_atTop.eventually (eventually_ge_atTop (2 * U₁ + |Real.log (2 * a)|)),
    tendsto_log_atTop.eventually
      (eventually_ge_atTop (2 * Real.log (4 / T) + |Real.log (2 * a)|))]
    with N hN1 hNlog hrN hℓe hℓU hℓT
  have hN0 : 0 < N := by linarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = Real.log N := ⟨_, rfl⟩
  rw [← hℓdef] at hNlog hrN hℓe hℓU hℓT
  have hexpℓ : rexp ℓ = N := by rw [hℓdef, exp_log hN0]
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (exp_pos 1) hℓe
  have he1 : (1 : ℝ) ≤ Real.log ℓ := by
    have := Real.log_le_log (exp_pos 1) hℓe; rwa [Real.log_exp] at this
  obtain ⟨r, hrdef⟩ : ∃ r, r = Real.log ℓ / ℓ := ⟨_, rfl⟩
  have hErr : tailErr N = r ^ 2 := by rw [tailErr, hrdef, hℓdef]
  obtain ⟨u0, hu0def⟩ : ∃ u, u = (ℓ + Real.log ℓ - Real.log (2 * a)) / 2 := ⟨_, rfl⟩
  have hS : tailShape a κ N = 1 - (2 * u0 - ℓ) / (2 * ℓ) + κ / ℓ := by
    rw [tailShape, hu0def, ← hℓdef]; ring
  have hzr : 1 / ℓ ≤ r := by rw [hrdef]; exact div_le_div_of_nonneg_right he1 hℓ0.le
  have hd : |2 * u0 - ℓ| ≤ D * r * ℓ := by
    have e : 2 * u0 - ℓ = Real.log ℓ - Real.log (2 * a) := by rw [hu0def]; ring
    have e2 : D * r * ℓ = D * Real.log ℓ := by rw [hrdef]; field_simp
    rw [e, e2, hDdef, abs_le]
    have f1 := neg_abs_le (Real.log (2 * a))
    have f2 := le_abs_self (Real.log (2 * a))
    have f3 : |Real.log (2 * a)| ≤ |Real.log (2 * a)| * Real.log ℓ :=
      le_mul_of_one_le_right hlog2a he1
    constructor <;> nlinarith
  have hsmall : (D + |κ| + 2) * r ≤ 1 / 40 := by
    have h1 := mul_le_mul_of_nonneg_left hrN (by positivity : (0 : ℝ) ≤ D + |κ| + 2)
    have h2 : (D + |κ| + 2) * (1 / (40 * (D + |κ| + 2))) = 1 / 40 := by
      field_simp
    rw [hrdef]; linarith
  obtain ⟨hu0, h1920, hS65, hlow, hup⟩ := sad2_alg hℓ0 hD hK' hzr hd hsmall
  rw [← hS] at hS65 hlow hup
  -- `u0` is large
  have hl2a := le_abs_self (Real.log (2 * a))
  have hu0U : U₁ ≤ u0 := by rw [hu0def]; linarith
  have hu0T : Real.log (4 / T) ≤ u0 := by rw [hu0def]; linarith
  -- `X = e^{u0}`, `A = 2aX/ℓ`
  obtain ⟨X, hXdef⟩ : ∃ X, X = rexp u0 := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hXdef]; exact exp_pos _
  have hX2 : X ^ 2 * (2 * a) = N * ℓ := by
    have e : u0 + u0 = ℓ + Real.log ℓ - Real.log (2 * a) := by rw [hu0def]; ring
    rw [hXdef, sq, ← exp_add, e, exp_sub, exp_add, exp_log hℓ0, exp_log (by positivity),
      hexpℓ]
    field_simp
  have hX2' : X ^ 2 = N * ℓ / (2 * a) := by rw [← hX2]; field_simp
  have hXT : 4 ≤ X * T := by
    have := Real.exp_le_exp.mpr hu0T
    rw [exp_log (by positivity), ← hXdef, div_le_iff₀ hT0] at this
    exact this
  have hX1 : 1 ≤ X := by rw [hXdef]; exact Real.one_le_exp (by linarith)
  obtain ⟨A, hAdef⟩ : ∃ A, A = 2 * a * X / ℓ := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hAdef]; positivity
  have hlam : tailLam a N = 2 * A := by
    rw [tailLam, ← hℓdef]
    have : 2 * a * N / ℓ = A ^ 2 := by
      rw [hAdef, div_pow, mul_pow, mul_pow, hX2']
      field_simp
    rw [this, Real.sqrt_sq hA0.le]
  have hNAX : N = A * X := by
    rw [hAdef]; field_simp; linear_combination -hX2
  have haX : ∀ y : ℝ, a * X * y = A * (ℓ / 2 * y) := by
    intro y; rw [hAdef]; field_simp
  rw [hlam, hErr]
  -- `τ = e^{-u0} = 1/X`
  have hτ : rexp (-u0) = 1 / X := by rw [hXdef, exp_neg, one_div]
  have hτt₀ : rexp (-u0) < t₀ := by
    rw [hτ, div_lt_iff₀ hX0]
    have := mul_le_mul_of_nonneg_left hTt₀ hX0.le
    linarith
  constructor
  · -- lower bound
    intro t ht
    have hΦt := hnonneg t ht
    rcases le_or_gt T t with hTt | hTt
    · have h1 : N * T ≤ N * t := mul_le_mul_of_nonneg_left hTt hN0.le
      have h2 : 4 * A ≤ N * T := by
        rw [hNAX]; have := mul_le_mul_of_nonneg_left hXT hA0.le; linarith
      have h3 : 2 * A * (tailShape a κ N - sad2_K D κ K' * r ^ 2) ≤ 2 * A * (6 / 5) :=
        mul_le_mul_of_nonneg_left
          (by have := mul_nonneg hKK (sq_nonneg r); linarith) (by positivity)
      linarith
    obtain ⟨u, hudef⟩ : ∃ u, u = -Real.log t := ⟨_, rfl⟩
    have htu : t = rexp (-u) := by rw [hudef, neg_neg, exp_log ht]
    have huU : U₁ < u := by
      have h := Real.log_lt_log ht (hTt.trans_le hTU)
      rw [Real.log_exp] at h
      rw [hudef]; linarith
    have htt₀ : rexp (-u) < t₀ := by rw [← htu]; linarith
    obtain ⟨v, hvdef⟩ : ∃ v, v = u - u0 := ⟨_, rfl⟩
    have heu : rexp u = X * rexp v := by
      rw [hXdef, ← exp_add, hvdef]; ring_nf
    have hNt : N * t = A * rexp (-v) := by
      rw [htu, hNAX, hvdef, show -(u - u0) = -u + u0 by ring, exp_add, ← hXdef]
      field_simp
    rcases le_or_gt v 1 with hv1 | hv1
    · -- `v ≤ 1`
      obtain ⟨hΦu, -⟩ := sad2_phi_bounds (κ := κ) ha ht₀1 hexp htt₀
      have eΦ : a * rexp u * sad2_h κ K' u = A * (ℓ / 2 * (rexp v * sad2_h κ K' u)) := by
        rw [heu, ← haX]; ring
      rw [← hK'def, ← htu, eΦ] at hΦu
      set P := ℓ / 2 * sad2_h κ K' u0 with hPdef
      set B := 3 * ℓ / (2 * u0 ^ 2) with hBdef
      set C := 3 * |κ| * ℓ / u0 ^ 3 with hCdef
      have hB0 : 0 ≤ B := by rw [hBdef]; positivity
      have hC0 : 0 ≤ C := by rw [hCdef]; positivity
      have hev : 0 < rexp v := exp_pos v
      have key : rexp (-v) + P * rexp v - B * max v 0 - C ≤
          rexp (-v) + ℓ / 2 * (rexp v * sad2_h κ K' u) := by
        rcases le_or_gt v 0 with hv0 | hv0
        · have hh := sad2_h_anti hK' (by linarith) (by rw [hvdef] at hv0; linarith)
            (by rw [hU₁] at huU; linarith) (u := u) (u0 := u0) (κ := κ)
          have : P * rexp v ≤ ℓ / 2 * (rexp v * sad2_h κ K' u) := by
            rw [hPdef]
            have := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ ℓ / 2 * rexp v)
            linarith
          rw [max_eq_right hv0]
          linarith
        · have hh := sad2_h_step (κ := κ) hK' hu0 hv0.le hv1
          rw [show u0 + v = u by rw [hvdef]; ring] at hh
          have hE0 : 0 ≤ v / u0 ^ 2 + 2 * |κ| / u0 ^ 3 := by positivity
          have he3 : rexp v ≤ 3 := by
            have := Real.exp_le_exp.mpr hv1
            have := Real.exp_one_lt_d9
            linarith
          have f1 := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ ℓ / 2 * rexp v)
          have f2 : ℓ / 2 * rexp v * (v / u0 ^ 2 + 2 * |κ| / u0 ^ 3) ≤
              ℓ / 2 * 3 * (v / u0 ^ 2 + 2 * |κ| / u0 ^ 3) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left he3 (by positivity)) hE0
          have f3 : ℓ / 2 * 3 * (v / u0 ^ 2 + 2 * |κ| / u0 ^ 3) = B * v + C := by
            rw [hBdef, hCdef]; ring
          rw [max_eq_left hv0.le, hPdef]
          linarith
      have hq := sad2_quad (δ := P - 1) hv1 hB0
      rw [show 1 + (P - 1) = P by ring] at hq
      have hfin : 2 * (tailShape a κ N - sad2_K D κ K' * r ^ 2) ≤
          rexp (-v) + ℓ / 2 * (rexp v * sad2_h κ K' u) := by linarith
      have := mul_le_mul_of_nonneg_left hfin hA0.le
      rw [hNt]
      linarith
    · -- `v > 1`: antitonicity
      have hw : U₁ ≤ u0 + 1 := by linarith
      have ht₂ : t ≤ rexp (-(u0 + 1)) := by
        rw [htu]; exact Real.exp_le_exp.mpr (by rw [hvdef] at hv1; linarith)
      have hΦ12 := hanti t _ ht ht₂
      have ht₂t₀ : rexp (-(u0 + 1)) < t₀ :=
        lt_of_lt_of_le (Real.exp_lt_exp.mpr (by linarith)) hτt₀.le
      obtain ⟨hΦw, -⟩ := sad2_phi_bounds (κ := κ) ha ht₀1 hexp ht₂t₀
      have eΦ : a * rexp (u0 + 1) * sad2_h κ K' (u0 + 1) =
          A * (ℓ / 2 * (rexp 1 * sad2_h κ K' (u0 + 1))) := by
        rw [exp_add, ← hXdef, ← haX]; ring
      rw [← hK'def, eΦ] at hΦw
      -- `(ℓ/2) h(u0+1) ≥ (19/20)²`
      have hw0 : 0 < u0 + 1 := by linarith
      have hhw : 361 / 400 ≤ ℓ / 2 * sad2_h κ K' (u0 + 1) := by
        obtain ⟨q, hq⟩ : ∃ q, q = 1 / (u0 + 1) := ⟨_, rfl⟩
        have hq0 : 0 < q := by rw [hq]; positivity
        have hq1 : q ≤ 1 := by rw [hq, div_le_one hw0]; linarith
        have hqU : (|κ| + K') * q ≤ 1 / 20 := by
          rw [hq, mul_one_div, div_le_iff₀ hw0]; rw [hU₁] at hw; linarith
        have e : ℓ / 2 * sad2_h κ K' (u0 + 1) =
            ℓ / (2 * (u0 + 1)) * (1 + κ * q - K' * q ^ 2) := by
          rw [sad2_h, hq]; field_simp
        rw [e]
        have g1 : -(|κ| * q) ≤ κ * q := by
          have := mul_le_mul_of_nonneg_right (neg_abs_le κ) hq0.le; linarith
        have g2 : K' * q ^ 2 ≤ K' * q := by
          apply mul_le_mul_of_nonneg_left _ hK'
          rw [sq]; exact mul_le_of_le_one_right hq0.le hq1
        have g3 : 19 / 20 ≤ 1 + κ * q - K' * q ^ 2 := by linarith
        calc (361 / 400 : ℝ) = 19 / 20 * (19 / 20) := by norm_num
          _ ≤ ℓ / (2 * (u0 + 1)) * (1 + κ * q - K' * q ^ 2) :=
            mul_le_mul h1920 g3 (by norm_num) (by positivity)
      have he := Real.exp_one_gt_d9
      have hNt0 : 0 ≤ N * t := by positivity
      have g4 : A * (361 / 400) * 2.7 ≤ A * (ℓ / 2 * (rexp 1 * sad2_h κ K' (u0 + 1))) := by
        have := mul_le_mul hhw (by linarith : (2.7 : ℝ) ≤ rexp 1) (by norm_num)
          (by linarith)
        have := mul_le_mul_of_nonneg_left this hA0.le
        linarith
      have h3 : 2 * A * (tailShape a κ N - sad2_K D κ K' * r ^ 2) ≤ 2 * A * (6 / 5) :=
        mul_le_mul_of_nonneg_left
          (by have := mul_nonneg hKK (sq_nonneg r); linarith) (by positivity)
      linarith
  · -- upper bound at `τ = e^{-u0}`
    refine ⟨rexp (-u0), ?_, ?_, ?_, ?_⟩
    · rw [hτ]
      apply one_div_le_one_div_of_le hX0
      have h1 : X ^ 2 ≤ N ^ 2 := by
        have := mul_le_mul_of_nonneg_left hNlog hN0.le
        have h2 : X ^ 2 * (2 * a) ≤ N ^ 2 * (2 * a) := by linarith
        exact le_of_mul_le_mul_right h2 (by positivity)
      exact (pow_le_pow_iff_left₀ hX0.le hN0.le two_ne_zero).mp h1
    · rw [hτ, div_le_one hX0]; exact hX1
    · rw [hτ, hNAX, mul_one_div, mul_div_assoc, div_self hX0.ne', mul_one]; linarith
    · obtain ⟨-, hΦu⟩ := sad2_phi_bounds (κ := κ) ha ht₀1 hexp hτt₀
      rw [← hK'def, ← hXdef, haX] at hΦu
      have hNτ : N * rexp (-u0) = A := by
        rw [hτ, hNAX, mul_one_div, mul_div_assoc, div_self hX0.ne', mul_one]
      rw [hNτ]
      have := mul_le_mul_of_nonneg_left hup hA0.le
      linarith
