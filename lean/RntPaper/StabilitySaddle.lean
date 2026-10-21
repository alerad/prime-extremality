import RntPaper.Stability
import RntPaper.TailAsymptotic

/-!
# Saddle-point bounds for the omission cost `Δ_1(p)`

With `x = e^{-t}` and `Φ(t) = ∑_p -log(1 - e^{-pt})` one has `xᵖ Q(x) = e^{-(pt + Φ(t))}`
(`pow_mul_Qfun_eq`), so `Δ_1(p) = ∫₀¹ xᵖ Q(x) dx` is governed by
`M_p = inf_{t>0} (p t + Φ(t))` (`saddleMin`):

* (a) `omitMoment_le_of_saddle`: `B ≤ p t + Φ(t)` for all `t > 0` gives `Δ_1(p) ≤ e^{-B}`;
* (b) `neg_log_omitMoment_le`: for every `τ > 0`,
  `-log Δ_1(p) ≤ pτ + Φ(τ) + τ + 1/p + 1 + log p` (window `τ ≤ t ≤ τ + 1/p`);
* (c) `primePhi_one_lt`: `Φ(1) < 1`, and `saddleMin_le_neg_log_omitMoment`,
  `neg_log_omitMoment_le_saddleMin`: `M_p ≤ -log Δ_1(p) ≤ M_p + log p + 3` for `p ≥ 2`;
* (d) `omitMoment_asymptotic`: under `θ ~ id`,
  `-log Δ_1(p) / √(p / log p) → 2π/√3`, i.e. `-log Δ_1(p) ~ 2π √(p / (3 log p))`.
-/

namespace RntPaper

open QProduct Real Filter Topology Asymptotics MeasureTheory Set

/-! ## `Q(e^{-t}) = e^{-Φ(t)}` -/

/-- `Q(e^{-t}) = exp(-Φ(t))` for `t > 0`. -/
theorem Qfun_exp_neg {t : ℝ} (ht : 0 < t) : Qfun (rexp (-t)) = rexp (-primePhi t) := by
  set x := rexp (-t) with hx
  have h0 : 0 ≤ x := (exp_pos _).le
  have h1 : x < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hP0 : 0 ∉ Primes := fun h => Nat.not_prime_zero h
  have hlog : Summable fun n : ℕ =>
      Real.log (Set.mulIndicator Primes (fun n : ℕ => 1 - x ^ n) n) := by
    rw [mulIndicator_eq_one_add_indicator]
    exact Real.summable_log_one_add_of_summable (summable_indicator_pow_set Primes h0 h1)
  unfold Qfun
  rw [qProdSet_eq_tprod_mulIndicator, ← Real.rexp_tsum_eq_tprod (mulIndicator_pos _ hP0 h0 h1) hlog,
    primePhi_eq_tsum_phiInd, ← tsum_neg]
  congr 1
  refine tsum_congr fun n => ?_
  unfold phiInd
  by_cases hn : n.Prime
  · have hmem : n ∈ {p : ℕ | p.Prime} := hn
    rw [Set.mulIndicator_of_mem (show n ∈ Primes from hn), Set.indicator_of_mem hmem, neg_neg]
  · have hmem : n ∉ {p : ℕ | p.Prime} := hn
    rw [Set.mulIndicator_of_notMem (show n ∉ Primes from hn), Set.indicator_of_notMem hmem,
      Real.log_one, neg_zero]

/-- `xᵖ Q(x) = exp(-(p t + Φ(t)))` with `t = -log x`, for `x ∈ (0,1)`. -/
theorem pow_mul_Qfun_eq (p : ℕ) {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    u ^ p * Qfun u = rexp (-(p * (-Real.log u) + primePhi (-Real.log u))) := by
  have ht : 0 < -Real.log u := by have := Real.log_neg h0 h1; linarith
  have hu : u = rexp (-(-Real.log u)) := by rw [neg_neg, exp_log h0]
  conv_lhs => rw [hu]
  rw [Qfun_exp_neg ht, ← Real.exp_nat_mul, ← exp_add]
  ring_nf

theorem ae_restrict_mem_Ioo01 :
    ∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) 1)), u ∈ Ioo (0 : ℝ) 1 := by
  have hz : volume ({(0 : ℝ), 1} : Set ℝ) = 0 :=
    (Set.toFinite _).measure_zero _
  have hne : ∀ᵐ u : ℝ ∂volume, u ∉ ({(0 : ℝ), 1} : Set ℝ) :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with u hu hu'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu'
  exact ⟨lt_of_le_of_ne hu.1 (Ne.symm hu'.1), lt_of_le_of_ne hu.2 hu'.2⟩

/-! ## (a) Upper bound -/

/-- **(a)** If `B ≤ p t + Φ(t)` for all `t > 0` then `Δ_1(p) ≤ e^{-B}`. -/
theorem omitMoment_le_of_saddle {p : ℕ} {B : ℝ}
    (hB : ∀ t : ℝ, 0 < t → B ≤ p * t + primePhi t) : omitMoment p 1 ≤ rexp (-B) := by
  have h := intervalIntegral.integral_mono_ae_restrict (zero_le_one' ℝ)
    (intervalIntegrable_pow_mul_Qfun p ⟨zero_le_one, le_rfl⟩)
    (intervalIntegrable_const (c := rexp (-B))) (f := fun u => u ^ p * Qfun u) (by
      filter_upwards [ae_restrict_mem_Ioo01] with u hu
      rw [pow_mul_Qfun_eq p hu.1 hu.2]
      have ht : 0 < -Real.log u := by have := Real.log_neg hu.1 hu.2; linarith
      exact Real.exp_le_exp.mpr (neg_le_neg (hB _ ht)))
  simpa [omitMoment] using h

/-! ## (b) Window lower bound -/

/-- **(b)** For `p ≥ 1` and every `τ > 0`:
`-log Δ_1(p) ≤ pτ + Φ(τ) + τ + 1/p + 1 + log p`. -/
theorem neg_log_omitMoment_le {p : ℕ} (hp : 1 ≤ p) {τ : ℝ} (hτ : 0 < τ) :
    -Real.log (omitMoment p 1) ≤ p * τ + primePhi τ + τ + 1 / p + 1 + Real.log p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set a := rexp (-(τ + 1 / p)) with ha
  set b := rexp (-τ) with hb
  set K := rexp (-(p * τ + primePhi τ + 1)) with hK
  have ha0 : 0 < a := exp_pos _
  have hab : a ≤ b := Real.exp_le_exp.mpr (by have : 0 < 1 / (p : ℝ) := (by positivity); linarith)
  have hb1 : b < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hI := intervalIntegrable_pow_mul_Qfun p ⟨zero_le_one, le_rfl⟩
  -- the window integral
  have hwin : (b - a) * K ≤ ∫ u in a..b, u ^ p * Qfun u := by
    have := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := K))
      (hI.mono_set (by
        rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]
        exact Set.Icc_subset_Icc ha0.le hb1.le))
      (fun u hu => by
        have hu0 : 0 < u := ha0.trans_le hu.1
        rw [pow_mul_Qfun_eq p hu0 (hu.2.trans_lt hb1)]
        set t := -Real.log u with htdef
        have ht1 : τ ≤ t := by
          have := Real.log_le_log hu0 hu.2
          rw [hb, Real.log_exp] at this; linarith
        have ht2 : t ≤ τ + 1 / p := by
          have := Real.log_le_log ha0 hu.1
          rw [ha, Real.log_exp] at this; linarith
        have hΦ := primePhi_anti hτ ht1
        have hpt : (p : ℝ) * t ≤ p * τ + 1 := by
          have := mul_le_mul_of_nonneg_left ht2 hp0.le
          rw [mul_add, mul_one_div_cancel hp0.ne'] at this
          exact this
        exact Real.exp_le_exp.mpr (by linarith))
    simpa using this
  have hmono : (∫ u in a..b, u ^ p * Qfun u) ≤ omitMoment p 1 :=
    intervalIntegral.integral_mono_interval ha0.le hab hb1.le
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        exact mul_nonneg (pow_nonneg hu.1.le p) (Qfun_nonneg ⟨hu.1.le, hu.2⟩))
      hI
  -- `b - a ≥ e^{-τ}/(p+1)`
  have hlen : rexp (-τ) / (p + 1) ≤ b - a := by
    have h1 := div_one_add_le_one_sub_exp (by positivity : (0 : ℝ) ≤ 1 / p)
    have hba : b - a = rexp (-τ) * (1 - rexp (-(1 / p))) := by
      rw [ha, hb, mul_sub, mul_one, ← exp_add]; ring_nf
    have he : (1 / (p : ℝ)) / (1 + 1 / p) = 1 / (p + 1) := by field_simp
    rw [he] at h1
    rw [hba, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h1 (exp_pos _).le
  set L := rexp (-τ) / (p + 1) * K with hL
  have hL0 : 0 < L := by positivity
  have hLle : L ≤ omitMoment p 1 :=
    (mul_le_mul_of_nonneg_right hlen (exp_pos _).le).trans (hwin.trans hmono)
  have hlogL : Real.log L = -τ - Real.log (p + 1) - (p * τ + primePhi τ + 1) := by
    rw [hL, hK, Real.log_mul (by positivity) (exp_pos _).ne', Real.log_div (exp_pos _).ne'
      (by positivity), Real.log_exp, Real.log_exp]
    ring
  have hlog := Real.log_le_log hL0 hLle
  have hlp : Real.log (p + 1) ≤ Real.log p + 1 / p := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ((p : ℝ) + 1) / p by positivity)
    rw [Real.log_div (by positivity) hp0.ne'] at h
    have : ((p : ℝ) + 1) / p - 1 = 1 / p := by field_simp; ring
    linarith
  linarith

/-! ## (c) Comparison with the saddle value `M_p` -/

/-- **(c)** `Φ(1) < 1`: `Φ(1) ≤ ∑_{n≥2} e^{-n}/(1-e^{-1}) = e^{-2}/(1-e^{-1})² < 1`. -/
theorem primePhi_one_lt : primePhi 1 < 1 := by
  set x := rexp (-1) with hx
  have h0 : 0 ≤ x := (exp_pos _).le
  have hxh : x < 1 / 2 := by
    rw [hx, Real.exp_neg, inv_lt_comm₀ (exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9
    norm_num
    linarith
  have h1 : x < 1 := by linarith
  have hx1 : 0 < 1 - x := by linarith
  rw [primePhi_eq_tsum_phiInd, ← hx, ← (summable_phiInd h0 h1).sum_add_tsum_nat_add 2]
  have hz0 : phiInd x 0 = 0 := Set.indicator_of_notMem Nat.not_prime_zero _
  have hz1 : phiInd x 1 = 0 := Set.indicator_of_notMem Nat.not_prime_one _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hz0, hz1, zero_add]
  have hgs : Summable fun i : ℕ => x ^ (i + 2) / (1 - x) := by
    have := ((summable_geometric_of_lt_one h0 h1).mul_left (x ^ 2)).div_const (1 - x)
    refine this.congr fun i => ?_
    rw [pow_add]; ring
  have htail : ∑' i : ℕ, phiInd x (i + 2) ≤ x ^ 2 / (1 - x) ^ 2 := by
    calc ∑' i : ℕ, phiInd x (i + 2)
        ≤ ∑' i : ℕ, x ^ (i + 2) / (1 - x) :=
          ((summable_nat_add_iff 2).mpr (summable_phiInd h0 h1)).tsum_le_tsum
            (fun i => phiInd_le h0 h1 _) hgs
      _ = x ^ 2 / (1 - x) * ∑' i : ℕ, x ^ i := by
          rw [← tsum_mul_left]
          congr 1; funext i; rw [pow_add]; ring
      _ = x ^ 2 / (1 - x) ^ 2 := by
          rw [tsum_geometric_of_lt_one h0 h1]; field_simp
  have hlt : x ^ 2 / (1 - x) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  linarith

/-- The saddle value `M_p = inf_{t>0} (p t + Φ(t))`. -/
noncomputable def saddleMin (p : ℕ) : ℝ := ⨅ t : Ioi (0 : ℝ), ((p : ℝ) * t + primePhi t)

theorem saddleMin_bddBelow (p : ℕ) :
    BddBelow (Set.range fun t : Ioi (0 : ℝ) => (p : ℝ) * t + primePhi t) :=
  ⟨0, by
    rintro _ ⟨t, rfl⟩
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg p) (le_of_lt t.2)) (primePhi_nonneg t.2)⟩

theorem saddleMin_le (p : ℕ) {t : ℝ} (ht : 0 < t) : saddleMin p ≤ p * t + primePhi t :=
  ciInf_le (saddleMin_bddBelow p) (⟨t, ht⟩ : Ioi (0 : ℝ))

theorem le_saddleMin {p : ℕ} {B : ℝ} (h : ∀ t : ℝ, 0 < t → B ≤ p * t + primePhi t) :
    B ≤ saddleMin p := by
  have : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, Set.mem_Ioi.mpr one_pos⟩⟩
  exact le_ciInf fun t => h t t.2

theorem exists_lt_saddleMin_add (p : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ p * t + primePhi t < saddleMin p + δ := by
  have : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, Set.mem_Ioi.mpr one_pos⟩⟩
  obtain ⟨t, ht⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right (saddleMin p) hδ)
  exact ⟨t, t.2, ht⟩

/-- **(c), lower bound.** `M_p ≤ -log Δ_1(p)`. -/
theorem saddleMin_le_neg_log_omitMoment (p : ℕ) : saddleMin p ≤ -Real.log (omitMoment p 1) := by
  have h := omitMoment_le_of_saddle (p := p) (fun t ht => saddleMin_le p ht)
  have hpos := omitMoment_pos (p := p) (c := 1) ⟨one_pos, le_rfl⟩
  have := Real.log_le_log hpos h
  rw [Real.log_exp] at this
  linarith

/-- **(c), upper bound.** `-log Δ_1(p) ≤ M_p + log p + 3` for `p ≥ 2`. -/
theorem neg_log_omitMoment_le_saddleMin {p : ℕ} (hp : 2 ≤ p) :
    -Real.log (omitMoment p 1) ≤ saddleMin p + Real.log p + 3 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hΦ1 := primePhi_one_lt
  have hΦ0 := primePhi_nonneg one_pos
  set δ := (1 - primePhi 1) / 3 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨τ, hτ, hτlt⟩ := exists_lt_saddleMin_add p hδ0
  have hM1 := saddleMin_le p one_pos
  have hΦτ := primePhi_nonneg hτ
  have hb := neg_log_omitMoment_le (by omega : 1 ≤ p) hτ
  set q := 1 / (p : ℝ) with hq
  have hpq : (p : ℝ) * q = 1 := by rw [hq]; field_simp
  have hq0 : 0 < q := by positivity
  have hq2 : q ≤ 1 / 2 := by rw [hq]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have hτp : (p : ℝ) * τ ≤ p * 1 + primePhi 1 + δ := by linarith
  have hτ' : τ ≤ 1 + (primePhi 1 + δ) * q := by
    have := mul_le_mul_of_nonneg_right hτp hq0.le
    have e1 : (p : ℝ) * τ * q = τ := by rw [mul_comm (p : ℝ) τ, mul_assoc, hpq, mul_one]
    have e2 : ((p : ℝ) * 1 + primePhi 1 + δ) * q = 1 + (primePhi 1 + δ) * q := by
      rw [add_mul, add_mul, mul_one, hpq]; ring
    linarith
  have hfin : (primePhi 1 + δ + 1) * q ≤ (primePhi 1 + δ + 1) * (1 / 2) :=
    mul_le_mul_of_nonneg_left hq2 (by linarith)
  linarith

/-! ## (d) Asymptotics under the prime number theorem -/

section PNT

variable (hθ : Chebyshev.theta ~[atTop] id)
include hθ

/-- For `κ < 1`, eventually `N t + Φ(t) ≥ κ (2π/√3) √(N / log N)` for every `t > 0`, i.e.
`M_N ≥ κ (2π/√3) √(N / log N)` (the saddle estimate behind `tail_upper_bound`). -/
theorem eventually_saddle_lower {κ : ℝ} (hκ : κ < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 < t →
      κ * (2 * π / √3 * √(N / Real.log N)) ≤ N * t + primePhi t := by
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
  intro t ht
  have h1 := hsad t ht
  have hcr : 0 ≤ c * √(N / Real.log N) := mul_nonneg hc0.le (Real.sqrt_nonneg _)
  have hℓ := one_le_log_of_three_le hN
  have := mul_le_mul_of_nonneg_right hκκ₁ hcr
  linarith

/-- **(d)** Under `θ ~ id`: `-log Δ_1(p) / √(p / log p) → 2π/√3`, i.e.
`-log Δ_1(p) ~ 2π √(p / (3 log p))` as `p → ∞`. -/
theorem omitMoment_asymptotic :
    Tendsto (fun p : ℕ => -Real.log (omitMoment p 1) / √(p / Real.log p))
      atTop (𝓝 (2 * π / √3)) := by
  have hc0 : 0 < 2 * π / √3 := by positivity
  set c := 2 * π / √3 with hc
  have hr : ∀ᶠ N : ℕ in atTop, 0 < √(N / Real.log N) := by
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hN0 : (0 : ℝ) < N := by
      have : (3 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hℓ := one_le_log_of_three_le hN
    exact Real.sqrt_pos.2 (by positivity)
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- `b < c`: lower bound from the saddle estimate and (a)
    set κ := max (1 / 2) ((b / c + 1) / 2) with hκdef
    have hbc : b / c < 1 := by rw [div_lt_one hc0]; exact hb
    have hκ1 : κ < 1 := max_lt (by norm_num) (by linarith)
    have hκb : b < κ * c := by
      have : b / c < κ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      rwa [div_lt_iff₀ hc0] at this
    filter_upwards [hr, eventually_saddle_lower hθ hκ1] with N hrN hS
    have hΔ := omitMoment_le_of_saddle hS
    have hpos := omitMoment_pos (p := N) (c := 1) ⟨one_pos, le_rfl⟩
    have hlog := Real.log_le_log hpos hΔ
    rw [Real.log_exp] at hlog
    rw [lt_div_iff₀ hrN]
    have := mul_lt_mul_of_pos_right hκb hrN
    linarith
  · -- `c < b`: upper bound from (c), `M_N ≤ 1 + 2 log N - log(I_N - Λ)`, and Theorem 1.6
    set κ := (b / c + 1) / 2 with hκdef
    have hbc : 1 < b / c := by rw [one_lt_div hc0]; exact hb
    have hκ1 : 1 < κ := by rw [hκdef]; linarith
    have hκb : κ * c < b := by
      have : κ < b / c := by rw [hκdef]; linarith
      rwa [lt_div_iff₀ hc0] at this
    set κ' := (1 + κ) / 2 with hκ'def
    have hκ'1 : 1 < κ' := by rw [hκ'def]; linarith
    set d := (κ - κ') * c with hd
    have hd0 : 0 < d := mul_pos (by rw [hκ'def]; linarith) hc0
    filter_upwards [eventually_ge_atTop 3, hr, tail_lower_bound hθ hκ'1,
      tendsto_log_natCast.eventually (eventually_sq_le_exp (γ := 1 / 2) (K := d / 7)
        (by norm_num) (by positivity))]
      with N hN hrN hL hXe
    obtain ⟨_, _, hrlo, _, _⟩ := sqrt_div_log_bounds hN
    have hℓ := one_le_log_of_three_le hN
    have hI : 0 < F (primesLE N) - primeLambda := (exp_pos _).trans_le hL
    have hlogI := Real.log_le_log (exp_pos _) hL
    rw [Real.log_exp] at hlogI
    have hT := tail_le_of_primePhi N hN (B := saddleMin N) (fun t ht => saddleMin_le N ht)
    have hlogT := Real.log_le_log hI hT
    rw [Real.log_exp] at hlogT
    have hU := neg_log_omitMoment_le_saddleMin (p := N) (by omega)
    have hXe' : Real.log N ^ 2 ≤ d / 7 * rexp (Real.log N / 2) := by
      rw [show Real.log N / 2 = 1 / 2 * Real.log N by ring]; exact hXe
    set ℓ := Real.log N with hℓdef
    set X := rexp (ℓ / 2) with hXdef
    set r := √(N / ℓ) with hrdef
    have h3 : 7 * ℓ * ℓ ≤ d * X := by nlinarith
    have h4 : 7 * ℓ ≤ d * (X / ℓ) := by
      rw [mul_div_assoc', le_div_iff₀ (by linarith)]; exact h3
    have h5 := mul_le_mul_of_nonneg_left hrlo hd0.le
    have hdr : d * r = κ * c * r - κ' * (c * r) := by rw [hd]; ring
    rw [div_lt_iff₀ hrN]
    have := mul_lt_mul_of_pos_right hκb hrN
    linarith

end PNT

end RntPaper
