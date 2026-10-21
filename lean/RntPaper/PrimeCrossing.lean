import RntPaper.ProductCont
import RntPaper.SingleCrossing

/-!
# Single crossing for the prime product and weighted running integrals

`q(x) = log(Q(x)/(1-x)) = log(1+x) + ∑_{p ≥ 3 prime} log(1 - xᵖ)` is strictly
concave on `[0,1)`, vanishes at `0`, is positive near `0` (it dominates the
analogous function `h` for `H`, because `Q ≥ H`) and negative near `1`
(`Q ≤ (1-x²)(1-x³)`).  Hence `Q - (1-x)` is `+` then `-` with a single crossing
`x* ∈ (0,1)`.  From this, positivity of the weighted running integrals
`J_s(z) = ∫₀ᶻ x^{s-1}(Q(x) - (1-x)) dx` for `1 ≤ s ≤ b` follows from `J_b(1) > 0`.
-/

namespace RntPaper

open QProduct MeasureTheory Set Filter Topology intervalIntegral

/-- Odd primes. -/
private abbrev OddPrimes : Set ℕ := Primes \ {2}

theorem zero_not_mem_oddPrimes : (0 : ℕ) ∉ OddPrimes := fun h => Nat.not_prime_zero h.1

theorem three_mem_oddPrimes : (3 : ℕ) ∈ OddPrimes := ⟨Nat.prime_three, by simp⟩

/-- `q(x) = log(Q(x)/(1-x))`. -/
noncomputable def qlog (x : ℝ) : ℝ := Real.log (Qfun x / (1 - x))

/-- `∑_{p odd prime} log(1 - xᵖ)`, written over `ℕ` with indicator factors. -/
noncomputable def qlogTail (x : ℝ) : ℝ := ∑' n : ℕ, Real.log (indFactor OddPrimes x n)

theorem indFactor_eq_one_add (A : Set ℕ) (x : ℝ) :
    indFactor A x = fun n => 1 + Set.indicator A (fun n : ℕ => -(x ^ n)) n := by
  rw [← mulIndicator_eq_indFactor, mulIndicator_eq_one_add_indicator]

theorem summable_log_indFactor (A : Set ℕ) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    Summable fun n : ℕ => Real.log (indFactor A x n) := by
  rw [indFactor_eq_one_add]
  exact Real.summable_log_one_add_of_summable (summable_indicator_pow_set A hx.1 hx.2)

theorem indFactor_pos {A : Set ℕ} (hA : 0 ∉ A) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) (n : ℕ) :
    0 < indFactor A x n := by
  rw [← mulIndicator_eq_indFactor]
  exact mulIndicator_pos A hA hx.1 hx.2 n

theorem qProdSet_oddPrimes_eq_exp {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    qProdSet OddPrimes x = Real.exp (qlogTail x) := by
  rw [qProdSet_eq_tprod_indFactor, qlogTail]
  exact (Real.rexp_tsum_eq_tprod (indFactor_pos zero_not_mem_oddPrimes hx)
    (summable_log_indFactor _ hx)).symm

/-- `q = log(1+x) + ∑_{p odd} log(1 - xᵖ)` on `[0,1)`. -/
theorem qlog_eq_tail {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    qlog x = Real.log (1 + x) + qlogTail x := by
  have h1x : 0 < 1 - x := by linarith [hx.2]
  unfold qlog
  rw [Qfun_eq_mul hx.1 hx.2, qProdSet_oddPrimes_eq_exp hx]
  have e : (1 - x ^ 2) * Real.exp (qlogTail x) / (1 - x)
      = (1 + x) * Real.exp (qlogTail x) := by
    field_simp; ring
  rw [e, Real.log_mul (by linarith [hx.1]) (Real.exp_pos _).ne', Real.log_exp]

/-- Each term `x ↦ log(1 - 1_A(n) xⁿ)` is concave on `[0,1)` when `0 ∉ A`. -/
theorem concaveOn_log_indFactor {A : Set ℕ} (hA : 0 ∉ A) (n : ℕ) :
    ConcaveOn ℝ (Ico (0:ℝ) 1) (fun x => Real.log (indFactor A x n)) := by
  by_cases hn : n ∈ A
  · have hn0 : n ≠ 0 := fun h => hA (h ▸ hn)
    have : (fun x => Real.log (indFactor A x n)) = fun x => Real.log (1 - x ^ n) := by
      funext x; simp [indFactor, hn]
    rw [this]
    exact concaveOn_log_one_sub_pow hn0
  · have : (fun x => Real.log (indFactor A x n)) = fun _ => (0:ℝ) := by
      funext x; simp [indFactor, hn]
    rw [this]
    exact concaveOn_const _ (convex_Ico _ _)

theorem qlogTail_concaveOn : ConcaveOn ℝ (Ico (0:ℝ) 1) qlogTail := by
  refine ⟨convex_Ico _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy : a • x + b • y ∈ Ico (0:ℝ) 1 := (convex_Ico (0:ℝ) 1) hx hy ha hb hab
  have sx := summable_log_indFactor OddPrimes hx
  have sy := summable_log_indFactor OddPrimes hy
  unfold qlogTail
  simp only [smul_eq_mul] at hxy ⊢
  rw [← tsum_mul_left, ← tsum_mul_left, ← (sx.mul_left a).tsum_add (sy.mul_left b)]
  refine Summable.tsum_le_tsum (fun n => ?_) ((sx.mul_left a).add (sy.mul_left b))
    (summable_log_indFactor OddPrimes hxy)
  have := (concaveOn_log_indFactor zero_not_mem_oddPrimes n).2 hx hy ha hb hab
  simpa only [smul_eq_mul] using this

/-- `q` is strictly concave on `[0,1)`. -/
theorem qlog_strictConcaveOn : StrictConcaveOn ℝ (Ico (0 : ℝ) 1) qlog :=
  (strictConcaveOn_log_one_add.add_concaveOn qlogTail_concaveOn).congr
    fun _ hx => (qlog_eq_tail hx).symm

theorem qlog_zero : qlog 0 = 0 := by
  unfold qlog
  rw [Qfun_zero]; simp

theorem qlog_continuousOn : ContinuousOn qlog (Ico (0:ℝ) 1) := by
  unfold qlog
  apply ContinuousOn.log
  · apply ContinuousOn.div (Qfun_continuousOn.mono Ico_subset_Icc_self) (by fun_prop)
    intro x hx; linarith [hx.2]
  · intro x hx
    exact (div_pos (Qfun_pos hx.1 hx.2) (by linarith [hx.2])).ne'

/-- `H ≤ Q` on `[0,1)`. -/
theorem Hfun_le_Qfun {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : Hfun x ≤ Qfun x :=
  Hfun_le_qProdSet_of_lt (fun _ hp => Nat.Prime.two_le hp) h0 h1

/-- `h ≤ q` on `[0,1)`. -/
theorem hlog_le_qlog {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) : hlog x ≤ qlog x := by
  unfold hlog qlog
  have h1x : 0 < 1 - x := by linarith [hx.2]
  exact Real.log_le_log (div_pos (Hfun_pos hx) h1x)
    (div_le_div_of_nonneg_right (Hfun_le_Qfun hx.1 hx.2) h1x.le)

theorem qlog_pos_near_zero : ∃ δ > 0, ∀ x ∈ Ioo (0 : ℝ) δ, 0 < qlog x := by
  obtain ⟨δ, hδ, h⟩ := hlog_pos_near_zero
  refine ⟨min δ 1, lt_min hδ one_pos, fun x hx => ?_⟩
  have hx' : x ∈ Ico (0:ℝ) 1 := ⟨hx.1.le, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
  exact (h x ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩).trans_le (hlog_le_qlog hx')

/-- `Q ≤ (1-x²)(1-x³)`, so `q < 0` on `(9/10, 1)`. -/
theorem qlog_neg_near_one : ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ x ∈ Ioo δ 1, qlog x < 0 := by
  refine ⟨9 / 10, ⟨by norm_num, by norm_num⟩, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hQ : Qfun x ≤ (1 - x ^ 2) * (1 - x ^ 3) := by
    rw [Qfun_eq_mul hx0 hx.2]
    have h2 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.2]
    exact mul_le_mul_of_nonneg_left
      (qProdSet_le_one_sub_pow three_mem_oddPrimes ⟨hx0, hx.2.le⟩) h2
  unfold qlog
  apply Real.log_neg (div_pos (Qfun_pos hx0 hx.2) h1x)
  rw [div_lt_one h1x]
  have e : (1 - x ^ 2) * (1 - x ^ 3) = (1 - x) * ((1 + x) * (1 - x ^ 3)) := by ring
  have hxp : (0:ℝ) < x := by linarith [hx.1]
  have h2 : 81 / 100 < x ^ 2 := by nlinarith [hx.1]
  have h3 : 729 / 1000 < x ^ 3 := by
    have : x ^ 3 = x ^ 2 * x := by ring
    rw [this]; nlinarith [hx.1]
  have hneg' : x * (1 - x ^ 2 - x ^ 3) < 0 := mul_neg_of_pos_of_neg hxp (by linarith)
  have hlt : (1 + x) * (1 - x ^ 3) < 1 := by
    have : (1 + x) * (1 - x ^ 3) = 1 + x * (1 - x ^ 2 - x ^ 3) := by ring
    rw [this]; linarith
  have : (1 - x) * ((1 + x) * (1 - x ^ 3)) < (1 - x) * 1 := mul_lt_mul_of_pos_left hlt h1x
  linarith

/-- Q(x) - (1-x) changes sign exactly once on (0,1), from + to −. -/
theorem Qfun_single_crossing : ∃ xs ∈ Ioo (0:ℝ) 1,
    (∀ x ∈ Ioo 0 xs, 1 - x < Qfun x) ∧ (∀ x ∈ Ioo xs 1, Qfun x < 1 - x) := by
  obtain ⟨δ, hδ, hpos⟩ := qlog_pos_near_zero
  obtain ⟨δ', hδ', hneg⟩ := qlog_neg_near_one
  set p := min δ δ' / 2 with hp
  set q := (δ' + 1) / 2 with hq
  have hp0 : 0 < p := by rw [hp]; exact half_pos (lt_min hδ hδ'.1)
  have hpδ : p < δ := by rw [hp]; linarith [min_le_left δ δ', half_lt_self (lt_min hδ hδ'.1)]
  have hpδ' : p < δ' := by rw [hp]; linarith [min_le_right δ δ', half_lt_self (lt_min hδ hδ'.1)]
  have hq1 : q < 1 := by rw [hq]; linarith [hδ'.2]
  have hqδ' : δ' < q := by rw [hq]; linarith [hδ'.2]
  have hpq : p < q := by linarith
  have hhp : 0 < qlog p := hpos p ⟨hp0, hpδ⟩
  have hhq : qlog q < 0 := hneg q ⟨hqδ', hq1⟩
  have hcont : ContinuousOn qlog (Icc p q) :=
    qlog_continuousOn.mono fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨a, ⟨hpa, haq⟩, ha0⟩ := intermediate_value_Ioo' hpq.le hcont ⟨hhq, hhp⟩
  have ha : a ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have ha' : a ∈ Ico (0:ℝ) 1 := ⟨ha.1.le, ha.2⟩
  have hsign_pos : ∀ x ∈ Ioo (0:ℝ) a, 0 < qlog x := by
    intro x hx
    have hxa : x / a < 1 := (div_lt_one ha.1).mpr hx.2
    have h := qlog_strictConcaveOn.2 (show (0:ℝ) ∈ Ico (0:ℝ) 1 by simp) ha' ha.1.ne
      (show 0 < 1 - x / a by linarith) (show 0 < x / a from div_pos hx.1 ha.1) (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, qlog_zero, ha0] at h
    rwa [div_mul_cancel₀ _ ha.1.ne'] at h
  have hsign_neg : ∀ x ∈ Ioo a 1, qlog x < 0 := by
    intro x hx
    have hx0 : 0 < x := by linarith [ha.1, hx.1]
    have hx' : x ∈ Ico (0:ℝ) 1 := ⟨hx0.le, hx.2⟩
    have hax : a / x < 1 := (div_lt_one hx0).mpr hx.1
    have h := qlog_strictConcaveOn.2 (show (0:ℝ) ∈ Ico (0:ℝ) 1 by simp) hx' hx0.ne
      (show 0 < 1 - a / x by linarith) (show 0 < a / x from div_pos ha.1 hx0) (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, qlog_zero] at h
    rw [div_mul_cancel₀ _ hx0.ne', ha0] at h
    by_contra hcon
    have := mul_nonneg (div_pos ha.1 hx0).le (not_lt.mp hcon)
    linarith
  have hratio : ∀ x ∈ Ico (0:ℝ) 1, 0 < Qfun x / (1 - x) :=
    fun x hx => div_pos (Qfun_pos hx.1 hx.2) (by linarith [hx.2])
  refine ⟨a, ha, fun x hx => ?_, fun x hx => ?_⟩
  · have hx' : x ∈ Ico (0:ℝ) 1 := ⟨hx.1.le, by linarith [hx.2, ha.2]⟩
    have h := hsign_pos x hx
    unfold qlog at h
    rw [Real.log_pos_iff (hratio x hx').le, one_lt_div (by linarith [hx'.2])] at h
    exact h
  · have hx' : x ∈ Ico (0:ℝ) 1 := ⟨by linarith [hx.1, ha.1], hx.2⟩
    have h := hsign_neg x hx
    unfold qlog at h
    rw [Real.log_neg_iff (hratio x hx'), div_lt_one (by linarith [hx'.2])] at h
    exact h

/-! ## Weighted running integrals -/

/-- Weighted running integral J_s(z) = ∫₀ᶻ x^{s-1} (Q(x) - (1-x)) dx (real exponent, `Real.rpow`). -/
noncomputable def Jw (s z : ℝ) : ℝ := ∫ x in (0:ℝ)..z, x ^ (s - 1) * (Qfun x - (1 - x))

theorem continuousOn_Jw_integrand {s : ℝ} (hs : 1 ≤ s) :
    ContinuousOn (fun x => x ^ (s - 1) * (Qfun x - (1 - x))) (Icc 0 1) :=
  ((Real.continuous_rpow_const (by linarith)).continuousOn).mul
    (Qfun_continuousOn.sub (by fun_prop))

/-- `Q(0) - (1 - 0) = 0` and `Q(1) - (1 - 1) = 0`. -/
private theorem g_zero : Qfun 0 - (1 - 0) = 0 := by rw [Qfun_zero]; ring
private theorem g_one : Qfun 1 - (1 - 1) = 0 := by rw [Qfun_one]; ring

/-- If J_b(1) > 0 then J_s(z) > 0 for 1 ≤ s ≤ b and every z ∈ (0,1]. -/
theorem Jw_pos_of {b s : ℝ} (h1s : 1 ≤ s) (hsb : s ≤ b) (hb : 0 < Jw b 1) {z : ℝ}
    (hz : z ∈ Ioc (0:ℝ) 1) : 0 < Jw s z := by
  obtain ⟨xs, hxs, hposo, hnego⟩ := Qfun_single_crossing
  set g : ℝ → ℝ := fun x => Qfun x - (1 - x) with hg
  -- sign of `g` on `[0,1]`
  have gpos : ∀ x ∈ Icc (0:ℝ) xs, 0 ≤ g x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; simp only [hg]; rw [g_zero]
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · subst h'
      -- continuity: `g xs ≥ 0` as a limit from the left; easier: use concavity-free argument
      by_contra hcon
      push Not at hcon
      have hc : ContinuousOn g (Icc 0 1) := Qfun_continuousOn.sub (by fun_prop)
      have hct : ContinuousWithinAt g (Ioo 0 x) x :=
        (hc x ⟨hx.1, hxs.2.le⟩).mono fun y hy => ⟨hy.1.le, by linarith [hy.2, hxs.2]⟩
      have hev : ∀ᶠ y in 𝓝[Ioo 0 x] x, g y < 0 := hct.eventually (gt_mem_nhds hcon)
      have hne : (𝓝[Ioo (0:ℝ) x] x).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo h.ne]
        exact ⟨h.le, le_rfl⟩
      obtain ⟨y, hy1, hy2⟩ := (hev.and self_mem_nhdsWithin).exists
      have := hposo y hy2
      simp only [hg] at hy1
      linarith
    · have := hposo x ⟨h, h'⟩; simp only [hg]; linarith
  have gneg : ∀ x ∈ Icc xs (1:ℝ), g x ≤ 0 := by
    intro x hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst h; simp only [hg]; rw [g_one]
    rcases eq_or_lt_of_le hx.1 with h' | h'
    · subst h'
      by_contra hcon
      push Not at hcon
      have hc : ContinuousOn g (Icc 0 1) := Qfun_continuousOn.sub (by fun_prop)
      have hct : ContinuousWithinAt g (Ioo xs 1) xs :=
        (hc xs ⟨hxs.1.le, hxs.2.le⟩).mono fun y hy => ⟨by linarith [hy.1, hxs.1], hy.2.le⟩
      have hev : ∀ᶠ y in 𝓝[Ioo xs 1] xs, 0 < g y := hct.eventually (lt_mem_nhds hcon)
      have hne : (𝓝[Ioo xs (1:ℝ)] xs).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo h.ne]
        exact ⟨le_rfl, h.le⟩
      obtain ⟨y, hy1, hy2⟩ := (hev.and self_mem_nhdsWithin).exists
      have := hnego y hy2
      simp only [hg] at hy1
      linarith
    · have := hnego x ⟨h', h⟩; simp only [hg]; linarith
  have hint : ∀ t : ℝ, 1 ≤ t → ∀ x y : ℝ, x ∈ Icc (0:ℝ) 1 → y ∈ Icc (0:ℝ) 1 →
      IntervalIntegrable (fun u => u ^ (t - 1) * (Qfun u - (1 - u))) volume x y :=
    fun t ht x y hx hy => ((continuousOn_Jw_integrand ht).mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  have h1b : 1 ≤ b := h1s.trans hsb
  obtain ⟨hz0, hz1⟩ := hz
  -- `J_s(1) ≥ xs^{s-b} J_b(1) > 0`
  have hJ1 : 0 < Jw s 1 := by
    set c := xs ^ (s - b) with hc
    have hc0 : 0 < c := Real.rpow_pos_of_pos hxs.1 _
    have hdiff : 0 ≤ ∫ x in (0:ℝ)..1,
        (x ^ (s - 1) * (Qfun x - (1 - x)) - c * (x ^ (b - 1) * (Qfun x - (1 - x)))) := by
      apply intervalIntegral.integral_nonneg zero_le_one
      intro x hx
      have hgx : g x = Qfun x - (1 - x) := rfl
      rcases eq_or_lt_of_le hx.1 with h0 | h0
      · subst h0; rw [g_zero]; simp
      have hsplit : x ^ (s - 1) = x ^ (s - b) * x ^ (b - 1) := by
        rw [← Real.rpow_add h0]; ring_nf
      have hxb : 0 ≤ x ^ (b - 1) := Real.rpow_nonneg hx.1 _
      have e : x ^ (s - 1) * (Qfun x - (1 - x)) - c * (x ^ (b - 1) * (Qfun x - (1 - x)))
          = (x ^ (s - b) - c) * x ^ (b - 1) * g x := by rw [hsplit, hgx]; ring
      rw [e]
      rcases le_total x xs with hle | hle
      · have : c ≤ x ^ (s - b) := Real.rpow_le_rpow_of_nonpos h0 hle (by linarith)
        exact mul_nonneg (mul_nonneg (by linarith) hxb) (gpos x ⟨hx.1, hle⟩)
      · have : x ^ (s - b) ≤ c := Real.rpow_le_rpow_of_nonpos hxs.1 hle (by linarith)
        exact mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) hxb) (gneg x ⟨hle, hx.2⟩)
    have I01 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have I11 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    rw [intervalIntegral.integral_sub (hint s h1s 0 1 I01 I11)
      ((hint b h1b 0 1 I01 I11).const_mul c), intervalIntegral.integral_const_mul] at hdiff
    unfold Jw
    have : 0 < c * Jw b 1 := mul_pos hc0 hb
    unfold Jw at this
    linarith
  rcases le_total z xs with hzx | hzx
  · -- integrand `≥ 0` on `[0,z]`, positive inside
    apply intervalIntegral.integral_pos hz0 ((continuousOn_Jw_integrand h1s).mono
      (Icc_subset_Icc le_rfl hz1))
    · intro x hx
      exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (gpos x ⟨hx.1.le, hx.2.trans hzx⟩)
    · refine ⟨z / 2, ⟨by positivity, by linarith⟩, ?_⟩
      exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
        (by linarith [hposo (z / 2) ⟨by positivity, by linarith⟩])
  · -- `J_s(z) ≥ J_s(1)` since the integrand is `≤ 0` on `[z,1]`
    have hsplit : Jw s 1 = Jw s z + ∫ x in z..1, x ^ (s - 1) * (Qfun x - (1 - x)) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hint s h1s 0 z ⟨le_rfl, zero_le_one⟩ ⟨hz0.le, hz1⟩)
        (hint s h1s z 1 ⟨hz0.le, hz1⟩ ⟨zero_le_one, le_rfl⟩)).symm
    have htail : (∫ x in z..1, x ^ (s - 1) * (Qfun x - (1 - x))) ≤ 0 := by
      have := intervalIntegral.integral_nonneg (μ := volume) hz1
        (f := fun x => -(x ^ (s - 1) * (Qfun x - (1 - x)))) fun x hx =>
        neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hz0.le.trans hx.1) _)
          (gneg x ⟨hzx.trans hx.1, hx.2⟩))
      rw [intervalIntegral.integral_neg] at this
      linarith
    linarith

end RntPaper
