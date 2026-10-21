import RntPaper.Basic
import QProduct.InfiniteProduct

/-!
# Analytic foundations for infinite exponent sets (plan, Phase 3)

For `A : Set ℕ` and `u ∈ [0,1)` the product `qProdSet A u = ∏' n : A, (1 - uⁿ)`
converges (comparison with the geometric series), is the pointwise limit of the
finite truncations `qProd ((range (N+1)).filter (· ∈ A)) u`, lies in `[0,1]`,
is positive when `0 ∉ A`, and is antitone in `A`. Dominated convergence
(bound `1` on `[0,c]`) passes the truncation limit through `∫₀ᶜ`, giving
`tendsto_Fc_truncation` and its prime instance `tendsto_Fc_primesLE`.

Everything is reduced to the `ℕ`-indexed function
`Set.mulIndicator A (fun n => 1 - uⁿ)`, whose `tprod` is `qProdSet A u`
(`tprod_subtype`).
-/

namespace RntPaper

open QProduct MeasureTheory Filter Set intervalIntegral
open scoped Topology

/-! ## Multipliability -/

/-- The indicator geometric coefficients of a set are summable for `0 ≤ u < 1`. -/
theorem summable_indicator_pow_set (A : Set ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    Summable (Set.indicator A (fun n : ℕ => -(u ^ n))) := by
  have hgeom : Summable fun n : ℕ => u ^ n := summable_geometric_of_lt_one h0 h1
  refine Summable.of_abs (hgeom.of_nonneg_of_le (fun n => abs_nonneg _) fun n => ?_)
  by_cases hn : n ∈ A
  · simp [Set.indicator_of_mem hn, abs_of_nonneg (pow_nonneg h0 n)]
  · simp [Set.indicator_of_notMem hn, pow_nonneg h0 n]

/-- The `ℕ`-indexed factor function `n ↦ (1 - uⁿ if n ∈ A else 1)`, written as
`1 + (indicator)`. -/
theorem mulIndicator_eq_one_add_indicator (A : Set ℕ) (u : ℝ) :
    Set.mulIndicator A (fun n : ℕ => 1 - u ^ n) =
      fun n => 1 + Set.indicator A (fun n : ℕ => -(u ^ n)) n := by
  funext n
  by_cases hn : n ∈ A <;> simp [hn, sub_eq_add_neg]

/-- Multipliability of the `ℕ`-indexed factor function. -/
theorem multipliable_mulIndicator (A : Set ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    Multipliable (Set.mulIndicator A (fun n : ℕ => 1 - u ^ n)) := by
  rw [mulIndicator_eq_one_add_indicator]
  exact Real.multipliable_one_add_of_summable (summable_indicator_pow_set A h0 h1)

/-- **Multipliability** of `∏_{n∈A}(1 - uⁿ)` for `0 ≤ u < 1`. -/
theorem multipliable_qProdSet (A : Set ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    Multipliable fun n : A => (1 - u ^ (n : ℕ)) :=
  multipliable_subtype_iff_mulIndicator.mpr (multipliable_mulIndicator A h0 h1)

/-- `qProdSet` as an `ℕ`-indexed product. -/
theorem qProdSet_eq_tprod_mulIndicator (A : Set ℕ) (u : ℝ) :
    qProdSet A u = ∏' n : ℕ, Set.mulIndicator A (fun n : ℕ => 1 - u ^ n) n :=
  tprod_subtype A (fun n : ℕ => 1 - u ^ n)

/-! ## Truncation limit -/

/-- Pointwise convergence of the truncations to `qProdSet`, for `0 ≤ u < 1`. -/
theorem qProdSet_eq_lim (A : Set ℕ) [DecidablePred (· ∈ A)] {u : ℝ}
    (h0 : 0 ≤ u) (h1 : u < 1) :
    Tendsto (fun N => qProd ((Finset.range (N + 1)).filter (· ∈ A)) u) atTop
      (𝓝 (qProdSet A u)) :=
  qProd_filter_tendsto_tprod (fun n => n ∈ A) h0 h1

/-! ## Bounds -/

/-- `0 ≤ qProdSet A u` on `[0,1]`. -/
theorem qProdSet_nonneg (A : Set ℕ) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ qProdSet A u :=
  tprod_nonneg fun _ => sub_nonneg.mpr (pow_le_one₀ hu.1 hu.2)

/-- `qProdSet A u ≤ 1` on `[0,1)`. -/
theorem qProdSet_le_one (A : Set ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    qProdSet A u ≤ 1 := by
  refine (multipliable_qProdSet A h0 h1).tprod_le_of_prod_le fun s => ?_
  refine Finset.prod_le_one₀ (fun _ _ => sub_nonneg.mpr (pow_le_one₀ h0 h1.le)) ?_
  intro _ _
  exact sub_le_self 1 (pow_nonneg h0 _)

/-- `qProdSet A u ∈ [0,1]` on `[0,1)`. -/
theorem qProdSet_mem_Icc (A : Set ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    qProdSet A u ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨qProdSet_nonneg A ⟨h0, h1.le⟩, qProdSet_le_one A h0 h1⟩

/-- Each factor is positive on `[0,1)` when the exponent is nonzero. -/
theorem mulIndicator_pos (A : Set ℕ) (hA : 0 ∉ A) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1)
    (n : ℕ) : 0 < Set.mulIndicator A (fun n : ℕ => 1 - u ^ n) n := by
  by_cases hn : n ∈ A
  · rw [Set.mulIndicator_of_mem hn]
    have hn0 : n ≠ 0 := fun h => hA (h ▸ hn)
    exact sub_pos.mpr (pow_lt_one₀ h0 h1 hn0)
  · rw [Set.mulIndicator_of_notMem hn]
    exact one_pos

/-- **Positivity**: `0 < qProdSet A u` on `[0,1)` when `0 ∉ A` (log/exp route). -/
theorem qProdSet_pos (A : Set ℕ) (hA : 0 ∉ A) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    0 < qProdSet A u := by
  rw [qProdSet_eq_tprod_mulIndicator]
  have hlog : Summable fun n : ℕ =>
      Real.log (Set.mulIndicator A (fun n : ℕ => 1 - u ^ n) n) := by
    rw [mulIndicator_eq_one_add_indicator]
    exact Real.summable_log_one_add_of_summable (summable_indicator_pow_set A h0 h1)
  rw [← Real.rexp_tsum_eq_tprod (mulIndicator_pos A hA h0 h1) hlog]
  exact Real.exp_pos _

/-- Positivity for sets of exponents `≥ 1`. -/
theorem qProdSet_pos_of_one_le (A : Set ℕ) (hA : ∀ n ∈ A, 1 ≤ n) {u : ℝ}
    (h0 : 0 ≤ u) (h1 : u < 1) : 0 < qProdSet A u :=
  qProdSet_pos A (fun h => by have := hA 0 h; omega) h0 h1

/-! ## Antitonicity in the exponent set -/

/-- More factors give a smaller product: `qProdSet T ≤ qProdSet S` for `S ⊆ T`. -/
theorem qProdSet_antitone {S T : Set ℕ} (hST : S ⊆ T) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    qProdSet T u ≤ qProdSet S u := by
  classical
  refine le_of_tendsto_of_tendsto' (qProdSet_eq_lim T h0 h1) (qProdSet_eq_lim S h0 h1)
    fun N => ?_
  apply qProd_antitone_pointwise _ ⟨h0, h1.le⟩
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hST hn.2⟩

/-- Finite/infinite version: `qProdSet T ≤ qProd S` for a finite `S ⊆ T`. -/
theorem qProdSet_le_qProd {T : Set ℕ} (S : Finset ℕ) (hST : (S : Set ℕ) ⊆ T) {u : ℝ}
    (h0 : 0 ≤ u) (h1 : u < 1) : qProdSet T u ≤ qProd S u := by
  rw [← qProdSet_coe]
  exact qProdSet_antitone hST h0 h1

/-- Infinite/finite version: `qProd T ≤ qProdSet S` for `S ⊆ T`, `T` finite. -/
theorem qProd_le_qProdSet {S : Set ℕ} (T : Finset ℕ) (hST : S ⊆ (T : Set ℕ)) {u : ℝ}
    (h0 : 0 ≤ u) (h1 : u < 1) : qProd T u ≤ qProdSet S u := by
  rw [← qProdSet_coe]
  exact qProdSet_antitone hST h0 h1

/-- `H(x) = ∏_{n≥2}(1 - xⁿ)` is below every product over exponents `≥ 2`. -/
theorem Hfun_le_qProdSet_of_lt {T : Set ℕ} (hT : T ⊆ {n | 2 ≤ n}) {x : ℝ}
    (h0 : 0 ≤ x) (h1 : x < 1) : Hfun x ≤ qProdSet T x :=
  qProdSet_antitone hT h0 h1

/-- `H(x) = ∏_{n≥2}(1 - xⁿ)` is below every finite product over exponents `≥ 2`. -/
theorem Hfun_le_qProd_of_lt (T : Finset ℕ) (hT : ∀ n ∈ T, 2 ≤ n) {x : ℝ}
    (h0 : 0 ≤ x) (h1 : x < 1) : Hfun x ≤ qProd T x :=
  qProdSet_le_qProd T (fun n hn => hT n (Finset.mem_coe.mp hn)) h0 h1

theorem Hfun_pos_of_lt {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : 0 < Hfun x :=
  qProdSet_pos _ (by simp) h0 h1

theorem Hfun_nonneg_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ Hfun x :=
  qProdSet_nonneg _ hx

theorem Hfun_le_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : Hfun x ≤ 1 :=
  qProdSet_le_one _ h0 h1

/-! ## Integrability of `qProdSet` on `[0,c]` -/

/-- Almost every `u` (w.r.t. Lebesgue measure restricted to any set) is `≠ 1`. -/
theorem ae_restrict_ne_one (s : Set ℝ) : ∀ᵐ u ∂(volume.restrict s), u ≠ (1 : ℝ) := by
  have hz : volume ({(1:ℝ)} : Set ℝ) = 0 := measure_singleton _
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ (1:ℝ) :=
    (MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hz).mono fun u hu => by simpa using hu
  exact hne.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)

/-- `qProdSet A` is a.e.-strongly measurable on `Ioc 0 c` for `c ≤ 1`, as the
a.e. pointwise limit of the continuous truncations. -/
theorem aestronglyMeasurable_qProdSet_restrict (A : Set ℕ) {c : ℝ} (hc : c ≤ 1) :
    AEStronglyMeasurable (qProdSet A) (volume.restrict (Set.Ioc (0 : ℝ) c)) := by
  classical
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N u => qProd ((Finset.range (N + 1)).filter (· ∈ A)) u)
    (fun N => ((qProd_continuous _).aestronglyMeasurable).restrict) ?_
  have hmem : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) c)),
      u ∈ Set.Ioc (0:ℝ) c := ae_restrict_mem measurableSet_Ioc
  filter_upwards [hmem, ae_restrict_ne_one (Set.Ioc (0:ℝ) c)] with u hu hu1
  exact qProdSet_eq_lim A hu.1.le (lt_of_le_of_ne (hu.2.trans hc) hu1)

/-- **Integrability**: `qProdSet A` is interval-integrable on `[0,c]` for `c ∈ [0,1]`. -/
theorem intervalIntegrable_qProdSet (A : Set ℕ) {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (qProdSet A) volume 0 c := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc.1]
  refine Integrable.mono' (g := fun _ => (1 : ℝ))
    (MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne)
    (aestronglyMeasurable_qProdSet_restrict A hc.2) ?_
  have hmem : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) c)),
      u ∈ Set.Ioc (0:ℝ) c := ae_restrict_mem measurableSet_Ioc
  filter_upwards [hmem, ae_restrict_ne_one (Set.Ioc (0:ℝ) c)] with u hu hu1
  have h1 : u < 1 := lt_of_le_of_ne (hu.2.trans hc.2) hu1
  rw [Real.norm_eq_abs, abs_of_nonneg (qProdSet_nonneg A ⟨hu.1.le, h1.le⟩)]
  exact qProdSet_le_one A hu.1.le h1

/-! ## Finite truncated integrals: basic facts -/

theorem intervalIntegrable_qProd (S : Finset ℕ) (a b : ℝ) :
    IntervalIntegrable (fun u => qProd S u) volume a b :=
  (qProd_continuous S).intervalIntegrable a b

theorem Fc_nonneg {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) (S : Finset ℕ) : 0 ≤ Fc c S := by
  unfold Fc
  apply intervalIntegral.integral_nonneg hc.1
  intro u hu
  exact qProd_nonneg S ⟨hu.1, hu.2.trans hc.2⟩

theorem Fc_le_c {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) (S : Finset ℕ) : Fc c S ≤ c := by
  unfold Fc
  have h := intervalIntegral.integral_mono_on hc.1 (intervalIntegrable_qProd S 0 c)
    (intervalIntegrable_const (c := (1 : ℝ)))
    (fun u hu => qProd_le_one S ⟨hu.1, hu.2.trans hc.2⟩)
  simpa using h

/-- `Fc c` is antitone in the exponent set for `c ∈ [0,1]`. -/
theorem Fc_antitone {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) {S T : Finset ℕ} (hST : S ⊆ T) :
    Fc c T ≤ Fc c S := by
  unfold Fc
  exact intervalIntegral.integral_mono_on hc.1 (intervalIntegrable_qProd T 0 c)
    (intervalIntegrable_qProd S 0 c)
    (fun u hu => qProd_antitone_pointwise hST ⟨hu.1, hu.2.trans hc.2⟩)

/-- The prime truncations `Fc c (primesLE N)` are antitone in `N`. -/
theorem Fc_primesLE_antitone {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    Antitone fun N => Fc c (primesLE N) := by
  intro a b hab
  apply Fc_antitone hc
  intro q hq
  rw [mem_primesLE] at hq ⊢
  exact ⟨hq.1, hq.2.trans hab⟩

/-- The truncations `(range (N+1)).filter (· ∈ A)` are monotone in `N`. -/
theorem filter_range_mono (A : Set ℕ) [DecidablePred (· ∈ A)] :
    Monotone fun N => (Finset.range (N + 1)).filter (· ∈ A) := by
  intro a b hab q hq
  simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢
  exact ⟨by omega, hq.2⟩

theorem Fc_filter_range_antitone {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) (A : Set ℕ)
    [DecidablePred (· ∈ A)] :
    Antitone fun N => Fc c ((Finset.range (N + 1)).filter (· ∈ A)) :=
  fun _ _ hab => Fc_antitone hc (filter_range_mono A hab)

/-! ## Dominated convergence for truncated integrals -/

section Predicate

variable (A : ℕ → Prop) [DecidablePred A]

/-- Dominated convergence on `[0,c]`, `c ∈ [0,1]`, predicate form (LeanCert's
`tendsto_F_filter_integral_tprod` with the upper limit `1` replaced by `c`). -/
theorem tendsto_Fc_filter_integral_tprod {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N => Fc c ((Finset.range (N + 1)).filter A)) atTop
      (𝓝 (∫ u in (0:ℝ)..c, ∏' n : {n : ℕ // A n}, (1 - u ^ (n : ℕ)))) := by
  have hF : ∀ N, Fc c ((Finset.range (N + 1)).filter A) =
      ∫ u in Set.Ioc (0:ℝ) c, qProd ((Finset.range (N + 1)).filter A) u := by
    intro N
    unfold Fc
    exact integral_of_le hc.1
  have hG : (∫ u in (0:ℝ)..c, ∏' n : {n : ℕ // A n}, (1 - u ^ (n : ℕ))) =
      ∫ u in Set.Ioc (0:ℝ) c, ∏' n : {n : ℕ // A n}, (1 - u ^ (n : ℕ)) :=
    integral_of_le hc.1
  simp only [hF, hG]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun _ : ℝ => (1 : ℝ))
  · exact fun N => ((qProd_continuous _).aestronglyMeasurable).restrict
  · exact MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne
  · intro N
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun u hu => ?_)
    have hu' : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu.1.le, hu.2.trans hc.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (qProd_nonneg _ hu')]
    exact qProd_le_one _ hu'
  · have hmem : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) c)),
        u ∈ Set.Ioc (0:ℝ) c := ae_restrict_mem measurableSet_Ioc
    have hne : ∀ᵐ u : ℝ ∂volume, u ≠ (1:ℝ) := by
      have hz : volume ({(1:ℝ)} : Set ℝ) = 0 := measure_singleton _
      have := MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hz
      exact this.mono fun u hu => by simpa using hu
    have hne' : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) c)), u ≠ (1:ℝ) :=
      hne.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)
    filter_upwards [hmem, hne'] with u hu hu1
    exact qProd_filter_tendsto_tprod A hu.1.le (lt_of_le_of_ne (hu.2.trans hc.2) hu1)

end Predicate

/-- **Dominated convergence**: the truncated integrals of the finite truncations
converge to `FcSet c A`, for `c ∈ [0,1]`. -/
theorem tendsto_Fc_truncation (A : Set ℕ) [DecidablePred (· ∈ A)] {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N => Fc c ((Finset.range (N + 1)).filter (· ∈ A))) atTop
      (𝓝 (FcSet c A)) :=
  tendsto_Fc_filter_integral_tprod (fun n => n ∈ A) hc

/-! ### The prime instance -/

/-- `qProdSet Primes` is the prime product of `Lfun` (the subtypes coincide). -/
theorem qProdSet_primes (u : ℝ) :
    qProdSet Primes u = ∏' p : Nat.Primes, (1 - u ^ (p : ℕ)) := rfl

theorem FcSet_primes (c : ℝ) : FcSet c Primes = Lfun c := rfl

/-- The prime truncations converge to `𝓛(c)`. -/
theorem tendsto_Fc_primesLE {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N => Fc c (primesLE N)) atTop (𝓝 (Lfun c)) :=
  tendsto_Fc_filter_integral_tprod Nat.Prime hc

/-- `𝓛(c)` is the infimum of the prime truncations. -/
theorem Lfun_eq_sInf {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    Lfun c = sInf (Set.range fun N => Fc c (primesLE N)) := by
  refine tendsto_nhds_unique (tendsto_Fc_primesLE hc) (tendsto_atTop_ciInf
    (Fc_primesLE_antitone hc) ⟨0, ?_⟩)
  rintro x ⟨N, rfl⟩
  exact Fc_nonneg hc _

/-! ## Monotone limits -/

/-- A bound holding for every truncation holds for `FcSet c A`. -/
theorem FcSet_le_of_forall_Fc_le (A : Set ℕ) [DecidablePred (· ∈ A)] {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) {b : ℝ}
    (h : ∀ N, Fc c ((Finset.range (N + 1)).filter (· ∈ A)) ≤ b) : FcSet c A ≤ b :=
  le_of_tendsto' (tendsto_Fc_truncation A hc) h

/-- A lower bound holding for every truncation holds for `FcSet c A`. -/
theorem le_FcSet_of_forall_le_Fc (A : Set ℕ) [DecidablePred (· ∈ A)] {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) {b : ℝ}
    (h : ∀ N, b ≤ Fc c ((Finset.range (N + 1)).filter (· ∈ A))) : b ≤ FcSet c A :=
  ge_of_tendsto' (tendsto_Fc_truncation A hc) h

/-- A lower bound holding for all large truncations holds for `FcSet c A`. -/
theorem le_FcSet_of_eventually_le_Fc (A : Set ℕ) [DecidablePred (· ∈ A)] {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) {b : ℝ}
    (h : ∀ᶠ N in atTop, b ≤ Fc c ((Finset.range (N + 1)).filter (· ∈ A))) :
    b ≤ FcSet c A :=
  ge_of_tendsto (tendsto_Fc_truncation A hc) h

theorem FcSet_nonneg {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) (A : Set ℕ) : 0 ≤ FcSet c A := by
  classical
  exact le_FcSet_of_forall_le_Fc A hc fun N => Fc_nonneg hc _

theorem FcSet_le_c {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) (A : Set ℕ) : FcSet c A ≤ c := by
  classical
  exact FcSet_le_of_forall_Fc_le A hc fun N => Fc_le_c hc _

/-- `FcSet c A` is the infimum of its truncation integrals. -/
theorem FcSet_eq_sInf (A : Set ℕ) [DecidablePred (· ∈ A)] {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    FcSet c A = sInf (Set.range fun N => Fc c ((Finset.range (N + 1)).filter (· ∈ A))) := by
  refine tendsto_nhds_unique (tendsto_Fc_truncation A hc) (tendsto_atTop_ciInf
    (Fc_filter_range_antitone hc A) ⟨0, ?_⟩)
  rintro x ⟨N, rfl⟩
  exact Fc_nonneg hc _

/-- Every truncation integral dominates the limit. -/
theorem FcSet_le_Fc_truncation (A : Set ℕ) [DecidablePred (· ∈ A)] {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (N : ℕ) :
    FcSet c A ≤ Fc c ((Finset.range (N + 1)).filter (· ∈ A)) :=
  (Fc_filter_range_antitone hc A).le_of_tendsto (tendsto_Fc_truncation A hc) N

/-- `FcSet c T ≤ Fc c S` for a finite `S ⊆ T`. -/
theorem FcSet_le_Fc {T : Set ℕ} (S : Finset ℕ) (hST : (S : Set ℕ) ⊆ T) {c : ℝ}
    (hc : c ∈ Set.Icc (0 : ℝ) 1) : FcSet c T ≤ Fc c S := by
  classical
  refine (FcSet_le_Fc_truncation T hc (S.sup id)).trans (Fc_antitone hc ?_)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hn), hST (Finset.mem_coe.mpr hn)⟩

/-- `FcSet c` is antitone in the exponent set. -/
theorem FcSet_antitone {S T : Set ℕ} (hST : S ⊆ T) {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    FcSet c T ≤ FcSet c S := by
  classical
  refine le_FcSet_of_forall_le_Fc S hc fun N => FcSet_le_Fc _ ?_ hc
  intro n hn
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
  exact hST hn.2

end RntPaper
