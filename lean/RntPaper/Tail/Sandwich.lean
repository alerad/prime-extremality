import RntPaper.Tail.Defs

/-!
# Lemma C: sandwiching `I_N - Λ` by finite products (blueprint `OP3_PLAN.md`)
-/

namespace RntPaper

open QProduct Real Filter Topology Asymptotics MeasureTheory Set

/-! ## Helpers -/

/-- `-log(1-y) ≤ y/(1-y)` for `0 ≤ y < 1`. -/
theorem neg_log_one_sub_le {y : ℝ} (_h0 : 0 ≤ y) (h1 : y < 1) :
    -Real.log (1 - y) ≤ y / (1 - y) := by
  have hpos : 0 < 1 - y := by linarith
  rw [← Real.log_inv]
  have := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  have he : (1 - y)⁻¹ - 1 = y / (1 - y) := by field_simp; ring
  linarith

/-- The `ℕ`-indexed summand of `Φ` at `x = e^{-t}`. -/
noncomputable def phiInd (x : ℝ) (n : ℕ) : ℝ :=
  Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => -Real.log (1 - x ^ n)) n

theorem primePhi_eq_tsum_phiInd {t : ℝ} :
    primePhi t = ∑' n : ℕ, phiInd (rexp (-t)) n := by
  unfold primePhi phiInd
  have h : ∀ p : ℕ, rexp (-((p : ℝ) * t)) = rexp (-t) ^ p := by
    intro p; rw [← Real.exp_nat_mul]; ring_nf
  simp_rw [h]
  exact tsum_subtype {p : ℕ | p.Prime} (fun n : ℕ => -Real.log (1 - rexp (-t) ^ n))

theorem phiInd_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) : 0 ≤ phiInd x n := by
  unfold phiInd
  by_cases hn : n ∈ {p : ℕ | p.Prime}
  · rw [Set.indicator_of_mem hn]
    have hn0 : n ≠ 0 := (show n.Prime from hn).ne_zero
    have hlt : x ^ n < 1 := pow_lt_one₀ h0 h1 hn0
    have : Real.log (1 - x ^ n) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith [pow_nonneg h0 n])
    linarith
  · rw [Set.indicator_of_notMem hn]

theorem phiInd_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    phiInd x n ≤ x ^ n / (1 - x) := by
  have hx1 : 0 < 1 - x := by linarith
  unfold phiInd
  by_cases hn : n ∈ {p : ℕ | p.Prime}
  · rw [Set.indicator_of_mem hn]
    have hn0 : n ≠ 0 := (show n.Prime from hn).ne_zero
    have hle : x ^ n ≤ x := pow_le_of_le_one h0 h1.le hn0
    have hlt : x ^ n < 1 := pow_lt_one₀ h0 h1 hn0
    refine (neg_log_one_sub_le (pow_nonneg h0 n) hlt).trans ?_
    exact div_le_div_of_nonneg_left (pow_nonneg h0 n) hx1 (by linarith)
  · rw [Set.indicator_of_notMem hn]
    exact div_nonneg (pow_nonneg h0 n) hx1.le

theorem summable_phiInd {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : Summable (phiInd x) :=
  Summable.of_nonneg_of_le (phiInd_nonneg h0 h1) (phiInd_le h0 h1)
    ((summable_geometric_of_lt_one h0 h1).div_const _)

/-- `P_N(x) = exp(-∑_{n ≤ N} phiInd x n)` on `[0,1)`. -/
theorem qProd_primesLE_eq_exp {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (N : ℕ) :
    qProd (primesLE N) x = rexp (-∑ n ∈ Finset.range (N + 1), phiInd x n) := by
  unfold qProd primesLE phiInd
  rw [Finset.prod_filter, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun n _ => ?_
  by_cases hn : n.Prime
  · have hmem : n ∈ {p : ℕ | p.Prime} := hn
    rw [ite_eq_left_of_eq_true _ _ (eq_true hn), Set.indicator_of_mem hmem, neg_neg,
      Real.exp_log (by linarith [pow_lt_one₀ h0 h1 hn.ne_zero])]
  · have hmem : n ∉ {p : ℕ | p.Prime} := hn
    rw [ite_eq_right_of_eq_false _ _ (eq_false hn), Set.indicator_of_notMem hmem, neg_zero, Real.exp_zero]

/-! ## Sandwich with finite products (Lemma C) -/

/-- The finite prime product dominates the infinite one:
`e^{-Φ(t)} ≤ P_N(e^{-t})`. -/
theorem exp_neg_primePhi_le_qProd (N : ℕ) {t : ℝ} (ht : 0 < t) :
    rexp (-primePhi t) ≤ qProd (primesLE N) (rexp (-t)) := by
  have h0 : 0 ≤ rexp (-t) := (Real.exp_pos _).le
  have h1 : rexp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [qProd_primesLE_eq_exp h0 h1, primePhi_eq_tsum_phiInd]
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  exact (summable_phiInd h0 h1).sum_le_tsum _ (fun i _ => phiInd_nonneg h0 h1 i)

/-- `P_N(e^{-t}) ≤ exp(-Φ(t) + e^{-(N+1)t}/(1-e^{-t})²)`. -/
theorem qProd_le_exp_neg_primePhi (N : ℕ) {t : ℝ} (ht : 0 < t) :
    qProd (primesLE N) (rexp (-t)) ≤
      rexp (-primePhi t + rexp (-((N + 1 : ℝ) * t)) / (1 - rexp (-t)) ^ 2) := by
  set x := rexp (-t) with hx
  have h0 : 0 ≤ x := (Real.exp_pos _).le
  have h1 : x < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hx1 : 0 < 1 - x := by linarith
  have hpow : rexp (-((N + 1 : ℝ) * t)) = x ^ (N + 1) := by
    rw [hx, ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [qProd_primesLE_eq_exp h0 h1, primePhi_eq_tsum_phiInd, hpow,
    ← (summable_phiInd h0 h1).sum_add_tsum_nat_add (N + 1)]
  refine Real.exp_le_exp.mpr ?_
  have hgs : Summable fun i : ℕ => x ^ (i + (N + 1)) / (1 - x) := by
    have := ((summable_geometric_of_lt_one h0 h1).mul_left (x ^ (N + 1))).div_const (1 - x)
    refine this.congr fun i => ?_
    rw [pow_add]; ring
  have htail : ∑' i : ℕ, phiInd x (i + (N + 1)) ≤ x ^ (N + 1) / (1 - x) ^ 2 := by
    calc ∑' i : ℕ, phiInd x (i + (N + 1))
        ≤ ∑' i : ℕ, x ^ (i + (N + 1)) / (1 - x) :=
          ((summable_nat_add_iff (N + 1)).mpr (summable_phiInd h0 h1)).tsum_le_tsum
            (fun i => phiInd_le h0 h1 _) hgs
      _ = x ^ (N + 1) / (1 - x) * ∑' i : ℕ, x ^ i := by
          rw [← tsum_mul_left]
          congr 1; funext i; rw [pow_add]; ring
      _ = x ^ (N + 1) / (1 - x) ^ 2 := by
          rw [tsum_geometric_of_lt_one h0 h1]; field_simp
  linarith

/-- Upper sandwich: `I_N - Λ` is at most any bound on
`P_N(x) · min(1, x^{N+1}/(1-x))` over `[0,1)`. -/
theorem tail_le_of_forall (N : ℕ) {B : ℝ}
    (hB : ∀ x ∈ Ico (0 : ℝ) 1, qProd (primesLE N) x * min 1 (x ^ (N + 1) / (1 - x)) ≤ B) :
    F (primesLE N) - primeLambda ≤ B := by
  -- pointwise bound for `M ≥ N`
  have hpt : ∀ M, N ≤ M → ∀ x ∈ Ioo (0 : ℝ) 1,
      qProd (primesLE N) x - qProd (primesLE M) x ≤ B := by
    intro M hNM x hx
    have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hST := primesLE_subset hNM
    have hPN := qProd_nonneg (primesLE N) hxI
    have hPM := qProd_nonneg (primesLE M) hxI
    have hbase := qProd_sub_le_commonPrefix_sum (R := primesLE N) (S := primesLE N)
      (T := primesLE M) (subset_refl _) hST hxI
    have hm : ∀ q ∈ primesLE M \ primesLE N, N + 1 ≤ q := by
      intro q hq
      rw [Finset.mem_sdiff, mem_primesLE, mem_primesLE] at hq
      by_contra h
      exact hq.2 ⟨hq.1.1, by omega⟩
    have hsum := one_sub_mul_sum_pow_le hm hxI
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hsum' : ∑ q ∈ primesLE M \ primesLE N, x ^ q ≤ x ^ (N + 1) / (1 - x) := by
      rw [le_div_iff₀ hx1]; linarith
    have hmin : qProd (primesLE N) x - qProd (primesLE M) x ≤
        qProd (primesLE N) x * min 1 (x ^ (N + 1) / (1 - x)) := by
      rcases min_cases 1 (x ^ (N + 1) / (1 - x)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
      · linarith
      · exact hbase.trans (mul_le_mul_of_nonneg_left hsum' hPN)
    exact hmin.trans (hB x ⟨hx.1.le, hx.2⟩)
  have hint : ∀ M, N ≤ M → F (primesLE N) - F (primesLE M) ≤ B := by
    intro M hNM
    unfold F
    rw [← intervalIntegral.integral_sub (intervalIntegrable_qProd _ 0 1)
      (intervalIntegrable_qProd _ 0 1)]
    have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) zero_le_one
      ((intervalIntegrable_qProd _ 0 1).sub (intervalIntegrable_qProd _ 0 1))
      (intervalIntegrable_const (c := B)) (hpt M hNM)
    simpa using this
  have hlim : Tendsto (fun M => F (primesLE N) - F (primesLE M)) atTop
      (𝓝 (F (primesLE N) - primeLambda)) := by
    have h := tendsto_Fc_primesLE (c := 1) ⟨zero_le_one, le_rfl⟩
    simp only [Fc_one, Lfun_one_eq_primeLambda] at h
    exact tendsto_const_nhds.sub h
  exact le_of_tendsto hlim (eventually_atTop.mpr ⟨N, hint⟩)

/-- Lower sandwich: for a prime `q > N` and a window `[a, b] ⊆ [0, 1]`,
`(b - a) · inf_{[a,b]} P_N(x) x^q ≤ I_N - Λ`. -/
theorem le_tail_of_window (N q : ℕ) (hq : q.Prime) (hNq : N < q) {a b B : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hB : ∀ x ∈ Icc a b, B ≤ qProd (primesLE N) x * x ^ q) :
    (b - a) * B ≤ F (primesLE N) - primeLambda := by
  have hq1 : q ∉ primesLE N := fun h => by have := (mem_primesLE.mp h).2; omega
  have hpt : ∀ M, q ≤ M → ∀ x ∈ Icc (0 : ℝ) 1,
      qProd (primesLE N) x * x ^ q ≤ qProd (primesLE N) x - qProd (primesLE M) x := by
    intro M hqM x hx
    have hsub : insert q (primesLE N) ⊆ primesLE M := by
      intro r hr
      rw [Finset.mem_insert] at hr
      rcases hr with rfl | hr
      · exact mem_primesLE.mpr ⟨hq, hqM⟩
      · exact primesLE_subset (by omega) hr
    have h := qProd_antitone_pointwise hsub hx
    have hins : qProd (insert q (primesLE N)) x = (1 - x ^ q) * qProd (primesLE N) x := by
      unfold qProd; rw [Finset.prod_insert hq1]
    rw [hins] at h
    linarith
  have hnn : ∀ M, N ≤ M → ∀ x ∈ Icc (0 : ℝ) 1,
      0 ≤ qProd (primesLE N) x - qProd (primesLE M) x := fun M hNM x hx =>
    sub_nonneg.mpr (qProd_antitone_pointwise (primesLE_subset hNM) hx)
  have hint : ∀ M, q ≤ M → (b - a) * B ≤ F (primesLE N) - F (primesLE M) := by
    intro M hqM
    set D := fun x => qProd (primesLE N) x - qProd (primesLE M) x with hD
    have hDi : ∀ c d : ℝ, IntervalIntegrable D volume c d := fun c d =>
      (intervalIntegrable_qProd _ c d).sub (intervalIntegrable_qProd _ c d)
    have hF : F (primesLE N) - F (primesLE M) = ∫ x in (0 : ℝ)..1, D x := by
      unfold F
      rw [← intervalIntegral.integral_sub (intervalIntegrable_qProd _ 0 1)
        (intervalIntegrable_qProd _ 0 1)]
    have hDnn : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ D x := hnn M (by omega)
    have hab' : (b - a) * B ≤ ∫ x in a..b, D x := by
      have := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := B)) (hDi a b)
        (fun x hx => (hB x hx).trans
          (hpt M hqM x ⟨ha.trans hx.1, hx.2.trans hb⟩))
      simpa using this
    have hsplit : ∫ x in (0 : ℝ)..1, D x =
        (∫ x in (0 : ℝ)..a, D x) + (∫ x in a..b, D x) + ∫ x in b..1, D x := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hDi 0 a) (hDi a b),
        intervalIntegral.integral_add_adjacent_intervals (hDi 0 b) (hDi b 1)]
    have h0a : 0 ≤ ∫ x in (0 : ℝ)..a, D x :=
      intervalIntegral.integral_nonneg ha fun x hx =>
        hDnn x ⟨hx.1, hx.2.trans (hab.trans hb)⟩
    have hb1 : 0 ≤ ∫ x in b..1, D x :=
      intervalIntegral.integral_nonneg hb fun x hx =>
        hDnn x ⟨ha.trans (hab.trans hx.1), hx.2⟩
    rw [hF, hsplit]
    linarith
  have hlim : Tendsto (fun M => F (primesLE N) - F (primesLE M)) atTop
      (𝓝 (F (primesLE N) - primeLambda)) := by
    have h := tendsto_Fc_primesLE (c := 1) ⟨zero_le_one, le_rfl⟩
    simp only [Fc_one, Lfun_one_eq_primeLambda] at h
    exact tendsto_const_nhds.sub h
  exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨q, hint⟩)

end RntPaper
