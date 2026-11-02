import RntPaper.CertAnalytic

/-!
# Executable certificate checks and their soundness

* `scCheck n D G K` (single crossing): `D = v^a (1-v)^b h` (verified factorization), and
  either `h > 0` on `[0,1]`, or `h` has one sign change (bracket found by bisection and
  verified by `crossOK`) and `∫₀¹ u^{K-1} G > 0` exactly. With `G = W · D(u^p)` this gives
  `RunPos (W · D(u^p)) K` (`scCheck_sound`).
* `v1Check` (envelopes): `runPos_of_V1` for `W(u) (E(u) - T(u))` with
  `E(u) ≥ P_M(u^p) (1 - u^{pB}/(1-u^p))`, `T = ∏_{r ∈ Tl}(1 - u^r)` (`v1Check_sound`).
-/

namespace RntPaper.CP

open MeasureTheory intervalIntegral Set RntPaper

/-! ## Substitution `u ↦ u^p` -/

/-- `ev (compPow p D) u = ev D (u^p)` for `p ≥ 1`. -/
def compPow (p : ℕ) : List ℚ → List ℚ
  | [] => []
  | c :: q => c :: shiftN (p - 1) (compPow p q)

theorem ev_compPow {p : ℕ} (hp : 1 ≤ p) (D : List ℚ) (u : ℝ) :
    ev (compPow p D) u = ev D (u ^ p) := by
  induction D with
  | nil => simp [compPow]
  | cons c q ih =>
    simp only [compPow, ev_cons, ev_shiftN, ih]
    congr 1
    rw [← mul_assoc, ← pow_succ']
    congr 2; omega

/-! ## Factorization `D = v^a (1-v)^b h` -/

/-- Strip the factor `v^a`. -/
def stripA : List ℚ → ℕ × List ℚ
  | [] => (0, [])
  | c :: p => if c = 0 then ((stripA p).1 + 1, (stripA p).2) else (0, c :: p)

/-- Quotient by `1 - v` (valid when the coefficient sum vanishes): prefix sums. -/
def divOneSub (p : List ℚ) : List ℚ := ((p.scanl (· + ·) 0).drop 1).dropLast

/-- Strip the factor `(1-v)^b` (at most `fuel` times). -/
def stripB : ℕ → List ℚ → ℕ × List ℚ
  | 0, h => (0, h)
  | fuel + 1, h =>
    if h ≠ [] ∧ h.sum = 0 then ((stripB fuel (divOneSub h)).1 + 1, (stripB fuel (divOneSub h)).2)
    else (0, h)

/-- `v^a (1-v)^b h` as a coefficient list. -/
def factorPoly (a b : ℕ) (h : List ℚ) : List ℚ := shiftN a (mul (prodOneSub (List.replicate b 1)) h)

theorem ev_factorPoly (a b : ℕ) (h : List ℚ) (x : ℝ) :
    ev (factorPoly a b h) x = x ^ a * ((1 - x) ^ b * ev h x) := by
  simp [factorPoly, List.map_replicate, List.prod_replicate]

/-! ## Root brackets -/

/-- Bisection for a sign change of `h` on `[lo, hi]` (`h(lo) > 0 ≥ h(hi)` expected). -/
def bisect (h : List ℚ) : ℕ → ℚ → ℚ → ℚ
  | 0, lo, hi => (lo + hi) / 2
  | n + 1, lo, hi =>
    let m := (lo + hi) / 2
    if 0 < evQ h m then bisect h n m hi else bisect h n lo m

/-- The checked conditions of `signPattern_of`. -/
def crossOK (n : ℕ) (h : List ℚ) (a b : ℚ) : Bool :=
  decide (0 < a) && decide (a < b) && decide (b < 1) && posOn n h 0 a && posOn n (neg h) b 1 &&
    posOn n (neg (deriv h)) a b

def bracketWidths : List ℕ := [6, 8, 10, 12, 14, 16, 18, 20, 22]

/-- A bracket `[a, b]` around the approximate root `m` with endpoints on the grid `2^{-j}`. -/
def tryBracket (n : ℕ) (h : List ℚ) (m : ℚ) (j : ℕ) : Option (ℚ × ℚ) :=
  let a : ℚ := ((⌊m * 2 ^ j⌋ - 1 : ℤ) : ℚ) / 2 ^ j
  let b : ℚ := ((⌈m * 2 ^ j⌉ + 1 : ℤ) : ℚ) / 2 ^ j
  if crossOK n h a b then some (a, b) else none

def findCross (n : ℕ) (h : List ℚ) : Option (ℚ × ℚ) :=
  bracketWidths.findSome? (tryBracket n h (bisect h 26 0 1))

theorem crossOK_sound {n : ℕ} {h : List ℚ} {a b : ℚ} (hc : crossOK n h a b = true) :
    ∃ x₀ ∈ Ioo (0 : ℝ) 1, ev h x₀ = 0 ∧ (∀ x ∈ Ico (0 : ℝ) x₀, 0 < ev h x) ∧
      (∀ x ∈ Ioc x₀ (1 : ℝ), ev h x < 0) := by
  simp only [crossOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨ha, hab⟩, hb⟩, h1⟩, h2⟩, h3⟩ := hc
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hbR : (b : ℝ) < 1 := by exact_mod_cast hb
  have p1 := posOn_sound ha h1
  have p2 := posOn_sound hb h2
  have p3 := posOn_sound hab h3
  simp only [Rat.cast_zero, Rat.cast_one] at p1 p2
  obtain ⟨x₀, hx₀, hpos, hneg⟩ := signPattern_of haR habR hbR (fun x hx => p1 x hx)
    (fun x hx => by have := p2 x hx; simp only [ev_neg] at this; linarith)
    (fun x hx => by have := p3 x hx; simp only [ev_neg] at this; linarith)
  refine ⟨x₀, ⟨haR.trans hx₀.1, hx₀.2.trans hbR⟩, ?_, hpos, hneg⟩
  -- `h(x₀) = 0` by continuity from both sides
  have hc := (continuous_ev h).continuousAt (x := x₀)
  apply le_antisymm
  · by_contra hcon
    push Not at hcon
    have hev : ∀ᶠ y in nhds x₀, 0 < ev h y := hc.eventually (lt_mem_nhds hcon)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hy : x₀ + min (ε / 2) ((1 - x₀) / 2) ∈ Ioc x₀ (1 : ℝ) := by
      have : 0 < 1 - x₀ := by linarith [hx₀.2, hbR]
      constructor
      · have : 0 < min (ε / 2) ((1 - x₀) / 2) := lt_min (by linarith) (by linarith)
        linarith
      · linarith [min_le_right (ε / 2) ((1 - x₀) / 2)]
    have h1' := hneg _ hy
    have h2' := hball (y := x₀ + min (ε / 2) ((1 - x₀) / 2)) (by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (lt_min (by linarith) (by linarith [hx₀.2, hbR]))]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith))
    linarith
  · by_contra hcon
    push Not at hcon
    have hev : ∀ᶠ y in nhds x₀, ev h y < 0 := hc.eventually (gt_mem_nhds hcon)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hx0pos : 0 < x₀ := haR.trans hx₀.1
    have hy : x₀ - min (ε / 2) (x₀ / 2) ∈ Ico (0 : ℝ) x₀ := by
      constructor
      · linarith [min_le_right (ε / 2) (x₀ / 2)]
      · have : 0 < min (ε / 2) (x₀ / 2) := lt_min (by linarith) (by linarith)
        linarith
    have h1' := hpos _ hy
    have h2' := hball (y := x₀ - min (ε / 2) (x₀ / 2)) (by
      rw [Real.dist_eq, show x₀ - min (ε / 2) (x₀ / 2) - x₀ = -min (ε / 2) (x₀ / 2) by ring,
        abs_neg, abs_of_pos (lt_min (by linarith) (by linarith))]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith))
    linarith

/-! ## The single-crossing check -/

/-- **SC check.** `D` is the sign polynomial (in `v`), `G` the integrand polynomial in `u`. -/
def scCheck (n : ℕ) (D G : List ℚ) (K : ℚ) : Bool :=
  let a := (stripA D).1
  let D1 := (stripA D).2
  let b := (stripB 200 D1).1
  let h := (stripB 200 D1).2
  decide (trim (factorPoly a b h) = trim D) &&
    (posOn n h 0 1 ||
      match findCross n h with
      | some (lo, hi) => crossOK n h lo hi && decide (0 < intUnit G K)
      | none => false)

/-- Every factor `1 - u^n` of a weight is in `[0,1]` on `[0,1]`, and positive on `(0,1)`. -/
theorem ev_prodOneSub_pos {l : List ℕ} (hl : ∀ n ∈ l, 1 ≤ n) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < ev (prodOneSub l) u := by
  rw [ev_prodOneSub]
  apply List.prod_pos
  intro x hx
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  have : u ^ n < 1 := pow_lt_one₀ hu.1.le hu.2 (by have := hl n hn; omega)
  linarith

theorem ev_prodOneSub_nonneg (l : List ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ ev (prodOneSub l) u := by
  rw [ev_prodOneSub]
  apply List.prod_nonneg
  intro x hx
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hx
  have : u ^ n ≤ 1 := pow_le_one₀ hu.1 hu.2
  linarith

theorem rpow_inv_pow {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : 1 ≤ p) : (x ^ ((1 : ℝ) / p)) ^ p = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have : (1 : ℝ) / p * p = 1 := by field_simp
  rw [this, Real.rpow_one]

/-- **Soundness of the SC check.** If `W ≥ 0` on `[0,1]`, `W > 0` on `(0,1)`, and the check
passes with `G = W · D(u^p)`, then the running integrals of `u^{k-1} W(u) D(u^p)` are positive
for every `1 ≤ k ≤ K`. -/
theorem scCheck_sound {n : ℕ} {D W : List ℚ} {p : ℕ} (hp : 1 ≤ p) {K : ℚ} (hK : 0 < K)
    (hW0 : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ ev W u) (hW : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < ev W u)
    (h : scCheck n D (mul W (compPow p D)) K = true) :
    RunPos (fun u => ev W u * ev D (u ^ p)) K := by
  simp only [scCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨hfac, hsign⟩ := h
  set a := (stripA D).1
  set b := (stripB 200 (stripA D).2).1
  set hh := (stripB 200 (stripA D).2).2
  have hD : ∀ v : ℝ, ev D v = v ^ a * ((1 - v) ^ b * ev hh v) := by
    intro v
    rw [← ev_trim D, ← hfac, ev_trim, ev_factorPoly]
  have hgc : Continuous fun u : ℝ => ev W u * ev D (u ^ p) :=
    (continuous_ev W).mul ((continuous_ev D).comp (continuous_pow p))
  have hvpos : ∀ v ∈ Ioo (0 : ℝ) 1, 0 < v ^ a * (1 - v) ^ b := fun v hv =>
    mul_pos (pow_pos hv.1 _) (pow_pos (by linarith [hv.2]) _)
  have hupI : ∀ u ∈ Ioo (0 : ℝ) 1, u ^ p ∈ Ioo (0 : ℝ) 1 := fun u hu =>
    ⟨pow_pos hu.1 _, pow_lt_one₀ hu.1.le hu.2 (by omega)⟩
  rcases hsign with hpos | hcross
  · -- no sign change
    have hhpos := posOn_sound (zero_lt_one) hpos
    refine runPos_of_pos hgc (fun u hu => ?_) K
    have hv := hupI u hu
    rw [hD]
    have h1 := hhpos (u ^ p) (by simp only [Rat.cast_zero, Rat.cast_one]; exact ⟨hv.1.le, hv.2.le⟩)
    have h2 := hvpos _ hv
    have h3 := hW u hu
    have : ev W u * ((u ^ p) ^ a * ((1 - u ^ p) ^ b * ev hh (u ^ p)))
        = ev W u * (((u ^ p) ^ a * (1 - u ^ p) ^ b) * ev hh (u ^ p)) := by ring
    rw [this]; exact mul_pos h3 (mul_pos h2 h1)
  · -- one sign change
    cases hfc : findCross n hh with
    | none => rw [hfc] at hcross; simp at hcross
    | some lohi =>
      obtain ⟨lo, hi⟩ := lohi
      rw [hfc] at hcross
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcross
      obtain ⟨hok, hI⟩ := hcross
      obtain ⟨x₀, hx₀, hz, hpos, hneg⟩ := crossOK_sound hok
      set x₁ := x₀ ^ ((1 : ℝ) / p)
      have hx₁p : x₁ ^ p = x₀ := rpow_inv_pow hx₀.1.le hp
      have hx₁0 : 0 < x₁ := Real.rpow_pos_of_pos hx₀.1 _
      have hx₁1 : x₁ < 1 := by
        by_contra hc
        push Not at hc
        have := pow_le_pow_left₀ zero_le_one hc p
        rw [one_pow, hx₁p] at this
        linarith [hx₀.2]
      refine runPos_of_signChange hgc ⟨hx₁0, hx₁1⟩ (fun u hu => ?_) (fun u hu => ?_) ?_
      · have hu1 : u < 1 := hu.2.trans hx₁1
        have hv := hupI u ⟨hu.1, hu1⟩
        have hvx : u ^ p < x₀ := by
          rw [← hx₁p]; exact pow_lt_pow_left₀ hu.2 hu.1.le (by omega)
        rw [hD]
        have h1 := hpos (u ^ p) ⟨hv.1.le, hvx⟩
        have h2 := hvpos _ hv
        have h3 := hW u ⟨hu.1, hu1⟩
        have : ev W u * ((u ^ p) ^ a * ((1 - u ^ p) ^ b * ev hh (u ^ p)))
            = ev W u * (((u ^ p) ^ a * (1 - u ^ p) ^ b) * ev hh (u ^ p)) := by ring
        rw [this]; exact mul_pos h3 (mul_pos h2 h1)
      · have hu0 : 0 ≤ u := hx₁0.le.trans hu.1
        have hvx : x₀ ≤ u ^ p := by rw [← hx₁p]; exact pow_le_pow_left₀ hx₁0.le hu.1 p
        have hv1 : u ^ p ≤ 1 := pow_le_one₀ hu0 hu.2
        have hh0 : ev hh (u ^ p) ≤ 0 := by
          rcases eq_or_lt_of_le hvx with he | hlt
          · rw [← he, hz]
          · exact (hneg _ ⟨hlt, hv1⟩).le
        have hfac0 : 0 ≤ (u ^ p) ^ a * (1 - u ^ p) ^ b :=
          mul_nonneg (pow_nonneg (pow_nonneg hu0 _) _) (pow_nonneg (by linarith) _)
        rw [hD]
        have hW' := hW0 u ⟨hu0, hu.2⟩
        have : (u ^ p) ^ a * ((1 - u ^ p) ^ b * ev hh (u ^ p)) ≤ 0 := by
          rw [← mul_assoc]; exact mul_nonpos_of_nonneg_of_nonpos hfac0 hh0
        exact mul_nonpos_of_nonneg_of_nonpos hW' this
      · have hcongr : (fun u : ℝ => u ^ ((K : ℝ) - 1) * (ev W u * ev D (u ^ p)))
            = fun u => u ^ ((K : ℝ) - 1) * ev (mul W (compPow p D)) u := by
          funext u; rw [ev_mul, ev_compPow hp]
        show 0 < ∫ u in (0 : ℝ)..1, u ^ ((K : ℝ) - 1) * (ev W u * ev D (u ^ p))
        rw [show (fun u : ℝ => u ^ ((K : ℝ) - 1) * (ev W u * ev D (u ^ p))) = _ from hcongr,
          integral_eq_intUnit _ hK]
        exact_mod_cast hI

end RntPaper.CP
