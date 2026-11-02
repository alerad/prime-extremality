import RntPaper.CertCheck

/-!
# Integer versions of the sign-pattern certificates

The bisection test of `CertPoly` in rational arithmetic is slow for degrees in the hundreds
(every operation normalizes a fraction). Here the same test runs on integer polynomials:

* `halfZ p = 2^{deg p} p(t/2)` (shifts), `taylorZ 1` (additions only) for the right half;
* `dyPoly p A W s` has value `2^{s·len} p((A + W t)/2^s)` up to the factor `2^s`;
* `posOnZ n p A B s` proves `p > 0` on `[A/2^s, B/2^s]`;
* `findCrossZ` locates a root bracket on a dyadic grid (unverified search), `crossOKZ` verifies it;
* `scCheckZ` is `scCheck` with these integer tests (`scCheckZ_sound`).
-/

namespace RntPaper.CP

open MeasureTheory intervalIntegral Set RntPaper

/-! ## Integer polynomials -/

def evZ : List ℤ → ℝ → ℝ
  | [], _ => 0
  | c :: p, x => (c : ℝ) + x * evZ p x

@[simp] theorem evZ_nil (x : ℝ) : evZ [] x = 0 := rfl
@[simp] theorem evZ_cons (c : ℤ) (p : List ℤ) (x : ℝ) : evZ (c :: p) x = c + x * evZ p x := rfl

theorem continuous_evZ (p : List ℤ) : Continuous (evZ p) := by
  induction p with
  | nil => exact continuous_const
  | cons c p ih => exact continuous_const.add (continuous_id.mul ih)

def addZ : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addZ p q

@[simp] theorem evZ_addZ (p q : List ℤ) (x : ℝ) : evZ (addZ p q) x = evZ p x + evZ q x := by
  induction p generalizing q with
  | nil => simp [addZ]
  | cons a p ih =>
    cases q with
    | nil => simp [addZ]
    | cons b q => simp [addZ, ih]; ring

def smulZ (a : ℤ) (p : List ℤ) : List ℤ := p.map (a * ·)

@[simp] theorem evZ_smulZ (a : ℤ) (p : List ℤ) (x : ℝ) : evZ (smulZ a p) x = a * evZ p x := by
  induction p with
  | nil => simp [smulZ]
  | cons c p ih =>
    simp only [smulZ, List.map_cons] at ih ⊢
    simp [ih]; ring

def negZ (p : List ℤ) : List ℤ := p.map (- ·)

@[simp] theorem evZ_negZ (p : List ℤ) (x : ℝ) : evZ (negZ p) x = - evZ p x := by
  induction p with
  | nil => simp [negZ]
  | cons c p ih =>
    simp only [negZ, List.map_cons] at ih ⊢
    simp [ih]; ring

/-- `(a + x) p(x)`. -/
def mulLinZ (a : ℤ) (p : List ℤ) : List ℤ := addZ (smulZ a p) (0 :: p)

@[simp] theorem evZ_mulLinZ (a : ℤ) (p : List ℤ) (x : ℝ) :
    evZ (mulLinZ a p) x = (a + x) * evZ p x := by
  simp [mulLinZ]; ring

def taylorZ (a : ℤ) : List ℤ → List ℤ
  | [] => []
  | c :: p => addZ [c] (mulLinZ a (taylorZ a p))

@[simp] theorem evZ_taylorZ (a : ℤ) (p : List ℤ) (t : ℝ) : evZ (taylorZ a p) t = evZ p (a + t) := by
  induction p with
  | nil => simp [taylorZ]
  | cons c p ih => simp [taylorZ, ih]

def scaleAuxZ (w : ℤ) : ℤ → List ℤ → List ℤ
  | _, [] => []
  | s, c :: p => (c * s) :: scaleAuxZ w (s * w) p

theorem evZ_scaleAuxZ (w : ℤ) (p : List ℤ) (s : ℤ) (t : ℝ) :
    evZ (scaleAuxZ w s p) t = s * evZ p (w * t) := by
  induction p generalizing s with
  | nil => simp [scaleAuxZ]
  | cons c p ih => simp [scaleAuxZ, ih]; ring

def scaleZ (w : ℤ) (p : List ℤ) : List ℤ := scaleAuxZ w 1 p

@[simp] theorem evZ_scaleZ (w : ℤ) (p : List ℤ) (t : ℝ) : evZ (scaleZ w p) t = evZ p (w * t) := by
  simp [scaleZ, evZ_scaleAuxZ]

/-- `halfZ p = 2^{len p - 1} p(t/2)` (as `2 · halfZ = 2^{len} p(t/2)`). -/
def halfZ : List ℤ → List ℤ
  | [] => []
  | c :: q => (2 ^ q.length * c) :: halfZ q

theorem length_halfZ (p : List ℤ) : (halfZ p).length = p.length := by
  induction p with
  | nil => rfl
  | cons c q ih => simp [halfZ, ih]

theorem evZ_halfZ (p : List ℤ) (t : ℝ) : 2 * evZ (halfZ p) t = 2 ^ p.length * evZ p (t / 2) := by
  induction p with
  | nil => simp [halfZ]
  | cons c q ih =>
    simp only [halfZ, evZ_cons, List.length_cons]
    push_cast
    have : 2 * (2 ^ q.length * (c : ℝ) + t * evZ (halfZ q) t)
        = 2 ^ (q.length + 1) * c + t * (2 * evZ (halfZ q) t) := by ring
    rw [this, ih]; ring

theorem length_halfZ_iter (s : ℕ) (p : List ℤ) : (halfZ^[s] p).length = p.length := by
  induction s with
  | zero => rfl
  | succ s ihs => rw [Function.iterate_succ_apply', length_halfZ, ihs]

theorem evZ_halfZ_iter (s : ℕ) (p : List ℤ) (t : ℝ) :
    2 ^ s * evZ (halfZ^[s] p) t = (2 ^ p.length) ^ s * evZ p (t / 2 ^ s) := by
  induction s generalizing t with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    have hlen : (halfZ^[s] p).length = p.length := length_halfZ_iter s p
    have h1 := evZ_halfZ (halfZ^[s] p) t
    rw [hlen] at h1
    have h2 := ih (t / 2)
    rw [pow_succ]
    calc 2 ^ s * 2 * evZ (halfZ (halfZ^[s] p)) t
        = 2 ^ s * (2 * evZ (halfZ (halfZ^[s] p)) t) := by ring
      _ = 2 ^ s * (2 ^ p.length * evZ (halfZ^[s] p) (t / 2)) := by rw [h1]
      _ = 2 ^ p.length * (2 ^ s * evZ (halfZ^[s] p) (t / 2)) := by ring
      _ = 2 ^ p.length * ((2 ^ p.length) ^ s * evZ p (t / 2 / 2 ^ s)) := by rw [h2]
      _ = (2 ^ p.length) ^ (s + 1) * evZ p (t / (2 ^ s * 2)) := by
        rw [div_div, mul_comm (2 : ℝ) (2 ^ s)]; ring

def derivZ : List ℤ → List ℤ
  | [] => []
  | _ :: p => addZ p (0 :: derivZ p)

theorem hasDerivAt_evZ (p : List ℤ) (x : ℝ) : HasDerivAt (evZ p) (evZ (derivZ p) x) x := by
  induction p with
  | nil =>
    have h0 : evZ [] = fun _ : ℝ => (0 : ℝ) := funext fun _ => rfl
    rw [h0]; simp only [derivZ, evZ_nil]; exact hasDerivAt_const x 0
  | cons c p ih =>
    have h := (hasDerivAt_id x).mul ih
    have h2 := (hasDerivAt_const x (c : ℝ)).add h
    convert h2 using 1
    · funext y; simp
    · simp [derivZ]

/-! ## Positivity tests -/

def negSumZ : List ℤ → ℤ
  | [] => 0
  | c :: p => min 0 c + negSumZ p

def lowBZ : List ℤ → ℤ
  | [] => 0
  | c :: p => c + negSumZ p

theorem negSumZ_nonpos (p : List ℤ) : negSumZ p ≤ 0 := by
  induction p with
  | nil => simp [negSumZ]
  | cons c p ih => simp only [negSumZ]; linarith [min_le_left (0 : ℤ) c]

theorem negSumZ_le_evZ (p : List ℤ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (negSumZ p : ℝ) ≤ evZ p t := by
  induction p with
  | nil => simp [negSumZ]
  | cons c p ih =>
    simp only [negSumZ, evZ_cons]
    push_cast
    have hn : (negSumZ p : ℝ) ≤ 0 := by exact_mod_cast negSumZ_nonpos p
    have h1 : (negSumZ p : ℝ) ≤ t * evZ p t := by
      have : t * (negSumZ p : ℝ) ≤ t * evZ p t := mul_le_mul_of_nonneg_left ih ht.1
      nlinarith [ht.2]
    have h2 : min 0 (c : ℝ) ≤ c := min_le_right _ _
    linarith

theorem lowBZ_le_evZ (p : List ℤ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (lowBZ p : ℝ) ≤ evZ p t := by
  cases p with
  | nil => simp [lowBZ]
  | cons c p =>
    simp only [lowBZ, evZ_cons]
    push_cast
    have hn : (negSumZ p : ℝ) ≤ 0 := by exact_mod_cast negSumZ_nonpos p
    have h := negSumZ_le_evZ p ht
    have : (negSumZ p : ℝ) ≤ t * evZ p t := by
      have : t * (negSumZ p : ℝ) ≤ t * evZ p t := mul_le_mul_of_nonneg_left h ht.1
      nlinarith [ht.2]
    linarith

def posUnitZ : ℕ → List ℤ → Bool
  | 0, p => decide (0 < lowBZ p)
  | n + 1, p => decide (0 < lowBZ p) ||
      (posUnitZ n (halfZ p) && posUnitZ n (taylorZ 1 (halfZ p)))

theorem posUnitZ_sound : ∀ (n : ℕ) (p : List ℤ), posUnitZ n p = true →
    ∀ t ∈ Icc (0 : ℝ) 1, 0 < evZ p t := by
  intro n
  induction n with
  | zero =>
    intro p h t ht
    simp only [posUnitZ, decide_eq_true_eq] at h
    exact lt_of_lt_of_le (by exact_mod_cast h) (lowBZ_le_evZ p ht)
  | succ n ih =>
    intro p h t ht
    simp only [posUnitZ, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
    rcases h with h | ⟨hl, hr⟩
    · exact lt_of_lt_of_le (by exact_mod_cast h) (lowBZ_le_evZ p ht)
    · have hpow : (0 : ℝ) < 2 ^ p.length := by positivity
      rcases le_total t (1 / 2) with h2 | h2
      · have := ih _ hl (2 * t) ⟨by linarith [ht.1], by linarith⟩
        have e := evZ_halfZ p (2 * t)
        rw [show 2 * t / 2 = t by ring] at e
        nlinarith
      · have := ih _ hr (2 * t - 1) ⟨by linarith, by linarith [ht.2]⟩
        simp only [evZ_taylorZ] at this
        have e := evZ_halfZ p ((1 : ℤ) + (2 * t - 1))
        push_cast at e this
        rw [show (1 + (2 * t - 1)) / 2 = t by ring] at e
        nlinarith

/-- The integer polynomial for the interval `[A/2^s, (A+W)/2^s]`. -/
def dyPoly (p : List ℤ) (A W : ℤ) (s : ℕ) : List ℤ := scaleZ W (taylorZ A (halfZ^[s] p))

theorem evZ_dyPoly (p : List ℤ) (A W : ℤ) (s : ℕ) (t : ℝ) :
    2 ^ s * evZ (dyPoly p A W s) t = (2 ^ p.length) ^ s * evZ p ((A + W * t) / 2 ^ s) := by
  simp only [dyPoly, evZ_scaleZ, evZ_taylorZ]
  exact evZ_halfZ_iter s p _

/-- `p > 0` on `[A/2^s, B/2^s]`. -/
def posOnZ (n : ℕ) (p : List ℤ) (A B : ℤ) (s : ℕ) : Bool :=
  decide (A < B) && posUnitZ n (dyPoly p A (B - A) s)

theorem posOnZ_sound {n : ℕ} {p : List ℤ} {A B : ℤ} {s : ℕ} (h : posOnZ n p A B s = true) :
    ∀ x ∈ Icc ((A : ℝ) / 2 ^ s) ((B : ℝ) / 2 ^ s), 0 < evZ p x := by
  simp only [posOnZ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hAB, hpos⟩ := h
  intro x hx
  have hs : (0 : ℝ) < 2 ^ s := by positivity
  have hBA : (0 : ℝ) < B - A := by exact_mod_cast sub_pos.mpr hAB
  set t := (x * 2 ^ s - A) / (B - A)
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    have h1 : (A : ℝ) ≤ x * 2 ^ s := by
      have := hx.1; rw [div_le_iff₀ hs] at this; linarith
    have h2 : x * 2 ^ s ≤ B := by
      have := hx.2; rw [le_div_iff₀ hs] at this; linarith
    exact ⟨div_nonneg (by linarith) hBA.le, (div_le_one hBA).mpr (by linarith)⟩
  have hpt := posUnitZ_sound n _ hpos t ht
  have e := evZ_dyPoly p A (B - A) s t
  have hx' : ((A : ℝ) + ((B - A : ℤ) : ℝ) * t) / 2 ^ s = x := by
    push_cast
    simp only [t]
    field_simp
    ring
  rw [hx'] at e
  have hP : (0 : ℝ) < (2 ^ p.length) ^ s := by positivity
  nlinarith [mul_pos hs hpt]

/-! ## Root brackets on a dyadic grid -/

/-- `∑ pᵢ mⁱ 2^{s(n-i)}`, which has the sign of `p(m/2^s)` (`n = len p - 1`). -/
def signVal (p : List ℤ) (m : ℤ) (s : ℕ) : ℤ :=
  (p.foldr (fun c (rP : ℤ × ℤ) => (rP.1 * m + c * rP.2, rP.2 * 2 ^ s)) (0, 1)).1

/-- Bisection on the grid `2^{-s}`: returns `lo` with a sign change in `[lo, lo+1]/2^s`. -/
def bisectZ (p : List ℤ) (s : ℕ) : ℕ → ℤ → ℤ → ℤ
  | 0, lo, _ => lo
  | k + 1, lo, hi =>
    let m := (lo + hi) / 2
    if 0 < signVal p m s then bisectZ p s k m hi else bisectZ p s k lo m

/-- The verified conditions of `signPattern_of` on the grid `2^{-j}`. -/
def crossOKZ (n : ℕ) (h : List ℤ) (A B : ℤ) (j : ℕ) : Bool :=
  decide (0 < A) && decide (A < B) && decide (B < 2 ^ j) && posOnZ n h 0 A j &&
    posOnZ n (negZ h) B (2 ^ j) j && posOnZ n (negZ (derivZ h)) A B j

def tryBracketZ (n : ℕ) (h : List ℤ) (lo : ℤ) (s j : ℕ) : Option (ℤ × ℤ × ℕ) :=
  let A := lo / 2 ^ (s - j) - 1
  let B := (lo + 1) / 2 ^ (s - j) + 2
  if crossOKZ n h A B j then some (A, B, j) else none

def bracketWidthsZ : List ℕ := [6, 8, 10, 12, 14, 16, 18, 20, 22, 24]

def findCrossZ (n : ℕ) (h : List ℤ) : Option (ℤ × ℤ × ℕ) :=
  bracketWidthsZ.findSome? (tryBracketZ n h (bisectZ h 28 28 0 (2 ^ 28)) 28)

theorem crossOKZ_sound {n : ℕ} {h : List ℤ} {A B : ℤ} {j : ℕ} (hc : crossOKZ n h A B j = true) :
    ∃ x₀ ∈ Ioo (0 : ℝ) 1, evZ h x₀ = 0 ∧ (∀ x ∈ Ico (0 : ℝ) x₀, 0 < evZ h x) ∧
      (∀ x ∈ Ioc x₀ (1 : ℝ), evZ h x < 0) := by
  simp only [crossOKZ, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hA, hAB⟩, hB⟩, h1⟩, h2⟩, h3⟩ := hc
  have hs : (0 : ℝ) < 2 ^ j := by positivity
  set a : ℝ := (A : ℝ) / 2 ^ j
  set b : ℝ := (B : ℝ) / 2 ^ j
  have ha : 0 < a := div_pos (by exact_mod_cast hA) hs
  have hab : a < b := div_lt_div_of_pos_right (by exact_mod_cast hAB) hs
  have hb : b < 1 := by
    rw [div_lt_one hs]; exact_mod_cast hB
  have p1 := posOnZ_sound h1
  have p2 := posOnZ_sound h2
  have p3 := posOnZ_sound h3
  simp only [Int.cast_zero, zero_div] at p1
  have h2j : ((2 ^ j : ℤ) : ℝ) / 2 ^ j = 1 := by push_cast; field_simp
  rw [h2j] at p2
  -- the continuous function and its derivative
  have hc : Continuous (evZ h) := continuous_evZ h
  have hanti : StrictAntiOn (evZ h) (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b) hc.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_evZ h x).deriv]
    have := p3 x ⟨hx.1.le, hx.2.le⟩
    simp only [evZ_negZ] at this
    linarith
  have hpa : 0 < evZ h a := p1 a ⟨ha.le, le_rfl⟩
  have hnb : evZ h b < 0 := by
    have := p2 b ⟨le_rfl, hb.le⟩; simp only [evZ_negZ] at this; linarith
  obtain ⟨x₀, hx₀, hz⟩ := intermediate_value_Ioo' hab.le hc.continuousOn ⟨hnb, hpa⟩
  refine ⟨x₀, ⟨ha.trans hx₀.1, hx₀.2.trans hb⟩, hz, fun x hx => ?_, fun x hx => ?_⟩
  · rcases le_or_gt x a with hxa | hxa
    · exact p1 x ⟨hx.1, hxa⟩
    · have := hanti ⟨hxa.le, by linarith [hx.2, hx₀.2]⟩ ⟨hx₀.1.le, hx₀.2.le⟩ hx.2
      linarith
  · rcases le_or_gt b x with hxb | hxb
    · have := p2 x ⟨hxb, hx.2⟩; simp only [evZ_negZ] at this; linarith
    · have := hanti ⟨hx₀.1.le, hx₀.2.le⟩ ⟨by linarith [hx.1, hx₀.1], hxb.le⟩ hx.1
      linarith

/-! ## Factorization over `ℤ` -/

def stripAZ : List ℤ → ℕ × List ℤ
  | [] => (0, [])
  | c :: p => if c = 0 then ((stripAZ p).1 + 1, (stripAZ p).2) else (0, c :: p)

def divOneSubZ (p : List ℤ) : List ℤ := ((p.scanl (· + ·) 0).drop 1).dropLast

def stripBZ : ℕ → List ℤ → ℕ × List ℤ
  | 0, h => (0, h)
  | fuel + 1, h =>
    if h ≠ [] ∧ h.sum = 0 then ((stripBZ fuel (divOneSubZ h)).1 + 1, (stripBZ fuel (divOneSubZ h)).2)
    else (0, h)

/-- Integer coefficients as rationals. -/
def ofZ (p : List ℤ) : List ℚ := p.map (Int.cast : ℤ → ℚ)

theorem ev_ofZ (p : List ℤ) (x : ℝ) : ev (ofZ p) x = evZ p x := by
  induction p with
  | nil => simp [ofZ]
  | cons c p ih =>
    simp only [ofZ, List.map_cons, ev_cons, Rat.cast_intCast] at ih ⊢
    rw [ih]; simp

/-- `true` if every coefficient is an integer. -/
def isIntL (p : List ℚ) : Bool := p.all fun c => c.den == 1

theorem ofZ_toZ {p : List ℚ} (h : isIntL p = true) : ofZ (p.map Rat.num) = p := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [isIntL, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [ofZ, List.map_cons, List.map_map] at ih ⊢
    rw [ih h.2]
    congr 1
    exact Rat.coe_int_num_of_den_eq_one h.1

/-! ## The fast SC check -/

def scCheckZ (n : ℕ) (D G : List ℚ) (K : ℚ) : Bool :=
  let Dz := D.map Rat.num
  let a := (stripAZ Dz).1
  let D1 := (stripAZ Dz).2
  let b := (stripBZ 200 D1).1
  let h := (stripBZ 200 D1).2
  isIntL D && decide (trim (factorPoly a b (ofZ h)) = trim D) &&
    ((decide (0 < h.sum) && posOnZ n h 0 1 0) ||
      match findCrossZ n h with
      | some (A, B, j) => crossOKZ n h A B j && decide (0 < intUnit G K)
      | none => false)

theorem scCheckZ_sound {n : ℕ} {D W : List ℚ} {p : ℕ} (hp : 1 ≤ p) {K : ℚ} (hK : 0 < K)
    (hW0 : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ ev W u) (hW : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < ev W u)
    (h : scCheckZ n D (mul W (compPow p D)) K = true) :
    RunPos (fun u => ev W u * ev D (u ^ p)) K := by
  simp only [scCheckZ, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨_, hfac⟩, hsign⟩ := h
  set a := (stripAZ (D.map Rat.num)).1
  set b := (stripBZ 200 (stripAZ (D.map Rat.num)).2).1
  set hh := (stripBZ 200 (stripAZ (D.map Rat.num)).2).2
  have hD : ∀ v : ℝ, ev D v = v ^ a * ((1 - v) ^ b * evZ hh v) := by
    intro v
    rw [← ev_trim D, ← hfac, ev_trim, ev_factorPoly, ev_ofZ]
  have hgc : Continuous fun u : ℝ => ev W u * ev D (u ^ p) :=
    (continuous_ev W).mul ((continuous_ev D).comp (continuous_pow p))
  have hvpos : ∀ v ∈ Ioo (0 : ℝ) 1, 0 < v ^ a * (1 - v) ^ b := fun v hv =>
    mul_pos (pow_pos hv.1 _) (pow_pos (by linarith [hv.2]) _)
  have hupI : ∀ u ∈ Ioo (0 : ℝ) 1, u ^ p ∈ Ioo (0 : ℝ) 1 := fun u hu =>
    ⟨pow_pos hu.1 _, pow_lt_one₀ hu.1.le hu.2 (by omega)⟩
  rcases hsign with ⟨_, hpos⟩ | hcross
  · have hhpos := posOnZ_sound hpos
    simp only [Int.cast_zero, zero_div, Int.cast_one, pow_zero, div_one] at hhpos
    refine runPos_of_pos hgc (fun u hu => ?_) K
    have hv := hupI u hu
    rw [hD]
    have h1 := hhpos (u ^ p) ⟨hv.1.le, hv.2.le⟩
    have h2 := hvpos _ hv
    have h3 := hW u hu
    have : ev W u * ((u ^ p) ^ a * ((1 - u ^ p) ^ b * evZ hh (u ^ p)))
        = ev W u * (((u ^ p) ^ a * (1 - u ^ p) ^ b) * evZ hh (u ^ p)) := by ring
    rw [this]; exact mul_pos h3 (mul_pos h2 h1)
  · cases hfc : findCrossZ n hh with
    | none => rw [hfc] at hcross; simp at hcross
    | some ABj =>
      obtain ⟨A, B, j⟩ := ABj
      rw [hfc] at hcross
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcross
      obtain ⟨hok, hI⟩ := hcross
      obtain ⟨x₀, hx₀, hz, hpos, hneg⟩ := crossOKZ_sound hok
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
        have : ev W u * ((u ^ p) ^ a * ((1 - u ^ p) ^ b * evZ hh (u ^ p)))
            = ev W u * (((u ^ p) ^ a * (1 - u ^ p) ^ b) * evZ hh (u ^ p)) := by ring
        rw [this]; exact mul_pos h3 (mul_pos h2 h1)
      · have hu0 : 0 ≤ u := hx₁0.le.trans hu.1
        have hvx : x₀ ≤ u ^ p := by rw [← hx₁p]; exact pow_le_pow_left₀ hx₁0.le hu.1 p
        have hv1 : u ^ p ≤ 1 := pow_le_one₀ hu0 hu.2
        have hh0 : evZ hh (u ^ p) ≤ 0 := by
          rcases eq_or_lt_of_le hvx with he | hlt
          · rw [← he, hz]
          · exact (hneg _ ⟨hlt, hv1⟩).le
        have hfac0 : 0 ≤ (u ^ p) ^ a * (1 - u ^ p) ^ b :=
          mul_nonneg (pow_nonneg (pow_nonneg hu0 _) _) (pow_nonneg (by linarith) _)
        rw [hD]
        have hW' := hW0 u ⟨hu0, hu.2⟩
        have : (u ^ p) ^ a * ((1 - u ^ p) ^ b * evZ hh (u ^ p)) ≤ 0 := by
          rw [← mul_assoc]; exact mul_nonpos_of_nonneg_of_nonpos hfac0 hh0
        exact mul_nonpos_of_nonneg_of_nonpos hW' this
      · have hcongr : (fun u : ℝ => u ^ ((K : ℝ) - 1) * (ev W u * ev D (u ^ p)))
            = fun u => u ^ ((K : ℝ) - 1) * ev (mul W (compPow p D)) u := by
          funext u; rw [ev_mul, ev_compPow hp]
        show 0 < ∫ u in (0 : ℝ)..1, u ^ ((K : ℝ) - 1) * (ev W u * ev D (u ^ p))
        rw [show (fun u : ℝ => u ^ ((K : ℝ) - 1) * (ev W u * ev D (u ^ p))) = _ from hcongr,
          integral_eq_intUnit _ hK]
        exact_mod_cast hI

/-- The integer sign check without integrand (for the tight case). -/
def signCheckZ (n : ℕ) (D : List ℚ) : Bool :=
  let Dz := D.map Rat.num
  let a := (stripAZ Dz).1
  let D1 := (stripAZ Dz).2
  let b := (stripBZ 200 D1).1
  let h := (stripBZ 200 D1).2
  isIntL D && decide (trim (factorPoly a b (ofZ h)) = trim D) &&
    match findCrossZ n h with
    | some (A, B, j) => crossOKZ n h A B j
    | none => false

theorem signCheckZ_sound {n : ℕ} {D : List ℚ} (h : signCheckZ n D = true) :
    ∃ x₀ ∈ Ioo (0 : ℝ) 1, (∀ u ∈ Ioo 0 x₀, 0 < ev D u) ∧ (∀ u ∈ Icc x₀ 1, ev D u ≤ 0) := by
  simp only [signCheckZ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨_, hfac⟩, hsign⟩ := h
  set a := (stripAZ (D.map Rat.num)).1
  set b := (stripBZ 200 (stripAZ (D.map Rat.num)).2).1
  set hh := (stripBZ 200 (stripAZ (D.map Rat.num)).2).2
  have hD : ∀ v : ℝ, ev D v = v ^ a * ((1 - v) ^ b * evZ hh v) := by
    intro v
    rw [← ev_trim D, ← hfac, ev_trim, ev_factorPoly, ev_ofZ]
  cases hfc : findCrossZ n hh with
  | none => rw [hfc] at hsign; simp at hsign
  | some ABj =>
    obtain ⟨A, B, j⟩ := ABj
    rw [hfc] at hsign
    obtain ⟨x₀, hx₀, hz, hpos, hneg⟩ := crossOKZ_sound hsign
    refine ⟨x₀, hx₀, fun u hu => ?_, fun u hu => ?_⟩
    · rw [hD]
      have h1 := hpos u ⟨hu.1.le, hu.2⟩
      have h2 : 0 < u ^ a * (1 - u) ^ b :=
        mul_pos (pow_pos hu.1 _) (pow_pos (by linarith [hu.2, hx₀.2]) _)
      have : u ^ a * ((1 - u) ^ b * evZ hh u) = (u ^ a * (1 - u) ^ b) * evZ hh u := by ring
      rw [this]; exact mul_pos h2 h1
    · have hu0 : 0 ≤ u := hx₀.1.le.trans hu.1
      have hh0 : evZ hh u ≤ 0 := by
        rcases eq_or_lt_of_le hu.1 with he | hlt
        · rw [← he, hz]
        · exact (hneg u ⟨hlt, hu.2⟩).le
      rw [hD]
      have : 0 ≤ u ^ a * (1 - u) ^ b := mul_nonneg (pow_nonneg hu0 _) (pow_nonneg (by linarith [hu.2]) _)
      have e : u ^ a * ((1 - u) ^ b * evZ hh u) = (u ^ a * (1 - u) ^ b) * evZ hh u := by ring
      rw [e]; exact mul_nonpos_of_nonneg_of_nonpos this hh0

end RntPaper.CP
