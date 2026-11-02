import RntPaper.CertCheck

/-!
# The envelope certificate (V1), executable form

For `g(u) = W(u) (E(u) - T(u))` with `T(u) = ∏_{r ∈ Tl}(1 - u^r)` and an envelope
`E(u) ≥ P_M(u^p) (1 - u^{pB}/(1 - u^p))` on `[0,1)`, `v1Check` verifies, in exact rational
arithmetic, the hypotheses of `runPos_of_V1` with the polynomial
`L(u) = P_M(u^p) (1 - c u^{pB})`, `c = 1/(1 - u₁^p)`:

* near `0` (`u ≤ u₀`): Weierstrass for `L`, Bonferroni for `T`,
  `L - T ≥ u^{r₀} ψ(u)` with `ψ` decreasing and `ψ(u₀) ≥ 0`;
* on `[u₀,u₁]`: a bisection partition, `L(b^p) ≥ T(a)` on each piece (both decreasing);
* the exact integrals `∫₀^{u₁} u^{K-1} W (L - T) > ∫_{u₁}^1 u^{K-1} W T`.
-/

namespace RntPaper.CP

open MeasureTheory intervalIntegral Set RntPaper

/-! ## Product inequalities -/

theorem sum_map_mul_left' (a : ℝ) (l : List ℕ) (f : ℕ → ℝ) :
    (l.map fun e => a * f e).sum = a * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons s l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Weierstrass: `∏ (1 - xᵢ) ≥ 1 - ∑ xᵢ` for `xᵢ ∈ [0,1]`. -/
theorem one_sub_sum_le_prod (xs : List ℝ) (h : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) :
    1 - xs.sum ≤ (xs.map fun x => 1 - x).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons, List.prod_cons]
    have hx := h x (List.mem_cons_self ..)
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hP : 0 ≤ (xs.map fun x => 1 - x).prod :=
      List.prod_nonneg fun z hz => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
        linarith [(h y (List.mem_cons_of_mem _ hy)).2]
    have hS : 0 ≤ xs.sum := List.sum_nonneg fun y hy => (h y (List.mem_cons_of_mem _ hy)).1
    nlinarith [mul_le_mul_of_nonneg_left ih' (by linarith : 0 ≤ 1 - x)]

/-- Pairwise exponents `r + s` (`r` before `s` in the list). -/
def pairExps : List ℕ → List ℕ
  | [] => []
  | r :: l => l.map (r + ·) ++ pairExps l

/-- Bonferroni: `∏ (1 - u^r) ≤ 1 - ∑ u^r + ∑_{r<s} u^{r+s}` on `[0,1]`. -/
theorem prod_le_bonferroni (l : List ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (l.map fun r => 1 - u ^ r).prod
      ≤ 1 - (l.map fun r => u ^ r).sum + ((pairExps l).map fun e => u ^ e).sum := by
  induction l with
  | nil => simp [pairExps]
  | cons r l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pairExps, List.map_append,
      List.sum_append, List.map_map]
    have hx0 : 0 ≤ u ^ r := pow_nonneg hu.1 _
    have hx1 : u ^ r ≤ 1 := pow_le_one₀ hu.1 hu.2
    have hQ : 0 ≤ ((pairExps l).map fun e => u ^ e).sum :=
      List.sum_nonneg fun z hz => by obtain ⟨e, _, rfl⟩ := List.mem_map.mp hz; exact pow_nonneg hu.1 _
    have hcross : ∀ l' : List ℕ, ((l'.map ((fun e => u ^ e) ∘ (r + ·))).sum)
        = u ^ r * (l'.map fun s => u ^ s).sum := by
      intro l'
      induction l' with
      | nil => simp
      | cons s l' ih => simp only [List.map_cons, List.sum_cons, ih, Function.comp_apply, pow_add]; ring
    rw [hcross]
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ 1 - u ^ r), mul_nonneg hx0 hQ]

/-- The product `∏ (1 - x^m)` is antitone on `[0,1]`. -/
theorem prod_one_sub_pow_anti (l : List ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    (l.map fun m => 1 - y ^ m).prod ≤ (l.map fun m => 1 - x ^ m).prod := by
  induction l with
  | nil => simp
  | cons m l ih =>
    simp only [List.map_cons, List.prod_cons]
    have h1 : x ^ m ≤ y ^ m := pow_le_pow_left₀ hx hxy m
    have h2 : y ^ m ≤ 1 := pow_le_one₀ (hx.trans hxy) hy
    have hP : 0 ≤ (l.map fun m => 1 - y ^ m).prod :=
      List.prod_nonneg fun z hz => by
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hz
        linarith [pow_le_one₀ (n := k) (hx.trans hxy) hy]
    exact mul_le_mul (by linarith) ih hP (by linarith)

theorem prod_one_sub_pow_nonneg (l : List ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (l.map fun m => 1 - x ^ m).prod :=
  List.prod_nonneg fun z hz => by
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hz
    linarith [pow_le_one₀ (n := k) hx hx1]

/-! ## Rational evaluations -/

def prodVal (M : List ℕ) (x : ℚ) : ℚ := (M.map fun m => 1 - x ^ m).prod

theorem prodVal_cast (M : List ℕ) (x : ℚ) :
    ((prodVal M x : ℚ) : ℝ) = (M.map fun m => 1 - (x : ℝ) ^ m).prod := by
  induction M with
  | nil => simp [prodVal]
  | cons m M ih =>
    simp only [prodVal, List.map_cons, List.prod_cons] at ih ⊢
    push_cast [ih]; ring

def Lval (M : List ℕ) (c : ℚ) (B : ℕ) (v : ℚ) : ℚ := prodVal M v * (1 - c * v ^ B)

/-- The partition test on `[a,b]`, bisecting `n` times. -/
def partOK (M : List ℕ) (c : ℚ) (B p : ℕ) (Tl : List ℕ) : ℕ → ℚ → ℚ → Bool
  | 0, a, b => decide (prodVal Tl a ≤ Lval M c B (b ^ p))
  | n + 1, a, b => decide (prodVal Tl a ≤ Lval M c B (b ^ p)) ||
      (partOK M c B p Tl n a ((a + b) / 2) && partOK M c B p Tl n ((a + b) / 2) b)

/-- The real lower envelope `L(u) = P_M(u^p)(1 - c u^{pB})`. -/
noncomputable def LR (M : List ℕ) (c : ℝ) (B p : ℕ) (u : ℝ) : ℝ :=
  (M.map fun m => 1 - (u ^ p) ^ m).prod * (1 - c * (u ^ p) ^ B)

noncomputable def TR (Tl : List ℕ) (u : ℝ) : ℝ := (Tl.map fun r => 1 - u ^ r).prod

theorem LR_anti {M : List ℕ} {c : ℝ} (hc : 0 ≤ c) {B p : ℕ} {u1 : ℝ} (hu1 : u1 ≤ 1)
    (hcB : c * (u1 ^ p) ^ B ≤ 1) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ u1) :
    LR M c B p y ≤ LR M c B p x := by
  unfold LR
  have hxp : x ^ p ≤ y ^ p := pow_le_pow_left₀ hx hxy p
  have hy1 : y ^ p ≤ 1 := pow_le_one₀ (hx.trans hxy) (hy.trans hu1)
  have hyu : (y ^ p) ^ B ≤ (u1 ^ p) ^ B :=
    pow_le_pow_left₀ (pow_nonneg (hx.trans hxy) _) (pow_le_pow_left₀ (hx.trans hxy) hy p) B
  have hxyB : (x ^ p) ^ B ≤ (y ^ p) ^ B := pow_le_pow_left₀ (pow_nonneg hx _) hxp B
  have h1 := prod_one_sub_pow_anti M (pow_nonneg hx p) hxp hy1
  have h2 : 0 ≤ 1 - c * (y ^ p) ^ B := by nlinarith [mul_le_mul_of_nonneg_left hyu hc]
  have hP := prod_one_sub_pow_nonneg M (pow_nonneg (hx.trans hxy) p) hy1
  exact mul_le_mul h1 (by nlinarith [mul_le_mul_of_nonneg_left hxyB hc]) h2
    (prod_one_sub_pow_nonneg M (pow_nonneg hx p) (hxp.trans hy1))

theorem TR_anti (Tl : List ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    TR Tl y ≤ TR Tl x := prod_one_sub_pow_anti Tl hx hxy hy

theorem partOK_sound {M : List ℕ} {c : ℚ} (hc : 0 ≤ c) {B p : ℕ} {Tl : List ℕ} {u1 : ℚ}
    (hu1 : u1 ≤ 1) (hcB : c * (u1 ^ p) ^ B ≤ 1) :
    ∀ (n : ℕ) (a b : ℚ), partOK M c B p Tl n a b = true → 0 ≤ a → b ≤ u1 →
      ∀ u ∈ Icc (a : ℝ) b, TR Tl u ≤ LR M c B p u := by
  have hcR : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have hu1R : (u1 : ℝ) ≤ 1 := by exact_mod_cast hu1
  have hcBR : (c : ℝ) * ((u1 : ℝ) ^ p) ^ B ≤ 1 := by exact_mod_cast hcB
  have base : ∀ a b : ℚ, prodVal Tl a ≤ Lval M c B (b ^ p) → 0 ≤ a → b ≤ u1 →
      ∀ u ∈ Icc (a : ℝ) b, TR Tl u ≤ LR M c B p u := by
    intro a b h ha hb u hu
    have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have hbR : (b : ℝ) ≤ u1 := by exact_mod_cast hb
    have hR : ((prodVal Tl a : ℚ) : ℝ) ≤ ((Lval M c B (b ^ p) : ℚ) : ℝ) := by exact_mod_cast h
    rw [prodVal_cast] at hR
    simp only [Lval] at hR
    push_cast [prodVal_cast] at hR
    have h1 : TR Tl u ≤ TR Tl a := TR_anti Tl haR hu.1 (hu.2.trans (hbR.trans hu1R))
    have h2 : LR M c B p b ≤ LR M c B p u :=
      LR_anti hcR hu1R hcBR (haR.trans hu.1) hu.2 hbR
    have h3 : TR Tl a = (Tl.map fun r => 1 - (a : ℝ) ^ r).prod := rfl
    have h4 : LR M c B p b = (M.map fun m => 1 - ((b : ℝ) ^ p) ^ m).prod * (1 - c * ((b : ℝ) ^ p) ^ B) := rfl
    linarith
  intro n
  induction n with
  | zero =>
    intro a b h ha hb
    simp only [partOK, decide_eq_true_eq] at h
    exact base a b h ha hb
  | succ n ih =>
    intro a b h ha hb u hu
    simp only [partOK, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact base a b h ha hb u hu
    · have hab : (a : ℝ) ≤ b := hu.1.trans hu.2
      have habQ : a ≤ b := by exact_mod_cast hab
      rcases le_total u (((a + b) / 2 : ℚ) : ℝ) with hm | hm
      · exact ih a _ h1 ha (by linarith) u ⟨hu.1, hm⟩
      · exact ih _ b h2 (by linarith) hb u ⟨hm, hu.2⟩

/-! ## The check -/

def v1Check (n : ℕ) (W : List ℚ) (M : List ℕ) (B : ℕ) (Tl : List ℕ) (p K : ℕ) (u1 u0 : ℚ) :
    Bool :=
  let c : ℚ := 1 / (1 - u1 ^ p)
  let r0 := Tl.headD 0
  let exps := pairExps Tl ++ M.map (p * ·)
  let Lp := mul (prodOneSub (M.map (p * ·))) (sub [1] (smul c (shiftN (p * B) [1])))
  let Tp := prodOneSub Tl
  decide (0 < u0) && decide (u0 ≤ u1) && decide (u1 < 1) && decide (c * (u1 ^ p) ^ B ≤ 1) &&
    decide (r0 ∈ Tl) && exps.all (fun e => decide (r0 ≤ e)) && decide (r0 < p * B) &&
    decide (0 ≤ 1 - (exps.map fun e => u0 ^ (e - r0)).sum - c * u0 ^ (p * B - r0)) &&
    partOK M c B p Tl n u0 u1 &&
    decide (intTo (mul W Tp) K 1 - intTo (mul W Tp) K u1 < intTo (mul W (sub Lp Tp)) K u1)

theorem ev_Lp (M : List ℕ) (c : ℚ) (B p : ℕ) (u : ℝ) :
    ev (mul (prodOneSub (M.map (p * ·))) (sub [1] (smul c (shiftN (p * B) [1])))) u
      = LR M c B p u := by
  simp only [ev_mul, ev_prodOneSub, ev_sub, ev_smul, ev_shiftN, LR, List.map_map]
  simp only [ev_cons, ev_nil, mul_zero, add_zero, Rat.cast_one, mul_one]
  congr 1
  · congr 1; apply List.map_congr_left; intro m _; simp [pow_mul]
  · rw [pow_mul]

theorem rpow_natSub_eq {u : ℝ} (hu : 0 ≤ u) {K : ℕ} (hK : 1 ≤ K) :
    u ^ ((K : ℝ) - 1) = u ^ (K - 1) := by
  rw [show (K : ℝ) - 1 = ((K - 1 : ℕ) : ℝ) by push_cast [Nat.cast_sub hK]; ring, Real.rpow_natCast]

theorem integral_rpow_eq_intTo (P : List ℚ) {K : ℕ} (hK : 1 ≤ K) {y : ℚ} (hy : 0 ≤ y) :
    ∫ u in (0 : ℝ)..y, u ^ ((K : ℝ) - 1) * ev P u = intTo P K y := by
  rw [← integral_pow_mul_ev P hK y]
  apply intervalIntegral.integral_congr
  intro u hu
  have hyR : (0 : ℝ) ≤ y := by exact_mod_cast hy
  rw [uIcc_of_le hyR] at hu
  simp only [rpow_natSub_eq hu.1 hK]

/-- **Soundness of the V1 check.** -/
theorem v1Check_sound {n : ℕ} {W : List ℚ} {M : List ℕ} {B : ℕ} {Tl : List ℕ} {p K : ℕ}
    {u1 u0 : ℚ} (hp : 1 ≤ p) (hK : 1 ≤ K)
    (hW0 : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ ev W u) (hW : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < ev W u)
    (h : v1Check n W M B Tl p K u1 u0 = true)
    {E : ℝ → ℝ} (hEc : Continuous E) (hE0 : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ E u)
    (hEL : ∀ u ∈ Ico (0 : ℝ) 1,
      (M.map fun m => 1 - (u ^ p) ^ m).prod * (1 - (u ^ p) ^ B / (1 - u ^ p)) ≤ E u) :
    RunPos (fun u => ev W u * (E u - ev (prodOneSub Tl) u)) K := by
  simp only [v1Check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hu0, hu01⟩, hu1⟩, hcB⟩, hr0⟩, hexps⟩, hr0B⟩, hpsi⟩, hpart⟩, hint⟩ := h
  set c : ℚ := 1 / (1 - u1 ^ p) with hcdef
  set r0 := Tl.headD 0
  set exps := pairExps Tl ++ M.map (p * ·)
  have hu1p : u1 ^ p < 1 := pow_lt_one₀ (hu0.le.trans hu01) hu1 (by omega)
  have hc0 : 0 < c := by rw [hcdef]; exact div_pos one_pos (by linarith)
  have hu0R : (0 : ℝ) < u0 := by exact_mod_cast hu0
  have hu01R : (u0 : ℝ) ≤ u1 := by exact_mod_cast hu01
  have hu1R : (u1 : ℝ) < 1 := by exact_mod_cast hu1
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc0
  have hcBR : (c : ℝ) * ((u1 : ℝ) ^ p) ^ B ≤ 1 := by exact_mod_cast hcB
  have hcval : (c : ℝ) = 1 / (1 - (u1 : ℝ) ^ p) := by rw [hcdef]; push_cast; ring
  -- the polynomial `L` and `T`
  set Lp := mul (prodOneSub (M.map (p * ·))) (sub [1] (smul c (shiftN (p * B) [1])))
  set Tp := prodOneSub Tl
  have hLp : ∀ u, ev Lp u = LR M c B p u := ev_Lp M c B p
  have hTp : ∀ u, ev Tp u = TR Tl u := fun u => by simp [Tp, TR]
  -- near zero: `L - T ≥ u^{r₀} ψ(u)`
  set ψ : ℝ → ℝ := fun u => 1 - (exps.map fun e => u ^ (e - r0)).sum - c * u ^ (p * B - r0)
  have hψ0 : 0 ≤ ψ u0 := by
    have h : (0 : ℝ) ≤ ((1 - (exps.map fun e => u0 ^ (e - r0)).sum - c * u0 ^ (p * B - r0) : ℚ) : ℝ) := by
      exact_mod_cast hpsi
    push_cast at h
    simpa [ψ, List.map_map, Function.comp_def] using h
  have hψmono : ∀ u ∈ Ico (0 : ℝ) u0, ψ u0 < ψ u := by
    intro u hu
    simp only [ψ]
    have hs : (exps.map fun e => u ^ (e - r0)).sum ≤ (exps.map fun e => (u0 : ℝ) ^ (e - r0)).sum :=
      List.sum_le_sum fun e _ => pow_le_pow_left₀ hu.1 hu.2.le _
    have hlt : u ^ (p * B - r0) < (u0 : ℝ) ^ (p * B - r0) :=
      pow_lt_pow_left₀ hu.2 hu.1 (by omega)
    nlinarith [mul_lt_mul_of_pos_left hlt hcR]
  have hnear : ∀ u ∈ Icc (0 : ℝ) u0, u ^ r0 * ψ u ≤ LR M c B p u - TR Tl u := by
    intro u hu
    have hu1' : u ≤ 1 := hu.2.trans (hu01R.trans hu1R.le)
    have hup : u ^ p ≤ (u1 : ℝ) ^ p := pow_le_pow_left₀ hu.1 (hu.2.trans hu01R) p
    have hup1 : u ^ p ≤ 1 := pow_le_one₀ hu.1 hu1'
    -- Weierstrass for `L`
    have hW1 : 1 - ((M.map fun m => (u ^ p) ^ m) ++ [(c : ℝ) * (u ^ p) ^ B]).sum
        ≤ (((M.map fun m => (u ^ p) ^ m) ++ [(c : ℝ) * (u ^ p) ^ B]).map fun x => 1 - x).prod := by
      apply one_sub_sum_le_prod
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
        exact ⟨pow_nonneg (pow_nonneg hu.1 _) _, pow_le_one₀ (pow_nonneg hu.1 _) hup1⟩
      · rw [List.mem_singleton] at hx; subst hx
        refine ⟨mul_nonneg hcR.le (pow_nonneg (pow_nonneg hu.1 _) _), ?_⟩
        calc (c : ℝ) * (u ^ p) ^ B ≤ c * ((u1 : ℝ) ^ p) ^ B :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg hu.1 _) hup B) hcR.le
          _ ≤ 1 := hcBR
    have hLeq : (((M.map fun m => (u ^ p) ^ m) ++ [(c : ℝ) * (u ^ p) ^ B]).map fun x => 1 - x).prod
        = LR M c B p u := by
      simp [LR, List.map_append, List.prod_append, List.map_map, Function.comp_def]
    have hLsum : ((M.map fun m => (u ^ p) ^ m) ++ [(c : ℝ) * (u ^ p) ^ B]).sum
        = ((M.map (p * ·)).map fun e => u ^ e).sum + c * u ^ (p * B) := by
      simp [List.sum_append, List.map_map, Function.comp_def, pow_mul]
    -- Bonferroni for `T`
    have hB := prod_le_bonferroni Tl ⟨hu.1, hu1'⟩
    have hTeq : TR Tl u = (Tl.map fun r => 1 - u ^ r).prod := rfl
    -- `∑_r u^r ≥ u^{r₀}`
    have hr0le : u ^ r0 ≤ (Tl.map fun r => u ^ r).sum :=
      List.single_le_sum (fun x hx => by
          obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx; exact pow_nonneg hu.1 _)
        _ (List.mem_map.mpr ⟨r0, hr0, rfl⟩)
    -- factor `u^{r₀}`
    have hfac : u ^ r0 * ψ u = u ^ r0 - (exps.map fun e => u ^ e).sum - c * u ^ (p * B) := by
      simp only [ψ, mul_sub, mul_one]
      rw [← sum_map_mul_left']
      have h1 : (exps.map fun e => u ^ r0 * u ^ (e - r0)) = exps.map fun e => u ^ e := by
        apply List.map_congr_left
        intro e he
        rw [← pow_add]
        congr 1; have := hexps e he; omega
      rw [h1]
      have h2 : u ^ r0 * (c * u ^ (p * B - r0)) = c * u ^ (p * B) := by
        rw [mul_left_comm, ← pow_add]; congr 2; omega
      rw [h2]
    have hexpsum : (exps.map fun e => u ^ e).sum
        = ((pairExps Tl).map fun e => u ^ e).sum + ((M.map (p * ·)).map fun e => u ^ e).sum := by
      simp [exps, List.map_append, List.sum_append]
    rw [hfac, ← hLeq, hTeq]
    linarith
  -- the hypotheses of `runPos_of_V1`
  have hLc : Continuous (ev Lp) := continuous_ev Lp
  have hTc : Continuous (ev Tp) := continuous_ev Tp
  have key := runPos_of_V1 (W := ev W) (E := E) (T := ev Tp) (L := ev Lp) (continuous_ev W) hEc
    hTc hLc hW0 hE0 (fun u hu => by rw [hTp]; exact prod_one_sub_pow_nonneg Tl hu.1 hu.2)
    hu0R hu01R hu1R
    (fun u hu => by
      -- `L ≤ E` on `[0,u₁]`
      have hu1' : u < 1 := hu.2.trans_lt hu1R
      have hup : u ^ p ≤ (u1 : ℝ) ^ p := pow_le_pow_left₀ hu.1 hu.2 p
      have hup1 : u ^ p < 1 := pow_lt_one₀ hu.1 hu1' (by omega)
      have hu1p' : (u1 : ℝ) ^ p < 1 := by exact_mod_cast hu1p
      rw [hLp]
      refine le_trans ?_ (hEL u ⟨hu.1, hu1'⟩)
      unfold LR
      apply mul_le_mul_of_nonneg_left _ (prod_one_sub_pow_nonneg M (pow_nonneg hu.1 _) hup1.le)
      have : (u ^ p) ^ B / (1 - u ^ p) ≤ c * (u ^ p) ^ B := by
        rw [hcval, div_le_iff₀ (by linarith)]
        have hB0 : 0 ≤ (u ^ p) ^ B := pow_nonneg (pow_nonneg hu.1 _) _
        rw [show 1 / (1 - (u1 : ℝ) ^ p) * (u ^ p) ^ B * (1 - u ^ p)
          = (u ^ p) ^ B * ((1 - u ^ p) / (1 - (u1 : ℝ) ^ p)) by field_simp]
        have : 1 ≤ (1 - u ^ p) / (1 - (u1 : ℝ) ^ p) := by
          rw [le_div_iff₀ (by linarith)]; linarith
        nlinarith
      linarith)
    (fun u hu => by
      have hu1' : u ≤ 1 := hu.2.trans hu1R.le
      apply mul_nonneg (hW0 u ⟨hu.1, hu1'⟩)
      rw [hLp, hTp]
      rcases le_total u u0 with h0 | h0
      · have := hnear u ⟨hu.1, h0⟩
        have : 0 ≤ ψ u := by
          rcases eq_or_lt_of_le h0 with he | hl
          · rw [he]; exact hψ0
          · exact (hψ0.trans_lt (hψmono u ⟨hu.1, hl⟩)).le
        nlinarith [pow_nonneg hu.1 r0, mul_nonneg (pow_nonneg hu.1 r0) this]
      · have := partOK_sound hc0.le hu1.le hcB n u0 u1 hpart hu0.le le_rfl u ⟨h0, hu.2⟩
        linarith)
    (fun u hu => by
      apply mul_pos (hW u ⟨hu.1, hu.2.trans (hu01R.trans_lt hu1R)⟩)
      rw [hLp, hTp]
      have := hnear u ⟨hu.1.le, hu.2.le⟩
      have hψp : 0 < ψ u := hψ0.trans_lt (hψmono u ⟨hu.1.le, hu.2⟩)
      nlinarith [mul_pos (pow_pos hu.1 r0) hψp])
    (K := (K : ℝ)) (by
      -- the exact integrals
      have hI1 : (∫ u in (0 : ℝ)..(u1 : ℝ), u ^ ((K : ℝ) - 1) * (ev W u * (ev Lp u - ev Tp u)))
          = intTo (mul W (sub Lp Tp)) K u1 := by
        rw [← integral_rpow_eq_intTo _ hK (hu0.le.trans hu01)]
        apply intervalIntegral.integral_congr; intro u _; simp
      have hI2 : (∫ u in (u1 : ℝ)..1, u ^ ((K : ℝ) - 1) * (ev W u * ev Tp u))
          = intTo (mul W Tp) K 1 - intTo (mul W Tp) K u1 := by
        have hcont : Continuous fun u : ℝ => u ^ ((K : ℝ) - 1) * ev (mul W Tp) u :=
          continuous_rpow_mul (continuous_ev _) (by exact_mod_cast hK)
        have := intervalIntegral.integral_interval_sub_left (μ := volume)
          (hcont.intervalIntegrable 0 1) (hcont.intervalIntegrable 0 (u1 : ℝ))
        have e1 := integral_rpow_eq_intTo (mul W Tp) hK (y := 1) zero_le_one
        have e2 := integral_rpow_eq_intTo (mul W Tp) hK (hu0.le.trans hu01)
        push_cast at e1 e2 ⊢
        rw [show (fun u : ℝ => u ^ ((K : ℝ) - 1) * (ev W u * ev Tp u))
          = fun u => u ^ ((K : ℝ) - 1) * ev (mul W Tp) u by funext u; simp, ← this, e1, e2]
      rw [hI1, hI2]
      exact_mod_cast hint)
  convert key using 2

end RntPaper.CP
