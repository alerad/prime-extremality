import RntPaper.K9Data
import RntPaper.CertFast

/-!
# The finitely many cases of the `k₉` certificate (executable)

* `antichains xs []`: all divisibility antichains of an increasing list `xs`.
* `checkMergedExplicit`: every maximal antichain `S` of 7-smooth numbers in `[2,63]` (maximal
  below `max S`) covering `2,3,5,7`, other than `{2,3,5,7}` and `A₉`, passes the SC test for
  `∏_{11 ≤ q ≤ max S}(1-u^q)(P_S - P_{2,3,5,7})` at `K = 126`.
* `checkSingleExplicit p m`: every maximal antichain `T` of `p`-smooth numbers in `[2,m)` passes
  the SC test for `∏_{q ∈ Q}(1-u^q) (P_T(u^p) - (1-u^p))`, `Q` the primes in `(p, min(p max T, cap)]`.
* `checkSingleTail p m B`: every maximal antichain `M` of `p`-smooth numbers in `[2,B)` passes V1.
* `checkMergedTail R'`: every antichain `A₀` of composites of `⟨R'⟩` in `[4,24)` passes V1.
* `checkSmall N`: every primitive `A ⊆ [2,N]`, `N ≤ 6`, passes SC against `𝒫_N`.
-/

namespace RntPaper.K9

open CP

/-- All prime factors are `≤ p`. -/
def smoothB (p n : ℕ) : Bool := n.primeFactorsList.all (· ≤ p)

/-- All prime factors lie in `ps`. -/
def smoothIn (ps : List ℕ) (n : ℕ) : Bool := n.primeFactorsList.all (· ∈ ps)

/-- `p`-smooth numbers in `[lo, hi)`. -/
def Xs (p lo hi : ℕ) : List ℕ := (List.range hi).filter fun n => decide (lo ≤ n) && smoothB p n

/-- Composites of `⟨R'⟩` in `[lo, hi)` (`lo ≥ 2`). -/
def compositesR (Rp : List ℕ) (lo hi : ℕ) : List ℕ :=
  (List.range hi).filter fun n => decide (lo ≤ n) && smoothIn Rp n && !(Rp.contains n)

/-- All divisibility antichains of the increasing list `xs` extending `ch` (reversed). -/
def antichains : List ℕ → List ℕ → List (List ℕ)
  | [], ch => [ch.reverse]
  | x :: xs, ch =>
    (if ch.all (fun a => x % a != 0) then antichains xs (x :: ch) else []) ++ antichains xs ch

def lmax (l : List ℕ) : ℕ := l.foldr max 0

/-- `l` is maximal among antichains of `X ∩ [2, max l]`. -/
def isMaxBelow (X l : List ℕ) : Bool :=
  X.all fun x => decide (lmax l < x) || l.contains x || l.any fun s => x % s == 0 || s % x == 0

/-- `l` is maximal among antichains of `X`. -/
def isMaxIn (X l : List ℕ) : Bool :=
  X.all fun x => l.contains x || l.any fun s => x % s == 0 || s % x == 0

/-- Primes in `[lo, hi]`. -/
def primesIn (lo hi : ℕ) : List ℕ := (List.range (hi + 1)).filter fun q => decide (lo ≤ q) && Nat.Prime q

def R4 : List ℕ := [2, 3, 5, 7]
def A9 : List ℕ := [4, 5, 6, 7, 9]

def fuel : ℕ := 40
def Kc : ℚ := 126

def covers (l : List ℕ) : Bool := R4.all fun r => l.any fun s => s % r == 0

/-! ## Merged explicit -/

def mergedD (l : List ℕ) : List ℚ := sub (prodOneSub l) (prodOneSub R4)
def mergedW (l : List ℕ) : List ℚ := prodOneSub (primesIn 11 (lmax l))

def mergedCert (l : List ℕ) : Bool :=
  scCheckZ fuel (mergedD l) (mul (mergedW l) (compPow 1 (mergedD l))) Kc

def X7 : List ℕ := Xs 7 2 64

def mergedOK (l : List ℕ) : Bool :=
  !(decide (l ≠ []) && isMaxBelow X7 l && covers l) || l == R4 || l == A9 || mergedCert l

def checkMergedExplicit : Bool := (antichains X7 []).all mergedOK

/-! ## Single explicit -/

def singleD (T : List ℕ) : List ℚ := sub (prodOneSub T) [1, -1]
def singleW (p : ℕ) (T : List ℕ) (cap : ℕ) : List ℚ := prodOneSub (primesIn (p + 1) (min (p * lmax T) cap))

def singleCertCap (p : ℕ) (T : List ℕ) (cap : ℕ) : Bool :=
  scCheckZ fuel (singleD T) (mul (singleW p T cap) (compPow p (singleD T))) Kc

def capList (p : ℕ) (T : List ℕ) : List ℕ := [3 * p, 6 * p, 12 * p, p * lmax T]

def singleOK (p m : ℕ) (l : List ℕ) : Bool :=
  !(decide (l ≠ []) && isMaxBelow (Xs p 2 m) l) || (capList p l).any (singleCertCap p l)

def checkSingleExplicit (p m : ℕ) : Bool := (antichains (Xs p 2 m) []).all (singleOK p m)

/-! ## Single tails -/

def singleTailCert (p m B : ℕ) (M : List ℕ) (cap : ℕ) (u1 u0 : ℚ) : Bool :=
  v1Check 18 (prodOneSub (primesIn (p + 1) (min (p * m) cap))) M B [p] p 126 u1 u0

def singleTailOK (p m B : ℕ) (l : List ℕ) : Bool :=
  !(isMaxIn (Xs p 2 B) l) ||
    match singleTailTbl.lookup (p, l) with
    | some (cap, u1, u0) => singleTailCert p m B l cap u1 u0
    | none => false

def checkSingleTail (p m B : ℕ) : Bool := (antichains (Xs p 2 B) []).all (singleTailOK p m B)

/-! ## Merged tails -/

def R0of (Rp : List ℕ) : List ℕ := R4.filter fun r => !(Rp.contains r)

def tailCl (Rp A0 : List ℕ) : List ℕ :=
  (compositesR Rp 24 120).filter fun n => !(A0.any fun a => n % a == 0)

def mergedTailCert (Rp A0 : List ℕ) (u1 u0 : ℚ) : Bool :=
  v1Check 18 (prodOneSub (primesIn 11 64 ++ R0of Rp)) (A0 ++ tailCl Rp A0) 120 Rp 1 126 u1 u0

def mergedTailOK (Rp A0 : List ℕ) : Bool :=
  match mergedTailTbl.lookup (Rp, A0) with
  | some (u1, u0) => mergedTailCert Rp A0 u1 u0
  | none => false

def checkMergedTail (Rp : List ℕ) : Bool := (antichains (compositesR Rp 4 24) []).all (mergedTailOK Rp)

/-! ## Small `N` -/

def smallD (N : ℕ) (A : List ℕ) : List ℚ := sub (prodOneSub A) (prodOneSub (primesIn 2 N))

def smallOK (N : ℕ) (A : List ℕ) : Bool :=
  A == primesIn 2 N || scCheckZ fuel (smallD N A) (mul [1] (compPow 1 (smallD N A))) Kc

def checkSmall (N : ℕ) : Bool := (antichains (List.range' 2 (N - 1)) []).all (smallOK N)

/-- The single-step parameters `(p, m_p, B_p)`. -/
def singleParams : List (ℕ × ℕ × ℕ) :=
  [(11, 30, 24), (13, 24, 20), (17, 20, 16), (19, 16, 14), (23, 14, 12), (29, 12, 10),
   (31, 10, 9), (37, 9, 8), (41, 8, 7), (43, 8, 7), (47, 6, 6), (53, 6, 6), (59, 5, 5)]

/-- The nonempty subsets `R'` of `{2,3,5,7}` (increasing). -/
def RpList : List (List ℕ) :=
  [[2], [3], [5], [7], [2, 3], [2, 5], [2, 7], [3, 5], [3, 7], [5, 7], [2, 3, 5], [2, 3, 7],
   [2, 5, 7], [3, 5, 7], [2, 3, 5, 7]]

end RntPaper.K9

namespace RntPaper.K9

/-! ## Partitioned checks (for parallel compilation): the part `j` of `q` keeps the lists
whose element sum is `≡ j (mod q)`. -/

def checkMergedPart (q j : ℕ) : Bool :=
  (antichains X7 []).all fun l => l.sum % q != j || mergedOK l

def checkSinglePart (p m q j : ℕ) : Bool :=
  (antichains (Xs p 2 m) []).all fun l => l.sum % q != j || singleOK p m l

def checkSingleTailPart (p m B q j : ℕ) : Bool :=
  (antichains (Xs p 2 B) []).all fun l => l.sum % q != j || singleTailOK p m B l

def checkMergedTailPart (Rp : List ℕ) (q j : ℕ) : Bool :=
  (antichains (compositesR Rp 4 24) []).all fun l => l.sum % q != j || mergedTailOK Rp l

end RntPaper.K9
