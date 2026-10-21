import Lean

/-!
# Axiom audit

Run by `scripts/check-axioms.sh`, which prepends `import` lines for every module under
`RntPaper/`. It fails if

* any declaration of the development depends on `sorryAx`,
* the development declares an axiom of its own (the trust axioms Lean generates for
  `native_decide`, named `<decl>._native.native_decide.ax_*`, are reported, not refused), or
* a paper result (the table in `README.md`) uses an axiom beyond `propext`,
  `Classical.choice`, `Quot.sound`. The two `native_decide` computations of the paper are
  the exception: they may additionally use their own generated `native_decide` axioms
  (or, on older Lean, `Lean.ofReduceBool` / `Lean.trustCompiler`).
-/

open Lean Elab Command

namespace RntPaper.AxiomCheck

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Axioms that record trust in compiled code (`native_decide`). -/
def isNativeAxiom (n : Name) : Bool :=
  n == `Lean.ofReduceBool || n == `Lean.trustCompiler ||
    (n.components.contains `_native && n.components.contains `native_decide)

/-- The digits of Λ and the `k = 126` comparison (paper §6). -/
def nativeDecideResults : List Name :=
  [`RntPaper.primeLambda_digits26, `RntPaper.A9_beats_primes_at_126]

/-- Paper results → Lean declarations, as listed in `README.md`. -/
def paperResults : List Name := [
  `RntPaper.Fc_primesLE_lt, `RntPaper.Lfun_le_FcSet, `RntPaper.Lfun_lt_FcSet,
  `RntPaper.pointwise_failure, `RntPaper.running_pos_set, `RntPaper.single_crossing,
  `RntPaper.endpoint_estimate, `RntPaper.block_exchange_lt_set, `RntPaper.Fc_minLE_lt,
  `RntPaper.FcSet_minElems_lt, `RntPaper.icv_minimality, `RntPaper.moment_primesLE_lt,
  `RntPaper.moment_primes_lt, `RntPaper.moment_primes_lt_of_Jw,
  `RntPaper.Qfun_single_crossing, `RntPaper.Jw_pos_of, `RntPaper.moment_cert,
  `RntPaper.Jw_three_neg, `RntPaper.primeLambda_digits26,
  `RntPaper.primeLogExpSum_asymp, `RntPaper.primeExpSum_asymp, `RntPaper.primePhi_asymp,
  `RntPaper.tail_le_of_primePhi, `RntPaper.tail_ge_of_window,
  `RntPaper.tail_asymptotic_pnt, `RntPaper.tail_asymptotic_nth_pnt,
  `RntPaper.FcSet_omitSet_lt, `RntPaper.FcSet_omitSet_eq,
  `RntPaper.omitCost_le_FcSet_sub, `RntPaper.eq_primes_of_lt, `RntPaper.tendsto_FcSet_iff,
  `RntPaper.saddleMin_le_neg_log_omitMoment, `RntPaper.neg_log_omitMoment_le_saddleMin,
  `RntPaper.omitMoment_asymptotic_pnt, `RntPaper.tail_second_order_pnt,
  `RntPaper.saddle_second_order, `RntPaper.A9_beats_primes_at_126]

elab "#rnt_axiom_check" : command => do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let mut total := 0
  let mut withSorry : Array Name := #[]
  let mut ownAxioms : Array Name := #[]
  let mut nativeAxs : Array Name := #[]
  for (n, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless (`RntPaper).isPrefixOf modules[idx.toNat]! do continue
    total := total + 1
    if info matches .axiomInfo _ then
      if isNativeAxiom n then nativeAxs := nativeAxs.push n else ownAxioms := ownAxioms.push n
    if (← collectAxioms n).contains ``sorryAx then withSorry := withSorry.push n
  let mut failed := false
  if total == 0 then
    logError "no RntPaper declarations found"; failed := true
  unless withSorry.isEmpty do
    logError m!"declarations depending on sorryAx: {withSorry.qsort Name.lt}"; failed := true
  unless ownAxioms.isEmpty do
    logError m!"axioms declared by the development: {ownAxioms.qsort Name.lt}"; failed := true
  for n in paperResults do
    unless env.contains n do
      logError m!"paper result {n} not found"; failed := true; continue
    let axs ← collectAxioms n
    let native := nativeDecideResults.contains n
    let extra := axs.filter fun a => !(standardAxioms.contains a || (native && isNativeAxiom a))
    if extra.isEmpty then
      logInfo m!"ok  {n}: {axs}"
    else
      logError m!"{n} uses unexpected axioms {extra}"; failed := true
  logInfo m!"native_decide trust axioms (compiled computations): {nativeAxs.qsort Name.lt}"
  if failed then throwError "axiom audit failed"
  logInfo m!"axiom audit passed: {total} declarations, none uses sorryAx; \
    {paperResults.length} paper results checked"

end RntPaper.AxiomCheck

#rnt_axiom_check
