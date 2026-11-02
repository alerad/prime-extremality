# Independent audit of the Lean formalization (2026-11-02)

Saved in substance from the reviewer's final report (the harness blocked the reviewer from writing files).

**Verdict: correct.** The final Lean statements match notes Thm 3.2, Cor 3.3, Thm 3.7 and Thm 3.8 (finite and
arbitrary sets, all c ∈ (0,1], strictness clauses, k ranges). No statement is vacuous; `k9` is the unique
positive root of E Z^k_{A9} = E Z^k_{P9} (`k9_unique_root`), `alpha0` is the right constant
(`Jw_one_nonneg_iff`, `Jw alpha0 1 = 0`). In the k₉ proof every Boolean check is used only through a proven
soundness theorem (`scCheckZ_sound`, `v1Check_sound`, `signCheckZ_sound`, enumeration completeness
`antichains_complete` + `exists_maximal_ext'`); `K9Data` tables and root brackets are untrusted inputs.
All cases of the descent are covered (explicit merged incl. A₉ subsets, merged tails, single blocks and
tails, p ≥ 61, N ≤ 6, k < 1, infinite sets without Dickson). Enumeration counts re-run: 3113 / 928 / 243 /
1031, matching the notes.

**Axioms.** Thm 3.2, Cor 3.3, Thm 3.7: `propext, Classical.choice, Quot.sound` only. Thm 3.8
(`moment_primesLE_k9`, `moment_primes_k9`, `k9_threshold`): standard + 121 auto-generated
`…._native.native_decide.ax_*` axioms (118 from `K9Cert`, 3 from `K9Tight`). No `sorry`, no user axiom, no
`implemented_by`/`extern`/`unsafe`/`csimp`.

**Low-severity issues.**
- L1 packaging: new modules are not imported by `lean/RntPaper.lean` and not covered by the CI axiom audit
  (`scripts/AxiomCheck.lean` allow-list of native_decide results).
- L2 notes text: notes mention Lean only for Thm 3.5; Lean certifies all 1031 merged tails (incl. the 12
  "vacuous" ones); small N enumerates 40 lists (incl. ∅ and 𝒫_N) vs "35 primitive sets" in the notes.
- L3 not formalized (not part of any theorem statement): the equality case at k = k₉; the remark on proper
  subsets of A₉; the decimal value of α₀ (only 17/8 < α₀ < 3); Lemma 3.9 only in strict form (non-strict
  inline in `merged_step`).
