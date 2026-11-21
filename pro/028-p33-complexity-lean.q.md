# Lean 4: prove the frozen target `Targets/P33Complexity.lean` (Problem 3.3 with 2^-K(i) weights)

Environment: Lean v4.35.0, Mathlib v4.35.0, kolmogorov-complexity-lean
(https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean, commit 17c50e560c337a8a702f8850a711f80a56b3cf91).
No `sorry`, `admit`, new axioms or `native_decide`.

Goal: a complete Lean proof of `P33Complexity.complexity_counterexample` in the attached target, with its
statement layer unchanged character for character (we diff it). It formalizes Corollary 5 of your report 008
(§4.2: base prior a_i = 2^{-K(i)}, two extra masses at the indices of P and Q). A fresh review found the target
faithful; notes at the end of the target file.

Already compiled (attached; import, do not re-prove): `HutterPrizes/P33Mixture.lean` (`mixture_counterexample`:
the same result with weights summing to 1; reuse its structure — the index of P, Q in `treeLSCEnum`, the
mixture identity, the transfer of `theorem4`), plus `P33Theorem4.lean` (`theorem4` for every `Background`) and
`P33Effective.lean` (`transport`, `toBitString`, the source's computability).

Hints from the reviewer: the background M = Σ_i 2^{-K(i)} ν_i satisfies `Background` (Kraft:
`tsum_complexityWeight_KPNat_le_one`; positivity: `KPNat_ne_top` and `lengthMeasure` in the enumeration). P and
Q built from this M have root M(ε) < 1, so `treeLSCEnum_complete` (root 1) needs P′ = (if x = [] then 1 else
P x); the child inequality at the root holds since M(0) + M(1) ≤ M(ε) ≤ 1. The mixture identity then holds for
x ≠ [], and you need a lemma that `loss`/`transport` read only levels ≥ 1. Weights 2^{-K(i)} are
`complexityWeight (KPNat U i)`; lower semicomputability: `isUniformlyLSC_complexityWeight_KPNat`.

Return one Lean code block for a new file `HutterPrizes/P33Complexity.lean` (namespace `P33Complexity`; helper
files are fine if you return each in full), then deviations. If the target is false, say so and prove the negation.
