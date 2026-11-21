# Lean 4: prove the frozen target `Targets/P27Selection.lean` (Problem 2.7, report 023 §3)

Environment: Lean v4.35.0, Mathlib v4.35.0, kolmogorov-complexity-lean
(https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean, commit 17c50e560c337a8a702f8850a711f80a56b3cf91).
No `sorry`, `admit`, new axioms or `native_decide`.

Goal: complete Lean proofs of `P27Selection.selection_lower_bound` and `P27Selection.log_window_lower_bound` in
the attached target, with its statement layer unchanged character for character (we diff it). They formalize
Theorem 1 and Corollary 2 of your report `023-p27-eventual.a.md` §3, for µ with computable rational conditionals.
A fresh review found the target faithful; its notes are at the end of the target file. A referee found the
report's proofs correct.

Already proved and compiled (attached; import them, do not re-prove):
- `HutterPrizes/P27Stochastic.lean`: Theorem 1 of the earlier report for dyadic blocks, with the bridge from
  `muProb`/`normalizedSiblingProb` to `P27.Model`, the Step-1 environment family, its uniform domination via
  `exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree`, and the dyadic coding bound. Reuse as much
  as possible.
- `HutterPrizes/P27SelectiveForcing.lean`: `P27.selective_forcing` = Lemma 1 of 023 (no full support needed).
- `HutterPrizes/P27BlockBound.lean`: `P27.Model`, `A`, `hybrid_inequality`.

Notes: eq. (24) needs a coding bound Σ_{t∈F_n} 2^{-K(t)} ≤ C·2^{-K(n)} for blocks along a general computable d
(the dyadic lemma in P27Stochastic does not cover it; the lower-semicomputable g route, SUV Theorem 62
`KPPlain_le_of_tsum_two_pow_neg_ne_top`, does). With rational µ you may force a bit with µ-probability ≤ 1/2, so
the forced mass is ≤ 2^{-ℓ_n} ≤ (n+2)^{-6}; K(n) ≤ 2 log₂(n+1) + O(1) (`KPPlain_le_two_mul_length`) gives
w_n ≳ (n+2)^{-2}.

Return one Lean code block for a new file `HutterPrizes/P27Selection.lean` (namespace `P27Selection`; extra
helper files are fine if you return each in full), then a list of deviations. If the target is false as stated,
say so and prove the negation.
