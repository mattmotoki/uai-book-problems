# Lean 4 formalization: Theorem 3 of your answer 008 (finite experiment robust to any semimeasure background)

Formalize and prove, in Lean 4 (`v4.35.0`, Mathlib `v4.35.0`; plain Mathlib, no other library), this
statement from your earlier answer:

> Let N ≥ 1 be a square, γ = 1/(32√N). μ_N, ν_N generate independent bits with P(1) = 1/2 + γ and
> 1/2 − γ during the first N positions (fair afterwards). π₋ = ¼μ_N + ¾ν_N, π₊ = ¾μ_N + ¼ν_N.
> For every semimeasure A with A(ε) = 1 and every 0 ≤ η ≤ 2^-20, put s± = (1−η)π± + ηA. Then under μ_N,
> √N/32 ≤ L_N^{s₋} − L_N^{s₊} ≤ √N/16, and every per-step expected loss difference is nonnegative.
> The Bayes 0-1 action of a positive semimeasure s at history h is 1 iff s(h1) ≥ s(h0).

No `sorry`, `admit`, new axioms, or `native_decide`.

Requirements:
- **Part 1 (statement layer)**: short, readable definitions and the main theorem, so a reviewer can
  compare them with the text above. Reuse the style of the attached file `P33Counterexample.lean`
  (Lean-checked earlier: `History n` as nested pairs, `Model` with conditionals, `prob`, Bayes 0-1
  prediction, `loss` under the true model). Add: a semimeasure on histories up to length N
  (nonnegative, root 1, children sum ≤ parent), mixtures of semimeasures, the action rule
  s(h1) ≥ s(h0), and expected cumulative loss under μ_N over steps 1..N.
  Quantify over every semimeasure A and every η in [0, 2^-20]; N = k² with k ≥ 1.
- **Part 2**: the proofs.
- If the theorem as stated is false or needs a change (constants, the range of η, ties), say so
  precisely, prove the corrected version, and explain the change.

Return the whole file in one Lean code block, then a map from Part 1 to the text above, then any
deviations.
