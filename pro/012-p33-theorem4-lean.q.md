# Lean 4: Theorem 4 aggregation (n^{1/4} gap over an arbitrary background semimeasure)

Attached: `P33Theorem3.lean`, which compiles (Lean v4.35.0, Mathlib v4.35.0; check PASS, standard axioms only)
and proves `RobustExperiment.theorem3`: your Theorem 3 from answer 008 (finite experiment robust to any
semimeasure background A with root 1, every η ≤ 2^-20, ties to `true`).

Now formalize the measure-theoretic core of your Theorem 4 (008, §3.1-3.3), with no computability yet:

> For j ≥ 0: z_j = 1^j 0, p_j = 2^{-j-1}, N_j = 16^j, γ_j = 1/(32·4^j). The source μ: fair bits until the
> first 0; if it follows j ones, N_j bits with P(1) = 1/2 + γ_j; then fair bits forever.
> For EVERY semimeasure M on binary strings with M(x) > 0 for all x (and M(ε) ≤ 1), define
> P(1^k) = Q(1^k) = M(1^k), P(z_j h) = M(z_j) μ_j(h), Q(z_j h) = M(z_j) ν_j(h),
> ξ₋ = (1−η)(¼P + ¾Q) + ηM, ξ₊ = (1−η)(¾P + ¼Q) + ηM, η = 2^-20.
> Then for every n ≥ 2: n^{1/4}/256 ≤ L_n^{ξ₋} − L_n^{ξ₊} ≤ n^{1/4}/8 under μ (0-1 loss, action true iff
> s(h1) ≥ s(h0)).

Requirements:
- Reuse the attached file's `History`, `Model`, `prob`, `predict`, `stepLoss`, `loss` (import it as
  `HutterPrizes.P33Theorem3`, namespace `RobustExperiment`) and call `theorem3` for each branch rather than
  re-proving it. You may add helper lemmas about `theorem3`'s internals only if you restate them; do not edit
  the attached file. If something in it must change, say exactly what and why.
- Part 1 (statement layer): μ as a `Model`, a semimeasure M on all depths (nonneg, positive, children sum ≤
  parent, root ≤ 1), P, Q, ξ±, and the main theorem with the n^{1/4} bounds (state n^{1/4} as `(n:ℝ)^(1/4:ℝ)`
  or in an equivalent integer form, and say which). Also prove P and Q are semimeasures and that ξ± ≥ η·M
  (the dominance used for universality).
- Part 2: proofs. No `sorry`, `admit`, new axioms or `native_decide`.

Return one Lean code block (the new file only), then a map from Part 1 to the text above, then any deviations.
