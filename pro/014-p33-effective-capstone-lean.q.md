# Lean 4: the effective capstone for Problem 3.3 (two universal lower-semicomputable semimeasures)

Environment: Lean v4.35.0, Mathlib v4.35.0, and https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean
at commit 17c50e560c337a8a702f8850a711f80a56b3cf91 (namespace `Kolmogorov`; `BitString = List Bool`).

Attached and compiling (standard axioms only):
- `P33Theorem3.lean` (`RobustExperiment.theorem3`) and `P33Theorem4.lean` (`RobustExperiment.Theorem4`):
  for EVERY strictly positive real semimeasure `M : Background` on `History`, with
  `ξ± = (1−η)(¾P+¼Q / ¼P+¾Q) + ηM`, η = 2^-20, the source `source`, and every n ≥ 2:
  n^{1/4}/256 ≤ loss source (xiMinus M) n − loss source (xiPlus M) n ≤ n^{1/4}/8;
  plus `xi_semimeasure` and `xi_dominates` (ξ± ≥ η·M).

Upstream definitions to use (in the library):
- `IsContinuousTreeSemimeasure a := a [] = 1 ∧ ∀ x, a (x ++ [false]) + a (x ++ [true]) ≤ a x`
  (`MonotoneComplexity/TreeSemimeasure.lean`), `IsLowerSemicomputableContinuousSemimeasure a :=
  IsContinuousTreeSemimeasure a ∧ IsLSC (fun x _ => a x)`, with `IsLSC` in
  `AlgorithmicProbability/KraftChaitinCore/LSCApproximation.lean` (monotone computable dyadic approximations).
- `universalContinuousSemimeasure` with `..._isLowerSemicomputableContinuousSemimeasure`,
  `universalContinuousSemimeasure_isMaximal`, `universalContinuousSemimeasure_pos`
  (`MonotoneComplexity/APrioriComplexity.lean`). Closure lemmas exist, e.g. `IsLSC.div_two_pow`,
  `IsLSC.comp_left`, `isLSC_ofReal_of_computable`, `isLSC_tsum_of_uniform`; check what else is there.

Goal: one new file `P33Effective.lean` that imports both attached files and the library, and proves:

> **Theorem (effective counterexample to "L^ξ − L^ξ' < ∞").** There exist ξ₋, ξ₊ : BitString → ℝ≥0∞ such that
> (1) both satisfy `IsLowerSemicomputableContinuousSemimeasure`;
> (2) both are universal: for every `a'` with `IsLowerSemicomputableContinuousSemimeasure a'` there is a
>     finite `c` with `a' x ≤ c * ξ± x` for all x;
> (3) the source μ (= `RobustExperiment.Theorem4.source`) is a computable measure: its conditional is
>     `fun n h => (r (toBitString h) : ℝ)` for a `Computable r : BitString → ℚ`, and it sums to 1 at each depth;
> (4) for every n ≥ 2, n^{1/4}/256 ≤ loss source ξ₋' n − loss source ξ₊' n, where ξ±' is ξ± transported to
>     `History` (as real numbers), and the action rule is the one in `P33Theorem3.lean`.

Suggested route: M := universalContinuousSemimeasure (root 1, positive, ≤ 1, so `toReal` is safe); build a
`Background` from it; define ξ± on BitString directly (trunk/branch split by the first `false`), prove they
agree with `Theorem4.xi` under the History ↔ BitString bijection, and prove IsLSC by closure: all coefficients
are dyadic (η = 2^-20, ¼, ¾, γ_j = 2^{-5-2j}, branch probabilities are dyadic and computable from x), and
P(x), Q(x) equal M at a computably determined string times a computable dyadic rational. Universality: ξ± ≥ η·M
and M is maximal.

Requirements: Part 1 (statement layer, short) and Part 2 (proofs); no `sorry`, `admit`, new axioms or
`native_decide`; do not edit the attached files (if one must change, say exactly why). Return one Lean code
block for the new file, then a map from Part 1 to the theorem above, then deviations.
