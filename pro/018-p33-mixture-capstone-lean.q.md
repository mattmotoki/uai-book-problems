# Lean 4: upgrade the effective 3.3 capstone from "universal" to "two Bayes mixtures over M_U"

Environment: Lean v4.35.0, Mathlib v4.35.0, https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean at
commit 17c50e560c337a8a702f8850a711f80a56b3cf91.

Attached and compiling (standard axioms only): `P33Theorem3.lean`, `P33Theorem4.lean`, `P33Effective.lean`
(your earlier capstone: `effective_counterexample` with background M = `universalContinuousSemimeasure`).

A fidelity review found: Hutter's Problem 3.3 is about two *mixtures* ξ, ξ' over a class M. The capstone
proves universality only, and `universalContinuousSemimeasure` is a `Classical.choose`. Fix: use the explicit
upstream mixture as the background. Upstream (`MonotoneComplexity/TreeMixture.lean`,
`MonotoneComplexity/MaximalSemimeasure.lean`) has `treeLSCEnum : ℕ → BitString → ℝ≥0∞` (each member a
root-1 lsc continuous semimeasure), `treeLSCEnum_complete` (every such semimeasure equals some
`treeLSCEnum i`), `continuousTreeMixture b x = ∑' i, dyadicWeight i * b i x`,
`treeMixture_isLowerSemicomputableContinuousSemimeasure`, `continuousTreeMixture_dominates_component`.

Goal: a new file `P33Mixture.lean` proving

> **Theorem.** Let ν = `treeLSCEnum` (the class M_U of all lsc continuous semimeasures, root 1). There exist
> weights w₋, w₊ : ℕ → ℝ≥0∞ and an index j such that
> (1) every weight is positive, and ∑' i, w± i ≤ 1 (or = 1);
> (2) ∀ i, w₋ i ≤ 3 * w₊ i ∧ w₊ i ≤ 3 * w₋ i;
> (3) with ξ±(x) := ∑' i, w± i * ν i x, both are lsc continuous semimeasures (`IsLowerSemicomputableContinuousSemimeasure`);
> (4) μ ∈ M_U: ν j equals the source's prefix probability (`fun x => ENNReal.ofReal (prob source |x| h_x)`
>     transported to BitString), so the true environment is a member of the class with weight w± j > 0;
> (5) ∀ n ≥ 2, n^{1/4}/256 ≤ loss source (transport ξ₋) n − loss source (transport ξ₊) n,
>     and the difference tends to +∞.

Route: background M := continuousTreeMixture treeLSCEnum (positive since it dominates the uniform measure, root 1);
P, Q from Theorem 4 are lsc root-1 semimeasures (reuse the capstone's lsc proofs), so P = ν p, Q = ν q by
completeness; then ξ± = (1−η)(w·P + (1−w)·Q) + η·M is ∑' i, w± i * ν i with
w± i = η·dyadicWeight i + [i = p]·(1−η)·w± + [i = q]·(1−η)·(1−w±) (w₊ = 3/4, w₋ = 1/4; check p ≠ q, or handle
p = q). Reuse `Theorem4.theorem4` for the gap.

Requirements: Part 1 (statement, short), Part 2 (proofs); no `sorry`, `admit`, new axioms or `native_decide`;
do not edit the attached files. One Lean code block, then a map to the theorem above, then deviations.
