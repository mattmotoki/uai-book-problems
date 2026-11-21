/- Frozen target (desk, 2026-11-21): Theorem 2 of Pro 027 (Problem 3.3 when M is a class of probability
   measures), for the class of computable measures with rational conditionals. Fidelity note at the end. -/
import HutterPrizes.P33Effective
import HutterPrizes.P27Stochastic

open scoped BigOperators ENNReal
open Kolmogorov RobustExperiment RobustExperiment.Theorem4 P33Effective

namespace P33Measures

/-- The class C: computable probability measures on binary strings given by computable rational next-bit
conditionals r(x) = ν(1 | x) ∈ [0, 1] (indexed by the conditional function; different r may give the same
measure). -/
def RatMeasure : Type := {r : BitString → ℚ // Computable r ∧ ∀ x, 0 ≤ r x ∧ r x ≤ 1}

/-- ν(x) for ν ∈ C, as the product of its conditionals (`P27Stochastic.muProb`). -/
noncomputable def measureMass (ν : RatMeasure) (x : BitString) : ℝ≥0∞ :=
  ENNReal.ofReal (P27Stochastic.muProb ν.1 x)

/-- The Bayes mixture ξ_w(x) = Σ_ν w_ν ν(x) over C. -/
noncomputable def classMixture (w : RatMeasure → ℝ≥0∞) (x : BitString) : ℝ≥0∞ :=
  ∑' ν, w ν * measureMass ν x

/-- 027 Theorem 2 (rational-conditional class): the source µ of the 3.3 construction is in C, and for every
strictly positive prior a on C with Σ a = 1 there are strictly positive priors w⁻, w⁺ on C, each summing to 1,
with w± ≥ a/2^20 and ratio in [1/3, 3], whose µ-expected 0-1 losses (ties toward 1) differ by ≥ n^{1/4}/256 for
all n ≥ 2, and the difference tends to +∞. -/
theorem measure_class_counterexample :
    ∃ μ : RatMeasure, (∀ n (h : History n), source.cond n h = (μ.1 (toBitString h) : ℝ)) ∧
      ∀ a : RatMeasure → ℝ≥0∞, (∀ ν, 0 < a ν) → (∑' ν, a ν) = 1 →
        ∃ wMinus wPlus : RatMeasure → ℝ≥0∞,
          (∀ ν, 0 < wMinus ν ∧ 0 < wPlus ν) ∧
          (∑' ν, wMinus ν) = 1 ∧ (∑' ν, wPlus ν) = 1 ∧
          (∀ ν, a ν / 2 ^ 20 ≤ wMinus ν ∧ a ν / 2 ^ 20 ≤ wPlus ν) ∧
          (∀ ν, wMinus ν ≤ 3 * wPlus ν ∧ wPlus ν ≤ 3 * wMinus ν) ∧
          (∀ n : ℕ, 2 ≤ n →
            (n : ℝ)^(1/4 : ℝ)/256 ≤
              loss source (transport (classMixture wMinus)) n -
                loss source (transport (classMixture wPlus)) n) ∧
          Filter.Tendsto
            (fun n : ℕ =>
              loss source (transport (classMixture wMinus)) n -
                loss source (transport (classMixture wPlus)) n)
            Filter.atTop Filter.atTop := by
  sorry

end P33Measures

/- Fidelity note.
Source: book Problem 3.3 with Sec. 3.2.2 (p. 70), where M is a countable class of probability measures, µ ∈ M,
and ξ = Σ_ν w_ν ν with w_ν > 0, Σ w_ν = 1 ((3.5)). Pro 027 Theorem 2; referee docs/reviews/2026-11-21-referee-027.md
(correct). Reuses `source`, `loss`, `predict` (ties toward 1), `transport`, `History`, `toBitString` from the
P33 files and `muProb` from P27Stochastic (reviewed in docs/reviews/2026-11-21-fidelity-27-stochastic.md).
- Class: measures with a total computable rational conditional r into [0,1], indexed by r (a multiset of
  measures). 027 Theorem 2 covers the class with conditionals only at positive-mass histories, and all
  computable measures; both are paper steps here. Review: docs/reviews/2026-11-21-fidelity-33-measures.md.
- w± are not claimed to equal a; ties toward 1 (as in the mixture review).
- Quantifiers: one µ for all priors a; w± depend on a. η is fixed at 2^-20 (the report allows any 0 < η ≤ 2^-20).
- No claim that w± or the mixtures are computable. Upper bound (11/112)n^{1/4} not stated.
- µ ∈ C is stated through the conditionals: source.cond n h = r(toBitString h) on every history.
-/
