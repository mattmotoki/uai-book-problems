/- Frozen statement layer of the 3.3 mixture capstone (Pro query 018), copied 2026-11-21.
   The class is upstream `treeLSCEnum`: every member is a root-1 lsc continuous semimeasure
   (`treeLSCEnum_isLowerSemicomputableContinuousSemimeasure`) and every such semimeasure occurs
   (`treeLSCEnum_complete`). This closes the 'mixtures' caveat of
   docs/reviews/2026-11-21-fidelity-33-effective.md. -/
/-
Two Bayes mixtures over the fixed enumeration of root-one lower
semicomputable continuous semimeasures.

Lean 4.35.0; Mathlib v4.35.0;
kolmogorov-complexity-lean 17c50e560c337a8a702f8850a711f80a56b3cf91.
The three attached files are imported without modification.
-/
import HutterPrizes.P33Effective
import KolmogorovMathlib.MonotoneComplexity.MaximalSemimeasure

open scoped BigOperators ENNReal
open Kolmogorov RobustExperiment RobustExperiment.Theorem4 P33Effective

namespace P33Mixture

set_option maxHeartbeats 2000000

/-! Part 1. Statement. -/

/-- A Bayes mixture over precisely the upstream enumeration. -/
noncomputable def bayesMixture (w : ℕ → ℝ≥0∞) : BitString → ℝ≥0∞ :=
  fun x => ∑' i, w i * treeLSCEnum i x

def MixtureStatement : Prop :=
  ∃ (wMinus wPlus : ℕ → ℝ≥0∞) (j : ℕ),
    (∀ i, 0 < wMinus i ∧ 0 < wPlus i) ∧
    (∑' i, wMinus i) = 1 ∧ (∑' i, wPlus i) = 1 ∧
    (∀ i, wMinus i ≤ 3 * wPlus i ∧ wPlus i ≤ 3 * wMinus i) ∧
    IsLowerSemicomputableContinuousSemimeasure (bayesMixture wMinus) ∧
    IsLowerSemicomputableContinuousSemimeasure (bayesMixture wPlus) ∧
    (∀ n (h : History n),
      treeLSCEnum j (toBitString h) = ENNReal.ofReal (prob source n h)) ∧
    (0 < wMinus j ∧ 0 < wPlus j) ∧
    (∀ n : ℕ, 2 ≤ n →
      (n : ℝ)^(1/4 : ℝ)/256 ≤
        loss source (transport (bayesMixture wMinus)) n -
          loss source (transport (bayesMixture wPlus)) n) ∧
    Filter.Tendsto
      (fun n : ℕ =>
        loss source (transport (bayesMixture wMinus)) n -
          loss source (transport (bayesMixture wPlus)) n)
      Filter.atTop Filter.atTop

theorem mixture_counterexample : MixtureStatement := by
  sorry

end P33Mixture
