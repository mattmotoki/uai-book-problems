/- Frozen statement layer of the effective 3.3 capstone (Pro query 014), copied 2026-11-21.
   Fidelity review: docs/reviews/ (pending). -/
/-
Effective capstone for the specified Problem 3.3 counterexample.
Lean 4.35.0, Mathlib v4.35.0, kolmogorov-complexity-lean
commit 17c50e560c337a8a702f8850a711f80a56b3cf91.
The two imported experiment files are used without modification.
-/
import HutterPrizes.P33Theorem3
import HutterPrizes.P33Theorem4
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.Solomonoff.Domination
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped BigOperators ENNReal
open Kolmogorov RobustExperiment RobustExperiment.Theorem4

namespace P33Effective

set_option maxHeartbeats 2000000

/-! Part 1. Statement layer. -/

def toBitString : {n : ℕ} → History n → BitString
  | 0, _ => []
  | _n + 1, (h, b) => toBitString h ++ [b]

def transport (a : BitString → ℝ≥0∞) : Mass :=
  fun _ h => (a (toBitString h)).toReal


/-- Universality among the upstream normalized lower semicomputable tree semimeasures. -/
def IsUniversal (a : BitString → ℝ≥0∞) : Prop :=
  ∀ a', IsLowerSemicomputableContinuousSemimeasure a' →
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ x, a' x ≤ c * a x

/-- The four requested conclusions, with the source and action rule fixed by the attachments. -/
def EffectiveStatement : Prop :=
  ∃ ξMinus ξPlus : BitString → ℝ≥0∞,
    IsLowerSemicomputableContinuousSemimeasure ξMinus ∧
    IsLowerSemicomputableContinuousSemimeasure ξPlus ∧
    IsUniversal ξMinus ∧ IsUniversal ξPlus ∧
    (∃ r : BitString → ℚ, Computable r ∧
      ∀ n (h : History n), source.cond n h = (r (toBitString h) : ℝ)) ∧
    (∀ n : ℕ, (∑ h : History n, prob source n h) = 1) ∧
    ∀ n : ℕ, 2 ≤ n →
      (n : ℝ)^(1/4 : ℝ)/256 ≤
        loss source (transport ξMinus) n - loss source (transport ξPlus) n

theorem effective_counterexample : EffectiveStatement := by
  sorry

end P33Effective
