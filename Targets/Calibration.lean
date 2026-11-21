/-
Calibration target C1 (known result, first part of Hutter 2005 Problem 3.3, rated C05u).

Book text (p. 119, Problem 3.3): for two mixtures ξ and ξ' over M,
  Σ_t E[Σ_{x_t} (ξ(x_t|x_<t) − ξ'(x_t|x_<t))²] ≤ 2[ln w_μ⁻¹ + ln w'_μ⁻¹] < ∞.

Formal reading: a and a' are semimeasures that dominate the true measure μ with
constants c and c' (this is what "mixture with weight w_μ" gives). The error is
per bit b, as in the upstream `predictionError`. Squared difference splits as
(a − a')² ≤ 2(a − μ)² + 2(μ − a')², so Theorem 3.19 (upstream
`sum_predictionError_le`, bound ln(1/c)/2 each) gives ln(1/c) + ln(1/c').

Purpose: test the Pro → Lean loop on a known statement next to the open part of 3.3.
-/
import KolmogorovMathlib.Solomonoff.Convergence

namespace HutterPrizes.Targets

open MeasureTheory Kolmogorov
open scoped ENNReal

theorem two_semimeasures_sum_sq_le (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a a' : BitString → ℝ≥0∞}
    (ha : IsContinuousTreeSemimeasure a) (ha' : IsContinuousTreeSemimeasure a')
    {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c')
    (hdom : ∀ x, ENNReal.ofReal c * cantorMass μ x ≤ a x)
    (hdom' : ∀ x, ENNReal.ofReal c' * cantorMass μ x ≤ a' x)
    (b : Bool) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        prefixExpectation μ n (fun x => (condProb a x b - condProb a' x b) ^ 2)
      ≤ Real.log c⁻¹ + Real.log c'⁻¹ := by
  sorry

end HutterPrizes.Targets
