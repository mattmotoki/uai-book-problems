/-
Smoke test: the upstream Solomonoff bound builds against our pinned toolchain.
Hutter (2005) Theorem 3.19: if c * mu <= a for a semimeasure a, the summed squared
prediction errors are at most ln(1/c) / 2.
-/
import KolmogorovMathlib.Solomonoff.Convergence

namespace HutterPrizes

open MeasureTheory Kolmogorov
open scoped ENNReal

/-- Restated through the upstream theorem, so a break upstream breaks this file. -/
theorem solomonoff_total_error (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ x, ENNReal.ofReal c * cantorMass μ x ≤ a x) (b : Bool) :
    ∑' n, predictionError μ a b n ≤ Real.log c⁻¹ / 2 :=
  (tsum_predictionError_le μ ha hc hdom b).2

end HutterPrizes
