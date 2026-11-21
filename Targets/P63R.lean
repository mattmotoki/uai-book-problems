/-
Target 6.3R (Problem 6.3, a side claim; Pro query 001, section 7).

Book (p. 208, Problem 6.3) asks whether a posterior error bound can be bounded by
≈ 2^{K(z_k:n | z_<k)}. A natural route would use M(x)/M(xy) ≤ C·2^{K(y|x)} uniformly in x, y.
This target refutes that uniform ratio: for x = 0^ℓ and y = 1 the conditional complexity
K(1 | 0^ℓ) stays bounded, but M(0^ℓ)/M(0^ℓ1) is unbounded (it grows like 2^{K(ℓ)}).
It does not refute the error-count bound itself (a one-bit tail has at most one error).

Upstream: `KP U x y` is K(x | y), so K(y | x) is `KP U y x`. M is the library's canonical
universal continuous semimeasure.
-/
import KolmogorovMathlib.Solomonoff.Basic

namespace HutterPrizes.Targets

open Kolmogorov
open scoped ENNReal

theorem uniform_conditional_ratio_fails (U : Map) (hU : IsOptimalPrefixConditional U) :
    (∃ C₀ : ℕ, ∀ ℓ : ℕ, KP U [true] (List.replicate ℓ false) ≤ C₀) ∧
    ∀ C : ℕ, ∃ ℓ : ℕ,
      (2 : ℝ≥0∞) ^ C * universalContinuousSemimeasure (List.replicate ℓ false ++ [true]) <
        universalContinuousSemimeasure (List.replicate ℓ false) := by
  sorry

end HutterPrizes.Targets
