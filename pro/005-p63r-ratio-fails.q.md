# Lean 4 proof request: the uniform conditional-complexity ratio M(x)/M(xy) ≤ C·2^K(y|x) fails

Write a complete Lean 4 proof replacing the `sorry` below. It must compile with Lean `v4.35.0`, Mathlib
`v4.35.0`, and https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean at commit
`17c50e560c337a8a702f8850a711f80a56b3cf91` (read its source on GitHub). No `sorry`, `admit`, new axioms, or
`native_decide`. Keep the theorem statement exactly as given; helper lemmas are fine. Give the whole file in
one Lean code block, then a short informal proof, then the upstream declarations you used.

## Target file

```lean
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
```

## Informal route (your own analysis from an earlier chat)

- First conjunct: K(1 | 0^ℓ) = O(1), since a fixed program prints `[true]` and ignores the condition
  (optimality / invariance of `U`).
- Second conjunct: M(0^ℓ) ≥ c > 0 for all ℓ (M dominates the computable Dirac measure on 000…).
  The words 0^ℓ1 form a computably enumerable prefix-free set, so ℓ ↦ M(0^ℓ1) is a discrete
  lower-semicomputable semimeasure on ℕ, hence M(0^ℓ1) ≤ C'·2^-K(ℓ) (coding theorem direction
  m(ℓ) ≥ c·M(0^ℓ1), and m(ℓ) ≈ 2^-K(ℓ)). Since K(ℓ) is unbounded, the ratio is unbounded.

In our project the same library already gave a proof (by you) of: ∃ C, ∀ x b,
(1/2)^(KPNat U (|x|+1) + C) ≤ normalizedSiblingProb M x b, using
`Kolmogorov.exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree`; the upper-bound direction
needed here is the converse coding-theorem fact, so look for the library's coding theorem / a-priori
probability results (`KolmogorovMathlib/AlgorithmicProbability/`, `MonotoneComplexity/`).
