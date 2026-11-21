# Lean 4 proof request: normalized Solomonoff prediction has per-step error at least 2^-(K(t)+C)

Write a complete Lean 4 proof replacing the `sorry` below. It must compile with Lean `v4.35.0`, Mathlib
`v4.35.0`, and https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean at commit
`17c50e560c337a8a702f8850a711f80a56b3cf91` (read its source on GitHub). No `sorry`, `admit`, new axioms, or
`native_decide`. Keep the theorem statement exactly as given; helper lemmas are fine. Give the whole file in
one Lean code block, then a short informal proof, then the list of upstream declarations you used.

## Target file

```lean
/-
Target 2.7F (Problem 2.7, normalized lower bound; Pro query 001, section 3).

Book (p. 62, Problem 2.7): "Do similar lower performance bounds hold for measure
M_norm(x_t|x_<t) := M(x_t|x_<t) / Σ_{x_t} M(x_t|x_<t), which has no defect?"
The lower bound for M is 1 − M(x_t|x_<t) ≥ (defect) ≳ 2^{-K(t)}.

Formal reading: for the library's canonical universal semimeasure M and optimal prefix
machine U, there is a constant C such that for every history x (of length t − 1) and every
bit b, the sibling-normalized probability of b is at least 2^{-(K(t) + C)}, with t = |x| + 1.
Taking b = the wrong bit gives a per-step lower bound on the normalized prediction error
of order 2^{-K(t)}: the normalized predictor errs by at least that much at every step.
C depends only on U (it is quantified before x and b).

Caveats: the canonical M is one dominant semimeasure, built from a maximality theorem
(Pro: its root mass is 1 in the library; the book allows ≤ 1). The extension to every
dominant M is a separate statement.
-/
import KolmogorovMathlib.Solomonoff.SelectedBits.Basic

namespace HutterPrizes.Targets

open Kolmogorov Kolmogorov.SelectedBits
open scoped ENNReal

theorem normalized_lower_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (x : BitString) (b : Bool),
      ((2 : ℝ)⁻¹) ^ ((KPNat U (x.length + 1)).toNat + C) ≤
        normalizedSiblingProb universalContinuousSemimeasure x b := by
  sorry

end HutterPrizes.Targets
```

## Suggested route (your own analysis from an earlier chat)

For t ≥ 1 define ν_t(y) = M(y) if |y| < t, M(parent y)/2 if |y| = t, 0 if |y| > t. These are a uniformly
lower-semicomputable family of continuous semimeasures, so their sums over prefix-free sets are ≤ 1. Mix
them with weights ≈ 2^-K(t). Domination gives M(xb) ≥ 2^-(K(|x|+1)+C) · M(x)/2. Divide by
M(x0) + M(x1) ≤ M(x).

Upstream helpers that look relevant (check the exact statements in the source):
- `Kolmogorov.exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree`
  (in `KolmogorovMathlib/Solomonoff/Domination/UniformFamily.lean`)
- `Kolmogorov.IsContinuousTreeSemimeasure.sum_antichain_le`
- `Kolmogorov.universalContinuousSemimeasure`, its positivity and semimeasure lemmas
- `Kolmogorov.SelectedBits.normalizedSiblingProb` (in `KolmogorovMathlib/Solomonoff/SelectedBits/Basic.lean`):
```lean
noncomputable def normalizedSiblingProb (a : BitString → ℝ≥0∞) (x : BitString) (b : Bool) :
    ℝ :=
  (a (x ++ [b])).toReal / ((a (x ++ [false])).toReal + (a (x ++ [true])).toReal)

theorem exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree (U : Map)
    (hU : IsOptimalPrefixConditional U) (ν : ℕ → BitString → ℝ≥0∞)
    (hν : IsUniformlyLowerSemicomputableTreeFamily ν)
    (hfree : ∀ (e : ℕ) (S : Finset BitString), IsPrefixFree (S : Set BitString) →
      ∑ x ∈ S, ν e x ≤ 1) :
    ∃ C : ℕ, ∀ (e : ℕ) (x : BitString),
      (2 : ℝ≥0∞)⁻¹ ^ ((KPNat U e).toNat + C) * ν e x ≤ universalContinuousSemimeasure x := by
```
