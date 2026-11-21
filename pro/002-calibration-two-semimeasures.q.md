# Lean 4 proof request (calibration): sum of squared differences of two dominating semimeasures

Write a complete Lean 4 proof that replaces the `sorry` below. It must compile with:
- Lean `leanprover/lean4:v4.35.0`, Mathlib tag `v4.35.0`;
- the library https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean at commit
  `17c50e560c337a8a702f8850a711f80a56b3cf91` (you can read its source on GitHub).

No `sorry`, no `admit`, no new axioms, no `native_decide`. Keep the theorem statement exactly as given.
Helper lemmas are fine. Give the whole file in one Lean code block, then a short informal proof.

Informal idea: (p − q)² ≤ 2(p − m)² + 2(m − q)², take prefixExpectation, sum over n, and apply
`Kolmogorov.sum_predictionError_le` to a and to a' (each gives ln(1/c)/2).

## Target file

```lean
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
```

## Upstream declarations you will need (namespace `Kolmogorov`)

```lean
noncomputable def prefixExpectation (μ : Measure CantorSeq) (n : ℕ) (f : BitString → ℝ) : ℝ :=
  ∑ x ∈ levelFinset n, (cantorMass μ x).toReal * f x

theorem prefixExpectation_add (μ : Measure CantorSeq) (n : ℕ) (f g : BitString → ℝ) :
    prefixExpectation μ n (fun x => f x + g x) =
      prefixExpectation μ n f + prefixExpectation μ n g := by
  -- (proof omitted)

theorem prefixExpectation_mono (μ : Measure CantorSeq) (n : ℕ) {f g : BitString → ℝ}
    (h : ∀ x, cantorMass μ x ≠ 0 → f x ≤ g x) :
    prefixExpectation μ n f ≤ prefixExpectation μ n g := by
  -- (proof omitted)

theorem prefixExpectation_nonneg (μ : Measure CantorSeq) (n : ℕ) {f : BitString → ℝ}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ prefixExpectation μ n f := by
  -- (proof omitted)

noncomputable def predictionError (μ : Measure CantorSeq) (a : BitString → ℝ≥0∞) (b : Bool)
    (n : ℕ) : ℝ :=
  prefixExpectation μ n (fun x => (condProb a x b - condProb (cantorMass μ) x b) ^ 2)

noncomputable def condProb (a : BitString → ℝ≥0∞) (x : BitString) (b : Bool) : ℝ :=
  (a (x ++ [b])).toReal / (a x).toReal

theorem sum_predictionError_le (μ : Measure CantorSeq) [IsProbabilityMeasure μ]
    {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ x, ENNReal.ofReal c * cantorMass μ x ≤ a x) (b : Bool) (N : ℕ) :
    ∑ n ∈ Finset.range N, predictionError μ a b n ≤ Real.log c⁻¹ / 2 := by
  -- (proof omitted)
```

`prefixExpectation μ n f` is a finite sum over strings of length n, so constant factors can be pulled out
with `Finset.mul_sum` after `unfold prefixExpectation`.
