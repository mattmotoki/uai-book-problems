This compiles successfully with **Lean 4.35.0**, **Mathlib v4.35.0**, and library commit `17c50e560c337a8a702f8850a711f80a56b3cf91`. The axiom check reports only `propext`, `Classical.choice`, and `Quot.sound`.

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
  have hmul (n : ℕ) (f : BitString → ℝ) :
      prefixExpectation μ n (fun x => 2 * f x) =
        2 * prefixExpectation μ n f := by
    unfold prefixExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hbound (n : ℕ) :
      prefixExpectation μ n
          (fun x => (condProb a x b - condProb a' x b) ^ 2) ≤
        2 * predictionError μ a b n + 2 * predictionError μ a' b n := by
    unfold predictionError
    rw [← hmul, ← hmul, ← prefixExpectation_add]
    apply prefixExpectation_mono
    intro x _
    nlinarith only [sq_nonneg
      (condProb a x b + condProb a' x b -
        2 * condProb (cantorMass μ) x b)]
  have hsum :=
    Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) => hbound n)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have h1 := sum_predictionError_le μ ha hc hdom b N
  have h2 := sum_predictionError_le μ ha' hc' hdom' b N
  linarith only [hsum, h1, h2]

end HutterPrizes.Targets
```

**Informal proof.** For each prefix \(x\), write \(p=a(b\mid x)\), \(q=a'(b\mid x)\), and \(m=\mu(b\mid x)\). Since
\[
2(p-m)^2+2(q-m)^2-(p-q)^2=(p+q-2m)^2\ge 0,
\]
monotonicity and linearity of `prefixExpectation` give
\[
E_n[(p-q)^2]
\le 2\,\operatorname{predictionError}(\mu,a,b,n)
  +2\,\operatorname{predictionError}(\mu,a',b,n).
\]
Sum over \(n<N\) and apply `sum_predictionError_le` to each semimeasure. The resulting bound is
\[
2\frac{\log(c^{-1})}{2}
+2\frac{\log((c')^{-1})}{2}
=\log(c^{-1})+\log((c')^{-1}),
\]
as required.