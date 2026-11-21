/- Frozen target (desk, 2026-11-21): Problem 3.3 with complexity priors (Pro 008 §4.2, Corollary 5).
   Matt's D2 answer: strengthen 3.3 before any contact. Fidelity note at the end. -/
import HutterPrizes.P33Mixture

open scoped BigOperators ENNReal
open Kolmogorov RobustExperiment RobustExperiment.Theorem4 P33Effective P33Mixture

namespace P33Complexity

/-- Both prior weight vectors are within constant factors of 2^{-K(i)}, K(i) = KPNat U i the prefix complexity of
the index i of the i-th enumerated lsc semimeasure `treeLSCEnum i`; each sums to at most 1 (book Sec. 2.4 p. 49, Problem 3.1 p. 120); their
ratio stays in [1/3, 3]; both mixtures are lower semicomputable semimeasures; µ = `treeLSCEnum j`; and the
µ-expected 0-1 loss difference is ≥ n^{1/4}/256 for n ≥ 2 and tends to +∞. -/
def ComplexityStatement (U : Map) : Prop :=
  ∃ (wMinus wPlus : ℕ → ℝ≥0∞) (j : ℕ) (c C : ℝ≥0∞),
    0 < c ∧ C ≠ ⊤ ∧
    (∀ i, c * complexityWeight (KPNat U i) ≤ wMinus i ∧ wMinus i ≤ C * complexityWeight (KPNat U i)) ∧
    (∀ i, c * complexityWeight (KPNat U i) ≤ wPlus i ∧ wPlus i ≤ C * complexityWeight (KPNat U i)) ∧
    (∑' i, wMinus i) ≤ 1 ∧ (∑' i, wPlus i) ≤ 1 ∧
    (∀ i, wMinus i ≤ 3 * wPlus i ∧ wPlus i ≤ 3 * wMinus i) ∧
    (∀ x, bayesMixture wMinus (x ++ [false]) + bayesMixture wMinus (x ++ [true]) ≤ bayesMixture wMinus x) ∧
    (∀ x, bayesMixture wPlus (x ++ [false]) + bayesMixture wPlus (x ++ [true]) ≤ bayesMixture wPlus x) ∧
    bayesMixture wMinus [] ≤ 1 ∧ bayesMixture wPlus [] ≤ 1 ∧
    IsLSC (fun x _ => bayesMixture wMinus x) ∧ IsLSC (fun x _ => bayesMixture wPlus x) ∧
    (∀ n (h : History n),
      treeLSCEnum j (toBitString h) = ENNReal.ofReal (prob source n h)) ∧
    (∀ n : ℕ, 2 ≤ n →
      (n : ℝ)^(1/4 : ℝ)/256 ≤
        loss source (transport (bayesMixture wMinus)) n -
          loss source (transport (bayesMixture wPlus)) n) ∧
    Filter.Tendsto
      (fun n : ℕ =>
        loss source (transport (bayesMixture wMinus)) n -
          loss source (transport (bayesMixture wPlus)) n)
      Filter.atTop Filter.atTop

theorem complexity_counterexample (U : Map) (hU : IsOptimalPrefixConditional U) :
    ComplexityStatement U := by
  sorry

end P33Complexity

/- Fidelity note.
Source: book Problem 3.3 (Sec. 3.2.9, p. 81, class M_U; Σ w ≤ 1: Sec. 2.4 p. 49, Problem 3.1 p. 120); Hutter's standard universal prior
w_ν = 2^{-K(ν)}; Pro 008 §4.2 Corollary 5 (weights ≍ 2^{-K_C(i)}). Builds on `P33Mixture` (review:
docs/reviews/2026-11-21-fidelity-33-mixture.md, faithful with caveats) with the same source µ, `loss`, `predict`
(ties toward 1), `transport`, `treeLSCEnum`.
- K(ν) is read as K(i) for the enumeration index i of ν (book p. 48: "K(ν_i) := K(i)" for the multiset M_U).
  Weights are per index; the total weight of one distinct ν is not bounded above by C·2^{-K(ν)}.
  the weights are within constant factors of 2^{-K(i)}, not equal to it (exact 2^{-K} weights are 008 Theorem 6,
  a separate target).
- Σ w ≤ 1 (not = 1), so the mixtures have root ≤ 1; they are stated as lsc tree semimeasures with root ≤ 1 rather
  than the upstream root-1 class. The 0-1 Bayes action compares s(h0) with s(h1), so it is scale-invariant.
- c, C, j may depend on U. µ is in the class (index j), with weight ≥ c·2^{-K(j)} > 0.
- Not stated: universality of the mixtures (paper step from c·2^{-K(i)} ≤ w_i); lsc or computable weights;
  measure classes (M_comp). The earlier "same mixtures over the full M_U" paper step does not carry over.
- Proof hint (review): P, Q built from M = Σ 2^{-K(i)} ν_i have root < 1; use root-1 versions (value 1 at [])
  and a lemma that `loss` reads only levels ≥ 1.
- Review: docs/reviews/2026-11-21-fidelity-33-complexity.md (faithful with caveats).
-/
