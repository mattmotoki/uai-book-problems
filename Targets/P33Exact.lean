/- Frozen target (desk, 2026-11-21): Problem 3.3 with exact complexity weights 2^{-K(i)} (Pro 008 Theorem 6;
   027 Theorem 5). Matt chose this after paper draft 3. Fidelity note at the end. -/
import HutterPrizes.P33Complexity

open scoped BigOperators ENNReal
open Kolmogorov RobustExperiment RobustExperiment.Theorem4 P33Effective

namespace P33Exact

/-- The mixture with exact weights 2^{-K_C(i)}, K_C(i) = KPNat C i the prefix complexity of the index i relative to
the machine C, over an enumeration τ of semimeasures. -/
noncomputable def exactMixture (C : Map) (τ : ℕ → BitString → ℝ≥0∞) (x : BitString) : ℝ≥0∞ :=
  ∑' i, complexityWeight (KPNat C i) * τ i x

/-- 3.3 with exact 2^{-K} weights: there are an effective enumeration τ of all lower semicomputable semimeasures
(root 1, with repetitions; a computable renumbering of upstream `treeLSCEnum` in both directions) and two optimal
prefix machines C⁻, C⁺ such that the mixtures ξ± = Σ_i 2^{-K_{C±}(i)} τ_i are universal lower semicomputable
semimeasures, their weights differ by at most a factor 4 at every index, the source µ
is some τ_j, and the µ-expected 0-1 losses (ties toward 1) differ by ≥ n^{1/4}/512 for n ≥ 3, tending to +∞. -/
theorem exact_counterexample :
    ∃ (τ : ℕ → BitString → ℝ≥0∞) (CMinus CPlus : Map),
      IsUniformlyLowerSemicomputableTreeFamily τ ∧
      (∀ i, IsLowerSemicomputableContinuousSemimeasure (τ i)) ∧
      (∀ a : BitString → ℝ≥0∞, IsLowerSemicomputableContinuousSemimeasure a → ∃ i, τ i = a) ∧
      IsOptimalPrefixConditional CMinus ∧ IsOptimalPrefixConditional CPlus ∧
      (∃ f g : ℕ → ℕ, Computable f ∧ Computable g ∧
        (∀ i, τ (f i) = treeLSCEnum i) ∧ (∀ i, treeLSCEnum (g i) = τ i)) ∧
      (∀ i,
        complexityWeight (KPNat CMinus i) ≤ 4 * complexityWeight (KPNat CPlus i) ∧
        complexityWeight (KPNat CPlus i) ≤ 4 * complexityWeight (KPNat CMinus i)) ∧
      IsUniversal (exactMixture CMinus τ) ∧ IsUniversal (exactMixture CPlus τ) ∧
      (∀ x, exactMixture CMinus τ (x ++ [false]) + exactMixture CMinus τ (x ++ [true]) ≤
        exactMixture CMinus τ x) ∧
      (∀ x, exactMixture CPlus τ (x ++ [false]) + exactMixture CPlus τ (x ++ [true]) ≤
        exactMixture CPlus τ x) ∧
      exactMixture CMinus τ [] ≤ 1 ∧ exactMixture CPlus τ [] ≤ 1 ∧
      IsLSC (fun x _ => exactMixture CMinus τ x) ∧ IsLSC (fun x _ => exactMixture CPlus τ x) ∧
      (∃ j, ∀ n (h : History n), τ j (toBitString h) = ENNReal.ofReal (prob source n h)) ∧
      (∀ n : ℕ, 3 ≤ n →
        (n : ℝ)^(1/4 : ℝ)/512 ≤
          loss source (transport (exactMixture CMinus τ)) n -
            loss source (transport (exactMixture CPlus τ)) n) ∧
      Filter.Tendsto
        (fun n : ℕ =>
          loss source (transport (exactMixture CMinus τ)) n -
            loss source (transport (exactMixture CPlus τ)) n)
        Filter.atTop Filter.atTop := by
  sorry

end P33Exact

/- Fidelity note.
Source: book Problem 3.3 (two mixtures ξ, ξ′ over M; is L^ξ − L^ξ′ < ∞?) with the universal prior of Sec. 2.4 /
Sec. 3.2 in the index convention K(ν_i) := K(i) (book p. 48; as in docs/reviews/2026-11-21-fidelity-33-complexity.md),
i.e. ξ_U = Σ_i 2^{-K_U(i)} ν_i over an enumeration of the class M_U of lsc semimeasures. Here the two mixtures differ
only in the reference machine: both use exact weights 2^{-K_C(i)} for optimal prefix machines C⁻, C⁺ (upstream
`IsOptimalPrefixConditional`, `KPNat` = prefix complexity of the binary code of i, `complexityWeight` = 2^{-·}).
Paper source: Pro 008 Theorem 6; 027 Theorem 5; referee docs/reviews/2026-11-21-referee-027.md. Fidelity review:
docs/reviews/2026-11-21-fidelity-33-exact.md (faithful with caveats; caveats L1-L4 applied here). Planned design:
τ_0 = τ_1 = P, τ_2 = τ_3 = Q, τ_{i+4} = treeLSCEnum i; C⁻ gives indices 0-3 short codes of lengths 4,4,2,3 (C⁺: 2,3,4,4)
and on 1^L·p (L ≥ 21) simulates U0(p, y); P, Q are the theorem4 splices of M ∝ Σ_{i≥4} 2^{-L-K_U0(i)} τ_i.
- τ and C± are constructed (existential); τ is exhaustive with repetitions, uniformly lsc, and a computable
  renumbering of `treeLSCEnum` (f, g); each τ_i has root 1 (upstream convention of P33Effective/P33Complexity).
- The mixtures are not normalized (root ≤ 1); Bayes actions do not depend on a positive scale.
- Per-index weight ratio ≤ 4 (027's {1/4, 1, 4}); universality (`P33Effective.IsUniversal`) stated.
- Constant 1/512 and n ≥ 3 follow 027 Thm 5; the planned design gives 1/256 for n ≥ 2, which implies it.
- Not claimed: the result for every pair of optimal machines, for the standard enumeration itself, or for semantic
  weights 2^{-K(ν)}; Solomonoff's M_U (monotone machines; 008 Theorem 7).
- Ties toward 1 (`predict`), as in the mixture review.
-/
