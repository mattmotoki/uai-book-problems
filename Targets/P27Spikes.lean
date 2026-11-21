/- Frozen target (desk, 2026-11-21): Theorem 6 of Pro 020b (Problem 2.7, upper-bound side), over the root-1
   universal class of `Targets/P27Stochastic.lean`. Fidelity note at the end. -/
import HutterPrizes.P27Stochastic

open scoped BigOperators ENNReal
open Kolmogorov Kolmogorov.SelectedBits P27Stochastic

namespace P27Spikes

/-- The fair coin: every next-bit conditional is 1/2. -/
def fairCoin : BitString → ℚ := fun _ => 1 / 2

/-- 020b Theorem 6: there is a universal lower semicomputable semimeasure M such that, for the fair coin, the
expected L1 and squared errors of the normalized M are not O(2^{-αK(t)}) for any α > 0. -/
theorem no_power_upper_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ a : BitString → ℝ≥0∞, IsLowerSemicomputableContinuousSemimeasure a ∧ P33Effective.IsUniversal a ∧
      ∀ α : ℝ, 0 < α → ∀ C : ℝ, ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧
        C * w U t ^ α < expSqErr a fairCoin t ∧ C * w U t ^ α < expAbsErr a fairCoin t := by
  sorry

/-- Stronger form (review suggestion): for every universal V there is an lsc semimeasure ν such that the
half-half mixture ½V + ½ν is universal and has the spikes. With V a Solomonoff prior, the mixture is again one
(paper step: 𝓑 is closed under ½V + ½ν, Wood-Sunehag-Hutter). -/
theorem no_power_upper_bound_mix (U : Map) (hU : IsOptimalPrefixConditional U)
    (V : BitString → ℝ≥0∞) (hV : IsLowerSemicomputableContinuousSemimeasure V)
    (huV : P33Effective.IsUniversal V) :
    ∃ ν : BitString → ℝ≥0∞, IsLowerSemicomputableContinuousSemimeasure ν ∧
      let a : BitString → ℝ≥0∞ := fun x => V x / 2 + ν x / 2
      IsLowerSemicomputableContinuousSemimeasure a ∧ P33Effective.IsUniversal a ∧
      ∀ α : ℝ, 0 < α → ∀ C : ℝ, ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧
        C * w U t ^ α < expSqErr a fairCoin t ∧ C * w U t ^ α < expAbsErr a fairCoin t := by
  sorry

end P27Spikes

/- Fidelity note.
Source: `pro/020-p27-expected.a.md` §6, Theorem 6, eq. (37): ∃ M ∈ 𝓑 ∀α > 0: limsup_t S_t(M, λ)/w_t^α = ∞, and
the same for A_t. Referee `docs/reviews/2026-11-21-referee-020b.md` (correct with minor gaps; the proof gives
"one of two priors", so the statement must be existential). Book question (2.7): "an upper bound better than
O(2^{-K(t)})" and "for which sequences does equality ≍ 2^{-K(t)} hold?".
- Class: the Lean statement asks for M in the root-1 universal class (`IsUniversal`, as in P27Stochastic), not
  for M ∈ 𝓑 (a Solomonoff prior of a universal monotone machine); upstream has no monotone-machine prior class.
  The 𝓑 membership is a paper fact (Wood-Sunehag-Hutter Def. 2; novelty check confirmed it).
- `w U t ^ α` is `Real.rpow` (α : ℝ). "limsup = ∞" is written as: for every C and T some t ≥ T has
  S_t > C·w_t^α. One t serves both errors: for the fair coin s_t(x) = 2d² ≤ 2|d| = a_t(x), so S_t ≤ A_t at
  every t. This is no strengthening.
- B(n) is defined from the same `U` as `w`, so (39) holds exactly.
- `no_power_upper_bound_mix` (∀ universal V ∃ ν: ½V + ½ν has the spikes) is the stronger form; Lean then
  certifies the 𝓑 claim up to the paper step "𝓑 is closed under ½V + ½ν for lsc ν".
- Review: docs/reviews/2026-11-21-fidelity-27-spikes.md (faithful with caveats).
- µ = fair coin (`fairCoin`, conditionals 1/2). Not stated: the pathwise claim (realized errors on a set of
  λ-probability ≥ 1/2).
- Scope: shows that an upper bound O(2^{-αK(t)}) fails for some universal M; it does not say every M fails.
-/
