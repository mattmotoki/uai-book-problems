/- Frozen target (desk, 2026-11-21): Theorem 1 of Pro 020b, Problem 2.7 stochastic.
   Fidelity note at the end. `sorry` is allowed only in Targets/. -/
import HutterPrizes.P27F
import HutterPrizes.P33Effective

open scoped BigOperators ENNReal
open Kolmogorov Kolmogorov.SelectedBits

namespace P27Stochastic

/-! Statement layer. -/

/-- The true environment µ, given by computable rational next-bit conditionals `r x = µ(1 | x)`. -/
def muCond (r : BitString → ℚ) (x : BitString) (b : Bool) : ℝ :=
  if b then (r x : ℝ) else 1 - (r x : ℝ)

/-- µ(x) as the product of its conditionals along x. -/
def muProb (r : BitString → ℚ) : BitString → ℝ
  | [] => 1
  | x => (List.range x.length).foldl
      (fun p i => p * muCond r (x.take i) (x.getD i false)) 1

/-- Expected one-step L1 error of the normalized predictor `a_norm` at time `t` (history length t-1):
  A_t = Σ_{|x| = t-1} µ(x) Σ_b |a_norm(b|x) − µ(b|x)|. -/
noncomputable def expAbsErr (a : BitString → ℝ≥0∞) (r : BitString → ℚ) (t : ℕ) : ℝ :=
  ∑ v : Fin (t - 1) → Bool, muProb r (List.ofFn v) *
    ∑ b : Bool, |normalizedSiblingProb a (List.ofFn v) b - muCond r (List.ofFn v) b|

/-- Expected one-step squared error: S_t = Σ_{|x| = t-1} µ(x) Σ_b (a_norm(b|x) − µ(b|x))². -/
noncomputable def expSqErr (a : BitString → ℝ≥0∞) (r : BitString → ℚ) (t : ℕ) : ℝ :=
  ∑ v : Fin (t - 1) → Bool, muProb r (List.ofFn v) *
    ∑ b : Bool, (normalizedSiblingProb a (List.ofFn v) b - muCond r (List.ofFn v) b) ^ 2

/-- 2^{-K(t)} with K(t) = KPNat U t, the same K on naturals as `HutterPrizes.normalized_lower_bound`. -/
noncomputable def w (U : Map) (t : ℕ) : ℝ := ((2 : ℝ)⁻¹) ^ (KPNat U t).toNat

/-- Theorem 1 of 020b: for every universal lsc semimeasure M and every computable µ (rational
conditionals), the expected errors of the normalized M reach c·2^{-K(t)} (L1) and (c²/2)·2^{-2K(t)}
(squared) at some time in every late dyadic block (2^n, 2^{n+1}]. -/
theorem expected_lower_bound_io (U : Map) (hU : IsOptimalPrefixConditional U)
    (a : BitString → ℝ≥0∞) (ha : IsLowerSemicomputableContinuousSemimeasure a)
    (hua : P33Effective.IsUniversal a)
    (r : BitString → ℚ) (hr : Computable r) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ t : ℕ, 2 ^ n < t ∧ t ≤ 2 ^ (n + 1) ∧
      c * w U t ≤ expAbsErr a r t ∧ c ^ 2 / 2 * w U t ^ 2 ≤ expSqErr a r t := by
  sorry

end P27Stochastic

/- Fidelity note.
Source: Hutter (2005) Problem 2.7 (book text in the scratch extract, line ~4183): the bound for M,
Σ_{x_t}|M(x_t|x<t) − µ(x_t|x<t)| ≥ defect ≳ 2^{-K(t)} for all t and x<t; question: "Do similar lower
performance bounds hold for M_norm ... which has no defect?" Pro 020b Theorem 1 answers the expected,
infinitely-often form. Referee: docs/reviews/2026-11-21-referee-020b.md.
- Class: M ranges over upstream root-1 lsc continuous semimeasures that dominate every such semimeasure
  (`IsUniversal`); this includes `universalContinuousSemimeasure`. Book's ν(ε) ≤ 1 (paper argument, not
  in Lean): set ν′(ε) = 1, ν′ = ν elsewhere; ν′ is an lsc root-1 semimeasure, and normalizedSiblingProb
  never reads the root, so the root-1 class loses no M and no dominated ν.
- µ: computable rational next-bit conditionals. Narrower than "every computable measure" (real-valued
  computable conditionals); any wording must say "rational conditionals".
- Quantifiers: c and n₀ depend on U, M, µ; t depends on n. The same t satisfies both bounds.
- K(t) = KPNat U t, as in P27F. `toNat` of ⊤ is 0; KPNat is finite for optimal U.
- Weaker than the book's M bound: expected (not pointwise) and once per dyadic block (not every t).
  For every t the expected version is open (020b §4). A uniform all-history lower bound fails for one
  symmetrized M ∈ 𝒜 (desk fact: pro/020-p27-expected.q.md l.12); 020b does not prove this; open for 𝓑.
  Does not address Hutter's question about equality.
- Review: docs/reviews/2026-11-21-fidelity-27-stochastic.md (faithful with caveats).
- normalizedSiblingProb a x b = a(xb)/(a(x0)+a(x1)); positive denominators since M is universal.
-/
