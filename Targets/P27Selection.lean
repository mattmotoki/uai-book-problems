/- Frozen target (desk, 2026-11-21): Theorem 1 and Corollary 2 of Pro 023 (Problem 2.7, eventual question),
   in the setting of `Targets/P27Stochastic.lean` (rational conditionals). Fidelity note at the end. -/
import HutterPrizes.P27Stochastic

open scoped BigOperators ENNReal
open Kolmogorov Kolmogorov.SelectedBits P27Stochastic

namespace P27Selection

/-- Block lengths ℓ_n = 6⌈log₂(n+2)⌉, written with `Nat.clog`. -/
def ell (n : ℕ) : ℕ := 6 * Nat.clog 2 (n + 2)

/-- B_n = Σ_{k=1}^{n} ℓ_k (so B_0 = 0). -/
def B (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, ell k

/-- 023 Theorem 1: along every computable strictly increasing selection of times d_1 < d_2 < ⋯ (d 0 is not
used), every
late selection block F_n = {d_j : B_{n-1} < j ≤ B_n} contains a time t with A_t ≥ c·2^{-K(t)} and
S_t ≥ (c²/2)·2^{-2K(t)}. -/
theorem selection_lower_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (a : BitString → ℝ≥0∞) (ha : IsLowerSemicomputableContinuousSemimeasure a)
    (hua : P33Effective.IsUniversal a)
    (r : BitString → ℚ) (hr : Computable r) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (d : ℕ → ℕ) (hd : Computable d) (hmono : StrictMono d) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ j : ℕ, B (n - 1) < j ∧ j ≤ B n ∧
      c * w U (d j) ≤ expAbsErr a r (d j) ∧ c ^ 2 / 2 * w U (d j) ^ 2 ≤ expSqErr a r (d j) := by
  sorry

/-- 023 Corollary 2: a witness in every late window of length O(log u). -/
theorem log_window_lower_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (a : BitString → ℝ≥0∞) (ha : IsLowerSemicomputableContinuousSemimeasure a)
    (hua : P33Effective.IsUniversal a)
    (r : BitString → ℚ) (hr : Computable r) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C T : ℕ, ∀ u, T ≤ u → ∃ t : ℕ, u ≤ t ∧ t ≤ u + C * (Nat.log 2 (u + 2) + 1) ∧
      c * w U t ≤ expAbsErr a r t ∧ c ^ 2 / 2 * w U t ^ 2 ≤ expSqErr a r t := by
  sorry

end P27Selection

/- Fidelity note.
Source: `pro/023-p27-eventual.a.md` §3 (Theorem 1, eq. (17)-(18); Corollary 2, eq. (26)); referee
`docs/reviews/2026-11-21-referee-023.md` (correct). Definitions `expAbsErr`, `expSqErr`, `w`, the classes of M
and µ, and the K on naturals are those of `Targets/P27Stochastic.lean` (reviewed: faithful with caveats).
- Selection: d computable, strictly increasing. The report indexes d_1 < d_2 < ⋯; here j ranges over
  B_{n-1} < j ≤ B_n, so d 0 is never used in a block, and StrictMono gives d j ≥ j ≥ 1.
- ⌈log₂(n+2)⌉ = `Nat.clog 2 (n + 2)`. In Corollary 2 the window ⌈C log₂(u+2)⌉ is written C·(⌊log₂(u+2)⌋+1)
  with C : ℕ; the two forms agree up to the constant.
- Quantifiers: c, n₀ depend on U, M, µ and d (no uniform c over selections; referee). In Corollary 2,
  c, C, T depend on U, M, µ.
- µ has rational conditionals (as in P27Stochastic); the report covers every computable µ (smoothing (19)).
  Corollary 1 (every infinite c.e. set) is a computability step from Theorem 1, not stated here.
- Not stated: eq. (27) (Ω(N/log N) witnesses up to N), Corollary 1, Theorem 2, every computable µ.
- Partial answer only: (E) "for every large t" stays open.
- Review: docs/reviews/2026-11-21-fidelity-27-selection.md (faithful with caveats; hd1 removed).
-/
