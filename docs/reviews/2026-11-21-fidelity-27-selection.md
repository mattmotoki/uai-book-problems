# Fidelity review: `Targets/P27Selection.lean` (023 Theorem 1, Corollary 2), 2026-11-21

Fresh-context reviewer (Claude Opus subagent), read-only. **Verdict: faithful with caveats.** Neither statement
is false or vacuous.
- `ell`, `B` match (17) (#eval: ℓ = 6, 12, 12, 18, …; B = 0, 12, 24, 42, …). Block n holds ℓ_n indices; at n = 0
  it is empty and n₀ ≥ 1 handles it. d j for j ≥ 1 is the source's d_j.
- Quantifiers match (18) and (26); one t satisfies both bounds.
- Window C·(⌊log₂(u+2)⌋+1) agrees with ⌈C log₂(u+2)⌉ up to the constant.
- Constant 6 is safe: K(n) ≤ 2 log₂(n+1) + O(1) gives w_n ≳ (n+1)^{-2}; forced mass ≤ (n+2)^{-6}.
- Fixed: `hd1 : 1 ≤ d 0` removed (it excluded d_j = j). Note now lists what is not stated (eq. 27, Cor. 1,
  Thm 2, every computable µ).
- Proof hint: eq. (24) needs a coding lemma for blocks along a general d (lsc g route).

Accepted claim: "For every universal lower semicomputable semimeasure M (root-1 class) and every computable µ
with rational next-bit conditionals: for every computable strictly increasing sequence of times d, there is
c > 0 such that each late block {d_j : B_{n−1} < j ≤ B_n}, with ℓ_n = 6⌈log₂(n+2)⌉, contains a time t where the
normalized predictor has A_t ≥ c·2^{−K(t)} and S_t ≥ (c²/2)·2^{−2K(t)}. The constant c depends on d. In ordinary
time, such a time occurs in every late window [u, u + O(log u)]."

Desk name check on the proved theorems (2026-11-21, `#check` with pp.fullNames after importing
`HutterPrizes.P27Selection`): `expected_lower_bound_io`, `selection_lower_bound`, `log_window_lower_bound` use
`Kolmogorov.Map`, `Kolmogorov.IsOptimalPrefixConditional`, `Kolmogorov.IsLowerSemicomputableContinuousSemimeasure`,
`P33Effective.IsUniversal`, root `Computable`, root `StrictMono`, `P27Stochastic.w` (= 2⁻¹ ^ (Kolmogorov.KPNat U t).toNat),
`P27Stochastic.expAbsErr`/`expSqErr` (via `Kolmogorov.SelectedBits.normalizedSiblingProb`, `muProb`, `muCond`),
`P27Selection.B`/`ell`. No helper shadows a statement name.
