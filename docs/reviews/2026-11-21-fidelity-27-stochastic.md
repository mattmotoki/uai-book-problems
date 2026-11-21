# Fidelity review: `P27Stochastic.expected_lower_bound_io` (target), 2026-11-21

Fresh-context reviewer (Claude Opus subagent), read-only; compiled scratch checks with pp.fullNames.
**Verdict: faithful with caveats.** Matches Theorem 1 of 020b and looks true as written.

- Names resolve as the note says. `KPNat_ne_top hU` holds upstream, so `toNat ⊤` cannot occur.
  Universality against `lengthMeasure` gives a(x) > 0; a(x) ≤ 1.
- `muProb`, `expAbsErr`, `expSqErr` compute µ(x), A_t, S_t with history length t−1 (compiled test: A_2 = 1/2
  for a parity test µ). t = 0 edge has no effect (t > 2^n ≥ 1). µ-null histories have weight 0.
- Quantifiers match 020b (6): ∀U, M, µ ∃c > 0 ∃n₀ ∀n ≥ n₀ ∃t ∈ (2^n, 2^{n+1}], one t for both bounds.
- Truth: class non-empty (`universalContinuousSemimeasure_isMaximal`); `IsUniversal` constant ≥ 1; mixture R
  must be renormalized to root 1 (upstream `KPNatWeightedTreeMixture` does this); rational conditionals make
  Step 1 exact; S_t ≥ A_t²/2 since the weights sum to 1.
- Fixed in the note (A, medium): the pointwise failure is a desk fact for one symmetrized M, not 020b §7.
  (B, low): the ν(ε) ≤ 1 paper argument written out. (C) every claim must say "rational conditionals".
  (D, cosmetic) the `[]` branch of `muProb` is redundant.

Accepted claim sentence: "For every optimal prefix machine U, every universal lower semicomputable
semimeasure M, and every computable measure µ with rational next-bit conditionals, there is c > 0 (depending
on U, M and µ) such that in every sufficiently late dyadic block (2^n, 2^{n+1}] some t has µ-expected one-step
L1 error of M_norm at least c·2^{-K(t)} and µ-expected squared error at least (c²/2)·2^{-2K(t)}. This is a
partial answer to the first question of Problem 2.7; the every-large-t version is open, and the equality
question is not addressed."

Desk name check on the proved theorems (2026-11-21, `#check` with pp.fullNames after importing
`HutterPrizes.P27Selection`): `expected_lower_bound_io`, `selection_lower_bound`, `log_window_lower_bound` use
`Kolmogorov.Map`, `Kolmogorov.IsOptimalPrefixConditional`, `Kolmogorov.IsLowerSemicomputableContinuousSemimeasure`,
`P33Effective.IsUniversal`, root `Computable`, root `StrictMono`, `P27Stochastic.w` (= 2⁻¹ ^ (Kolmogorov.KPNat U t).toNat),
`P27Stochastic.expAbsErr`/`expSqErr` (via `Kolmogorov.SelectedBits.normalizedSiblingProb`, `muProb`, `muCond`),
`P27Selection.B`/`ell`. No helper shadows a statement name.
