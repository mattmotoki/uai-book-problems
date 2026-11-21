# Fidelity review: `P33Mixture.mixture_counterexample` (Problem 3.3), 2026-11-21

Fresh-context reviewer (Claude Opus subagent), read-only; ran `#print` with `pp.fullNames`.
**Verdict: faithful with caveats.** Statement equals the frozen `Targets/P33Mixture.lean`.

1. Names resolve to `Kolmogorov.treeLSCEnum`, `Kolmogorov.IsLowerSemicomputableContinuousSemimeasure`,
   `RobustExperiment.Theorem4.source`, `RobustExperiment.loss`, `RobustExperiment.prob`, `P33Effective.transport`.
2. Class: `treeLSCEnum` lists every root-1 lsc continuous semimeasure (with repetitions), like the book's M_U
   (p. 48, "ordered multi set"). Weights match (3.5): Σw = 1, all w > 0. µ = ν_j with w±_j > 0. Paper step:
   the book allows ν(ε) ≤ 1; the loss never reads ε, so the same mixtures are mixtures over the full M_U.
   The 1/3-3 ratio gives ξ₋ ≤ 3ξ₊ and ξ₊ ≤ 3ξ₋: mutually dominating mixtures, unbounded gap (one line, not in Lean).
   Out of scope: M_comp, 2^-K(ν) weights, ξ_U.
3. Reused definitions pass: `predict` = Λ_ρ (3.45) for 0-1 loss; `loss N` = (3.46) over steps 1..N; `source`
   is the intended measure (trunk fair; branch j: 16^j bits with P(1) = 1/2 + 1/(32·4^j)).
4. Ties: proved for ties toward 1 only (valid Λ_ξ, footnote 6, p. 87). For any tie rule each step's gap is
   ≥ 0; it shrinks only at exact ties of ξ₊ inside a window broken toward 0 (mass not bounded in Lean).
   `P33Counterexample` breaks ties toward 0: give each theorem its own rule.
5. Risks: Sec. 3.2.2 (p. 70) has M as probability measures; for that reading cite
   `MixtureCounterexample.counterexample` (two computable measures, gap ≥ (1/32)H_n). Explain the L_∞ reading.
   n^{1/4} agrees with the O(√L) bound. Do not call the weights universal or computable.

Claim sentence (Lean-checked): "Let ν₀, ν₁, … be an enumeration, with repetitions, of all lower semicomputable
semimeasures with ν(ε) = 1. There are weights w⁻, w⁺ with all w±_i > 0, Σ_i w±_i = 1 and w⁻_i/w⁺_i ∈ [1/3, 3],
such that both mixtures ξ± = Σ_i w±_i ν_i are lower semicomputable, and an index j such that ν_j = µ is a
computable probability measure with rational conditionals. For binary 0-1 loss, with ties broken toward 1,
L_n^{Λξ⁻} − L_n^{Λξ⁺} ≥ n^{1/4}/256 for all n ≥ 2, and the difference tends to +∞."
Paper addition: "The same mixtures are Bayes mixtures over the book's M_U (ν(ε) ≤ 1) with positive weights."
