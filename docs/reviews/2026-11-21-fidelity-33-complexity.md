# Fidelity review: `Targets/P33Complexity.lean` (3.3 with 2^-K(i) weights), 2026-11-21

Fresh-context reviewer (Claude Opus subagent), read-only. **Verdict: faithful with caveats.** Plausibly true;
no statement change needed.
- Names resolve (pp.fullNames): `Kolmogorov.complexityWeight`, `KPNat U i` = KP of the index, `treeLSCEnum`,
  `IsLSC`, `bayesMixture`, `loss`, `source`, `transport`.
- K(ν) as K(i): the book itself says "K(ν_i) := K(i)" (p. 48) for M_U; constant-factor weights fit "w_ν ∼ 2^{-K(ν)}"
  (p. 67). Claim must say "complexity of the index".
- Root/sum clauses redundant but harmless; Σ w ≤ 1 is book-supported (p. 49, Problem 3.1). `predict` is
  scale-invariant and never reads level 0.
- Truth: background Σ 2^{-K(i)} ν_i satisfies `Background` (Kraft, `KPNat_ne_top`, `lengthMeasure`).
- Proof path (medium): P, Q have root < 1, so `treeLSCEnum_complete` needs root-1 versions; loss reads levels ≥ 1.
- Do not claim: w = 2^{-K(ν)}, "Hutter's prior" unqualified, Σ w = 1, computable weights; the earlier full-M_U
  paper step does not carry over.

Accepted claim: "Fix an optimal prefix machine U and the fixed enumeration ν₀, ν₁, … (with repetitions) of all lower
semicomputable semimeasures with ν(ε) = 1. There are weights w⁻, w⁺ with c·2^{-K(i)} ≤ w±_i ≤ C·2^{-K(i)} (K(i) the
prefix complexity of the index i; 0 < c ≤ C < ∞ depending on U), Σ_i w±_i ≤ 1 and w⁻_i/w⁺_i ∈ [1/3, 3], such that
both mixtures ξ± = Σ_i w±_i ν_i are lower semicomputable, and an index j with ν_j = µ a computable probability
measure. For binary 0-1 loss, ties toward 1, L_n^{Λξ⁻} − L_n^{Λξ⁺} ≥ n^{1/4}/256 for all n ≥ 2, and the difference
tends to +∞." Paper steps: all weights positive; both mixtures universal.

Desk name check on the proved theorem (pp.fullNames): `Kolmogorov.complexityWeight`, `Kolmogorov.KPNat`,
`Kolmogorov.treeLSCEnum`, `Kolmogorov.IsLSC`, `P33Mixture.bayesMixture`, `RobustExperiment.loss`, `RobustExperiment.prob`,
`RobustExperiment.Theorem4.source`, `P33Effective.transport`/`toBitString`. Definition and signature identical to the target.
