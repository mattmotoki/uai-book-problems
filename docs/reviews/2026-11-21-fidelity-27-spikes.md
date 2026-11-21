# Fidelity review: `Targets/P27Spikes.lean` (020b Theorem 6), 2026-11-21

Fresh-context reviewer (Claude Opus subagent), read-only. **Verdict: faithful with caveats.** True by the report's
proof; not false, not vacuous (Theorem 4 gives Σ S_t < ∞, so spikes need complex times).
- Witness ½V + ½ν_i is root-1 (ν_i(ε) = Σγ_n = 1), lsc (B(n) enumerable from
  `isUniformlyLSC_complexityWeight_KPNat`; use a strict test), and `IsUniversal` (≥ ½V). B uses the same U as w,
  so (39) holds exactly.
- ∀C ∀T ∃t ≥ T is "limsup = ∞" since w > 0. One t serves A_t and S_t (S_t ≤ A_t for the fair coin). Pigeonhole:
  one i for infinitely many n, t_n → ∞, (49) has no α, so one M serves every α.
- Edge cases fine (C ≤ 0, t = 0, `KPNat_ne_top`). (45)-(48) checked line by line.
- Adopted: stronger form `no_power_upper_bound_mix` (∀ universal V ∃ ν), note fixes B and C.

Accepted claim: "For every optimal prefix machine U there is a universal lower semicomputable semimeasure M (root
1) such that, for the fair coin, for every α > 0 and every C, infinitely many t have expected one-step squared and
L1 errors of M_norm above C·2^{-αK(t)}. So no positive power of 2^{-K(t)} is an upper bound valid for all
universal M. It is about one M, not every M. M ∈ 𝓑 (a Solomonoff prior) by a paper argument (Wood-Sunehag-Hutter)
that Lean does not check. The pathwise form is not stated."

Desk name check on the proved theorems (pp.fullNames): `Kolmogorov.IsOptimalPrefixConditional`, `Kolmogorov.IsLowerSemicomputableContinuousSemimeasure`, `P33Effective.IsUniversal`, `P27Stochastic.w`, `P27Stochastic.expSqErr`/`expAbsErr`, `P27Spikes.fairCoin`. The `let a` prints as `have a := …`; the body is applied to that function, so the claims are about ½V + ½ν.
