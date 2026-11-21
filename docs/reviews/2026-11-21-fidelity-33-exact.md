# Fidelity review: Targets/P33Exact.lean, 2026-11-21

Fresh-context reviewer (Claude Opus subagent). **Verdict: faithful with caveats; plausibly true; no blocker.**
- Names resolve; IsOptimalPrefixConditional forces Partrec, prefix-free domain per condition, conditional KP
  domination; KPNat C i ≠ ⊤ (prefixIndexComplexity_ne_top), so no weight is 0.
- Content: exhaustiveness, optimality, source ∈ τ, loss gap. Children/root/IsLSC/bounded-ratio follow for any optimal C
  and uniformly lsc root-1 τ (scratch proof G.lean).
- Reading: two mixtures with the same class and enumeration, differing only in the reference machine: faithful to ξ_U
  in 3.3 under the index convention K(ν_i) := K(i).
- Caveats (applied by the desk): L1 ratio clause was implied → now per-index ratio ≤ 4; L2 add IsUniversal; L3 τ is a
  computable renumbering of treeLSCEnum (f, g); L4 note describes the four-index design.
- Design gaps to cover in the proof: L ≥ 21 (M = (2^21 − 2)·R root ≤ 1); a positive-scale lemma for loss; uniform lsc
  of i ↦ complexityWeight (KPNat U0 (i+4)) and of τ piecewise; divergence filter unnecessary when L > 4.
Accepted claim: "There are an effective (uniformly lsc) enumeration τ of all lower semicomputable semimeasures with
ν(ε) = 1, with repetitions, and two optimal prefix machines C⁻, C⁺, such that the mixtures ξ± = Σ_i 2^{-K_{C±}(i)} τ_i
are lower semicomputable semimeasures, K_C(i) the exact prefix complexity of the index i. For the computable source
µ = τ_j, binary 0-1 loss and ties toward 1, L_n^{ξ⁻} − L_n^{ξ⁺} ≥ n^{1/4}/512 for all n ≥ 3, → +∞." Not for every
pair of machines, the standard enumeration, or semantic weights 2^{-K(ν)}.

Desk check of the proof (030): definition and theorem identical to the target; pp.fullNames names upstream Kolmogorov.* (KPNat, complexityWeight, IsOptimalPrefixConditional, treeLSCEnum, IsUniformlyLowerSemicomputableTreeFamily), P33Effective.IsUniversal/transport/toBitString, RobustExperiment.loss/prob, Theorem4.source; check PASS.
