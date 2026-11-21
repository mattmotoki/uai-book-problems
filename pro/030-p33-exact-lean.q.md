# Lean proof: Problem 3.3 with exact 2^{-K(i)} weights under two optimal prefix machines (target P33Exact)

## Goal and reason
We answer Hutter's Problem 3.3 ("Comparing two mixtures", UAI 2005) negatively. Lean already proves it with weights
within constant factors of 2^{-K(i)} (`P33Complexity`, attached). The strongest index-convention version uses the
exact universal weights 2^{-K_C(i)}, the two mixtures differing only in the reference machine C (your reports 008
Theorem 6 and 027 Theorem 5). A fidelity review accepted the target.

## Task
Prove `P33Exact.exact_counterexample` in the attached `P33Exact.lean` (repo path `Targets/P33Exact.lean`). Keep the
definition `exactMixture` and everything above the theorem's `:= by` character for character (we diff them). Add any
helpers. Return one complete file `HutterPrizes/P33Exact.lean` (namespace `P33Exact`), compiling with Lean 4.35.0,
Mathlib v4.35.0, kolmogorov-complexity-lean commit 17c50e560c337a8a702f8850a711f80a56b3cf91, with no sorry, admit,
axiom, or native_decide.

## Context you cannot find yourself
- Planned design (the reviewer checked it; use another if it is easier):
  - Fix an optimal prefix machine U0 (upstream `exists_isOptimalPrefixConditional`) and L = 30 (L ≥ 21 is needed).
  - R x := Σ_i 2^{-L-K_{U0}(i+4)} · treeLSCEnum i x; background M := (2^21 − 2)·R (positive via lengthMeasure, root ≤ 1).
    P, Q := root-one splices of M as in `P33Complexity` (rootSplice / rawSplice).
  - τ_0 = τ_1 = P, τ_2 = τ_3 = Q, τ_{i+4} = treeLSCEnum i. Renumbering: f i = i + 4; g = (p, p, q, q, i − 4) with p, q
    the treeLSCEnum indices of P, Q (`treeLSCEnum_complete`).
  - C⁻ on (program, condition y): codes 0000 ↦ index 0, 0001 ↦ index 1, 01 ↦ index 2, 001 ↦ index 3 (any prefix-free
    assignment with lengths 4,4,2,3 starting with 0), independent of y; 1^L·p ↦ U0(p, y). C⁺: lengths 2,3,4,4 on
    indices 0-3. Then KPNat C± i = L + KPNat U0 i for i ≥ 4 exactly (short codes are shorter than L, so no filter is
    needed), and ξ⁻ = P/8 + 3Q/8 + R', ξ⁺ = 3P/8 + Q/8 + R' with the same R'. On nonempty histories ξ± is a positive
    multiple of `xi M ∓`, so `RobustExperiment.Theorem4.theorem4` gives n^{1/4}/256 for n ≥ 2.
- Lemmas the reviewer found missing upstream: a positive-scale lemma for `loss` (predict compares s(h0) with s(h1));
  uniform lsc of i ↦ complexityWeight (KPNat U0 (i+4)) and a piecewise uniform-lsc lemma for τ.
- Optimality of C±: conditional KP domination with constant max(c + L, 4) for every condition y; prefix-freeness:
  short codes start with 0, long programs are 1^L·dom U0(·, y).
- The attached `helpers-from-review.lean` (compiled) shows that the children, root, IsLSC and ratio-type clauses
  follow for any optimal C and uniformly lsc root-1 τ; reuse it.

## Done
The complete file in one ```lean block, then a short list of the main lemmas and any deviation from the design.
