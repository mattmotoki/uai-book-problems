# Research: Hutter (2005) Problem 2.7 (lower convergence bounds and defect of M), the stochastic version

Problem 2.7 (book; prize €100) asks for a lower bound for the normalized M_norm like the one for M
(1 − M(x_t|x_<t) ≥ d_M(x_<t) ≥ c·2^{-K(t)}), or an upper bound better than O(2^{-K(t)}).

What this project already has:
- Lean-checked (2.7F): for every universal enumerable semimeasure M (library version), ∃C ∀x,b:
  NM(b|x) ≥ 2^{-(K(|x|+1)+C)}.
- Known (Leike-Hutter 2015, "Solomonoff induction violates Nicod's criterion", Lemmas 6 and 10, as read by
  an earlier session): for computable deterministic z, 1 − NM(z_t|z_<t) = Θ(2^{-K(t)}). So no better upper
  bound exists on deterministic sequences.
- False: a positive discrepancy lower bound uniform over all histories (an automorphism-symmetrized universal
  M gives NM(1|0^j1) = 1/2 exactly).

Open, stochastic versions. Work as a research mathematician:
1. Expected lower bound. For M ∈ 𝓑 (Solomonoff M_U) or M ∈ 𝒜, and computable μ (not deterministic):
   is E_μ Σ_b (NM(b|X_<t) − μ(b|X_<t))² ≥ c·2^{-2K(t)} for all large t, or for infinitely many t? Same with
   absolute error and c·2^{-K(t)}. Prove, refute (e.g. by symmetrization tricks that hit μ-typical histories),
   or find the right quantifiers. Compare with the unnormalized M, where E_μ d_M(X_<t) ≥ c·2^{-K(t)} follows
   from the defect bound.
2. Upper bound. For computable μ, the summed expected squared error of NM is finite, so per-step errors are
   o(1/t) on average. Is there a better per-step bound than O(2^{-K(t)}) for stochastic μ, e.g. along
   μ-typical paths, or for the expected error? Is the O(2^{-K(t)}) defect-driven term the bottleneck?
3. Novelty: is 2.7F (NM(b|x) ≥ c·2^{-K(|x|+1)} for every x, b and every universal M) stated in Leike-Hutter
   2015 or elsewhere? Quote it if so (arXiv 1507.04121 and the Nicod paper).
State each claim as a theorem with quantifiers; full proofs; mark confidence and novelty; cite sources you opened.
