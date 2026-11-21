# Fidelity review: Targets/P33Measures.lean, 2026-11-21

Fresh-context reviewer (Claude Opus subagent). **Verdict: faithful with caveats; none blocks proof work.**

1. Names resolve (pp.fullNames) to RobustExperiment.loss, RobustExperiment.Theorem4.source,
   P33Effective.transport/toBitString, P27Stochastic.muProb.
2. Class: probability measures with a *total* computable rational conditional r into [0,1]. Possibly smaller
   than 027's second class (conditionals only at positive-mass histories); harmless, since the book needs only some
   countable M containing µ. Indexing by r is harmless: priors on distinct measures lift to indices and back.
3. µ clause fixes µ.1 completely (toBitString onto per length); compiled `mu_mass`: muProb µ (toBitString h) =
   prob source n h.
4. 027's weights meet every clause with η = 2^-20. Non-vacuity: compiled `ratMeasure_countable` and
   `exists_positive_prior` (scratch Count2.lean; copied to pro/029 question).
5. Truth: M.mass := transport (classMixture a) is a positive Background (fair coin r ≡ 1/2 ∈ C). Simpler proof
   route: T±ν copies ν's selector, runs the experiment, then fair bits (no restart; injectivity unneeded since
   A±(ρ) sums a over fibers); then transport (classMixture w±) = xi± M and theorem4 applies.
6. Note fixes: "total" r; w± are not claimed to be a; ties toward 1.

Accepted claim: "Let C be the countable class of probability measures on binary sequences given by a total
computable r : {0,1}* → ℚ ∩ [0,1] with ν(1|x) = r(x), indexed by r. There is µ ∈ C, independent of the prior, such
that for every prior a on C with all a_ν > 0 and Σ a_ν = 1 there are priors w⁻, w⁺ on C, depending on a, strictly
positive, each summing to 1, with w± ≥ 2^-20·a and w⁺_ν/w⁻_ν ∈ [1/3, 3], such that for ξ± = Σ w±_ν ν, binary 0-1 loss
and Bayes actions with ties toward 1, L_n^{ξ⁻} − L_n^{ξ⁺} ≥ n^{1/4}/256 for all n ≥ 2. No computability claim for
w± or ξ±. All computable measures: paper step."

Desk check of the proof (029): definitions and theorem identical to the target; pp.fullNames names RobustExperiment.loss,
RobustExperiment.Theorem4.source(.cond), P33Effective.transport/toBitString, P33Measures.classMixture; check PASS.
