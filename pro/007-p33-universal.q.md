# Research question: does the Problem 3.3 counterexample survive for two *universal* mixtures?

## Background

Hutter, *Universal Artificial Intelligence* (2005), Problem 3.3 (p. 120): for two mixtures ξ, ξ' over a
class M with true μ ∈ M, the known bound is L^ξ_n − L^ξ'_n ≤ O(√L^ξ'_n); the question is whether
L^ξ − L^ξ' < ∞.

We have a Lean-checked counterexample for a finite class: M = {μ, ν} with independent bits,
μ(1) = 1/2 + 1/(32t), ν(1) = 1/2 − 1/(32t), ξ₋ = ¼μ + ¾ν, ξ₊ = ¾μ + ¼ν, 0-1 loss; under μ,
L^{ξ₋}_n − L^{ξ₊}_n ≥ (1/32) Σ_{t≤n} 1/t → ∞. The mechanism: the posterior odds R_n = ν(x)/μ(x) stay in a
bounded interval with probability bounded away from 0 (E R_n² bounded), and on that event the two
mixtures make different 0-1 decisions, each costing 2δ_t.

A reviewer noted that this does not cover the case Hutter most likely cares about: M = all computable (or
enumerable semi-) measures, ξ and ξ' two universal mixtures with different positive weights (for example
Solomonoff's M_U and M_V for two universal machines, or ξ_U with two weight functions w, w' both
≈ 2^{-K(ν)}).

## What I want

1. Does the finite-class counterexample lift to two universal mixtures over the class of all computable
   measures (or all enumerable semimeasures), with μ computable? Take μ as above. The obvious route: let
   ξ = w_μ μ + w_ν ν + (rest) and ξ' with the same rest but swapped mass on μ, ν. Then the "rest" also
   contributes to the posterior. Is the rest's posterior weight negligible under μ (it should shrink,
   since μ is ML-random-ish for its own paths, but universal mixtures keep weight on every computable
   measure close to μ)? State precisely what you need and prove it, or show where it breaks.
2. If it lifts, give a precise theorem: quantifiers, what is universal, what loss, and the rate of the
   divergence. If it does not lift directly, find the strongest version that does (e.g. ξ, ξ' universal
   mixtures over a countable class of computable Bernoulli product measures; or universal over all
   computable measures but with weights chosen adversarially).
3. Is there a regime where the answer flips to "yes" (L^ξ − L^ξ' bounded) for universal mixtures, e.g. for
   deterministic μ or for losses with a margin? Hutter's Corollary 3.49 (finite L^μ ⇒ finite L^ξ) is the
   trivial case; anything beyond it?
4. Sketch what a Lean formalization of your main theorem would need, given that we already have finite
   definitions (Model as conditional probabilities on histories, Prior, mixCond, Bayes 0-1 predictor,
   expected loss under μ) and the kolmogorov-complexity-lean library (universal semimeasure, computable
   measures).

Say for each claim whether you proved it, and how confident you are. Search for prior work on comparing
the losses of two Bayes mixtures (merging of opinions, Blackwell-Dubins, "difference of regrets") and
cite with arXiv IDs or DOIs.
