# Status map of the open prize problems in Hutter's *Universal Artificial Intelligence* (2005)

I am starting a research project that attacks the open problems that carry prizes in Marcus Hutter's
book *Universal Artificial Intelligence* (Springer 2005), with an LLM proposing proofs and Lean 4
checking them. Before any proof work, I need an accurate map of what is still open. The attached PDF
holds the book pages with the problems and the definitions they cite (Sections 2.4, 2.6, 3.2, 3.4 parts,
3.11, 6.2.2 and 6.7; 36 pages).

## The prizes (from https://www.hutter1.net/ai/uaibook.htm#prizes, read 2026-11-20)

- Problem 2.3 (Martin-Löf random sequences and convergence), €100: "construction of a universal
  semimeasure with posterior convergence individually for all Martin-Löf random sequences". Universal
  may mean (a) dominating all enumerable semimeasures, Eq. (2.27); (b) Solomonoff's M for some
  universal TM U, Eq. (2.21); (c) Levin's mixture ξ_U for some U with general weights, Eq. (2.26).
  See also Problem 3.10.
- Problem 2.7 (Lower convergence bounds and defect of M), €100: "showing a lower bound for M_norm
  similar to the one given for M, or for showing an upper bound better than O(2^-K(t))". The page also
  says the solutions to Problems 2.5, 2.6u and 2.7u were TeXed in 2005.
- Problem 2.9 (Prediction of selected bits), €100 + €100: M_norm question, and a positive solution
  for general computable selection rules. The page says: "This problem has now been solved [P11evenbits]".
- Problem 3.3 (Comparing two mixtures), €50. The book asks: is L^ξ − L^ξ' < ∞ true (finite difference
  of the cumulative losses of two Bayes mixtures over the same class)?
- Problem 6.2 (Prediction loss bounds for AIξ), €100–500: generalize or improve bound (6.17) to
  (a) general losses, (b) probabilistic passive environments, (c) horizon h_k > 1, (d) bounds linear or
  polynomial in K(z), or show impossibility. "Prize depends on achieved progress."
- Problem 6.3 (Posterization of prediction errors), €100: the open part is whether the numerator can
  be improved to ξ^SP(z_<k) and the expression bounded by ≈ 2^K(z_k:n | z_<k).

The page adds: prizes "may be split or reduced or withdrawn if the solution was essentially already
published."

## Leads from an earlier chat (unverified; check each)

- Lattimore & Hutter (2015 or so): every universal mixture fails to converge on some ML-random
  sequence, also after normalization. This would settle 2.3(b) and 2.3(c) negatively and leave 2.3(a).
- Hutter & Muchnik: (a), (b), (c) classes and their (non)equivalence [P11unipreq]; [HM04] construct a
  non-universal semimeasure W converging on all ML-random sequences for all computable μ.
- Leike & Hutter (2015), "Bad universal priors and notions of optimality": limits what 6.2 can claim.
- Chernov & Hutter (2005), posterior bounds with conditional complexity: refers to 6.3.
- Lattimore, Hutter & Gavane (2011), "Universal prediction of selected bits" [P11evenbits].
- Bauwens & Kuznetsov, selected-bits preprint (revised 2026-11-19).
- Lean library: https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean (commit 17c50e5),
  Lean 4.35 + Mathlib. It has universal continuous semimeasures, Martin-Löf randomness, Solomonoff's
  cumulative error bound (`Kolmogorov.tsum_predictionError_le`), almost-sure convergence
  (`Kolmogorov.ae_tendsto_condProb_sub_of_dominates`), selected-bit prediction, and an MDL predictor
  that converges on every ML-random sequence (`Kolmogorov.MDLPrediction.predictor_merges_on_random`).

## What I need, for each of 2.3, 2.7, 2.9, 3.3, 6.2, 6.3

1. The problem restated precisely in modern notation: every definition, every quantifier, and what
   each constant may depend on. Where the book is ambiguous, list the readings.
2. The literature status with full citations (authors, title, venue, year, arXiv ID or DOI). Search
   the web; include work up to November 2026. Say for each citation whether you opened it and what
   exactly it proves. Mark anything you could not verify.
3. The exact claim that is still open after that literature, stated as a theorem candidate (or its
   negation).
4. What a Lean formalization needs: definitions and lemmas, and which of them the Lean library above
   already has (name the declarations if you can read the repo).
5. One small first formal target for each problem: a precise statement that is either a new partial
   result or a needed stepping stone, with an informal proof sketch if you have one.

Then rank the six problems by expected progress per unit of effort for an LLM + Lean workflow, and say
why. Be explicit about what you verified and what you infer.
