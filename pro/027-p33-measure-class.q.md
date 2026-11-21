# Research: Problem 3.3 when the class M contains only probability measures

Pure mathematics: Bayesian sequence prediction (Hutter, *Universal Artificial Intelligence*, 2005, Problem 3.3).

In Sec. 3.2.2 (p. 70) of the book the class M is a countable class of probability measures; Problem 3.3 asks, for
two Bayes mixtures ξ = Σ_ν w_ν ν and ξ' = Σ_ν w'_ν ν over the same M with µ ∈ M, whether L^ξ − L^ξ' < ∞
(cumulative µ-expected loss of the Bayes-optimal predictors).

What we have (Lean-checked; your earlier answers attached):
- A finite class of two computable Bernoulli-product measures, weights 1/4, 3/4 swapped: the 0-1 loss gap
  is ≥ (1/32)·H_n → ∞ (ties toward 0).
- Over all lsc semimeasures M_U (your report 008, Theorems 3-4): two mixtures with weights in ratio [1/3, 3] and
  a gap ≥ n^{1/4}/256. Its P and Q are proper semimeasures built from the background's branch masses.

Questions:
1. The class M_comp of all computable probability measures (or any countable class of computable measures
   that contains a universal-like part, e.g. all computable measures with rational conditionals). Give two
   mixtures over such a class, with positive weights (ideally within constant factors of each other, and
   comparable to 2^{-K(ν)}), whose 0-1 loss difference under some µ ∈ M is unbounded. Is the n^{1/4} rate
   achievable here? Does Theorem 3's robustness (any background of weight η ≤ 2^{-20}) carry over when the
   background is a mixture of measures and P, Q must be measures?
2. Hutter's standard prior w_ν = 2^{-K(ν)} exactly (both mixtures with exact complexity weights under two
   different optimal reference machines, as in your 008 Theorem 6), for M_comp or for M_U. What is the cleanest
   exact statement?
3. Is there any natural reading of 3.3 under which the answer is "yes" (e.g. if ξ and ξ' share a reference
   machine and differ by a bounded factor in a specific way, or for log loss instead of 0-1 loss)? A short
   answer is fine.

For each result: a precise theorem with quantifiers, a full proof, confidence, and what needs checking. If a
finite lemma carries the proof, state it separately for Lean. Mark anything new; cite sources you opened.
