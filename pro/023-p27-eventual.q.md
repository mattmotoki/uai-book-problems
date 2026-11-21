# Research: the "every large t" expected lower bound for the normalized universal predictor (Problem 2.7)

This is pure mathematics: algorithmic information theory and sequence prediction (Hutter, *Universal
Artificial Intelligence*, 2005, Problem 2.7).

Setting and notation as in your earlier report (attached `020-p27-expected.a.md`, §1): 𝒜 = lower
semicomputable semimeasures that dominate every such semimeasure; 𝓑 ⊂ 𝒜 = Solomonoff priors of universal
monotone machines; q_M(b|x) = M(xb)/(M(x0)+M(x1)); w_t = 2^{-K(t)}; A_t, S_t = µ-expected one-step L1 and
squared errors of q_M at time t.

Done and checked:
- Theorem 1 (yours) is now proved in Lean for every M ∈ 𝒜 and every computable µ with rational conditionals:
  ∃c > 0, in every late dyadic block some t has A_t ≥ c·w_t and S_t ≥ (c²/2)·w_t².
- A referee found Theorems 1, 2, 6 correct (minor gaps). A literature check found none of 1, 2, 5, 6 in print.
  Hutter's 2009 open-problems list still asks the M_norm question ("I conjecture the answer is yes").

Open (your §4): the eventual version.
  (E)  ∀M ∀ computable µ ∃c > 0 ∃T ∀t ≥ T:  A_t ≥ c·w_t   (and S_t ≥ c·w_t²).

Work on (E) as a research mathematician, separately for 𝒜 and for 𝓑 (and, if useful, for the fair coin
first). Possible routes: a counterexample in 𝒜 built from a symmetrized prior that makes the discrepancy
quantitatively small on a set of times of density one, with the Theorem 1 block bound forcing it back only
rarely; or a proof that a single block's deficit cannot be concentrated on a few times (an averaging or
monotonicity argument along the block). Say where each route breaks.

For each claimed result: a precise theorem with quantifiers, a full proof, your confidence, and what needs
checking. If you find a clean finite or combinatorial lemma that the main proof rests on, state it separately
so that we can formalize it in Lean. Mark anything you believe is new, and cite sources you opened.
