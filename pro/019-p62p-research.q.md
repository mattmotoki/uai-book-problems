# Follow-up: Problem 6.2(d), polynomial error bounds for AIξ (horizon 1, deterministic passive)

Same setting as 015/017 (book pages attached earlier in this chat; Problem 6.2 is on p. 207-208). The book's
bound (6.17) on the number of errors of AIξ with horizon h_k = 1 on a deterministic computable sequence ż is
exponential in K(ż): E_∞ ≤ C·2^{K(ż)}. Problem 6.2(d) asks for "bounds linear or polynomial in K(ż) as in the
case of SPξ, or examples demonstrating the impossibility". A clean version (from an earlier status map):

  (6.2P) ∀U ∃C_U, d_U ∀ computable infinite ż: E_∞^{AIξ_U, h=1}(ż) ≤ C_U·(1 + K(ż))^{d_U}.

Its negation needs ONE fixed universal U for which every polynomial fails (a different malicious machine per
sequence does not count).

Your 017 answer gave a fixed universal AI prior with large AI/SP mass separation on its own greedy path, whose
extra mass disappears at the first mistake. Use what you learned there:
1. Try to refute (6.2P) (or even the linear version d = 1) for one fixed universal U: a dogmatic-style prior that
   charges the agent many errors on a simple ż, but stays universal. Can the "extra mass disappears at the first
   mistake" problem be fixed by layering (one dogmatic component per error), with total weight summable? What
   number of errors on a sequence of complexity K can one fixed prior force: 2^{Ω(K)}, K^{ω(1)}, or only O(K)?
2. Try to prove (6.2P) for some natural universal U (e.g. Solomonoff-Hutter's ξ^AI = Σ 2^{-K(ν)}ν over
   chronological semimeasures), or for every U with polynomial degree depending on U.
3. Check the literature: Leike-Hutter "Bad universal priors and notions of optimality" (COLT 2015,
   arXiv 1510.04931) and later work. Do their dogmatic priors already settle (6.2P), or explicitly leave the
   deterministic horizon-1 case open? Quote the relevant statement.

State each claim as a theorem with quantifiers; full proofs; mark confidence and novelty.
