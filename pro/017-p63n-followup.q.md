# Follow-up on 6.3: the numerator question (6.3N)

Your answer above (015) proves E_{k:n}+1 ≤ C(m+1)2^{K(m)} · M(x)/M(xy) (m = k−1, x = z_{<k}, y = z_{k:n},
M = ξ^SP, greedy horizon-1 AIξ policy) and leaves (6.3N), E_{k:n} ≤ C · M(x)/M(xy), open. Your Theorem 5
refutes the 2^{K(y|x)} version using x = 0^m. Note: on those witnesses M(x)/M(xy) is about 2^{K(m)}, which
exceeds the d−1 ≈ log m errors, so Theorem 5 does not refute (6.3N).

1. Try to refute (6.3N): find, for every universal U (or for one U, then say which), strings with
   E_{k:n} ≫ M(x)/M(xy). Where must the errors come from? The greedy policy errs only where the AI mixture
   ξ^AI puts its mass on the wrong bit; each error costs ξ^AI-mass. Can the AI mixture's extra environments
   (those not reducible to SP environments) make errors cheap in ξ^AI-mass while M(xy) stays ≈ M(x)?
   Consider environments that react to the agent's past actions.
2. Try to prove (6.3N), or (6.3N) with a smaller correction (K(m) alone, or log m, or a constant depending only
   on K(x)'s deficiency), and show which correction is necessary by a matching example.
3. Separately: is (6.3N) true for the passive Bayes-optimal SP predictor (the greedy predictor of M itself,
   not AIξ)? That case may be easier and would show whether the difficulty is the AI/SP gap.

State each claim as a theorem with quantifiers; full proofs; mark confidence and novelty.
