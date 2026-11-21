# Lean 4: the block bound behind the expected lower bound for M_norm (Problem 2.7)

Environment: Lean v4.35.0 and Mathlib v4.35.0 (plain Mathlib is enough). No `sorry`, `admit`, new axioms or
`native_decide`.

Context: a proof (attached report, §2, Theorem 1, Step 3, eqs. (10)-(15)) shows that for every universal M and
computable µ, the µ-expected one-step error of the normalized predictor is ≥ c·2^{-K(t)} at some t in every late
dyadic block. Its core is a finite, non-computable lemma. Formalize and prove it:

> **Block lemma.** Let µ and Q be probability distributions on binary strings of length r + ℓ (equivalently,
> sequential laws given by next-bit conditionals over the first r + ℓ bits), and let β > 0. Let G be a set of
> strings x of length r with µ(G) ≥ 1/2. Suppose every x ∈ G has a block b_x ∈ {0,1}^ℓ with
> Q(x b_x) ≥ β·µ(x) and µ(x b_x) ≤ (β/2)·µ(x). Then
> Σ_{t = r+1}^{r+ℓ} E_µ[ Σ_{b∈{0,1}} |Q(b | X_{<t}) − µ(b | X_{<t})| ] ≥ β/2.

Here E_µ averages over X_{<t} drawn from µ, and the conditionals Q(b|y) = Q(yb)/Q(y) (define them as you like
on µ- or Q-null histories, and say how). Include the hybrid inequality
‖P − Q‖₁ ≤ Σ_k E_P ‖P(·|Y_{<k}) − Q(·|Y_{<k})‖₁ for two sequential laws on a finite block as a separate lemma.
Note: the report's (11) uses Q(x) ≤ 2µ(x) on G to get Q(b_x | x) ≥ β/2-type bounds; state the hypothesis in
whichever equivalent form makes the lemma cleanest, and say exactly how it maps to (10)-(15).

Requirements: Part 1 (statement layer: finite histories, sequential laws, conditionals, the expected error A_t,
the block lemma), Part 2 (proofs). Reuse this style if convenient: `History n` as nested pairs and a `Model`
with next-bit conditionals in [0,1] (attached `P33Theorem3.lean`, Part 1). Return one Lean code block, then a
map to (10)-(15), then deviations.
