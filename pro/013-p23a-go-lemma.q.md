# Prove or refute the lemma GO(P) (the remaining step of Hutter's Problem 2.3(a), fair-coin case)

Attached is a research report (`011-p23a-reduction.a.md`) from an earlier session. Its Section 5 reduces the
fair-coin case of the following open question to one lemma, GO(P):

> 2.3A (Hutter 2005, Problem 2.3(a), as formulated by Lattimore-Hutter 2015): is there an enumerable
> semimeasure q that multiplicatively dominates every enumerable semimeasure and satisfies
> q(ω_t | ω_<t) → μ(ω_t | ω_<t) on every μ-ML-random ω, for every computable μ? Lattimore-Hutter showed every
> effective universal mixture fails (on a fair-coin random). The class 𝒜 \ 𝒞 is open.

Theorem H of the report: GO(P) ⟺ every q ∈ 𝒜 fails on some fair-coin ML-random sequence.

Your task, as a research mathematician:
1. Check the reduction itself first (Theorems A, E, H and the definitions of P = P_3[ξ], h_n, admissible
   arrays). If it is wrong, say exactly where, and stop there with a corrected statement.
2. Then try hard to settle GO(P), in either direction:
   - Negative (prove GO(P)): construct the bad α ∈ P for a given admissible array, e.g. by a priority or
     forcing argument against the permanent upper promises, by a ∅′-construction inside the Π⁰₁ class P,
     by a measure/counting argument (the integers on a deficiency layer can rise only O(n²) times; does that
     force an infinitely-often error somewhere in P?), or by a compactness argument.
   - Positive (refute GO(P)): build an admissible array whose flows are "correct" (ratio (n+1)a(xb) /
     ((n+3)a(x)) → 1 along every path of σP) while h·a ≥ cξ; e.g. a finite-injury construction where
     each node's integer is raised only when ξ forces it and the raise is spread evenly over children.
   - Consider first whether the counting bound alone settles it.
3. If neither direction closes, give the sharpest statement you can prove (a special case of admissible
   arrays, or GO for a smaller class) and say which single step fails.

State each claim as a theorem with quantifiers, give full proofs, and mark proof confidence. Pure mathematics
(algorithmic information theory / computability).
