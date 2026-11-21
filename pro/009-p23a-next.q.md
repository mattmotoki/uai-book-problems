# Follow-up on 2.3A: attack the remaining gap directly

Attached is your previous report (006). You found that the Lattimore-Hutter non-convergence proof needs an
effective subtraction (q − cν lower semicomputable), and that dominance alone does not provide it
(Proposition 1). You also proved a positive partial result relative to ∅′-computable randomness.

Now attack the gap itself, in both directions, and go as deep as you can:

1. Negative direction without subtraction. For an arbitrary q ∈ 𝒜 (enumerable, dominant), build a
   fair-coin ML-random ω on which q(ω_t|ω_<t) does not converge to 1/2. Ideas to test: a construction that
   watches q's own enumeration (q is lower semicomputable, so the adversary can see mass arriving) and
   steers ω into regions where q has committed extra mass to one continuation; a finite-injury or
   ∅′-oracle construction of ω, checking that ω stays ML-random (e.g. by building ω as a path through a
   Π⁰₁ class of positive measure, or via a Kučera-Gács-style coding); exploiting that every q ∈ 𝒜
   dominates the universal mixture ξ, so q = cξ + r with r ≥ 0 a (not necessarily enumerable) semimeasure,
   and asking whether r can cancel ξ's bad behaviour on every bad path at once.
2. Positive direction. Is there a q ∈ 𝒜 \ 𝒞 whose non-enumerable residual structure is exactly what
   makes convergence possible? Try to construct q = cξ + r with r chosen to cancel ξ's deviations on
   ML-random paths while keeping q lower semicomputable (r itself need not be enumerable, only the sum).
3. Report: any full proof of either direction (state it as a theorem); otherwise the sharpest
   reduction, e.g. "2.3A is equivalent to the following combinatorial/effective statement ...", and
   which special case (μ = fair coin only; q with a computable bound on its defect; q normalized) you
   can settle.

Mark confidence and novelty for each claim. This is pure mathematics (algorithmic information theory).
