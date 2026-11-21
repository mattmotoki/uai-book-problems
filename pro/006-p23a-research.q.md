# Research attempt: Hutter's Problem 2.3(a), convergence of a dominant semimeasure on every ML-random sequence

## The open question (your own formulation from an earlier status map, named 2.3A)

Let 𝒜 be the class of enumerable (uniformly lower-semicomputable) continuous semimeasures q on binary
strings that multiplicatively dominate every enumerable semimeasure ν (∃ c_{q,ν} > 0 ∀x: q(x) ≥ c ν(x)).

2.3A: ∃ q ∈ 𝒜 ∀ computable probability measure μ ∀ ω ∈ MLR(μ):
q(ω_t | ω_<t) − μ(ω_t | ω_<t) → 0.

Negation: ∀ q ∈ 𝒜 ∃ μ, ω ∈ MLR(μ), ε > 0 with |q(ω_t|ω_<t) − μ(ω_t|ω_<t)| ≥ ε infinitely often.
A negative answer with μ = fair coin suffices; a positive answer needs every computable μ.

Known (please re-check): Lattimore & Hutter, "On Martin-Löf (non-)convergence of Solomonoff's universal
mixture", TCS 588 (2015): every effective universal mixture (class 𝒞 = class ℬ of Solomonoff M_U, by
Wood-Sunehag-Hutter 2013) fails on some fair-coin-ML-random sequence, also after normalization; they leave
𝒜 \ 𝒞 open. Hutter & Muchnik (TCS 2007) construct a non-universal enumerable W that converges on all
ML-random sequences of all computable μ. Milovanov (ToCS 2024) proves ML-path merging for an MDL
selector (not a semimeasure in 𝒜).

## What I want

Work on 2.3A as a research mathematician. This is a long-horizon question; partial progress is valuable.

1. Explain exactly which step of the Lattimore-Hutter proof uses the mixture structure, and whether it can
   be replaced by an argument that uses only dominance plus enumerability. If yes, sketch the negative
   proof for all of 𝒜. If no, explain the obstruction precisely.
2. Explore the positive direction: can one combine a universal q₀ ∈ 𝒜 with the Hutter-Muchnik W (or
   with an MDL-style predictor) into a semimeasure that is still in 𝒜 (still enumerable and dominant)
   and inherits W's convergence? For example q = ½q₀ + ½W fails (why?); consider constructions where
   q₀'s influence is damped along paths where it disagrees with W, while keeping lower semicomputability.
   Identify the exact tension between enumerability and convergence.
3. Find the strongest partial result you can actually prove, with a full proof: e.g. a restricted
   class of μ (Bernoulli(θ) with computable θ, or finite-state sources), a restricted notion of
   randomness (e.g. Schnorr or 2-randomness, or ML-random relative to ∅′), convergence in a weaker sense
   (Cesàro, or along a density-one set of times), or a negative result for a natural subclass of 𝒜 \ 𝒞.
4. For each claimed result, state it as a precise theorem with quantifiers, give the proof, and say how
   confident you are and what would need checking. Mark anything you believe is new.

Cite sources with arXiv IDs or DOIs and say which ones you opened. Search for work up to November 2026,
in case 2.3A was settled recently (check also works citing Lattimore-Hutter 2015).
