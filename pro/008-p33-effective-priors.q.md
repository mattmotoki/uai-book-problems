# Follow-up: Problem 3.3 counterexample with *effective* universal priors

Attached is your previous answer (007). You proved: for the class of all computable measures there are two
full-support mixtures ξ₋, ξ₊ (weights agree except μ, ν swapped; ratio ≤ 3) with
(1/32)H_n ≤ L^{ξ₋}_n − L^{ξ₊}_n ≤ (1/16)H_n under μ, 0-1 loss. You flagged that your enumeration of all
computable measures is non-effective, so the priors are not lower semicomputable, and Solomonoff priors or
priors ≍ 2^-K(ρ) are not covered.

The version Hutter most likely means uses effective universal mixtures: ξ = Σ_ρ w_ρ ρ over an effective
enumeration of all enumerable semimeasures (or of all computable measures via a standard partial
enumeration), with w lower semicomputable, e.g. w_ρ = 2^-K(ρ); or Solomonoff's M_U for two universal U.

1. Can your construction be made effective? Where exactly does it use non-effectiveness (deciding which
   indices are total/computable measures, separating μ, ν from the rest, controlling the rest's
   predictions on the good set)? Can a semimeasure class (enumerable semimeasures, which do admit an
   effective enumeration) replace the measure class, with the "rest" handled through its normalized
   predictions?
2. Try to prove: there exist two lower-semicomputable positive weight functions w, w' on an effective
   enumeration of all enumerable semimeasures, with w'/w bounded above and below, and a computable μ, such
   that L^ξ_n − L^ξ'_n → ∞ under μ (0-1 loss, Bayes predictor of the normalized mixture or of the raw
   semimeasure — say which). Or show that effective universal priors force the difference to be bounded
   (or o(log n), or summable per-step) for every computable μ.
3. Then the two-Solomonoff-priors case: M_U vs M_V, and M_U vs ξ_U with weights 2^-K.
4. State every claim as a theorem with quantifiers, give proofs, mark confidence, and flag what is new.
