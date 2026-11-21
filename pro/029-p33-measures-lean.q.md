# Lean proof: Problem 3.3 over a class of computable probability measures (target P33Measures)

## Goal and reason
We answer Hutter's Problem 3.3 ("Comparing two mixtures", UAI 2005) negatively. Lean already proves it for mixtures
over all lsc semimeasures (`P33Mixture`, `P33Complexity`, attached). In the book's Sec. 3.2.2 the class M is a
countable class of *probability measures*, so we want the theorem for that reading. Your report 027, Theorem 2,
proves it on paper; a referee and a fidelity review accepted it.

## Task
Prove `P33Measures.measure_class_counterexample` in the attached `Targets/P33Measures.lean`. Keep everything above
the `:= by` of the theorem, and the three definitions `RatMeasure`, `measureMass`, `classMixture`, character for
character (we diff them). Add any helper definitions and lemmas you need. Return one complete Lean file
`HutterPrizes/P33Measures.lean` (namespace `P33Measures`, same imports or more from this repo/Mathlib/upstream).
It must compile with Lean 4.35.0, Mathlib v4.35.0, kolmogorov-complexity-lean commit
17c50e560c337a8a702f8850a711f80a56b3cf91, with no sorry, admit, axiom, or native_decide.

## Context you cannot find yourself
- `RobustExperiment.Theorem4.theorem4 (M : Background) (n) (hn : 2 ≤ n)` gives
  n^{1/4}/256 ≤ loss source (xiMinus M) n − loss source (xiPlus M) n for any positive `Background` M
  (P33Theorem4.lean). `P33Complexity.lean` shows a full transport from a concrete mixture to `theorem4`
  (rawSplice, loss_eq_of_nonempty, transport_rawXi); reuse that pattern.
- The fidelity reviewer suggested a simpler route: take M.mass := transport (classMixture a) (positive because the
  fair coin r ≡ 1/2 is in C with a > 0). Define T±ν to copy ν's selector masses, run the branch-j experiment with
  bias 1/2 ± γ_j, then emit fair bits (no restart). T±ν stays in C (total computable rational r). Injectivity is not
  needed: put A±(ρ) := Σ_{ν : T±ν = ρ} a_ν and w±_ρ := η a_ρ + (1−η)/4·(3A_±(ρ) + A_∓(ρ)) with η = 2^-20 (check
  which of ± gets 3/4 against `xiMinus`/`xiPlus`). Then classMixture w± should equal the theorem4 mixtures (or agree
  on every nonempty history, which suffices for loss). Use whatever route works.
- The attached `helpers-from-review.lean` has compiled lemmas `ratMeasure_countable`, `exists_positive_prior`, and
  `mu_mass` (muProb µ (toBitString h) = prob source n h); reuse them. `P33Effective.EffectiveStatement`'s proof gives
  the computable rational r for `source`.

## Done
The complete file in one ```lean block, then a short list of the main lemmas and anything that deviates from the
route above.
