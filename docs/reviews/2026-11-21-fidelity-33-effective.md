# Fidelity review: `P33Effective.effective_counterexample` (Problem 3.3), 2026-11-21

Fresh-context reviewer (Claude Opus subagent), read-only. **Verdict: faithful, with caveats.**

- Book p. 120: "Is L^{Λξ}_∞ − L^{Λξ'}_∞ < ∞ also true?" Both L_∞ are infinite (L^μ_n ≈ n/2), so the question
  is about L_n^ξ − L_n^ξ'. Lean gives ≥ n^{1/4}/256 and → +∞ (`loss_gap_tendsto_atTop`): refutes the sup,
  limit, absolute-value and series readings. 0-1 loss is one case of Λ.
- Conjuncts non-vacuous: `IsLSC` (monotone computable dyadic approximations), `IsUniversal` (root-1 lsc
  semimeasures). `transport` exact (finite values, `toBitString` bijection). `loss` = (3.46) with the
  Λ_ρ action (3.45) for 0-1 loss; `predict` compares ξ(x0), ξ(x1): same action for semimeasure or normalized.
  Ties to 1 is a valid Λ_ξ (footnote 6, p. 87); the gap is not proved for every tie rule.
- μ ∈ M is not a Lean conjunct; it follows on paper (computable ⇒ lsc ⇒ dominated). Add in Lean.
- Mixtures: Lean shows universal dominance only. U = `universalContinuousSemimeasure` is a
  Classical.choose; no Lean theorem says it equals Σ 2^-(i+1) ν_i. Universally dominant semimeasures are a
  strictly larger class than universal mixtures (Wood-Sunehag-Hutter 2011, from memory). Do not claim every
  universal lsc semimeasure is a mixture. Fix: Theorem 4 holds for every positive background, so take an
  explicit mixture Σ w_i ν_i as background; then P, Q ∈ M_U and ξ± are mixtures over M_U with different
  positive weights.
- Root mass 1 (upstream) vs ≤ 1 (book): no restriction (raise the root to 1; same on non-empty strings).
- Presentation: present the measure version (`MixtureCounterexample.counterexample`, Ch. 3 is about
  probability measures, Problem 3.1) with the universal version; explain the source (bias ½ ± 1/(32·4^j) on
  branch j); note n^{1/4} is consistent with the book's O(√L) bound; cite Hutter JMLR 2003 p. 988.

Claim sentence (Lean-checked): "There are two lower semicomputable semimeasures ξ₋, ξ₊ that each dominate
every lower semicomputable semimeasure, and a computable probability measure μ with rational conditionals,
such that for binary 0-1 loss the μ-expected cumulative losses of the Bayes-optimal predictors (ties to 1)
satisfy L_n^{ξ₋} − L_n^{ξ₊} ≥ n^{1/4}/256 for all n ≥ 2."

Extra sentence (paper step until the mixture background is in Lean): "Taking Levin's mixture as the
background, ξ₋ and ξ₊ are two Bayes mixtures over the class M_U of all enumerable semimeasures with different
positive weights, and μ ∈ M_U."
