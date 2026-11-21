# Lean 4 formalization: two Bayes mixtures whose cumulative 0-1 losses differ without bound

## Context

Hutter, *Universal Artificial Intelligence* (2005), Problem 3.3 (Comparing two mixtures, rated C05u/C40o):
"Consider two mixtures ξ and ξ' over M. Show that Σ_t E[Σ_{x_t}(ξ(x_t|x_<t) − ξ'(x_t|x_<t))²] ≤ 2[ln w_μ⁻¹ +
ln w'_μ⁻¹] < ∞ ... Furthermore, show that L^ξ_n − L^ξ'_n ≤ O(√L^ξ'_n) (cf. Theorem 3.48). Is the stronger
result L^ξ − L^ξ' < ∞ also true?" Here L^ρ_n = Σ_{t≤n} E_μ[ℓ(x_t, y^ρ_t)] is the μ-expected cumulative loss
of the Bayes-optimal predictor for ρ, and μ ∈ M is the true environment.

A proposed counterexample (yours, from an earlier analysis): δ_t = 1/(32t), μ(x_t=1) = 1/2 + δ_t,
ν(x_t=1) = 1/2 − δ_t, independent bits, M = {μ, ν}, 0-1 loss, ξ₋ = ¼μ + ¾ν, ξ₊ = ¾μ + ¼ν. With
R_n = ν(x_1:n)/μ(x_1:n): ξ₋ predicts 1 iff R < 1/3, ξ₊ predicts 1 iff R < 3; E_μ R_n² ≤ e^{8/255}, so by
Chebyshev P_μ(1/2 < R_{t−1} < 3/2) > 1/2, giving L^{ξ₋}_n − L^{ξ₊}_n ≥ Σ_{t≤n} δ_t → ∞.

## Task

Write a self-contained Lean 4 file that proves this. It must compile with Lean `v4.35.0` and Mathlib tag
`v4.35.0` (plain Mathlib is enough; the Kolmogorov library is not needed). No `sorry`, `admit`, new axioms,
or `native_decide`.

Split the file into two parts.

**Part 1, the statement layer** (short, readable; this is what a reviewer will check against the book):
general definitions for binary sequence prediction over a finite horizon, then the main theorem. A
suggested design (change it if you have a cleaner one, and say why):

- A model is `p : List Bool → ℝ`, the probability that the next bit is `true` after history `x`, with
  `0 ≤ p x ≤ 1`. Its prefix probability `prob p x` is the product of the conditionals along `x`.
- A class with weights: `ι` a `Fintype` (or countable index), models `m : ι → Model`, weights `w : ι → ℝ`,
  positive, summing to 1. The mixture's conditional `mixCond m w x = Σ w i * prob (m i) x * m i x /
  Σ w i * prob (m i) x`.
- The Bayes predictor for 0-1 loss predicts `true` iff the mixture conditional is > 1/2.
- `loss μ m w n` = Σ_{t < n} Σ_{x of length t} prob μ x * (probability under μ that the prediction at x is
  wrong).
- Main theorem, in a form that negates the book's "L^ξ − L^ξ' < ∞": there exist a finite class `m` with
  computable rational-valued models, a member `μ = m j` (the true environment), and two positive weight
  vectors `w, w'` (each summing to 1) such that `n ↦ loss μ m w n − loss μ m w' n` is not bounded above.
  Also state the explicit rate: `loss μ m w n − loss μ m w' n ≥ (1/32) * Σ_{t<n} 1/(t+1)`.

**Part 2, the proofs**: everything else, with helper lemmas.

Then give: the whole file in one Lean code block; a short map from each Part 1 definition to the book's
notation; and a list of every place where the formal statement differs from the book's setting (for
example finite horizon, binary alphabet, tie-breaking, the class being finite).
