/-
Target 6.3E (Hutter 2005, Problem 6.3, last question, book p. 208): "Is it possible ... to bound the
expression by ≈ 2^{K(z_{k:n} | z_{<k})} (cf. Problem 3.13)?" Read as an error-count bound: the number of
prediction errors E_{k:n} in cycles k..n is at most C·2^{K(z_{k:n} | z_{<k})}, with C independent of n, k, z.

Fidelity note.
- K(y | x) is ordinary conditional prefix complexity (Problem 3.13 posterizes K(ν) to K(ν | x_{<k})); in the
  library `KP U y x` = K(y | x) for an optimal prefix decompressor U.
- The AIξ policy in the SP setting is deterministic (fixed tie rule); it induces a predictor
  P : BitString → Bool (next-bit guess after the true prefix). The target quantifies over EVERY P, so it
  covers the AIξ policy for every U, computable or not.
- `errors P x y` counts j < |y| with P(x ++ y_{<j}) ≠ y_j: errors while predicting y after observing x.
  With x = z_{<k}, y = z_{k:n}: errors P x y = E_{k:n}.
- Claim (Pro 015, Theorem 5): one constant b (depending on U only) works for every P and every d.
  Antecedent: Chernov-Hutter ALT 2005 (arXiv cs/0507041) Lemma 5 uses the same length trick
  (x = 0^l) to show one-step deviation of M can be ≥ K(l) ln 2 while K(μ|x) = O(1); it is not an
  error-count statement over all predictors.
-/
import KolmogorovMathlib.Solomonoff.Basic

namespace HutterPrizes

open Kolmogorov

/-- Number of wrong next-bit guesses of `P` while it predicts `y` after observing `x`. -/
def errors (P : BitString → Bool) (x y : BitString) : ℕ :=
  ((List.range y.length).filter (fun j => P (x ++ y.take j) != y.getD j false)).length

theorem errorcount_complexity_bound_fails (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ b : ℕ, ∀ P : BitString → Bool, ∀ d : ℕ, ∃ x y : BitString,
      KP U y x ≤ b ∧ d ≤ errors P x y + 1 := by
  sorry

theorem no_errorcount_complexity_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : BitString → Bool) :
    ¬ ∃ C : ℕ, ∀ x y : BitString, ∀ k : ℕ, KP U y x ≤ k → errors P x y ≤ C * 2 ^ k := by
  sorry

end HutterPrizes
