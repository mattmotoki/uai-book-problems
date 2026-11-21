/-
Target 2.7F (Problem 2.7, normalized lower bound; Pro query 001, section 3).

Book (p. 62, Problem 2.7): "Do similar lower performance bounds hold for measure
M_norm(x_t|x_<t) := M(x_t|x_<t) / Σ_{x_t} M(x_t|x_<t), which has no defect?"
The lower bound for M is 1 − M(x_t|x_<t) ≥ (defect) ≳ 2^{-K(t)}.

Formal reading: for the library's canonical universal semimeasure M and optimal prefix
machine U, there is a constant C such that for every history x (of length t − 1) and every
bit b, the sibling-normalized probability of b is at least 2^{-(K(t) + C)}, with t = |x| + 1.
Taking b = the wrong bit gives a per-step lower bound on the normalized prediction error
of order 2^{-K(t)}: the normalized predictor errs by at least that much at every step.
C depends only on U (it is quantified before x and b).

Caveats: the canonical M is one dominant semimeasure, built from a maximality theorem
(Pro: its root mass is 1 in the library; the book allows ≤ 1). The extension to every
dominant M is a separate statement.
-/
import KolmogorovMathlib.Solomonoff.SelectedBits.Basic

namespace HutterPrizes.Targets

open Kolmogorov Kolmogorov.SelectedBits
open scoped ENNReal

theorem normalized_lower_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (x : BitString) (b : Bool),
      ((2 : ℝ)⁻¹) ^ ((KPNat U (x.length + 1)).toNat + C) ≤
        normalizedSiblingProb universalContinuousSemimeasure x b := by
  sorry

end HutterPrizes.Targets
