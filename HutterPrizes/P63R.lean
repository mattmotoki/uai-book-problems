/-
Target 6.3R (Problem 6.3, a side claim; Pro query 001, section 7).

Book (p. 208, Problem 6.3) asks whether a posterior error bound can be bounded by
≈ 2^{K(z_k:n | z_<k)}. A natural route would use M(x)/M(xy) ≤ C·2^{K(y|x)} uniformly in x, y.
This target refutes that uniform ratio: for x = 0^ℓ and y = 1 the conditional complexity
K(1 | 0^ℓ) stays bounded, but M(0^ℓ)/M(0^ℓ1) is unbounded (it grows like 2^{K(ℓ)}).
It does not refute the error-count bound itself (a one-bit tail has at most one error).

Upstream: `KP U x y` is K(x | y), so K(y | x) is `KP U y x`. M is the library's canonical
universal continuous semimeasure.
-/
import KolmogorovMathlib.Solomonoff.Basic

namespace HutterPrizes

open Kolmogorov
open scoped ENNReal

private lemma zero_path_lower_bound :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ n : ℕ,
      c ≤ universalContinuousSemimeasure (List.replicate n false) := by
  have hbranch : IsLowerSemicomputableContinuousSemimeasure
      (branchMeasure (fun _ : ℕ => false)) :=
    ⟨branchMeasure_isContinuousTreeSemimeasure _,
      branchMeasure_isLSC _ (Computable.const false)⟩
  obtain ⟨c, hctop, hc⟩ := universalContinuousSemimeasure_isMaximal _ hbranch
  have hprefix (n : ℕ) : cantorPrefix (fun _ : ℕ => false) n =
      List.replicate n false := by
    simp [cantorPrefix]
  have hdom (n : ℕ) : 1 ≤ c * universalContinuousSemimeasure (List.replicate n false) := by
    simpa [branchMeasure, hprefix] using hc (List.replicate n false)
  have hc0 : c ≠ 0 := by
    intro hc0
    simpa [hc0] using hdom 0
  refine ⟨c⁻¹, ENNReal.inv_pos.mpr hctop, fun n => ?_⟩
  have h : c⁻¹ * 1 ≤ c⁻¹ * (c * universalContinuousSemimeasure (List.replicate n false)) := by
    gcongr
    exact hdom n
  simpa [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop] using h

private lemma exists_scaled_one_child_lt
    {a : BitString → ℝ≥0∞} (ha : IsContinuousTreeSemimeasure a)
    {c : ℝ≥0∞} (hc : 0 < c)
    (hbound : ∀ n : ℕ, c ≤ a (List.replicate n false)) (C : ℕ) :
    ∃ n : ℕ, (2 : ℝ≥0∞) ^ C * a (List.replicate n false ++ [true]) <
      a (List.replicate n false) := by
  by_contra h
  push Not at h
  let k : ℝ := 2 ^ C
  have hk : 0 ≤ k := by positivity
  have hcfin : c ≠ ∞ := ne_top_of_le_ne_top (ha.ne_top _) (hbound 0)
  have hcR : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hcfin
  have hstep : ∀ n : ℕ,
      k * (a (List.replicate (n + 1) false)).toReal + c.toReal ≤
        k * (a (List.replicate n false)).toReal := by
    intro n
    have hs := ha.toReal_children_le (List.replicate n false)
    rw [← List.replicate_succ'] at hs
    have hr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) (ha.ne_top _)) (h n)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hr
    have hb := ENNReal.toReal_mono (ha.ne_top _) (hbound n)
    have hm := mul_le_mul_of_nonneg_left hs hk
    change (a (List.replicate n false)).toReal ≤
      k * (a (List.replicate n false ++ [true])).toReal at hr
    nlinarith
  have hind : ∀ n : ℕ,
      (n : ℝ) * c.toReal + k * (a (List.replicate n false)).toReal ≤ k := by
    intro n
    induction n with
    | zero => simp [ha.1]
    | succ n ih =>
      have hs := hstep n
      push_cast
      linarith
  obtain ⟨n, hn⟩ := exists_lt_nsmul hcR k
  have hn0 : 0 ≤ k * (a (List.replicate n false)).toReal :=
    mul_nonneg hk ENNReal.toReal_nonneg
  simp only [nsmul_eq_mul] at hn
  linarith [hind n]

theorem uniform_conditional_ratio_fails (U : Map) (hU : IsOptimalPrefixConditional U) :
    (∃ C₀ : ℕ, ∀ ℓ : ℕ, KP U [true] (List.replicate ℓ false) ≤ C₀) ∧
    ∀ C : ℕ, ∃ ℓ : ℕ,
      (2 : ℝ≥0∞) ^ C * universalContinuousSemimeasure (List.replicate ℓ false ++ [true]) <
        universalContinuousSemimeasure (List.replicate ℓ false) := by
  constructor
  · obtain ⟨C₀, hC₀⟩ :=
      KP_map_self_le U hU (fun _ => [true]) (Computable.const [true])
    exact ⟨C₀, fun ℓ => hC₀ (List.replicate ℓ false)⟩
  · obtain ⟨c, hc, hbound⟩ := zero_path_lower_bound
    intro C
    exact exists_scaled_one_child_lt
      universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
      hc hbound C

end HutterPrizes
