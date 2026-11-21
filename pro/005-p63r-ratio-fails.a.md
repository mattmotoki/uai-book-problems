```lean
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

namespace HutterPrizes.Targets

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

end HutterPrizes.Targets
```

### Informal proof

For the first conjunct, apply `KP_map_self_le` to the computable constant function \(f(x)=[\mathrm{true}]\). It gives a constant bound on \(K(f(x)\mid x)\), uniformly in \(x\), hence also on \(K(1\mid 0^\ell)\).

For the second conjunct, the computable all-zero sequence defines a branch measure assigning mass \(1\) to every \(0^n\). Universality therefore gives a finite multiplier \(D\) such that
\[
1\le D\,M(0^n)
\]
for every \(n\). Thus \(D\ne0\), and \(c=D^{-1}>0\) satisfies \(c\le M(0^n)\) uniformly.

Fix \(C\), write \(k=2^C\), \(A_n=M(0^n)\), and \(B_n=M(0^n1)\), viewing these finite masses as real numbers. Suppose the desired strict inequality fails for every \(n\). Then \(A_n\le kB_n\). Together with the semimeasure inequality and the lower bound, this gives
\[
A_{n+1}+B_n\le A_n,
\qquad
kA_{n+1}+c
\le kA_{n+1}+A_n
\le k(A_{n+1}+B_n)
\le kA_n.
\]
Induction yields
\[
nc+kA_n\le kA_0=k.
\]
Since \(A_n\ge0\) and \(c>0\), choosing \(n\) with \(nc>k\) gives a contradiction.

This establishes the required unboundedness directly; the coding theorem is unnecessary for the stated result.

### Upstream declarations used

All Kolmogorov declarations below are available through the single supplied import, at commit `17c50e560c337a8a702f8850a711f80a56b3cf91`.

| Declaration | Role | Source |
|---|---|---|
| `Kolmogorov.KP_map_self_le` | Uniform bound on \(K(f(x)\mid x)\) for computable \(f\). | [Prefix/Properties/Part01.lean](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/blob/17c50e560c337a8a702f8850a711f80a56b3cf91/KolmogorovMathlib/Prefix/Properties/Part01.lean) |
| `Kolmogorov.branchMeasure`, `Kolmogorov.branchMeasure_isContinuousTreeSemimeasure`, `Kolmogorov.branchMeasure_isLSC` | Construct the measure concentrated on the all-zero sequence and establish its required properties. | [MonotoneComplexity/APrioriComplexity.lean](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/blob/17c50e560c337a8a702f8850a711f80a56b3cf91/KolmogorovMathlib/MonotoneComplexity/APrioriComplexity.lean) |
| `Kolmogorov.universalContinuousSemimeasure_isMaximal` | Dominate that branch measure by a finite multiple of \(M\). | [MonotoneComplexity/APrioriComplexity.lean](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/blob/17c50e560c337a8a702f8850a711f80a56b3cf91/KolmogorovMathlib/MonotoneComplexity/APrioriComplexity.lean) |
| `Kolmogorov.universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure` | Supply the tree semimeasure property of \(M\). | [MonotoneComplexity/APrioriComplexity.lean](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/blob/17c50e560c337a8a702f8850a711f80a56b3cf91/KolmogorovMathlib/MonotoneComplexity/APrioriComplexity.lean) |
| `Kolmogorov.cantorPrefix` | Identify prefixes of the constant-false sequence with `List.replicate n false`. | [AlgorithmicRandomness/Cantor.lean](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/blob/17c50e560c337a8a702f8850a711f80a56b3cf91/KolmogorovMathlib/AlgorithmicRandomness/Cantor.lean) |
| `Kolmogorov.IsContinuousTreeSemimeasure`, `Kolmogorov.IsLowerSemicomputableContinuousSemimeasure`, `Kolmogorov.IsContinuousTreeSemimeasure.ne_top` | Root normalization, tree inequalities, lower semicomputability, and finiteness of masses. | [MonotoneComplexity/TreeSemimeasure.lean](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/blob/17c50e560c337a8a702f8850a711f80a56b3cf91/KolmogorovMathlib/MonotoneComplexity/TreeSemimeasure.lean) |
| `Kolmogorov.IsContinuousTreeSemimeasure.toReal_children_le` | Transfer the children inequality to real numbers for the telescoping argument. | [MonotoneComplexity/MeasureRepresentation.lean](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/blob/17c50e560c337a8a702f8850a711f80a56b3cf91/KolmogorovMathlib/MonotoneComplexity/MeasureRepresentation.lean) |

The explicitly invoked Mathlib and standard-library support declarations are:

- `Computable.const`, `List.replicate_succ'`.
- `ENNReal.inv_pos`, `ENNReal.inv_mul_cancel`.
- `ENNReal.toReal_pos`, `ENNReal.toReal_mono`, `ENNReal.toReal_mul`, `ENNReal.toReal_pow`, `ENNReal.toReal_ofNat`, `ENNReal.toReal_nonneg`.
- `ENNReal.mul_ne_top`, `ENNReal.pow_ne_top`, `ne_top_of_le_ne_top`.
- `mul_assoc`, `mul_le_mul_of_nonneg_left`, `mul_nonneg`, `exists_lt_nsmul`, `nsmul_eq_mul`.

### Verification

The complete file was checked successfully with **Lean 4.35.0**, **Mathlib v4.35.0**, and the exact requested Kolmogorov library commit. The theorem statement is unchanged. The axiom audit for `HutterPrizes.Targets.uniform_conditional_ratio_fails` reports only **`propext`, `Classical.choice`, and `Quot.sound`**.

[UniformConditionalRatioFails.lean](https://chatgpt.com/library?file_id=libfile_fde3_f-f8f8f5c4920481918f76409b8a2e2cc2_55156f90431c8191a9d99c52c310f59a&account_id=personal)