import KolmogorovMathlib.Solomonoff.SelectedBits.Basic
import KolmogorovMathlib.Solomonoff.Domination.UniformFamily

namespace HutterPrizes

open Kolmogorov Kolmogorov.SelectedBits
open scoped ENNReal

/-- Keep M before the cutoff, split the final mass equally, then stop. -/
noncomputable def cutoffFamily (t : ℕ) (y : BitString) : ℝ≥0∞ :=
  if y.length ≤ t - 1 then universalContinuousSemimeasure y
  else if y.length = t then universalContinuousSemimeasure (y.take (t - 1)) / 2
  else 0

theorem cutoffFamily_continuous (t : ℕ) : IsContinuousTreeSemimeasure (cutoffFamily t) := by
  have hM := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  constructor
  · simpa [cutoffFamily] using hM.1
  · intro y
    cases t with
    | zero => simp [cutoffFamily]
    | succ n =>
      by_cases hlt : y.length < n
      · have hparent : y.length ≤ n := by omega
        have hchild : y.length + 1 ≤ n := by omega
        simpa [cutoffFamily, hparent, hchild] using hM.2 y
      · by_cases heq : y.length = n
        · simp only [cutoffFamily, Nat.add_sub_cancel, List.length_append,
            List.length_singleton, heq, Nat.not_succ_le_self, ite_false, le_refl,
            ite_true, List.take_left' heq]
          rw [div_eq_mul_inv, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
        · have hchild : ¬ y.length + 1 ≤ n := by omega
          have hne : y.length + 1 ≠ n + 1 := by omega
          simp only [cutoffFamily, Nat.add_sub_cancel, List.length_append,
            List.length_singleton, hchild, hne, ite_false, zero_add]
          exact zero_le

theorem cutoffFamily_prefixFree (t : ℕ) (S : Finset BitString)
    (hS : IsPrefixFree (S : Set BitString)) :
    ∑ y ∈ S, cutoffFamily t y ≤ 1 := by
  apply (cutoffFamily_continuous t).sum_antichain_le S
  exact hS

theorem cutoffFamily_uniform : IsUniformlyLowerSemicomputableTreeFamily cutoffFamily := by
  have hM := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.2
  have hhalf : IsLSC (fun y _ => universalContinuousSemimeasure y / 2) := by
    simpa using hM.div_two_pow 1
  obtain ⟨q, hqmono, hqsup, hqcomp⟩ := hM
  obtain ⟨r, hrmono, hrsup, hrcomp⟩ := hhalf
  refine ⟨fun t s y =>
    if y.length ≤ t - 1 then q s y []
    else if y.length = t then r s (y.take (t - 1)) []
    else 0, ?_, ?_, ?_⟩
  · intro t s y
    by_cases h₁ : y.length ≤ t - 1
    · simpa only [ite_eq_left h₁] using hqmono s y []
    · by_cases h₂ : y.length = t
      · simpa only [ite_eq_right h₁, ite_eq_left h₂] using hrmono s (y.take (t - 1)) []
      · simp only [ite_eq_right h₁, ite_eq_right h₂]
        simp [dyadicValue]
  · intro t y
    by_cases h₁ : y.length ≤ t - 1
    · simpa only [cutoffFamily, ite_eq_left h₁] using hqsup y []
    · by_cases h₂ : y.length = t
      · simpa only [cutoffFamily, ite_eq_right h₁, ite_eq_left h₂] using hrsup (y.take (t - 1)) []
      · simp only [cutoffFamily, ite_eq_right h₁, ite_eq_right h₂]
        simp [dyadicValue]
  · have hs : Computable (fun p : ℕ × ℕ × BitString => p.2.1) :=
      Computable.fst.comp Computable.snd
    have hy : Primrec (fun p : ℕ × ℕ × BitString => p.2.2) :=
      Primrec.snd.comp Primrec.snd
    have ht : Primrec (fun p : ℕ × ℕ × BitString => p.1 - 1) :=
      Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)
    have hlen : Primrec (fun p : ℕ × ℕ × BitString => p.2.2.length) :=
      Primrec.list_length.comp hy
    have htake : Computable (fun p : ℕ × ℕ × BitString => p.2.2.take (p.1 - 1)) :=
      (Primrec.list_take.comp ht hy).to_comp
    obtain ⟨_, hbefore⟩ := (Primrec.nat_le.comp hlen ht :
      PrimrecPred (fun p : ℕ × ℕ × BitString => p.2.2.length ≤ p.1 - 1))
    obtain ⟨_, hat⟩ := (Primrec.eq.comp hlen Primrec.fst :
      PrimrecPred (fun p : ℕ × ℕ × BitString => p.2.2.length = p.1))
    have hq : Computable (fun p : ℕ × ℕ × BitString => q p.2.1 p.2.2 []) :=
      hqcomp.comp (hs.pair (hy.to_comp.pair (Computable.const [])))
    have hr : Computable (fun p : ℕ × ℕ × BitString =>
        r p.2.1 (p.2.2.take (p.1 - 1)) []) :=
      hrcomp.comp (hs.pair (htake.pair (Computable.const [])))
    exact (Computable.cond hbefore.to_comp hq
      (Computable.cond hat.to_comp hr (Computable.const 0))).of_eq
      (fun p => by
        by_cases h₁ : p.2.2.length ≤ p.1 - 1 <;>
          by_cases h₂ : p.2.2.length = p.1 <;> simp [h₁, h₂])

theorem normalized_lower_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (x : BitString) (b : Bool),
      ((2 : ℝ)⁻¹) ^ ((KPNat U (x.length + 1)).toNat + C) ≤
        normalizedSiblingProb universalContinuousSemimeasure x b := by
  obtain ⟨C, hC⟩ :=
    exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree U hU
      cutoffFamily cutoffFamily_uniform cutoffFamily_prefixFree
  refine ⟨C + 1, ?_⟩
  intro x b
  have hM := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  have hchild : (2 : ℝ≥0∞)⁻¹ ^ ((KPNat U (x.length + 1)).toNat + C) *
      (universalContinuousSemimeasure x / 2) ≤
        universalContinuousSemimeasure (x ++ [b]) := by
    simpa [cutoffFamily] using hC (x.length + 1) (x ++ [b])
  have hreal := ENNReal.toReal_mono (hM.ne_top (x ++ [b])) hchild
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, ENNReal.toReal_div] at hreal
  have hden_pos : 0 < (universalContinuousSemimeasure (x ++ [false])).toReal +
      (universalContinuousSemimeasure (x ++ [true])).toReal :=
    add_pos (universalContinuousSemimeasure_toReal_pos _)
      (universalContinuousSemimeasure_toReal_pos _)
  have hden_le : (universalContinuousSemimeasure (x ++ [false])).toReal +
      (universalContinuousSemimeasure (x ++ [true])).toReal ≤
      (universalContinuousSemimeasure x).toReal := by
    rw [← ENNReal.toReal_add (hM.ne_top _) (hM.ne_top _)]
    exact ENNReal.toReal_mono (hM.ne_top x) (hM.2 x)
  rw [normalizedSiblingProb, le_div_iff₀ hden_pos]
  calc
    ((2 : ℝ)⁻¹) ^ ((KPNat U (x.length + 1)).toNat + (C + 1)) *
        ((universalContinuousSemimeasure (x ++ [false])).toReal +
          (universalContinuousSemimeasure (x ++ [true])).toReal) ≤
        ((2 : ℝ)⁻¹) ^ ((KPNat U (x.length + 1)).toNat + (C + 1)) *
          (universalContinuousSemimeasure x).toReal :=
      mul_le_mul_of_nonneg_left hden_le (by positivity)
    _ = ((2 : ℝ)⁻¹) ^ ((KPNat U (x.length + 1)).toNat + C) *
        ((universalContinuousSemimeasure x).toReal / 2) := by
      rw [← Nat.add_assoc, pow_succ]
      ring
    _ ≤ _ := hreal

end HutterPrizes
