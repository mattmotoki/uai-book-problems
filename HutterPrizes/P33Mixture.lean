/-
Two Bayes mixtures over the fixed enumeration of root-one lower
semicomputable continuous semimeasures.

Lean 4.35.0; Mathlib v4.35.0;
kolmogorov-complexity-lean 17c50e560c337a8a702f8850a711f80a56b3cf91.
The three attached files are imported without modification.
-/
import HutterPrizes.P33Effective
import KolmogorovMathlib.MonotoneComplexity.MaximalSemimeasure

open scoped BigOperators ENNReal
open Kolmogorov RobustExperiment RobustExperiment.Theorem4 P33Effective

namespace P33Mixture

set_option maxHeartbeats 2000000

/-! Part 1. Statement. -/

/-- A Bayes mixture over precisely the upstream enumeration. -/
noncomputable def bayesMixture (w : ℕ → ℝ≥0∞) : BitString → ℝ≥0∞ :=
  fun x => ∑' i, w i * treeLSCEnum i x

def MixtureStatement : Prop :=
  ∃ (wMinus wPlus : ℕ → ℝ≥0∞) (j : ℕ),
    (∀ i, 0 < wMinus i ∧ 0 < wPlus i) ∧
    (∑' i, wMinus i) = 1 ∧ (∑' i, wPlus i) = 1 ∧
    (∀ i, wMinus i ≤ 3 * wPlus i ∧ wPlus i ≤ 3 * wMinus i) ∧
    IsLowerSemicomputableContinuousSemimeasure (bayesMixture wMinus) ∧
    IsLowerSemicomputableContinuousSemimeasure (bayesMixture wPlus) ∧
    (∀ n (h : History n),
      treeLSCEnum j (toBitString h) = ENNReal.ofReal (prob source n h)) ∧
    (0 < wMinus j ∧ 0 < wPlus j) ∧
    (∀ n : ℕ, 2 ≤ n →
      (n : ℝ)^(1/4 : ℝ)/256 ≤
        loss source (transport (bayesMixture wMinus)) n -
          loss source (transport (bayesMixture wPlus)) n) ∧
    Filter.Tendsto
      (fun n : ℕ =>
        loss source (transport (bayesMixture wMinus)) n -
          loss source (transport (bayesMixture wPlus)) n)
      Filter.atTop Filter.atTop

/-! Part 2. Proofs. -/

/-! 2a. Explicit background and exact transport to Theorem 4. -/

noncomputable def base : BitString → ℝ≥0∞ := continuousTreeMixture treeLSCEnum

lemma base_effective : IsLowerSemicomputableContinuousSemimeasure base :=
  treeMixture_isLowerSemicomputableContinuousSemimeasure

lemma base_pos (x : BitString) : 0 < base x := by
  obtain ⟨j, hj⟩ := treeLSCEnum_complete
    (show IsLowerSemicomputableContinuousSemimeasure lengthMeasure from
      ⟨lengthMeasure_isContinuousTreeSemimeasure, lengthMeasure_isLSC_core⟩)
  have hd := continuousTreeMixture_dominates_component treeLSCEnum j x
  rw [hj] at hd
  have hp : 0 < lengthMeasure x := by
    exact pos_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num [lengthMeasure]))
  exact lt_of_lt_of_le (ENNReal.mul_pos (dyadicWeight_pos j).ne' hp.ne') hd

noncomputable def background : Background where
  mass := transport base
  semimeasure := {
    nonneg := fun _ _ => ENNReal.toReal_nonneg
    root := by
      change (base []).toReal ≤ 1
      rw [base_effective.1.1]
      simp
    children := by
      intro n h
      have hm := base_effective.1
      change (base (toBitString h ++ [false])).toReal +
          (base (toBitString h ++ [true])).toReal ≤
        (base (toBitString h)).toReal
      rw [← ENNReal.toReal_add (hm.ne_top _) (hm.ne_top _)]
      exact (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hm.ne_top _, hm.ne_top _⟩)
        (hm.ne_top _)).mpr (hm.2 _)
  }
  positive := by
    intro n h
    exact ENNReal.toReal_pos (base_pos _).ne'
      (base_effective.1.ne_top _)

lemma background_root : background.mass 0 () = 1 := by
  change (base []).toReal = 1
  rw [base_effective.1.1]
  simp

lemma xi_root (i : Bool) : xi background i 0 () = 1 := by
  have hm := background_root
  cases i <;> simp only [xi, mix, P, Q, spliced, scan, spliceState, ones,
    Bool.false_eq_true, ↓reduceIte] <;> rw [hm] <;> ring

noncomputable def spliceBits (i : Bool) (x : BitString) : ℝ≥0∞ :=
  ENNReal.ofReal (coeff i x : ℝ) * base (stem x)

noncomputable def xiBits (i : Bool) : BitString → ℝ≥0∞ :=
  mixE (1 - etaQ)
    (mixE (priorWeight i) (spliceBits true) (spliceBits false))
    base

lemma spliceBits_lsc (i : Bool) : IsLSC (fun x _ => spliceBits i x) :=
  lsc_weighted_comp
    base_effective.2
    stem_computable (coeff_computable i)

lemma xiBits_lsc (i : Bool) : IsLSC (fun x _ => xiBits i x) :=
  lsc_mixE (1 - etaQ)
    (lsc_mixE (priorWeight i) (spliceBits_lsc true) (spliceBits_lsc false))
    base_effective.2

lemma spliceBits_word (i : Bool) (s : State) :
    spliceBits i (toBitString (word s).2) = ENNReal.ofReal (spliceState background i s) := by
  have hm := base_effective.1
  cases s with
  | trunk j =>
    simp only [word, toBitString_ones, spliceBits, coeff_trunk, stem_trunk,
      Rat.cast_one, ENNReal.ofReal_one, one_mul, spliceState]
    change base (List.replicate j true) =
      ENNReal.ofReal (base (toBitString (ones j))).toReal
    rw [toBitString_ones, ENNReal.ofReal_toReal (hm.ne_top _)]
  | branch j t h =>
    rw [toBitString_word_branch]
    simp only [spliceBits, coeff_branch, stem_branch, qProb_cast, spliceState]
    rw [ENNReal.ofReal_mul (branchWeight_pos background j).le]
    change ENNReal.ofReal (prob (experiment (scale j) (scale_pos j) i) t h) *
        base (List.replicate j true ++ [false]) =
      ENNReal.ofReal (base (toBitString (n := j+1) (ones j, false))).toReal * _
    rw [ENNReal.ofReal_toReal (hm.ne_top _)]
    simp only [toBitString, toBitString_ones, mul_comm]

lemma spliceBits_history (i : Bool) (n : ℕ) (h : History n) :
    spliceBits i (toBitString h) = ENNReal.ofReal (spliced background i n h) := by
  have hx := spliceBits_word i (scan n h)
  rw [word_scan] at hx
  exact hx

lemma xiBits_history (i : Bool) (n : ℕ) (h : History n) :
    xiBits i (toBitString h) = ENNReal.ofReal (xi background i n h) := by
  have hp := (P_semimeasure background).nonneg n h
  have hq := (Q_semimeasure background).nonneg n h
  have hw0 : (0 : ℝ) ≤ (if i then 3/4 else 1/4) := by cases i <;> norm_num
  have hw1 : (if i then 3/4 else 1/4 : ℝ) ≤ 1 := by cases i <;> norm_num
  have hc : 0 ≤ mix (if i then 3/4 else 1/4) (P background) (Q background) n h :=
    (IsSemimeasure.mix (P_semimeasure background) (Q_semimeasure background) _ hw0 hw1).nonneg n h
  have hcore :
      mixE (priorWeight i) (spliceBits true) (spliceBits false) (toBitString h) =
        ENNReal.ofReal (mix (if i then 3/4 else 1/4) (P background) (Q background) n h) := by
    rw [mixE, spliceBits_history, spliceBits_history]
    simpa only [priorWeight_cast, P, Q, mix] using
      mixE_ofReal (priorWeight i) (priorWeight_nonneg i) (priorWeight_le_one i)
        (P background n h) (Q background n h) hp hq
  unfold xiBits
  rw [mixE, hcore]
  rw [← ENNReal.ofReal_toReal
    (base_effective.1.ne_top (toBitString h))]
  change _ = ENNReal.ofReal (xi background i n h)
  rw [mixE_ofReal (1-etaQ) one_sub_etaQ_nonneg one_sub_etaQ_le_one _
    (base (toBitString h)).toReal hc ENNReal.toReal_nonneg]
  simp only [Rat.cast_sub, Rat.cast_one, etaQ_cast, xi, mix, background, transport]

lemma transport_xiBits (i : Bool) : transport (xiBits i) = xi background i := by
  funext n h
  change (xiBits i (toBitString h)).toReal = xi background i n h
  rw [xiBits_history, ENNReal.toReal_ofReal ((xi_semimeasure background i).nonneg n h)]

lemma semimeasure_of_history {a : BitString → ℝ≥0∞} {m : Mass}
    (hm : IsSemimeasure m) (hroot : m 0 () = 1)
    (ha : ∀ n (h : History n), a (toBitString h) = ENNReal.ofReal (m n h)) :
    IsContinuousTreeSemimeasure a := by
  constructor
  · change a (toBitString (n := 0) ()) = 1
    rw [ha, hroot, ENNReal.ofReal_one]
  · intro x
    obtain ⟨n,h,rfl⟩ := toBitString_surjective x
    change a (toBitString (n := n+1) (h,false)) +
      a (toBitString (n := n+1) (h,true)) ≤ _
    rw [ha (n+1) (h,false), ha (n+1) (h,true), ha n h,
      ← ENNReal.ofReal_add (hm.nonneg (n+1) (h,false))
        (hm.nonneg (n+1) (h,true))]
    exact ENNReal.ofReal_le_ofReal (hm.children n h)

lemma spliceBits_effective (i : Bool) :
    IsLowerSemicomputableContinuousSemimeasure (spliceBits i) := by
  refine ⟨semimeasure_of_history (spliced_semimeasure background i) ?_
    (spliceBits_history i), spliceBits_lsc i⟩
  change background.mass 0 () = 1
  exact background_root

lemma xiBits_effective (i : Bool) :
    IsLowerSemicomputableContinuousSemimeasure (xiBits i) :=
  ⟨semimeasure_of_history (xi_semimeasure background i) (xi_root i)
    (xiBits_history i), xiBits_lsc i⟩

lemma xiBits_loss_bounds (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ)^(1/4 : ℝ)/256 ≤
      loss source (transport (xiBits false)) n - loss source (transport (xiBits true)) n ∧
    loss source (transport (xiBits false)) n - loss source (transport (xiBits true)) n ≤
      (n : ℝ)^(1/4 : ℝ)/8 := by
  rw [transport_xiBits, transport_xiBits]
  exact theorem4 background n hn

/-! 2b. The source is a member of the same enumeration. -/

def sourceRat (x : BitString) : ℚ :=
  (1 / (2 : ℚ) ^ (stem x).length) * coeff true x

theorem sourceRat_computable : Computable sourceRat := by
  have hl : Computable (fun x : BitString => (stem x).length) :=
    Primrec.list_length.to_comp.comp stem_computable
  have hd : Computable (fun x : BitString => 2 ^ (stem x).length) :=
    natPow_computable.comp (Computable.const 2) hl
  have hf : Computable (fun x : BitString => (1 : ℚ) / 2 ^ (stem x).length) :=
    computable_of_num_den (N := fun _ : BitString => (1 : ℤ))
      (D := fun x => 2 ^ (stem x).length)
      (Computable.const 1) hd (fun x => by positivity) (fun x => by simp)
  exact computable₂_ratMul.comp hf (coeff_computable true)

theorem sourceRat_nonneg (x : BitString) : 0 ≤ sourceRat x :=
  mul_nonneg (by positivity) (coeff_nonneg true x)

theorem sourceRat_word (s : State) :
    (sourceRat (toBitString (word s).2) : ℝ) =
      prob source (word s).1 (word s).2 := by
  cases s with
  | trunk j =>
    simp [word, toBitString_ones, sourceRat, prob_source_ones]
  | branch j t h =>
    rw [toBitString_word_branch]
    simp only [sourceRat, stem_branch, coeff_branch, List.length_append,
      List.length_replicate, List.length_singleton, Rat.cast_mul, Rat.cast_div,
      Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat, qProb_cast, word, prob_source_branch,
      localModel]
    rw [div_pow, one_pow]

theorem sourceRat_history (n : ℕ) (h : History n) :
    (sourceRat (toBitString h) : ℝ) = prob source n h := by
  have hs := sourceRat_word (scan n h)
  rw [word_scan] at hs
  exact hs

noncomputable def sourceBits (x : BitString) : ℝ≥0∞ :=
  ENNReal.ofReal (sourceRat x : ℝ)

theorem sourceBits_history (n : ℕ) (h : History n) :
    sourceBits (toBitString h) = ENNReal.ofReal (prob source n h) := by
  rw [sourceBits, sourceRat_history]

theorem source_prob_nonneg (n : ℕ) (h : History n) : 0 ≤ prob source n h := by
  rw [← sourceRat_history]
  exact_mod_cast sourceRat_nonneg (toBitString h)

theorem sourceBits_semimeasure : IsContinuousTreeSemimeasure sourceBits := by
  constructor
  · change sourceBits (toBitString (n := 0) ()) = 1
    rw [sourceBits_history]
    simp [prob]
  · intro x
    obtain ⟨n, h, rfl⟩ := toBitString_surjective x
    change sourceBits (toBitString (n := n+1) (h, false)) +
      sourceBits (toBitString (n := n+1) (h, true)) ≤ _
    rw [sourceBits_history, sourceBits_history, sourceBits_history,
      ← ENNReal.ofReal_add (source_prob_nonneg (n+1) (h,false))
        (source_prob_nonneg (n+1) (h,true))]
    apply ENNReal.ofReal_le_ofReal
    simp only [prob, Bool.false_eq_true, ↓reduceIte]
    linarith

theorem sourceBits_effective : IsLowerSemicomputableContinuousSemimeasure sourceBits :=
  ⟨sourceBits_semimeasure, lsc_computable_rat sourceRat_computable⟩

theorem source_member : ∃ j, treeLSCEnum j = sourceBits :=
  treeLSCEnum_complete sourceBits_effective

/-! 2c. Positive normalized priors and their mixture identity. -/

noncomputable def priorBase : ℝ≥0∞ := ENNReal.ofReal (etaQ : ℝ)
noncomputable def priorP (b : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 - etaQ) * priorWeight b : ℚ) : ℝ)
noncomputable def priorQ (b : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 - etaQ) * (1 - priorWeight b) : ℚ) : ℝ)
noncomputable def prior (p q : ℕ) (b : Bool) (i : ℕ) : ℝ≥0∞ :=
  priorBase * dyadicWeight i + (if i = p then priorP b else 0) +
    (if i = q then priorQ b else 0)

lemma priorBase_pos : 0 < priorBase := by
  exact ENNReal.ofReal_pos.mpr (by norm_num [etaQ])

lemma prior_coeff_total (b : Bool) : priorBase + priorP b + priorQ b = 1 := by
  cases b <;> norm_num only [priorBase, priorP, priorQ, etaQ, priorWeight,
    Bool.false_eq_true, ite_false, ite_true, Rat.cast_mul, Rat.cast_sub, Rat.cast_one,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] <;>
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)] <;> norm_num

lemma prior_pos (p q : ℕ) (b : Bool) (i : ℕ) : 0 < prior p q b i := by
  exact lt_of_lt_of_le (ENNReal.mul_pos priorBase_pos.ne' (dyadicWeight_pos i).ne')
    (le_add_right (le_add_right le_rfl))

lemma prior_sum (p q : ℕ) (b : Bool) : (∑' i, prior p q b i) = 1 := by
  simpa only [prior, ENNReal.tsum_add, ENNReal.tsum_mul_left,
    tsum_dyadicWeight, mul_one, tsum_ite_eq] using prior_coeff_total b

lemma priorP_compare (b : Bool) : priorP b ≤ 3 * priorP (!b) := by
  cases b <;> unfold priorP <;>
    rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)] <;>
    apply ENNReal.ofReal_le_ofReal <;> norm_num [etaQ, priorWeight]

lemma priorQ_compare (b : Bool) : priorQ b ≤ 3 * priorQ (!b) := by
  cases b <;> unfold priorQ <;>
    rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)] <;>
    apply ENNReal.ofReal_le_ofReal <;> norm_num [etaQ, priorWeight]

lemma prior_compare (p q : ℕ) (b : Bool) (i : ℕ) :
    prior p q b i ≤ 3 * prior p q (!b) i := by
  unfold prior
  rw [mul_add, mul_add]
  apply add_le_add
  · apply add_le_add
    · exact le_mul_of_one_le_left' (by norm_num : (1 : ℝ≥0∞) ≤ 3)
    · split_ifs <;> simp_all [priorP_compare]
  · split_ifs <;> simp_all [priorQ_compare]

lemma prior_mixture (ν : ℕ → BitString → ℝ≥0∞)
    (p q : ℕ) (b : Bool) (x : BitString) :
    (∑' i, prior p q b i * ν i x) =
      mixE (1 - etaQ) (mixE (priorWeight b) (ν p) (ν q))
        (continuousTreeMixture ν) x := by
  simp only [prior, add_mul, ENNReal.tsum_add]
  have hp : (∑' i, (if i = p then priorP b else 0) * ν i x) = priorP b * ν p x := by
    simp only [ite_mul, zero_mul, tsum_ite_eq]
  have hq : (∑' i, (if i = q then priorQ b else 0) * ν i x) = priorQ b * ν q x := by
    simp only [ite_mul, zero_mul, tsum_ite_eq]
  rw [hp, hq]
  simp only [mul_assoc, ENNReal.tsum_mul_left]
  have he : (1 - (1 - etaQ) : ℚ) = etaQ := by ring
  have hpos : (0 : ℝ) ≤ (1 - etaQ : ℚ) := by norm_num [etaQ]
  simp only [mixE, he, priorP, priorQ, Rat.cast_mul,
    ENNReal.ofReal_mul hpos, mul_add, mul_assoc, priorBase, continuousTreeMixture]
  simp only [mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc]

/-! 2d. Assembly. -/

lemma bayesMixture_prior (p q : ℕ)
    (hp : treeLSCEnum p = spliceBits true)
    (hq : treeLSCEnum q = spliceBits false) (b : Bool) :
    bayesMixture (prior p q b) = xiBits b := by
  funext x
  rw [bayesMixture, prior_mixture, hp, hq]
  rfl

/-- All five requested assertions, with both prior sums equal to one. -/
theorem mixture_counterexample : MixtureStatement := by
  obtain ⟨p, hp⟩ := treeLSCEnum_complete (spliceBits_effective true)
  obtain ⟨q, hq⟩ := treeLSCEnum_complete (spliceBits_effective false)
  obtain ⟨j, hj⟩ := source_member
  have hmix := bayesMixture_prior p q hp hq
  have hgap (n : ℕ) (hn : 2 ≤ n) :
      (n : ℝ)^(1/4 : ℝ)/256 ≤
        loss source (transport (bayesMixture (prior p q false))) n -
          loss source (transport (bayesMixture (prior p q true))) n := by
    rw [hmix false, hmix true]
    exact (xiBits_loss_bounds n hn).1
  refine ⟨prior p q false, prior p q true, j,
    (fun i => ⟨prior_pos p q false i, prior_pos p q true i⟩),
    prior_sum p q false, prior_sum p q true,
    (fun i => ⟨prior_compare p q false i, prior_compare p q true i⟩),
    ?_, ?_, ?_, ⟨prior_pos p q false j, prior_pos p q true j⟩,
    hgap, gap_tendsto_atTop _ hgap⟩
  · rw [hmix false]
    exact xiBits_effective false
  · rw [hmix true]
    exact xiBits_effective true
  · intro n h
    rw [hj]
    exact sourceBits_history n h

end P33Mixture
