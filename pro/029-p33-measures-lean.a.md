Completed **P33Measures.lean[P33Measures.lean](sandbox:/workspace/scratch/968f33d53a5b/HutterPrizes/P33Measures.lean)**. It compiles without errors or warnings under Lean 4.35.0, Mathlib v4.35.0, and the specified upstream commit. The three frozen definitions and theorem statement are unchanged character for character. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

```lean
/- Frozen target (desk, 2026-11-21): Theorem 2 of Pro 027 (Problem 3.3 when M is a class of probability
   measures), for the class of computable measures with rational conditionals. Fidelity note at the end. -/
import HutterPrizes.P33Effective
import HutterPrizes.P27Stochastic
import HutterPrizes.P33Complexity

open scoped BigOperators ENNReal
open Kolmogorov RobustExperiment RobustExperiment.Theorem4 P33Effective

namespace P33Measures

/-- The class C: computable probability measures on binary strings given by computable rational next-bit
conditionals r(x) = ν(1 | x) ∈ [0, 1] (indexed by the conditional function; different r may give the same
measure). -/
def RatMeasure : Type := {r : BitString → ℚ // Computable r ∧ ∀ x, 0 ≤ r x ∧ r x ≤ 1}

/-- ν(x) for ν ∈ C, as the product of its conditionals (`P27Stochastic.muProb`). -/
noncomputable def measureMass (ν : RatMeasure) (x : BitString) : ℝ≥0∞ :=
  ENNReal.ofReal (P27Stochastic.muProb ν.1 x)

/-- The Bayes mixture ξ_w(x) = Σ_ν w_ν ν(x) over C. -/
noncomputable def classMixture (w : RatMeasure → ℝ≥0∞) (x : BitString) : ℝ≥0∞ :=
  ∑' ν, w ν * measureMass ν x

set_option maxHeartbeats 2000000

open P33Mixture

/-! The probability-measure class and its positive background. -/

lemma measureMass_root (ν : RatMeasure) : measureMass ν [] = 1 := by
  simp [measureMass, P27Stochastic.muProb]

lemma measureMass_children (ν : RatMeasure) (x : BitString) :
    measureMass ν (x ++ [false]) + measureMass ν (x ++ [true]) = measureMass ν x := by
  unfold measureMass
  rw [← ENNReal.ofReal_add
    (P27Stochastic.muProb_nonneg ν.1 ν.2.2 _)
    (P27Stochastic.muProb_nonneg ν.1 ν.2.2 _)]
  congr 1
  simp only [P27Stochastic.muProb_append_singleton, P27Stochastic.muCond,
    Bool.false_eq_true, ↓reduceIte]
  ring

lemma measureMass_le_one (ν : RatMeasure) (x : BitString) : measureMass ν x ≤ 1 := by
  apply ENNReal.ofReal_le_one.mpr
  induction x using List.reverseRecOn with
  | nil => simp [P27Stochastic.muProb]
  | append_singleton x b ih =>
    rw [P27Stochastic.muProb_append_singleton]
    calc
      P27Stochastic.muProb ν.1 x * P27Stochastic.muCond ν.1 x b ≤
          P27Stochastic.muProb ν.1 x * 1 :=
        mul_le_mul_of_nonneg_left (P27Stochastic.muCond_le_one ν.1 ν.2.2 x b)
          (P27Stochastic.muProb_nonneg ν.1 ν.2.2 x)
      _ ≤ 1 := by simpa using ih

lemma measureMass_ne_top (ν : RatMeasure) (x : BitString) : measureMass ν x ≠ ⊤ :=
  ENNReal.ofReal_ne_top

lemma classMixture_root (a : RatMeasure → ℝ≥0∞) : classMixture a [] = ∑' ν, a ν := by
  simp only [classMixture, measureMass_root, mul_one]

lemma classMixture_children (a : RatMeasure → ℝ≥0∞) (x : BitString) :
    classMixture a (x ++ [false]) + classMixture a (x ++ [true]) = classMixture a x := by
  unfold classMixture
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro ν
  rw [← mul_add, measureMass_children]

lemma classMixture_le_one (a : RatMeasure → ℝ≥0∞) (hsum : (∑' ν, a ν) = 1)
    (x : BitString) : classMixture a x ≤ 1 := by
  rw [← hsum]
  apply ENNReal.tsum_le_tsum
  intro ν
  calc
    a ν * measureMass ν x ≤ a ν * 1 := by gcongr; exact measureMass_le_one ν x
    _ = a ν := mul_one _

lemma classMixture_ne_top (a : RatMeasure → ℝ≥0∞) (hsum : (∑' ν, a ν) = 1)
    (x : BitString) : classMixture a x ≠ ⊤ :=
  ne_top_of_le_ne_top (by norm_num) (classMixture_le_one a hsum x)

def fairMeasure : RatMeasure :=
  ⟨fun _ => 1 / 2, Computable.const _, fun _ => by norm_num⟩

lemma fairMeasure_pos (x : BitString) : 0 < measureMass fairMeasure x := by
  apply ENNReal.ofReal_pos.mpr
  induction x using List.reverseRecOn with
  | nil => simp [P27Stochastic.muProb]
  | append_singleton x b ih =>
    rw [P27Stochastic.muProb_append_singleton]
    apply mul_pos ih
    cases b <;> norm_num [P27Stochastic.muCond, fairMeasure]

lemma classMixture_pos (a : RatMeasure → ℝ≥0∞) (ha : ∀ ν, 0 < a ν)
    (x : BitString) : 0 < classMixture a x := by
  have hterm : 0 < a fairMeasure * measureMass fairMeasure x :=
    ENNReal.mul_pos (ha fairMeasure).ne' (fairMeasure_pos x).ne'
  exact hterm.trans_le (ENNReal.le_tsum (f := fun ν => a ν * measureMass ν x) fairMeasure)

noncomputable def classBackground (a : RatMeasure → ℝ≥0∞) (ha : ∀ ν, 0 < a ν)
    (hsum : (∑' ν, a ν) = 1) : Background where
  mass := transport (classMixture a)
  semimeasure := {
    nonneg := fun _ _ => ENNReal.toReal_nonneg
    root := by
      change (classMixture a []).toReal ≤ 1
      rw [classMixture_root, hsum]
      simp
    children := by
      intro n h
      change (classMixture a (toBitString h ++ [false])).toReal +
          (classMixture a (toBitString h ++ [true])).toReal ≤
        (classMixture a (toBitString h)).toReal
      rw [← ENNReal.toReal_add (classMixture_ne_top a hsum _) (classMixture_ne_top a hsum _),
        classMixture_children]
  }
  positive := by
    intro n h
    exact ENNReal.toReal_pos (classMixture_pos a ha _).ne' (classMixture_ne_top a hsum _)

def sourceMeasure : RatMeasure :=
  ⟨r, r_computable, fun x => by
    unfold r
    split_ifs
    · exact ⟨qCond_nonneg _ _ _, qCond_le_one _ _ _⟩
    · norm_num⟩

lemma sourceMeasure_cond (n : ℕ) (h : History n) :
    source.cond n h = (sourceMeasure.1 (toBitString h) : ℝ) :=
  source_cond_r n h

lemma mu_mass (r : RatMeasure) (hr : ∀ n (h : History n),
    source.cond n h = (r.1 (toBitString h) : ℝ)) :
    ∀ n (h : History n), P27Stochastic.muProb r.1 (toBitString h) = prob source n h := by
  intro n h
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases h with ⟨h, b⟩
    simp only [toBitString, P27Stochastic.muProb_append_singleton, prob, ih,
      P27Stochastic.muCond, hr]

lemma ratMeasure_countable : Countable RatMeasure := by
  classical
  refine Function.Injective.countable
    (f := fun ν : RatMeasure => Classical.choose (Nat.Partrec.Code.exists_code.1 ν.2.1.partrec)) ?_
  intro ν μ h
  have h1 := Classical.choose_spec (Nat.Partrec.Code.exists_code.1 ν.2.1.partrec)
  have h2 := Classical.choose_spec (Nat.Partrec.Code.exists_code.1 μ.2.1.partrec)
  simp only at h
  rw [h, h2] at h1
  apply Subtype.ext
  funext x
  have := congrFun h1 (Encodable.encode x)
  simp [Encodable.encodek] at this
  exact this.symm

lemma exists_positive_prior : ∃ a : RatMeasure → ℝ≥0∞,
    (∀ ν, 0 < a ν) ∧ (∑' ν, a ν) = 1 := by
  have hc := ratMeasure_countable
  obtain ⟨ε, hε, hsum⟩ := ENNReal.exists_pos_sum_of_countable' (ε := 1) one_ne_zero RatMeasure
  have hpos : (∑' ν, ε ν) ≠ 0 := by
    intro h0
    have := (ENNReal.tsum_eq_zero.1 h0) fairMeasure
    exact (hε fairMeasure).ne' this
  refine ⟨fun ν => ε ν / ∑' ν, ε ν,
    fun ν => ENNReal.div_pos (hε ν).ne' (ne_top_of_lt hsum), ?_⟩
  simp only [div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, ENNReal.mul_inv_cancel hpos (ne_top_of_lt hsum)]

/-! Componentwise computable splicing. -/

/-- Keep the selector conditionals, then run the finite branch experiment and fair tail. -/
def spliceCond (i : Bool) (ν : RatMeasure) (x : BitString) : ℚ :=
  if branchIndex x < x.length then
    qCond i (branchIndex x) (suffix x).length else ν.1 x

lemma spliceCond_computable (i : Bool) (ν : RatMeasure) : Computable (spliceCond i ν) := by
  have hp : Computable (fun x : BitString => decide (branchIndex x < x.length)) :=
    Primrec.nat_lt.decide.to_comp.comp branchIndex_computable Primrec.list_length.to_comp
  have hq : Computable (fun x : BitString => qCond i (branchIndex x) (suffix x).length) :=
    (qCond_computable i).comp
      (g := fun x : BitString => (branchIndex x, (suffix x).length))
      (branchIndex_computable.pair (Primrec.list_length.to_comp.comp suffix_computable))
  exact (Computable.cond hp hq ν.2.1).of_eq
    (fun x => by simp [spliceCond, Bool.cond_eq_ite])

lemma spliceCond_bounds (i : Bool) (ν : RatMeasure) (x : BitString) :
    0 ≤ spliceCond i ν x ∧ spliceCond i ν x ≤ 1 := by
  unfold spliceCond
  split_ifs
  · exact ⟨qCond_nonneg _ _ _, qCond_le_one _ _ _⟩
  · exact ν.2.2 x

def spliceMeasure (i : Bool) (ν : RatMeasure) : RatMeasure :=
  ⟨spliceCond i ν, spliceCond_computable i ν, spliceCond_bounds i ν⟩

lemma spliceCond_trunk (i : Bool) (ν : RatMeasure) (j : ℕ) :
    spliceCond i ν (List.replicate j true) = ν.1 (List.replicate j true) := by
  simp [spliceCond, branchIndex]

lemma spliceCond_branch (i : Bool) (ν : RatMeasure) (j : ℕ) (ys : BitString) :
    spliceCond i ν (List.replicate j true ++ false :: ys) = qCond i j ys.length := by
  simp [spliceCond, branchIndex, suffix]

lemma muProb_splice_trunk (i : Bool) (ν : RatMeasure) (j : ℕ) :
    P27Stochastic.muProb (spliceCond i ν) (List.replicate j true) =
      P27Stochastic.muProb ν.1 (List.replicate j true) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ', P27Stochastic.muProb_append_singleton,
      P27Stochastic.muProb_append_singleton, ih]
    simp only [P27Stochastic.muCond, spliceCond_trunk]

lemma muProb_splice_tag (i : Bool) (ν : RatMeasure) (j : ℕ) :
    P27Stochastic.muProb (spliceCond i ν) (List.replicate j true ++ [false]) =
      P27Stochastic.muProb ν.1 (List.replicate j true ++ [false]) := by
  rw [P27Stochastic.muProb_append_singleton, P27Stochastic.muProb_append_singleton,
    muProb_splice_trunk]
  simp only [P27Stochastic.muCond, spliceCond_trunk]

lemma muProb_splice_branch (i : Bool) (ν : RatMeasure) (j : ℕ) (ys : BitString) :
    P27Stochastic.muProb (spliceCond i ν) (List.replicate j true ++ false :: ys) =
      P27Stochastic.muProb ν.1 (List.replicate j true ++ [false]) * (qProb i j ys : ℝ) := by
  induction ys using List.reverseRecOn with
  | nil => simp only [qProb_nil, Rat.cast_one, mul_one, muProb_splice_tag]
  | append_singleton ys b ih =>
    have hx : List.replicate j true ++ false :: (ys ++ [b]) =
        (List.replicate j true ++ false :: ys) ++ [b] := by simp
    rw [hx, P27Stochastic.muProb_append_singleton, ih, qProb_append]
    simp only [P27Stochastic.muCond, spliceCond_branch, Rat.cast_mul]
    cases b <;> simp <;> ring

lemma measureMass_splice_word (i : Bool) (ν : RatMeasure) (s : State) :
    measureMass (spliceMeasure i ν) (toBitString (word s).2) =
      P33Complexity.rawSplice (measureMass ν) i (toBitString (word s).2) := by
  cases s with
  | trunk j =>
    simp only [word, toBitString_ones, P33Complexity.rawSplice, coeff_trunk,
      Rat.cast_one, ENNReal.ofReal_one, one_mul, stem_trunk, measureMass,
      spliceMeasure, muProb_splice_trunk]
  | branch j t h =>
    rw [toBitString_word_branch]
    simp only [P33Complexity.rawSplice, coeff_branch, stem_branch, measureMass,
      spliceMeasure, muProb_splice_branch]
    rw [ENNReal.ofReal_mul (P27Stochastic.muProb_nonneg ν.1 ν.2.2 _), mul_comm]

lemma measureMass_splice (i : Bool) (ν : RatMeasure) (x : BitString) :
    measureMass (spliceMeasure i ν) x = P33Complexity.rawSplice (measureMass ν) i x := by
  obtain ⟨n, h, rfl⟩ := toBitString_surjective x
  have hs := measureMass_splice_word i ν (scan n h)
  rw [word_scan] at hs
  exact hs

/-! Pushforward priors and exact normalization. -/

noncomputable def pushPrior (a : RatMeasure → ℝ≥0∞)
    (F : RatMeasure → RatMeasure) (ρ : RatMeasure) : ℝ≥0∞ :=
  ∑' ν : {ν // F ν = ρ}, a ν

lemma pushPrior_sum (a : RatMeasure → ℝ≥0∞) (F : RatMeasure → RatMeasure) :
    (∑' ρ, pushPrior a F ρ) = ∑' ν, a ν := by
  exact ENNReal.tsum_fiberwise a F

lemma pushPrior_mixture (a : RatMeasure → ℝ≥0∞) (F : RatMeasure → RatMeasure)
    (x : BitString) :
    classMixture (pushPrior a F) x = ∑' ν, a ν * measureMass (F ν) x := by
  unfold classMixture pushPrior
  simp only [← ENNReal.tsum_mul_right]
  have h : (∑' ρ, ∑' ν : {ν // F ν = ρ}, a ν * measureMass ρ x) =
      ∑' ρ, ∑' ν : {ν // F ν = ρ}, a ν * measureMass (F ν) x := by
    apply tsum_congr
    intro ρ
    apply tsum_congr
    intro ν
    rw [ν.2]
  rw [h]
  exact ENNReal.tsum_fiberwise (fun ν => a ν * measureMass (F ν) x) F

noncomputable def classPrior (a : RatMeasure → ℝ≥0∞)
    (T : Bool → RatMeasure → RatMeasure) (b : Bool) (ρ : RatMeasure) : ℝ≥0∞ :=
  priorBase * a ρ + priorP b * pushPrior a (T true) ρ +
    priorQ b * pushPrior a (T false) ρ

lemma classPrior_sum (a : RatMeasure → ℝ≥0∞)
    (T : Bool → RatMeasure → RatMeasure) (ha : (∑' ν, a ν) = 1) (b : Bool) :
    (∑' ρ, classPrior a T b ρ) = 1 := by
  simpa only [classPrior, ENNReal.tsum_add, ENNReal.tsum_mul_left,
    pushPrior_sum, ha, mul_one] using prior_coeff_total b

lemma classPrior_pos (a : RatMeasure → ℝ≥0∞)
    (T : Bool → RatMeasure → RatMeasure) (ha : ∀ ν, 0 < a ν) (b : Bool)
    (ρ : RatMeasure) : 0 < classPrior a T b ρ := by
  exact lt_of_lt_of_le (ENNReal.mul_pos priorBase_pos.ne' (ha ρ).ne')
    (le_add_right (le_add_right le_rfl))

lemma classPrior_lower (a : RatMeasure → ℝ≥0∞)
    (T : Bool → RatMeasure → RatMeasure) (b : Bool) (ρ : RatMeasure) :
    a ρ / 2 ^ 20 ≤ classPrior a T b ρ := by
  have he : priorBase = (2 ^ 20 : ℝ≥0∞)⁻¹ := by
    norm_num [priorBase, etaQ, ENNReal.ofReal_div_of_pos]
  rw [div_eq_mul_inv, ← he, mul_comm]
  exact le_add_right (le_add_right le_rfl)

lemma classPrior_compare (a : RatMeasure → ℝ≥0∞)
    (T : Bool → RatMeasure → RatMeasure) (b : Bool) (ρ : RatMeasure) :
    classPrior a T b ρ ≤ 3 * classPrior a T (!b) ρ := by
  unfold classPrior
  rw [mul_add, mul_add]
  apply add_le_add
  · apply add_le_add
    · exact le_mul_of_one_le_left' (by norm_num : (1 : ℝ≥0∞) ≤ 3)
    · rw [← mul_assoc]
      exact mul_le_mul' (priorP_compare b) le_rfl
  · rw [← mul_assoc]
    exact mul_le_mul' (priorQ_compare b) le_rfl

lemma classPrior_mixture (a : RatMeasure → ℝ≥0∞)
    (T : Bool → RatMeasure → RatMeasure) (b : Bool) (x : BitString) :
    classMixture (classPrior a T b) x =
      mixE (1 - etaQ)
        (mixE (priorWeight b)
          (fun x => ∑' ν, a ν * measureMass (T true ν) x)
          (fun x => ∑' ν, a ν * measureMass (T false ν) x))
        (classMixture a) x := by
  have hp := pushPrior_mixture a (T true) x
  have hq := pushPrior_mixture a (T false) x
  simp only [classMixture, classPrior, add_mul, ENNReal.tsum_add,
    mul_assoc, ENNReal.tsum_mul_left]
  change priorBase * classMixture a x + priorP b * classMixture (pushPrior a (T true)) x +
    priorQ b * classMixture (pushPrior a (T false)) x = _
  rw [hp, hq]
  have he : (1 - (1 - etaQ) : ℚ) = etaQ := by ring
  have hpos : (0 : ℝ) ≤ (1 - etaQ : ℚ) := by norm_num [etaQ]
  simp only [mixE, he, priorP, priorQ, Rat.cast_mul,
    ENNReal.ofReal_mul hpos, mul_add, mul_assoc, priorBase]
  simp only [mul_comm, add_comm, add_left_comm]

/-! Exact transport to the arbitrary-background theorem. -/

lemma spliceMixture (a : RatMeasure → ℝ≥0∞) (i : Bool) (x : BitString) :
    (∑' ν, a ν * measureMass (spliceMeasure i ν) x) =
      P33Complexity.rawSplice (classMixture a) i x := by
  simp only [measureMass_splice, P33Complexity.rawSplice, classMixture]
  calc
    (∑' ν, a ν * (ENNReal.ofReal (coeff i x : ℝ) * measureMass ν (stem x))) =
        ∑' ν, ENNReal.ofReal (coeff i x : ℝ) * (a ν * measureMass ν (stem x)) := by
      apply tsum_congr
      intro ν
      ac_rfl
    _ = _ := ENNReal.tsum_mul_left

lemma classPrior_mixture_raw (a : RatMeasure → ℝ≥0∞) (b : Bool) :
    classMixture (classPrior a spliceMeasure b) = P33Complexity.rawXi (classMixture a) b := by
  funext x
  rw [classPrior_mixture]
  simp only [spliceMixture]
  rfl

lemma transport_classPrior (a : RatMeasure → ℝ≥0∞) (ha : ∀ ν, 0 < a ν)
    (hsum : (∑' ν, a ν) = 1) (b : Bool) :
    transport (classMixture (classPrior a spliceMeasure b)) =
      xi (classBackground a ha hsum) b := by
  rw [classPrior_mixture_raw]
  exact P33Complexity.transport_rawXi (classBackground a ha hsum)
    (classMixture_ne_top a hsum) rfl b

/-- 027 Theorem 2 (rational-conditional class): the source µ of the 3.3 construction is in C, and for every
strictly positive prior a on C with Σ a = 1 there are strictly positive priors w⁻, w⁺ on C, each summing to 1,
with w± ≥ a/2^20 and ratio in [1/3, 3], whose µ-expected 0-1 losses (ties toward 1) differ by ≥ n^{1/4}/256 for
all n ≥ 2, and the difference tends to +∞. -/
theorem measure_class_counterexample :
    ∃ μ : RatMeasure, (∀ n (h : History n), source.cond n h = (μ.1 (toBitString h) : ℝ)) ∧
      ∀ a : RatMeasure → ℝ≥0∞, (∀ ν, 0 < a ν) → (∑' ν, a ν) = 1 →
        ∃ wMinus wPlus : RatMeasure → ℝ≥0∞,
          (∀ ν, 0 < wMinus ν ∧ 0 < wPlus ν) ∧
          (∑' ν, wMinus ν) = 1 ∧ (∑' ν, wPlus ν) = 1 ∧
          (∀ ν, a ν / 2 ^ 20 ≤ wMinus ν ∧ a ν / 2 ^ 20 ≤ wPlus ν) ∧
          (∀ ν, wMinus ν ≤ 3 * wPlus ν ∧ wPlus ν ≤ 3 * wMinus ν) ∧
          (∀ n : ℕ, 2 ≤ n →
            (n : ℝ)^(1/4 : ℝ)/256 ≤
              loss source (transport (classMixture wMinus)) n -
                loss source (transport (classMixture wPlus)) n) ∧
          Filter.Tendsto
            (fun n : ℕ =>
              loss source (transport (classMixture wMinus)) n -
                loss source (transport (classMixture wPlus)) n)
            Filter.atTop Filter.atTop := by
  refine ⟨sourceMeasure, sourceMeasure_cond, ?_⟩
  intro a ha hsum
  have hgap (n : ℕ) (hn : 2 ≤ n) :
      (n : ℝ)^(1/4 : ℝ)/256 ≤
        loss source (transport (classMixture (classPrior a spliceMeasure false))) n -
          loss source (transport (classMixture (classPrior a spliceMeasure true))) n := by
    rw [transport_classPrior a ha hsum false, transport_classPrior a ha hsum true]
    exact (theorem4 (classBackground a ha hsum) n hn).1
  refine ⟨classPrior a spliceMeasure false, classPrior a spliceMeasure true,
    (fun ν => ⟨classPrior_pos a spliceMeasure ha false ν,
      classPrior_pos a spliceMeasure ha true ν⟩),
    classPrior_sum a spliceMeasure hsum false,
    classPrior_sum a spliceMeasure hsum true,
    (fun ν => ⟨classPrior_lower a spliceMeasure false ν,
      classPrior_lower a spliceMeasure true ν⟩),
    (fun ν => ⟨classPrior_compare a spliceMeasure false ν,
      classPrior_compare a spliceMeasure true ν⟩),
    hgap, gap_tendsto_atTop _ hgap⟩

end P33Measures

/- Fidelity note.
Source: book Problem 3.3 with Sec. 3.2.2 (p. 70), where M is a countable class of probability measures, µ ∈ M,
and ξ = Σ_ν w_ν ν with w_ν > 0, Σ w_ν = 1 ((3.5)). Pro 027 Theorem 2; referee docs/reviews/2026-11-21-referee-027.md
(correct). Reuses `source`, `loss`, `predict` (ties toward 1), `transport`, `History`, `toBitString` from the
P33 files and `muProb` from P27Stochastic (reviewed in docs/reviews/2026-11-21-fidelity-27-stochastic.md).
- Class: measures with a total computable rational conditional r into [0,1], indexed by r (a multiset of
  measures). 027 Theorem 2 covers the class with conditionals only at positive-mass histories, and all
  computable measures; both are paper steps here. Review: docs/reviews/2026-11-21-fidelity-33-measures.md.
- w± are not claimed to equal a; ties toward 1 (as in the mixture review).
- Quantifiers: one µ for all priors a; w± depend on a. η is fixed at 2^-20 (the report allows any 0 < η ≤ 2^-20).
- No claim that w± or the mixtures are computable. Upper bound (11/112)n^{1/4} not stated.
- µ ∈ C is stated through the conditionals: source.cond n h = r(toBitString h) on every history.
-/
```

### Main lemmas and construction choices

- **`sourceMeasure_cond`** gives the fixed source witness in `RatMeasure`, independently of the prior `a`. The included `ratMeasure_countable` and `exists_positive_prior` also establish that the prior hypothesis is nonvacuous.
- **`classBackground`** packages `transport (classMixture a)` as a positive background. Positivity follows from the strictly positive weight of `fairMeasure`.
- **`measureMass_splice`** proves that each computable componentwise splice has exactly the mass prescribed by `P33Complexity.rawSplice`. It preserves selector probabilities, runs the chosen branch experiment, and then emits fair bits.
- **`pushPrior_sum` and `pushPrior_mixture`** aggregate weights over fibers using `ENNReal.tsum_fiberwise`; injectivity is unnecessary. **`classPrior_sum`, `classPrior_pos`, `classPrior_lower`, and `classPrior_compare`** establish all requested prior properties.
- **`transport_classPrior`** identifies the resulting mixtures with `xi`. Taking `false` gives `wMinus`, with three quarters of the transformed weight on the negative-bias component; taking `true` gives `wPlus`. The final bound follows from `theorem4`, and divergence follows from `gap_tendsto_atTop`.

The proof follows the suggested route and reuses the existing `rawSplice`/`rawXi` transport lemmas through the additional `P33Complexity` import. The mixture identities hold at **every history, including the root**, so a nonempty-history restriction or root override is unnecessary.