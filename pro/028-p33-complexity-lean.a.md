**The frozen target is proved.** The complete file below compiles with Lean **4.35.0**, Mathlib **v4.35.0**, and the specified `kolmogorov-complexity-lean` commit. The frozen `ComplexityStatement` and theorem signature are preserved character for character.

Download: P33Complexity.lean[P33Complexity.lean](sandbox:/workspace/scratch/c0cab70f1081/HutterPrizes/P33Complexity.lean)

```lean
/- Frozen target (desk, 2026-11-21): Problem 3.3 with complexity priors (Pro 008 §4.2, Corollary 5).
   Matt's D2 answer: strengthen 3.3 before any contact. Fidelity note at the end. -/
import HutterPrizes.P33Mixture

open scoped BigOperators ENNReal
open Kolmogorov RobustExperiment RobustExperiment.Theorem4 P33Effective P33Mixture

namespace P33Complexity

/-- Both prior weight vectors are within constant factors of 2^{-K(i)}, K(i) = KPNat U i the prefix complexity of
the index i of the i-th enumerated lsc semimeasure `treeLSCEnum i`; each sums to at most 1 (book Sec. 2.4 p. 49, Problem 3.1 p. 120); their
ratio stays in [1/3, 3]; both mixtures are lower semicomputable semimeasures; µ = `treeLSCEnum j`; and the
µ-expected 0-1 loss difference is ≥ n^{1/4}/256 for n ≥ 2 and tends to +∞. -/
def ComplexityStatement (U : Map) : Prop :=
  ∃ (wMinus wPlus : ℕ → ℝ≥0∞) (j : ℕ) (c C : ℝ≥0∞),
    0 < c ∧ C ≠ ⊤ ∧
    (∀ i, c * complexityWeight (KPNat U i) ≤ wMinus i ∧ wMinus i ≤ C * complexityWeight (KPNat U i)) ∧
    (∀ i, c * complexityWeight (KPNat U i) ≤ wPlus i ∧ wPlus i ≤ C * complexityWeight (KPNat U i)) ∧
    (∑' i, wMinus i) ≤ 1 ∧ (∑' i, wPlus i) ≤ 1 ∧
    (∀ i, wMinus i ≤ 3 * wPlus i ∧ wPlus i ≤ 3 * wMinus i) ∧
    (∀ x, bayesMixture wMinus (x ++ [false]) + bayesMixture wMinus (x ++ [true]) ≤ bayesMixture wMinus x) ∧
    (∀ x, bayesMixture wPlus (x ++ [false]) + bayesMixture wPlus (x ++ [true]) ≤ bayesMixture wPlus x) ∧
    bayesMixture wMinus [] ≤ 1 ∧ bayesMixture wPlus [] ≤ 1 ∧
    IsLSC (fun x _ => bayesMixture wMinus x) ∧ IsLSC (fun x _ => bayesMixture wPlus x) ∧
    (∀ n (h : History n),
      treeLSCEnum j (toBitString h) = ENNReal.ofReal (prob source n h)) ∧
    (∀ n : ℕ, 2 ≤ n →
      (n : ℝ)^(1/4 : ℝ)/256 ≤
        loss source (transport (bayesMixture wMinus)) n -
          loss source (transport (bayesMixture wPlus)) n) ∧
    Filter.Tendsto
      (fun n : ℕ =>
        loss source (transport (bayesMixture wMinus)) n -
          loss source (transport (bayesMixture wPlus)) n)
      Filter.atTop Filter.atTop

/-! The complexity-weighted background. -/

set_option maxHeartbeats 200000

lemma complexityWeight_KPNat_pos (U : Map) (hU : IsOptimalPrefixConditional U) (i : ℕ) :
    0 < complexityWeight (KPNat U i) := by
  have hk : KPNat U i ≠ ⊤ := by
    obtain ⟨c, hc⟩ := KPPlain_le_two_mul_length U hU
    refine ne_top_of_le_natCast (n := 2 * (natToBitString i).length + c) ?_
    calc
      KPNat U i = KPPlain U (natToBitString i) := KPNat_def U i
      _ ≤ 2 * ((natToBitString i).length : ENat) + (c : ENat) := hc _
      _ = ((2 * (natToBitString i).length + c : ℕ) : ENat) := by push_cast; ring
  exact (complexityWeight_pos_iff (KPNat U i)).2 hk

noncomputable def complexityBase (U : Map) : BitString → ℝ≥0∞ :=
  bayesMixture (fun i => complexityWeight (KPNat U i))

lemma enumeration_uniform : IsUniformlyLowerSemicomputableTreeFamily treeLSCEnum := by
  refine ⟨fun i s x => treeSanitize (fun s out _ => makeMono (approxEnum i) s out []) s x,
    ?_, ?_, ?_⟩
  · intro i s x
    exact treeSanitize_stage_mono _ (fun s out _ => makeMono_mono _ s out []) s x
  · intro i x
    rfl
  · have hp : Computable (fun p : ℕ × ℕ × BitString =>
        (p.1, p.2.1, p.2.2, ([] : BitString))) :=
      Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
        ((Computable.snd.comp Computable.snd).pair (Computable.const [])))
    exact (treeLSCEnumApprox_uniform_computable.comp hp).of_eq (fun _ => rfl)

lemma complexityBase_lsc (U : Map) (hU : IsOptimalPrefixConditional U) :
    IsLSC (fun x _ => complexityBase U x) :=
  isLSC_tsum_of_uniform ((isUniformlyLSC_complexityWeight_KPNat U hU).mul enumeration_uniform)

lemma complexityBase_children (U : Map) (x : BitString) :
    complexityBase U (x ++ [false]) + complexityBase U (x ++ [true]) ≤
      complexityBase U x := by
  unfold complexityBase bayesMixture
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro i
  rw [← mul_add]
  gcongr
  exact (treeLSCEnum_isLowerSemicomputableContinuousSemimeasure i).1.2 x

lemma complexityBase_le_one (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) :
    complexityBase U x ≤ 1 := by
  change (∑' i, complexityWeight (KPNat U i) * treeLSCEnum i x) ≤ 1
  refine le_trans (ENNReal.tsum_le_tsum (fun i => ?_))
    (tsum_complexityWeight_KPNat_le_one U hU)
  exact mul_le_of_le_one_right' ((treeLSCEnum_isLowerSemicomputableContinuousSemimeasure i).1.le_one x)

lemma complexityBase_root_le_one (U : Map) (hU : IsOptimalPrefixConditional U) :
    complexityBase U [] ≤ 1 := complexityBase_le_one U hU []

lemma complexityBase_ne_top (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) :
    complexityBase U x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (complexityBase_le_one U hU x)

lemma complexityBase_pos (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) :
    0 < complexityBase U x := by
  obtain ⟨j, hj⟩ := treeLSCEnum_complete
    (show IsLowerSemicomputableContinuousSemimeasure lengthMeasure from
      ⟨lengthMeasure_isContinuousTreeSemimeasure, lengthMeasure_isLSC_core⟩)
  have hd : complexityWeight (KPNat U j) * treeLSCEnum j x ≤ complexityBase U x := by
    change _ ≤ ∑' i, complexityWeight (KPNat U i) * treeLSCEnum i x
    exact ENNReal.le_tsum (f := fun i => complexityWeight (KPNat U i) * treeLSCEnum i x) j
  rw [hj] at hd
  have hp : 0 < lengthMeasure x := by
    exact pos_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num [lengthMeasure]))
  exact lt_of_lt_of_le
    (ENNReal.mul_pos (complexityWeight_KPNat_pos U hU j).ne' hp.ne') hd

noncomputable def complexityBackground (U : Map) (hU : IsOptimalPrefixConditional U) : Background where
  mass := transport (complexityBase U)
  semimeasure := {
    nonneg := fun _ _ => ENNReal.toReal_nonneg
    root := by
      change (complexityBase U []).toReal ≤ 1
      exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using complexityBase_root_le_one U hU)
    children := by
      intro n h
      change (complexityBase U (toBitString h ++ [false])).toReal +
          (complexityBase U (toBitString h ++ [true])).toReal ≤
        (complexityBase U (toBitString h)).toReal
      rw [← ENNReal.toReal_add (complexityBase_ne_top U hU _) (complexityBase_ne_top U hU _)]
      exact (ENNReal.toReal_le_toReal
        (ENNReal.add_ne_top.mpr ⟨complexityBase_ne_top U hU _, complexityBase_ne_top U hU _⟩)
        (complexityBase_ne_top U hU _)).mpr (complexityBase_children U _)
  }
  positive := by
    intro n h
    exact ENNReal.toReal_pos (complexityBase_pos U hU _).ne'
      (complexityBase_ne_top U hU _)

/-! The two priors and their Bayes mixtures. -/

lemma prefixIndexComplexity_ne_top {U : Map} (hU : IsOptimalPrefixConditional U)
    (n : ℕ) : KPNat U n ≠ ⊤ :=
  (complexityWeight_pos_iff _).mp (complexityWeight_KPNat_pos U hU n)

noncomputable def complexityPrior (U : Map) (p q : ℕ) (b : Bool) (i : ℕ) : ℝ≥0∞ :=
  priorBase * complexityWeight (KPNat U i) + (if i = p then priorP b else 0) +
    (if i = q then priorQ b else 0)

lemma complexityPrior_sum (U : Map) (hU : IsOptimalPrefixConditional U)
    (p q : ℕ) (b : Bool) : (∑' i, complexityPrior U p q b i) ≤ 1 := by
  simp only [complexityPrior, ENNReal.tsum_add, ENNReal.tsum_mul_left, tsum_ite_eq]
  calc
    priorBase * (∑' i, complexityWeight (KPNat U i)) + priorP b + priorQ b ≤
        priorBase * 1 + priorP b + priorQ b := by
      gcongr
      exact tsum_complexityWeight_KPNat_le_one U hU
    _ = 1 := by simpa only [mul_one] using prior_coeff_total b

lemma complexityPrior_compare (U : Map) (p q : ℕ) (b : Bool) (i : ℕ) :
    complexityPrior U p q b i ≤ 3 * complexityPrior U p q (!b) i := by
  unfold complexityPrior
  rw [mul_add, mul_add]
  apply add_le_add
  · apply add_le_add
    · exact le_mul_of_one_le_left' (by norm_num : (1 : ℝ≥0∞) ≤ 3)
    · split_ifs <;> simp_all [priorP_compare]
  · split_ifs <;> simp_all [priorQ_compare]

lemma complexityPrior_lower (U : Map) (p q : ℕ) (b : Bool) (i : ℕ) :
    priorBase * complexityWeight (KPNat U i) ≤ complexityPrior U p q b i :=
  le_add_right (le_add_right le_rfl)

lemma priorP_le_one (b : Bool) : priorP b ≤ 1 := by
  calc
    priorP b ≤ priorBase + priorP b + priorQ b := by
      exact le_add_right (le_add_left le_rfl)
    _ = 1 := prior_coeff_total b

lemma priorQ_le_one (b : Bool) : priorQ b ≤ 1 := by
  calc
    priorQ b ≤ priorBase + priorP b + priorQ b := le_add_left le_rfl
    _ = 1 := prior_coeff_total b

noncomputable def complexityPriorUpper (U : Map) (p q : ℕ) : ℝ≥0∞ :=
  priorBase + (complexityWeight (KPNat U p))⁻¹ +
    (complexityWeight (KPNat U q))⁻¹

lemma complexityPriorUpper_ne_top (U : Map) (hU : IsOptimalPrefixConditional U)
    (p q : ℕ) : complexityPriorUpper U p q ≠ ⊤ := by
  apply ENNReal.add_ne_top.mpr
  constructor
  · apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.ofReal_ne_top
    · apply ENNReal.inv_ne_top.mpr
      exact ((complexityWeight_pos_iff _).mpr (prefixIndexComplexity_ne_top hU p)).ne'
  · apply ENNReal.inv_ne_top.mpr
    exact ((complexityWeight_pos_iff _).mpr (prefixIndexComplexity_ne_top hU q)).ne'

lemma complexityPrior_upper (U : Map) (hU : IsOptimalPrefixConditional U)
    (p q : ℕ) (b : Bool) (i : ℕ) :
    complexityPrior U p q b i ≤
      complexityPriorUpper U p q * complexityWeight (KPNat U i) := by
  have hpos (i : ℕ) : complexityWeight (KPNat U i) ≠ 0 :=
    ((complexityWeight_pos_iff _).mpr (prefixIndexComplexity_ne_top hU i)).ne'
  have hfinite (i : ℕ) : complexityWeight (KPNat U i) ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num) (complexityWeight_le_one _)
  unfold complexityPrior complexityPriorUpper
  rw [add_mul, add_mul]
  apply add_le_add
  · apply add_le_add le_rfl
    by_cases hi : i = p
    · subst i
      rw [ite_eq_left rfl, ENNReal.inv_mul_cancel (hpos p) (hfinite p)]
      exact priorP_le_one b
    · simp only [ite_eq_right hi]
      exact zero_le
  · by_cases hi : i = q
    · subst i
      rw [ite_eq_left rfl, ENNReal.inv_mul_cancel (hpos q) (hfinite q)]
      exact priorQ_le_one b
    · simp only [ite_eq_right hi]
      exact zero_le

lemma complexityPrior_bounds (U : Map) (hU : IsOptimalPrefixConditional U)
    (p q : ℕ) (b : Bool) (i : ℕ) :
    priorBase * complexityWeight (KPNat U i) ≤ complexityPrior U p q b i ∧
      complexityPrior U p q b i ≤
        complexityPriorUpper U p q * complexityWeight (KPNat U i) :=
  ⟨complexityPrior_lower U p q b i, complexityPrior_upper U hU p q b i⟩

lemma complexityPrior_mixture (U : Map) (ν : ℕ → BitString → ℝ≥0∞)
    (p q : ℕ) (b : Bool) (x : BitString) :
    (∑' i, complexityPrior U p q b i * ν i x) =
      mixE (1 - etaQ) (mixE (priorWeight b) (ν p) (ν q))
        (fun x => ∑' i, complexityWeight (KPNat U i) * ν i x) x := by
  simp only [complexityPrior, add_mul, ENNReal.tsum_add]
  have hp : (∑' i, (if i = p then priorP b else 0) * ν i x) = priorP b * ν p x := by
    simp only [ite_mul, zero_mul, tsum_ite_eq]
  have hq : (∑' i, (if i = q then priorQ b else 0) * ν i x) = priorQ b * ν q x := by
    simp only [ite_mul, zero_mul, tsum_ite_eq]
  rw [hp, hq]
  simp only [mul_assoc, ENNReal.tsum_mul_left]
  have he : (1 - (1 - etaQ) : ℚ) = etaQ := by ring
  have hpos : (0 : ℝ) ≤ (1 - etaQ : ℚ) := by norm_num [etaQ]
  simp only [mixE, he, priorP, priorQ, Rat.cast_mul,
    ENNReal.ofReal_mul hpos, mul_add, mul_assoc, priorBase]
  simp only [mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc]

lemma bayesMixture_children (w : ℕ → ℝ≥0∞) (x : BitString) :
    bayesMixture w (x ++ [false]) + bayesMixture w (x ++ [true]) ≤
      bayesMixture w x := by
  unfold bayesMixture
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro i
  rw [← mul_add]
  gcongr
  exact (treeLSCEnum_isLowerSemicomputableContinuousSemimeasure i).1.2 x

lemma bayesMixture_root (w : ℕ → ℝ≥0∞) : bayesMixture w [] = ∑' i, w i := by
  unfold bayesMixture
  congr 1
  funext i
  rw [(treeLSCEnum_isLowerSemicomputableContinuousSemimeasure i).1.1, mul_one]

lemma bayesMixture_root_le (w : ℕ → ℝ≥0∞) (hw : (∑' i, w i) ≤ 1) :
    bayesMixture w [] ≤ 1 := by
  rw [bayesMixture_root]
  exact hw

/-! Root-one representatives and invariance of loss. -/

noncomputable def rawSplice (a : BitString → ℝ≥0∞) (i : Bool) (x : BitString) : ℝ≥0∞ :=
  ENNReal.ofReal (coeff i x : ℝ) * a (stem x)

noncomputable def rootSplice (a : BitString → ℝ≥0∞) (i : Bool) (x : BitString) : ℝ≥0∞ :=
  if x = [] then 1 else rawSplice a i x

lemma rawSplice_lsc {a : BitString → ℝ≥0∞}
    (ha : IsLSC (fun x _ => a x)) (i : Bool) : IsLSC (fun x _ => rawSplice a i x) :=
  lsc_weighted_comp ha stem_computable (coeff_computable i)

lemma lsc_root_override {a : BitString → ℝ≥0∞}
    (ha : IsLSC (fun x _ => a x)) :
    IsLSC (fun x (_ : BitString) => if x = [] then 1 else a x) := by
  obtain ⟨A, hA_mono, hA_sup, hA_comp⟩ := ha
  refine ⟨fun s x _ => if x = [] then 2 ^ s else A s x [], ?_, ?_, ?_⟩
  · intro s x _
    by_cases hx : x = []
    · subst hx; simp [dyadicValue_two_pow_eq_one]
    · simp only [ite_eq_right hx]; exact hA_mono s x []
  · intro x _
    by_cases hx : x = []
    · subst hx; simp [dyadicValue_two_pow_eq_one]
    · simp only [ite_eq_right hx]; exact hA_sup x []
  · have hpred : Computable (fun p : ℕ × BitString × BitString => decide (p.2.1 = [])) :=
      (PrimrecRel.decide Primrec.eq).to_comp.comp
        (Computable.fst.comp Computable.snd) (Computable.const [])
    have hpow2 : Computable (fun p : ℕ × BitString × BitString => (2 : ℕ) ^ p.1) :=
      primrec_two_pow_aux.to_comp.comp Computable.fst
    have hAcomp' : Computable (fun p : ℕ × BitString × BitString => A p.1 p.2.1 []) :=
      hA_comp.comp (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
        (Computable.const [])))
    exact (Computable.cond hpred hpow2 hAcomp').of_eq
      (fun p => by by_cases h : p.2.1 = [] <;> simp [h])

lemma rootSplice_lsc {a : BitString → ℝ≥0∞}
    (ha : IsLSC (fun x _ => a x)) (i : Bool) : IsLSC (fun x _ => rootSplice a i x) :=
  lsc_root_override (rawSplice_lsc ha i)

lemma rootSplice_eq {a : BitString → ℝ≥0∞} {i : Bool} {x : BitString}
    (hx : x ≠ []) : rootSplice a i x = rawSplice a i x := ite_eq_right hx

lemma rawSplice_word {a : BitString → ℝ≥0∞} (M : Background)
    (ha : ∀ x, a x ≠ ⊤) (hM : M.mass = transport a) (i : Bool) (s : State) :
    rawSplice a i (toBitString (word s).2) = ENNReal.ofReal (spliceState M i s) := by
  have hmass (n : ℕ) (h : History n) :
      ENNReal.ofReal (M.mass n h) = a (toBitString h) := by
    rw [hM]
    exact ENNReal.ofReal_toReal (ha _)
  cases s with
  | trunk j =>
    simp only [word, toBitString_ones, rawSplice, coeff_trunk, stem_trunk,
      Rat.cast_one, ENNReal.ofReal_one, one_mul, spliceState]
    rw [hmass, toBitString_ones]
  | branch j t h =>
    rw [toBitString_word_branch]
    simp only [rawSplice, coeff_branch, stem_branch, qProb_cast, spliceState]
    rw [ENNReal.ofReal_mul (branchWeight_pos M j).le]
    unfold branchWeight
    rw [hmass]
    simp only [toBitString, toBitString_ones, mul_comm]

lemma rawSplice_history {a : BitString → ℝ≥0∞} (M : Background)
    (ha : ∀ x, a x ≠ ⊤) (hM : M.mass = transport a) (i : Bool) (n : ℕ) (h : History n) :
    rawSplice a i (toBitString h) = ENNReal.ofReal (spliced M i n h) := by
  have hx := rawSplice_word M ha hM i (scan n h)
  rw [word_scan] at hx
  exact hx

lemma rawSplice_children {a : BitString → ℝ≥0∞} (M : Background)
    (ha : ∀ x, a x ≠ ⊤) (hM : M.mass = transport a) (i : Bool) (x : BitString) :
    rawSplice a i (x ++ [false]) + rawSplice a i (x ++ [true]) ≤ rawSplice a i x := by
  obtain ⟨n, h, rfl⟩ := toBitString_surjective x
  have hm := spliced_semimeasure M i
  change rawSplice a i (toBitString (n := n+1) (h,false)) +
    rawSplice a i (toBitString (n := n+1) (h,true)) ≤ _
  rw [rawSplice_history M ha hM i (n+1) (h,false),
    rawSplice_history M ha hM i (n+1) (h,true), rawSplice_history M ha hM i n h,
    ← ENNReal.ofReal_add (hm.nonneg (n+1) (h,false)) (hm.nonneg (n+1) (h,true))]
  exact ENNReal.ofReal_le_ofReal (hm.children n h)

lemma rawSplice_root_le_one {a : BitString → ℝ≥0∞} (M : Background)
    (ha : ∀ x, a x ≠ ⊤) (hM : M.mass = transport a) (i : Bool) :
    rawSplice a i [] ≤ 1 := by
  change rawSplice a i (toBitString (n := 0) ()) ≤ 1
  rw [rawSplice_history M ha hM]
  exact ENNReal.ofReal_le_one.mpr (spliced_semimeasure M i).root

lemma rootSplice_effective {a : BitString → ℝ≥0∞} (M : Background)
    (ha : ∀ x, a x ≠ ⊤) (hM : M.mass = transport a)
    (hlsc : IsLSC (fun x _ => a x)) (i : Bool) :
    IsLowerSemicomputableContinuousSemimeasure (rootSplice a i) := by
  refine ⟨⟨by simp [rootSplice], ?_⟩, rootSplice_lsc hlsc i⟩
  intro x
  rw [rootSplice_eq (by simp : x ++ [false] ≠ []),
    rootSplice_eq (by simp : x ++ [true] ≠ [])]
  by_cases hx : x = []
  · subst x
    simpa [rootSplice] using
      (rawSplice_children M ha hM i []).trans (rawSplice_root_le_one M ha hM i)
  · rw [rootSplice_eq hx]
    exact rawSplice_children M ha hM i x

lemma loss_eq_of_succ_eq (μ : Model) {s t : Mass}
    (h : ∀ n (x : History n) b, s (n+1) (x,b) = t (n+1) (x,b)) (N : ℕ) :
    loss μ s N = loss μ t N := by
  simp only [loss, stepLoss, predict, h]

lemma loss_eq_of_nonempty (μ : Model) {a b : BitString → ℝ≥0∞}
    (h : ∀ x, x ≠ [] → a x = b x) (N : ℕ) :
    loss μ (transport a) N = loss μ (transport b) N := by
  apply loss_eq_of_succ_eq μ _ N
  intro n x c
  change (a (toBitString x ++ [c])).toReal = (b (toBitString x ++ [c])).toReal
  rw [h _ (by simp)]

/-! Transport to the arbitrary-background theorem. -/

noncomputable def rawXi (a : BitString → ℝ≥0∞) (i : Bool) : BitString → ℝ≥0∞ :=
  mixE (1 - etaQ)
    (mixE (priorWeight i) (rawSplice a true) (rawSplice a false)) a

lemma rawXi_history {a : BitString → ℝ≥0∞} (M : Background)
    (ha : ∀ x, a x ≠ ⊤) (hM : M.mass = transport a)
    (i : Bool) (n : ℕ) (h : History n) :
    rawXi a i (toBitString h) = ENNReal.ofReal (xi M i n h) := by
  have hp := (P_semimeasure M).nonneg n h
  have hq := (Q_semimeasure M).nonneg n h
  have hw0 : (0 : ℝ) ≤ (if i then 3/4 else 1/4) := by cases i <;> norm_num
  have hw1 : (if i then 3/4 else 1/4 : ℝ) ≤ 1 := by cases i <;> norm_num
  have hc : 0 ≤ mix (if i then 3/4 else 1/4) (P M) (Q M) n h :=
    (IsSemimeasure.mix (P_semimeasure M) (Q_semimeasure M) _ hw0 hw1).nonneg n h
  have hcore :
      mixE (priorWeight i) (rawSplice a true) (rawSplice a false) (toBitString h) =
        ENNReal.ofReal (mix (if i then 3/4 else 1/4) (P M) (Q M) n h) := by
    rw [mixE, rawSplice_history M ha hM, rawSplice_history M ha hM]
    simpa only [priorWeight_cast, P, Q, mix] using
      mixE_ofReal (priorWeight i) (priorWeight_nonneg i) (priorWeight_le_one i)
        (P M n h) (Q M n h) hp hq
  have hmass : a (toBitString h) = ENNReal.ofReal (M.mass n h) := by
    rw [hM]
    exact (ENNReal.ofReal_toReal (ha _)).symm
  unfold rawXi
  rw [mixE, hcore, hmass]
  rw [mixE_ofReal (1-etaQ) one_sub_etaQ_nonneg one_sub_etaQ_le_one _
    (M.mass n h) hc (M.semimeasure.nonneg n h)]
  simp only [Rat.cast_sub, Rat.cast_one, etaQ_cast, xi, mix]

lemma transport_rawXi {a : BitString → ℝ≥0∞} (M : Background)
    (ha : ∀ x, a x ≠ ⊤) (hM : M.mass = transport a) (i : Bool) :
    transport (rawXi a i) = xi M i := by
  funext n h
  change (rawXi a i (toBitString h)).toReal = xi M i n h
  rw [rawXi_history M ha hM,
    ENNReal.toReal_ofReal ((xi_semimeasure M i).nonneg n h)]

/-! The exact mixture and loss identities. -/

lemma complexityPrior_mixture_eq (U : Map) (p q : ℕ)
    (hp : treeLSCEnum p = rootSplice (complexityBase U) true)
    (hq : treeLSCEnum q = rootSplice (complexityBase U) false) (b : Bool) :
    bayesMixture (complexityPrior U p q b) =
      mixE (1 - etaQ)
        (mixE (priorWeight b) (rootSplice (complexityBase U) true)
          (rootSplice (complexityBase U) false)) (complexityBase U) := by
  funext x
  rw [bayesMixture, complexityPrior_mixture, hp, hq]
  rfl

lemma complexityPrior_loss (U : Map) (hU : IsOptimalPrefixConditional U) (p q : ℕ)
    (hp : treeLSCEnum p = rootSplice (complexityBase U) true)
    (hq : treeLSCEnum q = rootSplice (complexityBase U) false) (b : Bool) (n : ℕ) :
    loss source (transport (bayesMixture (complexityPrior U p q b))) n =
      loss source (xi (complexityBackground U hU) b) n := by
  rw [← transport_rawXi (complexityBackground U hU) (complexityBase_ne_top U hU) rfl b]
  apply loss_eq_of_nonempty
  intro x hx
  rw [complexityPrior_mixture_eq U p q hp hq b]
  simp only [rawXi, mixE, rootSplice_eq hx]

lemma complexityPrior_lsc (U : Map) (hU : IsOptimalPrefixConditional U) (p q : ℕ)
    (hp : treeLSCEnum p = rootSplice (complexityBase U) true)
    (hq : treeLSCEnum q = rootSplice (complexityBase U) false) (b : Bool) :
    IsLSC (fun x _ => bayesMixture (complexityPrior U p q b) x) := by
  rw [complexityPrior_mixture_eq U p q hp hq b]
  exact lsc_mixE (1 - etaQ)
    (lsc_mixE (priorWeight b)
      (rootSplice_lsc (complexityBase_lsc U hU) true)
      (rootSplice_lsc (complexityBase_lsc U hU) false))
    (complexityBase_lsc U hU)

theorem complexity_counterexample (U : Map) (hU : IsOptimalPrefixConditional U) :
    ComplexityStatement U := by
  have heff (b : Bool) :
      IsLowerSemicomputableContinuousSemimeasure (rootSplice (complexityBase U) b) :=
    rootSplice_effective (complexityBackground U hU) (complexityBase_ne_top U hU) rfl
      (complexityBase_lsc U hU) b
  obtain ⟨p, hp⟩ := treeLSCEnum_complete (heff true)
  obtain ⟨q, hq⟩ := treeLSCEnum_complete (heff false)
  obtain ⟨j, hj⟩ := source_member
  have hgap (n : ℕ) (hn : 2 ≤ n) :
      (n : ℝ)^(1/4 : ℝ)/256 ≤
        loss source (transport (bayesMixture (complexityPrior U p q false))) n -
          loss source (transport (bayesMixture (complexityPrior U p q true))) n := by
    rw [complexityPrior_loss U hU p q hp hq false n,
      complexityPrior_loss U hU p q hp hq true n]
    exact (theorem4 (complexityBackground U hU) n hn).1
  refine ⟨complexityPrior U p q false, complexityPrior U p q true, j,
    priorBase, complexityPriorUpper U p q,
    priorBase_pos, complexityPriorUpper_ne_top U hU p q,
    complexityPrior_bounds U hU p q false, complexityPrior_bounds U hU p q true,
    complexityPrior_sum U hU p q false, complexityPrior_sum U hU p q true,
    (fun i => ⟨complexityPrior_compare U p q false i,
      complexityPrior_compare U p q true i⟩),
    bayesMixture_children _, bayesMixture_children _,
    bayesMixture_root_le _ (complexityPrior_sum U hU p q false),
    bayesMixture_root_le _ (complexityPrior_sum U hU p q true),
    complexityPrior_lsc U hU p q hp hq false,
    complexityPrior_lsc U hU p q hp hq true,
    ?_, hgap, gap_tendsto_atTop _ hgap⟩
  intro n h
  rw [hj]
  exact sourceBits_history n h

end P33Complexity

/- Fidelity note.
Source: book Problem 3.3 (Sec. 3.2.9, p. 81, class M_U; Σ w ≤ 1: Sec. 2.4 p. 49, Problem 3.1 p. 120); Hutter's standard universal prior
w_ν = 2^{-K(ν)}; Pro 008 §4.2 Corollary 5 (weights ≍ 2^{-K_C(i)}). Builds on `P33Mixture` (review:
docs/reviews/2026-11-21-fidelity-33-mixture.md, faithful with caveats) with the same source µ, `loss`, `predict`
(ties toward 1), `transport`, `treeLSCEnum`.
- K(ν) is read as K(i) for the enumeration index i of ν (book p. 48: "K(ν_i) := K(i)" for the multiset M_U).
  Weights are per index; the total weight of one distinct ν is not bounded above by C·2^{-K(ν)}.
  the weights are within constant factors of 2^{-K(i)}, not equal to it (exact 2^{-K} weights are 008 Theorem 6,
  a separate target).
- Σ w ≤ 1 (not = 1), so the mixtures have root ≤ 1; they are stated as lsc tree semimeasures with root ≤ 1 rather
  than the upstream root-1 class. The 0-1 Bayes action compares s(h0) with s(h1), so it is scale-invariant.
- c, C, j may depend on U. µ is in the class (index j), with weight ≥ c·2^{-K(j)} > 0.
- Not stated: universality of the mixtures (paper step from c·2^{-K(i)} ≤ w_i); lsc or computable weights;
  measure classes (M_comp). The earlier "same mixtures over the full M_U" paper step does not carry over.
- Proof hint (review): P, Q built from M = Σ 2^{-K(i)} ν_i have root < 1; use root-1 versions (value 1 at [])
  and a lemma that `loss` reads only levels ≥ 1.
- Review: docs/reviews/2026-11-21-fidelity-33-complexity.md (faithful with caveats).
-/
```

## Deviations

**None to the frozen statement.** All helpers are included in this single file. The attached results are reused through `HutterPrizes.P33Mixture`; their files are unchanged.

The proof needs only the bound \(M(\epsilon)\le 1\). It does not need to establish the strict inequality mentioned in the proof hint.

## Verification

- The complete file compiled successfully, with no errors or warnings.
- The frozen definition, theorem signature, and fidelity note were checked for exact textual preservation.
- There is no `sorry`, `admit`, new axiom, or `native_decide`.
- `#print axioms P33Complexity.complexity_counterexample` reports exactly **`[propext, Classical.choice, Quot.sound]`**.

## Proof outline

Set \(a_i=2^{-K_U(i)}\) and \(M=\sum_i a_i\nu_i\). Kraft gives \(M(\epsilon)\le1\), uniform lower semicomputability gives the required effectivity, and the occurrence of `lengthMeasure` in the enumeration gives positivity at every string. Thus \(M\) supplies a `Background`.

Construct the two spliced models from this background and change their values at the empty string to one. These completed models remain lower semicomputable tree semimeasures, so `treeLSCEnum_complete` supplies their indices \(p,q\).

With \(\eta=2^{-20}\), the two priors are
\[
w_i^-=\eta a_i+(1-\eta)\frac14\,\mathbf1_{i=p}
                 +(1-\eta)\frac34\,\mathbf1_{i=q},
\qquad
w_i^+=\eta a_i+(1-\eta)\frac34\,\mathbf1_{i=p}
                 +(1-\eta)\frac14\,\mathbf1_{i=q}.
\]
The common comparison constants used in the proof are
\[
c=\eta,\qquad C=\eta+a_p^{-1}+a_q^{-1}.
\]
They satisfy \(c>0\) and \(C<\infty\), and the displayed formulas yield the prior-sum and factor-three bounds.

Finally, the mixture identity agrees with the imported `xi` construction on every nonempty string. Every prediction reads only two child strings, so completing the root preserves the cumulative loss exactly. The imported `theorem4` therefore gives the specified \(n^{1/4}/256\) lower bound, and `gap_tendsto_atTop` gives divergence to \(+\infty\).