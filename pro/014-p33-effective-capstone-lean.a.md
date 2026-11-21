**Completed and kernel-checked.** The new file compiles with Lean **4.35.0**, Mathlib **v4.35.0**, and the specified library commit. Both attached files were recompiled unchanged. The final theorem and the divergence corollary depend only on `propext`, `Classical.choice`, and `Quot.sound`.

P33Effective.lean[P33Effective.lean](sandbox:/workspace/scratch/133ab63cca14/P33Effective.lean)

```lean
/-
Effective capstone for the specified Problem 3.3 counterexample.
Lean 4.35.0, Mathlib v4.35.0, kolmogorov-complexity-lean
commit 17c50e560c337a8a702f8850a711f80a56b3cf91.
The two imported experiment files are used without modification.
-/
import HutterPrizes.P33Theorem3
import HutterPrizes.P33Theorem4
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity
import KolmogorovMathlib.Solomonoff.Domination
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.Foundation.PrimrecExtras
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped BigOperators ENNReal
open Kolmogorov RobustExperiment RobustExperiment.Theorem4

namespace P33Effective

set_option maxHeartbeats 2000000

/-! Part 1. Statement layer. -/

def toBitString : {n : ℕ} → History n → BitString
  | 0, _ => []
  | _n + 1, (h, b) => toBitString h ++ [b]

def transport (a : BitString → ℝ≥0∞) : Mass :=
  fun _ h => (a (toBitString h)).toReal


/-- Universality among the upstream normalized lower semicomputable tree semimeasures. -/
def IsUniversal (a : BitString → ℝ≥0∞) : Prop :=
  ∀ a', IsLowerSemicomputableContinuousSemimeasure a' →
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ x, a' x ≤ c * a x

/-- The four requested conclusions, with the source and action rule fixed by the attachments. -/
def EffectiveStatement : Prop :=
  ∃ ξMinus ξPlus : BitString → ℝ≥0∞,
    IsLowerSemicomputableContinuousSemimeasure ξMinus ∧
    IsLowerSemicomputableContinuousSemimeasure ξPlus ∧
    IsUniversal ξMinus ∧ IsUniversal ξPlus ∧
    (∃ r : BitString → ℚ, Computable r ∧
      ∀ n (h : History n), source.cond n h = (r (toBitString h) : ℝ)) ∧
    (∀ n : ℕ, (∑ h : History n, prob source n h) = 1) ∧
    ∀ n : ℕ, 2 ≤ n →
      (n : ℝ)^(1/4 : ℝ)/256 ≤
        loss source (transport ξMinus) n - loss source (transport ξPlus) n

/-! Part 2. Proofs and explicit witnesses. -/

/-! 2a. Histories and the universal positive real background. -/

lemma toBitString_length {n : ℕ} (h : History n) : (toBitString h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases h with ⟨h, b⟩
    simp [toBitString, ih]

lemma toBitString_surjective (x : BitString) : ∃ n, ∃ h : History n, toBitString h = x := by
  induction x using List.reverseRecOn with
  | nil => exact ⟨0, (), rfl⟩
  | append_singleton x b ih =>
    obtain ⟨n, h, rfl⟩ := ih
    exact ⟨n+1, (h,b), rfl⟩

lemma toBitString_ones (j : ℕ) : toBitString (ones j) = List.replicate j true := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [ones, toBitString, ih]
    exact List.replicate_succ'.symm

lemma toBitString_append {a : ℕ} (p : History a) (t : ℕ) (h : History t) :
    toBitString (append p t h) = toBitString p ++ toBitString h := by
  induction t with
  | zero => cases h; simp [append, toBitString]
  | succ t ih =>
    rcases h with ⟨h,b⟩
    simp only [append, toBitString, ih, List.append_assoc]

noncomputable def background : Background where
  mass := transport universalContinuousSemimeasure
  semimeasure := {
    nonneg := fun _ _ => ENNReal.toReal_nonneg
    root := by
      change (universalContinuousSemimeasure []).toReal ≤ 1
      rw [universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.1]
      simp
    children := by
      intro n h
      have hm := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
      change (universalContinuousSemimeasure (toBitString h ++ [false])).toReal +
          (universalContinuousSemimeasure (toBitString h ++ [true])).toReal ≤
        (universalContinuousSemimeasure (toBitString h)).toReal
      rw [← ENNReal.toReal_add (hm.ne_top _) (hm.ne_top _)]
      exact (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hm.ne_top _, hm.ne_top _⟩)
        (hm.ne_top _)).mpr (hm.2 _)
  }
  positive := by
    intro n h
    exact ENNReal.toReal_pos (universalContinuousSemimeasure_pos _).ne'
      (universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top _)

lemma background_root : background.mass 0 () = 1 := by
  change (universalContinuousSemimeasure []).toReal = 1
  rw [universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.1]
  simp

lemma xi_root (i : Bool) : xi background i 0 () = 1 := by
  have hm := background_root
  cases i <;> simp only [xi, mix, P, Q, spliced, scan, spliceState, ones,
    Bool.false_eq_true, ↓reduceIte] <;> rw [hm] <;> ring

/-! 2b. Computable rational branch probabilities and source. -/

def branchIndex (x : BitString) : ℕ := x.idxOf false
def stem (x : BitString) : BitString := x.take (branchIndex x + 1)
def suffix (x : BitString) : BitString := x.drop (branchIndex x + 1)

def qGamma (j : ℕ) : ℚ := 1 / (32 * (4 : ℚ)^j)

def qCond (i : Bool) (j t : ℕ) : ℚ :=
  if t < (4^j)^2 then 1/2 + (if i then qGamma j else -qGamma j) else 1/2

def qStep (i : Bool) (j : ℕ) (s : ℕ × ℚ) (b : Bool) : ℕ × ℚ :=
  (s.1+1, s.2 * (if b then qCond i j s.1 else 1-qCond i j s.1))

def qProb (i : Bool) (j : ℕ) (x : BitString) : ℚ :=
  (x.foldl (qStep i j) (0,1)).2

def coeff (i : Bool) (x : BitString) : ℚ :=
  qProb i (branchIndex x) (suffix x)

def r (x : BitString) : ℚ :=
  if branchIndex x < x.length then
    qCond true (branchIndex x) (suffix x).length else 1/2

theorem branchIndex_computable : Computable branchIndex :=
  Primrec.list_idxOf.to_comp.comp (Computable.const false) Computable.id

theorem stem_computable : Computable stem :=
  Primrec.list_take.to_comp.comp
    (Primrec.nat_add.to_comp.comp branchIndex_computable (Computable.const 1)) Computable.id

theorem suffix_computable : Computable suffix :=
  Primrec.list_drop.to_comp.comp
    (Primrec.nat_add.to_comp.comp branchIndex_computable (Computable.const 1)) Computable.id

theorem natPow_computable : Computable₂ (fun a b : ℕ => a^b) :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).to_comp

theorem qGamma_computable : Computable qGamma := by
  have hd : Computable (fun j : ℕ => 32 * 4^j) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 32)
      (natPow_computable.comp (Computable.const 4) Computable.id)
  exact computable_of_num_den (N := fun _ : ℕ => (1 : ℤ)) (D := fun j => 32*4^j)
    (Computable.const 1) hd (fun j => by positivity) (fun j => by simp [qGamma])

theorem qCond_computable (i : Bool) :
    Computable (fun p : ℕ × ℕ => qCond i p.1 p.2) := by
  have hp : Computable (fun p : ℕ × ℕ => decide (p.2 < (4^p.1)^2)) :=
    Primrec.nat_lt.decide.to_comp.comp Computable.snd
      (natPow_computable.comp
        (natPow_computable.comp (Computable.const 4) Computable.fst)
        (Computable.const 2))
  have hg : Computable (fun p : ℕ × ℕ => if i then qGamma p.1 else -qGamma p.1) := by
    cases i
    · exact ComputableReals.computable_ratNeg.comp (qGamma_computable.comp Computable.fst)
    · exact qGamma_computable.comp Computable.fst
  exact (Computable.cond hp
    (computable₂_ratAdd.comp (Computable.const (1/2)) hg)
    (Computable.const (1/2))).of_eq (fun p => by simp [qCond, Bool.cond_eq_ite])

theorem qProb_computable (i : Bool) :
    Computable (fun p : ℕ × BitString => qProb i p.1 p.2) := by
  have ht : Computable (fun p : (ℕ × BitString) × ((ℕ × ℚ) × Bool) => p.2.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hq : Computable (fun p : (ℕ × BitString) × ((ℕ × ℚ) × Bool) =>
      qCond i p.1.1 p.2.1.1) :=
    (qCond_computable i).comp
      (g := fun p : (ℕ × BitString) × ((ℕ × ℚ) × Bool) => (p.1.1, p.2.1.1))
      ((Computable.fst.comp Computable.fst).pair ht)
  have hf : Computable (fun p : (ℕ × BitString) × ((ℕ × ℚ) × Bool) =>
      if p.2.2 then qCond i p.1.1 p.2.1.1 else 1-qCond i p.1.1 p.2.1.1) :=
    (Computable.cond (Computable.snd.comp Computable.snd) hq
      (computable₂_ratSub.comp (Computable.const 1) hq)).of_eq
        (fun p => by simp [Bool.cond_eq_ite])
  have hs : Computable₂ (fun p : ℕ × BitString =>
      fun s : (ℕ × ℚ) × Bool => qStep i p.1 s.1 s.2) :=
    ((Computable.succ.comp ht).pair
      (computable₂_ratMul.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
        hf)).to₂
  have hfold : Computable (fun p : ℕ × BitString =>
      p.2.foldl (qStep i p.1) (0, (1 : ℚ))) :=
    Computable.list_foldl
      (l := fun p : ℕ × BitString => p.2)
      (g := fun _ : ℕ × BitString => (0, (1 : ℚ)))
      (h := fun p : ℕ × BitString => fun s : (ℕ × ℚ) × Bool => qStep i p.1 s.1 s.2)
      Computable.snd (Computable.const (0,1)) hs
  exact Computable.snd.comp
    (g := fun p : ℕ × BitString => p.2.foldl (qStep i p.1) (0, (1 : ℚ))) hfold


theorem coeff_computable (i : Bool) : Computable (coeff i) :=
  (qProb_computable i).comp (g := fun x : BitString => (branchIndex x, suffix x))
    (branchIndex_computable.pair suffix_computable)

theorem r_computable : Computable r := by
  have hp : Computable (fun x : BitString => decide (branchIndex x < x.length)) :=
    Primrec.nat_lt.decide.to_comp.comp branchIndex_computable Primrec.list_length.to_comp
  have hq : Computable (fun x : BitString => qCond true (branchIndex x) (suffix x).length) :=
    (qCond_computable true).comp
      (g := fun x : BitString => (branchIndex x, (suffix x).length)) (branchIndex_computable.pair
      (Primrec.list_length.to_comp.comp suffix_computable))
  exact (Computable.cond hp hq (Computable.const (1/2))).of_eq
    (fun x => by simp [r, Bool.cond_eq_ite])

theorem qCond_cast (i : Bool) (j t : ℕ) (h : History t) :
    (qCond i j t : ℝ) = (experiment (scale j) (scale_pos j) i).cond t h := by
  simp only [qCond, experiment, scale, qGamma, gamma]
  split_ifs <;> cases i <;> simp_all

theorem qCond_nonneg (i : Bool) (j t : ℕ) : 0 ≤ qCond i j t := by
  have h := (experiment (scale j) (scale_pos j) i).nonneg t (ones t)
  rw [← qCond_cast] at h
  exact_mod_cast h

theorem qCond_le_one (i : Bool) (j t : ℕ) : qCond i j t ≤ 1 := by
  have h := (experiment (scale j) (scale_pos j) i).le_one t (ones t)
  rw [← qCond_cast] at h
  exact_mod_cast h

theorem qFold_length (i : Bool) (j : ℕ) (x : BitString) (s : ℕ × ℚ) :
    (x.foldl (qStep i j) s).1 = s.1+x.length := by
  induction x generalizing s with
  | nil => simp
  | cons b x ih =>
    simp only [List.foldl_cons, ih, qStep, List.length_cons]
    omega

@[simp] theorem qProb_nil (i : Bool) (j : ℕ) : qProb i j [] = 1 := rfl

theorem qProb_append (i : Bool) (j : ℕ) (x : BitString) (b : Bool) :
    qProb i j (x++[b]) = qProb i j x *
      (if b then qCond i j x.length else 1-qCond i j x.length) := by
  simp [qProb, List.foldl_append, qStep, qFold_length]

theorem qProb_nonneg (i : Bool) (j : ℕ) (x : BitString) : 0 ≤ qProb i j x := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x b ih =>
    rw [qProb_append]
    apply mul_nonneg ih
    cases b
    · exact sub_nonneg.mpr (qCond_le_one i j x.length)
    · exact qCond_nonneg i j x.length

theorem coeff_nonneg (i : Bool) (x : BitString) : 0 ≤ coeff i x :=
  qProb_nonneg i (branchIndex x) (suffix x)

/-! 2c. Exact agreement with the history-based source and branch models. -/

@[simp] lemma idxOf_trunk (j : ℕ) :
    (List.replicate j true).idxOf false = j := by
  rw [List.idxOf_eq_length (by simp)]
  simp

@[simp] lemma idxOf_branch (j : ℕ) (ys : List Bool) :
    (List.replicate j true ++ false :: ys).idxOf false = j := by
  rw [List.idxOf_append_of_notMem (by simp)]
  simp

@[simp] lemma take_trunk (j : ℕ) :
    (List.replicate j true).take (j + 1) = List.replicate j true := by
  simp

@[simp] lemma drop_trunk (j : ℕ) :
    (List.replicate j true).drop (j + 1) = [] := by
  simp

@[simp] lemma take_branch (j : ℕ) (ys : List Bool) :
    (List.replicate j true ++ false :: ys).take (j + 1) =
      List.replicate j true ++ [false] := by
  rw [List.take_append]
  simp

@[simp] lemma drop_branch (j : ℕ) (ys : List Bool) :
    (List.replicate j true ++ false :: ys).drop (j + 1) = ys := by
  rw [List.drop_append]
  simp

lemma trunk_index_not_lt (j : ℕ) :
    ¬ (List.replicate j true).idxOf false < (List.replicate j true).length := by
  simp

lemma branch_index_lt (j : ℕ) (ys : List Bool) :
    (List.replicate j true ++ false :: ys).idxOf false <
      (List.replicate j true ++ false :: ys).length := by
  simp
@[simp] theorem stem_trunk (j : ℕ) :
    stem (List.replicate j true) = List.replicate j true := by
  simp [stem, branchIndex]

@[simp] theorem stem_branch (j : ℕ) (ys : BitString) :
    stem (List.replicate j true ++ false :: ys) = List.replicate j true ++ [false] := by
  simp [stem, branchIndex]

@[simp] theorem coeff_trunk (i : Bool) (j : ℕ) :
    coeff i (List.replicate j true) = 1 := by
  simp [coeff, suffix, branchIndex]

@[simp] theorem coeff_branch (i : Bool) (j : ℕ) (ys : BitString) :
    coeff i (List.replicate j true ++ false :: ys) = qProb i j ys := by
  simp [coeff, suffix, branchIndex]

/-- Rational branch products agree with the real products in Theorem 3. -/
theorem qProb_cast (i : Bool) (j : ℕ) {t : ℕ} (h : History t) :
    (qProb i j (toBitString h) : ℝ) =
      prob (experiment (scale j) (scale_pos j) i) t h := by
  induction t with
  | zero => cases h; simp [toBitString, prob]
  | succ t ih =>
    rcases h with ⟨h, b⟩
    rw [toBitString, qProb_append, toBitString_length]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,
      Rat.cast_mul, Rat.cast_sub, Rat.cast_one, prob]
    · rw [ih h, qCond_cast i j t h]
    · rw [ih h, qCond_cast i j t h]

/-- The string of a branch state is its unary trunk, tag, and local history. -/
theorem toBitString_word_branch (j t : ℕ) (h : History t) :
    toBitString (word (.branch j t h)).2 =
      List.replicate j true ++ false :: toBitString h := by
  simp [word, toBitString_append, toBitString, toBitString_ones, List.append_assoc]

/-- The rational conditional agrees with the real state conditional. -/
theorem r_word (s : State) :
    (r (toBitString (word s).2) : ℝ) = stateCond s := by
  cases s with
  | trunk j =>
    simp [word, toBitString_ones, r, branchIndex, stateCond]
  | branch j t h =>
    rw [toBitString_word_branch]
    have hlt : branchIndex (List.replicate j true ++ false :: toBitString h) <
        (List.replicate j true ++ false :: toBitString h).length :=
      branch_index_lt j (toBitString h)
    rw [r, ite_eq_left hlt]
    simp only [suffix, branchIndex, idxOf_branch, drop_branch, toBitString_length]
    exact qCond_cast true j t h

/-- The source in Theorem 4 has the explicitly computable rational conditional `r`. -/
theorem source_cond_r (n : ℕ) (h : History n) :
    source.cond n h = (r (toBitString h) : ℝ) := by
  have hs := r_word (scan n h)
  rw [word_scan] at hs
  exact hs.symm

/-! 2d. Lower semicomputability closure. -/

lemma lsc_add {f g : BitString → BitString → ℝ≥0∞}
    (hf : IsLSC f) (hg : IsLSC g) : IsLSC (fun x c => f x c + g x c) := by
  obtain ⟨A, hAm, hAs, hAc⟩ := hf
  obtain ⟨B, hBm, hBs, hBc⟩ := hg
  refine ⟨fun s x c => A s x c + B s x c, ?_, ?_, ?_⟩
  · intro s x c
    simp only [dyadicValue_add]
    exact add_le_add (hAm s x c) (hBm s x c)
  · intro x c
    simp only [dyadicValue_add]
    rw [← hAs x c, ← hBs x c]
    exact (ENNReal.iSup_add_iSup_of_monotone
      (monotone_nat_of_le_succ fun s => hAm s x c)
      (monotone_nat_of_le_succ fun s => hBm s x c)).symm
  · exact (Primrec.nat_add.comp Primrec.fst Primrec.snd).to_comp.comp (hAc.pair hBc)

lemma lsc_uniform {f : BitString → ℝ≥0∞} (hf : IsLSC (fun x _ => f x)) :
    IsUniformlyLowerSemicomputableTreeFamily (fun _ x => f x) := by
  obtain ⟨A, hAm, hAs, hAc⟩ := hf
  refine ⟨fun _ s x => A s x [], fun _ s x => hAm s x [],
    fun _ x => hAs x [], ?_⟩
  exact hAc.comp ((Computable.fst.comp Computable.snd).pair
    ((Computable.snd.comp Computable.snd).pair (Computable.const [])))

lemma lsc_of_uniform {f : ℕ → BitString → ℝ≥0∞}
    (hf : IsUniformlyLowerSemicomputableTreeFamily f) (e : ℕ) :
    IsLSC (fun x _ => f e x) := by
  obtain ⟨A, hAm, hAs, hAc⟩ := hf
  refine ⟨fun s x _ => A e s x, fun s x _ => hAm e s x,
    fun x _ => hAs e x, ?_⟩
  exact hAc.comp ((Computable.const e).pair
    (Computable.fst.pair (Computable.fst.comp Computable.snd)))

lemma lsc_mul {f g : BitString → ℝ≥0∞}
    (hf : IsLSC (fun x _ => f x)) (hg : IsLSC (fun x _ => g x)) :
    IsLSC (fun x _ => f x * g x) :=
  lsc_of_uniform ((lsc_uniform hf).mul (lsc_uniform hg)) 0

lemma lsc_computable_rat {r : BitString → ℚ} (hr : Computable r) :
    IsLSC (fun x _ => ENNReal.ofReal (r x : ℝ)) := by
  refine ⟨fun s x _ => ratDyadicFloor (r x) s, ?_, ?_, ?_⟩
  · exact fun s x _ => dyadicValue_ratDyadicFloor_mono_of_le (le_refl _) s
  · intro x _
    simpa using iSup_dyadicValue_ratDyadicFloor (f := fun _ : ℕ => r x) monotone_const
  · exact computable_ratDyadicFloor.comp
      (hr.comp (Computable.fst.comp Computable.snd)) Computable.fst

lemma lsc_comp {f : BitString → BitString → ℝ≥0∞} (hf : IsLSC f)
    {g : BitString → BitString} (hg : Computable g) :
    IsLSC (fun x c => f (g x) c) := by
  obtain ⟨A, hAm, hAs, hAc⟩ := hf
  refine ⟨fun s x c => A s (g x) c, fun s x c => hAm s (g x) c,
    fun x c => hAs (g x) c, ?_⟩
  exact hAc.comp (Computable.fst.pair
    ((hg.comp (Computable.fst.comp Computable.snd)).pair
      (Computable.snd.comp Computable.snd)))

lemma lsc_weighted_comp {f : BitString → ℝ≥0∞}
    (hf : IsLSC (fun x _ => f x)) {g : BitString → BitString}
    (hg : Computable g) {r : BitString → ℚ} (hr : Computable r) :
    IsLSC (fun x _ => ENNReal.ofReal (r x : ℝ) * f (g x)) :=
  lsc_mul (lsc_computable_rat hr) (lsc_comp hf hg)
noncomputable def mixE (w : ℚ) (p q : BitString → ℝ≥0∞) (x : BitString) : ℝ≥0∞ :=
  ENNReal.ofReal (w : ℝ) * p x + ENNReal.ofReal ((1 - w : ℚ) : ℝ) * q x

lemma lsc_mixE (w : ℚ) {p q : BitString → ℝ≥0∞}
    (hp : IsLSC (fun x _ => p x)) (hq : IsLSC (fun x _ => q x)) :
    IsLSC (fun x _ => mixE w p q x) :=
  lsc_add (lsc_mul (lsc_computable_rat (Computable.const w)) hp)
    (lsc_mul (lsc_computable_rat (Computable.const (1 - w))) hq)

lemma mixE_ofReal (w : ℚ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (w : ℝ) * ENNReal.ofReal a +
      ENNReal.ofReal ((1 - w : ℚ) : ℝ) * ENNReal.ofReal b =
      ENNReal.ofReal ((w : ℝ) * a + (1 - (w : ℝ)) * b) := by
  have hw0R : (0 : ℝ) ≤ w := by exact_mod_cast hw0
  have hw1R : (w : ℝ) ≤ 1 := by exact_mod_cast hw1
  rw [Rat.cast_sub, Rat.cast_one, ← ENNReal.ofReal_mul hw0R,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr hw1R),
    ← ENNReal.ofReal_add (mul_nonneg hw0R ha) (mul_nonneg (sub_nonneg.mpr hw1R) hb)]

/-! 2e. Universal effective witnesses. -/

lemma universal_of_dominance {a : BitString → ℝ≥0∞} {ε : ℝ≥0∞}
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ⊤)
    (hdom : ∀ x, ε * universalContinuousSemimeasure x ≤ a x) :
    ∀ a', IsLowerSemicomputableContinuousSemimeasure a' →
      ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ x, a' x ≤ c * a x := by
  intro a' ha'
  obtain ⟨c, hctop, hc⟩ := universalContinuousSemimeasure_isMaximal a' ha'
  refine ⟨c * ε⁻¹, ENNReal.mul_ne_top hctop (ENNReal.inv_ne_top.mpr hε0), ?_⟩
  intro x
  calc
    a' x ≤ c * universalContinuousSemimeasure x := hc x
    _ = (c * ε⁻¹) * (ε * universalContinuousSemimeasure x) := by
      rw [mul_assoc, ENNReal.inv_mul_cancel_left hε0 hεtop]
    _ ≤ (c * ε⁻¹) * a x := mul_le_mul' le_rfl (hdom x)

def etaQ : ℚ := 1 / 2 ^ 20

def priorWeight (i : Bool) : ℚ := if i then 3/4 else 1/4

noncomputable def spliceBits (i : Bool) (x : BitString) : ℝ≥0∞ :=
  ENNReal.ofReal (coeff i x : ℝ) * universalContinuousSemimeasure (stem x)

noncomputable def xiBits (i : Bool) : BitString → ℝ≥0∞ :=
  mixE (1 - etaQ)
    (mixE (priorWeight i) (spliceBits true) (spliceBits false))
    universalContinuousSemimeasure

lemma spliceBits_lsc (i : Bool) : IsLSC (fun x _ => spliceBits i x) :=
  lsc_weighted_comp
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.2
    stem_computable (coeff_computable i)

lemma xiBits_lsc (i : Bool) : IsLSC (fun x _ => xiBits i x) :=
  lsc_mixE (1 - etaQ)
    (lsc_mixE (priorWeight i) (spliceBits_lsc true) (spliceBits_lsc false))
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.2

@[simp] lemma etaQ_cast : (etaQ : ℝ) = eta := by
  norm_num [etaQ, eta]

@[simp] lemma priorWeight_cast (i : Bool) :
    (priorWeight i : ℝ) = (if i then 3/4 else 1/4) := by
  cases i <;> norm_num [priorWeight]

lemma etaQ_pos : 0 < etaQ := by norm_num [etaQ]
lemma etaQ_nonneg : 0 ≤ etaQ := etaQ_pos.le
lemma etaQ_le_one : etaQ ≤ 1 := by norm_num [etaQ]
lemma one_sub_etaQ_nonneg : 0 ≤ 1 - etaQ := sub_nonneg.mpr etaQ_le_one
lemma one_sub_etaQ_le_one : 1 - etaQ ≤ 1 := sub_le_self _ etaQ_nonneg

lemma priorWeight_nonneg (i : Bool) : 0 ≤ priorWeight i := by
  cases i <;> norm_num [priorWeight]

lemma priorWeight_le_one (i : Bool) : priorWeight i ≤ 1 := by
  cases i <;> norm_num [priorWeight]

lemma xiBits_dominates (i : Bool) (x : BitString) :
    ENNReal.ofReal eta * universalContinuousSemimeasure x ≤ xiBits i x := by
  have he : (1 - (1 - etaQ) : ℚ) = etaQ := by ring
  unfold xiBits mixE
  rw [he, etaQ_cast]
  exact le_add_self

/-! 2f. Transport, normalization, and the capstone. -/

lemma spliceBits_word (i : Bool) (s : State) :
    spliceBits i (toBitString (word s).2) = ENNReal.ofReal (spliceState background i s) := by
  have hm := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1
  cases s with
  | trunk j =>
    simp only [word, toBitString_ones, spliceBits, coeff_trunk, stem_trunk,
      Rat.cast_one, ENNReal.ofReal_one, one_mul, spliceState]
    change universalContinuousSemimeasure (List.replicate j true) =
      ENNReal.ofReal (universalContinuousSemimeasure (toBitString (ones j))).toReal
    rw [toBitString_ones, ENNReal.ofReal_toReal (hm.ne_top _)]
  | branch j t h =>
    rw [toBitString_word_branch]
    simp only [spliceBits, coeff_branch, stem_branch, qProb_cast, spliceState]
    rw [ENNReal.ofReal_mul (branchWeight_pos background j).le]
    change ENNReal.ofReal (prob (experiment (scale j) (scale_pos j) i) t h) *
        universalContinuousSemimeasure (List.replicate j true ++ [false]) =
      ENNReal.ofReal (universalContinuousSemimeasure (toBitString (n := j+1) (ones j, false))).toReal * _
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
    (universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure.1.ne_top (toBitString h))]
  change _ = ENNReal.ofReal (xi background i n h)
  rw [mixE_ofReal (1-etaQ) one_sub_etaQ_nonneg one_sub_etaQ_le_one _
    (universalContinuousSemimeasure (toBitString h)).toReal hc ENNReal.toReal_nonneg]
  simp only [Rat.cast_sub, Rat.cast_one, etaQ_cast, xi, mix, background, transport]

lemma transport_xiBits (i : Bool) : transport (xiBits i) = xi background i := by
  funext n h
  change (xiBits i (toBitString h)).toReal = xi background i n h
  rw [xiBits_history, ENNReal.toReal_ofReal ((xi_semimeasure background i).nonneg n h)]

lemma xiBits_semimeasure (i : Bool) : IsContinuousTreeSemimeasure (xiBits i) := by
  constructor
  · change xiBits i (toBitString (n := 0) ()) = 1
    rw [xiBits_history, xi_root, ENNReal.ofReal_one]
  · intro x
    obtain ⟨n,h,rfl⟩ := toBitString_surjective x
    change xiBits i (toBitString (n := n+1) (h,false)) +
      xiBits i (toBitString (n := n+1) (h,true)) ≤ _
    rw [xiBits_history i (n+1) (h,false), xiBits_history i (n+1) (h,true),
      xiBits_history i n h,
      ← ENNReal.ofReal_add ((xi_semimeasure background i).nonneg (n+1) (h,false))
        ((xi_semimeasure background i).nonneg (n+1) (h,true))]
    exact ENNReal.ofReal_le_ofReal ((xi_semimeasure background i).children n h)

lemma xiBits_effective (i : Bool) : IsLowerSemicomputableContinuousSemimeasure (xiBits i) :=
  ⟨xiBits_semimeasure i, xiBits_lsc i⟩

lemma xiBits_universal (i : Bool) :
    ∀ a', IsLowerSemicomputableContinuousSemimeasure a' →
      ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ x, a' x ≤ c * xiBits i x :=
  universal_of_dominance (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num [eta]))
    ENNReal.ofReal_ne_top (xiBits_dominates i)
theorem gap_tendsto_atTop (d : ℕ → ℝ)
    (hd : ∀ n : ℕ, 2 ≤ n → (n : ℝ)^(1/4 : ℝ)/256 ≤ d n) :
    Filter.Tendsto d Filter.atTop Filter.atTop := by
  have hp : Filter.Tendsto (fun n : ℕ => (n : ℝ)^(1/4 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
      tendsto_natCast_atTop_atTop
  exact Filter.tendsto_atTop_mono' Filter.atTop
    ((Filter.eventually_ge_atTop 2).mono fun n hn => hd n hn)
    (Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 256) hp)

/-- Both bounds from Theorem 4 hold for the effective witnesses. -/
theorem xiBits_loss_bounds (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ)^(1/4 : ℝ)/256 ≤
      loss source (transport (xiBits false)) n - loss source (transport (xiBits true)) n ∧
    loss source (transport (xiBits false)) n - loss source (transport (xiBits true)) n ≤
      (n : ℝ)^(1/4 : ℝ)/8 := by
  rw [transport_xiBits, transport_xiBits]
  exact theorem4 background n hn

/-- The effective counterexample requested in Part 1. -/
theorem effective_counterexample : EffectiveStatement := by
  refine ⟨xiBits false, xiBits true,
    xiBits_effective false, xiBits_effective true,
    xiBits_universal false, xiBits_universal true,
    ⟨r, r_computable, source_cond_r⟩, ?_, ?_⟩
  · exact branch_prob_total source
  · intro n hn
    exact (xiBits_loss_bounds n hn).1

/-- The finite-horizon loss difference actually tends to positive infinity. -/
theorem loss_gap_tendsto_atTop :
    Filter.Tendsto
      (fun n : ℕ => loss source (transport (xiBits false)) n -
        loss source (transport (xiBits true)) n)
      Filter.atTop Filter.atTop :=
  gap_tendsto_atTop _ (fun n hn => (xiBits_loss_bounds n hn).1)

end P33Effective
```

## Map from Part 1 to the requested theorem

The main result is **`P33Effective.effective_counterexample : P33Effective.EffectiveStatement`**. It supplies the explicit witnesses
\[
\xi_-=\texttt{xiBits false},
\qquad
\xi_+=\texttt{xiBits true}.
\]

| Requested conclusion | Part 1 statement | Proof |
|---|---|---|
| **1. Both are lower semicomputable continuous semimeasures.** | The two `IsLowerSemicomputableContinuousSemimeasure` conjuncts. | `xiBits_effective false` and `xiBits_effective true`, combining `xiBits_semimeasure` with `xiBits_lsc`. Root mass is exactly \(1\). |
| **2. Both are universal, with finite domination constants.** | `IsUniversal ξMinus ∧ IsUniversal ξPlus`. The definition explicitly requires `c ≠ ⊤`. | `xiBits_dominates` proves \(\eta M\leq\xi_\pm\). `universal_of_dominance` turns an upstream domination constant \(c_0\) into the finite constant \(c_0\eta^{-1}\). |
| **3. The specified source has a computable rational conditional and total mass \(1\) at every depth.** | The existential rational function and the following level-sum conjunct. | The witness is `r`; `r_computable` proves computability, `source_cond_r` proves exact equality with `Theorem4.source.cond`, and the attached `branch_prob_total source` gives normalization. |
| **4. The prescribed loss gap is at least \(n^{1/4}/256\) for every \(n\geq2\).** | The last conjunct, using `transport` for both predictors. | `transport_xiBits` identifies the transported witnesses exactly with `Theorem4.xi background false/true`. The lower bound then follows from the attached `theorem4`. |

The construction follows the suggested first-`false` decomposition. On a trunk string, `stem` is the whole string and `coeff` is \(1\). On a branch string \(1^j0h\), `stem` is \(1^j0\) and `coeff` is the rational probability of \(h\) under the corresponding finite experiment. Thus
\[
\texttt{spliceBits}\ i\ x
=
\operatorname{ofReal}(\texttt{coeff}\ i\ x)\,
M(\texttt{stem}\ x).
\]
Computability of `stem` and `coeff`, together with the proved lower-semicomputability closure lemmas, establishes the effective part of the construction.

The exact transport identity also preserves the action rule from `P33Theorem3.lean`: the losses are evaluated on precisely the same real masses as in the attached theorem.

## Deviations

- **No changes to either attached file, no additional hypotheses, and no weakening of the requested conclusions.**
- The lower-semicomputability proof uses closure under **computable rational factors**, proved through the upstream dyadic approximation machinery. This handles the construction’s dyadic coefficients without requiring a separate dyadic-only representation.
- The history conversion is defined directly and its needed properties, including surjectivity, are proved. An explicit inverse bijection is unnecessary for the transport argument.
- Two additional results are included: `xiBits_loss_bounds` preserves the upper bound \(n^{1/4}/8\), and `loss_gap_tendsto_atTop` proves that the finite-horizon loss difference tends to \(+\infty\).
- The imports use `HutterPrizes.P33Theorem3` and `HutterPrizes.P33Theorem4`, consistent with the module layout already required by the attached Theorem 4 file.