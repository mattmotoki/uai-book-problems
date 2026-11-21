**Completed and verified.** The frozen definitions and the statement of `P27Stochastic.expected_lower_bound_io` are preserved character for character.

The single file compiles **without warnings** under Lean **4.35.0**, Mathlib **v4.35.0**, and the specified library commit `17c50e560c337a8a702f8850a711f80a56b3cf91`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. There are no proof holes, new axioms, or uses of `native_decide`.

Download: P27Stochastic.lean[P27Stochastic.lean](sandbox:/workspace/scratch/3bc6ab06518f/HutterPrizes/P27Stochastic.lean) · [Saved copy](https://chatgpt.com/library?file_id=libfile_fde3_f-c6ae3ed9a4048191b6c55e3010d65226_55156f90431c8191a9d99c52c310f59a&account_id=personal)

```lean
/-
Theorem 1 of 020b, Problem 2.7 stochastic.
Lean 4.35.0, Mathlib v4.35.0, kolmogorov-complexity-lean
commit 17c50e560c337a8a702f8850a711f80a56b3cf91.
The frozen definitions and theorem statement are preserved verbatim.
-/
import HutterPrizes.P27F
import HutterPrizes.P33Effective
import HutterPrizes.P27BlockBound
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import Mathlib.Data.Nat.Size

open scoped BigOperators ENNReal
open Kolmogorov Kolmogorov.SelectedBits

namespace P27Stochastic

/-! Statement layer. -/

/-- The true environment µ, given by computable rational next-bit conditionals `r x = µ(1 | x)`. -/
def muCond (r : BitString → ℚ) (x : BitString) (b : Bool) : ℝ :=
  if b then (r x : ℝ) else 1 - (r x : ℝ)

/-- µ(x) as the product of its conditionals along x. -/
def muProb (r : BitString → ℚ) : BitString → ℝ
  | [] => 1
  | x => (List.range x.length).foldl
      (fun p i => p * muCond r (x.take i) (x.getD i false)) 1

/-- Expected one-step L1 error of the normalized predictor `a_norm` at time `t` (history length t-1):
  A_t = Σ_{|x| = t-1} µ(x) Σ_b |a_norm(b|x) − µ(b|x)|. -/
noncomputable def expAbsErr (a : BitString → ℝ≥0∞) (r : BitString → ℚ) (t : ℕ) : ℝ :=
  ∑ v : Fin (t - 1) → Bool, muProb r (List.ofFn v) *
    ∑ b : Bool, |normalizedSiblingProb a (List.ofFn v) b - muCond r (List.ofFn v) b|

/-- Expected one-step squared error: S_t = Σ_{|x| = t-1} µ(x) Σ_b (a_norm(b|x) − µ(b|x))². -/
noncomputable def expSqErr (a : BitString → ℝ≥0∞) (r : BitString → ℚ) (t : ℕ) : ℝ :=
  ∑ v : Fin (t - 1) → Bool, muProb r (List.ofFn v) *
    ∑ b : Bool, (normalizedSiblingProb a (List.ofFn v) b - muCond r (List.ofFn v) b) ^ 2

/-- 2^{-K(t)} with K(t) = KPNat U t, the same K on naturals as `HutterPrizes.normalized_lower_bound`. -/
noncomputable def w (U : Map) (t : ℕ) : ℝ := ((2 : ℝ)⁻¹) ^ (KPNat U t).toNat

set_option maxHeartbeats 2000000

/-! ## Prefix probabilities -/

lemma muProb_eq_foldl (r : BitString → ℚ) (x : BitString) :
    muProb r x = (List.range x.length).foldl
      (fun p i => p * muCond r (x.take i) (x.getD i false)) 1 := by
  cases x <;> rfl

lemma muProb_nil (r : BitString → ℚ) : muProb r [] = 1 := rfl

lemma muProb_append_singleton (r : BitString → ℚ) (x : BitString) (b : Bool) :
    muProb r (x ++ [b]) = muProb r x * muCond r x b := by
  rw [muProb_eq_foldl, List.length_append, List.length_singleton, List.range_succ,
    List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hh : (List.range x.length).foldl
      (fun p i => p * muCond r ((x ++ [b]).take i) ((x ++ [b]).getD i false)) 1 =
      muProb r x := by
    rw [muProb_eq_foldl]
    apply List.foldl_ext
    intro p i hi
    have hi' : i < x.length := List.mem_range.mp hi
    rw [List.take_append_of_le_length hi'.le, List.getD_append _ _ _ _ hi']
  rw [hh, List.take_append_of_le_length (le_refl _), List.take_length,
    List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma muCond_nonneg (r : BitString → ℚ) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (x : BitString) (b : Bool) : 0 ≤ muCond r x b := by
  have h0 : (0 : ℝ) ≤ r x := by exact_mod_cast (hr01 x).1
  have h1 : (r x : ℝ) ≤ 1 := by exact_mod_cast (hr01 x).2
  cases b <;> simp only [muCond, Bool.false_eq_true, ↓reduceIte] <;> linarith

lemma muCond_le_one (r : BitString → ℚ) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (x : BitString) (b : Bool) : muCond r x b ≤ 1 := by
  have h0 : (0 : ℝ) ≤ r x := by exact_mod_cast (hr01 x).1
  have h1 : (r x : ℝ) ≤ 1 := by exact_mod_cast (hr01 x).2
  cases b <;> simp only [muCond, Bool.false_eq_true, ↓reduceIte] <;> linarith

lemma muCond_total (r : BitString → ℚ) (x : BitString) :
    (∑ b : Bool, muCond r x b) = 1 := by simp [muCond]

lemma muProb_nonneg (r : BitString → ℚ) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (x : BitString) : 0 ≤ muProb r x := by
  induction x using List.reverseRecOn with
  | nil => simp [muProb]
  | append_singleton x b ih =>
    rw [muProb_append_singleton]
    exact mul_nonneg ih (muCond_nonneg r hr01 x b)

/-! ## Computable rare-continuation environments -/

def rationalCond (r : BitString → ℚ) (x : BitString) (b : Bool) : ℚ :=
  if b then r x else 1 - r x

def rationalProb (r : BitString → ℚ) (x : BitString) : ℚ :=
  (List.range x.length).foldl
    (fun p i => p * rationalCond r (x.take i) (x.getD i false)) 1

lemma rationalCond_cast (r : BitString → ℚ) (x : BitString) (b : Bool) :
    (rationalCond r x b : ℝ) = muCond r x b := by
  cases b <;> simp [rationalCond, muCond]

lemma rationalProb_cast (r : BitString → ℚ) (x : BitString) :
    (rationalProb r x : ℝ) = muProb r x := by
  have hfold (l : List ℕ) (q : ℚ) :
      ((l.foldl (fun p i => p * rationalCond r (x.take i) (x.getD i false)) q : ℚ) : ℝ) =
      l.foldl (fun p i => p * muCond r (x.take i) (x.getD i false)) (q : ℝ) := by
    induction l generalizing q with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldl_cons, ih, Rat.cast_mul, rationalCond_cast]
  cases x with
  | nil => simp [rationalProb, muProb]
  | cons b x =>
    simpa only [rationalProb, muProb, Rat.cast_one] using hfold (List.range (b :: x).length) 1

lemma rationalProb_computable {f : ℕ → BitString → ℚ}
    (hf : Computable (fun p : ℕ × BitString => f p.1 p.2)) :
    Computable (fun p : ℕ × BitString => rationalProb (f p.1) p.2) := by
  have hx : Computable (fun p : (ℕ × BitString) × (ℚ × ℕ) => p.1.2) := Computable.snd.comp Computable.fst
  have hi : Computable (fun p : (ℕ × BitString) × (ℚ × ℕ) => p.2.2) := Computable.snd.comp Computable.snd
  have ht : Computable (fun p : (ℕ × BitString) × (ℚ × ℕ) => p.1.2.take p.2.2) :=
    Computable₂.comp Primrec.list_take.to_comp hi hx
  have hb : Computable (fun p : (ℕ × BitString) × (ℚ × ℕ) => p.1.2.getD p.2.2 false) :=
    ((Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)).to_comp
  have hr : Computable (fun p : (ℕ × BitString) × (ℚ × ℕ) => f p.1.1 (p.1.2.take p.2.2)) :=
    hf.comp (g := fun p : (ℕ × BitString) × (ℚ × ℕ) => (p.1.1, p.1.2.take p.2.2))
      ((Computable.fst.comp Computable.fst).pair ht)
  have hc : Computable (fun p : (ℕ × BitString) × (ℚ × ℕ) =>
      rationalCond (f p.1.1) (p.1.2.take p.2.2) (p.1.2.getD p.2.2 false)) :=
    (Computable.cond hb hr (computable₂_ratSub.comp (Computable.const 1) hr)).of_eq
      (fun p => by simp [rationalCond, Bool.cond_eq_ite])
  have hs : Computable₂ (fun p : ℕ × BitString => fun s : ℚ × ℕ =>
      s.1 * rationalCond (f p.1) (p.2.take s.2) (p.2.getD s.2 false)) :=
    (computable₂_ratMul.comp (Computable.fst.comp Computable.snd) hc).to₂
  unfold rationalProb
  exact Computable.list_foldl
    (l := fun p : ℕ × BitString => List.range p.2.length)
    (g := fun _ : ℕ × BitString => (1 : ℚ))
    (h := fun p : ℕ × BitString => fun s : ℚ × ℕ =>
      s.1 * rationalCond (f p.1) (p.2.take s.2) (p.2.getD s.2 false))
    ((Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)).to_comp)
    (Computable.const 1) hs

lemma uniform_of_computable_rat {f : ℕ → BitString → ℚ}
    (hf : Computable (fun p : ℕ × BitString => f p.1 p.2)) :
    IsUniformlyLowerSemicomputableTreeFamily
      (fun n x => ENNReal.ofReal (f n x : ℝ)) := by
  refine ⟨fun n s x => ratDyadicFloor (f n x) s, ?_, ?_, ?_⟩
  · exact fun n s x => dyadicValue_ratDyadicFloor_mono_of_le (le_refl _) s
  · intro n x
    simpa using iSup_dyadicValue_ratDyadicFloor
      (f := fun _ : ℕ => f n x) monotone_const
  · exact computable_ratDyadicFloor.comp
      (hf.comp (g := fun p : ℕ × ℕ × BitString => (p.1, p.2.2))
        (Computable.fst.pair (Computable.snd.comp Computable.snd)))
      (Computable.fst.comp Computable.snd)

def rareBit (r : BitString → ℚ) (x : BitString) : Bool :=
  decide (r x + r x ≤ 1)

def rareCond (r : BitString → ℚ) (k : ℕ) (x : BitString) : ℚ :=
  if x.length < k then r x else if rareBit r x then 1 else 0

noncomputable def rareFamily (r : BitString → ℚ) (n : ℕ) (x : BitString) : ℝ≥0∞ :=
  ENNReal.ofReal (muProb (rareCond r (2 ^ n)) x)

lemma rareCond_computable (r : BitString → ℚ) (hr : Computable r) :
    Computable (fun p : ℕ × BitString => rareCond r (2 ^ p.1) p.2) := by
  have hpred : Computable (fun p : ℕ × BitString =>
      decide (p.2.length < 2 ^ p.1)) :=
    (Primrec.nat_lt.decide.to_comp.comp
      (Primrec.list_length.to_comp.comp Computable.snd)
      (comp_pow.comp Computable.fst))
  have hrare : Computable (fun p : ℕ × BitString => rareBit r p.2) :=
    computable_ratLeOne.comp
      (computable₂_ratAdd.comp (hr.comp Computable.snd) (hr.comp Computable.snd))
  exact (Computable.cond hpred (hr.comp Computable.snd)
    (Computable.cond hrare (Computable.const 1) (Computable.const 0))).of_eq
    (fun p => by simp [rareCond, Bool.cond_eq_ite])

lemma rareFamily_uniform (r : BitString → ℚ) (hr : Computable r) :
    IsUniformlyLowerSemicomputableTreeFamily (rareFamily r) := by
  change IsUniformlyLowerSemicomputableTreeFamily
    (fun n x => ENNReal.ofReal (muProb (rareCond r (2 ^ n)) x))
  simpa only [rationalProb_cast] using
    uniform_of_computable_rat
      (f := fun n x => rationalProb (rareCond r (2^n)) x)
      (rationalProb_computable (f := fun n x => rareCond r (2^n) x)
        (rareCond_computable r hr))

lemma rareCond_bounds (r : BitString → ℚ) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (k : ℕ) (x : BitString) : 0 ≤ rareCond r k x ∧ rareCond r k x ≤ 1 := by
  simp only [rareCond]
  split_ifs <;> simp_all

lemma rareBit_small (r : BitString → ℚ) (x : BitString) :
    muCond r x (rareBit r x) ≤ (1 / 2 : ℝ) := by
  unfold rareBit muCond
  by_cases h : r x + r x ≤ 1
  · simp only [h, decide_true, ↓reduceIte]
    have : (r x : ℝ) + (r x : ℝ) ≤ 1 := by exact_mod_cast h
    linarith
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    have : (1 : ℝ) < (r x : ℝ) + (r x : ℝ) := by exact_mod_cast (lt_of_not_ge h)
    linarith

lemma rareCond_at_rareBit (r : BitString → ℚ) (k : ℕ) (x : BitString)
    (hx : k ≤ x.length) : muCond (rareCond r k) x (rareBit r x) = 1 := by
  have hlt : ¬ x.length < k := by omega
  simp only [muCond, rareCond, hlt, ↓reduceIte]
  cases rareBit r x <;> norm_num

lemma rareProb_before (r : BitString → ℚ) (k : ℕ) (x : BitString)
    (hx : x.length ≤ k) : muProb (rareCond r k) x = muProb r x := by
  induction x using List.reverseRecOn with
  | nil => rfl
  | append_singleton x b ih =>
    have hlen : x.length < k := by
      simp only [List.length_append, List.length_singleton] at hx
      omega
    rw [muProb_append_singleton, muProb_append_singleton, ih (by omega)]
    congr 1
    simp [muCond, rareCond, hlen]

lemma rareFamily_continuous (r : BitString → ℚ)
    (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (n : ℕ) :
    IsContinuousTreeSemimeasure (rareFamily r n) := by
  have hbound := rareCond_bounds r hr01 (2^n)
  constructor
  · simp [rareFamily, muProb_nil]
  · intro x
    have hp := muProb_nonneg (rareCond r (2^n)) hbound x
    have h0 := muCond_nonneg (rareCond r (2^n)) hbound x false
    have h1 := muCond_nonneg (rareCond r (2^n)) hbound x true
    simp only [rareFamily, muProb_append_singleton]
    rw [← ENNReal.ofReal_add (mul_nonneg hp h0) (mul_nonneg hp h1)]
    apply ENNReal.ofReal_le_ofReal
    simp only [muCond, Bool.false_eq_true, ↓reduceIte]
    nlinarith

lemma rareFamily_prefixFree (r : BitString → ℚ)
    (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (n : ℕ) (S : Finset BitString)
    (hS : IsPrefixFree (S : Set BitString)) : ∑ x ∈ S, rareFamily r n x ≤ 1 :=
  (rareFamily_continuous r hr01 n).sum_antichain_le S hS

lemma rare_continuation (r : BitString → ℚ)
    (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (k ℓ : ℕ) (x : BitString)
    (hx : x.length = k) :
    ∃ z : BitString, z.length = ℓ ∧
      muProb (rareCond r k) (x ++ z) = muProb r x ∧
      muProb r (x ++ z) ≤ (1 / 2 : ℝ)^ℓ * muProb r x := by
  induction ℓ with
  | zero =>
    refine ⟨[], rfl, ?_, ?_⟩
    · simpa using rareProb_before r k x hx.le
    · simp
  | succ ℓ ih =>
    obtain ⟨z, hzlen, hzrare, hzsmall⟩ := ih
    let b := rareBit r (x ++ z)
    refine ⟨z ++ [b], by simp [hzlen], ?_, ?_⟩
    · rw [← List.append_assoc, muProb_append_singleton, hzrare,
        rareCond_at_rareBit r k (x++z) (by simp [hx, hzlen])]
      ring
    · rw [← List.append_assoc, muProb_append_singleton, pow_succ]
      calc
        muProb r (x ++ z) * muCond r (x ++ z) b ≤
            muProb r (x ++ z) * (1 / 2) :=
          mul_le_mul_of_nonneg_left (rareBit_small r (x ++ z))
            (muProb_nonneg r hr01 (x ++ z))
        _ ≤ ((1 / 2 : ℝ)^ℓ * muProb r x) * (1 / 2) :=
          mul_le_mul_of_nonneg_right hzsmall (by norm_num)
        _ = _ := by ring

lemma rareFamily_continuation (r : BitString → ℚ)
    (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (n ℓ : ℕ) (x : BitString)
    (hx : x.length = 2^n) :
    ∃ z : BitString, z.length = ℓ ∧
      rareFamily r n (x ++ z) = ENNReal.ofReal (muProb r x) ∧
      muProb r (x ++ z) ≤ (1 / 2 : ℝ)^ℓ * muProb r x := by
  obtain ⟨z, hzlen, hzrare, hzsmall⟩ := rare_continuation r hr01 (2^n) ℓ x hx
  exact ⟨z, hzlen, congrArg ENNReal.ofReal hzrare, hzsmall⟩

/-! ## Dyadic coding weights and eventual tail decay -/

lemma codingKPNat_ne_top {U : Map} (hU : IsOptimalPrefixConditional U) (n : ℕ) :
    KPNat U n ≠ ⊤ := by
  obtain ⟨c, hc⟩ := KPPlain_le_two_mul_length U hU
  refine ne_top_of_le_ne_top (ENat.natCast_ne_top (2 * (natToBitString n).length + c)) ?_
  simpa only [KPNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hc (natToBitString n)

/-- Index of the dyadic block, with irrelevant small inputs sent to zero. -/
def codingBlockIndex (t : ℕ) : ℕ := (Nat.bits (t - 1)).length - 1

lemma codingBlockIndex_computable : Computable codingBlockIndex := by
  exact (Primrec.nat_sub.comp
    (Primrec.list_length.comp (primrec_natBits.comp
      (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))) (Primrec.const 1)).to_comp

lemma codingBlockIndex_eq (n k : ℕ) (hk : k < 2 ^ n) :
    codingBlockIndex (2 ^ n + k + 1) = n := by
  simp only [codingBlockIndex, Nat.add_sub_cancel, Nat.size_eq_bits_len]
  have hlow : n < (2 ^ n + k).size := Nat.lt_size.mpr (by omega)
  have hupp : (2 ^ n + k).size ≤ n + 1 := Nat.size_le.mpr (by
    rw [pow_succ]
    omega)
  omega

noncomputable def codingBlockMass (U : Map) (x : BitString) : ℝ≥0∞ :=
  ∑' t : ℕ, if natToBitString (codingBlockIndex t) = x then
    complexityWeight (KPNat U t) else 0

lemma codingBlockMass_lsc (U : Map) (hU : IsOptimalPrefixConditional U) :
    IsLSC (fun x _ => codingBlockMass U x) := by
  apply isLSC_tsum_of_uniform
  obtain ⟨A, hmono, hsup, hcomp⟩ := isUniformlyLSC_complexityWeight_KPNat U hU
  refine ⟨fun t s x => if natToBitString (codingBlockIndex t) = x then A t s x else 0,
    ?_, ?_, ?_⟩
  · intro t s x
    by_cases hx : natToBitString (codingBlockIndex t) = x
    · simpa only [ite_eq_left hx] using hmono t s x
    · simp only [ite_eq_right hx, dyadicValue_zero, le_refl]
  · intro t x
    by_cases hx : natToBitString (codingBlockIndex t) = x
    · simpa only [ite_eq_left hx] using hsup t x
    · simp only [ite_eq_right hx, dyadicValue_zero, iSup_const]
  · have ht : Computable (fun p : ℕ × ℕ × BitString =>
        natToBitString (codingBlockIndex p.1)) :=
      computable_natToBitString.comp (codingBlockIndex_computable.comp Computable.fst)
    have hx : Computable (fun p : ℕ × ℕ × BitString => p.2.2) :=
      Computable.snd.comp Computable.snd
    exact (Computable.cond
      ((PrimrecRel.decide Primrec.eq).to_comp.comp ht hx) hcomp
      (Computable.const 0)).of_eq (fun p => by simp)

lemma codingBlockMass_semimeasure (U : Map) (hU : IsOptimalPrefixConditional U) :
    IsSemimeasure (codingBlockMass U) := by
  change (∑' x : BitString, ∑' t : ℕ,
    if natToBitString (codingBlockIndex t) = x then complexityWeight (KPNat U t) else 0) ≤ 1
  rw [ENNReal.tsum_comm]
  simpa using tsum_complexityWeight_KPNat_le_one U hU

lemma dyadic_complexity_mass_le (U : Map) (n : ℕ) :
    (∑ k ∈ Finset.range (2 ^ n), complexityWeight (KPNat U (2 ^ n + k + 1))) ≤
      codingBlockMass U (natToBitString n) := by
  let f : ℕ → ℝ≥0∞ := fun t => if natToBitString (codingBlockIndex t) = natToBitString n
    then complexityWeight (KPNat U t) else 0
  have hsub : (∑ k ∈ Finset.range (2 ^ n), f (2 ^ n + k + 1)) ≤ ∑' t, f t := by
    calc
      _ ≤ ∑' k, f (2 ^ n + k + 1) := ENNReal.sum_le_tsum _
      _ ≤ ∑' t, f t := ENNReal.tsum_comp_le_tsum_of_injective
        (f := fun k : ℕ => 2 ^ n + k + 1) (by intro i j hij; dsimp at hij; omega) f
  calc
    _ = ∑ k ∈ Finset.range (2 ^ n), f (2 ^ n + k + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [f, codingBlockIndex_eq n k (Finset.mem_range.mp hk)]
    _ ≤ _ := hsub

lemma dyadic_weight_sum_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∑ k ∈ Finset.range (2 ^ n), w U (2 ^ n + k + 1)) ≤ C * w U n := by
  obtain ⟨c, hc⟩ := lowerSemicomputableSemimeasure_le_prefixComplexityWeight
    ⟨codingBlockMass_semimeasure U hU, codingBlockMass_lsc U hU⟩ hU
  refine ⟨(2 : ℝ) ^ c, by positivity, ?_⟩
  intro n
  have h := (mul_le_mul' (le_refl ((2 : ℝ≥0∞)⁻¹ ^ c))
    (dyadic_complexity_mass_le U n)).trans (hc (natToBitString n))
  have hn : prefixComplexityWeight U (natToBitString n) ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (complexityWeight_le_one _)
  have hreal := ENNReal.toReal_mono hn h
  have hw (t : ℕ) : (complexityWeight (KPNat U t)).toReal = w U t := by
    rw [← ENat.natCast_toNat (codingKPNat_ne_top hU t), complexityWeight_coe]
    simp [w]
  have hf (t : ℕ) : complexityWeight (KPNat U t) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (complexityWeight_le_one _)
  change (∑ k ∈ Finset.range (2 ^ n), w U (2 ^ n + k + 1)) ≤ (2 : ℝ) ^ c * w U n
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, ENNReal.toReal_sum (fun k hk => hf _)] at hreal
  change (2 : ℝ)⁻¹ ^ c * (∑ k ∈ Finset.range (2 ^ n),
      (complexityWeight (KPNat U (2 ^ n + k + 1))).toReal) ≤
        (complexityWeight (KPNat U n)).toReal at hreal
  simp only [hw] at hreal
  have hpos : (0 : ℝ) < 2 ^ c := by positivity
  have hmul := mul_le_mul_of_nonneg_left hreal hpos.le
  simpa [inv_pow, ← mul_assoc, ne_of_gt hpos] using hmul

lemma complexity_toNat_linear_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, (KPNat U n).toNat ≤ 2 * (n + 1) + c := by
  obtain ⟨c, hc⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c, fun n => ?_⟩
  have hcode : (natToBitString n).length ≤ n + 1 := by
    have hsize : (n + 1).size ≤ n + 1 := Nat.size_le.mpr (Nat.lt_two_pow_self)
    simpa only [natToBitString, List.length_dropLast, Nat.size_eq_bits_len] using
      (Nat.sub_le (n + 1).size 1).trans hsize
  have hknat : (KPNat U n).toNat ≤ 2 * (natToBitString n).length + c := by
    have hcast : ((KPNat U n).toNat : ENat) ≤
        2 * (natToBitString n).length + c :=
      (ENat.natCast_toNat (codingKPNat_ne_top hU n)).trans_le (hc _)
    exact_mod_cast hcast
  omega

lemma four_mul_le_two_pow (n : ℕ) (hn : 4 ≤ n) : 4 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    omega

lemma eventually_half_pow_le_weight (U : Map) (hU : IsOptimalPrefixConditional U)
    (a₀ : ℝ) (ha₀ : 0 < a₀) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (1 / 2 : ℝ) ^ (2 ^ n) ≤ a₀ * w U n / 4 := by
  obtain ⟨c, hc⟩ := complexity_toNat_linear_bound U hU
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < a₀ / 4 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨c + m + 4, ?_⟩
  intro n hn
  have hfour := four_mul_le_two_pow n (by omega)
  have hindex : (KPNat U n).toNat + m ≤ 2 ^ n := by
    have := hc n
    omega
  calc
    (1 / 2 : ℝ) ^ (2 ^ n) ≤ (1 / 2 : ℝ) ^ ((KPNat U n).toNat + m) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hindex
    _ = w U n * (1 / 2 : ℝ) ^ m := by simp [pow_add, w]
    _ ≤ w U n * (a₀ / 4) := mul_le_mul_of_nonneg_left hm.le (by unfold w; positivity)
    _ = a₀ * w U n / 4 := by ring

/-! ## Finite-model bridge and expected squared error -/

noncomputable section

def toList : {n : ℕ} → P27.History n → BitString
  | 0, _ => []
  | _ + 1, (x,b) => toList x ++ [b]

lemma toList_length {n : ℕ} (x : P27.History n) : (toList x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rcases x with ⟨x,b⟩; simp [toList, ih]

lemma toList_append {r : ℕ} (x : P27.History r) (n : ℕ) (y : P27.History n) :
    toList (P27.append x n y) = toList x ++ toList y := by
  induction n with
  | zero => simp [P27.append, toList]
  | succ n ih => rcases y with ⟨y,b⟩; simp [P27.append, toList, ih, List.append_assoc]

def historyEquiv : (n : ℕ) → P27.History n ≃ (Fin n → Bool)
  | 0 => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ()
      left_inv := by intro x; cases x; rfl
      right_inv := by intro f; funext i; exact Fin.elim0 i }
  | n+1 => ((Equiv.prodCongr (historyEquiv n) (Equiv.refl Bool)).trans
      (Equiv.prodComm _ _)).trans (Fin.snocEquiv (fun _ => Bool))

lemma historyEquiv_toList (n : ℕ) (x : P27.History n) :
    List.ofFn (historyEquiv n x) = toList x := by
  induction n with
  | zero => simp [toList]
  | succ n ih =>
    rcases x with ⟨x,b⟩
    change List.ofFn (Fin.snoc (historyEquiv n x) b) = toList x ++ [b]
    rw [List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, ih]

lemma toList_surjective {n : ℕ} (x : BitString) (hx : x.length = n) :
    ∃ y : P27.History n, toList y = x := by
  subst n
  refine ⟨(historyEquiv x.length).symm x.get, ?_⟩
  rw [← historyEquiv_toList, Equiv.apply_symm_apply, List.ofFn_get]

def trueModel (r : BitString → ℚ) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) : P27.Model where
  cond n x := (r (toList x) : ℝ)
  nonneg n x := by exact_mod_cast (hr01 (toList x)).1
  le_one n x := by exact_mod_cast (hr01 (toList x)).2

lemma trueModel_bitProb (r : BitString → ℚ) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (n : ℕ) (x : P27.History n) (b : Bool) :
    P27.bitProb (trueModel r hr01) n x b = muCond r (toList x) b := rfl

lemma trueModel_prob (r : BitString → ℚ) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (n : ℕ) (x : P27.History n) :
    P27.prob (trueModel r hr01) n x = muProb r (toList x) := by
  induction n with
  | zero => simp [P27.prob, toList, muProb]
  | succ n ih =>
    rcases x with ⟨x,b⟩
    simp only [P27.prob, toList, muProb_append_singleton, trueModel_bitProb, ih]

lemma universal_toReal_pos (a : BitString → ℝ≥0∞)
    (ha : IsLowerSemicomputableContinuousSemimeasure a) (hua : P33Effective.IsUniversal a)
    (x : BitString) : 0 < (a x).toReal := by
  obtain ⟨c,hc,hd⟩ := hua universalContinuousSemimeasure
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure
  apply ENNReal.toReal_pos _ (ha.1.ne_top x)
  intro hx
  have hh := hd x
  rw [hx, mul_zero] at hh
  exact (not_le_of_gt (universalContinuousSemimeasure_pos x)) hh

lemma norm_den_pos (a : BitString → ℝ≥0∞)
    (ha : IsLowerSemicomputableContinuousSemimeasure a) (hua : P33Effective.IsUniversal a)
    (x : BitString) :
    0 < (a (x++[false])).toReal + (a (x++[true])).toReal :=
  add_pos (universal_toReal_pos a ha hua _) (universal_toReal_pos a ha hua _)

lemma normalized_nonneg (a : BitString → ℝ≥0∞) (x : BitString) (b : Bool) :
    0 ≤ normalizedSiblingProb a x b := by unfold normalizedSiblingProb; positivity

lemma normalized_le_one (a : BitString → ℝ≥0∞)
    (ha : IsLowerSemicomputableContinuousSemimeasure a) (hua : P33Effective.IsUniversal a)
    (x : BitString) (b : Bool) : normalizedSiblingProb a x b ≤ 1 := by
  rw [normalizedSiblingProb, div_le_one (norm_den_pos a ha hua x)]
  cases b <;> linarith [ENNReal.toReal_nonneg (a := a (x++[false])),
    ENNReal.toReal_nonneg (a := a (x++[true]))]

lemma normalized_false (a : BitString → ℝ≥0∞)
    (ha : IsLowerSemicomputableContinuousSemimeasure a) (hua : P33Effective.IsUniversal a)
    (x : BitString) :
    1 - normalizedSiblingProb a x true = normalizedSiblingProb a x false := by
  unfold normalizedSiblingProb
  have h := (norm_den_pos a ha hua x).ne'
  field_simp
  ring

def predictorModel (a : BitString → ℝ≥0∞)
    (ha : IsLowerSemicomputableContinuousSemimeasure a) (hua : P33Effective.IsUniversal a) :
    P27.Model where
  cond _n x := normalizedSiblingProb a (toList x) true
  nonneg _n _x := normalized_nonneg a _ _
  le_one _n _x := normalized_le_one a ha hua _ _

lemma predictorModel_bitProb (a : BitString → ℝ≥0∞)
    (ha : IsLowerSemicomputableContinuousSemimeasure a) (hua : P33Effective.IsUniversal a)
    (n : ℕ) (x : P27.History n) (b : Bool) :
    P27.bitProb (predictorModel a ha hua) n x b = normalizedSiblingProb a (toList x) b := by
  cases b
  · exact normalized_false a ha hua (toList x)
  · rfl

lemma predictorModel_dominates (a : BitString → ℝ≥0∞)
    (ha : IsLowerSemicomputableContinuousSemimeasure a) (hua : P33Effective.IsUniversal a)
    (n : ℕ) (x : P27.History n) :
    (a (toList x)).toReal ≤ P27.prob (predictorModel a ha hua) n x := by
  induction n with
  | zero => simpa [toList, P27.prob] using (ENNReal.toReal_mono ENNReal.one_ne_top (ha.1.le_one []))
  | succ n ih =>
    rcases x with ⟨x,b⟩
    rw [P27.prob, predictorModel_bitProb, normalizedSiblingProb, ← mul_div_assoc,
      le_div_iff₀ (norm_den_pos a ha hua (toList x))]
    have hden : (a (toList x ++ [false])).toReal + (a (toList x ++ [true])).toReal ≤
        (a (toList x)).toReal := by
      rw [← ENNReal.toReal_add (ha.1.ne_top _) (ha.1.ne_top _)]
      exact ENNReal.toReal_mono (ha.1.ne_top _) (ha.1.2 _)
    change (a (toList x ++ [b])).toReal * _ ≤ _
    calc
      _ ≤ (a (toList x ++ [b])).toReal * P27.prob (predictorModel a ha hua) n x :=
        mul_le_mul_of_nonneg_left (hden.trans (ih x)) ENNReal.toReal_nonneg
      _ = _ := mul_comm _ _

lemma expAbsErr_eq_stepError (a : BitString → ℝ≥0∞)
    (ha : IsLowerSemicomputableContinuousSemimeasure a) (hua : P33Effective.IsUniversal a)
    (r : BitString → ℚ) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (n : ℕ) :
    expAbsErr a r (n+1) = P27.stepError (trueModel r hr01) (predictorModel a ha hua) n := by
  change (∑ v : Fin n → Bool, muProb r (List.ofFn v) *
    ∑ b : Bool, |normalizedSiblingProb a (List.ofFn v) b - muCond r (List.ofFn v) b|) = _
  rw [← (historyEquiv n).sum_comp]
  unfold P27.stepError P27.localError
  apply Finset.sum_congr rfl
  intro x _
  rw [historyEquiv_toList, trueModel_prob]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [trueModel_bitProb, predictorModel_bitProb, abs_sub_comm]

lemma muProb_total (r : BitString → ℚ) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (n : ℕ) :
    (∑ v : Fin n → Bool, muProb r (List.ofFn v)) = 1 := by
  rw [← (historyEquiv n).sum_comp]
  simp_rw [historyEquiv_toList, ← trueModel_prob r hr01]
  exact P27.prob_total _ n

lemma expAbsErr_nonneg (a : BitString → ℝ≥0∞) (r : BitString → ℚ)
    (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (t : ℕ) : 0 ≤ expAbsErr a r t := by
  exact Finset.sum_nonneg fun v _ => mul_nonneg (muProb_nonneg r hr01 _)
    (Finset.sum_nonneg fun b _ => abs_nonneg _)

lemma expAbsErr_sq_le_two_expSqErr (a : BitString → ℝ≥0∞) (r : BitString → ℚ)
    (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (t : ℕ) :
    expAbsErr a r t ^ 2 ≤ 2 * expSqErr a r t := by
  let f (v : Fin (t-1) → Bool) : ℝ :=
    ∑ b : Bool, |normalizedSiblingProb a (List.ofFn v) b - muCond r (List.ofFn v) b|
  let g (v : Fin (t-1) → Bool) : ℝ :=
    ∑ b : Bool, (normalizedSiblingProb a (List.ofFn v) b - muCond r (List.ofFn v) b)^2
  have hpoint (v : Fin (t-1) → Bool) : f v ^ 2 ≤ 2*g v := by
    change (∑ b : Bool, |normalizedSiblingProb a (List.ofFn v) b - muCond r (List.ofFn v) b|)^2 ≤
      2 * ∑ b : Bool, (normalizedSiblingProb a (List.ofFn v) b - muCond r (List.ofFn v) b)^2
    simp only [Fintype.sum_bool]
    have h := sq_nonneg (|normalizedSiblingProb a (List.ofFn v) true - muCond r (List.ofFn v) true| -
      |normalizedSiblingProb a (List.ofFn v) false - muCond r (List.ofFn v) false|)
    nlinarith [sq_abs (normalizedSiblingProb a (List.ofFn v) true - muCond r (List.ofFn v) true),
      sq_abs (normalizedSiblingProb a (List.ofFn v) false - muCond r (List.ofFn v) false)]
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ) Finset.univ
    (r := fun v : Fin (t-1) → Bool => muProb r (List.ofFn v) * f v)
    (f := fun v => muProb r (List.ofFn v))
    (g := fun v => muProb r (List.ofFn v) * (2*g v))
    (fun v _ => muProb_nonneg r hr01 _)
    (fun v _ => mul_nonneg (muProb_nonneg r hr01 _) (by dsimp [g]; positivity))
    (fun v _ => by
      have hv := mul_le_mul_of_nonneg_left (hpoint v) (sq_nonneg (muProb r (List.ofFn v)))
      nlinarith)
  rw [muProb_total r hr01, one_mul] at hh
  change expAbsErr a r t ^ 2 ≤ _ at hh
  calc
    _ ≤ _ := hh
    _ = 2 * expSqErr a r t := by
      rw [expSqErr, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      dsimp [g]
      ring

end

/-! ## Domination and block selection -/

lemma w_pos (U : Map) (n : ℕ) : 0 < w U n := by
  unfold w
  positivity

/-- Uniform index-weighted domination transfers from the standard universal law to any
universal lower semicomputable semimeasure. -/
lemma family_domination (U : Map) (hU : IsOptimalPrefixConditional U)
    (a : BitString → ℝ≥0∞) (ha : IsLowerSemicomputableContinuousSemimeasure a)
    (hua : P33Effective.IsUniversal a) (ν : ℕ → BitString → ℝ≥0∞)
    (hν : IsUniformlyLowerSemicomputableTreeFamily ν)
    (hfree : ∀ (n : ℕ) (S : Finset BitString), IsPrefixFree (S : Set BitString) →
      ∑ x ∈ S, ν n x ≤ 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ n x, d * w U n * (ν n x).toReal ≤ (a x).toReal := by
  obtain ⟨C, hC⟩ :=
    exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree U hU ν hν hfree
  have hM := universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure
  obtain ⟨c, hc, hca⟩ := hua universalContinuousSemimeasure hM
  have hc1 : 1 ≤ c := by
    simpa only [hM.1.1, ha.1.1, mul_one] using hca []
  have hcp : 0 < c.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hc1)) hc
  refine ⟨((2 : ℝ)⁻¹)^C / c.toReal, by positivity, ?_⟩
  intro n x
  have hl := ENNReal.toReal_mono (hM.1.ne_top x) (hC n x)
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hc (ha.1.ne_top x)) (hca x)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat] at hl hr
  calc
    (2 : ℝ)⁻¹ ^ C / c.toReal * w U n * (ν n x).toReal =
        ((2 : ℝ)⁻¹ ^ ((KPNat U n).toNat + C) * (ν n x).toReal) / c.toReal := by
      rw [w, pow_add]
      ring
    _ ≤ (c.toReal * (a x).toReal) / c.toReal :=
      div_le_div_of_nonneg_right (hl.trans hr) hcp.le
    _ = (a x).toReal := by field_simp

/-- A positive total discrepancy and an upper bound on total coding weight select one time. -/
lemma select_from_block (U : Map) (A : ℕ → ℝ) (n : ℕ) (d C : ℝ)
    (hd : 0 < d) (hC : 0 < C)
    (herror : d / 4 * w U n ≤ ∑ k ∈ Finset.range (2^n), A (2^n+k+1))
    (hweight : (∑ k ∈ Finset.range (2^n), w U (2^n+k+1)) ≤ C * w U n) :
    ∃ t : ℕ, 2^n < t ∧ t ≤ 2^(n+1) ∧ d / (4*C) * w U t ≤ A t := by
  classical
  by_contra h
  have hlt (k : ℕ) (hk : k ∈ Finset.range (2^n)) :
      A (2^n+k+1) < d / (4*C) * w U (2^n+k+1) := by
    have hk' : k < 2^n := Finset.mem_range.mp hk
    have hlow : 2^n < 2^n+k+1 := by omega
    have hupp : 2^n+k+1 ≤ 2^(n+1) := by rw [pow_succ]; omega
    exact lt_of_not_ge (fun hge => h ⟨2^n+k+1, hlow, hupp, hge⟩)
  have hs := Finset.sum_lt_sum_of_nonempty
    (show (Finset.range (2^n)).Nonempty from ⟨0, Finset.mem_range.mpr (by positivity)⟩) hlt
  rw [← Finset.mul_sum] at hs
  have hbound := mul_le_mul_of_nonneg_left hweight
    (show 0 ≤ d / (4*C) by positivity)
  have heq : d / (4*C) * (C * w U n) = d / 4 * w U n := by
    field_simp
  rw [heq] at hbound
  linarith

/-- The good-prefix argument packages the imported finite block theorem. -/
lemma block_lower_of_joint (μ Q : P27.Model) (r ℓ : ℕ) (α : ℝ)
    (hα : 0 < α)
    (hjoint : ∀ x : P27.History r, ∃ z : P27.History ℓ,
      α * P27.prob μ r x ≤ P27.prob Q (r + ℓ) (P27.append x ℓ z) ∧
      P27.prob μ (r + ℓ) (P27.append x ℓ z) ≤ (α / 4) * P27.prob μ r x) :
    α / 4 ≤ P27.blockError μ Q r ℓ := by
  classical
  apply P27.block_bound_of_joint μ Q r ℓ α
    (Finset.univ.filter (fun x : P27.History r =>
      0 < P27.prob μ r x ∧ P27.prob Q r x ≤ 2 * P27.prob μ r x)) hα
    (P27.good_prefix_mass μ Q r)
  · intro x hx
    exact (Finset.mem_filter.mp hx).2.1
  · intro x hx
    exact (Finset.mem_filter.mp hx).2.2
  · intro x _
    exact hjoint x

/-! ## Application to the dyadic blocks -/

/-- The joint discrepancy generated by the computable rare continuation family. -/
lemma dyadic_error_sum_lower (U : Map) (a : BitString → ℝ≥0∞)
    (ha : IsLowerSemicomputableContinuousSemimeasure a)
    (hua : P33Effective.IsUniversal a) (r : BitString → ℚ)
    (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (d : ℝ) (hd : 0 < d)
    (hdom : ∀ n x, d * w U n * (rareFamily r n x).toReal ≤ (a x).toReal)
    (n : ℕ) (htail : (1 / 2 : ℝ) ^ (2 ^ n) ≤ d * w U n / 4) :
    d / 4 * w U n ≤ ∑ k ∈ Finset.range (2 ^ n), expAbsErr a r (2 ^ n + k + 1) := by
  have hb := block_lower_of_joint (trueModel r hr01) (predictorModel a ha hua)
    (2 ^ n) (2 ^ n) (d * w U n) (mul_pos hd (w_pos U n))
  have hsep : ∀ x : P27.History (2 ^ n), ∃ y : P27.History (2 ^ n),
      d * w U n * P27.prob (trueModel r hr01) (2 ^ n) x ≤
        P27.prob (predictorModel a ha hua) (2 ^ n + 2 ^ n) (P27.append x (2 ^ n) y) ∧
      P27.prob (trueModel r hr01) (2 ^ n + 2 ^ n) (P27.append x (2 ^ n) y) ≤
        (d * w U n / 4) * P27.prob (trueModel r hr01) (2 ^ n) x := by
    intro x
    obtain ⟨z, hz, hν, hμ⟩ := rareFamily_continuation r hr01 n (2 ^ n)
      (toList x) (toList_length x)
    obtain ⟨y, hy⟩ := toList_surjective z hz
    refine ⟨y, ?_, ?_⟩
    · calc
        d * w U n * P27.prob (trueModel r hr01) (2 ^ n) x =
            d * w U n * (rareFamily r n (toList (P27.append x (2 ^ n) y))).toReal := by
          rw [trueModel_prob, toList_append, hy, hν,
            ENNReal.toReal_ofReal (muProb_nonneg r hr01 (toList x))]
        _ ≤ (a (toList (P27.append x (2 ^ n) y))).toReal := hdom _ _
        _ ≤ _ := predictorModel_dominates a ha hua _ _
    · rw [trueModel_prob, trueModel_prob, toList_append, hy]
      exact hμ.trans (mul_le_mul_of_nonneg_right htail (muProb_nonneg r hr01 _))
  have h := hb hsep
  simp only [P27.blockError, P27.A, ← expAbsErr_eq_stepError a ha hua r hr01] at h
  convert h using 1; ring

/-- Theorem 1 of 020b: for every universal lsc semimeasure M and every computable µ (rational
conditionals), the expected errors of the normalized M reach c·2^{-K(t)} (L1) and (c²/2)·2^{-2K(t)}
(squared) at some time in every late dyadic block (2^n, 2^{n+1}]. -/
theorem expected_lower_bound_io (U : Map) (hU : IsOptimalPrefixConditional U)
    (a : BitString → ℝ≥0∞) (ha : IsLowerSemicomputableContinuousSemimeasure a)
    (hua : P33Effective.IsUniversal a)
    (r : BitString → ℚ) (hr : Computable r) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ t : ℕ, 2 ^ n < t ∧ t ≤ 2 ^ (n + 1) ∧
      c * w U t ≤ expAbsErr a r t ∧ c ^ 2 / 2 * w U t ^ 2 ≤ expSqErr a r t := by
  obtain ⟨d, hd, hdom⟩ := family_domination U hU a ha hua (rareFamily r)
    (rareFamily_uniform r hr) (rareFamily_prefixFree r hr01)
  obtain ⟨C, hC, hweight⟩ := dyadic_weight_sum_le U hU
  obtain ⟨n₀, htail⟩ := eventually_half_pow_le_weight U hU d hd
  refine ⟨d / (4 * C), by positivity, n₀, ?_⟩
  intro n hn
  have hblock := dyadic_error_sum_lower U a ha hua r hr01 d hd hdom n (htail n hn)
  obtain ⟨t, htlow, htupp, ht⟩ :=
    select_from_block U (expAbsErr a r) n d C hd hC hblock (hweight n)
  refine ⟨t, htlow, htupp, ht, ?_⟩
  have hs := expAbsErr_sq_le_two_expSqErr a r hr01 t
  have ha0 := expAbsErr_nonneg a r hr01 t
  have hc0 : 0 ≤ d / (4 * C) * w U t := by unfold w; positivity
  have hsq := mul_self_le_mul_self hc0 ht
  nlinarith


end P27Stochastic

/- Fidelity note.
Source: Hutter (2005) Problem 2.7 (book text in the scratch extract, line ~4183): the bound for M,
Σ_{x_t}|M(x_t|x<t) − µ(x_t|x<t)| ≥ defect ≳ 2^{-K(t)} for all t and x<t; question: "Do similar lower
performance bounds hold for M_norm ... which has no defect?" Pro 020b Theorem 1 answers the expected,
infinitely-often form. Referee: docs/reviews/2026-11-21-referee-020b.md.
- Class: M ranges over upstream root-1 lsc continuous semimeasures that dominate every such semimeasure
  (`IsUniversal`); this includes `universalContinuousSemimeasure`. Book's ν(ε) ≤ 1 (paper argument, not
  in Lean): set ν′(ε) = 1, ν′ = ν elsewhere; ν′ is an lsc root-1 semimeasure, and normalizedSiblingProb
  never reads the root, so the root-1 class loses no M and no dominated ν.
- µ: computable rational next-bit conditionals. Narrower than "every computable measure" (real-valued
  computable conditionals); any wording must say "rational conditionals".
- Quantifiers: c and n₀ depend on U, M, µ; t depends on n. The same t satisfies both bounds.
- K(t) = KPNat U t, as in P27F. `toNat` of ⊤ is 0; KPNat is finite for optimal U.
- Weaker than the book's M bound: expected (not pointwise) and once per dyadic block (not every t).
  For every t the expected version is open (020b §4). A uniform all-history lower bound fails for one
  symmetrized M ∈ 𝒜 (desk fact: pro/020-p27-expected.q.md l.12); 020b does not prove this; open for 𝓑.
  Does not address Hutter's question about equality.
- Review: docs/reviews/2026-11-21-fidelity-27-stochastic.md (faithful with caveats).
- normalizedSiblingProb a x b = a(xb)/(a(x0)+a(x1)); positive denominators since M is universal.
-/
```

### Deviations from the suggested proof structure

- **No changes to the frozen definitions, hypotheses, conclusion, or constants in the conclusion.** The attached `P27F` and `P27BlockBound` files are imported unchanged.
- **Stronger continuation estimate.** Exact rational conditionals allow a computable choice of a least-probable bit. The proof therefore obtains
  \[
  \mu(xz)\le 2^{-|z|}\mu(x),
  \]
  replacing the report’s \((2/3)^{|z|}\) estimate.
- **Direct use of the discrete coding theorem.** The block-weight estimate uses `lowerSemicomputableSemimeasure_le_prefixComplexityWeight`. It collects the weights of times with the same computable dyadic block index into a discrete lower semicomputable semimeasure. This avoids introducing rounded logarithms to apply `KPPlain_le_of_tsum_two_pow_neg_ne_top`.
- **Elementary eventual-decay argument.** The sufficient estimate \(K(n)\le 2(n+1)+O(1)\), together with \(4n\le 2^n\) for \(n\ge4\), establishes the eventual tail inequality. The sharper logarithmic complexity estimate from the report is unnecessary here.
- **All helpers are included in one file.** The final proof combines the block discrepancy \(\sum_{t\in I_n}A_t\ge(d/4)w_n\) with \(\sum_{t\in I_n}w_t\le Cw_n\), chooses \(c=d/(4C)\), and applies \(A_t^2\le2S_t\) at the same selected time.