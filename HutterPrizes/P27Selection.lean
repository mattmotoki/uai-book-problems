/- Frozen target (desk, 2026-11-21): Theorem 1 and Corollary 2 of Pro 023 (Problem 2.7, eventual question),
   in the setting of `Targets/P27Stochastic.lean` (rational conditionals). Fidelity note at the end. -/
import HutterPrizes.P27Stochastic
import HutterPrizes.P27SelectiveForcing

open scoped BigOperators ENNReal
open Kolmogorov Kolmogorov.SelectedBits P27Stochastic

namespace P27Selection

/-- Block lengths ℓ_n = 6⌈log₂(n+2)⌉, written with `Nat.clog`. -/
def ell (n : ℕ) : ℕ := 6 * Nat.clog 2 (n + 2)

/-- B_n = Σ_{k=1}^{n} ℓ_k (so B_0 = 0). -/
def B (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, ell k


set_option maxHeartbeats 2000000

/-! ## Computability and coding weights for arbitrary selections -/

lemma coding_clog_eq_bits (n : ℕ) :
    Nat.clog 2 (n + 2) = (Nat.bits (n + 1)).length := by
  rw [Nat.size_eq_bits_len]
  apply le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr
    have h := Nat.size_le.mp (show (n + 1).size ≤ (n + 1).size from le_rfl)
    omega
  · apply Nat.size_le.mpr
    have h := Nat.le_pow_clog (by norm_num : 1 < 2) (n + 2)
    omega

lemma ell_computable : Computable ell := by
  exact (Primrec.nat_mul.comp (Primrec.const 6)
    (Primrec.list_length.comp (primrec_natBits.comp Primrec.succ))).to_comp.of_eq
      (fun n => by simp [ell, coding_clog_eq_bits])

lemma coding_B_zero : B 0 = 0 := by simp [B]

lemma coding_B_succ (n : ℕ) : B (n + 1) = B n + ell (n + 1) := by
  exact Finset.sum_Icc_succ_top (by omega) _

lemma coding_B_mono : Monotone B := by
  apply monotone_nat_of_le_succ
  intro n
  rw [coding_B_succ]
  omega

lemma B_computable : Computable B := by
  have hstep : Computable₂ fun (_ : ℕ) (p : ℕ × ℕ) => p.2 + ell (p.1 + 1) :=
    (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (ell_computable.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)))).to₂
  refine (Computable.nat_rec Computable.id (Computable.const (0 : ℕ)) hstep).of_eq fun n => ?_
  dsimp only [id]
  induction n with
  | zero => exact coding_B_zero.symm
  | succ n ih => rw [coding_B_succ, ← ih]

lemma coding_block_unique {n m j : ℕ}
    (hn : B (n - 1) < j ∧ j ≤ B n) (hm : B (m - 1) < j ∧ j ≤ B m) : n = m := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have hb := coding_B_mono (show n ≤ m - 1 by omega)
    omega
  · have hb := coding_B_mono (show m ≤ n - 1 by omega)
    omega

noncomputable def selectionCodingMass (U : Map) (d : ℕ → ℕ) (x : BitString) : ℝ≥0∞ :=
  ∑' j : ℕ, if B (bitStringToNat x - 1) < j ∧ j ≤ B (bitStringToNat x)
    then complexityWeight (KPNat U (d j)) else 0

lemma selectionCodingMass_lsc (U : Map) (hU : IsOptimalPrefixConditional U)
    (d : ℕ → ℕ) (hd : Computable d) :
    IsLSC (fun x _ => selectionCodingMass U d x) := by
  apply isLSC_tsum_of_uniform
  obtain ⟨A, hmono, hsup, hcomp⟩ := isUniformlyLSC_complexityWeight_KPNat U hU
  refine ⟨fun j s x => if B (bitStringToNat x - 1) < j ∧ j ≤ B (bitStringToNat x)
      then A (d j) s x else 0, ?_, ?_, ?_⟩
  · intro j s x
    by_cases hx : B (bitStringToNat x - 1) < j ∧ j ≤ B (bitStringToNat x)
    · simpa only [ite_eq_left hx] using hmono (d j) s x
    · simp only [ite_eq_right hx, dyadicValue_zero, le_refl]
  · intro j x
    by_cases hx : B (bitStringToNat x - 1) < j ∧ j ≤ B (bitStringToNat x)
    · simpa only [ite_eq_left hx] using hsup (d j) x
    · simp only [ite_eq_right hx, dyadicValue_zero, iSup_const]
  · have hx : Computable (fun p : ℕ × ℕ × BitString => bitStringToNat p.2.2) :=
      computable_bitStringToNat.comp (Computable.snd.comp Computable.snd)
    have hlo : Computable (fun p : ℕ × ℕ × BitString =>
        decide (B (bitStringToNat p.2.2 - 1) < p.1)) :=
      Primrec.nat_lt.decide.to_comp.comp
        (B_computable.comp (Primrec.nat_sub.to_comp.comp hx (Computable.const 1)))
        Computable.fst
    have hhi : Computable (fun p : ℕ × ℕ × BitString =>
        decide (p.1 ≤ B (bitStringToNat p.2.2))) :=
      Primrec.nat_le.decide.to_comp.comp Computable.fst (B_computable.comp hx)
    have hpred : Computable (fun p : ℕ × ℕ × BitString =>
        decide (B (bitStringToNat p.2.2 - 1) < p.1 ∧ p.1 ≤ B (bitStringToNat p.2.2))) := by
      simpa only [Bool.decide_and] using Primrec.and.to_comp.comp hlo hhi
    have hA : Computable (fun p : ℕ × ℕ × BitString => A (d p.1) p.2.1 p.2.2) :=
      hcomp.comp ((hd.comp Computable.fst).pair Computable.snd)
    exact (Computable.cond hpred hA (Computable.const 0)).of_eq (fun p => by simp)

lemma selectionCodingMass_semimeasure (U : Map) (hU : IsOptimalPrefixConditional U)
    (d : ℕ → ℕ) (hmono : StrictMono d) : IsSemimeasure (selectionCodingMass U d) := by
  classical
  change (∑' x : BitString, ∑' j : ℕ,
    if B (bitStringToNat x - 1) < j ∧ j ≤ B (bitStringToNat x)
      then complexityWeight (KPNat U (d j)) else 0) ≤ 1
  rw [ENNReal.tsum_comm]
  have hinner (j : ℕ) :
      (∑' x : BitString, if B (bitStringToNat x - 1) < j ∧ j ≤ B (bitStringToNat x)
        then complexityWeight (KPNat U (d j)) else 0) ≤ complexityWeight (KPNat U (d j)) := by
    by_cases he : ∃ n, B (n - 1) < j ∧ j ≤ B n
    · obtain ⟨n, hn⟩ := he
      calc
        _ ≤ ∑' x : BitString, if x = natToBitString n
            then complexityWeight (KPNat U (d j)) else 0 := by
          apply ENNReal.tsum_le_tsum
          intro x
          by_cases hx : B (bitStringToNat x - 1) < j ∧ j ≤ B (bitStringToNat x)
          · have heq := coding_block_unique hx hn
            have heqx : x = natToBitString n := by
              rw [← heq, natToBitString_bitStringToNat]
            rw [ite_eq_left hx, ite_eq_left heqx]
          · simp [hx]
        _ = _ := by simp
    · have hfalse (x : BitString) :
          ¬ (B (bitStringToNat x - 1) < j ∧ j ≤ B (bitStringToNat x)) :=
        fun hx => he ⟨bitStringToNat x, hx⟩
      simp only [hfalse, ↓reduceIte, tsum_zero, zero_le]
  exact (ENNReal.tsum_le_tsum hinner).trans
    ((ENNReal.tsum_comp_le_tsum_of_injective hmono.injective
      (fun t => complexityWeight (KPNat U t))).trans (tsum_complexityWeight_KPNat_le_one U hU))

lemma selection_complexity_mass_le (U : Map) (d : ℕ → ℕ) (n : ℕ) :
    (∑ j ∈ Finset.Ioc (B (n - 1)) (B n), complexityWeight (KPNat U (d j))) ≤
      selectionCodingMass U d (natToBitString n) := by
  classical
  let f : ℕ → ℝ≥0∞ := fun j =>
    if B (n - 1) < j ∧ j ≤ B n then complexityWeight (KPNat U (d j)) else 0
  calc
    _ = ∑ j ∈ Finset.Ioc (B (n - 1)) (B n), f j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [f, Finset.mem_Ioc.mp hj]
    _ ≤ ∑' j, f j := ENNReal.sum_le_tsum _
    _ = _ := by simp only [selectionCodingMass, bitStringToNat_natToBitString, f]

lemma selection_weight_sum_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (d : ℕ → ℕ) (hd : Computable d) (hmono : StrictMono d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∑ j ∈ Finset.Ioc (B (n - 1)) (B n), w U (d j)) ≤ C * w U n := by
  obtain ⟨c, hc⟩ := lowerSemicomputableSemimeasure_le_prefixComplexityWeight
    ⟨selectionCodingMass_semimeasure U hU d hmono, selectionCodingMass_lsc U hU d hd⟩ hU
  refine ⟨(2 : ℝ) ^ c, by positivity, ?_⟩
  intro n
  have h := (mul_le_mul' (le_refl ((2 : ℝ≥0∞)⁻¹ ^ c))
    (selection_complexity_mass_le U d n)).trans (hc (natToBitString n))
  have hn : prefixComplexityWeight U (natToBitString n) ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (complexityWeight_le_one _)
  have hreal := ENNReal.toReal_mono hn h
  have hw (t : ℕ) : (complexityWeight (KPNat U t)).toReal = w U t := by
    rw [← ENat.natCast_toNat (codingKPNat_ne_top hU t), complexityWeight_coe]
    simp [w]
  have hf (t : ℕ) : complexityWeight (KPNat U t) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (complexityWeight_le_one _)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, ENNReal.toReal_sum (fun j hj => hf _)] at hreal
  change (2 : ℝ)⁻¹ ^ c * (∑ j ∈ Finset.Ioc (B (n - 1)) (B n),
      (complexityWeight (KPNat U (d j))).toReal) ≤
        (complexityWeight (KPNat U n)).toReal at hreal
  simp only [hw] at hreal
  have hpos : (0 : ℝ) < 2 ^ c := by positivity
  have hmul := mul_le_mul_of_nonneg_left hreal hpos.le
  simpa [inv_pow, ← mul_assoc, ne_of_gt hpos] using hmul

/-! ## An explicit eventual estimate for the forced event -/

lemma selection_complexity_clog_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, (KPNat U n).toNat ≤ 2 * Nat.clog 2 (n + 2) + c := by
  obtain ⟨c, hc⟩ := KPPlain_le_two_mul_length U hU
  refine ⟨c, fun n => ?_⟩
  have hsize : (n + 1).size ≤ Nat.clog 2 (n + 2) := by
    apply Nat.size_le.mpr
    have hp := Nat.le_pow_clog (by norm_num : 1 < 2) (n + 2)
    omega
  have hcode : (natToBitString n).length ≤ Nat.clog 2 (n + 2) := by
    simpa only [natToBitString, List.length_dropLast, Nat.size_eq_bits_len] using
      (Nat.sub_le (n + 1).size 1).trans hsize
  have hknat : (KPNat U n).toNat ≤ 2 * (natToBitString n).length + c := by
    have hcast : ((KPNat U n).toNat : ENat) ≤
        2 * (natToBitString n).length + c :=
      (ENat.natCast_toNat (codingKPNat_ne_top hU n)).trans_le (hc _)
    exact_mod_cast hcast
  omega

lemma eventually_half_pow_ell_le_weight (U : Map) (hU : IsOptimalPrefixConditional U)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (1 / 2 : ℝ) ^ ell n ≤ δ * w U n / 2 := by
  obtain ⟨c, hc⟩ := selection_complexity_clog_bound U hU
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 2 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨2 ^ (c + m), ?_⟩
  intro n hn
  have hclog : c + m ≤ Nat.clog 2 (n + 2) := by
    have hp : 2 ^ (c + m) < n + 2 := by omega
    exact (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mpr hp |>.le
  have hindex : (KPNat U n).toNat + m ≤ ell n := by
    have := hc n
    unfold ell
    omega
  calc
    (1 / 2 : ℝ) ^ ell n ≤ (1 / 2 : ℝ) ^ ((KPNat U n).toNat + m) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hindex
    _ = w U n * (1 / 2 : ℝ) ^ m := by simp [pow_add, w]
    _ ≤ w U n * (δ / 2) := mul_le_mul_of_nonneg_left hm.le (w_pos U n).le
    _ = δ * w U n / 2 := by ring

/-! ## Selected rare-bit environments and the block discrepancy -/

def selectedTimes (d : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.Ioc (B (n - 1)) (B n)).image d

lemma env_B_succ (n : ℕ) : B (n + 1) = B n + ell (n + 1) := by
  simp [B, Finset.sum_Icc_succ_top]

lemma env_B_increment (n : ℕ) (hn : 1 ≤ n) : B n = B (n - 1) + ell n := by
  simpa only [Nat.sub_add_cancel hn] using env_B_succ (n - 1)

lemma env_selectedTimes_card (d : ℕ → ℕ) (hmono : StrictMono d)
    (n : ℕ) (hn : 1 ≤ n) : (selectedTimes d n).card = ell n := by
  rw [selectedTimes, Finset.card_image_of_injective _ hmono.injective, Nat.card_Ioc]
  rw [env_B_increment n hn]
  omega

lemma env_selectedTimes_bounds (d : ℕ → ℕ) (hmono : StrictMono d)
    (n t : ℕ) (ht : t ∈ selectedTimes d n) : 1 ≤ t ∧ t ≤ d (B n) := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hj0, hj1⟩ := Finset.mem_Ioc.mp hj
  have hjpos : 1 ≤ j := by omega
  exact ⟨hjpos.trans (hmono.id_le j), hmono.monotone hj1⟩

lemma env_computable_list_any {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Computable f) (hp : Computable₂ p) :
    Computable (fun a ↦ (f a).any (p a)) := by
  have hstep : Computable₂ (fun (a : α) (q : β × Bool) ↦ p a q.1 || q.2) :=
    (Primrec.or.to_comp.comp
      (hp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂
  refine (Computable.list_foldr hf (Computable.const false) hstep).of_eq (fun a ↦ ?_)
  induction f a with
  | nil => rfl
  | cons b t ih => simp [List.any_cons, ih]

lemma env_selectedTimes_computable (d : ℕ → ℕ) (hd : Computable d)
    (hB : Computable B) :
    Computable (fun p : ℕ × ℕ => decide (p.2 ∈ selectedTimes d p.1)) := by
  have hlo : Computable (fun p : (ℕ × ℕ) × ℕ => B (p.1.1 - 1)) :=
    hB.comp (Primrec.nat_sub.to_comp.comp
      (Computable.fst.comp Computable.fst) (Computable.const 1))
  have hlt : Computable (fun p : (ℕ × ℕ) × ℕ => decide (B (p.1.1 - 1) < p.2)) :=
    Primrec.nat_lt.decide.to_comp.comp hlo Computable.snd
  have heq : Computable (fun p : (ℕ × ℕ) × ℕ => decide (d p.2 = p.1.2)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp (hd.comp Computable.snd)
      (Computable.snd.comp Computable.fst)
  have hp : Computable₂ (fun p : ℕ × ℕ => fun j : ℕ =>
      decide (B (p.1 - 1) < j) && decide (d j = p.2)) :=
    (Primrec.and.to_comp.comp hlt heq).to₂
  have hl : Computable (fun p : ℕ × ℕ => List.range (B p.1 + 1)) :=
    Primrec.list_range.to_comp.comp
      (Primrec.succ.to_comp.comp (hB.comp Computable.fst))
  apply (env_computable_list_any hl hp).of_eq
  intro p
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.mem_range, selectedTimes, Finset.mem_image, Finset.mem_Ioc]
  constructor
  · rintro ⟨j, hj, hjlo, hjeq⟩
    exact ⟨j, ⟨hjlo, by omega⟩, hjeq⟩
  · rintro ⟨j, ⟨hjlo, hjhi⟩, hjeq⟩
    exact ⟨j, by omega, hjlo, hjeq⟩

def selectedCond (r : BitString → ℚ) (d : ℕ → ℕ) (n : ℕ) (x : BitString) : ℚ :=
  if x.length + 1 ∈ selectedTimes d n then (if rareBit r x then 1 else 0) else r x

noncomputable def selectedFamily (r : BitString → ℚ) (d : ℕ → ℕ)
    (n : ℕ) (x : BitString) : ℝ≥0∞ :=
  ENNReal.ofReal (muProb (selectedCond r d n) x)

lemma selectedCond_computable (r : BitString → ℚ) (hr : Computable r)
    (d : ℕ → ℕ) (hd : Computable d) (hB : Computable B) :
    Computable (fun p : ℕ × BitString => selectedCond r d p.1 p.2) := by
  have hpred : Computable (fun p : ℕ × BitString =>
      decide (p.2.length + 1 ∈ selectedTimes d p.1)) :=
    (env_selectedTimes_computable d hd hB).comp
      (g := fun p : ℕ × BitString => (p.1, p.2.length + 1))
      (Computable.fst.pair (Primrec.succ.to_comp.comp
        (Primrec.list_length.to_comp.comp Computable.snd)))
  have hrare : Computable (fun p : ℕ × BitString => rareBit r p.2) :=
    computable_ratLeOne.comp
      (computable₂_ratAdd.comp (hr.comp Computable.snd) (hr.comp Computable.snd))
  exact (Computable.cond hpred
    (Computable.cond hrare (Computable.const 1) (Computable.const 0))
    (hr.comp Computable.snd)).of_eq
    (fun p => by simp [selectedCond, Bool.cond_eq_ite])

lemma selectedFamily_uniform (r : BitString → ℚ) (hr : Computable r)
    (d : ℕ → ℕ) (hd : Computable d) (hB : Computable B) :
    IsUniformlyLowerSemicomputableTreeFamily (selectedFamily r d) := by
  change IsUniformlyLowerSemicomputableTreeFamily
    (fun n x => ENNReal.ofReal (muProb (selectedCond r d n) x))
  simpa only [rationalProb_cast] using
    uniform_of_computable_rat
      (f := fun n x => rationalProb (selectedCond r d n) x)
      (rationalProb_computable (f := fun n x => selectedCond r d n x)
        (selectedCond_computable r hr d hd hB))

lemma selectedCond_bounds (r : BitString → ℚ) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (d : ℕ → ℕ) (n : ℕ) (x : BitString) :
    0 ≤ selectedCond r d n x ∧ selectedCond r d n x ≤ 1 := by
  simp only [selectedCond]
  split_ifs <;> simp_all

lemma selectedFamily_continuous (r : BitString → ℚ)
    (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (d : ℕ → ℕ) (n : ℕ) :
    IsContinuousTreeSemimeasure (selectedFamily r d n) := by
  have hbound := selectedCond_bounds r hr01 d n
  constructor
  · simp [selectedFamily, muProb_nil]
  · intro x
    have hp := muProb_nonneg (selectedCond r d n) hbound x
    have h0 := muCond_nonneg (selectedCond r d n) hbound x false
    have h1 := muCond_nonneg (selectedCond r d n) hbound x true
    simp only [selectedFamily, muProb_append_singleton]
    rw [← ENNReal.ofReal_add (mul_nonneg hp h0) (mul_nonneg hp h1)]
    apply ENNReal.ofReal_le_ofReal
    simp only [muCond, Bool.false_eq_true, ↓reduceIte]
    nlinarith

lemma selectedFamily_prefixFree (r : BitString → ℚ)
    (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (d : ℕ → ℕ) (n : ℕ) (S : Finset BitString)
    (hS : IsPrefixFree (S : Set BitString)) : ∑ x ∈ S, selectedFamily r d n x ≤ 1 :=
  (selectedFamily_continuous r hr01 d n).sum_antichain_le S hS

noncomputable section

lemma selected_forcingModel (r : BitString → ℚ)
    (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (d : ℕ → ℕ) (n : ℕ) :
    P27.forcingModel (trueModel r hr01) (selectedTimes d n)
      (fun _ x => rareBit r (toList x)) =
      trueModel (selectedCond r d n) (selectedCond_bounds r hr01 d n) := by
  unfold P27.forcingModel trueModel
  congr 1
  funext k x
  simp only [selectedCond, toList_length]
  split_ifs <;> norm_num

lemma selected_forcing_prob (r : BitString → ℚ)
    (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) (d : ℕ → ℕ) (n k : ℕ) (x : P27.History k) :
    P27.prob (P27.forcingModel (trueModel r hr01) (selectedTimes d n)
      (fun _ x => rareBit r (toList x))) k x =
      (selectedFamily r d n (toList x)).toReal := by
  rw [selected_forcingModel, trueModel_prob, selectedFamily,
    ENNReal.toReal_ofReal (muProb_nonneg _ (selectedCond_bounds r hr01 d n) _)]

lemma selected_error_sum_lower (U : Map) (hU : IsOptimalPrefixConditional U)
    (a : BitString → ℝ≥0∞) (ha : IsLowerSemicomputableContinuousSemimeasure a)
    (hua : P33Effective.IsUniversal a)
    (r : BitString → ℚ) (hr : Computable r) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (d : ℕ → ℕ) (hd : Computable d) (hmono : StrictMono d) (hB : Computable B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, 1 ≤ n →
      (1 / 2 : ℝ) ^ ell n ≤ δ * w U n / 2 →
      δ * w U n ≤ ∑ j ∈ Finset.Ioc (B (n - 1)) (B n), expAbsErr a r (d j) := by
  obtain ⟨δ, hδ, hdom⟩ := family_domination U hU a ha hua (selectedFamily r d)
    (selectedFamily_uniform r hr d hd hB) (selectedFamily_prefixFree r hr01 d)
  refine ⟨δ, hδ, ?_⟩
  intro n hn htail
  have hforced := P27.selective_forcing_bound (trueModel r hr01) (predictorModel a ha hua)
    (d (B n)) (ell n) (selectedTimes d n) (fun _ x => rareBit r (toList x))
    (1 / 2) (δ * w U n) (env_selectedTimes_bounds d hmono n)
    (env_selectedTimes_card d hmono n hn) (mul_pos hδ (w_pos U n)).le
    (fun k _ x => by simpa only [trueModel_bitProb] using rareBit_small r (toList x))
    (fun x => by
      rw [selected_forcing_prob]
      exact (hdom n (toList x)).trans (predictorModel_dominates a ha hua _ _))
  have hsum : (∑ t ∈ selectedTimes d n,
      P27.A (trueModel r hr01) (predictorModel a ha hua) t) =
      ∑ j ∈ Finset.Ioc (B (n - 1)) (B n), expAbsErr a r (d j) := by
    rw [selectedTimes, Finset.sum_image (fun i hi j hj hij => hmono.injective hij)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjpos : 1 ≤ d j := (env_selectedTimes_bounds d hmono n (d j)
      (Finset.mem_image.mpr ⟨j, hj, rfl⟩)).1
    have he := expAbsErr_eq_stepError a ha hua r hr01 (d j - 1)
    rw [Nat.sub_add_cancel hjpos] at he
    rw [he]
    cases ht : d j with
    | zero => omega
    | succ k => simp [P27.A]
  rw [hsum] at hforced
  linarith

end

/-! ## Extracting a coordinate from the two block estimates -/

lemma selection_extract (U : Map) (A : ℕ → ℝ) (d : ℕ → ℕ) (n : ℕ)
    (s : Finset ℕ) (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (herror : δ * w U n ≤ ∑ j ∈ s, A (d j))
    (hweight : (∑ j ∈ s, w U (d j)) ≤ C * w U n) :
    ∃ j ∈ s, δ / C * w U (d j) ≤ A (d j) := by
  classical
  have hs : s.Nonempty := by
    by_contra he
    have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [hempty, Finset.sum_empty] at herror
    exact (not_le_of_gt (mul_pos hδ (w_pos U n))) herror
  by_contra h
  have hlt (j : ℕ) (hj : j ∈ s) : A (d j) < δ / C * w U (d j) :=
    lt_of_not_ge (fun hge => h ⟨j, hj, hge⟩)
  have hsum := Finset.sum_lt_sum_of_nonempty hs hlt
  rw [← Finset.mul_sum] at hsum
  have hbound := mul_le_mul_of_nonneg_left hweight (show 0 ≤ δ / C by positivity)
  have heq : δ / C * (C * w U n) = δ * w U n := by field_simp
  rw [heq] at hbound
  linarith

/-! ## From selected blocks to logarithmic windows -/

lemma window_ell_pos (n : ℕ) : 0 < ell n := by
  have h := Nat.clog_pos (by omega : 1 < 2) (by omega : 1 < n + 2)
  unfold ell
  omega

lemma window_B_zero : B 0 = 0 := by simp [B]

lemma window_B_succ (n : ℕ) : B (n + 1) = B n + ell (n + 1) := by
  unfold B
  exact Finset.sum_Icc_succ_top (by omega) ell

lemma window_B_mono : Monotone B := by
  apply monotone_nat_of_le_succ
  intro n
  rw [window_B_succ]
  omega

lemma window_index_le_B (n : ℕ) : n ≤ B n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [window_B_succ]
    have h := window_ell_pos (n+1)
    omega

lemma window_ell_bound (u k : ℕ) (hk : k ≤ u + 1) :
    ell k ≤ 12 * (Nat.log 2 (u + 2) + 1) := by
  have hpow : u + 2 < 2 ^ (Nat.log 2 (u + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by omega) _
  have hkpow : k + 2 ≤ 2 ^ (Nat.log 2 (u + 2) + 2) := by
    rw [show Nat.log 2 (u+2)+2 = (Nat.log 2 (u+2)+1)+1 by omega, pow_succ]
    omega
  have hclog : Nat.clog 2 (k + 2) ≤ Nat.log 2 (u + 2) + 2 :=
    Nat.clog_le_of_le_pow hkpow
  unfold ell
  omega

/-- A block witness for every sufficiently large block gives a logarithmic window witness. -/
lemma window_of_blocks (P : ℕ → Prop) (n₀ : ℕ)
    (hP : ∀ n, n₀ ≤ n → ∃ j : ℕ, B (n - 1) < j ∧ j ≤ B n ∧ P j) :
    ∃ C T : ℕ, ∀ u, T ≤ u → ∃ t : ℕ,
      u ≤ t ∧ t ≤ u + C * (Nat.log 2 (u + 2) + 1) ∧ P t := by
  refine ⟨24, B n₀ + 1, ?_⟩
  intro u hu
  have hu0 : 0 < u := by omega
  have hex : ∃ n, u ≤ B n := ⟨u, window_index_le_B u⟩
  let k := Nat.find hex
  have hku : k ≤ u := Nat.find_min' hex (window_index_le_B u)
  have hub : u ≤ B k := Nat.find_spec hex
  have hk0 : 0 < k := by
    by_contra h
    have hk : k = 0 := by omega
    rw [hk, window_B_zero] at hub
    omega
  have hprev : B (k - 1) < u := by
    have h := Nat.find_min hex (show k - 1 < k by omega)
    omega
  have hlate : n₀ ≤ k + 1 := by
    by_contra h
    have hkn : k ≤ n₀ := by omega
    have hb := window_B_mono hkn
    omega
  obtain ⟨t, htlo, hthi, htP⟩ := hP (k+1) hlate
  have htlow : u ≤ t := by
    simp only [Nat.add_sub_cancel] at htlo
    omega
  have hstep : B k = B (k-1) + ell k := by
    simpa only [Nat.sub_add_cancel hk0] using window_B_succ (k-1)
  have hbound0 := window_ell_bound u k (by omega)
  have hbound1 := window_ell_bound u (k+1) (by omega)
  refine ⟨t, htlow, ?_, htP⟩
  rw [window_B_succ, hstep] at hthi
  omega

/-- 023 Theorem 1: along every computable strictly increasing selection of times d_1 < d_2 < ⋯ (d 0 is not
used), every
late selection block F_n = {d_j : B_{n-1} < j ≤ B_n} contains a time t with A_t ≥ c·2^{-K(t)} and
S_t ≥ (c²/2)·2^{-2K(t)}. -/
theorem selection_lower_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (a : BitString → ℝ≥0∞) (ha : IsLowerSemicomputableContinuousSemimeasure a)
    (hua : P33Effective.IsUniversal a)
    (r : BitString → ℚ) (hr : Computable r) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1)
    (d : ℕ → ℕ) (hd : Computable d) (hmono : StrictMono d) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ j : ℕ, B (n - 1) < j ∧ j ≤ B n ∧
      c * w U (d j) ≤ expAbsErr a r (d j) ∧ c ^ 2 / 2 * w U (d j) ^ 2 ≤ expSqErr a r (d j) := by
  obtain ⟨δ, hδ, herror⟩ := selected_error_sum_lower U hU a ha hua r hr hr01
    d hd hmono B_computable
  obtain ⟨C, hC, hweight⟩ := selection_weight_sum_le U hU d hd hmono
  obtain ⟨n₀, htail⟩ := eventually_half_pow_ell_le_weight U hU δ hδ
  refine ⟨δ / C, div_pos hδ hC, max 1 n₀, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : n₀ ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨j, hj, hAj⟩ := selection_extract U (expAbsErr a r) d n
    (Finset.Ioc (B (n - 1)) (B n)) δ C hδ hC
    (herror n hn1 (htail n hn0)) (hweight n)
  obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ioc.mp hj
  refine ⟨j, hjlo, hjhi, hAj, ?_⟩
  have hs := expAbsErr_sq_le_two_expSqErr a r hr01 (d j)
  have hc0 : 0 ≤ δ / C * w U (d j) :=
    (mul_pos (div_pos hδ hC) (w_pos U (d j))).le
  have hsq := mul_self_le_mul_self hc0 hAj
  nlinarith

/-- 023 Corollary 2: a witness in every late window of length O(log u). -/
theorem log_window_lower_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (a : BitString → ℝ≥0∞) (ha : IsLowerSemicomputableContinuousSemimeasure a)
    (hua : P33Effective.IsUniversal a)
    (r : BitString → ℚ) (hr : Computable r) (hr01 : ∀ x, 0 ≤ r x ∧ r x ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ C T : ℕ, ∀ u, T ≤ u → ∃ t : ℕ, u ≤ t ∧ t ≤ u + C * (Nat.log 2 (u + 2) + 1) ∧
      c * w U t ≤ expAbsErr a r t ∧ c ^ 2 / 2 * w U t ^ 2 ≤ expSqErr a r t := by
  obtain ⟨c, hc, n₀, hblock⟩ := selection_lower_bound U hU a ha hua r hr hr01
    id Computable.id strictMono_id
  refine ⟨c, hc, ?_⟩
  exact window_of_blocks
    (fun t => c * w U t ≤ expAbsErr a r t ∧
      c ^ 2 / 2 * w U t ^ 2 ≤ expSqErr a r t) n₀ hblock

end P27Selection

/- Fidelity note.
Source: `pro/023-p27-eventual.a.md` §3 (Theorem 1, eq. (17)-(18); Corollary 2, eq. (26)); referee
`docs/reviews/2026-11-21-referee-023.md` (correct). Definitions `expAbsErr`, `expSqErr`, `w`, the classes of M
and µ, and the K on naturals are those of `Targets/P27Stochastic.lean` (reviewed: faithful with caveats).
- Selection: d computable, strictly increasing. The report indexes d_1 < d_2 < ⋯; here j ranges over
  B_{n-1} < j ≤ B_n, so d 0 is never used in a block, and StrictMono gives d j ≥ j ≥ 1.
- ⌈log₂(n+2)⌉ = `Nat.clog 2 (n + 2)`. In Corollary 2 the window ⌈C log₂(u+2)⌉ is written C·(⌊log₂(u+2)⌋+1)
  with C : ℕ; the two forms agree up to the constant.
- Quantifiers: c, n₀ depend on U, M, µ and d (no uniform c over selections; referee). In Corollary 2,
  c, C, T depend on U, M, µ.
- µ has rational conditionals (as in P27Stochastic); the report covers every computable µ (smoothing (19)).
  Corollary 1 (every infinite c.e. set) is a computability step from Theorem 1, not stated here.
- Not stated: eq. (27) (Ω(N/log N) witnesses up to N), Corollary 1, Theorem 2, every computable µ.
- Partial answer only: (E) "for every large t" stays open.
- Review: docs/reviews/2026-11-21-fidelity-27-selection.md (faithful with caveats; hd1 removed).
-/
