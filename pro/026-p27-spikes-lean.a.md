Both frozen theorems are proved. The complete file **compiles without warnings** with Lean **4.35.0**, Mathlib **v4.35.0**, and the requested upstream commit `17c50e560c337a8a702f8850a711f80a56b3cf91`.

The `fairCoin` definition and both theorem statements are preserved character for character. For each theorem, `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`. The file imports `HutterPrizes.P27Stochastic` and includes all new helpers; no additional helper files are required.

Download: P27Spikes.lean[P27Spikes.lean](sandbox:/workspace/scratch/4257d0f6b6dd/HutterPrizes/P27Spikes.lean)

```lean
/- Frozen target (desk, 2026-11-21): Theorem 6 of Pro 020b (Problem 2.7, upper-bound side), over the root-1
   universal class of `Targets/P27Stochastic.lean`. Fidelity note at the end. -/
import HutterPrizes.P27Stochastic

open scoped BigOperators ENNReal
open Kolmogorov Kolmogorov.SelectedBits P27Stochastic

namespace P27Spikes

/-- The fair coin: every next-bit conditional is 1/2. -/
def fairCoin : BitString → ℚ := fun _ => 1 / 2

open scoped Topology
open Filter

set_option maxHeartbeats 2000000

/-! ## Finite complexity sublevels and computable stopping lengths -/

lemma stopping_sublevel_finite (U : Map) (n : ℕ) :
    {j : ℕ | KPNat U j ≤ (n : ENat)}.Finite := by
  classical
  have hex : ∀ j ∈ {j : ℕ | KPNat U j ≤ (n : ENat)},
      ∃ p : BitString, programLength p ≤ n ∧ produces U p [] (natToBitString j) := by
    intro j hj
    exact (condK_le_iff U (natToBitString j) [] n).1 hj
  choose! p hplen hprod using hex
  refine Set.Finite.of_finite_image (f := p) ?_ ?_
  · refine Set.Finite.subset (Finset.finite_toSet (boundedPrograms n).toFinset) ?_
    rintro _ ⟨j, hj, rfl⟩
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact (mem_boundedPrograms_iff (p j) n).2 (hplen j hj)
  · intro j hj k hk heq
    have h1 : natToBitString j ∈ U (p j, ([] : BitString)) := hprod j hj
    have h2 : natToBitString k ∈ U (p k, ([] : BitString)) := hprod k hk
    rw [heq] at h1
    exact natToBitString_injective (Part.mem_unique h1 h2)

/-- The largest natural of prefix complexity at most the budget, or zero if none exists. -/
noncomputable def stoppingLength (U : Map) (n : ℕ) : ℕ :=
  sSup {j : ℕ | KPNat U j ≤ (n : ENat)}

lemma le_stoppingLength {U : Map} {n j : ℕ} (h : KPNat U j ≤ (n : ENat)) :
    j ≤ stoppingLength U n :=
  le_csSup (stopping_sublevel_finite U n).bddAbove h

lemma stoppingLength_le {U : Map} {n b : ℕ}
    (h : ∀ j, KPNat U j ≤ (n : ENat) → j ≤ b) : stoppingLength U n ≤ b := by
  rcases Set.eq_empty_or_nonempty {j : ℕ | KPNat U j ≤ (n : ENat)} with he | hn
  · simp [stoppingLength, he]
  · exact csSup_le hn h

lemma stoppingLength_mono (U : Map) : Monotone (stoppingLength U) := by
  intro m n hmn
  apply stoppingLength_le
  intro j hj
  apply le_stoppingLength
  exact hj.trans (by exact_mod_cast hmn)

lemma stoppingLength_complex (U : Map) (hU : IsOptimalPrefixConditional U) (n : ℕ) :
    n < (KPNat U (stoppingLength U n + 1)).toNat := by
  by_contra hn
  have h : KPNat U (stoppingLength U n + 1) ≤ (n : ENat) := by
    rw [← ENat.natCast_toNat (codingKPNat_ne_top hU _)]
    exact_mod_cast (not_lt.mp hn)
  have := le_stoppingLength h
  omega

lemma stoppingLength_eventually_ge (U : Map) (hU : IsOptimalPrefixConditional U) (T : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → T ≤ stoppingLength U n := by
  refine ⟨(KPNat U T).toNat, fun n hn => le_stoppingLength ?_⟩
  rw [← ENat.natCast_toNat (codingKPNat_ne_top hU _)]
  exact_mod_cast hn

private lemma fold_max_le (l : List ℕ) (z b : ℕ) :
    l.foldl max z ≤ b ↔ z ≤ b ∧ ∀ j ∈ l, j ≤ b := by
  induction l generalizing z with
  | nil => simp
  | cons j l ih => simp [List.foldl_cons, ih, and_assoc]

private lemma le_fold_max_of_mem {l : List ℕ} {j : ℕ} (hj : j ∈ l) (z : ℕ) :
    j ≤ l.foldl max z := by
  exact ((fold_max_le l z (l.foldl max z)).mp le_rfl).2 j hj

private def stoppingApprox (g : ℕ → ℕ → ℕ) (n s : ℕ) : ℕ :=
  ((List.range (s + 1)).map (fun j => if g s j ≤ n then j else 0)).foldl max 0

private lemma stoppingApprox_computable (g : ℕ → ℕ → ℕ) (hg : Computable₂ g) :
    Computable₂ (stoppingApprox g) := by
  have hval : Computable (fun p : (ℕ × ℕ) × ℕ => g p.1.2 p.2) :=
    hg.comp (Computable.snd.comp Computable.fst) Computable.snd
  have htest : Computable (fun p : (ℕ × ℕ) × ℕ => decide (g p.1.2 p.2 ≤ p.1.1)) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp hval (Computable.fst.comp Computable.fst)
  have hterm : Computable₂ (fun p : ℕ × ℕ => fun j : ℕ => if g p.2 j ≤ p.1 then j else 0) :=
    by
      change Computable (fun p : (ℕ × ℕ) × ℕ => if g p.1.2 p.2 ≤ p.1.1 then p.2 else 0)
      exact (Computable.cond htest Computable.snd (Computable.const 0)).of_eq
        (fun p => by simp)
  have hm : Computable (fun p : ℕ × ℕ =>
      (List.range (p.2 + 1)).map (fun j => if g p.2 j ≤ p.1 then j else 0)) :=
    Computable.list_map (Primrec.list_range.to_comp.comp (Computable.succ.comp Computable.snd)) hterm
  exact (Computable.list_foldl hm (Computable.const 0)
    ((Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to_comp.to₂)).to₂

/-- A computable increasing stage approximation, uniformly in the complexity budget. -/
theorem exists_stopping_approx (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ B : ℕ → ℕ → ℕ, Computable₂ B ∧
      (∀ n, Monotone (B n)) ∧
      (∀ n s, B n s ≤ stoppingLength U n) ∧
      (∀ n, ∃ s, B n s = stoppingLength U n) := by
  obtain ⟨g, hgcomp, hgstep, hgevent⟩ := isUpperSemicomputableNat_KPNat_toNat U hU
  dsimp only at hgevent
  have hganti : ∀ j, Antitone (fun s => g s j) := fun j =>
    antitone_nat_of_succ_le (fun s => hgstep s j)
  have hglower : ∀ s j, (KPNat U j).toNat ≤ g s j := by
    intro s j
    obtain ⟨q, hq⟩ := hgevent j
    rw [← hq (max s q) (le_max_right _ _)]
    exact hganti j (le_max_left _ _)
  have hbound : ∀ n s, stoppingApprox g n s ≤ stoppingLength U n := by
    intro n s
    apply (fold_max_le _ _ _).mpr
    refine ⟨Nat.zero_le _, ?_⟩
    intro j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
    split_ifs with h
    · apply le_stoppingLength
      rw [← ENat.natCast_toNat (codingKPNat_ne_top hU _)]
      exact_mod_cast ((hglower s k).trans h)
    · exact Nat.zero_le _
  refine ⟨stoppingApprox g, stoppingApprox_computable g hgcomp, ?_, hbound, ?_⟩
  · intro n s q hsq
    apply (fold_max_le _ _ _).mpr
    refine ⟨Nat.zero_le _, ?_⟩
    intro j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
    split_ifs with h
    · apply le_fold_max_of_mem (l := (List.range (q + 1)).map
        (fun k => if g q k ≤ n then k else 0)) (z := 0)
      apply List.mem_map.mpr
      refine ⟨k, List.mem_range.mpr (by have := List.mem_range.mp hk; omega), ?_⟩
      simp [(hganti k hsq).trans h]
    · exact Nat.zero_le _
  · intro n
    rcases Set.eq_empty_or_nonempty {j : ℕ | KPNat U j ≤ (n : ENat)} with he | hn
    · refine ⟨0, le_antisymm (hbound n 0) ?_⟩
      simp [stoppingLength, he]
    · have hbK : KPNat U (stoppingLength U n) ≤ (n : ENat) :=
        Nat.sSup_mem hn (stopping_sublevel_finite U n).bddAbove
      have hbKn : (KPNat U (stoppingLength U n)).toNat ≤ n := by
        rw [← ENat.natCast_toNat (codingKPNat_ne_top hU _)] at hbK
        exact_mod_cast hbK
      obtain ⟨q, hq⟩ := hgevent (stoppingLength U n)
      refine ⟨max q (stoppingLength U n), le_antisymm (hbound _ _) ?_⟩
      apply le_fold_max_of_mem (l := (List.range (max q (stoppingLength U n) + 1)).map
        (fun k => if g (max q (stoppingLength U n)) k ≤ n then k else 0)) (z := 0)
      apply List.mem_map.mpr
      refine ⟨stoppingLength U n, List.mem_range.mpr (Nat.lt_succ_of_le (le_max_right _ _)), ?_⟩
      rw [hq _ (le_max_left _ _)]
      simp [hbKn]

/-! ## Asymmetric stopping semimeasures -/

/-- The asymmetric stopping law, represented by rational cylinder masses. -/
def stopQ (L : ℕ) (i : Bool) (x : BitString) : ℚ :=
  if x.length ≤ L ∨ (x.length = L + 1 ∧ x.getD L false = i)
  then (1 / 2) ^ x.length else 0

noncomputable def stopMass (L : ℕ) (i : Bool) (x : BitString) : ℝ≥0∞ :=
  ENNReal.ofReal (stopQ L i x : ℝ)

lemma stopQ_nonneg (L : ℕ) (i : Bool) (x : BitString) : 0 ≤ stopQ L i x := by
  unfold stopQ
  split <;> positivity

lemma stopQ_le (L : ℕ) (i : Bool) (x : BitString) :
    stopQ L i x ≤ (1 / 2 : ℚ) ^ x.length := by
  unfold stopQ
  split
  · exact le_rfl
  · positivity

lemma stopQ_mono (i : Bool) (x : BitString) : Monotone (fun L => stopQ L i x) := by
  intro L K hLK
  by_cases h : L = K
  · subst K; rfl
  have hLK' : L < K := lt_of_le_of_ne hLK h
  dsimp only [stopQ]
  split_ifs with hL hK
  · rfl
  · exfalso
    apply hK
    left
    rcases hL with hL | ⟨hL, _⟩ <;> omega
  · positivity
  · rfl

lemma stopQ_child (L : ℕ) (i : Bool) (x : BitString) (b : Bool) :
    stopQ L i (x ++ [b]) =
      if x.length < L ∨ (x.length = L ∧ b = i)
      then (1 / 2 : ℚ) ^ (x.length + 1) else 0 := by
  unfold stopQ
  simp only [List.length_append, List.length_singleton]
  congr 1
  apply propext
  constructor
  · rintro (h | ⟨h, hb⟩)
    · left; omega
    · right
      have hx : x.length = L := by omega
      subst L
      simpa using hb
  · rintro (h | ⟨h, hb⟩)
    · left; omega
    · right
      subst L
      simp [hb]

lemma stopQ_children_le (L : ℕ) (i : Bool) (x : BitString) :
    stopQ L i (x ++ [false]) + stopQ L i (x ++ [true]) ≤ stopQ L i x := by
  rw [stopQ_child, stopQ_child]
  have hp : 0 ≤ (1 / 2 : ℚ) ^ x.length := by positivity
  by_cases hlt : x.length < L
  · have hle : x.length ≤ L := hlt.le
    simp only [hlt, true_or, ↓reduceIte, stopQ, hle, pow_succ]
    linarith
  · by_cases heq : x.length = L
    · have hval : stopQ L i x = (1 / 2 : ℚ) ^ x.length :=
        ite_eq_left (Or.inl heq.le)
      rw [hval]
      simp only [heq, one_div, inv_pow] at hp
      cases i <;> simp [heq, pow_succ] <;> nlinarith
    · simp only [hlt, heq, false_and, or_self, ↓reduceIte, add_zero]
      exact stopQ_nonneg L i x

lemma stopMass_semimeasure (L : ℕ) (i : Bool) :
    IsContinuousTreeSemimeasure (stopMass L i) := by
  constructor
  · simp [stopMass, stopQ]
  · intro x
    unfold stopMass
    rw [← ENNReal.ofReal_add (by exact_mod_cast stopQ_nonneg L i (x ++ [false]))
      (by exact_mod_cast stopQ_nonneg L i (x ++ [true]))]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast stopQ_children_le L i x

/-- Geometric weights, with the stopping complexity parameter later taken quadratic. -/
noncomputable def spikeNu (B : ℕ → ℕ) (i : Bool) : BitString → ℝ≥0∞ :=
  continuousTreeMixture (fun n => stopMass (B ((n + 1) ^ 2)) i)

lemma spikeNu_semimeasure (B : ℕ → ℕ) (i : Bool) :
    IsContinuousTreeSemimeasure (spikeNu B i) :=
  continuousTreeMixture_isContinuousTreeSemimeasure _ (fun _ => stopMass_semimeasure _ _)

/-! ## Uniform lower semicomputability -/

lemma stopQ_computable (i : Bool) :
    Computable (fun p : ℕ × BitString => stopQ p.1 i p.2) := by
  have hlen : Computable (fun p : ℕ × BitString => p.2.length) :=
    Primrec.list_length.to_comp.comp Computable.snd
  have hle : Computable (fun p : ℕ × BitString => decide (p.2.length ≤ p.1)) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp.comp hlen Computable.fst
  have heq : Computable (fun p : ℕ × BitString => decide (p.2.length = p.1 + 1)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp hlen
      (Computable.succ.comp Computable.fst)
  have hbit : Computable (fun p : ℕ × BitString => p.2.getD p.1 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd Computable.fst
  have hbi : Computable (fun p : ℕ × BitString => decide (p.2.getD p.1 false = i)) :=
    (PrimrecRel.decide Primrec.eq).to_comp.comp hbit (Computable.const i)
  have hpred : Computable (fun p : ℕ × BitString =>
      decide (p.2.length ≤ p.1 ∨ (p.2.length = p.1 + 1 ∧ p.2.getD p.1 false = i))) := by
    simpa only [Bool.decide_or, Bool.decide_and] using
      (Primrec.dom_bool₂ (fun a b : Bool => a || b)).to_comp.comp hle
        ((Primrec.dom_bool₂ (fun a b : Bool => a && b)).to_comp.comp heq hbi)
  have hpow : Computable (fun p : ℕ × BitString => (1 / 2 : ℚ) ^ p.2.length) := by
    apply computable_of_num_den (N := fun _ => (1 : ℤ))
      (D := fun p : ℕ × BitString => 2 ^ p.2.length)
      (Computable.const 1) (comp_pow.comp hlen)
    · intro p; positivity
    · intro p; simp
  exact (Computable.cond hpred hpow (Computable.const 0)).of_eq fun p => by
    simp [stopQ]

lemma stopMass_uniform (B : ℕ → ℕ) (Ba : ℕ → ℕ → ℕ)
    (hcomp : Computable₂ Ba) (hmono : ∀ n, Monotone (Ba n))
    (hbound : ∀ n s, Ba n s ≤ B n) (hreach : ∀ n, ∃ s, Ba n s = B n)
    (i : Bool) :
    IsUniformlyLowerSemicomputableTreeFamily
      (fun n => stopMass (B ((n + 1) ^ 2)) i) := by
  refine ⟨fun n s x => ratDyadicFloor (stopQ (Ba ((n + 1) ^ 2) s) i x) s, ?_, ?_, ?_⟩
  · intro n s x
    exact dyadicValue_ratDyadicFloor_mono_of_le
      (stopQ_mono i x (hmono _ (Nat.le_succ s))) s
  · intro n x
    rw [iSup_dyadicValue_ratDyadicFloor
      (show Monotone (fun s => stopQ (Ba ((n + 1) ^ 2) s) i x) from
        (stopQ_mono i x).comp (hmono _))]
    apply le_antisymm
    · apply iSup_le
      intro s
      exact ENNReal.ofReal_le_ofReal (by exact_mod_cast stopQ_mono i x (hbound _ s))
    · obtain ⟨s, hs⟩ := hreach ((n + 1) ^ 2)
      change ENNReal.ofReal (stopQ (B ((n + 1) ^ 2)) i x : ℝ) ≤ _
      rw [← hs]
      exact le_iSup (fun s => ENNReal.ofReal (stopQ (Ba ((n + 1) ^ 2) s) i x : ℝ)) s
  · have hn : Computable (fun p : ℕ × ℕ × BitString => (p.1 + 1) ^ 2) :=
      nat_pow_primrec₂.to_comp.comp (Computable.succ.comp Computable.fst) (Computable.const 2)
    have hs : Computable (fun p : ℕ × ℕ × BitString => p.2.1) :=
      Computable.fst.comp Computable.snd
    have hx : Computable (fun p : ℕ × ℕ × BitString => p.2.2) :=
      Computable.snd.comp Computable.snd
    have hb : Computable (fun p : ℕ × ℕ × BitString => Ba ((p.1 + 1) ^ 2) p.2.1) :=
      hcomp.comp hn hs
    have hq : Computable (fun p : ℕ × ℕ × BitString =>
        stopQ (Ba ((p.1 + 1) ^ 2) p.2.1) i p.2.2) :=
      (stopQ_computable i).comp
        (g := fun p : ℕ × ℕ × BitString => (Ba ((p.1 + 1) ^ 2) p.2.1, p.2.2))
        (hb.pair hx)
    exact computable_ratDyadicFloor.comp hq hs

lemma spikeNu_effective (B : ℕ → ℕ) (Ba : ℕ → ℕ → ℕ)
    (hcomp : Computable₂ Ba) (hmono : ∀ n, Monotone (Ba n))
    (hbound : ∀ n s, Ba n s ≤ B n) (hreach : ∀ n, ∃ s, Ba n s = B n)
    (i : Bool) : IsLowerSemicomputableContinuousSemimeasure (spikeNu B i) := by
  obtain ⟨A, hAmono, hAsup, hAcomp⟩ :=
    stopMass_uniform B Ba hcomp hmono hbound hreach i
  apply continuousTreeMixture_dyadicWeight_isLowerSemicomputableContinuousSemimeasure
    (a := fun n s x _ => A n s x)
  · intro n s x _; exact hAmono n s x
  · intro n x _; exact hAsup n x
  · intro n; exact stopMass_semimeasure _ _
  · have hp : Computable (fun p : ℕ × ℕ × BitString × BitString =>
        (p.1, p.2.1, p.2.2.1)) :=
      Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    exact hAcomp.comp
      (g := fun p : ℕ × ℕ × BitString × BitString => (p.1, p.2.1, p.2.2.1)) hp

/-! ## The fair-coin comparison inequality -/

lemma fairCoin_bounds (x : BitString) : 0 ≤ fairCoin x ∧ fairCoin x ≤ 1 := by
  norm_num [fairCoin]

lemma fairCoin_cond (x : BitString) (b : Bool) : muCond fairCoin x b = (1 / 2 : ℝ) := by
  cases b <;> norm_num [muCond, fairCoin]

lemma fairCoin_muProb (x : BitString) : muProb fairCoin x = (1 / 2 : ℝ) ^ x.length := by
  induction x using List.reverseRecOn with
  | nil => simp [muProb]
  | append_singleton x b ih =>
    rw [muProb_append_singleton, ih, fairCoin_cond]
    simp [pow_succ]

lemma fairCoin_muProb_pos (x : BitString) : 0 < muProb fairCoin x := by
  rw [fairCoin_muProb]
  positivity

noncomputable def childDen (a : BitString → ℝ≥0∞) (x : BitString) : ℝ :=
  (a (x ++ [false])).toReal + (a (x ++ [true])).toReal

lemma semimeasure_level_sum_le (a : BitString → ℝ≥0∞)
    (ha : IsContinuousTreeSemimeasure a) (L : ℕ) :
    (∑ v : Fin L → Bool, (a (List.ofFn v)).toReal) ≤ 1 := by
  classical
  let S : Finset BitString := Finset.univ.image (List.ofFn : (Fin L → Bool) → BitString)
  have hanti : ∀ y ∈ S, ∀ z ∈ S, y <+: z → y = z := by
    intro y hy z hz hp
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
    exact hp.eq_of_length (by simp)
  have h := ha.sum_antichain_le S hanti
  have hs : (∑ v : Fin L → Bool, a (List.ofFn v)) ≤ 1 := by
    simpa only [S, Finset.sum_image (fun _ _ _ _ he => List.ofFn_injective he)] using h
  have ht := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hs
  rw [ENNReal.toReal_sum (fun _ _ => ha.ne_top _), ENNReal.toReal_one] at ht
  exact ht

lemma childDen_sum_le (a : BitString → ℝ≥0∞)
    (ha : IsContinuousTreeSemimeasure a) (L : ℕ) :
    (∑ v : Fin L → Bool, childDen a (List.ofFn v)) ≤ 1 := by
  refine le_trans (Finset.sum_le_sum fun v _ => ?_) (semimeasure_level_sum_le a ha L)
  unfold childDen
  rw [← ENNReal.toReal_add (ha.ne_top _) (ha.ne_top _)]
  exact ENNReal.toReal_mono (ha.ne_top _) (ha.2 _)

/-- The tangent-line inequality for the reciprocal square, in weighted form. -/
lemma reciprocal_square_tangent (m D : ℝ) (hm : 0 ≤ m) (hD : 0 < D) :
    3 * m - 2 * D ≤ m * (m / D) ^ 2 := by
  have hp : 0 ≤ (D - m) ^ 2 * (2 * D + m) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hD)).mp
  field_simp
  nlinarith [hp]

lemma normalized_binary_sq (a : BitString → ℝ≥0∞)
    (ha : IsLowerSemicomputableContinuousSemimeasure a) (hua : P33Effective.IsUniversal a)
    (x : BitString) :
    (∑ b : Bool, (normalizedSiblingProb a x b - muCond fairCoin x b) ^ 2) =
      2 * (normalizedSiblingProb a x false - 1 / 2) ^ 2 := by
  simp only [Fintype.sum_bool, fairCoin_cond]
  have h := normalized_false a ha hua x
  have ht : normalizedSiblingProb a x true = 1 - normalizedSiblingProb a x false := by linarith
  rw [ht]
  ring

lemma fairCoin_sq_le_abs (a : BitString → ℝ≥0∞)
    (ha : IsLowerSemicomputableContinuousSemimeasure a) (hua : P33Effective.IsUniversal a)
    (t : ℕ) : expSqErr a fairCoin t ≤ expAbsErr a fairCoin t := by
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_left _ (fairCoin_muProb_pos _).le
  apply Finset.sum_le_sum
  intro b _
  rw [fairCoin_cond]
  have h0 := normalized_nonneg a (List.ofFn v) b
  have h1 := normalized_le_one a ha hua (List.ofFn v) b
  have habs : |normalizedSiblingProb a (List.ofFn v) b - 1 / 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hsq := mul_le_mul_of_nonneg_left habs (abs_nonneg
    (normalizedSiblingProb a (List.ofFn v) b - 1 / 2))
  nlinarith [sq_abs (normalizedSiblingProb a (List.ofFn v) b - 1 / 2)]

/-- A uniform gap in child masses forces expected squared error for one of two predictors. -/
lemma comparison_of_child_gap
    (a₀ a₁ : BitString → ℝ≥0∞)
    (ha₀ : IsLowerSemicomputableContinuousSemimeasure a₀) (hua₀ : P33Effective.IsUniversal a₀)
    (ha₁ : IsLowerSemicomputableContinuousSemimeasure a₁) (hua₁ : P33Effective.IsUniversal a₁)
    (L : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hden : ∀ x : BitString, x.length = L → childDen a₀ x = childDen a₁ x)
    (hgap : ∀ x : BitString, x.length = L →
      δ * muProb fairCoin x ≤ (a₀ (x ++ [false])).toReal - (a₁ (x ++ [false])).toReal) :
    δ ^ 2 ≤ expSqErr a₀ fairCoin (L + 1) + expSqErr a₁ fairCoin (L + 1) := by
  change δ ^ 2 ≤
    (∑ v : Fin L → Bool, muProb fairCoin (List.ofFn v) *
      ∑ b : Bool, (normalizedSiblingProb a₀ (List.ofFn v) b - muCond fairCoin (List.ofFn v) b)^2) +
    ∑ v : Fin L → Bool, muProb fairCoin (List.ofFn v) *
      ∑ b : Bool, (normalizedSiblingProb a₁ (List.ofFn v) b - muCond fairCoin (List.ofFn v) b)^2
  have hpoint (x : BitString) (hx : x.length = L) :
      δ ^ 2 * (3 * muProb fairCoin x - 2 * childDen a₀ x) ≤
        muProb fairCoin x *
          ((∑ b : Bool, (normalizedSiblingProb a₀ x b - muCond fairCoin x b)^2) +
            ∑ b : Bool, (normalizedSiblingProb a₁ x b - muCond fairCoin x b)^2) := by
    have hm := (fairCoin_muProb_pos x).le
    have hD : 0 < childDen a₀ x := norm_den_pos a₀ ha₀ hua₀ x
    have hqr : δ * (muProb fairCoin x / childDen a₀ x) ≤
        normalizedSiblingProb a₀ x false - normalizedSiblingProb a₁ x false := by
      change δ * (muProb fairCoin x / childDen a₀ x) ≤
        (a₀ (x ++ [false])).toReal / childDen a₀ x -
          (a₁ (x ++ [false])).toReal / childDen a₁ x
      rw [← hden x hx, ← sub_div, ← mul_div_assoc]
      exact (div_le_div_iff_of_pos_right hD).mpr (hgap x hx)
    have hqr0 : 0 ≤ δ * (muProb fairCoin x / childDen a₀ x) :=
      mul_nonneg hδ (div_nonneg hm hD.le)
    have hsq : (δ * (muProb fairCoin x / childDen a₀ x)) ^ 2 ≤
        (normalizedSiblingProb a₀ x false - normalizedSiblingProb a₁ x false) ^ 2 := by
      nlinarith
    have htriangle :
        (normalizedSiblingProb a₀ x false - normalizedSiblingProb a₁ x false) ^ 2 ≤
          (∑ b : Bool, (normalizedSiblingProb a₀ x b - muCond fairCoin x b)^2) +
            ∑ b : Bool, (normalizedSiblingProb a₁ x b - muCond fairCoin x b)^2 := by
      rw [normalized_binary_sq a₀ ha₀ hua₀, normalized_binary_sq a₁ ha₁ hua₁]
      nlinarith [sq_nonneg (normalizedSiblingProb a₀ x false +
        normalizedSiblingProb a₁ x false - 1)]
    have hj := mul_le_mul_of_nonneg_left
      (reciprocal_square_tangent (muProb fairCoin x) (childDen a₀ x) hm hD) (sq_nonneg δ)
    have he := mul_le_mul_of_nonneg_left (le_trans hsq htriangle) hm
    nlinarith
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin L → Bool)))
    (fun v _ => hpoint (List.ofFn v) (by simp))
  have hm := muProb_total fairCoin fairCoin_bounds L
  have hD := childDen_sum_le a₀ ha₀.1 L
  have hδD := mul_le_mul_of_nonneg_left hD (sq_nonneg δ)
  have hl : δ ^ 2 ≤ ∑ v : Fin L → Bool,
      δ ^ 2 * (3 * muProb fairCoin (List.ofFn v) - 2 * childDen a₀ (List.ofFn v)) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hm]
    nlinarith
  apply le_trans hl
  simpa only [mul_add, Finset.sum_add_distrib] using hsum

/-! ## Half mixtures and universality -/

noncomputable def halfMix (V ν : BitString → ℝ≥0∞) : BitString → ℝ≥0∞ :=
  fun x => V x / 2 + ν x / 2

lemma halfMix_eq_mixE (V ν : BitString → ℝ≥0∞) :
    halfMix V ν = P33Effective.mixE (1 / 2) V ν := by
  have hcoef : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  funext x
  unfold halfMix P33Effective.mixE
  norm_num only [show (1 - (1 / 2 : ℚ)) = (1 / 2 : ℚ) by norm_num,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rw [hcoef]
  simp only [div_eq_mul_inv, mul_comm]

lemma halfMix_semimeasure (V ν : BitString → ℝ≥0∞)
    (hV : IsContinuousTreeSemimeasure V) (hν : IsContinuousTreeSemimeasure ν) :
    IsContinuousTreeSemimeasure (halfMix V ν) := by
  constructor
  · simp only [halfMix, hV.1, hν.1]
    rw [← ENNReal.add_div]
    norm_num [ENNReal.div_self]
  · intro x
    calc
      halfMix V ν (x ++ [false]) + halfMix V ν (x ++ [true]) =
          (V (x ++ [false]) + V (x ++ [true])) / 2 +
          (ν (x ++ [false]) + ν (x ++ [true])) / 2 := by
            simp only [halfMix, ENNReal.add_div]
            ac_rfl
      _ ≤ V x / 2 + ν x / 2 :=
        add_le_add (ENNReal.div_le_div_right (hV.2 x) 2)
          (ENNReal.div_le_div_right (hν.2 x) 2)
      _ = halfMix V ν x := rfl

lemma halfMix_effective (V ν : BitString → ℝ≥0∞)
    (hV : IsLowerSemicomputableContinuousSemimeasure V)
    (hν : IsLowerSemicomputableContinuousSemimeasure ν) :
    IsLowerSemicomputableContinuousSemimeasure (halfMix V ν) := by
  refine ⟨halfMix_semimeasure V ν hV.1 hν.1, ?_⟩
  rw [halfMix_eq_mixE]
  exact P33Effective.lsc_mixE (1 / 2) hV.2 hν.2

lemma halfMix_universal (V ν : BitString → ℝ≥0∞)
    (hV : P33Effective.IsUniversal V) : P33Effective.IsUniversal (halfMix V ν) := by
  intro a ha
  obtain ⟨c, hctop, hc⟩ := hV a ha
  refine ⟨c * 2, ENNReal.mul_ne_top hctop (by norm_num), ?_⟩
  intro x
  calc
    a x ≤ c * V x := hc x
    _ = (c * 2) * (V x / 2) := by
      rw [mul_assoc, mul_comm (2 : ℝ≥0∞) (V x / 2), ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    _ ≤ (c * 2) * halfMix V ν x :=
      mul_le_mul' le_rfl (le_self_add (a := V x / 2) (b := ν x / 2))

lemma halfMix_toReal (V ν : BitString → ℝ≥0∞) (x : BitString)
    (hV : V x ≠ ⊤) (hν : ν x ≠ ⊤) :
    (halfMix V ν x).toReal = (V x).toReal / 2 + (ν x).toReal / 2 := by
  rw [halfMix, ENNReal.toReal_add
    (ENNReal.div_ne_top hV (by norm_num)) (ENNReal.div_ne_top hν (by norm_num))]
  simp

lemma halfMix_childDen_eq (V ν₀ ν₁ : BitString → ℝ≥0∞)
    (hV : IsContinuousTreeSemimeasure V)
    (hν₀ : IsContinuousTreeSemimeasure ν₀) (hν₁ : IsContinuousTreeSemimeasure ν₁)
    (x : BitString)
    (hchild : (ν₀ (x ++ [false])).toReal + (ν₀ (x ++ [true])).toReal =
      (ν₁ (x ++ [false])).toReal + (ν₁ (x ++ [true])).toReal) :
    (halfMix V ν₀ (x ++ [false])).toReal + (halfMix V ν₀ (x ++ [true])).toReal =
      (halfMix V ν₁ (x ++ [false])).toReal + (halfMix V ν₁ (x ++ [true])).toReal := by
  rw [halfMix_toReal V ν₀ _ (hV.ne_top _) (hν₀.ne_top _),
    halfMix_toReal V ν₀ _ (hV.ne_top _) (hν₀.ne_top _),
    halfMix_toReal V ν₁ _ (hV.ne_top _) (hν₁.ne_top _),
    halfMix_toReal V ν₁ _ (hV.ne_top _) (hν₁.ne_top _)]
  linarith

lemma universalContinuousSemimeasure_universal :
    P33Effective.IsUniversal universalContinuousSemimeasure :=
  universalContinuousSemimeasure_isMaximal

/-! ## The child-mass gap -/

lemma stopMass_child (L : ℕ) (i : Bool) (x : BitString) (b : Bool) :
    stopMass L i (x ++ [b]) =
      if x.length < L ∨ (x.length = L ∧ b = i)
      then ENNReal.ofReal ((1 / 2 : ℝ) ^ (x.length + 1)) else 0 := by
  rw [stopMass, stopQ_child]
  split <;> simp

lemma stopMass_false_le (L : ℕ) (x : BitString) :
    stopMass L true (x ++ [false]) ≤ stopMass L false (x ++ [false]) := by
  simp only [stopMass_child]
  by_cases hlt : x.length < L
  · simp [hlt]
  · by_cases heq : x.length = L <;> simp [hlt, heq]

lemma stopMass_childsum_eq (L : ℕ) (x : BitString) :
    stopMass L false (x ++ [false]) + stopMass L false (x ++ [true]) =
      stopMass L true (x ++ [false]) + stopMass L true (x ++ [true]) := by
  simp only [stopMass_child]
  by_cases hlt : x.length < L
  · simp [hlt]
  · by_cases heq : x.length = L <;> simp [hlt, heq]

lemma spikeNu_childsum_eq (B : ℕ → ℕ) (x : BitString) :
    spikeNu B false (x ++ [false]) + spikeNu B false (x ++ [true]) =
      spikeNu B true (x ++ [false]) + spikeNu B true (x ++ [true]) := by
  unfold spikeNu continuousTreeMixture
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  apply tsum_congr
  intro n
  rw [← mul_add, ← mul_add, stopMass_childsum_eq]

lemma spikeNu_childDen_eq (B : ℕ → ℕ) (x : BitString) :
    childDen (spikeNu B false) x = childDen (spikeNu B true) x := by
  unfold childDen
  rw [← ENNReal.toReal_add ((spikeNu_semimeasure B false).ne_top _)
      ((spikeNu_semimeasure B false).ne_top _),
    ← ENNReal.toReal_add ((spikeNu_semimeasure B true).ne_top _)
      ((spikeNu_semimeasure B true).ne_top _), spikeNu_childsum_eq]

lemma spikeNu_false_gap (B : ℕ → ℕ) (n : ℕ) (x : BitString)
    (hx : x.length = B ((n + 1) ^ 2)) :
    spikeNu B true (x ++ [false]) +
      dyadicWeight n * ENNReal.ofReal ((1 / 2 : ℝ) ^ (x.length + 1)) ≤
        spikeNu B false (x ++ [false]) := by
  have hpoint (m : ℕ) :
      dyadicWeight m * stopMass (B ((m + 1) ^ 2)) true (x ++ [false]) +
        (if m = n then dyadicWeight n * ENNReal.ofReal ((1 / 2 : ℝ) ^ (x.length + 1)) else 0) ≤
      dyadicWeight m * stopMass (B ((m + 1) ^ 2)) false (x ++ [false]) := by
    by_cases h : m = n
    · subst m
      simp [stopMass_child, hx]
    · simp only [h, ↓reduceIte, add_zero]
      exact mul_le_mul' le_rfl (stopMass_false_le _ x)
  have hh := ENNReal.tsum_le_tsum hpoint
  simpa only [ENNReal.tsum_add, tsum_ite_eq, spikeNu, continuousTreeMixture] using hh

lemma dyadicWeight_toReal (n : ℕ) :
    (dyadicWeight n).toReal = (1 / 2 : ℝ) ^ (n + 1) := by
  simp [dyadicWeight]

lemma spikeNu_false_real_gap (B : ℕ → ℕ) (n : ℕ) (x : BitString)
    (hx : x.length = B ((n + 1) ^ 2)) :
    (1 / 2 : ℝ) ^ (n + 1) * muProb fairCoin x / 2 ≤
      (spikeNu B false (x ++ [false])).toReal -
        (spikeNu B true (x ++ [false])).toReal := by
  have hh := ENNReal.toReal_mono ((spikeNu_semimeasure B false).ne_top _)
    (spikeNu_false_gap B n x hx)
  rw [ENNReal.toReal_add ((spikeNu_semimeasure B true).ne_top _)
      (ENNReal.mul_ne_top (by simp [dyadicWeight]) ENNReal.ofReal_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), dyadicWeight_toReal] at hh
  rw [fairCoin_muProb]
  rw [pow_succ (1 / 2 : ℝ) x.length] at hh
  linarith

/-! ## A fixed predictor defeats every positive exponent -/

/-- Quadratic complexity at the selected times defeats geometric spike amplitudes. -/
lemma eventually_weight_below_geometric
    (U : Map) (t : ℕ → ℕ)
    (hK : ∀ n, (n + 1) ^ 2 ≤ (KPNat U (t n)).toNat)
    (α : ℝ) (hα : 0 < α) (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ n in atTop,
      C * w U (t n) ^ α < ((1 / 2 : ℝ) ^ (2 * (n + 1))) / c := by
  by_cases hC : 0 < C
  · have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
      simpa only [pow_succ, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2 : ℝ)
    have he : ∀ᶠ n in atTop, C * (1 / 2 : ℝ) ^ (n + 1) < 1 / c := by
      have hh : Tendsto (fun n : ℕ => C * (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
        simpa only [mul_zero] using hp.const_mul C
      exact hh.eventually (gt_mem_nhds (one_div_pos.mpr hc))
    obtain ⟨N, hN⟩ := exists_nat_gt (3 / α)
    filter_upwards [he, eventually_ge_atTop N] with n hn hnN
    have hnreal : (3 : ℝ) / α < (n + 1 : ℕ) :=
      hN.trans_le (by exact_mod_cast (show N ≤ n + 1 by omega))
    have hna : (3 : ℝ) < (n + 1 : ℕ) * α := (div_lt_iff₀ hα).mp hnreal
    have hks : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (KPNat U (t n)).toNat := by
      exact_mod_cast hK n
    have hksα := mul_le_mul_of_nonneg_right hks hα.le
    have hnnonneg : (0 : ℝ) ≤ (n + 1 : ℕ) := Nat.cast_nonneg _
    have hq := mul_le_mul_of_nonneg_right hna.le hnnonneg
    have hexp : ((3 * (n + 1) : ℕ) : ℝ) ≤ (KPNat U (t n)).toNat * α := by
      push_cast
      push_cast at hksα hq
      nlinarith
    have hw : w U (t n) ^ α ≤ (1 / 2 : ℝ) ^ (3 * (n + 1)) := by
      unfold w
      norm_num only [one_div]
      rw [← Real.rpow_natCast_mul (by positivity)]
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hexp
    calc
      C * w U (t n) ^ α ≤ C * (1 / 2 : ℝ) ^ (3 * (n + 1)) :=
        mul_le_mul_of_nonneg_left hw hC.le
      _ = (C * (1 / 2 : ℝ) ^ (n + 1)) * (1 / 2 : ℝ) ^ (2 * (n + 1)) := by
        rw [show 3 * (n + 1) = (n + 1) + 2 * (n + 1) by omega, pow_add]
        ring
      _ < (1 / c) * (1 / 2 : ℝ) ^ (2 * (n + 1)) :=
        mul_lt_mul_of_pos_right hn (by positivity)
      _ = (1 / 2 : ℝ) ^ (2 * (n + 1)) / c := by ring
  · have hC' : C ≤ 0 := le_of_not_gt hC
    filter_upwards [] with n
    exact lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg hC' (Real.rpow_nonneg (w_pos U _).le _))
      (by positivity)

/-- One of two predictors has cofinally many spikes.  The selected predictor is independent of
both the exponent and the proposed upper-bound constant. -/
lemma extract_one_spiking_predictor
    (U : Map) (t : ℕ → ℕ) (ht : Tendsto t atTop atTop)
    (hK : ∀ n, (n + 1) ^ 2 ≤ (KPNat U (t n)).toNat)
    (f : Bool → ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hspike : ∀ n, ((1 / 2 : ℝ) ^ (2 * (n + 1))) / c ≤
      f false (t n) + f true (t n)) :
    ∃ i : Bool, ∀ α : ℝ, 0 < α → ∀ C : ℝ, ∀ T : ℕ,
      ∃ s : ℕ, T ≤ s ∧ C * w U s ^ α < f i s := by
  let g : ℕ → ℝ := fun n => ((1 / 2 : ℝ) ^ (2 * (n + 1))) / (2 * c)
  have hsum (n : ℕ) : 2 * g n ≤ f false (t n) + f true (t n) := by
    have hh := hspike n
    dsimp [g]
    convert hh using 1
    field_simp
  have hi : ∃ i : Bool, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ g n ≤ f i (t n) := by
    by_cases hh : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ g n ≤ f false (t n)
    · exact ⟨false, hh⟩
    · push Not at hh
      obtain ⟨N, hN⟩ := hh
      refine ⟨true, ?_⟩
      intro M
      refine ⟨max N M, le_max_right _ _, ?_⟩
      have hbad := hN (max N M) (le_max_left _ _)
      have hh := hsum (max N M)
      linarith
  obtain ⟨i, hi⟩ := hi
  refine ⟨i, ?_⟩
  intro α hα C T
  have hw := eventually_weight_below_geometric U t hK α hα C (2 * c) (by positivity)
  have htime : ∀ᶠ n in atTop, T ≤ t n := ht.eventually (eventually_ge_atTop T)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hw.and htime)
  obtain ⟨n, hn, hni⟩ := hi N
  refine ⟨t n, (hN n hn).2, ?_⟩
  exact lt_of_lt_of_le (hN n hn).1 hni

/-! ## Assembling the witness -/

lemma spike_mixture_witness (U : Map) (hU : IsOptimalPrefixConditional U)
    (V : BitString → ℝ≥0∞) (hV : IsLowerSemicomputableContinuousSemimeasure V)
    (huV : P33Effective.IsUniversal V) :
    ∃ ν : BitString → ℝ≥0∞, IsLowerSemicomputableContinuousSemimeasure ν ∧
      IsLowerSemicomputableContinuousSemimeasure (halfMix V ν) ∧
      P33Effective.IsUniversal (halfMix V ν) ∧
      ∀ α : ℝ, 0 < α → ∀ C : ℝ, ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧
        C * w U t ^ α < expSqErr (halfMix V ν) fairCoin t ∧
        C * w U t ^ α < expAbsErr (halfMix V ν) fairCoin t := by
  obtain ⟨Ba, hBa, hmono, hbound, hreach⟩ := exists_stopping_approx U hU
  let B := stoppingLength U
  let a : Bool → BitString → ℝ≥0∞ := fun i => halfMix V (spikeNu B i)
  have hν (i : Bool) : IsLowerSemicomputableContinuousSemimeasure (spikeNu B i) :=
    spikeNu_effective B Ba hBa hmono hbound hreach i
  have ha (i : Bool) : IsLowerSemicomputableContinuousSemimeasure (a i) :=
    halfMix_effective V (spikeNu B i) hV (hν i)
  have hua (i : Bool) : P33Effective.IsUniversal (a i) :=
    halfMix_universal V (spikeNu B i) huV
  let t : ℕ → ℕ := fun n => B ((n + 1) ^ 2) + 1
  have ht : Tendsto t atTop atTop := by
    apply tendsto_atTop.mpr
    intro T
    obtain ⟨N, hN⟩ := stoppingLength_eventually_ge U hU T
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : N ≤ (n + 1) ^ 2 := by nlinarith
    exact (hN _ hn').trans (Nat.le_succ _)
  have hK (n : ℕ) : (n + 1) ^ 2 ≤ (KPNat U (t n)).toNat :=
    (stoppingLength_complex U hU ((n + 1) ^ 2)).le
  have hspike (n : ℕ) : (1 / 2 : ℝ) ^ (2 * (n + 1)) / 16 ≤
      expSqErr (a false) fairCoin (t n) + expSqErr (a true) fairCoin (t n) := by
    have hden (x : BitString) (_hx : x.length = B ((n + 1) ^ 2)) :
        childDen (a false) x = childDen (a true) x :=
      halfMix_childDen_eq V (spikeNu B false) (spikeNu B true) hV.1
        (hν false).1 (hν true).1 x (spikeNu_childDen_eq B x)
    have hgap (x : BitString) (hx : x.length = B ((n + 1) ^ 2)) :
        ((1 / 2 : ℝ) ^ (n + 1) / 4) * muProb fairCoin x ≤
          (a false (x ++ [false])).toReal - (a true (x ++ [false])).toReal := by
      have hh := spikeNu_false_real_gap B n x hx
      dsimp only [a]
      rw [halfMix_toReal V (spikeNu B false) _ (hV.1.ne_top _) ((hν false).1.ne_top _),
        halfMix_toReal V (spikeNu B true) _ (hV.1.ne_top _) ((hν true).1.ne_top _)]
      linarith
    have hh := comparison_of_child_gap (a false) (a true) (ha false) (hua false)
      (ha true) (hua true) (B ((n + 1) ^ 2)) ((1 / 2 : ℝ) ^ (n + 1) / 4)
      (by positivity) hden hgap
    have heq : ((1 / 2 : ℝ) ^ (n + 1) / 4) ^ 2 =
        (1 / 2 : ℝ) ^ (2 * (n + 1)) / 16 := by
      rw [div_pow, ← pow_mul]
      norm_num [Nat.mul_comm]
    rw [heq] at hh
    exact hh
  obtain ⟨i, hi⟩ := extract_one_spiking_predictor U t ht hK
    (fun i s => expSqErr (a i) fairCoin s) 16 (by norm_num) hspike
  refine ⟨spikeNu B i, hν i, ha i, hua i, ?_⟩
  intro α hα C T
  obtain ⟨s, hsT, hs⟩ := hi α hα C T
  exact ⟨s, hsT, hs, hs.trans_le (fairCoin_sq_le_abs (a i) (ha i) (hua i) s)⟩


/-- 020b Theorem 6: there is a universal lower semicomputable semimeasure M such that, for the fair coin, the
expected L1 and squared errors of the normalized M are not O(2^{-αK(t)}) for any α > 0. -/
theorem no_power_upper_bound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ a : BitString → ℝ≥0∞, IsLowerSemicomputableContinuousSemimeasure a ∧ P33Effective.IsUniversal a ∧
      ∀ α : ℝ, 0 < α → ∀ C : ℝ, ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧
        C * w U t ^ α < expSqErr a fairCoin t ∧ C * w U t ^ α < expAbsErr a fairCoin t := by
  obtain ⟨ν, _hν, ha, hua, hsp⟩ := spike_mixture_witness U hU
    universalContinuousSemimeasure
    universalContinuousSemimeasure_isLowerSemicomputableContinuousSemimeasure
    universalContinuousSemimeasure_universal
  exact ⟨halfMix universalContinuousSemimeasure ν, ha, hua, hsp⟩

/-- Stronger form (review suggestion): for every universal V there is an lsc semimeasure ν such that the
half-half mixture ½V + ½ν is universal and has the spikes. With V a Solomonoff prior, the mixture is again one
(paper step: 𝓑 is closed under ½V + ½ν, Wood-Sunehag-Hutter). -/
theorem no_power_upper_bound_mix (U : Map) (hU : IsOptimalPrefixConditional U)
    (V : BitString → ℝ≥0∞) (hV : IsLowerSemicomputableContinuousSemimeasure V)
    (huV : P33Effective.IsUniversal V) :
    ∃ ν : BitString → ℝ≥0∞, IsLowerSemicomputableContinuousSemimeasure ν ∧
      let a : BitString → ℝ≥0∞ := fun x => V x / 2 + ν x / 2
      IsLowerSemicomputableContinuousSemimeasure a ∧ P33Effective.IsUniversal a ∧
      ∀ α : ℝ, 0 < α → ∀ C : ℝ, ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧
        C * w U t ^ α < expSqErr a fairCoin t ∧ C * w U t ^ α < expAbsErr a fairCoin t := by
  exact spike_mixture_witness U hU V hV huV

end P27Spikes

/- Fidelity note.
Source: `pro/020-p27-expected.a.md` §6, Theorem 6, eq. (37): ∃ M ∈ 𝓑 ∀α > 0: limsup_t S_t(M, λ)/w_t^α = ∞, and
the same for A_t. Referee `docs/reviews/2026-11-21-referee-020b.md` (correct with minor gaps; the proof gives
"one of two priors", so the statement must be existential). Book question (2.7): "an upper bound better than
O(2^{-K(t)})" and "for which sequences does equality ≍ 2^{-K(t)} hold?".
- Class: the Lean statement asks for M in the root-1 universal class (`IsUniversal`, as in P27Stochastic), not
  for M ∈ 𝓑 (a Solomonoff prior of a universal monotone machine); upstream has no monotone-machine prior class.
  The 𝓑 membership is a paper fact (Wood-Sunehag-Hutter Def. 2; novelty check confirmed it).
- `w U t ^ α` is `Real.rpow` (α : ℝ). "limsup = ∞" is written as: for every C and T some t ≥ T has
  S_t > C·w_t^α. One t serves both errors: for the fair coin s_t(x) = 2d² ≤ 2|d| = a_t(x), so S_t ≤ A_t at
  every t. This is no strengthening.
- B(n) is defined from the same `U` as `w`, so (39) holds exactly.
- `no_power_upper_bound_mix` (∀ universal V ∃ ν: ½V + ½ν has the spikes) is the stronger form; Lean then
  certifies the 𝓑 claim up to the paper step "𝓑 is closed under ½V + ½ν for lsc ν".
- Review: docs/reviews/2026-11-21-fidelity-27-spikes.md (faithful with caveats).
- µ = fair coin (`fairCoin`, conditionals 1/2). Not stated: the pathwise claim (realized errors on a set of
  λ-probability ≥ 1/2).
- Scope: shows that an upper bound O(2^{-αK(t)}) fails for some universal M; it does not say every M fails.
-/
```

### Deviations

1. **No changes to the frozen statement layer.** The definition of `fairCoin`, both theorem statements, their declaration order, and the original fidelity note are preserved. There are no `sorry`, `admit`, new axioms, or uses of `native_decide`.

2. **Geometric weights at quadratic complexity budgets replace Elias-gamma weights.** The construction uses
   \[
   \gamma_n=2^{-(n+1)},\qquad
   \nu_i=\sum_{n\ge0}\gamma_n\,\nu_{B_U((n+1)^2),i},
   \qquad
   t_n=B_U((n+1)^2)+1.
   \]
   These weights sum to one. The same comparison argument gives
   \[
   S_{t_n}(M^{(0)})+S_{t_n}(M^{(1)})
   \ge \frac{2^{-2(n+1)}}{16},
   \qquad
   K_U(t_n)>(n+1)^2.
   \]
   One fixed predictor therefore has spikes of at least \(2^{-2(n+1)}/32\) along cofinally many indices. For every fixed \(\alpha>0\), the quadratic exponent in \(w_U(t_n)^\alpha\) defeats this geometric spike scale. This changes the witness construction while proving exactly the requested conclusions.

3. **The approximation to \(B_U\) uses upper approximations to \(K_U\).** The proof invokes the existing theorem `isUpperSemicomputableNat_KPNat_toNat`. At stage \(s\), it scans \(j\le s\) and takes the maximum of those whose current integer complexity approximation is at most the budget. The resulting approximation is computable, increasing in \(s\), bounded by the exact stopping length, and eventually attains it. Thus the suggested strict test on approximations to \(2^{-K_U}\) is unnecessary.

4. **An elementary tangent inequality replaces Jensen’s inequality.** The formal proof uses
   \[
   3m-2D\le m\left(\frac mD\right)^2,
   \qquad m\ge0,\ D>0,
   \]
   obtained from \((D-m)^2(2D+m)\ge0\). Summing and using \(\sum m=1\) and \(\sum D\le1\) gives the same comparison constant as the report.

5. **A shared mixture-witness lemma preserves the frozen declaration order.** Both public theorems use `spike_mixture_witness`; the plain theorem specializes it to `universalContinuousSemimeasure`. The selected Boolean index is chosen before \(\alpha,C,T\), so a single semimeasure works for every positive exponent. The formal scope remains the root-one universal lower semicomputable class specified by the target.