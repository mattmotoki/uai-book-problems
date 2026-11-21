Completed [P33Exact.lean](https://chatgpt.com/library?file_id=libfile_fde3_f-763540aff6b48191aedc149ed46a5758_55156f90431c8191a9d99c52c310f59a&account_id=personal). It **compiles successfully** with Lean 4.35.0, Mathlib v4.35.0, and the specified upstream commit. The frozen prefix is preserved byte-for-byte; all helpers are local to the theorem’s proof.

```lean
/- Frozen target (desk, 2026-11-21): Problem 3.3 with exact complexity weights 2^{-K(i)} (Pro 008 Theorem 6;
   027 Theorem 5). Matt chose this after paper draft 3. Fidelity note at the end. -/
import HutterPrizes.P33Complexity

open scoped BigOperators ENNReal
open Kolmogorov RobustExperiment RobustExperiment.Theorem4 P33Effective

namespace P33Exact

/-- The mixture with exact weights 2^{-K_C(i)}, K_C(i) = KPNat C i the prefix complexity of the index i relative to
the machine C, over an enumeration τ of semimeasures. -/
noncomputable def exactMixture (C : Map) (τ : ℕ → BitString → ℝ≥0∞) (x : BitString) : ℝ≥0∞ :=
  ∑' i, complexityWeight (KPNat C i) * τ i x

/-- 3.3 with exact 2^{-K} weights: there are an effective enumeration τ of all lower semicomputable semimeasures
(root 1, with repetitions; a computable renumbering of upstream `treeLSCEnum` in both directions) and two optimal
prefix machines C⁻, C⁺ such that the mixtures ξ± = Σ_i 2^{-K_{C±}(i)} τ_i are universal lower semicomputable
semimeasures, their weights differ by at most a factor 4 at every index, the source µ
is some τ_j, and the µ-expected 0-1 losses (ties toward 1) differ by ≥ n^{1/4}/512 for n ≥ 3, tending to +∞. -/
theorem exact_counterexample :
    ∃ (τ : ℕ → BitString → ℝ≥0∞) (CMinus CPlus : Map),
      IsUniformlyLowerSemicomputableTreeFamily τ ∧
      (∀ i, IsLowerSemicomputableContinuousSemimeasure (τ i)) ∧
      (∀ a : BitString → ℝ≥0∞, IsLowerSemicomputableContinuousSemimeasure a → ∃ i, τ i = a) ∧
      IsOptimalPrefixConditional CMinus ∧ IsOptimalPrefixConditional CPlus ∧
      (∃ f g : ℕ → ℕ, Computable f ∧ Computable g ∧
        (∀ i, τ (f i) = treeLSCEnum i) ∧ (∀ i, treeLSCEnum (g i) = τ i)) ∧
      (∀ i,
        complexityWeight (KPNat CMinus i) ≤ 4 * complexityWeight (KPNat CPlus i) ∧
        complexityWeight (KPNat CPlus i) ≤ 4 * complexityWeight (KPNat CMinus i)) ∧
      IsUniversal (exactMixture CMinus τ) ∧ IsUniversal (exactMixture CPlus τ) ∧
      (∀ x, exactMixture CMinus τ (x ++ [false]) + exactMixture CMinus τ (x ++ [true]) ≤
        exactMixture CMinus τ x) ∧
      (∀ x, exactMixture CPlus τ (x ++ [false]) + exactMixture CPlus τ (x ++ [true]) ≤
        exactMixture CPlus τ x) ∧
      exactMixture CMinus τ [] ≤ 1 ∧ exactMixture CPlus τ [] ≤ 1 ∧
      IsLSC (fun x _ => exactMixture CMinus τ x) ∧ IsLSC (fun x _ => exactMixture CPlus τ x) ∧
      (∃ j, ∀ n (h : History n), τ j (toBitString h) = ENNReal.ofReal (prob source n h)) ∧
      (∀ n : ℕ, 3 ≤ n →
        (n : ℝ)^(1/4 : ℝ)/512 ≤
          loss source (transport (exactMixture CMinus τ)) n -
            loss source (transport (exactMixture CPlus τ)) n) ∧
      Filter.Tendsto
        (fun n : ℕ =>
          loss source (transport (exactMixture CMinus τ)) n -
            loss source (transport (exactMixture CPlus τ)) n)
        Filter.atTop Filter.atTop := by
  classical
  open P33Complexity in
    set_option maxHeartbeats 0 in
      all_goals
        let shortCode (b : Bool) (i : Fin 4) : BitString :=
          if b then
            if i = 0 then [false, true] else
            if i = 1 then [false, false, true] else
            if i = 2 then [false, false, false, false] else
            [false, false, false, true]
          else
            if i = 0 then [false, false, false, false] else
            if i = 1 then [false, false, false, true] else
            if i = 2 then [false, true] else
            [false, false, true]

        let simulationTag : BitString := List.replicate 30 true

        have shortCode_prefix_eq (b : Bool) (i j : Fin 4)
            (h : shortCode b i <+: shortCode b j) : i = j := by
          have h' : ∀ b : Bool, ∀ i j : Fin 4,
              shortCode b i <+: shortCode b j → i = j := by decide
          exact h' b i j h

        have shortCode_tag_incomparable (b : Bool) (i : Fin 4) :
            ¬ shortCode b i <+: simulationTag ∧ ¬ simulationTag <+: shortCode b i := by
          have h : ∀ b : Bool, ∀ i : Fin 4,
              ¬ shortCode b i <+: simulationTag ∧ ¬ simulationTag <+: shortCode b i := by decide
          exact h b i

        have shortCode_length_le (b : Bool) (i : Fin 4) : (shortCode b i).length ≤ 4 := by
          have h : ∀ b : Bool, ∀ i : Fin 4, (shortCode b i).length ≤ 4 := by decide
          exact h b i

        let exactShort (b : Bool) : Map := fun pr =>
          if pr.1 = shortCode b 0 then Part.some (natToBitString 0) else
          if pr.1 = shortCode b 1 then Part.some (natToBitString 1) else
          if pr.1 = shortCode b 2 then Part.some (natToBitString 2) else
          if pr.1 = shortCode b 3 then Part.some (natToBitString 3) else Part.none

        have exactShort_produces_iff (b : Bool) (p y x : BitString) :
            produces (exactShort b) p y x ↔
              ∃ i : Fin 4, p = shortCode b i ∧ x = natToBitString i.val := by
          constructor
          · intro h
            unfold produces exactShort at h
            split_ifs at h with h0 h1 h2 h3
            · exact ⟨0, h0, by simpa using h⟩
            · exact ⟨1, h1, by simpa using h⟩
            · exact ⟨2, h2, by simpa using h⟩
            · exact ⟨3, h3, by simpa using h⟩
            · exact (Part.notMem_none _ h).elim
          · rintro ⟨i, rfl, rfl⟩
            fin_cases i <;> cases b <;> simp [produces, exactShort, shortCode]

        have exactShort_partrec (b : Bool) : isDecompressor (exactShort b) := by
          have heq (i : Fin 4) : Computable (fun pr : BitString × BitString =>
              decide (pr.1 = shortCode b i)) :=
            (PrimrecRel.decide Primrec.eq).to_comp.comp Computable.fst
              (Computable.const (shortCode b i))
          have h := Partrec.cond (heq 0) (Computable.const (natToBitString 0)).partrec
            (Partrec.cond (heq 1) (Computable.const (natToBitString 1)).partrec
              (Partrec.cond (heq 2) (Computable.const (natToBitString 2)).partrec
                (Partrec.cond (heq 3) (Computable.const (natToBitString 3)).partrec Partrec.none)))
          exact h.of_eq (fun pr => by simp [exactShort, Bool.cond_eq_ite])

        let exactMachine (U : Map) (b : Bool) : Map := fun pr =>
          if simulationTag <+: pr.1 then U (pr.1.drop 30, pr.2) else exactShort b pr

        have exactMachine_long (U : Map) (b : Bool) (p y : BitString) :
            exactMachine U b (simulationTag ++ p, y) = U (p, y) := by
          simp [exactMachine, List.prefix_append, simulationTag]

        have exactMachine_produces_iff (U : Map) (b : Bool) (p y x : BitString) :
            produces (exactMachine U b) p y x ↔
              (∃ i : Fin 4, p = shortCode b i ∧ x = natToBitString i.val) ∨
              ∃ q, p = simulationTag ++ q ∧ produces U q y x := by
          constructor
          · intro h
            by_cases ht : simulationTag <+: p
            · right
              refine ⟨p.drop 30, ?_, ?_⟩
              · simpa [simulationTag] using ((prefix_iff_append_drop simulationTag p).mp ht).symm
              · simpa [produces, exactMachine, ht] using h
            · exact Or.inl ((exactShort_produces_iff b p y x).mp (by
                simpa [produces, exactMachine, ht] using h))
          · rintro (⟨i, rfl, rfl⟩ | ⟨q, rfl, hq⟩)
            · have ht := (shortCode_tag_incomparable b i).2
              simpa only [produces, exactMachine, ite_eq_right ht] using
                (exactShort_produces_iff b (shortCode b i) y (natToBitString i.val)).mpr ⟨i, rfl, rfl⟩
            · simpa only [produces, exactMachine_long] using hq

        have exactMachine_partrec (U : Map) (hU : isDecompressor U) (b : Bool) :
            isDecompressor (exactMachine U b) := by
          have hg : Computable (fun pr : BitString × BitString => decide (simulationTag <+: pr.1)) :=
            decide_prefix_primrec.to_comp.comp ((Computable.const simulationTag).pair Computable.fst)
          have hd : Computable (fun pr : BitString × BitString => (pr.1.drop 30, pr.2)) :=
            (list_drop_primrec.to_comp.comp Computable.fst (Computable.const 30)).pair Computable.snd
          exact (Partrec.cond hg (hU.comp hd) (exactShort_partrec b)).of_eq
            (fun pr => by simp [exactMachine, Bool.cond_eq_ite])

        have exactMachine_prefix (U : Map) (hU : IsPrefixMachine U) (b : Bool) :
            IsPrefixMachine (exactMachine U b) := by
          intro y p hp q hq hpq
          obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hp
          obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp hq
          rcases (exactMachine_produces_iff U b p y x).mp hx with
            ⟨i, rfl, _⟩ | ⟨p', rfl, hp'⟩
          · rcases (exactMachine_produces_iff U b q y z).mp hz with
              ⟨j, rfl, _⟩ | ⟨q', rfl, hq'⟩
            · exact congrArg (shortCode b) (shortCode_prefix_eq b i j hpq)
            · rcases List.prefix_or_prefix_of_prefix hpq (List.prefix_append simulationTag q') with h | h
              · exact ((shortCode_tag_incomparable b i).1 h).elim
              · exact ((shortCode_tag_incomparable b i).2 h).elim
          · rcases (exactMachine_produces_iff U b q y z).mp hz with
              ⟨j, rfl, _⟩ | ⟨q', rfl, hq'⟩
            · exact ((shortCode_tag_incomparable b j).2
                ((List.prefix_append simulationTag p').trans hpq)).elim
            · have htail : p' <+: q' := (List.prefix_append_right_inj simulationTag).mp hpq
              exact congrArg (fun t => simulationTag ++ t) (hU.eq_of_prefix hp' hq' htail)

        have exactMachine_KP_le (U : Map) (b : Bool) (x y : BitString) :
            KP (exactMachine U b) x y ≤ KP U x y + 30 := by
          by_cases ht : KP U x y = ⊤
          · simp [ht]
          obtain ⟨p, hp, hlen⟩ := exists_program_of_KP_ne_top ht
          have hp' : produces (exactMachine U b) (simulationTag ++ p) y x := by
            simpa only [produces, exactMachine_long] using hp
          calc
            KP (exactMachine U b) x y ≤ ((simulationTag ++ p).length : ENat) :=
              KP_le_programLength_of_produces hp'
            _ = KP U x y + 30 := by
              simp only [List.length_append, simulationTag, List.length_replicate, Nat.cast_add]
              rw [hlen, add_comm]
              norm_num

        have exactMachine_optimal (U : Map) (hU : IsOptimalPrefixConditional U) (b : Bool) :
            IsOptimalPrefixConditional (exactMachine U b) := by
          refine ⟨⟨exactMachine_partrec U hU.isDecompressor b,
            exactMachine_prefix U hU.isPrefixMachine b⟩, fun D hD => ?_⟩
          obtain ⟨c, hc⟩ := hU.invariance hD
          refine ⟨c + 30, fun x y => ?_⟩
          calc
            KP (exactMachine U b) x y ≤ KP U x y + 30 := exactMachine_KP_le U b x y
            _ ≤ (KP D x y + (c : ENat)) + 30 := add_le_add (hc x y) le_rfl
            _ = KP D x y + ((c + 30 : ℕ) : ENat) := by simp [Nat.cast_add, add_assoc]

        have exactMachine_KPNat_small (U : Map) (b : Bool) (i : Fin 4) :
            KPNat (exactMachine U b) i.val = ((shortCode b i).length : ENat) := by
          apply le_antisymm
          · exact KP_le_programLength_of_produces
              ((exactMachine_produces_iff U b (shortCode b i) [] (natToBitString i.val)).mpr
                (Or.inl ⟨i, rfl, rfl⟩))
          · change _ ≤ sInf (candidateLengths (exactMachine U b) (natToBitString i.val) [])
            refine le_sInf ?_
            rintro n ⟨p, hp, rfl⟩
            rcases (exactMachine_produces_iff U b p [] (natToBitString i.val)).mp hp with
              ⟨j, rfl, hij⟩ | ⟨q, rfl, hq⟩
            · have he : i = j := Fin.ext (natToBitString_injective hij)
              simp [he]
            · have hlen := shortCode_length_le b i
              have hn : (shortCode b i).length ≤ (simulationTag ++ q).length := by
                simp only [simulationTag, List.length_append, List.length_replicate]
                omega
              exact_mod_cast hn

        have exactMachine_KPNat_tail (U : Map) (b : Bool) (i : ℕ) :
            KPNat (exactMachine U b) (i + 4) = 30 + KPNat U (i + 4) := by
          apply le_antisymm
          · change KP (exactMachine U b) (natToBitString (i + 4)) [] ≤
              30 + KP U (natToBitString (i + 4)) []
            simpa only [add_comm] using exactMachine_KP_le U b (natToBitString (i + 4)) []
          · change _ ≤ sInf (candidateLengths (exactMachine U b) (natToBitString (i + 4)) [])
            refine le_sInf ?_
            rintro n ⟨p, hp, rfl⟩
            rcases (exactMachine_produces_iff U b p [] (natToBitString (i + 4))).mp hp with
              ⟨j, rfl, hij⟩ | ⟨q, rfl, hq⟩
            · have hj := j.isLt
              have he := natToBitString_injective hij
              omega
            · change 30 + KP U (natToBitString (i + 4)) [] ≤
                ((simulationTag ++ q).length : ENat)
              calc
                30 + KP U (natToBitString (i + 4)) [] ≤ 30 + (q.length : ENat) :=
                  add_le_add le_rfl (KP_le_programLength_of_produces hq)
                _ = ((simulationTag ++ q).length : ENat) := by
                  simp only [simulationTag, List.length_append, List.length_replicate, Nat.cast_add]
                  norm_num

        have exactMachine_weights_compare (U : Map) (i : ℕ) :
            complexityWeight (KPNat (exactMachine U false) i) ≤
                4 * complexityWeight (KPNat (exactMachine U true) i) ∧
              complexityWeight (KPNat (exactMachine U true) i) ≤
                4 * complexityWeight (KPNat (exactMachine U false) i) := by
          by_cases hi : i < 4
          · let j : Fin 4 := ⟨i, hi⟩
            change complexityWeight (KPNat (exactMachine U false) j.val) ≤
                4 * complexityWeight (KPNat (exactMachine U true) j.val) ∧
              complexityWeight (KPNat (exactMachine U true) j.val) ≤
                4 * complexityWeight (KPNat (exactMachine U false) j.val)
            rw [exactMachine_KPNat_small, exactMachine_KPNat_small]
            dsimp [j]
            interval_cases i <;> norm_num [shortCode, complexityWeight_coe] <;>
              constructor <;>
              apply (ENNReal.toReal_le_toReal (by simp)
                (ENNReal.mul_ne_top (by norm_num) (by simp))).mp <;> norm_num
          · obtain ⟨j, rfl⟩ : ∃ j, i = j + 4 := ⟨i - 4, by omega⟩
            rw [exactMachine_KPNat_tail, exactMachine_KPNat_tail]
            constructor <;> exact le_mul_of_one_le_left' (by norm_num : (1 : ℝ≥0∞) ≤ 4)

        have uniform_reindex {a : ℕ → BitString → ℝ≥0∞}
            (ha : IsUniformlyLowerSemicomputableTreeFamily a)
            {g : ℕ → ℕ} (hg : Computable g) :
            IsUniformlyLowerSemicomputableTreeFamily (fun i x => a (g i) x) := by
          obtain ⟨A, hAm, hAs, hAc⟩ := ha
          refine ⟨fun i s x => A (g i) s x,
            fun i s x => hAm (g i) s x, fun i x => hAs (g i) x, ?_⟩
          exact hAc.comp ((hg.comp Computable.fst).pair Computable.snd)

        have add_four_computable : Computable (fun i : ℕ => i + 4) :=
          Primrec.nat_add.to_comp.comp Computable.id (Computable.const 4)

        have sub_four_computable : Computable (fun i : ℕ => i - 4) :=
          Primrec.nat_sub.to_comp.comp Computable.id (Computable.const 4)

        let shiftedBase (U : Map) (x : BitString) : ℝ≥0∞ :=
          ∑' i, complexityWeight (KPNat U (i + 4)) * treeLSCEnum i x

        have shiftedBase_lsc (U : Map) (hU : IsOptimalPrefixConditional U) :
            IsLSC (fun x _ => shiftedBase U x) :=
          isLSC_tsum_of_uniform
            ((uniform_reindex (isUniformlyLSC_complexityWeight_KPNat U hU)
              add_four_computable).mul enumeration_uniform)

        have shiftedBase_children (U : Map) (x : BitString) :
            shiftedBase U (x ++ [false]) + shiftedBase U (x ++ [true]) ≤ shiftedBase U x := by
          unfold shiftedBase
          rw [← ENNReal.tsum_add]
          apply ENNReal.tsum_le_tsum
          intro i
          rw [← mul_add]
          gcongr
          exact (treeLSCEnum_isLowerSemicomputableContinuousSemimeasure i).1.2 x

        have shiftedBase_le_one (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) :
            shiftedBase U x ≤ 1 := by
          have ht : (∑' i, complexityWeight (KPNat U (i + 4))) ≤
              ∑' i, complexityWeight (KPNat U i) :=
            ENNReal.tsum_comp_le_tsum_of_injective (f := fun i : ℕ => i + 4)
              (fun _ _ h => Nat.add_right_cancel h)
              (fun i => complexityWeight (KPNat U i))
          refine le_trans (ENNReal.tsum_le_tsum (fun i => ?_))
            (ht.trans (tsum_complexityWeight_KPNat_le_one U hU))
          exact mul_le_of_le_one_right'
            ((treeLSCEnum_isLowerSemicomputableContinuousSemimeasure i).1.le_one x)

        have shiftedBase_pos (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) :
            0 < shiftedBase U x := by
          obtain ⟨j, hj⟩ := treeLSCEnum_complete
            (show IsLowerSemicomputableContinuousSemimeasure lengthMeasure from
              ⟨lengthMeasure_isContinuousTreeSemimeasure, lengthMeasure_isLSC_core⟩)
          have hd : complexityWeight (KPNat U (j + 4)) * treeLSCEnum j x ≤ shiftedBase U x := by
            exact ENNReal.le_tsum (f := fun i =>
              complexityWeight (KPNat U (i + 4)) * treeLSCEnum i x) j
          rw [hj] at hd
          have hp : 0 < lengthMeasure x :=
            pos_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num [lengthMeasure]))
          exact lt_of_lt_of_le
            (ENNReal.mul_pos (complexityWeight_KPNat_pos U hU (j + 4)).ne' hp.ne') hd

        let backgroundScale : ℚ := (2 ^ 21 - 2) / 2 ^ 30

        let exactBase (U : Map) (x : BitString) : ℝ≥0∞ :=
          ENNReal.ofReal (backgroundScale : ℝ) * shiftedBase U x

        have backgroundScale_pos : (0 : ℝ) < backgroundScale := by
          norm_num [backgroundScale]

        have backgroundScale_le_one : (backgroundScale : ℝ) ≤ 1 := by
          norm_num [backgroundScale]

        have exactBase_lsc (U : Map) (hU : IsOptimalPrefixConditional U) :
            IsLSC (fun x _ => exactBase U x) :=
          lsc_mul (lsc_computable_rat (Computable.const backgroundScale)) (shiftedBase_lsc U hU)

        have exactBase_children (U : Map) (x : BitString) :
            exactBase U (x ++ [false]) + exactBase U (x ++ [true]) ≤ exactBase U x := by
          simp only [exactBase, ← mul_add]
          exact mul_le_mul' le_rfl (shiftedBase_children U x)

        have exactBase_le_one (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) :
            exactBase U x ≤ 1 := by
          calc
            exactBase U x ≤ ENNReal.ofReal (backgroundScale : ℝ) * 1 :=
              mul_le_mul' le_rfl (shiftedBase_le_one U hU x)
            _ ≤ 1 := by
              rw [mul_one]
              exact ENNReal.ofReal_le_one.mpr backgroundScale_le_one

        have exactBase_ne_top (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) :
            exactBase U x ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top (exactBase_le_one U hU x)

        have exactBase_pos (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) :
            0 < exactBase U x :=
          ENNReal.mul_pos (ENNReal.ofReal_pos.mpr backgroundScale_pos).ne'
            (shiftedBase_pos U hU x).ne'

        let exactBackground (U : Map) (hU : IsOptimalPrefixConditional U) : Background := {
          mass := transport (exactBase U)
          semimeasure := {
            nonneg := fun _ _ => ENNReal.toReal_nonneg
            root := by
              change (exactBase U []).toReal ≤ 1
              exact ENNReal.toReal_le_of_le_ofReal (by norm_num)
                (by simpa using exactBase_le_one U hU [])
            children := by
              intro n h
              change (exactBase U (toBitString h ++ [false])).toReal +
                (exactBase U (toBitString h ++ [true])).toReal ≤ (exactBase U (toBitString h)).toReal
              rw [← ENNReal.toReal_add (exactBase_ne_top U hU _) (exactBase_ne_top U hU _)]
              exact (ENNReal.toReal_le_toReal
                (ENNReal.add_ne_top.mpr ⟨exactBase_ne_top U hU _, exactBase_ne_top U hU _⟩)
                (exactBase_ne_top U hU _)).mpr (exactBase_children U _)
          }
          positive := fun _ _ =>
            ENNReal.toReal_pos (exactBase_pos U hU _).ne' (exactBase_ne_top U hU _)

        }

        let prefixedFamily (p q : BitString → ℝ≥0∞) (i : ℕ) : BitString → ℝ≥0∞ :=
          if i < 2 then p else if i < 4 then q else treeLSCEnum (i - 4)

        have prefixedFamily_zero (p q : BitString → ℝ≥0∞) : prefixedFamily p q 0 = p := by
          simp [prefixedFamily]

        have prefixedFamily_one (p q : BitString → ℝ≥0∞) : prefixedFamily p q 1 = p := by
          simp [prefixedFamily]

        have prefixedFamily_two (p q : BitString → ℝ≥0∞) : prefixedFamily p q 2 = q := by
          simp [prefixedFamily]

        have prefixedFamily_three (p q : BitString → ℝ≥0∞) : prefixedFamily p q 3 = q := by
          simp [prefixedFamily]

        have prefixedFamily_add_four (p q : BitString → ℝ≥0∞) (i : ℕ) :
            prefixedFamily p q (i + 4) = treeLSCEnum i := by
          simp [prefixedFamily, show ¬i + 4 < 2 by omega, show ¬i + 4 < 4 by omega]

        have prefixedFamily_uniform {p q : BitString → ℝ≥0∞}
            (hp : IsLSC (fun x _ => p x)) (hq : IsLSC (fun x _ => q x)) :
            IsUniformlyLowerSemicomputableTreeFamily (prefixedFamily p q) := by
          obtain ⟨A, hAm, hAs, hAc⟩ := hp
          obtain ⟨B, hBm, hBs, hBc⟩ := hq
          obtain ⟨E, hEm, hEs, hEc⟩ := enumeration_uniform
          refine ⟨fun i s x => if i < 2 then A s x [] else if i < 4 then B s x [] else E (i - 4) s x,
            ?_, ?_, ?_⟩
          · intro i s x
            dsimp only
            split_ifs with h2 h4
            · exact hAm s x []
            · exact hBm s x []
            · exact hEm (i - 4) s x
          · intro i x
            unfold prefixedFamily
            dsimp only
            split_ifs with h2 h4
            · exact hAs x []
            · exact hBs x []
            · exact hEs (i - 4) x
          · have h2 : Computable (fun t : ℕ × ℕ × BitString => decide (t.1 < 2)) :=
              Primrec.nat_lt.decide.to_comp.comp Computable.fst (Computable.const 2)
            have h4 : Computable (fun t : ℕ × ℕ × BitString => decide (t.1 < 4)) :=
              Primrec.nat_lt.decide.to_comp.comp Computable.fst (Computable.const 4)
            have ha : Computable (fun t : ℕ × ℕ × BitString => A t.2.1 t.2.2 []) :=
              hAc.comp ((Computable.fst.comp Computable.snd).pair
                ((Computable.snd.comp Computable.snd).pair (Computable.const [])))
            have hb : Computable (fun t : ℕ × ℕ × BitString => B t.2.1 t.2.2 []) :=
              hBc.comp ((Computable.fst.comp Computable.snd).pair
                ((Computable.snd.comp Computable.snd).pair (Computable.const [])))
            have he : Computable (fun t : ℕ × ℕ × BitString => E (t.1 - 4) t.2.1 t.2.2) :=
              hEc.comp ((sub_four_computable.comp Computable.fst).pair Computable.snd)
            exact (Computable.cond h2 ha (Computable.cond h4 hb he)).of_eq (fun t => by
              by_cases h2 : t.1 < 2 <;> by_cases h4 : t.1 < 4 <;> simp [h2, h4])

        have prefixedFamily_effective {p q : BitString → ℝ≥0∞}
            (hp : IsLowerSemicomputableContinuousSemimeasure p)
            (hq : IsLowerSemicomputableContinuousSemimeasure q) (i : ℕ) :
            IsLowerSemicomputableContinuousSemimeasure (prefixedFamily p q i) := by
          unfold prefixedFamily
          split_ifs
          · exact hp
          · exact hq
          · exact treeLSCEnum_isLowerSemicomputableContinuousSemimeasure _

        have prefixedFamily_complete (p q : BitString → ℝ≥0∞)
            (a : BitString → ℝ≥0∞) (ha : IsLowerSemicomputableContinuousSemimeasure a) :
            ∃ i, prefixedFamily p q i = a := by
          obtain ⟨i, hi⟩ := treeLSCEnum_complete ha
          exact ⟨i + 4, (prefixedFamily_add_four p q i).trans hi⟩

        have prefixedFamily_renumbering {p q : BitString → ℝ≥0∞}
            (hp : IsLowerSemicomputableContinuousSemimeasure p)
            (hq : IsLowerSemicomputableContinuousSemimeasure q) :
            ∃ f g : ℕ → ℕ, Computable f ∧ Computable g ∧
              (∀ i, prefixedFamily p q (f i) = treeLSCEnum i) ∧
              (∀ i, treeLSCEnum (g i) = prefixedFamily p q i) := by
          obtain ⟨j, hj⟩ := treeLSCEnum_complete hp
          obtain ⟨k, hk⟩ := treeLSCEnum_complete hq
          refine ⟨fun i => i + 4, fun i => if i < 2 then j else if i < 4 then k else i - 4,
            add_four_computable, ?_, prefixedFamily_add_four p q, ?_⟩
          · have h2 : Computable (fun i : ℕ => decide (i < 2)) :=
              Primrec.nat_lt.decide.to_comp.comp Computable.id (Computable.const 2)
            have h4 : Computable (fun i : ℕ => decide (i < 4)) :=
              Primrec.nat_lt.decide.to_comp.comp Computable.id (Computable.const 4)
            exact (Computable.cond h2 (Computable.const j)
              (Computable.cond h4 (Computable.const k) sub_four_computable)).of_eq (fun i => by
                by_cases h2 : i < 2 <;> by_cases h4 : i < 4 <;> simp [h2, h4])
          · intro i
            unfold prefixedFamily
            dsimp only
            split_ifs <;> first | exact hj | exact hk | rfl

        have prefixedFamily_source (p q : BitString → ℝ≥0∞) :
            ∃ j, ∀ n (h : History n),
              prefixedFamily p q j (toBitString h) = ENNReal.ofReal (prob source n h) := by
          obtain ⟨j, hj⟩ := P33Mixture.source_member
          refine ⟨j + 4, fun n h => ?_⟩
          rw [prefixedFamily_add_four, hj]
          exact P33Mixture.sourceBits_history n h

        /- Multiplying all masses read by the Bayes rule by a positive constant preserves loss. -/
        have loss_eq_of_succ_mul (μ : Model) {s t : Mass} {c : ℝ}
            (hc : 0 < c)
            (h : ∀ n (x : History n) b, s (n + 1) (x, b) = c * t (n + 1) (x, b))
            (N : ℕ) : loss μ s N = loss μ t N := by
          simp only [loss, stepLoss, predict, h, mul_le_mul_iff_right₀ hc]

        /- The four special indices contribute total weights `1/8, 3/8`, in either order. -/
        let exactCore (a R : BitString → ℝ≥0∞) (b : Bool)
            (x : BitString) : ℝ≥0∞ :=
          ENNReal.ofReal ((if b then 3 else 1 : ℝ) / 8) * P33Complexity.rootSplice a true x +
            ENNReal.ofReal ((if b then 1 else 3 : ℝ) / 8) * P33Complexity.rootSplice a false x + R x

        /- Separate the four distinguished indices from the common infinite tail. -/
        have tsum_prefix4 (f : ℕ → ℝ≥0∞) :
            (∑' i, f i) = f 0 + f 1 + f 2 + f 3 + ∑' i, f (i + 4) := by
          simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using
            ((ENNReal.summable : Summable (fun i : ℕ => f (i + 4))).sum_add_tsum_nat_add'
              (f := f) (k := 4)).symm

        have exactCore_eq_tsum (w : ℕ → ℝ≥0∞) (τ : ℕ → BitString → ℝ≥0∞)
            (a R : BitString → ℝ≥0∞) (b : Bool)
            (hτ0 : τ 0 = P33Complexity.rootSplice a true)
            (hτ1 : τ 1 = P33Complexity.rootSplice a true)
            (hτ2 : τ 2 = P33Complexity.rootSplice a false)
            (hτ3 : τ 3 = P33Complexity.rootSplice a false)
            (hp : w 0 + w 1 = ENNReal.ofReal ((if b then 3 else 1 : ℝ) / 8))
            (hq : w 2 + w 3 = ENNReal.ofReal ((if b then 1 else 3 : ℝ) / 8))
            (htail : ∀ x, (∑' i, w (i + 4) * τ (i + 4) x) = R x) :
            (fun x => ∑' i, w i * τ i x) = exactCore a R b := by
          funext x
          rw [tsum_prefix4, htail, hτ0, hτ1, hτ2, hτ3]
          calc
            _ = (w 0 + w 1) * P33Complexity.rootSplice a true x +
                (w 2 + w 3) * P33Complexity.rootSplice a false x + R x := by ring
            _ = exactCore a R b x := by simp only [exactCore, hp, hq]

        /- The background multiplier is chosen so this exact mixture has the same actions as `xi`. -/
        have exactCore_loss {a R : BitString → ℝ≥0∞} (M : Background)
            (ha : ∀ x, a x ≠ ⊤) (hM : M.mass = transport a)
            (hR : ∀ x, R x ≠ ⊤)
            (hscale : ∀ x, a x = (2097150 : ℝ≥0∞) * R x)
            (b : Bool) (N : ℕ) :
            loss source (transport (exactCore a R b)) N = loss source (xi M b) N := by
          apply loss_eq_of_succ_mul source (c := (1048576 : ℝ) / 2097150) (by norm_num) _ N
          intro n h d
          let x := toBitString (n := n + 1) (h, d)
          have hx : x ≠ [] := by simp [x, toBitString]
          have hp0 : (0 : ℝ) ≤ (if b then 3 else 1 : ℝ) / 8 := by cases b <;> norm_num
          have hq0 : (0 : ℝ) ≤ (if b then 1 else 3 : ℝ) / 8 := by cases b <;> norm_num
          have hpfin :
              ENNReal.ofReal ((if b then 3 else 1 : ℝ) / 8) *
                ENNReal.ofReal (spliced M true (n + 1) (h, d)) ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
          have hqfin :
              ENNReal.ofReal ((if b then 1 else 3 : ℝ) / 8) *
                ENNReal.ofReal (spliced M false (n + 1) (h, d)) ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
          have hm : M.mass (n + 1) (h, d) = (a x).toReal := by rw [hM]; rfl
          have hs : (a x).toReal = (2097150 : ℝ) * (R x).toReal := by
            rw [hscale, ENNReal.toReal_mul]
            norm_num
          change (exactCore a R b x).toReal = _
          unfold exactCore
          rw [P33Complexity.rootSplice_eq hx, P33Complexity.rootSplice_eq hx]
          change (ENNReal.ofReal ((if b then 3 else 1 : ℝ) / 8) *
              P33Complexity.rawSplice a true (toBitString (n := n + 1) (h, d)) +
            ENNReal.ofReal ((if b then 1 else 3 : ℝ) / 8) *
              P33Complexity.rawSplice a false (toBitString (n := n + 1) (h, d)) + R x).toReal = _
          rw [P33Complexity.rawSplice_history M ha hM,
            P33Complexity.rawSplice_history M ha hM,
            ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hpfin, hqfin⟩) (hR x),
            ENNReal.toReal_add hpfin hqfin]
          simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0,
            ENNReal.toReal_ofReal hq0,
            ENNReal.toReal_ofReal ((spliced_semimeasure M true).nonneg (n + 1) (h, d)),
            ENNReal.toReal_ofReal ((spliced_semimeasure M false).nonneg (n + 1) (h, d))]
          cases b <;> norm_num [xi, mix, eta, P, Q, hm] <;> linarith

        have exactCore_gap {a R : BitString → ℝ≥0∞} (M : Background)
            (ha : ∀ x, a x ≠ ⊤) (hM : M.mass = transport a)
            (hR : ∀ x, R x ≠ ⊤)
            (hscale : ∀ x, a x = (2097150 : ℝ≥0∞) * R x)
            (n : ℕ) (hn : 2 ≤ n) :
            (n : ℝ) ^ (1 / 4 : ℝ) / 256 ≤
              loss source (transport (exactCore a R false)) n -
                loss source (transport (exactCore a R true)) n := by
          rw [exactCore_loss M ha hM hR hscale false,
            exactCore_loss M ha hM hR hscale true]
          exact (theorem4 M n hn).1

        have exactMixture_properties (C : Map) (hC : IsOptimalPrefixConditional C)
            (τ : ℕ → BitString → ℝ≥0∞)
            (hτu : IsUniformlyLowerSemicomputableTreeFamily τ)
            (hτ : ∀ i, IsLowerSemicomputableContinuousSemimeasure (τ i)) :
            (∀ x, exactMixture C τ (x ++ [false]) + exactMixture C τ (x ++ [true]) ≤
              exactMixture C τ x) ∧
            exactMixture C τ [] ≤ 1 ∧ IsLSC (fun x _ => exactMixture C τ x) := by
          refine ⟨fun x => ?_, ?_, ?_⟩
          · unfold exactMixture
            rw [← ENNReal.tsum_add]
            exact ENNReal.tsum_le_tsum fun i => by
              rw [← mul_add]
              gcongr
              exact (hτ i).1.2 x
          · unfold exactMixture
            simp only [(hτ _).1.1, mul_one]
            exact tsum_complexityWeight_KPNat_le_one C hC
          · exact isLSC_tsum_of_uniform ((isUniformlyLSC_complexityWeight_KPNat C hC).mul hτu)

        have exactMixture_universal (C : Map) (hC : IsOptimalPrefixConditional C)
            (τ : ℕ → BitString → ℝ≥0∞)
            (hcomplete : ∀ a : BitString → ℝ≥0∞,
              IsLowerSemicomputableContinuousSemimeasure a → ∃ i, τ i = a) :
            IsUniversal (exactMixture C τ) := by
          intro a ha
          obtain ⟨i, hi⟩ := hcomplete a ha
          have hw0 := (P33Complexity.complexityWeight_KPNat_pos C hC i).ne'
          have hwt := complexityWeight_ne_top (KPNat C i)
          refine ⟨(complexityWeight (KPNat C i))⁻¹, ENNReal.inv_ne_top.mpr hw0, fun x => ?_⟩
          have hterm : complexityWeight (KPNat C i) * τ i x ≤ exactMixture C τ x :=
            ENNReal.le_tsum (f := fun j => complexityWeight (KPNat C j) * τ j x) i
          calc
            a x = (complexityWeight (KPNat C i))⁻¹ *
                (complexityWeight (KPNat C i) * τ i x) := by
                  rw [← mul_assoc, ENNReal.inv_mul_cancel hw0 hwt, one_mul, hi]
            _ ≤ (complexityWeight (KPNat C i))⁻¹ * exactMixture C τ x :=
              mul_le_mul' le_rfl hterm

        obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
        let a := exactBase U
        let R : BitString → ℝ≥0∞ := fun x => (2 : ℝ≥0∞)⁻¹ ^ 30 * shiftedBase U x
        let p := P33Complexity.rootSplice a true
        let q := P33Complexity.rootSplice a false
        let τ := prefixedFamily p q
        have heff (b : Bool) : IsLowerSemicomputableContinuousSemimeasure
            (P33Complexity.rootSplice a b) :=
          P33Complexity.rootSplice_effective (exactBackground U hU)
            (exactBase_ne_top U hU) rfl (exactBase_lsc U hU) b
        have hτu : IsUniformlyLowerSemicomputableTreeFamily τ :=
          prefixedFamily_uniform (heff true).2 (heff false).2
        have hτ : ∀ i, IsLowerSemicomputableContinuousSemimeasure (τ i) :=
          prefixedFamily_effective (heff true) (heff false)
        have hcomplete : ∀ a' : BitString → ℝ≥0∞,
            IsLowerSemicomputableContinuousSemimeasure a' → ∃ i, τ i = a' :=
          prefixedFamily_complete p q
        have hC (b : Bool) : IsOptimalPrefixConditional (exactMachine U b) :=
          exactMachine_optimal U hU b
        have hR : ∀ x, R x ≠ ⊤ := fun x =>
          ENNReal.mul_ne_top (by norm_num)
            (ne_top_of_le_ne_top ENNReal.one_ne_top (shiftedBase_le_one U hU x))
        have hscale : ∀ x, a x = (2097150 : ℝ≥0∞) * R x := by
          intro x
          dsimp [a, R, exactBase]
          rw [← mul_assoc]
          congr 1
          apply (ENNReal.toReal_eq_toReal_iff' ENNReal.ofReal_ne_top
            (ENNReal.mul_ne_top (by norm_num) (by simp))).mp
          norm_num [backgroundScale]
        have hpairP (b : Bool) :
            complexityWeight (KPNat (exactMachine U b) 0) +
              complexityWeight (KPNat (exactMachine U b) 1) =
                ENNReal.ofReal ((if b then 3 else 1 : ℝ) / 8) := by
          change complexityWeight (KPNat (exactMachine U b) (0 : Fin 4).val) +
            complexityWeight (KPNat (exactMachine U b) (1 : Fin 4).val) = _
          rw [exactMachine_KPNat_small, exactMachine_KPNat_small]
          cases b <;> norm_num [shortCode, complexityWeight] <;>
            apply (ENNReal.toReal_eq_toReal_iff' (by simp) ENNReal.ofReal_ne_top).mp <;>
            norm_num [ENNReal.toReal_add]
        have hpairQ (b : Bool) :
            complexityWeight (KPNat (exactMachine U b) 2) +
              complexityWeight (KPNat (exactMachine U b) 3) =
                ENNReal.ofReal ((if b then 1 else 3 : ℝ) / 8) := by
          change complexityWeight (KPNat (exactMachine U b) (2 : Fin 4).val) +
            complexityWeight (KPNat (exactMachine U b) (3 : Fin 4).val) = _
          rw [exactMachine_KPNat_small, exactMachine_KPNat_small]
          cases b <;> norm_num [shortCode, complexityWeight] <;>
            apply (ENNReal.toReal_eq_toReal_iff' (by simp) ENNReal.ofReal_ne_top).mp <;>
            norm_num [ENNReal.toReal_add]
        have htail (b : Bool) (x : BitString) :
            (∑' i, complexityWeight (KPNat (exactMachine U b) (i + 4)) * τ (i + 4) x) = R x := by
          simp only [τ, prefixedFamily_add_four]
          change (∑' i, complexityWeight (KPNat (exactMachine U b) (i + 4)) * treeLSCEnum i x) =
            ((2 : ℝ≥0∞)⁻¹ ^ 30) * ∑' i, complexityWeight (KPNat U (i + 4)) * treeLSCEnum i x
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro i
          rw [exactMachine_KPNat_tail, add_comm (30 : ENat)]
          change complexityWeight (KPNat U (i + 4) + (30 : ℕ)) * treeLSCEnum i x = _
          rw [complexityWeight_add_nat]
          ring
        have hmixture (b : Bool) : exactMixture (exactMachine U b) τ = exactCore a R b :=
          exactCore_eq_tsum (fun i => complexityWeight (KPNat (exactMachine U b) i))
            τ a R b (prefixedFamily_zero p q) (prefixedFamily_one p q)
            (prefixedFamily_two p q) (prefixedFamily_three p q) (hpairP b) (hpairQ b) (htail b)
        have hgap (n : ℕ) (hn : 2 ≤ n) :
            (n : ℝ) ^ (1 / 4 : ℝ) / 256 ≤
              loss source (transport (exactMixture (exactMachine U false) τ)) n -
                loss source (transport (exactMixture (exactMachine U true) τ)) n := by
          rw [hmixture false, hmixture true]
          exact exactCore_gap (exactBackground U hU) (exactBase_ne_top U hU) rfl hR hscale n hn
        obtain ⟨hchildm, hrootm, hlscm⟩ := exactMixture_properties _ (hC false) τ hτu hτ
        obtain ⟨hchildp, hrootp, hlscp⟩ := exactMixture_properties _ (hC true) τ hτu hτ
        refine ⟨τ, exactMachine U false, exactMachine U true,
          hτu, hτ, hcomplete, hC false, hC true,
          prefixedFamily_renumbering (heff true) (heff false),
          exactMachine_weights_compare U,
          exactMixture_universal _ (hC false) τ hcomplete,
          exactMixture_universal _ (hC true) τ hcomplete,
          hchildm, hchildp, hrootm, hrootp, hlscm, hlscp,
          prefixedFamily_source p q, ?_, gap_tendsto_atTop _ hgap⟩
        intro n hn
        have hb := hgap n (by omega)
        have hn0 : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        linarith

end P33Exact

/- Fidelity note.
Source: book Problem 3.3 (two mixtures ξ, ξ′ over M; is L^ξ − L^ξ′ < ∞?) with the universal prior of Sec. 2.4 /
Sec. 3.2 in the index convention K(ν_i) := K(i) (book p. 48; as in docs/reviews/2026-11-21-fidelity-33-complexity.md),
i.e. ξ_U = Σ_i 2^{-K_U(i)} ν_i over an enumeration of the class M_U of lsc semimeasures. Here the two mixtures differ
only in the reference machine: both use exact weights 2^{-K_C(i)} for optimal prefix machines C⁻, C⁺ (upstream
`IsOptimalPrefixConditional`, `KPNat` = prefix complexity of the binary code of i, `complexityWeight` = 2^{-·}).
Paper source: Pro 008 Theorem 6; 027 Theorem 5; referee docs/reviews/2026-11-21-referee-027.md. Fidelity review:
docs/reviews/2026-11-21-fidelity-33-exact.md (faithful with caveats; caveats L1-L4 applied here). Planned design:
τ_0 = τ_1 = P, τ_2 = τ_3 = Q, τ_{i+4} = treeLSCEnum i; C⁻ gives indices 0-3 short codes of lengths 4,4,2,3 (C⁺: 2,3,4,4)
and on 1^L·p (L ≥ 21) simulates U0(p, y); P, Q are the theorem4 splices of M ∝ Σ_{i≥4} 2^{-L-K_U0(i)} τ_i.
- τ and C± are constructed (existential); τ is exhaustive with repetitions, uniformly lsc, and a computable
  renumbering of `treeLSCEnum` (f, g); each τ_i has root 1 (upstream convention of P33Effective/P33Complexity).
- The mixtures are not normalized (root ≤ 1); Bayes actions do not depend on a positive scale.
- Per-index weight ratio ≤ 4 (027's {1/4, 1, 4}); universality (`P33Effective.IsUniversal`) stated.
- Constant 1/512 and n ≥ 3 follow 027 Thm 5; the planned design gives 1/256 for n ≥ 2, which implies it.
- Not claimed: the result for every pair of optimal machines, for the standard enumeration itself, or for semantic
  weights 2^{-K(ν)}; Solomonoff's M_U (monotone machines; 008 Theorem 7).
- Ties toward 1 (`predict`), as in the mixture review.
-/
```

Main lemmas and verification:

- **Exact machine complexities:** `exactMachine_KPNat_small` proves the four prescribed short-code lengths; `exactMachine_KPNat_tail` proves \(K_{C^\pm}(i+4)=30+K_U(i+4)\). `exactMachine_optimal` establishes optimality for every condition, and `exactMachine_weights_compare` proves the factor-four comparison.
- **Effective enumeration and background:** `shiftedBase_lsc`, `exactBackground`, `prefixedFamily_uniform`, and `prefixedFamily_renumbering` supply the positive background and the required computable enumeration in both directions.
- **Exact mixture and loss:** `exactCore_eq_tsum` identifies the four distinguished contributions and common tail. `loss_eq_of_succ_mul` and `exactCore_loss` transfer the losses to Theorem 4 using the positive factor \(1048576/2097150\). `exactCore_gap` gives the stronger \(n^{1/4}/256\) bound for \(n\ge2\).
- **Remaining clauses:** `exactMixture_properties` proves the children inequalities, root bounds, and lower semicomputability; `exactMixture_universal` proves universality from completeness and positive complexity weights.
- **Deviations:** No change to the mathematical construction. Optimality uses the direct simulation overhead \(c+30\). Helpers are local to preserve the frozen prefix exactly.
- **Verification:** `lake build HutterPrizes.P33Exact` succeeded. The file contains no `sorry`, `admit`, new axiom declarations, or `native_decide`. The axiom audit reports only **`propext`, `Classical.choice`, and `Quot.sound`**.