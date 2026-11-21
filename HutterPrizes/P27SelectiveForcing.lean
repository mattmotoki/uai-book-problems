/-
Lemma 1 (selective forcing) of report 023, equations (5)--(13).
Checked with Lean 4.35.0 and Mathlib v4.35.0.
The attached P27BlockBound.lean is imported unchanged.
No support assumption on either law is needed: the backward invariant is
proved without division, including zero-probability branches.
-/
import HutterPrizes.P27BlockBound

open scoped BigOperators

noncomputable section
namespace P27

set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

/-! ## Part 1: statement layer. -/

/-- The law ν: follow P off F and force f at each selected time. -/
def forcingModel (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) : Model where
  cond n x := if n + 1 ∈ F then (if f n x then 1 else 0) else P.cond n x
  nonneg n x := by split_ifs <;> first | exact P.nonneg n x | norm_num
  le_one n x := by split_ifs <;> first | exact P.le_one n x | norm_num

/-- The report's hypotheses, with no full-support assumption. -/
structure SelectiveForcingHypotheses (P Q : Model) (N m : ℕ) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (ρ r : ℝ) : Prop where
  times : ∀ t ∈ F, 1 ≤ t ∧ t ≤ N
  card_eq : F.card = m
  rho_lt_one : ρ < 1
  r_pos : 0 < r
  r_le_one : r ≤ 1
  rare : ∀ n, n + 1 ∈ F → ∀ x, bitProb P n x (f n x) ≤ ρ
  dominates : ∀ z : History N,
    r * prob (forcingModel P F f) N z ≤ prob Q N z

/-- The exact lower bound (7); proved by `selective_forcing` below. -/
def SelectiveForcingClaim : Prop :=
  ∀ (P Q : Model) (N m : ℕ) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (ρ r : ℝ),
    SelectiveForcingHypotheses P Q N m F f ρ r →
      2 * (r - ρ ^ m) ≤ ∑ t ∈ F, A P Q t

/-! ## Part 2: proofs. -/

/-- The law Q̂: use Q on F and P elsewhere. -/
def selectiveModel (P Q : Model) (F : Finset ℕ) : Model where
  cond n x := if n + 1 ∈ F then Q.cond n x else P.cond n x
  nonneg n x := by split_ifs <;> first | exact Q.nonneg n x | exact P.nonneg n x
  le_one n x := by split_ifs <;> first | exact Q.le_one n x | exact P.le_one n x

/-- All prescribed bits through the current history have occurred. -/
def forcingEvent (F : Finset ℕ) (f : (n : ℕ) → History n → Bool) :
    (n : ℕ) → History n → Prop
  | 0, _ => True
  | n + 1, (x, b) => forcingEvent F f n x ∧ (n + 1 ∈ F → b = f n x)

/-- Probability of the forcing event through time n. -/
def eventMass (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (n : ℕ) : ℝ := by
  classical
  exact ∑ x : History n, if forcingEvent F f n x then prob P n x else 0

/-- Probability of satisfying the next k steps, starting at history x. -/
def remainingSuccess (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) :
    (k n : ℕ) → History n → ℝ
  | 0, _, _ => 1
  | k + 1, n, x =>
      if n + 1 ∈ F then
        bitProb P n x (f n x) * remainingSuccess P F f k (n + 1) (x, f n x)
      else ∑ b : Bool, bitProb P n x b * remainingSuccess P F f k (n + 1) (x, b)

lemma remainingSuccess_nonneg (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (k n : ℕ) (x : History n) :
    0 ≤ remainingSuccess P F f k n x := by
  induction k generalizing n with
  | zero => simp [remainingSuccess]
  | succ k ih =>
    rw [remainingSuccess]
    split_ifs
    · exact mul_nonneg (bitProb_nonneg P n x _) (ih _ _)
    · exact Finset.sum_nonneg (fun b _ =>
        mul_nonneg (bitProb_nonneg P n x b) (ih _ _))

lemma eventMass_eq_sum_remaining (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (n k : ℕ) :
    eventMass P F f (n + k) =
      ∑ x : History n, if forcingEvent F f n x then
        prob P n x * remainingSuccess P F f k n x else 0 := by
  classical
  induction k generalizing n with
  | zero => simp [eventMass, remainingSuccess]
  | succ k ih =>
    rw [show n + (k + 1) = (n + 1) + k by omega, ih, history_sum_succ]
    apply Finset.sum_congr rfl
    intro x _
    by_cases he : forcingEvent F f n x
    · by_cases hs : n + 1 ∈ F
      · cases hf : f n x <;>
          simp [forcingEvent, prob, he, remainingSuccess, hs, hf, mul_assoc]
      · simp [forcingEvent, prob, he, remainingSuccess, hs]
        ring
    · simp [forcingEvent, he]

lemma remainingSuccess_root (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (N : ℕ) :
    remainingSuccess P F f N 0 () = eventMass P F f N := by
  have h := eventMass_eq_sum_remaining P F f 0 N
  simpa [forcingEvent, prob] using h.symm

lemma eventMass_le_one (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (n : ℕ) :
    eventMass P F f n ≤ 1 := by
  classical
  rw [eventMass, ← prob_total P n]
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact prob_nonneg P n x

lemma eventMass_succ_selected (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (n : ℕ) (hn : n + 1 ∈ F) :
    eventMass P F f (n + 1) =
      ∑ x : History n, if forcingEvent F f n x then
        prob P n x * bitProb P n x (f n x) else 0 := by
  classical
  unfold eventMass
  rw [history_sum_succ]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : forcingEvent F f n x
  · cases hf : f n x <;> simp [forcingEvent, hn, hx, hf, prob]
  · simp [forcingEvent, hx]

lemma eventMass_succ_unselected (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (n : ℕ) (hn : n + 1 ∉ F) :
    eventMass P F f (n + 1) = eventMass P F f n := by
  classical
  unfold eventMass
  rw [history_sum_succ]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : forcingEvent F f n x
  · simp [forcingEvent, hn, hx, prob, bitProb]
    ring
  · simp [forcingEvent, hx]

lemma eventMass_succ_le (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (n : ℕ) (ρ : ℝ)
    (hn : n + 1 ∈ F)
    (hrare : ∀ x, bitProb P n x (f n x) ≤ ρ) :
    eventMass P F f (n + 1) ≤ eventMass P F f n * ρ := by
  classical
  rw [eventMass_succ_selected P F f n hn, eventMass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : forcingEvent F f n x
  · simp only [hx, ↓reduceIte]
    exact mul_le_mul_of_nonneg_left (hrare x) (prob_nonneg P n x)
  · simp [hx]

lemma eventMass_le_filtered_pow (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (N : ℕ) (ρ : ℝ)
    (hF : ∀ t ∈ F, 1 ≤ t) (hρ : 0 ≤ ρ)
    (hrare : ∀ n, n + 1 ∈ F → ∀ x, bitProb P n x (f n x) ≤ ρ) :
    eventMass P F f N ≤ ρ ^ (F.filter (fun t => t ≤ N)).card := by
  classical
  induction N with
  | zero =>
      have hzero : F.filter (fun t => t ≤ 0) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro t ht
        obtain ⟨htF, ht0⟩ := Finset.mem_filter.mp ht
        have := hF t htF
        omega
      rw [hzero]
      simp [eventMass, forcingEvent, prob]
  | succ n ih =>
      by_cases hn : n + 1 ∈ F
      · have hfilter : F.filter (fun t => t ≤ n + 1) =
            insert (n + 1) (F.filter (fun t => t ≤ n)) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨ht, htn⟩
            by_cases heq : t = n + 1
            · exact Or.inl heq
            · exact Or.inr ⟨ht, by omega⟩
          · rintro (rfl | ⟨ht, htn⟩)
            · exact ⟨hn, le_rfl⟩
            · exact ⟨ht, by omega⟩
        have hnot : n + 1 ∉ F.filter (fun t => t ≤ n) := by simp
        rw [hfilter, Finset.card_insert_of_notMem hnot, pow_succ]
        exact (eventMass_succ_le P F f n ρ hn (hrare n hn)).trans
          (mul_le_mul_of_nonneg_right ih hρ)
      · have hfilter : F.filter (fun t => t ≤ n + 1) =
            F.filter (fun t => t ≤ n) := by
          ext t
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨ht, htn⟩
            refine ⟨ht, ?_⟩
            by_contra h
            have heq : t = n + 1 := by omega
            exact hn (heq ▸ ht)
          · rintro ⟨ht, htn⟩
            exact ⟨ht, by omega⟩
        rw [eventMass_succ_unselected P F f n hn, hfilter]
        exact ih

lemma eventMass_le_pow (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (N m : ℕ) (ρ : ℝ)
    (hF : ∀ t ∈ F, 1 ≤ t ∧ t ≤ N) (hm : F.card = m)
    (hrare : ∀ n, n + 1 ∈ F → ∀ x, bitProb P n x (f n x) ≤ ρ) :
    eventMass P F f N ≤ ρ ^ m := by
  classical
  by_cases hρ : 0 ≤ ρ
  · have hfilter : F.filter (fun t => t ≤ N) = F := by
      apply Finset.filter_eq_self.mpr
      exact fun t ht => (hF t ht).2
    have h := eventMass_le_filtered_pow P F f N ρ (fun t ht => (hF t ht).1) hρ hrare
    simpa [hfilter, hm] using h
  · have hFempty : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have htpos := (hF t ht).1
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
      have hex : ∀ k, Nonempty (History k) := by
        intro k
        induction k with
        | zero => exact ⟨()⟩
        | succ k ih => exact ⟨(Classical.choice ih, false)⟩
      let x : History n := Classical.choice (hex n)
      exact hρ ((bitProb_nonneg P n x (f n x)).trans (hrare n ht x))
    have hmzero : m = 0 := by simpa [hFempty] using hm.symm
    simpa [hmzero] using eventMass_le_one P F f N

lemma binary_weighted_lower
    (a₀ a₁ c p q : ℝ)
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hc : 0 ≤ c)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (h₀ : c * (1 - p) ≤ (1 - q) * a₀)
    (h₁ : c * p ≤ q * a₁) :
    c ≤ (1 - p) * a₀ + p * a₁ := by
  by_cases hc0 : c = 0
  · subst c
    positivity
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  by_cases hq0 : q = 0
  · subst q
    have hp0 : p = 0 := by nlinarith
    subst p
    simpa using h₀
  by_cases hq1 : q = 1
  · subst q
    have hp1 : p = 1 := by nlinarith
    subst p
    simpa using h₁
  have hqpos : 0 < q := lt_of_le_of_ne hq₀ (Ne.symm hq0)
  have hqlt : q < 1 := lt_of_le_of_ne hq₁ hq1
  have hu := mul_le_mul_of_nonneg_left h₀
    (mul_nonneg hq₀ (sub_nonneg.mpr hp₁))
  have hv := mul_le_mul_of_nonneg_left h₁
    (mul_nonneg (sub_nonneg.mpr hq₁) hp₀)
  have hs := mul_nonneg hc (sq_nonneg (p - q))
  have hmul : q * (1 - q) * c ≤
      q * (1 - q) * ((1 - p) * a₀ + p * a₁) := by
    nlinarith only [hu, hv, hs]
  exact le_of_mul_le_mul_left hmul (mul_pos hqpos (sub_pos.mpr hqlt))

lemma forcing_bit_of_mem (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (n : ℕ) (x : History n) (b : Bool)
    (hn : n + 1 ∈ F) :
    bitProb (forcingModel P F f) n x b = if b = f n x then 1 else 0 := by
  cases b <;> cases hf : f n x <;> simp [bitProb, forcingModel, hn, hf]

lemma forcing_bit_of_notMem (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (n : ℕ) (x : History n) (b : Bool)
    (hn : n + 1 ∉ F) :
    bitProb (forcingModel P F f) n x b = bitProb P n x b := by
  simp [bitProb, forcingModel, hn]

lemma selective_bit_of_mem (P Q : Model) (F : Finset ℕ)
    (n : ℕ) (x : History n) (b : Bool) (hn : n + 1 ∈ F) :
    bitProb (selectiveModel P Q F) n x b = bitProb Q n x b := by
  simp [bitProb, selectiveModel, hn]

/-- Division-free form of the report's backward invariant. -/
lemma remainingSuccess_lower (P Q : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (N : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hdom : ∀ z : History N, r * prob (forcingModel P F f) N z ≤ prob Q N z)
    (k : ℕ) :
    ∀ (n : ℕ) (x : History n), n + k = N →
      r * prob (forcingModel P F f) n x ≤
        prob Q n x * remainingSuccess (selectiveModel P Q F) F f k n x := by
  induction k with
  | zero =>
      intro n x hn
      have hn' : n = N := by omega
      subst n
      simpa [remainingSuccess] using hdom x
  | succ k ih =>
      intro n x hn
      have hnk : n + 1 + k = N := by omega
      by_cases hs : n + 1 ∈ F
      · have h := ih (n + 1) (x, f n x) hnk
        rw [prob, forcing_bit_of_mem P F f n x (f n x) hs, ite_eq_left rfl, mul_one] at h
        calc
          r * prob (forcingModel P F f) n x ≤
              prob Q (n + 1) (x, f n x) *
                remainingSuccess (selectiveModel P Q F) F f k (n + 1) (x, f n x) := h
          _ = prob Q n x *
              remainingSuccess (selectiveModel P Q F) F f (k + 1) n x := by
            rw [remainingSuccess, ite_eq_left hs, selective_bit_of_mem P Q F n x (f n x) hs]
            simp only [prob, mul_assoc]
      · have hb (b : Bool) :
            (r * prob (forcingModel P F f) n x) * bitProb P n x b ≤
              bitProb Q n x b * (prob Q n x *
                remainingSuccess (selectiveModel P Q F) F f k (n + 1) (x, b)) := by
          have h := ih (n + 1) (x, b) hnk
          rw [prob, forcing_bit_of_notMem P F f n x b hs, prob] at h
          simpa only [mul_assoc, mul_comm, mul_left_comm] using h
        have hnum := binary_weighted_lower
          (prob Q n x * remainingSuccess (selectiveModel P Q F) F f k (n + 1) (x, false))
          (prob Q n x * remainingSuccess (selectiveModel P Q F) F f k (n + 1) (x, true))
          (r * prob (forcingModel P F f) n x) (P.cond n x) (Q.cond n x)
          (mul_nonneg (prob_nonneg Q n x) (remainingSuccess_nonneg _ _ _ _ _ _))
          (mul_nonneg (prob_nonneg Q n x) (remainingSuccess_nonneg _ _ _ _ _ _))
          (mul_nonneg hr (prob_nonneg _ _ _))
          (P.nonneg n x) (P.le_one n x) (Q.nonneg n x) (Q.le_one n x)
          (by simpa [bitProb] using hb false)
          (by simpa [bitProb] using hb true)
        calc
          r * prob (forcingModel P F f) n x ≤
              (1 - P.cond n x) * (prob Q n x *
                remainingSuccess (selectiveModel P Q F) F f k (n + 1) (x, false)) +
              P.cond n x * (prob Q n x *
                remainingSuccess (selectiveModel P Q F) F f k (n + 1) (x, true)) := hnum
          _ = prob Q n x *
              remainingSuccess (selectiveModel P Q F) F f (k + 1) n x := by
            simp [remainingSuccess, hs, bitProb, selectiveModel]
            ring

lemma eventMass_selective_ge (P Q : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (N : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hdom : ∀ z : History N, r * prob (forcingModel P F f) N z ≤ prob Q N z) :
    r ≤ eventMass (selectiveModel P Q F) F f N := by
  have h := remainingSuccess_lower P Q F f N r hr hdom N 0 () (by omega)
  simpa [prob, remainingSuccess_root] using h

lemma eventMass_nonneg (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (N : ℕ) :
    0 ≤ eventMass P F f N := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact prob_nonneg P N x
  · exact le_rfl

/-- Push a finite law forward to the indicator of the forcing event. -/
def eventBinaryModel (P : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (N : ℕ) : Model where
  cond _ _ := eventMass P F f N
  nonneg _ _ := eventMass_nonneg P F f N
  le_one _ _ := eventMass_le_one P F f N

lemma eventBinary_l1_le (P R : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (N : ℕ) :
    l1 (eventBinaryModel P F f N) (eventBinaryModel R F f N) 1 ≤ l1 P R N := by
  classical
  have hc (T : Model) :
      (∑ x : History N, if forcingEvent F f N x then 0 else prob T N x) =
        1 - eventMass T F f N := by
    have hs : eventMass T F f N +
        (∑ x : History N, if forcingEvent F f N x then 0 else prob T N x) = 1 := by
      rw [← prob_total T N]
      unfold eventMass
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : forcingEvent F f N x <;> simp [hx]
    linarith
  have he : (∑ x : History N,
      if forcingEvent F f N x then prob P N x - prob R N x else 0) =
        eventMass P F f N - eventMass R F f N := by
    unfold eventMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : forcingEvent F f N x <;> simp [hx]
  have hn : (∑ x : History N,
      if forcingEvent F f N x then 0 else prob P N x - prob R N x) =
        (1 - eventMass P F f N) - (1 - eventMass R F f N) := by
    rw [← hc P, ← hc R, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : forcingEvent F f N x <;> simp [hx]
  change (∑ x : History 1,
    |prob (eventBinaryModel P F f N) 1 x - prob (eventBinaryModel R F f N) 1 x|) ≤ _
  rw [history_sum_succ]
  simp only [prob, bitProb, eventBinaryModel, Bool.false_eq_true, ↓reduceIte,
    one_mul, Fintype.sum_unique]
  rw [← hn, ← he]
  calc
    _ ≤ (∑ x : History N,
        |if forcingEvent F f N x then 0 else prob P N x - prob R N x|) +
      (∑ x : History N,
        |if forcingEvent F f N x then prob P N x - prob R N x else 0|) :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ = l1 P R N := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : forcingEvent F f N x <;> simp [hx]

/-- An event version of the imported single-coordinate L1 gap inequality. -/
lemma two_mul_event_gap_le_l1 (P R : Model) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (N : ℕ) :
    2 * (eventMass R F f N - eventMass P F f N) ≤ l1 P R N := by
  have h := two_mul_gap_le_l1
    (eventBinaryModel P F f N) (eventBinaryModel R F f N) 1 ((), true)
  simp only [prob, bitProb, eventBinaryModel, ↓reduceIte, one_mul] at h
  exact h.trans (eventBinary_l1_le P R F f N)

lemma selective_stepError (P Q : Model) (F : Finset ℕ) (n : ℕ) :
    stepError P (selectiveModel P Q F) n =
      if n + 1 ∈ F then stepError P Q n else 0 := by
  by_cases hn : n + 1 ∈ F
  · simp [stepError, localError, bitProb, selectiveModel, hn]
  · simp [stepError, localError, bitProb, selectiveModel, hn]

lemma selective_error_sum (P Q : Model) (F : Finset ℕ) (N : ℕ)
    (hF : ∀ t ∈ F, 1 ≤ t ∧ t ≤ N) :
    (∑ n ∈ Finset.range N, stepError P (selectiveModel P Q F) n) =
      ∑ t ∈ F, A P Q t := by
  simp_rw [selective_stepError]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn
    exact (Finset.mem_filter.mp hn).2
  · intro n hn m hm hnm
    omega
  · intro t ht
    obtain ⟨ht1, htN⟩ := hF t ht
    refine ⟨t - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, ?_⟩
    · simpa [Nat.sub_add_cancel ht1] using ht
    · omega
  · intro n hn
    rfl

lemma selective_hybrid_inequality (P Q : Model) (F : Finset ℕ) (N : ℕ)
    (hF : ∀ t ∈ F, 1 ≤ t ∧ t ≤ N) :
    l1 P (selectiveModel P Q F) N ≤ ∑ t ∈ F, A P Q t := by
  have h := hybrid_inequality P (selectiveModel P Q F) N
  rw [selective_error_sum P Q F N hF] at h
  exact h


/-- A slightly stronger form exposing exactly the hypotheses used in the proof. -/
theorem selective_forcing_bound (P Q : Model) (N m : ℕ) (F : Finset ℕ)
    (f : (n : ℕ) → History n → Bool) (ρ r : ℝ)
    (hF : ∀ t ∈ F, 1 ≤ t ∧ t ≤ N) (hm : F.card = m)
    (hr : 0 ≤ r)
    (hrare : ∀ n, n + 1 ∈ F → ∀ x, bitProb P n x (f n x) ≤ ρ)
    (hdom : ∀ z : History N,
      r * prob (forcingModel P F f) N z ≤ prob Q N z) :
    2 * (r - ρ ^ m) ≤ ∑ t ∈ F, A P Q t := by
  have hu := eventMass_le_pow P F f N m ρ hF hm hrare
  have hl := eventMass_selective_ge P Q F f N r hr hdom
  have he := two_mul_event_gap_le_l1 P (selectiveModel P Q F) F f N
  have hh := selective_hybrid_inequality P Q F N hF
  linarith

/-- Lemma 1 of report 023, with the same conclusion and weaker support assumptions. -/
theorem selective_forcing : SelectiveForcingClaim := by
  intro P Q N m F f ρ r h
  exact selective_forcing_bound P Q N m F f ρ r
    h.times h.card_eq h.r_pos.le h.rare h.dominates

end P27
