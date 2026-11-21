/-
Theorem 4: aggregation over an arbitrary strictly positive semimeasure.
Lean 4.35.0; Mathlib v4.35.0.
The imported P33Theorem3 file is used without modification.
-/
import HutterPrizes.P33Theorem3

open scoped BigOperators

namespace RobustExperiment.Theorem4

set_option maxHeartbeats 2000000

/-! Part 1. Statement layer: the source, arbitrary background, and predictors. -/

inductive State where
  | trunk (j : ℕ)
  | branch (j t : ℕ) (h : History t)

def next : State → Bool → State
  | .trunk j, true => .trunk (j + 1)
  | .trunk j, false => .branch j 0 ()
  | .branch j t h, b => .branch j (t + 1) (h, b)

def scan : (n : ℕ) → History n → State
  | 0, _ => .trunk 0
  | n + 1, (h, b) => next (scan n h) b

def ones : (j : ℕ) → History j
  | 0 => ()
  | j + 1 => (ones j, true)

def append {a : ℕ} (p : History a) : (t : ℕ) → History t → History (a + t)
  | 0, _ => p
  | t + 1, (h, b) => (append p t h, b)

def word : State → Σ n, History n
  | .trunk j => ⟨j, ones j⟩
  | .branch j t h => ⟨j + 1 + t, append (ones j, false) t h⟩

def extendWord (w : Σ n, History n) (b : Bool) : Σ n, History n :=
  ⟨w.1 + 1, (w.2, b)⟩

def scale (j : ℕ) : ℕ := 4 ^ j

lemma scale_pos (j : ℕ) : 1 ≤ scale j := by
  unfold scale
  exact Nat.one_le_pow _ _ (by norm_num)

noncomputable def localModel (j : ℕ) : Model := experiment (scale j) (scale_pos j) true

noncomputable def stateCond : State → ℝ
  | .trunk _ => 1 / 2
  | .branch j t h => (localModel j).cond t h

lemma stateCond_nonneg (s : State) : 0 ≤ stateCond s := by
  cases s with
  | trunk j => norm_num [stateCond]
  | branch j t h => exact (localModel j).nonneg t h

lemma stateCond_le_one (s : State) : stateCond s ≤ 1 := by
  cases s with
  | trunk j => norm_num [stateCond]
  | branch j t h => exact (localModel j).le_one t h

noncomputable def source : Model where
  cond n h := stateCond (scan n h)
  nonneg _ _ := stateCond_nonneg _
  le_one _ _ := stateCond_le_one _

structure IsSemimeasure (s : Mass) : Prop where
  nonneg : ∀ n h, 0 ≤ s n h
  root : s 0 () ≤ 1
  children : ∀ n h, s (n+1) (h,false) + s (n+1) (h,true) ≤ s n h

structure Background where
  mass : Mass
  semimeasure : IsSemimeasure mass
  positive : ∀ n h, 0 < mass n h

def atState (s : Mass) (v : State) : ℝ := s (word v).1 (word v).2

def branchWeight (M : Background) (j : ℕ) : ℝ := M.mass (j+1) (ones j,false)

noncomputable def spliceState (M : Background) (i : Bool) : State → ℝ
  | .trunk j => M.mass j (ones j)
  | .branch j t h => branchWeight M j * prob (experiment (scale j) (scale_pos j) i) t h

noncomputable def spliced (M : Background) (i : Bool) : Mass :=
  fun n h => spliceState M i (scan n h)

noncomputable def P (M : Background) : Mass := spliced M true

noncomputable def Q (M : Background) : Mass := spliced M false

noncomputable def eta : ℝ := 1 / 2 ^ 20

noncomputable def xi (M : Background) (i : Bool) : Mass :=
  mix (1-eta) (mix (if i then 3/4 else 1/4) (P M) (Q M)) M.mass

noncomputable def xiMinus (M : Background) : Mass := xi M false

noncomputable def xiPlus (M : Background) : Mass := xi M true

/-- The requested conclusion, stated before its proof. -/
def Theorem4Statement (M : Background) : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (n : ℝ)^(1/4 : ℝ)/256 ≤
      loss source (xiMinus M) n - loss source (xiPlus M) n ∧
    loss source (xiMinus M) n - loss source (xiPlus M) n ≤
      (n : ℝ)^(1/4 : ℝ)/8

/-! Part 2a. History encoding and exact source probabilities. -/

lemma word_next (s : State) (b : Bool) : word (next s b) = extendWord (word s) b := by
  cases s <;> cases b <;> rfl

lemma word_scan (n : ℕ) (h : History n) : word (scan n h) = ⟨n, h⟩ := by
  induction n with
  | zero => cases h; rfl
  | succ n ih =>
    rcases h with ⟨h, b⟩
    rw [scan, word_next, ih]
    rfl

lemma scan_ones (j : ℕ) : scan j (ones j) = .trunk j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [ones, scan, ih, next]

lemma scan_branch (j t : ℕ) (h : History t) :
    scan (j + 1 + t) (append (ones j, false) t h) = .branch j t h := by
  induction t with
  | zero => cases h; simp only [append, scan, scan_ones, next]
  | succ t ih =>
    rcases h with ⟨h, b⟩
    change next (scan (j + 1 + t) (append (ones j, false) t h)) b = _
    rw [ih]
    rfl

lemma scan_word (s : State) : scan (word s).1 (word s).2 = s := by
  cases s with
  | trunk j => exact scan_ones j
  | branch j t h => exact scan_branch j t h

lemma source_cond_ones (j : ℕ) : source.cond j (ones j) = 1 / 2 := by
  change stateCond (scan j (ones j)) = _
  rw [scan_ones]
  rfl

lemma source_cond_branch (j t : ℕ) (h : History t) :
    source.cond (j + 1 + t) (append (ones j, false) t h) = (localModel j).cond t h := by
  change stateCond (scan (j + 1 + t) (append (ones j, false) t h)) = _
  rw [scan_branch]
  rfl

lemma prob_source_ones (j : ℕ) : prob source j (ones j) = (1 / 2 : ℝ) ^ j := by
  induction j with
  | zero => simp [prob]
  | succ j ih =>
    simp only [ones, prob, ↓reduceIte, source_cond_ones, ih, pow_succ]

lemma prob_source_branch (j t : ℕ) (h : History t) :
    prob source (j + 1 + t) (append (ones j, false) t h) =
      (1 / 2 : ℝ) ^ (j + 1) * prob (localModel j) t h := by
  induction t with
  | zero =>
    cases h
    simp only [append, prob, Bool.false_eq_true, ↓reduceIte,
      source_cond_ones, prob_source_ones, pow_succ]
    ring
  | succ t ih =>
    rcases h with ⟨h, b⟩
    change prob source (j + 1 + t) (append (ones j, false) t h) *
        (if b then source.cond (j + 1 + t) (append (ones j, false) t h)
          else 1 - source.cond (j + 1 + t) (append (ones j, false) t h)) =
      (1 / 2 : ℝ) ^ (j + 1) *
        (prob (localModel j) t h * (if b then (localModel j).cond t h
          else 1 - (localModel j).cond t h))
    rw [ih, source_cond_branch]
    ring

lemma state_history_sum_succ (n : ℕ) (f : History (n + 1) → ℝ) :
    (∑ x : History (n + 1), f x) = ∑ x : History n, (f (x, false) + f (x, true)) := by
  change (∑ x : History n × Bool, f x) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  congr 1
  funext x
  ring

noncomputable def evolve (f : State → ℝ) (s : State) : ℝ :=
  (1 - stateCond s) * f (next s false) + stateCond s * f (next s true)

noncomputable def branchExpectation (j t : ℕ) (f : State → ℝ) : ℝ :=
  ∑ h : History t, prob (localModel j) t h * f (.branch j t h)

noncomputable def sourceExpectation (n : ℕ) (f : State → ℝ) : ℝ :=
  ∑ h : History n, prob source n h * f (scan n h)

lemma branchExpectation_evolve (j t : ℕ) (f : State → ℝ) :
    branchExpectation j t (evolve f) = branchExpectation j (t + 1) f := by
  unfold branchExpectation
  rw [state_history_sum_succ]
  apply Finset.sum_congr rfl
  intro h _
  simp only [evolve, stateCond, next, prob, Bool.false_eq_true, ↓reduceIte]
  ring

lemma sourceExpectation_succ (n : ℕ) (f : State → ℝ) :
    sourceExpectation (n + 1) f = sourceExpectation n (evolve f) := by
  unfold sourceExpectation
  rw [state_history_sum_succ]
  apply Finset.sum_congr rfl
  intro h _
  simp only [evolve, scan, prob, source, Bool.false_eq_true, ↓reduceIte]
  ring

lemma expectation_decomp (n : ℕ) (f : State → ℝ) :
    sourceExpectation n f = (1 / 2 : ℝ) ^ n * f (.trunk n) +
      ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1) *
        branchExpectation j (n - (j + 1)) f := by
  induction n generalizing f with
  | zero => simp [sourceExpectation, prob, scan]
  | succ n ih =>
    rw [sourceExpectation_succ, ih, Finset.sum_range_succ]
    have hs : (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1) *
          branchExpectation j (n - (j + 1)) (evolve f)) =
        ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1) *
          branchExpectation j (n + 1 - (j + 1)) f := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [branchExpectation_evolve]
      congr 2
      omega
    rw [hs]
    rw [Nat.sub_self]
    simp only [evolve, stateCond, next,
      branchExpectation, prob, Fintype.sum_unique, one_mul]
    rw [pow_succ]
    ring

/-! Part 2b. Semimeasures, dominance, and normalized branch predictors. -/

lemma atState_scan (s : Mass) (n : ℕ) (h : History n) :
    atState s (scan n h) = s n h := by
  unfold atState
  rw [word_scan]

lemma atState_children (M : Background) (v : State) :
    atState M.mass (next v false) + atState M.mass (next v true) ≤
      atState M.mass v := by
  cases v <;> exact M.semimeasure.children _ _

lemma branchWeight_pos (M : Background) (j : ℕ) : 0 < branchWeight M j :=
  M.positive _ _

lemma spliceState_nonneg (M : Background) (i : Bool) (v : State) :
    0 ≤ spliceState M i v := by
  cases v with
  | trunk j => exact M.semimeasure.nonneg _ _
  | branch j t h => exact mul_nonneg (branchWeight_pos M j).le (prob_nonneg _ _ _)

lemma spliceState_children (M : Background) (i : Bool) (v : State) :
    spliceState M i (next v false) + spliceState M i (next v true) ≤
      spliceState M i v := by
  cases v with
  | trunk j =>
    simpa only [next, spliceState, prob, mul_one, branchWeight, ones] using
      M.semimeasure.children j (ones j)
  | branch j t h =>
    simp only [next, spliceState, prob, Bool.false_eq_true, ↓reduceIte]
    apply le_of_eq
    ring

lemma spliced_semimeasure (M : Background) (i : Bool) : IsSemimeasure (spliced M i) where
  nonneg _ _ := spliceState_nonneg M i _
  root := M.semimeasure.root
  children n h := spliceState_children M i (scan n h)

theorem P_semimeasure (M : Background) : IsSemimeasure (P M) := spliced_semimeasure M true

theorem Q_semimeasure (M : Background) : IsSemimeasure (Q M) := spliced_semimeasure M false

lemma IsSemimeasure.mix {p q : Mass} (hp : IsSemimeasure p) (hq : IsSemimeasure q)
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : IsSemimeasure (mix w p q) where
  nonneg n h := add_nonneg (mul_nonneg hw0 (hp.nonneg n h))
    (mul_nonneg (sub_nonneg.mpr hw1) (hq.nonneg n h))
  root := by
    have h₁ := mul_le_mul_of_nonneg_left hp.root hw0
    have h₂ := mul_le_mul_of_nonneg_left hq.root (sub_nonneg.mpr hw1)
    dsimp only [RobustExperiment.mix]
    nlinarith
  children n h := by
    have h₁ := mul_le_mul_of_nonneg_left (hp.children n h) hw0
    have h₂ := mul_le_mul_of_nonneg_left (hq.children n h) (sub_nonneg.mpr hw1)
    dsimp only [RobustExperiment.mix]
    nlinarith

lemma eta_nonneg : 0 ≤ eta := by norm_num [eta]

lemma eta_le_one : eta ≤ 1 := by norm_num [eta]

theorem xi_semimeasure (M : Background) (i : Bool) : IsSemimeasure (xi M i) := by
  apply IsSemimeasure.mix
    (IsSemimeasure.mix (P_semimeasure M) (Q_semimeasure M) _
      (by cases i <;> norm_num) (by cases i <;> norm_num)) M.semimeasure
  · exact sub_nonneg.mpr eta_le_one
  · linarith [eta_nonneg]

theorem xi_dominates (M : Background) (i : Bool) (n : ℕ) (h : History n) :
    eta * M.mass n h ≤ xi M i n h := by
  have hp := (P_semimeasure M).nonneg n h
  have hq := (Q_semimeasure M).nonneg n h
  have he := sub_nonneg.mpr eta_le_one
  cases i <;> simp only [xi, mix, Bool.false_eq_true, ↓reduceIte]
  · nlinarith [mul_nonneg he hp, mul_nonneg he hq]
  · nlinarith [mul_nonneg he hp, mul_nonneg he hq]

theorem xiMinus_dominates (M : Background) (n : ℕ) (h : History n) :
    eta * M.mass n h ≤ xiMinus M n h := xi_dominates M false n h

theorem xiPlus_dominates (M : Background) (n : ℕ) (h : History n) :
    eta * M.mass n h ≤ xiPlus M n h := xi_dominates M true n h

noncomputable def branchBackground (M : Background) (j : ℕ) : Semimeasure ((scale j)^2) where
  mass t h := atState M.mass (.branch j t h) / branchWeight M j
  nonneg t _ h := div_nonneg (M.semimeasure.nonneg _ _) (branchWeight_pos M j).le
  root := by
    change branchWeight M j / branchWeight M j = 1
    exact div_self (ne_of_gt (branchWeight_pos M j))
  children t _ h := by
    simpa only [next, add_div] using
      div_le_div_of_nonneg_right (atState_children M (.branch j t h))
        (branchWeight_pos M j).le

noncomputable def xiState (M : Background) (i : Bool) (v : State) : ℝ :=
  (1-eta) * ((if i then 3/4 else 1/4) * spliceState M true v +
    (1-(if i then 3/4 else 1/4)) * spliceState M false v) + eta * atState M.mass v

lemma xi_atState (M : Background) (i : Bool) (n : ℕ) (h : History n) :
    xi M i n h = xiState M i (scan n h) := by
  simp only [xi, mix, P, Q, spliced, xiState, atState_scan]
  ring

lemma xiState_branch (M : Background) (i : Bool) (j t : ℕ) (h : History t) :
    xiState M i (.branch j t h) = branchWeight M j *
      contaminated (scale j) (scale_pos j) (branchBackground M j) eta i t h := by
  have hw : branchWeight M j ≠ 0 := ne_of_gt (branchWeight_pos M j)
  simp only [xiState, spliceState, contaminated, core, mix, branchBackground]
  field_simp
  ring

noncomputable def statePredict (M : Background) (i : Bool) (v : State) : Bool :=
  if xiState M i (next v false) ≤ xiState M i (next v true) then true else false

lemma predict_xi (M : Background) (i : Bool) (n : ℕ) (h : History n) :
    predict (xi M i) n h = statePredict M i (scan n h) := by
  simp only [predict, xi_atState, scan, statePredict]

lemma statePredict_branch (M : Background) (i : Bool) (j t : ℕ) (h : History t) :
    statePredict M i (.branch j t h) =
      predict (contaminated (scale j) (scale_pos j) (branchBackground M j) eta i) t h := by
  simp only [statePredict, next, xiState_branch, predict,
    mul_le_mul_iff_right₀ (branchWeight_pos M j)]

noncomputable def stateGap (M : Background) (v : State) : ℝ :=
  (if statePredict M false v then 1-stateCond v else stateCond v) -
  (if statePredict M true v then 1-stateCond v else stateCond v)

lemma stateGap_trunk (M : Background) (j : ℕ) : stateGap M (.trunk j) = 0 := by
  unfold stateGap
  simp only [stateCond]
  split_ifs <;> norm_num

lemma stateGap_branch (M : Background) (j t : ℕ) (h : History t) :
    stateGap M (.branch j t h) =
      risk (localModel j) t h
        (predict (contaminated (scale j) (scale_pos j) (branchBackground M j) eta false) t h) -
      risk (localModel j) t h
        (predict (contaminated (scale j) (scale_pos j) (branchBackground M j) eta true) t h) := by
  simp only [stateGap, statePredict_branch, stateCond, risk]

lemma scale_squared (j : ℕ) : (scale j)^2 = 16^j := by
  unfold scale
  rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
  norm_num

/-! Part 2c. Explicit equations identifying the construction in the question. -/

lemma spliced_ones (M : Background) (i : Bool) (j : ℕ) :
    spliced M i j (ones j) = M.mass j (ones j) := by
  simp only [spliced, scan_ones, spliceState]

lemma spliced_branch (M : Background) (i : Bool) (j t : ℕ) (h : History t) :
    spliced M i (j + 1 + t) (append (ones j, false) t h) =
      M.mass (j + 1) (ones j, false) *
        prob (experiment (scale j) (scale_pos j) i) t h := by
  simp only [spliced, scan_branch, spliceState, branchWeight]

lemma P_ones (M : Background) (j : ℕ) : P M j (ones j) = M.mass j (ones j) :=
  spliced_ones M true j

lemma Q_ones (M : Background) (j : ℕ) : Q M j (ones j) = M.mass j (ones j) :=
  spliced_ones M false j

lemma P_branch (M : Background) (j t : ℕ) (h : History t) :
    P M (j + 1 + t) (append (ones j, false) t h) =
      M.mass (j + 1) (ones j, false) * prob (localModel j) t h :=
  spliced_branch M true j t h

lemma Q_branch (M : Background) (j t : ℕ) (h : History t) :
    Q M (j + 1 + t) (append (ones j, false) t h) =
      M.mass (j + 1) (ones j, false) *
        prob (experiment (scale j) (scale_pos j) false) t h :=
  spliced_branch M false j t h

lemma source_cond_explicit (j t : ℕ) (h : History t) :
    source.cond (j + 1 + t) (append (ones j, false) t h) =
      if t < 16 ^ j then 1 / 2 + 1 / (32 * (4 : ℝ) ^ j) else 1 / 2 := by
  rw [source_cond_branch]
  change (if t < (scale j) ^ 2 then 1 / 2 + gamma (scale j) else 1 / 2) = _
  rw [scale_squared]
  simp only [gamma, scale, Nat.cast_pow, Nat.cast_ofNat]

lemma prob_source_tag (j : ℕ) :
    prob source (j + 1) (ones j, false) = (1 / 2 : ℝ) ^ (j + 1) := by
  simp only [prob, Bool.false_eq_true, ↓reduceIte, source_cond_ones,
    prob_source_ones, pow_succ]
  ring

lemma xiMinus_explicit (M : Background) (n : ℕ) (h : History n) :
    xiMinus M n h =
      (1 - eta) * ((1 / 4) * P M n h + (3 / 4) * Q M n h) + eta * M.mass n h := by
  simp only [xiMinus, xi, mix, Bool.false_eq_true, ↓reduceIte]
  ring

lemma xiPlus_explicit (M : Background) (n : ℕ) (h : History n) :
    xiPlus M n h =
      (1 - eta) * ((3 / 4) * P M n h + (1 / 4) * Q M n h) + eta * M.mass n h := by
  simp only [xiPlus, xi, mix, ↓reduceIte]
  ring

/-! Part 2d. Branch bounds obtained from the imported theorem3. -/

lemma branch_prob_total (p : Model) (n : ℕ) :
    (∑ x : History n, prob p n x) = 1 := by
  induction n with
  | zero =>
    change (∑ _x : Unit, (1 : ℝ)) = 1
    simp
  | succ n ih =>
    change (∑ x : History n × Bool, prob p (n+1) x) = 1
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, prob, Bool.false_eq_true, ↓reduceIte]
    convert ih using 1
    apply Finset.sum_congr rfl
    intro x _
    ring

noncomputable def branchGap (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ) (t : ℕ) : ℝ :=
  loss (experiment k hk true) (contaminated k hk A η false) t -
    loss (experiment k hk true) (contaminated k hk A η true) t

lemma branchGap_sum (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ) (t : ℕ) :
    branchGap k hk A η t =
      ∑ n ∈ Finset.range t,
        (stepLoss (experiment k hk true) (contaminated k hk A η false) n -
         stepLoss (experiment k hk true) (contaminated k hk A η true) n) := by
  simp only [branchGap, loss, Finset.sum_sub_distrib]

lemma branchGap_step_nonneg (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ) (hη0 : 0 ≤ η)
    (hη1 : η ≤ (1 : ℝ) / 2 ^ 20) (n : ℕ) :
    0 ≤ stepLoss (experiment k hk true) (contaminated k hk A η false) n -
      stepLoss (experiment k hk true) (contaminated k hk A η true) n :=
  (theorem3 k hk A η hη0 hη1).2.2 n

lemma branchGap_nonneg (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ) (hη0 : 0 ≤ η)
    (hη1 : η ≤ (1 : ℝ) / 2 ^ 20) (t : ℕ) :
    0 ≤ branchGap k hk A η t := by
  rw [branchGap_sum]
  exact Finset.sum_nonneg fun n _ => branchGap_step_nonneg k hk A η hη0 hη1 n

lemma branchGap_mono (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ) (hη0 : 0 ≤ η)
    (hη1 : η ≤ (1 : ℝ) / 2 ^ 20) :
    Monotone (branchGap k hk A η) := by
  intro s t hst
  rw [branchGap_sum, branchGap_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hst)
    (fun n _ _ => branchGap_step_nonneg k hk A η hη0 hη1 n)

lemma branchGap_lower (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ) (hη0 : 0 ≤ η)
    (hη1 : η ≤ (1 : ℝ) / 2 ^ 20) (t : ℕ) (ht : k ^ 2 ≤ t) :
    (k : ℝ) / 32 ≤ branchGap k hk A η t := by
  exact (theorem3 k hk A η hη0 hη1).1.trans
    (branchGap_mono k hk A η hη0 hη1 ht)

lemma branch_risk_fair (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : k ^ 2 ≤ n) (x : History n) (b : Bool) :
    risk (experiment k hk true) n x b = 1 / 2 := by
  have h : ¬n < k ^ 2 := by omega
  cases b <;> norm_num [risk, experiment, h]

lemma branchGap_step_zero (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ)
    (n : ℕ) (hn : k ^ 2 ≤ n) :
    stepLoss (experiment k hk true) (contaminated k hk A η false) n -
      stepLoss (experiment k hk true) (contaminated k hk A η true) n = 0 := by
  simp only [stepLoss, branch_risk_fair k hk n hn, sub_self]

lemma branchGap_step_upper (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ) (n : ℕ) :
    stepLoss (experiment k hk true) (contaminated k hk A η false) n -
      stepLoss (experiment k hk true) (contaminated k hk A η true) n ≤
        2 * gamma k := by
  by_cases hn : n < k ^ 2
  · have hr (x : History n) :
        risk (experiment k hk true) n x
            (predict (contaminated k hk A η false) n x) -
          risk (experiment k hk true) n x
            (predict (contaminated k hk A η true) n x) ≤ 2 * gamma k := by
      have hg := (gamma_pos k hk).le
      cases predict (contaminated k hk A η false) n x <;>
        cases predict (contaminated k hk A η true) n x <;>
        simp only [risk, experiment, hn, ↓reduceIte, Bool.false_eq_true] <;> linarith
    calc
      _ = ∑ x : History n, prob (experiment k hk true) n x *
          (risk (experiment k hk true) n x
              (predict (contaminated k hk A η false) n x) -
            risk (experiment k hk true) n x
              (predict (contaminated k hk A η true) n x)) := by
        simp only [stepLoss, mul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ x : History n, prob (experiment k hk true) n x * (2 * gamma k) := by
        exact Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (hr x) (prob_nonneg _ n x)
      _ = 2 * gamma k := by rw [← Finset.sum_mul, branch_prob_total, one_mul]
  · rw [branchGap_step_zero k hk A η n (by omega)]
    positivity [gamma_pos k hk]

lemma branchGap_eq_min (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ) (t : ℕ) :
    branchGap k hk A η t = branchGap k hk A η (min t (k ^ 2)) := by
  rw [branchGap_sum, branchGap_sum]
  symm
  apply Finset.sum_subset (Finset.range_mono (min_le_left _ _))
  intro n hnt hnm
  have hn : k ^ 2 ≤ n := by
    simp only [Finset.mem_range] at hnt hnm
    omega
  exact branchGap_step_zero k hk A η n hn

lemma branchGap_upper (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ) (t : ℕ) :
    branchGap k hk A η t ≤ ((min t (k ^ 2) : ℕ) : ℝ) / (16 * (k : ℝ)) := by
  rw [branchGap_eq_min, branchGap_sum]
  calc
    _ ≤ ∑ _n ∈ Finset.range (min t (k ^ 2)), 2 * gamma k :=
      Finset.sum_le_sum fun n _ => branchGap_step_upper k hk A η n
    _ = ((min t (k ^ 2) : ℕ) : ℝ) / (16 * (k : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, gamma]
      ring

/-! Part 2e. Geometric aggregation and the real fourth-root bounds. -/

lemma two_pow_four (j : ℕ) : ((2 : ℝ) ^ j) ^ 4 = (16 : ℝ) ^ j := by
  rw [← pow_mul, Nat.mul_comm j 4, pow_mul]
  norm_num

lemma two_pow_three (j : ℕ) : ((2 : ℝ) ^ j) ^ 3 = (8 : ℝ) ^ j := by
  rw [← pow_mul, Nat.mul_comm j 3, pow_mul]
  norm_num

lemma index_le_sixteen_pow (j : ℕ) : j + 1 ≤ 16 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ]
    have hp : 1 ≤ 16 ^ j := Nat.one_le_pow j 16 (by decide)
    nlinarith

lemma sum_two_pow (k : ℕ) : (∑ j ∈ Finset.range k, (2 : ℝ) ^ j) = 2 ^ k - 1 := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, mul_one] using geom_sum_mul (2 : ℝ) k

lemma sum_eighth_pow_le (k : ℕ) : (∑ j ∈ Finset.range k, (1 / 8 : ℝ) ^ j) ≤ 8 / 7 := by
  have h := geom_sum_mul_neg (1 / 8 : ℝ) k
  have hp : 0 ≤ (1 / 8 : ℝ) ^ k := by positivity
  nlinarith

lemma geometric_cutoff_bound (g : ℕ → ℝ) (N : ℝ) (hN : 0 ≤ N)
    (hg : ∀ j, 0 ≤ g j)
    (hcap : ∀ j, g j ≤ (2 : ℝ) ^ j / 32)
    (htime : ∀ j, g j ≤ N * (1 / 8 : ℝ) ^ j / 32)
    (n k : ℕ) :
    (∑ j ∈ Finset.range n, g j) ≤ (2 : ℝ) ^ k / 32 +
      N * (1 / 8 : ℝ) ^ k / 28 := by
  have hmono : (∑ j ∈ Finset.range n, g j) ≤ ∑ j ∈ Finset.range (k + n), g j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => hg j)
  have hhead : (∑ j ∈ Finset.range k, g j) ≤ (2 : ℝ) ^ k / 32 := by
    calc
      (∑ j ∈ Finset.range k, g j) ≤ ∑ j ∈ Finset.range k, (2 : ℝ) ^ j / 32 :=
        Finset.sum_le_sum (fun j _ => hcap j)
      _ = ((2 : ℝ) ^ k - 1) / 32 := by rw [← Finset.sum_div, sum_two_pow]
      _ ≤ (2 : ℝ) ^ k / 32 := by linarith
  have htail : (∑ j ∈ Finset.range n, g (k + j)) ≤
      N * (1 / 8 : ℝ) ^ k / 28 := by
    calc
      (∑ j ∈ Finset.range n, g (k + j)) ≤
          ∑ j ∈ Finset.range n, N * (1 / 8 : ℝ) ^ (k + j) / 32 :=
        Finset.sum_le_sum (fun j _ => htime (k + j))
      _ = (N * (1 / 8 : ℝ) ^ k / 32) *
          (∑ j ∈ Finset.range n, (1 / 8 : ℝ) ^ j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_add]
        ring
      _ ≤ (N * (1 / 8 : ℝ) ^ k / 32) * (8 / 7) :=
        mul_le_mul_of_nonneg_left (sum_eighth_pow_le n) (by positivity)
      _ = N * (1 / 8 : ℝ) ^ k / 28 := by ring
  rw [Finset.sum_range_add] at hmono
  linarith

theorem aggregate_bounds (g : ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hg : ∀ j, 0 ≤ g j)
    (hcap : ∀ j, g j ≤ (2 : ℝ) ^ j / 32)
    (htime : ∀ j, g j ≤ (n : ℝ) * (1 / 8 : ℝ) ^ j / 32)
    (hcomplete : ∀ j, j + 1 + 16 ^ j ≤ n → (2 : ℝ) ^ j / 64 ≤ g j) :
    (n : ℝ) ^ (1 / 4 : ℝ) / 256 ≤ (∑ j ∈ Finset.range n, g j) ∧
    (∑ j ∈ Finset.range n, g j) ≤ (n : ℝ) ^ (1 / 4 : ℝ) / 8 := by
  let r : ℝ := (n : ℝ) ^ (1 / 4 : ℝ)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hr0 : 0 ≤ r := Real.rpow_nonneg hn0 _
  have hr4 : r ^ 4 = n := by
    simpa [r] using Real.rpow_inv_natCast_pow hn0 (show (4 : ℕ) ≠ 0 by decide)
  constructor
  · obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ (n : ℝ) / 2 by linarith)
      (show (1 : ℝ) < 16 by norm_num)
    have hindex : (j : ℝ) + 1 ≤ (16 : ℝ) ^ j := by exact_mod_cast index_le_sixteen_pow j
    have hdone : j + 1 + 16 ^ j ≤ n := by
      have hc : ((j + 1 + 16 ^ j : ℕ) : ℝ) ≤ n := by
        push_cast
        linarith
      exact_mod_cast hc
    have hjn : j < n := by
      have hp : 1 ≤ 16 ^ j := Nat.one_le_pow j 16 (by decide)
      omega
    have hlower := hcomplete j hdone
    have hsingle : g j ≤ ∑ i ∈ Finset.range n, g i :=
      Finset.single_le_sum (fun i _ => hg i) (Finset.mem_range.mpr hjn)
    have hrlarge : r ≤ 4 * (2 : ℝ) ^ j := by
      apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity)
      rw [hr4, mul_pow, two_pow_four, pow_succ] at *
      have hp : 0 ≤ (16 : ℝ) ^ j := by positivity
      norm_num
      nlinarith
    change r / 256 ≤ _
    linarith
  · obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ (n : ℝ) by linarith)
      (show (1 : ℝ) < 16 by norm_num)
    have hrlower : (2 : ℝ) ^ j ≤ r := by
      apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) hr0
      rw [two_pow_four, hr4]
      exact hjlo
    have hrupper : r ≤ (2 : ℝ) ^ (j + 1) := by
      apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity)
      rw [hr4, two_pow_four]
      exact hjhi.le
    have hcube : r ^ 3 ≤ (8 : ℝ) ^ (j + 1) := by
      have h := pow_le_pow_left₀ hr0 hrupper 3
      rwa [two_pow_three] at h
    have htime_root : (n : ℝ) * (1 / 8 : ℝ) ^ (j + 1) ≤ r := by
      have hm := mul_le_mul_of_nonneg_left hcube hr0
      have hnle : (n : ℝ) ≤ r * (8 : ℝ) ^ (j + 1) := by
        nlinarith [hr4]
      rw [one_div_pow, mul_one_div]
      exact (div_le_iff₀ (by positivity)).2 hnle
    have hsum := geometric_cutoff_bound g (n : ℝ) hn0 hg hcap htime n (j + 1)
    have hpow : (2 : ℝ) ^ (j + 1) / 32 ≤ r / 16 := by
      rw [pow_succ]
      linarith
    change _ ≤ r / 8
    have htail : (n : ℝ) * (1 / 8 : ℝ) ^ (j + 1) / 28 ≤ r / 28 :=
      div_le_div_of_nonneg_right htime_root (by norm_num)
    linarith

lemma branch_weight_mul_four (j : ℕ) :
    (1 / 2 : ℝ) ^ (j + 1) * (4 : ℝ) ^ j = (2 : ℝ) ^ j / 2 := by
  calc
    _ = ((1 / 2 : ℝ) ^ j * (4 : ℝ) ^ j) / 2 := by rw [pow_succ]; ring
    _ = (2 : ℝ) ^ j / 2 := by rw [← mul_pow]; norm_num

lemma branch_weight_div_four (j : ℕ) :
    (1 / 2 : ℝ) ^ (j + 1) / (16 * (4 : ℝ) ^ j) = (1 / 8 : ℝ) ^ j / 32 := by
  calc
    _ = ((1 / 2 : ℝ) ^ j / (4 : ℝ) ^ j) / 32 := by rw [pow_succ]; ring
    _ = (1 / 8 : ℝ) ^ j / 32 := by rw [← div_pow]; norm_num

theorem weighted_aggregate_bounds (d : ℕ → ℕ → ℝ)
    (hzero : ∀ j t, 0 ≤ d j t)
    (hupper : ∀ j t, d j t ≤ ((min t (16 ^ j) : ℕ) : ℝ) / (16 * (4 : ℝ) ^ j))
    (hlower : ∀ j t, 16 ^ j ≤ t → (4 : ℝ) ^ j / 32 ≤ d j t)
    (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ (1 / 4 : ℝ) / 256 ≤
      (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1) * d j (n - (j + 1))) ∧
    (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1) * d j (n - (j + 1))) ≤
      (n : ℝ) ^ (1 / 4 : ℝ) / 8 := by
  apply aggregate_bounds (fun j => (1 / 2 : ℝ) ^ (j + 1) * d j (n - (j + 1))) n hn
  · intro j
    exact mul_nonneg (by positivity) (hzero j _)
  · intro j
    have hmin : ((min (n - (j + 1)) (16 ^ j) : ℕ) : ℝ) ≤ (16 : ℝ) ^ j := by
      exact_mod_cast min_le_right (n - (j + 1)) (16 ^ j)
    have hd : d j (n - (j + 1)) ≤ (4 : ℝ) ^ j / 16 := by
      calc
        _ ≤ ((min (n - (j + 1)) (16 ^ j) : ℕ) : ℝ) / (16 * (4 : ℝ) ^ j) := hupper j _
        _ ≤ (16 : ℝ) ^ j / (16 * (4 : ℝ) ^ j) :=
          div_le_div_of_nonneg_right hmin (by positivity)
        _ = ((16 : ℝ) ^ j / (4 : ℝ) ^ j) / 16 := by ring
        _ = (4 : ℝ) ^ j / 16 := by rw [← div_pow]; norm_num
    calc
      _ ≤ (1 / 2 : ℝ) ^ (j + 1) * ((4 : ℝ) ^ j / 16) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ = (2 : ℝ) ^ j / 32 := by rw [← mul_div_assoc, branch_weight_mul_four]; ring
  · intro j
    have hmin : ((min (n - (j + 1)) (16 ^ j) : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show min (n - (j + 1)) (16 ^ j) ≤ n by omega)
    have hd : d j (n - (j + 1)) ≤ (n : ℝ) / (16 * (4 : ℝ) ^ j) :=
      (hupper j _).trans (div_le_div_of_nonneg_right hmin (by positivity))
    calc
      _ ≤ (1 / 2 : ℝ) ^ (j + 1) * ((n : ℝ) / (16 * (4 : ℝ) ^ j)) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ = (n : ℝ) * ((1 / 2 : ℝ) ^ (j + 1) / (16 * (4 : ℝ) ^ j)) := by ring
      _ = (n : ℝ) * (1 / 8 : ℝ) ^ j / 32 := by rw [branch_weight_div_four]; ring
  · intro j hj
    have ht : 16 ^ j ≤ n - (j + 1) := by omega
    calc
      (2 : ℝ) ^ j / 64 = (1 / 2 : ℝ) ^ (j + 1) * ((4 : ℝ) ^ j / 32) := by
        rw [← mul_div_assoc, branch_weight_mul_four]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlower j _ ht) (by positivity)

/-! Part 2f. Exact aggregation of the branch losses. -/

lemma triangular_convolution (w : ℕ → ℝ) (e : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.range n, ∑ j ∈ Finset.range t,
      w j * e j (t - (j + 1))) =
    ∑ j ∈ Finset.range n, w j *
      (∑ t ∈ Finset.range (n - (j + 1)), e j t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [Nat.sub_self, Finset.sum_range_zero, mul_zero, add_zero]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have he : n + 1 - (j + 1) = (n - (j + 1)) + 1 := by omega
    rw [he, Finset.sum_range_succ, mul_add]

lemma stepLoss_decomposition (M : Background) (n : ℕ) :
    stepLoss source (xiMinus M) n - stepLoss source (xiPlus M) n =
      ∑ j ∈ Finset.range n, (1/2 : ℝ)^(j+1) *
        (stepLoss (localModel j)
          (contaminated (scale j) (scale_pos j) (branchBackground M j) eta false)
          (n-(j+1)) -
         stepLoss (localModel j)
          (contaminated (scale j) (scale_pos j) (branchBackground M j) eta true)
          (n-(j+1))) := by
  calc
    _ = sourceExpectation n (stateGap M) := by
      simp only [xiMinus, xiPlus, stepLoss, sourceExpectation, stateGap, risk,
        predict_xi, source, mul_sub, Finset.sum_sub_distrib]
    _ = _ := by
      rw [expectation_decomp, stateGap_trunk, mul_zero, zero_add]
      apply Finset.sum_congr rfl
      intro j _
      simp only [branchExpectation, stateGap_branch, stepLoss,
        mul_sub, Finset.sum_sub_distrib]

theorem loss_decomposition (M : Background) (n : ℕ) :
    loss source (xiMinus M) n - loss source (xiPlus M) n =
      ∑ j ∈ Finset.range n, (1/2 : ℝ)^(j+1) *
        branchGap (scale j) (scale_pos j) (branchBackground M j) eta (n-(j+1)) := by
  simp only [loss]
  rw [← Finset.sum_sub_distrib]
  simp_rw [stepLoss_decomposition]
  rw [triangular_convolution (fun j => (1/2 : ℝ)^(j+1))
    (fun j t =>
      stepLoss (localModel j)
        (contaminated (scale j) (scale_pos j) (branchBackground M j) eta false) t -
      stepLoss (localModel j)
        (contaminated (scale j) (scale_pos j) (branchBackground M j) eta true) t) n]
  apply Finset.sum_congr rfl
  intro j _
  rw [branchGap_sum]
  rfl

theorem theorem4 (M : Background) (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ)^(1/4 : ℝ)/256 ≤
      loss source (xiMinus M) n - loss source (xiPlus M) n ∧
    loss source (xiMinus M) n - loss source (xiPlus M) n ≤
      (n : ℝ)^(1/4 : ℝ)/8 := by
  rw [loss_decomposition]
  apply weighted_aggregate_bounds _ ?_ ?_ ?_ n hn
  · intro j t
    exact branchGap_nonneg (scale j) (scale_pos j) (branchBackground M j)
      eta eta_nonneg le_rfl t
  · intro j t
    have h := branchGap_upper (scale j) (scale_pos j) (branchBackground M j) eta t
    rw [scale_squared] at h
    simpa only [scale, Nat.cast_pow, Nat.cast_ofNat] using h
  · intro j t ht
    have h : (scale j)^2 ≤ t := by simpa only [scale_squared] using ht
    simpa only [scale, Nat.cast_pow, Nat.cast_ofNat] using
      branchGap_lower (scale j) (scale_pos j) (branchBackground M j)
        eta eta_nonneg le_rfl t h

/-- The complete statement from Part 1. -/
theorem theorem4_statement (M : Background) : Theorem4Statement M :=
  fun n hn => theorem4 M n hn

end RobustExperiment.Theorem4
