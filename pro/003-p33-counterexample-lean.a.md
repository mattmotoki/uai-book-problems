**The formalization compiles successfully with Lean `v4.35.0` and Mathlib tag `v4.35.0`.** It proves the exact rational models, both prescribed priors, the harmonic lower bound, and unboundedness above. The axiom audit reports only Lean’s standard `propext`, `Classical.choice`, and `Quot.sound`; there are no new axioms or prohibited proof constructs.

File: P33Counterexample.lean[P33Counterexample.lean](sandbox:/workspace/scratch/3515466b00f8/P33Counterexample.lean)

Two design choices keep the statement readable:

- `History n` stores a history as nested chronological extensions `(x, b)`. This represents the same histories as lists of length `n`, while making finite sums and induction straightforward.
- Part 1 ends with the main theorem statement. Part 2 is its proof, with auxiliary definitions introduced by `let` and helper lemmas proved with `have`. This preserves the requested statement-first ordering without forward declarations.

```lean
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

open scoped BigOperators

namespace MixtureCounterexample

/-! Part 1: definitions and the statement. -/

/-- A length-indexed history, extended chronologically by `(x, b)`. -/
abbrev History : ℕ → Type
  | 0 => Unit
  | n + 1 => History n × Bool

instance historyFintype : (n : ℕ) → Fintype (History n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd (History n) Bool (historyFintype n) inferInstance

/-- The probability of the next bit being `true`, after any finite history. -/
structure Model where
  cond : (n : ℕ) → History n → ℝ
  nonneg : ∀ n x, 0 ≤ cond n x
  le_one : ∀ n x, cond n x ≤ 1

/-- Probability of a whole prefix, obtained by multiplying conditionals. -/
def prob (p : Model) : (n : ℕ) → History n → ℝ
  | 0, _ => 1
  | n + 1, (x, b) => prob p n x * (if b then p.cond n x else 1 - p.cond n x)

/-- Strictly positive normalized weights on a finite model class. -/
structure Prior (ι : Type) [Fintype ι] where
  weight : ι → ℝ
  positive : ∀ i, 0 < weight i
  total : ∑ i, weight i = 1

noncomputable def mixCond {ι : Type} [Fintype ι] (m : ι → Model) (w : Prior ι)
    (n : ℕ) (x : History n) : ℝ :=
  (∑ i, w.weight i * prob (m i) n x * (m i).cond n x) /
    (∑ i, w.weight i * prob (m i) n x)

/-- A Bayes decision for binary 0-1 loss; ties are resolved as `false`. -/
noncomputable def predict {ι : Type} [Fintype ι] (m : ι → Model) (w : Prior ι)
    (n : ℕ) (x : History n) : Bool :=
  if (1 : ℝ) / 2 < mixCond m w n x then true else false

/-- Expected one-step 0-1 loss under the true model. -/
def risk (μ : Model) (n : ℕ) (x : History n) (prediction : Bool) : ℝ :=
  if prediction then 1 - μ.cond n x else μ.cond n x

noncomputable def loss {ι : Type} [Fintype ι] (μ : Model) (m : ι → Model)
    (w : Prior ι) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, ∑ x : History t, prob μ t x * risk μ t x (predict m w t x)

/-- Executable rational conditionals: `true` indexes μ, `false` indexes ν. -/
def rationalCond (i : Bool) (n : ℕ) (_x : History n) : ℚ :=
  1 / 2 + (if i then 1 else -1) / (32 * ((n : ℚ) + 1))

/-- The prescribed computable models and priors have the stated rate,
    and their expected cumulative loss difference is not bounded above. -/
theorem counterexample :
  ∃ (m : Bool → Model) (wMinus wPlus : Prior Bool),
    (∀ i n x, (m i).cond n x = (rationalCond i n x : ℝ)) ∧
    (∀ i, wMinus.weight i = if i then 1 / 4 else 3 / 4) ∧
    (∀ i, wPlus.weight i = if i then 3 / 4 else 1 / 4) ∧
    (∀ n, (1 : ℝ) / 32 * (∑ t ∈ Finset.range n, 1 / ((t : ℝ) + 1)) ≤
      loss (m true) m wMinus n - loss (m true) m wPlus n) ∧
    ¬ BddAbove (Set.range (fun n => loss (m true) m wMinus n - loss (m true) m wPlus n)) := by

  /- Part 2: proofs. Auxiliary definitions and lemmas are local to this proof. -/
  have history_sum_succ (n : ℕ) (f : History (n + 1) → ℝ) :
      (∑ x : History (n + 1), f x) = ∑ x : History n, (f (x, false) + f (x, true)) := by
    change (∑ x : History n × Bool, f x) = _
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    congr 1
    funext x
    ring

  have prob_nonneg (p : Model) (n : ℕ) (x : History n) : 0 ≤ prob p n x := by
    induction n with
    | zero => simp [prob]
    | succ n ih =>
      rcases x with ⟨x, b⟩
      cases b <;> simp only [prob, Bool.false_eq_true, ↓reduceIte]
      · exact mul_nonneg (ih x) (sub_nonneg.mpr (p.le_one n x))
      · exact mul_nonneg (ih x) (p.nonneg n x)

  have prob_total (p : Model) (n : ℕ) : (∑ x : History n, prob p n x) = 1 := by
    induction n with
    | zero =>
      change (∑ _x : Unit, (1 : ℝ)) = 1
      simp
    | succ n ih =>
      rw [history_sum_succ]
      simp only [prob, Bool.false_eq_true, ↓reduceIte]
      convert ih using 1
      apply Finset.sum_congr rfl
      intro x _
      ring

  have mixCond_nonneg {ι : Type} [Fintype ι] (m : ι → Model) (w : Prior ι)
      (n : ℕ) (x : History n)
      (hden : 0 < ∑ i, w.weight i * prob (m i) n x) :
      0 ≤ mixCond m w n x := by
    apply div_nonneg _ hden.le
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (w.positive i).le (prob_nonneg (m i) n x)) ((m i).nonneg n x))

  have mixCond_le_one {ι : Type} [Fintype ι] (m : ι → Model) (w : Prior ι)
      (n : ℕ) (x : History n)
      (hden : 0 < ∑ i, w.weight i * prob (m i) n x) :
      mixCond m w n x ≤ 1 := by
    unfold mixCond
    apply (div_le_one hden).mpr
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_of_le_one_right
      (mul_nonneg (w.positive i).le (prob_nonneg (m i) n x)) ((m i).le_one n x)

  /- The defined predictor minimizes its mixture's conditional binary 0-1 risk. -/
  have predict_optimal {ι : Type} [Fintype ι] (m : ι → Model) (w : Prior ι)
      (n : ℕ) (x : History n) (b : Bool) :
      (if predict m w n x then 1 - mixCond m w n x else mixCond m w n x) ≤
        (if b then 1 - mixCond m w n x else mixCond m w n x) := by
    by_cases h : (1 : ℝ) / 2 < mixCond m w n x
    · simp only [predict, ite_eq_left h]
      cases b <;> norm_num
      linarith
    · simp only [predict, ite_eq_right h]
      cases b <;> norm_num
      linarith

  let delta (n : ℕ) : ℝ := 1 / (32 * ((n : ℝ) + 1))
  let factor (n : ℕ) : ℝ := 1 + 4 / (256 * ((n : ℝ) + 1) ^ 2 - 1)
  let upper (n : ℕ) : ℝ := 9 / 8 - 1 / (8 * ((n : ℝ) + 1))

  have delta_pos (n : ℕ) : 0 < delta n := by
    unfold delta
    positivity

  have delta_le (n : ℕ) : delta n ≤ 1 / 32 := by
    unfold delta
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * ((n : ℝ) + 1))).2
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

  have delta_lt_half (n : ℕ) : delta n < 1 / 2 := by
    have h := delta_le n
    linarith

  have factor_den_pos (n : ℕ) : 0 < 256 * ((n : ℝ) + 1) ^ 2 - 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [sq_nonneg (n : ℝ)]

  have factor_nonneg (n : ℕ) : 0 ≤ factor n := by
    unfold factor
    have := factor_den_pos n
    positivity

  have moment_factor (n : ℕ) :
      (1 / 2 - delta n) ^ 2 / (1 / 2 + delta n) +
        (1 / 2 + delta n) ^ 2 / (1 / 2 - delta n) = factor n := by
    have hdp := delta_pos n
    have hdh := delta_lt_half n
    have hp : (1 / 2 + delta n : ℝ) ≠ 0 := by linarith
    have hq : (1 / 2 - delta n : ℝ) ≠ 0 := by linarith
    have hk : (n : ℝ) + 1 ≠ 0 := by positivity
    have hd := ne_of_gt (factor_den_pos n)
    unfold delta at hp hq ⊢
    unfold factor
    field_simp (disch := positivity)
    ring_nf
    field_simp (disch := positivity)
    ring

  have upper_step_real (k : ℝ) (hk : 1 ≤ k) :
      (9 / 8 - 1 / (8 * k)) * (1 + 4 / (256 * k ^ 2 - 1)) ≤
        9 / 8 - 1 / (8 * (k + 1)) := by
    have hk0 : 0 < k := by linarith
    have hk1 : 0 < k + 1 := by linarith
    have hd : 0 < 256 * k ^ 2 - 1 := by nlinarith [sq_nonneg (k - 1)]
    have hu : (9 / 8 - 1 / (8 * k)) = (9 * k - 1) / (8 * k) := by
      field_simp
    have hf : (1 + 4 / (256 * k ^ 2 - 1)) =
        (256 * k ^ 2 + 3) / (256 * k ^ 2 - 1) := by
      field_simp
      ring
    have hv : (9 / 8 - 1 / (8 * (k + 1))) =
        (9 * (k + 1) - 1) / (8 * (k + 1)) := by
      field_simp
    rw [hu, hf, hv, div_mul_div_comm]
    apply (div_le_div_iff₀ (mul_pos (by positivity) hd) (by positivity)).2
    nlinarith [sq_nonneg (k - 1)]

  have upper_step (n : ℕ) : upper n * factor n ≤ upper (n + 1) := by
    unfold upper factor
    push_cast
    convert upper_step_real ((n : ℝ) + 1) (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) using 1

  have upper_zero : upper 0 = 1 := by norm_num [upper]

  have upper_le (n : ℕ) : upper n ≤ 9 / 8 := by
    unfold upper
    have h : 0 ≤ 1 / (8 * ((n : ℝ) + 1)) := by positivity
    linarith

  let models (i : Bool) : Model := {
    cond n _ := if i then 1 / 2 + delta n else 1 / 2 - delta n
    nonneg n _ := by
      have h₁ := delta_pos n
      have h₂ := delta_lt_half n
      cases i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
    le_one n _ := by
      have h₁ := delta_pos n
      have h₂ := delta_lt_half n
      cases i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  }

  have models_strict (i : Bool) (n : ℕ) (x : History n) :
      0 < (models i).cond n x ∧ (models i).cond n x < 1 := by
    have h₁ := delta_pos n
    have h₂ := delta_lt_half n
    cases i <;> simp only [models, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith

  have prob_pos (p : Model) (hp : ∀ n x, 0 < p.cond n x ∧ p.cond n x < 1)
      (n : ℕ) (x : History n) : 0 < prob p n x := by
    induction n with
    | zero => simp [prob]
    | succ n ih =>
      rcases x with ⟨x, b⟩
      cases b <;> simp only [prob, Bool.false_eq_true, ↓reduceIte]
      · exact mul_pos (ih x) (sub_pos.mpr (hp n x).2)
      · exact mul_pos (ih x) (hp n x).1

  have models_prob_pos (i : Bool) (n : ℕ) (x : History n) :
      0 < prob (models i) n x := prob_pos (models i) (models_strict i) n x

  let minusPrior : Prior Bool := {
    weight i := if i then 1 / 4 else 3 / 4
    positive i := by cases i <;> norm_num
    total := by norm_num [Fintype.sum_bool]
  }

  let plusPrior : Prior Bool := {
    weight i := if i then 3 / 4 else 1 / 4
    positive i := by cases i <;> norm_num
    total := by norm_num [Fintype.sum_bool]
  }

  have models_rational (i : Bool) (n : ℕ) (x : History n) :
      (models i).cond n x = (rationalCond i n x : ℝ) := by
    cases i <;> simp [models, rationalCond, delta, sub_eq_add_neg]
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

  let moment (p q : Model) (n : ℕ) : ℝ :=
    ∑ x : History n, (prob q n x) ^ 2 / prob p n x

  let variance (p q : Model) (n : ℕ) : ℝ :=
    ∑ x : History n, (prob q n x - prob p n x) ^ 2 / prob p n x

  have moment_zero (p q : Model) : moment p q 0 = 1 := by
    change (∑ _x : Unit, (1 : ℝ) ^ 2 / 1) = 1
    simp

  have moment_succ (p q : Model) (n : ℕ) (u v : ℝ)
      (hp : ∀ x, p.cond n x = u) (hq : ∀ x, q.cond n x = v) :
      moment p q (n + 1) = moment p q n * (v ^ 2 / u + (1 - v) ^ 2 / (1 - u)) := by
    unfold moment
    rw [history_sum_succ, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    simp only [prob, Bool.false_eq_true, ↓reduceIte, hp, hq, mul_pow,
      mul_div_mul_comm]
    ring

  have variance_eq (p q : Model) (n : ℕ) (hp : ∀ x, 0 < prob p n x) :
      variance p q n = moment p q n - 1 := by
    have hpoint (x : History n) :
        (prob q n x - prob p n x) ^ 2 / prob p n x =
          (prob q n x) ^ 2 / prob p n x - 2 * prob q n x + prob p n x := by
      field_simp [ne_of_gt (hp x)]
      ring
    unfold variance
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      prob_total]
    unfold moment
    ring

  have moment_le_upper (p q : Model)
      (hp : ∀ n x, p.cond n x = 1 / 2 + delta n)
      (hq : ∀ n x, q.cond n x = 1 / 2 - delta n) (n : ℕ) :
      moment p q n ≤ upper n := by
    induction n with
    | zero => rw [moment_zero, upper_zero]
    | succ n ih =>
      rw [moment_succ p q n _ _ (hp n) (hq n)]
      have hf :
          (1 / 2 - delta n) ^ 2 / (1 / 2 + delta n) +
            (1 - (1 / 2 - delta n)) ^ 2 /
              (1 - (1 / 2 + delta n)) = factor n := by
        convert moment_factor n using 1
        congr 1
        ring
      rw [hf]
      exact (mul_le_mul_of_nonneg_right ih (factor_nonneg n)).trans
        (upper_step n)

  have variance_le_eighth (p q : Model)
      (hp : ∀ n x, p.cond n x = 1 / 2 + delta n)
      (hq : ∀ n x, q.cond n x = 1 / 2 - delta n)
      (n : ℕ) (hpos : ∀ x, 0 < prob p n x) : variance p q n ≤ 1 / 8 := by
    rw [variance_eq p q n hpos]
    have h := (moment_le_upper p q hp hq n).trans (upper_le n)
    linarith

  have pointwise_loss_gap (a b d : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
      2 * d * (a - 4 * ((b - a) ^ 2 / a)) ≤
        a * ((if 3 * b < a then 1 / 2 - d else 1 / 2 + d) -
          (if b < 3 * a then 1 / 2 - d else 1 / 2 + d)) := by
    have hvar : 0 ≤ (b - a) ^ 2 / a := div_nonneg (sq_nonneg _) ha.le
    by_cases hm : 3 * b < a
    · have hp : b < 3 * a := by linarith
      simp only [hm, hp, ite_true, sub_self, mul_zero]
      have hfar : a ≤ 4 * ((b - a) ^ 2 / a) := by
        rw [← mul_div_assoc, le_div_iff₀ ha]
        have hprod : 0 ≤ (a - 2 * b) * (3 * a - 2 * b) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    · by_cases hp : b < 3 * a
      · simp only [hm, hp, ite_false, ite_true]
        nlinarith [mul_nonneg hd.le hvar]
      · simp only [hm, hp, ite_false, sub_self, mul_zero]
        have hfar : a ≤ 4 * ((b - a) ^ 2 / a) := by
          rw [← mul_div_assoc, le_div_iff₀ ha]
          have hprod : 0 ≤ (2 * b - a) * (2 * b - 3 * a) :=
            mul_nonneg (by linarith) (by linarith)
          nlinarith
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

  have weighted_pointwise_gap
      (m : Bool → Model) (wMinus wPlus : Prior Bool)
      (hMinus : ∀ i, wMinus.weight i = if i then 1 / 4 else 3 / 4)
      (hPlus : ∀ i, wPlus.weight i = if i then 3 / 4 else 1 / 4)
      (n : ℕ) (x : History n) (d : ℝ)
      (hmu : (m true).cond n x = 1 / 2 + d)
      (hnu : (m false).cond n x = 1 / 2 - d)
      (ha : 0 < prob (m true) n x) (hb : 0 < prob (m false) n x) (hd : 0 < d) :
      2 * d * (prob (m true) n x -
        4 * ((prob (m false) n x - prob (m true) n x) ^ 2 / prob (m true) n x)) ≤
      prob (m true) n x *
        (risk (m true) n x (predict m wMinus n x) -
          risk (m true) n x (predict m wPlus n x)) := by
    have hm : (1 / 2 < mixCond m wMinus n x) ↔
        3 * prob (m false) n x < prob (m true) n x := by
      simp only [mixCond, Fintype.sum_bool, hMinus, hmu, hnu, Bool.false_eq_true, ↓reduceIte]
      rw [lt_div_iff₀ (by positivity)]
      constructor <;> intro h <;> nlinarith
    have hp : (1 / 2 < mixCond m wPlus n x) ↔
        prob (m false) n x < 3 * prob (m true) n x := by
      simp only [mixCond, Fintype.sum_bool, hPlus, hmu, hnu, Bool.false_eq_true, ↓reduceIte]
      rw [lt_div_iff₀ (by positivity)]
      constructor <;> intro h <;> nlinarith
    have hc : 1 - (1 / 2 + d) = 1 / 2 - d := by ring
    simpa only [risk, predict, Bool.ite_false_right_eq_true, and_true, hmu, hm, hp, hc] using
      pointwise_loss_gap (prob (m true) n x) (prob (m false) n x) d ha hb hd

  have harmonic_unbounded (f : ℕ → ℝ)
      (hf : ∀ n, (1 / 32 : ℝ) * (∑ t ∈ Finset.range n, 1 / ((t : ℝ) + 1)) ≤ f n) :
      ∀ B : ℝ, ∃ n, B < f n := by
    intro B
    have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
    obtain ⟨n, hn⟩ := (Filter.eventually_atTop.1 (h.eventually (Filter.eventually_gt_atTop (32 * B))))
    refine ⟨n, lt_of_lt_of_le ?_ (hf n)⟩
    have hb := hn n le_rfl
    linarith

  have harmonic_not_bddAbove (f : ℕ → ℝ)
      (hf : ∀ n, (1 / 32 : ℝ) * (∑ t ∈ Finset.range n, 1 / ((t : ℝ) + 1)) ≤ f n) :
      ¬ BddAbove (Set.range f) := by
    rintro ⟨B, hB⟩
    obtain ⟨n, hn⟩ := harmonic_unbounded f hf B
    exact (not_lt_of_ge (hB (Set.mem_range_self n))) hn

  have step_gap (n : ℕ) :
      delta n ≤
        (∑ x : History n, prob (models true) n x *
          risk (models true) n x (predict models minusPrior n x)) -
        (∑ x : History n, prob (models true) n x *
          risk (models true) n x (predict models plusPrior n x)) := by
    have hv := variance_le_eighth (models true) (models false)
      (fun _ _ => rfl) (fun _ _ => rfl) n (models_prob_pos true n)
    calc
      delta n ≤ 2 * delta n * (1 - 4 * variance (models true) (models false) n) := by
        nlinarith [mul_nonneg (delta_pos n).le (sub_nonneg.mpr hv)]
      _ = ∑ x : History n, 2 * delta n * (prob (models true) n x -
          4 * ((prob (models false) n x - prob (models true) n x) ^ 2 /
            prob (models true) n x)) := by
        simp only [← Finset.mul_sum, Finset.sum_sub_distrib, prob_total, variance]
      _ ≤ ∑ x : History n, prob (models true) n x *
          (risk (models true) n x (predict models minusPrior n x) -
            risk (models true) n x (predict models plusPrior n x)) := by
        apply Finset.sum_le_sum
        intro x _
        exact weighted_pointwise_gap models minusPrior plusPrior (fun _ => rfl)
          (fun _ => rfl) n x (delta n) rfl rfl
          (models_prob_pos true n x) (models_prob_pos false n x) (delta_pos n)
      _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib]

  have total_gap (n : ℕ) :
      (1 : ℝ) / 32 * (∑ t ∈ Finset.range n, 1 / ((t : ℝ) + 1)) ≤
        loss (models true) models minusPrior n - loss (models true) models plusPrior n := by
    calc
      (1 : ℝ) / 32 * (∑ t ∈ Finset.range n, 1 / ((t : ℝ) + 1)) =
          ∑ t ∈ Finset.range n, delta t := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        simp [delta, div_eq_mul_inv, mul_inv_rev, mul_comm]
      _ ≤ ∑ t ∈ Finset.range n,
          ((∑ x : History t, prob (models true) t x *
            risk (models true) t x (predict models minusPrior t x)) -
          (∑ x : History t, prob (models true) t x *
            risk (models true) t x (predict models plusPrior t x))) :=
        Finset.sum_le_sum (fun t _ => step_gap t)
      _ = _ := by simp only [loss, Finset.sum_sub_distrib]

  refine ⟨models, minusPrior, plusPrior, models_rational,
    (fun _ => rfl), (fun _ => rfl), total_gap, ?_⟩
  exact harmonic_not_bddAbove _ total_gap

end MixtureCounterexample
```

## Map to the book’s notation

In this table, a Lean history of length `n` is the history before book time \(t=n+1\).

| Part 1 definition | Meaning in the book’s notation |
|---|---|
| `History n` | A binary prefix \(x_{1:n}=x_{<n+1}\). The pair `(x, b)` appends the newest observation. |
| `historyFintype` | Enumeration of every binary history of the given length, used in finite expectations. |
| `Model`, `Model.cond n x` | An environment \(\rho\), with conditional probability \(\rho(1\mid x)\). Its probability of `false` is \(1-\rho(1\mid x)\). |
| `prob p n x` | The prefix probability \(\rho(x_{1:n})\), obtained by the chain rule. |
| `Prior`, `Prior.weight i` | The prior weights \(w_{\rho_i}>0\), with \(\sum_i w_{\rho_i}=1\). |
| `mixCond m w n x` | \(\xi(1\mid x)\), where \(\xi(x)=\sum_i w_i\rho_i(x)\). |
| `predict m w n x` | The Bayes action \(y^\xi_{n+1}\) for binary 0–1 loss. |
| `risk μ n x b` | \(\sum_{x_{n+1}}\mu(x_{n+1}\mid x)\,\mathbf 1[x_{n+1}\ne b]\). |
| `loss μ m w n` | \(L^\xi_n\), the cumulative expected loss under \(\mu\) over the first \(n\) predictions. |
| `rationalCond true n x` | \(\mu(1\mid x)=\frac12+\frac1{32(n+1)}\). |
| `rationalCond false n x` | \(\nu(1\mid x)=\frac12-\frac1{32(n+1)}\). |
| `counterexample` | Existence of the prescribed class and priors with \(L^{\xi_-}_n-L^{\xi_+}_n\ge H_n/32\), and no finite upper bound on these differences. |

The member serving as the true environment is explicitly `m true`, so the requested index \(j\) is `true`.

## Short informal proof

Write
\[
d_n=\frac1{32(n+1)},\qquad
R_n(x)=\frac{\nu(x)}{\mu(x)},\qquad
S_n=\mathbb E_\mu[R_n^2].
\]

The proof uses an elementary rational bound on the second moment. Independence and the two Bernoulli conditionals give
\[
S_0=1,\qquad
S_{n+1}
=
S_n\left(1+\frac4{256(n+1)^2-1}\right).
\]
Define
\[
U_n=\frac98-\frac1{8(n+1)}.
\]
The helper `upper_step_real` proves
\[
U_n\left(1+\frac4{256(n+1)^2-1}\right)\le U_{n+1}.
\]
Consequently, induction gives \(S_n\le U_n\le9/8\). Since both prefix distributions sum to one,
\[
\mathbb E_\mu[(R_n-1)^2]=S_n-1\le\frac18.
\]

At a fixed history, put \(a=\mu(x)>0\) and \(b=\nu(x)>0\). The two decisions satisfy
\[
\xi_-\text{ predicts }1\iff 3b<a,
\qquad
\xi_+\text{ predicts }1\iff b<3a.
\]
The pointwise arithmetic lemma proves
\[
a\bigl(\operatorname{risk}_--\operatorname{risk}_+\bigr)
\ge
2d_n\left(a-4\frac{(b-a)^2}{a}\right).
\]
This follows by considering the two decision thresholds: when the predictors disagree, their conditional loss difference is \(2d_n\); when they agree, the quadratic expression on the right is nonpositive.

Summing over histories therefore gives
\[
\mathbb E_\mu[\operatorname{risk}_--\operatorname{risk}_+]
\ge
2d_n\left(1-4\mathbb E_\mu[(R_n-1)^2]\right)
\ge d_n.
\]
Summing over time proves
\[
L^{\xi_-}_n-L^{\xi_+}_n
\ge
\sum_{t<n}d_t
=
\frac1{32}\sum_{t<n}\frac1{t+1}.
\]
The harmonic divergence theorem then supplies unboundedness above.

This proof establishes the requested construction and rate using the rational estimate \(S_n\le9/8\). It does not need the sharper exponential estimate or an explicitly constructed Chebyshev event from the proposed argument.

## Specializations and formalization choices

1. **Binary observations and actions; 0–1 loss.** The formalization specializes the general prediction setting to \(\{0,1\}\) and \(\ell(x,y)=\mathbf 1[x\ne y]\).

2. **A finite class containing exactly the prescribed two models.** General definitions support any finite index type. The theorem uses `Bool`, with `true` indexing \(\mu\) and `false` indexing \(\nu\). It does not formalize arbitrary countable classes.

3. **Proper probability models.** Each conditional assigns total probability one to the two possible next observations. There is no lost probability mass or termination outcome. The concrete models have full support.

4. **The priors are fixed explicitly.** The theorem requires exactly \((w_\mu,w_\nu)=(1/4,3/4)\) and \((w'_\mu,w'_\nu)=(3/4,1/4)\). Strict positivity and normalization are fields of `Prior`, so they are obligations that the witnesses satisfy.

5. **Histories use a length-indexed representation.** `History n` represents the same mathematical objects as binary lists of length `n`. Lean time `t` corresponds to book time \(t+1\); horizon `n` still means the first \(n\) predictions.

6. **Ties predict `false`.** The threshold is strictly greater than \(1/2\). The proof includes a general lemma showing that this rule minimizes the mixture’s conditional 0–1 risk.

7. **Zero denominators are totalized by Lean’s real division.** For an arbitrary class, `mixCond` evaluates to zero if its denominator is zero. Both concrete prefix probabilities are proved strictly positive, so the counterexample never uses that convention.

8. **Computability is exhibited by an explicit algorithm.** `rationalCond` is a terminating executable definition using rational arithmetic. The theorem requires every model conditional to equal its real cast. No separate general Turing-machine `Computable` predicate is introduced.

9. **The probability argument uses finite marginals at every horizon.** The file proves normalization of the finite-prefix distributions and works directly with their finite expectations. It does not construct a measure on infinite sequences.

10. **The conclusion concerns finite-horizon differences.** It states `¬ BddAbove` for the sequence \(L^{\xi_-}_n-L^{\xi_+}_n\), together with the explicit lower bound for every \(n\). This gives the requested precise negation of a uniformly finite cumulative loss gap without forming the undefined subtraction of two individually infinite total losses.