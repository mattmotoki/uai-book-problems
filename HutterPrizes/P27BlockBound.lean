/-
Finite block lower bounds for sequential binary probability laws.
Target: Lean 4.35.0 and Mathlib v4.35.0.

The literal joint-mass lemma in the question is false. `BlockClaim` is
the conditional version used by the attached report;
`block_bound_of_joint` states the corresponding sufficient joint bounds.
`literal_block_claim_false` proves that the original claim is false.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open scoped BigOperators

noncomputable section
namespace P27

set_option maxHeartbeats 2000000

/-! ## Part 1: statement layer. -/

/-- A binary history of the indicated length. -/
abbrev History : ℕ → Type
  | 0 => Unit
  | n + 1 => History n × Bool

instance historyFintype : (n : ℕ) → Fintype (History n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd (History n) Bool (historyFintype n) inferInstance

/--
A sequential law. Only the finitely many levels under discussion are used.
At a null history, `cond` supplies an arbitrary number in `[0,1]`; for a
law initially given by joint masses, one may choose `1/2` there.
At nonnull histories, `bitProb_eq_ratio` below proves the usual quotient
formula. Every result holds for every choice of normalized null kernels.
-/
structure Model where
  cond : (n : ℕ) → History n → ℝ
  nonneg : ∀ n x, 0 ≤ cond n x
  le_one : ∀ n x, cond n x ≤ 1

def bitProb (p : Model) (n : ℕ) (x : History n) (b : Bool) : ℝ :=
  if b then p.cond n x else 1 - p.cond n x

def prob (p : Model) : (n : ℕ) → History n → ℝ
  | 0, _ => 1
  | n + 1, (x, b) => prob p n x * bitProb p n x b

def append {r : ℕ} (x : History r) : (n : ℕ) → History n → History (r + n)
  | 0, _ => x
  | n + 1, (y, b) => (append x n y, b)

/-- The conditional continuation law, including the chosen null kernels. -/
def tailModel (p : Model) (r : ℕ) (x : History r) : Model where
  cond n y := p.cond (r + n) (append x n y)
  nonneg n y := p.nonneg (r + n) (append x n y)
  le_one n y := p.le_one (r + n) (append x n y)

def localError (p q : Model) (n : ℕ) (x : History n) : ℝ :=
  ∑ b : Bool, |bitProb p n x b - bitProb q n x b|

def stepError (p q : Model) (n : ℕ) : ℝ :=
  ∑ x : History n, prob p n x * localError p q n x

/-- The expected L1 prediction error at time `t`; `A p q 0 = 0`. -/
def A (p q : Model) : ℕ → ℝ
  | 0 => 0
  | n + 1 => stepError p q n

/-- The sum over times `r + 1, ..., r + ℓ`. -/
def blockError (p q : Model) (r ℓ : ℕ) : ℝ :=
  ∑ k ∈ Finset.range ℓ, A p q (r + k + 1)

def l1 (p q : Model) (n : ℕ) : ℝ :=
  ∑ x : History n, |prob p n x - prob q n x|

/-- The finite hybrid inequality, with expectations under `p`. -/
def HybridClaim : Prop :=
  ∀ (p q : Model) (n : ℕ),
    l1 p q n ≤ ∑ k ∈ Finset.range n, stepError p q k

/--
The corrected conditional block lemma. Its lower bound is `β / 2`.
The report uses `β = a * w_n / 2`.
-/
def BlockClaim : Prop :=
  ∀ (μ Q : Model) (r ℓ : ℕ) (β : ℝ) (G : Finset (History r)),
    0 < β → (1 / 2 : ℝ) ≤ ∑ x ∈ G, prob μ r x →
    (∀ x ∈ G, ∃ z : History ℓ,
      β ≤ prob (tailModel Q r x) ℓ z ∧
      prob (tailModel μ r x) ℓ z ≤ β / 2) →
    β / 2 ≤ blockError μ Q r ℓ

/-- The literal joint-mass statement in the question. -/
def LiteralBlockClaim : Prop :=
  ∀ (μ Q : Model) (r ℓ : ℕ) (β : ℝ) (G : Finset (History r)),
    0 < β → (1 / 2 : ℝ) ≤ ∑ x ∈ G, prob μ r x →
    (∀ x ∈ G, ∃ z : History ℓ,
      β * prob μ r x ≤ prob Q (r + ℓ) (append x ℓ z) ∧
      prob μ (r + ℓ) (append x ℓ z) ≤ (β / 2) * prob μ r x) →
    β / 2 ≤ blockError μ Q r ℓ

/-! ## Part 2: proofs. -/

lemma history_sum_succ (n : ℕ) (f : History (n + 1) → ℝ) :
    (∑ x : History (n + 1), f x) =
      ∑ x : History n, (f (x, false) + f (x, true)) := by
  change (∑ x : History n × Bool, f x) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  congr 1
  funext x
  ring

lemma bitProb_nonneg (p : Model) (n : ℕ) (x : History n) (b : Bool) :
    0 ≤ bitProb p n x b := by
  cases b
  · exact sub_nonneg.mpr (p.le_one n x)
  · exact p.nonneg n x

lemma bitProb_total (p : Model) (n : ℕ) (x : History n) :
    (∑ b : Bool, bitProb p n x b) = 1 := by
  simp [bitProb]

lemma prob_nonneg (p : Model) (n : ℕ) (x : History n) : 0 ≤ prob p n x := by
  induction n with
  | zero => simp [prob]
  | succ n ih => exact mul_nonneg (ih x.1) (bitProb_nonneg p n x.1 x.2)

lemma prob_total (p : Model) (n : ℕ) : (∑ x : History n, prob p n x) = 1 := by
  induction n with
  | zero => change (∑ _ : Unit, (1 : ℝ)) = 1; simp
  | succ n ih =>
    rw [history_sum_succ]
    simp only [prob, bitProb, Bool.false_eq_true, ↓reduceIte]
    convert ih using 1
    apply Finset.sum_congr rfl
    intro x _
    ring

lemma localError_nonneg (p q : Model) (n : ℕ) (x : History n) :
    0 ≤ localError p q n x :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma stepError_nonneg (p q : Model) (n : ℕ) : 0 ≤ stepError p q n :=
  Finset.sum_nonneg (fun x _ =>
    mul_nonneg (prob_nonneg p n x) (localError_nonneg p q n x))

lemma prob_append (p : Model) (r n : ℕ) (x : History r) (y : History n) :
    prob p (r + n) (append x n y) =
      prob p r x * prob (tailModel p r x) n y := by
  induction n with
  | zero => simp [append, prob]
  | succ n ih =>
    rcases y with ⟨y, b⟩
    change prob p (r + n) (append x n y) *
        bitProb p (r + n) (append x n y) b =
      prob p r x * (prob (tailModel p r x) n y *
        bitProb p (r + n) (append x n y) b)
    rw [ih, mul_assoc]

lemma sum_append (r n : ℕ) (f : History (r + n) → ℝ) :
    (∑ y : History (r + n), f y) =
      ∑ x : History r, ∑ z : History n, f (append x n z) := by
  induction n with
  | zero => simp [append]
  | succ n ih =>
    change (∑ y : History ((r + n) + 1), f y) =
      ∑ x : History r, ∑ z : History (n + 1), f (append x (n + 1) z)
    rw [history_sum_succ (r + n), ih]
    apply Finset.sum_congr rfl
    intro x _
    rw [history_sum_succ n]
    rfl

lemma expected_tail_step (μ Q : Model) (r k : ℕ) :
    (∑ x : History r, prob μ r x *
      stepError (tailModel μ r x) (tailModel Q r x) k) =
        stepError μ Q (r + k) := by
  unfold stepError
  rw [sum_append r k]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [prob_append]
  simp only [mul_assoc]
  rfl

lemma expected_tail_block (μ Q : Model) (r ℓ : ℕ) :
    (∑ x : History r, prob μ r x *
      (∑ k ∈ Finset.range ℓ,
        stepError (tailModel μ r x) (tailModel Q r x) k)) =
          blockError μ Q r ℓ := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [expected_tail_step, blockError, A]

/-- At a nonnull history, the supplied kernel is the usual conditional. -/
lemma bitProb_eq_ratio (p : Model) (n : ℕ) (x : History n) (b : Bool)
    (hx : prob p n x ≠ 0) :
    bitProb p n x b = prob p (n + 1) (x, b) / prob p n x := by
  rw [prob]
  field_simp

/-- At a nonnull prefix, the tail law is the usual conditional block law. -/
lemma tail_prob_eq_ratio (p : Model) (r n : ℕ) (x : History r) (y : History n)
    (hx : prob p r x ≠ 0) :
    prob (tailModel p r x) n y =
      prob p (r + n) (append x n y) / prob p r x := by
  rw [prob_append]
  field_simp

lemma product_difference_bound (a c u v : ℝ) (ha : 0 ≤ a) (hv : 0 ≤ v) :
    |a * u - c * v| ≤ a * |u - v| + |a - c| * v := by
  calc
    |a * u - c * v| = |a * (u - v) + (a - c) * v| := by
      congr 1
      ring
    _ ≤ |a * (u - v)| + |(a - c) * v| := abs_add_le _ _
    _ = a * |u - v| + |a - c| * v := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hv]

lemma l1_succ_le (p q : Model) (n : ℕ) :
    l1 p q (n + 1) ≤ stepError p q n + l1 p q n := by
  change (∑ z : History n × Bool,
    |prob p n z.1 * bitProb p n z.1 z.2 -
      prob q n z.1 * bitProb q n z.1 z.2|) ≤ _
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ x : History n, ∑ b : Bool,
        (prob p n x * |bitProb p n x b - bitProb q n x b| +
          |prob p n x - prob q n x| * bitProb q n x b) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro b _
      exact product_difference_bound _ _ _ _ (prob_nonneg p n x)
        (bitProb_nonneg q n x b)
    _ = stepError p q n + l1 p q n := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, bitProb_total, mul_one]
      rfl

/-- The finite hybrid inequality, weighted by the first law's prefixes. -/
theorem hybrid_inequality : HybridClaim := by
  intro p q n
  induction n with
  | zero => simp [l1, prob]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      l1 p q (n + 1) ≤ stepError p q n + l1 p q n := l1_succ_le p q n
      _ ≤ stepError p q n + ∑ k ∈ Finset.range n, stepError p q k :=
        add_le_add le_rfl ih
      _ = (∑ k ∈ Finset.range n, stepError p q k) + stepError p q n := add_comm _ _

/-- A single-coordinate probability gap contributes twice its size to L1. -/
lemma two_mul_gap_le_l1 (p q : Model) (n : ℕ) (z : History n) :
    2 * (prob q n z - prob p n z) ≤ l1 p q n := by
  classical
  have hs := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun x : History n =>
      |prob p n x - prob q n x| - (prob p n x - prob q n x))
    (fun x _ => sub_nonneg.mpr (le_abs_self _))
    (Finset.mem_univ z)
  simp only [Finset.sum_sub_distrib, prob_total, sub_self, sub_zero] at hs
  have hz := neg_le_abs (prob p n z - prob q n z)
  unfold l1
  linarith

/-- Equation (10): at least half the true mass has likelihood ratio at most two. -/
lemma good_prefix_mass (μ Q : Model) (r : ℕ) :
    (1 / 2 : ℝ) ≤
      ∑ x ∈ Finset.univ.filter (fun x : History r =>
        0 < prob μ r x ∧ prob Q r x ≤ 2 * prob μ r x), prob μ r x := by
  classical
  let G := Finset.univ.filter (fun x : History r =>
    0 < prob μ r x ∧ prob Q r x ≤ 2 * prob μ r x)
  have hx (x : History r) :
      prob μ r x ≤ (if x ∈ G then prob μ r x else 0) + prob Q r x / 2 := by
    by_cases hG : x ∈ G
    · simp only [hG, ↓reduceIte]
      have hQ := prob_nonneg Q r x
      linarith
    · simp only [hG, ↓reduceIte]
      by_cases hμ : 0 < prob μ r x
      · have hQ : ¬ prob Q r x ≤ 2 * prob μ r x := by
          intro hQ
          exact hG (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hμ, hQ⟩)
        linarith
      · have hQ := prob_nonneg Q r x
        linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hx x)
  have hg : (∑ x : History r, if x ∈ G then prob μ r x else 0) =
      ∑ x ∈ G, prob μ r x := by simp
  rw [prob_total, Finset.sum_add_distrib, hg, ← Finset.sum_div, prob_total] at hs
  change (1 / 2 : ℝ) ≤ ∑ x ∈ G, prob μ r x
  linarith

/-- The corrected block lemma, with the requested lower bound `β / 2`. -/
theorem block_bound : BlockClaim := by
  intro μ Q r ℓ β G hβ hG hsep
  have hpoint (x : History r) (hx : x ∈ G) :
      β ≤ ∑ k ∈ Finset.range ℓ,
        stepError (tailModel μ r x) (tailModel Q r x) k := by
    obtain ⟨z, hQ, hμ⟩ := hsep x hx
    have hd := two_mul_gap_le_l1 (tailModel μ r x) (tailModel Q r x) ℓ z
    have hh := hybrid_inequality (tailModel μ r x) (tailModel Q r x) ℓ
    linarith
  have hsum :
      β * (∑ x ∈ G, prob μ r x) ≤
        ∑ x ∈ G, prob μ r x *
          (∑ k ∈ Finset.range ℓ,
            stepError (tailModel μ r x) (tailModel Q r x) k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    rw [mul_comm β]
    exact mul_le_mul_of_nonneg_left (hpoint x hx) (prob_nonneg μ r x)
  have hsub :
      (∑ x ∈ G, prob μ r x *
        (∑ k ∈ Finset.range ℓ,
          stepError (tailModel μ r x) (tailModel Q r x) k)) ≤
        ∑ x : History r, prob μ r x *
          (∑ k ∈ Finset.range ℓ,
            stepError (tailModel μ r x) (tailModel Q r x) k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
    intro x _ _
    exact mul_nonneg (prob_nonneg μ r x)
      (Finset.sum_nonneg (fun k _ => stepError_nonneg _ _ k))
  rw [expected_tail_block] at hsub
  nlinarith

/-- The joint-mass form used in the report: the small mass is `α / 4`. -/
theorem block_bound_of_joint (μ Q : Model) (r ℓ : ℕ) (α : ℝ)
    (G : Finset (History r)) (hα : 0 < α)
    (hG : (1 / 2 : ℝ) ≤ ∑ x ∈ G, prob μ r x)
    (hpos : ∀ x ∈ G, 0 < prob μ r x)
    (hgood : ∀ x ∈ G, prob Q r x ≤ 2 * prob μ r x)
    (hjoint : ∀ x ∈ G, ∃ z : History ℓ,
      α * prob μ r x ≤ prob Q (r + ℓ) (append x ℓ z) ∧
      prob μ (r + ℓ) (append x ℓ z) ≤ (α / 4) * prob μ r x) :
    α / 4 ≤ blockError μ Q r ℓ := by
  have h := block_bound μ Q r ℓ (α / 2) G (by positivity) hG
  have hsep : ∀ x ∈ G, ∃ z : History ℓ,
      α / 2 ≤ prob (tailModel Q r x) ℓ z ∧
      prob (tailModel μ r x) ℓ z ≤ (α / 2) / 2 := by
    intro x hx
    obtain ⟨z, hlarge, hsmall⟩ := hjoint x hx
    rw [prob_append] at hlarge hsmall
    have hmul := mul_le_mul_of_nonneg_right (hgood x hx)
      (prob_nonneg (tailModel Q r x) ℓ z)
    have hxpos := hpos x hx
    refine ⟨z, ?_, ?_⟩ <;> nlinarith
  have hout := h hsep
  linarith

/-! A verified counterexample to the literal joint-mass formulation. -/

def counterexampleMu : Model where
  cond n _ := if n = 0 then 1 / 2 else 1 / 4
  nonneg n x := by split_ifs <;> norm_num
  le_one n x := by split_ifs <;> norm_num

def counterexampleQ : Model where
  cond
    | 0, _ => 1 / 4
    | 1, (_, b) => if b then 1 / 4 else 1 / 3
    | _ + 2, _ => 1 / 4
  nonneg n x := by
    rcases n with _ | (_ | n)
    · norm_num
    · rcases x with ⟨u, b⟩; cases b <;> norm_num
    · norm_num
  le_one n x := by
    rcases n with _ | (_ | n)
    · norm_num
    · rcases x with ⟨u, b⟩; cases b <;> norm_num
    · norm_num

theorem literal_counterexample :
    let μ := counterexampleMu
    let Q := counterexampleQ
    let x : History 1 := ((), false)
    prob μ 1 x = 1 / 2 ∧
    prob Q 1 x ≤ 2 * prob μ 1 x ∧
    (1 / 2 : ℝ) * prob μ 1 x ≤ prob Q 2 (x, true) ∧
    prob μ 2 (x, true) ≤ (1 / 4 : ℝ) * prob μ 1 x ∧
    blockError μ Q 1 1 < (1 / 4 : ℝ) := by
  dsimp
  refine ⟨by norm_num [counterexampleMu, prob, bitProb],
    by norm_num [counterexampleMu, counterexampleQ, prob, bitProb],
    by norm_num [counterexampleMu, counterexampleQ, prob, bitProb],
    by norm_num [counterexampleMu, prob, bitProb], ?_⟩
  simp only [blockError, Finset.sum_range_one]
  change stepError counterexampleMu counterexampleQ 1 < 1 / 4
  unfold stepError
  rw [history_sum_succ]
  norm_num [prob, bitProb, localError, counterexampleMu, counterexampleQ,
    Fintype.sum_bool]

theorem literal_block_claim_false : ¬ LiteralBlockClaim := by
  classical
  intro h
  rcases literal_counterexample with ⟨hμ, _, hQ, hp, herr⟩
  have hb := h counterexampleMu counterexampleQ 1 1 (1 / 2) {((), false)}
    (by norm_num)
    (by simpa using hμ.ge)
    (by
      intro x hx
      have heq : x = ((), false) := by simpa using hx
      subst x
      refine ⟨((), true), hQ, ?_⟩
      convert hp using 1 <;> norm_num [append])
  norm_num at hb
  linarith

end P27
