/-
Finite experiment robust to an arbitrary normalized semimeasure background.
Target environment: Lean 4.35.0 and Mathlib v4.35.0.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open scoped BigOperators

namespace RobustExperiment

set_option maxHeartbeats 2000000

/-! Part 1: definitions and the main theorem statement. -/

abbrev History : ℕ → Type
  | 0 => Unit
  | n + 1 => History n × Bool

instance historyFintype : (n : ℕ) → Fintype (History n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd (History n) Bool (historyFintype n) inferInstance

structure Model where
  cond : (n : ℕ) → History n → ℝ
  nonneg : ∀ n x, 0 ≤ cond n x
  le_one : ∀ n x, cond n x ≤ 1

def prob (p : Model) : (n : ℕ) → History n → ℝ
  | 0, _ => 1
  | n + 1, (x, b) => prob p n x * (if b then p.cond n x else 1 - p.cond n x)

abbrev Mass := (n : ℕ) → History n → ℝ

/-- Only levels at most `N` are constrained or used. -/
structure Semimeasure (N : ℕ) where
  mass : Mass
  nonneg : ∀ n, n ≤ N → ∀ x, 0 ≤ mass n x
  root : mass 0 () = 1
  children : ∀ n, n < N → ∀ x,
    mass (n + 1) (x, false) + mass (n + 1) (x, true) ≤ mass n x

def mix (w : ℝ) (p q : Mass) : Mass :=
  fun n x => w * p n x + (1 - w) * q n x

noncomputable def predict (s : Mass) (n : ℕ) (x : History n) : Bool :=
  if s (n + 1) (x, false) ≤ s (n + 1) (x, true) then true else false

def risk (μ : Model) (n : ℕ) (x : History n) (b : Bool) : ℝ :=
  if b then 1 - μ.cond n x else μ.cond n x

noncomputable def stepLoss (μ : Model) (s : Mass) (n : ℕ) : ℝ :=
  ∑ x : History n, prob μ n x * risk μ n x (predict s n x)

noncomputable def loss (μ : Model) (s : Mass) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, stepLoss μ s n

noncomputable def gamma (k : ℕ) : ℝ := 1 / (32 * (k : ℝ))

lemma gamma_pos (k : ℕ) (hk : 1 ≤ k) : 0 < gamma k := by
  unfold gamma
  have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  positivity

lemma gamma_le (k : ℕ) (hk : 1 ≤ k) : gamma k ≤ 1 / 32 := by
  have h : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold gamma
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * k)).2
  nlinarith

/-- `true` is μ; `false` is ν. The first `k²` bits have fixed bias. -/
noncomputable def experiment (k : ℕ) (hk : 1 ≤ k) (i : Bool) : Model where
  cond n _ := if n < k ^ 2 then 1 / 2 + (if i then gamma k else -gamma k) else 1 / 2
  nonneg n x := by
    have h₁ := gamma_pos k hk
    have h₂ := gamma_le k hk
    split_ifs <;> cases i <;> simp_all <;> linarith
  le_one n x := by
    have h₁ := gamma_pos k hk
    have h₂ := gamma_le k hk
    split_ifs <;> cases i <;> simp_all <;> linarith

noncomputable def core (k : ℕ) (hk : 1 ≤ k) (plus : Bool) : Mass :=
  mix (if plus then 3 / 4 else 1 / 4)
    (prob (experiment k hk true)) (prob (experiment k hk false))

noncomputable def contaminated (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ) (plus : Bool) : Mass :=
  mix (1 - η) (core k hk plus) A.mass

theorem theorem3 (k : ℕ) (hk : 1 ≤ k) (A : Semimeasure (k ^ 2))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ (1 : ℝ) / 2 ^ 20) :
    let μ := experiment k hk true
    let sMinus := contaminated k hk A η false
    let sPlus := contaminated k hk A η true
    (k : ℝ)/32 ≤ loss μ sMinus (k^2)-loss μ sPlus (k^2) ∧
    loss μ sMinus (k^2)-loss μ sPlus (k^2) ≤ (k : ℝ)/16 ∧
    ∀ n, 0 ≤ stepLoss μ sMinus n-stepLoss μ sPlus n := by

  /- Part 2: proofs. All auxiliary definitions and lemmas are local. -/

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

  have prob_pos (p : Model) (hp : ∀ n x, 0 < p.cond n x ∧ p.cond n x < 1)
      (n : ℕ) (x : History n) : 0 < prob p n x := by
    induction n with
    | zero => simp [prob]
    | succ n ih =>
      rcases x with ⟨x, b⟩
      cases b <;> simp only [prob, Bool.false_eq_true, ↓reduceIte]
      · exact mul_pos (ih x) (sub_pos.mpr (hp n x).2)
      · exact mul_pos (ih x) (hp n x).1

  have experiment_pos (k : ℕ) (hk : 1 ≤ k) (i : Bool) (n : ℕ) (x : History n) :
      0 < prob (experiment k hk i) n x := by
    apply prob_pos
    intro t h
    have h₁ := gamma_pos k hk
    have h₂ := gamma_le k hk
    by_cases ht : t < k ^ 2
    · cases i <;> simp only [experiment, ht, ↓reduceIte, Bool.false_eq_true] <;>
        constructor <;> linarith
    · norm_num [experiment, ht]

  have semimeasure_total {N : ℕ} (A : Semimeasure N) (n : ℕ) (hn : n ≤ N) :
      (∑ x : History n, A.mass n x) ≤ 1 := by
    induction n with
    | zero => simpa only [Fintype.sum_unique] using A.root.le
    | succ n ih =>
      rw [history_sum_succ]
      exact (Finset.sum_le_sum (fun x _ => A.children n (by omega) x)).trans (ih (by omega))


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

  have constant_moment_factor (k : ℝ) (hk : 1 ≤ k) :
      (1 / 2 - 1 / (32 * k)) ^ 2 / (1 / 2 + 1 / (32 * k)) +
        (1 / 2 + 1 / (32 * k)) ^ 2 / (1 / 2 - 1 / (32 * k)) =
        1 + 4 / (256 * k ^ 2 - 1) := by
    have hk0 : 0 < k := by linarith
    have hkne : k ≠ 0 := ne_of_gt hk0
    have hp : (1 / 2 + 1 / (32 * k) : ℝ) ≠ 0 := by positivity
    have hdiv : (1 : ℝ) / (32 * k) ≤ 1 / 32 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * k)).2
      nlinarith
    have hq : (1 / 2 - 1 / (32 * k) : ℝ) ≠ 0 := by linarith
    have hd : (256 * k ^ 2 - 1 : ℝ) ≠ 0 := by
      have : 1 ≤ k ^ 2 := by nlinarith
      nlinarith
    field_simp
    ring_nf
    have h32 : -2 + k * 32 ≠ 0 := by linarith
    have h256 : -1 + k ^ 2 * 256 ≠ 0 := by nlinarith
    field_simp [h32, h256]
    ring

  have constant_upper_step (K t : ℝ) (hK : 1 ≤ K) (ht : t ≤ K) :
      (1 + t / (50 * K)) * (1 + 4 / (256 * K - 1)) ≤
        1 + (t + 1) / (50 * K) := by
    have hK0 : 0 < K := by linarith
    have hd : 0 < 256 * K - 1 := by linarith
    have hU : (1 + t / (50 * K)) = (50 * K + t) / (50 * K) := by
      field_simp
    have hF : (1 + 4 / (256 * K - 1)) = (256 * K + 3) / (256 * K - 1) := by
      field_simp
      ring
    have hV : (1 + (t + 1) / (50 * K)) = (50 * K + t + 1) / (50 * K) := by
      field_simp
      ring
    rw [hU, hF, hV, div_mul_div_comm]
    apply (div_le_div_iff₀ (mul_pos (by positivity) hd) (by positivity)).2
    nlinarith

  have finite_moment_bound (p q : Model) (k : ℕ) (hk : 1 ≤ k)
      (hp : ∀ n < k ^ 2, ∀ x, p.cond n x = 1 / 2 + 1 / (32 * (k : ℝ)))
      (hq : ∀ n < k ^ 2, ∀ x, q.cond n x = 1 / 2 - 1 / (32 * (k : ℝ)))
      (n : ℕ) (hn : n ≤ k ^ 2) :
      moment p q n ≤ 1 + (n : ℝ) / (50 * (k : ℝ) ^ 2) := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hK : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have hd : (0 : ℝ) < 256 * (k : ℝ) ^ 2 - 1 := by nlinarith
    induction n with
    | zero => simp [moment_zero]
    | succ n ih =>
      have hnlt : n < k ^ 2 := by omega
      have hnle : n ≤ k ^ 2 := by omega
      have hnR : (n : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hnle
      have ih' := ih hnle
      rw [moment_succ p q n _ _ (hp n hnlt) (hq n hnlt)]
      have hf :
          (1 / 2 - 1 / (32 * (k : ℝ))) ^ 2 / (1 / 2 + 1 / (32 * (k : ℝ))) +
            (1 - (1 / 2 - 1 / (32 * (k : ℝ)))) ^ 2 /
              (1 - (1 / 2 + 1 / (32 * (k : ℝ)))) =
            1 + 4 / (256 * (k : ℝ) ^ 2 - 1) := by
        convert constant_moment_factor (k : ℝ) hkR using 1; ring
      rw [hf]
      calc
        moment p q n * (1 + 4 / (256 * (k : ℝ) ^ 2 - 1)) ≤
            (1 + (n : ℝ) / (50 * (k : ℝ) ^ 2)) *
              (1 + 4 / (256 * (k : ℝ) ^ 2 - 1)) := by
          apply mul_le_mul_of_nonneg_right ih'
          positivity
        _ ≤ 1 + ((n : ℝ) + 1) / (50 * (k : ℝ) ^ 2) :=
          constant_upper_step ((k : ℝ) ^ 2) (n : ℝ) hK hnR
        _ = _ := by push_cast; rfl

  have finite_variance_bound (p q : Model) (k : ℕ) (hk : 1 ≤ k)
      (hp : ∀ n < k ^ 2, ∀ x, p.cond n x = 1 / 2 + 1 / (32 * (k : ℝ)))
      (hq : ∀ n < k ^ 2, ∀ x, q.cond n x = 1 / 2 - 1 / (32 * (k : ℝ)))
      (n : ℕ) (hn : n ≤ k ^ 2) (hpos : ∀ x, 0 < prob p n x) :
      variance p q n ≤ 1 / 50 := by
    have hm := finite_moment_bound p q k hk hp hq n hn
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    have hnR : (n : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hn
    have hfrac : (n : ℝ) / (50 * (k : ℝ) ^ 2) ≤ 1 / 50 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 50 * (k : ℝ) ^ 2)).2
      nlinarith
    rw [variance_eq p q n hpos]
    linarith


  have reciprocal_increment_nonneg (a p q q0 q1 : ℝ)
      (ha : 0 < a)
      (hq0 : 0 < q0) (hq1 : 0 < q1) (hqs : q0 + q1 ≤ q) :
      0 ≤ (a * (1-p))^2 / q0 + (a*p)^2/q1 - a^2/q := by
    have hq : 0 < q := lt_of_lt_of_le (add_pos hq0 hq1) hqs
    have hid :
        (a * (1-p))^2 / q0 + (a*p)^2/q1 - a^2/q =
        a^2/q^2 * ((q0-(1-p)*q)^2/q0 + (q1-p*q)^2/q1 + (q-q0-q1)) := by
      field_simp
      ring
    rw [hid]
    apply mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
    have h0 : 0 ≤ (q0-(1-p)*q)^2/q0 := div_nonneg (sq_nonneg _) hq0.le
    have h1 : 0 ≤ (q1-p*q)^2/q1 := div_nonneg (sq_nonneg _) hq1.le
    linarith

  have reciprocal_centered_bound (a p q q0 q1 : ℝ)
      (ha : 0 < a) (hq0 : 0 < q0) (hq1 : 0 < q1)
      (hqs : q0 + q1 ≤ q) (hqa : q ≤ 5*a/4) :
      ((q1-p*q)-(q0-(1-p)*q))^2/(4*a) ≤
        (a*(1-p))^2/q0 + (a*p)^2/q1 - a^2/q := by
    have hq : 0 < q := lt_of_lt_of_le (add_pos hq0 hq1) hqs
    have h0q : q0 ≤ q := by linarith
    have h1q : q1 ≤ q := by linarith
    let x0 := q0-(1-p)*q
    let x1 := q1-p*q
    have hid :
        (a*(1-p))^2/q0 + (a*p)^2/q1 - a^2/q =
        a^2/q^2 * (x0^2/q0+x1^2/q1+(q-q0-q1)) := by
      dsimp [x0, x1]
      field_simp
      ring
    have hj0 : x0^2/q ≤ x0^2/q0 :=
      div_le_div_of_nonneg_left (sq_nonneg _) hq0 h0q
    have hj1 : x1^2/q ≤ x1^2/q1 :=
      div_le_div_of_nonneg_left (sq_nonneg _) hq1 h1q
    have hj : (x1-x0)^2/(2*q) ≤ x0^2/q0+x1^2/q1+(q-q0-q1) := by
      have hh : (x1-x0)^2/(2*q) ≤ x0^2/q+x1^2/q := by
        apply (div_le_iff₀ (by positivity : 0 < 2*q)).2
        field_simp
        nlinarith [sq_nonneg (x0+x1)]
      linarith
    have hcube : 2*q^3 ≤ 4*a^3 := by
      have hm : q^3 ≤ (5*a/4)^3 := pow_le_pow_left₀ hq.le hqa 3
      have ha3 : 0 ≤ a^3 := by positivity
      nlinarith
    calc
      ((q1-p*q)-(q0-(1-p)*q))^2/(4*a) = (x1-x0)^2/(4*a) := rfl
      _ ≤ a^2/q^2 * ((x1-x0)^2/(2*q)) := by
        apply (div_le_iff₀ (by positivity : 0 < 4*a)).2
        field_simp
        nlinarith [mul_nonneg (sq_nonneg (x1-x0)) (sub_nonneg.mpr hcube)]
      _ ≤ a^2/q^2 * (x0^2/q0+x1^2/q1+(q-q0-q1)) :=
        mul_le_mul_of_nonneg_left hj (by positivity)
      _ = _ := hid.symm


  let augmented (μ : Model) {N : ℕ} (A : Semimeasure N) (η : ℝ) : Mass :=
    fun n x => prob μ n x + η * A.mass n x

  let potential (μ : Model) {N : ℕ} (A : Semimeasure N) (η : ℝ)
      (n : ℕ) : ℝ := ∑ x : History n, (prob μ n x)^2 / augmented μ A η n x

  let increment (μ : Model) {N : ℕ} (A : Semimeasure N) (η : ℝ)
      (n : ℕ) (x : History n) : ℝ :=
    (prob μ (n+1) (x,false))^2 / augmented μ A η (n+1) (x,false) +
    (prob μ (n+1) (x,true))^2 / augmented μ A η (n+1) (x,true) -
    (prob μ n x)^2 / augmented μ A η n x

  have augmented_pos (μ : Model) {N : ℕ} (A : Semimeasure N) (η : ℝ)
      (hη : 0 ≤ η) (hμ : ∀ n x, 0 < prob μ n x) (n : ℕ) (hn : n ≤ N)
      (x : History n) : 0 < augmented μ A η n x := by
    exact add_pos_of_pos_of_nonneg (hμ n x) (mul_nonneg hη (A.nonneg n hn x))

  have increment_nonneg (μ : Model) {N : ℕ} (A : Semimeasure N) (η : ℝ)
      (hη : 0 ≤ η) (hμ : ∀ n x, 0 < prob μ n x) (n : ℕ) (hn : n < N)
      (x : History n) : 0 ≤ increment μ A η n x := by
    have hqs : augmented μ A η (n+1) (x,false) +
        augmented μ A η (n+1) (x,true) ≤ augmented μ A η n x := by
      have hh := mul_le_mul_of_nonneg_left (A.children n hn x) hη
      simp only [augmented, prob, Bool.false_eq_true, ↓reduceIte]
      nlinarith
    have h := reciprocal_increment_nonneg (prob μ n x) (μ.cond n x)
      (augmented μ A η n x) (augmented μ A η (n+1) (x,false))
      (augmented μ A η (n+1) (x,true)) (hμ n x)
      (augmented_pos μ A η hη hμ (n+1) (by omega) (x,false))
      (augmented_pos μ A η hη hμ (n+1) (by omega) (x,true)) hqs
    simpa only [increment, prob, Bool.false_eq_true, ↓reduceIte] using h

  have potential_le_one (μ : Model) {N : ℕ} (A : Semimeasure N) (η : ℝ)
      (hη : 0 ≤ η) (hμ : ∀ n x, 0 < prob μ n x) (n : ℕ) (hn : n ≤ N) :
      potential μ A η n ≤ 1 := by
    calc
      potential μ A η n ≤ ∑ x : History n, prob μ n x := by
        apply Finset.sum_le_sum
        intro x hx
        apply (div_le_iff₀ (augmented_pos μ A η hη hμ n hn x)).2
        have hh := mul_nonneg (hμ n x).le (mul_nonneg hη (A.nonneg n hn x))
        dsimp [augmented]
        nlinarith
      _ = 1 := prob_total μ n

  have potential_zero (μ : Model) {N : ℕ} (A : Semimeasure N) (η : ℝ) :
      potential μ A η 0 = 1 / (1+η) := by
    simp [potential, augmented, prob, A.root]

  have increment_total (μ : Model) {N : ℕ} (A : Semimeasure N) (η : ℝ) (n : ℕ) :
      (∑ x : History n, increment μ A η n x) =
        potential μ A η (n+1) - potential μ A η n := by
    unfold potential increment
    rw [history_sum_succ, Finset.sum_sub_distrib]

  have increment_telescope (μ : Model) {N : ℕ} (A : Semimeasure N) (η : ℝ) (n : ℕ) :
      (∑ t ∈ Finset.range n, ∑ x : History t, increment μ A η t x) =
        potential μ A η n - potential μ A η 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, increment_total]
      ring

  have increment_budget (μ : Model) {N : ℕ} (A : Semimeasure N) (η : ℝ)
      (hη : 0 ≤ η) (hμ : ∀ n x, 0 < prob μ n x) :
      (∑ t ∈ Finset.range N, ∑ x : History t, increment μ A η t x) ≤ η := by
    rw [increment_telescope, potential_zero]
    have hh := potential_le_one μ A η hη hμ N le_rfl
    have hη1 : 0 < 1+η := by linarith
    have hbound : 1 - 1/(1+η) ≤ η := by
      have hd : 1 - η ≤ 1/(1+η) := by
        apply (le_div_iff₀ hη1).2
        nlinarith [sq_nonneg η]
      linarith
    linarith



  have small_variance_near (a b : ℝ) (ha : 0 < a)
      (h : 4 * ((b-a)^2/a) < a) : a/2 < b ∧ b < 2*a := by
    have he : 4 * ((b-a)^2/a) * a = 4*(b-a)^2 := by field_simp
    have hh := mul_lt_mul_of_pos_right h ha
    rw [he] at hh
    constructor
    · by_contra hn
      have hb : b ≤ a/2 := le_of_not_gt hn
      have hp : 0 ≤ (a-2*b)*(3*a-2*b) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    · by_contra hn
      have hb : 2*a ≤ b := le_of_not_gt hn
      have hp : 0 ≤ (2*b-a)*(2*b-3*a) := mul_nonneg (by linarith) (by linarith)
      nlinarith

  have bad_score_cost (a b d eta r w I : ℝ)
      (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
      (he : eta ≤ 1/4) (hr : 0 ≤ r) (hI : 0 ≤ I)
      (hcenter : r ≤ a/32 → (w-2*d*r)^2 ≤ 4*a*I)
      (hbad : 0 ≤ (1-eta)*d*(a-3*b)/2+w ∨
        (1-eta)*d*(3*a-b)/2+w < 0) :
      a ≤ 4*((b-a)^2/a)+32*r+256*(I/d^2) := by
    have hv : 0 ≤ (b-a)^2/a := div_nonneg (sq_nonneg _) ha.le
    have hj : 0 ≤ I/d^2 := div_nonneg hI (sq_nonneg _)
    by_cases hfar : a ≤ 4*((b-a)^2/a)
    · linarith
    have hnear := small_variance_near a b ha (lt_of_not_ge hfar)
    by_cases hlarge : a ≤ 32*r
    · linarith
    have hrsmall : r ≤ a/32 := by linarith
    have hc := hcenter hrsmall
    have hcent : d*a/8 ≤ w-2*d*r ∨ w-2*d*r ≤ -(d*a/8) := by
      have hm : 3*a/16 ≤ (1-eta)*(3*b-a)/2 := by
        have hh : 0 ≤ (1-eta-3/4)*(3*b-a) :=
          mul_nonneg (by linarith) (by linarith [hnear.1])
        nlinarith [hnear.1]
      have hp : 3*a/16 ≤ (1-eta)*(3*a-b)/2 := by
        have hh : 0 ≤ (1-eta-3/4)*(3*a-b) :=
          mul_nonneg (by linarith) (by linarith [hnear.2])
        nlinarith [hnear.2]
      have hmd := mul_le_mul_of_nonneg_left hm hd.le
      have hpd := mul_le_mul_of_nonneg_left hp hd.le
      have hrd := mul_le_mul_of_nonneg_left hrsmall (by positivity : 0 ≤ 2*d)
      have hrzero := mul_nonneg hd.le hr
      rcases hbad with hm_bad | hp_bad
      · left; nlinarith
      · right; nlinarith
    have hs : (d*a/8)^2 ≤ (w-2*d*r)^2 := by
      rcases hcent with h | h
      · exact pow_le_pow_left₀ (by positivity) h 2
      · have hh := pow_le_pow_left₀ (by positivity : 0 ≤ d*a/8)
          (show d*a/8 ≤ -(w-2*d*r) by linarith) 2
        simpa only [neg_sq] using hh
    have hmul : a * (d^2*a-256*I) ≤ 0 := by nlinarith
    have hjbound : d^2*a ≤ 256*I := by
      have h : d^2*a-256*I ≤ 0 :=
        le_of_mul_le_mul_left (by simpa only [mul_zero] using hmul) ha
      linarith
    have hfinal : a ≤ 256*(I/d^2) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : 0 < d^2)).2
      nlinarith
    linarith

  have abstract_pointwise_gap (a b d eta r w I : ℝ)
      (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
      (he : eta ≤ 1/4) (hr : 0 ≤ r) (hI : 0 ≤ I)
      (hcenter : r ≤ a/32 → (w-2*d*r)^2 ≤ 4*a*I) :
      let sm := (1-eta)*d*(a-3*b)/2+w
      let sp := (1-eta)*d*(3*a-b)/2+w
      let g := a*((if 0 ≤ sm then 1/2-d else 1/2+d) -
        (if 0 ≤ sp then 1/2-d else 1/2+d))
      0 ≤ g ∧ g ≤ 2*d*a ∧
        2*d*(a-4*((b-a)^2/a)-32*r-256*(I/d^2)) ≤ g := by
    dsimp only
    have hmon : (1-eta)*d*(a-3*b)/2+w ≤ (1-eta)*d*(3*a-b)/2+w := by
      have h := mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1-eta) hd.le)
        (show 0 ≤ a+b by linarith)
      nlinarith
    have hv : 0 ≤ (b-a)^2/a := div_nonneg (sq_nonneg _) ha.le
    have hj : 0 ≤ I/d^2 := div_nonneg hI (sq_nonneg _)
    by_cases hm : 0 ≤ (1-eta)*d*(a-3*b)/2+w
    · have hp := hm.trans hmon
      have hbnd := bad_score_cost a b d eta r w I ha hb hd he hr hI hcenter (Or.inl hm)
      simp only [hm, hp, ite_true, sub_self, mul_zero]
      refine ⟨le_rfl, by positivity, ?_⟩
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    · by_cases hp : 0 ≤ (1-eta)*d*(3*a-b)/2+w
      · simp only [hm, hp, ite_true, ite_false]
        have hcost : 0 ≤ 4*((b-a)^2/a)+32*r+256*(I/d^2) := by positivity
        have hh := mul_nonneg (show 0 ≤ 2*d by positivity) hcost
        constructor
        · nlinarith
        constructor <;> nlinarith
      · have hbnd := bad_score_cost a b d eta r w I ha hb hd he hr hI hcenter
          (Or.inr (lt_of_not_ge hp))
        simp only [hm, hp, ite_false, sub_self, mul_zero]
        refine ⟨le_rfl, by positivity, ?_⟩
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

  have pointwise_gap (a b d eta z z0 z1 : ℝ)
      (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdh : d < 1/2)
      (he0 : 0 ≤ eta) (he : eta ≤ 1/4)
      (hz0 : 0 ≤ z0) (hz1 : 0 ≤ z1) (hz : z0+z1 ≤ z) :
      let I := (a*(1/2-d))^2/(a*(1/2-d)+eta*z0) +
        (a*(1/2+d))^2/(a*(1/2+d)+eta*z1)-a^2/(a+eta*z)
      let sm := (1-eta)*d*(a-3*b)/2+eta*(z1-z0)
      let sp := (1-eta)*d*(3*a-b)/2+eta*(z1-z0)
      let g := a*((if 0 ≤ sm then 1/2-d else 1/2+d)-
        (if 0 ≤ sp then 1/2-d else 1/2+d))
      0 ≤ g ∧ g ≤ 2*d*a ∧
        2*d*(a-4*((b-a)^2/a)-32*eta*z-256*(I/d^2)) ≤ g := by
    let I := (a*(1/2-d))^2/(a*(1/2-d)+eta*z0) +
        (a*(1/2+d))^2/(a*(1/2+d)+eta*z1)-a^2/(a+eta*z)
    have hq0 : 0 < a*(1/2-d)+eta*z0 := by positivity
    have hq1 : 0 < a*(1/2+d)+eta*z1 := by positivity
    have hqs : a*(1/2-d)+eta*z0+(a*(1/2+d)+eta*z1) ≤ a+eta*z := by
      have h := mul_le_mul_of_nonneg_left hz he0
      nlinarith
    have hI : 0 ≤ I := by
      have h := reciprocal_increment_nonneg a (1/2+d) (a+eta*z)
        (a*(1/2-d)+eta*z0) (a*(1/2+d)+eta*z1) ha hq0 hq1 hqs
      convert h using 1; dsimp [I]; congr 2; ring
    have hcenter : eta*z ≤ a/32 → (eta*(z1-z0)-2*d*(eta*z))^2 ≤ 4*a*I := by
      intro hr
      have hqa : a+eta*z ≤ 5*a/4 := by linarith
      have h := reciprocal_centered_bound a (1/2+d) (a+eta*z)
        (a*(1/2-d)+eta*z0) (a*(1/2+d)+eta*z1) ha hq0 hq1 hqs hqa
      have hce : (a*(1/2+d)+eta*z1-(1/2+d)*(a+eta*z))-
          (a*(1/2-d)+eta*z0-(1-(1/2+d))*(a+eta*z)) =
          eta*(z1-z0)-2*d*(eta*z) := by ring
      have heq : (a*(1-(1/2+d)))^2/(a*(1/2-d)+eta*z0)+
          (a*(1/2+d))^2/(a*(1/2+d)+eta*z1)-a^2/(a+eta*z) = I := by
        dsimp [I]
        congr 3; ring
      rw [hce, heq] at h
      have hh := (div_le_iff₀ (by positivity : 0 < 4*a)).mp h
      nlinarith
    have hr : 0 ≤ eta*z := mul_nonneg he0 (by linarith)
    simpa only [I, mul_assoc] using
      abstract_pointwise_gap a b d eta (eta*z) (eta*(z1-z0)) I
        ha hb hd he hr hI hcenter


  have contaminated_score (k : ℕ) (hk : 1 ≤ k)
      (A : Semimeasure (k ^ 2)) (η : ℝ) (i : Bool)
      (n : ℕ) (hn : n < k ^ 2) (x : History n) :
      contaminated k hk A η i (n+1) (x,true) -
        contaminated k hk A η i (n+1) (x,false) =
      (1-η)*gamma k*((if i then 3 else 1)*prob (experiment k hk true) n x -
        (if i then 1 else 3)*prob (experiment k hk false) n x)/2 +
        η*(A.mass (n+1) (x,true)-A.mass (n+1) (x,false)) := by
    cases i <;> simp [contaminated, mix, core, prob, experiment, hn] <;> ring

  have risk_predict_score (μ : Model) (s : Mass) (n : ℕ) (x : History n) (d : ℝ)
      (hμ : μ.cond n x = 1/2+d) :
      risk μ n x (predict s n x) =
        if 0 ≤ s (n+1) (x,true)-s (n+1) (x,false) then 1/2-d else 1/2+d := by
    simp only [risk, predict, Bool.ite_false_right_eq_true, and_true, hμ, sub_nonneg]
    split_ifs <;> ring

  have history_gap (k : ℕ) (hk : 1 ≤ k) (A : Semimeasure (k ^ 2))
      (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/4)
      (n : ℕ) (hn : n < k ^ 2) (x : History n) :
      let μ := experiment k hk true
      let ν := experiment k hk false
      let g := prob μ n x * (risk μ n x (predict (contaminated k hk A η false) n x) -
        risk μ n x (predict (contaminated k hk A η true) n x))
      0 ≤ g ∧ g ≤ 2*gamma k*prob μ n x ∧
        2*gamma k*(prob μ n x - 4*((prob ν n x-prob μ n x)^2/prob μ n x) -
          32*η*A.mass n x - 256*(increment μ A η n x/(gamma k)^2)) ≤ g := by
    dsimp only
    rw [risk_predict_score _ _ _ _ (gamma k) (by simp [experiment, hn]),
      risk_predict_score _ _ _ _ (gamma k) (by simp [experiment, hn]),
      contaminated_score k hk A η false n hn x, contaminated_score k hk A η true n hn x]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hg := gamma_le k hk
    have hp := pointwise_gap
      (prob (experiment k hk true) n x) (prob (experiment k hk false) n x)
      (gamma k) η (A.mass n x) (A.mass (n+1) (x,false)) (A.mass (n+1) (x,true))
      (experiment_pos k hk true n x) (experiment_pos k hk false n x)
      (gamma_pos k hk) (by linarith) hη0 hη1
      (A.nonneg (n+1) (by omega) (x,false)) (A.nonneg (n+1) (by omega) (x,true))
      (A.children n hn x)
    have hc : 1 - (1/2+gamma k) = 1/2-gamma k := by ring
    simpa only [increment, augmented, prob, experiment, hn, Bool.false_eq_true,
      ↓reduceIte, hc, one_mul] using hp

  have step_bounds (k : ℕ) (hk : 1 ≤ k) (A : Semimeasure (k ^ 2))
      (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/4)
      (n : ℕ) (hn : n < k ^ 2) :
      let μ := experiment k hk true
      let g := stepLoss μ (contaminated k hk A η false) n -
        stepLoss μ (contaminated k hk A η true) n
      0 ≤ g ∧ g ≤ 2*gamma k ∧
        2*gamma k*(1-4*variance μ (experiment k hk false) n - 32*η -
          256*((∑ x : History n, increment μ A η n x)/(gamma k)^2)) ≤ g := by
    let μ := experiment k hk true
    let ν := experiment k hk false
    have hsum : stepLoss μ (contaminated k hk A η false) n -
        stepLoss μ (contaminated k hk A η true) n =
        ∑ x : History n, prob μ n x *
          (risk μ n x (predict (contaminated k hk A η false) n x) -
            risk μ n x (predict (contaminated k hk A η true) n x)) := by
      simp only [stepLoss, mul_sub, Finset.sum_sub_distrib]
    change 0 ≤ _ ∧ _ ≤ _ ∧ _ ≤ _
    rw [hsum]
    constructor
    · exact Finset.sum_nonneg (fun x _ => (history_gap k hk A η hη0 hη1 n hn x).1)
    constructor
    · calc
        _ ≤ ∑ x : History n, 2*gamma k*prob μ n x :=
          Finset.sum_le_sum (fun x _ => (history_gap k hk A η hη0 hη1 n hn x).2.1)
        _ = 2*gamma k := by rw [← Finset.mul_sum, prob_total, mul_one]
    · have hm := semimeasure_total A n (Nat.le_of_lt hn)
      have hpen := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 32*η)
      calc
        _ ≤ 2*gamma k*(1-4*variance μ ν n - 32*η*(∑ x : History n, A.mass n x) -
            256*((∑ x : History n, increment μ A η n x)/(gamma k)^2)) := by
          apply mul_le_mul_of_nonneg_left _ (by have := gamma_pos k hk; positivity)
          linarith
        _ = ∑ x : History n, 2*gamma k*(prob μ n x -
            4*((prob ν n x-prob μ n x)^2/prob μ n x) - 32*η*A.mass n x -
            256*(increment μ A η n x/(gamma k)^2)) := by
          simp only [← Finset.mul_sum, Finset.sum_sub_distrib, prob_total, variance,
            Finset.sum_div]
        _ ≤ _ := Finset.sum_le_sum
          (fun x _ => (history_gap k hk A η hη0 hη1 n hn x).2.2)

  let μ := experiment k hk true
  let ν := experiment k hk false
  let sMinus := contaminated k hk A η false
  let sPlus := contaminated k hk A η true
  have he : η ≤ 1/4 := by norm_num at hη1 ⊢; linarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hd := gamma_pos k hk
  have hv (n : ℕ) (hn : n < k^2) : variance μ ν n ≤ 1/50 := by
    exact finite_variance_bound μ ν k hk
      (by intro t ht x; simp [μ, experiment, ht, gamma])
      (by intro t ht x; simp [ν, experiment, ht, gamma, sub_eq_add_neg])
      n (Nat.le_of_lt hn) (experiment_pos k hk true n)
  have hi := increment_budget μ A η hη0 (experiment_pos k hk true)
  have hloss : loss μ sMinus (k^2)-loss μ sPlus (k^2) =
      ∑ n ∈ Finset.range (k^2), (stepLoss μ sMinus n-stepLoss μ sPlus n) := by
    simp only [loss, Finset.sum_sub_distrib]
  have hlower : 2*gamma k*((k : ℝ)^2*(1-4/50-32*η)-256*η/(gamma k)^2) ≤
      loss μ sMinus (k^2)-loss μ sPlus (k^2) := by
    calc
      _ ≤ 2*gamma k*((k : ℝ)^2*(1-4/50-32*η)-
          256*(∑ n ∈ Finset.range (k^2), ∑ x : History n, increment μ A η n x)/(gamma k)^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hdiv := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 256)) (sq_nonneg (gamma k))
        linarith
      _ = ∑ n ∈ Finset.range (k^2),
          2*gamma k*(1-4/50-32*η-256*((∑ x : History n, increment μ A η n x)/(gamma k)^2)) := by
        simp only [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow]
        ring
      _ ≤ ∑ n ∈ Finset.range (k^2),
          2*gamma k*(1-4*variance μ ν n-32*η-256*((∑ x : History n,
            increment μ A η n x)/(gamma k)^2)) := by
        apply Finset.sum_le_sum
        intro n hn
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hh := hv n (Finset.mem_range.mp hn)
        linarith
      _ ≤ ∑ n ∈ Finset.range (k^2), (stepLoss μ sMinus n-stepLoss μ sPlus n) := by
        apply Finset.sum_le_sum
        intro n hn
        exact (step_bounds k hk A η hη0 he n (Finset.mem_range.mp hn)).2.2
      _ = _ := hloss.symm
  have hconst : (k : ℝ)/32 ≤
      2*gamma k*((k : ℝ)^2*(1-4/50-32*η)-256*η/(gamma k)^2) := by
    have heta : η ≤ 1/1048576 := by norm_num at hη1; exact hη1
    unfold gamma
    field_simp
    nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) (sub_nonneg.mpr heta)]
  have hupper : loss μ sMinus (k^2)-loss μ sPlus (k^2) ≤ (k : ℝ)/16 := by
    rw [hloss]
    calc
      _ ≤ ∑ _n ∈ Finset.range (k^2), 2*gamma k := by
        apply Finset.sum_le_sum
        intro n hn
        exact (step_bounds k hk A η hη0 he n (Finset.mem_range.mp hn)).2.1
      _ = (k : ℝ)/16 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, gamma]
        field_simp
        ring
  refine ⟨hconst.trans hlower, hupper, ?_⟩
  intro n
  by_cases hn : n < k^2
  · exact (step_bounds k hk A η hη0 he n hn).1
  · have hr (s : Mass) (x : History n) : risk μ n x (predict s n x) = 1/2 := by
      unfold risk
      simp only [μ, experiment, hn, ↓reduceIte]
      split_ifs <;> norm_num
    change 0 ≤ stepLoss μ sMinus n - stepLoss μ sPlus n
    simp only [stepLoss, hr, sub_self, le_refl]


/-! Further checks of the statement-layer definitions. -/

lemma prob_nonneg (p : Model) (n : ℕ) (x : History n) : 0 ≤ prob p n x := by
  induction n with
  | zero => simp [prob]
  | succ n ih =>
    rcases x with ⟨x, b⟩
    cases b <;> simp only [prob, Bool.false_eq_true, ↓reduceIte]
    · exact mul_nonneg (ih x) (sub_nonneg.mpr (p.le_one n x))
    · exact mul_nonneg (ih x) (p.nonneg n x)

lemma prob_pos (p : Model) (hp : ∀ n x, 0 < p.cond n x ∧ p.cond n x < 1)
    (n : ℕ) (x : History n) : 0 < prob p n x := by
  induction n with
  | zero => simp [prob]
  | succ n ih =>
    rcases x with ⟨x, b⟩
    cases b <;> simp only [prob, Bool.false_eq_true, ↓reduceIte]
    · exact mul_pos (ih x) (sub_pos.mpr (hp n x).2)
    · exact mul_pos (ih x) (hp n x).1

lemma experiment_pos (k : ℕ) (hk : 1 ≤ k) (i : Bool) (n : ℕ) (x : History n) :
    0 < prob (experiment k hk i) n x := by
  apply prob_pos
  intro t h
  have h₁ := gamma_pos k hk
  have h₂ := gamma_le k hk
  by_cases ht : t < k ^ 2
  · cases i <;> simp only [experiment, ht, ↓reduceIte, Bool.false_eq_true] <;>
      constructor <;> linarith
  · norm_num [experiment, ht]

/-- A model's prefix probabilities form a normalized measure, hence a semimeasure. -/
noncomputable def modelSemimeasure (p : Model) (N : ℕ) : Semimeasure N where
  mass := prob p
  nonneg n _ x := prob_nonneg p n x
  root := rfl
  children n _ x := by
    simp only [prob, Bool.false_eq_true, ↓reduceIte]
    apply le_of_eq
    ring

/-- Convex combinations preserve finite semimeasures and their unit root. -/
noncomputable def Semimeasure.mix {N : ℕ} (w : ℝ) (p q : Semimeasure N)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : Semimeasure N where
  mass := RobustExperiment.mix w p.mass q.mass
  nonneg n hn x := by
    exact add_nonneg (mul_nonneg hw0 (p.nonneg n hn x))
      (mul_nonneg (sub_nonneg.mpr hw1) (q.nonneg n hn x))
  root := by simp only [RobustExperiment.mix, p.root, q.root]; ring
  children n hn x := by
    have hp := p.children n hn x
    have hq := q.children n hn x
    have hwp := mul_le_mul_of_nonneg_left hp hw0
    have hwq := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hw1)
    dsimp only [RobustExperiment.mix]
    nlinarith

lemma core_pos (k : ℕ) (hk : 1 ≤ k) (plus : Bool)
    (n : ℕ) (x : History n) : 0 < core k hk plus n x := by
  have hp := experiment_pos k hk true n x
  have hq := experiment_pos k hk false n x
  cases plus <;> norm_num [core, mix] <;> positivity

/-- Every contaminated mixture used in the theorem is strictly positive. -/
lemma contaminated_pos (k : ℕ) (hk : 1 ≤ k) (A : Semimeasure (k ^ 2))
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (plus : Bool)
    (n : ℕ) (hn : n ≤ k ^ 2) (x : History n) :
    0 < contaminated k hk A η plus n x := by
  have hc := core_pos k hk plus n x
  have hA := A.nonneg n hn x
  have hcη : 0 < 1 - η := by linarith
  have hm : 0 ≤ 1 - (1 - η) := by linarith
  exact add_pos_of_pos_of_nonneg (mul_pos hcη hc) (mul_nonneg hm hA)

/-- The unperturbed prior mixture as a finite semimeasure. -/
noncomputable def coreSemimeasure (k : ℕ) (hk : 1 ≤ k) (plus : Bool) :
    Semimeasure (k ^ 2) :=
  Semimeasure.mix (if plus then 3 / 4 else 1 / 4)
    (modelSemimeasure (experiment k hk true) (k ^ 2))
    (modelSemimeasure (experiment k hk false) (k ^ 2))
    (by cases plus <;> norm_num) (by cases plus <;> norm_num)

lemma coreSemimeasure_mass (k : ℕ) (hk : 1 ≤ k) (plus : Bool) :
    (coreSemimeasure k hk plus).mass = core k hk plus := rfl

/-- The common-background mixture as a finite semimeasure. -/
noncomputable def contaminatedSemimeasure (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (plus : Bool) : Semimeasure (k ^ 2) :=
  Semimeasure.mix (1 - η) (coreSemimeasure k hk plus) A
    (by linarith) (by linarith)

lemma contaminatedSemimeasure_mass (k : ℕ) (hk : 1 ≤ k)
    (A : Semimeasure (k ^ 2)) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (plus : Bool) :
    (contaminatedSemimeasure k hk A η hη0 hη1 plus).mass =
      contaminated k hk A η plus := rfl


/-- `k` is exactly the square root of the experiment's horizon. -/
lemma sqrt_horizon (k : ℕ) : Real.sqrt ((k ^ 2 : ℕ) : ℝ) = (k : ℝ) := by
  rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg k)]

lemma gamma_sqrt (k : ℕ) :
    gamma k = 1 / (32 * Real.sqrt ((k ^ 2 : ℕ) : ℝ)) := by
  rw [sqrt_horizon]
  rfl

/-- The chosen action minimizes binary zero-one loss, with ties going to `true`. -/
lemma predict_optimal (s : Mass) (n : ℕ) (x : History n) (b : Bool) :
    (if predict s n x then s (n+1) (x,false) else s (n+1) (x,true)) ≤
      (if b then s (n+1) (x,false) else s (n+1) (x,true)) := by
  by_cases h : s (n+1) (x,false) ≤ s (n+1) (x,true)
  · cases b <;> simp [predict, h]
  · have hh := le_of_lt (lt_of_not_ge h)
    cases b <;> simp [predict, h, hh]

end RobustExperiment
