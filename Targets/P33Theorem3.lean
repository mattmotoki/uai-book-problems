/-
Target: Theorem 3 of Pro answer 008 (`pro/008-p33-effective-priors.a.md`, Section 2), the core lemma of the
effective counterexample to Hutter (2005) Problem 3.3 ("Is L^ξ − L^ξ' < ∞?").

Fidelity note. Horizon N = k² (k ≥ 1), γ = 1/(32k) = 1/(32√N). μ_N, ν_N: independent bits with
P(1) = 1/2 ± γ for the first N positions, fair afterwards. π₋ = ¼μ + ¾ν, π₊ = ¾μ + ¼ν. For every
semimeasure A through depth N with A(ε) = 1 and every η ∈ [0, 2^-20]: s± = (1−η)π± + ηA. Bayes 0-1 action
at h is `true` iff s(h1) ≥ s(h0) (ties to true; the book allows any tie rule and the referee showed the
ordering holds for every tie rule). L_N^s = Σ_{n<N} E_μ[0-1 loss of the action at step n+1]. Claim:
√N/32 ≤ L^{s₋} − L^{s₊} ≤ √N/16 under μ_N, with every per-step difference ≥ 0. Constants are absolute.
The statement was frozen after the proof arrived (Pro wrote both in query 010); it is the statement
below, compared line by line with 008 §2 by the desk on 2026-11-21.
-/
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
  sorry

end RobustExperiment
