/-
Target 6.3E (Hutter 2005, Problem 6.3, last question, book p. 208): "Is it possible ... to bound the
expression by ≈ 2^{K(z_{k:n} | z_{<k})} (cf. Problem 3.13)?" Read as an error-count bound: the number of
prediction errors E_{k:n} in cycles k..n is at most C·2^{K(z_{k:n} | z_{<k})}, with C independent of n, k, z.

Fidelity note.
- K(y | x) is ordinary conditional prefix complexity (Problem 3.13 posterizes K(ν) to K(ν | x_{<k})); in the
  library `KP U y x` = K(y | x) for an optimal prefix decompressor U.
- The AIξ policy in the SP setting is deterministic (fixed tie rule); it induces a predictor
  P : BitString → Bool (next-bit guess after the true prefix). The target quantifies over EVERY P, so it
  covers the AIξ policy for every U, computable or not.
- `errors P x y` counts j < |y| with P(x ++ y_{<j}) ≠ y_j: errors while predicting y after observing x.
  With x = z_{<k}, y = z_{k:n}: errors P x y = E_{k:n}.
- Claim (Pro 015, Theorem 5): one constant b (depending on U only) works for every P and every d.
  Antecedent: Chernov-Hutter ALT 2005 (arXiv cs/0507041) Lemma 5 uses the same length trick
  (x = 0^l) to show one-step deviation of M can be ≥ K(l) ln 2 while K(μ|x) = O(1); it is not an
  error-count statement over all predictors.
-/
import KolmogorovMathlib.Solomonoff.Basic

namespace HutterPrizes

open Kolmogorov

/-- Number of wrong next-bit guesses of `P` while it predicts `y` after observing `x`. -/
def errors (P : BitString → Bool) (x y : BitString) : ℕ :=
  ((List.range y.length).filter (fun j => P (x ++ y.take j) != y.getD j false)).length

/-- A common upper bound for the codes of all words of length `d`. -/
def blockBound (d : ℕ) : ℕ :=
  Encodable.encode (List.replicate d true)

lemma encode_le_blockBound (b : BitString) :
    Encodable.encode b ≤ blockBound b.length := by
  induction b with
  | nil => simp [blockBound]
  | cons a b ih =>
      simp only [List.length_cons, blockBound, List.replicate_succ,
        Encodable.encode_list_cons]
      apply Nat.succ_le_succ
      have ha : Encodable.encode a ≤ Encodable.encode true := by cases a <;> decide
      have hleft : Nat.pair (Encodable.encode a) (Encodable.encode b) ≤
          Nat.pair (Encodable.encode true) (Encodable.encode b) :=
        (show StrictMono (fun n => Nat.pair n (Encodable.encode b)) from
          fun _ _ h => Nat.pair_lt_pair_left _ h).monotone ha
      have hright : Nat.pair (Encodable.encode true) (Encodable.encode b) ≤
          Nat.pair (Encodable.encode true) (blockBound b.length) :=
        (show StrictMono (fun n => Nat.pair (Encodable.encode true) n) from
          fun _ _ h => Nat.pair_lt_pair_right _ h).monotone ih
      exact hleft.trans hright

/-- Total decoding, with the empty word as the default for an invalid code. -/
def lengthDecode (n : ℕ) : BitString :=
  (Encodable.decode (α := BitString) n).getD []

/-- Recover a word from the input length and pad to its common block endpoint. -/
def lengthContinuation (x : BitString) : BitString :=
  let b := lengthDecode x.length
  List.replicate (blockBound b.length - x.length) false ++ b

lemma blockBound_primrec : Primrec blockBound := by
  exact Primrec.encode.comp (Primrec.list_replicate.comp Primrec.id (Primrec.const true))

lemma lengthDecode_primrec : Primrec lengthDecode := by
  exact Primrec.option_getD.comp (Primrec.decode (α := BitString))
    (Primrec.const ([] : BitString))

lemma lengthContinuation_computable : Computable lengthContinuation := by
  have hb : Primrec (fun x : BitString => lengthDecode x.length) :=
    lengthDecode_primrec.comp Primrec.list_length
  have hn : Primrec (fun x : BitString => blockBound (lengthDecode x.length).length) :=
    blockBound_primrec.comp (Primrec.list_length.comp hb)
  exact (Primrec.list_append.comp
    (Primrec.list_replicate.comp (Primrec.nat_sub.comp hn Primrec.list_length)
      (Primrec.const false)) hb).to_comp

lemma lengthContinuation_replicate (b : BitString) :
    lengthContinuation (List.replicate (Encodable.encode b) false) =
      List.replicate (blockBound b.length - Encodable.encode b) false ++ b := by
  simp [lengthContinuation, lengthDecode, Encodable.encodek]

lemma errors_cons (P : BitString → Bool) (x y : BitString) (a : Bool) :
    errors P x (a :: y) = (if P x != a then 1 else 0) + errors P (x ++ [a]) y := by
  simp only [errors, List.length_cons, List.range_succ_eq_map]
  simp only [List.filter_cons, List.take_zero, List.append_nil, List.getD_cons_zero]
  rw [List.filter_map]
  simp only [Function.comp_def, List.take_succ_cons, List.getD_cons_succ,
    List.singleton_append, List.append_assoc]
  split <;> simp_all [Nat.add_comm]

/-- Error counts add when a continuation is split into two pieces. -/
lemma errors_append (P : BitString → Bool) (x u v : BitString) :
    errors P x (u ++ v) = errors P x u + errors P (x ++ u) v := by
  induction u generalizing x with
  | nil => simp [errors]
  | cons a u ih =>
    simp only [List.cons_append, errors_cons, ih, List.append_assoc,
      List.nil_append, Nat.add_assoc]

lemma errors_suffix_le (P : BitString → Bool) (x u v : BitString) :
    errors P (x ++ u) v ≤ errors P x (u ++ v) := by
  rw [errors_append]
  omega

/-- Every predictor has a length-`d` continuation on which every guess is wrong. -/
lemma exists_adversarial_tail (P : BitString → Bool) (x : BitString) (d : ℕ) :
    ∃ b : BitString, b.length = d ∧ errors P x b = d := by
  induction d generalizing x with
  | zero => exact ⟨[], rfl, by simp [errors]⟩
  | succ d ih =>
    obtain ⟨b, hb, he⟩ := ih (x ++ [!P x])
    refine ⟨(!P x) :: b, by simp [hb], ?_⟩
    rw [errors_cons, he]
    have h : (P x != !P x) = true := by cases P x <;> rfl
    simp [h, Nat.add_comm]

lemma errors_zeros_suffix_le (P : BitString → Bool) (m N : ℕ) (hm : m ≤ N)
    (b : BitString) :
    errors P (List.replicate N false) b ≤
      errors P (List.replicate m false) (List.replicate (N - m) false ++ b) := by
  have h := errors_suffix_le P (List.replicate m false)
    (List.replicate (N - m) false) b
  simpa [← List.replicate_add, Nat.add_sub_of_le hm] using h

theorem errorcount_complexity_bound_fails (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ b : ℕ, ∀ P : BitString → Bool, ∀ d : ℕ, ∃ x y : BitString,
      KP U y x ≤ b ∧ d ≤ errors P x y + 1 := by
  obtain ⟨c, hc⟩ := KP_map_self_le U hU lengthContinuation lengthContinuation_computable
  refine ⟨c, ?_⟩
  intro P d
  obtain ⟨b, hb, he⟩ := exists_adversarial_tail P (List.replicate (blockBound d) false) d
  let m := Encodable.encode b
  let x : BitString := List.replicate m false
  let y : BitString := List.replicate (blockBound d - m) false ++ b
  have hm : m ≤ blockBound d := by
    simpa [m, hb] using encode_le_blockBound b
  have hF : lengthContinuation x = y := by
    simpa [x, y, m, hb] using lengthContinuation_replicate b
  refine ⟨x, y, ?_, ?_⟩
  · rw [← hF]
    exact hc x
  · have h := errors_zeros_suffix_le P m (blockBound d) hm b
    rw [he] at h
    change d ≤ errors P x y at h
    omega

theorem no_errorcount_complexity_bound (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : BitString → Bool) :
    ¬ ∃ C : ℕ, ∀ x y : BitString, ∀ k : ℕ, KP U y x ≤ k → errors P x y ≤ C * 2 ^ k := by
  rintro ⟨C, hC⟩
  obtain ⟨b, hb⟩ := errorcount_complexity_bound_fails U hU
  obtain ⟨x, y, hK, he⟩ := hb P (C * 2 ^ b + 2)
  have h := hC x y b hK
  omega

end HutterPrizes
