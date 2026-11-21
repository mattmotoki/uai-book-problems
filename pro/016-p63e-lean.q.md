# Lean 4: prove the frozen target `Targets/P63E.lean` (error-count bound by 2^{K(y|x)} fails)

Environment: Lean v4.35.0, Mathlib v4.35.0, https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean at
commit 17c50e560c337a8a702f8850a711f80a56b3cf91 (namespace `Kolmogorov`, `BitString = List Bool`,
`KP U x y` = K(x | y)).

Attached: `P63E.lean` (the frozen statement with two `sorry`s and a fidelity note) and `P63R.lean` (compiles;
it uses the upstream lemma `KP_map_self_le U hU f hf : ∃ C, ∀ x, KP U (f x) x ≤ C` for computable f).

Prove both theorems without changing their statements or the definition of `errors`. Math (from an earlier
answer): fix d ≥ 1 (d = 0 is trivial), N = 2^d. Build b ∈ {0,1}^d with b₁ = 1 and
b_j = ¬P(0^N b_{<j}) for j ≥ 2. Let m be the number with binary representation b (so 2^{d−1} ≤ m < 2^d).
x = 0^m, y = 0^{N−m} b. Then xy = 0^N b, so P errs at the last d−1 positions of y. A fixed computable F
maps x to y: m = |x|, b = binary(m), d = |b|, output 0^{2^d − m} ++ b. So KP U y x ≤ b_U by `KP_map_self_le`.
The second theorem follows from the first (take d > C·2^{b_U} + 1).

Requirements: one Lean file `HutterPrizes/P63E.lean` (namespace `HutterPrizes`) with the statements exactly
as in the target plus your helper lemmas; no `sorry`, `admit`, new axioms or `native_decide`. The
computability of F is the main technical work; Mathlib's `Nat.bits`/`Nat.binaryRec` or a primrec encoding
are fine, as is any equivalent F, as long as it is `Computable`. Return the whole file in one Lean code block,
then a short note on any deviation.
