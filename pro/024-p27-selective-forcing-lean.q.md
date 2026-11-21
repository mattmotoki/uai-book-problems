# Lean 4: Lemma 1 (selective forcing) of report 023

Environment: Lean v4.35.0, Mathlib v4.35.0 (plain Mathlib is enough). No `sorry`, `admit`, new axioms or
`native_decide`.

Goal: formalize and prove Lemma 1 of your attached report `023-p27-eventual.a.md` (§2, eqs. (5)-(13)), exactly as
stated there: P, Q laws on {0,1}^N with kernels p, q; a selected set F ⊆ {1..N} with |F| = m; prescribed bits f_t(x)
with p(f_t(x)|x) ≤ ρ < 1; ν follows P off F and outputs f_t(x) on F; if Q(z) ≥ r ν(z) for all |z| = N (0 < r ≤ 1),
then Σ_{t∈F} A_t(P,Q) ≥ 2(r − ρ^m). A referee checked the proof and found it correct; it noted that full support
of P is not needed, only q > 0 where you divide (state the hypotheses you actually use, and say so).

Build on the attached compiled file `P27BlockBound.lean` (namespace `P27`): reuse `History`, `Model`, `prob`,
`stepError`, `A`, `l1`, `hybrid_inequality`, `two_mul_gap_le_l1`; import it, do not copy it. Time t in the report
corresponds to `A μ Q t` there (history length t − 1). Represent F as a `Finset ℕ` of times in [1, N] and the
prescribed bits as `f : (n : ℕ) → History n → Bool`.

Return: Part 1 (statement layer: ν as a `Model`, the hypotheses, the theorem), Part 2 (proofs), in one Lean code
block for a new file `HutterPrizes/P27SelectiveForcing.lean` (namespace `P27`); then a map from each hypothesis to
(5)-(6) and a list of deviations. If the lemma is false as you state it, give the counterexample in Lean.
