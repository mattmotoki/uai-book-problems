# Lean 4: prove the frozen target `Targets/P27Spikes.lean` (Problem 2.7, upper-bound side)

Environment: Lean v4.35.0, Mathlib v4.35.0, kolmogorov-complexity-lean
(https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean, commit 17c50e560c337a8a702f8850a711f80a56b3cf91).
No `sorry`, `admit`, new axioms or `native_decide`.

Goal: complete Lean proofs of `P27Spikes.no_power_upper_bound_mix` and `P27Spikes.no_power_upper_bound` in the
attached target, with its statement layer unchanged character for character (we diff it). They formalize Theorem
6 of your report `020-p27-expected.a.md` §6 (stopping lengths B(n), Elias-gamma weights, the asymmetric stopping
semimeasures ν_{L,i}, the comparison (45)-(48), the pigeonhole over i). A referee and a fidelity reviewer found
the proof and the target correct; review notes are at the end of the target file. The plain theorem should
follow from the mixture form with V = `universalContinuousSemimeasure`.

Hints from the reviewers:
- B(n) = max{j : K_U(j) ≤ n} uses the same `U` as `w`, so K(t_n) > n holds exactly for t_n = B(n) + 1. Its lower
  approximation can come from `isUniformlyLSC_complexityWeight_KPNat U hU`; use a strict test (approximation
  > 2^{-(n+1)}) because the supremum 2^{-n} need not be reached.
- ν_i(ε) = Σ_{n≥1} γ_n = 1, so ν_i and ½V + ½ν_i are root-1; ½V + ½ν_i ≥ ½V gives `IsUniversal`.
- For the fair coin, S_t ≤ A_t at every t, so the A_t conjunct follows from the S_t conjunct.
- The pigeonhole gives one i ∈ {0,1} for infinitely many n, and (49) has no α, so one ν serves every α.

Already compiled (attached; import, do not re-prove): `HutterPrizes/P27Stochastic.lean` (definitions `w`,
`expAbsErr`, `expSqErr`, `muProb`; bridges to normalized predictions).

Return one Lean code block for a new file `HutterPrizes/P27Spikes.lean` (namespace `P27Spikes`; extra helper
files are fine if you return each in full), then a list of deviations. If the target is false as stated, say so
and prove the negation.
