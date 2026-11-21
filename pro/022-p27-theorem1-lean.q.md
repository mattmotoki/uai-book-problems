# Lean 4: prove the frozen target `P27Stochastic.expected_lower_bound_io` (Problem 2.7, stochastic)

Environment: Lean v4.35.0, Mathlib v4.35.0, and the library kolmogorov-complexity-lean
(https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean, commit 17c50e560c337a8a702f8850a711f80a56b3cf91,
imported as `KolmogorovMathlib.*`). No `sorry`, `admit`, new axioms or `native_decide`.

Goal: a complete Lean proof of the theorem in the attached `P27Stochastic.lean` (Targets), with its statement
layer unchanged character for character (we diff it). It formalizes Theorem 1 of your earlier report (attached
`020-p27-expected.a.md`, §2). A fresh review found the statement faithful and plausibly true; its notes are
at the end of the target file.

Already proved and compiled (attached, import them, do not re-prove):
- `HutterPrizes/P27BlockBound.lean`: `P27.block_bound_of_joint` is exactly (15) for finite `P27.Model`s:
  with Q(x) ≤ 2µ(x) on G, µ(G) ≥ ½, Q(xz) ≥ α µ(x), µ(xz) ≤ (α/4) µ(x) ⇒ Σ_{t=r+1}^{r+ℓ} A_t ≥ α/4.
  Also `good_prefix_mass` (10) and `hybrid_inequality` (14).
- `HutterPrizes/P27F.lean`: the deterministic sibling; its `cutoffFamily_uniform` shows how to prove
  `IsUniformlyLowerSemicomputableTreeFamily` for a concrete family.

Upstream lemmas that cover Step 2 and help with (16):
- `Kolmogorov.exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree U hU ν hν hfree :
  ∃ C, ∀ e x, 2⁻¹ ^ ((KPNat U e).toNat + C) * ν e x ≤ universalContinuousSemimeasure x`
  (Solomonoff/Domination/UniformFamily.lean). Use it with ν n = your Step-1 environment ν_n; transfer to a
  general universal `a` via `IsUniversal a` applied to `universalContinuousSemimeasure`.
- `KPPlain_le_of_tsum_two_pow_neg_ne_top` (Prefix/UpperSemicomputableBound.lean, SUV Thm 62) for the coding
  step (16): Σ_{t∈(2^n,2^{n+1}]} 2^{-K(t)} ≤ C·2^{-K(n)}.
- `KPNat_ne_top`, `universalContinuousSemimeasure_isMaximal`, `normalizedSiblingProb`
  (Solomonoff/SelectedBits/Basic.lean).

Suggested structure (change it if you have a cleaner route, and say why):
- Part A, a conditional theorem: from (i) uniform domination a ≥ a₀·2^{-K(n)}·ν_n, (ii) the tail bound (7),
  (iii) the coding bound (16) and (iv) (2/3)^{2^n} ≤ a₀·2^{-K(n)}/4 eventually, derive the conclusion using
  `P27.block_bound_of_joint`. This needs a bridge from `muProb`/`normalizedSiblingProb` to `P27.Model`
  (Q(x) ≥ a(x) for the normalized measure, (5) in your report).
- Part B: discharge (i)-(iv). Step 1 is exact here, since µ has computable rational conditionals.

Return one Lean code block for a new file `HutterPrizes/P27Stochastic.lean` (namespace `P27Stochastic`; you may
split helper lemmas into more files if you return each in full), then a list of any deviation. If you find the
target false as stated, say so and prove the negation instead.
