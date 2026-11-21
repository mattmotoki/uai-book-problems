# Prize problems

Source: Hutter's book page, https://www.hutter1.net/ai/uaibook.htm#prizes (read 2026-11-20)
(<https://www.hutter1.net/ai/uaibook.htm#prizes>). The page says prizes "may be
split or reduced or withdrawn if the solution was essentially already published".
Full problem text: the 2005 book (see `docs/sources/BOOKS.md`); problem pages with the definitions they cite
are in `uai2005-prize-pages.pdf` on the SSD (36 pages, PDF pages 64-70, 79-82, 87-99, 105-106, 137-141, 207-209, 224-225).

Column "Later work" comes from a ChatGPT Pro chat of 2026-11-20
(<https://chatgpt.com/c/6b004200-231c-83ec-a2d6-aae16dbbb519>). It is unverified.

| Problem | Prize (page) | Page text | Later work (chat, unverified) |
|---|---|---|---|
| 2.3 Martin-Löf random sequences and convergence (also 3.10) | €100 | Build a universal semimeasure with posterior convergence on every ML-random sequence; "universal" in sense (a), (b) or (c) | Lattimore-Hutter 2015: impossible for (b) and (c). (a) left open. |
| 2.7 Lower convergence bounds and defect of M | €100 | Lower bound for M_norm like the one for M, or an upper bound better than O(2^-K(t)) | No resolution found. Note: the page also says "Solutions to Problems 2.5 and 2.6u and 2.7u have been TeXed (2005)"; check what part that covers. |
| 2.9 Prediction of selected bits | €100 + €100 | M_norm question, plus general computable selection rules | Page: "This problem has now been solved [P11evenbits]". |
| 3.3 Comparing two mixtures | €50 | Book [C05u/C40o]: two mixtures ξ, ξ' over M; known part Σ_t E[(ξ−ξ')²] ≤ 2[ln w_μ⁻¹ + ln w'_μ⁻¹] and L^ξ − L^ξ' ≤ O(√L). Open: is L^ξ − L^ξ' < ∞? | Status unknown. Known part = calibration C1. |
| 6.2 Prediction loss bounds for AIXI | €100-500 | Non-asymptotic value bounds or related optimality; prize depends on progress | Leike-Hutter 2015 negative results limit the possible theorems. |
| 6.3 Posterization of prediction errors | €100 | Title only | Chernov-Hutter 2005 posterior bounds refer to it. Check what remains. |

Next facts to get: the book's exercise text for 2.3, 2.7, 3.3, 6.3; Hutter's current
view of which prizes stand (ask him by email only after Matt decides).

## Status map, Pro query 001 (2026-11-20; `pro/001-status-map.a.md`)

Pro opened the primary papers; claims below are Pro's until a Lean proof or our own reading confirms them.

| Problem | Pro's status | Named open target | First formal target |
|---|---|---|---|
| 2.3 | (b), (c) negative: Lattimore-Hutter TCS 2015, incl. normalized. Classes: Wood-Sunehag-Hutter 2013 (B = C ⊊ A). | **2.3A**: some dominant enumerable q converges (difference sense) on every ML-random path of every computable μ. | Eventual proportionality lemma (bridge). |
| 2.7 | Deterministic normalized error is Θ(2^-K(t)) (from Leike-Hutter 2015 lemmas). Uniform all-history stochastic lower bound is false (symmetrized prior). | Expected-error lower bound: needs exact quantifiers first. | **2.7F**: NM(b|x) ≥ c·2^-K(|x|+1) for every dominant M. |
| 2.9 | Solved (Lattimore-Hutter-Gavane 2011; Bauwens-Kuznetsov 2026 rates). Upstream Lean claims a linear bound the preprint calls unknown. | Stochastic and partial-rule extensions. | Reproduce upstream `SelectedBits` endpoints; prior-comparison adapter. |
| 3.3 | **Pro's counterexample**: two-element class of computable Bernoulli products, δ_t = 1/(32t), weights 1/4 vs 3/4, 0-1 loss; L^ξ− − L^ξ+ ≥ (1/32)Σ1/t → ∞. Not found in literature. | Negation of the natural claim. | Lean proof of the counterexample (finite probability only). |
| 6.2 | Longer horizons and stochastic passive cases fail (dogmatic-prior deductions). | **6.2P**: polynomial bound in K_m(z) for horizon 1, deterministic z, every U. | Horizon-2 counterexample. |
| 6.3 | Uniform ratio M(x)/M(xy) ≤ C·2^K(y|x) is false; with K(|x|) factor it is known (Chernov-Hutter). | **6.3N**: E_{k:n} ≤ C·M(z_<k)/M(z_1:n) for the greedy active policy. | Formalize the ratio counterexample. |

Pro's ranking by progress per effort: 3.3, 2.7, 6.3, 2.9, 6.2, 2.3.
Library caution from Pro: upstream `IsContinuousTreeSemimeasure` needs root mass exactly 1; the book allows ≤ 1.

## Reproduced locally

- 2026-11-20: upstream `Kolmogorov.SelectedBits.square_loss_le_index_complexity` and
  `power_loss_summable_le_index_complexity` build on our Mac at the pinned commit and use only the three
  standard axioms (`HutterPrizes/Reproduce.lean`, `scripts/check.sh`). Statement: for the canonical M, a
  constant C (after U, before all data) bounds the forced-position square loss by K(e) + C for every
  decidable prefix tree with index e and every branch. Bauwens-Kuznetsov (arXiv 2610.18632v2) call a
  polynomial bound unknown; reconciling the two is open (check definitions of "forced" and of the error).
- 2026-11-20: Monte Carlo of the 3.3 counterexample (`scripts/sim/p33_mc.py`, 200k paths, n ≤ 4000,
  `uv run --with numpy python scripts/sim/p33_mc.py`): L^ξ− − L^ξ+ = 0.18, 0.32, 0.47, 0.55 at n = 10, 100,
  1000, 4000; exactly 2·Σδ_t, twice Pro's lower bound. It grows like (1/16)·ln n: unbounded, but slowly.

## Results (Lean-checked; fidelity review in `docs/reviews/2026-11-20-fidelity-33-27F.md`)

| Result | Lean | Fidelity | Claim we can make |
|---|---|---|---|
| 3.3: Σ-loss difference of two mixtures is unbounded | `MixtureCounterexample.counterexample` | faithful (finite class, 0-1 loss) | "No" to "is L^ξ − L^ξ' < ∞?" for general M; not for universal mixtures over M_U. Novelty unchecked beyond Pro's search. |
| 2.7F: M_norm(b|x) ≥ 2^-(K(t)+C) | `HutterPrizes.normalized_lower_bound` | faithful, deterministic reading only | Normalized predictor still errs ≳ 2^-K(t) on deterministic sequences. KNOWN: follows from Hutter 2007 (arXiv 0709.1516, eq. 17) plus normalization (Pro 020b, Thm 10). |
| 6.3R: M(x)/M(xy) ≤ C·2^K(y|x) fails uniformly | `HutterPrizes.uniform_conditional_ratio_fails` | statement frozen by desk (`Targets/P63R.lean`) | Rules out one route to 6.3; does not refute the error-count bound. Known with a K(|x|) factor (Chernov-Hutter). |
| 3.3 core: robust finite experiment (008 Thm 3) | `RobustExperiment.theorem3` | desk compared with 008 §2; referee 2026-11-21 | For every semimeasure background A and η ≤ 2^-20: √N/32 ≤ L^{s₋} − L^{s₊} ≤ √N/16. |
| 3.3 aggregation (008 Thm 4, no computability) | `RobustExperiment.Theorem4.theorem4_statement` | desk compared with 008 §3 | For every positive semimeasure M: ξ± = (1−η)(mix of P, Q) + ηM dominate ηM and n^{1/4}/256 ≤ L^ξ₋ − L^ξ₊ ≤ n^{1/4}/8. |
| **3.3 effective capstone** | `P33Effective.effective_counterexample`, `P33Effective.loss_gap_tendsto_atTop` | faithful with caveats (`docs/reviews/2026-11-21-fidelity-33-effective.md`) | Two universal lower-semicomputable continuous semimeasures ξ₋, ξ₊ (dominating every such semimeasure) and a computable measure μ (rational conditionals) with L^ξ₋_n − L^ξ₊_n ≥ n^{1/4}/256 → ∞. |
| **6.3E: E_{k:n} ≤ C·2^{K(z_{k:n}|z_{<k})} fails** | `HutterPrizes.errorcount_complexity_bound_fails`, `HutterPrizes.no_errorcount_complexity_bound` | faithful with caveats (`docs/reviews/2026-11-21-fidelity-63E.md`): refutes the end of the chain; 6.3N and the K_* version stay open | For every optimal U there is b such that every predictor P (incl. AIξ) makes ≥ d−1 errors on some y with K(y|x) ≤ b; so no C works. |
| **3.3 as two Bayes mixtures** | `P33Mixture.mixture_counterexample` | faithful with caveats (`docs/reviews/2026-11-21-fidelity-33-mixture.md`); ties toward 1 | Two Bayes mixtures Σ w±_i ν_i over the full upstream enumeration ν = `treeLSCEnum` of lsc semimeasures (weights positive, Σ = 1, ratio ≤ 3 coordinatewise), both lsc; the true computable μ is ν_j; L^ξ₋_n − L^ξ₊_n ≥ n^{1/4}/256 → ∞. |
| C1: known part of 3.3 | `HutterPrizes.two_semimeasures_sum_sq_le` | calibration | none (known) |

## Research answers (Pro, not Lean-checked)

- **007, 3.3 with universal mixtures** (`pro/007-p33-universal.a.md`): Pro proves a lift to two full-support
  mixtures over *all computable measures* (priors agree except swapped μ, ν weights; ratio within 3):
  (1/32)H_n ≤ L^ξ− − L^ξ+ ≤ (1/16)H_n. Caveat: the enumeration of computable measures is non-effective,
  so the priors are not lower semicomputable; Solomonoff priors and priors ≍ 2^-K(ρ) are NOT covered. Also:
  "rest's posterior vanishes" is false (fair coin is equivalent to μ here); a small common background can
  make the difference finite. Finite difference holds under a decision margin, log loss, squared loss.
- **006b, 2.3A** (`pro/006-p23a-research.a.md`; first attempt 006 hit a ChatGPT safety-filter false
  positive): not solved. The Lattimore-Hutter proof needs an effective subtraction (q − c·ν enumerable);
  Prop. 1: dominance alone does not give it. Fixed mixtures with W cannot repair failures; several damping
  constructions fail. Positive partial: for every q ∈ 𝒜, on sequences computably random relative to ∅′,
  cumulative conditional KL is finite (so normalized convergence there). Pro claims no novelty.
- **008, 3.3 with effective priors** (`pro/008-p33-effective-priors.a.md`): Pro claims a full effective
  counterexample: a computable μ (randomly picks one finite experiment, then fair bits) and two universal
  mixtures with computable weights (ratio in [1/3, 3]), including two actual Solomonoff priors M_U, M_V,
  2^-K-comparable priors, and M_U vs ξ_U, with n^{1/4}/256 ≤ L^ξ− − L^ξ+ ≤ n^{1/4}/8. Core: Theorem 3, a
  finite experiment whose gap survives any semimeasure background of weight η ≤ 2^-20. Status: referee
  (Claude Opus, `docs/reviews/2026-11-21-referee-008.md`): correct with minor gaps, none fatal. Theorem 3 is
  Lean-checked (`HutterPrizes/P33Theorem3.lean`, `RobustExperiment.theorem3`). Theorem 4 aggregation (n^{1/4} gap
  over every positive background semimeasure M) is Lean-checked (`HutterPrizes/P33Theorem4.lean`). Left: the
  computability layer (query 014). Antecedent: Hutter JMLR 2003
  p. 988 (one mixture's regret vs μ diverges; no two-mixture comparison).
- **009, 2.3A** (`pro/009-p23a-next.a.md`): not solved. Every q ∈ 𝒜 has near-total relative defects densely
  (but the witnesses leave every deficiency layer); no enumerable universal semimeasure has an
  lsc defect; a family Q_K ∈ 𝒜 \ 𝒞 is exactly additive on a whole bounded-deficiency layer; exact
  reductions to well-foundedness of computable trees. Follow-up 011 running.
- **011, 2.3A** (`pro/011-p23a-reduction.a.md`): not solved. Weighted sums of envelopes fail when the base is
  an effective universal mixture (and for some non-mixture bases). Depth-growing thresholds converge on all
  fair-coin randoms but lose dominance. The fair-coin case reduces to one "integer-flow lemma" (§5).
  Novelty corrections: the near-total-defect argument, the envelope operator and Prop. 8 are known.
- **013, 2.3A** (`pro/013-p23a-go-lemma.a.md`, fresh chat): the GO(P) reduction is valid; GO(P) not settled.
  The counting bound alone does not decide it; GO holds for o(λ) perturbations of universal mixtures; a
  ∅′-computable measure dominating ξ/2 predicts correctly on all fair-coin randoms but cannot be lsc.
  Desk: 2.3A is parked after four rounds without a step toward a full answer; return with a new idea.
- **015, 6.3** (`pro/015-p63-research.a.md`; book pages attached): easy parts proved (ξ^AI ≳ ξ^SP, reverse
  fails, (E_{k:n}+1)·c·M(xy) ≤ ξ^AI(h_m)). (6.3N) open; corrected by a factor (m+1)·2^{K(m)}. The last question
  (E_{k:n} ≲ 2^{K(z_{k:n}|z_{<k})}) is FALSE for every deterministic predictor (Thm 5: x = 0^m, y = 0^{2^d−m}b,
  b adversarial, m = bin(b)); corrected bound C·2^{K(m)+K(y|x)} holds. Antecedent: Chernov-Hutter ALT 2005
  Lemma 5 (same length trick, one-step deviation of M). Lean target `Targets/P63E.lean`, query 016.
- **017, 6.3N** (`pro/017-p63n-followup.a.md`): passive SP predictor: E ≤ log₂(M(x)/M(xy)) (halving; the book's
  argument), sharp. Active AIξ: still open; a fixed universal AI prior can have large AI/SP mass separation on
  its own greedy path, but that does not give cheap errors. Desk: 6.3N parked.
- **019, 6.2(d)** (`pro/019-p62p-research.a.md`): (6.2P) open. Leike-Hutter 2015 §6.1 explicitly exclude horizon 1
  ("if we have a constant horizon of 1, AIXI does succeed in sequence prediction"). Pro: two polynomial comparison
  theorems and a linear bound for a forced initial segment; no fixed-U superpolynomial counterexample. Desk: parked.
- **020b, 2.7 stochastic** (`pro/020-p27-expected.a.md`; first try blocked by the safety filter): Thm 1: for every
  M ∈ 𝒜 and every computable μ, ∃c, n₀ ∀n ≥ n₀ ∃t ∈ (2^n, 2^{n+1}]: E_μ Σ_b|NM − μ| ≥ c·2^{-K(t)} and
  E_μ Σ_b(NM − μ)² ≥ (c²/2)·2^{-2K(t)} (infinitely often; "for all large t" open). Thm 2: for uniformly
  nondegenerate μ (fair coin) S_t ≥ c·2^{-K(t)} i.o. Thm 5: no computable pointwise expected rate. Thm 6: for a
  genuine Solomonoff prior and fair coin, no upper bound O(2^{-αK(t)}) for any α > 0. Thm 8: expected defect
  can vanish eventually in 𝒜. Thm 10: 2.7F is known (Hutter 2007 eq. 17). Novelty: Thms 1, 2, 6 not found in print (docs/reviews/2026-11-21-novelty.md). Referee: Thms 1, 2, 6 correct with
  minor gaps (`docs/reviews/2026-11-21-referee-020b.md`). Lean: `P27.block_bound_of_joint` (021) proves (15) exactly: with Q(x) ≤ 2µ(x) on G, µ(G) ≥ ½,
  Q(xz) ≥ α µ(x), µ(xz) ≤ (α/4) µ(x) ⇒ Σ_{t=r+1}^{r+ℓ} A_t ≥ α/4 (α = a w_n); plus `hybrid_inequality` (14).
  The desk's own question had wrong constants; `literal_block_claim_false` refutes that form.
- **2.7 stochastic, Theorem 1 in Lean** (022): `P27Stochastic.expected_lower_bound_io` proved; statement identical
  to `Targets/P27Stochastic.lean` (fidelity: faithful with caveats). Claim: for every optimal U, every universal
  lsc semimeasure M and every computable µ with rational conditionals, ∃c > 0 such that in every late dyadic block
  some t has E_µ L1 error of M_norm ≥ c·2^{-K(t)} and squared error ≥ (c²/2)·2^{-2K(t)}. Partial answer to the
  first question of 2.7; every-large-t open; equality question not addressed. Novelty: not found in print.
- **023, 2.7 eventual** (`pro/023-p27-eventual.a.md`, referee `docs/reviews/2026-11-21-referee-023.md`: correct):
  (E) open. Witnesses A_t ≥ c·w_t in every infinite c.e. set of times and in every late O(log t) window, for every
  computable µ; S_t ≥ c·w_t for nondegenerate µ; quiet times of a counterexample form an immune set. Lean: Lemma 1 =
  `P27.selective_forcing` (024; desk check: statement matches (5)-(7), time t ↔ history length t−1; no full
  support needed). Next Lean: Lemma 3, then the c.e.-selection theorem (needs computable-real conditionals).
- **2.7 selection, in Lean** (025): `P27Selection.selection_lower_bound` (every computable increasing selection of
  times; every late block of 6⌈log₂(n+2)⌉ selected times has a witness A_t ≥ c·w_t, S_t ≥ (c²/2)·w_t²) and
  `P27Selection.log_window_lower_bound` (a witness in every late window [u, u + C·(log₂(u+2)+1)]); statements
  identical to `Targets/P27Selection.lean` (review: faithful with caveats). Rational conditionals. (E) open.
- **2.7 (E) "every large t" parked** (2026-11-21): no proof or counterexample in 020b §4 and 023. Record: a
  counterexample's quiet times (A_t/w_t → 0) form an immune set, and quiet runs are at most C·log t long.
- **2.7 upper-bound side, in Lean** (026): `P27Spikes.no_power_upper_bound_mix` (for every universal V there is an
  lsc ν such that ½V + ½ν is universal and, for the fair coin, S_t and A_t exceed C·2^{-αK(t)} infinitely often for
  every α > 0, C) and `no_power_upper_bound`; statements identical to `Targets/P27Spikes.lean` (review: faithful
  with caveats); names checked with pp.fullNames. M ∈ 𝓑 is a paper step (Wood-Sunehag-Hutter).
- **3.3 with complexity priors, in Lean** (028): `P33Complexity.complexity_counterexample`: weights within constant
  factors of 2^{-K(i)} (K of the index), Σ ≤ 1, ratio [1/3, 3], gap ≥ n^{1/4}/256 → ∞; statement identical to
  `Targets/P33Complexity.lean` (review: faithful with caveats); names checked with pp.fullNames.
- **Closed lead (2026-11-21): known.** CHS07 Lemma 5 proof gives KM(0^ℓ1) − KM(0^ℓ) ≥ K(ℓ) − O(1), so the constant version of 2.6(ii) fails for every K̃; Hutter lists 2.6 solved (Chernov–Hutter 2005). Our Prop 4.4 is a weaker Lean form. Original note: Problem 2.6(ii) (book p. 61) asks whether the
  constant version of an upper bound holds; our 6.3R example (x = 0^ℓ, K̃(1|0^ℓ) bounded) may answer it negatively
  for every K̃ variant. Check against Chernov-Hutter 2005 (the prize page marks 2.6 solved) before any claim.
- **3.3 over computable probability measures, in Lean** (029): `P33Measures.measure_class_counterexample`: class C of
  measures with total computable rational conditionals; for every positive normalized prior a on C, priors w± ≥ 2^-20 a,
  sums 1, ratio [1/3, 3], gap ≥ n^{1/4}/256 → ∞. Statement identical to `Targets/P33Measures.lean` (review: faithful
  with caveats); names checked. All computable measures and exact 2^-K priors (027 Thm 4): paper steps.
- **3.3 with exact 2^{-K(i)} weights, in Lean** (030): `P33Exact.exact_counterexample`: a computable renumbering τ of
  `treeLSCEnum` and two optimal prefix machines C±; ξ± = Σ 2^{-K_{C±}(i)} τ_i universal lsc semimeasures, per-index weight
  ratio ≤ 4, gap ≥ n^{1/4}/512 (n ≥ 3) → ∞. Statement identical to the target (review: faithful with caveats); names checked.
