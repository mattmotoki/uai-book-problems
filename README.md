# Prize problems from Hutter's *Universal Artificial Intelligence*, checked in Lean 4

This repository holds the Lean 4 proofs, the frozen statements, the review notes and the paper for

> Matt Motoki, *Answers to three prize problems from Hutter's Universal Artificial Intelligence*
> (paper source in `docs/paper/`).

The problems are from M. Hutter, *Universal Artificial Intelligence* (Springer, 2005); the list with prizes is at
https://www.hutter1.net/ai/uaibook.htm#prizes.

## Results

| Problem | Result | Lean theorem |
|---|---|---|
| 3.3 | Two Bayes mixtures over the computable probability measures (rational conditionals), priors within a factor 3: the µ-expected 0-1 loss difference is ≥ n^{1/4}/256 and tends to ∞ | `P33Measures.measure_class_counterexample` |
| 3.3 | The same over all lower semicomputable semimeasures | `P33Mixture.mixture_counterexample` |
| 3.3 | The same with weights within constant factors of 2^{-K(i)} | `P33Complexity.complexity_counterexample` |
| 3.3 | The same with exact weights 2^{-K_C(i)}, two universal mixtures that differ only in the optimal prefix machine C | `P33Exact.exact_counterexample` |
| 6.3 | No constant C gives E_{k:n} ≤ C·2^{K(z_{k:n} \| z_{<k})} for any deterministic predictor | `HutterPrizes.no_errorcount_complexity_bound` |
| 2.7 | Expected normalized error ≥ c·2^{-K(t)} along every computable selection and in O(log t) windows; no power of 2^{-K(t)} is a general upper bound | `P27Selection.*`, `P27Stochastic.*`, `P27Spikes.*` |

The paper's Table 2 maps every theorem to its Lean name, and says where the formal statement is narrower than the
paper statement. `docs/PROBLEMS.md` has the status of every problem we worked on, including the open ones.

## Check it

Requirements: [elan](https://github.com/leanprover/elan). The toolchain (Lean 4.35.0), Mathlib v4.35.0 and the
library [kolmogorov-complexity-lean](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean) are pinned in
`lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get        # Mathlib build cache
scripts/check.sh          # builds HutterPrizes/ and prints the axioms of every claimed theorem
```

`scripts/check.sh` fails on any `sorry`, `admit` or `axiom` in `HutterPrizes/`, and on any theorem in
`HutterPrizes/Audit.lean` that uses an axiom other than `propext`, `Classical.choice` and `Quot.sound`.

## Layout

- `Targets/`: the statements, frozen before any proof work, each with a fidelity note against the book's text
  (these files contain `sorry` by design).
- `HutterPrizes/`: the proofs. Each proved statement is identical to its target.
- `docs/reviews/`: fidelity reviews of each statement, referee reports on each proof and on the paper, and the
  novelty checks.
- `pro/`: the questions sent to the proof-writing model and its answers, in order (`pro/LOG.md`).
- `docs/paper/`: the paper source.

## How the work was done

Large language models did most of the work: ChatGPT Pro (OpenAI) proposed proofs and Lean code; Claude (Anthropic)
froze and reviewed the statements, refereed the proofs, searched the literature and drafted the paper. A result
counts here only when the Lean kernel accepts a proof of a statement that a separate review found faithful to the
book. See the paper's "Use of AI tools" statement.

## License

Apache-2.0 (see `LICENSE`), the same as kolmogorov-complexity-lean.
