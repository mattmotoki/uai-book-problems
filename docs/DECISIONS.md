# Decisions for Matt

The desk adds a section per decision and pushes once per wake. Matt answers here or on the phone; the desk
records the answer and moves on. Only stopping and kind-of-work questions belong here. Options in random
order, each with: kind of work | cost | upside | what it gives up. "Something else" last.

<!-- template
## D<n> (open) — <question>   <date>, from <worker>
- <option>: <kind of work> | <cost> | <upside> | <gives up>
- Something else.
Answer (Matt, 2026-11-20): try them all eventually; the desk or Pro picks the order.
Desk order: (1) calibration proof and a status map of all prize problems from the book text (one Pro query);
(2) 6.3 and 2.7, the cheap status checks; (3) 2.3(a); (4) 6.2 last, because it needs an AIXI layer in Lean first.
The status map may change this order; the desk records any change here.
-->

## D1 (answered) — Which prize problem first?   2026-11-20, from desk
Before any choice: the desk gets the book's exercise text and runs one calibration proof (a known Solomonoff
bound through the Pro → Lean loop). Query counts below are guesses; one Pro query takes about 10-60 min.
3.3 is not an option yet: the page gives only its title, so we cannot judge it before we have the book text.
- 6.3 Posterization of prediction errors (€100): literature map of Chernov-Hutter 2005 against the exercise, then a narrow extension | low, about 5-15 queries to know what is left | the cheapest way to a clear status, a claim with a known paper beside it | the 2005 paper may already cover most of it, so the prize may be reduced
- 2.3(a) Convergence on every ML-random sequence (€100): new construction or impossibility proof over all dominating semimeasures | high, open since 2005, weeks of queries with a low chance | a publishable result either way | slow feedback; upstream has Martin-Löf randomness and an MDL predictor that converges on every ML-random sequence (`predictor_merges_on_random`), but that predictor is not a universal semimeasure, so the core step is new
- 2.7 Normalized predictor M_norm, lower bound or better upper bound (€100): inequalities and constructions on semimeasures over binary strings | medium, about 20-60 queries | a focused statement where Lean feedback is fast, and upstream already has semimeasure and conditional-probability definitions | the page says a "2.7u" solution exists from 2005; we must first find out which part that covers
- 6.2 AIXI loss bounds (€100-500): define AIXI agents and environments in Lean first, then a restricted bound | high, a new Lean layer before any proof | the largest prize and the core open question about AIXI | weeks of setup before the first real theorem; negative results limit what can be true
- Something else.
Answer:

## D2 (answered) — What to do with the 3.3, 6.3E and 2.7 results?   2026-11-21, from desk
Results (Lean-checked, fresh-context reviews "faithful with caveats", novelty check in
`docs/reviews/2026-11-21-novelty.md`): 3.3 answered "no", also for two Bayes mixtures over all lsc semimeasures
(gap ≥ n^{1/4}/256); 6.3 last question answered "no" for ordinary conditional K (every predictor, incl. AIξ).
Since then: 2.7 stochastic lower bounds are in Lean too (once per dyadic block, along every computable
selection, and in every O(log t) window; partial answer). Novelty: none found in print (2007-2015 Hutter-group
papers; Bauwens-Kuznetsov 2026 read in full, cite as related work).
Summary page: `docs/results-2026-11-21.html`. The repo is private; Hutter would need the Lean files.
- Short note on arXiv first, then an email to Hutter with the link: a 4-6 page write-up (desk drafts, Pro checks
  proofs) plus a public copy of the Lean files | about 1-2 days of desk time, Matt reads and approves the text
  and the public release | public priority and a citable record; Hutter gets a finished result | slower; a public
  claim can be wrong in a way the reviews missed, and the note carries Matt's name
- Keep working before contact: Lean versions with 2^-K(ν) weights or Solomonoff M_U vs M_V (Pro's 008 Thm 7), and
  the measure-class (M_comp) version | several more Pro rounds, about 1 day | a stronger, more complete answer that
  matches more readings of the problem | delays any feedback from Hutter on whether he sees the problem as solved
- Email Hutter now with a short summary and the Lean files attached (Matt sends) | about 1 hour of desk drafting,
  Matt sends one email | fastest feedback on whether these count as solutions and on the prize | no public record;
  Hutter may find the presentation rough or point to prior work we missed
- Something else.
Answer (Matt, 2026-11-21): keep working before contact (2^-K(ν) weights or Solomonoff priors for 3.3, the
measure-class version, the 2.7 upper bound in Lean). No contact with Hutter yet.
