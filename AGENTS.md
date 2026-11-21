# hutter-prizes

Goal: solve open problems with prizes from Hutter's book *Universal Artificial
Intelligence* (2005), with an LLM writing proofs and Lean checking them. A result
counts when a completed Lean proof exists for a statement that a review found
faithful to the problem. Partial results (a lemma, a counterexample, a corrected
hypothesis) count too. Problem list and status: `docs/PROBLEMS.md`. The book PDFs are on the SSD (`docs/sources/BOOKS.md`); keep them out of git and out of Pro chats
beyond the pages a question needs.

## Roles

- Desk: the Claude session Matt talks to. It picks the next question, runs Lean,
  keeps the records, and brings Matt only kind-of-work and stopping decisions
  (`docs/DECISIONS.md`, trade-off format).
- Worker: ChatGPT Pro in Matt's signed-in Chrome. Send one question at a time with
  `~/repos/competitions/tools/pro-query.sh pro/NNN-slug.q.md pro/NNN-slug.a.md </dev/null`,
  or drive the browser directly. Pro text is an untrusted suggestion until Lean
  accepts it.

## Proof loop

1. Freeze the target: a Lean statement in `Targets/` (sorry allowed there) plus a
   fidelity note: definitions, quantifiers, what each constant may depend on, and
   the source text it comes from. A fresh-context reviewer checks the note against
   the source before proof work starts. Lean checks a proof of the statement as
   written. This review is the check that the statement is Hutter's problem.
2. Ask Pro for a proof sketch, then Lean code. Paste the Lean into `HutterPrizes/`
   and run `scripts/check.sh`. `pro-query.sh` opens a new chat each call, so each
   round's question file stands alone: target, fidelity note, current Lean, exact
   errors, and the upstream lemmas in play. Repeat.
3. Keep every proved lemma. Add each claimed theorem to `HutterPrizes/Audit.lean`.

`scripts/check.sh` passes only with no sorry and only the three standard axioms.
`HutterPrizes/` must always pass it.

## Toolchain

Lean 4.35.0 via elan (`export PATH=$HOME/.elan/bin:$PATH`; the installer did not
edit shell profiles). Mathlib comes as a prebuilt cache. The upstream library
`kolmogorov_complexity` (Milovanov, Apache-2.0) is pinned by commit in
`lakefile.toml` and builds from source on first use. Read its theorems in
`.lake/packages/kolmogorov_complexity/` before you prove anything again. Record a
reason in `docs/DECISIONS.md` before you move a pin.
