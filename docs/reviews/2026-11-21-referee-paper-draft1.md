# Referee report on paper draft 1 (docs/paper/main.tex), 2026-11-21

Skeptical fresh-context referee (Claude Opus subagent), read-only. **No fatal issue; no error in a proof.** Every
proof read by hand; constants of Thms 3.1-3.2 computed (e^{4/255} = 1.015810 < 255/251 = 1.015936). Paper
statements compared with the Lean statements (P33Mixture, P33Complexity, P33Theorem3, P63E, P63R, P27F,
P27Selection, P27Spikes). Unchecked paper steps correct: Lemma 2.1 (limit m1), Remark 3.3 (any tie rule:
Theorems 3.4, 3.5, 3.8 hold for every fixed tie rule), Remark 3.6, Thm 3.8 (c = η, C = η + 2^{max(K(p),K(q))}),
Prop 5.1, Cor 4.3, Cors 5.6-5.8, Prop 5.11. Attribution follows the novelty review.

Major: M1 abstract l.65 immune-set sentence false as read (fix: "a set of times along which A_t/2^{-K(t)} → 0
must be immune"). M2 TODO-REPO prints twice; affiliation TODO open (Matt's input).
Minor: m1 Lemma 2.1 "for lsc M"; m2 narrower-formal-scope notes at Thm 3.1 (H_n/16 upper bound), Thm 4.2 (AIξ
to P), Prop 4.4 and Prop 5.1 (library M only), and in "What the formal proofs do not cover"; m3 Remark 3.3 tie
rule for Thms 3.4, 3.5, 3.8; m4 §5 Process (Thm 3.8 status; "every file in HutterPrizes/"); m5 check Prop 4.4
against solved Problem 2.6(ii); m6 Prop 5.11 define "quiet"; m7 Prop 4.4 symbol C twice; m8 Remark 3.7 Thm 3.5
weights are computable; m9 remove unsupported "Monte Carlo run", "our notes contain", "a referee found gaps";
m10 small gaps (P ≠ Q in Thm 3.5; V dominates M in Prop 5.1; horizon-1 unnecessary in §4.1; A_t identity in
Lemma 5.4; define s_t(x), a_t(x) in Thm 5.9); m11 notation collisions (ξ±, μ, P, j, w, C); m12 intro l.100 state
the book's bound in full; m13 "agree" → "are consistent".
