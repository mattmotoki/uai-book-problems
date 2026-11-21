# Referee report on paper §3.6 and related edits (draft 3), 2026-11-21

Fresh-context referee (Claude Opus subagent). No fatal issue; no proof error. Thm 3.9 matches
`P33Measures.measure_class_counterexample` clause by clause; its proof, Remark 3.10, Cor 3.11, Remark 3.12 and the
positive-boundary paragraph are correct.
Major (fixed): "The negative answer needs the 0-1 loss" was false; now "uses a loss with a discrete decision ... and a
source whose conditionals approach the decision threshold".
Minor (fixed): r_µ index renamed r_0; "for every positive base prior" → priors w± ≥ 2^-20 a built from any positive
base prior; "n ≥ 2" added in abstract and intro; referee phrase removed; Remark 3.10 marked not formally verified;
Remark 3.12 K(ν) wording. Optional symbol collisions (p_t/p_j, D_n/D_j, δ/δ_t) left. Not verified by this referee:
citation pointers liteng2026 Thm 5, suwandi2026 Ex 5, dawidvovk2009 Prop 4 (checked earlier by the bibliography agent).
