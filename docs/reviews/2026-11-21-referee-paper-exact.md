# Referee report on paper Thm 3.9 (exact 2^-K weights), draft 4, 2026-11-21

Fresh-context referee (Claude Opus subagent). No fatal issue; the proof is correct and matches the Lean proof
(short codes prefix-free with 1^30·U_0; K_{C±}(i+4) = 30 + K_{U_0}(i+4); weights 1/8, 3/8; ηM₀ = 2(1−η)R; no
circularity). Lean derives n^{1/4}/256 (n ≥ 2) internally (`hgap`); the exported statement keeps /512 (n ≥ 3).
Major (fixed): abstract claimed /256 for n ≥ 2 under "checked in Lean" → now says constructed machines and
enumeration, formal bound n^{1/4}/512 for n ≥ 3.
Minor (fixed): "Formal version: as stated" → library enumeration, weaker bound; "a weaker constant" added to the
narrowing list; Table 1 "constructed optimal prefix machines"; Remark 3.13 defines K_V(ν) := min{K_V(q) : q computes ν}.
Optional (left): local symbol reuse (C, R, τ).
