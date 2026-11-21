# Research: Hutter (2005) Problem 6.3, "Posterization of prediction errors"

Attached: the book pages for Section 6.2 (Sequence prediction inside the AIξ model, book pp. 189-192) and the
problems page (pp. 207-208). Problem 6.3 [C20u/C40o] asks:

> Show ξ^AI(ż_{1:n}) ≳ ξ^SP(z_{1:n}) (z_k = b_k x_k), and that the other direction is wrong. Use this to
> "improve" bound (6.17) to E_{n} ≲ [ξ^SP(z_{1:n})]^{-1}. Posterize this to a bound
> E_{k:n} ≲ ξ^AI(ẏẋ_{<k}) / ξ^SP(z_{1:n}) on the number of errors in cycles k to n. Is it possible to improve
> the numerator to ξ^SP(z_{<k}) and to bound the expression by ≲ 2^{K(z_{k:n} | z_{<k})} (cf. Problem 3.13)?

Earlier work in this project (Lean-checked): the plain conditional ratio M(x)/M(xy) ≤ C·2^{K(y|x)} fails
uniformly (x = 0^ℓ, y = 1). Known (Chernov-Hutter 2005): M(x)/M(xy) ≤ C·2^{K(y|x)+K(|x|)}. So the last
question cannot be answered through that ratio with an O(1) constant, but a direct error-count bound may still
hold (a one-bit tail has at most one error).

Work as a research mathematician:
1. Prove the "easy" parts precisely, with the book's definitions (ξ^AI, ξ^SP, the greedy horizon-1 policy,
   E_{k:n}): ξ^AI ≳ ξ^SP, the failure of the reverse, E_n ≲ 1/ξ^SP(z_{1:n}), and the posterized bound
   E_{k:n} ≲ ξ^AI(history_{<k})/ξ^SP(z_{1:n}). State each with explicit quantifiers and constants.
2. The open part, (6.3N): ∃C ∀n, z_{1:n}, k ≤ n: E_{k:n} ≤ C·ξ^SP(z_{<k})/ξ^SP(z_{1:n}). Prove it or give a
   counterexample (for one universal U, or for every U). If it fails, find the right correction factor
   (e.g. 2^{K(k)} or 2^{K(|z_{<k}|)}) and prove the corrected bound.
3. The final question: E_{k:n} ≲ 2^{K(z_{k:n} | z_{<k})}? Answer it directly as an error-count statement, with
   either a proof or a counterexample, and say exactly which form of K and which constant dependence you mean.
4. For each result, give a statement suitable for a Lean formalization with plain finite objects (finite
   histories, abstract semimeasures with stated properties), and say what library facts it would need.

State every claim as a theorem with quantifiers, give proofs, mark confidence and novelty, and cite sources
(arXiv ID or DOI) you opened.
