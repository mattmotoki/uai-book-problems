# Status map as of 20 November 2026

**The cleanest unresolved targets are 2.3(a), a narrowly specified polynomial-bound version of 6.2, and the active numerator replacement in 6.3.** The other prize headings contain known results, false formulations, or wording that needs further specification.

There are also two findings worth acting on immediately:

- **Problem 3.3’s natural bounded-loss-difference claim is false.** I give an explicit counterexample with two computable product measures below. This is a mathematical deduction from this investigation, not a published resolution I located or a Lean-checked result.
- **The selected-bits repository and the November 2026 preprint need reconciliation.** The pinned Lean source claims a general linear complexity bound where the preprint says polynomial bounds remain unknown. The inspected definitions appear to describe the same setting.

The complete 20-page report contains the detailed formulations, proof sketches, declaration inventory, and source-access ledger:

:chatgpt-content-reference{index="15"}[hutter-prize-status-2026-11-20.pdf](sandbox:/workspace/scratch/26ef5ab818e1/output/pdf/hutter-prize-status-2026-11-20.pdf)

| Problem | Status supported by this investigation | Best research interpretation |
|---|---|---|
| **2.3** | Universal-machine and effective-mixture versions are negative, including normalization. Dominant enumerable semimeasures remain unresolved in the literature located. | Retain the dominance-only existence question, with a named convergence criterion. |
| **2.7** | Deterministic normalized error has matching order \(2^{-K(t)}\). A literal all-history stochastic analogue is false. | Formalize the normalized lower bound; specify the remaining stochastic-rate question before calling it open. |
| **2.9** | Deterministic convergence was resolved in 2011. The 2026 preprint gives normalized power-loss summability. The repository claims a stronger linear rate. | Reproduce and reconcile the formalization; distinguish stochastic and unrestricted partial-rule extensions. |
| **3.3** | The natural bounded cumulative-loss-difference assertion is false by the counterexample below. | Certify the counterexample; investigate publication history separately. |
| **6.2** | Several unrestricted extensions fail for bad universal priors. The deterministic binary, horizon-one polynomial question survives the sources inspected. | Keep that precise polynomial question. |
| **6.3** | Passive posterior results do not establish the active numerator replacement. The constant-factor ordinary conditional-complexity ratio is false. | Separate the active conjecture from the false ratio simplification. |

## What I verified

I read the supplied extract, including visual checks of the equation-heavy problem pages:

:chatgpt-content-reference{index="16"}

I opened the current prize page and the primary papers identified below. The page confirms the advertised prizes and the solved notice for 2.9; continued listing is not evidence that every subquestion remains open. Its note about TeXed solutions to “2.7u” concerns the exercise portion, not necessarily its open extension. [hutter1.net](https://www.hutter1.net/ai/uaibook.htm?utm_source=chatgpt.com)

I also inspected the actual repository at commit **`17c50e560c337a8a702f8850a711f80a56b3cf91`**. Its exact-commit build-and-audit job succeeded; the overall workflow failed in documentation generation. **I did not independently rebuild the repository, and no new Lean proof was produced here.**

Throughout, “unresolved in the literature located” is a bounded search finding, not a proof that no solution exists.

---

# 1. Common definitions and constants

Let \(\mathbb B=\{0,1\}\), with finite words \(\mathbb B^*\), empty word \(\epsilon\), and paths \(\mathbb B^{\mathbb N}\). Write \(x_{<t}=x_1\cdots x_{t-1}\).

A continuous semimeasure \(q\) satisfies

\[
q(\epsilon)\le1,\qquad q(x0)+q(x1)\le q(x).
\]

“Enumerable” means **uniformly lower semicomputable**: one algorithm provides increasing rational approximations to all \(q(x)\). A computable probability measure \(\mu\) has root mass one, equality at each split, and uniformly computable cylinder probabilities with effective two-sided precision.

For positive denominators, distinguish

\[
q(b\mid x)=\frac{q(xb)}{q(x)}
\quad\text{from}\quad
Nq(b\mid x)=\frac{q(xb)}{q(x0)+q(x1)}.
\]

Here \(Nq\) denotes Solomonoff’s sibling normalization. Its cylinder probabilities are products of these normalized conditionals; this is not levelwise renormalization.

Fix optimal reference machines and encodings throughout:

- \(K(t)\): prefix complexity of the integer \(t\).
- \(K(y\mid x)\): ordinary conditional prefix complexity.
- \(K(\mu)\): complexity of a program computing the measure to arbitrary precision.
- \(K_m(z)\), for an infinite computable \(z\): length of a finite monotone program emitting all of \(z\), not complexity of a moving finite prefix.

For computable \(\mu\), Martin-Löf randomness can equivalently be expressed using a fixed dominant enumerable semimeasure \(m_*\):

\[
\omega\in\operatorname{MLR}(\mu)
\iff
\exists D<\infty\ \forall n:\quad
m_*(\omega_{1:n})\le D\mu(\omega_{1:n}).
\]

The constant \(D\) may depend on \(\omega,\mu,m_*\), but not on \(n\).

Unless explicitly stated otherwise, constants below may depend on the fixed machines, encodings, prior, and specified model or selector. They may **not** depend on a subsequently quantified path, history, time, or horizon.

---

# 2. Problem 2.3 — Convergence on every ML-random sequence

## Precise readings

Define:

\[
\mathcal A=
\left\{
q:\ q\text{ enumerable semimeasure},\
\forall\nu\text{ enumerable}\ 
\exists c_{q,\nu}>0\ 
\forall x,\ q(x)\ge c_{q,\nu}\nu(x)
\right\}.
\]

Let \(\mathcal B\) be the Solomonoff output semimeasures \(M_U\) of universal-by-adjunction monotone machines.

Let \(\mathcal C\) consist of mixtures

\[
\xi(x)=\sum_i w_i\nu_i(x),
\]

where \((\nu_i)\) is an effective exhaustive enumeration of enumerable semimeasures, \(w_i>0\), \(\sum_iw_i\le1\), and the weights are uniformly lower semicomputable.

Two ambiguities matter:

1. If reading (a) does **not** require the dominant semimeasure itself to be enumerable, it is a larger problem.
2. If “general weights” in (c) includes non-effective weights, the effective-mixture results do not automatically cover that interpretation.

The convergence predicate must also be fixed. These are different:

\[
\begin{aligned}
D_{\rm on}:&\quad
q(\omega_t\mid\omega_{<t})-\mu(\omega_t\mid\omega_{<t})\to0,\\
D_{\rm all}:&\quad
\max_b|q(b\mid\omega_{<t})-\mu(b\mid\omega_{<t})|\to0,\\
R_{\rm on}:&\quad
q(\omega_t\mid\omega_{<t})/\mu(\omega_t\mid\omega_{<t})\to1,\\
S_{\rm on}:&\quad
\sum_t[q(\omega_t\mid\omega_{<t})-\mu(\omega_t\mid\omega_{<t})]^2<\infty.
\end{aligned}
\]

Each of the last three implies \(D_{\rm on}\), but they are not interchangeable. Normalized versions replace \(q\) by \(Nq\).

## Verified literature status

**The class-equivalence attribution in the earlier lead needs correction.** It is **Wood–Sunehag–Hutter**, rather than Hutter–Muchnik, who prove

\[
\mathcal B=\mathcal C\subsetneq\mathcal A,
\]

with the empty-string convention excluded from the exact equality. [hutter1.net](https://www.hutter1.net/publ/unipreq.pdf?utm_source=chatgpt.com)

**Hutter–Muchnik** construct bad universal priors and a good enumerable but **non-universal** semimeasure \(W\) that converges in all-symbol difference on every computable-source ML-random path. Thus their positive construction does not solve the dominance requirement. [hutter1.net](https://www.hutter1.net/ai/mlconvxx.pdf?utm_source=chatgpt.com)

**Lattimore–Hutter** prove that for every effective universal mixture \(M\), some fair-coin-ML-random \(\alpha\) has prediction errors bounded away from zero on a set of positive upper natural density. Theorem 13 establishes normalized failure too. This excludes \(\mathcal B\) and \(\mathcal C\) for all four convergence requirements above. Their discussion explicitly leaves the dominant-only class unresolved. [hutter1.net](https://www.hutter1.net/publ/mnonconvx.pdf?utm_source=chatgpt.com)

## Exact surviving candidate

The weakest natural residual is

\[
\boxed{
\exists q\in\mathcal A\
\forall\mu\text{ computable probability measure}\
\forall\omega\in\operatorname{MLR}(\mu):
D_{\rm on}(q,\mu,\omega).
}
\tag{2.3A}
\]

Its negation is

\[
\forall q\in\mathcal A\
\exists\mu,\omega\in\operatorname{MLR}(\mu),\varepsilon>0\
\forall N\ \exists t\ge N:
|q(\omega_t\mid\omega_{<t})-\mu(\omega_t\mid\omega_{<t})|
\ge\varepsilon.
\]

A negative result with \(\mu\) fixed to fair coin would suffice. A positive result only for fair coin would not settle the all-source question.

**Status:** unresolved in the sources located. Keep the all-symbol, ratio, square-sum, and normalized variants separately named.

## Lean needs and first target

The repository already has:

- `Kolmogorov.IsMartinLofRandom`
- `Kolmogorov.isMartinLofRandom_iff_boundedAPrioriDeficiency`
- `Kolmogorov.universalContinuousSemimeasure_isMaximal`
- `Kolmogorov.ae_tendsto_condProb_sub_of_dominates`

The last theorem is almost-sure convergence. It does not provide the required every-ML-random-path quantifier.

The MDL endpoint `Kolmogorov.MDLPrediction.predictor_merges_on_random` concerns a changing selection of proper computable measures. Neither the paper nor the inspected code identifies this predictor with an enumerable dominant semimeasure. [arxiv.org](https://arxiv.org/html/2005.03467v3?utm_source=chatgpt.com)

**First formal target — eventual proportionality.** If positive \(p,q\) satisfy

\[
\exists c>0,N\ \forall x,\quad |x|\ge N\Rightarrow q(x)=cp(x),
\]

then their raw and normalized conditionals agree after \(N\), and all four asymptotic predicates agree on every path.

The proof cancels \(c\). This elementary bridge prevents a misleading approach: changing finitely many levels to leave the mixture class need not improve prediction at all.

---

# 3. Problem 2.7 — Defect and normalized lower bounds

## Exact statements and ambiguities

For the book’s machine prior \(M\), set

\[
d_M(x)=1-\frac{M(x0)+M(x1)}{M(x)}.
\]

At \(|x|=t-1\), the exercise gives a fixed-machine constant \(c>0\) such that

\[
1-M(b\mid x)\ge d_M(x)\ge c2^{-K(t)}.
\]

For any proper source \(\mu\) with \(\mu(x)>0\),

\[
\sum_b|M(b\mid x)-\mu(b\mid x)|\ge d_M(x).
\]

Here \(c\) is independent of \(x,t,b,\mu\). The defect argument uses the machine prior’s stopping mass; it should not automatically be transferred to every member of \(\mathcal A\).

The normalized question must distinguish:

- wrong-bit probability on a deterministic path;
- discrepancy from a stochastic source;
- pathwise versus expected error;
- absolute versus squared error;
- all times, eventual times, or infinitely many times.

The website’s “better upper bound” wording does not uniquely select among these.

## What is already known

For a computable infinite \(z\), the deterministic normalized rate is

\[
\boxed{
1-NM(z_t\mid z_{<t})
=\Theta_{M,z}(2^{-K(t)}).
}
\]

Leike–Hutter’s *Solomonoff Induction Violates Nicod’s Criterion*, Lemmas 6 and 10, supplies the relevant wrong-continuation estimates. The binary statement above is a corollary extracted from their argument, not a theorem they label as adjudicating this prize. [jan.leike.name](https://jan.leike.name/publications/Solomonoff%20Induction%20Violates%20Nicod's%20Criterion%20-%20Leike,%20Hutter%202015.pdf?utm_source=chatgpt.com)

Thus a little-\(o(2^{-K(t)})\) upper bound is impossible for this deterministic quantity. Squared error has scale \(2^{-2K(t)}\), which is a different question.

## A useful stronger lower-bound lemma

The following deduction applies to every \(M\in\mathcal A\):

\[
\boxed{
\exists c_{M,V}>0\ \forall x,b:
NM(b\mid x)\ge c_{M,V}2^{-K_V(|x|+1)}.
}
\tag{2.7F}
\]

The constant is independent of the history and bit.

**Proof sketch.** For \(t\ge1\), define

\[
\nu_t(y)=
\begin{cases}
M(y),&|y|<t,\\
M(\operatorname{parent}(y))/2,&|y|=t,\\
0,&|y|>t.
\end{cases}
\]

These form a uniformly enumerable family of semimeasures. Mix them using a universal discrete semidistribution \(m(t)\asymp2^{-K(t)}\). Dominance gives

\[
M(xb)\ge c\,m(|x|+1)M(x)/2.
\]

Divide by \(M(x0)+M(x1)\le M(x)\).

For computable \(z\), the wrong-branch words \(z_{<t}\overline{z_t}\) are effectively prefix-free. Their \(M\)-masses form a discrete enumerable subprobability, hence are at most \(C_z2^{-K(t)}\). Dirac domination bounds the normalization denominator below. This also extends the computable-path \(\Theta\) result to all \(M\in\mathcal A\).

These are deductions supplied here; I make no novelty claim.

## What remains, and what does not

A positive discrepancy lower bound **uniform over all histories** is false after normalization.

Let \(T\) flip the bit immediately after the first \(1\), leaving words without that next bit unchanged. It is a computable involutive tree automorphism. Set

\[
M(x)=\tfrac12(M_0(x)+M_0(Tx))
\]

for a universal \(M_0\). Then \(M\) remains universal, and

\[
M(0^j10)=M(0^j11),\qquad NM(1\mid0^j1)=1/2.
\]

The discrepancy from fair coin is exactly zero at arbitrarily late histories.

An expected-error statement is different. For example,

\[
\forall M\in\mathcal B\ \forall\mu\text{ computable}\
\exists c>0,t_0\ \forall t\ge t_0:
\mathbb E_\mu\sum_b
[NM(b\mid X_{<t})-\mu(b\mid X_{<t})]^2
\ge c2^{-2K(t)}
\]

is a precise question one could investigate. **I did not verify the literature status of this exact formulation. It must not be advertised as the established remaining prize conjecture.**

The accurate status is: deterministic normalized order known; the literal all-history stochastic analogue false; other rate requests need explicit quantifiers.

## Lean first target

Prove (2.7F) for the library’s canonical semimeasure. The especially relevant existing helper is

```text
Kolmogorov.exists_const_two_pow_KPNat_mul_le_universal_of_uniform_prefixFree
```

together with

```text
Kolmogorov.IsContinuousTreeSemimeasure.sum_antichain_le
```

The repository also has normalized sibling probabilities and discrete coding results. This is a particularly well-aligned first formal development.

---

# 4. Problem 2.9 — Prediction of selected bits

## Precise original question

For repeated pairs, the raw square-sum question is

\[
\exists C_M<\infty\ \forall\omega:
\left[
\forall j\ge1,\ \omega_{2j}=\omega_{2j-1}
\right]
\Rightarrow
\sum_{j\ge1}
(1-M(\omega_{2j}\mid\omega_{<2j}))^2
\le C_M.
\]

The normalized version substitutes \(NM\). The constant may depend on \(M\), but not on the arbitrary odd subsequence.

For general rules, let a total computable

\[
f:\mathbb B^*\to\{0,1,\bot\}
\]

return either a prediction or explicit abstention. A path is consistent when every non-abstaining prediction is correct. The question asks whether normalized probability tends to one along its selected positions, and potentially whether a complexity-only loss bound holds uniformly over consistent paths.

A partial function that halts on **every prefix of the target path**, possibly returning \(\bot\), is a stronger halting requirement than allowing divergence itself to mean abstention.

## Verified literature status

Lattimore–Hutter–Gavane prove normalized convergence for total rules, extend it to partial rules halting along the entire path, and construct a repeated-pair path on which raw \(M\) fails. Their Theorems 10–12 therefore resolve the convergence questions, but do not themselves give a complexity-only square-sum bound. Their proof uses an auxiliary result cited as private communication; I did not obtain its public proof. [hutter1.net](https://www.hutter1.net/publ/evenbits.pdf?utm_source=chatgpt.com)

The **19 November 2026 revision** of Bauwens–Kuznetsov is real and directly relevant. For a decidable pattern with a \(k\)-bit description, arbitrary compatible path, and fixed \(\gamma>1\), it proves

\[
\sum_{\text{forced }t}e_t^\gamma
\le C_{M,\gamma}(k+1)^{2\gamma}2^{\gamma k},
\qquad
e_t=1-NM(\omega_t\mid\omega_{<t}).
\]

It also gives divergent absolute-loss examples and polynomial classification bounds under a fixed computable runtime restriction. In particular, repeated pairs with \(\gamma=2\) receive the requested uniform finite bound. [arxiv.org](https://arxiv.org/html/2610.18632v2?utm_source=chatgpt.com)

## The repository/preprint discrepancy

The inspected repository states, for its canonical \(M\),

\[
\exists C\ \forall T,e,\omega,n:
\operatorname{DecidesTree}(e,T)\land\operatorname{Branch}(T,\omega)
\Rightarrow
\sum_{\substack{t\le n\\t\text{ forced}}}e_t^2
\le K(e)+C.
\]

For every \(\gamma>1\), it also states a bound linear in \(K(e)\) for the whole power-loss sum.

Relevant declarations in `Kolmogorov.SelectedBits` are:

```text
square_loss_le_index_complexity
power_loss_le_index_complexity
power_loss_summable_le_index_complexity
power_loss_le_treeComplexity
```

I checked the assumptions: total decidable tree, arbitrary branch, actual sibling normalization, and constants preceding the tree, index, path, and horizon. There is no inspected runtime restriction or randomness assumption on the branch. The infinite-series endpoint explicitly includes summability.

That appears stronger than the general rate described as unknown in the preprint. The [pinned statements](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/blob/17c50e560c337a8a702f8850a711f80a56b3cf91/KolmogorovMathlib/Solomonoff/SelectedBits/Statements.lean) and [successful build-and-audit job](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/actions/runs/44024228829/job/133840609552) are substantial evidence, but **independent reproduction and reconciliation remain necessary**.

## Exact remaining variants

The advertised deterministic questions should not be called open.

A precise ordinary stochastic extension is:

> For every dominant enumerable \(M\), decidable \(S\subseteq\mathbb B^*\), uniformly computable \(g:S\to[0,1]\), and probability measure \(\mu\), possibly noncomputable, satisfying  
> \(\mu(1\mid x)=g(x)\) whenever \(x\in S\) and \(\mu(x)>0\), does
> \[
> |NM(1\mid\omega_{<t})-g(\omega_{<t})|\to0
> \]
> along selected times, for \(\mu\)-almost every \(\omega\)?

Require convergence when selection is infinite; finite selection is vacuous. If \(\mu\) is globally computable, ordinary Solomonoff convergence already handles the case.

Kusum’s November 2026 paper proves a related stochastic guarantee for a **reflective-oracle predictor**, while distinguishing ordinary normalized Solomonoff prediction. It does not settle this candidate. [arxiv.org](https://arxiv.org/html/2611.14454v1?utm_source=chatgpt.com)

Another unresolved-in-search variant permits an arbitrary partial computable \(f:\mathbb B^*\rightharpoonup\mathbb B\), with divergence meaning abstention, and asks for convergence along infinitely many correct defined predictions. The 2011 partial theorem does not cover it.

## Lean first target

Prove a prior-comparison adapter. If positive semimeasures satisfy

\[
ap(x)\le q(x)\le bp(x)\qquad(\forall x),\quad 0<a\le b<\infty,
\]

then

\[
Nq(c\mid x)\le(b/a)Np(c\mid x).
\]

Consequently, \(\gamma\)-power loss transfers with factor \((b/a)^\gamma\). The proof bounds the numerator above and the denominator below.

Universal enumerable priors mutually dominate, so this transfers a canonical-prior result to arbitrary universal priors. I did not find this exact adapter among the inspected endpoints.

---

# 5. Problem 3.3 — Comparing two mixtures

## Exact decision-theoretic statement

Fix finite outcomes \(\mathcal X\), actions \(\mathcal Y\), loss \(\ell:\mathcal X\times\mathcal Y\to[0,1]\), countable class \(\mathcal M\) of probability measures, and true \(\mu\in\mathcal M\). Let

\[
\xi=\sum_{\nu\in\mathcal M}w_\nu\nu,\qquad
\xi'=\sum_{\nu\in\mathcal M}w'_\nu\nu
\]

with both weight families positive and summing to one.

Using fixed ties, let

\[
a_\rho(x)\in\arg\min_a\sum_b\rho(b\mid x)\ell(b,a),
\qquad
L_n^\rho=\sum_{t=1}^n
\mathbb E_\mu\ell(X_t,a_\rho(X_{<t})).
\]

Both losses are evaluated under the **same true \(\mu\)**.

The literal expression \(L_\infty^\xi-L_\infty^{\xi'}\) is undefined when both totals are infinite. Natural readings are:

- bounded partial differences;
- convergence of their difference to a finite limit;
- absolute summability of per-step differences.

The standard mixture-loss bounds do not imply these; they permit a difference growing with the informed predictor’s cumulative loss. [jmlr.org](https://www.jmlr.org/papers/volume4/hutter03a/hutter03a.pdf?utm_source=chatgpt.com)

## Counterexample: the natural claim is false

This is **derived here**, not a published resolution located by the search.

Let

\[
\delta_t=\frac1{32t},\qquad
\mu(X_t=1)=\frac12+\delta_t,\qquad
\nu(X_t=1)=\frac12-\delta_t,
\]

with independence across time. Both measures are computable. Use zero-one loss and

\[
\xi_-=\tfrac14\mu+\tfrac34\nu,\qquad
\xi_+=\tfrac34\mu+\tfrac14\nu.
\]

Write \(R_n=\nu(X_{1:n})/\mu(X_{1:n})\). At time \(t\):

- \(\xi_-\) predicts \(1\) when \(R_{t-1}<1/3\);
- \(\xi_+\) predicts \(1\) when \(R_{t-1}<3\).

The low-\(\mu\) mixture is never better under \(\mu\). On \(1/2<R_{t-1}<3/2\), their conditional expected loss gap is \(2\delta_t\).

Now

\[
\mathbb E_\mu R_n=1,
\]

and direct multiplication gives

\[
\mathbb E_\mu R_n^2
=
\prod_{t=1}^n
\left(1+\frac{16\delta_t^2}{1-4\delta_t^2}\right)
\le e^{8/255}.
\]

Thus \(\operatorname{Var}(R_n)<1/8\), so Chebyshev gives

\[
\mathbb P_\mu(1/2<R_n<3/2)>1/2
\]

uniformly in \(n\). Therefore

\[
\boxed{
L_n^{\xi_-}-L_n^{\xi_+}
\ge\sum_{t=1}^n\delta_t
=\frac1{32}\sum_{t=1}^n\frac1t
\longrightarrow\infty.
}
\]

This defeats all three interpretations above, using the same two-element class and positive computable priors. It does not rely on tie-breaking.

## Remaining claim and Lean target

For the unrestricted problem, the target should be the **negation**, certified by this example. Any positive residual needs additional assumptions on losses or model classes.

No general Bayes-action/cumulative-decision-loss interface was found in the repository.

**First formal target:** prove the finite likelihood-ratio second-moment identity and uniform probability bound. This needs finite product probabilities, finite sums, and algebra—not computability or Martin-Löf randomness. The harmonic loss gap is then a short second stage.

I would not claim publication novelty or prize eligibility before checking the history with Hutter.

---

# 6. Problem 6.2 — Loss bounds for AIXI

## Exact active setup

An active chronological semimeasure

\[
\Xi(r_{1:n}\Vert a_{1:n})
\]

is nonnegative, has root mass at most one, does not depend on future actions, and satisfies

\[
\sum_{r_n}\Xi(r_{1:n}\Vert a_{1:n})
\le
\Xi(r_{<n}\Vert a_{<n})
\]

for every history and next action. Universality means multiplicative domination of each enumerable chronological semimeasure by a positive constant independent of the history.

For binary sequence prediction,

\[
a_t,z_t,r_t\in\{0,1\},\qquad r_t=\mathbf1\{a_t=z_t\}.
\]

Actions and rewards recover the target bits: \(z_t=\mathbf1\{a_t=r_t\}\).

At horizon one, with fixed ties,

\[
a_t\in\arg\max_a
\Xi(r_{<t}1\Vert a_{<t}a).
\]

Let \(E_{k:n}=\sum_{t=k}^n\mathbf1\{a_t\ne z_t\}\). The book’s bound has the form

\[
\exists C_{U,V}>0\
\forall z\text{ computable infinite}:
E_\infty^{U,h=1}(z)
\le C_{U,V}2^{K_{m,V}(z)}.
\]

For a finite horizon ending at \(m\), the book’s expectimax maximizes

\[
\sum_{r_t}\max_{a_{t+1}}\sum_{r_{t+1}}\cdots
\max_{a_m}\sum_{r_m}
(r_t+\cdots+r_m)
\Xi(r_{1:m}\Vert a_{1:m}).
\]

With defective semimeasures, this terminal-prefix convention and recursively accumulated reward can differ; a theorem must identify which it uses.

## What the literature excludes

Leike–Hutter’s dogmatic-prior theorem constructs universal priors that enforce specified computable behavior under an appropriate positive-value condition. Crucially, their discussion distinguishes deterministic horizon-one sequence prediction. It does **not** disprove the polynomial version of the book’s bound in that special case. [proceedings.mlr.press](https://proceedings.mlr.press/v40/Leike15.pdf?utm_source=chatgpt.com)

Here are concrete deductions that clarify the other branches.

### Longer horizons: a fixed-prior counterexample

Let \(\Xi_0\) be universal and

\[
\Xi=\tfrac{15}{16}\nu+\tfrac1{16}\Xi_0.
\]

Take true \(z=0101\ldots\). Let \(\nu\) give the corresponding alternating rewards while all actions are zero, and zero forever after the first action one.

At an all-zero history, a plan continuing zero for \(H\ge2\) steps has unnormalized value at least

\[
\tfrac{15}{16}\lfloor H/2\rfloor\ge5H/16.
\]

Every plan starting with one has value at most \(H/16\). Thus the agent always predicts zero and makes \(\lfloor n/2\rfloor\) errors. One fixed universal prior suffices.

### Stochastic passive sources: sublinear regret can fail at horizon one

Take iid \(Z_t\sim\operatorname{Bernoulli}(3/4)\). Let \(\nu\) model the correct reward process under action zero and punish action one with zero forever.

Along the counterfactual all-zero action path, the likelihood ratio \(\Xi_0(h)/P(h)\) is a nonnegative supermartingale. With probability at least \(1/2\), it never exceeds \(2\). On that event, the \(15/16\) dogmatic component keeps the actual agent choosing zero.

Consequently \(\Pr(a_t=0)\ge1/2\), yielding expected regret at least \(n/4\) against always predicting one.

These are explicit deductions, not claims that the numerical constructions occur as numbered theorems in the paper.

### General losses

This branch additionally needs the loss range, feedback, reward encoding, model-class knowledge, and whether the objective is absolute loss or regret.

For instance, positive reward for an incorrect prediction permits another horizon-one dogmatic example. That does not settle every interpretation where the learner is told a restrictive passive loss structure.

## Exact surviving polynomial candidate

A clean version is

\[
\boxed{
\forall U\ \exists C_U>0,d_U\in\mathbb N\
\forall z\text{ computable infinite}:
E_\infty^{U,h=1}(z)
\le C_U(1+K_{m,V}(z))^{d_U}.
}
\tag{6.2P}
\]

The linear version fixes \(d_U=1\). A degree uniform over \(U\) is stronger; existence of one favorable \(U\) is weaker.

Its negation requires **one fixed \(U\)** for which every polynomial fails. Choosing a different malicious machine for each target sequence does not establish that negation.

**Status:** unresolved in the literature located.

## Lean needs and first target

The repository’s passive Solomonoff theorem is not an active loss theorem. Missing foundations include chronological semimeasures, action/reward histories, finite expectimax, induced true processes, and error/regret.

**First target:** the deterministic horizon-two counterexample. Prove that continuation zero scores at least \(15/16\), whereas a first action one scores at most \(2/16\), then induct on the actual history. Add universality preservation under a positive mixture afterward.

---

# 7. Problem 6.3 — Posterization of prediction errors

## Separate the active bound from the passive ratio

Fix the greedy horizon-one policy above. Let \(M=\xi^{SP}\), and write \(h_{<k}\) for its action/reward history.

The passive-to-active compiler gives

\[
\exists c_{\Xi,M}>0\ \forall a,r,n:
\Xi(r_{1:n}\Vert a_{1:n})
\ge c_{\Xi,M}M(z_{1:n}).
\]

At each mistake, greediness and this domination force a drop in active prefix mass. Telescoping gives

\[
c_{\Xi,M}M(z_{1:n})E_{k:n}
\le
\Xi(h_{<k})-\Xi(h_{\le n})
\le\Xi(h_{<k}).
\]

The proposed numerator replacement is therefore

\[
\boxed{
\exists C_{\Xi,M}<\infty\
\forall n,z_{1:n},1\le k\le n:
E_{k:n}^{\pi_\Xi}(z)
\le C_{\Xi,M}
\frac{M(z_{<k})}{M(z_{1:n})}.
}
\tag{6.3N}
\]

The policy starts from the empty history, with fixed ties. The constant cannot depend on \(z,k,n\). Uniform quantification over computable infinite targets is equivalent, because every finite word has a computable continuation.

**I found neither a proof nor a counterexample to this exact policy-constrained statement.**

## The ordinary conditional-complexity ratio is false

The separate claim

\[
\exists C\ \forall x,y:
\frac{M(x)}{M(xy)}
\le C2^{K(y\mid x)}
\]

fails.

Take \(x=0^\ell\), \(y=1\). Dirac domination gives \(M(0^\ell)\ge c>0\). The prefix-free family \(0^\ell1\) gives, by discrete coding,

\[
M(0^\ell1)\le C'2^{-K(\ell)}.
\]

Hence

\[
\frac{M(0^\ell)}{M(0^\ell1)}
\ge c'2^{K(\ell)}\to\infty,
\]

although \(K(1\mid0^\ell)=O(1)\).

This refutes the **ratio simplification**, not a direct error-count bound by \(2^{K(y\mid x)}\): a one-bit tail has at most one error.

## What Chernov–Hutter proves

The conference paper and expanded Chernov–Hutter–Schmidhuber paper give the passive bound

\[
\log_2\frac{\mu(y\mid x)}{M(y\mid x)}
\le K(\mu\mid x)+K(|x|)+O(1).
\]

Applying this to the computable Dirac measure on \(xy000\ldots\) gives

\[
\boxed{
\frac{M(x)}{M(xy)}
\le C2^{K(y\mid x)+K(|x|)}.
}
\]

Their sharper theorem uses

\[
K_*(\mu\mid x*)
+
K_{\mathbb Z}\!\left(\left\lceil
\log_2\frac{M(x)}{\mu(x)}
\right\rceil\right)+O(1).
\]

Here \(K_*\) is their condition-monotone complexity from twice-prefix machines, not ordinary conditional \(K\). The deficiency can be negative, so the integer complexity requires a signed encoding. These results are passive; they do not establish (6.3N). [hutter1.net](https://www.hutter1.net/ai/postbndx.pdf?utm_source=chatgpt.com)

Thus “approximately” matters:

- Within a uniform constant factor, the ordinary conditional ratio is false.
- Allowing the factor \(2^{K(|x|)}\), the corrected passive ratio is known.
- The active numerator replacement remains separate.

## Lean first target

Formalize the **failure of the uniform conditional ratio**, using \(0^\ell1\). Existing antichain mass bounds, discrete coding, Dirac measures, and conditional prefix complexity fit this argument.

Then formalize the known telescoping inequality with an abstract compiler constant. That separates the finite active argument from machine-construction details.

---

# 8. What the Lean library provides—and what it does not

The inspected snapshot uses **Lean 4.35.0**, with Mathlib pinned to

```text
56a005855ea17e0b0958f73ec801ae140b0a1679
```

Important declarations include:

| Area | Inspected declarations |
|---|---|
| Universal semimeasure | `exists_maximal_lowerSemicomputableContinuousSemimeasure`, `universalContinuousSemimeasure`, `universalContinuousSemimeasure_isMaximal` |
| Computability and complexity | `IsComputableMeasure`, `computableMeasureComplexity`, `KP`, `KPPlain`, `KPNat`, `exists_isOptimalPrefixConditional` |
| Randomness | `IsMartinLofTest`, `IsMartinLofRandom`, `isMartinLofRandom_iff_boundedAPrioriDeficiency` |
| Passive prediction | `sum_predictionError_le`, `tsum_predictionError_le`, `ae_tendsto_condProb_sub_of_dominates`, `solomonoff_tsum_predictionError_le_complexity` |
| Selected bits | The four endpoints listed in §4 |
| MDL | `MDLPrediction.predictor_merges_on_random`, `MDLPrediction.globalChoice_spec`, `MDLPrediction.vovk_merging_summable` |

All names have namespace prefix `Kolmogorov`.

Three semantic cautions are essential:

1. **Root mass:** `IsContinuousTreeSemimeasure` requires root mass exactly one, whereas the book permits at most one. Add an explicit bridge.
2. **Predictor class:** the canonical prior is obtained from a proved maximality existence theorem. Its probabilistic-generator representation does not alone prove universal-by-adjunction representation.
3. **Quantifiers:** the generic prediction theorem proves expected square summability and almost-sure convergence from dominance. It does not prove convergence on every ML-random path.

The audit script follows proof dependencies and allows only `propext`, `Classical.choice`, and `Quot.sound`; its optional `sorryAx` relaxation is not enabled in the workflow. Raw CI logs were inaccessible, but the exact job status, workflow, audit implementation, and source were inspected. This is the precise limit of the verification performed.

---

# 9. Ranking for an LLM + Lean workflow

This ranks **credible mathematical progress per effort**, including useful certificates of negative results—not expected prize payment.

| Rank | Problem | Reason |
|---|---|---|
| **1** | **3.3** | Explicit counterexample with modest finite-probability dependencies. A clear end state and no algorithmic-information infrastructure are needed. |
| **2** | **2.7** | The normalized lower-bound proof closely matches existing family-domination and antichain lemmas. Low mathematical novelty, high formalization tractability. |
| **3** | **6.3** | The conditional-ratio obstruction is inexpensive and eliminates an invalid goal. The telescoping lemma is modular; the actual numerator conjecture remains hard. |
| **4** | **2.9** | Excellent existing infrastructure, but the advertised deterministic questions are answered. Reproduction could clarify an important rate discrepancy; genuinely new stochastic extensions are harder. |
| **5** | **6.2** | Small counterexamples are tractable, but the polynomial residual needs active foundations and a new mathematical idea. |
| **6** | **2.3** | The remaining dominance-only question is a substantial randomness/recursion-theoretic problem. Existing almost-sure and MDL results do not bridge the missing condition. |

For the **fastest first reproducible result**, build the existing 2.9 endpoint first. For the first new formal development, I would choose the 3.3 counterexample.

---

# 10. Bibliography and access ledger

“Opened” below means the full primary text was obtained and relevant statements inspected, not that every proof was independently reconstructed.

### Original sources

- **Marcus Hutter.** *Universal Artificial Intelligence: Sequential Decisions based on Algorithmic Probability*. Springer, 2005. DOI **[10.1007/b138233](https://doi.org/10.1007/b138233)**. **Read:** supplied 36-page extract, not the entire book.
- **Marcus Hutter.** [Book/prize page](https://www.hutter1.net/ai/uaibook.htm#prizes), accessed 20 November 2026. **Opened.** Establishes current advertised wording and solved notices; the separate 2005 TeX solution files were not inspected.
- **Marcus Hutter.** “Open Problems in Universal Induction & Intelligence.” *Algorithms* **2**(3):879–906, 2009. DOI **[10.3390/a2030879](https://doi.org/10.3390/a2030879)**. **Full opened.** Historical clarification of the questions, not evidence of current openness. [hutter1.net](https://www.hutter1.net/ai/aixiopen.pdf?utm_source=chatgpt.com)

### ML-random convergence and prior classes

- **Marcus Hutter and Andrej A. Muchnik.** “Universal Convergence of Semimeasures on Individual Random Sequences.” *ALT 2004*, LNAI **3244**:234–248. DOI **10.1007/978-3-540-30215-5_19**; **[arXiv:cs/0407057](https://arxiv.org/abs/cs/0407057)**. **Full opened.** Early bad-prior and non-universal convergence constructions.
- **Marcus Hutter and Andrej Muchnik.** “On Semimeasures Predicting Martin-Löf Random Sequences.” *Theoretical Computer Science* **382**(3):247–261, 2007. DOI **10.1016/j.tcs.2007.03.040**; **[arXiv:0708.2319](https://arxiv.org/abs/0708.2319)**. **Full opened.** Expanded results distinguishing bad universal priors from a good non-universal \(W\).
- **Ian Wood, Peter Sunehag, and Marcus Hutter.** “(Non-)Equivalence of Universal Priors.” *Algorithmic Probability and Friends*, LNAI **7070**:417–425, Springer, **2013**; conference/preprint 2011. DOI **10.1007/978-3-642-44958-1_33**; **[arXiv:1111.3854](https://arxiv.org/abs/1111.3854)**. **Full opened.** Establishes the class relations used above.
- **Tor Lattimore and Marcus Hutter.** “On Martin-Löf (non-)convergence of Solomonoff’s universal mixture.” *Theoretical Computer Science* **588**:2–15, **2015**. DOI **[10.1016/j.tcs.2014.12.004](https://doi.org/10.1016/j.tcs.2014.12.004)**. **Full opened.** Every-mixture negative result and normalized extension; no arXiv identifier located.
- **Alexey Milovanov.** “Prediction and MDL for infinite sequences.” *Theory of Computing Systems* **68**:1124–1137, 2024. DOI **10.1007/s00224-024-10180-0**; **[arXiv:2005.03467](https://arxiv.org/abs/2005.03467)**. **Full opened.** ML-path merging for an MDL selector, not an enumerable dominant prior.
- **Simon M. Huttegger, Sean Walsh, and Francesca Zaffora Blando.** “Algorithmic randomness and the weak merging of computable probability measures.” *Annals of Pure and Applied Logic* **177**(8), 103737, 2026. DOI **10.1016/j.apal.2026.103737**; **[arXiv:2504.00440](https://arxiv.org/abs/2504.00440)**. **Full arXiv text opened; publisher full text blocked.** Concerns computable measures, not a solution of 2.3A. [arxiv.org](https://arxiv.org/html/2504.00440v2?utm_source=chatgpt.com)

### Rates and selected bits

- **Jan Leike and Marcus Hutter.** “Solomonoff Induction Violates Nicod’s Criterion.” *ALT 2015*, LNAI **9355**:349–363. **[arXiv:1507.04121](https://arxiv.org/abs/1507.04121)**. **Full opened.** Lemmas 6 and 10 support the normalized computable-path rate corollary.
- **Tor Lattimore, Marcus Hutter, and Vaibhav Gavane.** “Universal Prediction of Selected Bits.” *ALT 2011*, LNAI **6925**:262–276. DOI **10.1007/978-3-642-24412-4_22**; **[arXiv:1107.5531](https://arxiv.org/abs/1107.5531)**. **Full opened.** Normalized selective convergence and raw failure.
- **Bruno Bauwens and German Kuznetsov.** “Solomonoff induction of selected bits and online classification.” Preprint, 2026. **[arXiv:2610.18632v2](https://arxiv.org/abs/2610.18632v2)**, revised **19 November 2026**. **Full opened.** Power-loss summability, absolute-loss divergence, runtime-restricted polynomial bounds. No peer-reviewed venue verified.
- **Damini Kusum.** “Solomonoff Induction with Reflective Oracles.” Preprint/PIBBSS fellowship project, 2026. **[arXiv:2611.14454v1](https://arxiv.org/abs/2611.14454v1)**, 10 November 2026. **Full opened.** Related stochastic selection guarantee for a different predictor.
- **Lempp–Miller–Ng–Turetsky, 2010 private communication**, as cited by Lattimore–Hutter–Gavane. **Not obtained.** No public proof was verified; this remains an explicit access limitation.

### Mixture loss, active priors, and posterior bounds

- **Marcus Hutter.** “Optimality of Universal Bayesian Sequence Prediction for General Loss and Alphabet.” *JMLR* **4**:971–1000, 2003. **[arXiv:cs/0311014](https://arxiv.org/abs/cs/0311014)**. **Full opened.** General mixture-loss bounds; no bounded-two-mixture-difference resolution located. This is **cs/0311014**, not the different paper cs/0301014.
- **Jan Leike and Marcus Hutter.** “Bad Universal Priors and Notions of Optimality.” *COLT 2015*, PMLR **40**:1244–1259. **[arXiv:1510.04931](https://arxiv.org/abs/1510.04931)**. **Full opened.** Dogmatic priors and their scope; does not resolve deterministic horizon-one polynomial complexity.
- **Alexey Chernov and Marcus Hutter.** “Monotone Conditional Complexity Bounds on Future Prediction Errors.” *ALT 2005*, LNAI **3734**:414–428. **[arXiv:cs/0507041](https://arxiv.org/abs/cs/0507041)**. **Full opened.** Passive posterior bounds, not the active numerator replacement.
- **Alexey Chernov, Marcus Hutter, and Jürgen Schmidhuber.** “Algorithmic Complexity Bounds on Future Prediction Errors.” *Information and Computation* **205**(2):242–261, 2007. DOI **10.1016/j.ic.2006.10.004**; **[arXiv:cs/0701120](https://arxiv.org/abs/cs/0701120)**. **Full opened.** Expanded length-corrected and \(K_*\)/deficiency posterior theorems.

### Formalization

- **Alexey Milovanov.** [*kolmogorov-complexity-lean*, pinned commit `17c50e5`](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/tree/17c50e560c337a8a702f8850a711f80a56b3cf91), 17 November 2026. **Source inspected and exact-commit build/audit status verified; not independently rebuilt.** Its selected-bit rate claim is an important existing formalization claim whose relationship to the November preprint remains unresolved.

The project should keep **2.3A, 6.2P, and 6.3N** as separately named long-term goals. Before attacking them, reproduce the selected-bits endpoint and certify one of the short negative results above. That establishes both the proof environment and the discipline of checking that a Lean theorem has the exact predictor class, quantifier order, loss, and normalization required by the mathematical question.