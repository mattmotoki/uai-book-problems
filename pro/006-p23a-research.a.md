# Research report on 2.3A

**I have not proved or refuted 2.3A. My search through 20 November 2026 did not locate a verified settlement of the exact dominance-only formulation.** I did obtain several rigorous partial results and identify a specific false inference that prevents a direct extension of the Lattimore–Hutter argument.

The main conclusions are:

- **The critical mixture assumption is an effective subtraction property.** Dominance supplies a nonnegative residual semimeasure in the relevant argument, but does not make that residual lower semicomputable.
- **Mixing with \(W\) cannot repair an existing failure.** More precisely, on every path where \(W\) converges, a fixed positive mixture of \(q_0\) and \(W\) converges if and only if \(q_0\) does.
- **Several natural damping constructions can be ruled out completely**, including monotone multiplicative damping with a universal lower bound, and summable mixtures of components capped by multiples of \(W\).
- **A strong positive partial theorem holds for every \(q\in\mathcal A\):** on every sequence computably random relative to \(\emptyset'\), the cumulative conditional KL divergence is finite. This implies summable squared prediction error, summable semimeasure defect, and convergence after normalization.
- **There are explicit subclasses of \(\mathcal A\setminus\mathcal C\) with the same strong failure as universal mixtures**, including failure of Cesàro error convergence and convergence along any density-one set of times.

I give complete proofs of the partial results below. **I do not claim research novelty for them.** Some are elementary consequences of known constructions; the KL theorem is a useful formulation of a standard martingale argument, closely related to recent work.

---

## 1. Scope, notation, and literature status

Write \(\epsilon\) for the empty string and \(\lambda(x)=2^{-|x|}\) for fair coin measure. A continuous semimeasure satisfies
\[
q(\epsilon)\le 1,\qquad q(x)\ge q(x0)+q(x1).
\]
“Enumerable” means uniformly lower semicomputable.

For \(\mu(x)>0\), put
\[
p_x(b)=\frac{\mu(xb)}{\mu(x)},\qquad
r_x(b)=\frac{q(xb)}{q(x)}.
\]
Every \(q\in\mathcal A\) is positive on every finite string, since it dominates \(\lambda\).

The target concerns the observed symbol:
\[
r_{\omega_{<t}}(\omega_t)-p_{\omega_{<t}}(\omega_t)\longrightarrow 0.
\tag{1}
\]
Several results below establish the stronger conclusion for both \(b=0,1\).

### What the literature check supports

The distinction
\[
\mathcal B=\mathcal C\subsetneq\mathcal A
\]
is substantive. Wood–Sunehag–Hutter establish the equivalence of the Solomonoff and effective universal-mixture constructions, and strict inclusion in the dominant enumerable semimeasures. Empty-string conventions deserve care when comparing representations, but do not affect the constructions below. [hutter1.net](https://www.hutter1.net/publ/unipreq.pdf?utm_source=chatgpt.com)

The relevant Lattimore–Hutter conclusion is stronger than infinitely many errors: for every \(M\in\mathcal C\), there are \(\alpha\in\mathrm{MLR}(\lambda)\) and \(\eta>0\) such that
\[
\overline d\left\{t:
\left|M(\alpha_t\mid\alpha_{<t})-\tfrac12\right|>\eta
\right\}>0.
\tag{2}
\]
Their Theorems 6 and 13 cover the raw and normalized predictors, respectively. **The density here is upper density.** [hutter1.net](https://www.hutter1.net/publ/mnonconvx.pdf?utm_source=chatgpt.com)

Hutter–Muchnik’s \(W\) is enumerable, converges on every corresponding ML-random path of every computable measure, and is not universally dominant. Milovanov’s later MDL predictor has pathwise square-summable error; the published paper explicitly adopts rational-valued computable measures as its convention. Neither result supplies a member of \(\mathcal A\) satisfying 2.3A. [arxiv.org](https://arxiv.org/pdf/0708.2319?utm_source=chatgpt.com)

The recent search found two particularly relevant 2025 theses:

- **Damini Kusum** studies stronger randomness assumptions, including computable randomness relative to \(\emptyset'\).
- **Joel Artturi Saarinen** extends a nonconvergence argument to further source measures, but the formal theorem retains the **universal-mixture** hypothesis. Broader wording elsewhere in that thesis must not be read as removing it. [kdamini.com](https://kdamini.com/thesispdf.pdf?utm_source=chatgpt.com)

I also checked later citing work and nearby 2025–2026 papers. The source list in Section 7 records what was opened and why it does or does not address this question. This was a targeted literature and citation search, not an exhaustive citation-index export.

---

## 2. Exactly where the Lattimore–Hutter proof needs a mixture

### 2.1 The decisive operation

In the paragraph **“Auxiliary mixture”**, immediately after Lemma 11, Lattimore–Hutter use their particular enumerable additive semimeasure \(\nu\) from Definition 8/Lemma 9. If \(\nu=\nu_i\) in
\[
M=\sum_j w_j\nu_j,
\]
they form
\[
\widetilde M=M-\frac{w_i}{2}\nu.
\tag{3}
\]
Reducing that component’s coefficient preserves lower semicomputability. The subsequent effective decoding argument uses lower approximations to both \(M\) and \(\widetilde M\). [hutter1.net](https://www.hutter1.net/publ/mnonconvx.pdf?utm_source=chatgpt.com)

Here is the distinction that matters.

Suppose only that \(q\in\mathcal A\). Dominance gives \(d>0\) with
\[
q(x)\ge d\nu(x)\qquad\forall x.
\]
Choose rational \(0<c<d/2\) and define
\[
r=q-c\nu.
\]
Then
\[
r\ge q/2,
\]
so the residual is nonnegative and remains universally dominant.

Furthermore, because this particular \(\nu\) is additive,
\[
\begin{aligned}
r(x)-r(x0)-r(x1)
&=q(x)-q(x0)-q(x1)\\
&\quad-c\bigl(\nu(x)-\nu(x0)-\nu(x1)\bigr)\\
&=q(x)-q(x0)-q(x1)\ge0.
\end{aligned}
\]
Thus **semimeasurehood is not the missing step in this main on-sequence argument. Lower semicomputability is.**

### 2.2 The missing inference is actually false

The following proposition shows that this is more than an unfilled technical detail.

### Proposition 1 — Dominance does not permit enumerable subtraction

There exist \(q\in\mathcal A\) and an additive enumerable subprobability measure \(\nu\) such that:

1. for some positive rational \(c\), \(q-c\nu\) is a nonnegative, universally dominant semimeasure;
2. for every positive rational \(c\), \(q-c\nu\) is not lower semicomputable.

#### Proof

Take any \(U\in\mathcal A\), and set
\[
q(\epsilon)=1,\qquad q(x)=U(x)\quad(x\ne\epsilon).
\]
This is an enumerable semimeasure and dominates \(U\), hence belongs to \(\mathcal A\).

Choose a noncomputable left-c.e. real \(a\in(0,1)\). For a binary string \(x\), let
\[
I_x=[\ell_x,\ell_x+2^{-|x|})
\]
be its dyadic interval, and define
\[
\nu(x)=\lambda(I_x\cap[0,a))
=\max\{0,\min\{2^{-|x|},a-\ell_x\}\}.
\tag{4}
\]
The formula is uniformly lower semicomputable in \(x\). The dyadic interval partition gives
\[
\nu(x)=\nu(x0)+\nu(x1),\qquad \nu(\epsilon)=a.
\]

Universality supplies \(d>0\) such that \(q\ge d\nu\). For rational \(0<c<d/2\), the calculation above proves that \(q-c\nu\) is a semimeasure and dominates \(q/2\).

But if \(q-c\nu\) were lower semicomputable for any positive rational \(c\), then its root value
\[
1-ca
\]
would be left-c.e. This would make \(a\) right-c.e. Since \(a\) is already left-c.e., it would be computable, a contradiction. ∎

This example uses the same type of additive interval measure that appears in the nonconvergence construction.

**What this establishes:** a general replacement of the removable-component step by “dominance plus enumerability” is invalid.

**What it does not establish:** no redesigned negative proof can work. In the example, changing only the root creates the subtraction obstruction, while leaving tail predictions unchanged. A proof that bypasses this operation could still succeed.

### 2.3 Why pointwise domination is not a hidden mixture decomposition

There is a second distinction worth making explicit. For arbitrary semimeasures \(Q,U\), the inequality
\[
Q\ge cU
\]
does not imply that \(Q-cU\) is a semimeasure.

Writing
\[
\Delta_P(x)=P(x)-P(x0)-P(x1),
\]
the latter assertion requires
\[
\Delta_Q(x)\ge c\Delta_U(x)\qquad\forall x.
\tag{5}
\]
Pointwise domination supplies no such defect inequality. Even if (5) holds, enumerability of the difference is a separate requirement.

Consequently, one cannot extend a fixed-mixture impossibility argument to all of \(\mathcal A\) by treating domination as a permanent, effectively removable component.

---

## 3. Positive constructions: what can and cannot work

### 3.1 Fixed mixtures preserve existing failures

There is a necessary qualification to the question’s phrase “\(q=\tfrac12q_0+\tfrac12W\) fails.”

For an arbitrary \(q_0\in\mathcal A\), saying that it always fails would already assume the negative answer to 2.3A. The exact statement is an equivalence.

### Proposition 2 — Fixed-mixture equivalence

Let \(U,V\) be semimeasures with
\[
U(x)\ge cV(x)\qquad\forall x
\]
for some \(c>0\). Fix \(a\in(0,1)\), and let
\[
Q=aU+(1-a)V.
\]
Fix a measure \(\mu\) and a path \(\omega\) with positive relevant denominators. If
\[
V(\omega_t\mid\omega_{<t})
-\mu(\omega_t\mid\omega_{<t})\to0,
\]
then
\[
Q(\omega_t\mid\omega_{<t})
-\mu(\omega_t\mid\omega_{<t})\to0
\]
if and only if
\[
U(\omega_t\mid\omega_{<t})
-\mu(\omega_t\mid\omega_{<t})\to0.
\]

The same statement holds for each fixed next symbol.

#### Proof

At a prefix \(x\), define
\[
\rho_x=\frac{aU(x)}{aU(x)+(1-a)V(x)}.
\]
The domination assumption gives the uniform bound
\[
\rho_x\ge
\delta:=\frac{ac}{ac+1-a}>0.
\tag{6}
\]
The conditional probabilities satisfy
\[
Q(b\mid x)
=\rho_xU(b\mid x)+(1-\rho_x)V(b\mid x).
\]
For the respective errors,
\[
e_Q=\rho_xe_U+(1-\rho_x)e_V.
\tag{7}
\]
If \(e_U,e_V\to0\), then \(e_Q\to0\). Conversely,
\[
|e_U|\le\frac{|e_Q|+|e_V|}{\delta},
\]
so \(e_Q,e_V\to0\) implies \(e_U\to0\). ∎

Apply this with \(U=q_0\), \(V=W\). Since \(W\) is enumerable, \(q_0\in\mathcal A\) supplies the required domination.

Thus a fixed mixture cannot repair any bad ML path of \(q_0\). In particular, it cannot repair any effective universal mixture. If a good \(q_0\in\mathcal A\) exists, however, mixing it with \(W\) preserves its success.

There is also a quantitative version. If \(|e_U|\ge\eta\) on a set \(E\), then eventually on \(E\),
\[
|e_Q|\ge\delta\eta-|e_V|\ge\delta\eta/2.
\]
Hence positive-upper-density failure is preserved.

### 3.2 Monotone multiplicative damping cannot repair on-path predictions

Consider the natural construction
\[
Q(x)=b(x)U(x),
\]
where \(b\) decreases as the prefix grows.

### Proposition 3 — A positive universal lower bound makes this damping asymptotically ineffective

Let \(U\in\mathcal A\), and suppose \(b(x)>0\) satisfies
\[
b(xa)\le b(x)\qquad\forall x,a.
\]
If \(Q=bU\) belongs to \(\mathcal A\), then for every infinite path \(\omega\),
\[
Q(\omega_t\mid\omega_{<t})
-U(\omega_t\mid\omega_{<t})\to0.
\tag{8}
\]

#### Proof

Because \(U\) is enumerable and \(Q\) is universal, \(Q\ge cU\) for some \(c>0\). Thus \(b(x)\ge c\) everywhere.

Along a path,
\[
b_n:=b(\omega_{\le n})
\]
is nonincreasing and bounded below by \(c\), so it converges to a positive limit. Therefore
\[
\frac{b_n}{b_{n-1}}\to1.
\]
But
\[
Q(\omega_n\mid\omega_{<n})
=
U(\omega_n\mid\omega_{<n})
\frac{b_n}{b_{n-1}},
\]
and \(0\le U(\omega_n\mid\omega_{<n})\le1\). This proves (8). ∎

This is a genuine obstruction for this architecture. Prefix-monotonicity preserves the semimeasure inequality; a lower-semicomputable multiplier preserves enumerability. But retaining universality forces a positive lower bound, which makes the multiplicative correction vanish at the level of observed one-step predictions.

If instead \(\inf_x b(x)=0\), then \(Q\) does not dominate \(U\), so \(Q\notin\mathcal A\).

### 3.3 Capping by \(W\) preserves enumerability but destroys universality

One appealing way to avoid subtraction is
\[
V_K(x)=\min\{U(x),KW(x)\}.
\tag{9}
\]
This is enumerable when \(U,W\) are enumerable and \(K\) is a positive computable constant. It is also a semimeasure:
\[
\begin{aligned}
\sum_bV_K(xb)
&\le
\min\left\{\sum_bU(xb),K\sum_bW(xb)\right\}\\
&\le \min\{U(x),KW(x)\}.
\end{aligned}
\]

Could an infinite sequence of increasingly loose caps restore universality? Not with summable component weights.

### Proposition 4 — Summable mixtures of capped components are not universal

Let \(U\in\mathcal A\), and let \(W\) be an enumerable semimeasure not in \(\mathcal A\). Let \(t\ge0\), \(a_j\ge0\), and finite \(K_j\ge0\), with
\[
\sum_j a_j<\infty.
\]
Define
\[
Q(x)=tW(x)+\sum_j a_j\min\{U(x),K_jW(x)\}.
\tag{10}
\]
Then \(Q\) does not dominate \(U\). In particular, whenever the coefficients and normalization make \(Q\) an enumerable semimeasure, \(Q\notin\mathcal A\).

#### Proof

If \(W\) dominated \(U\), it would dominate every enumerable semimeasure. Therefore there are strings \(x_n\) with
\[
r_n:=\frac{W(x_n)}{U(x_n)}\to0.
\]
Dividing (10) by \(U(x_n)\),
\[
\frac{Q(x_n)}{U(x_n)}
=
tr_n+\sum_j a_j\min\{1,K_jr_n\}.
\]
For each fixed \(j\), the summand tends to zero and is bounded by \(a_j\). Summability gives
\[
Q(x_n)/U(x_n)\to0.
\]
Thus \(Q\) cannot dominate \(U\). ∎

This remains true when \(K_j\to\infty\), even if \(\sum_j a_jK_j=\infty\).

### 3.4 A stronger obstruction to making a universal semimeasure asymptotically equal to \(W\)

Matching predictions is weaker than matching prefix masses. The latter can be ruled out for the particular Hutter–Muchnik \(W\), already on computable paths.

The following general proposition isolates the argument.

### Proposition 5 — Approximation by computable finite heads obstructs uniform asymptotic mass matching

Let \(U\in\mathcal A\), and let \(W>0\) be a semimeasure. Suppose that for every \(k\) there are a computable semimeasure \(P_k\), an integer \(N_k\), and \(e_k\ge0\), with \(e_k\to0\), such that
\[
W(x)\le P_k(x)+e_kU(x)\qquad(|x|\ge N_k).
\tag{11}
\]
If \(Q\ge cU\) for some \(c>0\), then
\[
\sup_{\alpha\ \mathrm{computable}}
\liminf_n\frac{Q(\alpha_{\le n})}{W(\alpha_{\le n})}
=\infty.
\tag{12}
\]

#### Proof

Fix \(k\). Construct a computable path \(\alpha=\alpha^{(k)}\) satisfying
\[
P_k(\alpha_{\le n})<(3/4)^n\qquad(n\ge1).
\tag{13}
\]
Suppose \(x\) of length \(n\) has been selected with \(P_k(x)\le(3/4)^n\). One child has value at most
\[
\tfrac12P_k(x)\le\tfrac12(3/4)^n<(3/4)^{n+1}.
\]
Compute both child values until one is certified strictly below the final threshold, and choose it. The strict margin guarantees termination, including when some values are zero.

Since \(\alpha\) is computable, its Dirac measure is computable. Universality gives \(d_k>0\) with
\[
U(\alpha_{\le n})\ge d_k\qquad\forall n.
\]
Consequently, for sufficiently large \(n\),
\[
\frac{W(\alpha_{\le n})}{U(\alpha_{\le n})}
\le \frac{(3/4)^n}{d_k}+e_k.
\]
Thus
\[
\limsup_nW(\alpha_{\le n})/U(\alpha_{\le n})\le e_k,
\]
and
\[
\liminf_nQ(\alpha_{\le n})/W(\alpha_{\le n})
\ge c/e_k,
\]
interpreted as \(+\infty\) when \(e_k=0\). Letting \(k\) grow proves (12). ∎

#### Application to Hutter–Muchnik’s \(W\)

Their construction has
\[
W=\sum_{i\ge1}\varepsilon_i\widetilde\nu_i,
\qquad \varepsilon_i=i^{-6}2^{-i},
\]
where \(\widetilde\nu_i\le\nu_i\), and each \(\widetilde\nu_i\) is either a computable probability measure or vanishes beyond a finite depth. These are the quasimeasures of Definition 15/Lemma 16. [arxiv.org](https://arxiv.org/pdf/0708.2319?utm_source=chatgpt.com)

To check (11), form the enumerable semimeasure
\[
V=\frac12\sum_{i\ge1}i^{-2}\nu_i.
\]
Universality of \(U\) gives a uniform \(c_0>0\) such that
\[
U\ge c_0i^{-2}\nu_i\qquad\forall i.
\]
Therefore
\[
\sum_{i>k}\varepsilon_i\widetilde\nu_i
\le
\underbrace{c_0^{-1}\sum_{i>k}i^{-4}2^{-i}}_{e_k}
\,U,
\qquad e_k\to0.
\]
For each fixed \(k\), let
\[
P_k=\sum_{\substack{i\le k\\\widetilde\nu_i\text{ is a measure}}}
\varepsilon_i\widetilde\nu_i.
\]
This is computable **nonuniformly in \(k\)**: the finite set of relevant indices can be hardcoded. The other finitely many components vanish beyond some \(N_k\). Hence (11) holds.

It follows that no \(Q\in\mathcal A\) can satisfy
\[
Q(\alpha_{\le n})/W(\alpha_{\le n})\to1
\]
for every computable \(\alpha\).

In particular, a proposed construction
\[
Q=W+R,\qquad R/W\to0
\tag{14}
\]
on every ML-random path of every computable source cannot work. Every computable \(\alpha\) is ML-random for its computable Dirac measure.

This is an elementary consequence of the finite-head/tail argument underlying Hutter–Muchnik’s nonuniversality proof. [arxiv.org](https://arxiv.org/pdf/0708.2319?utm_source=chatgpt.com)

**The limitation is essential:** this does not rule out predictive merging with \(W\). Predictive merging can coexist with very different, path-dependent prefix-mass factors.

### 3.5 Why detecting disagreement is an effectivity problem

Lower semicomputability of \(q(x)\) and \(q(xb)\) does not imply lower semicomputability of their ratio.

For an explicit example, take a noncomputable left-c.e. \(\beta\in(1/2,1)\), and define
\[
q(\epsilon)=\beta,\qquad q(0)=q(1)=1/4,
\]
with all longer values zero. This is an enumerable semimeasure, but
\[
q(0\mid\epsilon)=\frac1{4\beta}
\]
is upper semicomputable and not lower semicomputable. If it were both, then \(\beta\) would be computable.

Therefore a general instruction such as “wait until \(q_0\)’s prediction disagrees with \(W\), then reduce its contribution” has two unproved steps:

1. The relevant posterior-disagreement event need not be c.e.
2. Lower approximations cannot retract mass already enumerated.

Withholding mass before committing it can avoid the second problem. But then one must prove that a single positive domination constant survives all subsequent withholding decisions. Propositions 3–5 show why several direct ways of doing that fail.

### 3.6 The MDL route does not automatically produce an enumerable universal semimeasure

Suppose a predictor \(H(b\mid x)\) gives proper probabilities and has the desired convergence. Stitching its conditionals together defines a measure:
\[
R(\epsilon)=1,\qquad R(xb)=R(x)H(b\mid x).
\tag{15}
\]
Neither enumerability nor universal dominance follows.

Indeed, there is a general obstruction.

### Proposition 6 — A normalized enumerable measure cannot belong to \(\mathcal A\)

Every lower-semicomputable probability measure \(R\), with \(R(\epsilon)=1\), is computable. No computable semimeasure dominates all computable Dirac measures.

#### Proof

For \(|x|=n\),
\[
R(x)=1-\sum_{\substack{|y|=n\\y\ne x}}R(y).
\]
The right side provides upper approximations, while enumerability provides lower approximations. Thus \(R\) is computable.

For any computable semimeasure, the geometric construction in Proposition 5 produces a computable path \(\alpha\) with
\[
R(\alpha_{\le n})<(3/4)^n.
\]
Since \(\delta_\alpha(\alpha_{\le n})=1\), no positive constant witnesses \(R\ge c\delta_\alpha\). ∎

Thus an enumerable implementation of (15) cannot solve 2.3A. Multiplication by a positive computable constant does not evade the argument.

This leaves open more delicate constructions of a defective enumerable semimeasure whose predictions approximate an MDL predictor. The normalized stitching operation alone does not supply one.

---

## 4. Strongest positive partial result: summable KL error under relative computable randomness

This is the most useful complete positive theorem obtained in this attempt.

Let
\[
\mathrm{CR}^{\emptyset'}(\mu)
\]
denote computable randomness for \(\mu\) relative to the halting problem: every nonnegative \(\emptyset'\)-computable \(\mu\)-martingale is bounded along the sequence.

This assumption is weaker than ML-randomness relative to \(\emptyset'\), so the result includes the \(2\)-random case.

### Theorem 7 — Finite cumulative conditional KL divergence

Let \(\mu\) be any computable probability measure, and let \(q\) be an enumerable semimeasure satisfying
\[
\exists c_0>0\ \forall x,\qquad q(x)\ge c_0\mu(x).
\tag{16}
\]
For every
\[
\omega\in\mathrm{CR}^{\emptyset'}(\mu),
\]
one has
\[
\boxed{
\sum_{t=1}^{\infty}
\sum_{\substack{b\in\{0,1\}\\p_{\omega_{<t}}(b)>0}}
p_{\omega_{<t}}(b)
\log\frac{p_{\omega_{<t}}(b)}{r_{\omega_{<t}}(b)}
<\infty.
}
\tag{17}
\]

Consequently,
\[
\sum_t\sum_b
\bigl(\sqrt{p_{\omega_{<t}}(b)}
-\sqrt{r_{\omega_{<t}}(b)}\bigr)^2<\infty,
\tag{18}
\]
\[
\sum_t\sum_b
\bigl(p_{\omega_{<t}}(b)-r_{\omega_{<t}}(b)\bigr)^2<\infty,
\tag{19}
\]
and
\[
\sum_t
\left(1-\sum_b r_{\omega_{<t}}(b)\right)<\infty.
\tag{20}
\]

The locally normalized predictions
\[
\widehat r_x(b)=\frac{q(xb)}{q(x0)+q(x1)}
\]
also have summable KL divergence and squared error.

In particular,
\[
\forall q\in\mathcal A\
\forall\mu\text{ computable}\
\forall\omega\in\mathrm{CR}^{\emptyset'}(\mu),
\]
the requested convergence holds, even for both next symbols.

### Proof

Use natural logarithms. For \(\mu(x)>0\), write
\[
R(x)=\frac{q(x)}{\mu(x)}
\]
and
\[
d(x)=\sum_{p_x(b)>0}p_x(b)\log\frac{p_x(b)}{r_x(b)}.
\tag{21}
\]
Domination ensures \(r_x(b)>0\) whenever \(p_x(b)>0\).

Choose a positive rational \(c<c_0\). Define
\[
T(x)=
\log\frac{R(x)}c
+\sum_{y\prec x}d(y)
\qquad\text{if }\mu(x)>0,
\tag{22}
\]
where the sum is over proper prefixes, and set \(T(x)=0\) when \(\mu(x)=0\).

#### Step 1: \(T\) is nonnegative

By Jensen’s inequality,
\[
\begin{aligned}
d(x)
&=-\sum_{p_x(b)>0}p_x(b)
\log\frac{r_x(b)}{p_x(b)}\\
&\ge-\log\sum_{p_x(b)>0}r_x(b)\ge0,
\end{aligned}
\]
because \(\sum_b r_x(b)\le1\).

Also \(R(x)\ge c_0>c\), so the logarithmic term in (22) is nonnegative.

#### Step 2: \(T\) is a \(\mu\)-martingale

On the positive support,
\[
R(xb)=R(x)\frac{r_x(b)}{p_x(b)}
\qquad(p_x(b)>0).
\]
Hence
\[
\sum_b p_x(b)\log R(xb)
=\log R(x)-d(x).
\tag{23}
\]
The new term \(d(x)\) in the prefix sum cancels this decrement:
\[
\sum_b p_x(b)T(xb)=T(x).
\tag{24}
\]
Equivalently,
\[
\mu(x)T(x)=\mu(x0)T(x0)+\mu(x1)T(x1).
\]
At a zero-measure cylinder both children have measure zero, so this identity remains valid.

#### Step 3: \(T\) is computable relative to \(\emptyset'\)

A bounded lower-semicomputable real \(q(x)\) is uniformly computable from \(\emptyset'\), by deciding its c.e. rational lower-cut predicates.

For computable \(\mu\), the predicate \(\mu(x)>0\) is c.e. Thus \(\emptyset'\) can decide which cylinders have zero measure. On positive cylinders, all divisions, logarithms, and finite sums in (21)–(22) are computable relative to that oracle. Zero-probability summands are assigned zero.

Therefore \(T\) is a total nonnegative \(\emptyset'\)-computable \(\mu\)-martingale.

The rational \(c\) need not be extracted effectively from indices for \(q,\mu\). Its existence suffices: fixing it defines one of the martingales quantified over by relative computable randomness.

#### Step 4: Randomness gives summability

Since \(\omega\in\mathrm{CR}^{\emptyset'}(\mu)\),
\[
B:=\sup_nT(\omega_{\le n})<\infty.
\]
The first term in (22) is nonnegative, so
\[
0\le\sum_{t=1}^n d(\omega_{<t})
\le T(\omega_{\le n})\le B.
\]
The increasing partial sums are bounded, proving (17).

#### Step 5: Obtain Hellinger, squared-error, and defect bounds

Let
\[
s(x)=\sum_b r_x(b),\qquad
A(x)=\sum_b\sqrt{p_x(b)r_x(b)}
\]
and
\[
h(x)=\sum_b(\sqrt{p_x(b)}-\sqrt{r_x(b)})^2.
\]
The elementary inequality
\[
-\log u\ge2(1-\sqrt u)
\]
gives
\[
d(x)\ge2(1-A(x))
=h(x)+1-s(x).
\tag{25}
\]
Both terms on the right are nonnegative. Their sums are therefore finite.

Also
\[
(p-r)^2
=(\sqrt p-\sqrt r)^2(\sqrt p+\sqrt r)^2
\le4(\sqrt p-\sqrt r)^2,
\]
which proves (19).

Finally \(s(x)>0\) on the support, and
\[
d(x)=D(p_x\Vert\widehat r_x)-\log s(x).
\tag{26}
\]
Both terms on the right are nonnegative. Thus normalized KL is at most \(d(x)\), giving the normalized conclusions. ∎

### What this proof says about the original gap

The same martingale also gives the familiar expectation bound:
\[
\mathbb E_\mu\sum_t d(\omega_{<t})
\le \log\frac{q(\epsilon)}c.
\tag{27}
\]
Indeed, \(\mathbb E_\mu T(\omega_{\le n})=T(\epsilon)\), and then monotone convergence applies.

The obstacle to replacing relative computable randomness by ordinary ML randomness is now visible in a single formula: **\(T\) is not generally lower semicomputable without the oracle.** The conditional KL terms contain logarithms of ratios of lower-semicomputable quantities with both signs.

The convergence consequence under \(\mathrm{CR}^{\emptyset'}\) appears in Kusum’s 2025 thesis. The explicit KL martingale above avoids relying on that thesis’s proof details. Its mechanism is also closely related to the effective Doob decomposition and KL compensator identity in Huttegger–Walsh–Zaffora Blando. I therefore make no novelty claim for this strengthening in presentation. [kdamini.com](https://kdamini.com/thesispdf.pdf?utm_source=chatgpt.com)

---

## 5. Further fully proved partial results

### 5.1 A guarantee on every ordinary ML-random path

Although cumulative conditional KL need not be finite on every ML path, realized logarithmic loss has a strong pathwise guarantee.

### Theorem 8 — Bounded realized cumulative log-loss difference

For every \(q\in\mathcal A\), every computable probability measure \(\mu\), and every \(\omega\in\mathrm{MLR}(\mu)\),
\[
\sum_{t=1}^{n}
\log\frac{\mu(\omega_t\mid\omega_{<t})}
{q(\omega_t\mid\omega_{<t})}
=O(1)
\qquad(n\to\infty).
\tag{28}
\]
In particular, average realized logarithmic loss difference tends to zero.

#### Proof

Dominance supplies \(c>0\) with \(q\ge c\mu\).

For \(k\ge0\), consider the effectively open set
\[
G_k=\bigcup_{\{x:q(x)>2^k\mu(x)\}}[x].
\]
It is effectively open because \(q\) is lower semicomputable and \(\mu\) is computable.

Take the prefix-minimal strings defining this union. They form a prefix-free set \(S_k\). Therefore
\[
\mu(G_k)
=\sum_{x\in S_k}\mu(x)
\le2^{-k}\sum_{x\in S_k}q(x)
\le2^{-k}.
\]
Thus \((G_k)\) is an ML test. On an ML-random path there is a finite \(B\) such that
\[
c\le\frac{q(\omega_{\le n})}{\mu(\omega_{\le n})}\le B
\qquad\forall n.
\tag{29}
\]

The chain rule telescopes:
\[
\begin{aligned}
\sum_{t=1}^{n}
\log\frac{\mu(\omega_t\mid\omega_{<t})}
{q(\omega_t\mid\omega_{<t})}
&=\log q(\epsilon)
-\log\frac{q(\omega_{\le n})}{\mu(\omega_{\le n})}.
\end{aligned}
\]
Equation (29) bounds this expression above and below. ∎

This does **not** imply Cesàro convergence of absolute or squared prediction errors. The realized log-loss increments can have either sign. Conditional KL averages over the possible next symbols before observing which one occurs, and is nonnegative.

### 5.2 A negative subclass genuinely outside \(\mathcal C\)

Merely constructing an element of \(\mathcal A\setminus\mathcal C\) does not remove the prediction obstruction.

### Theorem 9 — Finite-prefix completion preserves nonconvergence

For every \(M\in\mathcal C\) and integer \(h\ge2\), define
\[
q_h(x)=
\begin{cases}
\displaystyle\sum_{|y|=h-|x|}M(xy),&|x|<h,\\[1ex]
M(x),&|x|\ge h.
\end{cases}
\tag{30}
\]
Then \(q_h\in\mathcal A\setminus\mathcal C\). Moreover, there are \(\alpha\in\mathrm{MLR}(\lambda)\) and \(\eta>0\) for which the large-error times of \(q_h\) have positive upper density. The same holds for its normalized predictor.

#### Proof

Each altered value is a finite sum of lower-semicomputable values, so \(q_h\) is enumerable.

For \(|x|<h\), its children partition the depth-\(h\) descendants, giving
\[
q_h(x)=q_h(x0)+q_h(x1).
\]
At and below depth \(h\), the original semimeasure inequalities hold. Also
\[
q_h(\epsilon)\le M(\epsilon)\le1.
\]
Thus \(q_h\) is a semimeasure.

All its values are positive. Only finitely many values differ from \(M\), so
\[
d:=\min\left(
1,\min_{|x|<h}\frac{q_h(x)}{M(x)}
\right)>0.
\]
Therefore \(q_h\ge dM\), which proves universal dominance.

Every effective universal mixture has strictly positive defect at every node: its components include, with positive weight, the computable semimeasure that follows the prefixes of that node and terminates there. In contrast, \(q_h\) has zero defect above depth \(h\), including at a nonempty node. Hence \(q_h\notin\mathcal C\).

Take a counterexample path \(\alpha\) for \(M\) from (2). For \(t>h\), both the parent and child in the conditional ratio are unchanged:
\[
q_h(\alpha_t\mid\alpha_{<t})
=M(\alpha_t\mid\alpha_{<t}).
\]
The same eventual equality holds for normalized conditionals. Finitely many altered times do not change upper density. ∎

This is a corollary of the class-separation and nonconvergence constructions, not a new resolution of their remaining case.

For the path supplied by this theorem, writing
\[
e_t=q_h(\alpha_t\mid\alpha_{<t})-\tfrac12,
\]
we have
\[
\limsup_n\frac1n\sum_{t\le n}|e_t|>0,
\qquad
\limsup_n\frac1n\sum_{t\le n}e_t^2>0.
\]
Indeed, the averages are bounded below by \(\eta\), respectively \(\eta^2\), times the proportion of large-error times.

Likewise, convergence cannot hold along a density-one set of times: convergence there would force every fixed-threshold error set to have density zero.

### 5.3 What the proposed restrictions do and do not buy

Three distinctions prevent misleading partial answers:

- **Computable Bernoulli or finite-state sources:** these classes include fair coin. Thus they do not bypass the negative result for every effective universal mixture. Whether some special \(q\in\mathcal A\setminus\mathcal C\) succeeds for all computable Bernoulli sources is not answered here.
- **Schnorr randomness:** this is weaker than ML randomness, so requiring convergence on all Schnorr-random paths enlarges the target set. It does not remove the existing ML counterexamples.
- **Weak \(2\)-randomness or density randomness:** one cannot simply apply a theorem about left-c.e. martingales to \(q/\mu\), which is generally only a supermartingale. The density-randomness characterization in Miyabe–Nies–Zhang explicitly concerns martingales. I do not claim that it settles this intermediate case. [arxiv.org](https://arxiv.org/pdf/1411.0732?utm_source=chatgpt.com)

---

## 6. Assessment and the remaining research targets

### Confidence and novelty ledger

| Result | Assessment | What remains to check |
|---|---|---|
| Proposition 1: enumerable subtraction can fail | High confidence; complete proof | No mathematical gap identified |
| Proposition 2: fixed-mixture equivalence | High confidence; exact algebra | No gap; crucially does not assert every \(q_0\in\mathcal A\) is bad |
| Proposition 3: monotone damping obstruction | High confidence; complete proof | Applies to observed-symbol predictions and the stated architecture |
| Proposition 4: summable capped mixtures fail dominance | High confidence; complete proof | Enumerability needs effective coefficients; non-dominance does not |
| Proposition 5 and its application to HM \(W\) | High confidence; complete proof | The finite-head computability is nonuniform, as explicitly allowed |
| Proposition 6: normalized enumerable measures are excluded | High confidence; complete proof | Does not address arbitrary noncomputable root scaling |
| Theorem 7: relative computable randomness gives summable KL | High confidence; effectivity and zero cylinders checked | Not mechanically formalized; novelty not claimed |
| Theorems 8–9 | High confidence; standard arguments/corollaries | Not mechanically formalized |
| “No settlement located by November 2026” | A search finding, not a theorem | A missed or unindexed publication remains possible |

There are three concrete directions left after these exclusions.

**A negative proof needs an effective operation beyond pointwise domination.** The removable-component argument cannot be justified by the existing hypotheses. A successful replacement would need a different enumerable test, coding construction, or structural theorem about dominant semimeasures.

**A positive construction needs more than attenuation of an identifiable bad component.** Fixed mixing, prefix-monotone damping, and summable \(W\)-caps do not work. A viable construction may have to redistribute mass while keeping the final semimeasure enumerable and above a fixed universal lower bound, without requiring an enumerable residual after subtraction.

**The randomness threshold is a useful separate problem.** The explicit martingale \(T\) in (22) provides a precise object to study. Ordinary ML randomness does not control it from the available effectivity, while \(\emptyset'\)-computable randomness does. Proving that a weaker randomness notion controls this particular family of martingales would be a meaningful partial advance.

The strongest completed positive statement in this report is therefore (17), and the exact unresolved step toward 2.3A is lowering its randomness requirement without losing control of the nonnegative cumulative prediction error.

---

## 7. Sources opened and checked

I opened the primary texts listed below and inspected the relevant statements or sections. “Opened” does not mean I independently verified every theorem in a paper.

| Source | Identifier and material inspected |
|---|---|
| **Lattimore & Hutter**, *On Martin-Löf (Non-)Convergence of Solomonoff’s Universal Mixture* (2015) | **DOI: 10.1016/j.tcs.2014.12.004.** Opened author PDF; inspected Theorems 6 and 13, auxiliary-mixture step, and open problems. [hutter1.net](https://www.hutter1.net/publ/mnonconvx.pdf?utm_source=chatgpt.com) |
| **Wood, Sunehag & Hutter**, *(Non-)Equivalence of Universal Priors* (2013 proceedings; 2011 preprint) | **arXiv:1111.3854; DOI: 10.1007/978-3-642-44958-1_33.** Opened full PDF; inspected class equivalence, defect conditions, and strict inclusion. [arxiv.org](https://arxiv.org/pdf/1111.3854?utm_source=chatgpt.com) |
| **Hutter & Muchnik**, *On Semimeasures Predicting Martin-Löf Random Sequences* (2007) | **arXiv:0708.2319; DOI: 10.1016/j.tcs.2007.03.040.** Opened full PDF; inspected \(W\), quasimeasures, and Theorem 19. [arxiv.org](https://arxiv.org/pdf/0708.2319?utm_source=chatgpt.com) |
| **Milovanov**, *Prediction and MDL for infinite sequences* (2024) | **DOI: 10.1007/s00224-024-10180-0; related preprint arXiv:2005.03467.** Opened published text/PDF and preprint landing page; inspected measure convention and Theorems 4 and 7. [link.springer.com](https://link.springer.com/content/pdf/10.1007/s00224-024-10180-0.pdf?utm_source=chatgpt.com) |
| **Miyabe**, *An Optimal Superfarthingale and Its Convergence over a Computable Topological Space* (2013; conference 2011) | **DOI: 10.1007/978-3-642-44958-1_21.** Opened author PDF, including its convergence section. [kenshi.miyabe.name](https://kenshi.miyabe.name/wordpress/wp-content/uploads/2011/06/optpred_lncs.pdf?utm_source=chatgpt.com) |
| **Miyabe, Nies & Zhang**, *Using Almost-Everywhere Theorems from Analysis to Study Randomness* (2016) | **arXiv:1411.0732; DOI: 10.1017/bsl.2016.10.** Opened PDF; checked that Theorem 3.3 concerns left-c.e. martingales. [arxiv.org](https://arxiv.org/pdf/1411.0732?utm_source=chatgpt.com) |
| **Kusum**, *Inductive Success of Semimeasures on Random Sequences* (July 2025) | Opened [CMU MSc thesis PDF](https://kdamini.com/thesispdf.pdf), especially Sections 6–8. It studies relative computable randomness and reports a difference-randomness counterexample. No arXiv ID or DOI located. [kdamini.com](https://kdamini.com/thesispdf.pdf?utm_source=chatgpt.com) |
| **Huttegger, Walsh & Zaffora Blando**, *Algorithmic randomness and the weak merging of computable probability measures* (2025–2026) | **arXiv:2504.00440.** Opened v3 HTML; inspected effective Doob decomposition and KL identities. Its setting is computable probability measures, so its theorems do not directly supply an enumerable universal semimeasure. [arxiv.org](https://arxiv.org/html/2504.00440v3?utm_source=chatgpt.com) |
| **Steifer**, *A Note on the Learning-Theoretic Characterizations of Randomness and Convergence* (online 2021; volume 2022) | **DOI: 10.1017/S1755020321000125.** Opened full HTML. An actual citer of LH2015; Proposition 4.17 requires computable approximating functions and does not directly apply to the conditionals here. [Cambridge Core](https://www.cambridge.org/core/journals/review-of-symbolic-logic/article/note-on-the-learningtheoretic-characterizations-of-randomness-and-convergence/BEB98143DA5F2FF4A378B5C7B07B5EC9?utm_source=chatgpt.com) |
| **Saarinen**, *Limits of Solomonoff Induction* (2025) | Opened institutional thesis **ILLC MoL-2025-11**, particularly Theorem 4.1. Its formal hypothesis is a universal mixture; it does not settle \(\mathcal A\setminus\mathcal C\). No arXiv ID or DOI located. [eprints.illc.uva.nl](https://eprints.illc.uva.nl/id/eprint/2380/1/MoL-2025-11.text.pdf?utm_source=chatgpt.com) |
| **Bauwens & Kuznetsov**, *Solomonoff induction of selected bits and online classification* (2026) | **arXiv:2610.18632**, v2 dated **19 November 2026**. Opened abstract and full HTML; its selected-bit and classification results do not assert the ML-path convergence sought here. [arxiv.org](https://arxiv.org/html/2610.18632v2?utm_source=chatgpt.com) |
| **Hutter, Quarel & Catt**, *An Introduction to Universal Artificial Intelligence* (2024) | **DOI: 10.1201/9781003460299.** Opened author PDF; checked §3.12, printed p. 171. Its compressed historical discussion does not state a construction satisfying the dominance requirement of 2.3A. [hutter1.net](https://www.hutter1.net/publ/uaibook2.pdf?utm_source=chatgpt.com) |

**The original quantifier remains unresolved in this attempt:**
\[
\exists q\in\mathcal A\
\forall\mu\text{ computable}\
\forall\omega\in\mathrm{MLR}(\mu):
\quad
q(\omega_t\mid\omega_{<t})
-\mu(\omega_t\mid\omega_{<t})\to0.
\]
The results above narrow several plausible approaches and provide complete theorems that can be used independently of a future solution.