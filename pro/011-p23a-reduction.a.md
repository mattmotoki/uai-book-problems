# Report on 011: the envelope construction, an exact remaining lemma, and the novelty audit

**I do not obtain a resolution of the fair-coin case for every \(q\in\mathcal A\).** I do obtain a negative result for the proposed weighted-envelope construction, a precise account of what its weights preserve, and a more concrete form of the remaining problem.

The principal results are:

- **Every fixed positive weighted sum of these envelopes fails when the base is an effective universal mixture.** The failure occurs on a fair-coin Martin-Löf random sequence and persists after normalization.
- **The same construction also fails for an explicit family of bases that are nowhere locally universal mixtures.** Thus the obstruction extends beyond bases in \(\mathcal C\).
- **Increasing the envelope threshold with depth gives convergence on every fair-coin ML-random sequence**, while preserving lower semicomputability. Its surviving measure is exactly a constant multiple of fair coin, so it loses universal dominance.
- **The unresolved fair-coin question reduces exactly to the integer-flow lemma in Section 5.** This is the single remaining lemma; I do not claim to prove it.
- The novelty audit requires corrections to the earlier report: **the near-total-defect argument is known, the envelope operator is classical, and Proposition 8 is a standard consequence of known prediction bounds.**

“**Proof confidence: high**” below means that a complete argument is supplied or a precise published theorem is identified, with the relevant hypotheses checked. It does not mean formal verification. For deductions made here, I make no priority claim.

## 1. Definitions and what the individual envelopes actually prove

Let
\[
\lambda(x)=2^{-|x|}.
\]
As before, \(\mathcal A\) consists of uniformly lower-semicomputable continuous semimeasures that multiplicatively dominate every lower-semicomputable semimeasure. Let \(\mathcal C\) denote the effective universal mixtures.

Write
\[
q(b\mid x)=\frac{q(xb)}{q(x)},\qquad
\widehat q(b\mid x)=\frac{q(xb)}{q(x0)+q(x1)}
\]
for ordinary and normalized predictions, and
\[
\Delta_q(x)=q(x)-q(x0)-q(x1),\qquad
\delta_q(x)=\frac{\Delta_q(x)}{q(x)}.
\]

For \(U\in\mathcal A\) and an integer \(K\ge1\), define
\[
H_K^U(x)=
\sup_{\substack{A\text{ finite prefix-free}\\
                 A\subseteq x\{0,1\}^{<\mathbb N}}}
\sum_{y\in A}\max\{\lambda(y),U(y)/K\},
\]
where the one-element set \(\{x\}\) is allowed, and put
\[
Q_K^U(x)=\frac{K}{K+1}H_K^U(x).
\]
Also define the bounded-deficiency layer
\[
P_K[U]=
\left\{\omega:\forall n,\ 
U(\omega_{\le n})\le K\lambda(\omega_{\le n})\right\}.
\]

### Theorem A — Envelope properties and the precise convergence guarantee

For every \(U\in\mathcal A\) and every integer \(K\ge1\):

1. \(Q_K^U\in\mathcal A\), uniformly in an index for \(U\) and in \(K\), and
   \[
   \lambda\le H_K^U\le\lambda+\frac UK,\qquad
   Q_K^U\ge\frac{U}{K+1}.
   \]

2. At every finite string \(x\) satisfying \(U(x)\le K\lambda(x)\),
   \[
   \Delta_{Q_K^U}(x)=0.
   \]

3. \(P_K[U]\) is effectively closed,
   \[
   \lambda(P_K[U])\ge1-\frac1K,
   \qquad
   \bigcup_{K\ge1}P_K[U]=\operatorname{MLR}(\lambda).
   \]

4. Put \(R_K=H_K^U-\lambda\). If every prefix of \(x\) satisfies the layer bound, then
   \[
   0\le R_K(x)
   \le
   \min\left\{\frac{U(x)}K,\,
               2\lambda([x]\setminus P_K[U])\right\}.
   \]
   Consequently, writing
   \[
   d_K(x)=\lambda(P_K[U]^c\mid[x]),
   \]
   for both \(b\in\{0,1\}\),
   \[
   \left|Q_K^U(b\mid x)-\frac12\right|
   \le
   \min\left\{\frac14,\frac{d_K(x)}{1+2d_K(x)}\right\}
   \le d_K(x).
   \]

In particular, for every density-one point \(\omega\) of \(P_K[U]\), ordinary and normalized predictions of \(Q_K^U\) converge to \(1/2\).

**Proof confidence: high.**  
**Attribution:** the envelope operation is classical; the particular layer specialization and quantitative estimate are discussed in the audit below.

#### Proof

Every finite prefix-free sum in the definition is bounded by
\[
\lambda(x)+U(x)/K.
\]
The supremum is uniformly lower semicomputable. Separating cutsets containing \(x\) from those lying below its children gives
\[
H_K^U(x)=
\max\left\{U(x)/K,\ H_K^U(x0)+H_K^U(x1)\right\}.
\]
Here the child sum is at least \(\lambda(x)\). This proves the semimeasure property, the bounds, and exact additivity when \(U(x)\le K\lambda(x)\).

The first crossings of \(U(x)>K\lambda(x)\) form a prefix-free set. Their total \(\lambda\)-mass is at most \(1/K\). Effective closedness follows from lower semicomputability of \(U\). The equality of the union with the ML-random sequences is the usual universal-semimeasure characterization of randomness. An opened source stating this characterization explicitly is Barmpalias–Shen, Section 1. [arxiv.org](https://arxiv.org/pdf/2111.00516?utm_source=chatgpt.com)

For the quantitative estimate, one may complete finite cutsets using the baseline \(\lambda\), obtaining
\[
R_K(x)=
\sup_A\sum_{y\in A}\bigl(U(y)/K-\lambda(y)\bigr)_+.
\]
Group the positive summands according to their first crossing \(s\) below \(x\). Since the parent \(s^-\) has not crossed,
\[
U(s)\le U(s^-)\le K\lambda(s^-)=2K\lambda(s).
\]
The semimeasure inequality therefore gives
\[
R_K(x)\le
\sum_{\text{first crossings }s}\frac{U(s)}K
\le2\lambda([x]\setminus P_K[U]).
\]

At a good node, \(R_K(x)=R_K(x0)+R_K(x1)\). Thus
\[
\left|\frac{H_K^U(xb)}{H_K^U(x)}-\frac12\right|
\le
\frac{R_K(x)}{2(\lambda(x)+R_K(x))}.
\]
Now use
\[
R_K(x)/\lambda(x)\le\min\{1,2d_K(x)\}.
\]
Scaling does not change conditionals, and additivity makes ordinary and normalized conditionals equal at these nodes. ∎

**The distinction needed for the proposed extension is this:** Theorem A gives exact additivity on the whole layer. Its full convergence conclusion uses density one. Exact additivity by itself does not establish that \(Q_K^U\) is correct at every point of \(P_K[U]\).

## 2. Fixed weights: what survives, and an actual negative theorem

Let \((w_K)_{K\ge1}\) be uniformly computable nonnegative weights with
\[
0<s:=\sum_Kw_K\le1,
\]
and define
\[
F(U)=q_w^U:=\sum_Kw_KQ_K^U.
\]
This includes \(w_K=2^{-K}\). Starting the sum at \(K=3\) instead makes no difference to the negative conclusion below.

### Theorem B — Exact analysis of the weighted sum

For every \(U\in\mathcal A\) and every such weight sequence, let
\[
k_0=\min\{K:w_K>0\}.
\]
Then:

1. \(q_w^U\in\mathcal A\). In particular, neither lower semicomputability nor dominance breaks:
   \[
   q_w^U\ge
   \left(\sum_K\frac{w_K}{K+1}\right)U.
   \]

2. Its zero-defect region is exactly that of the smallest-threshold component:
   \[
   \boxed{\quad
   \Delta_{q_w^U}(x)=0
   \iff
   \Delta_{Q_{k_0}^U}(x)=0.
   \quad}
   \]

3. Every positively weighted component retains a uniformly positive posterior weight:
   \[
   \boxed{\quad
   \frac{w_KQ_K^U(x)}{q_w^U(x)}
   \ge
   \frac{w_Kk_0}{s(K+1)}
   \quad}
   \]
   for every finite string \(x\).

4. For every \(J\) for which
   \[
   T_J=\sum_{K\ge J}w_KQ_K^U
   \]
   is nonzero,
   \[
   \left|T_J(b\mid x)-\frac12\right|
   \le\frac{U(x)}{2J\lambda(x)}.
   \]
   Hence on \(P_L[U]\), the tail predictor has error at most \(L/(2J)\), uniformly in time.

5. For every \(U\in\mathcal A\), there is no \(q\in\mathcal A\) that is exactly additive at every prefix of every \(P_K[U]\), simultaneously for all \(K\).

**Proof confidence: high.**  
**Novelty assessment:** the calculations and their application are proved here; priority is not established.

#### Proof

The first assertion follows by summing the lower bounds in Theorem A.

For the defect assertion, set
\[
E_K=KH_K^U.
\]
This is the envelope of \(\max\{K\lambda,U\}\), so \(E_K\) increases with \(K\). Its recursion gives
\[
\Delta_{E_K}(x)=
\bigl(U(x)-E_K(x0)-E_K(x1)\bigr)_+.
\]
Thus \(\Delta_{E_K}(x)\) decreases with \(K\), and so does
\[
\Delta_{Q_K^U}(x)=\frac{\Delta_{E_K}(x)}{K+1}.
\]
Since defects are nonnegative and
\[
\Delta_{q_w^U}(x)=\sum_Kw_K\Delta_{Q_K^U}(x),
\]
the second assertion follows.

For posterior weights, \(H_K^U\le H_{k_0}^U\) when \(K\ge k_0\), while
\[
KH_K^U\ge k_0H_{k_0}^U.
\]
Therefore
\[
q_w^U\le sH_{k_0}^U,\qquad
Q_K^U\ge\frac{k_0}{K+1}H_{k_0}^U,
\]
which gives the displayed lower bound.

For the tail, write
\[
T_J=A_J\lambda+S_J,
\]
where
\[
A_J=\sum_{K\ge J}\frac{w_KK}{K+1},
\qquad
S_J=\sum_{K\ge J}\frac{w_KK}{K+1}R_K.
\]
The function \(S_J\) is a nonnegative semimeasure, and
\[
S_J\le B_JU,\qquad
B_J=\sum_{K\ge J}\frac{w_K}{K+1},
\qquad
\frac{B_J}{A_J}\le\frac1J.
\]
Consequently,
\[
\left|T_J(b\mid x)-\frac12\right|
\le
\frac{S_J(x)}{2(A_J\lambda(x)+S_J(x))}
\le\frac{U(x)}{2J\lambda(x)}.
\]

Finally, every finite string extends to an ML-random sequence, and every such sequence belongs to some \(P_K[U]\). Exact additivity on all these layers would therefore imply additivity at every finite string. A member of \(\mathcal A\) cannot be additive everywhere; this follows from the established near-total-defect argument, or from Theorem J below with \(f=0\). ∎

On a particular layer \(P_L[U]\), all components with \(K\ge L\) are additive along the path. The remaining defects come from the finitely many components with \(K<L\). Theorem B shows why those components cannot simply be declared asymptotically negligible: each has a positive posterior floor.

These calculations identify the obstruction, but they do not alone prove nonconvergence—prediction biases can cancel. The following theorem supplies the missing negative argument.

### Theorem C — Every fixed weighted-envelope construction over a mixture base fails

For every \(U\in\mathcal C\) and every weight sequence as above, there exist
\[
\omega\in\operatorname{MLR}(\lambda)
\quad\text{and}\quad \varepsilon>0
\]
such that
\[
\overline d\left\{
t:q_w^U(\omega_t\mid\omega_{<t})>
\frac12+\varepsilon
\right\}>0.
\]
The same \(\omega\) witnesses nonconvergence of the normalized predictions.

More generally, this conclusion holds whenever \(U\in\mathcal A\) has a finite subtree restriction
\[
U^\tau(x):=U(\tau x)
\]
belonging to \(\mathcal C\).

**Proof confidence: high.**  
**Attribution:** this is a deduction from the envelope identity below and Lattimore–Hutter’s nonconvergence theorem.

#### Proof

Choose \(K_0\) with \(w_{K_0}>0\).

First, every \(U\in\mathcal A\) has a subtree on which its density relative to \(\lambda\) is uniformly arbitrarily large. To see this, let \(\mu\) be the computable probability measure that generates zeros with probability \(3/4\) until the first one, and thereafter generates fair-coin bits. For every \(n\) and every \(y\),
\[
\frac{\mu(0^n1y)}{\lambda(0^n1y)}
=
\frac12\left(\frac32\right)^n.
\]
Since \(U\ge c\mu\) for some \(c>0\), there is a finite string \(\sigma\) such that
\[
U(z)\ge K_0\lambda(z)\qquad\forall z\succeq\sigma.
\]

On this entire subtree, the envelope is exactly the original semimeasure, scaled:
\[
H_{K_0}^U(z)=U(z)/K_0,
\qquad
Q_{K_0}^U(z)=U(z)/(K_0+1).
\]
Indeed, every payoff in the defining supremum equals \(U/K_0\); the semimeasure inequality bounds every prefix-free sum by \(U(z)/K_0\), and the singleton \(\{z\}\) attains that bound.

Next, finite subtree restrictions preserve membership in \(\mathcal C\). If
\[
U=\sum_i a_i\nu_i,
\]
then
\[
U^\sigma=\sum_i a_i\nu_i(\sigma\cdot).
\]
The restricted enumeration still contains every enumerable semimeasure: any such semimeasure can be embedded below \(\sigma\), with its root value assigned along the stem and zero assigned off that stem and subtree.

Therefore
\[
(q_w^U)^\sigma
=
\frac{w_{K_0}}{K_0+1}U^\sigma
+
\sum_{K\ne K_0}w_K(Q_K^U)^\sigma
\]
is itself an effective universal mixture. The total displayed coefficient mass is at most \(s\le1\).

Apply Lattimore–Hutter. Their Theorem 6 gives failure on a fair-coin random sequence; Theorem 13, including its overprediction argument, gives the normalized conclusion on the same sequence. I opened and checked both statements in the full paper, *On Martin-Löf (non-)convergence of Solomonoff’s universal mixture*, DOI **10.1016/j.tcs.2014.12.004**. [hutter1.net](https://www.hutter1.net/publ/mnonconvx.pdf?utm_source=chatgpt.com)

If \(\alpha\) is the resulting random sequence for \((q_w^U)^\sigma\), then \(\omega=\sigma\alpha\) is ML-random, and the predictions after \(\sigma\) agree exactly. Finite prefixing preserves upper density.

If only \(U^\tau\in\mathcal C\), perform the same construction inside that subtree. ∎

Thus the proposed sum
\[
\sum_K2^{-K}Q_K
\]
has a definite negative answer for every universal-mixture base. Its bad-prediction trees have a random infinite branch for at least one error threshold and one bounded-deficiency layer.

## 3. A moving threshold succeeds on randoms—and loses dominance

The tail estimate suggests letting the threshold increase with depth. That construction can be completed exactly.

### Theorem D — Depth-dependent envelopes converge everywhere on fair-coin randoms

For every \(U\in\mathcal A\) and every computable nondecreasing sequence of positive rational numbers
\[
K_n\longrightarrow\infty,
\]
put
\[
c=\frac{K_0}{K_0+1},
\qquad
p(x)=cH_{K_{|x|}}^U(x).
\]
Then:

1. \(p\) is a lower-semicomputable semimeasure, and
   \[
   c\lambda(x)\le p(x)
   \le c\lambda(x)+\frac{cU(x)}{K_{|x|}},
   \qquad
   p(x)\ge\frac{cU(x)}{K_{|x|}}.
   \]

2. For every finite string \(x\), \(n=|x|\), and \(b\in\{0,1\}\), writing \(D_x=U(x)/\lambda(x)\),
   \[
   \left|p(b\mid x)-\frac12\right|
   \le
   \frac{D_x}{2(K_n+D_x)}.
   \]
   The same bound holds for normalized predictions.

3. For every \(\omega\in\operatorname{MLR}(\lambda)\), both predictions converge to \(1/2\).

4. The measure part of \(p\) is exactly
   \[
   \overline p(x):=
   \lim_{m\to\infty}
   \sum_{\substack{|y|=m\\y\succeq x}}p(y)
   =c\lambda(x).
   \]
   Consequently, for every probability measure \(\mu\),
   \[
   p\text{ multiplicatively dominates }\mu
   \iff
   \lambda\text{ multiplicatively dominates }\mu.
   \]
   In particular, \(p\notin\mathcal A\).

**Proof confidence: high.**  
**Novelty assessment:** explicit construction and estimates proved here; priority not established.

#### Proof

Since \(H_K^U\) decreases with \(K\),
\[
p(x0)+p(x1)
\le
c\bigl(H_{K_n}^U(x0)+H_{K_n}^U(x1)\bigr)
\le p(x).
\]
The root bound and lower semicomputability follow directly.

Write \(p=c\lambda+R\). Then \(R\) is a nonnegative semimeasure and
\[
R(x)\le cU(x)/K_n.
\]
Hence
\[
\left|p(b\mid x)-\frac12\right|
\le
\frac{R(x)}{2(c\lambda(x)+R(x))}
\le
\frac{D_x}{2(K_n+D_x)}.
\]
For normalized predictions, replace \(R(x)\) in the first bound by \(R(x0)+R(x1)\le R(x)\).

On an ML-random sequence, \(D_x\) is bounded along its prefixes, proving convergence.

Finally, for \(m\ge|x|\),
\[
c\lambda(x)
\le
\sum_{\substack{|y|=m\\y\succeq x}}p(y)
\le
c\lambda(x)+\frac{cU(x)}{K_m}.
\]
Taking limits proves the measure-part identity. If \(p\ge d\mu\), summing at level \(m\) and taking limits gives \(c\lambda\ge d\mu\). The converse follows from \(p\ge c\lambda\).

In particular, \(p\) cannot dominate a computable Dirac measure. ∎

This locates the failure of this repair precisely: **enumerability survives, convergence holds, and universal dominance is lost.** The surviving lower bound on \(U\) has the depth-dependent coefficient \(c/K_n\), which tends to zero.

## 4. Why extracting a mixture subtree cannot settle the general case

Theorem C suggests trying to prove that every member of \(\mathcal A\) has a mixture subtree. That proposed lemma is false.

### Theorem E — Granularization preserves all asymptotic predictions

For every \(U\in\mathcal A\), there is a rational-valued \(G(U)\in\mathcal A\) with the following properties.

For \(n=|x|\), set
\[
S(x)=\frac{\lambda(x)}{n+1},
\qquad
h_n=\frac{2^{-n}}{2(n+1)(n+2)},
\qquad
v(x)=\frac{U(x)+S(x)}2.
\]
Define \(G(U)(x)\) to be the greatest nonnegative integer multiple of \(h_n\) **strictly below** \(v(x)\).

Then
\[
G(U)=\frac U2+e,
\]
where \(e\) is a nonnegative semimeasure satisfying
\[
\frac{\lambda(x)}{2(n+2)}
\le e(x)<
\frac{\lambda(x)}{2(n+1)}.
\]
If \(U\ge a\lambda\), \(a>0\), then
\[
\sup_{\substack{|x|=n\\b\in\{0,1\}}}
|G(U)(b\mid x)-U(b\mid x)|
\le\frac1{a(n+1)},
\]
and
\[
\sup_{\substack{|x|=n\\b\in\{0,1\}}}
|\widehat{G(U)}(b\mid x)-\widehat U(b\mid x)|
\le\frac1{a(n+2)}.
\]

Thus \(G(U)\) and \(U\) have the same asymptotic prediction-convergence behavior along every infinite sequence, against every target predictor.

**Proof confidence: high.**  
**Attribution:** the safety-margin-and-rounding construction is known. Barmpalias–Shen explain Levin’s construction in Proposition 2 and its subsequent refinement: **arXiv:2111.00516**, DOI **10.1016/j.tcs.2023.113693**. The explicit estimates here are derived below. [arxiv.org](https://arxiv.org/pdf/2111.00516?utm_source=chatgpt.com)

#### Proof

Strict rounding is lower semicomputable: enumerate the value \(kh_n\) once a lower approximation to \(v(x)\) exceeds it. Also,
\[
v(x)-h_n\le G(U)(x)<v(x).
\]
The safety margin satisfies
\[
\Delta_S(x)=\frac{\lambda(x)}{(n+1)(n+2)}=2h_n,
\]
so
\[
\Delta_v(x)=\frac12\Delta_U(x)+h_n.
\]
Rounding loses at most \(h_n\) at the parent and never increases the children. Therefore
\[
\Delta_{G(U)}(x)\ge\frac12\Delta_U(x).
\]
This proves both the semimeasure property and the semimeasure property of \(e=G(U)-U/2\). The stated bounds on \(e\) follow by subtraction, and \(G(U)\ge U/2\) proves universality.

For ordinary prediction, put \(r=U(b\mid x)\). Then
\[
G(U)(b\mid x)-r
=
\frac{e(xb)-r e(x)}{U(x)/2+e(x)}.
\]
Since \(0\le r\le1\) and \(0\le e(xb)\le e(x)\), the numerator’s absolute value is at most \(e(x)\). The bound follows from \(U(x)\ge a\lambda(x)\).

For normalized predictions, use the same calculation with the child-sum denominators and
\[
e(x0)+e(x1)<\frac{\lambda(x)}{2(n+2)},\qquad
U(x0)+U(x1)\ge a\lambda(x).
\]
∎

### Theorem F — Universal rational-valued semimeasures are nowhere locally mixtures

For every \(M\in\mathcal C\) and every nonempty finite string \(x\), \(M(x)\) is noncomputable.

Consequently, for every \(U\in\mathcal A\) and every finite string \(\sigma\),
\[
G(U)^\sigma\notin\mathcal C.
\]
In particular,
\[
\forall q\in\mathcal A\ \exists\sigma\;(q^\sigma\in\mathcal C)
\]
is false.

Moreover, if \(U\in\mathcal C\), the semimeasure residual
\[
e=G(U)-U/2
\]
from Theorem E is not lower semicomputable, while \(G(U)\) still inherits \(U\)’s prediction failures.

**Proof confidence: high.**  
**Novelty assessment:** elementary consequences of granularization and effective mixtures; no priority claim.

#### Proof

Choose a noncomputable left-c.e. real \(\Omega\in(0,1)\). There is an enumerable semimeasure having value \(\Omega\) on the prefixes of a fixed nonempty \(x\), and zero elsewhere. It occurs in the universal mixture \(M\) with positive weight \(w\).

Choose a rational \(r\) with \(0<r<w\). Then
\[
M(x)=r\Omega+\beta
\]
with \(\beta\) left-c.e.; this remains true when the mixture weights are merely lower semicomputable. If \(M(x)\) were computable, \(r\Omega=M(x)-\beta\) would also be upper semicomputable, a contradiction.

Every value \(G(U)(\sigma0)\) is rational, so \(G(U)^\sigma\) cannot be a universal mixture.

Finally, if \(U\in\mathcal C\) and \(e(x)\) were left-c.e. at a nonempty \(x\), the identity
\[
U(x)/2=G(U)(x)-e(x)
\]
would make \(U(x)\) upper semicomputable, again a contradiction. Prediction failure transfers by Theorem E. ∎

Rational-valued here does **not** mean uniformly computable. The unresolved information is when the lower approximation to each rational value has finished changing.

The negative result for envelopes can be pushed through this rounding operation as well.

### Theorem G — Weighted envelopes also fail for explicit nowhere-mixture bases

For every \(M\in\mathcal C\), let \(U=G(M)\). For every weight sequence from Section 2, \(F(U)\) fails on a fair-coin ML-random sequence, both ordinarily and after normalization.

**Proof confidence: high.**  
**Novelty assessment:** deduction proved here; priority not established.

#### Proof

First, whenever \(U=V+e\) with \(e\ge0\) a semimeasure—whether or not \(e\) is enumerable—
\[
0\le H_K^U(x)-H_K^V(x)\le e(x)/K.
\]
This follows by comparing the payoffs on each finite cutset and using
\[
\sum_{y\in A}e(y)\le e(x).
\]

Put
\[
A=\sum_K\frac{w_KK}{K+1}>0,\qquad
B=\sum_K\frac{w_K}{K+1}.
\]
Then
\[
0\le F(U)-F(V)\le Be,\qquad F(V)\ge A\lambda.
\]
A direct ratio comparison gives
\[
|F(U)(b\mid x)-F(V)(b\mid x)|
\le\frac{Be(x)}{A\lambda(x)}.
\]

Apply this with \(U=G(M)=M/2+e\) and \(V=M/2\). Theorem E makes the right side at most
\[
\frac{B}{2A(|x|+1)}.
\]
The normalized comparison similarly tends to zero, using the child-sum bound on \(e\).

But \(M/2\in\mathcal C\), so \(F(M/2)\) fails by Theorem C. Uniform asymptotic equivalence transfers its failure to \(F(G(M))\). ∎

Thus neither “the base is outside \(\mathcal C\)” nor “the base has no mixture subtree” is sufficient to rescue the weighted-envelope proposal.

## 5. The exact remaining lemma, on one fixed random closed class

Fix a universal mixture \(\xi\), and fix once and for all
\[
P=P_3[\xi].
\]
By Theorem A, \(P\) is effectively closed, has positive measure, and consists entirely of ML-random sequences.

Continue to use
\[
h_n=\frac{2^{-n}}{2(n+1)(n+2)}.
\]

Call a uniformly computable integer array \(a_s(x)\) **admissible** if:

- \(a_s(x)\) is nonnegative and nondecreasing in \(s\);
- \(a_s(\epsilon)\le4\);
- for every stage \(s\), every string \(x\), and \(n=|x|\),
  \[
  (n+1)\bigl(a_s(x0)+a_s(x1)\bigr)
  \le2(n+3)a_s(x);
  \]
- writing \(a(x)=\lim_s a_s(x)\), there is a constant \(c>0\) such that
  \[
  h_{|x|}a(x)\ge c\xi(x)\qquad\forall x.
  \]

The root and flow bounds make every limit finite. The associated semimeasure is
\[
q_a(x)=h_{|x|}a(x).
\]

### Remaining lemma \(\mathsf{GO}(P)\) — Unproved

For every admissible array \(a_s\), there exist a finite string \(\sigma\), a sequence \(\alpha\in P\), and a rational \(\varepsilon>0\) such that, for infinitely many \(t\), putting
\[
y=\sigma\alpha_{<t},\qquad n=|y|,
\]
one has
\[
\boxed{
\left|(n+1)a(y\alpha_t)-(n+3)a(y)\right|
>
2\varepsilon(n+3)a(y).
}
\]

**Status:** unproved. I assign no proof confidence to its truth.

### Theorem H — This lemma is exactly equivalent to the negative fair-coin answer

The following statements are equivalent:

1. \(\mathsf{GO}(P)\) holds.

2. For every \(q\in\mathcal A\), there exist \(\omega\in\operatorname{MLR}(\lambda)\) and \(\varepsilon>0\) such that
   \[
   \left|q(\omega_t\mid\omega_{<t})-\frac12\right|>\varepsilon
   \quad\text{infinitely often}.
   \]

If \(\mathsf{GO}(P)\) fails, its counterexample array gives a member of \(\mathcal A\) that predicts correctly on every fair-coin ML-random sequence.

Furthermore, on any path satisfying
\[
q_a(x)/\lambda(x)\le L
\]
at all its prefixes,
\[
a(x)\le2L(|x|+1)(|x|+2).
\]
Thus the integer at a node of length \(n\) on that layer can increase at most \(O_L(n^2)\) times.

**Proof confidence: high for the equivalence and the bound.**

#### Proof

The flow inequalities are precisely the semimeasure inequalities, because
\[
\frac{h_{n+1}}{h_n}=\frac{n+1}{2(n+3)}.
\]
In particular,
\[
q_a(b\mid x)=
\frac{(n+1)a(xb)}{2(n+3)a(x)}.
\]
The boxed inequality in \(\mathsf{GO}(P)\) is therefore exactly an ordinary prediction error exceeding \(\varepsilon\).

For \(1\Rightarrow2\), start with arbitrary \(U\in\mathcal A\) and apply Theorem E. Its rounded values have the form \(h_na(x)\).

They admit stagewise admissible flow approximations. Indeed, an enumerable semimeasure has increasing computable rational semimeasure approximations; applying the same safety-margin rounding at every stage preserves the flow inequalities. The lemma gives a random bad path for \(G(U)\), and Theorem E transfers nonconvergence to \(U\).

For \(2\Rightarrow1\), apply statement 2 to \(q_a\), obtaining a bad random sequence \(\omega\). Kučera’s tail theorem supplies a decomposition
\[
\omega=\sigma\alpha,\qquad \alpha\in P.
\]
Removing a finite prefix preserves infinitely many prediction errors. The tail theorem is explicitly stated as Theorem 1 in the opened paper by Bienvenu–Day–Hoyrup–Mezhirov–Shen. [lirmm.fr](https://www.lirmm.fr/~ashen/nafit/2010ergodic.pdf?utm_source=chatgpt.com)

Equivalently, if the lemma is false, the counterexample predictor converges along every \(\sigma\alpha\) with \(\alpha\in P\). Every ML-random sequence has such a decomposition, so it converges on all of them.

Finally,
\[
q_a(x)/\lambda(x)
=\frac{a(x)}{2(n+1)(n+2)},
\]
which gives the polynomial bound. ∎

### Why this remaining lemma is hard

The reduction gives finite integer capacities, even polynomial capacities along a fixed randomness layer. It does not give recognizable stabilization.

For example, a proposed bad edge can guess final integers
\[
a(y)=A,\qquad a(yb)=B.
\]
The lower assertions \(a(y)\ge A\) and \(a(yb)\ge B\) can be witnessed by enumeration. The upper assertions
\[
a(y)\le A,\qquad a(yb)\le B
\]
must survive every later stage. These are exactly the permanent upper promises in the bad-visit trees of report 009.

A computable bound on the number of changes does not give a computable bound on the time of the last change. The construction must coordinate infinitely many such promises while retaining a path through \(P\). Arbitrarily long finite strings of apparent successes do not by themselves produce a coherent infinite branch in the tree of visit times and stabilization promises.

There is also a precise barrier to replacing these promises by sound c.e. certificates.

### Theorem I — Sound c.e. bad-edge certificates cannot witness an ML-random failure

For every \(q\in\mathcal A\), every \(\varepsilon>0\), and every c.e. set \(B\) of distinct strings \(xb\) satisfying
\[
\left|q(b\mid x)-\frac12\right|>\varepsilon,
\]
one has
\[
\sum_{xb\in B}\lambda(xb)<\infty.
\]
Consequently, every \(\lambda\)-ML-random sequence has only finitely many prefixes in \(B\).

**Proof confidence: high.**  
**Attribution:** standard consequence of the expected Hellinger bound and the Solovay-test criterion; this is the status of the previous Proposition 8.

#### Proof

Since \(q\ge c\lambda\), the expected cumulative Hellinger discrepancy is finite. This bounds the total \(\lambda\)-weight of all edges whose prediction discrepancy exceeds a fixed \(\varepsilon\). Any c.e. subset of those edges therefore forms a Solovay test, which an ML-random sequence can enter only finitely often. The relevant expected bound is in Hutter–Muchnik, Lemma 4, **arXiv:cs/0407057**. [hutter1.net](https://www.hutter1.net/ai/mlconvx.pdf?utm_source=chatgpt.com) ∎

The outstanding construction must therefore use non-enumerable information about which apparent bad predictions remain bad. The granular form isolates that issue; it does not remove it.

## 6. A strengthening of the old defect-majorant theorem

The literature audit suggested a useful extension of the old Theorem 5: the null majorant need not be computable.

### Theorem J — No lower-semicomputable null majorant for absolute defects

For every \(q\in\mathcal A\), every uniformly lower-semicomputable function
\[
f:\mathbb N\to[0,\infty)
\quad\text{with}\quad f(n)\to0,
\]
every finite string \(\sigma\), and every \(N\), there exists \(x\succeq\sigma\), \(|x|\ge N\), such that
\[
\boxed{\Delta_q(x)>f(|x|).}
\]

The same construction produces strings extending \(\sigma\) whose relative defects tend to \(1\).

**Proof confidence: high.**  
**Novelty assessment:** this refines the known terminal-output argument. I did not locate this exact lower-semicomputable-majorant formulation in the sources checked; priority is undetermined.

#### Proof

Choose a stem \(\tau\succeq\sigma\) with \(|\tau|\ge N\). For each \(j\ge1\), put
\[
\eta_j=2^{-3j}.
\]
Run the following computable procedure, beginning with output \(x=\tau\). Dovetail searches for either of the positive witnesses
\[
f(|x|)>\eta_j
\quad\text{or}\quad
q(xb)>\eta_j
\]
for some \(b\).

If the first is found, append \(0\). If the second is found, append \(1-b\). Then repeat.

There are finitely many first-type steps, since they occur at distinct lengths at which \(f(n)>\eta_j\). There are finitely many second-type steps, since their abandoned sibling cylinders are pairwise disjoint and each has \(q\)-mass exceeding \(\eta_j\).

Thus the procedure eventually stops extending its output, at some finite \(z_j\). Terminality implies
\[
f(|z_j|)\le\eta_j,\qquad
q(z_j0)\le\eta_j,\qquad q(z_j1)\le\eta_j.
\]

Let \(\nu_j\) be the enumerable semimeasure assigning mass \(1\) to the prefixes printed by this procedure. Recognizing its eventual termination is unnecessary. Then
\[
\nu=\sum_{j\ge1}2^{-j}\nu_j
\]
is an enumerable semimeasure. Universality gives a single constant \(c>0\) with \(q\ge c\nu\). Hence
\[
q(z_j)\ge c2^{-j}
\]
and
\[
\Delta_q(z_j)\ge c2^{-j}-2\eta_j>\eta_j\ge f(|z_j|)
\]
for all sufficiently large \(j\). Also,
\[
\delta_q(z_j)
\ge1-\frac{2\eta_j}{c2^{-j}}
=1-\frac2c\,2^{-2j}\longrightarrow1.
\]
∎

This proof does not furnish a random bad path. For every \(q\ge a\lambda\),
\[
1-\delta_q(x)
=\frac{q(x0)+q(x1)}{q(x)}
\ge\frac{a\lambda(x)}{q(x)}.
\]
Thus relative defects tending to \(1\) force \(q(x)/\lambda(x)\) to become unbounded. A path visiting such defects infinitely often cannot be ML-random. That is why the established defect argument does not settle \(\mathsf{GO}(P)\).

## 7. Novelty audit of the five requested results

The table separates mathematical validity from attribution. **Proof confidence for all five statements is high.** “Not located” means that an exact predecessor was not found in the primary sources examined; it is not a claim of novelty.

| Result in report 009 | Assessment |
|---|---|
| **Theorem 2:** arbitrarily near-total relative defects, locally in every cylinder | **Known argument, with routine localization and extension to \(\mathcal A\).** |
| **Theorem 5:** no computable null upper bound for absolute defects | **Known consequence for universal mixtures; the exact all-\(\mathcal A\) formulation was not located.** Theorem J above strengthens the formulation to lower-semicomputable null majorants. |
| **Theorem 6:** the enumerable universal envelope \(Q_K\), additive on its bounded-deficiency layer | **The envelope operator is classical.** The particular application to these layers was not located as a named theorem. |
| **Theorem 7:** \(R_K(x)\le2\lambda([x]\setminus P_K)\) and the resulting prediction estimate | **Exact quantitative formulation not located.** It is an elementary first-crossing estimate built on the classical envelope. |
| **Proposition 8:** sound c.e. bad-edge certificates form a Solovay test | **Standard corollary of known prediction bounds and the Solovay-test criterion.** It should not be presented as a new result. |

### Previous Theorem 2: the proof is already in the literature

Lattimore–Hutter–Gavane, *Universal Prediction of Selected Bits*, **arXiv:1107.5531**, Lemma 14, proves
\[
\exists\omega\quad
\liminf_n\bigl(M(0\mid\omega_{<n})+M(1\mid\omega_{<n})\bigr)=0.
\]
Its proof uses the same procedure: wait until a child has sufficiently large enumerated mass, then extend into the other child. The paper itself attributes the finite-node version to Li–Vitányi, Exercise 4.5.6. I opened the Lattimore–Hutter–Gavane proof; I did not independently open that textbook exercise. [hutter1.net](https://www.hutter1.net/publ/evenbits.pdf?utm_source=chatgpt.com)

The extension from a fixed universal mixture \(M\) to arbitrary \(q\in\mathcal A\) is immediate from two-sided dominance. If
\[
cM\le q\le CM,
\]
then
\[
\frac{q(x0)+q(x1)}{q(x)}
\le
\frac Cc\,
\frac{M(x0)+M(x1)}{M(x)}.
\]
Localization follows by applying the argument to finite subtree restrictions.

**Correction to the earlier report:** this result should be credited as an established argument and its immediate consequences.

### Previous Theorem 5: a known mixture consequence, with a scope distinction

Wood–Sunehag–Hutter, *(Non-)Equivalence of Universal Priors*, **arXiv:1111.3854**, Lemma 15, proves for every universal mixture \(M\) that
\[
\delta_M(x)\ge c\,2^{-K(|x|)}
\]
for some \(c>0\). Their Theorem 16 also establishes the strict separation between universally dominant semimeasures and universal mixtures. [hutter1.net](https://www.hutter1.net/publ/unipreq.pdf?utm_source=chatgpt.com)

Along \(0^n\), universality gives \(M(0^n)\ge c_0>0\), by dominance of the computable atom \(0^\infty\). Hence
\[
\Delta_M(0^n)\gtrsim 2^{-K(n)}.
\]
The universal discrete semimeasure \(m(n)\asymp2^{-K(n)}\) has no computable null majorant; Gács discusses this explicitly in his opened notes, Section 2.2.2, printed page 42. [cs.bu.edu](https://www.cs.bu.edu/fac/gacs/papers/ait-notes.pdf?utm_source=chatgpt.com)

This gives the computable-majorant obstruction for \(\mathcal C\). It does not automatically transfer to \(\mathcal A\), because multiplicative comparisons of semimeasures do not give comparisons of their absolute defects.

I did not locate the exact all-\(\mathcal A\) statement, or Theorem J’s stronger formulation, in the checked sources. The proof above establishes them without making a priority claim.

### Previous Theorem 6: the envelope operation is textbook machinery

Shen–Uspensky–Vereshchagin, *Kolmogorov Complexity and Algorithmic Randomness*, DOI **10.1090/surv/220**, uses precisely the prefix-free-supremum construction in the proof of Theorem 79, printed page 140. Problem 131(b) gives the related general majorant formulation. I opened the relevant book passage. [old.mccme.ru](https://old.mccme.ru/shen/kolmbook/kolmbook-eng.pdf?utm_source=chatgpt.com)

The specific payoff
\[
\max\{\lambda(x),U(x)/K\}
\]
then gives the normalization, universal dominance, and layer additivity by the short arguments in Theorem A.

**Assessment:** a classical construction with a useful specialization, not a new envelope method.

### Previous Theorem 7: the exact estimate was not located

The first-crossing proof in Theorem A is complete. The nearest density-randomness literature checked includes Miyabe–Nies–Zhang, *Using almost-everywhere theorems from analysis to study randomness*, **arXiv:1411.0732**, DOI **10.1017/bsl.2016.10**. Its relevant equivalences concern density randomness, left-c.e. **martingales**, and integral tests. They do not state this envelope estimate. [arxiv.org](https://arxiv.org/pdf/1411.0732?utm_source=chatgpt.com)

The appropriate description is:

> The envelope operation is classical. The bounded-deficiency specialization and its quantitative density-to-prediction estimate are proved here; an exact prior formulation was not located in the primary sources examined. Priority is undetermined.

In particular, those martingale results should not be cited as a general convergence theorem for arbitrary lower-semicomputable supermartingales.

### Previous Proposition 8: a standard consequence

Hutter–Muchnik’s *Universal Convergence of Semimeasures on Individual Random Sequences*, **arXiv:cs/0407057**, provides the expected Hellinger bound used in Theorem I. The journal treatment is *On semimeasures predicting Martin-Löf random sequences*, DOI **10.1016/j.tcs.2007.03.040**. I opened the arXiv record and the full author-hosted paper. [arxiv.org](https://arxiv.org/abs/cs/0407057?utm_source=chatgpt.com)

Passing from a finite expected error sum to a Solovay test for any sound c.e. collection of fixed-size errors is standard. Proposition 8 is useful in diagnosing the construction problem, but it is not an independent novelty claim.

### Additional sources checked

I also examined the following relevant primary works:

- **Bienvenu–Hölzl–Porter–Shafer**, *Randomness and Semi-measures*, **arXiv:1310.5133**, DOI **10.1215/00294527-3839446**. Its semimeasure-randomness and measure-extraction questions are relevant background; I did not locate the particular envelope or defect-majorant statements there. [arxiv.org](https://arxiv.org/abs/1310.5133?utm_source=chatgpt.com)
- **Leike–Hutter**, *On the Computability of Solomonoff Induction and Knowledge-Seeking*, **arXiv:1507.04124**. It addresses computability classifications of Solomonoff priors and related objects; I did not locate the five statements under audit there. [arxiv.org](https://arxiv.org/abs/1507.04124?utm_source=chatgpt.com)
- **Barmpalias–Shen**, **arXiv:2111.00516**, as used in Theorem E. This is an important attribution: the existence of universal granular, rational-valued semimeasures and the safety-margin rounding method are already known. [arxiv.org](https://arxiv.org/pdf/2111.00516?utm_source=chatgpt.com)

The unresolved mathematical task is now exactly \(\mathsf{GO}(P)\): prove that every admissible universal integer flow has a permanently bad sequence of predictions along some \(\sigma\alpha\), with \(\alpha\) in the one fixed random closed class, or construct an admissible flow for which this never happens. The fixed-weight envelope method is excluded for the substantial classes proved above. The depth-dependent repair gives the desired fair-coin predictions, but its measure-part calculation proves that it cannot supply the required universal semimeasure.