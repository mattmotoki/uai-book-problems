# Follow-up on 2.3A

**I did not obtain a full positive or negative solution to 2.3A.** I did obtain several rigorous results that sharpen the gap:

1. A construction that watches \(q\)’s enumeration proves that **every** \(q\in\mathcal A\) has relative mass loss arbitrarily close to \(1\), arbitrarily deep inside every cylinder.
2. Those witnesses necessarily leave every fixed randomness-deficiency layer. This identifies precisely why that construction does not produce the required ML-random counterexample.
3. Several proposed regularity assumptions on the defect are impossible: there is no universal enumerable additive finite measure, no universal enumerable semimeasure with lower-semicomputable defect, and no computable vanishing bound on its absolute defects.
4. There is an explicit family \(Q_K\in\mathcal A\setminus\mathcal C\) that is **exactly additive throughout an entire bounded-deficiency layer**. It predicts the fair coin correctly at every density-one point of that layer.
5. The full problem has an exact formulation in terms of well-foundedness of explicit **computable trees of successive bad predictions**. For fair coin, there is also an exact reduction to one fixed positive effectively closed class of randoms, using all finite subtree restrictions of the predictor.

There is also a correction to a premise in the question: pointwise dominance \(q\ge c\xi\) does **not** imply that \(q-c\xi\) is a semimeasure.

Throughout, **“derived here” means established by the argument below, with publication novelty unverified**. I make no priority claim. The proved statements below have high proof confidence; unresolved steps are identified explicitly.

---

## 1. Setup and the residual correction

Write

\[
\Delta_q(x)=q(x)-q(x0)-q(x1),
\qquad
\delta_q(x)=\frac{\Delta_q(x)}{q(x)}.
\]

Thus \(\Delta_q\) is the absolute defect and \(\delta_q\) the relative defect. Let

\[
\lambda(x)=2^{-|x|}
\]

be the fair-coin measure.

As in the earlier report, \(\mathcal A\) consists of lower-semicomputable semimeasures with root mass at most \(1\) that multiplicatively dominate every lower-semicomputable semimeasure. Fix a universal enumerable semimeasure \(\xi\). An enumerable semimeasure \(q\) belongs to \(\mathcal A\) exactly when

\[
q\ge c\xi
\]

for some \(c>0\).

The distinction between this class and effective universal mixtures remains essential: universal mixtures form a proper subclass, and the Lattimore–Hutter nonconvergence theorem concerns that mixture class. [hutter1.net](https://www.hutter1.net/publ/unipreq.pdf?utm_source=chatgpt.com)

### Proposition 1: dominance does not give a semimeasure residual

Suppose \(q\ge c\xi\), and set \(r=q-c\xi\). Then \(r\ge0\), but

\[
\Delta_r(x)=\Delta_q(x)-c\Delta_\xi(x).
\]

Consequently,

\[
\boxed{
r\text{ is a semimeasure}
\iff
\Delta_q(x)\ge c\Delta_\xi(x)\quad\text{for every }x.
}
\tag{1}
\]

The root-mass condition is automatic from \(0\le r\le q\).

Thus there are two distinct potential obstacles:

- \(r\) may fail to be lower semicomputable;
- \(r\) may fail to be a semimeasure at all.

The positive construction in Section 4 gives an explicit example where the second failure occurs for **every** positive choice of \(c\).

**Confidence:** high.  
**Novelty:** elementary identity, not a novelty claim.

---

## 2. A subtraction-free adversary for every \(q\in\mathcal A\)

The first substantial result comes directly from watching mass arrive in \(q\)’s enumeration.

### Theorem 2: near-total defects occur densely

For every \(q\in\mathcal A\), every finite string \(\sigma\), every \(N\), and every \(\varepsilon>0\), there is an extension \(x\succeq\sigma\), with \(|x|\ge N\), such that

\[
\frac{q(x0)+q(x1)}{q(x)}<\varepsilon.
\tag{2}
\]

Equivalently,

\[
\boxed{
\sup_{\substack{x\succeq\sigma\\|x|\ge N}}\delta_q(x)=1.
}
\tag{3}
\]

### Proof

Fix an extension \(w\succeq\sigma\) with \(|w|\ge N\). For \(j\ge1\), let

\[
\tau_j=2^{-2j}.
\]

Construct a uniformly enumerable semimeasure \(\nu_j\) by emitting one finite or infinite deterministic path.

First emit \(w\). At the current endpoint \(x\):

1. Watch the lower approximation to \(q\).
2. If it certifies \(q(xb)>\tau_j\) for either child \(b\), emit the opposite bit \(1-b\).
3. Repeat from that child.

The associated semimeasure has value \(1\) on every emitted prefix and \(0\) elsewhere. Its enumeration is effective even though we cannot decide whether another output bit will ever appear.

Every such path is finite. At each successful step, the construction abandons a sibling cylinder of \(q\)-mass greater than \(\tau_j\). These abandoned cylinders are pairwise disjoint. Since the \(q\)-mass of a prefix-free family is at most \(q(\epsilon)\le1\), fewer than \(1/\tau_j\) successful steps are possible.

Let \(x_j\) be the terminal endpoint. Then

\[
q(x_j0)\le\tau_j,
\qquad
q(x_j1)\le\tau_j.
\tag{4}
\]

Otherwise the corresponding strict lower bound would eventually be witnessed, causing another step.

Now combine all these processes into the single enumerable semimeasure

\[
\nu=\sum_{j\ge1}2^{-j}\nu_j.
\]

Universality supplies one constant \(c>0\) such that \(q\ge c\nu\). Hence

\[
q(x_j)\ge c2^{-j}.
\tag{5}
\]

Combining (4) and (5),

\[
\frac{q(x_j0)+q(x_j1)}{q(x_j)}
\le
\frac{2\tau_j}{c2^{-j}}
=
\frac2c\,2^{-j}\longrightarrow0.
\]

Every \(x_j\) extends \(w\), proving the theorem. \(\square\)

The crucial feature is that the terminal endpoints need not be effectively recognizable. The semimeasures that *emit their prefixes* are nevertheless uniformly enumerable, and one domination constant applies to their aggregate.

**Confidence:** high.  
**Novelty:** derived here; publication priority unverified.

### 2.1 Why this does not yield an ML-random counterexample

Choose \(a>0\) with \(q\ge a\lambda\), and put

\[
D_q(x)=\frac{q(x)}{\lambda(x)}.
\]

Then

\[
1-\delta_q(x)
=
\frac{q(x0)+q(x1)}{q(x)}
\ge
\frac{a\lambda(x)}{q(x)}
=
\frac a{D_q(x)}.
\]

Therefore

\[
\boxed{
D_q(x)\ge \frac a{1-\delta_q(x)}.
}
\tag{6}
\]

So defects approaching \(1\) force \(D_q(x)\) to become unbounded.

The universal-semimeasure characterization of randomness says that \(q/\lambda\) is bounded along every \(\lambda\)-ML-random sequence. More generally, for a fixed universal enumerable \(\xi\) and computable \(\mu\), boundedness of \(\xi/\mu\), together with positive prefix probabilities, characterizes \(\mu\)-ML randomness. [static1.squarespace.com](https://static1.squarespace.com/static/5d4e174e652fc20001100877/t/6500dd5fc96758438a64ef0d/1694555487427/Bayesian%2Bmerging%2Bof%2Bopinions%2Band%2Balgorithmic%2Brandomness.pdf?utm_source=chatgpt.com)

For the particular endpoints above, (4) and \(q\ge a\lambda\) give

\[
a\lambda(x_j)\le 2\tau_j.
\]

Together with (5), this yields

\[
D_q(x_j)\ge \frac{ac}{2}\,2^j.
\tag{7}
\]

Thus the construction does not merely lack a randomness verification: **its strongest witnesses explicitly escape every fixed randomness layer.**

One can choose nested witnesses and obtain a path with maximal prediction error infinitely often. Indeed, the paths with

\[
\limsup_n\delta_q(\omega_{1:n})=1
\]

form a comeager set, and on those paths

\[
\limsup_n
\left|
q(\omega_{n+1}\mid\omega_{1:n})-\frac12
\right|
=\frac12.
\]

But (6) shows that every such path is non-ML-random.

This is the first precise boundary for the proposed adversary:

> A successful negative argument needs a fixed positive prediction gap while remaining in one bounded-deficiency layer. Forcing relative defects toward \(1\) cannot accomplish that.

---

## 3. Consequences for defects, completions, and normalization

These consequences settle several interpretations of the “computable defect” and “normalized” special cases.

### 3.1 No enumerable universal additive finite measure

**Corollary 3.** There is no lower-semicomputable additive semimeasure in \(\mathcal A\).

This follows immediately from Theorem 2: an additive semimeasure has \(\delta_q(x)=0\) everywhere.

The statement allows a **noncomputable root mass**. It is therefore stronger than the familiar observation that an enumerable probability measure with computable total mass is computable.

### 3.2 Neither absolute nor relative defect can be lower semicomputable

**Corollary 4.** For \(q\in\mathcal A\), neither

\[
x\longmapsto \Delta_q(x)
\quad\text{nor}\quad
x\longmapsto\delta_q(x)
\]

is uniformly lower semicomputable.

#### Proof for the absolute defect

Suppose \(\Delta_q\) were lower semicomputable. Complete each terminated mass by fair-coin continuation:

\[
m(x)=q(x)+
\sum_{y\prec x}
\Delta_q(y)\,2^{-(|x|-|y|)}.
\tag{8}
\]

For each \(x\), this is a finite sum of lower-semicomputable quantities. Also,

\[
m\ge q,
\qquad
m(\epsilon)=q(\epsilon)\le1.
\]

At a node \(x\), the contributions from proper ancestors add across the two children exactly as they do at \(x\). The new contributions from \(y=x\) sum to \(\Delta_q(x)\). Hence

\[
m(x0)+m(x1)=m(x).
\]

Thus \(m\) would be an enumerable additive semimeasure dominating \(q\), and therefore universal. This contradicts Corollary 3.

If \(\delta_q\) were lower semicomputable, then

\[
\Delta_q=q\,\delta_q
\]

would be lower semicomputable, since both factors are nonnegative. That gives the second assertion. \(\square\)

This proves that an effective “fill the missing mass” procedure cannot simply enumerate the genuine defects of a universal semimeasure.

### 3.3 No computable vanishing bound on absolute defects

The next statement does **not** require an effective convergence modulus.

### Theorem 5

For \(q\in\mathcal A\), there is no computable \(f:\mathbb N\to[0,\infty)\) satisfying

\[
f(n)\longrightarrow0
\quad\text{and}\quad
\Delta_q(x)\le f(|x|)\quad\text{for every }x.
\tag{9}
\]

### Proof

First suppose \(f\) is rational-valued. Modify the terminal walk used in Theorem 2, again with \(\tau_j=2^{-2j}\).

At endpoint \(x\):

- If \(f(|x|)>\tau_j\), append \(0\) immediately.
- Otherwise, wait for a child with \(q(xb)>\tau_j\), and append the opposite bit if one is witnessed.

For a fixed \(j\), only finitely many unconditional steps occur, since \(f(n)\to0\). There are also only finitely many threshold-driven steps: the abandoned sibling cylinders remain pairwise disjoint even when unconditional steps intervene.

The process therefore stops at some \(x_j\), where

\[
f(|x_j|)\le\tau_j,
\qquad
q(x_j0),q(x_j1)\le\tau_j.
\]

As before, aggregate the emitted-path semimeasures with weights \(2^{-j}\). Universality gives a single \(c>0\) such that

\[
q(x_j)\ge c2^{-j}.
\]

Consequently,

\[
\Delta_q(x_j)
\ge c2^{-j}-2\tau_j
>\tau_j
\ge f(|x_j|)
\]

for all sufficiently large \(j\), a contradiction.

For computable real-valued \(f\), choose computable rational upper approximations \(h(n)\ge f(n)\) with

\[
h(n)-f(n)\le 2^{-n}.
\]

Then \(h(n)\to0\), and the rational-valued case applies. \(\square\)

There is nevertheless a noneffective vanishing envelope. Telescoping gives

\[
\sum_x\Delta_q(x)\le q(\epsilon)\le1,
\]

so

\[
\sup_{|x|\ge n}\Delta_q(x)\longrightarrow0.
\tag{10}
\]

The obstruction is therefore specifically effective: these defects vanish uniformly by depth, but no computable sequence tending to zero bounds them.

This also excludes a computable summable function \(g(x)\) bounding \(\Delta_q(x)\), because

\[
f(n)=\max_{|x|=n}g(x)
\]

would be computable and would tend to zero.

**Confidence for Corollaries 3–4 and Theorem 5:** high.  
**Novelty:** derived here; publication priority unverified.

### 3.4 Relative bounds and finite lookahead

Theorem 2 gives an even stronger exclusion for relative defects:

\[
\delta_q(x)\le \eta<1
\]

cannot hold uniformly at all sufficiently deep nodes, regardless of whether the proposed bound is computable.

It also rules out a simple smoothing operation. Define

\[
q^+(x)=q(x0)+q(x1).
\]

This is an enumerable semimeasure, but it is never universal when \(q\in\mathcal A\). Otherwise \(q^+\) would dominate \(q\), contradicting

\[
\inf_x\frac{q^+(x)}{q(x)}=0.
\]

The same conclusion holds for any fixed positive lookahead depth.

### 3.5 Normalization cannot preserve enumerability, even after rescaling

Let

\[
q^{\mathrm{norm}}(\epsilon)=1,
\qquad
q^{\mathrm{norm}}(xb)
=
q^{\mathrm{norm}}(x)
\frac{q(xb)}{q(x0)+q(x1)}.
\]

The semimeasure inequality gives

\[
q^{\mathrm{norm}}(x)\ge \frac{q(x)}{q(\epsilon)}.
\tag{11}
\]

Hence:

\[
\boxed{
\text{No positive scalar multiple }
\beta q^{\mathrm{norm}}
\text{ is lower semicomputable.}
}
\tag{12}
\]

Indeed, if one were, a further rational scaling would give an enumerable additive semimeasure of root mass at most \(1\) dominating \(q\), contradicting Corollary 3.

This settles the **effectivity** issue for normalization. It does not settle the prediction behavior of \(q^{\mathrm{norm}}\) on all ML-random paths.

---

## 4. A concrete positive construction in \(\mathcal A\setminus\mathcal C\)

The positive direction yields more than a hypothetical residual. We can construct the total enumerable semimeasure directly.

Fix \(U\in\mathcal A\) and a rational \(K>2\). Define

\[
H_K(x)=
\sup_{\substack{A\text{ finite prefix-free}\\
                 y\succeq x\ \text{for all }y\in A}}
\sum_{y\in A}
\max\{\lambda(y),U(y)/K\}.
\tag{13}
\]

Then put

\[
Q_K(x)=\frac K{K+1}H_K(x).
\tag{14}
\]

The function \(H_K\) is the least semimeasure majorizing both \(\lambda\) and \(U/K\).

### Theorem 6: an enumerable universal envelope

The construction satisfies

\[
\max\{\lambda(x),U(x)/K\}
\le H_K(x)
\le \lambda(x)+U(x)/K,
\tag{15}
\]

and

\[
H_K(x)=
\max\{U(x)/K,\ H_K(x0)+H_K(x1)\}.
\tag{16}
\]

Moreover,

\[
Q_K\in\mathcal A\setminus\mathcal C.
\]

### Proof

The finite prefix-free sets in (13) can be effectively enumerated. Each corresponding finite sum is lower semicomputable, so their supremum is lower semicomputable.

For every admissible \(A\),

\[
\begin{aligned}
\sum_{y\in A}\max\{\lambda(y),U(y)/K\}
&\le
\sum_{y\in A}\lambda(y)
+
K^{-1}\sum_{y\in A}U(y)\\
&\le \lambda(x)+U(x)/K.
\end{aligned}
\]

Taking \(A=\{x\}\) proves the lower bound in (15).

Combining antichains from the two child subtrees shows that \(H_K\) satisfies the semimeasure inequality. Its root mass is at most \(1+1/K\), so \(Q_K\) has root mass at most \(1\). Also,

\[
Q_K\ge \frac{U}{K+1},
\]

which proves universal dominance.

An admissible antichain either consists of \(x\), or splits between its two child subtrees. Thus

\[
H_K(x)=
\max\{\lambda(x),U(x)/K,H_K(x0)+H_K(x1)\}.
\]

But the child sum is at least \(\lambda(x)\), yielding (16).

In particular,

\[
U(x)\le K\lambda(x)
\quad\Longrightarrow\quad
H_K(x)=H_K(x0)+H_K(x1).
\tag{17}
\]

Since \(K>2\), both length-one nodes satisfy this inequality: \(U(x)\le1<K/2\).

Every effective universal mixture has strictly positive defect at every nonempty string, because it contains a positive-weight component that outputs exactly that string and stops. Therefore \(Q_K\), which has zero defect at both length-one nodes, cannot be such a mixture. \(\square\)

The use of positive defects to distinguish mixture priors from more general dominant semimeasures is consistent with the structural distinction established by Wood–Sunehag–Hutter; the construction here removes defects on infinitely many nodes, as described next. [hutter1.net](https://www.hutter1.net/publ/unipreq.pdf?utm_source=chatgpt.com)

**Confidence:** high.  
**Novelty:** this construction and its analysis were derived here; publication priority unverified.

### 4.1 Exact additivity on an entire randomness layer

Define

\[
P_K=
\left\{
\omega:
\forall n,\ 
U(\omega_{1:n})\le K\lambda(\omega_{1:n})
\right\}.
\tag{18}
\]

This is effectively closed, consists entirely of ML-random sequences, and satisfies

\[
\lambda(P_K)\ge1-\frac1K.
\tag{19}
\]

For (19), use the prefix-free family of first crossings of \(U>K\lambda\): its total \(\lambda\)-mass is at most \(U(\epsilon)/K\le1/K\).

By (17),

\[
\boxed{
\Delta_{Q_K}(x)=0
\quad\text{at every prefix of every }\omega\in P_K.
}
\tag{20}
\]

Thus an enumerable dominant semimeasure can be additive along every path in a prescribed infinite randomness layer.

This sharply limits any negative proof based only on mass loss inside an arbitrarily chosen closed class of randoms.

### 4.2 A quantitative prediction bound

The construction also controls directional prediction errors through the local density of \(P_K\).

### Theorem 7

If \(x\) is a prefix of a member of \(P_K\), then, for both \(b\in\{0,1\}\),

\[
\boxed{
\left|Q_K(b\mid x)-\frac12\right|
\le
\lambda(P_K^c\mid[x]).
}
\tag{21}
\]

Consequently, if \(\omega\in P_K\) is a dyadic density-one point of \(P_K\), then

\[
Q_K(b\mid\omega_{1:n})\longrightarrow\frac12
\qquad(b=0,1).
\tag{22}
\]

Raw and normalized conditionals coincide along these paths.

### Proof

Set

\[
R_K=H_K-\lambda.
\]

By (15), \(R_K\ge0\). Since \(\lambda\) is computable and additive, \(R_K\) is a lower-semicomputable semimeasure.

Fix \(x\) as in the theorem. Let \(S\) consist of the first descendants \(s\) crossing \(U>K\lambda\). Their cylinders are disjoint and cover \([x]\setminus P_K\). At such a crossing,

\[
U(s)\le U(s^-)
\le K\lambda(s^-)
=2K\lambda(s).
\tag{23}
\]

For any antichain in (13), positive excess over its fair-coin contribution occurs only at leaves below one of these first crossings. Group those leaves according to their first crossing \(s\). The semimeasure inequality bounds the contribution of each group by \(U(s)/K\). Hence

\[
R_K(x)
\le
\frac1K\sum_{s\in S}U(s)
\le
2\sum_{s\in S}\lambda(s)
=
2\lambda([x]\setminus P_K).
\tag{24}
\]

Because \(R_K\) is a nonnegative semimeasure,

\[
0\le R_K(xb)\le R_K(x).
\]

Scaling does not change conditionals, so

\[
\begin{aligned}
\left|Q_K(b\mid x)-\frac12\right|
&=
\frac{|R_K(xb)-R_K(x)/2|}
     {\lambda(x)+R_K(x)}\\
&\le
\frac{R_K(x)}{2\lambda(x)}\\
&\le
\lambda(P_K^c\mid[x]).
\end{aligned}
\]

This proves (21), and density one gives (22). \(\square\)

**Confidence:** high.  
**Novelty:** the envelope-specific estimate is derived here; publication priority unverified.

There is also a weaker conclusion covering **every** member of \(P_K\). Every ML-random member of an effectively closed class has upper dyadic density \(1\) in that class. Applying this standard result to (21) gives

\[
\boxed{
\forall\omega\in P_K,\qquad
\liminf_n
\max_b\left|Q_K(b\mid\omega_{1:n})-\frac12\right|=0.
}
\tag{25}
\]

This uses Proposition 2.7(i) of Miyabe–Nies–Zhang. It gives arbitrarily accurate prediction times, not convergence or a density-one set of accurate times. [cs.auckland.ac.nz](https://www.cs.auckland.ac.nz/~nies/papersnew/MiyabeNiesZhang_Density_Randomness.pdf?utm_source=chatgpt.com)

### 4.3 What the residual actually does

Take \(U=\xi\), with \(\xi\) an effective universal mixture. Then

\[
Q_K\ge \frac{\xi}{K+1}.
\]

Nevertheless,

\[
r=Q_K-\frac{\xi}{K+1}
\]

is not a semimeasure. At either length-one node,

\[
\Delta_r(x)
=
-\frac{\Delta_\xi(x)}{K+1}<0.
\]

Indeed, no positive \(c\) makes \(Q_K-c\xi\) a semimeasure.

So this construction exploits cancellation of defects in the total \(q\), while keeping the total enumerable. It lies outside the stronger ansatz that the residual must itself be a semimeasure.

I have not ruled out successful constructions within that stronger ansatz. The point is that it does not represent all of \(\mathcal A\).

### 4.4 Why this is still short of a positive solution

Two quantifiers remain unresolved.

First, \(Q_K\) depends on \(K\). The fact that every ML-random sequence belongs to some \(P_K\) does not provide one \(Q_K\) that works on all layers.

Second, a member of \(P_K\) need not be a density-one point of \(P_K\). Equation (25) does not upgrade to convergence.

Exact additivity alone cannot resolve the second issue. Here is a direct example.

Choose a left-c.e. ML-random real \(\alpha\), with binary expansion \(\omega\). For the dyadic interval \(I_x\), set

\[
m(x)=\operatorname{Leb}(I_x\cap[0,\alpha)),
\qquad
v(x)=\frac{\lambda(x)+m(x)}2.
\]

Then \(v\) is enumerable and additive, with \(\lambda/2\le v\le\lambda\). At a prefix of \(\omega\), let \(r\) be the relative position of \(\alpha\) inside \(I_x\). Whenever the next two bits are \(01\), \(r\in[1/4,1/2)\), and

\[
v(0\mid x)=\frac{1/2+r}{1+r}\ge\frac35.
\]

There are infinitely many such occurrences, so observed prediction fails. The underlying random-cut martingale is a standard example; the calculation displays its predictive error explicitly. [cs.auckland.ac.nz](https://www.cs.auckland.ac.nz/~nies/papersnew/MiyabeNiesZhang_Density_Randomness.pdf?utm_source=chatgpt.com)

This \(v\) is not universal. It shows why eliminating leakage still leaves a directional-bias problem.

---

## 5. A rigorous obstruction to sound enumeration-based error certificates

The mass-arrival strategy faces another limitation, separate from the near-total-defect issue.

### Proposition 8: effectively certified genuine errors cannot witness ML failure

Suppose \(q\ge a\lambda\). Fix \(\varepsilon>0\), and let

\[
B_\varepsilon=
\left\{
xb:
\left|q(b\mid x)-\frac12\right|\ge\varepsilon
\right\}.
\]

Every c.e. subset \(S\subseteq B_\varepsilon\) contains only finitely many prefixes of each ML-random sequence.

The same holds for locally normalized predictions.

### Proof

Write

\[
p_b(x)=q(b\mid x),
\qquad
d(x)=\sum_b\frac12\log\frac{1/2}{p_b(x)}.
\]

Adding a termination outcome makes \(p\) a probability distribution, with the fair coin assigning that outcome probability zero. Thus \(d(x)\ge0\). Telescoping gives

\[
\sum_{|x|<N}\lambda(x)d(x)
=
\log q(\epsilon)
+
\sum_{|y|=N}\lambda(y)\log\frac{\lambda(y)}{q(y)}
\le
\log\frac{q(\epsilon)}a.
\tag{26}
\]

Pinsker’s inequality gives

\[
\sum_x\lambda(x)\sum_b
\left(p_b(x)-\frac12\right)^2
\le
2\log\frac{q(\epsilon)}a.
\]

Since \(\lambda(xb)=\lambda(x)/2\),

\[
\sum_{y\in B_\varepsilon}\lambda(y)
\le
\frac1{\varepsilon^2}\log\frac{q(\epsilon)}a
<\infty.
\tag{27}
\]

Therefore every c.e. subset \(S\) is a Solovay test.

For completeness, no computable bound on this sum is needed. The function

\[
F(\omega)=\sum_{y\in S}\mathbf 1_{[y]}(\omega)
\]

is lower semicomputable with finite integral. Choose an integer \(C>\int F\,d\lambda\). Then

\[
\{F>C2^n\}
\]

forms an ML test, so \(F\) is finite at every ML-random point.

For normalized probabilities, the raw conditional divergence equals the normalized divergence minus the logarithm of the surviving mass. It therefore bounds the normalized divergence, and the same argument applies. \(\square\)

**Confidence:** high.  
**Novelty:** a standard KL/Solovay-test deduction, applied here to the proposed strategy.

The consequence is precise:

> An effective procedure that irrevocably lists only genuine fixed-size prediction errors cannot supply infinitely many witnesses along an ML-random path.

This does not exclude finite injury or oracle constructions. They must use provisional certificates, a non-c.e. final selection, or information conditional on a noneffective restriction.

---

## 6. Raw prediction, normalized prediction, and likelihood-ratio convergence

These distinctions matter when choosing what to force.

Let

\[
D(x)=\frac{q(x)}{\lambda(x)}.
\]

Then

\[
q(b\mid x)-\frac12
=
\frac{D(xb)-D(x)}{2D(x)}.
\tag{28}
\]

Along an ML-random path, \(D\) is bounded above and bounded away from zero. Therefore

\[
\boxed{
\text{raw observed-symbol convergence}
\iff
D(\omega_{1:n+1})-D(\omega_{1:n})\to0.
}
\tag{29}
\]

This requires vanishing increments, not convergence of \(D\) itself. A Doob-style convergence theorem is sufficient but stronger than the original prediction requirement.

To separate bias and loss, define

\[
\ell(x)=D(x)-\frac{D(x0)+D(x1)}2\ge0,
\]

\[
\beta(x)=\frac{D(x1)-D(x0)}2.
\]

Then

\[
D(xb)-D(x)=(2b-1)\beta(x)-\ell(x).
\]

On an ML-random path:

| Prediction property | Equivalent asymptotic condition |
|---|---|
| Raw observed-symbol convergence | \((2\omega_{n+1}-1)\beta(\omega_{1:n})-\ell(\omega_{1:n})\to0\) |
| Normalized prediction convergence | \(\beta(\omega_{1:n})\to0\) |
| Raw convergence for both symbols | \(\beta(\omega_{1:n})\to0\) and \(\ell(\omega_{1:n})\to0\) |

For an arbitrary binary source \(\mu\), if

\[
e_b=q(b\mid x)-\mu(b\mid x),
\]

then

\[
e_0+e_1=-\delta_q(x).
\]

Consequently,

\[
\text{full-vector raw convergence}
\iff
\text{observed raw convergence and }\delta_q\to0,
\tag{30}
\]

and

\[
\text{full-vector raw convergence}
\iff
\text{normalized convergence and }\delta_q\to0.
\tag{31}
\]

These identities prevent a leakage argument from being mistaken for a normalized-prediction argument, or an observed-symbol theorem from being silently strengthened.

**Confidence:** high.  
**Novelty:** elementary identities.

---

## 7. Two exact reductions of the remaining problem

### 7.1 Fair coin: one fixed closed randomness class suffices, with subtree restrictions

Fix any nonempty effectively closed class

\[
P\subseteq \operatorname{MLR}(\lambda).
\]

Such a class has positive measure. For a finite string \(\sigma\), define

\[
q^\sigma(x)=q(\sigma x).
\tag{32}
\]

No normalization is performed.

Then \(q^\sigma\in\mathcal A\): given an enumerable semimeasure \(\nu\), embed it below \(\sigma\), put mass \(\nu(\epsilon)\) on the prefix chain leading to \(\sigma\), and put zero on incomparable strings. Universality of \(q\) applied to this embedding gives dominance of \(\nu\) by \(q^\sigma\).

### Proposition 9

\[
\boxed{
\begin{aligned}
&q\text{ predicts }\lambda\text{ on every ML-random path}\\
&\quad\iff
\forall\sigma\ \forall\alpha\in P,\ 
q^\sigma(\alpha_t\mid\alpha_{<t})\longrightarrow\frac12.
\end{aligned}
}
\tag{33}
\]

The same equivalence holds after local normalization.

The key fact is Kučera’s tail theorem: every ML-random sequence has a suffix in every positive effectively closed class. A primary account with proof is Bienvenu–Day–Hoyrup–Mezhirov–Shen, Theorem 1. [lirmm.fr](https://www.lirmm.fr/~ashen/nafit/2010ergodic.pdf?utm_source=chatgpt.com)

A brief proof of that fact is useful here. Write \(P^c=[W]\), where \(W\) is a c.e. prefix-free code. Since \(\lambda(P^c)<1\), choose an integer \(m\) such that \(\lambda(P^c)^m\le1/2\). Concatenations of \(mn\) codewords from \(W\) define uniformly effectively open sets of measure at most \(2^{-n}\). A sequence whose every suffix lies outside \(P\) can be parsed into arbitrarily many such codewords and fails this ML test. The constant \(m\) may be hard-coded; it need not be computable uniformly from \(P\).

Now prove (33). In the forward direction, adding a finite prefix preserves fair-coin ML randomness, and the tail conditionals of \(q\) on \(\sigma\alpha\) equal those of \(q^\sigma\) on \(\alpha\). Conversely, write an arbitrary ML-random \(\omega\) as \(\sigma\alpha\) with \(\alpha\in P\), and apply the right-hand side.

This is a genuine fixed-class reduction. The quantifier over \(\sigma\) is essential; it cannot simply be dropped.

**Confidence:** high.  
**Novelty:** a direct application of Kučera’s theorem; no priority claim.

### 7.2 Full 2.3A: explicit computable trees of successive bad predictions

Here is an oracle-free combinatorial formulation that covers **every computable \(\mu\)**, including measures with zero-probability cylinders.

Fix increasing rational approximations

\[
\xi_s(x)\uparrow\xi(x),
\qquad
q_s(x)\uparrow q(x).
\]

For a computable \(\mu\), choose decreasing rational upper approximations

\[
u_s(x)\downarrow\mu(x).
\]

For \(K\ge1\), define

\[
P_{\mu,K}
=
\left\{
\omega:\forall n,\ 
\xi(\omega_{1:n})\le K\mu(\omega_{1:n})
\right\}.
\tag{34}
\]

Then

\[
\operatorname{MLR}(\mu)=\bigcup_{K\ge1}P_{\mu,K}.
\]

An explicit computable tree for this class is

\[
T_{\mu,K}
=
\left\{
z:\forall y\preceq z,\
\xi_{|z|}(y)\le K u_{|z|}(y)
\right\}.
\tag{35}
\]

Monotonicity of the approximations makes this prefix closed, and

\[
[T_{\mu,K}]=P_{\mu,K}.
\]

Every prefix of an infinite path through this tree has positive \(\mu\)-measure, since \(\xi(x)>0\).

#### Encoding a strict prediction error

For \(y=xb\) and rational \(\varepsilon>0\), put

\[
\begin{aligned}
A^+(x,b)&=\mu(x)q(xb),\\
B^+(x,b)&=\mu(xb)q(x)+\varepsilon\mu(x)q(x),\\
A^-(x,b)&=\mu(xb)q(x),\\
B^-(x,b)&=\mu(x)q(xb)+\varepsilon\mu(x)q(x).
\end{aligned}
\tag{36}
\]

All four quantities are uniformly lower semicomputable and nonnegative. On positive-probability prefixes,

\[
A^+>B^+
\iff
q(b\mid x)-\mu(b\mid x)>\varepsilon,
\]

\[
A^->B^-
\iff
\mu(b\mid x)-q(b\mid x)>\varepsilon.
\tag{37}
\]

Choose monotone rational approximations \(A_s^\pm,B_s^\pm\).

#### The tree

A node of \(\mathcal B(q,\mu,K,\varepsilon)\) is a finite list

\[
(y_i,\eta_i,r_i,s_i)_{i=1}^{m},
\]

where \(\eta_i\in\{+,-\}\), \(r_i\) is rational, \(s_i\in\mathbb N\), and \(y_i=x_i b_i\) is nonempty.

The list belongs to the tree exactly when:

1. \(y_1\prec y_2\prec\cdots\prec y_m\);
2. \(y_m\in T_{\mu,K}\);
3. for every \(i\le m\),

   \[
   A^{\eta_i}_{s_i}(x_i,b_i)>r_i,
   \qquad
   B^{\eta_i}_{m}(x_i,b_i)\le r_i.
   \tag{38}
   \]

Every finite check is decidable. Shortening the list weakens each upper-bound check, so this is a computable tree.

### Theorem 10: exact equivalence

\[
\boxed{
\begin{aligned}
&\mathcal B(q,\mu,K,\varepsilon)\text{ is ill founded}\\
&\quad\iff
\exists\omega\in P_{\mu,K}\ 
\left|
q(\omega_t\mid\omega_{<t})
-\mu(\omega_t\mid\omega_{<t})
\right|>\varepsilon
\text{ infinitely often}.
\end{aligned}
}
\tag{39}
\]

#### Proof

An infinite branch gives strictly nested strings with union \(\omega\in P_{\mu,K}\). For each fixed label \(i\), the checks at all sufficiently long list lengths imply

\[
B^{\eta_i}(x_i,b_i)
\le r_i
<
A^{\eta_i}_{s_i}(x_i,b_i)
\le A^{\eta_i}(x_i,b_i).
\]

Thus every selected edge is genuinely bad.

Conversely, choose the successive bad prefixes of such an \(\omega\). At each one, the appropriate strict inequality \(A^\eta>B^\eta\) admits a rational separator

\[
B^\eta<r<A^\eta
\]

and a finite stage \(s\) with \(A_s^\eta>r\). These labels form an infinite branch. \(\square\)

Therefore full 2.3A is equivalent to the following statement:

> **There exist an enumerable semimeasure \(q\) and a rational \(c>0\) with \(q\ge c\xi\), such that for every computable probability measure \(\mu\), every positive integer \(K\), and every positive rational \(\varepsilon\), the explicit computable tree \(\mathcal B(q,\mu,K,\varepsilon)\) is well founded.**

For the fair-coin version, fix \(\mu=\lambda\).

For normalized prediction, replace the denominator \(q(x)\) in the cross-product formulas by

\[
q(x0)+q(x1).
\]

The same construction remains computable.

**Confidence:** high.  
**Novelty:** the exact reduction is established here; the arithmetization technique is standard. I do not claim that the well-foundedness problem is easier.

Its useful content is the separation between:

\[
\underbrace{A_s>r}_{\text{finite observable witness}}
\qquad\text{and}\qquad
\underbrace{\forall t,\ B_t\le r}_{\text{permanent upper promise}}.
\]

Mass arrivals supply the first. They do not certify the second.

The tree is countably branching. Arbitrarily long finite chains do not imply an infinite branch, so an appeal to compactness cannot replace a stabilization proof.

---

## 8. What a successful \(0'\)-construction would still need

Let \(P\subseteq\operatorname{MLR}(\lambda)\) be nonempty and effectively closed. The following condition is sufficient:

For some \(\varepsilon>0\), every cylinder \([\sigma]\) meeting \(P\) has arbitrarily deep extensions \(xb\succeq\sigma\) such that

\[
P\cap[xb]\ne\varnothing
\quad\text{and}\quad
\left|q(b\mid x)-\frac12\right|>\varepsilon.
\tag{40}
\]

Under this hypothesis, a nested construction gives an ML-random counterexample. It can be carried out with \(0'\):

- extendibility in \(P\) is \(0'\)-decidable;
- the values of \(q\) are uniformly \(0'\)-computable;
- a strict conditional error is therefore semidecidable using \(0'\).

The important requirement is an **allowed bad edge**. A large defect at \(x\) is insufficient if the required continuation leaves \(P\).

There is a complementary necessary condition for a successful predictor. Suppose \(q\) converges on every member of \(P\). For fixed \(\varepsilon>0\), the closed sets

\[
F_N=
\left\{
\omega\in P:
\forall n\ge N,\
\left|q(\omega_{n+1}\mid\omega_{1:n})-\frac12\right|
\le\varepsilon
\right\}
\]

cover \(P\). Baire’s theorem yields a nonempty relative cylinder \(P\cap[\sigma]\) contained in some \(F_N\). Thus all sufficiently late allowed edges in that relative cylinder are uniformly \(\varepsilon\)-good.

Universality alone has not contradicted this local possibility. The envelope construction shows that at least the corresponding **zero-defect** possibility is entirely compatible with universality.

Kučera coding can maintain randomness or encode information into random paths, but it does not by itself establish (40). That geometric extension property is the missing mathematical input.

**Confidence:** high for the conditional construction and Baire deduction.  
**Novelty:** standard forcing and category methods applied to this problem.  
**Unresolved:** whether a suitable condition of this kind follows from universality for every \(q\).

---

## 9. A literature issue that must not be used to close the gap

There is a tempting stronger positive claim: density randomness might force convergence of every lower-semicomputable supermartingale.

I did **not** use it.

Theorem 3.3 of Miyabe–Nies–Zhang establishes the density-randomness characterization for left-c.e. **martingales**. [cs.auckland.ac.nz](https://www.cs.auckland.ac.nz/~nies/papersnew/MiyabeNiesZhang_Density_Randomness.pdf?utm_source=chatgpt.com) Zaffora Blando’s Appendix Theorem A.2 asserts a semimeasure-ratio characterization, but its forward proof invokes the extension from martingales to supermartingales. [static1.squarespace.com](https://static1.squarespace.com/static/5d4e174e652fc20001100877/t/6500dd5fc96758438a64ef0d/1694555487427/Bayesian%2Bmerging%2Bof%2Bopinions%2Band%2Balgorithmic%2Brandomness.pdf?utm_source=chatgpt.com) Kusum’s 2025 thesis, Section 8.2, explicitly identifies the claimed extension as problematic and leaves the implication from density randomness to convergence of all c.e. supermartingales unresolved. [kdamini.com](https://kdamini.com/thesispdf.pdf?utm_source=chatgpt.com)

Accordingly, I am not treating that general extension as established. Theorem 7 above has a direct first-crossing proof and does not depend on it.

---

## 10. Status of the requested special cases

| Question or restriction | What is established | Confidence and novelty |
|---|---|---|
| Every \(q\in\mathcal A\) fails on some fair-coin ML-random sequence | **Not proved here** | Unresolved |
| Some \(q\in\mathcal A\) succeeds for every computable \(\mu\) on every \(\mu\)-ML-random sequence | **Not constructed here** | Unresolved |
| Universal enumerable additive finite measure, allowing noncomputable root mass | **Impossible** | High; derived here, priority unverified |
| Uniformly computable or lower-semicomputable absolute defect | **No such \(q\in\mathcal A\)** | High; derived here, priority unverified |
| Uniformly computable or lower-semicomputable relative defect | **No such \(q\in\mathcal A\)** | High; derived here, priority unverified |
| Computable \(f(n)\to0\) bounding every absolute defect at depth \(n\) | **Impossible**, even without an effective convergence modulus | High; derived here, priority unverified |
| Eventual uniform relative-defect bound below \(1\) | **Impossible**, even noneffectively | High; consequence of Theorem 2 |
| Local normalization of an arbitrary \(q\in\mathcal A\) | No positive rescaling is enumerable; all-ML prediction remains unresolved here | High for effectivity result |
| The explicit \(Q_K\) at density-one points of \(P_K\) | **Both raw and normalized full-vector convergence** | High; construction and estimate derived here |
| The explicit \(Q_K\) at every point of \(P_K\) | **Zero defect everywhere along the path and liminf prediction error \(0\)** | High; standard upper-density theorem plus the new estimate |
| Full problem as a combinatorial statement | Exactly equivalent to well-foundedness of the computable trees in Section 7.2 | High; standard technique, no priority claim |

The negative task is now more precise than “avoid effective subtraction”: it must produce an infinite coherent sequence of fixed-size errors **inside one bounded randomness layer**, with permanent upper promises that survive later enumeration.

The positive task is also more precise. Enumerable universal dominance is compatible with removing leakage on a whole randomness layer. What remains is a single construction that controls directional bias on every relevant layer, for every computable source. The envelope provides that control at density-one points, but the remaining quantifiers are not yet resolved.