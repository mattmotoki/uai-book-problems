# Mathematical report: stochastic convergence rates of normalized universal semimeasures

**The infinitely-often lower bounds in the question hold for every computable probability measure and every universally dominating enumerable semimeasure.** In fact, the required inequalities hold at some time in every sufficiently late dyadic block. For uniformly nondegenerate stochastic measures—including the fair coin—the expected squared-error lower bound can be strengthened from \(c\,2^{-2K(t)}\) to \(c\,2^{-K(t)}\).

The upper-bound question has a different answer: **\(O(2^{-K(t)})\) is not a general stochastic upper bound.** I give a construction within the genuine Solomonoff-machine class for which the expected squared error exceeds every fixed power of \(2^{-K(t)}\) by unbounded factors, even when the true environment is an iid fair coin.

The stronger lower-bound assertion “for every sufficiently large \(t\)” remains unresolved by this report. I distinguish it throughout from the infinitely-often theorem proved below.

The novelty check also has a definite answer: **2.7F is an immediate consequence of Hutter’s 2007 all-history lower bound**, followed by normalization and, for the larger class of universal semimeasures, a mutual-domination argument. [arxiv.org](https://arxiv.org/pdf/0709.1516?utm_source=chatgpt.com)

---

## 1. Definitions and conventions

Work over \(\{0,1\}\). Fix a universal prefix machine defining \(K\), and write
\[
w_t:=2^{-K(t)},\qquad t\ge1.
\]

Let:

- \(\mathcal A\) be the class of lower semicomputable semimeasures that multiplicatively dominate every lower semicomputable semimeasure;
- \(\mathcal B\) be the class of Solomonoff priors induced by universal monotone machines, with universality understood by adjunction.

These classes differ: \(\mathcal B\subsetneq\mathcal A\). Wood, Sunehag, and Hutter establish this distinction and identify the Solomonoff-machine and universal-mixture classes. [arxiv.org](https://arxiv.org/pdf/1111.3854?utm_source=chatgpt.com)

For \(M\in\mathcal A\), define
\[
q_M(b\mid x):=\frac{M(xb)}{M(x0)+M(x1)}.
\]
Let \(Q=N(M)\) be the associated normalized sequence measure:
\[
Q(\epsilon)=1,\qquad Q(xb)=Q(x)q_M(b\mid x).
\]

For a computable probability measure \(\mu\), put
\[
\begin{aligned}
a_t(x)&:=\sum_b|q_M(b\mid x)-\mu(b\mid x)|,\\
s_t(x)&:=\sum_b(q_M(b\mid x)-\mu(b\mid x))^2,
\end{aligned}
\qquad |x|=t-1,
\]
and
\[
A_t:=\mathbb E_\mu a_t(X_{<t}),\qquad
S_t:=\mathbb E_\mu s_t(X_{<t}).
\]
Conditionals at \(\mu\)-null histories do not affect these expectations.

For binary probability vectors,
\[
s_t(x)=\frac12a_t(x)^2.
\]
Consequently,
\[
\boxed{\frac12A_t^2\le S_t,\qquad A_t\le\sqrt{2S_t}.}
\tag{1}
\]

We will use three standard consequences of prefix coding:
\[
\sum_{t\ge1}w_t\le1,
\tag{2}
\]
\[
g\text{ lower semicomputable},\quad g\ge0,\quad \sum_tg(t)\le1
\quad\Longrightarrow\quad
g(t)\le C_gw_t,
\tag{3}
\]
and
\[
w_t\ge c_0(t+1)^{-2}.
\tag{4}
\]
Here (3) is the discrete coding theorem, obtained by applying Kraft–Chaitin coding to \(g\); (4) follows from a self-delimiting integer code of length at most \(2\log_2(t+1)+O(1)\).

Finally, normalization preserves dominance. Indeed,
\[
Q(x)
=\prod_{i=1}^{|x|}
\frac{M(x_{\le i})}
     {M(x_{<i}0)+M(x_{<i}1)}
\ge
\prod_{i=1}^{|x|}
\frac{M(x_{\le i})}{M(x_{<i})}
=
\frac{M(x)}{M(\epsilon)}
\ge M(x).
\tag{5}
\]

---

## 2. The general expected lower bound: proved infinitely often

### Theorem 1 — the requested lower bounds hold in every sufficiently late dyadic block

For every \(M\in\mathcal A\) and every computable probability measure \(\mu\), there exist \(c>0\) and \(n_0\) such that
\[
\forall n\ge n_0\ \exists t\in\{2^n+1,\ldots,2^{n+1}\}:
\]
\[
\boxed{
A_t\ge c\,w_t,
\qquad
S_t\ge\frac{c^2}{2}w_t^2.
}
\tag{6}
\]

The same selected time satisfies both inequalities.

Thus the infinitely-often assertions in the question are true for **all computable measures**, without requiring stochasticity, full support, or conditional probabilities bounded away from zero. In particular, they hold for both \(\mathcal A\) and \(\mathcal B\).

### Proof

The argument has two parts: force a discrepancy somewhere in a block, then compare the total coding weight of the block with the coding weight of its index.

#### Step 1: uniformly computable continuations that are unlikely under \(\mu\)

For every \(x\) with \(\mu(x)>0\), construct a computable infinite continuation \(z^x\) such that
\[
\mu(xz^x_{\le k})\le(2/3)^k\mu(x)
\qquad(k\ge0).
\tag{7}
\]

Suppose a tail prefix \(z^x_{\le k}\) has already been selected. The masses of its two children sum to at most \((2/3)^k\mu(x)\), so one child has mass at most
\[
\frac12(2/3)^k\mu(x)
<
(2/3)^{k+1}\mu(x).
\]
Because \(\mu\) is computable and the inequality is strict, a search for a certified child below the latter threshold terminates.

The threshold always uses the **initial positive mass \(\mu(x)\)**. Therefore the algorithm continues even if a selected continuation enters a \(\mu\)-null cylinder.

For any computable starting length \(r_n\), let \(\nu_n\) first generate \(r_n\) bits according to \(\mu\), then follow \(z^x\) forever.

The family \((\nu_n)\) is uniformly computable. To see the only delicate point, consider computing \(\nu_n(xz)\) when \(|x|=r_n\). Its value is either \(\mu(x)\) or zero, according to whether \(z\) agrees with the selected continuation. To approximate within \(\varepsilon\), dovetail until either:

- an upper bound certifies \(\mu(x)<\varepsilon\), allowing output zero to the required accuracy; or
- a lower bound certifies \(\mu(x)>0\), allowing computation of the required finite continuation.

At least one alternative terminates, including when \(\mu(x)=0\).

#### Step 2: one domination constant works for the entire family

The mixture
\[
R:=\sum_{n\ge1}w_n\nu_n
\tag{8}
\]
is a lower semicomputable semimeasure. Universality and (5) therefore give a constant \(a>0\), independent of \(n\), such that
\[
Q(y)\ge M(y)\ge aR(y)\ge aw_n\nu_n(y).
\tag{9}
\]

#### Step 3: a lower bound on the accumulated absolute error in a block

At length \(r_n\), define
\[
G_n:=\{x:\mu(x)>0,\ Q(x)\le2\mu(x)\}.
\]
Since
\[
\mathbb E_\mu\frac{Q(X_{1:r_n})}{\mu(X_{1:r_n})}
=
\sum_{\substack{|x|=r_n\\\mu(x)>0}}Q(x)
\le1,
\]
Markov’s inequality yields
\[
\mu(G_n)\ge\frac12.
\tag{10}
\]

Fix a block length \(\ell_n\). For \(x\in G_n\), consider the next-\(\ell_n\)-bit cylinder
\[
B_x=[z^x_{\le\ell_n}].
\]
By (9),
\[
Q(B_x\mid x)
\ge
\frac{aw_n\mu(x)}{Q(x)}
\ge\frac{aw_n}{2},
\tag{11}
\]
whereas
\[
\mu(B_x\mid x)\le(2/3)^{\ell_n}.
\tag{12}
\]

Assume
\[
(2/3)^{\ell_n}=o(w_n).
\tag{13}
\]
Then, for all sufficiently large \(n\), the conditional block distributions differ on \(B_x\) by at least \(aw_n/4\). Their \(L^1\) distance is therefore at least \(aw_n/2\).

For any two sequential laws \(P,Q\) on a finite block,
\[
\|P-Q\|_1
\le
\sum_k
\mathbb E_P
\left\|
P(\cdot\mid Y_{<k})-Q(\cdot\mid Y_{<k})
\right\|_1.
\tag{14}
\]
To prove this, telescope the hybrid laws that use \(P\) for the first \(k\) symbols and \(Q\) thereafter. Adjacent hybrids differ in one conditional distribution; summing out their common \(Q\)-suffix leaves the \(P\)-weighted one-step discrepancy.

Apply (14) conditionally on each \(x\in G_n\), then average. Equations (10)–(12) give the useful general block bound
\[
\boxed{
\sum_{t=r_n+1}^{r_n+\ell_n}A_t
\ge\frac a4w_n
}
\tag{15}
\]
for all sufficiently large \(n\), whenever (13) holds.

#### Step 4: specialize to dyadic blocks

Take
\[
r_n=\ell_n=2^n,\qquad
I_n=\{2^n+1,\ldots,2^{n+1}\}.
\]
Condition (13) follows from (4).

The function
\[
g(n):=\sum_{t\in I_n}w_t
\]
is lower semicomputable, and the blocks are disjoint, so \(\sum_ng(n)\le1\). By (3), some constant \(C\) satisfies
\[
\sum_{t\in I_n}w_t\le Cw_n.
\tag{16}
\]

Combining (15) and (16), at least one \(t\in I_n\) satisfies
\[
A_t\ge\frac{a}{4C}w_t.
\]
Equation (1) then gives
\[
S_t\ge\frac{a^2}{32C^2}w_t^2.
\]
This proves the theorem. \(\square\)

### What prevents symmetrization from defeating this theorem?

The proof does not identify a history at which symmetry must fail. It uses universal dominance of an entire computable family of alternative environments: follow \(\mu\) until a specified block, then continue deterministically in a way that is unlikely under \(\mu\).

The normalized predictor must retain enough probability on each alternative to create a block discrepancy. Symmetry can redistribute the discrepancy among times and histories, but the block estimate prevents it from eliminating the asserted infinitely-often expected lower bounds.

---

## 3. A stronger squared-error lower bound for uniformly stochastic measures

### Theorem 2 — uniformly nondegenerate measures have \(S_t\gtrsim2^{-K(t)}\) infinitely often

Suppose \(\mu\) is computable and there is an \(\varepsilon>0\) such that
\[
\varepsilon\le\mu(b\mid x)\le1-\varepsilon
\tag{17}
\]
for both bits and every \(\mu\)-positive history.

Then for every \(M\in\mathcal A\), there exist \(c>0,n_0\) such that
\[
\forall n\ge n_0\ \exists t\in I_n:
\qquad
\boxed{S_t\ge c\,w_t.}
\tag{18}
\]

In particular, for the fair-coin measure \(\lambda\),
\[
S_t\ge c\,2^{-K(t)}
\quad\text{infinitely often}.
\tag{19}
\]

### Proof

Let \(N=2^n\). This time let \(\nu_n\) follow \(\mu\) for \(N\) steps and then output \(0^\infty\).

As before, one constant \(a>0\) gives \(Q\ge aw_n\nu_n\). For starting histories \(x\in G_n\), where \(\mu(G_n)\ge1/2\),
\[
Q(0^\infty\mid x)\ge r:=\frac{aw_n}{2}.
\tag{20}
\]

Write \(Q_x,\mu_x\) for the conditional future laws given \(x\). Under \(\mu_x\), the likelihood ratio
\[
L_k:=\frac{Q_x(Y_{\le k})}{\mu_x(Y_{\le k})}
\]
is a martingale with \(L_0=1\).

Let
\[
\tau:=\inf\{k\ge1:L_k\ge2\}.
\]
Along the continuation \(0^\infty\),
\[
L_N\ge\frac{r}{(1-\varepsilon)^N}>2
\]
for all sufficiently large \(n\). Thus
\[
Q_x(\tau\le N)\ge r.
\tag{21}
\]

At the first crossing, the likelihood ratio is at most \(2/\varepsilon\): before crossing it is below \(2\), and each one-step likelihood multiplier is at most \(1/\varepsilon\). Hence
\[
Q_x(\tau\le N)
=
\mathbb E_{\mu_x}[L_\tau\mathbf1_{\{\tau\le N\}}]
\le
\frac2\varepsilon\,\mu_x(\tau\le N).
\]
Together with (21),
\[
\mu_x(\tau\le N)\ge\frac{\varepsilon r}{2}.
\tag{22}
\]

On crossing, \((L_\tau-1)^2\ge1\). The stopped martingale variance identity gives
\[
\begin{aligned}
\frac{\varepsilon r}{2}
&\le
\mathbb E_{\mu_x}(L_{\tau\wedge N}-1)^2\\
&=
\sum_{k=1}^N
\mathbb E_{\mu_x}\!\left[
\mathbf1_{\{\tau\ge k\}}L_{k-1}^2
\sum_b\frac{(q_k(b)-\mu_k(b))^2}{\mu_k(b)}
\right]\\
&\le
\frac4\varepsilon
\sum_{k=1}^N\mathbb E_{\mu_x}s_{N+k}.
\end{aligned}
\]
Therefore
\[
\sum_{k=1}^N\mathbb E_{\mu_x}s_{N+k}
\ge\frac{\varepsilon^2r}{8}.
\]

Averaging over \(G_n\) yields
\[
\sum_{t=N+1}^{2N}S_t
\ge\frac{a\varepsilon^2}{32}w_n.
\tag{23}
\]
Combine this with (16) to obtain (18). \(\square\)

Thus, for every fixed pair satisfying (17),
\[
\boxed{S_t\ne o(2^{-K(t)}).}
\tag{24}
\]
This does not establish a matching upper bound.

---

## 4. The stronger “every sufficiently large \(t\)” question

Theorems 1 and 2 establish blockwise and infinitely-often conclusions. **They do not establish the requested lower bounds at every sufficiently large time.**

There are useful sufficient conditions for that stronger conclusion.

### Theorem 3 — eventual lower bounds when deterministic transitions retain positive mass

Let \(c_M>0\) satisfy 2.7F:
\[
q_M(b\mid x)\ge c_Mw_{|x|+1}.
\tag{25}
\]
Define
\[
\rho_t:=
\mu\{x:\mu(\cdot\mid x)\text{ is deterministic}\},
\qquad |x|=t-1.
\]
Then, for every \(t\),
\[
\boxed{
A_t\ge2c_M\rho_tw_t,\qquad
S_t\ge2c_M^2\rho_tw_t^2.
}
\tag{26}
\]

Consequently, \(\liminf_t\rho_t>0\) gives the proposed eventual bounds.

**Proof.** At a deterministic transition, the incorrect bit has true probability zero and predicted probability at least \(c_Mw_t\). Binary absolute and squared errors are therefore at least \(2c_Mw_t\) and \(2c_M^2w_t^2\). Integrate over those histories. \(\square\)

More generally, if
\[
\mu\left\{x:\min_b\mu(b\mid x)\le\frac{c_M}{2}w_t\right\}\ge\rho_t,
\]
the same argument gives
\[
A_t\ge c_M\rho_tw_t,\qquad
S_t\ge\frac{c_M^2}{2}\rho_tw_t^2.
\tag{27}
\]

These results cover some nondeterministic measures, including finite mixtures of distinct computable deterministic sequences after their paths have separated.

### Why exact global symmetrization is insufficient

For the fair coin, \(A_t=0\) implies \(q_M(b\mid x)=1/2\) at every history of length \(t-1\). This cannot happen at infinitely many times: along \(0^\infty\), infinitely many such factors would force \(Q(0^n)\to0\), contradicting the positive atom \(Q(\{0^\infty\})>0\) supplied by universality.

There is also a much weaker eventual bound. Since that atom is positive,
\[
q_M(0\mid0^{t-1})\longrightarrow1.
\]
Eventually it is at least \(3/4\), giving
\[
S_t\ge\frac14\,2^{-t},\qquad A_t\ge2^{-t}.
\tag{28}
\]

Neither observation settles the eventual \(w_t^2\) and \(w_t\) scales. A counterexample would require quantitatively small discrepancies, not merely repeated exact cancellation at selected individual histories.

**Status:** the general eventual assertion is neither proved nor refuted here.

---

## 5. What the summed upper bound does—and does not—give

### Theorem 4 — finite cumulative expected squared error

For every \(M\in\mathcal A\), every computable \(\mu\), and every \(u>0\) with
\[
M(x)\ge u\mu(x)\quad\forall x,
\]
one has
\[
\boxed{
\sum_{t\ge1}S_t
\le\ln\frac{M(\epsilon)}u.
}
\tag{29}
\]

**Proof.** Equation (5) gives \(Q\ge u\mu/M(\epsilon)\). The relative-entropy chain rule therefore yields
\[
\sum_{t=1}^n
\mathbb E_\mu
D_{\rm KL}\!\left(\mu(\cdot\mid X_{<t})\Vert q_M(\cdot\mid X_{<t})\right)
=
D_{\rm KL}(\mu_n\Vert Q_n)
\le\ln\frac{M(\epsilon)}u.
\]
For binary probability vectors, squared-vector distance is at most KL divergence. Let \(n\to\infty\). \(\square\)

This is the standard dominance/relative-entropy convergence argument; Hutter’s treatment develops the relevant distance comparisons and cumulative bounds. [jmlr.org](https://www.jmlr.org/papers/volume4/hutter03a/hutter03a.pdf?utm_source=chatgpt.com)

Tonelli’s theorem also gives
\[
\sum_ts_t(X_{<t})<\infty
\quad\mu\text{-almost surely},
\tag{30}
\]
and (1) gives
\[
\sum_tA_t^2<\infty.
\tag{31}
\]

### Correction to “\(o(1/t)\) on average”

If \(S:=\sum_tS_t<\infty\), then
\[
\frac1n\sum_{t=1}^nS_t
=\frac Sn+o(1/n).
\tag{32}
\]
Thus the average from the beginning is generally of order \(1/n\).

A correct little-\(o\) statement is the moving-block average
\[
\frac1n\sum_{t=n+1}^{2n}S_t=o(1/n).
\tag{33}
\]

Also, \(tS_t\to0\) in natural density. For fixed \(\eta>0\) and \(N<n\),
\[
\frac1n\#\{t\le n:tS_t>\eta\}
\le
\frac Nn+\frac1\eta\sum_{t>N}S_t.
\]
First let \(n\to\infty\), then \(N\to\infty\).

None of these is a pointwise rate. Indeed, the block argument proves a stronger obstruction.

### Theorem 5 — no computable pointwise expected convergence rate

For every \(M\in\mathcal A\), every computable probability measure \(\mu\), and every total computable nonnegative function \(r(t)\to0\),
\[
\boxed{
S_t\notin O(r(t)),
\qquad
A_t\notin O(r(t)).
}
\tag{34}
\]

Constants in the proposed \(O\)-bound may depend on \(M,\mu,r\); the conclusion still holds.

### Proof

Computably choose increasing disjoint blocks \(J_n\), each of length \(n\), such that
\[
r(t)<2^{-n}\qquad(t\in J_n).
\tag{35}
\]
No computable convergence modulus is needed. Search over candidate finite blocks using sufficiently accurate rational approximations to \(r(t)\), with a strict acceptance margin. Because \(r(t)\to0\), a passing block eventually exists.

Apply the general block construction from Theorem 1 with these starting positions and \(\ell_n=n\). Since
\[
(2/3)^n=o(w_n),
\]
equation (15) gives
\[
\sum_{t\in J_n}A_t\ge c\,w_n
\tag{36}
\]
eventually. The constant can depend on the fixed program computing \(r\), but not on \(n\).

If \(S_t\le Cr(t)\) eventually, then by (1),
\[
\sum_{t\in J_n}A_t
\le n\sqrt{2C}\,2^{-n/2},
\]
contradicting (36) and \(w_n\ge c_0(n+1)^{-2}\).

If \(A_t\le Cr(t)\) eventually, the upper bound \(Cn2^{-n}\) produces the same contradiction. \(\square\)

This is an **expectation theorem**. It does not, by itself, establish failure of every computable rate almost surely.

---

## 6. A genuine Solomonoff prior with large fair-coin error spikes

The preceding theorem concerns computable rates. Since \(w_t\) is not computable, it does not itself refute \(S_t=O(w_t)\). The following construction does.

### Theorem 6 — no general upper bound by any positive power of \(2^{-K(t)}\)

There exists \(M\in\mathcal B\) such that, for the iid fair-coin measure \(\lambda\),
\[
\boxed{
\forall\alpha>0,\qquad
\limsup_{t\to\infty}\frac{S_t(M,\lambda)}{w_t^\alpha}
=\infty.
}
\tag{37}
\]
The same holds for \(A_t\).

Moreover, \(M\) can be chosen so that on a set of \(\lambda\)-probability at least \(1/2\), both realized absolute and squared errors fail every bound \(O(w_t^\alpha)\).

### Proof

#### Step 1: lower semicomputable stopping lengths with complex endpoints

Define
\[
B(n):=
\max\bigl(\{0\}\cup
\{j:\text{some prefix program of length }\le n
\text{ outputs }j\}\bigr).
\tag{38}
\]
This finite, nondecreasing, unbounded function is lower semicomputable.

Set
\[
t_n:=B(n)+1.
\]
By definition,
\[
K(t_n)>n,\qquad w_{t_n}<2^{-n}.
\tag{39}
\]

Use the computable weights
\[
\gamma_n:=2^{-(2\lfloor\log_2n\rfloor+1)}.
\tag{40}
\]
These are the probabilities of Elias gamma codes:
\[
\sum_n\gamma_n=1,\qquad \gamma_n\asymp n^{-2}.
\tag{41}
\]

#### Step 2: asymmetric stopping semimeasures

For \(L\ge0\) and \(i\in\{0,1\}\), define
\[
\nu_{L,i}(x)=
\begin{cases}
\lambda(x),& |x|\le L,\\
\lambda(x),& |x|=L+1\text{ and the final bit is }i,\\
0,&\text{otherwise}.
\end{cases}
\tag{42}
\]
This is a semimeasure, and its value at every fixed \(x\) is nondecreasing in \(L\). Hence
\[
\nu_i:=\sum_{n\ge1}\gamma_n\nu_{B(n),i}
\tag{43}
\]
is lower semicomputable. Also \(\nu_i\le\lambda\).

Fix a Solomonoff prior \(V\), and put
\[
M^{(i)}:=\frac12V+\frac12\nu_i.
\tag{44}
\]
Both belong to \(\mathcal B\): a machine reads one initial bit, then either simulates the universal machine for \(V\), or implements \(\nu_i\).

For completeness, the latter branch gamma-decodes \(n\). At output position \(j\), it reads a fair bit \(b\), then waits until the current lower approximation to \(B(n)\) is at least \(j-1\) if \(b=i\), or at least \(j\) otherwise. It then prints \(b\). This produces exactly (42) with \(L=B(n)\). The universal branch preserves universality by adjunction.

#### Step 3: compare the two normalized predictions

For \(t\ge1\), write
\[
W_t:=\sum_{\{n:B(n)=t-1\}}\gamma_n,
\]
and
\[
h_t:=\sum_{\{n:B(n)\ge t\}}\gamma_n+\frac12W_t.
\]
At every history \(|x|=t-1\), the two priors have the same child-sum denominator:
\[
D_t(x)
:=
M^{(0)}(x0)+M^{(0)}(x1)
=
M^{(1)}(x0)+M^{(1)}(x1)
=
\frac12\bigl(V(x0)+V(x1)+h_t\lambda(x)\bigr).
\tag{45}
\]

Their normalized probabilities of bit zero differ by
\[
q_0(0\mid x)-q_1(0\mid x)
=
\frac{W_t\lambda(x)}{4D_t(x)}.
\tag{46}
\]

Since
\[
\sum_{|x|=t-1}D_t(x)\le1,
\]
Jensen’s inequality gives
\[
\mathbb E_\lambda(q_0-q_1)^2
=
\frac{W_t^2}{16}
\mathbb E_\lambda\left(\frac{\lambda(X_{<t})}{D_t(X_{<t})}\right)^2
\ge\frac{W_t^2}{16}.
\tag{47}
\]

For real \(u,v\),
\[
2(u-\tfrac12)^2+2(v-\tfrac12)^2\ge(u-v)^2.
\]
Consequently,
\[
S_t(M^{(0)},\lambda)+S_t(M^{(1)},\lambda)
\ge\frac{W_t^2}{16}.
\tag{48}
\]

At \(t=t_n\), \(W_{t_n}\ge\gamma_n\). Therefore one fixed \(i\) satisfies
\[
S_{t_n}(M^{(i)},\lambda)\ge\frac{\gamma_n^2}{32}
\asymp n^{-4}
\tag{49}
\]
for infinitely many \(n\).

By (39), for every fixed \(\alpha>0\),
\[
\frac{S_{t_n}(M^{(i)},\lambda)}{w_{t_n}^{\alpha}}
\ge c\,n^{-4}2^{\alpha n}\longrightarrow\infty
\]
along that subsequence. This proves the expected-error assertion. Absolute error is at least squared error, so its assertion follows too.

#### Step 4: the pathwise assertion

Under \(\lambda\),
\[
\frac{V(X_{<t})}{\lambda(X_{<t})}
\]
is a nonnegative supermartingale. Therefore
\[
C(\omega):=
\sup_t\left(1+\frac{V(\omega_{<t})}{\lambda(\omega_{<t})}\right)
<\infty
\quad\lambda\text{-almost surely}.
\tag{50}
\]

Using \(\nu_i\le\lambda\) in (45),
\[
D_t(x)\le\frac12(V(x)+\lambda(x)).
\]
Thus (46) implies
\[
|q_0(0\mid\omega_{<t_n})-q_1(0\mid\omega_{<t_n})|
\ge\frac{\gamma_n}{2C(\omega)}.
\]
For every such \(\omega\), at least one fixed \(i\) satisfies
\[
|q_i(0\mid\omega_{<t_n})-\tfrac12|
\ge\frac{\gamma_n}{4C(\omega)}
\tag{51}
\]
infinitely often. The two corresponding events cover a set of full measure, so one has probability at least \(1/2\). On that event, (39), (41), and (51) imply failure of every \(O(w_t^\alpha)\) bound.

The same selected prior also has the expected-error failures. Otherwise, an expected bound \(S_t\le C_0w_t^\alpha\), Markov’s inequality, and
\[
\sum_n\frac{w_{t_n}^{\alpha}}{\gamma_n^2}
\le
\sum_n\frac{2^{-\alpha n}}{\gamma_n^2}
<\infty
\]
would, by Borel–Cantelli, rule out (51) on every set \(C(\omega)\le k\). Taking the union over \(k\) contradicts its positive probability. \(\square\)

### Why summability cannot be converted into a coding upper bound

The exact stopping mass
\[
W_t=\sum_{\{n:B(n)=t-1\}}\gamma_n
\]
need not be lower semicomputable. It is a difference of lower semicomputable survival tails.

Likewise, although \(\sum_tS_t<\infty\), the sequence \(S_t\) need not possess a summable lower semicomputable envelope. Such an envelope would imply \(S_t=O(w_t)\) by (3), contradicting Theorem 6.

---

## 7. The defect comparison needs a class distinction

Define
\[
d_M(x):=
\frac{M(x)-M(x0)-M(x1)}{M(x)}.
\tag{52}
\]

### Theorem 7 — the standard defect floor holds for \(\mathcal B\)

For every \(M\in\mathcal B\), there is \(c_M>0\) such that
\[
d_M(x)\ge c_Mw_{|x|+1}\qquad\forall x.
\tag{53}
\]

This is Wood–Sunehag–Hutter’s Lemma 15, with \(K(|x|)\) instead of \(K(|x|+1)\), an equivalent scale up to constants. Its proof uses a compiler that simulates an input program until the prescribed number of output bits has appeared, then stops. [arxiv.org](https://arxiv.org/pdf/1111.3854?utm_source=chatgpt.com)

Indeed, encoding the stopping length \(n\) costs \(K(n)+O(1)\) bits. Applying this wrapper to all random inputs producing a given length-\(n\) prefix \(x\) puts at least \(c2^{-K(n)}M(x)\) mass on outputs that stop exactly at \(x\), proving (53).

Consequently, for every probability measure \(\mu\),
\[
\mathbb E_\mu d_M(X_{<t})\ge c_Mw_t.
\tag{54}
\]

For unnormalized predictions \(p_M(b\mid x)=M(xb)/M(x)\),
\[
\sum_b|p_M(b\mid x)-\mu(b\mid x)|\ge d_M(x),
\]
and
\[
\sum_b(p_M(b\mid x)-\mu(b\mid x))^2\ge\frac12d_M(x)^2.
\tag{55}
\]
These follow because the coordinate differences sum to \(-d_M(x)\).

Normalization removes that particular argument:
\[
p_M(\cdot\mid x)=(1-d_M(x))q_M(\cdot\mid x).
\]
A mass deficit alone does not force a directional error in \(q_M\).

### Theorem 8 — expected defect can vanish eventually in \(\mathcal A\)

There exist \(M\in\mathcal A\) and a nondeterministic computable probability measure \(\mu\) such that
\[
\boxed{\mathbb E_\mu d_M(X_{<t})=0\qquad(t\ge2).}
\tag{56}
\]

**Proof.** Fix a universal semimeasure \(V\), and let
\[
\mu=\tfrac12\delta_{0^\infty}+\tfrac12\delta_{1^\infty}.
\]
Set \(M(\epsilon)=1\). For \(n\ge1\) and \(b\in\{0,1\}\), define
\[
M(b^n)=\frac14+\frac14\sum_{k\ge n}V(b^k\bar b).
\tag{57}
\]
For strings that have left either constant spine, define
\[
M(b^k\bar b\,y)=\frac14V(b^k\bar b\,y),
\qquad k\ge1.
\tag{58}
\]

All values are lower semicomputable. On each spine,
\[
M(b^n)=M(b^{n+1})+M(b^n\bar b).
\]
Off the spines, the semimeasure inequality follows from that for \(V\). At the root,
\[
M(0)+M(1)
\le\frac12+\frac14\sum_{b,k\ge1}V(b^k\bar b)
\le\frac34,
\]
because the departure strings form a prefix-free set.

Also \(M\ge V/4\): this is equality off the spines, and follows from \(M(b^n)\ge1/4\) on them. Thus \(M\in\mathcal A\), while its defect vanishes at every history occurring under \(\mu\) after the first observation. \(\square\)

This is an atomic stochastic example. It does **not** refute a normalized-error lower bound: from time \(2\), its true transitions are deterministic, so Theorem 3 applies.

### Theorem 9 — \(2^{-K(t)}\) is a defect floor, not a defect ceiling

For every \(M\in\mathcal B\), every computable \(\mu\), and every \(\alpha>0\),
\[
\boxed{
\mathbb E_\mu d_M(X_{<t})\notin O(w_t^\alpha).
}
\tag{59}
\]
Moreover,
\[
d_M(X_{<t})\notin O(w_t^\alpha)
\quad\mu\text{-almost surely}.
\tag{60}
\]

**Proof.** Reuse \(B(n),t_n,\gamma_n\) from Theorem 6. Define
\[
\sigma_\mu(x)
:=
\mu(x)\sum_{\{n:B(n)\ge|x|\}}\gamma_n.
\tag{61}
\]
This lower semicomputable semimeasure samples \(n\), then samples from \(\mu\), printing additional bits whenever the current lower approximation to \(B(n)\) permits them. It eventually prints exactly \(B(n)\) bits.

Because \(M\) is a genuine universal-machine prior, its compiler contains this sampler as a fixed input branch. Thus
\[
M=c\sigma_\mu+\rho
\tag{62}
\]
for some \(c>0\) and a semimeasure \(\rho\). This additive decomposition is stronger than multiplicative dominance.

At every \(|x|=t_n-1\),
\[
M(x)-M(x0)-M(x1)
\ge c\gamma_n\mu(x).
\]
Therefore
\[
\begin{aligned}
\mathbb E_\mu d_M(X_{<t_n})
&\ge c\gamma_n
\sum_{|x|=t_n-1}\frac{\mu(x)^2}{M(x)}\\
&\ge c\gamma_n,
\end{aligned}
\tag{63}
\]
by Cauchy–Schwarz and \(\sum_{|x|=t_n-1}M(x)\le1\).

Equations (39) and (41) prove (59).

For (60), \(M(X_{<t})/\mu(X_{<t})\) is a nonnegative \(\mu\)-supermartingale, so its supremum is finite almost surely. Along such a path,
\[
d_M(X_{<t_n})
\ge
\frac{c\gamma_n}
{\sup_t M(X_{<t})/\mu(X_{<t})},
\]
which again exceeds every \(w_{t_n}^{\alpha}\) by unbounded factors. \(\square\)

Thus the phrase “the \(O(2^{-K(t)})\) defect-driven term” should be replaced: the known \(2^{-K(t)}\) statement is a **lower** bound on the defect. Normalization can remove much larger scalar defects, while asymmetric stopping can still produce the normalized-error spikes of Theorem 6.

---

## 8. Novelty of 2.7F and the deterministic result

### Theorem 10 — 2.7F is a known consequence

For every \(M\in\mathcal A\), there is \(c_M>0\) such that
\[
\boxed{
\forall x,b,\qquad
q_M(b\mid x)\ge c_M2^{-K(|x|+1)}.
}
\tag{64}
\]

Hutter’s *On Universal Prediction and Bayesian Confirmation* (2007), equation (17), states the unnormalized lower bound
\[
2^{-K(n)}\stackrel{\times}{\le}
M(\bar x_n\mid x_{<n}),
\]
and specifies that it is

> “valid for all \(n\) and \(x_{1:n}\) and \(\bar x_n\ne x_n\).”

The proof is in Appendix A. Since the designated \(x_n\) is arbitrary, its lower half covers every history and next symbol. [arxiv.org](https://arxiv.org/pdf/0709.1516?utm_source=chatgpt.com)

For a Solomonoff prior \(V\), normalization gives
\[
q_V(b\mid x)\ge\frac{V(xb)}{V(x)}\ge cw_{|x|+1}.
\]
For arbitrary \(M\in\mathcal A\), mutual universal dominance supplies \(a,A>0\) with
\[
aV(x)\le M(x)\le AV(x).
\]
Hence
\[
q_M(b\mid x)
\ge\frac{M(xb)}{M(x)}
\ge\frac aA\frac{V(xb)}{V(x)}
\ge c_Mw_{|x|+1}.
\]
This proves (64).

The Lean-checked result is therefore a formal verification of a known mathematical consequence.

### Theorem 11 — the deterministic normalized rate

For every \(M\in\mathcal A\) and every computable infinite sequence \(z\),
\[
1-q_M(z_t\mid z_{<t})=\Theta(w_t).
\tag{65}
\]

**Proof.** The lower bound is (64). For the upper bound, the strings \(z_{<t}\bar z_t\) form a computably enumerable prefix-free set. Thus
\[
g(t):=M(z_{<t}\bar z_t)
\]
is a lower semicomputable summable sequence, so \(g(t)\le Cw_t\). Universality gives \(M(z_{\le t})\ge u_z>0\), and therefore
\[
q_M(\bar z_t\mid z_{<t})
\le\frac{g(t)}{M(z_{\le t})}
\le\frac C{u_z}w_t.
\]
\(\square\)

This agrees with the deterministic bounds in Leike–Hutter’s PDF Lemmas 6 and 10. **arXiv:1507.04121 is the Nicod paper itself**, not a second source. Its stochastic discussion does not state the expected-discrepancy theorems proved above. [arxiv.org](https://arxiv.org/pdf/1507.04121?utm_source=chatgpt.com)

---

## 9. Status, confidence, and novelty assessment

The mathematical claims marked “proved here” have complete arguments above. I have not established publication priority for those derivations.

| Claim | Status | Confidence and novelty assessment |
|---|---|---|
| \(A_t\ge c\,2^{-K(t)}\) and \(S_t\ge c'\,2^{-2K(t)}\) infinitely often, for every \(M\in\mathcal A\) and computable \(\mu\) | **Proved**, with a witness in every sufficiently late dyadic block | High confidence; publication novelty not established |
| \(S_t\ge c\,2^{-K(t)}\) infinitely often for uniformly nondegenerate computable \(\mu\) | **Proved**, including the fair coin | High confidence; publication novelty not established |
| The requested lower bounds at every sufficiently large time, for arbitrary computable stochastic \(\mu\) | **Unresolved here** | Neither a proof nor a counterexample is claimed |
| A computable pointwise expected convergence rate for a fixed universal \(M\) and computable \(\mu\) | **Impossible**, even with pair-dependent constants | High confidence; proved by computably selected blocks |
| A general stochastic upper bound \(S_t=O(2^{-K(t)})\) | **False**, already for iid fair coin and \(M\in\mathcal B\) | High confidence; explicit two-prior construction, at least one of which is a counterexample |
| Upper bounds \(O(2^{-\alpha K(t)})\), \(\alpha>0\), for that construction | **All fail**, in expectation and on a positive-probability set of paths | High confidence; publication novelty not established |
| Expected defect floor for every \(M\in\mathcal A\) | **False** | Explicit eventually-zero example |
| Defect floor for \(M\in\mathcal B\) | **Known** | Wood–Sunehag–Hutter, Lemma 15 |
| Defect upper bounds \(O(2^{-\alpha K(t)})\) for \(M\in\mathcal B\) | **All fail**, for every computable \(\mu\), in expectation and almost surely | High confidence; busy-beaver stopping proof above |
| Uniform normalized symbol floor 2.7F | **Known consequence** | Hutter 2007, equation (17), plus normalization and mutual dominance |
| Deterministic normalized \(\Theta(2^{-K(t)})\) rate | **Known** | Consistent with Leike–Hutter 2015 and the prefix-free proof above |

The principal remaining question from the attachment is precisely the eventual quantifier:
\[
\forall M\in\mathcal A\ \forall\text{ computable stochastic }\mu\
\exists c>0\ \exists T\ \forall t\ge T:
\quad S_t\ge c\,2^{-2K(t)},
\]
and its absolute-error analogue. The infinitely-often versions are established by Theorem 1; the stronger eventual versions should remain separate research targets.