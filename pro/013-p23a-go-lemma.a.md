# Result

**The reduction is valid. I do not prove or refute \(\mathsf{GO}(P)\).** In particular, I found no error in Theorems A, E, or H that would trigger your instruction to stop.

I can establish several more precise results:

1. **The counting bound alone does not settle the question.** I give two constructions satisfying all the structural admissibility conditions except universal dominance, with the same global quadratic capacity bound. One converges uniformly on every sequence, while the other fails on a sequence in the exact class \(P\).
2. **Quadratic capacity is not intrinsic to the reduction.** An equivalent granular formulation has only \(O(n\log ^2 n)\) possible increases per node on a deficiency layer.
3. **A larger subclass satisfies GO:** arbitrary signed \(o(\lambda)\) perturbations of universal mixtures, and more generally predictors whose multiplicative ratio to a universal mixture changes asymptotically by a factor tending to one.
4. **There is a positive construction after dropping enumerability.** A \(\varnothing'\)-computable probability measure can dominate \(\xi/2\) and predict correctly on every fair-coin ML-random sequence. I prove that this measure is necessarily not lower semicomputable.
5. **The proposed compactness shortcut fails even on \(P\) itself:** arbitrarily long finite chains of permanent visits, finite total event weight, and \(\varnothing'\)-decidable edge labels do not ensure an infinite chain.

All the proved statements below have **high informal proof confidence**. I make no priority claim for the deductions or constructions.

---

# 1. Audit of the reduction

Write \(2^{<\mathbb N}\) for finite binary strings, \(\epsilon\) for the empty string, and
\[
\lambda(x)=2^{-|x|}.
\]
A semimeasure satisfies
\[
q(\epsilon)\le 1,
\qquad
q(x0)+q(x1)\le q(x).
\]
“Enumerable” means uniformly lower semicomputable.

As in the report, let \(\mathcal A\) be the enumerable semimeasures dominating every enumerable semimeasure, let \(\mathcal C\) be the effective universal mixtures, and fix \(\xi\in\mathcal C\).

## Theorem 1 — Theorem A is valid

For every \(U\in\mathcal A\) and integer \(K\ge1\), define
\[
H_K^U(x)=
\sup_{\substack{A\text{ finite prefix-free}\\y\in A\Rightarrow x\preceq y}}
\sum_{y\in A}\max\{\lambda(y),U(y)/K\},
\qquad
Q_K^U=\frac K{K+1}H_K^U.
\]
Then all four conclusions of Theorem A hold. In particular,
\[
P=P_3[\xi]
\]
is effectively closed,
\[
\lambda(P)\ge\frac23,
\qquad
P\subseteq\operatorname{MLR}(\lambda).
\]

**Proof confidence: high.**

### Proof

Every defining prefix-free sum is at most
\[
\sum_{y\in A}\lambda(y)+\frac1K\sum_{y\in A}U(y)
\le \lambda(x)+\frac{U(x)}K.
\]
Taking singleton cutsets and cutsets below the two children gives
\[
\lambda\le H_K^U\le\lambda+U/K
\]
and
\[
H_K^U(x)
=
\max\left\{\frac{U(x)}K,\,
H_K^U(x0)+H_K^U(x1)\right\}.
\tag{1}
\]
The baseline term \(\lambda(x)\) need not appear separately in (1), since the child sum is already at least \(\lambda(x)\).

The supremum is uniformly lower semicomputable. Equation (1) proves the semimeasure inequality and additivity whenever
\[
U(x)\le K\lambda(x).
\]
Also,
\[
Q_K^U(\epsilon)\le
\frac K{K+1}\left(1+\frac1K\right)=1,
\qquad
Q_K^U\ge\frac{U}{K+1}.
\]
Thus \(Q_K^U\in\mathcal A\).

The complement of \(P_K[U]\) is effectively open. Its first-crossing cylinders are disjoint, and
\[
\sum_{\text{first crossings }s}\lambda(s)
\le
\frac1K\sum_sU(s)
\le\frac1K.
\]
The first-crossing set itself need not be c.e.; this does not affect the measure estimate.

The standard universal-semimeasure characterization says
\[
\omega\in\operatorname{MLR}(\lambda)
\iff
\sup_n\frac{U(\omega{\upharpoonright}n)}
{\lambda(\omega{\upharpoonright}n)}<\infty.
\tag{2}
\]
It applies to every \(U\in\mathcal A\), not just to mixtures. Hence
\[
\bigcup_{K\ge1}P_K[U]=\operatorname{MLR}(\lambda).
\]
This characterization is explicitly stated in Barmpalias–Shen. [arxiv.org](https://arxiv.org/pdf/2111.00516?utm_source=chatgpt.com)

For the quantitative assertion, put \(R_K=H_K^U-\lambda\). Completing finite cutsets with baseline leaves gives
\[
R_K(x)=
\sup_A\sum_{y\in A}\bigl(U(y)/K-\lambda(y)\bigr)_+.
\tag{3}
\]
Suppose all prefixes of \(x\) satisfy the layer bound. Group the positive terms in (3) by their first crossing \(s\) below \(x\). At such a crossing,
\[
U(s)\le U(s^-)\le K\lambda(s^-)=2K\lambda(s).
\]
The semimeasure inequality therefore gives
\[
0\le R_K(x)
\le
\min\left\{\frac{U(x)}K,\,
2\lambda([x]\setminus P_K[U])\right\}.
\tag{4}
\]

At a good node, \(R_K(x)=R_K(x0)+R_K(x1)\), so
\[
\left|
\frac{H_K^U(xb)}{H_K^U(x)}-\frac12
\right|
\le
\frac{R_K(x)}{2(\lambda(x)+R_K(x))}.
\]
Writing \(d_K(x)=\lambda(P_K[U]^c\mid[x])\), equation (4) yields
\[
\left|Q_K^U(b\mid x)-\frac12\right|
\le
\min\left\{\frac14,\frac{d_K(x)}{1+2d_K(x)}\right\}.
\]
Ordinary and normalized predictions agree at these additive nodes. This proves the asserted density-one convergence, with exactly the qualification made in the report. ∎

## Theorem 2 — Theorem E and its stagewise realization are valid

For every \(U\in\mathcal A\), let
\[
S(x)=\frac{\lambda(x)}{|x|+1},
\qquad
h_n=\frac{2^{-n}}{2(n+1)(n+2)},
\qquad
v(x)=\frac{U(x)+S(x)}2,
\]
and let \(G(U)(x)\) be the greatest nonnegative multiple of \(h_{|x|}\) strictly below \(v(x)\).

Then
\[
G(U)=\frac U2+e,
\]
where \(e\) is a nonnegative semimeasure satisfying
\[
\frac{\lambda(x)}{2(n+2)}
\le e(x)<
\frac{\lambda(x)}{2(n+1)}.
\tag{5}
\]
The ordinary and normalized prediction estimates in Theorem E hold.

Moreover, \(G(U)\) has a computable increasing integer presentation satisfying the report’s flow inequality at every stage.

**Proof confidence: high.**

### Proof

Let
\[
r(x)=v(x)-G(U)(x).
\]
Strict rounding gives
\[
0<r(x)\le h_n.
\]
Since
\[
\Delta_S(x)=2h_n,
\]
we have
\[
\begin{aligned}
\Delta_{G(U)}(x)
&=\frac12\Delta_U(x)+h_n-r(x)+r(x0)+r(x1)\\
&\ge\frac12\Delta_U(x).
\end{aligned}
\tag{6}
\]
Thus \(e=G(U)-U/2\) is a semimeasure. Subtracting the rounding loss gives (5), in particular \(e\ge0\).

Strict rounding is lower semicomputable: the assertion \(kh_n<v(x)\) is c.e. The use of **strict** rounding handles equality correctly. If \(v(x)=kh_n\), the rounded value is \((k-1)h_n\).

If \(U\ge d\lambda\), put \(p=U(xb)/U(x)\). Then
\[
G(U)(b\mid x)-p
=
\frac{e(xb)-p\,e(x)}{U(x)/2+e(x)}.
\]
Both terms in the numerator belong to \([0,e(x)]\), so
\[
|G(U)(b\mid x)-U(b\mid x)|
\le\frac1{d(n+1)}.
\tag{7}
\]
The normalized calculation uses
\[
e(x0)+e(x1)<\frac{\lambda(x)}{2(n+2)},
\qquad
U(x0)+U(x1)\ge d\lambda(x),
\]
and gives the report’s bound \(1/[d(n+2)]\).

Here is the detailed justification of stagewise admissibility.

Choose increasing computable rational lower bounds \(u_s(x)\uparrow U(x)\), with finite support at each stage. Define their finite-tree envelopes
\[
U_s(x)=
\max_{\substack{A\text{ prefix-free}\\A\subseteq x2^{<\mathbb N}}}
\sum_{y\in A}u_s(y).
\]
Finite support makes this maximum computable by the recursion
\[
U_s(x)=\max\{u_s(x),U_s(x0)+U_s(x1)\}.
\]
Thus \(U_s\) is a rational semimeasure,
\[
u_s\le U_s\le U,
\qquad
U_s\uparrow U.
\]

Now define
\[
a_s(x)=
\max\left\{k\in\mathbb N:
kh_{|x|}<\frac{U_s(x)+S(x)}2
\right\}.
\tag{8}
\]
These integers are computable and nondecreasing. The calculation (6), applied to \(U_s\), proves the semimeasure inequality at every stage. Equivalently,
\[
(n+1)\bigl(a_s(x0)+a_s(x1)\bigr)
\le2(n+3)a_s(x).
\]

Strict rounding commutes with the increasing limit: \(kh_n<v(x)\) holds exactly when it holds at some stage. Consequently,
\[
h_{|x|}\lim_sa_s(x)=G(U)(x).
\]

At the root, \(v(\epsilon)\le1\) and \(h_0=1/4\), so strict rounding actually gives
\[
a_s(\epsilon)\le3,
\]
stronger than the required bound \(4\). Finally, \(G(U)\ge U/2\), so it dominates \(\xi\). ∎

The safety-margin rounding method is standard; Barmpalias–Shen discuss it in their exposition of Levin’s construction. The estimates and stagewise verification above are direct checks of the report’s particular choice. [arxiv.org](https://arxiv.org/pdf/2111.00516?utm_source=chatgpt.com)

## Theorem 3 — Theorem H is an exact equivalence

For the fixed \(P=P_3[\xi]\), the following are equivalent:

1. \(\mathsf{GO}(P)\).
2. Every \(q\in\mathcal A\) fails to predict fair coin on some \(\lambda\)-ML-random sequence.

Negating \(\mathsf{GO}(P)\) gives an admissible array whose predictor converges on every fair-coin ML-random sequence.

**Proof confidence: high.**

### Proof

For any admissible array,
\[
q_a(x)=h_{|x|}a(x)
\]
is an enumerable semimeasure with root at most one, and the dominance requirement puts it in \(\mathcal A\). Since
\[
\frac{h_{n+1}}{h_n}=\frac{n+1}{2(n+3)},
\]
we have
\[
q_a(b\mid x)=
\frac{(n+1)a(xb)}{2(n+3)a(x)}.
\tag{9}
\]
Thus the boxed GO inequality is exactly a prediction error exceeding \(\varepsilon\).

We also need the tail property
\[
\operatorname{MLR}(\lambda)
=
\bigcup_{\sigma\in2^{<\mathbb N}}\sigma P.
\tag{10}
\]
This is the applicable form of Kučera’s tail theorem. [lirmm.fr](https://www.lirmm.fr/~ashen/nafit/2010ergodic.pdf?utm_source=chatgpt.com)

For completeness, let \(B\) be a c.e. prefix-free cylinder code for \(P^c\). Its Kraft sum is at most \(1/3\). Concatenations \(B^k\) form c.e. prefix-free codes with measure at most \(3^{-k}\le2^{-k}\). If a sequence has no tail in \(P\), it can be parsed successively into \(k\) words from \(B\), for every \(k\). It therefore belongs to every \([B^k]\), contradicting ML-randomness. Conversely, adjoining a fixed finite prefix preserves randomness, and every member of \(P\) is random. This proves (10).

Now assume GO and take arbitrary \(U\in\mathcal A\). Theorem 2 supplies an admissible presentation of \(G(U)\). GO gives a bad random path for \(G(U)\), and (7) transfers infinitely many fixed-size errors to \(U\).

Conversely, apply statement 2 to \(q_a\), and use (10) to write its bad random sequence as \(\sigma\alpha\), \(\alpha\in P\). Deleting finitely many initial predictions preserves infinitely many errors. A smaller positive rational threshold gives the exact GO formulation.

Negating GO and using (10) proves the final assertion. ∎

The capacity calculation is also correct:
\[
a(x)=2(n+1)(n+2)\frac{q_a(x)}{\lambda(x)}.
\tag{11}
\]
There is a uniform polynomial bound on all paths of each fixed \(\sigma P\): universality of \(\xi\) gives
\[
q_a(\sigma x)\le C_\sigma\xi(x),
\]
so for \(x\prec\alpha\in P\),
\[
\frac{q_a(\sigma x)}{\lambda(\sigma x)}
\le3C_\sigma2^{|\sigma|}.
\tag{12}
\]

---

# 2. What the counting bound does—and does not—prove

## Theorem 4 — The structural conditions and polynomial capacities support both outcomes

There exist computable increasing integer arrays \(a_s^+\) and \(a_s^-\) satisfying the root and stagewise flow conditions, with associated semimeasures \(q^+\) and \(q^-\), such that
\[
q^\pm(\epsilon)=\frac34,
\qquad
\frac14\lambda\le q^\pm\le\lambda.
\tag{13}
\]
In particular, at every node,
\[
a_s^\pm(x)\le2(|x|+1)(|x|+2).
\tag{14}
\]

Nevertheless:

- \(q^+\) converges uniformly to the fair-coin predictor on every sequence.
- \(q^-\) fails on some \(\beta\in P\), with error exceeding \(1/20\) infinitely often.
- The presentation of \(q^+\) can have no computable depthwise stabilization bound.

Neither array satisfies universal dominance.

**Proof confidence: high.**

### Proof

Let \(\beta=\min_{\mathrm{lex}}P\), identified with its binary real. It is left-c.e.: the minima of finite clopen approximations \(P_s\searrow P\) increase computably to \(\beta\). Because \(\beta\in P\), it is random, noncomputable, and non-dyadic.

Set
\[
\theta=\frac{1+\beta}{2}\in(1/2,1).
\]

### The convergent array

Apply the same rounding construction to \(U^+=\theta\lambda\):
\[
q^+=G(\theta\lambda).
\]
The proof of Theorem 2 applies without universality whenever a positive fair-coin lower bound is available.

At depth \(n\), its integer is
\[
a^+(x)=
\max\{k\in\mathbb N:
k<(n+1)(n+2)\theta+(n+2)\}.
\tag{15}
\]
A rational increasing approximation \(\theta_s\uparrow\theta\) gives the required stagewise arrays.

Writing \(r_n=q^+(x)/\lambda(x)\), equation (5) gives
\[
\frac\theta2+\frac1{2(n+2)}
\le r_n<
\frac\theta2+\frac1{2(n+1)}.
\]
Thus \(r_n\to\theta/2>0\), and
\[
q^+(b\mid x)=\frac12\frac{r_{n+1}}{r_n}\longrightarrow\frac12
\]
uniformly.

If a computable function \(s(n)\) supplied the final integer at depth \(n\), then (15) would give computable intervals
\[
\frac{a^+(x)-(n+2)}{(n+1)(n+2)}
<
\theta
\le
\frac{a^+(x)+1-(n+2)}{(n+1)(n+2)}
\]
of effectively vanishing length. This would compute \(\theta\), a contradiction.

### The divergent array

For the dyadic interval \(I_x\) corresponding to \(x\), put
\[
\nu_\beta(x)=\operatorname{Leb}(I_x\cap[0,\beta)).
\]
This is an enumerable additive subprobability with \(0\le\nu_\beta\le\lambda\). Define
\[
U^-=\frac{\lambda+\nu_\beta}{2},
\qquad
q^-=G(U^-).
\]
Since \(\lambda/2\le U^-\le\lambda\), the rounding estimates give (13)–(14). Both constructions have root \(3/4\), because their unrounded root is
\[
v(\epsilon)=\frac{3+\beta}{4}\in(3/4,1).
\]

Consider a position where \(\beta_t\beta_{t+1}=01\), with \(x=\beta_{<t}\). Let
\[
r=\frac{\nu_\beta(x)}{\lambda(x)}.
\]
Then \(1/4\le r<1/2\) and \(\nu_\beta(x0)=\nu_\beta(x)\), so
\[
U^-(0\mid x)
=
\frac{1/2+r}{1+r}
=
\frac12+\frac{r}{2(1+r)}
\ge\frac12+\frac1{10}.
\]
The prediction comparison for \(G\), using \(U^-\ge\lambda/2\), gives
\[
|q^-(b\mid x)-U^-(b\mid x)|
\le\frac2{|x|+1}.
\]
Hence all sufficiently late occurrences of \(01\) give
\[
q^-(0\mid x)>\frac12+\frac1{20}.
\]
There are infinitely many such occurrences: a binary sequence with only finitely many \(01\) transitions is eventually constant, whereas \(\beta\) is random.

Finally, \(q^\pm\le\lambda\), so neither dominates the computable Dirac measure on \(0^\infty\). ∎

This establishes a precise limitation of counting: **flows, polynomial capacities, a fair-coin lower bound, and even nonrecognizable stabilization do not determine the answer.** It does not rule out an argument that combines the counting bound with the full hypothesis \(q_a\ge c\xi\).

---

# 3. The quadratic bound can be reduced

## Theorem 5 — An equivalent formulation has \(O(n\log ^2 n)\) capacities

Let \(f_n>0\) be computable rationals whose tails
\[
T_n=\sum_{k\ge n}f_k
\]
are uniformly computable rational numbers, with \(T_0\le1\). Define
\[
S_f(x)=\lambda(x)T_{|x|},
\qquad
h_n^f=\frac{2^{-n}f_n}{2}.
\]
Strictly round \((U+S_f)/2\) to this grid, obtaining \(G_f(U)\).

For every \(U\in\mathcal A\),
\[
G_f(U)=\frac U2+e_f,
\]
where \(e_f\) is a nonnegative semimeasure and
\[
\frac{\lambda(x)T_{n+1}}2
\le e_f(x)<
\frac{\lambda(x)T_n}2.
\tag{16}
\]
The corresponding granular GO assertion is equivalent to the original \(\mathsf{GO}(P)\).

There is a choice of \(f\) for which the number of increases at a node on a fixed density layer is
\[
O_L\!\left(n\log ^2(n+2)\right).
\]

**Proof confidence: high.**

### Proof

The safety margin is
\[
\Delta_{S_f}(x)=\lambda(x)f_n=2h_n^f.
\]
The rounding calculation (6) therefore applies unchanged and proves (16). If \(U\ge d\lambda\), the prediction distances are at most
\[
\frac{T_n}{d}
\quad\text{and}\quad
\frac{T_{n+1}}d
\]
for ordinary and normalized prediction respectively. Both tend to zero. Rational tails allow the same computable stagewise construction as (8).

The new flow inequality is
\[
f_{n+1}\bigl(a_s(x0)+a_s(x1)\bigr)
\le2f_na_s(x),
\]
and the bad-edge inequality is
\[
|f_{n+1}a(xb)-f_na(x)|
>
2\varepsilon f_na(x).
\]
Repeating Theorem 3 proves equivalence.

On a layer \(q_a(x)\le L\lambda(x)\),
\[
a(x)\le\frac{2L}{f_n}.
\tag{17}
\]

Now take
\[
k(n)=\lfloor\log_2(n+1)\rfloor,
\qquad
f_n=\frac1{2^{k(n)}(k(n)+1)(k(n)+2)}.
\]
The \(k\)-th block has \(2^k\) entries and total mass
\[
\frac1{(k+1)(k+2)}.
\]
These block masses telescope to one. For \(k=k(n)\), the exact tail is
\[
T_n=
\frac1{k+2}
+
\frac{2^{k+1}-n-1}{2^k(k+1)(k+2)}.
\]
Thus all hypotheses hold, and (17) becomes
\[
a(x)\le2L\,2^k(k+1)(k+2)
=
O_L(n\log^2(n+2)).
\]
Also \(f_0=1/2\), so the root grid is still \(1/4\). ∎

Thus the original quadratic count is a feature of the chosen margin, not a sharp dividing line for this problem.

---

# 4. What the measure bound actually supplies

## Theorem 6 — Finite error weight and the effectivity distinction

For every semimeasure \(q\ge c\lambda\), \(c>0\), and every \(\varepsilon>0\), define
\[
B_\varepsilon(q)=
\left\{xb:
\left|\frac{q(xb)}{q(x)}-\frac12\right|>\varepsilon
\right\}.
\]
Then, using natural logarithms,
\[
\sum_{xb\in B_\varepsilon(q)}\lambda(xb)
\le
\frac{\log(q(\epsilon)/c)}{2\varepsilon^2}.
\tag{18}
\]

Every c.e. subset of \(B_\varepsilon(q)\) is visited only finitely often by every ML-random sequence. For an admissible array, \(B_\varepsilon(q_a)\) is decidable in \(\varnothing'\), and every \(2\)-random sequence has only finitely many such errors.

**Proof confidence: high.**

### Proof

At node \(x\), write \(p_b=q(xb)/q(x)\) and
\[
L(x)=-\frac12\log(4p_0p_1).
\]
Since \(p_0+p_1\le1\),
\[
p_0p_1\le p_b(1-p_b)
=\frac14-(p_b-\tfrac12)^2.
\]
Therefore
\[
L(x)\ge2(p_b-\tfrac12)^2
\]
for each \(b\), and hence
\[
L(x)\ge
(p_0-\tfrac12)^2+(p_1-\tfrac12)^2.
\]
Expected log loss telescopes:
\[
\sum_{|x|<N}\lambda(x)L(x)
=
\sum_{|z|=N}\lambda(z)
\log\frac{\lambda(z)q(\epsilon)}{q(z)}
\le\log\frac{q(\epsilon)}c.
\]
Since \(\lambda(xb)=\lambda(x)/2\), letting \(N\to\infty\) proves (18).

For a c.e. set of strings of finite total weight, the number of visits is a lower-semicomputable function of finite expectation. Markov bounds on its level sets give an ML-test covering paths with infinitely many visits. The same argument relativizes.

For an admissible array, the global root bound implies
\[
a(x)\le\frac1{h_{|x|}}
=2^{|x|+1}(|x|+1)(|x|+2).
\]
The halting oracle decides each question
\[
\exists s\;a_s(x)\ge k,
\]
so it computes the final integer exactly. It therefore decides the rational GO inequality. Apply the relativized finite-weight argument. ∎

The desired failure set must consequently be a null set containing an ML-random point, and its permanently bad edges cannot be supplied by a sound c.e. enumeration. A finite measure bound does not itself establish that such a point exists.

---

# 5. A proved negative subclass

## Theorem 7 — GO holds when changes in the relative multiplier vanish

Let \(M\in\mathcal C\) and \(q\in\mathcal A\). For each \(\omega\), put
\[
R_\omega(n)=
\frac{q(\omega{\upharpoonright}n)}
     {M(\omega{\upharpoonright}n)}.
\]
Suppose
\[
\forall\omega\in\operatorname{MLR}(\lambda),\qquad
\frac{R_\omega(n+1)}{R_\omega(n)}\longrightarrow1.
\tag{19}
\]
Then \(q\) fails on a fair-coin ML-random sequence. If \(q=q_a\), the array satisfies \(\mathsf{GO}(P)\).

It is enough that (19) hold on one ML-random nonconvergence witness for \(M\).

**Proof confidence: high, using the published Lattimore–Hutter theorem.**

### Proof

Lattimore–Hutter’s Theorem 6 supplies a random \(\omega\) and \(\eta>0\) for which \(M\)’s prediction error exceeds \(\eta\) infinitely often—in fact, on a set of positive upper density. [hutter1.net](https://www.hutter1.net/publ/mnonconvx.pdf?utm_source=chatgpt.com)

But
\[
q(\omega_{n+1}\mid\omega{\upharpoonright}n)
=
M(\omega_{n+1}\mid\omega{\upharpoonright}n)
\frac{R_\omega(n+1)}{R_\omega(n)}.
\]
Since \(M\)’s conditional is at most one, the two predictions differ by at most
\[
\left|\frac{R_\omega(n+1)}{R_\omega(n)}-1\right|,
\]
which tends to zero. Thus \(q\)’s error exceeds \(\eta/2\) infinitely often. The tail decomposition (10) gives GO. ∎

Because \(q\) and \(M\) dominate one another, \(R_\omega(n)\) is globally bounded above and below by positive constants. Consequently, (19) is equivalent to
\[
R_\omega(n+1)-R_\omega(n)\to0.
\]

An immediate useful case is
\[
q(x)=cM(x)+r(x),
\qquad c>0,
\]
with
\[
\forall\omega\in\operatorname{MLR}(\lambda),\qquad
\frac{r(\omega{\upharpoonright}n)}
{\lambda(\omega{\upharpoonright}n)}\to0.
\tag{20}
\]
Indeed, \(M\ge d\lambda\) implies \(R_\omega(n)\to c\).

**No sign, semimeasure, or computability condition on \(r\) is needed.** Thus this includes arbitrary signed perturbations satisfying (20), beyond the nonnegative semimeasure residual in Theorem E. In particular, every \(G(M)\), \(M\in\mathcal C\), satisfies GO.

---

# 6. A positive construction using the halting oracle

The following is a stronger analytical comparison than a merely “nearly universal” convergent predictor.

## Theorem 8 — A \(\varnothing'\)-computable universal probability measure predicts every fair-coin random sequence

For every \(\xi\in\mathcal A\), there exists a \(\varnothing'\)-computable probability measure \(\mu\) such that
\[
\mu(x)\ge\frac12\xi(x)
\qquad\forall x,
\tag{21}
\]
and
\[
\sup_n\frac{\xi(\omega{\upharpoonright}n)}
{\lambda(\omega{\upharpoonright}n)}<\infty
\quad\Longrightarrow\quad
\mu(\omega_{n+1}\mid\omega{\upharpoonright}n)\to\frac12.
\tag{22}
\]
Hence \(\mu\) predicts correctly on every fair-coin ML-random sequence.

The measure \(\mu\) is **not lower semicomputable**.

**Proof confidence: high.**

### Step 1: Upcrossing portfolios

Let
\[
D(x)=\frac{\xi(x)}{\lambda(x)}.
\]
Then \(D\) is a nonnegative supermartingale:
\[
D(x)\ge\frac{D(x0)+D(x1)}2,
\qquad D(\epsilon)\le1.
\]
Universality gives a constant \(d>0\) with \(D\ge d\).

Enumerate all rational intervals \(0<r_i<s_i\), \(i\ge1\), and let
\[
w_i=\frac{2^{-i}}{1+r_i}.
\]
Thus
\[
\sum_iw_i\le1,
\qquad
\sum_iw_ir_i\le1.
\]

Portfolio \(i\) starts with cash \(r_i\), holding no share of \(D\). At node \(x\), it:

- buys one share if it holds none and \(D(x)\le r_i\);
- sells if it holds one and \(D(x)>s_i\);
- otherwise retains its position.

Let \(S_i(x)\) be its wealth and \(h_i(x)\in\{0,1\}\) its holding for the next edge. Transactions do not change wealth, so
\[
S_i(xb)-S_i(x)
=
h_i(x)\bigl(D(xb)-D(x)\bigr).
\tag{23}
\]
Cash remains nonnegative: purchases cost at most \(r_i\), and each completed trade earns more than \(s_i-r_i\). Hence \(S_i\ge0\), and (23) shows that it is a supermartingale.

If the path has infinitely many upcrossings of \([r_i,s_i]\), then
\[
S_i(\omega{\upharpoonright}n)\to\infty.
\tag{24}
\]
Indeed, after \(j\) completed trades, even while holding a newly purchased share, cash is at least \(j(s_i-r_i)\).

Define
\[
Q(x)=D(x)+\sum_iw_iS_i(x).
\tag{25}
\]
Every nonnegative supermartingale satisfies \(S_i(x)\le2^{|x|}S_i(\epsilon)\). Therefore
\[
\sum_{i>N}w_iS_i(x)\le2^{|x|-N}.
\tag{26}
\]
The series is finite and has an effective tail bound.

We have
\[
Q\ge D,\qquad Q(\epsilon)\le2,
\]
and, by (23),
\[
Q(xb)-Q(x)
=
H(x)\bigl(D(xb)-D(x)\bigr),
\qquad
1\le H(x):=1+\sum_iw_ih_i(x)\le2.
\tag{27}
\]

### Step 2: Add back the supermartingale losses

Put
\[
d_Q(x)=Q(x)-\frac{Q(x0)+Q(x1)}2\ge0,
\]
\[
A(x)=\sum_{y\prec x}d_Q(y),
\qquad
R(x)=Q(x)+A(x).
\]
Then \(R\) is a martingale, because
\[
\frac{R(x0)+R(x1)}2
=
\frac{Q(x0)+Q(x1)}2+A(x)+d_Q(x)
=R(x).
\]

Let
\[
C=2-Q(\epsilon)\ge0,
\qquad
\mu(x)=\frac{\lambda(x)}2\bigl(R(x)+C\bigr).
\tag{28}
\]
This is additive and has root one, so it is a probability measure. Moreover,
\[
\mu(x)\ge\frac{\lambda(x)Q(x)}2
\ge\frac{\lambda(x)D(x)}2
=\frac{\xi(x)}2.
\]

### Step 3: Convergence on every bounded-\(D\) path

Fix \(\omega\) with \(D(\omega{\upharpoonright}n)\le B\) for every \(n\). Along its realized edges, (27) gives
\[
|\Delta Q|\le2B.
\]
Averaging (27) also gives
\[
d_Q(x)=H(x)d_D(x)\le2D(x)\le2B.
\]
Consequently,
\[
|\Delta R|\le4B.
\tag{29}
\]

There are three cases.

**If \(D\) does not converge**, choose rational thresholds strictly between its liminf and limsup. The corresponding portfolio completes infinitely many upcrossings. By (24),
\[
Q\to\infty,\qquad R\to\infty.
\]
Equation (29) then gives
\[
\frac{\Delta R}{R+C}\to0.
\]

**If \(D\) converges and \(A\to\infty\)**, again \(R\to\infty\), so the same conclusion follows from (29).

**If \(D\) converges and \(A\) is bounded**, equation (27) gives \(\Delta Q\to0\). The nonnegative increments of bounded \(A\) tend to zero, so
\[
\Delta R=\Delta Q+d_Q\to0.
\]
The denominator is bounded below by \(R+C\ge D\ge d>0\).

In every case,
\[
\mu(\omega_{n+1}\mid\omega{\upharpoonright}n)-\frac12
=
\frac{\Delta R}{2(R+C)}
\longrightarrow0.
\]
This proves (22). Since \(\mu\) is a measure, the other bit’s conditional has the same absolute error.

### Step 4: Effectivity and its exact limitation

Because \(D\) is left-c.e., the predicates
\[
D(x)>s_i,
\qquad
D(x)\le r_i
\]
are respectively c.e. and co-c.e. They are decidable in \(\varnothing'\). Thus the oracle computes every finite trading history. The tail bound (26) then makes \(Q\), and hence \(A,R,\mu\), uniformly \(\varnothing'\)-computable.

Suppose \(\mu\) were lower semicomputable. A lower-semicomputable probability measure is computable: at each finite level,
\[
\mu(x)=1-\sum_{\substack{|y|=|x|\\y\ne x}}\mu(y)
\]
also provides an upper approximation.

No computable probability measure can dominate every computable Dirac measure. To see this, construct a computable path \(z\) with
\[
\mu(z{\upharpoonright}n)<(3/4)^n
\qquad(n\ge1).
\]
At each step, one child has at most half the parent’s mass, and computability lets us find a child satisfying the next strict bound. Then \(\mu(z{\upharpoonright}n)\to0\), contradicting domination of the computable Dirac measure \(\delta_z\).

But (21) and universality of \(\xi\) imply precisely that domination. Therefore \(\mu\) is not lower semicomputable. ∎

This is **not a refutation of GO**. The positive construction uses permanent upper information in the buying decisions and differences in the compensation step. Its final probability measure provably lacks a computable monotone lower approximation.

For the fixed mixture \(\xi\), its density can also become unbounded on an ML-random sequence: a Lattimore–Hutter failure witness has bounded but nonconvergent \(D\), so the portfolios force \(Q\to\infty\). Thus this construction does not preserve the polynomial capacities on \(\xi\)-deficiency layers either.

---

# 7. Why compactness and a \(\varnothing'\)-search do not finish the proof

## Theorem 9 — Arbitrarily long finite visit chains need not give an infinite visit chain on \(P\)

There exists a set \(B\subseteq2^{<\mathbb N}\), decidable in \(\varnothing'\), such that
\[
\sum_{w\in B}\lambda(w)<\infty,
\tag{30}
\]
and
\[
\forall k\ \exists\alpha\in P:
\alpha\text{ has at least }k\text{ prefixes in }B,
\tag{31}
\]
but
\[
\forall\alpha\in P:
\alpha\text{ has only finitely many prefixes in }B.
\tag{32}
\]

**Proof confidence: high.**

### Proof

The class \(P\) has no isolated points. An isolated point of an effectively closed class is computable: after an isolating prefix, one can find the correct next child by waiting for the other child’s cylinder to be covered by the enumerated complement. This would contradict \(P\subseteq\operatorname{MLR}(\lambda)\).

Choose \(\beta\in P\) computable in \(\varnothing'\), for example its leftmost path. Extendibility through \(P\) is decidable in \(\varnothing'\): emptiness of \(P\cap[x]\) has a finite-cover certificate.

Along \(\beta\), choose increasing splitting depths \(n_k\ge k^2\). Let \(\tau_k\) be the sibling prefix departing from \(\beta\) at the \(k\)-th chosen split. Then
\[
P\cap[\tau_k]\ne\varnothing,
\]
and the \(\tau_k\) are pairwise incompatible.

Mark the next \(k\) levels below \(\tau_k\):
\[
B=
\{w:\exists k,\ \tau_k\prec w,\ |w|\le|\tau_k|+k\}.
\]
Every path entering \([\tau_k]\) has exactly \(k\) marked prefixes. No path enters two such cylinders. This proves (31)–(32).

At each marked level below \(\tau_k\), total cylinder weight is \(\lambda(\tau_k)\). Hence
\[
\sum_{w\in B}\lambda(w)
=
\sum_k k\lambda(\tau_k)
\le\sum_k k2^{-k^2}<\infty.
\]
The construction and membership test are computable in \(\varnothing'\). ∎

This is an abstract edge-label countermodel, **not** a claim that \(B\) is realized as the bad edges of a universal semimeasure. It identifies the invalid compactness inference: the sets “at least \(k\) visits somewhere” are open relative to \(P\), rather than closed. Their witnesses can move into incompatible cylinders and accumulate on a path with no visits.

## The precise missing step

For an admissible array, \(\varnothing'\) can already:

- compute every final integer \(a(x)\);
- decide whether an edge is permanently \(\varepsilon\)-bad;
- decide whether its cylinder meets \(P\).

Thus the oracle is sufficient to find a next compatible bad extension **if one exists**.

A sufficient extension principle would be the following: for some fixed \(\sigma,\varepsilon>0\) and nonempty effectively closed \(F\subseteq P\),
\[
\begin{gathered}
\forall u\ \forall N,\quad F\cap[u]\ne\varnothing\\
\Longrightarrow
\exists v\succeq u,\ b,\quad
|v|\ge N,\quad F\cap[vb]\ne\varnothing,
\end{gathered}
\]
with the edge \(\sigma v\to\sigma vb\) permanently \(\varepsilon\)-bad.

Under that hypothesis, a \(\varnothing'\)-construction chooses longer compatible bad extensions successively, and their union lies in \(F\) and witnesses GO. The proof is immediate from the three decision procedures above.

**I cannot derive that persistence principle—or another principle ensuring one infinite compatible chain—from universal dominance.** The finite change count, the finite expected-error budget, and arbitrarily long finite visit chains do not supply it.

Accordingly, the remaining unresolved assertion is still the full
\[
\boxed{\mathsf{GO}(P).}
\]
The audit validates the reduction; the results above establish its counting limitations, a broader negative subclass, and a positive oracle construction whose exact failure is lower semicomputability.