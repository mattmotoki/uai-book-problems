# Problem 3.3 for classes of computable probability measures

**Restricting the model class to probability measures still gives a negative answer.** The \(n^{1/4}\) counterexample extends to mixtures over **all computable probability measures**, with positive normalized priors whose coordinatewise ratios lie in \([1/3,3]\). Both priors can also be comparable to the same fixed complexity prior.

There is a further extension to **exact \(2^{-K}\) weights under two constructed optimal reference machines**. The distinction between complexity of a model’s *index* and shortest-description complexity of a *distinct measure* matters; I give precise versions for both.

The complete report is available here:

:chatgpt-content-reference{index="5"}[027-p33-measure-class.a.md](sandbox:/workspace/scratch/8bd14e93ae4a/027-p33-measure-class.a.md)

The proofs follow below. “New” means developed in this answer, without a claim of publication priority. **The new extensions have not been Lean-checked in this task.** Confidence and the remaining formalization targets are stated at the end.

## 1. Conventions and the finite robustness lemma

Write \(\epsilon\) for the empty word. A probability measure satisfies
\[
\nu(\epsilon)=1,\qquad \nu(h)=\nu(h0)+\nu(h1).
\]
A semimeasure has root at most one and the corresponding inequalities.

Use ties toward zero:
\[
a_s(h)=\mathbf 1\{s(h1)>s(h0)\}.
\]
For semimeasures this is the Bayes action for the locally normalized forecast
\[
q_s(1\mid h)=\frac{s(h1)}{s(h0)+s(h1)}.
\]
All denominators used below are positive. A common tie convention toward one also works.

Define
\[
L_n^s=\mathbb E_\mu\sum_{t=1}^n
\mathbf 1\{a_s(X_{<t})\ne X_t\},
\qquad
\Delta_n=L_n^{s_-}-L_n^{s_+}.
\]
We discuss finite-horizon differences and their limits; this avoids an undefined subtraction of two infinite losses.

The standard external ingredient is the dominance-to-KL bound and its squared prediction-error consequence. Hutter’s sequence-prediction paper gives these in its dominance inequality, equation (8), and Theorem 1. The argument needed here is included below. [hutter1.net](https://www.hutter1.net/ai/spupper.pdf?utm_source=chatgpt.com)

### Lemma 1 — finite robustness, suitable for Lean

Let \(N\ge1\), \(\gamma>0\), and
\[
N\gamma^2=\frac1{1024}.
\]
Let \(\alpha,\beta\) generate independent bits with probabilities \(1/2+\gamma\) and \(1/2-\gamma\) for their first \(N\) positions, and fair bits thereafter.

For every
\[
a\in[1/5,1/4],\qquad 0\le\eta\le2^{-20},
\]
and every root-one semimeasure \(A\), put
\[
\pi_-=a\alpha+(1-a)\beta,\qquad
\pi_+=(1-a)\alpha+a\beta,
\]
\[
s_\pm=(1-\eta)\pi_\pm+\eta A.
\]
Under the true measure \(\alpha\),
\[
\boxed{\gamma N\le L_N^{s_-}-L_N^{s_+}\le2\gamma N.}
\]
Every one-step conditional expected loss difference is nonnegative.

For \(\gamma=1/(32\sqrt N)\), these bounds are \(\sqrt N/32\) and \(\sqrt N/16\).

This includes both the \(1:3\) cores of report 008 and the \(1:4\) cores needed below. **Restricting \(A\) to probability measures requires no change.**

#### Proof

**Likelihood-ratio control.** For \(m\le N\), let
\[
R_m=\frac{\beta(X_{1:m})}{\alpha(X_{1:m})}.
\]
Independence gives
\[
\mathbb E_\alpha R_m=1,\qquad
\mathbb E_\alpha R_m^2=(1+b)^m,\qquad
b=\frac{16\gamma^2}{1-4\gamma^2}.
\]
Since \(\gamma\le1/32\),
\[
Nb\le\frac4{255}.
\]
The elementary inequality
\[
(1+b)^m\le\frac1{1-mb}\qquad(mb<1)
\]
follows by induction: its induction step reduces to
\[
(1+b)(1-(m+1)b)\le1-mb.
\]
Consequently,
\[
\mathbb E_\alpha R_m^2\le\frac{255}{251},
\]
and
\[
\Pr_\alpha\{R_m\notin[1/2,2]\}
\le4\,\mathbb E_\alpha(R_m-1)^2
\le\frac{16}{251}<\frac14.
\]

Call \(R_{t-1}\in[1/2,2]\) the good event. On it,
\[
q_{\pi_-}
=\frac12+\gamma\frac{a-(1-a)R}{a+(1-a)R}
\le\frac12-\frac\gamma5,
\]
\[
q_{\pi_+}
=\frac12+\gamma\frac{(1-a)-aR}{(1-a)+aR}
\ge\frac12+\frac\gamma5.
\]
The worst margin over the specified ranges is
\[
\gamma\frac{1-3a}{1+a}\ge\frac\gamma5.
\]

**Contamination budget.** Let \(\bar s_\pm\) be sequential normalization of \(s_\pm\). Induction down the tree gives
\[
\bar s_\pm(h)\ge s_\pm(h)\ge(1-\eta)\pi_\pm(h),
\]
using \(s(h0)+s(h1)\le s(h)\). Therefore
\[
D(\pi_{\pm,1:N}\Vert\bar s_{\pm,1:N})
\le\log\frac1{1-\eta}.
\]
The chain rule and binary inequality \(d(p\Vert q)\ge2(p-q)^2\) imply
\[
\sum_{t=1}^N\mathbb E_{\pi_\pm}
(q_{s_\pm}-q_{\pi_\pm})^2
\le\frac12\log\frac1{1-\eta}.
\]
The binary inequality follows, for example, because the second derivative of \(d(p\Vert q)\) in \(p\) is \(1/[p(1-p)]\ge4\), while its value and first derivative vanish at \(p=q\).

Both cores dominate \(\alpha/5\). Thus their combined squared perturbation budget under \(\alpha\) is at most
\[
B:=5\log\frac1{1-\eta}\le10\eta.
\]
Destroying a good disagreement requires at least one forecast to move by \(\gamma/5\). The expected number destroyed is therefore at most
\[
\frac{25B}{\gamma^2}
\le\frac{250\eta}{\gamma^2}
\le\frac{125}{512}N.
\]
There are at least \(3N/4\) good times in expectation, leaving at least
\[
\left(\frac34-\frac{125}{512}\right)N
=\frac{259}{512}N>\frac N2
\]
intended disagreements.

**No negative contributions.** At every history within the experiment,
\[
\begin{aligned}
&[s_+(h1)-s_+(h0)]-[s_-(h1)-s_-(h0)]\\
&\quad=2(1-2a)(1-\eta)\gamma
[\alpha(h)+\beta(h)]>0.
\end{aligned}
\]
Hence \(a_{s_+}(h)\ge a_{s_-}(h)\). Each disagreement costs exactly \(2\gamma\) under \(\alpha\). This proves both bounds and nonnegativity. \(\square\)

### A smaller finite abstraction

For Lean, the counting step can be isolated from information theory.

Suppose the true next-bit probability is \(1/2+\gamma\), actual actions satisfy \(a_+\ge a_-\), the expected good-history count is at least \(G\), and on good histories
\[
q_{\mathrm{core},-}\le\frac12-\frac\gamma5,\qquad
q_{\mathrm{core},+}\ge\frac12+\frac\gamma5.
\]
If the combined squared perturbation budget is at most \(B\), then
\[
\boxed{
2\gamma\left(G-\frac{25B}{\gamma^2}\right)
\le\Delta_N\le2\gamma N.
}
\]
This is a finite indicator-and-sum argument. Lemma 1 uses \(G=3N/4\) and \(B=10\eta\).

## 2. Counterexamples over all computable probability measures

### Theorem 2 — positive priors, ratio three, and the original rate

Let \(\mathcal C\) be either:

- all computable binary probability measures; or
- all computable binary probability measures with rational conditionals at positive-mass histories.

There exists one computable rational-conditional source \(\mu\), independent of the prior, with the following property.

For **every** strictly positive prior \(a_\nu\) on \(\mathcal C\) with
\(\sum_\nu a_\nu=1\), and **every** \(0<\eta\le2^{-20}\), there are normalized strictly positive priors \(w^-,w^+\) on the same class satisfying
\[
\frac13\le\frac{w_\nu^+}{w_\nu^-}\le3
\]
and
\[
\boxed{
\frac{n^{1/4}}{256}
\le L_n^{\xi_-}-L_n^{\xi_+}
\le\frac{11}{112}n^{1/4}
<\frac{n^{1/4}}8,\qquad n\ge2.
}
\]
The differences are nondecreasing.

More generally, this holds for any countable class of computable measures containing \(\mu\) and closed under the transformations below.

**Status: new extension of report 008.**

#### Proof

**The source.** Set
\[
z_j=1^j0,\quad p_j=2^{-j-1},\quad
N_j=16^j,\quad \gamma_j=\frac1{32\cdot4^j}.
\]
Let \(\kappa_j^\pm\) generate \(N_j\) independent bits of bias \(1/2\pm\gamma_j\), then fair bits.

The source generates fair bits until the first zero; if that zero follows \(j\) ones, it follows \(\kappa_j^+\). Thus
\[
\mu(1^k)=2^{-k},\qquad
\mu(z_jh)=p_j\kappa_j^+(h).
\]
Its cylinder probabilities and positive-history conditionals are computable rationals.

**Transform each background component.** For every \(\nu\in\mathcal C\), define \(T_\pm\nu\) as follows:

1. Copy \(\nu\)’s selector probabilities.
2. After selecting \(j\), run the corresponding \(N_j\)-bit experiment.
3. Restart an independent copy of \(\nu\) afterward.

Writing \(b_j^\pm\) for the finite Bernoulli law through length \(N_j\),
\[
(T_\pm\nu)(1^k)=\nu(1^k),
\]
\[
(T_\pm\nu)(z_jh)=\nu(z_j)b_j^\pm(h)
\quad(|h|\le N_j),
\]
\[
(T_\pm\nu)(z_juv)
=\nu(z_j)b_j^\pm(u)\nu(v)
\quad(|u|=N_j).
\]

These formulas define probability measures: additivity at selector nodes comes from \(\nu\), inside an experiment from the Bernoulli law, and afterward from the restarted copy. They are uniform computable transformations and preserve rational conditionals.

Each \(T_\pm\) is injective. Equality of transformed measures gives equality of selector masses. If all selector masses vanish, both originals are the point mass on \(1^\infty\). Otherwise choose a positive-mass selector \(z_j\) and a word \(u\) of length \(N_j\). Then
\[
\nu(v)=
\frac{(T_\pm\nu)(z_juv)}{(T_\pm\nu)(z_ju)}.
\]
This recovers the original measure.

**The mixtures.** Put
\[
B=\sum_\nu a_\nu\nu,\qquad
P=\sum_\nu a_\nu T_+\nu,\qquad
Q=\sum_\nu a_\nu T_-\nu,
\]
and
\[
\xi_-=\eta B+(1-\eta)(P/4+3Q/4),
\]
\[
\xi_+=\eta B+(1-\eta)(3P/4+Q/4).
\]
All are probability measures.

To exhibit the actual priors on \(\mathcal C\), define
\[
A_\pm(\rho)=\sum_{\nu:T_\pm\nu=\rho}a_\nu.
\]
Then
\[
w_\rho^-=\eta a_\rho+
\frac{1-\eta}{4}[A_+(\rho)+3A_-(\rho)],
\]
\[
w_\rho^+=\eta a_\rho+
\frac{1-\eta}{4}[3A_+(\rho)+A_-(\rho)].
\]
They are positive, sum to one, and satisfy
\[
w_\rho^-/3\le w_\rho^+\le3w_\rho^-.
\]

**The aggregate \(P,Q\) need not be computable. Every constituent in their displayed expansions is computable and belongs to \(\mathcal C\).** Thus these are mixtures over the required class.

**Conditional contamination.** The key identities are
\[
P(1^k)=Q(1^k)=B(1^k),\qquad
P(z_j)=Q(z_j)=B(z_j)>0.
\]
Through the first \(N_j\) positions after \(z_j\), division by \(B(z_j)\) gives exactly Lemma 1’s finite mixtures with
\[
A_j(h)=\frac{B(z_jh)}{B(z_j)},\qquad a=\frac14.
\]
Here \(A_j\) is a probability measure, and the contamination is **exactly \(\eta\) in every branch**.

Let \(D_j(m)\) denote the expected gap during the first \(m\le N_j\) experimental positions. Then
\[
D_j(m)\ge0,\qquad
D_j(N_j)\ge\gamma_jN_j=\frac{4^j}{32},\qquad
D_j(m)\le2\gamma_jm,
\]
and \(D_j\) is nondecreasing.

Before selection, the predictors agree. After the experiment, the true source is fair, so both predictors have conditional expected loss \(1/2\), even if their actions differ. Hence
\[
\Delta_n=\sum_{j\ge0}p_jD_j(m_j(n)),
\qquad
m_j(n)=\min\{16^j,(n-j-1)_+\}.
\]

**Aggregation.** Each completed branch contributes at least
\[
p_jD_j(N_j)\ge\frac{2^j}{64}.
\]
For \(n\ge2\), let \(J\) be the largest integer with \(2\cdot16^J\le n\). Since \(j+1\le16^j\), all branches \(j\le J\) are complete. Therefore
\[
\Delta_n\ge\frac1{64}\sum_{j=0}^J2^j
\ge\frac{2^J}{64}\ge\frac{n^{1/4}}{256}.
\]

Conversely,
\[
\Delta_n\le\frac1{32}\sum_{j\ge0}8^{-j}\min(16^j,n).
\]
Splitting at \(K=\lfloor\log_{16}n\rfloor\), the part through \(K\) is at most \(2n^{1/4}\), and the tail at most \((8/7)n^{1/4}\), before multiplication by \(1/32\). Thus
\[
\Delta_n\le\frac1{32}\left(2+\frac87\right)n^{1/4}
=\frac{11}{112}n^{1/4}.
\]
This proves the theorem. \(\square\)

### What this says about robustness

**The finite robustness theorem carries over unchanged.** The infinite construction also works for every background mixture and every \(0<\eta\le2^{-20}\), because it transforms each background component.

It does not require two fixed computable foreground models to work against every background. A small global background weight can become large after conditioning on a rare selector. Matching selector masses prevents that problem.

No effective exhaustive enumeration of all total computable measures, semantic equality algorithm, or computability of the aggregate prior is assumed.

## 3. Both priors comparable to one fixed complexity prior

### Corollary 3 — semantic complexity comparability

Fix any optimal prefix description system for computable measures, and define
\[
K(\nu)=\min\{|p|:p\text{ describes a program computing }\nu\},
\]
minimizing over all valid descriptions of the same **extensional measure**.

For either class in Theorem 2, the priors can be chosen so that
\[
w_\nu^-\asymp2^{-K(\nu)},\qquad
w_\nu^+\asymp2^{-K(\nu)}
\]
uniformly in \(\nu\), while retaining the ratio-three bound and the same rate.

#### Proof

Choose one shortest description for each distinct measure. These programs are prefix-free, so
\[
0<Z:=\sum_{\nu\in\mathcal C}2^{-K(\nu)}\le1.
\]
Use
\[
a_\nu=\frac{2^{-K(\nu)}}Z
\]
in Theorem 2.

The transformations have fixed forward compiler overheads:
\[
K(T_\pm\nu)\le K(\nu)+c_\pm.
\]
Because each transformation is injective, each pushforward weight has at most one summand. Therefore
\[
A_\pm(\rho)\le2^{c_\pm}a_\rho.
\]
The formulas for \(w^\pm\) now bound each prior below by \(\eta a_\rho\) and above by a fixed constant times \(a_\rho\). \(\square\)

The restart after the experiment supplies the needed injectivity. This avoids assuming an unjustified coding theorem for aggregated descriptions of infinite objects.

## 4. Exact \(2^{-K}\) weights under two optimal machines

Report 008 used complexity of an integer model index. Leike–Hutter explicitly uses that convention as well. Minimizing over all names of a distinct measure is a different convention, so it deserves its own theorem. [hutter1.net](https://www.hutter1.net/publ/aixiprior.pdf?utm_source=chatgpt.com)

### Theorem 4 — exact priors on distinct models

Let \(\mathcal C\) be either all computable probability measures or all lower-semicomputable semimeasures, viewed as distinct extensional models. Fix an optimal prefix description machine \(V\).

There is a fixed computable rational-conditional source \(\mu_*\), independent of \(V\), such that two optimal prefix machines \(U_-,U_+\) can be constructed with
\[
\Xi_\pm=\sum_{\rho\in\mathcal C}2^{-K_{U_\pm}(\rho)}\rho
\]
and
\[
\boxed{
\frac{n^{1/4}}{512}
\le L_n^{\Xi_-}-L_n^{\Xi_+}
<\frac{n^{1/4}}8,\qquad n\ge3.
}
\]
Every coordinatewise weight ratio belongs to \(\{1/4,1,4\}\). Both priors are comparable to the fixed \(2^{-K_V(\rho)}\) prior.

For distinct lsc semimeasures, this is a mathematical statement about the semantic mixture; **uniform lower semicomputability of that quotient mixture is not asserted**. An effective indexed version follows in Section 5.

**Status: new.**

#### Proof

### 4.1 A transformation with a uniform inverse

Retain \(z_j,p_j,N_j,\gamma_j,\kappa_j^\pm\) from Section 2. Define
\[
\begin{aligned}
(F_\pm\nu)(\epsilon)&=\frac{\nu(\epsilon)+1}{2},\\
(F_\pm\nu)(0h)&=\frac{\nu(h)}2,\\
(F_\pm\nu)(1^{k+1})
&=\frac{\nu(1^{k+1})+(\nu(0)+1)2^{-k}}4,\\
(F_\pm\nu)(1z_jh)
&=\frac{\nu(1z_j)+(\nu(0)+1)p_j}{4}\,
\kappa_j^\pm(h).
\end{aligned}
\tag{F}
\]
These cases cover every finite string.

For a semimeasure, at the root,
\[
F\nu(0)+F\nu(1)
\le\frac{3\nu(\epsilon)+1}{4}
\le\frac{\nu(\epsilon)+1}{2}
=F\nu(\epsilon)\le1.
\]
At header nodes, use the inequality for \(\nu\) and
\(2^{-k-1}+p_k=2^{-k}\). The zero subtree inherits the inequalities of \(\nu\); experimental subtrees use additivity of \(\kappa_j^\pm\).

For probability measures all these inequalities become equalities, with
\[
F\nu(\epsilon)=1,\qquad F\nu(0)=F\nu(1)=1/2.
\]
The formulas preserve computability, rational conditionals, and lower semicomputability in their respective classes.

There is a uniform inverse on either image:
\[
\nu(h)=2(F_\pm\nu)(0h).
\]
Thus both transformations are injective. Their images are disjoint: equality would imply the same original \(\nu\), but branch \(10\) has mass at least \(1/8\), and its first experimental next-bit probabilities have opposite biases.

### 4.2 The description representation

Use prefix descriptions of cylinder-computation programs, or lower-approximation programs for semimeasures.

The transformations can be implemented so that **validity is reflected**: a valid transformed description implies a valid original description. The zero subtree copies the entire original name by exact scaling. It therefore recovers totality, approximation accuracy, nonnegativity, and the tree equalities or inequalities. The root formula enforces the original normalization or root bound.

For example, if a cylinder name returns \(r(h,m)\) with required error at most \(2^{-m}\), set the transformed output at \((0h,m+1)\) exactly to \(r(h,m)/2\). Validity of the transformed name forces the original error bound.

This matters: invalid source programs must not create extra valid transformed models with unexpectedly short descriptions.

### 4.3 Exact shortest lengths

The inverse compiler gives a constant \(d\) such that
\[
K_V(\nu)\le K_V(F_\pm\nu)+d.
\]
Choose
\[
L\ge\max\{24,d+5\},\qquad \varepsilon=2^{-L}.
\]

Use the following prefix dispatch, with the remaining input interpreted by \(V\):

| Prefix | \(U_-\) operation | \(U_+\) operation |
| --- | --- | --- |
| \(0100\) | Apply \(F_+\) | Apply \(F_-\) |
| \(00\) | Apply \(F_-\) | Apply \(F_+\) |
| \(1^L\) | Keep the model unchanged | Keep the model unchanged |

These prefixes are prefix-free. The unchanged simulation branch makes both machines optimal.

Injectivity, disjointness, and validity reflection account for all possible descriptions. An unchanged simulation of \(F_\pm\nu\) has length at least
\[
L+K_V(F_\pm\nu)
\ge L+K_V(\nu)-d
>4+K_V(\nu).
\]
It therefore cannot beat either short branch. The shortest lengths are exactly:

| Model | \(K_{U_-}\) | \(K_{U_+}\) |
| --- | --- | --- |
| \(F_+\nu\) | \(4+K_V(\nu)\) | \(2+K_V(\nu)\) |
| \(F_-\nu\) | \(2+K_V(\nu)\) | \(4+K_V(\nu)\) |
| \(\rho\) outside both images | \(L+K_V(\rho)\) | \(L+K_V(\rho)\) |

### 4.4 The exact mixture and its conditional background

Put
\[
a_\nu=2^{-K_V(\nu)},\qquad S=\sum_\nu a_\nu\in(0,1],
\]
\[
B=\sum_\nu a_\nu\nu,\quad
P=\sum_\nu a_\nu F_+\nu,\quad
Q=\sum_\nu a_\nu F_-\nu,
\]
and
\[
R=\sum_{\rho\notin\operatorname{im}F_+\cup\operatorname{im}F_-}
a_\rho\rho.
\]
Then \(R\le B\) pointwise, and the exact shortest-length table gives
\[
\boxed{
\Xi_-=\frac1{16}P+\frac14Q+\varepsilon R,\qquad
\Xi_+=\frac14P+\frac1{16}Q+\varepsilon R.
}
\tag{E}
\]

Their core selector masses agree:
\[
r_j:=P(1z_j)=Q(1z_j)
=\frac{B(1z_j)+(B(0)+S)p_j}{4}>0.
\]
Also,
\[
R(1z_j)\le B(1z_j)\le4r_j.
\]
Thus, conditional on \(1z_j\), the common background fraction is
\[
\eta_j=
\frac{\varepsilon R(1z_j)}
{(5/16)r_j+\varepsilon R(1z_j)}
\le\frac{64}{5}\varepsilon
\le2^{-20}.
\]
A zero background branch simply has \(\eta_j=0\).

The normalized cores are
\[
(\kappa_j^++4\kappa_j^-)/5,\qquad
(4\kappa_j^++\kappa_j^-)/5,
\]
so Lemma 1 applies with \(a=1/5\).

### 4.5 The source and rate

Let \(\mu_*\) output one initial bit \(1\), then run the source \(\mu\) from Section 2. Its selector \(1z_j\) has probability \(p_j\).

The two predictors agree on the initial bit and selector bits: the transformed core measures agree there, and their total coefficients agree. After each finite experiment, both core suffixes are fair, leaving the same background signed score for both predictors.

The aggregation is therefore Section 2’s calculation shifted by one time step:
\[
\frac{(n-1)^{1/4}}{256}
\le L_n^{\Xi_-}-L_n^{\Xi_+}
\le\frac{11}{112}(n-1)^{1/4}
\quad(n\ge3).
\]
This implies the stated bounds.

The exact weight ratios are \(4,1/4,1\). For comparison with the base prior, the unchanged branch supplies the lower bound \(\varepsilon a_\rho\). A **forward** compiler bound
\[
K_V(F_\pm\nu)\le K_V(\nu)+c
\]
gives
\[
a_\nu\le2^c a_{F_\pm\nu},
\]
and hence the required constant upper bound. \(\square\)

### Normalization and “exact”

Exact complexity weights generally sum to at most one. The two systems above have the same total weight
\[
(5/16)S+
\varepsilon\sum_{\rho\notin\operatorname{im}F_+\cup\operatorname{im}F_-}a_\rho.
\]

For probability models, the raw mixture is an additive subprobability measure. Dividing by this common positive constant produces a probability measure and leaves all conditional predictions and losses unchanged.

The weights **before this optional normalization** are exactly \(2^{-K_{U_\pm}}\). Requiring both literal powers \(2^{-K}\) and prior sum exactly one would impose an additional convention.

## 5. Exact effective indexed priors over all lsc semimeasures

### Theorem 5 — the convention of report 008

There are an effective enumeration \((\rho_i)\) of all lsc semimeasures and two optimal prefix machines \(C_-,C_+\) describing integer indices such that
\[
\Xi_\pm=\sum_i2^{-K_{C_\pm}(i)}\rho_i
\]
are lower-semicomputable universal mixtures, have indexwise prior ratios in \(\{1/4,1,4\}\), and satisfy
\[
\frac{n^{1/4}}{512}
\le L_n^{\Xi_-}-L_n^{\Xi_+}
<\frac{n^{1/4}}8
\quad(n\ge3)
\]
under the same computable \(\mu_*\).

#### Proof

Start with any effective exhaustive enumeration \((\sigma_i)\) of lsc semimeasures. Using \(F_\pm\), recursively define
\[
\rho_{3i}=\sigma_i,\qquad
\rho_{3i+1}=F_+\rho_i,\qquad
\rho_{3i+2}=F_-\rho_i.
\]
The recursion terminates because each non-base case uses a smaller index. The enumeration is effective and exhaustive.

The name transformations
\[
f_+(i)=3i+1,\qquad f_-(i)=3i+2
\]
are injective, have disjoint ranges, and have the computable inverse
\(\lfloor k/3\rfloor\).

Take an optimal machine \(V\) for natural numbers. Use the same dispatch construction, now outputting \(f_+(V(p))\), \(f_-(V(p))\), or \(V(p)\). The inverse on integers supplies the constant \(d\), and the same minimum-length calculation applies.

Identity (E) follows with
\[
B=\sum_i2^{-K_V(i)}\rho_i,\qquad
R=\sum_{i\equiv0\pmod3}2^{-K_V(i)}\rho_i.
\]
The conditional-background and rate arguments are unchanged.

Every weight \(2^{-K_{C_\pm}(i)}\) is positive and uniformly lower semicomputable. Since the model enumeration is effective, both mixtures are lower semicomputable. Each dominates every listed semimeasure by its positive weight. \(\square\)

Repeated semantic names are retained. Aggregating their weights gives a prior on distinct semimeasures, but those aggregated weights need not be single powers \(2^{-K(\nu)}\).

**Report 008’s Theorem 6 is valid under its stated index convention.** The new work above supplies a measure-only result and a separate semantic result. The conventional effective universal-mixture definition and its relationship to Solomonoff priors do not identify index weights with semantic shortest-description weights. [arxiv.org](https://arxiv.org/html/1111.3854v1?utm_source=chatgpt.com)

## 6. Readings under which the answer is positive

### Proposition 6 — log loss

Let \(\xi,\xi'\) be normalized probability mixtures containing \(\mu\) with weights \(w_\mu,w'_\mu>0\). Their expected cumulative conditional log-loss difference converges to a finite real number.

#### Proof

By the chain rule,
\[
D_n(\mu\Vert\xi)
=\mathbb E_\mu\log\frac{\mu(X_{1:n})}{\xi(X_{1:n})}
\]
is nondecreasing. Dominance gives
\[
0\le D_n(\mu\Vert\xi)\le\log\frac1{w_\mu}.
\]
The corresponding sequence for \(\xi'\) is also nondecreasing and bounded. Both converge finitely.

Telescoping conditional log probabilities gives
\[
L_{n,\log}^{\xi}-L_{n,\log}^{\xi'}
=D_n(\mu\Vert\xi)-D_n(\mu\Vert\xi').
\]
Thus the difference converges, with
\[
-\log\frac1{w'_\mu}
\le L_{n,\log}^{\xi}-L_{n,\log}^{\xi'}
\le\log\frac1{w_\mu}.
\]

If additionally \(c\le w'_\nu/w_\nu\le C\), then
\[
\log c\le
L_{n,\log}^{\xi}-L_{n,\log}^{\xi'}
=\mathbb E_\mu\log\frac{\xi'(X_{1:n})}{\xi(X_{1:n})}
\le\log C.
\]
For nonnormalized additive mixtures, include the root normalization factors. \(\square\)

### Proposition 7 — a uniform classification margin

Suppose there is \(\delta>0\) such that, at every positive-\(\mu\) history, either \(p=\mu(1\mid h)=1/2\), or
\[
|2p-1|\ge\delta.
\]
Then any normalized probability mixture \(\xi\) containing \(\mu\) with positive weight has total 0–1 regret at most
\[
\frac2\delta\log\frac1{w_\mu}.
\]
Consequently, two such predictors have a cumulative expected loss difference that converges finitely.

#### Proof

Put \(q=\xi(1\mid h)\) and \(d=|p-1/2|\). A wrong Bayes action costs \(2d\) and requires \(|p-q|\ge d\). At nonties, \(d\ge\delta/2\), so
\[
2d\,\mathbf1_{\{\text{wrong action}\}}
\le\frac4\delta(p-q)^2.
\]
At true ties the regret is zero. The KL/Pinsker bound gives
\[
\sum_t\mathbb E_\mu(p_t-q_t)^2
\le\frac12\log\frac1{w_\mu}.
\]
Each cumulative regret is therefore nonnegative, nondecreasing, and bounded. Subtracting two such regrets proves the claim. \(\square\)

Deterministic sources are included. Our counterexamples use experiments with positive margins tending to zero.

**Quadratic loss also has a positive answer without a margin assumption.** For loss \((X_t-q_t)^2\), conditional excess loss over \(q_t=p_t\) is exactly \((p_t-q_t)^2\). Its expected sum is finite by the same bound, so the difference of two cumulative quadratic-loss regrets converges finitely.

### Same machine and bounded factors

If the model class, naming, reference machine, exact complexity formula, and tie rule are identical, the predictors are identical. Multiplying all prior weights by one common constant also leaves predictions identical.

Merely being comparable to the same complexity prior does **not** suffice, by Corollary 3. Changing the reference machine does not suffice, by Theorems 4–5.

Nor does moving the prior toward the truth generally suffice. The supplied finite-class example satisfies
\[
\xi_+=\frac13\xi_-+\frac23\mu
\]
and still has its divergent 0–1 loss gap.

## 7. Confidence and what remains to check

| Result | Confidence and status | Main Lean target |
| --- | --- | --- |
| Finite robustness for probability backgrounds | High; full proof | Likelihood-ratio second moment, KL budget, threshold counting |
| \(\Theta(n^{1/4})\) over all computable measures | High; new full proof | Componentwise transforms and branch aggregation |
| Comparability to any fixed semantic complexity prior | High; new full proof | Injectivity and the forward compiler inequality |
| Exact semantic \(2^{-K}\) priors | High; new full proof | Description representation, validity reflection, exact shortest-length table |
| Exact effective indexed lsc mixtures | High; full construction | Recursive naming and inverse compiler |
| Positive log-loss, quadratic-loss, and margin results | High; full proofs | Standard chain rule and summability |

The most useful formalization sequence is:

1. Prove the finite threshold-counting abstraction.
2. Establish Lemma 1 for both core ratios through its single parameter range.
3. Formalize the \(T_\pm\) measure transformations and geometric aggregation.
4. Formalize the \(F_\pm\) inverse, disjoint images, validity reflection, and exact prefix-code minima.

These constructions answer the mathematical formulations stated here. No new Lean kernel verification or external prize adjudication is claimed. Hutter’s public page lists Problem 3.3 as “Comparing two mixtures”; that listing does not establish whether these particular constructions have received external review. [hutter1.net](https://www.hutter1.net/ai/uaibook.htm?utm_source=chatgpt.com)