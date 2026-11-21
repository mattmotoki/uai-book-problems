# The counterexample does lift to all computable measures—with a qualification about the priors

**For unrestricted positive priors over the class of all computable probability measures, the answer is yes.** Below I prove that your particular computable \(\mu\) admits two such universal mixtures satisfying
\[
\boxed{
\frac{1}{32}H_n
\;\le\;
L_n^{\xi_-}-L_n^{\xi_+}
\;\le\;
\frac{1}{16}H_n,
\qquad
H_n=\sum_{t=1}^n\frac1t.
}
\]
Their priors agree on every model except \(\mu,\nu\), where the weights are exactly swapped. Moreover, their entire prior functions are within a factor of three of each other.

**This proof does not establish the result for two Solomonoff priors, or for priors both uniformly comparable to a fixed \(2^{-K(\rho)}\).** The construction uses a noneffective enumeration of all computable measures. That distinction is substantive.

The proposed justification that the rest’s posterior weight should disappear is false. The successful construction instead makes the rest’s conditional predictions exactly controlled on a set of histories whose probability is uniformly large.

## Results and proof status

| Claim | Result | Status and confidence |
|---|---|---|
| The rest’s posterior weight vanishes under your \(\mu\) | Generally false; an equivalent computable model such as the fair-coin measure retains positive posterior weight almost surely | Proved below; high confidence |
| Adding an arbitrarily small common background preserves the finite counterexample | False without further control; one additional computable product measure can make the loss difference finite | Proved below; high confidence |
| Two full-support mixtures over **all computable probability measures** can have divergent loss difference | Yes, with the explicit harmonic bounds above | Proved below; high confidence; not Lean-checked |
| The two priors can agree except for exactly swapped \(\mu,\nu\) weights | Yes; their weight ratios are \(3,1/3,1\) | Included in the proof |
| The same conclusion holds for Solomonoff priors or fixed complexity-comparable priors | Not established here | Unresolved by this answer |
| Fixed positive decision margins, logarithmic loss, or squared loss give finite differences | Yes, under domination of \(\mu\) | Established theory, with derivations below |

Throughout, \(L_n^Q\) denotes **cumulative expected loss under \(\mu\)**. Thus the question concerns the sequence \(L_n^Q-L_n^{Q'}\), rather than subtracting two infinite total losses.

---

## 1. Why the rest need not disappear

Write
\[
\delta_t=\frac1{32t},\qquad
\mu(X_t=1)=\frac12+\delta_t,\qquad
\nu(X_t=1)=\frac12-\delta_t,
\]
and let \(\lambda\) be the fair-coin measure.

### 1.1 These models are equivalent as measures on infinite sequences

The relevant feature is
\[
\sum_t\delta_t^2<\infty.
\]
For example, the finite-prefix likelihood ratios satisfy
\[
\mathbb E_\lambda
 \left[\left(\frac{\mu(X_{1:n})}{\lambda(X_{1:n})}\right)^2\right]
=
\prod_{t=1}^n(1+4\delta_t^2),
\]
and
\[
\mathbb E_\mu
 \left[\left(\frac{\lambda(X_{1:n})}{\mu(X_{1:n})}\right)^2\right]
=
\prod_{t=1}^n\frac1{1-4\delta_t^2}.
\]
Both products are uniformly bounded. Consequently the likelihood-ratio martingales are uniformly integrable in both directions, giving
\[
\mu\sim\lambda.
\]
The analogous calculation gives \(\nu\sim\mu\).

Thus the observations do not almost surely identify which of these equivalent measures generated the sequence.

### 1.2 An equivalent alternative retains positive posterior weight

Let \(\Xi\) be a probability mixture containing \(\mu\) and \(\lambda\) with positive weights \(w_\mu,w_\lambda\). Its posterior weight on \(\lambda\) is
\[
\pi_{\lambda,n}
=
\frac{w_\lambda\lambda(X_{1:n})}{\Xi(X_{1:n})}
=
w_\lambda
\frac{\lambda(X_{1:n})/\mu(X_{1:n})}
     {\Xi(X_{1:n})/\mu(X_{1:n})}.
\]

Under \(\mu\):

- The numerator converges to a finite, strictly positive limit, by equivalence.
- The denominator is a nonnegative martingale, bounded below by \(w_\mu>0\), and converges to a finite limit.

Therefore
\[
\boxed{\pi_{\lambda,n}\longrightarrow\pi_{\lambda,\infty}>0
\quad\mu\text{-almost surely}.}
\]

A universal mixture over all computable measures contains \(\lambda\). If the “rest” excludes only \(\mu,\nu\), its posterior weight therefore cannot tend to zero.

The same argument works for a mixture of enumerable semimeasures containing these measure components: the denominator is then a nonnegative **supermartingale**.

This also answers the Martin-Löf-randomness intuition. Since \(\mu\) is computable, its Martin-Löf-random sequences have \(\mu\)-measure one; the nonconcentration above occurs on a full-measure subset of those sequences. Randomness does not force identification of a unique equivalent model.

### 1.3 Even a very small common background can remove the divergence

Here is a concrete obstruction to simply adding an arbitrary small rest.

For any fixed \(0<\varepsilon<1\), let \(q\) be the computable product measure
\[
q(X_t=1)=\frac12+\beta_t,
\qquad
\beta_t=\frac1{8t^{3/4}},
\]
and define
\[
\widetilde\xi_-=(1-\varepsilon)
 \left(\frac14\mu+\frac34\nu\right)+\varepsilon q,
\]
\[
\widetilde\xi_+=(1-\varepsilon)
 \left(\frac34\mu+\frac14\nu\right)+\varepsilon q.
\]

Then
\[
\boxed{
\sup_n\left(L_n^{\widetilde\xi_-}-L_n^{\widetilde\xi_+}\right)<\infty.
}
\]

**Proof.** The two decision scores remain ordered, so disagreement can only mean that \(\widetilde\xi_-\) predicts \(0\) and \(\widetilde\xi_+\) predicts \(1\). For the minus predictor to predict \(0\), necessarily
\[
\varepsilon\beta_t q(h)
\le
\frac34(1-\varepsilon)\delta_t\nu(h).
\]
Hence, for a constant \(A_\varepsilon\),
\[
\Pr_\mu(\text{disagreement at }t)
\le
A_\varepsilon\frac{\delta_t}{\beta_t}
\mathbb E_\mu\frac{\nu(X_{<t})}{q(X_{<t})}.
\]
Independence gives
\[
\mathbb E_\mu\frac{\nu(X_{<t})}{q(X_{<t})}
=
\prod_{s<t}\frac{1-4\delta_s^2}{1-4\beta_s^2}.
\]
This is uniformly bounded because \(\sum_s\beta_s^2<\infty\). A disagreement costs \(2\delta_t\), so
\[
\sum_t 2\delta_t\Pr_\mu(\text{disagreement at }t)
\le
A'_\varepsilon\sum_t\frac{\delta_t^2}{\beta_t}
=
A''_\varepsilon\sum_t t^{-5/4}<\infty.
\]
This proves the assertion.

This example is not itself universal. It proves that **small prior mass and predictive merging alone do not justify the proposed lift**.

More precisely, with a common background \(B\), a sufficient condition on histories where
\[
\frac12\le\frac{\nu(h)}{\mu(h)}\le2
\]
is
\[
\frac{\varepsilon\,|B(h1)-B(h0)|}{\mu(h)}
<
\frac{1-\varepsilon}{4}\delta_t.
\]
This makes the common directional contribution small enough to preserve the opposite decisions. The required scale is \(1/t\), which ordinary convergence to zero does not supply.

---

## 2. A counterexample universal over all computable probability measures

### Theorem

Let \(\mathcal C\) be the class of all computable probability measures on \(\{0,1\}^{\mathbb N}\), where computability means uniform computability of cylinder probabilities.

For the particular \(\mu,\nu\) above, there exist priors
\[
w_-,w_+:\mathcal C\to(0,1),
\qquad
\sum_{\rho\in\mathcal C}w_\pm(\rho)=1,
\]
such that:

1. Their distinguished weights are
   \[
   w_-(\mu)=\frac{15}{64},\qquad
   w_-(\nu)=\frac{45}{64},
   \]
   \[
   w_+(\mu)=\frac{45}{64},\qquad
   w_+(\nu)=\frac{15}{64}.
   \]

2. For every \(\rho\notin\{\mu,\nu\}\),
   \[
   w_-(\rho)=w_+(\rho)>0.
   \]

3. The mixtures
   \[
   \xi_\pm(h)=\sum_{\rho\in\mathcal C}w_\pm(\rho)\rho(h)
   \]
   therefore dominate every computable probability measure:
   \[
   \xi_\pm(h)\ge w_\pm(\rho)\rho(h)
   \quad\text{for every }\rho,h.
   \]

4. For binary \(0\)-\(1\) loss and a common deterministic tie convention,
   \[
   \frac{H_n}{32}
   \le L_n^{\xi_-}-L_n^{\xi_+}
   \le\frac{H_n}{16}
   \quad(n\ge1).
   \]

In particular, the difference is \(\Theta(\log n)\).

The priors also satisfy
\[
\frac13 w_-(\rho)\le w_+(\rho)\le3w_-(\rho)
\]
for every \(\rho\), and consequently
\[
\frac13\xi_-(h)\le\xi_+(h)\le3\xi_-(h).
\]

**Proof status:** complete ordinary mathematical proof below; high confidence. No Lean verification of this extension has been performed.

### 2.1 Construct measures that imitate \(\mu\) until a rare trigger

Choose an enumeration
\[
\mathcal C\setminus\{\mu,\nu\}=\{q_0,q_1,\ldots\}.
\]
This enumeration is **not asserted to be effective**.

Set
\[
K_i=2^{i+6}+1,\qquad
a_i=2^{-i-1},\qquad
c_i=\frac1{3K_i}.
\]

For each \(i\), define
\[
Z_i(h)=\frac{q_i(h)}{\mu(h)}.
\]
Since \(q_i\) is computable and \(\mu(h)\) is a positive rational, there is a computable rational approximation \(r_i(h)\) satisfying
\[
|r_i(h)-Z_i(h)|\le\frac12.
\]

Declare \(h\) a **trigger** when
\[
r_i(h)>K_i.
\]
This predicate is decidable. Using a rational approximation matters: exact comparison of a computable real with a rational need not be decidable.

Define \(\tau_i\) to follow \(\mu\) through the first trigger and then follow \(q_i\) conditioned on that prefix. Explicitly,
\[
\tau_i(h)=
\begin{cases}
\mu(h),&\text{if no prefix of }h\text{ triggers},\\[4pt]
\displaystyle \mu(z)\frac{q_i(h)}{q_i(z)},
&\text{if }z\preceq h\text{ is the first trigger}.
\end{cases}
\]

At a first trigger \(z\), the second expression equals \(\mu(z)\). In particular, if no trigger has occurred through a history \(h\), then
\[
\tau_i(hb)=\mu(hb),\qquad b\in\{0,1\},
\]
even if the child \(hb\) itself triggers.

This proves cylinder consistency before the switch; consistency afterward follows from \(q_i\). Thus \(\tau_i\) is a probability measure.

It is also computable. Computing its value at \(h\) requires finitely many rational comparisons. Any denominator \(q_i(z)\) occurs at a trigger, where
\[
q_i(z)>\left(K_i-\frac12\right)\mu(z)>0.
\]

### 2.2 Each switched measure contains a positive amount of its original model

Every conditional bit probability of \(\mu\) lies in
\[
\left[\frac{15}{32},\frac{17}{32}\right].
\]

Before a trigger,
\[
Z_i(h)\le K_i+\frac12.
\]
At the first trigger \(z=hb\), therefore,
\[
Z_i(z)
\le\frac{32}{15}Z_i(h)
\le\frac{32}{15}\left(K_i+\frac12\right)
<3K_i.
\]
The first inequality uses \(q_i(hb)\le q_i(h)\).

For any extension \(x\succeq z\),
\[
\tau_i(x)
=
\frac{q_i(x)}{Z_i(z)}
\ge\frac{q_i(x)}{3K_i}.
\]
The same bound holds before the trigger. Consequently,
\[
\boxed{\tau_i(x)\ge c_iq_i(x)\quad\text{for all }x.}
\]

Define the residual
\[
\sigma_i
=
\frac{\tau_i-c_iq_i}{1-c_i}.
\]
Its cylinder values are nonnegative, additive, normalized, and computable. Hence \(\sigma_i\) is a computable probability measure, and
\[
\tau_i=c_iq_i+(1-c_i)\sigma_i.
\]

Now put
\[
B=\sum_{i=0}^\infty a_i\tau_i
=
\sum_{i=0}^\infty
a_i\bigl(c_iq_i+(1-c_i)\sigma_i\bigr).
\]
Because \(\sum_i a_i=1\), this is a probability mixture. Every \(q_i\) appears with positive weight \(a_ic_i\).

### 2.3 The common rest can exclude \(\mu,\nu\) exactly

We need this additional detail to make the *total* \(\mu,\nu\) weights exactly swapped.

First, \(\sigma_i\ne\mu\). If \(\sigma_i=\mu\), then
\[
\tau_i=(1-c_i)\mu+c_iq_i.
\]
At any first trigger \(z\), the equality \(\tau_i(z)=\mu(z)\) would force
\[
q_i(z)=\mu(z),
\]
contradicting \(Z_i(z)>K_i-\frac12>1\). If there are no triggers anywhere, then \(\tau_i=\mu\), and the same mixture identity forces \(q_i=\mu\), which was excluded.

Second, \(\sigma_i\ne\nu\). The switched measure has
\[
\tau_i(1)=\mu(1)=\frac{17}{32}.
\]
Therefore
\[
\sigma_i(1)
=
\frac{17/32-c_iq_i(1)}{1-c_i}
\ge
\frac{17/32-c_i}{1-c_i}
>
\frac{15}{32}
=
\nu(1),
\]
where the strict inequality follows from \(c_i<2/17\).

Thus, after aggregating duplicate models in its displayed expansion, \(B\) is a mixture over exactly
\[
\mathcal C\setminus\{\mu,\nu\},
\]
with positive weight on every member and no \(\mu,\nu\) atoms in that prior representation.

Finally, define
\[
\boxed{
\xi_-=\frac{15}{64}\mu+\frac{45}{64}\nu+\frac1{16}B,
\qquad
\xi_+=\frac{45}{64}\mu+\frac{15}{64}\nu+\frac1{16}B.
}
\]
These have all the claimed prior and universality properties.

### 2.4 With uniformly high probability, the rest predicts exactly as \(\mu\)

Fix a finite horizon \(m\). For each \(i\), the first-trigger strings of length at most \(m\) form a finite prefix-free set \(A_{i,m}\).

For every \(z\in A_{i,m}\),
\[
q_i(z)>\left(K_i-\frac12\right)\mu(z).
\]
Since a probability measure assigns total cylinder mass at most one to a prefix-free set,
\[
\Pr_\mu(\text{rule }i\text{ triggers by }m)
=
\sum_{z\in A_{i,m}}\mu(z)
\le\frac1{K_i-\frac12}.
\]

Let \(E_m\) be the event that none of the rules has triggered through time \(m\). A countable union bound gives
\[
\Pr_\mu(E_m^c)
\le
\sum_{i=0}^\infty\frac1{K_i-\frac12}
\le
\sum_{i=0}^\infty 2^{-i-6}
=
\frac1{32}.
\]

On a history \(h\in E_m\), \(|h|=m\), every component satisfies
\[
\tau_i(h)=\mu(h),\qquad
\tau_i(hb)=\mu(hb).
\]
Hence
\[
\boxed{
B(h)=\mu(h),\qquad B(hb)=\mu(hb)\quad(b=0,1).
}
\]

The background’s posterior mass remains present. Its conditional contribution is exactly known on these histories.

### 2.5 The likelihood-ratio interval still has large probability

Set
\[
R_m=\frac{\nu(X_{1:m})}{\mu(X_{1:m})}.
\]
Then \(\mathbb E_\mu R_m=1\), and independence gives
\[
\begin{aligned}
\mathbb E_\mu R_m^2
&=
\prod_{t=1}^m
\left(1+\frac{16\delta_t^2}{1-4\delta_t^2}\right)\\
&=
\prod_{t=1}^m
\left(1+\frac4{256t^2-1}\right)\\
&\le
\exp\left(\frac4{255}\sum_{t=1}^m\frac1{t^2}\right)\\
&\le e^{8/255}
\le\frac{255}{247}.
\end{aligned}
\]
Here we used \(\sum_{t\ge1}t^{-2}\le2\) and \(e^x\le(1-x)^{-1}\) for \(0\le x<1\).

Thus
\[
\mathbb E_\mu(R_m-1)^2\le\frac8{247}.
\]
Chebyshev gives
\[
\Pr_\mu\left(R_m\notin[1/2,2]\right)
\le\frac{32}{247}.
\]
Consequently,
\[
\Pr_\mu\left(E_m\cap\{1/2\le R_m\le2\}\right)
\ge
1-\frac1{32}-\frac{32}{247}
>
\frac12.
\]

No independence between these two events is needed.

### 2.6 The decisions separate, and other histories cannot cancel the gain

For a measure \(Q\), define its signed decision score
\[
S_Q(h)=Q(h1)-Q(h0).
\]
Choose action \(1\) when \(S_Q(h)\ge0\), and action \(0\) otherwise.

At time \(t=m+1\), on the event above,
\[
S_{\xi_-}(h)
=
\frac{2\delta_t\mu(h)}{64}(19-45R_m),
\]
\[
S_{\xi_+}(h)
=
\frac{2\delta_t\mu(h)}{64}(49-15R_m).
\]
For \(R_m\in[1/2,2]\), the first expression is strictly negative and the second strictly positive. Thus the minus mixture predicts \(0\), and the plus mixture predicts \(1\).

At **every** history, including histories outside this event,
\[
S_{\xi_+}(h)-S_{\xi_-}(h)
=
\frac{15}{16}\delta_t\bigl(\mu(h)+\nu(h)\bigr)>0.
\]
Therefore the plus predictor never chooses \(0\) when the minus predictor chooses \(1\).

Under \(\mu\), predicting \(0\) instead of \(1\) costs
\[
\mu(1\mid h)-\mu(0\mid h)=2\delta_t.
\]
The conditional expected loss difference is consequently always nonnegative, is at most \(2\delta_t\), and equals \(2\delta_t\) on an event of probability greater than \(1/2\).

Writing \(\Delta_n=L_n^{\xi_-}-L_n^{\xi_+}\), we obtain
\[
\frac1{32t}
\le
\Delta_t-\Delta_{t-1}
\le
\frac1{16t}.
\]
Summing proves
\[
\boxed{\frac{H_n}{32}\le\Delta_n\le\frac{H_n}{16}.}
\qquad\square
\]

This lies outside the finite-oracle-loss case:
\[
L_n^\mu=\frac n2-\frac{H_n}{32}\longrightarrow\infty.
\]

The theorem is about expected loss. It does not assert that the realized difference between the two error counts tends to \(+\infty\) on individual sample paths.

---

## 3. What this establishes about universality—and what remains unresolved

The theorem covers the **entire class of computable probability measures**. It is not restricted to a selected countable family of product measures. It also shows that uniformly comparable priors, and even priors differing at only two models, do not ensure finite cumulative \(0\)-\(1\) loss differences.

The remaining distinction is effectiveness.

In the standard enumerable-semimeasure formulation, universal mixtures use an effective enumeration of enumerable semimeasures and a lower-semicomputable positive weight function. Wood, Sunehag, and Hutter show that this class agrees with Solomonoff priors, subject to the empty-string convention; universally dominant enumerable semimeasures form a strictly larger class. See **arXiv:1111.3854**, especially Definition 8 and the equivalence results. [arxiv.org](https://arxiv.org/html/1111.3854v1?utm_source=chatgpt.com)

The construction above does not provide that effectiveness:

1. **The enumeration of all computable probability measures is noneffective.** Each listed measure has its own algorithm, but the list is not a uniformly computable enumeration of total measure algorithms.

2. **The residual construction uses subtraction.** For computable \(q_i,\tau_i\), the residual \(\sigma_i\) is computable. For merely lower-semicomputable semimeasures, the corresponding subtraction need not be lower semicomputable.

3. **Mutual prior comparability is different from complexity comparability.** We proved
   \[
   w_+\asymp w_-.
   \]
   We did not prove
   \[
   w_\pm(\rho)\asymp2^{-K(\rho)}
   \]
   uniformly over \(\rho\).

Accordingly, I have not proved either a counterexample or a finite-difference theorem for two universal machines \(U,V\) with your fixed \(\mu\). The same qualification applies to the specified complexity-weighted regime.

The precise remaining constructive target is an **effective** universal background whose signed child-mass contribution is sufficiently controlled on the \(1/t\) scale on a substantial set of histories. The noneffective switching construction supplies that control for computable-measure mixtures.

---

## 4. Regimes where the difference is finite

These positive results need only domination of the true measure, so they apply to universal predictors whenever the relevant loss and margin assumptions hold.

Let \(Q\) be a probability measure satisfying
\[
Q(h)\ge c\,\mu(h)\qquad\text{for every }h,
\]
and put
\[
B_Q=\log(1/c).
\]
Write \(p_t=\mu(\cdot\mid X_{<t})\), \(q_t=Q(\cdot\mid X_{<t})\). The chain rule gives the finite KL budget
\[
\sum_{t=1}^\infty
\mathbb E_\mu D_{\mathrm{KL}}(p_t\Vert q_t)
\le B_Q.
\]
This is the standard dominance-based prediction bound; Hutter develops it in **arXiv:cs/0301014**, DOI **10.1109/TIT.2003.814488**. [hutter1.net](https://www.hutter1.net/ai/spupper.pdf?utm_source=chatgpt.com)

Here are explicit consequences.

### 4.1 A uniform positive decision margin

Suppose
\[
|2p_t(1)-1|\ge\gamma>0
\]
almost surely, at every time. Let \(a_t^*\) be the true Bayes action and \(a_t^Q\) the action selected by \(Q\).

If they disagree, then
\[
|p_t(1)-q_t(1)|
\ge\frac{|2p_t(1)-1|}{2}.
\]
Pinsker’s inequality gives
\[
D_{\mathrm{KL}}(p_t\Vert q_t)
\ge
\frac{|2p_t(1)-1|^2}{2}.
\]
The conditional excess loss is
\[
r_t^Q
=
|2p_t(1)-1|\,
\mathbf1_{\{a_t^Q\ne a_t^*\}}.
\]
Therefore
\[
r_t^Q
\le
\frac2\gamma D_{\mathrm{KL}}(p_t\Vert q_t),
\]
and
\[
\mathbf1_{\{a_t^Q\ne a_t^*\}}
\le
\frac2{\gamma^2}D_{\mathrm{KL}}(p_t\Vert q_t).
\]

Summing,
\[
\boxed{
0\le L_n^Q-L_n^\mu\le\frac{2B_Q}{\gamma},
}
\]
and
\[
\boxed{
\mathbb E_\mu\#\{t:a_t^Q\ne a_t^*\}
\le\frac{2B_Q}{\gamma^2}.
}
\]

For two dominating predictors \(Q,Q'\), both expected regrets are nondecreasing and bounded. Their difference therefore converges to a finite real number. More strongly, the increments are absolutely summable:
\[
\sum_t
\left|
\mathbb E_\mu\ell_t^Q-\mathbb E_\mu\ell_t^{Q'}
\right|
\le
\frac2\gamma(B_Q+B_{Q'}).
\]

The two predictors also disagree in only finitely many actions almost surely, so their **realized** cumulative loss difference eventually becomes constant.

This goes beyond finite oracle loss. For example, computable iid Bernoulli \(p=0.6\) has
\[
L_n^\mu=0.4n,
\]
yet all dominating Bayes predictors have finite expected regret.

The margin phenomenon is already in Hutter’s 2003 JMLR paper, and Leike’s thesis gives an explicit KL-over-margin bound in Theorem 3.48. The derivation above makes the constants and pairwise consequences explicit. [jmlr.org](https://www.jmlr.org/papers/volume4/hutter03a/hutter03a.pdf?utm_source=chatgpt.com)

For a varying positive margin \(m_t=|2p_t(1)-1|\), the same argument gives
\[
r_t^Q\le\frac{2}{m_t}D_{\mathrm{KL}}(p_t\Vert q_t).
\]
Thus
\[
\sum_t\mathbb E_\mu
\frac{D_{\mathrm{KL}}(p_t\Vert q_t)}{m_t}<\infty
\]
is a sufficient condition. Summable unweighted KL alone does not imply this when \(m_t\to0\).

### 4.2 General finite-action losses with an action gap

For losses \(\ell(x,a)\in[0,1]\), suppose the true Bayes action is unique and every other action has conditional excess risk at least \(\gamma>0\).

If \(a_Q\) minimizes \(q\)-risk and \(a^*\) minimizes \(p\)-risk, then
\[
r
=
p\cdot(\ell_{a_Q}-\ell_{a^*})
\le\|p-q\|_1.
\]
Pinsker implies
\[
D_{\mathrm{KL}}(p\Vert q)\ge r^2/2.
\]
On a suboptimal action, \(r\ge\gamma\), hence
\[
r\le\frac2\gamma D_{\mathrm{KL}}(p\Vert q).
\]
The same finite-regret and pairwise-convergence conclusions follow.

**Status:** proved by the displayed argument; high confidence.

### 4.3 Logarithmic loss

For probability forecasts scored by log loss,
\[
L_n^Q-L_n^\mu
=
D_{\mathrm{KL}}(\mu_{1:n}\Vert Q_{1:n})
\in[0,B_Q].
\]
These regrets are nondecreasing and bounded. Therefore
\[
\boxed{
L_n^Q-L_n^{Q'}\text{ converges to a finite limit},
}
\]
with
\[
-B_{Q'}\le L_n^Q-L_n^{Q'}\le B_Q.
\]

There is also a pathwise identity:
\[
\sum_{t\le n}
\bigl[-\log q_t(X_t)+\log q_t'(X_t)\bigr]
=
\log\frac{Q'(X_{1:n})}{Q(X_{1:n})}.
\]
Under domination, both likelihood ratios relative to \(\mu\) are nonnegative supermartingales bounded below by positive constants. Their finite positive limits imply convergence of this realized log-loss difference as well.

Hutter explicitly states the finite expected log-loss regret bound in the cited prediction paper. [hutter1.net](https://www.hutter1.net/ai/spupper.pdf?utm_source=chatgpt.com)

### 4.4 Squared loss

For binary outcomes, with probability forecast \(q\) and loss
\[
\ell(x,q)=(x-q)^2,
\]
the conditional excess loss is exactly
\[
(p-q)^2
\le\frac12D_{\mathrm{KL}}(\operatorname{Ber}(p)\Vert\operatorname{Ber}(q)).
\]
Thus
\[
\boxed{
0\le L_n^Q-L_n^\mu\le\frac12B_Q.
}
\]
Again, the difference between any two dominating predictors’ cumulative expected losses converges finitely.

More generally, the same conclusion holds for any scoring rule whose conditional regret is bounded above by a fixed constant times KL divergence.

### 4.5 Deterministic \(\mu\), and semimeasure normalization

For deterministic \(\mu\), every mistaken binary Bayes prediction assigns probability at most \(1/2\) to the correct bit. Hence
\[
\#\text{mistakes}\le\frac{B_Q}{\log2}.
\]
This is the finite-oracle-loss case mentioned in your question.

For a semimeasure \(\rho\), use normalized next-symbol probabilities
\[
q(b\mid h)=\frac{\rho(hb)}{\rho(h0)+\rho(h1)}.
\]
The associated probability measure \(Q\) satisfies
\[
Q(h)\ge\frac{\rho(h)}{\rho(\epsilon)}.
\]
This follows inductively from the semimeasure inequality. Normalization preserves Bayes action rankings, so the margin conclusions apply to semimeasure-based decisions as well.

---

## 5. Relation to prior work

### Merging does not imply summable classification-loss differences

Blackwell–Dubins shows that absolute continuity implies merging of conditional future distributions in total variation. Since each constructed mixture contains \(\mu\) with positive weight, both merge to \(\mu\), and therefore to each other. The theorem is compatible with the counterexample: convergence of probabilities does not force convergence of their thresholded decisions when the true probability approaches \(1/2\). See Blackwell and Dubins, **“Merging of Opinions with Increasing Information”**, DOI **[10.1214/aoms/1177704456](https://doi.org/10.1214/aoms/1177704456)**; a precise formulation is also given in Leike’s Theorem 3.25. [jan.leike.name](https://jan.leike.name/publications/Nonparametric%20General%20Reinforcement%20Learning%20-%20Leike%202016.pdf?utm_source=chatgpt.com)

The related merging literature includes:

- **Kalai and Lehrer (1994), “Weak and strong merging of opinions.”** DOI **[10.1016/0304-4068(94)90037-X](https://doi.org/10.1016/0304-4068(94)90037-X)**. This develops several notions of predictive agreement. [sciencedirect.com](https://www.sciencedirect.com/science/article/pii/030440689490037X?utm_source=chatgpt.com)
- **Lehrer and Smorodinsky (1996), “Compatible Measures and Merging.”** DOI **[10.1287/moor.21.3.697](https://doi.org/10.1287/moor.21.3.697)**. It studies weaker merging conditions, including settings without absolute continuity. [Mathematics of Operations Research](https://pubsonline.informs.org/doi/10.1287/moor.21.3.697?utm_source=chatgpt.com)

For the present question, the elementary “difference of regrets” identity is
\[
L_n^\xi-L_n^{\xi'}
=
\bigl(L_n^\xi-L_n^\mu\bigr)
-
\bigl(L_n^{\xi'}-L_n^\mu\bigr).
\]
It yields finite limits when both regrets are finite, as in the positive regimes above. Bounds allowing both regrets to diverge do not establish boundedness of their difference.

### The basic finite-class mechanism has a published antecedent

Hutter’s **“Optimality of Universal Bayesian Sequence Prediction for General Loss and Alphabet,” arXiv:[cs/0311014](https://arxiv.org/abs/cs/0311014)**, discusses on printed p. 988 a horizon-independent two-model class with nonstationary probabilities \(1/2\pm\varepsilon_t\) and divergent regret against the true-model predictor. The same discussion identifies logarithmic loss, quadratic loss, and separation from the classification boundary as finite-regret regimes. That is an antecedent of the finite-class mechanism; it does not supply the full-support universal-mixture construction proved here. [jmlr.org](https://www.jmlr.org/papers/volume4/hutter03a/hutter03a.pdf?utm_source=chatgpt.com)

For a broader account connecting dominance, merging, and decision regret, see Leike, **“Nonparametric General Reinforcement Learning,” arXiv:[1611.08944](https://arxiv.org/abs/1611.08944)**, Chapter 3. [jan.leike.name](https://jan.leike.name/publications/Nonparametric%20General%20Reinforcement%20Learning%20-%20Leike%202016.pdf?utm_source=chatgpt.com)

Recent work directly relevant to the randomness intuition is Huttegger, Walsh, and Zaffora Blando, **“Algorithmic randomness and the weak merging of computable probability measures,” arXiv:[2504.00440](https://arxiv.org/abs/2504.00440)**, revised March 2026. It characterizes randomness through weak merging and summable KL; it does not identify predictive merging with posterior concentration on a unique equivalent model. [arxiv.org](https://arxiv.org/abs/2504.00440?utm_source=chatgpt.com)

### Search status

I did not locate a published direct resolution of the two-Solomonoff-prior loss-comparison question in the searches for Problem 3.3, two-mixture loss differences, and differences of regrets. As checked on **20 November 2026**, Hutter’s official page still lists Problem 3.3 and its €50 prize without a solution annotation. This supports a qualified search-status statement, not a claim that no resolution exists or that the construction above is necessarily new. [hutter1.net](https://www.hutter1.net/ai/uaibook.htm?utm_source=chatgpt.com)

---

## 6. Lean formalization plan

The main counterexample can be formalized using **finite histories throughout**. An infinite sample-space construction, almost-sure convergence, and Blackwell–Dubins are unnecessary for the harmonic lower bound.

The existing finite definitions you describe provide most of the loss-comparison layer. The new work divides naturally into an abstract countable-mixture theorem and a computability construction.

### 6.1 First prove an abstract background lemma

Generalize `Prior` and `mixCond` from finite sums to a summable countable prior. For nonnegative weights summing to one, define cylinder masses by
\[
\xi(h)=\sum_i w_i\rho_i(h).
\]
Establish normalization, cylinder consistency, and componentwise domination.

Then prove a lemma with these hypotheses on a background measure \(B\):

- For each history length \(m\), there is a set \(E_m\) with
  \[
  \mu(E_m^c)\le1/32.
  \]
- On \(E_m\),
  \[
  B(hb)=\mu(hb)\qquad(b=0,1).
  \]

Together with the existing likelihood-ratio moment estimate, this lemma should derive
\[
H_n/32\le L_n^{\xi_-}-L_n^{\xi_+}\le H_n/16.
\]

Its main ingredients are finite sums over histories, Chebyshev, rational inequalities, and the monotonicity of the Bayes action in the signed child-mass score.

### 6.2 Then construct the universal background

The additional proof obligations are:

| Component | Required statement |
|---|---|
| Rational approximation | For each computable cylinder measure \(q\), obtain a computable rational approximation to \(q(h)/\mu(h)\) with error at most \(1/2\) |
| First-trigger operation | Search the finite list of prefixes using a decidable rational predicate |
| Switched measure | Prove normalization, cylinder additivity, and computability of \(\tau_i\) |
| Domination | Prove \(\tau_i(h)\ge q_i(h)/(3K_i)\) |
| Residual measure | Prove \((\tau_i-c_iq_i)/(1-c_i)\) is a computable probability measure |
| Exact prior support | Prove the residual is neither \(\mu\) nor \(\nu\), then aggregate duplicate models |
| Trigger probability | Bound the finite prefix-free first-trigger set by \(1/(K_i-1/2)\) |
| Countable union | Obtain the total bad-history bound \(1/32\) |
| Final growth | Combine the per-time loss bound with harmonic divergence |

The prefix-free trigger argument is particularly convenient: it avoids introducing stopping-time and martingale infrastructure solely for this theorem.

### 6.3 Keep the computability statements at the cylinder level

There are two important interface points.

First, use the library’s notion of **computable cylinder probabilities**. A computable measure can have zero-probability histories; a total computable conditional-probability function with an arbitrary convention at all such histories is an additional requirement. The switched cylinder formula avoids that issue. All mixture histories relevant here have positive mass because \(\mu\) has full support.

Second, the enumeration of all computable measures should be a classical, noneffective object. Lean can prove an existential theorem using that enumeration without claiming an executable universal prior. The global prior’s effectiveness must remain separate from the computability of each component.

The repository’s documented Solomonoff development includes computable-measure indices and the universal prediction framework, so it provides the relevant representation layer. The switching and residual closure lemmas are the main new obligations; an existing universal-semimeasure existence theorem does not by itself establish them. [GitHub](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean/blob/main/KolmogorovMathlib.lean?utm_source=chatgpt.com)

**The appropriate first formal target is the exact theorem in Section 2:** all computable probability measures, unrestricted positive priors, exactly swapped \(\mu,\nu\) weights, and the explicit \(H_n/32\) lower bound. The machine-specific and complexity-weighted versions require an additional mathematical construction before they become Lean proof tasks.