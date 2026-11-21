# An effective counterexample, including Solomonoff priors

**Yes. The existential statement in your follow-up has a counterexample with effective universal priors.** A different construction gives a single computable source \(\mu\) and two universal mixtures, with positive **computable** weights whose coordinatewise ratios lie in \([1/3,3]\), such that
\[
\boxed{
\frac{n^{1/4}}{256}
\;\le\;
L_n^{\xi_-}-L_n^{\xi_+}
\;\le\;
\frac{n^{1/4}}8
\qquad(n\ge2).
}
\]

The construction also yields:

- Two actual Solomonoff priors with this divergent loss difference.
- Two priors both uniformly comparable to the same fixed \(2^{-K(i)}\) prior.
- Two exact shortest-description mixtures, for two chosen optimal prefix machines.
- A same-machine example \(M_U\) versus \(\xi_U=\sum_i2^{-K_U(i)}\rho_i\), under the explicit shared-machine convention specified below.

**The source changes.** It is a computable process that randomly selects one finite experiment, then produces fair bits afterward. This answer does **not** establish the effective result for the particular independent-bit source \(1/2+1/(32t)\) from question 007.

All the new results below have complete mathematical proofs and have received independent proof-level checks. My confidence is high, but **these extensions have not been Lean-checked**. “New” here means developed in this answer; I am not claiming established publication priority.

## Conventions

Fix an effective, acceptable enumeration \((\rho_i)_{i\in\mathbb N}\) of all lower-semicomputable binary semimeasures. Repeated names are allowed.

For a positive semimeasure \(s\), define its Bayes \(0\)-\(1\) action by
\[
a_s(h)=
\begin{cases}
1,&s(h1)\ge s(h0),\\
0,&s(h1)<s(h0).
\end{cases}
\]
This is also the Bayes action of the locally normalized forecast
\[
q_s(1\mid h)=\frac{s(h1)}{s(h0)+s(h1)}.
\]

Thus the results apply both to normalized prediction and to Bayes decisions obtained from the raw semimeasure. Thresholding \(s(h1)/s(h)\) at \(1/2\) would be a different rule when the semimeasure has a defect.

Throughout,
\[
L_n^s
=
\mathbb E_\mu\sum_{t=1}^n
\mathbf1\{a_s(X_{<t})\ne X_t\}.
\]

For complexity priors, \(K(i)\) means prefix complexity of the **model index**. This is an explicit convention in Leike–Hutter’s treatment of universal mixtures. A quotient over distinct extensional semimeasures would require separate naming and effectivity conventions. [hutter1.net](https://www.hutter1.net/publ/aixiprior.pdf?utm_source=chatgpt.com)

---

# 1. What fails in the previous effectivization route

The old switching construction remains a valid noneffective construction over computable probability measures. Its direct replacement by enumerable semimeasures fails at several specific points.

### Proposition 1: A universal common rest cannot have vanishing posterior weight

Let \(B,\mu,\nu\) be semimeasures with
\[
B(h)\ge c_\mu\mu(h),\qquad B(h)\ge c_\nu\nu(h)
\]
for positive constants \(c_\mu,c_\nu\). For \(a,b\ge0\), \(\varepsilon>0\), put
\[
\xi=a\mu+b\nu+\varepsilon B.
\]
Then, whenever \(B(h)>0\),
\[
\boxed{
\frac{\varepsilon B(h)}{\xi(h)}
\ge
\frac{\varepsilon}
     {a/c_\mu+b/c_\nu+\varepsilon}>0.
}
\]

**Proof.** Substitute \(\mu(h)\le B(h)/c_\mu\) and \(\nu(h)\le B(h)/c_\nu\) into the denominator. \(\square\)

An effective universal rest dominates both computable measures. Consequently, posterior disappearance is unavailable even as an asymptotic argument: its posterior fraction has a positive lower bound uniformly over histories.

### Proposition 2: The old residual formula generally fails for semimeasures

Let \(\tau\) be a probability measure, let \(\rho\) be a semimeasure with positive defect at some history, and let \(0<c<1\). Even if
\[
\sigma=\frac{\tau-c\rho}{1-c}
\]
is pointwise nonnegative, it is not a semimeasure at that history.

**Proof.** Its defect is
\[
\sigma(h)-\sigma(h0)-\sigma(h1)
=
-\frac{c}{1-c}
\bigl[\rho(h)-\rho(h0)-\rho(h1)\bigr]<0.
\]
\(\square\)

There are additional effectiveness problems:

- The old proof selected a noneffective list of total computable measures.
- Its stopping rule used two-sided approximations to cylinder probabilities. Lower semicomputability alone does not provide them.
- Subtracting one lower-semicomputable function from another need not preserve lower semicomputability.
- Separating semantic measures \(\mu,\nu\) from every equivalent program name is not an effective operation.

Normalization does not fix these issues. For example, take a noncomputable left-c.e. real \(\alpha\in(1/4,1/2)\) and an enumerable semimeasure with child masses
\[
s(0)=1/4,\qquad s(1)=\alpha.
\]
Its normalized probability of zero is
\[
\frac{1/4}{1/4+\alpha}.
\]
This is right-c.e. and noncomputable, hence not left-c.e. Thus normalized predictions need not remain lower semicomputable.

**Status:** these are proved obstructions to the previous proof route, not impossibility results for effective counterexamples. The construction below avoids each of them.

---

# 2. A finite experiment robust to an arbitrary semimeasure background

This lemma is the quantitative core of the new construction.

### Theorem 3: Uniform finite-experiment lower bound

Let \(N\ge1\) be a square and set
\[
\gamma=\frac1{32\sqrt N}.
\]
Let \(\mu_N,\nu_N\) generate independent bits with probabilities
\[
\mu_N(1\mid h)=\frac12+\gamma,\qquad
\nu_N(1\mid h)=\frac12-\gamma
\]
during their first \(N\) positions, and fair bits afterward.

Define
\[
\pi_-=\frac14\mu_N+\frac34\nu_N,\qquad
\pi_+=\frac34\mu_N+\frac14\nu_N.
\]

For **every** semimeasure \(A\) with \(A(\epsilon)=1\), and every \(0\le\eta\le2^{-20}\), put
\[
s_-=(1-\eta)\pi_-+\eta A,\qquad
s_+=(1-\eta)\pi_++\eta A.
\]
Then, under \(\mu_N\),
\[
\boxed{
\frac{\sqrt N}{32}
\le
L_N^{s_-}-L_N^{s_+}
\le
\frac{\sqrt N}{16}.
}
\]
Moreover, every per-step expected loss difference is nonnegative.

**Status:** proved here; high confidence.

## Proof

### Step 1: The finite core has a decision margin on most histories

Let
\[
R_m=\frac{\nu_N(X_{1:m})}{\mu_N(X_{1:m})}.
\]
For \(m\le N\),
\[
\mathbb E_{\mu_N}R_m=1
\]
and
\[
\begin{aligned}
\mathbb E_{\mu_N}R_m^2
&=
\left(1+\frac{16\gamma^2}{1-4\gamma^2}\right)^m\\
&\le
\exp\left(\frac{16N\gamma^2}{1-4\gamma^2}\right)
\le e^{4/255}
\le\frac{255}{251}.
\end{aligned}
\]
Here \(N\gamma^2=1/1024\). Therefore
\[
\Pr_{\mu_N}\{R_m\notin[1/2,2]\}
\le4\operatorname{Var}(R_m)
\le\frac{16}{251}<\frac14.
\]

On \(R_{t-1}\in[1/2,2]\), the core forecasts satisfy
\[
q_{\pi_-}(1\mid h)
=
\frac12+\gamma\frac{1-3R_{t-1}}{1+3R_{t-1}}
\le\frac12-\frac{\gamma}{5},
\]
and
\[
q_{\pi_+}(1\mid h)
=
\frac12+\gamma\frac{3-R_{t-1}}{3+R_{t-1}}
\ge\frac12+\frac{\gamma}{5}.
\]

Call these histories good. The cores make opposite decisions on good histories, with margins at least \(\gamma/5\).

### Step 2: Small contamination has a finite prediction-error budget

Let \(\bar s_\pm\) be the probability measures obtained by sequentially normalizing \(s_\pm\). The semimeasure inequality gives
\[
\bar s_\pm(h)\ge s_\pm(h)\ge(1-\eta)\pi_\pm(h).
\]
The KL chain rule and binary Pinsker inequality imply
\[
\sum_{t=1}^N
\mathbb E_{\pi_\pm}
\bigl(q_{s_\pm}(1\mid X_{<t})
-q_{\pi_\pm}(1\mid X_{<t})\bigr)^2
\le\frac12\log\frac1{1-\eta}.
\]

This is the standard dominance-to-summed-prediction-error argument; Hutter’s **arXiv:cs/0301014**, DOI **10.1109/TIT.2003.814488**, supplies the underlying KL framework. [hutter1.net](https://www.hutter1.net/ai/spupper.pdf?utm_source=chatgpt.com)

Since \(\pi_\pm(h)\ge\mu_N(h)/4\), changing the history distribution yields
\[
\sum_{t=1}^N
\mathbb E_{\mu_N}
\bigl(q_{s_\pm}-q_{\pi_\pm}\bigr)^2
\le2\log\frac1{1-\eta}.
\]

A good disagreement can disappear only if at least one forecast changes by \(\gamma/5\) or more. The expected number of such lost disagreements is therefore at most
\[
\frac{100}{\gamma^2}\log\frac1{1-\eta}
\le
\frac{200\eta}{\gamma^2}
\le\frac{25}{128}N.
\]
There are at least \(3N/4\) good rounds in expectation. Hence the actual predictors disagree in the intended direction on at least
\[
\left(\frac34-\frac{25}{128}\right)N
=
\frac{71}{128}N>\frac N2
\]
rounds in expectation.

### Step 3: There is no negative contribution elsewhere

For every history within the experiment,
\[
\begin{aligned}
&[s_+(h1)-s_+(h0)]-[s_-(h1)-s_-(h0)]\\
&\qquad=(1-\eta)\gamma\bigl(\mu_N(h)+\nu_N(h)\bigr)>0.
\end{aligned}
\]
Thus the plus predictor never chooses zero when the minus predictor chooses one.

Under \(\mu_N\), each disagreement costs \(2\gamma\). Consequently,
\[
L_N^{s_-}-L_N^{s_+}
\ge2\gamma(N/2)=\frac{\sqrt N}{32}.
\]
The upper bound \(2\gamma N=\sqrt N/16\) is immediate. \(\square\)

The key feature is that the lemma is uniform over **every** background \(A\). It requires no effective convergence rate for that background.

---

# 3. The effective universal construction

The old proof tried to neutralize every background model separately. Here, two added semimeasures copy the universal background’s probability of selecting each experiment. That keeps its relative contamination uniformly small in every experiment.

### Theorem 4: Effective universal mixtures with an \(n^{1/4}\) loss gap

There exists a computable probability measure \(\mu\) with the following property.

For every lower-semicomputable universal semimeasure \(M\), one can uniformly construct lower-semicomputable universal semimeasures \(\xi_-,\xi_+\) such that, for every \(n\ge2\),
\[
\boxed{
\frac{n^{1/4}}{256}
\le
L_n^{\xi_-}-L_n^{\xi_+}
\le
\frac{n^{1/4}}8.
}
\]

When \(M\) is an effective universal mixture, so are \(\xi_-,\xi_+\). They admit positive lower-semicomputable prior weights with coordinatewise ratios in \([1/3,3]\). An instance has positive computable weights summing to one.

**Status:** new construction; proved below; high confidence.

## 3.1 The source

For \(j\ge0\), define
\[
z_j=1^j0,\qquad
p_j=2^{-j-1},\qquad
N_j=16^j,\qquad
\gamma_j=\frac1{32\cdot4^j}.
\]
Let \(\mu_j,\nu_j\) be the measures from Theorem 3 with \(N=N_j\).

The true source \(\mu\) operates as follows:

1. Generate fair bits until the first zero.
2. If that zero follows \(j\) ones, generate \(N_j\) bits with probability \(1/2+\gamma_j\) of one.
3. Generate fair bits forever.

Thus \(J=j\) has probability \(p_j\). Its cylinder probabilities are explicitly
\[
\mu(1^k)=2^{-k},
\qquad
\mu(z_jh)=2^{-j-1}\mu_j(h).
\]
All these values are uniformly computable; in fact, they are rational.

## 3.2 Two enumerable semimeasures that copy the background’s branch masses

Define \(P,Q\) by
\[
P(1^k)=Q(1^k)=M(1^k)
\qquad(k\ge0),
\]
and
\[
P(z_jh)=M(z_j)\mu_j(h),\qquad
Q(z_jh)=M(z_j)\nu_j(h).
\]

These formulas cover every finite binary string.

They define semimeasures:

- At a header node \(1^k\), the semimeasure inequality is exactly the inequality for \(M\).
- Inside a selected branch, cylinder additivity follows from \(\mu_j,\nu_j\).

They are uniformly lower semicomputable. The construction uses products of nonnegative computable numbers with lower-semicomputable numbers. It uses neither subtraction nor normalization.

Set
\[
\eta=2^{-20},
\]
\[
\xi_-=(1-\eta)\left(\frac14P+\frac34Q\right)+\eta M,
\]
\[
\xi_+=(1-\eta)\left(\frac34P+\frac14Q\right)+\eta M.
\]
Both dominate \(\eta M\), so both are universal over all enumerable semimeasures.

The decisive identity is
\[
P(z_j)=Q(z_j)=M(z_j)>0.
\]
After observing \(z_j\),
\[
\frac{\xi_\pm(z_jh)}{M(z_j)}
=
(1-\eta)\pi_j^\pm(h)+\eta A_j(h),
\]
where
\[
A_j(h)=\frac{M(z_jh)}{M(z_j)}
\]
is a semimeasure with root value one.

The relative contamination is therefore **exactly \(\eta\) in every branch**, regardless of how small \(M(z_j)\) is. Theorem 3 applies uniformly.

The quotient defining \(A_j\) is used only in the proof. Neither the construction of \(P,Q\) nor their lower-semicomputability requires computing it.

## 3.3 Aggregating the experiments

Let \(D_j(m)\) be the conditional expected loss gap after \(m\le N_j\) experiment rounds. Theorem 3 gives
\[
D_j(m)\ge0,\qquad
D_j(N_j)\ge\gamma_jN_j=\frac{4^j}{32},
\qquad
D_j(m)\le2\gamma_jm.
\]
The function \(D_j\) is nondecreasing.

Before selection, the predictors agree. After the experiment, both added components have fair conditional probabilities, so their signed child scores vanish and the two predictors again agree.

Consequently,
\[
\Delta_n:=L_n^{\xi_-}-L_n^{\xi_+}
=
\sum_{j\ge0}p_jD_j(m_j(n)),
\]
where
\[
m_j(n)=\min\{16^j,(n-j-1)_+\}.
\]

Every completed branch contributes at least
\[
p_jD_j(N_j)\ge\frac{2^j}{64}.
\]
For \(n\ge2\), let \(J\) be the largest integer with \(2\cdot16^J\le n\). Since \(j+1\le16^j\), all branches \(j\le J\) are complete. Thus
\[
\Delta_n
\ge
\frac1{64}\sum_{j=0}^J2^j
\ge\frac{n^{1/4}}{256}.
\]

Conversely,
\[
\Delta_n
\le
\frac1{32}\sum_{j\ge0}2^{-3j}\min(16^j,n).
\]
Splitting at \(j=\lfloor\log_{16}n\rfloor\) gives
\[
\Delta_n\le\frac{11}{112}n^{1/4}<\frac18n^{1/4}.
\]
This proves the theorem’s rate. \(\square\)

In particular, effectiveness does not force bounded differences, \(o(\log n)\) differences, or summable per-step expected differences for every computable source.

### A distinction about individual paths

Each realized path selects only one finite experiment. For this pair, its realized error-count difference eventually becomes constant. The expected difference diverges because the experiment length has a sufficiently heavy tail.

That is a counterexample to the requested statement about **expected cumulative losses**. It is not a claim of pathwise divergence.

---

# 4. Effective weights and complexity priors

## 4.1 Positive computable weights, with ratio at most three

Suppose
\[
M=\sum_i a_i\rho_i,
\]
where \(a_i>0\) are lower semicomputable and \(\sum_i a_i\le1\).

Since \(P,Q\) are constructed effectively from \(M\), obtain known, distinct program indices \(p,q\) with
\[
\rho_p=P,\qquad \rho_q=Q.
\]
Define
\[
w_i^-=
\eta a_i+
(1-\eta)\left(
\frac14\mathbf1_{\{i=p\}}+
\frac34\mathbf1_{\{i=q\}}
\right),
\]
and
\[
w_i^+=
\eta a_i+
(1-\eta)\left(
\frac34\mathbf1_{\{i=p\}}+
\frac14\mathbf1_{\{i=q\}}
\right).
\]

These give precisely \(\xi_-,\xi_+\). Every weight is positive and lower semicomputable, their sums are at most one, and
\[
\boxed{\frac13\le\frac{w_i^+}{w_i^-}\le3\quad\text{for all }i.}
\]

Taking \(a_i=2^{-i-1}\) makes all the weights computable and their sums exactly one.

There is no totality test and no semantic equality test. We add mass to two known program indices; duplicate names elsewhere cause no problem.

## 4.2 Both priors can be comparable to the same fixed \(2^{-K(i)}\)

### Corollary 5

For every fixed optimal prefix description machine \(C\), there exist positive lower-semicomputable weights \(w^-,w^+\) such that
\[
w_i^-\asymp2^{-K_C(i)},\qquad
w_i^+\asymp2^{-K_C(i)},
\]
\[
\frac13\le w_i^+/w_i^-\le3,
\]
and their mixtures have the loss gap of Theorem 4 under the same computable \(\mu\).

**Proof.** Use
\[
a_i=2^{-K_C(i)}
\]
as the base prior above. Both new priors equal \(\eta a_i\) except at two coordinates. Since \(a_p,a_q>0\), finite increases preserve two-sided comparability to \(a_i\). The constants may depend on \(p,q\), but are uniform in \(i\). \(\square\)

This directly resolves the complexity-**comparable** version omitted from my previous answer.

## 4.3 Two exact shortest-description priors

### Theorem 6

There are an effective enumeration \((\tau_i)\) of all enumerable semimeasures and two optimal prefix machines \(C_-,C_+\) such that
\[
\Xi_\pm=\sum_i2^{-K_{C_\pm}(i)}\tau_i
\]
have
\[
L_n^{\Xi_-}-L_n^{\Xi_+}=\Theta(n^{1/4})
\]
under the computable source above. Their corresponding weights have ratios in \([1/4,4]\).

**Proof.** Start with an optimal prefix machine \(C_0\) and an effective enumeration \((\rho_i)\). Define
\[
M=\sum_{i\ge2}2^{-K_{C_0}(i)}\rho_{i-2}.
\]
Construct \(P,Q\) from this \(M\), and set
\[
\tau_0=P,\quad\tau_1=Q,\quad\tau_{i+2}=\rho_i.
\]

Build \(C_-\) with:

- code \(00\) outputting index \(1\);
- code \(0100\) outputting index \(0\);
- prefix \(1^{30}\), followed by a \(C_0\)-program, simulating \(C_0\).

Let \(C_+\) swap the outputs of the two short codes. These are optimal prefix machines. Their exact canonical mixtures are
\[
\Xi_-=\frac1{16}P+\frac14Q+2^{-30}M,
\]
\[
\Xi_+=\frac14P+\frac1{16}Q+2^{-30}M.
\]

After any selector, the ideal core weights are \(1/5,4/5\), swapped. On \(R\in[1/2,2]\), their margins are at least \(\gamma/3\), and \(\mu_N\le5\pi_\pm\). The proof of Theorem 3 therefore bounds lost disagreements by
\[
\frac{45}{\gamma^2}\log\frac1{1-\eta'},
\qquad
\eta'=\frac{2^{-30}}{5/16+2^{-30}}.
\]
Since
\[
\log\frac1{1-\eta'}
=
\log\left(1+\frac{16}{5}2^{-30}\right)
\le4\cdot2^{-30},
\]
this loses less than \(N/4\) good disagreements. The score ordering still holds, and the same aggregation proves \(\Theta(n^{1/4})\). \(\square\)

These are exact \(2^{-K}\) weights, not merely weights of the same order.

---

# 5. Two actual Solomonoff priors

### Theorem 7

There exist universal monotone machines \(U_-,U_+\) and a computable probability measure \(\mu\) such that
\[
\boxed{
L_n^{M_{U_-}}-L_n^{M_{U_+}}=\Theta(n^{1/4}).
}
\]

**Proof by direct machine construction.**

Start with any universal monotone machine \(U_0\), and use \(M=M_{U_0}\) in Theorem 4.

A machine realizing \(P\) runs \(U_0\) and copies its output until the first zero. If that zero follows \(j\) ones, it switches to a sampler for \(\mu_j\), using unread fair input bits. A machine for \(Q\) switches to \(\nu_j\).

The unread input tail is independent fair randomness. All required biased probabilities are dyadic, so their sampling is exact.

Use a fixed 22-bit dispatch header to select:

- \(U_0\) on \(4\) header patterns;
- the \(P\) machine on \(2^{20}-1\) patterns;
- the \(Q\) machine on \(3(2^{20}-1)\) patterns.

These counts sum to \(2^{22}\) and realize
\[
\eta M+(1-\eta)(P/4+3Q/4).
\]
Swapping the last two counts realizes the other mixture.

Both machines are universal because a fixed header simulates \(U_0\). Their nonempty cylinder masses are the constructed \(\xi_-,\xi_+\), so all their Bayes actions coincide with those already analyzed. \(\square\)

This is also consistent with Wood–Sunehag–Hutter’s exact equivalence between effective universal mixtures and Solomonoff priors, with the usual empty-string qualification: **arXiv:1111.3854**, Lemma 13 and Theorem 14. [arxiv.org](https://arxiv.org/html/1111.3854v1?utm_source=chatgpt.com)

---

# 6. A single machine: \(M_U\) versus \(\xi_U\)

This comparison needs an explicit convention because monotone sampling and prefix descriptions are distinct machine interfaces. Leike–Hutter explicitly distinguishes the shortest-index mixture and random-input construction, noting that they are equivalent but need not be equal. [hutter1.net](https://www.hutter1.net/publ/aixiprior.pdf?utm_source=chatgpt.com)

Here is a construction in which **one physical interpreter provides both interfaces**.

## 6.1 Shared-machine convention

Use a one-way input-stream machine with no end-of-input oracle.

- \(M_U(x)\) is the probability that \(U\), on fair infinite input, outputs a string beginning with \(x\).
- A halting description is the finite input prefix actually consumed when \(U\) halts.
- Fix an injective computable index encoding \(\operatorname{enc}(i)\), every value of which begins with \(00\).
- Define
  \[
  K_U(i)=\min\{|p|:U\text{ consumes }p,\text{ outputs }\operatorname{enc}(i),
  \text{ and halts}\}.
  \]
- Define
  \[
  \xi_U=\sum_i2^{-K_U(i)}\rho_i.
  \]

Consumed-input halting descriptions form a prefix-free set. Choose the base interpreter to be universal for monotone sampling and optimal for these prefix descriptions. Such an interpreter is obtained by combining a universal monotone simulator with an optimal self-delimiting halting interpreter.

### Theorem 8: Same-machine counterexample

Under this convention, there exists such a universal \(U\) for which the same computable \(\mu\) satisfies
\[
\boxed{
\frac{n^{1/4}}{512}
\le
L_n^{M_U}-L_n^{\xi_U}
\le
\frac{n^{1/4}}8
\qquad(n\ge2).
}
\]

**Status:** new extension; proved below; high confidence under the stated convention.

## 6.2 Construction

Fix a base interpreter \(U_0\). Write
\[
M_0=M_{U_0},\qquad
\kappa_i=2^{-K_{U_0}(i)},\qquad
B_0=\sum_i\kappa_i\rho_i,
\]
and
\[
R=\frac12(M_0+B_0).
\]
Construct \(P,Q\) by copying the selector masses of \(R\), exactly as in Section 3. Let their known indices be \(p,q\).

Set \(\varepsilon=2^{-40}\). Define \(U\) by the following prefix-free dispatch:

| Input prefix | Operation |
|---|---|
| \(0\) | Run a sampler for \(Q\) |
| \(100\) | Run a sampler for \(P\) |
| \(101\) | Output \(\operatorname{enc}(p)\) and halt |
| \(11000\) | Output \(\operatorname{enc}(q)\) and halt |
| A fixed 40-bit word \(s_{40}\) beginning \(111\) | Simulate \(U_0\) on the remaining input |
| Unused branches | Loop without output |

The \(P,Q\) samplers are wrapped so that they **never halt**, even if an underlying computation stops producing output. This prevents unintended short halting descriptions.

Therefore
\[
K_U(p)=3,\qquad K_U(q)=5,
\]
and
\[
K_U(i)=40+K_{U_0}(i)\qquad(i\ne p,q).
\]
Consequently,
\[
\boxed{
\xi_U=\frac18P+\frac1{32}Q+\varepsilon B_{\rm rest},
}
\]
where
\[
B_{\rm rest}=\sum_{i\ne p,q}\kappa_i\rho_i\le B_0.
\]

For nonempty strings, the sampling semimeasure is
\[
\boxed{
M_U=
\frac18P+\frac12Q
+\frac18H_p+\frac1{32}H_q
+\varepsilon M_0,
}
\]
where \(H_i(x)=1\) if \(x\) is a prefix of \(\operatorname{enc}(i)\), and zero otherwise.

The universal simulation branch makes \(U\) universal in both required senses. The finite-output terms are genuine parts of \(M_U\); they cannot be omitted.

## 6.3 Branches \(j\ge1\)

For \(j\ge1\), the selector \(z_j\) starts with one. Since all encodings begin \(00\),
\[
H_p(z_jh)=H_q(z_jh)=0.
\]

Let
\[
r_j=R(z_j).
\]
By construction,
\[
M_0(z_j)\le2r_j,\qquad
B_{\rm rest}(z_j)\le2r_j.
\]

Thus, inside branch \(j\), the two ideal normalized cores are
\[
\pi_-=\frac15\mu_j+\frac45\nu_j
\]
for \(M_U\), and
\[
\pi_+=\frac45\mu_j+\frac15\nu_j
\]
for \(\xi_U\).

Their core masses are respectively \(5/8\) and \(5/32\). Normalizing the contaminated suffix semimeasures gives KL budgets at most
\[
\log\left(1+\frac{16}{5}\varepsilon\right)
\le\frac{16}{5}\varepsilon,
\]
and
\[
\log\left(1+\frac{64}{5}\varepsilon\right)
\le\frac{64}{5}\varepsilon.
\]
The sum is at most \(16\varepsilon\).

Since \(\mu_j\le5\pi_\pm\), the sum of the two squared prediction-error budgets under \(\mu_j\) is at most
\[
40\varepsilon.
\]

On the same good likelihood-ratio event as before, both core decision margins are at least \(\gamma_j/3\). Hence the expected total number of individual action changes on good histories is at most
\[
\frac{360\varepsilon}{\gamma_j^2}.
\]

Let \(D_j(m)\) now denote the conditional loss difference
\[
L_m^{M_U}-L_m^{\xi_U}
\]
within this branch. On a good history, if \(I_-,I_+\) record the two individual action changes, the actual conditional difference is at least
\[
2\gamma_j(1-I_--I_+).
\]
Outside the good event it is at least \(-2\gamma_j\).

Using the bad-event bound \(16/251\), we obtain
\[
D_j(m)
\ge
a\gamma_jm-\frac{720\varepsilon}{\gamma_j},
\qquad
a=2\left(1-\frac{32}{251}\right)>1.
\]
Also, trivially,
\[
D_j(m)\ge-2\gamma_jm.
\]
Combining,
\[
\boxed{
D_j(m)\ge
a\gamma_jm-
\min\left\{4\gamma_jm,\frac{720\varepsilon}{\gamma_j}\right\}.
}
\]

This handles different backgrounds without assuming pointwise ordering of the two actual predictors.

## 6.4 The exceptional branch \(j=0\)

Here \(N_0=1\). The finite halting outputs matter, but their effect has the desired sign.

At history \(0\), both halting outputs continue with zero. Thus
\[
M_U(01)-M_U(00)
\le-\frac5{32}+\varepsilon<0.
\]
For the canonical mixture,
\[
\xi_U(01)-\xi_U(00)
\ge
r_0\left(\frac3{512}-2\varepsilon\right)>0.
\]
Therefore \(M_U\) predicts zero and \(\xi_U\) predicts one on the single biased bit. Its conditional loss difference is exactly \(2\gamma_0\).

## 6.5 Aggregation and the rate

The true source is fair during headers and after experiments. Hence expected loss differences vanish there, even if the predictors disagree.

Set
\[
S_n=\sum_jp_j\gamma_jm_j(n).
\]
The completed-branch calculation above gives
\[
S_n\ge\frac{n^{1/4}}{256}\qquad(n\ge2).
\]

The total possible perturbation penalty is bounded by
\[
\begin{aligned}
E_n
&\le
\sum_{j\ge0}
\min\left\{
\frac n{16}8^{-j},
11520\varepsilon\,2^j
\right\}\\
&\le
4096\varepsilon^{3/4}n^{1/4}.
\end{aligned}
\]
The last inequality follows by splitting the geometric sums where
\(16^j\) is comparable to \(n/\varepsilon\). More generally,
\[
\sum_{j\ge0}\min\{A8^{-j},B2^j\}
\le\frac{22}{7}A^{1/4}B^{3/4}.
\]

Since \(\varepsilon=2^{-40}\),
\[
E_n\le2^{-18}n^{1/4}.
\]
Including the positive \(j=0\) contribution,
\[
L_n^{M_U}-L_n^{\xi_U}
\ge aS_n-E_n
\ge
\left(2^{-8}-2^{-18}\right)n^{1/4}
\ge\frac{n^{1/4}}{512}.
\]

For any two predictors, the absolute expected difference on a biased round is at most \(2\gamma_j\), and it is zero on a fair round. Therefore
\[
\left|L_n^{M_U}-L_n^{\xi_U}\right|
\le2S_n
\le\frac{11}{112}n^{1/4}
<\frac18n^{1/4}.
\]
This proves Theorem 8. \(\square\)

There is no circular definition: \(U_0,M_0,B_0,R\) are fixed first; \(P,Q\) are then compiled from \(R\); their indices are obtained; finally those finite indices are inserted into \(U\).

---

# 7. What has been established, and what remains

| Formulation | Outcome |
|---|---|
| Positive computable weights on an effective enumeration of all enumerable semimeasures, bounded weight ratios | **Counterexample proved**, gap \(\Theta(n^{1/4})\) |
| Two priors both \(\asymp2^{-K(i)}\) for one fixed reference complexity | **Counterexample proved** |
| Two exact \(2^{-K(i)}\) priors from chosen optimal prefix machines | **Counterexample proved** |
| Two Solomonoff priors \(M_U,M_V\) | **Counterexample proved by direct machine construction** |
| Same-machine \(M_U\) versus \(\xi_U\) | **Counterexample proved under the explicit shared-interpreter convention** |
| Original product source \(1/2+1/(32t)\), with full effective universality | **Not resolved by this construction** |
| Lean certification of these extensions | **Not yet performed** |

The main new device is to make the two added enumerable semimeasures **copy the universal background’s selector masses**. This allows arbitrarily long experiments while keeping the background’s conditional fraction uniformly small. A finite KL budget then controls how many core decisions the background can change.

The primary literature used here supplies the standard prediction bounds and representation conventions:

- Hutter, **“Convergence and Loss Bounds for Bayesian Sequence Prediction,”** [arXiv:cs/0301014](https://arxiv.org/abs/cs/0301014), DOI **10.1109/TIT.2003.814488**.
- Wood, Sunehag, and Hutter, **“(Non-)Equivalence of Universal Priors,”** [arXiv:1111.3854](https://arxiv.org/abs/1111.3854). Its semimeasure realization theorem also explains the harmless empty-string convention in machine representations. [arxiv.org](https://arxiv.org/html/1111.3854v1?utm_source=chatgpt.com)
- Leike and Hutter, **“Bad Universal Priors and Notions of Optimality,”** [arXiv:1510.04931](https://arxiv.org/abs/1510.04931), for the indexed complexity convention and the distinction between the two universal-prior constructions. [hutter1.net](https://www.hutter1.net/publ/aixiprior.pdf?utm_source=chatgpt.com)

I did not locate this selector-mass construction or a published direct resolution of the requested expected-loss comparison in the searches performed. Hutter’s page still lists Problem 3.3 without a solution annotation. That is a qualified literature-search result; the proofs above should be treated as a mathematical contribution awaiting formal verification and external review, rather than as a certified prize resolution. [hutter1.net](https://www.hutter1.net/ai/uaibook.htm?utm_source=chatgpt.com)