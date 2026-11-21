**I did not obtain a fixed-\(U\) superlinear counterexample or an unrestricted polynomial upper bound.** I did obtain two polynomial comparison theorems, a linear bound for the initial forced portion of a fixed computable dogmatic construction, and a stronger version of the mass-survival observation from 017.

The literature check is also definite on the central distinction: **Leike–Hutter explicitly exclude horizon-one prediction from their persistent dogmatic failure example. Their result does not settle the polynomial-rate question.**

The complete report, including quantified statements, full proofs, unsuccessful construction attempts, and confidence and novelty assessments, is here:

:chatgpt-content-reference{index="5"}[019-p62p-research.a.md](sandbox:/workspace/scratch/42e8a0ac4efb/019-p62p-research.a.md)

## 1. The precise question and the literature answer

Write \(E_A(z)\) for the total mistakes of the horizon-one greedy policy of a fixed universal chronological semimeasure \(A\), on a computable infinite passive truth sequence \(z\). Let \(K(z)\) be the shortest prefix description of an algorithm generating that entire sequence.

The assertion under investigation is
\[
\forall A\ \exists C_A>0,\ d_A\in\mathbb N\
\forall\text{ computable }z:
\qquad
E_A(z)\le C_A(1+K(z))^{d_A}.
\tag{P}
\]
Its negation requires
\[
\exists A\ \forall C>0\ \forall d\in\mathbb N\
\exists\text{ computable }z:
\qquad
E_A(z)>C(1+K(z))^d.
\tag{\(\neg P\)}
\]
Changing the universal prior with the desired number of mistakes does not establish this negation.

### What Leike–Hutter actually say

In §6.1 of *Bad Universal Priors and Notions of Optimality*, immediately after their sequence-prediction failure example, they write:

> “However, if we have a constant horizon of 1, AIXI does succeed in sequence prediction”

They cite Hutter’s §6.2.2. Their dogmatic theorem is conditional on a baseline value exceeding a chosen threshold; neither that theorem nor this exception supplies a polynomial total-error rate. [proceedings.mlr.press](https://proceedings.mlr.press/v40/Leike15.pdf?utm_source=chatgpt.com)

Leike’s 2016 thesis repeats the horizon-one exception. The 2024 Hutter–Quarel–Catt book also explicitly warns that the indifference machine depends on the selected lifetime: increasing the lifetime while fixing that machine invalidates the example. [arxiv.org](https://arxiv.org/pdf/1611.08944?utm_source=chatgpt.com)

I found no later primary source resolving the precise assertion (P). Hutter’s maintained prize page still lists broad Problem 6.2, but it does not separately track part (d), so it cannot conclusively establish this subproblem’s current status. [hutter1.net](https://www.hutter1.net/ai/uaibook.htm?utm_source=chatgpt.com)

## 2. The common finite error budget

For a history
\[
h=(a_1,r_1)\cdots(a_t,r_t),
\]
decode its truth string by
\[
d(h)_i=
\begin{cases}
a_i,&r_i=1,\\
1-a_i,&r_i=0.
\end{cases}
\]
Chronology means
\[
A(h(a,0))+A(h(a,1))\le A(h).
\]
The greedy policy maximizes \(A(h(a,1))\).

### Theorem 1: established exponential bound

For every universal \(A\), there is \(c_A>0\) such that, for every computable infinite \(z\),
\[
\boxed{
(E_A(z)+1)c_A2^{-K(z)}\le A(\epsilon)\le1.
}
\tag{1}
\]

**Proof.** A fixed interpreter converts a generator for \(z\) into the deterministic passive environment \(\mu_z\) returning reward \([a_t=z_t]\). Universal domination gives
\[
A(h)\ge w_z\mu_z(h),
\qquad
w_z=c_A2^{-K(z)}.
\]
At a mistake, the actual reward is zero. If \(a_t\ne z_t\), chronology and greediness give
\[
\begin{aligned}
A(h_{t-1})-A(h_t)
&\ge A(h_{t-1}(a_t,1))\\
&\ge A(h_{t-1}(z_t,1))
\ge w_z.
\end{aligned}
\]
At other cycles mass does not increase. Therefore
\[
E_{1:T}w_z+A(h_T)\le A(\epsilon).
\]
Since \(A(h_T)\ge w_z\), take the supremum over \(T\). \(\square\)

**Confidence:** high. **Novelty:** the book’s established argument, with terminal mass retained.

The question is whether universality imposes additional structure beyond this additive budget. The next two theorems show that it does when a suitable computable comparison predictor is available.

## 3. A polynomial comparison theorem for every universal AI prior

### Theorem 2: near-quadratic transfer from a computable predictor

Fix any universal chronological \(A\) and maximizing tie rule. There is \(C_A>0\) such that, for every total computable predictor
\[
\pi:\{0,1\}^*\to\{0,1\}
\]
and every infinite truth sequence \(z\) on which \(\pi\) makes \(e<\infty\) mistakes,
\[
\boxed{
E_A(z)\le
C_A2^{K(\pi)}(e+1)^2
\bigl(1+\log_2(e+1)\bigr)^2.
}
\tag{2}
\]
Here
\[
K(\pi)=\min\{K(i):\varphi_i=\pi\}
\]
uses prefix descriptions of predictor program indices. For a fixed \(\pi\), its description factor is absorbed into a constant \(C_{A,\pi}\).

**Proof.** For each \(j\ge0\), construct a chronological environment \(F_{\pi,j}\):

- It follows \(A\) until just after the \(j\)-th mistake of \(\pi\), computing these mistakes from the decoded truth.
- From that boundary onward, it returns the deterministic prediction reward for \(\pi\).

For \(j=0\), the boundary is the root, and the environment is \(A(\epsilon)\) times the deterministic \(\pi\)-environment.

For fixed \(j\), the histories ending at the \(j\)-th \(\pi\)-mistake form a computable prefix-free stopping set. Thus this construction is lower semicomputable and chronological. If \(h_j\) is the boundary on the actual run, its accumulated mass there is exactly \(A(h_j)\).

Choose positive computable weights \(w_j\) summing to one, and form
\[
F_\pi=\sum_{j\ge0}w_jF_{\pi,j}.
\]
Universality supplies \(c_\pi>0\) with
\[
A\ge c_\pi F_\pi.
\]

Consider the interval after the \(j\)-th \(\pi\)-mistake and before the next one. Throughout this interval, \(\pi\) is correct, so \(F_{\pi,j}\) preserves its entire boundary mass \(A(h_j)\). Every AI mistake therefore costs at least
\[
c_\pi w_jA(h_j):
\]
the correct-action reward-one counterfactual receives this contribution, and greediness makes the chosen wrong action’s reward-one score at least as large.

The interval begins with actual mass \(A(h_j)\), so it contains at most \(1/(c_\pi w_j)\) AI mistakes. There are at most \(e\) additional AI mistakes at the cycles where \(\pi\) itself is wrong. Hence
\[
\boxed{
E_A(z)\le e+\frac1{c_\pi}\sum_{j=0}^{e}\frac1{w_j}.
}
\tag{3}
\]

Use the explicit rational weights
\[
w_0=\frac12,
\]
and, for \(2^b\le j<2^{b+1}\),
\[
w_j=\frac{2^{-b-1}}{(b+1)(b+2)}.
\tag{4}
\]
Block \(b\) has total weight
\[
\frac1{2(b+1)(b+2)},
\]
so all weights sum to one. Moreover,
\[
\frac1{w_j}
\le2j(1+\log_2j)(2+\log_2j)
\qquad(j\ge1).
\]
Consequently,
\[
\sum_{j=0}^{e}\frac1{w_j}
=
O\!\left((e+1)^2(1+\log_2(e+1))^2\right).
\tag{5}
\]

Finally, the construction is effective from a predictor program. It also defines a chronological semimeasure for partial programs: if a required prediction computation fails to halt, the environment stops. Mixing these constructions over a globally prefix-free language of descriptions gives the uniform estimate
\[
c_\pi\ge c_A2^{-K(\pi)}.
\]
Substitute into (3). Infinite final intervals are handled by applying the estimate to every finite initial segment. \(\square\)

A simpler weight choice,
\[
w_j=\frac1{(j+1)(j+2)},
\]
gives the exact cubic variant
\[
\boxed{
E_A(z)\le
e+\frac{(e+1)(e+2)(e+3)}{3c_\pi}.
}
\tag{6}
\]

The same reasoning works for a partial computable predictor that is defined at every prefix of the specified target.

**Confidence:** high; independently checked. **Novelty:** a refinement of the stopping-boundary method developed in 017; publication priority unclaimed.

## 4. Polynomial bounds for uniformly total description families

The preceding theorem can be applied with one fixed computable predictor for an entire description family.

### Theorem 3: near-quadratic error in total-family description length

Let
\[
G:\{0,1\}^*\times\mathbb N_{\ge1}\to\{0,1\}
\]
be a fixed total computable function. A seed \(s\) describes the sequence
\[
z^s_t=G(s,t).
\]
For every universal \(A\), there is \(C_{A,G}>0\) such that
\[
\boxed{
E_A(z^s)\le
C_{A,G}(|s|+1)^2
\bigl(1+\log_2(|s|+2)\bigr)^2
\quad\text{for every }s.
}
\tag{7}
\]

**Proof.** Put
\[
p_n=\frac1{(n+1)(n+2)},
\qquad
\sum_{n\ge0}p_n=1,
\]
and define
\[
\mu(x)=
\frac12\,2^{-|x|}
+
\frac12\sum_{n\ge0}p_n2^{-n}
\sum_{|s|=n}[x\preceq z^s].
\tag{8}
\]
This is a computable probability measure. The tail over seed lengths exceeding \(N\) has an explicit computable bound, and every retained finite-prefix test terminates because \(G\) is uniformly total. The fair-coin component ensures \(\mu(x)>0\) everywhere.

Construct a single computable predictor \(\pi_G\) by dovetailing searches for a bit \(b\) satisfying
\[
3\mu(xb)>\mu(x).
\tag{9}
\]
Strict inequalities between computable reals are semidecidable. One child has mass at least \(\mu(x)/2\), so the search terminates.

At a mistake, the true child has mass less than \(2\mu(x)/3\). For a target with \(n=|s|\), its component also gives
\[
\mu(z^s_{1:T})\ge\frac12p_n2^{-n}.
\]
Therefore
\[
\frac12p_n2^{-n}
\le
(2/3)^{E_{\pi_G,1:T}(z^s)},
\]
and
\[
E_{\pi_G}(z^s)
\le
\frac{n+1+\log_2((n+1)(n+2))}
{\log_2(3/2)}
=O(n+1).
\tag{10}
\]
The predictor \(\pi_G\) is fixed independently of the seed and seed length. Apply Theorem 2. \(\square\)

Equivalently, if
\[
K_G(z)=\min\{|s|:\forall t,\ G(s,t)=z_t\},
\]
the bound is near-quadratic in \(K_G(z)\).

**Confidence:** high; independently checked. **Novelty:** computable-mixture prediction combined with Theorem 2; priority unclaimed.

### Why this does not prove (P)

There is no uniformly total computable family containing every computable infinite sequence. Enumerate all seeds as \(s_1,s_2,\ldots\), and define
\[
\gamma_t=1-G(s_t,t).
\]
Then \(\gamma\) is computable but differs from \(z^{s_t}\) at coordinate \(t\), for every \(t\).

Also, \(K_G\) need not be polynomially bounded by unrestricted \(K\), even inside a fixed family. For
\[
G(s)=s0^\infty,\qquad z_N=0^N10^\infty,
\]
we have
\[
K_G(z_N)=N+1,
\qquad
K(z_N)\le K(N)+O(1).
\tag{11}
\]

Thus Theorem 3 rules out a proposed superpolynomial construction when its targets come from one uniformly total generator family **with seed length polynomially bounded by their unrestricted complexity**. It does not make that condition automatic.

These positive results apply to every effectively universal chronological prior, including the usual program-mixture implementation of Solomonoff–Hutter’s prior. They do not establish its unrestricted ordinary-\(K\) rate.

## 5. A fixed computable dogmatic policy: a linear bound

There is a stronger limitation on the standard dogmatic construction than merely observing that the long-horizon argument does not apply.

Fix a universal \(B\), a total computable history policy \(\pi\), and a computable rational \(0<\eta<1\). Let \(D_\pi B\) agree with \(B\) while actions follow \(\pi\), and return zero starting at the first deviating action and forever afterwards. Set
\[
A=\eta B+(1-\eta)D_\pi B.
\tag{12}
\]
This is a universal lower semicomputable chronological semimeasure.

### Theorem 4: linearly many mistakes before the first deviation

There is \(C_{B,\pi,\eta}\) such that, for every computable passive truth \(z\), the greedy policy for (12) makes at most
\[
\boxed{
C_{B,\pi,\eta}(K(z)+1)
}
\tag{13}
\]
mistakes during its initial segment of following \(\pi\).

**Proof.** First restrict \(B\) to the computable policy \(\pi\). For a truth string \(x\), let \(h^\pi(x)\) be its corresponding history and define
\[
\nu_\pi(x)=B(h^\pi(x)).
\]
This is a lower semicomputable sequence semimeasure. Its passive lift is therefore dominated by \(B\): for some \(c_\pi>0\),
\[
B(g)\ge c_\pi\nu_\pi(d(g)).
\]

At a \(\pi\)-consistent history \(h\), write \(a=\pi(h)\) and \(b=1-a\). Both \(h(b,1)\) and \(h(a,0)\) decode to the same truth extension, and the latter is the extension generated by \(\pi\). Hence
\[
B(h(b,1))\ge c_\pi B(h(a,0)).
\tag{14}
\]

The dogmatic success scores are exactly
\[
A(h(a,1))=B(h(a,1)),
\qquad
A(h(b,1))=\eta B(h(b,1)).
\]
If greedy \(A\) selects \(a\) and is wrong, then
\[
B(h(a,1))
\ge\eta B(h(b,1))
\ge\eta c_\pi B(h(a,0)).
\]
Thus
\[
B(h)\ge(1+\eta c_\pi)B(h(a,0)).
\tag{15}
\]
Each such mistake shrinks actual \(B\)-mass geometrically. Other cycles cannot increase it.

Universal passive domination gives
\[
B(h_t)\ge w_z=c_B2^{-K(z)}.
\]
Therefore
\[
w_z\le(1+\eta c_\pi)^{-e_{\rm initial}},
\]
so
\[
e_{\rm initial}
\le
\frac{\log(1/w_z)}{\log(1+\eta c_\pi)}
=O_{B,\pi,\eta}(K(z)+1).
\tag{16}
\]
This also covers an infinite initial segment by taking finite prefixes. \(\square\)

After the first deviation, the dogmatic component contributes zero to every future success score. The maximizing-action sets then equal those of \(B\); selected actions agree if the same tie rule is used.

This does not give a global polynomial theorem, because the resulting history need not be one reached by \(B\)’s original greedy run. Also, the constant in (16) can depend strongly on \(\pi\) and \(\eta\). Increasingly complex policies or varying mixture scales remain outside this fixed-policy conclusion.

**Confidence:** high; independently checked. **Novelty:** a quantitative deduction about the dogmatic construction, supplied here; priority unclaimed.

## 6. Layering works finitely, but the machine dependence matters

### Theorem 5: any finite number of errors can be forced by changing the machine

Fix a base universal chronological machine with semimeasure \(B\). For every \(N\ge1\), there is a universal \(A_N\) whose greedy policy makes at least \(N\) errors on \(0^\infty\), independently of tie-breaking.

**Proof.** For \(1\le j\le N\), let \(D_j\) always return zero except at cycle \(j\), where it returns one exactly for action one. Put
\[
\varepsilon_N=\frac1{4N},
\qquad
A_N=\varepsilon_NB+
\frac{1-\varepsilon_N}{N}\sum_{j=1}^ND_j.
\tag{17}
\]
This is universal because \(A_N\ge\varepsilon_NB\).

Assume the first \(i-1\) predictions on \(0^\infty\) were one, giving zero rewards. The component \(D_i\) survives and contributes
\[
\frac{1-\varepsilon_N}{N}
\]
to the success score of action one. Every \(D_j\) contributes zero to the success score of action zero, so that score is at most \(\varepsilon_N\). But
\[
\frac{1-\varepsilon_N}{N}-\varepsilon_N
=\frac{3N-1}{4N^2}>0.
\]
Thus action one is uniquely greedy and wrong. The current component is eliminated; future components survive. Induction proves the claim. A computable mixture selector implements the construction with a universal base branch. \(\square\)

**Confidence:** high. **Novelty:** elementary construction supplied here; priority unclaimed.

This realizes the proposed “one component per error” mechanism. Its quantifiers are
\[
\forall N\ \exists A_N.
\]
For one fixed \(A\), Theorem 1 gives one fixed finite bound on its errors on \(0^\infty\). Summable layering cannot evade that restriction.

For varying truths, the mass budget allows an exponential number of errors in principle. It does not prove that a single fixed prior can attain that number.

## 7. A stronger mass-survival result than 017

The disappearance of the additional mass at the first mistake is not an unavoidable history-level obstruction.

### Theorem 6: every universal AI has an all-error path with surviving mass

For every universal \(A\), every fixed maximizing tie rule, and every universal sequence semimeasure \(M\), there is an infinite decoded truth \(\beta\) whose greedy histories \(h_n\) satisfy
\[
r_i=0\quad\text{for all }i,
\qquad
A(h_n)\ge w>0,
\tag{18}
\]
and
\[
\boxed{
\sum_{n\ge1}M(\beta_{1:n})<\infty,
\qquad
\frac{A(h_n)}{nM(\beta_{1:n})}\to\infty.
}
\tag{19}
\]
The sequence \(\beta\) is noncomputable.

**Proof.** Run the agent against the computable environment \(Z\) that always returns zero. Universality gives
\[
A(h_n)\ge wZ(h_n)=w>0.
\]
Define
\[
\beta_i=1-a_i.
\]
As a passive truth, \(\beta\) reproduces exactly this all-error interaction.

The passive lift \(h\mapsto M(d(h))\) is chronological and lower semicomputable, so \(A\) dominates it by some \(c>0\). At every cycle,
\[
A(h_{i-1})-A(h_i)
\ge A(h_{i-1}(a_i,1))
\ge A(h_{i-1}(\beta_i,1))
\ge cM(\beta_{1:i}).
\]
Therefore
\[
c\sum_{i=1}^nM(\beta_{1:i})
\le A(\epsilon)-A(h_n)\le1.
\tag{20}
\]

The sequence \(u_n=M(\beta_{1:n})\) is nonincreasing and summable, so
\[
nu_n\le2\sum_{i=\lceil n/2\rceil}^nu_i\to0.
\]
Combine this with \(A(h_n)\ge w\). Finally, computable \(\beta\) would give a positive lower bound on all its \(M\)-prefix masses, contradicting summability. \(\square\)

**Confidence:** high; independently checked. **Novelty:** a deduction strengthening 017’s mass-separation conclusion to every universal prior.

For every finite \(n\),
\[
z^{(n)}=\beta_{1:n}0^\infty
\]
is computable and causes at least \(n\) errors. But the available upper description bound is only
\[
K(z^{(n)})\le n+K(n)+O(1).
\tag{21}
\]

Indeed, the summability argument gives a necessary lower estimate:
\[
K(z^{(n)})-\log_2n\to\infty.
\tag{22}
\]
To see this, a fixed interpreter gives
\[
M(\beta_{1:n})\ge c'2^{-K(z^{(n)})},
\]
while \(nM(\beta_{1:n})\to0\).

A decisive sufficient construction would therefore be:

> Find one fixed universal \(A\) whose all-error path has infinitely many prefixes satisfying  
> \[
> K(\beta_{1:n}0^\infty)\le C\log_2(n+2).
> \]

Then those computable witnesses would have \(n\) errors at logarithmic description cost, refuting every polynomial for that same \(A\). **No such upper complexity estimate is established here.**

The always-zero component preserves mass but contributes zero to both success scores. Consequently, it does not itself control the actions. This is the remaining distinction between keeping mass alive and making the desired errors cheap.

## 8. The lower bound actually established: linear order

### Theorem 7: every fixed policy has linear worst-case errors

For every deterministic policy \(P\), computable or not, and every \(n\ge2\), there is a computable infinite \(z\) such that
\[
E_P(z)\ge n/2
\]
and
\[
n-K(n)-O(1)
\le K(z)\le
n+K(n)+O(1).
\tag{23}
\]
The coding constants can be independent of \(P,n\).

**Proof.** The map from a truth word \(v\in\{0,1\}^n\) to its error pattern under \(P\) is bijective: given the errors, reconstruct each action from the preceding history, then its reward and truth bit.

At least \(2^{n-1}\) error patterns contain at least \(n/2\) errors. Fewer than \(2^{n-1}\) words have \(K(v)<n-1\). Thus some \(v\) satisfies
\[
E_P(v)\ge n/2,\qquad K(v)\ge n-1.
\]
Let \(z=v0^\infty\). Literal coding proves the upper complexity bound. A generator for \(z\), together with \(n\), prints \(v\) and halts, proving
\[
K(v)\le K(z)+K(n)+O(1)
\]
and hence the lower bound. \(\square\)

Because \(K(n)=O(\log n)\), the witness complexities are \(n+O(\log n)\). Thus an \(o(K(z))\) worst-case upper bound is impossible for any fixed policy.

**Confidence:** high. **Novelty:** standard counting reasoning. This establishes linear necessity, without establishing superlinear necessity.

## 9. Where the attempted exponential construction breaks

Short descriptions of exponentially long candidate sequences are available.

### Lemma 8: finite halting tables have short descriptions

Fix a universal prefix machine. Let \(H_n\) list the halting answers for all inputs of length at most \(n\). Then, for sufficiently large \(n\),
\[
|H_n|=2^{n+1}-1,
\qquad
K(H_n0^\infty)\le n+O(\log n).
\tag{24}
\]

**Proof.** Choose a longest-running halting program \(p_n\) among those of length at most \(n\). Encode \(n\), \(|p_n|\), and \(p_n\). This costs at most \(n+O(\log n)\) bits.

Run \(p_n\) to obtain its halting time \(T\), then simulate every input of length at most \(n\) for \(T\) steps. By maximality, this decides every entry of \(H_n\). Print the table and then zeros. The choice of \(p_n\) need not be computable in \(n\). \(\square\)

**Confidence:** high. **Novelty:** standard finite halting-time description argument.

I examined layers with one spike per program: a default spike favors one action, while a larger opposing spike becomes available when that program halts. Against the complement halting table, the intended predictions would be wrong.

The construction remains incomplete:

- If unused components predict zero reward before their designated cycles, a single correct AI prediction eliminates them together.
- If they copy a universal base before their designated cycles, they survive more histories, but their small weighted contribution need not overcome the base’s correct-action score.
- Short target descriptions and sufficient total mass do not establish the required greedy inequalities.

There is also an obstruction to an easy positive construction. A universal reactive component cannot have equal success scores everywhere. More generally, no universal \(S\) can satisfy
\[
S(h(0,1))\ge cS(h(1,1))
\quad\text{for all }h
\]
with fixed \(c>0\). Along \(h_n=(0,0)^n\), universality for passive truth \(1^\infty\) gives \(S(h_n(1,1))\ge w>0\); the displayed inequality would make \(S(h_n)\) lose at least \(cw\) every cycle, a contradiction. The reverse inequality fails symmetrically.

Thus adding an action-neutral universal reactive component to passive \(M\) cannot implement a simple positive solution. More elaborate constructions remain possible.

A relevant comparison is Hutter’s monotone-complexity predictor: its passive off-sequence bound is polynomial, while adjacent exponential examples change the universal machine with the parameter. That proof does not transfer directly to AI’s different-action comparisons, and its noncomputable predictor cannot serve as the comparator in Theorem 2. [arxiv.org](https://arxiv.org/pdf/cs/0508043?utm_source=chatgpt.com)

## 10. Exact outcome

| Question | Established here |
|---|---|
| One fixed universal prior with superlinear, superpolynomial, or exponential errors in \(K(z)\) | **Not obtained.** Linear-order lower bounds are established; finite layered examples change the machine. |
| Polynomial bound for every universal prior, or for one particular natural prior, in unrestricted \(K(z)\) | **Not obtained.** |
| Polynomial bounds under effective restrictions | **Proved:** near-quadratic transfer from a computable predictor, and near-quadratic bounds in uniformly total-family description length. |
| Can a fixed computable dogmatic policy force superpolynomially many initial errors? | **No:** its initial following segment has an \(O(K(z)+1)\) error bound, with construction-dependent constant. |
| Does mass necessarily disappear at the first mistake? | **No:** every universal prior has an all-error path with positive surviving mass. The missing ingredient is sufficiently short descriptions of its finite truth prefixes. |
| Do Leike–Hutter’s dogmatic priors settle (6.2P)? | **No.** Their prediction-failure discussion explicitly exempts horizon one, and the finite-lifetime constructions do not supply the required fixed-machine quantifiers. |

The principal new positive result is the computable-comparator theorem. The most concrete unresolved negative route is a fixed prior with unusually compressible all-error prefixes. Both isolate the same remaining difficulty: controlling the actual greedy choices while retaining a short description of the passive truth sequence.