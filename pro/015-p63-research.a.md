I proved the four “easy” assertions and obtained a direct counterexample to the final conditional-complexity bound: **that bound fails for every deterministic predictor**, including every fixed universal horizon-one AI predictor.

**I did not settle (6.3N).** I obtained a proved correction to its numerator bound, but neither a proof nor a counterexample for the assertion with no correction. That distinction is explicit below.

The complete research response, including the proofs, constant dependencies, and Lean formalization targets, is in 015-p63-research.a.md[015-p63-research.a.md](sandbox:/workspace/scratch/42e8a0ac4efb/015-p63-research.a.md).

## Results

Write
\[
A=\xi^{AI},\qquad M=\xi^{SP},\qquad
m=k-1,\quad x=z_{<k},\quad y=z_{k:n},
\]
and let \(h_m\) denote the actual action–reward history through cycle \(m\).

| Claim | Result |
|---|---|
| \(A(h)\gtrsim M(d(h))\), uniformly over finite histories | **True** |
| \(A(h)\lesssim M(d(h))\), uniformly over finite histories | **False for every universal \(A,M\)** |
| Total and posterized error bounds | **True:** \((E_{k:n}+1)cM(xy)\le A(h_m)\) |
| (6.3N): \(E_{k:n}\le C M(x)/M(xy)\) | **Unresolved by this work** |
| Corrected sequence-mass bound | **True:** \(E_{k:n}+1\le C(m+1)2^{K(m)}M(x)/M(xy)\) |
| \(E_{k:n}\le C2^{K(y\mid x)}\) | **False for every deterministic predictor** |
| Corrected direct complexity bound | **True:** \(E_{k:n}+1\le C2^{K(m)+K(y\mid x)}\) |

Every positive result has a constant independent of \(n,k,z\). Constants may depend on the fixed universal machines and encodings. The correction factors are sufficient; I do not establish that they are optimal.

These are mathematical proofs, **not Lean-checked results**.

---

## 1. Definitions and conventions

The setup is the binary, observation-free sequence-prediction environment in the supplied book pages, especially equation (6.15) on page 191 and Problem 6.3 on page 208. 015-uai2005-sec6.2-and-problem6.3.pdf

Let \(\mathbb B=\{0,1\}\). A finite history is
\[
h=(a_1,r_1)\cdots(a_t,r_t)\in(\mathbb B\times\mathbb B)^*,
\]
where \(a_i\) is the prediction and \(r_i\) is its binary reward. Decode the truth string by
\[
d(h)_i=
\begin{cases}
a_i,&r_i=1,\\
1-a_i,&r_i=0.
\end{cases}
\]
This is the book’s \(z_i=\delta_{a_i r_i}\).

A chronological semimeasure satisfies
\[
A(\epsilon)\le1,\qquad A(h)\ge0,
\]
and, for every history \(h\) and next action \(a\),
\[
A(h(a,0))+A(h(a,1))\le A(h).
\tag{1}
\]
Here \(h(a,r)\) means appending one cycle. Universality means that \(A\) multiplicatively dominates every lower semicomputable chronological semimeasure.

The sequence semimeasure \(M\) satisfies
\[
M(\epsilon)\le1,\qquad M(w0)+M(w1)\le M(w),
\tag{2}
\]
and is universal among lower semicomputable binary semimeasures.

Fix a deterministic maximizing choice
\[
\pi(h)\in\arg\max_{a\in\mathbb B}A(h(a,1)).
\tag{3}
\]
This is exactly the horizon-one policy. Its unnormalized reward-one score suffices because the conditional denominator is independent of the next action.

For a finite truth string \(z_1\ldots z_n\), define the actual run recursively:
\[
h_0=\epsilon,\qquad
a_i=\pi(h_{i-1}),\qquad
r_i=\mathbf1\{a_i=z_i\},\qquad
h_i=h_{i-1}(a_i,r_i).
\]
Thus \(d(h_i)=z_{1:i}\). Define
\[
E_{k:n}(z)=\sum_{i=k}^{n}\mathbf1\{a_i\ne z_i\}.
\tag{4}
\]
This is an actual error count, not an expectation.

Finally, fix an optimal conditional prefix machine \(V\), with
\[
K_V(y\mid x)=
\min\{|p|:V(p,x)\text{ halts with exact output }y\}.
\tag{5}
\]
The finite condition \(x\) is supplied with its end available. Integers and pairs use fixed computable encodings. Below, \(K\) always means this ordinary conditional prefix complexity.

---

## 2. The comparison \(A\gtrsim M\), and failure of its reverse

### Theorem 1 — Passive-lift domination

For every fixed universal chronological semimeasure \(A\) and lower semicomputable binary semimeasure \(M\), there is \(c=c(A,M)>0\) such that
\[
\forall h,\qquad A(h)\ge cM(d(h)).
\tag{6}
\]

For machine-based definitions, \(c\) may be chosen as \(2^{-d_0}\), where \(d_0\) is a fixed compiler overhead.

**Proof.** Define
\[
L_M(h)=M(d(h)).
\]
For a fixed next action \(a\), the two reward outcomes decode to the two possible truth bits. Hence
\[
\begin{aligned}
L_M(h(a,0))+L_M(h(a,1))
&=M(d(h)0)+M(d(h)1)\\
&\le M(d(h))=L_M(h).
\end{aligned}
\]
The lift is lower semicomputable and has root mass at most one. Universality of \(A\) gives (6).

At the program level, a fixed interpreter runs a sequence generator, obtains each next truth bit, reads the next action, and emits the equality reward. The compiler prefix multiplies the corresponding program mass by \(2^{-d_0}\). ∎

Universal \(M\) dominates the fair-coin measure, so \(M(w)>0\) for every finite \(w\). Consequently, \(A(h)>0\) for every finite history.

**Confidence:** high. **Novelty:** the intended elementary deduction in Problem 6.3.

### Theorem 2 — No uniform reverse comparison on arbitrary histories

For every fixed universal \(A,M\),
\[
\forall C>0\ \exists h:\quad A(h)>CM(d(h)).
\tag{7}
\]
More precisely, there is \(w>0\) such that for every \(n\), some length-\(n\) history satisfies
\[
\frac{A(h)}{M(d(h))}\ge w2^n.
\tag{8}
\]

**Proof.** The computable environment that always returns reward \(1\), independently of actions, has a fixed positive weight \(w\) in \(A\). Therefore
\[
A((a_1,1)\cdots(a_n,1))\ge w
\]
for every action string \(a\).

The level-mass inequality gives
\[
\sum_{a\in\mathbb B^n}M(a)\le1.
\]
Some \(a\) therefore satisfies \(M(a)\le2^{-n}\). For its all-reward-one history \(h\), we have \(d(h)=a\), establishing (8). Choosing \(n\) sufficiently large proves (7). ∎

**Essential quantifier distinction:** these are arbitrary histories. The proof does not establish reverse-comparison failure along the greedy policy’s own histories. It therefore does **not** refute (6.3N).

**Confidence:** high. **Novelty:** standard separation.

---

## 3. The exact finite error budget

### Lemma 3 — Weighted mass decrease

For every nonnegative chronological semimeasure \(A\), every policy satisfying (3), every finite truth string, and every \(1\le k\le n\),
\[
\sum_{i=k}^{n}
\mathbf1\{a_i\ne z_i\}
A(h_{i-1}(z_i,1))
\le A(h_{k-1})-A(h_n).
\tag{9}
\]

This statement requires neither universality nor computability.

**Proof.** Every actual step satisfies
\[
A(h_i)\le A(h_{i-1}).
\]
If step \(i\) is erroneous, the actual reward is zero, so
\[
\begin{aligned}
A(h_{i-1})-A(h_i)
&\ge A(h_{i-1}(a_i,1))\\
&\ge A(h_{i-1}(z_i,1)).
\end{aligned}
\tag{10}
\]
The first inequality uses the chronological semimeasure property; the second uses greediness. Summing these inequalities, with a zero contribution on correct steps, telescopes to (9). ∎

### Theorem 4 — Total and posterized error bounds

Fix \(c>0\) satisfying (6). Then
\[
\forall n\ge1\ \forall z\in\mathbb B^n\
\forall 1\le k\le n:
\qquad
\boxed{
(E_{k:n}(z)+1)cM(z_{1:n})\le A(h_{k-1}).
}
\tag{11}
\]
In particular,
\[
E_{k:n}(z)\le
\frac{A(h_{k-1})}{cM(z_{1:n})},
\tag{12}
\]
and
\[
E_n(z)+1\le\frac1{cM(z_{1:n})}.
\tag{13}
\]

**Proof.** The correct-action counterfactual \(h_{i-1}(z_i,1)\) decodes to \(z_{1:i}\). Thus
\[
A(h_{i-1}(z_i,1))
\ge cM(z_{1:i})
\ge cM(z_{1:n}),
\]
using prefix monotonicity of \(M\).

Put \(\alpha=cM(z_{1:n})>0\). Lemma 3 gives
\[
\alpha E_{k:n}\le A(h_{k-1})-A(h_n).
\]
The actual terminal history also satisfies \(A(h_n)\ge\alpha\). Hence
\[
\alpha(E_{k:n}+1)\le A(h_{k-1}).
\]
For the total bound, use \(A(h_0)\le1\). ∎

This proves both requested error bounds with the same constant \(C=1/c\). The extra \(+1\) comes from retaining terminal mass instead of discarding it.

**Confidence:** high. **Novelty:** the intended mass-decrease argument, with an elementary strengthening.

---

## 4. The final direct conditional-complexity bound is false

Here is an error-count counterexample that does not rely on a failed probability-ratio bound.

### Theorem 5 — Failure for every deterministic predictor

For every optimal conditional prefix machine \(V\), there is a constant \(b_V\) such that
\[
\forall P:\mathbb B^*\to\mathbb B\ \forall d\ge1\
\exists x,y:
\qquad
K_V(y\mid x)\le b_V,\qquad E_P(x,y)\ge d-1.
\tag{14}
\]
Here \(E_P(x,y)\) counts errors while predicting \(y\) after observing \(x\).

Consequently, for every deterministic predictor \(P\),
\[
\neg\left[
\exists C<\infty\ \forall x,y:
E_P(x,y)\le C2^{K_V(y\mid x)}
\right].
\tag{15}
\]

No computability assumption on \(P\) is needed.

### Proof

Fix \(P\) and \(d\), and set
\[
N=2^d.
\]
Construct a \(d\)-bit word \(b=b_1\ldots b_d\) by
\[
b_1=1,\qquad
b_j=1-P(0^N b_{1:j-1})
\quad(2\le j\le d).
\tag{16}
\]
Thus, on the full string \(0^N b\), the last \(d-1\) bits of \(b\) are all predicted incorrectly.

Let \(m\) be the integer whose ordinary binary representation is \(b\). Since \(b\) starts with \(1\),
\[
2^{d-1}\le m<2^d=N,
\qquad \operatorname{bin}(m)=b.
\]
Now split the completed string at position \(m\):
\[
x=0^m,\qquad
y=0^{N-m}b,\qquad
xy=0^N b.
\tag{17}
\]
All \(d-1\) deliberately incorrect predictions occur in the suffix \(y\), so
\[
E_P(x,y)\ge d-1.
\tag{18}
\]

Nevertheless, one fixed program computes \(y\) from \(x\):

1. Read \(m=|x|\).
2. Compute \(b=\operatorname{bin}(m)\).
3. Compute \(d=|b|\) and \(N=2^d\).
4. Output \(0^{N-m}b\) and halt.

This defines a fixed total computable function \(F\), with an arbitrary fixed output at the empty input. It does not depend on \(P\) or \(d\). Therefore
\[
K_V(y\mid x)=K_V(F(x)\mid x)\le b_V
\tag{19}
\]
for one fixed constant.

Taking \(d-1>C2^{b_V}\) contradicts any proposed bound with constant \(C\). ∎

### Why this applies to the AI policy

A deterministic AI policy induces the mathematical predictor
\[
P(u)=\pi(h_\pi(u)),
\]
where \(h_\pi(u)\) is reconstructed recursively from the truth prefix \(u\). This definition is valid even if the policy is incomputable.

There is also no effectiveness gap in the witness construction. The adverse word \(b\) is selected by finite recursion against the mathematical predictor. The short conditional program does not compute that recursion: it reads the resulting word from the binary expansion of the prefix length.

The cut is chosen retrospectively. That is permitted by the proposed quantifier
\[
\forall n,z,k.
\]

Each finite witness can be hardcoded and extended by zeros, so the refutation also applies when the finite strings must occur in computable infinite deterministic environments. It does not produce one computable environment on which the universal predictor makes infinitely many errors.

### Complexity conventions and quantitative consequence

The same witnesses satisfy
\[
K(y\mid |x|)=O(1),\qquad K(y\mid h_m)=O(1),
\]
because either condition gives \(m\). They also refute the version using ordinary monotone output complexity with a finite, end-marked condition.

They do **not** establish bounded complexity for the distinct \(K_*(\,\cdot\mid x*)\) notion monotone in its condition. That distinction is central in the Chernov–Hutter work. [arxiv.org](https://arxiv.org/pdf/cs/0701120?utm_source=chatgpt.com)

The witnesses have
\[
k=m+1\le2^d,\qquad
E_{k:n}\ge d-1\ge\log_2 k-1.
\]
Therefore no correction of the form
\[
E_{k:n}\le Cg(k)2^{K(y\mid x)}
\]
can hold with \(g(k)=o(\log k)\).

**Confidence:** high; independently checked. **Novelty:** proof supplied here; publication priority unclaimed.

---

## 5. A direct corrected bound by restarting the environment

The following construction also supplies the corrected numerator theorem later.

### Lemma 6 — General chronological restart bound

Fix universal \(A\), prefix complexity \(K\), and a uniformly lower semicomputable conditional binary semimeasure \(Q(v\mid x)\) satisfying
\[
Q(\epsilon\mid x)\le1.
\]
There is a constant \(c_Q>0\) such that, for every finite greedy run, every split \(z=xy\), and \(m=|x|\), with \(|y|\ge1\),
\[
\boxed{
(E_\pi(x,y)+1)c_Q2^{-K(m)}Q(y\mid x)\le1.
}
\tag{20}
\]

### Proof

For each \(m\), define
\[
R_m(h)=
\begin{cases}
A(h),&|h|\le m,\\[1mm]
A(h_{\le m})
Q(d(h_{>m})\mid d(h_{\le m})),&|h|>m.
\end{cases}
\tag{21}
\]

This is a lower semicomputable chronological semimeasure:

- Before the switch, it inherits the inequality from \(A\).
- At the switching node, the total child mass is at most
  \[
  A(h)\bigl(Q(0\mid d(h))+Q(1\mid d(h))\bigr)\le A(h).
  \]
- Afterwards, it inherits the suffix semimeasure inequality from \(Q\).

By Kraft’s inequality,
\[
R=\sum_{m\ge0}2^{-K(m)}R_m
\]
is a lower semicomputable chronological semimeasure. Universality gives
\[
A(g)\ge c_Q2^{-K(m)}R_m(g)
\quad\text{for all }m,g.
\tag{22}
\]

Fix the actual prefix history \(h_m\). Every correct-action reward-one counterfactual in the tail has decoded continuation equal to a prefix of \(y\). Therefore its \(A\)-mass is at least
\[
L=c_Q2^{-K(m)}A(h_m)Q(y\mid x).
\]
The terminal actual history has the same lower bound. Lemma 3 yields
\[
(E_\pi(x,y)+1)L\le A(h_m).
\]
Cancel \(A(h_m)>0\), proving (20). ∎

Using \(A\) inside \(R_m\) is not circular: \(A\) is a fixed lower semicomputable function, and the construction operates on its fixed enumeration.

### Theorem 7 — Corrected direct conditional-complexity bound

For every fixed universal \(A\) and optimal conditional prefix machine \(V\), there is \(C_{A,V}>0\) such that
\[
\forall n,z,k,\quad
\boxed{
E_{k:n}(z)+1
\le
C_{A,V}\,
2^{K(k-1)+K(z_{k:n}\mid z_{<k})},
}
\tag{23}
\]
where \(n\ge1\), \(z\in\mathbb B^n\), and \(1\le k\le n\).

**Proof.** Use the conditional output-prefix semimeasure
\[
Q(v\mid x)=
\sum_{\substack{p:\,V(p,x)\text{ halts}\\
v\preceq V(p,x)}}2^{-|p|}.
\]
For each \(x\), the halting program domain is prefix-free, so its root mass is at most one. A shortest program for \(y\) contributes, giving
\[
Q(y\mid x)\ge2^{-K(y\mid x)}.
\]
Apply Lemma 6 with \(C_{A,V}=c_Q^{-1}\). ∎

The computable conversions between \(k-1\) and \(k\) allow \(K(k-1)\) to be replaced by \(K(k)\), changing only the constant.

This is a direct error-count theorem. It does not pass through \(M(x)/M(xy)\).

**Confidence:** high. **Novelty:** a chronological application of the splice-and-mixture method; priority unclaimed. The established sequence-prediction likelihood bounds with a \(K(|x|)\) correction are in Chernov–Hutter, Theorem 1. [hutter1.net](https://www.hutter1.net/ai/postbnd.pdf?utm_source=chatgpt.com)

---

## 6. The numerator question and a proved correction

### What remains unresolved

I do not have a valid proof or counterexample for
\[
\exists C>0\ \forall n,z,k:
\qquad
E_{k:n}(z)\le C\frac{M(z_{<k})}{M(z_{1:n})}.
\tag{N}
\]

Two tempting arguments do not settle it:

- The failure of \(A(h)\lesssim M(d(h))\) concerns arbitrary histories, not necessarily the greedy policy’s actual histories.
- The direct conditional-complexity counterexample does not refute a probability-ratio bound. Those two bounds are different assertions.

A useful precise sufficient condition is the following.

### Lemma 8 — Policy pullback

For any deterministic policy \(\pi\),
\[
A_\pi(u):=A(h_\pi(u))
\]
is a binary semimeasure. If \(A\) is lower semicomputable and \(\pi\) is computable, then \(A_\pi\) is lower semicomputable, and hence
\[
\exists d_\pi>0\ \forall u:
\qquad M(u)\ge d_\pi A_\pi(u).
\tag{24}
\]
More generally, (24) itself, together with Theorem 4, implies (N) with \(C=(cd_\pi)^{-1}\).

**Proof.** At a fixed truth prefix, the policy chooses one action. The two possible next truth bits correspond to the two reward branches for that same action, giving the semimeasure inequality. A computable policy makes the history transformation computable, proving the effectivity assertion. Then apply universality of \(M\). ∎

The actual greedy universal policy cannot simply be assumed computable. Otherwise choosing the opposite truth bit recursively would produce a computable infinite sequence with an error at every step, contradicting Theorem 4 and the positive fixed mass of that sequence.

### Lemma 9 — Effective capping

There is a uniformly lower semicomputable conditional semimeasure \(T(v\mid x,j)\), for \(j\in\mathbb N\), with root at most one and the property
\[
2^jM(x)\le1
\quad\Longrightarrow\quad
T(v\mid x,j)=2^jM(xv)
\quad\text{for every }v.
\tag{25}
\]

**Proof.** Choose increasing computable rational semimeasures \(M_s\uparrow M\), starting with \(M_0=0\).

For fixed \(x,j\), follow the scaled semimeasures
\[
v\longmapsto2^jM_s(xv)
\]
while their root is at most one. At the first stage with
\[
2^jM_s(x)>1,
\]
freeze permanently at the preceding accepted **whole semimeasure**.

All accepted stages are semimeasures with root at most one. Values increase before freezing and remain constant afterwards. The strict crossing test is decidable at each rational stage. If \(2^jM(x)\le1\), no crossing occurs, proving exactness.

The approximation presentation exists for the book’s monotone-machine \(M\) by finite simulation. For a general lower semicomputable semimeasure, construct it from rational lower approximations on finite trees: assign each internal node the maximum of its own lower approximation and the sum of its two children. These finite-tree semimeasures increase to \(M\) and never exceed it. ∎

### Theorem 10 — Corrected numerator bound

For every fixed universal \(A,M\) and optimal conditional prefix machine \(V\), there are constants \(C_1,C_2>0\) such that for every valid \(n,z,k\), putting
\[
m=k-1,\qquad x=z_{<k},\qquad y=z_{k:n},
\]
and choosing \(q=q(x)\ge0\) by
\[
2^{-q-1}<M(x)\le2^{-q},
\tag{26}
\]
one has
\[
\boxed{
E_{k:n}+1
\le
C_1\,2^{K(m)+K(q\mid x)}
\frac{M(x)}{M(xy)}
\le
C_2(m+1)2^{K(m)}
\frac{M(x)}{M(xy)}.
}
\tag{27}
\]

### Proof

Using Lemma 9, define
\[
S(v\mid x)=
\sum_{j\ge0}2^{-K(j\mid x)}T(v\mid x,j).
\tag{28}
\]
Conditional Kraft gives
\[
\sum_j2^{-K(j\mid x)}\le1.
\]
Thus \(S\) is a uniformly lower semicomputable conditional semimeasure with root at most one.

Apply Lemma 6 to \(S\):
\[
(E_{k:n}+1)c_S2^{-K(m)}S(y\mid x)\le1.
\tag{29}
\]
For the \(q\) in (26),
\[
\tfrac12<2^qM(x)\le1,
\]
so the exact branch of Lemma 9 gives
\[
\begin{aligned}
S(y\mid x)
&\ge2^{-K(q\mid x)}2^qM(xy)\\
&\ge\tfrac12\,2^{-K(q\mid x)}
\frac{M(xy)}{M(x)}.
\end{aligned}
\]
Substitution proves the first inequality with \(C_1=2/c_S\).

For the second, universality over the fair-coin measure supplies a fixed integer \(b\ge0\) such that
\[
M(x)\ge2^{-b-|x|}.
\]
Hence \(q\le m+b\). Given \(x\), a conditional program already knows \(m=|x|\). It can read \(q\) from a fixed-width field of length
\[
\left\lceil\log_2(m+b+1)\right\rceil.
\]
Therefore
\[
K(q\mid x)\le
\left\lceil\log_2(m+b+1)\right\rceil+O_{M,V}(1),
\]
and
\[
2^{K(q\mid x)}\le C_{M,V}(m+1).
\]
This proves the second inequality. ∎

Equivalently, after changing the constant,
\[
\boxed{
E_{k:n}
\le C\,k\,2^{K(k)}
\frac{M(z_{<k})}{M(z_{1:n})}.
}
\tag{30}
\]

An alternative refined formulation is
\[
E_{k:n}+1\le
C'\,2^{K(m,q)}\frac{M(x)}{M(xy)}.
\tag{31}
\]
It follows by mixing restart environments indexed by \((m,j)\) with weights \(2^{-K(m,j)}\).

The selected \(q\) need not be computable from \(x\): the effective construction includes every \(j\), and the proof selects the appropriate one afterwards. This avoids treating \(M(xy)/M(x)\) as a lower semicomputable conditional semimeasure.

**Scope:** these are sufficient corrections. They do not prove that (N) is false, and they do not establish that \(2^{K(k)}\) alone suffices.

**Confidence:** high; independently derived and audited. **Novelty:** proofs supplied here; priority unclaimed.

---

## 7. Lean formalization targets

The useful separation is between **finite error accounting** and **effective universal-machine instantiation**.

Use
```lean
abbrev Bit := Bool
abbrev Hist := List (Bit × Bit)

def decode (h : Hist) : List Bit :=
  h.map (fun ar => if ar.2 then ar.1 else !ar.1)
```

Take
\[
A:\texttt{Hist}\to\mathbb R,\qquad
M:\texttt{List Bool}\to\mathbb R,
\]
with explicit nonnegativity, root bounds, and child-sum inequalities. A policy is `Hist → Bool`; its greediness hypothesis is
\[
\forall h,a,\quad
A(h\mathbin{++}[(a,\mathrm{true})])
\le
A(h\mathbin{++}[(\pi(h),\mathrm{true})]).
\]

The following are theorem specifications, not a claimed compiling Lean file.

| Result | Finite statement to formalize | Additional facts for the universal conclusion |
|---|---|---|
| Passive lift | \(h\mapsto M(d(h))\) is chronological whenever \(M\) is a binary semimeasure | Lower semicomputability under computable precomposition; universal domination |
| Reverse comparison | If \(A(a,1^n)\ge w>0\), then for every \(n\) some corresponding history has \(M(d(h))\le2^{-n}\) | Constant-reward environment belongs to the universal class |
| Weighted budget | Equation (9) for every finite greedy run | None |
| Posterization | Assuming \(c>0\) and \(cM(d(h))\le A(h)\), prove \((E+1)cM(xy)\le A(h_\pi(x))\) | Passive-lift domination |
| Restart | Equation (21) preserves chronological semimeasures | Effectivity of products and uniform constructions |
| Local restart bound | If \(A\ge\eta R_m\) and \(A(h_m)>0\), prove \((E+1)\eta Q(y\mid x)\le1\) | Kraft-weighted mixture and universality |
| Direct counterexample | For every \(P\) and \(d\ge1\), construct \(m\in[2^{d-1},2^d)\) with \(E_P(0^m,F(0^m))\ge d-1\) | A fixed computable decoder has bounded conditional description length |
| Capping | The accept/freeze sequence is increasing, has root at most one, and is exact when safe | Rational semimeasure approximation and lower semicomputability |
| Corrected numerator | Instantiate the local restart bound with the capped conditional mixture | Conditional Kraft, coding of \(q\), and fair-coin domination |

The finite proofs need Boolean case splits, list take/drop/append identities, prefix monotonicity, finite sums, telescoping, and ordered-field arithmetic. The direct counterexample additionally needs binary-value/binary-expansion inverses and their length bounds. It can instead use an abstract bijection
\[
\mathbb B^{d-1}\longleftrightarrow
\{m:2^{d-1}\le m<2^d\}
\]
to separate the argument from binary-digit library conventions.

For the effective layer, the required interfaces include:

- Universality for sequence and chronological semimeasures.
- Closure of lower semicomputability under nonnegative products and effective sums.
- Unconditional and conditional Kraft inequalities.
- The conditional output-prefix kernel and its shortest-program lower bound.
- Constant conditional description length for a fixed computable function.
- Fixed-width integer coding and constant-cost conversion between \(k\) and \(k-1\).

I have not assumed that all those interfaces already exist in your current Lean library. The best initial finite targets are Lemma 3, Theorem 4, and the combinatorial part of Theorem 5.

---

## 8. Sources and research status

The relevant primary sources opened were:

- **Hutter, *Universal Artificial Intelligence* (2005)**, DOI **10.1007/b138233**: the supplied pages provide the definitions and intended elementary argument. The identifier is also listed on the author’s book page. [hutter1.net](https://www.hutter1.net/ai/uaibook.htm?utm_source=chatgpt.com)
- **Chernov–Hutter, “Monotone Conditional Complexity Bounds on Future Prediction Errors”**, **arXiv:cs/0507041**: the established length-corrected posterior likelihood bound and its relationship to Problem 6.3. [arxiv.org](https://arxiv.org/abs/cs/0507041?utm_source=chatgpt.com)
- **Chernov–Hutter–Schmidhuber, “Algorithmic Complexity Bounds on Future Prediction Errors”**, **arXiv:cs/0701120**, DOI **10.1016/j.ic.2006.10.004**: the extended treatment of posterior bounds and complexity monotone in the condition. [arxiv.org](https://arxiv.org/abs/cs/0701120?utm_source=chatgpt.com)
- **Hutter, “Open Problems in Universal Induction & Intelligence” (2009)**, DOI **10.3390/a2030879**: Section 5(h) discusses the obstacles to naive posterization. [hutter1.net](https://www.hutter1.net/ai/aixiopen.pdf?utm_source=chatgpt.com)
- **Leike–Hutter, “Bad Universal Priors and Notions of Optimality”**, **arXiv:1510.04931**: its discussion explicitly exempts horizon-one sequence prediction from the dogmatic-prior failure argument. Those examples therefore cannot simply be imported as a counterexample to (6.3N). [arxiv.org](https://arxiv.org/abs/1510.04931?utm_source=chatgpt.com)

The author’s current book page lists Problem 6.3 without a cited solution. That is evidence about the page, not proof that no solution exists elsewhere. [hutter1.net](https://www.hutter1.net/ai/uaibook.htm?utm_source=chatgpt.com)

**The precise remaining gap is (6.3N):** proving or refuting the uncorrected sequence-mass numerator bound. The direct conditional-complexity proposal is refuted, and the two corrected bounds above are proved, but neither result closes that gap.