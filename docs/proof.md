# A tower obstruction for Erdős #197: drifting near-dyadic run colourings fail (partial result)

*Partial progress on [Erdős Problem #197](https://www.erdosproblems.com/197). The problem itself remains open, and this note does not solve it.*

## Background

**Problem (Erdős–Graham).** Can $\mathbb N$ be partitioned into two sets, each of which admits an enumeration (a listing of order type $\omega$) with no monotone 3-term arithmetic progression? Call $S\subseteq\mathbb N$ *permutable* if it has such an enumeration.

Davis, Entringer, Graham and Simmons (1977) showed that $\mathbb N$ itself is not permutable. W. Kasel (arXiv:2609.02939, 2026, Theorem 21) showed that the dyadic partition fails, using a finite *order gadget* and a toolkit of ladder lemmas (zigzag and flood, his Lemmas 23–26). Theorem I below, proved and formalized in [Alex-lop/erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget), is a sharp anchored version of that gadget. Pulled back along an affine map (Lemma W\* below) it says: if $w,w+\delta\in S$ and a block $w+\delta[M,2M+6]$ ($M\ge8$) lies in $S$, then in every admissible order some element of that block comes before $w$ or before $w+\delta$.

This note proves that a set containing a suitable *tower* of intervals is not permutable (Theorem R\*). The new ingredient is Lemma S: five overlapping Theorem-I blocks inside one interval produce a new *pair* $w',w'+\delta'$ of that interval, both listed before the later of $w,w+\delta$. Iterating from interval to interval makes the position of the later element of the pair decrease at every level, which is impossible for more than finitely many levels. As a consequence (Corollary R2\*), every colouring of $[r_0,\infty)$ by alternating runs $[r_k,r_{k+1})$ with $r_{k+1}/r_k\to2$ fails for both colours, with no assumption on the enumeration (no lag hypothesis) and no assumption on the speed of convergence. Kasel's dyadic partition, with blocks $(2^k,2^{k+1}]$, is the special case $r_k=2^k+1$.

The main statements of Sections 2–6 (Lemma W\*, Lemma S, Theorem R\*, Corollary R0\* and the colouring sentence of Corollary R2\*) are formalized in Lean 4 in this repository (Section 8); the remarks are not.

This note is a rewrite of the refereed text, the project's working note `work/p197_m2_r2/verify_Rstar/repair1/proof.md` (not included in this repository; Section 9 has its history). The following parts are not in the refereed text, so they were not refereed:

* the proof of Corollary R2\* by R0\* applied to every fourth run (every other run of colour $c$), with $\varepsilon=1/100$ (Section 6). The refereed text derives R2\* from its general second sentence, through a Corollary R1\* that uses every eighth run;
* the invariants of Theorem R\* (Section 4): (J3) here is "the hypotheses of Lemma S hold for $(w_k,\delta_k)$ and $I_{k+1}$", while the refereed (J3) is "$\alpha_k\le w_k$ and $w_k+\delta_k\le\beta_k$". (J2) here has the weaker lower bound $\delta_k\ge1$ in place of $\delta_k\ge d$;
* the steps of the proof of Corollary R0\* (Section 5). The refereed text proves R0\* in steps R0a–R0g.

Each of these parts is mirrored by the kernel-checked Lean proof (`ratio_bounds`, `six_terms` and `drifting_adm`; `tower_levels`; `clean_adm`, whose arithmetic steps are `omega` calls).

## 0. Setting and conventions

* $S\subseteq\mathbb N$. Integer intervals are $[p,q]=\{p,p+1,\dots,q\}$ (empty when $q<p$). For integers $w$, $\delta\ge1$ and $p\le q$, the *AP-block* $w+\delta[p,q]$ is $\{w+\delta k:\ p\le k\le q\}$.
* A *3-AP* of $S$ is a triple $x<y<z$ in $S$ with $x+z=2y$.
* A linear order $\prec$ of $S$ is *admissible* if no 3-AP $x<y<z$ of $S$ satisfies $x\prec y\prec z$ or $z\prec y\prec x$. Equivalently (**midpoint rule**): for every 3-AP $x<y<z$ of $S$, $y\prec x\iff y\prec z$.
* An order has *type $\omega$* if every element has finitely many predecessors. Then $\operatorname{pos}(v)=\#\{s\in S:\ s\prec v\}\in\mathbb N$ is injective and $s\prec s'\iff\operatorname{pos}(s)<\operatorname{pos}(s')$.
* $S$ is *permutable* if it has an admissible order of type $\omega$. For infinite $S$ this is exactly the condition of Erdős #197 and of formal-conjectures (`ErdosProblems/197.lean`): a bijection $f:\mathbb N\simeq S$ with $\neg\,\mathrm{HasMonotoneAP}(\mathrm{Subtype.val}\circ f)\ 3$, and then $\operatorname{pos}=f^{-1}$.
* For distinct $x,y\in S$, $\max_\prec(x,y)$ is the $\prec$-later of the two.
* The *deficit* of an interval $I=[\alpha,\beta]$ is $D(I)=2\alpha-\beta$ (an integer, possibly negative).

The refereed text states Lemma W\*, Lemma S, Theorem R\* and Corollary R0\* for $S\subseteq\mathbb Z$ (with integer $w$, $u$, $\alpha_k$, $\beta_k$, $a_j$, $b_j$). This note and the Lean statements work over $\mathbb N$, the case of Erdős #197. The arguments of Sections 2–5 work verbatim over $\mathbb Z$. The $\mathbb Z$ forms of R\* and R0\* also follow from the $\mathbb N$ forms: restrict the order to the tower, then translate the tower into $\mathbb N$. That reduction is not proved in Lean.

## 1. The core: Theorem I

**Theorem I.** Let $M\ge8$. There is no admissible linear order $\prec'$ of $G=[M,2M+6]$ satisfying the eight *anchor constraints*
$$U(j,a):\qquad 2(M+j)-a\ \prec'\ M+j\qquad (j\in\{0,1,2,3\},\ a\in\{0,1\}).$$

The proof (zigzag and flood lemmas, then 16 cases: $M\bmod 8$ times the leading parity) is Sections 1–4 of `docs/proof.md` of [Alex-lop/erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget). Its Lean proof is `Erdos197Interval/Basic.lean`, which this repository contains verbatim (same file, same namespace). The theorem used below is `Erdos197Interval.gadget_thm`:

```lean
theorem gadget_thm (M : ℕ) (hM : 8 ≤ M) (σ : ℕ → ℕ)
    (hσ : Set.InjOn σ (Set.Icc M (2 * M + 6)))
    (hAP : ∀ x y z : ℕ, x ∈ Set.Icc M (2 * M + 6) → z ∈ Set.Icc M (2 * M + 6) →
      x < y → y < z → y - x = z - y →
        ¬ (σ x < σ y ∧ σ y < σ z) ∧ ¬ (σ z < σ y ∧ σ y < σ x)) :
    ¬ ∀ j a : ℕ, j ≤ 3 → a ≤ 1 → σ (2 * (M + j) - a) < σ (M + j)
```

Here $x$ comes before $y$ when $\sigma x<\sigma y$.

## 2. The witness lemma

**Lemma W\*.** Let $\prec$ be an admissible linear order of $S$, of any order type (in Lean, an injective ranking; see the note after the proof). Let $w\in\mathbb N$, $\delta\ge1$, $M\ge8$ with $w,\,w+\delta\in S$ and $w+\delta[M,2M+6]\subseteq S$. Then there are $j\in\{0,1,2,3\}$ and $a\in\{0,1\}$ with
$$w+\delta(M+j)\ \prec\ w+\delta a .$$
In particular some element of $w+\delta[M,M+3]$ precedes $\max_\prec(w,w+\delta)$.

*Proof.*
1. $\psi(k)=w+\delta k$ is strictly increasing and maps 3-APs to 3-APs: $\psi(x)+\psi(z)-2\psi(y)=\delta(x+z-2y)$. Also $\psi(G)\subseteq S$ for $G=[M,2M+6]$.
2. Define $k\prec'k'$ on $G$ by $\psi(k)\prec\psi(k')$. As $\psi$ is injective, $\prec'$ is a linear order of $G$.
3. $\prec'$ is admissible: a 3-AP $k<k'<k''$ of $G$ maps to the 3-AP $\psi(k)<\psi(k')<\psi(k'')$ of $S$, which is not monotone in $\prec$.
4. By Theorem I some $U(j,a)$ fails: $2(M+j)-a\prec' M+j$ is false.
5. $2(M+j)-a$ and $M+j$ both lie in $G$ (as $M\ge8$, $j\le3$, $a\le1$) and are distinct, so $M+j\prec'2(M+j)-a$, i.e. $y\prec z$ for $y:=\psi(M+j)$, $z:=\psi(2(M+j)-a)$.
6. $x:=\psi(a)\in\{w,w+\delta\}\subseteq S$, $x<y<z$ (as $a<M+j<2(M+j)-a$) and $x+z=2y$.
7. The midpoint rule turns $y\prec z$ into $y\prec x$. $\square$

*In Lean* (`witness`, and `step` for Lemma S below), the order is not arbitrary. It is given by an injective ranking $\rho:\mathbb N\to\mathbb N$ on $S$, so it is an order that embeds in $\omega$ (of type $\omega$, or finite). That is all Theorem R\* needs. The versions for an arbitrary order type follow by restricting $\prec$ to the finitely many points involved. That step is not done in Lean.

**Corollary I\*** (for orientation; the case $\delta=1$ is Corollary I of the interval-gadget repository, `Erdos197Interval.main_result` there and `Erdos197Interval.corollary` in the copied module). If $S$ is permutable and $v,v+\delta\in S$, only finitely many $K\ge8$ satisfy $v+\delta[K,2K+6]\subseteq S$: otherwise pairwise disjoint blocks $v+\delta[K_i,K_i+3]$ would each contain an element of position below $\max(\operatorname{pos}v,\operatorname{pos}(v+\delta))$. Corollary I\* is not used in the proofs below (Section 6 cites it for some of Kasel's schedules).

## 3. One step of the tower

**Lemma S.** Let $\prec$ be an admissible linear order of $S$, of any order type (in Lean, an injective ranking, as for Lemma W\*). Let $w\in\mathbb N$, $\delta\ge1$, $w,w+\delta\in S$, and let $I=[\alpha,\beta]\subseteq S$ satisfy
$$\text{(a)}\ \ \alpha\ge w+8\delta,\qquad\text{(b)}\ \ w\ge D(I)+16\delta\ \ (\text{i.e. }\beta\ge2\alpha-w+16\delta).$$
Then there are $w'$ and $e\in\{1,2,3,4\}$ such that, with $\delta':=e\delta$:
(i) $\alpha\le w'<w'+\delta'\le\beta$, so $w',w'+\delta'\in I\subseteq S$;
(ii) $\delta\le\delta'\le4\delta$;
(iii) both $w'$ and $w'+\delta'$ precede $\max_\prec(w,w+\delta)$; hence $\max_\prec(w',w'+\delta')\prec\max_\prec(w,w+\delta)$.

*Proof.*
1. Let $M:=\lceil(\alpha-w)/\delta\rceil$, so (S0) $\alpha\le w+\delta M<\alpha+\delta$, and (S1) $M\ge8$ by (a).
2. Every $w+\delta k$ with $M\le k\le 2M+14$ lies in $I$: the lower end by (S0), and $w+\delta k\le w+\delta(2M+14)=2(w+\delta M)-w+14\delta<2\alpha-w+16\delta\le\beta$ by (S0) and (b).
3. Hence for $t\in\{0,\dots,4\}$ the blocks $X_t:=w+\delta[M+t,\,2(M+t)+6]$ lie in $I\subseteq S$, and $M+t\ge8$. Lemma W\* with $M+t$ in place of $M$ gives $j_t\le3$, $a_t\le1$ with $y_t:=w+\delta m_t\prec w+\delta a_t$, where $m_t:=M+t+j_t\in[M+t,M+t+3]$.
4. $m_4\ge M+4>M+3\ge m_0$, so $m_t\ne m_{t+1}$ for some $t\in\{0,\dots,3\}$; fix one. Then $-2\le m_{t+1}-m_t\le4$ and $m_t,m_{t+1}\in[M,M+7]$.
5. Let $m^*:=\min(m_t,m_{t+1})$, $e:=|m_{t+1}-m_t|\in\{1,2,3,4\}$, $w':=w+\delta m^*$ and $\delta':=e\delta$. Then $\{w',w'+\delta'\}=\{y_t,y_{t+1}\}$, which lies in $I$ by step 2 (as $M+7\le2M+14$); this gives (i), and (ii) is $1\le e\le4$.
6. (iii): $y_t\prec w+\delta a_t$ and $y_{t+1}\prec w+\delta a_{t+1}$, and both right-hand sides are in $\{w,w+\delta\}$, hence equal to or before $\max_\prec(w,w+\delta)$. $\square$

## 4. Theorem R\*

**Theorem R\*.** Let $S\subseteq\mathbb N$. Suppose there are $u,d\in\mathbb N$ with $d\ge1$ and $u,u+d\in S$, and intervals $I_k=[\alpha_k,\beta_k]\subseteq S$ $(k\ge1)$ with deficits $D_k:=2\alpha_k-\beta_k$, such that
$$\text{(T1*)}\quad \alpha_1\ge u+8d\ \text{ and }\ u\ge D_1+16d;\qquad
\text{(T2*)}\quad \alpha_{k+1}\ge\beta_k+8\cdot4^kd\ \text{ and }\ \alpha_k\ge D_{k+1}+16\cdot4^kd\ \ (k\ge1).$$
Then $S$ is not permutable.

Without subtraction: $u+8d\le\alpha_1$, $2\alpha_1+16d\le u+\beta_1$, $\beta_k+8\cdot4^kd\le\alpha_{k+1}$ and $2\alpha_{k+1}+16\cdot4^kd\le\alpha_k+\beta_{k+1}$. These are the hypotheses `hT1a`, `hT1b`, `hT2a`, `hT2b` of `Erdos197Tower.tower`. They force every $I_k$ to be nonempty: $\beta_1\ge2\alpha_1-u+16d\ge\alpha_1+24d$ and $\beta_{k+1}\ge2\alpha_{k+1}-\alpha_k+16\cdot4^kd>\alpha_{k+1}$.

*Proof.* Let $\prec$ be an admissible order of $S$ of type $\omega$. We show by induction on $k\ge0$ that there are $w_k,\delta_k$ with
(J1) $w_k,\,w_k+\delta_k\in S$; (J2) $1\le\delta_k\le4^kd$; (J3) the hypotheses (a), (b) of Lemma S hold for the pair $(w_k,\delta_k)$ and the interval $I_{k+1}$; (J4) $P_k+k\le P_0$, where $P_k:=\max(\operatorname{pos}w_k,\operatorname{pos}(w_k+\delta_k))$.

*Base.* $w_0=u$, $\delta_0=d$; (J3) is (T1\*).

*Step $k\to k+1$.* Lemma S, applied to $(w_k,\delta_k)$ and $I_{k+1}$, gives $(w_{k+1},\delta_{k+1}):=(w',\delta')$ with $\alpha_{k+1}\le w_{k+1}$, $w_{k+1}+\delta_{k+1}\le\beta_{k+1}$ and $\delta_k\le\delta_{k+1}\le4\delta_k$. So (J1) holds, and (J2) holds since $4\delta_k\le4^{k+1}d$. For (J3) at level $k+1$:
- (a): $\alpha_{k+2}\ge\beta_{k+1}+8\cdot4^{k+1}d\ge(w_{k+1}+\delta_{k+1})+7\delta_{k+1}=w_{k+1}+8\delta_{k+1}$, by (T2\*) and (J2);
- (b): $w_{k+1}\ge\alpha_{k+1}\ge D_{k+2}+16\cdot4^{k+1}d\ge D_{k+2}+16\delta_{k+1}$, by (T2\*) and (J2).

By Lemma S (iii), $P_{k+1}<P_k$, so $P_{k+1}+k+1\le P_k+k\le P_0$: (J4).

*Conclusion.* For $k=P_0+1$, (J4) reads $P_k+P_0+1\le P_0$, which is impossible. $\square$

The induction proves one statement per $k$; no infinite sequence or choice principle is needed. The Lean proof (`tower_levels`, `tower_adm`) carries (J3) in the invariant exactly as above.

**Remarks.**
1. *Finite form.* Type $\omega$ is used only in the last line. If (T1\*) holds and (T2\*) holds for $1\le k\le K-1$, then for every admissible linear order of any $S\supseteq\{u,u+d\}\cup I_1\cup\dots\cup I_K$ the pairs $(w_k,\delta_k)$, $0\le k\le K$, exist with $\max_\prec(w_{k+1},w_{k+1}+\delta_{k+1})\prec\max_\prec(w_k,w_k+\delta_k)$. In particular two elements of $I_K$ precede $u$ or $u+d$.
2. *No lag hypothesis.* Only that positions are natural numbers is used. The intervals need not be maximal runs of $S$, and nothing is assumed about $S$ outside $\{u,u+d\}\cup\bigcup_kI_k$.
3. *AP directions.* If $S$ is permutable, so is $\{k:\ c+ek\in S\}$ for $e\ge1$ (pull the order back along $k\mapsto c+ek$). So $S$ contains no tower of AP-blocks $c+eI_k$ satisfying (T1\*)–(T2\*) in $k$-coordinates. (Not formalized.)
4. *Constants.* They are what the proof uses, not what is best possible: the $8$ in the first half of (T2\*) can be lowered to $7$, and computer checks show Lemma S already holds with four blocks for small $M$.

## 5. Corollary R0\*

**Corollary R0\*** (clean form). Suppose $S$ contains intervals $[a_j,b_j]$ $(j\ge0)$ with $a_0\ge32$, $b_0\ge a_0+1$ and, for every $j\ge0$,
$$a_{j+1}\ge4b_j\qquad\text{and}\qquad 2a_{j+1}-b_{j+1}\le a_j/2\quad(\text{i.e. }4a_{j+1}\le a_j+2b_{j+1}).$$
Then $S$ is not permutable.

*Proof.* Theorem R\* with $u=b_0-1$, $d=1$ and $I_k=[a_k,b_k]$ for $k\ge1$.
1. By induction, $a_k\ge32\cdot4^k$ and $b_k\ge a_k+1$ for all $k$. The case $k=0$ is a hypothesis. Then $a_{k+1}\ge4b_k\ge4a_k+4\ge32\cdot4^{k+1}+4$, and $2b_{k+1}\ge4a_{k+1}-a_k\ge2a_{k+1}+2$ because $2a_{k+1}\ge8a_k+8\ge a_k+2$.
2. $u,u+1\in[a_0,b_0]\subseteq S$ since $b_0\ge a_0+1$.
3. (T1\*): $a_1\ge4b_0\ge b_0+99>u+8$; and from $4a_1\le a_0+2b_1$, $a_0\ge32$ and $b_0-1\ge a_0$: $2a_1+16\le a_0+b_1\le u+b_1$.
4. (T2\*) for $k\ge1$: $a_{k+1}\ge4b_k=b_k+3b_k\ge b_k+96\cdot4^k\ge b_k+8\cdot4^k$; and from $4a_{k+1}\le a_k+2b_{k+1}$ and $a_k\ge32\cdot4^k$: $2a_{k+1}+16\cdot4^k\le a_k+b_{k+1}$. $\square$

## 6. Corollary R2\*

**Corollary R2\*** (drifting near-dyadic run colourings). Let $1\le r_0<r_1<\cdots$ be integers with $r_{k+1}/r_k\to2$, and colour $[r_k,r_{k+1})$ by $k\bmod2$. Then neither colour class is permutable.

Only this sentence, the colouring form, is formalized (`Erdos197Tower.main_result`). The refereed statement of R2\* has a second sentence, which is **not formalized**: "More generally, no set containing intervals $[a_j,b_j]$ $(j\ge1)$ with integers $1\le a_j\le b_j$, $b_j<a_{j+1}$, $b_j/a_j\to2$ and $\sup_ja_{j+1}/a_j<\infty$ is permutable." The refereed text derives it from Corollary R1\* (see the end of this section).

*Proof.* Fix $c\in\{0,1\}$ and let $S$ be the class of colour $c$. We apply R0\* to every fourth run (every other run of colour $c$).
1. ($\varepsilon=1/100$.) There is $K_0$ with $1.99\,r_k<r_{k+1}<2.01\,r_k$, i.e. $199\,r_k<100\,r_{k+1}<201\,r_k$, for all $k\ge K_0$.
2. As $r$ is strictly increasing, $r_k\ge k$. Let $K:=2(K_0+32)+c$, so $K\equiv c\pmod2$, $K\ge K_0$ and $r_K\ge K\ge64$.
3. Put $a_m:=r_{K+4m}$ and $b_m:=r_{K+4m+1}-1$. Then $[a_m,b_m]=[r_k,r_{k+1})$ with $k=K+4m\equiv c$, so $[a_m,b_m]\subseteq S$.
4. $a_0=r_K\ge32$, and $b_0\ge a_0+1$ since $r_{K+1}>1.99\,r_K\ge r_K+63$.
5. Fix $m$, let $k=K+4m$ and $x_i=r_{k+i}$, so $x_0\ge32$ and the bounds of step 1 hold for $x_0,\dots,x_5$.
   - $a_{m+1}\ge4b_m$, i.e. $x_4\ge4(x_1-1)$: $x_4>1.99^3x_1>4x_1$.
   - $4a_{m+1}\le a_m+2b_{m+1}$, i.e. $4x_4\le x_0+2(x_5-1)$: from $100x_5\ge199x_4+1$ we get $2x_5-2\ge3.98\,x_4-1.98$, so it suffices that $0.02\,x_4+1.98\le x_0$; and $x_4<2.01^4x_0<16.33\,x_0$, so $0.02\,x_4+1.98<0.33\,x_0+1.98\le x_0$ because $x_0\ge32$.
6. Corollary R0\* applies. $\square$

In Lean, step 1 is `ratio_bounds` (from `Metric.tendsto_atTop` with $\varepsilon=1/100$), step 5 is `six_terms` (one `omega` call over the six integers $x_0,\dots,x_5$), and the rest is `drifting_adm`. The proof uses only that $S$ contains the runs $[r_k,r_{k+1})$ with $k\equiv c\pmod2$, so it also shows that no superset of a colour class is permutable. Lean proves this as `drifting_sub` in `Erdos197Tower/Basic.lean` (`checks/fidelity.lean` uses it), but it is not a statement of `Challenge.lean`. It is different from, and weaker than, the second sentence quoted above: it is the special case $[a_j,b_j]=[r_{2j+c},r_{2j+c+1}-1]$ of that sentence. `main_result` is the case where $S$ is the colour class. The hypothesis $r_0\ge1$ is used only to make the ratios well defined; it is part of the statement as in the source.

*Other corollaries of the refereed text (not formalized).* The refereed text derives both sentences of R2\* from a Corollary R1\* (intervals $[a_j,b_j]$ of positive integers with $b_j<a_{j+1}$, $b_j/a_j\to2$ and $a_{j+1}\le Ca_j$; it takes the subsequence $j_0+4m$ of the intervals, which for the colouring is every eighth run). The second sentence is R1\* with $C=\sup_ja_{j+1}/a_j$. The refereed text also proves two quantitative versions: R1′\* ($a_0\ge32$, $b_0\ge1$, $(2-\varepsilon)a_j\le b_j\le2a_j$, $4b_j\le a_{j+1}\le Kb_j$, $\varepsilon\ge0$, $4\varepsilon K\le1$) and R1″\* (run partitions with $r_0\ge32$ and $(2-\varepsilon)r_i\le r_{i+1}-1\le2r_i$, $0\le\varepsilon\le1/33$, so deficits up to $r_i/33$ that need not be $o(r_i)$). None of these is part of this formalization. The proof of R2\* above, and its Lean proof, go directly to R0\* with every fourth run, which needs only one explicit $\varepsilon$.

### What Theorem R\* kills, and what it does not reach

*Killed.* Every colouring of $[r_0,\infty)$ by alternating runs $[r_k,r_{k+1})$ with $r_{k+1}/r_k\to2$ fails for both colours (R2\*), with any enumeration and no lag assumption, whatever the deficits $2r_k-r_{k+1}$ are, as long as they are $o(r_k)$ (which is what $r_{k+1}/r_k\to2$ means). Kasel's dyadic partition (his Theorem 21) is the case $r_k=2^k+1$: its blocks are $(2^k,2^{k+1}]=[r_k,r_{k+1})$, and his set $S_A$ is the class of odd $k$. Kasel's Part II notes 38–40 (github `Wkasel/erdos197`) study "growing-sliver" two-team schedules whose teams are run colourings with $r_t=2^{t-1}+s_t+1$; there $r_{t+1}/r_t\to2$ exactly when the necks $2s_t-s_{t+1}$ are $o(r_t)$, and the referees of the working notes checked that the nine schedules of those notes have this property (and replayed the R0\* chain by computer over many levels; this is not in Lean). So R2\* applies to both teams of each schedule, including Kasel's "clean" teams geo/A and geomirror/B.

Kasel's Geneson-matched ("gm") schedule (notes 38–39; octave-alternating, with necks that tend to $-\infty$ at the stage seams) and his stage-alternating ownership family (notes 40 §4 and 42–43) are not run colourings with ratios $\to2$, so R2\* does not apply to them. They are killed all the same. The round-2 scope referee of the refereed text found that every team of either family contains a fixed pair $v,v+1$ and infinitely many intervals $[P,2P-v+6]$, that is, blocks $v+[K,2K+6]$ with $K\ge8$. So Corollary I\* with $\delta=1$ (`Erdos197Interval.corollary` in the copied module) shows that neither team is permutable, and so does Theorem R\*. Kasel's own notes 42–43 report the stage-alternating family dead, on machine-checked rungs. The referee derived the shape of the teams from Kasel's definitions and checked it by computer, with two independent programs that agree, up to $2^{141}$ and $2^{24}$ (`work/p197_m2_r2/verify_Rstar/v2_scope/gm_check.py` and `gm_check2.py` of the working notes). None of this is checked in Lean. The refereed text itself still lists these teams as not covered.

*Not reached.*
1. **Ratio barrier.** No tower satisfies (T2\*) with $\alpha_1>0$ and $\beta_k\le\rho\,\alpha_k$ for all $k$ when $\rho<7/4$: the second half of (T2\*) gives $\alpha_k\ge(2-\rho)\alpha_{k+1}+16\cdot4^kd$ and the first half makes the $\alpha_k$ increasing and positive, so $\alpha_k\le\alpha_1(2-\rho)^{1-k}$ while $\alpha_k\ge16\cdot4^kd$; both hold for all $k$ only if $1/(2-\rho)\ge4$. So R\* sees only runs of ratio at least $7/4$, asymptotically.
2. **$\rho$-type colourings** (many short runs per octave): $\delta$ may grow by a factor $4$ per level while the scale grows only by a factor $2^{2/3}$ per run.
3. **Sparse near-doubling runs whose deficit exceeds the scale of the previous run.** In Geneson's permutable set of upper density $2/3$ (arXiv:2608.12604) every R0\*-chain breaks at each stage boundary, consistent with that set being permutable: Theorem R\* is not too strong.
4. **Non-interval colourings and unbounded lag in general**: the crux of #197, untouched.

## 7. Relation to earlier work

* **Kasel, arXiv:2609.02939.** Source of the ladder toolkit (zigzag and flood, Lemmas 23–26) behind Theorem I, and of the theorem that the dyadic partition fails (Theorem 21), which is the case $r_k=2^k+1$ of R2\* (his set $S_A=\bigcup_{k\ge2\text{ even}}(2^{k-1},2^k]$ is the class of odd $k$). Kasel's *Theorem 40* ("tower characterization", Appendix B.1) is a Kőnig-compactness characterisation of the permutability of his dyadic set $S_A$: $S_A$ is permutable iff there is $B:\mathbb N\to\mathbb N$ such that for every block top the finite system "pure-complete up to that top, with at most $B(v)$ predecessors of each $v$" is satisfiable. Despite the shared word it concerns a different kind of tower; it neither implies nor is implied by Theorem R\*. Kasel's Part II notes (github `Wkasel/erdos197`) prove that some team of a growing-sliver schedule carries a fixed attacking pair at infinitely many scales, kill "at least one team" only modulo machine-checked per-scale rungs, and record that a single-attacker regress fails because "pair conclusions do not overflow" (notes/39 §4b). Lemma S supplies the missing mechanism: it turns a pair into a new pair, both before the later point, so the maximal position descends. Kasel's Theorem B1₀ (complete dyadic blocks at infinitely many scales) concerns full dyadic blocks, like Corollary I\* with $\delta=1$, and does not anticipate R\*.
* **trureturing PR #9626** ([the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing/pull/9626)) proves in Lean that Kasel's order gadget $\mathrm{OG}(M)$ is infeasible for all $M\ge16$. The first (round-1) version of the tower theorem, Theorem R of the working notes (constants $(2,23)$ instead of $(8,16)$), rested on that PR's four-guard core $\mathrm{OG}(M)$, read as text. Theorem R\* replaces it by Theorem I, which is Lean-verified in our own repository; Lemma I of Theorem I is the PR's four-flood cycle. No code was taken from the PR.
* **Theorem I** ([Alex-lop/erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget)) is the core: Lemma W\* is Theorem I pulled back along an affine map. Its Lean module is included here verbatim.
* To the best of the referees' searches (arXiv math.CO/math.NT listings 2026-08-15 to 2026-11-04, erdosproblems.com, GitHub), Theorem R\* and Corollary R2\* are new.

## 8. Lean formalization

`Erdos197Tower/Basic.lean` follows Sections 2–6; `Erdos197Interval/Basic.lean` is Theorem I.

* An order of $S$ is an injective ranking $\rho:\mathbb N\to\mathbb N$ on $S$ ($x\prec y$ iff $\rho x<\rho y$). `Adm S ρ` packages injectivity on $S$ and the midpoint rule; `adm_of_enum` shows that the positions $f^{-1}$ of an enumeration $f:\mathbb N\simeq S$ without monotone 3-term APs (the formal-conjectures predicate, unfolded) form such a ranking. Positions are natural numbers, which is all that type $\omega$ contributes. So the Lean lemmas cover the orders that embed in $\omega$, not every order type (Section 2).
* `witness` is Lemma W\* (it calls `Erdos197Interval.gadget_thm` with $\sigma(k)=\rho(w+\delta k)$), `step` is Lemma S, `tower_levels` and `tower_adm` are the induction and conclusion of Theorem R\*, `clean_adm` is Corollary R0\*, and `ratio_bounds`, `six_terms`, `drifting_adm` are the proof of Corollary R2\*. `drifting_adm` and `drifting_sub` are stated for any set containing the runs of one colour (Section 6), which is not a statement of `Challenge.lean`; `drifting` is its special case, the colouring sentence.
* `tower_thm`, `clean_thm` and `drifting` prove the statements of `Challenge.lean`, which `Solution.lean` restates as `Erdos197Tower.tower`, `Erdos197Tower.clean` and `Erdos197Tower.main_result`.
* The ceiling $M=\lceil(\alpha-w)/\delta\rceil$ is $\lfloor(\alpha-w+\delta-1)/\delta\rfloor$; products such as $\delta M$ and $4^kd$ are atoms for `omega`.

The Lean statements use Lean's $\mathbb N=\{0,1,2,\dots\}$, as formal-conjectures does. Nothing above needs positivity except where stated ($d\ge1$, $r_0\ge1$).

## 9. Verification history

The refereed text is `work/p197_m2_r2/verify_Rstar/repair1/proof.md` of the project's working notes, which is not included in this repository. This note is a rewrite of it; the introduction lists the parts that were not in the refereed text. That text was checked by three adversarial AI referees (lenses: proof, computation, scope) in three rounds. Round 0 found two corollaries of the first write-up false in degenerate cases with empty intervals (the "more generally" sentence of R2\* without $1\le a_j\le b_j$, and R1′\* without $b_0\ge1$); both were repaired by one added hypothesis each. Round 1 found five false or inaccurate sentences of commentary, none used by any proof (the formal refutation was one of them, a comparison with the round-1 Theorem R); they were corrected in a second repair. Round 2 refuted nothing; it found cosmetic issues, a one-line gap in a remark about the round-1 corollaries, and an under-claim about Kasel's Geneson-matched and stage-alternating schedules. The under-claim is not corrected in the refereed text; it is corrected here (Section 6, *Killed*). Theorem R\*, Lemmas W\* and S and Corollaries R0\* and R2\* (colouring form) were never changed. The referees' independent programs (SAT encoders with CaDiCaL, exhaustive arithmetic checks, exact rational replays of the induction) agree with every statement; those computations are evidence for the informal proof and are not needed for the Lean proof. The statements formalized here are proved by the Lean kernel. Neither the refereed text nor this note has been refereed by a human.
