# Erdős #197: a tower obstruction, and drifting near-dyadic run colourings fail

> **Status: PARTIAL result toward Erdős #197, NOT a solution.** This repository does **not** solve [Erdős Problem #197](https://www.erdosproblems.com/197), which is still open. It proves, and formally verifies in Lean 4, an obstruction for permutable sets (Theorem R\*) and its consequence for alternating run colourings with ratios tending to $2$ (Corollary R2\*).

## The result

Erdős #197 (Erdős–Graham) asks whether $\mathbb N$ can be partitioned into two sets, each with an enumeration (a listing of order type $\omega$) that contains no monotone 3-term arithmetic progression. Call such a set *permutable*. Davis–Entringer–Graham–Simmons (1977) showed that $\mathbb N$ itself is not permutable. Kasel (arXiv:2609.02939, 2026) showed that the dyadic partition fails.

**Theorem R\*** (tower obstruction). Let $S\subseteq\mathbb N$ contain two points $u,u+d$ ($d\ge1$) and intervals $[\alpha_k,\beta_k]$ ($k\ge1$) such that

* (T1\*) $\alpha_1\ge u+8d$ and $2\alpha_1-\beta_1\le u-16d$;
* (T2\*) $\alpha_{k+1}\ge\beta_k+8\cdot4^kd$ and $2\alpha_{k+1}-\beta_{k+1}\le\alpha_k-16\cdot4^kd$ for every $k\ge1$.

Then $S$ is not permutable.

**Corollary R0\*.** If $S$ contains intervals $[a_j,b_j]$ ($j\ge0$) with $a_0\ge32$, $b_0\ge a_0+1$, $a_{j+1}\ge4b_j$ and $2a_{j+1}-b_{j+1}\le a_j/2$ for all $j$, then $S$ is not permutable.

Theorem R\* and Corollary R0\* are stated here, as in Lean, for $S\subseteq\mathbb N$. The refereed text states them for $S\subseteq\mathbb Z$ (with integer $u$, $\alpha_k$, $\beta_k$, $a_j$, $b_j$). The two forms are equivalent (restrict to the tower, then translate it into $\mathbb N$), but that reduction is not proved in Lean.

**Corollary R2\*** (main result). Let $1\le r_0<r_1<r_2<\cdots$ be integers with $r_{k+1}/r_k\to2$, and colour each run $[r_k,r_{k+1})$ by the parity of $k$. Then **neither** colour class is permutable.

Only this colouring sentence of R2\* is formalized. The refereed text adds a second sentence, which is **not** formalized: "More generally, no set containing intervals $[a_j,b_j]$ $(j\ge1)$ with integers $1\le a_j\le b_j$, $b_j<a_{j+1}$, $b_j/a_j\to2$ and $\sup_ja_{j+1}/a_j<\infty$ is permutable." The Lean lemma `Erdos197Tower.drifting_sub` proves a different, weaker statement (no set containing all runs of one colour is permutable). It is not one of the statements in `Challenge.lean`.

**What it kills.** Every 2-colouring of $[r_0,\infty)$ by alternating runs with ratios $r_{k+1}/r_k\to2$ fails, for both colours, with any enumeration: there is no lag assumption and no assumption on how fast the ratios converge, and the deficits $2r_k-r_{k+1}$ may be anything that is $o(r_k)$. Kasel's dyadic partition (blocks $(2^k,2^{k+1}]$; his set $S_A$ is the class of odd $k$) is the case $r_k=2^k+1$. The runs $[2^k,2^{k+1})$ ($r_k=2^k$) and drifting runs such as $r_k=2^k+k$ are covered as well; these two examples are checked in [`checks/nonvacuity.lean`](checks/nonvacuity.lean). In particular this covers the "growing-sliver" two-team schedules of Kasel's Part II notes 38–40 (github `Wkasel/erdos197`), whose runs have necks $o(r_t)$ (checked by the referees by computer, not in Lean); there Kasel killed at least one team modulo machine-checked rungs, here both teams fail unconditionally.

**What it does not reach** ([`docs/proof.md`](docs/proof.md), Section 6):

* runs of ratio below $7/4$ (no tower satisfying (T2\*) has $\beta_k\le\rho\,\alpha_k$ for all $k$ when $\rho<7/4$), in particular colourings with many short runs per octave;
* sparse near-doubling runs whose deficit exceeds the scale of the previous run (consistently, Geneson's permutable set of upper density $2/3$, arXiv:2608.12604, contains no infinite tower);
* non-interval colourings and unbounded lag in general, which is the crux of #197.

**Idea of the proof.** Theorem I of [Alex-lop/erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget), pulled back along $k\mapsto w+\delta k$, says: if $w$ and $w+\delta$ are in $S$ and so is the block $w+\delta[M,2M+6]$ ($M\ge8$), then some element of $w+\delta[M,M+3]$ is listed before $w$ or before $w+\delta$ (Lemma W\*). Five overlapping blocks of this kind inside one interval give two such early elements at different places, which form a new pair $w',w'+\delta'$ with $\delta\le\delta'\le4\delta$ inside the interval, both listed before the later of $w,w+\delta$ (Lemma S). Hypotheses (T1\*) and (T2\*) make Lemma S applicable from each interval to the next, so the position of the later element of the pair drops at every level: impossible for more than finitely many levels. Corollary R2\* applies R0\* to every fourth run (every other run of colour $c$), once the ratios are within $1/100$ of $2$. The whole argument is in [`docs/proof.md`](docs/proof.md).

## Lean formalization

| File | Contents |
| --- | --- |
| [`Challenge.lean`](Challenge.lean) | The three statements to audit (Mathlib-only, proofs `sorry`). |
| [`Solution.lean`](Solution.lean) | The same statements, proved. |
| [`Erdos197Tower/Basic.lean`](Erdos197Tower/Basic.lean) | The proof: Lemma W\*, Lemma S, Theorem R\*, Corollaries R0\* and R2\*. |
| [`Erdos197Interval/Basic.lean`](Erdos197Interval/Basic.lean) | Theorem I, a verbatim copy of the module of [Alex-lop/erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget) (same content and namespace). |
| [`checks/`](checks) | Fidelity and non-vacuity checks (not part of the build). |

```lean
theorem Erdos197Tower.tower (S : Set ℕ) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·))
    (u d : ℕ) (hd : 1 ≤ d) (hu : u ∈ S) (hud : u + d ∈ S)
    (α β : ℕ → ℕ) (hI : ∀ k, 1 ≤ k → Set.Icc (α k) (β k) ⊆ S)
    (hT1a : u + 8 * d ≤ α 1) (hT1b : 2 * α 1 + 16 * d ≤ u + β 1)
    (hT2a : ∀ k, 1 ≤ k → β k + 8 * 4 ^ k * d ≤ α (k + 1))
    (hT2b : ∀ k, 1 ≤ k → 2 * α (k + 1) + 16 * 4 ^ k * d ≤ α k + β (k + 1)) :
    False

theorem Erdos197Tower.clean (S : Set ℕ) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·))
    (a b : ℕ → ℕ) (hI : ∀ j, Set.Icc (a j) (b j) ⊆ S) (h32 : 32 ≤ a 0) (h01 : a 0 + 1 ≤ b 0)
    (hgrow : ∀ j, 4 * b j ≤ a (j + 1)) (hdef : ∀ j, 4 * a (j + 1) ≤ a j + 2 * b (j + 1)) :
    False

theorem Erdos197Tower.main_result (r : ℕ → ℕ) (hr : StrictMono r) (h0 : 1 ≤ r 0)
    (hlim : Filter.Tendsto (fun k => (r (k + 1) : ℝ) / r k) Filter.atTop (nhds 2))
    (c : ℕ) (hc : c < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | ∃ k, k % 2 = c ∧ r k ≤ n ∧ n < r (k + 1)},
      ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·)
```

How to read them:

- An enumeration of $S$ is `f : ℕ ≃ S`, listing `f 0, f 1, f 2, …`. The `¬ ∃ l …` clause is `¬HasMonotoneAP (Subtype.val ∘ f) 3` from [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983/FormalConjectures/ErdosProblems/197.lean) with the definitions unfolded: no strictly increasing list of indices is mapped onto $a,a+d,a+2d$ or onto $a+2d,a+d,a$. It is the predicate of formal-conjectures' `Erdos197.erdos_197`, written exactly as in `Erdos197Interval.main_result`.
- In `tower` and `clean` the enumeration and its property are hypotheses and the conclusion is `False`, i.e. $S$ is not permutable. The hypotheses (T1\*), (T2\*) and the deficit bound of R0\* are written without subtraction ($2a_{j+1}-b_{j+1}\le a_j/2$ is `4 * a (j + 1) ≤ a j + 2 * b (j + 1)`).
- In `main_result`, the colour class of `c ∈ {0, 1}` is `{n | ∃ k, k % 2 = c ∧ r k ≤ n ∧ n < r (k + 1)}`, the union of the runs $[r_k,r_{k+1})$ with $k\equiv c$, and the ratio is the real number `(r (k + 1) : ℝ) / r k`. The conclusion says that this class has no enumeration without monotone 3-term APs.
- $\mathbb N$ is Lean's $\{0,1,2,\dots\}$, as in formal-conjectures.

Checks performed (Lean `v4.35.0`, Mathlib `v4.35.0`):

- `lake build` succeeds. Its only warnings are the three deliberate `sorry`s in `Challenge.lean`. There is no `sorry`, `admit`, `native_decide`, `decide`, `implemented_by`, `opaque` or `axiom` anywhere else.
- `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` for all three theorems.
- The statements in `Challenge.lean` and `Solution.lean` elaborate to identical terms (checked with `pp.all`; the outputs are byte-identical).
- In [`checks/fidelity.lean`](checks/fidelity.lean), verbatim copies of formal-conjectures' `HasMonotoneAP`, `List.IsAPOfLength` and `List.IsAPOfLengthWith` are used to restate all three theorems; each restatement is proved by `exact` from the Challenge statement, i.e. by definitional unfolding alone. The file also proves `fc_erdos197_runs`: if `IsCompl A B` and $A$ contains exactly the runs $[r_k,r_{k+1})$ with $k$ even (any split of $[0,r_0)$), then neither $A$ nor $B$ has an enumeration $f$ with `¬HasMonotoneAP (Subtype.val ∘ f) 3`, so $(A,B)$ is not a witness for `Erdos197.erdos_197`.
- Non-vacuity ([`checks/nonvacuity.lean`](checks/nonvacuity.lean)): the enumeration hypothesis `hf`, exactly as unfolded in `Challenge.lean`, is satisfiable (`hf_sat`: the powers of two, listed in increasing order, have no monotone 3-term AP); explicit data satisfying every hypothesis of `tower` and of `clean` except the enumeration property, inside sets that do have enumerations (`tower_hyps`, `clean_hyps`); every colour class of a strictly increasing `r` has enumerations, so the conclusion of `main_result` is not trivially true (`class_enumerable`); $r_k=2^k$ (the runs $[2^k,2^{k+1})$) and the drifting $r_k=2^k+k$ satisfy the hypotheses of `main_result` (`dyadic_hyps`, `dyadic`, `lin_hyps`, `lin`).
- The formalizer ran `check-lean-sources.py` and `validate-formalization.rb` from the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate) (commit `2891de4`) and reports that both passed. The scripts are not vendored here and no log of that run is included; copy them from the template to rerun them.

The repository follows the [Palomar](https://palomar-registry.org) layout, with `comparator.json` and `formalization.yaml`. It has **not** been submitted to the registry.

To build:

```sh
lake exe cache get   # download Mathlib build files
lake build
```

## Reproducing the checks

After `lake build`, run `lake env lean checks/fidelity.lean` and `lake env lean checks/nonvacuity.lean` from the repository root. Both end with `#print axioms`, which reports only `propext`, `Classical.choice` and `Quot.sound`. The first copies formal-conjectures' definitions verbatim from commit [`5d8b04d3`](https://github.com/google-deepmind/formal-conjectures/blob/5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983/FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean).

## Related repositories

- [Alex-lop/erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget): Theorem I (the anchored gadget $[M,2M+6]$ is infeasible for $M\ge8$) and Corollary I. This repository builds on it; its Lean module is included verbatim.
- [Alex-lop/erdos-197-bounded-lag](https://github.com/Alex-lop/erdos-197-bounded-lag): an earlier, independent partial result on #197 from the same project (no two-set solution with eventual lag ratio below $2$).

## Credits

- W. Kasel, *Structural rigidity in the Erdős–Graham two-set permutation problem*, arXiv:2609.02939: the ladder toolkit (zigzag and flood) behind Theorem I, the order gadget, and the theorem that the dyadic partition fails (Theorem 21). His Theorem 40 ("tower characterization") is a compactness characterisation of the permutability of his dyadic set; it is a different notion of tower from the interval towers here, and neither result implies the other.
- [the-omega-institute/trureturing PR #9626](https://github.com/the-omega-institute/trureturing/pull/9626): Lean proof that Kasel's gadget $\mathrm{OG}(M)$ is infeasible for $M\ge16$. It was the Lean core of the first version of the tower theorem (Theorem R of the working notes); Theorem R\* uses Theorem I instead. Lemma I in the proof of Theorem I is that PR's four-flood cycle (`even_four_guards_impossible` / `odd_four_guards_impossible`; after a translation, the PR's four guards are exactly the anchor constraints that Lemma I uses). No code was taken from it.
- Theorem I ([Alex-lop/erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget)) is the core of Lemma W\*.

## Use of AI

This work was produced by **Claude Fable 5.1** and **Claude Opus 5.5** (Anthropic), running in Claude Code, under the direction of **Alex Lopez**. Claude Opus 5.5 wrote the Lean formalization and this repository. The informal proof was checked by three adversarial AI referees (proof, computation and scope lenses) over three rounds, with two repairs (two corollaries were false in degenerate cases with empty intervals and received one added hypothesis each; some commentary was corrected; Theorem R\* itself never changed), and the Lean kernel checks all three theorems. The refereed text is the project's working note `work/p197_m2_r2/verify_Rstar/repair1/proof.md`, which is not included here. `docs/proof.md` is a rewrite of it. The parts it re-derives were not refereed: the proof of R2\* by R0\* on every fourth run, the invariant (J3) of Theorem R\*, and the steps of the proof of R0\*. Each of them is mirrored by the kernel-checked Lean proof. Neither text has been refereed by a human.

## License

Apache-2.0; see [LICENSE](LICENSE).
