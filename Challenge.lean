module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

/-!
# Advertised statements

Partial progress on Erdős Problem #197 (<https://www.erdosproblems.com/197>), which remains open.

Erdős #197 asks whether `ℕ` can be split into two sets, each admitting an enumeration (a listing
of order type `ω`) with no monotone 3-term arithmetic progression. A set with such an
enumeration is called *permutable*. The three statements below are Theorem R\*, Corollary R0\*
and Corollary R2\* of `docs/proof.md`. Each says that a set of a certain shape is not permutable.

**Theorem R\* (`Erdos197Tower.tower`).** Let `S ⊆ ℕ` contain two points `u, u + d` (`d ≥ 1`) and
intervals `[α k, β k]` for `k ≥ 1` that form a *tower*:
* (T1\*) `α 1 ≥ u + 8d` and `2 α 1 - β 1 ≤ u - 16d`;
* (T2\*) `α (k + 1) ≥ β k + 8 · 4^k · d` and `2 α (k + 1) - β (k + 1) ≤ α k - 16 · 4^k · d`
  for every `k ≥ 1`.

Then `S` is not permutable. The hypotheses are written without subtraction:
`2 α 1 + 16d ≤ u + β 1` and `2 α (k + 1) + 16 · 4^k · d ≤ α k + β (k + 1)`.

**Corollary R0\* (`Erdos197Tower.clean`).** If `S ⊆ ℕ` contains intervals `[a j, b j]` (`j ≥ 0`)
with `a 0 ≥ 32`, `b 0 ≥ a 0 + 1` and, for every `j`, `a (j + 1) ≥ 4 b j` and
`2 a (j + 1) - b (j + 1) ≤ a j / 2` (written `4 a (j + 1) ≤ a j + 2 b (j + 1)`), then `S` is not
permutable.

The refereed text states Theorem R\* and Corollary R0\* for `S ⊆ ℤ` (with integer `u`, `α k`,
`β k`, `a j`, `b j`); here they are stated over `ℕ`, the setting of Erdős #197 and of
formal-conjectures. The two forms are equivalent (restrict to the tower, then translate it into
`ℕ`), but that reduction is not proved in Lean.

**Corollary R2\* (`Erdos197Tower.main_result`).** Let `1 ≤ r 0 < r 1 < r 2 < ⋯` be integers with
`r (k + 1) / r k → 2`, and colour each run `[r k, r (k + 1))` by the parity of `k`. Then neither
colour class is permutable. No assumption is made on how fast the ratios converge or on the
order of the enumeration.

**Encoding.**
* An enumeration of `S` is a bijection `f : ℕ ≃ S`, read as the list `f 0, f 1, f 2, …`.
* "No monotone 3-term AP" is the predicate `¬HasMonotoneAP (Subtype.val ∘ f) 3` of
  google-deepmind/formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`),
  written out by unfolding `HasMonotoneAP`, `List.IsAPOfLength` and `List.IsAPOfLengthWith`: no
  strictly increasing list of indices `l` is mapped by `Subtype.val ∘ f` onto `a, a + d, a + 2d`
  or onto `a + 2d, a + d, a`. This is the condition used in formal-conjectures'
  `Erdos197.erdos_197`; writing it out keeps this file Mathlib-only and free of new definitions.
  It is written exactly as in `Erdos197Interval.main_result`
  (<https://github.com/Alex-lop/erdos-197-interval-gadget>). It agrees with the original up to
  definitional unfolding of instances: here `n • d` uses `instSMulOfMul` for `ℕ`, while
  formal-conjectures' definitions, stated for an `AddCommMonoid`, use the `AddMonoid` scalar
  multiplication `NSMul.toSMul (AddMonoid.toNSMul _)` (the monoid's `nsmul`);
  `checks/fidelity.lean` checks by `exact` that the two predicates agree.
* In `tower` and `clean` the enumeration and its property are hypotheses and the conclusion is
  `False`; in `main_result` the conclusion is `¬ ∃ f : ℕ ≃ C, …` for the colour class `C`.
* The colour class of `c ∈ {0, 1}` is `{n | ∃ k, k % 2 = c ∧ r k ≤ n ∧ n < r (k + 1)}`, and the
  ratio is the real number `(r (k + 1) : ℝ) / r k`.
-/

/-- **Theorem R\*** (tower obstruction). Let `f : ℕ ≃ S` be an enumeration of `S ⊆ ℕ` with no
monotone 3-term arithmetic progression (formal-conjectures' `¬HasMonotoneAP (Subtype.val ∘ f) 3`,
unfolded). Then `S` contains no tower: two points `u, u + d` with `d ≥ 1` and intervals
`[α k, β k]`, `k ≥ 1`, satisfying (T1\*) and (T2\*). -/
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
    False := by
  sorry

/-- **Corollary R0\*** (clean form). An enumeration `f : ℕ ≃ S` with no monotone 3-term AP
(formal-conjectures' predicate, unfolded) does not exist if `S` contains intervals `[a j, b j]`
with `a 0 ≥ 32`, `b 0 ≥ a 0 + 1`, `a (j + 1) ≥ 4 b j` and `2 a (j + 1) - b (j + 1) ≤ a j / 2`. -/
theorem Erdos197Tower.clean (S : Set ℕ) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·))
    (a b : ℕ → ℕ) (hI : ∀ j, Set.Icc (a j) (b j) ⊆ S) (h32 : 32 ≤ a 0) (h01 : a 0 + 1 ≤ b 0)
    (hgrow : ∀ j, 4 * b j ≤ a (j + 1)) (hdef : ∀ j, 4 * a (j + 1) ≤ a j + 2 * b (j + 1)) :
    False := by
  sorry

/-- **Corollary R2\*** (drifting near-dyadic run colourings). Let `r : ℕ → ℕ` be strictly
increasing with `1 ≤ r 0` and `r (k + 1) / r k → 2`. For each colour `c ∈ {0, 1}`, the class
`{n | ∃ k, k % 2 = c ∧ r k ≤ n ∧ n < r (k + 1)}` (the union of the runs `[r k, r (k + 1))` with
`k ≡ c mod 2`) has no enumeration without monotone 3-term APs (formal-conjectures' predicate,
unfolded). -/
theorem Erdos197Tower.main_result (r : ℕ → ℕ) (hr : StrictMono r) (h0 : 1 ≤ r 0)
    (hlim : Filter.Tendsto (fun k => (r (k + 1) : ℝ) / r k) Filter.atTop (nhds 2))
    (c : ℕ) (hc : c < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | ∃ k, k % 2 = c ∧ r k ≤ n ∧ n < r (k + 1)},
      ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·) := by
  sorry
