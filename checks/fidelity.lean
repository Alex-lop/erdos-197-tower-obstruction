module

public import Solution
public import Mathlib.Algebra.Module.NatInt

public section

section FC

/-! Verbatim copies of the formal-conjectures definitions (commit
5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983,
FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean, lines 36, 51-52, 129-130, 246-247),
at top level as there (Mathlib defines none of these names). -/

variable {α : Type*} [AddCommMonoid α]

def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)

def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

end FC

/-- Theorem R\* restated with the formal-conjectures predicate itself; accepted by `exact`
(definitional unfolding only), so the inlined predicate of `Challenge.lean` is the same
proposition. -/
theorem fc_tower (S : Set ℕ) (f : ℕ ≃ S) (hf : ¬HasMonotoneAP (Subtype.val ∘ f) 3)
    (u d : ℕ) (hd : 1 ≤ d) (hu : u ∈ S) (hud : u + d ∈ S)
    (α β : ℕ → ℕ) (hI : ∀ k, 1 ≤ k → Set.Icc (α k) (β k) ⊆ S)
    (hT1a : u + 8 * d ≤ α 1) (hT1b : 2 * α 1 + 16 * d ≤ u + β 1)
    (hT2a : ∀ k, 1 ≤ k → β k + 8 * 4 ^ k * d ≤ α (k + 1))
    (hT2b : ∀ k, 1 ≤ k → 2 * α (k + 1) + 16 * 4 ^ k * d ≤ α k + β (k + 1)) :
    False := by
  exact Erdos197Tower.tower S f hf u d hd hu hud α β hI hT1a hT1b hT2a hT2b

/-- Corollary R0\* with the formal-conjectures predicate, by `exact`. -/
theorem fc_clean (S : Set ℕ) (f : ℕ ≃ S) (hf : ¬HasMonotoneAP (Subtype.val ∘ f) 3)
    (a b : ℕ → ℕ) (hI : ∀ j, Set.Icc (a j) (b j) ⊆ S) (h32 : 32 ≤ a 0) (h01 : a 0 + 1 ≤ b 0)
    (hgrow : ∀ j, 4 * b j ≤ a (j + 1)) (hdef : ∀ j, 4 * a (j + 1) ≤ a j + 2 * b (j + 1)) :
    False := by
  exact Erdos197Tower.clean S f hf a b hI h32 h01 hgrow hdef

/-- Corollary R2\* with the formal-conjectures predicate, by `exact`: no colour class has an
enumeration `f` with `¬HasMonotoneAP (Subtype.val ∘ f) 3`. -/
theorem fc_main (r : ℕ → ℕ) (hr : StrictMono r) (h0 : 1 ≤ r 0)
    (hlim : Filter.Tendsto (fun k => (r (k + 1) : ℝ) / r k) Filter.atTop (nhds 2))
    (c : ℕ) (hc : c < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | ∃ k, k % 2 = c ∧ r k ≤ n ∧ n < r (k + 1)},
      ¬HasMonotoneAP (Subtype.val ∘ f) 3 := by
  exact Erdos197Tower.main_result r hr h0 hlim c hc

/-- The link with formal-conjectures' `Erdos197.erdos_197`, whose witness would be a pair
`A, B` with `IsCompl A B`, `∃ f : ℕ ≃ A, ¬HasMonotoneAP (Subtype.val ∘ f) 3` and
`∃ g : ℕ ≃ B, ¬HasMonotoneAP (Subtype.val ∘ g) 3`. If `A` contains exactly the runs
`[r k, r (k + 1))` with `k` even (the points below `r 0` may lie in `A` or `B`), then neither
enumeration exists, so `A, B` is not a witness. (From `Erdos197Tower.drifting_sub`, the superset
form of the colouring statement of Corollary R2\*, proved in `Erdos197Tower/Basic.lean`.) -/
theorem fc_erdos197_runs (r : ℕ → ℕ) (hr : StrictMono r) (h0 : 1 ≤ r 0)
    (hlim : Filter.Tendsto (fun k => (r (k + 1) : ℝ) / r k) Filter.atTop (nhds 2))
    (A B : Set ℕ) (hAB : IsCompl A B)
    (hA : ∀ k n, r k ≤ n → n < r (k + 1) → (n ∈ A ↔ k % 2 = 0)) :
    (¬ ∃ f : ℕ ≃ A, ¬HasMonotoneAP (Subtype.val ∘ f) 3) ∧
      ¬ ∃ g : ℕ ≃ B, ¬HasMonotoneAP (Subtype.val ∘ g) 3 := by
  refine ⟨fun ⟨f, hf⟩ => Erdos197Tower.drifting_sub r hr h0 hlim 0 (by norm_num) A
    (fun k n hk h1 h2 => (hA k n h1 h2).2 hk) f hf, fun ⟨g, hg⟩ => ?_⟩
  refine Erdos197Tower.drifting_sub r hr h0 hlim 1 (by norm_num) B (fun k n hk h1 h2 => ?_) g hg
  have hn : n ∈ Aᶜ := fun hn => by have := (hA k n h1 h2).1 hn; omega
  rwa [hAB.compl_eq] at hn

#print axioms fc_tower
#print axioms fc_clean
#print axioms fc_main
#print axioms fc_erdos197_runs
