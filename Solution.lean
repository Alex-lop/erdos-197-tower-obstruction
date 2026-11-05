module

public import Erdos197Tower

public section

/-!
# Proved solution

Comparator checks that the declarations below have exactly the statements of their
counterparts in `Challenge.lean` and use only the permitted axioms. The proofs live in
`Erdos197Tower/Basic.lean`, which builds on Theorem I (`Erdos197Interval.gadget_thm` in
`Erdos197Interval/Basic.lean`, a verbatim copy of the module of
<https://github.com/Alex-lop/erdos-197-interval-gadget>).
-/

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
    False :=
  Erdos197Tower.tower_thm S f hf u d hd hu hud α β hI hT1a hT1b hT2a hT2b

theorem Erdos197Tower.clean (S : Set ℕ) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·))
    (a b : ℕ → ℕ) (hI : ∀ j, Set.Icc (a j) (b j) ⊆ S) (h32 : 32 ≤ a 0) (h01 : a 0 + 1 ≤ b 0)
    (hgrow : ∀ j, 4 * b j ≤ a (j + 1)) (hdef : ∀ j, 4 * a (j + 1) ≤ a j + 2 * b (j + 1)) :
    False :=
  Erdos197Tower.clean_thm S f hf a b hI h32 h01 hgrow hdef

theorem Erdos197Tower.main_result (r : ℕ → ℕ) (hr : StrictMono r) (h0 : 1 ≤ r 0)
    (hlim : Filter.Tendsto (fun k => (r (k + 1) : ℝ) / r k) Filter.atTop (nhds 2))
    (c : ℕ) (hc : c < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | ∃ k, k % 2 = c ∧ r k ≤ n ∧ n < r (k + 1)},
      ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·) :=
  Erdos197Tower.drifting r hr h0 hlim c hc
