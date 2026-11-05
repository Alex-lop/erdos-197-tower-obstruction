module

public import Erdos197Interval.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

/-!
# Theorem R\*, Corollary R0\* and Corollary R2\*

The proof follows `docs/proof.md`. An order of `S ⊆ ℕ` is given by an injective ranking
`ρ : ℕ → ℕ` on `S`: `x` comes before `y` when `ρ x < ρ y`.

* `Adm S ρ`: `ρ` is injective on `S` and obeys the *midpoint rule* on `S` (the middle term of
  every 3-term AP of `S` comes before both ends or after both), i.e. no monotone 3-term AP.
  `adm_of_enum` gets such a `ρ` (the position `f.symm`) from an enumeration `f : ℕ ≃ S` with no
  monotone 3-term AP (formal-conjectures' predicate, unfolded).
* `witness` (Lemma W\*): Theorem I (`Erdos197Interval.gadget_thm`) pulled back along the affine
  map `k ↦ w + δ k`. If `w, w + δ ∈ S` and `w + δ [M, 2M + 6] ⊆ S` (`M ≥ 8`), some
  `w + δ (M + j)`, `j ≤ 3`, comes before `w` or before `w + δ`.
* `step` (Lemma S): five overlapping blocks give a new pair `w', w' + δ'` inside the next
  interval, with `δ ≤ δ' ≤ 4δ`, both points before the later of `w, w + δ`.
* `tower_levels`, `tower_adm` (Theorem R\*): induction on the level `k`, invariants (J1)–(J4);
  the position of the later point of the pair drops by at least one per level, which is
  impossible for more than `P₀` levels.
* `clean_adm` (Corollary R0\*): Theorem R\* with `u = b 0 - 1`, `d = 1`.
* `ratio_bounds`, `six_terms`, `drifting_adm` (Corollary R2\*): eventually
  `1.99 r k < r (k + 1) < 2.01 r k`, and the runs `[r k, r (k + 1) - 1]` with `k = K + 4m`
  (`K ≡ c mod 2`) satisfy the hypotheses of Corollary R0\*. `drifting_sub` is the form for any
  set containing the runs of one colour.
* `tower_thm`, `clean_thm` and `drifting` prove the three statements of `Challenge.lean`;
  `Solution.lean` restates them as `tower`, `clean` and `main_result`.

All arithmetic side conditions are discharged by `omega` (products such as `δ * M` are atoms);
the limit is used once, with `ε = 1/100`.
-/

namespace Erdos197Tower

open Erdos197Interval

/-- `ρ` ranks the elements of `S` injectively, and the middle term `y` of every 3-term AP
`x < y < z` of `S` comes before both ends or after both (the *midpoint rule*). -/
structure Adm (S : Set ℕ) (ρ : ℕ → ℕ) : Prop where
  inj : ∀ x y, x ∈ S → y ∈ S → ρ x = ρ y → x = y
  mid : ∀ x y z, x ∈ S → y ∈ S → z ∈ S → x < y → x + z = 2 * y → (ρ y < ρ x ↔ ρ y < ρ z)

/-- The positions `f.symm` of an enumeration `f : ℕ ≃ S` with no monotone 3-term AP
(formal-conjectures' predicate, unfolded) form an admissible ranking of `S`. -/
theorem adm_of_enum (S : Set ℕ) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·)) :
    ∃ ρ : ℕ → ℕ, Adm S ρ := by
  classical
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℕ, ∀ x (hx : x ∈ S), ρ x = f.symm ⟨x, hx⟩ :=
    ⟨fun x => if hx : x ∈ S then f.symm ⟨x, hx⟩ else 0, fun x hx => by simp [hx]⟩
  have hfρ : ∀ x, x ∈ S → (f (ρ x) : ℕ) = x := fun x hx => by simp [hρ x hx]
  have inj : ∀ x y, x ∈ S → y ∈ S → ρ x = ρ y → x = y := fun x y hx hy h => by
    rw [← hfρ x hx, ← hfρ y hy, h]
  refine ⟨ρ, ⟨inj, fun x y z hx hy hz hxy hxz => ?_⟩⟩
  have ex := hfρ x hx
  have ey := hfρ y hy
  have ez := hfρ z hz
  have n₁ : ρ y ≠ ρ x := fun e => by have := inj y x hy hx e; omega
  have n₂ : ρ y ≠ ρ z := fun e => by have := inj y z hy hz e; omega
  constructor
  · intro h
    by_contra h'
    exact no_ap hf (p := ρ z) (q := ρ y) (r := ρ x) (by omega) h
      (by simp only [Function.comp_apply, ex, ey, ez]; omega)
  · intro h
    by_contra h'
    exact no_ap hf (p := ρ x) (q := ρ y) (r := ρ z) (by omega) h
      (by simp only [Function.comp_apply, ex, ey, ez]; omega)

variable {S : Set ℕ} {ρ : ℕ → ℕ}

/-- **Lemma W\*.** Theorem I pulled back along `k ↦ w + δ k`: if `w, w + δ ∈ S` and
`w + δ k ∈ S` for `M ≤ k ≤ 2M + 6` (`M ≥ 8`), then some `w + δ (M + j)` with `j ≤ 3` comes
before `w + δ a` for some `a ≤ 1`. -/
theorem witness (hρ : Adm S ρ) {w δ M : ℕ} (hδ : 1 ≤ δ) (hM : 8 ≤ M) (hw : w ∈ S)
    (hwδ : w + δ ∈ S) (hX : ∀ k, M ≤ k → k ≤ 2 * M + 6 → w + δ * k ∈ S) :
    ∃ j a, j ≤ 3 ∧ a ≤ 1 ∧ ρ (w + δ * (M + j)) < ρ (w + δ * a) := by
  -- (W7) the affine map sends 3-term APs to 3-term APs; (W8) it is strictly increasing
  have key : ∀ x y z, x + z = 2 * y → (w + δ * x) + (w + δ * z) = 2 * (w + δ * y) := by
    intro x y z h
    have : δ * x + δ * z = 2 * (δ * y) := by rw [← mul_add, h]; ring
    omega
  have mono : ∀ x y, x < y → w + δ * x < w + δ * y := fun x y h => by
    have := Nat.mul_lt_mul_of_pos_left h (by omega : δ > 0)
    omega
  have hinj : Set.InjOn (fun k => ρ (w + δ * k)) (Set.Icc M (2 * M + 6)) := by
    intro x hx y hy h
    rw [Set.mem_Icc] at hx hy
    have := hρ.inj _ _ (hX x hx.1 hx.2) (hX y hy.1 hy.2) h
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · have := mono x y hxy; omega
    · rfl
    · have := mono y x hxy; omega
  have hAP : ∀ x y z : ℕ, x ∈ Set.Icc M (2 * M + 6) → z ∈ Set.Icc M (2 * M + 6) →
      x < y → y < z → y - x = z - y →
        ¬ (ρ (w + δ * x) < ρ (w + δ * y) ∧ ρ (w + δ * y) < ρ (w + δ * z)) ∧
          ¬ (ρ (w + δ * z) < ρ (w + δ * y) ∧ ρ (w + δ * y) < ρ (w + δ * x)) := by
    intro x y z hx hz hxy hyz hd
    rw [Set.mem_Icc] at hx hz
    have hxS := hX x hx.1 hx.2
    have hyS := hX y (by omega) (by omega)
    have hzS := hX z hz.1 hz.2
    have hm := hρ.mid _ _ _ hxS hyS hzS (mono x y hxy) (key x y z (by omega))
    have n₁ : ρ (w + δ * y) ≠ ρ (w + δ * x) := fun e => by
      have := hρ.inj _ _ hyS hxS e
      have := mono x y hxy
      omega
    have n₂ : ρ (w + δ * y) ≠ ρ (w + δ * z) := fun e => by
      have := hρ.inj _ _ hyS hzS e
      have := mono y z hyz
      omega
    omega
  -- Theorem I: some anchor constraint fails
  have hg := gadget_thm M hM (fun k => ρ (w + δ * k)) hinj hAP
  push Not at hg
  obtain ⟨j, a, hj, ha, hle⟩ := hg
  refine ⟨j, a, hj, ha, ?_⟩
  have hyS := hX (M + j) (by omega) (by omega)
  have hzS := hX (2 * (M + j) - a) (by omega) (by omega)
  have hxS : w + δ * a ∈ S := by
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
    · simpa using hw
    · simpa using hwδ
  -- `y = w + δ (M + j)` comes before `z = w + δ (2 (M + j) - a)`; the midpoint rule at
  -- `x = w + δ a < y < z` puts `y` before `x`
  have hne : ρ (w + δ * (M + j)) ≠ ρ (w + δ * (2 * (M + j) - a)) := fun e => by
    have := hρ.inj _ _ hyS hzS e
    have := mono (M + j) (2 * (M + j) - a) (by omega)
    omega
  have hlt : ρ (w + δ * (M + j)) < ρ (w + δ * (2 * (M + j) - a)) := by
    have hle' : ρ (w + δ * (M + j)) ≤ ρ (w + δ * (2 * (M + j) - a)) := hle
    omega
  exact (hρ.mid _ _ _ hxS hyS hzS (mono a (M + j) (by omega))
    (key a (M + j) (2 * (M + j) - a) (by omega))).2 hlt

/-- **Lemma S.** Let `w, w + δ ∈ S` (`δ ≥ 1`) and `[α, β] ⊆ S` with (a) `α ≥ w + 8δ` and
(b) `β ≥ 2α - w + 16δ`. Then `[α, β]` contains a pair `w', w' + δ'` with `δ ≤ δ' ≤ 4δ` whose
two points both come before the later of `w` and `w + δ`. -/
theorem step (hρ : Adm S ρ) {w δ α β : ℕ} (hδ : 1 ≤ δ) (hw : w ∈ S) (hwδ : w + δ ∈ S)
    (hI : ∀ x, α ≤ x → x ≤ β → x ∈ S) (ha : w + 8 * δ ≤ α) (hb : 2 * α + 16 * δ ≤ w + β) :
    ∃ w' δ', δ ≤ δ' ∧ δ' ≤ 4 * δ ∧ α ≤ w' ∧ w' + δ' ≤ β ∧
      ρ w' < max (ρ w) (ρ (w + δ)) ∧ ρ (w' + δ') < max (ρ w) (ρ (w + δ)) := by
  -- (S0) `M = ⌈(α - w) / δ⌉`, (S1) `M ≥ 8`
  obtain ⟨M, hM1, hM2⟩ : ∃ M, α ≤ w + δ * M ∧ w + δ * M < α + δ := by
    refine ⟨(α - w + δ - 1) / δ, ?_⟩
    have h1 := Nat.div_add_mod (α - w + δ - 1) δ
    have h2 := Nat.mod_lt (α - w + δ - 1) (by omega : δ > 0)
    omega
  have hM : 8 ≤ M := by
    by_contra h
    have := Nat.mul_le_mul_left δ (by omega : M ≤ 7)
    omega
  -- (S2), (S3), (S6): `w + δ k ∈ [α, β]` for `M ≤ k ≤ 2M + 14`
  have range : ∀ k, M ≤ k → k ≤ 2 * M + 14 → α ≤ w + δ * k ∧ w + δ * k ≤ β := by
    intro k h1 h2
    have e1 := Nat.mul_le_mul_left δ h1
    have e2 := Nat.mul_le_mul_left δ h2
    have e3 : δ * (2 * M + 14) = 2 * (δ * M) + 14 * δ := by ring
    omega
  -- five applications of Lemma W*, at `M, M + 1, …, M + 4`
  have W : ∀ t, t ≤ 4 → ∃ j a, j ≤ 3 ∧ a ≤ 1 ∧ ρ (w + δ * (M + t + j)) < ρ (w + δ * a) :=
    fun t ht => witness hρ hδ (M := M + t) (by omega) hw hwδ fun k h1 h2 =>
      hI _ (range k (by omega) (by omega)).1 (range k (by omega) (by omega)).2
  choose! j a hj ha hW using W
  have hmax : ∀ t, t ≤ 4 → ρ (w + δ * (M + t + j t)) < max (ρ w) (ρ (w + δ)) := by
    intro t ht
    have h := hW t ht
    rcases (by have := ha t ht; omega : a t = 0 ∨ a t = 1) with e | e
    · rw [e, mul_zero, add_zero] at h
      exact lt_max_of_lt_left h
    · rw [e, mul_one] at h
      exact lt_max_of_lt_right h
  -- (S4), (S5): two consecutive witnesses differ
  obtain ⟨t, ht, hne⟩ : ∃ t, t < 4 ∧ M + t + j t ≠ M + (t + 1) + j (t + 1) := by
    by_contra h
    have h0 : M + 0 + j 0 = M + 1 + j 1 := by by_contra h'; exact h ⟨0, by omega, h'⟩
    have h1 : M + 1 + j 1 = M + 2 + j 2 := by by_contra h'; exact h ⟨1, by omega, h'⟩
    have h2 : M + 2 + j 2 = M + 3 + j 3 := by by_contra h'; exact h ⟨2, by omega, h'⟩
    have h3 : M + 3 + j 3 = M + 4 + j 4 := by by_contra h'; exact h ⟨3, by omega, h'⟩
    have := hj 0 (by omega)
    omega
  -- the new pair: the two witnesses, `δ' = e δ` with `1 ≤ e ≤ 4`
  have pair : ∀ m e, 1 ≤ e → e ≤ 4 → M ≤ m → m + e ≤ M + 7 →
      ρ (w + δ * m) < max (ρ w) (ρ (w + δ)) → ρ (w + δ * (m + e)) < max (ρ w) (ρ (w + δ)) →
      ∃ w' δ', δ ≤ δ' ∧ δ' ≤ 4 * δ ∧ α ≤ w' ∧ w' + δ' ≤ β ∧
        ρ w' < max (ρ w) (ρ (w + δ)) ∧ ρ (w' + δ') < max (ρ w) (ρ (w + δ)) := by
    intro m e he1 he4 hm1 hm2 hρm hρm'
    have e1 := Nat.mul_le_mul_left δ he1
    have e4 := Nat.mul_le_mul_left δ he4
    have hsum : w + δ * m + δ * e = w + δ * (m + e) := by ring
    refine ⟨w + δ * m, δ * e, by omega, by omega, (range m hm1 (by omega)).1, ?_, hρm, ?_⟩
    · rw [hsum]; exact (range (m + e) (by omega) (by omega)).2
    · rw [hsum]; exact hρm'
  have h₁ := hmax t (by omega)
  have h₂ := hmax (t + 1) (by omega)
  have := hj t (by omega)
  have := hj (t + 1) (by omega)
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨e, he⟩ : ∃ e, M + (t + 1) + j (t + 1) = M + t + j t + e :=
      ⟨_, (Nat.add_sub_of_le h.le).symm⟩
    rw [he] at h₂
    exact pair _ e (by omega) (by omega) (by omega) (by omega) h₁ h₂
  · obtain ⟨e, he⟩ : ∃ e, M + t + j t = M + (t + 1) + j (t + 1) + e :=
      ⟨_, (Nat.add_sub_of_le h.le).symm⟩
    rw [he] at h₁
    exact pair _ e (by omega) (by omega) (by omega) (by omega) h₂ h₁

/-- **Theorem R\*** for an admissible ranking: the induction (J1)–(J4). At level `k` there is a
pair `w, w + δ` in `S` with `1 ≤ δ ≤ 4^k d`, satisfying the hypotheses (a), (b) of Lemma S for the
interval `[α (k + 1), β (k + 1)]`, whose later point has position at most `P₀ - k`. -/
theorem tower_levels (hρ : Adm S ρ) (u d : ℕ) (hd : 1 ≤ d) (hu : u ∈ S) (hud : u + d ∈ S)
    (α β : ℕ → ℕ) (hI : ∀ k, 1 ≤ k → Set.Icc (α k) (β k) ⊆ S)
    (hT1a : u + 8 * d ≤ α 1) (hT1b : 2 * α 1 + 16 * d ≤ u + β 1)
    (hT2a : ∀ k, 1 ≤ k → β k + 8 * 4 ^ k * d ≤ α (k + 1))
    (hT2b : ∀ k, 1 ≤ k → 2 * α (k + 1) + 16 * 4 ^ k * d ≤ α k + β (k + 1)) (k : ℕ) :
    ∃ w δ, w ∈ S ∧ w + δ ∈ S ∧ 1 ≤ δ ∧ δ ≤ 4 ^ k * d ∧
      w + 8 * δ ≤ α (k + 1) ∧ 2 * α (k + 1) + 16 * δ ≤ w + β (k + 1) ∧
      max (ρ w) (ρ (w + δ)) + k ≤ max (ρ u) (ρ (u + d)) := by
  induction k with
  | zero => exact ⟨u, d, hu, hud, hd, by simp, hT1a, hT1b, by simp⟩
  | succ k ih =>
    obtain ⟨w, δ, hw, hwδ, hδ1, hδ2, ha, hb, hP⟩ := ih
    have hIk : ∀ x, α (k + 1) ≤ x → x ≤ β (k + 1) → x ∈ S := fun x h1 h2 =>
      hI (k + 1) (by omega) (Set.mem_Icc.2 ⟨h1, h2⟩)
    obtain ⟨w', δ', h1, h2, h3, h4, h5, h6⟩ := step hρ hδ1 hw hwδ hIk ha hb
    -- (J2) `δ' ≤ 4 δ ≤ 4^(k+1) d`; (P1), (P2) from (T2*) at `k + 1`
    have hq : 4 ^ (k + 1) * d = 4 * (4 ^ k * d) := by ring
    have T2a := hT2a (k + 1) (by omega)
    have T2b := hT2b (k + 1) (by omega)
    have e8 : 8 * 4 ^ (k + 1) * d = 8 * (4 ^ (k + 1) * d) := by ring
    have e16 : 16 * 4 ^ (k + 1) * d = 16 * (4 ^ (k + 1) * d) := by ring
    -- (J4) the later point moves strictly earlier
    have hlt := max_lt h5 h6
    exact ⟨w', δ', hIk _ h3 (by omega), hIk _ (by omega) h4, by omega, by omega, by omega,
      by omega, by omega⟩

/-- **Theorem R\*** for an admissible ranking. -/
theorem tower_adm (hρ : Adm S ρ) (u d : ℕ) (hd : 1 ≤ d) (hu : u ∈ S) (hud : u + d ∈ S)
    (α β : ℕ → ℕ) (hI : ∀ k, 1 ≤ k → Set.Icc (α k) (β k) ⊆ S)
    (hT1a : u + 8 * d ≤ α 1) (hT1b : 2 * α 1 + 16 * d ≤ u + β 1)
    (hT2a : ∀ k, 1 ≤ k → β k + 8 * 4 ^ k * d ≤ α (k + 1))
    (hT2b : ∀ k, 1 ≤ k → 2 * α (k + 1) + 16 * 4 ^ k * d ≤ α k + β (k + 1)) : False := by
  obtain ⟨w, δ, -, -, -, -, -, -, hP⟩ := tower_levels hρ u d hd hu hud α β hI hT1a hT1b hT2a hT2b
    (max (ρ u) (ρ (u + d)) + 1)
  omega

/-- **Theorem R\*** (the statement of `Erdos197Tower.tower` in `Challenge.lean`). -/
theorem tower_thm (S : Set ℕ) (f : ℕ ≃ S)
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
  obtain ⟨ρ, hρ⟩ := adm_of_enum S f hf
  exact tower_adm hρ u d hd hu hud α β hI hT1a hT1b hT2a hT2b

/-- **Corollary R0\*** for an admissible ranking: Theorem R\* with `u = b 0 - 1`, `d = 1`,
`[α k, β k] = [a k, b k]`. -/
theorem clean_adm (hρ : Adm S ρ) (a b : ℕ → ℕ) (hI : ∀ j, Set.Icc (a j) (b j) ⊆ S)
    (h32 : 32 ≤ a 0) (h01 : a 0 + 1 ≤ b 0) (hgrow : ∀ j, 4 * b j ≤ a (j + 1))
    (hdef : ∀ j, 4 * a (j + 1) ≤ a j + 2 * b (j + 1)) : False := by
  -- (R0c), (R0g): `a k ≥ 32 · 4^k` and `b k ≥ a k + 1`
  have inv : ∀ k, 32 * 4 ^ k ≤ a k ∧ a k + 1 ≤ b k := by
    intro k
    induction k with
    | zero => simpa using ⟨h32, h01⟩
    | succ k ih =>
      have := hgrow k
      have := hdef k
      have e : 4 ^ (k + 1) = 4 * 4 ^ k := by ring
      omega
  have mem : ∀ x, a 0 ≤ x → x ≤ b 0 → x ∈ S := fun x h1 h2 => hI 0 (Set.mem_Icc.2 ⟨h1, h2⟩)
  have g0 := hgrow 0
  have d0 := hdef 0
  simp only [zero_add] at g0 d0
  -- (R0f) `u = b 0 - 1`, `u + 1 = b 0`; (R0a), (R0b) give (T1*); (R0d), (R0e) give (T2*)
  refine tower_adm hρ (b 0 - 1) 1 le_rfl (mem _ (by omega) (by omega)) (mem _ (by omega) (by omega))
    a b (fun k _ => hI k) (by omega) (by omega) (fun k _ => ?_) (fun k _ => ?_)
  · have := hgrow k
    have := inv k
    omega
  · have := hdef k
    have := inv k
    omega

/-- **Corollary R0\*** (the statement of `Erdos197Tower.clean` in `Challenge.lean`). -/
theorem clean_thm (S : Set ℕ) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·))
    (a b : ℕ → ℕ) (hI : ∀ j, Set.Icc (a j) (b j) ⊆ S) (h32 : 32 ≤ a 0) (h01 : a 0 + 1 ≤ b 0)
    (hgrow : ∀ j, 4 * b j ≤ a (j + 1)) (hdef : ∀ j, 4 * a (j + 1) ≤ a j + 2 * b (j + 1)) :
    False := by
  obtain ⟨ρ, hρ⟩ := adm_of_enum S f hf
  exact clean_adm hρ a b hI h32 h01 hgrow hdef

/-- The limit `r (k + 1) / r k → 2`, used once with `ε = 1/100`: from some `K₀` on,
`1.99 r k < r (k + 1) < 2.01 r k`. -/
theorem ratio_bounds (r : ℕ → ℕ) (hr : StrictMono r) (h0 : 1 ≤ r 0)
    (hlim : Filter.Tendsto (fun k => (r (k + 1) : ℝ) / r k) Filter.atTop (nhds 2)) :
    ∃ K₀, ∀ k, K₀ ≤ k → 199 * r k < 100 * r (k + 1) ∧ 100 * r (k + 1) < 201 * r k := by
  obtain ⟨K₀, hK⟩ := Metric.tendsto_atTop.1 hlim (1 / 100) (by norm_num)
  refine ⟨K₀, fun k hk => ?_⟩
  have h := hK k hk
  rw [Real.dist_eq, abs_sub_lt_iff] at h
  have hpos : (0 : ℝ) < r k := by
    have : 1 ≤ r k := h0.trans (hr.monotone (Nat.zero_le k))
    exact_mod_cast (by omega : 0 < r k)
  have h1 : (199 / 100 : ℝ) < (r (k + 1) : ℝ) / r k := by linarith [h.2]
  have h2 : (r (k + 1) : ℝ) / r k < 201 / 100 := by linarith [h.1]
  rw [lt_div_iff₀ hpos] at h1
  rw [div_lt_iff₀ hpos] at h2
  constructor
  · have : (199 : ℝ) * r k < 100 * r (k + 1) := by linarith
    exact_mod_cast this
  · have : (100 : ℝ) * r (k + 1) < 201 * r k := by linarith
    exact_mod_cast this

/-- The arithmetic of Corollary R2\*: for six consecutive terms with ratios in `(1.99, 2.01)`
and `x₀ ≥ 32`, the runs `[x₀, x₁ - 1]` and `[x₄, x₅ - 1]` satisfy the two conditions of
Corollary R0\*. -/
theorem six_terms {x₀ x₁ x₂ x₃ x₄ x₅ : ℕ} (h32 : 32 ≤ x₀)
    (l₀ : 199 * x₀ < 100 * x₁) (l₁ : 199 * x₁ < 100 * x₂) (l₂ : 199 * x₂ < 100 * x₃)
    (l₃ : 199 * x₃ < 100 * x₄) (l₄ : 199 * x₄ < 100 * x₅)
    (u₀ : 100 * x₁ < 201 * x₀) (u₁ : 100 * x₂ < 201 * x₁) (u₂ : 100 * x₃ < 201 * x₂)
    (u₃ : 100 * x₄ < 201 * x₃) :
    4 * (x₁ - 1) ≤ x₄ ∧ 4 * x₄ ≤ x₀ + 2 * (x₅ - 1) := by
  omega

/-- **Corollary R2\*** for an admissible ranking of any set `S` that contains every run
`[r k, r (k + 1))` with `k ≡ c (mod 2)`. The runs `[r k, r (k + 1) - 1]` with `k = K + 4m`
(`K ≡ c (mod 2)`, `K ≥ K₀`, `K ≥ 64`) satisfy the hypotheses of Corollary R0\*. -/
theorem drifting_adm (r : ℕ → ℕ) (hr : StrictMono r) (h0 : 1 ≤ r 0)
    (hlim : Filter.Tendsto (fun k => (r (k + 1) : ℝ) / r k) Filter.atTop (nhds 2))
    (c : ℕ) (hc : c < 2) (hS : ∀ k n, k % 2 = c → r k ≤ n → n < r (k + 1) → n ∈ S)
    (hρ : Adm S ρ) : False := by
  obtain ⟨K₀, hK⟩ := ratio_bounds r hr h0 hlim
  obtain ⟨K, hKdef⟩ : ∃ K, K = 2 * (K₀ + 32) + c := ⟨_, rfl⟩
  have hge : ∀ k, k ≤ r k := fun k => hr.le_apply
  have run : ∀ m, 4 * (r (K + 4 * m + 1) - 1) ≤ r (K + 4 * m + 1 + 1 + 1 + 1) ∧
      4 * r (K + 4 * m + 1 + 1 + 1 + 1) ≤
        r (K + 4 * m) + 2 * (r (K + 4 * m + 1 + 1 + 1 + 1 + 1) - 1) := by
    intro m
    have := hge (K + 4 * m)
    exact six_terms (by omega) (hK (K + 4 * m) (by omega)).1
      (hK (K + 4 * m + 1) (by omega)).1 (hK (K + 4 * m + 1 + 1) (by omega)).1
      (hK (K + 4 * m + 1 + 1 + 1) (by omega)).1 (hK (K + 4 * m + 1 + 1 + 1 + 1) (by omega)).1
      (hK (K + 4 * m) (by omega)).2 (hK (K + 4 * m + 1) (by omega)).2
      (hK (K + 4 * m + 1 + 1) (by omega)).2 (hK (K + 4 * m + 1 + 1 + 1) (by omega)).2
  have shift : ∀ m, K + 4 * (m + 1) = K + 4 * m + 1 + 1 + 1 + 1 := fun m => by ring
  refine clean_adm hρ (fun m => r (K + 4 * m)) (fun m => r (K + 4 * m + 1) - 1) ?_ ?_ ?_ ?_ ?_
  · intro m x hx
    have hx' : r (K + 4 * m) ≤ x ∧ x ≤ r (K + 4 * m + 1) - 1 := hx
    have := hge (K + 4 * m + 1)
    exact hS (K + 4 * m) x (by omega) hx'.1 (by omega)
  · show 32 ≤ r (K + 4 * 0)
    have := hge (K + 4 * 0)
    omega
  · show r (K + 4 * 0) + 1 ≤ r (K + 4 * 0 + 1) - 1
    have := hge (K + 4 * 0)
    have := (hK (K + 4 * 0) (by omega)).1
    omega
  · intro m
    show 4 * (r (K + 4 * m + 1) - 1) ≤ r (K + 4 * (m + 1))
    rw [shift]
    exact (run m).1
  · intro m
    show 4 * r (K + 4 * (m + 1)) ≤ r (K + 4 * m) + 2 * (r (K + 4 * (m + 1) + 1) - 1)
    rw [shift]
    exact (run m).2

/-- Superset form of the colouring statement of **Corollary R2\*** (not the refereed "more generally"
sentence, which is not formalized): a set `S ⊆ ℕ` that contains every run `[r k, r (k + 1))`
with `k ≡ c (mod 2)` has no enumeration without monotone 3-term APs (formal-conjectures'
predicate, unfolded). -/
theorem drifting_sub (r : ℕ → ℕ) (hr : StrictMono r) (h0 : 1 ≤ r 0)
    (hlim : Filter.Tendsto (fun k => (r (k + 1) : ℝ) / r k) Filter.atTop (nhds 2))
    (c : ℕ) (hc : c < 2) (S : Set ℕ)
    (hS : ∀ k n, k % 2 = c → r k ≤ n → n < r (k + 1) → n ∈ S) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·)) :
    False := by
  obtain ⟨ρ, hρ⟩ := adm_of_enum S f hf
  exact drifting_adm r hr h0 hlim c hc hS hρ

/-- **Corollary R2\*** (the statement of `Erdos197Tower.main_result` in `Challenge.lean`). -/
theorem drifting (r : ℕ → ℕ) (hr : StrictMono r) (h0 : 1 ≤ r 0)
    (hlim : Filter.Tendsto (fun k => (r (k + 1) : ℝ) / r k) Filter.atTop (nhds 2))
    (c : ℕ) (hc : c < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | ∃ k, k % 2 = c ∧ r k ≤ n ∧ n < r (k + 1)},
      ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·) := by
  rintro ⟨f, hf⟩
  exact drifting_sub r hr h0 hlim c hc {n : ℕ | ∃ k, k % 2 = c ∧ r k ≤ n ∧ n < r (k + 1)}
    (fun k n hk h1 h2 => ⟨k, hk, h1, h2⟩) f hf

end Erdos197Tower
