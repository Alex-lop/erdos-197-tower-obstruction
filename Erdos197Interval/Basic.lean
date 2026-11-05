module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Ring

public section

/-!
# Theorem I and Corollary I

The proof follows `docs/proof.md`. A linear order of the interval `I = [L, R]` is given by an
injective ranking `σ : ℕ → ℕ`: `u` comes before `w` when `σ u < σ w`.

* `Good L R σ`: `σ` is injective on `[L, R]` and obeys the *midpoint rule* (the middle term of
  every 3-term AP of `[L, R]` comes before both ends or after both), i.e. no monotone 3-term AP.
* `Good.alt` (Lemma 1, zigzag): along a ladder of step `g` the orientation of consecutive rungs
  alternates.
* `Good.flood` (Lemma 2, flood): around a centre `c`, every `c ± e` with `e` an odd multiple of
  `h` relates to `c` as `c + h` does. `Good.ruleA` and `Good.ruleB` are the cases `h = 1, 2`.
* `Good.lead_iff`: the leading parity of the 1-ladder `[L, R]`.
* `Good.lemmaI`, `Good.lemmaII` (Lemmas I and II) and `gadget_core`: the 16-case analysis
  (`M mod 8` times the leading parity) refuting the eight anchor constraints on `[M, 2M + 6]`.
* `gadget_thm` (Theorem I) and `corollary` (Corollary I) prove the two statements of
  `Challenge.lean`; `Solution.lean` restates them as `gadget` and `main_result`. `no_ap` turns
  the unfolded formal-conjectures predicate into "no positions `p < q < r` carry a 3-term AP";
  the anchor rule inside `corollary` is the midpoint rule at `(f, w, 2w - f)`.

All arithmetic side conditions are discharged by `omega`. To keep `omega`'s atoms `σ x`
syntactically aligned, points are introduced as variables with linear defining equations.
-/

namespace Erdos197Interval

/-- `σ` ranks the integers of `[L, R]` injectively, and the middle term `y` of every 3-term AP
`x < y < z` of `[L, R]` comes before both ends or after both (the *midpoint rule*). -/
structure Good (L R : ℕ) (σ : ℕ → ℕ) : Prop where
  inj : ∀ x y, L ≤ x → x ≤ R → L ≤ y → y ≤ R → σ x = σ y → x = y
  mid : ∀ x y z, L ≤ x → z ≤ R → x < y → x + z = 2 * y → (σ y < σ x ↔ σ y < σ z)

namespace Good

variable {L R : ℕ} {σ : ℕ → ℕ}

theorem ne (hσ : Good L R σ) {x y : ℕ} (h : L ≤ x ∧ x ≤ R ∧ L ≤ y ∧ y ≤ R ∧ x ≠ y) :
    σ x ≠ σ y := fun e => h.2.2.2.2 (hσ.inj x y h.1 h.2.1 h.2.2.1 h.2.2.2.1 e)

/-- **Lemma 1 (zigzag).** On a ladder of step `g`, the orientation of the rung pair
`(w', w' + g)` equals that of `(w, w + g)` when `w' - w` is an even multiple of `g`. -/
theorem alt (hσ : Good L R σ) {g : ℕ} (hg : 0 < g) (m : ℕ) :
    ∀ w w₁ w' w'₁, w₁ = w + g → w' = w + 2 * g * m → w'₁ = w' + g → L ≤ w → w'₁ ≤ R →
      (σ w' < σ w'₁ ↔ σ w < σ w₁) := by
  induction m with
  | zero =>
    intro w w₁ w' w'₁ h₁ h' h'₁ _ _
    obtain rfl : w' = w := by simpa using h'
    obtain rfl : w'₁ = w₁ := by omega
    exact Iff.rfl
  | succ m ih =>
    intro w w₁ w' w'₁ h₁ h' h'₁ hL hR
    have e : 2 * g * (m + 1) = 2 * g * m + 2 * g := by ring
    -- the rungs `a < a₁ < w' < w'₁`, spaced by `g`
    obtain ⟨a, ha⟩ : ∃ a, a = w + 2 * g * m := ⟨_, rfl⟩
    obtain ⟨a₁, ha₁⟩ : ∃ a₁, a₁ = a + g := ⟨_, rfl⟩
    have IH := ih w w₁ a a₁ h₁ ha ha₁ hL (by omega)
    have m₁ := hσ.mid a a₁ w' (by omega) (by omega) (by omega) (by omega)
    have m₂ := hσ.mid a₁ w' w'₁ (by omega) (by omega) (by omega) (by omega)
    have n₁ := hσ.ne (x := a) (y := a₁) (by omega)
    have n₂ := hσ.ne (x := a₁) (y := w') (by omega)
    omega

/-- **Lemma 2 (flood), right-hand form.** If `e = h (2k + 1)` and `c ± e ∈ [L, R]`, then `c`
precedes `c + e` iff it precedes `c + h`. -/
theorem flood (hσ : Good L R σ) {h c c₁ : ℕ} (hh : 0 < h) (hc₁ : c₁ = c + h) (k : ℕ) :
    ∀ w, w = c + h * (2 * k + 1) → L + h * (2 * k + 1) ≤ c → w ≤ R →
      (σ c < σ w ↔ σ c < σ c₁) := by
  induction k with
  | zero =>
    intro w hw _ _
    obtain rfl : w = c₁ := by rw [hw, hc₁]; ring
    exact Iff.rfl
  | succ k ih =>
    intro w hw hL hR
    obtain ⟨e, he⟩ : ∃ e, e = h * (2 * k + 1) := ⟨_, rfl⟩
    have e₀ : h ≤ e := he ▸ Nat.le_mul_of_pos_right h (by omega)
    have e₁ : h * (2 * (k + 1) + 1) = e + 2 * h := by rw [he]; ring
    have e₂ : 2 * (2 * h) * (k + 1) = 2 * e + 2 * h := by rw [he]; ring
    -- the points `ym < xm < c < xp < w`, at distances `e + 2h` and `e` from `c`
    obtain ⟨xp, hxp⟩ : ∃ x, x = c + e := ⟨_, rfl⟩
    obtain ⟨xm, hxm⟩ : ∃ x, x = c - e := ⟨_, rfl⟩
    obtain ⟨ym, hym⟩ : ∃ x, x = c - e - 2 * h := ⟨_, rfl⟩
    have IH := ih xp (by omega) (by omega) (by omega)
    -- `xp - ym = 2e + 2h` is an even multiple of the step `2h`
    have A := hσ.alt (g := 2 * h) (by omega) (k + 1) ym xm xp w
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have m₁ := hσ.mid xm c xp (by omega) (by omega) (by omega) (by omega)
    have m₂ := hσ.mid ym c w (by omega) (by omega) (by omega) (by omega)
    have n₁ := hσ.ne (x := c) (y := xp) (by omega)
    have n₂ := hσ.ne (x := c) (y := w) (by omega)
    have n₃ := hσ.ne (x := c) (y := xm) (by omega)
    have n₄ := hσ.ne (x := c) (y := ym) (by omega)
    have n₅ := hσ.ne (x := ym) (y := xm) (by omega)
    have n₆ := hσ.ne (x := xp) (y := w) (by omega)
    omega

/-- **Lemma 2 (flood), two-sided form.** `w` and `w' = 2x - w` lie in `[L, R]` and one of them
is `x + h (2k + 1)`; then `x` precedes `w` iff it precedes `x + h`. -/
theorem rule (hσ : Good L R σ) {h x x₁ w w' : ℕ} (hh : 0 < h) (hx₁ : x₁ = x + h)
    (hww' : w + w' = 2 * x) (hw : L ≤ w ∧ w ≤ R) (hw' : L ≤ w' ∧ w' ≤ R) (k : ℕ)
    (hk : w = x + h * (2 * k + 1) ∨ w' = x + h * (2 * k + 1)) :
    σ x < σ w ↔ σ x < σ x₁ := by
  have e₀ : h ≤ h * (2 * k + 1) := Nat.le_mul_of_pos_right h (by omega)
  rcases hk with hk | hk
  · exact hσ.flood hh hx₁ k w hk (by omega) (by omega)
  · rw [← hσ.flood hh hx₁ k w' hk (by omega) (by omega)]
    exact hσ.mid w x w' (by omega) (by omega) (by omega) (by omega)

/-- **Rule A.** If `w - x` is odd and `w, 2x - w ∈ [L, R]`, then `x` precedes `w` iff `x`
precedes `x + 1`. -/
theorem ruleA (hσ : Good L R σ) {x x₁ w : ℕ} (hx₁ : x₁ = x + 1)
    (h : L ≤ w ∧ w ≤ R ∧ L + w ≤ 2 * x ∧ 2 * x ≤ R + w ∧ (w + x) % 2 = 1) :
    σ x < σ w ↔ σ x < σ x₁ := by
  have hww' : w + (2 * x - w) = 2 * x := by omega
  rcases le_total x w with h' | h'
  · exact hσ.rule one_pos hx₁ hww' ⟨h.1, h.2.1⟩ ⟨by omega, by omega⟩ ((w - x) / 2)
      (Or.inl (by omega))
  · exact hσ.rule one_pos hx₁ hww' ⟨h.1, h.2.1⟩ ⟨by omega, by omega⟩ ((x - w) / 2)
      (Or.inr (by omega))

/-- **Rule B.** If `w - x ≡ 2 (mod 4)` and `w, 2x - w ∈ [L, R]`, then `x` precedes `w` iff `x`
precedes `x + 2`. -/
theorem ruleB (hσ : Good L R σ) {x x₂ w : ℕ} (hx₂ : x₂ = x + 2)
    (h : L ≤ w ∧ w ≤ R ∧ L + w ≤ 2 * x ∧ 2 * x ≤ R + w ∧ w % 4 = (x + 2) % 4) :
    σ x < σ w ↔ σ x < σ x₂ := by
  have hww' : w + (2 * x - w) = 2 * x := by omega
  rcases le_total x w with h' | h'
  · exact hσ.rule two_pos hx₂ hww' ⟨h.1, h.2.1⟩ ⟨by omega, by omega⟩ ((w - x) / 4)
      (Or.inl (by omega))
  · exact hσ.rule two_pos hx₂ hww' ⟨h.1, h.2.1⟩ ⟨by omega, by omega⟩ ((x - w) / 4)
      (Or.inr (by omega))

/-- Points of the same parity have the same orientation towards their right neighbour. -/
theorem par (hσ : Good L R σ) {x x₁ y y₁ : ℕ} (hx₁ : x₁ = x + 1) (hy₁ : y₁ = y + 1)
    (hx : L ≤ x) (hy : L ≤ y) (hxR : x₁ ≤ R) (hyR : y₁ ≤ R) (hxy : x % 2 = y % 2) :
    σ x < σ x₁ ↔ σ y < σ y₁ := by
  rcases le_total x y with h | h
  · exact (hσ.alt one_pos ((y - x) / 2) x x₁ y y₁ hx₁ (by omega) hy₁ hx hyR).symm
  · exact hσ.alt one_pos ((x - y) / 2) y y₁ x x₁ hy₁ (by omega) hx₁ hy hxR

/-- **Leading parity.** `x` precedes `x + 1` iff (`L` precedes `L + 1` iff `x ≡ L (mod 2)`). -/
theorem lead_iff (hσ : Good L R σ) (hLR : L + 2 ≤ R) {x x₁ : ℕ} (hx₁ : x₁ = x + 1)
    (hx : L ≤ x) (hxR : x₁ ≤ R) :
    σ x < σ x₁ ↔ (σ L < σ (L + 1) ↔ x % 2 = L % 2) := by
  have m := hσ.mid L (L + 1) (L + 2) le_rfl hLR (by omega) (by omega)
  have n₁ := hσ.ne (x := L) (y := L + 1) (by omega)
  have n₂ := hσ.ne (x := L + 1) (y := L + 2) (by omega)
  by_cases h : x % 2 = L % 2
  · have := hσ.par (y := L) (y₁ := L + 1) hx₁ rfl hx le_rfl hxR (by omega) h
    omega
  · have := hσ.par (y := L + 1) (y₁ := L + 2) hx₁ rfl hx (by omega) hxR (by omega) (by omega)
    omega

/-- **Lemma I (two adjacent centres).** Let `c` and `c + 2` have the leading parity, and let
`u ≺ b`, `u' ≺ b'` be anchor constraints such that Rule A applies at `c` towards `u` and at
`c + 2` towards `u'`, and Rule B at `c` towards `b` and at `c + 2` towards `b'`. Then both `c`
and `c + 2` precede their right `2`-neighbours, which is impossible. -/
theorem lemmaI (hσ : Good L R σ) {c u b u' b' : ℕ} (hLR : L + 2 ≤ R)
    (hbr : σ L < σ (L + 1) ↔ c % 2 = L % 2) (hc : L + 2 ≤ c ∧ c + 4 ≤ R)
    (U : σ u < σ b) (U' : σ u' < σ b')
    (h₁ : L ≤ u ∧ u ≤ R ∧ L + u ≤ 2 * c ∧ 2 * c ≤ R + u ∧ (u + c) % 2 = 1)
    (h₂ : L ≤ b ∧ b ≤ R ∧ L + b ≤ 2 * c ∧ 2 * c ≤ R + b ∧ b % 4 = (c + 2) % 4)
    (h₃ : L ≤ u' ∧ u' ≤ R ∧ L + u' ≤ 2 * (c + 2) ∧ 2 * (c + 2) ≤ R + u' ∧
      (u' + (c + 2)) % 2 = 1)
    (h₄ : L ≤ b' ∧ b' ≤ R ∧ L + b' ≤ 2 * (c + 2) ∧ 2 * (c + 2) ≤ R + b' ∧
      b' % 4 = (c + 2 + 2) % 4) :
    False := by
  -- `c` and `c + 2` precede their right neighbours (they have the leading parity)
  have l₁ := (hσ.lead_iff hLR (x₁ := c + 1) rfl (by omega) (by omega)).mpr hbr
  have l₂ := (hσ.lead_iff hLR (x₁ := c + 2 + 1) rfl (by omega) (by omega)).mpr
    (by rwa [Nat.add_mod_right])
  -- Rule A, anchor, Rule B: `c ≺ u ≺ b` gives `c ≺ c + 2`; `c + 2 ≺ u' ≺ b'` gives
  -- `c + 2 ≺ c + 4`
  have t₁ := (hσ.ruleB (x₂ := c + 2) rfl h₂).mp (((hσ.ruleA rfl h₁).mpr l₁).trans U)
  have t₂ := (hσ.ruleB (x₂ := c + 2 + 2) rfl h₄).mp (((hσ.ruleA rfl h₃).mpr l₂).trans U')
  -- the midpoint rule at `c + 2` then gives `c + 2 ≺ c`
  have m := hσ.mid c (c + 2) (c + 2 + 2) (by omega) (by omega) (by omega) (by omega)
  exact absurd (t₁.trans (m.mpr t₂)) (lt_irrefl _)

/-- **Lemma II (one centre, one AP).** `c` has the trailing parity and `d = c ± 2`; the anchor
constraints `u₁ ≺ b₁`, `u₂ ≺ b₂`, `u₃ ≺ b₃` satisfy hypotheses 1-5 of Lemma II of
`docs/proof.md` (`h₁`-`h₅`). -/
theorem lemmaII (hσ : Good L R σ) {c d u₁ b₁ u₂ b₂ u₃ b₃ : ℕ} (hLR : L + 2 ≤ R)
    (hbr : ¬ (σ L < σ (L + 1) ↔ c % 2 = L % 2)) (hd : d = c + 2 ∨ d + 2 = c)
    (hc : L + 2 ≤ c ∧ c + 2 ≤ R) (hd' : L + 2 ≤ d ∧ d + 2 ≤ R)
    (U₁ : σ u₁ < σ b₁) (U₂ : σ u₂ < σ b₂) (U₃ : σ u₃ < σ b₃)
    (h₁ : L ≤ b₁ ∧ b₁ ≤ R ∧ L + b₁ ≤ 2 * c ∧ 2 * c ≤ R + b₁ ∧ (b₁ + c) % 2 = 1)
    (h₂ : L ≤ u₁ ∧ u₁ ≤ R ∧ L + u₁ ≤ 2 * c ∧ 2 * c ≤ R + u₁ ∧ u₁ % 4 = (c + 2) % 4)
    (h₃ : L ≤ u₂ ∧ u₂ ≤ R ∧ L + u₂ ≤ 2 * d ∧ 2 * d ≤ R + u₂ ∧ u₂ % 4 = (d + 2) % 4)
    (h₄ : L ≤ b₃ ∧ b₃ ≤ R ∧ L + b₃ ≤ 2 * d ∧ 2 * d ≤ R + b₃ ∧ (b₃ + d) % 2 = 1)
    (h₅ : L ≤ b₂ ∧ u₃ ≤ R ∧ b₂ < d ∧ b₂ + u₃ = 2 * d) : False := by
  -- `c` and `d` come after their right neighbours (they have the trailing parity)
  have tc : ¬ σ c < σ (c + 1) := fun h =>
    hbr ((hσ.lead_iff hLR rfl (by omega) (by omega)).mp h)
  have td : ¬ σ d < σ (d + 1) := fun h => hbr (by
    have := (hσ.lead_iff hLR rfl (by omega) (by omega)).mp h
    rwa [show d % 2 = c % 2 by omega] at this)
  -- Rule A at `c`: `u₁ ≺ b₁ ≺ c`
  have A₁ := hσ.ruleA rfl h₁
  have s₁ : σ u₁ < σ c := by
    have := hσ.ne (x := c) (y := b₁) (by omega)
    exact U₁.trans (by omega)
  -- Rule B(ii) at `c`: `c + 2 ≺ c`
  have B₁ := hσ.ruleB rfl h₂
  have s₂ : σ (c + 2) < σ c := by
    have := hσ.ne (x := c) (y := c + 2) (by omega)
    omega
  -- so the neighbour `d` precedes `d + 2` (Lemma 1)
  have s₃ : σ d < σ (d + 2) := by
    rcases hd with rfl | rfl
    · exact (hσ.mid c (c + 2) (c + 2 + 2) (by omega) (by omega) (by omega) (by omega)).mp s₂
    · have := hσ.mid d (d + 2) (d + 2 + 2) (by omega) (by omega) (by omega) (by omega)
      have := hσ.ne (x := d) (y := d + 2) (by omega)
      omega
  -- Rule B(i) at `d`: `d ≺ u₂ ≺ b₂`
  have s₄ : σ d < σ b₂ := ((hσ.ruleB rfl h₃).mpr s₃).trans U₂
  -- Rule A at `d`: `u₃ ≺ b₃ ≺ d`
  have A₃ := hσ.ruleA rfl h₄
  have s₅ : σ u₃ < σ d := by
    have := hσ.ne (x := d) (y := b₃) (by omega)
    exact U₃.trans (by omega)
  -- the midpoint rule for the AP `(b₂, d, u₃)`: `d ≺ b₂` forces `d ≺ u₃`
  have m := hσ.mid b₂ d u₃ h₅.1 h₅.2.1 h₅.2.2.1 h₅.2.2.2
  exact absurd ((m.mp s₄).trans s₅) (lt_irrefl _)

end Good

open Good in
/-- **Theorem I**, in terms of `Good`: the 16 cases (`M mod 8` and the leading parity). The
anchor constraint `U(j, a)` is `hU j a`. -/
theorem gadget_core {M : ℕ} {σ : ℕ → ℕ} (hM : 8 ≤ M) (hσ : Good M (2 * M + 6) σ)
    (hU : ∀ j a x y, j ≤ 3 ∧ a ≤ 1 ∧ x = 2 * (M + j) - a ∧ y = M + j → σ x < σ y) :
    False := by
  obtain ⟨q, hq⟩ : ∃ q, q = M / 8 := ⟨_, rfl⟩
  have hLR : M + 2 ≤ 2 * M + 6 := by omega
  by_cases hπ : σ M < σ (M + 1)
  · -- the parity of `M` leads
    by_cases hr : M % 8 ≤ 4
    · -- Lemma I with `j = 0`, `a = 1 - π`, `s = ⌊M / 8⌋`
      apply hσ.lemmaI hLR (c := M + 2 + 4 * q)
        (U := hU 0 ((M + 1) % 2) (2 * M - (M + 1) % 2) M (by omega))
        (U' := hU 2 ((M + 1) % 2) (2 * M + 4 - (M + 1) % 2) (M + 2) (by omega)) <;> omega
    · -- Lemma II, rows `M ≡ 5, 6, 7 (mod 8)`
      rcases (by omega : M % 8 = 5 ∨ M % 8 = 6 ∨ M % 8 = 7) with h | h | h
      · apply hσ.lemmaII hLR (c := 12 * q + 8) (d := 12 * q + 10)
          (U₁ := hU 0 0 (16 * q + 10) (8 * q + 5) (by omega))
          (U₂ := hU 1 0 (16 * q + 12) (8 * q + 6) (by omega))
          (U₃ := hU 2 0 (16 * q + 14) (8 * q + 7) (by omega)) <;> omega
      · apply hσ.lemmaII hLR (c := 12 * q + 9) (d := 12 * q + 11)
          (U₁ := hU 0 1 (16 * q + 11) (8 * q + 6) (by omega))
          (U₂ := hU 1 1 (16 * q + 13) (8 * q + 7) (by omega))
          (U₃ := hU 2 1 (16 * q + 15) (8 * q + 8) (by omega)) <;> omega
      · apply hσ.lemmaII hLR (c := 12 * q + 12) (d := 12 * q + 14)
          (U₁ := hU 0 0 (16 * q + 14) (8 * q + 7) (by omega))
          (U₂ := hU 3 0 (16 * q + 20) (8 * q + 10) (by omega))
          (U₃ := hU 2 0 (16 * q + 18) (8 * q + 9) (by omega)) <;> omega
  · -- the parity of `M` trails
    by_cases hr : 1 ≤ M % 8 ∧ M % 8 ≤ 5
    · -- Lemma I with `j = 1`, `a = 1 - π`, `s = ⌊M / 8⌋`
      apply hσ.lemmaI hLR (c := M + 3 + 4 * q)
        (U := hU 1 (M % 2) (2 * M + 2 - M % 2) (M + 1) (by omega))
        (U' := hU 3 (M % 2) (2 * M + 6 - M % 2) (M + 3) (by omega)) <;> omega
    · -- Lemma II, rows `M ≡ 0, 6, 7 (mod 8)`
      rcases (by omega : M % 8 = 0 ∨ M % 8 = 6 ∨ M % 8 = 7) with h | h | h
      · apply hσ.lemmaII hLR (c := 12 * q + 4) (d := 12 * q + 2)
          (U₁ := hU 3 0 (16 * q + 6) (8 * q + 3) (by omega))
          (U₂ := hU 2 0 (16 * q + 4) (8 * q + 2) (by omega))
          (U₃ := hU 1 0 (16 * q + 2) (8 * q + 1) (by omega)) <;> omega
      · apply hσ.lemmaII hLR (c := 12 * q + 12) (d := 12 * q + 10)
          (U₁ := hU 1 0 (16 * q + 14) (8 * q + 7) (by omega))
          (U₂ := hU 0 0 (16 * q + 12) (8 * q + 6) (by omega))
          (U₃ := hU 1 0 (16 * q + 14) (8 * q + 7) (by omega)) <;> omega
      · apply hσ.lemmaII hLR (c := 12 * q + 13) (d := 12 * q + 11)
          (U₁ := hU 1 1 (16 * q + 15) (8 * q + 8) (by omega))
          (U₂ := hU 0 1 (16 * q + 13) (8 * q + 7) (by omega))
          (U₃ := hU 1 1 (16 * q + 15) (8 * q + 8) (by omega)) <;> omega

/-- **Theorem I** (the statement of `Erdos197Interval.gadget` in `Challenge.lean`). -/
theorem gadget_thm (M : ℕ) (hM : 8 ≤ M) (σ : ℕ → ℕ)
    (hσ : Set.InjOn σ (Set.Icc M (2 * M + 6)))
    (hAP : ∀ x y z : ℕ, x ∈ Set.Icc M (2 * M + 6) → z ∈ Set.Icc M (2 * M + 6) →
      x < y → y < z → y - x = z - y →
        ¬ (σ x < σ y ∧ σ y < σ z) ∧ ¬ (σ z < σ y ∧ σ y < σ x)) :
    ¬ ∀ j a : ℕ, j ≤ 3 → a ≤ 1 → σ (2 * (M + j) - a) < σ (M + j) := by
  intro hU
  have inj : ∀ x y, M ≤ x → x ≤ 2 * M + 6 → M ≤ y → y ≤ 2 * M + 6 → σ x = σ y → x = y :=
    fun x y hx hx' hy hy' h => hσ (Set.mem_Icc.2 ⟨hx, hx'⟩) (Set.mem_Icc.2 ⟨hy, hy'⟩) h
  refine gadget_core hM ⟨inj, fun x y z hx hz hxy hxz => ?_⟩
    (fun j a x y ⟨hj, ha, hx, hy⟩ => by subst hx hy; exact hU j a hj ha)
  have h := hAP x y z (Set.mem_Icc.2 ⟨hx, by omega⟩) (Set.mem_Icc.2 ⟨by omega, hz⟩) hxy
    (by omega) (by omega)
  have n₁ : σ y ≠ σ x := fun e => by have := inj y x (by omega) (by omega) hx (by omega) e; omega
  have n₂ : σ y ≠ σ z := fun e => by have := inj y z (by omega) (by omega) (by omega) hz e; omega
  omega

/-- An enumeration `v` with no monotone 3-term AP (formal-conjectures' predicate, unfolded) has
no positions `p < q < r` with `v p + v r = 2 v q`. -/
theorem no_ap {v : ℕ → ℕ}
    (hv : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map v = (List.range 3).map (fun n => a + n • d) ∨
          l.map v = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·))
    {p q r : ℕ} (hpq : p < q) (hqr : q < r) (hap : v p + v r = 2 * v q) : False := by
  rcases le_total (v p) (v q) with h | h
  · exact hv ⟨[p, q, r], ⟨v p, v q - v p, Or.inl (by simp [List.range_succ]; omega)⟩,
      by simp; omega⟩
  · exact hv ⟨[p, q, r], ⟨v r, v q - v r, Or.inr (by simp [List.range_succ]; omega)⟩,
      by simp; omega⟩

/-- **Corollary I** (the statement of `Erdos197Interval.main_result` in `Challenge.lean`). -/
theorem corollary (S : Set ℕ) (f : ℕ ≃ S)
    (hf : ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·))
    (v : ℕ) (hv : v ∈ S) (hv1 : v + 1 ∈ S) :
    ∃ P₀ : ℕ, ∀ P ≥ P₀, ¬ Set.Icc P (2 * P + 6 - v) ⊆ S := by
  classical
  -- `ρ x` is the position of `x ∈ S` in the enumeration
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℕ, ∀ x (hx : x ∈ S), ρ x = f.symm ⟨x, hx⟩ :=
    ⟨fun x => if hx : x ∈ S then f.symm ⟨x, hx⟩ else 0, fun x hx => by simp [hx]⟩
  have hfρ : ∀ x, x ∈ S → (f (ρ x) : ℕ) = x := fun x hx => by simp [hρ x hx]
  -- the anchor rule (Lemma 2 of the working note)
  have anchor : ∀ p w t, p ∈ S → w ∈ S → t ∈ S → p < w → p + t = 2 * w → ρ p < ρ w →
      ρ t < ρ w := by
    intro p w t hp hw ht hpw hpt hlt
    by_contra hc
    have hne : ρ t ≠ ρ w := fun e => by
      have := congrArg (fun i => (f i : ℕ)) e
      simp only [hfρ t ht, hfρ w hw] at this
      omega
    exact no_ap hf (p := ρ p) (q := ρ w) (r := ρ t) hlt (by omega)
      (by simp only [Function.comp_apply, hfρ p hp, hfρ w hw, hfρ t ht]; omega)
  -- everything listed up to `v` and `v + 1` is at most `B`
  obtain ⟨B, hB⟩ : ∃ B, ∀ i, i ≤ ρ v + ρ (v + 1) → (f i : ℕ) ≤ B := by
    have key : ∀ N, ∃ B, ∀ i, i ≤ N → (f i : ℕ) ≤ B := by
      intro N
      induction N with
      | zero => exact ⟨f 0, fun i hi => by rw [show i = 0 by omega]⟩
      | succ N ih =>
        obtain ⟨B, hB⟩ := ih
        refine ⟨max B (f (N + 1)), fun i hi => ?_⟩
        rcases Nat.lt_or_ge i (N + 1) with h | h
        · exact le_max_of_le_left (hB i (by omega))
        · obtain rfl : i = N + 1 := by omega
          exact le_max_right _ _
    exact key _
  have late : ∀ w, w ∈ S → B < w → ρ v < ρ w ∧ ρ (v + 1) < ρ w := by
    intro w hw hBw
    by_contra hc
    have := hB (ρ w) (by omega)
    rw [hfρ w hw] at this
    omega
  refine ⟨B + v + 9, fun P hP hsub => ?_⟩
  have mem : ∀ x, P ≤ x → x ≤ 2 * P + 6 - v → x ∈ S := fun x h₁ h₂ =>
    hsub (Set.mem_Icc.2 ⟨h₁, h₂⟩)
  -- translate `[P, 2P + 6 - v]` to `[M, 2M + 6]` with `M = P - v` and apply Theorem I
  refine gadget_thm (P - v) (by omega) (fun x => ρ (x + v)) ?_ ?_ ?_
  · intro x hx y hy hxy
    rw [Set.mem_Icc] at hx hy
    have := congrArg (fun i => (f i : ℕ)) hxy
    simp only [hfρ _ (mem (x + v) (by omega) (by omega)),
      hfρ _ (mem (y + v) (by omega) (by omega))] at this
    omega
  · intro x y z hx hz hxy hyz hd
    rw [Set.mem_Icc] at hx hz
    have ex := hfρ _ (mem (x + v) (by omega) (by omega))
    have ey := hfρ _ (mem (y + v) (by omega) (by omega))
    have ez := hfρ _ (mem (z + v) (by omega) (by omega))
    refine ⟨fun ⟨h₁, h₂⟩ => no_ap hf h₁ h₂ ?_, fun ⟨h₁, h₂⟩ => no_ap hf h₁ h₂ ?_⟩
    · simp only [Function.comp_apply, ex, ey, ez]; omega
    · simp only [Function.comp_apply, ex, ey, ez]; omega
  · intro j a hj ha
    show ρ (2 * (P - v + j) - a + v) < ρ (P - v + j + v)
    have hw := mem (P - v + j + v) (by omega) (by omega)
    have ht := mem (2 * (P - v + j) - a + v) (by omega) (by omega)
    have hva : v + a ∈ S := by
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · simpa using hv
      · exact hv1
    have hl : ρ (v + a) < ρ (P - v + j + v) := by
      have := late _ hw (by omega)
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · simpa using this.1
      · exact this.2
    exact anchor (v + a) _ _ hva hw ht (by omega) (by omega) hl

end Erdos197Interval
