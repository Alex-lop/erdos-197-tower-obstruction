module

public import Solution
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Analysis.SpecificLimits.Normed

public section

/-! Non-vacuity of the three statements of `Challenge.lean`.

* `hf_sat`: the enumeration hypothesis `hf`, unfolded exactly as in `Challenge.lean`, is
  satisfiable: the powers of two, listed in increasing order, have no monotone 3-term AP. So
  `tower` and `clean` are not trivially true because `hf` is always false.
* `tower_hyps`, `clean_hyps`: explicit data satisfying every hypothesis of `Erdos197Tower.tower`
  and of `Erdos197Tower.clean` except the enumeration without monotone 3-term APs, in a set that
  has enumerations. So these theorems say "such a set is not permutable", not something vacuous.
* `class_enumerable`: for every strictly increasing `r`, each colour class is infinite and has
  enumerations `ℕ ≃ C`; so the conclusion of `Erdos197Tower.main_result` is not trivially true.
* `dyadic_hyps`, `dyadic`: `r k = 2 ^ k` (the runs `[2 ^ k, 2 ^ (k + 1))`) satisfies the
  hypotheses of `main_result`. Kasel's dyadic partition (arXiv:2609.02939, Theorem 21), with
  blocks `(2 ^ k, 2 ^ (k + 1)]`, is the case `r k = 2 ^ k + 1`, which is not checked here.
* `lin_hyps`, `lin`: `r k = 2 ^ k + k` also satisfies them; its runs drift away from the dyadic
  blocks, so this colouring is not covered by the dyadic theorem. -/

/-- The hypothesis `hf` of `Challenge.lean` is satisfiable: `f k = 2 ^ k` enumerates the powers of
two, and they have no 3-term AP at all. -/
theorem hf_sat : ∃ S : Set ℕ, ∃ f : ℕ ≃ S, ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·) := by
  refine ⟨_, Equiv.ofInjective (2 ^ ·) (Nat.pow_right_injective le_rfl), ?_⟩
  rintro ⟨l, ⟨a, d, h⟩, hl⟩
  rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨_, _⟩⟩⟩⟩ <;> simp [List.range_succ] at h
  simp at hl
  have hij : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right Nat.one_lt_two hl.1.1
  have hjk : 2 ^ (j + 1) ≤ 2 ^ k := Nat.pow_le_pow_right Nat.two_pos hl.2
  rw [pow_succ] at hjk
  have := Nat.one_le_two_pow (n := i)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega

/-- The tower `[32 · 8^k, 64 · 8^k]` with `u = 63`, `d = 1` satisfies (T1\*) and (T2\*), and the
union `S` of its intervals is infinite, so it has enumerations. -/
theorem tower_hyps : ∃ S : Set ℕ, Nonempty (ℕ ≃ S) ∧ ∃ u d : ℕ, ∃ α β : ℕ → ℕ,
    1 ≤ d ∧ u ∈ S ∧ u + d ∈ S ∧ (∀ k, 1 ≤ k → Set.Icc (α k) (β k) ⊆ S) ∧
    u + 8 * d ≤ α 1 ∧ 2 * α 1 + 16 * d ≤ u + β 1 ∧
    (∀ k, 1 ≤ k → β k + 8 * 4 ^ k * d ≤ α (k + 1)) ∧
    (∀ k, 1 ≤ k → 2 * α (k + 1) + 16 * 4 ^ k * d ≤ α k + β (k + 1)) := by
  have hinf : Set.Infinite {n : ℕ | ∃ k, 32 * 8 ^ k ≤ n ∧ n ≤ 64 * 8 ^ k} := by
    refine Set.infinite_of_forall_exists_gt fun a => ⟨32 * 8 ^ a, ⟨a, le_rfl, by omega⟩, ?_⟩
    have := Nat.lt_pow_self (n := a) (by norm_num : 1 < 8)
    omega
  have := hinf.to_subtype
  refine ⟨{n : ℕ | ∃ k, 32 * 8 ^ k ≤ n ∧ n ≤ 64 * 8 ^ k}, ⟨(Nat.Subtype.orderIsoOfNat _).toEquiv⟩,
    63, 1, fun k => 32 * 8 ^ k,
    fun k => 64 * 8 ^ k, le_rfl, ⟨0, by norm_num⟩, ⟨0, by norm_num⟩,
    fun k _ x hx => ⟨k, hx.1, hx.2⟩, by norm_num, by norm_num, fun k _ => ?_, fun k _ => ?_⟩
  · have h1 : 4 ^ k ≤ 8 ^ k := Nat.pow_le_pow_left (by norm_num) k
    have h2 : 8 ^ (k + 1) = 8 * 8 ^ k := by ring
    show 64 * 8 ^ k + 8 * 4 ^ k * 1 ≤ 32 * 8 ^ (k + 1)
    omega
  · have h1 : 4 ^ k ≤ 8 ^ k := Nat.pow_le_pow_left (by norm_num) k
    have h2 : 8 ^ (k + 1) = 8 * 8 ^ k := by ring
    show 2 * (32 * 8 ^ (k + 1)) + 16 * 4 ^ k * 1 ≤ 32 * 8 ^ k + 64 * 8 ^ (k + 1)
    omega

/-- The intervals `[32 · 8^j, 64 · 8^j]` satisfy the hypotheses of Corollary R0\*, and their union
has enumerations. -/
theorem clean_hyps : ∃ S : Set ℕ, Nonempty (ℕ ≃ S) ∧ ∃ a b : ℕ → ℕ,
    (∀ j, Set.Icc (a j) (b j) ⊆ S) ∧ 32 ≤ a 0 ∧ a 0 + 1 ≤ b 0 ∧
    (∀ j, 4 * b j ≤ a (j + 1)) ∧ (∀ j, 4 * a (j + 1) ≤ a j + 2 * b (j + 1)) := by
  have hinf : Set.Infinite {n : ℕ | ∃ k, 32 * 8 ^ k ≤ n ∧ n ≤ 64 * 8 ^ k} := by
    refine Set.infinite_of_forall_exists_gt fun a => ⟨32 * 8 ^ a, ⟨a, le_rfl, by omega⟩, ?_⟩
    have := Nat.lt_pow_self (n := a) (by norm_num : 1 < 8)
    omega
  have := hinf.to_subtype
  refine ⟨{n : ℕ | ∃ k, 32 * 8 ^ k ≤ n ∧ n ≤ 64 * 8 ^ k}, ⟨(Nat.Subtype.orderIsoOfNat _).toEquiv⟩,
    fun k => 32 * 8 ^ k, fun k => 64 * 8 ^ k,
    fun k x hx => ⟨k, hx.1, hx.2⟩, by norm_num, by norm_num, fun j => ?_, fun j => ?_⟩
  · show 4 * (64 * 8 ^ j) ≤ 32 * 8 ^ (j + 1)
    rw [pow_succ]
    omega
  · show 4 * (32 * 8 ^ (j + 1)) ≤ 32 * 8 ^ j + 2 * (64 * 8 ^ (j + 1))
    omega

/-- Each colour class of a strictly increasing `r` is infinite, hence has enumerations. -/
theorem class_enumerable (r : ℕ → ℕ) (hr : StrictMono r) (c : ℕ) (hc : c < 2) :
    Nonempty (ℕ ≃ {n : ℕ | ∃ k, k % 2 = c ∧ r k ≤ n ∧ n < r (k + 1)}) := by
  have hinf : Set.Infinite {n : ℕ | ∃ k, k % 2 = c ∧ r k ≤ n ∧ n < r (k + 1)} := by
    refine Set.infinite_of_forall_exists_gt fun a =>
      ⟨r (2 * a + c + 2), ⟨2 * a + c + 2, by omega, le_rfl, hr (by omega)⟩, ?_⟩
    have : 2 * a + c + 2 ≤ r (2 * a + c + 2) := hr.le_apply
    omega
  have := hinf.to_subtype
  exact ⟨(Nat.Subtype.orderIsoOfNat _).toEquiv⟩

/-- `r k = 2 ^ k` satisfies the hypotheses of `Erdos197Tower.main_result`. -/
theorem dyadic_hyps : StrictMono (fun k : ℕ => 2 ^ k) ∧ 1 ≤ 2 ^ 0 ∧
    Filter.Tendsto (fun k : ℕ => ((2 ^ (k + 1) : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ)) Filter.atTop
      (nhds 2) := by
  refine ⟨fun a b h => Nat.pow_lt_pow_right (by norm_num) h, by norm_num,
    tendsto_const_nhds.congr fun k => ?_⟩
  push_cast
  rw [pow_succ]
  field_simp

/-- The dyadic colouring: neither class `{n | ∃ k, k % 2 = c ∧ 2 ^ k ≤ n ∧ n < 2 ^ (k + 1)}` is
permutable (a special case of `Erdos197Tower.main_result`). -/
theorem dyadic (c : ℕ) (hc : c < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | ∃ k, k % 2 = c ∧ 2 ^ k ≤ n ∧ n < 2 ^ (k + 1)},
      ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·) :=
  Erdos197Tower.main_result (fun k => 2 ^ k) dyadic_hyps.1 dyadic_hyps.2.1 dyadic_hyps.2.2 c hc

/-- `r k = 2 ^ k + k` satisfies the hypotheses of `Erdos197Tower.main_result`: the ratio is
squeezed between `2 - k / 2 ^ k` and `2`. -/
theorem lin_hyps : StrictMono (fun k : ℕ => 2 ^ k + k) ∧ 1 ≤ 2 ^ 0 + 0 ∧
    Filter.Tendsto (fun k : ℕ => ((2 ^ (k + 1) + (k + 1) : ℕ) : ℝ) / ((2 ^ k + k : ℕ) : ℝ))
      Filter.atTop (nhds 2) := by
  refine ⟨fun a b h => by
    show 2 ^ a + a < 2 ^ b + b
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h
    omega, by norm_num, ?_⟩
  have h0 : Filter.Tendsto (fun k : ℕ => (k : ℝ) / 2 ^ k) Filter.atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  have hlow : Filter.Tendsto (fun k : ℕ => 2 - (k : ℝ) / 2 ^ k) Filter.atTop (nhds 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards with k
    rw [le_div_iff₀ (by positivity)]
    push_cast
    have e : (2 - (k : ℝ) / 2 ^ k) * (2 ^ k + k) = 2 * 2 ^ k + k - k ^ 2 / 2 ^ k := by
      field_simp
      ring
    have hk2 : (0 : ℝ) ≤ k ^ 2 / 2 ^ k := by positivity
    rw [e, pow_succ (2 : ℝ) k]
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    rw [div_le_iff₀ (by positivity)]
    have : 2 ^ (k + 1) + (k + 1) ≤ 2 * (2 ^ k + k) := by rw [pow_succ]; omega
    exact_mod_cast this

/-- The drifting colouring by the runs `[2 ^ k + k, 2 ^ (k + 1) + k + 1)`: neither class is
permutable. -/
theorem lin (c : ℕ) (hc : c < 2) :
    ¬ ∃ f : ℕ ≃ {n : ℕ | ∃ k, k % 2 = c ∧ 2 ^ k + k ≤ n ∧ n < 2 ^ (k + 1) + (k + 1)},
      ¬ ∃ l : List ℕ, (∃ a d : ℕ,
        l.map (Subtype.val ∘ f) = (List.range 3).map (fun n => a + n • d) ∨
          l.map (Subtype.val ∘ f) = (List.range 3).reverse.map (fun n => a + n • d)) ∧
        l.Pairwise (· < ·) :=
  Erdos197Tower.main_result (fun k => 2 ^ k + k) lin_hyps.1 lin_hyps.2.1 lin_hyps.2.2 c hc

#print axioms hf_sat
#print axioms tower_hyps
#print axioms clean_hyps
#print axioms class_enumerable
#print axioms dyadic
#print axioms lin
