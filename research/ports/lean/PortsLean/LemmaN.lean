import Mathlib

/-!
# Lemma N (balanced cut against a two-point star)

Source: `research/sat3/q2-notes.md` §2.2 (Lemma N and its proof) and `research/sat3/review-q2.md`
(item 6: the lemma needs `K ≥ 4`; it is false at `K = 2`).

Statement (`lemmaN`): for `K ≥ 4` even and points `x : Fin K → α` of a pseudometric space there is an
exactly balanced cut `(A, B)` of `Fin K` such that for all `y₀ y₁`
  `Σ_{u<v} d(x_u, x_v) ≤ (K − 1)·[Σ_{i∈A} d(x_i, y₀) + Σ_{i∈B} d(x_i, y₁)]`.

A cut is encoded by `b : Fin K → Bool` with signs `sg b i = ±1`; it is balanced iff `Σ_i sg b i = 0`.
The same-side indicator of `u, v` is `(1 + sg b u · sg b v)/2 ∈ {0, 1}`.

* `core`: for EVERY balanced cut and every choice `y : Bool → α` of the two suppliers,
  `Σ_{u,v} same(u,v)·d(x_u,x_v) ≤ (K − 2)·Σ_i d(x_i, y (b i))` (ordered pairs; this is
  `Σ_{same, u<v} d ≤ (K/2 − 1)·star`).
* `M_swap`, `M_off`: for `u ≠ v`, `Σ_{balanced b} sg b u · sg b v = −#cuts/(K − 1)` (symmetry under the
  transposition fixing `u`, and `Σ_v sg b v = 0`).
* `sum_cuts_same`: the sum over all balanced cuts of the same-side weight is
  `#cuts · (K − 2)/(K − 1) · Σ_{u,v} d / 2` (averaging).
* `lemmaN`: existence of the cut.
* `lemmaN_false_K2`: the counterexample at `K = 2` (two points of `ℝ` at distance 1).
-/

open Finset

noncomputable section

namespace LemmaN

/-- The sign of row `i` under the cut `b`. -/
def sg {K : ℕ} (b : Fin K → Bool) (i : Fin K) : ℝ := if b i then 1 else -1

lemma sg_mul_self {K : ℕ} (b : Fin K → Bool) (i : Fin K) : sg b i * sg b i = 1 := by
  unfold sg; split_ifs <;> norm_num

/-- The balanced cuts. -/
def cuts (K : ℕ) : Finset (Fin K → Bool) :=
  univ.filter (fun b => ∑ i, sg b i = 0)

lemma mem_cuts {K : ℕ} (b : Fin K → Bool) : b ∈ cuts K ↔ ∑ i, sg b i = 0 := by
  simp [cuts]

/-- Row sums of the same-side weight: `Σ_v (1 + s_u s_v) = K` on a balanced cut. -/
lemma row_same {K : ℕ} (b : Fin K → Bool) (hb : ∑ i, sg b i = 0) (u : Fin K) :
    ∑ v, (1 + sg b u * sg b v) = (K : ℝ) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hb]
  simp

/-- The deterministic core: for every balanced cut and all suppliers,
`Σ_{u,v} same·d ≤ (K − 2)·star`. -/
theorem core {α : Type*} [PseudoMetricSpace α] {K : ℕ} (x : Fin K → α) (b : Fin K → Bool)
    (hb : ∑ i, sg b i = 0) (y : Bool → α) :
    ∑ u, ∑ v, (1 + sg b u * sg b v) / 2 * dist (x u) (x v)
      ≤ ((K : ℝ) - 2) * ∑ i, dist (x i) (y (b i)) := by
  set r : Fin K → ℝ := fun i => dist (x i) (y (b i)) with hr
  -- pointwise bound
  have hpt : ∀ u v, (1 + sg b u * sg b v) / 2 * dist (x u) (x v)
      ≤ (1 + sg b u * sg b v) / 2 * r u + (1 + sg b v * sg b u) / 2 * r v
          - (if u = v then 2 * r u else 0) := by
    intro u v
    by_cases hbe : b u = b v
    · have hs : sg b u * sg b v = 1 := by
        unfold sg; rw [hbe]; split_ifs <;> norm_num
      have hs' : sg b v * sg b u = 1 := by rw [mul_comm]; exact hs
      rw [hs, hs']
      have htri : dist (x u) (x v) ≤ r u + r v := by
        simp only [hr]
        rw [hbe]
        calc dist (x u) (x v) ≤ dist (x u) (y (b v)) + dist (y (b v)) (x v) := dist_triangle _ _ _
          _ = dist (x u) (y (b v)) + dist (x v) (y (b v)) := by rw [dist_comm (y (b v))]
      split_ifs with huv
      · subst huv; rw [dist_self]; linarith
      · linarith
    · have hs : sg b u * sg b v = -1 := by
        unfold sg
        cases h1 : b u <;> cases h2 : b v <;> simp_all
      have hs' : sg b v * sg b u = -1 := by rw [mul_comm]; exact hs
      have huv : u ≠ v := by rintro rfl; exact hbe rfl
      rw [hs, hs', ite_eq_right_iff.2 (fun h => absurd h huv)]
      norm_num
  have hsum := Finset.sum_le_sum (fun u (_ : u ∈ univ) =>
    Finset.sum_le_sum (fun v (_ : v ∈ univ) => hpt u v))
  refine le_trans hsum (le_of_eq ?_)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- the three pieces
  have h1 : ∑ u, ∑ v, (1 + sg b u * sg b v) / 2 * r u = (K : ℝ) / 2 * ∑ i, r i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.sum_mul, ← Finset.sum_div, row_same b hb u]
  have h2 : ∑ u, ∑ v, (1 + sg b v * sg b u) / 2 * r v = (K : ℝ) / 2 * ∑ i, r i := by
    rw [Finset.sum_comm]; exact h1
  have h3 : ∑ u, ∑ v, (if u = v then 2 * r u else 0) = 2 * ∑ i, r i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_ite_eq]; simp
  rw [h1, h2, h3]; ring

/-- The correlation of two rows over all balanced cuts. -/
def M (K : ℕ) (u v : Fin K) : ℝ := ∑ b ∈ cuts K, sg b u * sg b v

lemma sg_comp {K : ℕ} (b : Fin K → Bool) (σ : Equiv.Perm (Fin K)) (i : Fin K) :
    sg (b ∘ σ) i = sg b (σ i) := rfl

lemma comp_mem_cuts {K : ℕ} (b : Fin K → Bool) (σ : Equiv.Perm (Fin K)) (hb : b ∈ cuts K) :
    b ∘ σ ∈ cuts K := by
  rw [mem_cuts] at *
  simp only [sg_comp]
  rw [Equiv.sum_comp σ (fun i => sg b i)]; exact hb

/-- Symmetry: the transposition of `v, w` fixes `u`. -/
lemma M_swap {K : ℕ} {u v w : Fin K} (hv : u ≠ v) (hw : u ≠ w) : M K u v = M K u w := by
  unfold M
  set σ : Equiv.Perm (Fin K) := Equiv.swap v w
  refine Finset.sum_nbij' (fun b => b ∘ σ) (fun b => b ∘ σ)
    (fun b hb => comp_mem_cuts b σ hb) (fun b hb => comp_mem_cuts b σ hb) ?_ ?_ ?_
  · intro b _; funext i; simp [σ, Equiv.swap_apply_self]
  · intro b _; funext i; simp [σ, Equiv.swap_apply_self]
  · intro b _
    simp only [sg_comp, σ]
    rw [Equiv.swap_apply_of_ne_of_ne hv hw, Equiv.swap_apply_right]

lemma M_self {K : ℕ} (u : Fin K) : M K u u = ((cuts K).card : ℝ) := by
  unfold M; simp [sg_mul_self]

lemma M_rowsum {K : ℕ} (u : Fin K) : ∑ v, M K u v = 0 := by
  unfold M
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun b hb => ?_)
  rw [← Finset.mul_sum, (mem_cuts b).1 hb, mul_zero]

/-- For `u ≠ v`: `M u v = −#cuts/(K − 1)`. -/
lemma M_off {K : ℕ} (hK : 2 ≤ K) {u v : Fin K} (huv : u ≠ v) :
    M K u v = -((cuts K).card : ℝ) / ((K : ℝ) - 1) := by
  have hK1 : (K : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have h := M_rowsum (K := K) u
  rw [← Finset.add_sum_erase _ _ (mem_univ u), M_self] at h
  have hc : ∑ w ∈ univ.erase u, M K u w = ∑ w ∈ univ.erase u, M K u v :=
    Finset.sum_congr rfl (fun w hw => (M_swap huv (Ne.symm (Finset.ne_of_mem_erase hw))).symm)
  rw [hc, Finset.sum_const, Finset.card_erase_of_mem (mem_univ u), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ K)] at h
  field_simp
  push_cast at h
  linarith

/-- Averaging over all balanced cuts. -/
theorem sum_cuts_same {α : Type*} [PseudoMetricSpace α] {K : ℕ} (hK : 2 ≤ K) (x : Fin K → α) :
    ∑ b ∈ cuts K, ∑ u, ∑ v, (1 + sg b u * sg b v) / 2 * dist (x u) (x v)
      = ((cuts K).card : ℝ) * (((K : ℝ) - 2) / ((K : ℝ) - 1) * ((∑ u, ∑ v, dist (x u) (x v)) / 2)) := by
  have hK1 : (K : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  rw [Finset.sum_comm]
  rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_comm, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_one]
  change ((cuts K).card + M K u v) / 2 * dist (x u) (x v) = _
  by_cases huv : u = v
  · subst huv; simp
  · rw [M_off hK huv]
    field_simp
    ring

/-- Ordered pairs versus unordered pairs. -/
lemma sum_pairs {α : Type*} [PseudoMetricSpace α] {K : ℕ} (x : Fin K → α) :
    ∑ u, ∑ v, dist (x u) (x v) = 2 * ∑ u, ∑ v ∈ univ.filter (fun v => u < v), dist (x u) (x v) := by
  have hpt : ∀ u v, dist (x u) (x v)
      = (if u < v then dist (x u) (x v) else 0) + (if v < u then dist (x v) (x u) else 0) := by
    intro u v
    rcases lt_trichotomy u v with h | h | h
    · simp [h, not_lt.2 h.le]
    · subst h; simp
    · simp [h, not_lt.2 h.le, dist_comm]
  have e1 : ∑ u, ∑ v, dist (x u) (x v)
      = ∑ u, ∑ v, (if u < v then dist (x u) (x v) else 0)
        + ∑ u, ∑ v, (if v < u then dist (x v) (x u) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => hpt u v)
  have e2 : ∑ u, ∑ v, (if v < u then dist (x v) (x u) else 0)
      = ∑ u, ∑ v, (if u < v then dist (x u) (x v) else 0) := Finset.sum_comm
  rw [e1, e2, two_mul]
  simp only [Finset.sum_filter]

/-- **Lemma N.** -/
theorem lemmaN {α : Type*} [PseudoMetricSpace α] (K : ℕ) (hK : 4 ≤ K) (heven : Even K)
    (x : Fin K → α) :
    ∃ A B : Finset (Fin K), Disjoint A B ∧ A ∪ B = univ ∧ A.card = K / 2 ∧ B.card = K / 2 ∧
      ∀ y₀ y₁ : α,
        ∑ u, ∑ v ∈ univ.filter (fun v => u < v), dist (x u) (x v)
          ≤ ((K : ℝ) - 1) * (∑ i ∈ A, dist (x i) y₀ + ∑ i ∈ B, dist (x i) y₁) := by
  -- a balanced cut exists
  have hne : (cuts K).Nonempty := by
    obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin K)))
      (n := K / 2) (by simp; omega)
    refine ⟨fun i => decide (i ∈ A), ?_⟩
    rw [mem_cuts]
    unfold sg
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hc := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin K))) (fun i => decide (i ∈ A) = true)
    have hfa : (univ.filter (fun i : Fin K => decide (i ∈ A) = true)) = A := by
      ext i; simp
    rw [hfa, hA, Finset.card_univ, Fintype.card_fin] at hc
    obtain ⟨k, hk⟩ := heven
    have h1 : (univ.filter (fun i : Fin K => ¬ decide (i ∈ A) = true)).card = K / 2 := by omega
    rw [hfa, hA, h1]; ring
  -- averaging: some balanced cut has at least the average same-side weight
  set D : ℝ := ∑ u, ∑ v, dist (x u) (x v)
  set c : ℝ := ((K : ℝ) - 2) / ((K : ℝ) - 1) * (D / 2)
  obtain ⟨b, hbC, hbig⟩ : ∃ b ∈ cuts K,
      c ≤ ∑ u, ∑ v, (1 + sg b u * sg b v) / 2 * dist (x u) (x v) := by
    apply Finset.exists_le_of_sum_le hne
    rw [sum_cuts_same (by omega) x, Finset.sum_const, nsmul_eq_mul]
  have hb := (mem_cuts b).1 hbC
  -- the cut as two finsets
  refine ⟨univ.filter (fun i => b i = true), univ.filter (fun i => ¬ b i = true),
    Finset.disjoint_filter_filter_not _ _ _, Finset.filter_union_filter_not_eq _ _, ?_, ?_, ?_⟩
  · have hc := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin K))) (fun i => b i = true)
    rw [Finset.card_univ, Fintype.card_fin] at hc
    have hs : ((univ.filter (fun i => b i = true)).card : ℝ)
        = (univ.filter (fun i => ¬ b i = true)).card := by
      unfold sg at hb
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at hb
      linarith
    have hs' : (univ.filter (fun i => b i = true)).card
        = (univ.filter (fun i => ¬ b i = true)).card := by exact_mod_cast hs
    omega
  · have hc := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin K))) (fun i => b i = true)
    rw [Finset.card_univ, Fintype.card_fin] at hc
    have hs : ((univ.filter (fun i => b i = true)).card : ℝ)
        = (univ.filter (fun i => ¬ b i = true)).card := by
      unfold sg at hb
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at hb
      linarith
    have hs' : (univ.filter (fun i => b i = true)).card
        = (univ.filter (fun i => ¬ b i = true)).card := by exact_mod_cast hs
    omega
  · intro y₀ y₁
    set y : Bool → α := fun t => if t then y₀ else y₁
    have hcore := core x b hb y
    have hstar : ∑ i, dist (x i) (y (b i))
        = ∑ i ∈ univ.filter (fun i => b i = true), dist (x i) y₀
          + ∑ i ∈ univ.filter (fun i => ¬ b i = true), dist (x i) y₁ := by
      rw [← Finset.sum_ite]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [y]; split_ifs <;> rfl
    rw [← hstar]
    have hpairs := sum_pairs x
    have hK2 : (0 : ℝ) < (K : ℝ) - 2 := by
      have : (4 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    have hK1 : (0 : ℝ) < (K : ℝ) - 1 := by linarith
    have hstar0 : 0 ≤ ∑ i, dist (x i) (y (b i)) := Finset.sum_nonneg (fun i _ => dist_nonneg)
    -- c ≤ (K-2)·star, i.e. (K-2)/(K-1)·D/2 ≤ (K-2)·star
    have h1 : ((K : ℝ) - 2) / ((K : ℝ) - 1) * (D / 2) ≤ ((K : ℝ) - 2) * ∑ i, dist (x i) (y (b i)) :=
      le_trans hbig hcore
    have h2 : D / 2 ≤ ((K : ℝ) - 1) * ∑ i, dist (x i) (y (b i)) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hK1] at h1
      nlinarith
    have hD : D / 2 = ∑ u, ∑ v ∈ univ.filter (fun v => u < v), dist (x u) (x v) := by
      simp only [D]; rw [hpairs]; ring
    rw [← hD]; exact h2

/-- **Remark (review-q2.md): Lemma N is false at `K = 2`.** Two points of `ℝ` at distance 1: for each
balanced cut put `y₀, y₁` at the two points. -/
theorem lemmaN_false_K2 :
    ¬ ∃ A B : Finset (Fin 2), Disjoint A B ∧ A ∪ B = univ ∧ A.card = 2 / 2 ∧ B.card = 2 / 2 ∧
      ∀ y₀ y₁ : ℝ,
        ∑ u, ∑ v ∈ univ.filter (fun v => u < v), dist (![(0 : ℝ), 1] u) (![(0 : ℝ), 1] v)
          ≤ ((2 : ℝ) - 1) * (∑ i ∈ A, dist (![(0 : ℝ), 1] i) y₀
              + ∑ i ∈ B, dist (![(0 : ℝ), 1] i) y₁) := by
  rintro ⟨A, B, -, -, hA, hB, h⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hA
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 hB
  have := h (![(0 : ℝ), 1] a) (![(0 : ℝ), 1] b)
  simp only [Finset.sum_singleton, dist_self, add_zero, mul_zero] at this
  have hl : ∑ u, ∑ v ∈ univ.filter (fun v => u < v), dist (![(0 : ℝ), 1] u) (![(0 : ℝ), 1] v)
      = 1 := by
    rw [Fin.sum_univ_two]
    have e0 : (univ.filter (fun v : Fin 2 => (0 : Fin 2) < v)) = {1} := by decide
    have e1 : (univ.filter (fun v : Fin 2 => (1 : Fin 2) < v)) = ∅ := by decide
    rw [e0, e1]; simp [Real.dist_eq]
  linarith

end LemmaN

end
