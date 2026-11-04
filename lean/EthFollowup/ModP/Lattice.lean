/-
# Divisor sums and the Gauss circle problem as tuple counts (module Lattice, pure Mathlib)

Counts over the network's box `[0, B)^k` (any `B > x`):
* `divQ B x = #{(a, b, s) : a·b + s = x, a > 0, b > 0}`; **`divQ_eq`**: `divQ B x = Σ_{m ≤ x} τ(m)` (`divSum x`).
* `sigQ B x = #{(a, b, c, s) : a·b + s = x, b > 0, 1 ≤ c ≤ a}`; **`sigQ_eq`**: `= Σ_{m ≤ x} σ(m)` (`sigSum x`).
  (The addendum's tuple lacks `b > 0`; without it `b = 0` adds `Σ_{a < B} a` — M0 finding.)
* `circ x = #{(u, v) ∈ [-x, x]² : u² + v² ≤ x}` (the statement's form),
  `circQ B x = #{(a, b, s) : a·a + b·b + s = x, a > 0}`; **`circ_eq`**: `circ x = 4·circQ B x + 1`
  (the nonzero lattice points split into four quadrants exchanged by the rotation `(u, v) ↦ (-v, u)`).
* `pairs B x = #{(a, b) : a, b > 0, a·b ≤ x}` and its fibres `pairs_fiber` (= `divisorsAntidiagonal`).

Standard axioms only.
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset

/-! ## Definitions -/

/-- `Σ_{m ≤ x} τ(m)`. -/
def divSum (x : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 x, (Nat.divisors m).card

/-- `Σ_{m ≤ x} σ(m)`. -/
def sigSum (x : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 x, ∑ d ∈ Nat.divisors m, d

/-- `#{(a, b, s) ∈ [0, B)³ : a·b + s = x, a > 0, b > 0}`. -/
def divQ (B x : ℕ) : ℕ :=
  ((range B ×ˢ range B ×ˢ range B).filter fun t : ℕ × ℕ × ℕ =>
    t.1 * t.2.1 + t.2.2 = x ∧ 0 < t.1 ∧ 0 < t.2.1).card

/-- `#{(a, b, c, s) ∈ [0, B)⁴ : a·b + s = x, b > 0, 1 ≤ c ≤ a}`. -/
def sigQ (B x : ℕ) : ℕ :=
  ((range B ×ˢ range B ×ˢ range B ×ˢ range B).filter fun t : ℕ × ℕ × ℕ × ℕ =>
    t.1 * t.2.1 + t.2.2.2 = x ∧ 0 < t.2.1 ∧ 1 ≤ t.2.2.1 ∧ t.2.2.1 ≤ t.1).card

/-- The lattice points of the disc `u² + v² ≤ x`. -/
def discPts (x : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(x : ℤ)) x ×ˢ Finset.Icc (-(x : ℤ)) x).filter fun q : ℤ × ℤ => q.1 ^ 2 + q.2 ^ 2 ≤ x

/-- Gauss circle count `#{(u, v) ∈ [-x, x]² : u² + v² ≤ x}`. -/
def circ (x : ℕ) : ℕ :=
  ((Finset.Icc (-(x : ℤ)) x ×ˢ Finset.Icc (-(x : ℤ)) x).filter fun q : ℤ × ℤ =>
    q.1 ^ 2 + q.2 ^ 2 ≤ x).card

/-- `#{(a, b, s) ∈ [0, B)³ : a·a + b·b + s = x, a > 0}`. -/
def circQ (B x : ℕ) : ℕ :=
  ((range B ×ˢ range B ×ˢ range B).filter fun t : ℕ × ℕ × ℕ =>
    t.1 * t.1 + t.2.1 * t.2.1 + t.2.2 = x ∧ 0 < t.1).card

/-- The pairs `(a, b) ∈ [0, B)²` with `a, b > 0`, `a·b ≤ x`. -/
def pairs (B x : ℕ) : Finset (ℕ × ℕ) :=
  (range B ×ˢ range B).filter fun q : ℕ × ℕ => 0 < q.1 ∧ 0 < q.2 ∧ q.1 * q.2 ≤ x

/-! ## Divisor sums -/

theorem divQ_eq_pairs {B x : ℕ} (hB : x < B) : divQ B x = (pairs B x).card := by
  unfold divQ pairs
  apply Finset.card_nbij' (fun t : ℕ × ℕ × ℕ => (t.1, t.2.1))
    (fun q : ℕ × ℕ => (q.1, q.2, x - q.1 * q.2))
  · rintro ⟨a, b, s⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h ⊢
    obtain ⟨⟨ha, hb, -⟩, he, ha0, hb0⟩ := h
    exact ⟨⟨ha, hb⟩, ha0, hb0, by omega⟩
  · rintro ⟨a, b⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h ⊢
    obtain ⟨⟨ha, hb⟩, ha0, hb0, hle⟩ := h
    exact ⟨⟨ha, hb, by omega⟩, by omega, ha0, hb0⟩
  · rintro ⟨a, b, s⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h
    simp only [Prod.mk.injEq, true_and]
    omega
  · rintro ⟨a, b⟩ -
    rfl

theorem pairs_fiber {B x m : ℕ} (hB : x < B) (hm : m ∈ Icc 1 x) :
    (pairs B x).filter (fun q => q.1 * q.2 = m) = m.divisorsAntidiagonal := by
  simp only [mem_Icc] at hm
  ext ⟨a, b⟩
  simp only [pairs, mem_filter, mem_product, mem_range, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨-, h⟩; exact ⟨h, by omega⟩
  · rintro ⟨h, -⟩
    have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at h; omega)
    have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at h; omega)
    have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb0
    have h2 : b ≤ a * b := Nat.le_mul_of_pos_left b ha0
    exact ⟨⟨⟨by omega, by omega⟩, ha0, hb0, by omega⟩, h⟩

theorem pairs_mapsTo {B x : ℕ} (q : ℕ × ℕ) (hq : q ∈ pairs B x) : q.1 * q.2 ∈ Icc 1 x := by
  simp only [pairs, mem_filter, mem_product, mem_range] at hq
  simp only [mem_Icc]
  exact ⟨Nat.mul_pos hq.2.1 hq.2.2.1, hq.2.2.2⟩

theorem card_pairs {B x : ℕ} (hB : x < B) : (pairs B x).card = divSum x := by
  rw [card_eq_sum_card_fiberwise (f := fun q : ℕ × ℕ => q.1 * q.2) (t := Icc 1 x)
    (fun q hq => pairs_mapsTo q (by simpa using hq))]
  apply sum_congr rfl
  intro m hm
  rw [pairs_fiber hB hm, ← Nat.map_div_right_divisors, card_map]

/-- **Divisor sum**: `Σ_{m ≤ x} τ(m) = #{(a, b, s) : a·b + s = x, a, b > 0}` for `x < B`. -/
theorem divQ_eq {B x : ℕ} (hB : x < B) : divQ B x = divSum x := by
  rw [divQ_eq_pairs hB, card_pairs hB]

/-! ## Sums of divisors -/

theorem sigQ_eq_triples {B x : ℕ} (hB : x < B) :
    sigQ B x = ((range B ×ˢ range B ×ˢ range B).filter fun t : ℕ × ℕ × ℕ =>
      0 < t.2.1 ∧ 1 ≤ t.2.2 ∧ t.2.2 ≤ t.1 ∧ t.1 * t.2.1 ≤ x).card := by
  unfold sigQ
  apply Finset.card_nbij' (fun t : ℕ × ℕ × ℕ × ℕ => (t.1, t.2.1, t.2.2.1))
    (fun t : ℕ × ℕ × ℕ => (t.1, t.2.1, t.2.2, x - t.1 * t.2.1))
  · rintro ⟨a, b, c, s⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h ⊢
    obtain ⟨⟨ha, hb, hc, -⟩, he, hb0, hc1, hca⟩ := h
    exact ⟨⟨ha, hb, hc⟩, hb0, hc1, hca, by omega⟩
  · rintro ⟨a, b, c⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h ⊢
    obtain ⟨⟨ha, hb, hc⟩, hb0, hc1, hca, hle⟩ := h
    exact ⟨⟨ha, hb, hc, by omega⟩, by omega, hb0, hc1, hca⟩
  · rintro ⟨a, b, c, s⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h
    simp only [Prod.mk.injEq, true_and]
    omega
  · rintro ⟨a, b, c⟩ -
    rfl

/-- **Sum of divisors**: `Σ_{m ≤ x} σ(m) = #{(a, b, c, s) : a·b + s = x, b > 0, 1 ≤ c ≤ a}`. -/
theorem sigQ_eq {B x : ℕ} (hB : x < B) : sigQ B x = sigSum x := by
  rw [sigQ_eq_triples hB]
  set T := (range B ×ˢ range B ×ˢ range B).filter fun t : ℕ × ℕ × ℕ =>
      0 < t.2.1 ∧ 1 ≤ t.2.2 ∧ t.2.2 ≤ t.1 ∧ t.1 * t.2.1 ≤ x
  have hmaps : ∀ t ∈ T, (t.1, t.2.1) ∈ pairs B x := by
    intro t ht
    simp only [T, mem_filter, mem_product, mem_range] at ht
    simp only [pairs, mem_filter, mem_product, mem_range]
    exact ⟨⟨ht.1.1, ht.1.2.1⟩, by omega, ht.2.1, ht.2.2.2.2⟩
  rw [card_eq_sum_card_fiberwise (f := fun t : ℕ × ℕ × ℕ => (t.1, t.2.1)) (t := pairs B x)
    (fun t ht => hmaps t (by simpa using ht))]
  have hfib : ∀ q ∈ pairs B x, (T.filter fun t => (t.1, t.2.1) = q).card = q.1 := by
    rintro ⟨a, b⟩ hq
    simp only [pairs, mem_filter, mem_product, mem_range] at hq
    have hab : a ≤ a * b := Nat.le_mul_of_pos_right a hq.2.2.1
    have hI : (Icc 1 a).card = a := by simp
    refine Eq.trans ?_ hI
    apply Finset.card_nbij' (fun t : ℕ × ℕ × ℕ => t.2.2) (fun c => (a, b, c))
    · rintro ⟨a', b', c⟩ h
      simp only [T, coe_filter, mem_filter, mem_product, mem_range, Set.mem_setOf_eq,
        Prod.mk.injEq, mem_coe, mem_Icc] at h ⊢
      obtain ⟨⟨-, -, hc1, hca, -⟩, rfl, rfl⟩ := h
      exact ⟨hc1, hca⟩
    · intro c h
      simp only [T, coe_filter, mem_filter, mem_product, mem_range, Set.mem_setOf_eq,
        Prod.mk.injEq, mem_coe, mem_Icc] at h ⊢
      exact ⟨⟨⟨hq.1.1, hq.1.2, by omega⟩, hq.2.2.1, h.1, h.2, hq.2.2.2⟩, trivial, trivial⟩
    · rintro ⟨a', b', c⟩ h
      simp only [T, coe_filter, mem_filter, Set.mem_setOf_eq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      rfl
    · intro c _
      rfl
  rw [sum_congr rfl hfib]
  rw [← sum_fiberwise_of_maps_to (g := fun q : ℕ × ℕ => q.1 * q.2) (t := Icc 1 x)
    (fun q hq => pairs_mapsTo q (by simpa using hq))]
  unfold sigSum
  apply sum_congr rfl
  intro m hm
  rw [pairs_fiber hB hm, Nat.sum_divisorsAntidiagonal (fun a _ => a)]

/-! ## The Gauss circle -/

theorem circ_eq_card (x : ℕ) : circ x = (discPts x).card := rfl

/-- The rotation `(u, v) ↦ (-v, u)` exchanges the parts of the disc cut out by `P` and `Q`. -/
theorem card_rot {x : ℕ} (P Q : ℤ × ℤ → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ q : ℤ × ℤ, Q q ↔ P (q.2, -q.1)) :
    ((discPts x).filter P).card = ((discPts x).filter Q).card := by
  apply Finset.card_nbij' (fun q : ℤ × ℤ => (-q.2, q.1)) (fun q : ℤ × ℤ => (q.2, -q.1))
  · rintro ⟨u, v⟩ h
    simp only [discPts, coe_filter, mem_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at h ⊢
    obtain ⟨⟨⟨⟨hu1, hu2⟩, hv1, hv2⟩, hx⟩, hP⟩ := h
    refine ⟨⟨⟨⟨by linarith, by linarith⟩, hu1, hu2⟩, by nlinarith⟩, ?_⟩
    rw [hPQ]; simpa using hP
  · rintro ⟨u, v⟩ h
    simp only [discPts, coe_filter, mem_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at h ⊢
    obtain ⟨⟨⟨⟨hu1, hu2⟩, hv1, hv2⟩, hx⟩, hQ⟩ := h
    refine ⟨⟨⟨⟨hv1, hv2⟩, by linarith, by linarith⟩, by nlinarith⟩, ?_⟩
    exact (hPQ _).1 hQ
  · rintro ⟨u, v⟩ -
    simp
  · rintro ⟨u, v⟩ -
    simp

theorem card_quadrant (B x : ℕ) (hB : x < B) :
    ((discPts x).filter fun q => 0 < q.1 ∧ 0 ≤ q.2).card =
      ((range B ×ˢ range B).filter fun q : ℕ × ℕ => 0 < q.1 ∧ q.1 * q.1 + q.2 * q.2 ≤ x).card := by
  symm
  apply Finset.card_nbij' (fun q : ℕ × ℕ => ((q.1 : ℤ), (q.2 : ℤ)))
    (fun q : ℤ × ℤ => (q.1.toNat, q.2.toNat))
  · rintro ⟨a, b⟩ h
    simp only [discPts, coe_filter, mem_filter, mem_product, mem_Icc, mem_range,
      Set.mem_setOf_eq] at h ⊢
    obtain ⟨-, ha0, hx⟩ := h
    have h1 : a ≤ a * a := Nat.le_mul_self a
    have h2 : b ≤ b * b := Nat.le_mul_self b
    have hx' : ((a * a + b * b : ℕ) : ℤ) ≤ x := by exact_mod_cast hx
    push_cast at hx'
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by nlinarith⟩, by omega, by omega⟩
  · rintro ⟨u, v⟩ h
    simp only [discPts, coe_filter, mem_filter, mem_product, mem_Icc, mem_range,
      Set.mem_setOf_eq] at h ⊢
    obtain ⟨⟨⟨⟨-, hu2⟩, -, hv2⟩, hx⟩, hu0, hv0⟩ := h
    obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hu0.le
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hv0
    simp only [Int.toNat_natCast]
    have hx' : ((a * a + b * b : ℕ) : ℤ) ≤ x := by push_cast; nlinarith
    exact ⟨⟨by omega, by omega⟩, by omega, by exact_mod_cast hx'⟩
  · rintro ⟨a, b⟩ -
    simp
  · rintro ⟨u, v⟩ h
    simp only [discPts, coe_filter, mem_filter, Set.mem_setOf_eq] at h
    simp [Int.toNat_of_nonneg h.2.1.le, Int.toNat_of_nonneg h.2.2]

theorem circQ_eq_pairs {B x : ℕ} (hB : x < B) :
    circQ B x =
      ((range B ×ˢ range B).filter fun q : ℕ × ℕ => 0 < q.1 ∧ q.1 * q.1 + q.2 * q.2 ≤ x).card := by
  unfold circQ
  apply Finset.card_nbij' (fun t : ℕ × ℕ × ℕ => (t.1, t.2.1))
    (fun q : ℕ × ℕ => (q.1, q.2, x - (q.1 * q.1 + q.2 * q.2)))
  · rintro ⟨a, b, s⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h ⊢
    obtain ⟨⟨ha, hb, -⟩, he, ha0⟩ := h
    exact ⟨⟨ha, hb⟩, ha0, by omega⟩
  · rintro ⟨a, b⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h ⊢
    obtain ⟨⟨ha, hb⟩, ha0, hle⟩ := h
    exact ⟨⟨ha, hb, by omega⟩, by omega, ha0⟩
  · rintro ⟨a, b, s⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h
    simp only [Prod.mk.injEq, true_and]
    omega
  · rintro ⟨a, b⟩ -
    rfl

/-- **Gauss circle**: `#{(u, v) ∈ [-x, x]² : u² + v² ≤ x} = 4·#{(a, b, s) : a·a + b·b + s = x, a > 0} + 1`. -/
theorem circ_eq {B x : ℕ} (hB : x < B) : circ x = 4 * circQ B x + 1 := by
  have r1 := card_rot (x := x) (fun q : ℤ × ℤ => 0 < q.1 ∧ 0 ≤ q.2)
    (fun q => q.1 ≤ 0 ∧ 0 < q.2) (fun q => by dsimp only; omega)
  have r2 := card_rot (x := x) (fun q : ℤ × ℤ => q.1 ≤ 0 ∧ 0 < q.2)
    (fun q => q.1 < 0 ∧ q.2 ≤ 0) (fun q => by dsimp only; omega)
  have r3 := card_rot (x := x) (fun q : ℤ × ℤ => q.1 < 0 ∧ q.2 ≤ 0)
    (fun q => 0 ≤ q.1 ∧ q.2 < 0) (fun q => by dsimp only; omega)
  have h0 : ((discPts x).filter fun q : ℤ × ℤ => q.1 = 0 ∧ q.2 = 0).card = 1 := by
    rw [card_eq_one]
    refine ⟨(0, 0), ?_⟩
    ext ⟨u, v⟩
    simp only [discPts, mem_filter, mem_product, mem_Icc, mem_singleton, Prod.mk.injEq]
    constructor
    · exact fun h => h.2
    · rintro ⟨rfl, rfl⟩
      refine ⟨⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by norm_num⟩, rfl, rfl⟩
  have hsplit : (discPts x).card =
      ((discPts x).filter fun q : ℤ × ℤ => q.1 = 0 ∧ q.2 = 0).card +
      ((discPts x).filter fun q : ℤ × ℤ => 0 < q.1 ∧ 0 ≤ q.2).card +
      ((discPts x).filter fun q : ℤ × ℤ => q.1 ≤ 0 ∧ 0 < q.2).card +
      ((discPts x).filter fun q : ℤ × ℤ => q.1 < 0 ∧ q.2 ≤ 0).card +
      ((discPts x).filter fun q : ℤ × ℤ => 0 ≤ q.1 ∧ q.2 < 0).card := by
    rw [card_eq_sum_ones, card_filter, card_filter, card_filter, card_filter, card_filter,
      ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    rintro ⟨u, v⟩ -
    dsimp only
    split_ifs <;> omega
  rw [circ_eq_card, hsplit, h0, ← r3, ← r2, ← r1, card_quadrant B x hB, circQ_eq_pairs hB]
  ring

/-! ## Sanity checks (addendum values) -/

example : divSum 10 = 27 ∧ divQ 11 10 = 27 := by decide +kernel
example : circ 10 = 37 ∧ circQ 11 10 = 9 := by decide +kernel
example : sigSum 10 = 87 := by decide +kernel

end EthFollowup.ModP
