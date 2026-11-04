/-
# Square roots and quadratic non-residues: definitions and counting identities (module M4, pure Mathlib)

* `minRoot m a`: the least `y < m` with `y² ≡ a (mod m)`, or `m` if there is none;
  `lqnr p`: the least `x < p` that is not a square mod `p`, or `p` if there is none.
  `minRoot_spec`, `minRoot_eq_min'`, `minRoot_eq_of_empty`, `minRoot_mod`, `minRoot_zero/one`;
  `lqnr_spec` (`p` prime, `2 < p`), `lqnr_lt` (via `FiniteField.exists_nonsquare`),
  `lqnr_eq_min'`, `lqnr_small`; `isSquare_zmod_iff`.
* `S3A n' n m a π`: `#{(y, k, x) ∈ [0, 2^n')³ : y² = x + k m ∧ y < m ∧ x < m ∧ pre(y) ∧ x = a}`
  with `pre(y) := y / 2^(n - |π|) = ofWord π`. **(I-A)** `S3A_eq`: for `m ≤ 2^n'` it is
  `#{y < m : y² mod m = a ∧ pre(y)}` (bijection `(y, k, x) ↦ y`, inverse `y ↦ (y, y²/m, y² mod m)`,
  `card_triples`); `S3A_pos_iff`.
* `S3B n' n p π`: `#{(y, k, x) : y² = x + k p ∧ y < p ∧ x < p ∧ pre(x)}`.
  `rootCount_eq` (two roots of a nonzero square mod an odd prime, one root of `0`, none of a
  non-square), **(I-B)** `S3B_eq`, `S3B_eq_isSquare`:
  `S3B = 2·#{x < p : pre(x) ∧ x ≠ 0 ∧ IsSquare (x : ZMod p)} + [ofWord π = 0]`.
* `NR n p π = #{x < p : pre(x) ∧ x non-square}`, `rangeCount`, `z0`, `nrOf`;
  `card_pre` (`#{x < p : pre x} = rangeCount`), **NR formula** `NR_eq`:
  `NR = rangeCount - z0 - (S3B - z0)/2`; positivity `NR_pos_iff`, `nrOf_S3B_pos_iff`.

Standard axioms only.
-/
import EthFollowup.Factoring.Search
import Mathlib.FieldTheory.Finite.Basic

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset EthFollowup.Factoring.Search

/-! ## Definitions (§2, verbatim) -/

/-- The least square root of `a` modulo `m` (none: `m`). -/
def minRoot (m a : ℕ) : ℕ :=
  Nat.find (⟨m, Or.inl rfl⟩ : ∃ y, y = m ∨ (y < m ∧ y * y % m = a % m))

/-- The least quadratic non-residue modulo `p` (none: `p`). -/
def lqnr (p : ℕ) : ℕ := Nat.find (⟨p, Or.inl rfl⟩ : ∃ x, x = p ∨ (x < p ∧ ∀ y < p, y * y % p ≠ x))

/-- The roots of `a` modulo `m` in `[0, m)`. -/
def rootSet (m a : ℕ) : Finset ℕ := (range m).filter fun y => y * y % m = a % m

/-- The non-residues modulo `p` in `[0, p)`. -/
def nrSet (p : ℕ) : Finset ℕ := (range p).filter fun x => ∀ y < p, y * y % p ≠ x

/-! ## `minRoot` -/

theorem minRoot_le (m a : ℕ) : minRoot m a ≤ m := Nat.find_min' _ (Or.inl rfl)

theorem minRoot_spec' (m a : ℕ) :
    minRoot m a = m ∨ (minRoot m a < m ∧ minRoot m a * minRoot m a % m = a % m) :=
  Nat.find_spec (⟨m, Or.inl rfl⟩ : ∃ y, y = m ∨ (y < m ∧ y * y % m = a % m))

theorem not_root_of_lt_minRoot {m a y : ℕ} (hy : y < minRoot m a) : y * y % m ≠ a % m := by
  have h := Nat.find_min (⟨m, Or.inl rfl⟩ : ∃ y, y = m ∨ (y < m ∧ y * y % m = a % m)) hy
  have hle := minRoot_le m a
  intro hr
  exact h (Or.inr ⟨by omega, hr⟩)

theorem minRoot_spec (m a : ℕ) :
    minRoot m a ≤ m ∧ (minRoot m a < m → minRoot m a * minRoot m a % m = a % m) ∧
      (∀ y < minRoot m a, y * y % m ≠ a % m) ∧
      (minRoot m a = m ↔ ∀ y < m, y * y % m ≠ a % m) := by
  refine ⟨minRoot_le m a, fun h => ?_, fun y hy => not_root_of_lt_minRoot hy, ⟨fun h y hy => ?_, fun h => ?_⟩⟩
  · rcases minRoot_spec' m a with h' | h'
    · omega
    · exact h'.2
  · exact not_root_of_lt_minRoot (by omega)
  · rcases minRoot_spec' m a with h' | h'
    · exact h'
    · exact absurd h'.2 (h _ h'.1)

theorem minRoot_mem {m a : ℕ} (h : (rootSet m a).Nonempty) : minRoot m a ∈ rootSet m a := by
  obtain ⟨y, hy⟩ := h
  simp only [rootSet, mem_filter, mem_range] at hy ⊢
  rcases minRoot_spec' m a with h' | h'
  · have := Nat.find_min' (⟨m, Or.inl rfl⟩ : ∃ y, y = m ∨ (y < m ∧ y * y % m = a % m))
      (Or.inr hy)
    unfold minRoot at h'; omega
  · exact h'

theorem minRoot_eq_min' {m a : ℕ} (h : (rootSet m a).Nonempty) :
    minRoot m a = (rootSet m a).min' h := by
  apply le_antisymm
  · have hm := (rootSet m a).min'_mem h
    simp only [rootSet, mem_filter, mem_range] at hm
    exact Nat.find_min' _ (Or.inr hm)
  · exact (rootSet m a).min'_le _ (minRoot_mem h)

theorem minRoot_eq_of_empty {m a : ℕ} (h : rootSet m a = ∅) : minRoot m a = m := by
  rcases minRoot_spec' m a with h' | h'
  · exact h'
  · have : minRoot m a ∈ rootSet m a := by simp only [rootSet, mem_filter, mem_range]; exact h'
    rw [h] at this; simp at this

theorem rootSet_mod (m a : ℕ) : rootSet m (a % m) = rootSet m a := by
  simp only [rootSet, Nat.mod_mod]

theorem minRoot_mod (m a : ℕ) : minRoot m (a % m) = minRoot m a := by
  by_cases h : (rootSet m a).Nonempty
  · have h' : (rootSet m (a % m)).Nonempty := by rwa [rootSet_mod]
    rw [minRoot_eq_min' h, minRoot_eq_min' h']
    simp only [rootSet_mod]
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [minRoot_eq_of_empty h, minRoot_eq_of_empty (by rw [rootSet_mod]; exact h)]

theorem minRoot_zero (a : ℕ) : minRoot 0 a = 0 := Nat.find_eq_zero _ |>.2 (Or.inl rfl)

theorem minRoot_one (a : ℕ) : minRoot 1 a = 0 :=
  Nat.find_eq_zero _ |>.2 (Or.inr ⟨one_pos, by simp [Nat.mod_one]⟩)

/-! ## Squares in `ZMod p` -/

theorem isSquare_zmod_iff {p x : ℕ} (hp : 0 < p) (hx : x < p) :
    IsSquare (x : ZMod p) ↔ ∃ y < p, y * y % p = x := by
  have : NeZero p := ⟨hp.ne'⟩
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r.val, ZMod.val_lt r, ?_⟩
    have h : ((r.val * r.val : ℕ) : ZMod p) = (x : ZMod p) := by
      push_cast; rw [ZMod.natCast_zmod_val, hr]
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx] at h
    exact h
  · rintro ⟨y, -, h⟩
    exact ⟨y, by rw [← h, ZMod.natCast_mod]; push_cast; ring⟩

theorem natCast_ne_zero_of_lt {p x : ℕ} (h0 : x ≠ 0) (hx : x < p) : (x : ZMod p) ≠ 0 := by
  intro h
  have := ZMod.val_cast_of_lt hx
  rw [h, ZMod.val_zero] at this
  omega

/-! ## `lqnr` -/

theorem lqnr_le (p : ℕ) : lqnr p ≤ p := Nat.find_min' _ (Or.inl rfl)

theorem lqnr_spec' (p : ℕ) : lqnr p = p ∨ (lqnr p < p ∧ ∀ y < p, y * y % p ≠ lqnr p) :=
  Nat.find_spec (⟨p, Or.inl rfl⟩ : ∃ x, x = p ∨ (x < p ∧ ∀ y < p, y * y % p ≠ x))

theorem square_of_lt_lqnr {p x : ℕ} (hx : x < lqnr p) : ∃ y < p, y * y % p = x := by
  have h := Nat.find_min (⟨p, Or.inl rfl⟩ : ∃ x, x = p ∨ (x < p ∧ ∀ y < p, y * y % p ≠ x)) hx
  have hle := lqnr_le p
  by_contra hc
  simp only [not_exists, not_and] at hc
  exact h (Or.inr ⟨by omega, hc⟩)

theorem lqnr_mem {p : ℕ} (h : (nrSet p).Nonempty) : lqnr p ∈ nrSet p := by
  obtain ⟨x, hx⟩ := h
  simp only [nrSet, mem_filter, mem_range] at hx ⊢
  rcases lqnr_spec' p with h' | h'
  · have := Nat.find_min' (⟨p, Or.inl rfl⟩ : ∃ x, x = p ∨ (x < p ∧ ∀ y < p, y * y % p ≠ x))
      (Or.inr hx)
    unfold lqnr at h'; omega
  · exact h'

theorem lqnr_eq_min' {p : ℕ} (h : (nrSet p).Nonempty) : lqnr p = (nrSet p).min' h := by
  apply le_antisymm
  · have hm := (nrSet p).min'_mem h
    simp only [nrSet, mem_filter, mem_range] at hm
    exact Nat.find_min' _ (Or.inr hm)
  · exact (nrSet p).min'_le _ (lqnr_mem h)

theorem lqnr_eq_of_empty {p : ℕ} (h : nrSet p = ∅) : lqnr p = p := by
  rcases lqnr_spec' p with h' | h'
  · exact h'
  · have : lqnr p ∈ nrSet p := by simp only [nrSet, mem_filter, mem_range]; exact h'
    rw [h] at this; simp at this

/-- A non-residue exists modulo every prime `p ≥ 3`. -/
theorem nrSet_nonempty {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : (nrSet p).Nonempty := by
  have := Fact.mk hp
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; omega)
  refine ⟨x.val, ?_⟩
  simp only [nrSet, mem_filter, mem_range]
  refine ⟨ZMod.val_lt x, fun y hy hyx => hx ?_⟩
  have := (isSquare_zmod_iff hp.pos (ZMod.val_lt x)).2 ⟨y, hy, hyx⟩
  rwa [ZMod.natCast_zmod_val] at this

theorem lqnr_lt {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : lqnr p < p := by
  have := lqnr_mem (nrSet_nonempty hp h3)
  simp only [nrSet, mem_filter, mem_range] at this
  exact this.1

/-- **`lqnr` is the least quadratic non-residue** modulo an odd prime. -/
theorem lqnr_spec {p : ℕ} (hp : p.Prime) (h2 : 2 < p) :
    lqnr p < p ∧ ¬IsSquare (lqnr p : ZMod p) ∧ ∀ x < lqnr p, IsSquare (x : ZMod p) := by
  have hlt := lqnr_lt hp h2
  refine ⟨hlt, fun hsq => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, h⟩ := (isSquare_zmod_iff hp.pos hlt).1 hsq
    rcases lqnr_spec' p with h' | h'
    · omega
    · exact h'.2 y hy h
  · exact (isSquare_zmod_iff hp.pos (by omega)).2 (square_of_lt_lqnr hx)

theorem lqnr_small : lqnr 0 = 0 ∧ lqnr 1 = 1 ∧ lqnr 2 = 2 := by
  refine ⟨Nat.find_eq_zero _ |>.2 (Or.inl rfl), ?_, ?_⟩
  · rw [lqnr, Nat.find_eq_iff]
    refine ⟨Or.inl rfl, fun k hk => ?_⟩
    interval_cases k
    simp
  · rw [lqnr, Nat.find_eq_iff]
    refine ⟨Or.inl rfl, fun k hk => ?_⟩
    interval_cases k
    · simp only [not_or]; exact ⟨by omega, fun h => h.2 0 (by omega) rfl⟩
    · simp only [not_or]; exact ⟨by omega, fun h => h.2 1 (by omega) rfl⟩

/-! ## The triple counts -/


/-- `S3A n' n m a π = #{(y, k, x) ∈ [0,2^n')³ : y*y = x + k*m ∧ y < m ∧ x < m ∧ pre(y) ∧ x = a}`. -/
def S3A (n' n m a : ℕ) (π : List Bool) : ℕ :=
  ((range (2 ^ n') ×ˢ range (2 ^ n') ×ˢ range (2 ^ n')).filter fun t : ℕ × ℕ × ℕ =>
    t.1 * t.1 = t.2.2 + t.2.1 * m ∧ t.1 < m ∧ t.2.2 < m ∧
      t.1 / 2 ^ (n - π.length) = ofWord π ∧ t.2.2 = a).card

/-- `S3B n' n p π = #{(y, k, x) ∈ [0,2^n')³ : y*y = x + k*p ∧ y < p ∧ x < p ∧ pre(x)}`. -/
def S3B (n' n p : ℕ) (π : List Bool) : ℕ :=
  ((range (2 ^ n') ×ˢ range (2 ^ n') ×ˢ range (2 ^ n')).filter fun t : ℕ × ℕ × ℕ =>
    t.1 * t.1 = t.2.2 + t.2.1 * p ∧ t.1 < p ∧ t.2.2 < p ∧
      t.2.2 / 2 ^ (n - π.length) = ofWord π).card

/-- The bijection `(y, k, x) ↦ y` of the triples with `y² = x + k m`, `y, x < m` onto `[0, m)`. -/
theorem card_triples {n' m : ℕ} (hm : m ≤ 2 ^ n') (P : ℕ → ℕ → Prop) [DecidableRel P] :
    ((range (2 ^ n') ×ˢ range (2 ^ n') ×ˢ range (2 ^ n')).filter fun t : ℕ × ℕ × ℕ =>
      t.1 * t.1 = t.2.2 + t.2.1 * m ∧ t.1 < m ∧ t.2.2 < m ∧ P t.1 t.2.2).card =
    ((range m).filter fun y => P y (y * y % m)).card := by
  apply Finset.card_nbij' (fun t => t.1) (fun y => (y, y * y / m, y * y % m))
  · rintro ⟨y, k, x⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h ⊢
    obtain ⟨-, he, hy, hx, hP⟩ := h
    have hm0 : 0 < m := by omega
    have hxm : y * y % m = x := by rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
    rw [hxm]; exact ⟨hy, hP⟩
  · intro y h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h ⊢
    obtain ⟨hy, hP⟩ := h
    have hm0 : 0 < m := by omega
    have hk : y * y / m ≤ y := Nat.div_le_of_le_mul (Nat.mul_le_mul_right y hy.le)
    exact ⟨⟨by omega, by omega, lt_of_lt_of_le (Nat.mod_lt _ hm0) hm⟩,
      (Nat.mod_add_div' _ _).symm, hy, Nat.mod_lt _ hm0, hP⟩
  · rintro ⟨y, k, x⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h
    obtain ⟨-, he, hy, hx, -⟩ := h
    have hm0 : 0 < m := by omega
    simp only [Prod.mk.injEq, true_and]
    rw [he, Nat.add_mul_div_right _ _ hm0, Nat.div_eq_of_lt hx, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hx]
    simp
  · intro y _
    rfl

/-- **(I-A)** For `m ≤ 2^n'` the count `S3A` is the number of roots `y < m` of `a` with prefix `π`. -/
theorem S3A_eq {n' n m a : ℕ} (π : List Bool) (hm : m ≤ 2 ^ n') :
    S3A n' n m a π =
      ((range m).filter fun y => y * y % m = a ∧ y / 2 ^ (n - π.length) = ofWord π).card := by
  rw [S3A, card_triples hm (fun y x => y / 2 ^ (n - π.length) = ofWord π ∧ x = a)]
  congr 1
  apply filter_congr
  intro y _
  exact and_comm

/-- Positivity of `S3A` at the reduced residue `a % m`: some root of `a` has prefix `π`. -/
theorem S3A_pos_iff {n' n m a : ℕ} (π : List Bool) (hm : m ≤ 2 ^ n') :
    0 < S3A n' n m (a % m) π ↔ ∃ y ∈ rootSet m a, y / 2 ^ (n - π.length) = ofWord π := by
  rw [S3A_eq π hm, card_pos, filter_nonempty_iff]
  simp only [rootSet, mem_filter, mem_range]
  constructor
  · rintro ⟨y, hy, h1, h2⟩; exact ⟨y, ⟨hy, h1⟩, h2⟩
  · rintro ⟨y, ⟨hy, h1⟩, h2⟩; exact ⟨y, hy, h1, h2⟩

/-! ## Roots modulo an odd prime -/

/-- The number of roots `y < p` of `x` modulo `p`. -/
def rootCount (p x : ℕ) : ℕ := ((range p).filter fun y => y * y % p = x).card

theorem rootCount_eq_zmod {p x : ℕ} [NeZero p] (hx : x < p) :
    rootCount p x = (univ.filter fun r : ZMod p => r * r = (x : ZMod p)).card := by
  apply Finset.card_nbij' (fun y : ℕ => (y : ZMod p)) (fun r => r.val)
  · intro y h
    simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_univ, true_and] at h ⊢
    have : ((y * y : ℕ) : ZMod p) = (x : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff', h.2, Nat.mod_eq_of_lt hx]
    push_cast at this; exact this
  · intro r h
    simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_univ, true_and] at h ⊢
    refine ⟨ZMod.val_lt r, ?_⟩
    have e : ((r.val * r.val : ℕ) : ZMod p) = (x : ZMod p) := by
      push_cast; rw [ZMod.natCast_zmod_val, h]
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx] at e
    exact e
  · intro y h
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at h
    exact ZMod.val_cast_of_lt h.1
  · intro r _
    exact ZMod.natCast_zmod_val r

/-- **(I-B), local form**: modulo an odd prime, a nonzero square has two roots, `0` has one, a
non-square has none. -/
theorem rootCount_eq {p x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hx : x < p) :
    rootCount p x = 2 * (if x ≠ 0 ∧ ∃ y < p, y * y % p = x then 1 else 0) +
      (if x = 0 then 1 else 0) := by
  have := Fact.mk hp
  rw [rootCount_eq_zmod hx]
  by_cases h0 : x = 0
  · subst h0
    have : (univ.filter fun r : ZMod p => r * r = ((0 : ℕ) : ZMod p)) = {0} := by
      ext r; simp
    rw [this]; simp
  · rw [if_neg h0]
    by_cases hsq : ∃ y < p, y * y % p = x
    · rw [if_pos ⟨h0, hsq⟩]
      obtain ⟨s, hs⟩ := (isSquare_zmod_iff hp.pos hx).2 hsq
      have hs0 : s ≠ 0 := by
        rintro rfl; exact natCast_ne_zero_of_lt h0 hx (by rw [hs, mul_zero])
      have h2 : (2 : ZMod p) ≠ 0 := by
        have := natCast_ne_zero_of_lt (p := p) (x := 2) (by omega)
          (lt_of_le_of_ne hp.two_le (Ne.symm hp2))
        exact_mod_cast this
      have hne : s ≠ -s := by
        intro h
        have : (2 : ZMod p) * s = 0 := by rw [two_mul]; nth_rewrite 2 [h]; exact add_neg_cancel s
        rcases mul_eq_zero.1 this with h' | h'
        · exact h2 h'
        · exact hs0 h'
      have : (univ.filter fun r : ZMod p => r * r = (x : ZMod p)) = {s, -s} := by
        ext r
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, hs]
        exact mul_self_eq_mul_self_iff
      rw [this, card_pair hne]
    · rw [if_neg (fun h => hsq h.2)]
      have : (univ.filter fun r : ZMod p => r * r = (x : ZMod p)) = ∅ := by
        ext r
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
        intro hr
        exact hsq ((isSquare_zmod_iff hp.pos hx).1 ⟨r, hr.symm⟩)
      rw [this]; simp

/-- The prefix-`π` residues `x < p`. -/
theorem S3B_eq_sum {n' n p : ℕ} (π : List Bool) (hpn : p ≤ 2 ^ n') :
    S3B n' n p π = ∑ x ∈ (range p).filter (fun x => x / 2 ^ (n - π.length) = ofWord π),
      rootCount p x := by
  rw [S3B, card_triples hpn (fun _ x => x / 2 ^ (n - π.length) = ofWord π)]
  rw [card_eq_sum_card_fiberwise (f := fun y => y * y % p)
    (t := (range p).filter (fun x => x / 2 ^ (n - π.length) = ofWord π))]
  · apply sum_congr rfl
    intro x hx
    simp only [mem_filter, mem_range] at hx
    unfold rootCount
    congr 1
    ext y
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨⟨hy, -⟩, h⟩; exact ⟨hy, h⟩
    · rintro ⟨hy, h⟩; exact ⟨⟨hy, by rw [h]; exact hx.2⟩, h⟩
  · intro y hy
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hy ⊢
    exact ⟨Nat.mod_lt _ (by omega), hy.2⟩

/-- **(I-B)** (decidable form): `S3B = 2·#{x < p : pre(x) ∧ x ≠ 0 ∧ x square} + [ofWord π = 0]`. -/
theorem S3B_eq {n' n p : ℕ} (π : List Bool) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ≤ 2 ^ n') :
    S3B n' n p π = 2 * ((range p).filter fun x => x / 2 ^ (n - π.length) = ofWord π ∧
        x ≠ 0 ∧ ∃ y < p, y * y % p = x).card + (if ofWord π = 0 then 1 else 0) := by
  rw [S3B_eq_sum π hpn]
  have hc : ∀ x ∈ (range p).filter (fun x => x / 2 ^ (n - π.length) = ofWord π),
      rootCount p x = 2 * (if x ≠ 0 ∧ ∃ y < p, y * y % p = x then 1 else 0) +
        (if x = 0 then 1 else 0) := by
    intro x hx
    simp only [mem_filter, mem_range] at hx
    exact rootCount_eq hp hp2 hx.1
  rw [sum_congr rfl hc, sum_add_distrib, ← mul_sum, sum_boole, sum_ite_eq']
  simp only [Nat.cast_id, filter_filter, mem_filter, mem_range, Nat.zero_div]
  congr 2
  · simp only [hp.pos, true_and, eq_comm]

open Classical in
/-- **(I-B)** in the form of the plan, with `IsSquare` in `ZMod p`. -/
theorem S3B_eq_isSquare {n' n p : ℕ} (π : List Bool) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ≤ 2 ^ n') :
    S3B n' n p π = 2 * ((range p).filter fun x => x / 2 ^ (n - π.length) = ofWord π ∧
        x ≠ 0 ∧ IsSquare (x : ZMod p)).card + (if ofWord π = 0 then 1 else 0) := by
  rw [S3B_eq π hp hp2 hpn]
  congr 3
  ext x
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hx, h1, h2, h3⟩; exact ⟨hx, h1, h2, (isSquare_zmod_iff hp.pos hx).2 h3⟩
  · rintro ⟨hx, h1, h2, h3⟩; exact ⟨hx, h1, h2, (isSquare_zmod_iff hp.pos hx).1 h3⟩

/-! ## The non-residue count -/

/-- `#{x < p : pre(x) ∧ x is a non-square mod p}`. -/
def NR (n p : ℕ) (π : List Bool) : ℕ :=
  ((range p).filter fun x => x / 2 ^ (n - π.length) = ofWord π ∧ ∀ y < p, y * y % p ≠ x).card

/-- `#{x < p : pre(x)}` in closed form. -/
def rangeCount (n p : ℕ) (π : List Bool) : ℕ :=
  min ((ofWord π + 1) * 2 ^ (n - π.length)) p - min (ofWord π * 2 ^ (n - π.length)) p

/-- `[x = 0 has prefix π]`. -/
def z0 (π : List Bool) : ℕ := if ofWord π = 0 then 1 else 0

/-- The non-residue count computed from the triple count `k = S3B`. -/
def nrOf (n p : ℕ) (π : List Bool) (k : ℕ) : ℕ := rangeCount n p π - z0 π - (k - z0 π) / 2

theorem card_div_eq (p s c : ℕ) :
    ((range p).filter fun x => x / 2 ^ s = c).card = min ((c + 1) * 2 ^ s) p - min (c * 2 ^ s) p := by
  have hpos : 0 < 2 ^ s := by positivity
  have : ((range p).filter fun x => x / 2 ^ s = c) = Ico (min (c * 2 ^ s) p) (min ((c + 1) * 2 ^ s) p) := by
    ext x
    simp only [mem_filter, mem_range, mem_Ico]
    have e : x / 2 ^ s = c ↔ c * 2 ^ s ≤ x ∧ x < (c + 1) * 2 ^ s := by
      rw [← Nat.le_div_iff_mul_le hpos, ← Nat.div_lt_iff_lt_mul hpos]; omega
    rw [e]
    generalize c * 2 ^ s = A
    generalize (c + 1) * 2 ^ s = B
    omega
  rw [this, Nat.card_Ico]

theorem card_pre (n p : ℕ) (π : List Bool) :
    ((range p).filter fun x => x / 2 ^ (n - π.length) = ofWord π).card = rangeCount n p π :=
  card_div_eq p _ _

/-- `#{x < p : pre(x) ∧ x ≠ 0 ∧ x square}`. -/
def Qc (n p : ℕ) (π : List Bool) : ℕ :=
  ((range p).filter fun x => x / 2 ^ (n - π.length) = ofWord π ∧
    x ≠ 0 ∧ ∃ y < p, y * y % p = x).card

/-- **(I-B)** with the named counts: `S3B = 2·Qc + z0`. -/
theorem S3B_eq_Qc {n' n p : ℕ} (π : List Bool) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ≤ 2 ^ n') :
    S3B n' n p π = 2 * Qc n p π + z0 π :=
  S3B_eq π hp hp2 hpn

theorem z0_eq_card {n p : ℕ} (π : List Bool) (hp : 0 < p) :
    z0 π = ((range p).filter fun x => x / 2 ^ (n - π.length) = ofWord π ∧ x = 0).card := by
  unfold z0
  split_ifs with hc
  · rw [eq_comm, card_eq_one]
    refine ⟨0, ?_⟩
    ext x
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨-, -, h⟩; exact h
    · rintro rfl; exact ⟨hp, by rw [Nat.zero_div, hc], rfl⟩
  · symm
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro x - ⟨h, rfl⟩
    rw [Nat.zero_div] at h
    exact hc h.symm

/-- The prefix-`π` residues split into non-squares, nonzero squares and `0`. -/
theorem pre_split (n : ℕ) {p : ℕ} (π : List Bool) (hp : 0 < p) :
    rangeCount n p π = NR n p π + Qc n p π + z0 π := by
  rw [z0_eq_card (n := n) π hp, ← card_pre, NR, Qc, card_filter, card_filter, card_filter,
    card_filter, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  by_cases h2 : x = 0
  · subst h2
    have h3 : ∃ y < p, y * y % p = 0 := ⟨0, hp, by simp⟩
    by_cases h1 : 0 / 2 ^ (n - π.length) = ofWord π <;> simp [h1, h3]
  · by_cases h1 : x / 2 ^ (n - π.length) = ofWord π <;>
      by_cases h3 : ∃ y < p, y * y % p = x <;> simp_all

/-- **The NR formula**: `NR = rangeCount - z0 - (S3B - z0)/2` for an odd prime `p ≤ 2^n'`. -/
theorem NR_eq {n' n p : ℕ} (π : List Bool) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ≤ 2 ^ n') :
    NR n p π = nrOf n p π (S3B n' n p π) := by
  rw [nrOf, S3B_eq_Qc π hp hp2 hpn, pre_split n π hp.pos]
  omega

theorem NR_pos_iff (n p : ℕ) (π : List Bool) :
    0 < NR n p π ↔ ∃ x ∈ nrSet p, x / 2 ^ (n - π.length) = ofWord π := by
  rw [NR, card_pos, filter_nonempty_iff]
  simp only [nrSet, mem_filter, mem_range]
  constructor
  · rintro ⟨x, hx, h1, h2⟩; exact ⟨x, ⟨hx, h2⟩, h1⟩
  · rintro ⟨x, ⟨hx, h2⟩, h1⟩; exact ⟨x, hx, h1, h2⟩

/-- **Positivity lemma** for the (B) search step: the non-residue count computed from the triple
count is positive iff some non-residue has prefix `π`. -/
theorem nrOf_S3B_pos_iff {n' n p : ℕ} (π : List Bool) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ≤ 2 ^ n') :
    0 < nrOf n p π (S3B n' n p π) ↔ ∃ x ∈ nrSet p, x / 2 ^ (n - π.length) = ofWord π := by
  rw [← NR_eq π hp hp2 hpn, NR_pos_iff]

/-! ## Sanity checks (§4 values) -/

example : S3A 3 3 7 2 [] = 2 := by decide +kernel
example : S3A 3 3 7 2 [false] = 1 := by decide +kernel
example : S3A 3 3 7 2 [true] = 1 := by decide +kernel
example : S3A 3 3 7 3 [] = 0 := by decide +kernel
example : S3B 3 3 7 [] = 7 := by decide +kernel
example : S3B 3 3 7 [false] = 5 := by decide +kernel
example : NR 3 7 [] = 3 := by decide +kernel
example : NR 3 7 [false] = 1 := by decide +kernel
example : nrOf 3 7 [] 7 = 3 := by decide +kernel
example : nrOf 3 7 [false] 5 = 1 := by decide +kernel
example : rangeCount 3 7 [] = 7 ∧ rangeCount 3 7 [false] = 4 ∧ z0 [] = 1 := by decide +kernel
example : minRoot 7 2 = 3 := by rw [minRoot, Nat.find_eq_iff]; decide
example : minRoot 7 3 = 7 := by rw [minRoot, Nat.find_eq_iff]; decide
example : minRoot 13 10 = 6 := by rw [minRoot, Nat.find_eq_iff]; decide
example : minRoot 1 5 = 0 ∧ minRoot 0 5 = 0 := ⟨minRoot_one 5, minRoot_zero 5⟩
example : lqnr 7 = 3 := by rw [lqnr, Nat.find_eq_iff]; decide
example : lqnr 11 = 2 := by rw [lqnr, Nat.find_eq_iff]; decide
example : lqnr 13 = 2 := by rw [lqnr, Nat.find_eq_iff]; decide
example : lqnr 17 = 3 := by rw [lqnr, Nat.find_eq_iff]; decide
example : lqnr 41 = 3 := by rw [lqnr, Nat.find_eq_iff]; decide

end EthFollowup.ModP
