/-
# Roots of polynomials modulo `m`: the pure definitions and the Horner identity (roots-plan.md, H1)

* `polyEvalMod m a x` (Horner, little-endian coefficients `a = [a_0, …, a_d]`), `rootSetP m a`,
  `minRootP m a` (least root in `[0, m)`, or `m`), `nextRootP m a lo` (least root `≥ lo`, or `m`);
* canonical Horner values `hH m a x i`, quotients `hK m a x i`.

Pure Mathlib; compiles in both toolchains. Standard axioms only.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.GetD

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset

/-! ## Definitions (FROZEN, roots-plan.md §2) -/

/-- Σ_{i<|a|} a_i x^i mod m by Horner; a = [a_0, …, a_d] little-endian. -/
def polyEvalMod (m : ℕ) (a : List ℕ) (x : ℕ) : ℕ := a.foldr (fun c h => (h * x + c) % m) 0
def rootSetP (m : ℕ) (a : List ℕ) : Finset ℕ := (Finset.range m).filter fun x => polyEvalMod m a x = 0
/-- The least root of a modulo m in [0, m), or m if there is none. -/
def minRootP (m : ℕ) (a : List ℕ) : ℕ :=
  Nat.find (⟨m, Or.inl rfl⟩ : ∃ x, x = m ∨ (x < m ∧ polyEvalMod m a x = 0))
/-- The least root ≥ lo, or m. -/
def nextRootP (m : ℕ) (a : List ℕ) (lo : ℕ) : ℕ :=
  Nat.find (⟨m, Or.inl rfl⟩ : ∃ x, x = m ∨ (lo ≤ x ∧ x < m ∧ polyEvalMod m a x = 0))

/-! ## Canonical Horner values -/

/-- The Horner value after the top `i + 1` coefficients `a_d, …, a_{d-i}` (`d + 1 = |a|`). -/
def hH (m : ℕ) (a : List ℕ) (x i : ℕ) : ℕ := (a.reverse.take (i + 1)).foldl (fun h c => (h * x + c) % m) 0

/-- The quotient of Horner step `i` (degree `d`): `(hH i · x + a_{d-1-i}) / m`. -/
def hK (m d : ℕ) (a : List ℕ) (x i : ℕ) : ℕ := (hH m a x i * x + a.getD (d - 1 - i) 0) / m


/-! ## Horner evaluation -/

theorem polyEvalMod_nil (m x : ℕ) : polyEvalMod m [] x = 0 := rfl

theorem polyEvalMod_cons (m c : ℕ) (t : List ℕ) (x : ℕ) :
    polyEvalMod m (c :: t) x = (polyEvalMod m t x * x + c) % m := rfl

theorem polyEvalMod_lt {m : ℕ} (hm : 0 < m) (a : List ℕ) (x : ℕ) : polyEvalMod m a x < m := by
  cases a with
  | nil => exact hm
  | cons c t => exact Nat.mod_lt _ hm

theorem polyEvalMod_one (a : List ℕ) (x : ℕ) : polyEvalMod 1 a x = 0 := by
  have := polyEvalMod_lt Nat.one_pos a x; omega

/-- Reducing the coefficients does not change the value. -/
theorem polyEvalMod_mod (m : ℕ) (a : List ℕ) (x : ℕ) :
    polyEvalMod m (a.map (· % m)) x = polyEvalMod m a x := by
  induction a with
  | nil => rfl
  | cons c t ih =>
    simp only [List.map_cons, polyEvalMod_cons, ih]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-- The value is the sum `Σ a_i x^i` reduced modulo `m`. -/
theorem polyEvalMod_eq_sum {m : ℕ} (_hm : 0 < m) (a : List ℕ) (x : ℕ) :
    polyEvalMod m a x = (∑ i ∈ range a.length, a.getD i 0 * x ^ i) % m := by
  induction a with
  | nil => simp [polyEvalMod_nil]
  | cons c t ih =>
    rw [polyEvalMod_cons, ih, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    have e : ∑ i ∈ range t.length, t.getD i 0 * (x ^ i * x) = (∑ i ∈ range t.length, t.getD i 0 * x ^ i) * x := by
      rw [sum_mul]; exact sum_congr rfl fun i _ => by ring
    rw [e, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- **`ZMod` form**: a root modulo `m` is a zero of `Σ a_i x^i` in `ZMod m`. -/
theorem polyEvalMod_eq_zero_iff_zmod {m : ℕ} (hm : 0 < m) (a : List ℕ) (x : ℕ) :
    polyEvalMod m a x = 0 ↔ (∑ i ∈ range a.length, (a.getD i 0 : ZMod m) * (x : ZMod m) ^ i) = 0 := by
  rw [polyEvalMod_eq_sum hm, ← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
  push_cast; rfl

/-- The polynomial `Σ_{i < |a|} a_i X^i` over `ZMod m`. -/
noncomputable def polyOf (m : ℕ) (a : List ℕ) : Polynomial (ZMod m) :=
  ∑ i ∈ range a.length, Polynomial.C (a.getD i 0 : ZMod m) * Polynomial.X ^ i

theorem eval_polyOf (m : ℕ) (a : List ℕ) (x : ZMod m) :
    (polyOf m a).eval x = ∑ i ∈ range a.length, (a.getD i 0 : ZMod m) * x ^ i := by
  simp [polyOf, Polynomial.eval_finset_sum]

/-- **Polynomial form**: `x` is a root modulo `m` iff `(x : ZMod m)` is a root of `Σ a_i X^i`. -/
theorem polyEvalMod_eq_zero_iff_eval {m : ℕ} (hm : 0 < m) (a : List ℕ) (x : ℕ) :
    polyEvalMod m a x = 0 ↔
      Polynomial.eval (x : ZMod m)
        (∑ i ∈ range a.length, Polynomial.C (a.getD i 0 : ZMod m) * Polynomial.X ^ i) = 0 := by
  rw [polyEvalMod_eq_zero_iff_zmod hm]
  exact (eval_polyOf m a x).symm ▸ Iff.rfl

/-! ## Canonical Horner values -/

theorem hH_zero {m d : ℕ} {a : List ℕ} (hlen : a.length = d + 1) (x : ℕ) :
    hH m a x 0 = a.getD d 0 % m := by
  have h0 : 0 < a.reverse.length := by simp [hlen]
  rw [hH, List.take_succ, List.take_zero, List.getElem?_eq_getElem h0]
  simp only [Option.toList_some, List.nil_append, List.foldl_cons, List.foldl_nil, zero_mul, zero_add]
  rw [List.getElem_reverse, List.getD_eq_getElem _ _ (by omega)]
  congr 2; simp [hlen]

theorem hH_succ {m d : ℕ} {a : List ℕ} (hlen : a.length = d + 1) (x : ℕ) {i : ℕ} (hi : i < d) :
    hH m a x (i + 1) = (hH m a x i * x + a.getD (d - 1 - i) 0) % m := by
  have h0 : i + 1 < a.reverse.length := by simp [hlen]; omega
  rw [hH, List.take_succ, List.getElem?_eq_getElem h0, List.foldl_append]
  simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
  rw [← hH, List.getElem_reverse, List.getD_eq_getElem _ _ (by omega)]
  congr 3; simp [hlen]; omega

theorem hH_lt {m d : ℕ} (hm : 0 < m) {a : List ℕ} (hlen : a.length = d + 1) (x i : ℕ) (hi : i ≤ d) :
    hH m a x i < m := by
  rcases i with _ | i
  · rw [hH_zero hlen]; exact Nat.mod_lt _ hm
  · rw [hH_succ hlen x (by omega)]; exact Nat.mod_lt _ hm

/-- The full Horner value is `polyEvalMod`. -/
theorem polyEvalMod_eq_hH {m d : ℕ} {a : List ℕ} (hlen : a.length = d + 1) (x : ℕ) :
    polyEvalMod m a x = hH m a x d := by
  rw [hH, List.take_of_length_le (by simp [hlen]), List.foldl_reverse]; rfl

theorem hK_eq (m d : ℕ) (a : List ℕ) (x i : ℕ) :
    hK m d a x i = (hH m a x i * x + a.getD (d - 1 - i) 0) / m := rfl

/-- `N = r + q·m` with `r < m` determines `r` and `q`. -/
theorem eq_add_mul_iff {m N r q : ℕ} (hm : 0 < m) : (N = r + q * m ∧ r < m) ↔ (r = N % m ∧ q = N / m) := by
  constructor
  · rintro ⟨rfl, h2⟩
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt h2]
    simp
  · rintro ⟨rfl, rfl⟩
    exact ⟨(Nat.mod_add_div' N m).symm, Nat.mod_lt _ hm⟩

/-- A bound on the Horner quotients: `hK < m` when the coefficients and `x` are `< m`. -/
theorem hK_lt {m d : ℕ} (hm : 0 < m) {a : List ℕ} (hlen : a.length = d + 1) (ha : ∀ c ∈ a, c < m)
    {x : ℕ} (hx : x < m) {i : ℕ} (hi : i < d) : hK m d a x i < m := by
  rw [hK_eq, Nat.div_lt_iff_lt_mul hm]
  have h1 := hH_lt hm hlen x i (by omega)
  have h2 : a.getD (d - 1 - i) 0 < m := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact ha _ (List.getElem_mem _)
  have h3 : hH m a x i * x ≤ (m - 1) * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h4 : (m - 1) * (m - 1) + m ≤ m * m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; nlinarith
  omega

/-- **The Horner chain**: with `h_0 := a_d` and `h_d := 0`, the chain equations
`h_i·x + a_{d-1-i} = h_{i+1} + k_i·m` with `h_i < m` (`1 ≤ i < d`) hold iff `x` is a root and the
`h_i, k_i` are the canonical Horner values and quotients. -/
theorem horner_chain_iff {m d : ℕ} {a : List ℕ} {x : ℕ} (h k : ℕ → ℕ) (hm : 0 < m) (hd : 1 ≤ d)
    (hlen : a.length = d + 1) (had : a.getD d 0 < m) :
    ((∀ i < d, (if i = 0 then a.getD d 0 else h i) * x + a.getD (d - 1 - i) 0 =
        (if i + 1 < d then h (i + 1) else 0) + k i * m) ∧ (∀ i, 1 ≤ i → i < d → h i < m)) ↔
      ((polyEvalMod m a x = 0 ∧ ∀ i, 1 ≤ i → i < d → h i = hH m a x i) ∧
        ∀ i < d, k i = hK m d a x i) := by
  have hv0 : a.getD d 0 = hH m a x 0 := by rw [hH_zero hlen, Nat.mod_eq_of_lt had]
  rw [polyEvalMod_eq_hH hlen]
  -- one step, given the value at `i`
  have step : ∀ i < d, ∀ v, v = hH m a x i →
      (((v * x + a.getD (d - 1 - i) 0 = (if i + 1 < d then h (i + 1) else 0) + k i * m) ∧
        (i + 1 < d → h (i + 1) < m)) ↔
      ((if i + 1 < d then h (i + 1) = hH m a x (i + 1) else hH m a x (i + 1) = 0) ∧
        k i = hK m d a x i)) := by
    intro i hi v hv
    subst hv
    rw [hH_succ hlen x hi, hK_eq]
    split_ifs with hi1
    · have := eq_add_mul_iff (N := hH m a x i * x + a.getD (d - 1 - i) 0) (r := h (i + 1)) (q := k i) hm
      constructor
      · rintro ⟨e, b⟩; exact this.1 ⟨e, b hi1⟩
      · intro e; exact ⟨(this.2 e).1, fun _ => (this.2 e).2⟩
    · have := eq_add_mul_iff (N := hH m a x i * x + a.getD (d - 1 - i) 0) (r := 0) (q := k i) hm
      constructor
      · rintro ⟨e, -⟩; obtain ⟨e1, e2⟩ := this.1 ⟨e, hm⟩; exact ⟨e1.symm, e2⟩
      · rintro ⟨e1, e2⟩; exact ⟨(this.2 ⟨e1.symm, e2⟩).1, fun h => absurd h hi1⟩
  constructor
  · rintro ⟨hc, hb⟩
    -- the values agree with the canonical ones, by induction
    have hval : ∀ i < d, (if i = 0 then a.getD d 0 else h i) = hH m a x i := by
      intro i
      induction i with
      | zero => intro _; simpa using hv0
      | succ i ih =>
        intro hi
        have := (step i (by omega) _ (ih (by omega))).1 ⟨hc i (by omega), fun h1 => hb _ (by omega) h1⟩
        rw [if_pos hi] at this
        simpa using this.1
    refine ⟨⟨?_, fun i hi1 hi => ?_⟩, fun i hi => ?_⟩
    · have := (step (d - 1) (by omega) _ (hval _ (by omega))).1
        ⟨hc _ (by omega), fun h1 => hb _ (by omega) h1⟩
      rw [if_neg (by omega), show d - 1 + 1 = d by omega] at this
      exact this.1
    · have := hval i hi; rwa [if_neg (by omega)] at this
    · exact ((step i hi _ (hval i hi)).1 ⟨hc i hi, fun h1 => hb _ (by omega) h1⟩).2
  · rintro ⟨⟨hz, hh⟩, hk⟩
    have hval : ∀ i < d, (if i = 0 then a.getD d 0 else h i) = hH m a x i := by
      intro i hi
      split_ifs with h0
      · subst h0; exact hv0
      · exact hh i (by omega) hi
    refine ⟨fun i hi => ((step i hi _ (hval i hi)).2 ⟨?_, hk i hi⟩).1, fun i hi1 hi => ?_⟩
    · split_ifs with hi1
      · exact hh _ (by omega) hi1
      · rw [show i + 1 = d by omega]; exact hz
    · rw [hh i hi1 hi]; exact hH_lt hm hlen x i (by omega)

/-! ## Root sets -/

theorem mem_rootSetP {m : ℕ} {a : List ℕ} {x : ℕ} : x ∈ rootSetP m a ↔ x < m ∧ polyEvalMod m a x = 0 := by
  simp [rootSetP]

theorem rootSetP_mod (m : ℕ) (a : List ℕ) : rootSetP m (a.map (· % m)) = rootSetP m a := by
  simp only [rootSetP, polyEvalMod_mod]

theorem card_rootSetP_le_self (m : ℕ) (a : List ℕ) : (rootSetP m a).card ≤ m :=
  (card_filter_le (range m) _).trans (card_range m).le

theorem rootSetP_one (a : List ℕ) : rootSetP 1 a = {0} := by
  ext x; simp [rootSetP, polyEvalMod_one]

theorem rootSetP_zero (a : List ℕ) : rootSetP 0 a = ∅ := by simp [rootSetP]

/-- **At most `deg` roots modulo a prime** (some coefficient nonzero mod `p`). -/
theorem card_rootSetP_le {p : ℕ} (hp : p.Prime) {a : List ℕ} (h : ∃ c ∈ a, ¬ p ∣ c) :
    (rootSetP p a).card ≤ a.length - 1 := by
  have := Fact.mk hp
  set f := polyOf p a
  have hcoeff : ∀ j, f.coeff j = if j < a.length then (a.getD j 0 : ZMod p) else 0 := by
    intro j
    simp only [f, polyOf, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [sum_ite_eq]; simp
  have hf0 : f ≠ 0 := by
    obtain ⟨c, hc, hpc⟩ := h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    intro hf
    have := hcoeff j
    rw [hf, Polynomial.coeff_zero, if_pos hj, List.getD_eq_getElem _ _ hj, eq_comm,
      ZMod.natCast_eq_zero_iff] at this
    exact hpc this
  have hdeg : f.natDegree ≤ a.length - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [hcoeff, if_neg (by
      have : a.length - 1 < j := by exact_mod_cast hj
      omega)]
  have hinj : (rootSetP p a).card ≤ f.roots.toFinset.card := by
    apply card_le_card_of_injOn (fun x : ℕ => (x : ZMod p))
    · intro x hx
      rw [mem_coe, mem_rootSetP] at hx
      rw [mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hf0, Polynomial.IsRoot.def, eval_polyOf]
      exact (polyEvalMod_eq_zero_iff_zmod hp.pos a x).1 hx.2
    · intro x hx y hy hxy
      rw [mem_coe, mem_rootSetP] at hx hy
      have := congrArg ZMod.val hxy
      simp only at this
      rwa [ZMod.val_cast_of_lt hx.1, ZMod.val_cast_of_lt hy.1] at this
  calc (rootSetP p a).card ≤ f.roots.toFinset.card := hinj
    _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ ≤ a.length - 1 := hdeg

/-! ## The least root `≥ lo` -/

/-- The roots `≥ lo`. -/
def nextSetP (m : ℕ) (a : List ℕ) (lo : ℕ) : Finset ℕ := (rootSetP m a).filter fun x => lo ≤ x

theorem mem_nextSetP {m : ℕ} {a : List ℕ} {lo x : ℕ} :
    x ∈ nextSetP m a lo ↔ lo ≤ x ∧ x < m ∧ polyEvalMod m a x = 0 := by
  simp only [nextSetP, mem_filter, mem_rootSetP]; tauto

theorem nextSetP_zero (m : ℕ) (a : List ℕ) : nextSetP m a 0 = rootSetP m a := by
  simp [nextSetP]

theorem nextRootP_le (m : ℕ) (a : List ℕ) (lo : ℕ) : nextRootP m a lo ≤ m := Nat.find_min' _ (Or.inl rfl)

theorem nextRootP_spec' (m : ℕ) (a : List ℕ) (lo : ℕ) :
    nextRootP m a lo = m ∨ (lo ≤ nextRootP m a lo ∧ nextRootP m a lo < m ∧ polyEvalMod m a (nextRootP m a lo) = 0) :=
  Nat.find_spec (⟨m, Or.inl rfl⟩ : ∃ x, x = m ∨ (lo ≤ x ∧ x < m ∧ polyEvalMod m a x = 0))

theorem not_root_of_lt_nextRootP {m : ℕ} {a : List ℕ} {lo x : ℕ} (hlo : lo ≤ x) (hx : x < nextRootP m a lo) :
    polyEvalMod m a x ≠ 0 := by
  have h := Nat.find_min (⟨m, Or.inl rfl⟩ : ∃ x, x = m ∨ (lo ≤ x ∧ x < m ∧ polyEvalMod m a x = 0)) hx
  have hle := nextRootP_le m a lo
  intro hr
  exact h (Or.inr ⟨hlo, lt_of_lt_of_le hx hle, hr⟩)

/-- **Specification of `nextRootP`.** -/
theorem nextRootP_spec (m : ℕ) (a : List ℕ) (lo : ℕ) :
    nextRootP m a lo ≤ m ∧
      (nextRootP m a lo < m → lo ≤ nextRootP m a lo ∧ polyEvalMod m a (nextRootP m a lo) = 0) ∧
      (∀ x, lo ≤ x → x < nextRootP m a lo → polyEvalMod m a x ≠ 0) ∧
      (nextRootP m a lo = m ↔ ∀ x, lo ≤ x → x < m → polyEvalMod m a x ≠ 0) := by
  refine ⟨nextRootP_le m a lo, fun h => ?_, fun x hlo hx => not_root_of_lt_nextRootP hlo hx,
    ⟨fun h x hlo hx => not_root_of_lt_nextRootP hlo (by omega), fun h => ?_⟩⟩
  · rcases nextRootP_spec' m a lo with h' | h'
    · omega
    · exact ⟨h'.1, h'.2.2⟩
  · rcases nextRootP_spec' m a lo with h' | h'
    · exact h'
    · exact absurd h'.2.2 (h _ h'.1 h'.2.1)

theorem nextRootP_mem {m : ℕ} {a : List ℕ} {lo : ℕ} (h : (nextSetP m a lo).Nonempty) :
    nextRootP m a lo ∈ nextSetP m a lo := by
  obtain ⟨y, hy⟩ := h
  rw [mem_nextSetP] at hy ⊢
  rcases nextRootP_spec' m a lo with h' | h'
  · have := Nat.find_min' (⟨m, Or.inl rfl⟩ : ∃ x, x = m ∨ (lo ≤ x ∧ x < m ∧ polyEvalMod m a x = 0))
      (Or.inr hy)
    unfold nextRootP at h'; omega
  · exact h'

theorem nextRootP_eq_min' {m : ℕ} {a : List ℕ} {lo : ℕ} (h : (nextSetP m a lo).Nonempty) :
    nextRootP m a lo = (nextSetP m a lo).min' h := by
  apply le_antisymm
  · have hm := (nextSetP m a lo).min'_mem h
    rw [mem_nextSetP] at hm
    exact Nat.find_min' _ (Or.inr hm)
  · exact (nextSetP m a lo).min'_le _ (nextRootP_mem h)

theorem nextRootP_eq_of_empty {m : ℕ} {a : List ℕ} {lo : ℕ} (h : nextSetP m a lo = ∅) :
    nextRootP m a lo = m := by
  rcases nextRootP_spec' m a lo with h' | h'
  · exact h'
  · have : nextRootP m a lo ∈ nextSetP m a lo := mem_nextSetP.2 h'
    rw [h] at this; simp at this

/-- `nextRootP` as `min'`-or-`m`. -/
theorem nextRootP_eq_minOr (m : ℕ) (a : List ℕ) (lo : ℕ) :
    nextRootP m a lo = if h : (nextSetP m a lo).Nonempty then (nextSetP m a lo).min' h else m := by
  split_ifs with h
  · exact nextRootP_eq_min' h
  · exact nextRootP_eq_of_empty (Finset.not_nonempty_iff_eq_empty.1 h)

theorem nextSetP_mod (m : ℕ) (a : List ℕ) (lo : ℕ) : nextSetP m (a.map (· % m)) lo = nextSetP m a lo := by
  simp only [nextSetP, rootSetP_mod]

theorem nextRootP_mod (m : ℕ) (a : List ℕ) (lo : ℕ) : nextRootP m (a.map (· % m)) lo = nextRootP m a lo := by
  rw [nextRootP_eq_minOr, nextRootP_eq_minOr m a lo]; simp only [nextSetP_mod]

theorem nextRootP_zero (a : List ℕ) (lo : ℕ) : nextRootP 0 a lo = 0 :=
  Nat.find_eq_zero _ |>.2 (Or.inl rfl)

theorem nextRootP_of_le {m : ℕ} {a : List ℕ} {lo : ℕ} (h : m ≤ lo) : nextRootP m a lo = m :=
  (nextRootP_spec m a lo).2.2.2.2 fun _ hx hxm => absurd (lt_of_le_of_lt (h.trans hx) hxm) (lt_irrefl _)

/-! ## The least root -/

/-- `minRootP` is `nextRootP` from `0`. -/
theorem minRootP_eq_next (m : ℕ) (a : List ℕ) : minRootP m a = nextRootP m a 0 := by
  apply le_antisymm
  · rcases nextRootP_spec' m a 0 with h | h
    · exact Nat.find_min' _ (Or.inl h)
    · exact Nat.find_min' _ (Or.inr h.2)
  · rcases Nat.find_spec (⟨m, Or.inl rfl⟩ : ∃ x, x = m ∨ (x < m ∧ polyEvalMod m a x = 0)) with h | h
    · exact Nat.find_min' _ (Or.inl h)
    · exact Nat.find_min' _ (Or.inr ⟨Nat.zero_le _, h⟩)

/-- **Specification of `minRootP`.** -/
theorem minRootP_spec (m : ℕ) (a : List ℕ) :
    minRootP m a ≤ m ∧ (minRootP m a < m → polyEvalMod m a (minRootP m a) = 0) ∧
      (∀ x < minRootP m a, polyEvalMod m a x ≠ 0) ∧
      (minRootP m a = m ↔ ∀ x < m, polyEvalMod m a x ≠ 0) := by
  rw [minRootP_eq_next]
  obtain ⟨h1, h2, h3, h4⟩ := nextRootP_spec m a 0
  exact ⟨h1, fun h => (h2 h).2, fun x hx => h3 x (Nat.zero_le _) hx,
    h4.trans ⟨fun h x hx => h x (Nat.zero_le _) hx, fun h x _ hx => h x hx⟩⟩

theorem minRootP_le (m : ℕ) (a : List ℕ) : minRootP m a ≤ m := (minRootP_spec m a).1

theorem minRootP_eq_min' {m : ℕ} {a : List ℕ} (h : (rootSetP m a).Nonempty) :
    minRootP m a = (rootSetP m a).min' h := by
  rw [minRootP_eq_next, nextRootP_eq_min' (by rwa [nextSetP_zero])]
  simp only [nextSetP_zero]

theorem minRootP_mem {m : ℕ} {a : List ℕ} (h : (rootSetP m a).Nonempty) : minRootP m a ∈ rootSetP m a := by
  rw [minRootP_eq_min' h]; exact min'_mem _ _

theorem minRootP_eq_of_empty {m : ℕ} {a : List ℕ} (h : rootSetP m a = ∅) : minRootP m a = m := by
  rw [minRootP_eq_next, nextRootP_eq_of_empty (by rwa [nextSetP_zero])]

theorem minRootP_eq_minOr (m : ℕ) (a : List ℕ) :
    minRootP m a = if h : (rootSetP m a).Nonempty then (rootSetP m a).min' h else m := by
  split_ifs with h
  · exact minRootP_eq_min' h
  · exact minRootP_eq_of_empty (Finset.not_nonempty_iff_eq_empty.1 h)

theorem minRootP_mod (m : ℕ) (a : List ℕ) : minRootP m (a.map (· % m)) = minRootP m a := by
  rw [minRootP_eq_next, minRootP_eq_next, nextRootP_mod]

theorem minRootP_zero (a : List ℕ) : minRootP 0 a = 0 := Nat.find_eq_zero _ |>.2 (Or.inl rfl)

theorem minRootP_one (a : List ℕ) : minRootP 1 a = 0 :=
  Nat.find_eq_zero _ |>.2 (Or.inr ⟨one_pos, polyEvalMod_one a 0⟩)

/-! ## Sanity checks (roots-plan.md §4 values) -/

example : minRootP 7 [1, 1, 1] = 2 := by rw [minRootP, Nat.find_eq_iff]; decide
example : minRootP 7 [1, 0, 1] = 7 := by rw [minRootP, Nat.find_eq_iff]; decide
example : minRootP 7 [2, 3] = 4 := by rw [minRootP, Nat.find_eq_iff]; decide
example : minRootP 7 [1, 1, 0, 1] = 7 := by rw [minRootP, Nat.find_eq_iff]; decide
example : minRootP 7 [0, 6, 0, 1] = 0 := by rw [minRootP, Nat.find_eq_iff]; decide
example : minRootP 8 [7, 0, 1] = 1 := by rw [minRootP, Nat.find_eq_iff]; decide
example : minRootP 9 [0, 0, 1] = 0 := by rw [minRootP, Nat.find_eq_iff]; decide
example : minRootP 1 [5] = 0 ∧ minRootP 0 [5] = 0 := ⟨minRootP_one _, minRootP_zero _⟩
example : nextRootP 7 [1, 1, 1] 3 = 4 := by rw [nextRootP, Nat.find_eq_iff]; decide
example : nextRootP 7 [1, 1, 1] 5 = 7 := by rw [nextRootP, Nat.find_eq_iff]; decide
example : (rootSetP 8 [7, 0, 1]).card = 4 := by decide

end EthFollowup.ModP
