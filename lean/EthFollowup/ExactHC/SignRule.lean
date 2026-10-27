/-
# Chord / parity combinatorics of the sign rule (§4 of `exact-hc-theorem.md`)

Pure combinatorics; no Grassmann algebra. Module M3 of `research/lean-blueprint.md`.

## Data and definitions (reusable by later modules)

* `sgn : ZMod 2 → ℤ`, `sgn x = (-1)^x` (`sgn 0 = 1`, `sgn 1 = -1`); it turns sums into products
  (`sgn_add`, `sgn_sum`) and `sgn (n : ZMod 2) = (-1)^n` for `n : ℕ` (`sgn_natCast`).
* `Chords g m`: `m` crossing edges `k : Fin m` (listed in the crossing order `<` of `Fin m`),
  each with blob indices `C.a k < C.b k` in `Fin g` (low end blob, high end blob).
  Parities are an arbitrary `π : Fin m → ZMod 2` (later: `π k = π(ℓ_k)`).
* `C.ends k = {a_k, b_k}` (the chord), `C.delta x = δ(x)` (crossing edges at blob `x`),
  `C.E x y = E(x,y)` (edges with chord `(x,y)`).
* `C.cross k l = c_{kl} = #{(x,y) ∈ {a_k,b_k} × {a_l,b_l} : y < x}` (`cross_eq`: four-term form).
* `C.epsExp π = Σ_{k<l} π_k π_l c_{kl} ∈ ZMod 2`, `C.eps π = sgn (C.epsExp π) = ε`.
* `C.Meet k l` (chords meet; `meet_iff_not_disjoint`), `C.shared k l = s(k,l)`, the minimum of
  `{a_k,b_k} ∩ {a_l,b_l}` when the chords meet (`shared_mem_ends_left/right`, `shared_le`).
* `C.sigma π x = σ_x`, `C.P π x y = P_{xy} = Σ_{k ∈ E(x,y)} π_k ∈ ZMod 2`.
* `C.Interleave k l = I(k,l)`.
* `C.interleaveExp π = Σ_{a<c<b<d} P_{ab} P_{cd} ∈ ZMod 2`.
* `Q x = Q_x = {(c,d) : x < c < d}`, `C.chi π x y = χ_x(y)` for `y : Fin g × Fin g → ZMod 2`
  (only the values on `Q x` matter).

## Results

* Lemma 4.3 `cross_mod_two_of_not_meet`: disjoint chords ⇒ `(c_{kl} : ZMod 2) = [I(k,l)]`.
* Proposition 4.4 `eps_eq_prod_sigma_mul`: `ε = (Π_x σ_x) · sgn (Σ_{a<c<b<d} P_{ab} P_{cd})`.
* Lemma 4.5 `prod_chi_eq`: correct copies ⇒ `Π_x χ_x(y^{(x)}) = sgn (Σ_{a<c<b<d} P_{ab} P_{cd})`.
* Corollary `eps_eq_prod_sigma_chi`: `ε = Π_x σ_x χ_x(P)` (the form used in Theorem 4.6).
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace EthFollowup.ExactHC

open Finset

/-! ### Signs from `ZMod 2` -/

/-- The sign `(-1)^x ∈ ℤ` of a parity `x ∈ ZMod 2`. -/
def sgn (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

@[simp] theorem sgn_zero : sgn 0 = 1 := rfl

@[simp] theorem sgn_one : sgn 1 = -1 := rfl

theorem sgn_add (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y := by
  fin_cases x <;> fin_cases y <;> rfl

theorem sgn_mul_self (x : ZMod 2) : sgn x * sgn x = 1 := by
  fin_cases x <;> rfl

theorem sgn_eq_one_or_neg_one (x : ZMod 2) : sgn x = 1 ∨ sgn x = -1 := by
  unfold sgn; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem sgn_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, prod_insert hi, sgn_add, ih]

theorem sgn_natCast (n : ℕ) : sgn (n : ZMod 2) = (-1) ^ n := by
  unfold sgn
  split_ifs with h
  · exact ((ZMod.natCast_eq_zero_iff_even).1 h).neg_one_pow.symm
  · rw [ZMod.natCast_eq_zero_iff_even, Nat.not_even_iff_odd] at h
    exact h.neg_one_pow.symm

/-! ### Chord data -/

/-- `m` crossing edges, listed in the crossing order of `Fin m`; edge `k` has chord
`{a k, b k}` with `a k < b k` (blob of the low end, blob of the high end). -/
structure Chords (g m : ℕ) where
  /-- Blob of the low end `s_k`. -/
  a : Fin m → Fin g
  /-- Blob of the high end `t_k`. -/
  b : Fin m → Fin g
  a_lt_b : ∀ k, a k < b k

namespace Chords

variable {g m : ℕ} (C : Chords g m)

/-- The chord `{a_k, b_k}`. -/
def ends (k : Fin m) : Finset (Fin g) := {C.a k, C.b k}

/-- `δ(x)`: the crossing edges at blob `x`. -/
def delta (x : Fin g) : Finset (Fin m) := univ.filter fun k => C.a k = x ∨ C.b k = x

/-- `E(x,y)`: the crossing edges with chord `(x,y)` (`a_k = x`, `b_k = y`). -/
def E (x y : Fin g) : Finset (Fin m) := univ.filter fun k => C.a k = x ∧ C.b k = y

/-- `c_{kl} = #{(x,y) ∈ {a_k,b_k} × {a_l,b_l} : y < x}`. -/
def cross (k l : Fin m) : ℕ := ((C.ends k ×ˢ C.ends l).filter fun p => p.2 < p.1).card

theorem cross_eq (k l : Fin m) :
    C.cross k l = ((if C.a l < C.a k then 1 else 0) + (if C.b l < C.a k then 1 else 0)) +
      ((if C.a l < C.b k then 1 else 0) + (if C.b l < C.b k then 1 else 0)) := by
  rw [cross, card_filter, sum_product, ends, ends,
    sum_pair (C.a_lt_b k).ne, sum_pair (C.a_lt_b l).ne, sum_pair (C.a_lt_b l).ne]

/-- The parity exponent `Σ_{k<l} π_k π_l c_{kl}` of `ε`. -/
def epsExp (π : Fin m → ZMod 2) : ZMod 2 :=
  ∑ k, ∑ l, if k < l then π k * π l * (C.cross k l : ZMod 2) else 0

/-- `ε = (-1)^{Σ_{k<l} π_k π_l c_{kl}}`. -/
def eps (π : Fin m → ZMod 2) : ℤ := sgn (C.epsExp π)

/-- `ε` as a power of `-1` with natural-number exponent (parities `π k ∈ {0,1} ⊆ ℕ`). -/
theorem eps_eq_neg_one_pow (π : Fin m → ℕ) :
    C.eps (fun k => (π k : ZMod 2)) =
      (-1) ^ (∑ k, ∑ l, if k < l then π k * π l * C.cross k l else 0) := by
  rw [eps, ← sgn_natCast]
  congr 1
  simp only [epsExp, Nat.cast_sum]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

/-- The chords of `k` and `l` meet. -/
def Meet (k l : Fin m) : Prop :=
  C.a k = C.a l ∨ C.a k = C.b l ∨ C.b k = C.a l ∨ C.b k = C.b l

instance (k l : Fin m) : Decidable (C.Meet k l) := by unfold Meet; infer_instance

theorem meet_iff_not_disjoint (k l : Fin m) : C.Meet k l ↔ ¬ Disjoint (C.ends k) (C.ends l) := by
  simp only [Meet, ends, disjoint_insert_left, disjoint_insert_right, disjoint_singleton,
    mem_insert, mem_singleton]
  tauto

theorem meet_comm (k l : Fin m) : C.Meet k l ↔ C.Meet l k := by
  unfold Meet; constructor <;> intro h <;> rcases h with h | h | h | h <;> simp [h]

/-- `s(k,l)`: the smallest common blob of the chords of `k` and `l` (when they meet). -/
def shared (k l : Fin m) : Fin g :=
  if C.a k = C.a l ∨ C.a k = C.b l then C.a k else C.b k

theorem shared_mem_ends_left (k l : Fin m) : C.shared k l ∈ C.ends k := by
  unfold shared ends; split_ifs <;> simp

theorem shared_mem_ends_right {k l : Fin m} (h : C.Meet k l) : C.shared k l ∈ C.ends l := by
  unfold shared ends; unfold Meet at h
  split_ifs with h'
  · rcases h' with h' | h' <;> simp [h']
  · simp only [not_or] at h'
    rcases h with h | h | h | h
    · exact absurd h h'.1
    · exact absurd h h'.2
    · simp [h]
    · simp [h]

theorem shared_le {k l : Fin m} {x : Fin g} (hx : x ∈ C.ends k ∩ C.ends l) :
    C.shared k l ≤ x := by
  have := C.a_lt_b k
  simp only [ends, mem_inter, mem_insert, mem_singleton] at hx
  obtain ⟨hx1, hx2⟩ := hx
  unfold shared
  split_ifs with h
  · rcases hx1 with rfl | rfl
    · exact le_rfl
    · exact this.le
  · simp only [not_or] at h
    rcases hx1 with rfl | rfl
    · rcases hx2 with h2 | h2
      · exact absurd h2 h.1
      · exact absurd h2 h.2
    · exact le_rfl

theorem mem_delta_shared_left (k l : Fin m) : k ∈ C.delta (C.shared k l) := by
  have := C.shared_mem_ends_left k l
  simp only [ends, mem_insert, mem_singleton] at this
  simp only [delta, mem_filter, mem_univ, true_and]
  tauto

theorem mem_delta_shared_right {k l : Fin m} (h : C.Meet k l) :
    l ∈ C.delta (C.shared k l) := by
  have := C.shared_mem_ends_right h
  simp only [ends, mem_insert, mem_singleton] at this
  simp only [delta, mem_filter, mem_univ, true_and]
  tauto

/-- `σ_x = (-1)^{Σ_{k<l, chords meet, s(k,l) = x} π_k π_l c_{kl}}`. -/
def sigma (π : Fin m → ZMod 2) (x : Fin g) : ℤ :=
  sgn (∑ k, ∑ l,
    if k < l ∧ C.Meet k l ∧ C.shared k l = x then π k * π l * (C.cross k l : ZMod 2) else 0)

/-- `P_{xy} = Σ_{k ∈ E(x,y)} π_k mod 2`. -/
def P (π : Fin m → ZMod 2) (x y : Fin g) : ZMod 2 := ∑ k ∈ C.E x y, π k

/-- `I(k,l)`: the chords of `k` and `l` interleave. -/
def Interleave (k l : Fin m) : Prop :=
  (C.a k < C.a l ∧ C.a l < C.b k ∧ C.b k < C.b l) ∨
    (C.a l < C.a k ∧ C.a k < C.b l ∧ C.b l < C.b k)

instance (k l : Fin m) : Decidable (C.Interleave k l) := by unfold Interleave; infer_instance

theorem interleave_comm (k l : Fin m) : C.Interleave k l ↔ C.Interleave l k := by
  unfold Interleave; tauto

theorem not_meet_of_interleave {k l : Fin m} (h : C.Interleave k l) : ¬ C.Meet k l := by
  have := C.a_lt_b k; have := C.a_lt_b l
  unfold Interleave at h; unfold Meet
  simp only [Fin.lt_def, Fin.ext_iff] at *
  omega

/-- **Lemma 4.3.** For disjoint chords, `c_{kl} ≡ I(k,l) (mod 2)`. -/
theorem cross_mod_two_of_not_meet {k l : Fin m} (h : ¬ C.Meet k l) :
    (C.cross k l : ZMod 2) = if C.Interleave k l then 1 else 0 := by
  have hk := C.a_lt_b k; have hl := C.a_lt_b l
  have key : C.cross k l % 2 = if C.Interleave k l then 1 else 0 := by
    rw [cross_eq]
    unfold Interleave
    unfold Meet at h
    simp only [Fin.lt_def, Fin.ext_iff] at *
    split_ifs <;> omega
  rw [← ZMod.natCast_mod, key]
  split_ifs <;> simp

/-- Lemma 4.3, consequence: for disjoint chords `c_{kl} mod 2` is symmetric. -/
theorem cross_mod_two_comm_of_not_meet {k l : Fin m} (h : ¬ C.Meet k l) :
    (C.cross k l : ZMod 2) = (C.cross l k : ZMod 2) := by
  rw [C.cross_mod_two_of_not_meet h,
    C.cross_mod_two_of_not_meet (fun h' => h ((C.meet_comm k l).2 h'))]
  simp only [C.interleave_comm k l]

/-- `Σ_{a<c<b<d} P_{ab} P_{cd}` (summed in the order `a, c, d, b`). -/
def interleaveExp (π : Fin m → ZMod 2) : ZMod 2 :=
  ∑ a, ∑ c, ∑ d, ∑ b, if a < c ∧ c < b ∧ b < d then C.P π a b * C.P π c d else 0

/-- The directed interleaving `a_k < a_l < b_k < b_l`. -/
private def J (k l : Fin m) : Prop := C.a k < C.a l ∧ C.a l < C.b k ∧ C.b k < C.b l

private instance (k l : Fin m) : Decidable (C.J k l) := by unfold J; infer_instance

/-- `Σ_{a<c<b<d} P_{ab} P_{cd} = Σ_{k,l} π_k π_l [a_k < a_l < b_k < b_l]`. -/
private theorem interleaveExp_eq (π : Fin m → ZMod 2) :
    C.interleaveExp π = ∑ k, ∑ l, if C.J k l then π k * π l else 0 := by
  have step1 : C.interleaveExp π = ∑ a, ∑ c, ∑ d, ∑ b, ∑ k, ∑ l,
      if (a < c ∧ c < b ∧ b < d) ∧ (C.a k = a ∧ C.b k = b) ∧ (C.a l = c ∧ C.b l = d)
      then π k * π l else 0 := by
    unfold interleaveExp
    refine sum_congr rfl fun a _ => sum_congr rfl fun c _ => sum_congr rfl fun d _ =>
      sum_congr rfl fun b _ => ?_
    simp only [P, E, sum_filter, sum_mul_sum]
    split_ifs with hA
    · refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
      split_ifs <;> simp_all
    · simp [hA]
  rw [step1]
  simp only [Finset.sum_comm (s := (univ : Finset (Fin g))) (t := (univ : Finset (Fin m)))]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  have hpt : ∀ a c d b : Fin g,
      (if (a < c ∧ c < b ∧ b < d) ∧ (C.a k = a ∧ C.b k = b) ∧ (C.a l = c ∧ C.b l = d)
        then π k * π l else 0) =
      if C.b k = b then (if C.b l = d then (if C.a l = c then (if C.a k = a then
        (if C.J k l then π k * π l else 0) else 0) else 0) else 0) else 0 := by
    intro a c d b
    by_cases h1 : C.a k = a
    · by_cases h2 : C.a l = c
      · by_cases h3 : C.b l = d
        · by_cases h4 : C.b k = b
          · subst h1 h2 h3 h4
            simp [J]
          · simp [h4]
        · simp [h3]
      · simp [h2]
    · simp [h1]
  simp only [hpt, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- **Proposition 4.4 (sign factorisation).**
`ε = Π_x σ_x · (-1)^{Σ_{a<c<b<d} P_{ab} P_{cd}}`. -/
theorem eps_eq_prod_sigma_mul (π : Fin m → ZMod 2) :
    C.eps π = (∏ x, C.sigma π x) * sgn (C.interleaveExp π) := by
  -- split into meeting and disjoint pairs
  have hsplit : C.epsExp π =
      (∑ k, ∑ l, if k < l ∧ C.Meet k l then π k * π l * (C.cross k l : ZMod 2) else 0) +
      ∑ k, ∑ l, if k < l ∧ ¬ C.Meet k l then π k * π l * (C.cross k l : ZMod 2) else 0 := by
    unfold epsExp
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    split_ifs <;> simp_all
  -- meeting pairs: one blob `s(k,l)` each
  have hmeet : sgn (∑ k, ∑ l, if k < l ∧ C.Meet k l then π k * π l * (C.cross k l : ZMod 2)
      else 0) = ∏ x, C.sigma π x := by
    unfold sigma
    rw [← sgn_sum]
    congr 1
    simp only [Finset.sum_comm (s := (univ : Finset (Fin g))) (t := (univ : Finset (Fin m)))]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    have hpt : ∀ x : Fin g, (if k < l ∧ C.Meet k l ∧ C.shared k l = x then
        π k * π l * (C.cross k l : ZMod 2) else 0) =
        if C.shared k l = x then (if k < l ∧ C.Meet k l then
          π k * π l * (C.cross k l : ZMod 2) else 0) else 0 := by
      intro x; split_ifs <;> simp_all
    simp only [hpt, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  -- disjoint pairs: Lemma 4.3, then regroup by chords
  have hdisj : (∑ k, ∑ l, if k < l ∧ ¬ C.Meet k l then π k * π l * (C.cross k l : ZMod 2)
      else 0) = C.interleaveExp π := by
    have h1 : ∀ k l : Fin m, (if k < l ∧ ¬ C.Meet k l then π k * π l * (C.cross k l : ZMod 2)
        else 0) = (if k < l then (if C.J k l then π k * π l else 0) +
          (if C.J l k then π l * π k else 0) else 0) := by
      intro k l
      by_cases hkl : k < l
      · by_cases hm : C.Meet k l
        · have hI : ¬ C.Interleave k l := fun hI => C.not_meet_of_interleave hI hm
          have hJ1 : ¬ C.J k l := fun hJ => hI (Or.inl hJ)
          have hJ2 : ¬ C.J l k := fun hJ => hI (Or.inr hJ)
          simp [hkl, hm, hJ1, hJ2]
        · simp only [hkl, hm, not_false_eq_true, and_self, ↓reduceIte,
            C.cross_mod_two_of_not_meet hm]
          unfold Interleave
          have := C.a_lt_b k; have := C.a_lt_b l
          unfold J
          simp only [Fin.lt_def] at *
          split_ifs <;> first | omega | ring
      · simp [hkl]
    simp only [h1]
    rw [interleaveExp_eq]
    -- `Σ_{k<l} (X k l + X l k) = Σ_{k,l} X k l`, since `X k k = 0`
    have h2 : ∀ k l : Fin m, (if k < l then (if C.J k l then π k * π l else 0) +
        (if C.J l k then π l * π k else 0) else 0) =
        (if k < l then (if C.J k l then π k * π l else 0) else 0) +
        (if k < l then (if C.J l k then π l * π k else 0) else 0) := by
      intro k l; split_ifs <;> simp
    simp only [h2, sum_add_distrib]
    rw [Finset.sum_comm (f := fun k l => if k < l then (if C.J l k then π l * π k else 0)
      else 0), ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy k l with h | rfl | h
    · simp [h, h.not_gt]
    · have : ¬ C.J k k := by unfold J; intro h; exact lt_irrefl _ h.1
      simp [this]
    · simp [h, h.not_gt]
  rw [eps, hsplit, sgn_add, hmeet, hdisj]

/-! ### Parity copies -/

/-- `Q_x = {(c,d) : x < c < d}`. -/
def Q {g : ℕ} (x : Fin g) : Finset (Fin g × Fin g) := univ.filter fun p => x < p.1 ∧ p.1 < p.2

/-- `χ_x(y) = (-1)^{Σ_{(c,d) ∈ Q_x} y_{cd} Σ_{c<b<d} P_{xb}}`; only `y` on `Q_x` matters. -/
def chi (π : Fin m → ZMod 2) (x : Fin g) (y : Fin g × Fin g → ZMod 2) : ℤ :=
  sgn (∑ p ∈ Q x, y p * ∑ b ∈ univ.filter (fun b => p.1 < b ∧ b < p.2), C.P π x b)

/-- **Lemma 4.5.** If every copy is correct (`y^{(x)}_{cd} = P_{cd}` on `Q_x`), then
`Π_x χ_x(y^{(x)}) = (-1)^{Σ_{a<c<b<d} P_{ab} P_{cd}}`. -/
theorem prod_chi_eq (π : Fin m → ZMod 2) (y : Fin g → Fin g × Fin g → ZMod 2)
    (hy : ∀ x, ∀ p ∈ Q x, y x p = C.P π p.1 p.2) :
    ∏ x, C.chi π x (y x) = sgn (C.interleaveExp π) := by
  unfold chi
  rw [← sgn_sum]
  congr 1
  unfold interleaveExp
  refine sum_congr rfl fun a _ => ?_
  rw [sum_congr rfl fun p hp => by rw [hy a p hp], Q, sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun c _ => sum_congr rfl fun d _ => ?_
  simp only [sum_filter, mul_sum]
  split_ifs with h
  · refine sum_congr rfl fun b _ => ?_
    by_cases hb : c < b ∧ b < d
    · simp only [hb, h.1, and_self, ↓reduceIte]
      ring
    · simp only [hb, and_false, ↓reduceIte, mul_zero]
  · refine (sum_eq_zero fun b _ => ?_).symm
    split_ifs with h'
    · exact absurd ⟨h'.1, h'.2.1.trans h'.2.2⟩ h
    · rfl

/-- **Proposition 4.4 + Lemma 4.5.** `ε = Π_x σ_x χ_x(y^{(x)})` for correct copies `y`. -/
theorem eps_eq_prod_sigma_chi (π : Fin m → ZMod 2) (y : Fin g → Fin g × Fin g → ZMod 2)
    (hy : ∀ x, ∀ p ∈ Q x, y x p = C.P π p.1 p.2) :
    C.eps π = ∏ x, C.sigma π x * C.chi π x (y x) := by
  rw [prod_mul_distrib, C.prod_chi_eq π y hy, C.eps_eq_prod_sigma_mul]

end Chords

end EthFollowup.ExactHC
