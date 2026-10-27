/-
# A counting form of the Calabro–Impagliazzo–Kabanets–Paturi isolation lemma

CIKP (CCC 2003, Lemma 3) isolate one element of a set `S ⊆ {0,1}^N` in two steps. Their proof
uses only that `S` is a set, and this file follows it for an arbitrary finite `S`.

* **Step I.** Intersect `S` with `m` sparse random GF(2) equations, each on `k` coordinates drawn
  with replacement, with random coefficients and right-hand side. With good probability some
  surviving point is *semi-isolated*: every survivor lies within Hamming distance `< r` of it.
* **Step II.** Fix `d ≥ 2r` random coordinates to random values. If the coordinates and values
  are right, exactly one survivor remains.

Everything is stated as counting over finite parameter spaces; there are no real numbers.
-/
import Mathlib

namespace EthFollowup.Isolation

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hamming distance. -/
def hdist (x y : ι → Bool) : ℕ := (univ.filter fun i => x i ≠ y i).card

theorem hdist_comm (x y : ι → Bool) : hdist x y = hdist y x := by
  unfold hdist; congr 1; ext i; simp [ne_comm]

theorem hdist_self (x : ι → Bool) : hdist x x = 0 := by simp [hdist]

theorem hdist_eq_zero {x y : ι → Bool} (h : hdist x y = 0) : x = y := by
  funext i
  by_contra hi
  have : i ∈ univ.filter fun i => x i ≠ y i := by simp [hi]
  rw [hdist, Finset.card_eq_zero] at h
  simp [h] at this

theorem hdist_triangle (x y z : ι → Bool) : hdist x z ≤ hdist x y + hdist y z := by
  unfold hdist
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
  by_contra h
  push_neg at h
  exact hi (h.1.trans h.2)

/-! ### Step II: fixing coordinates isolates a point of a set of small diameter -/

/-- If `u, w` are a farthest pair of `T` and `y ∈ T` agrees with `u` on the coordinates where
`u, w` differ, then `y = u`. -/
theorem eq_of_agree_on_diff {T : Finset (ι → Bool)} {u w y : ι → Bool}
    (hmax : ∀ a ∈ T, ∀ b ∈ T, hdist a b ≤ hdist u w) (hy : y ∈ T)
    (hw : w ∈ T) (hagree : ∀ i, u i ≠ w i → y i = u i) : y = u := by
  have hsplit : hdist y w = hdist u w + hdist y u := by
    unfold hdist
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases hui : u i = w i
      · constructor
        · intro h; right; rwa [hui]
        · rintro (h | h)
          · exact absurd hui h
          · rwa [← hui]
      · constructor
        · intro _; left; exact hui
        · intro _; rw [hagree i hui]; exact hui
    · rw [Finset.disjoint_left]
      intro i h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact h2 (hagree i h1)
  have := hmax y hy w hw
  have h0 : hdist y u = 0 := by omega
  exact hdist_eq_zero h0

/-- **Step II.** A nonempty set `T` of diameter `< 2r`, restricted to agree with some `u ∈ T` on
any coordinate set `D` containing the difference set of a farthest pair, leaves exactly `u`. The
difference set has fewer than `2r` elements. -/
theorem exists_isolating_set (T : Finset (ι → Bool)) (hT : T.Nonempty) {r : ℕ}
    (hdiam : ∀ a ∈ T, ∀ b ∈ T, hdist a b < 2 * r) :
    ∃ u ∈ T, ∃ D₀ : Finset ι, D₀.card < 2 * r ∧
      ∀ D : Finset ι, D₀ ⊆ D → T.filter (fun y => ∀ i ∈ D, y i = u i) = {u} := by
  obtain ⟨⟨u, w⟩, hp, hmax⟩ := Finset.exists_max_image (T ×ˢ T) (fun p => hdist p.1 p.2) (hT.product hT)
  rw [Finset.mem_product] at hp
  refine ⟨u, hp.1, univ.filter (fun i => u i ≠ w i), hdiam u hp.1 w hp.2, fun D hD => ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hy, hyD⟩
    refine eq_of_agree_on_diff (T := T) (w := w) ?_ hy hp.2 ?_
    · intro a ha b hb
      exact hmax ⟨a, b⟩ (Finset.mem_product.2 ⟨ha, hb⟩)
    · intro i hi
      exact hyD i (hD (by simp [hi]))
  · rintro rfl
    exact ⟨hp.1, fun _ _ => rfl⟩

/-! ### Step I, Claim 4: a sparse equation separates far points about half the time -/

theorem zmod2_cases (s : ZMod 2) : s = 0 ∨ s = 1 := by
  fin_cases s
  exacts [Or.inl rfl, Or.inr rfl]

theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := rfl

theorem zmod2_ne_one {s : ZMod 2} (h : s ≠ 1) : s = 0 := by
  rcases zmod2_cases s with h' | h'
  · exact h'
  · exact absurd h' h

theorem zmod2_eq_iff_add (a b : ZMod 2) : a = b ↔ a + b = 0 := by
  rw [add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two]

/-- `0/1` in `ZMod 2`. -/
def bit (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bit_add_bit (a b : Bool) : bit a + bit b = bit (a != b) := by
  cases a <;> cases b <;> rfl

theorem bit_not (b : Bool) : bit (!b) = bit b + 1 := by
  cases b <;> rfl

/-- A sparse equation: `k` coordinates (with replacement) and `k` coefficients. -/
abbrev Eqn (ι : Type*) (k : ℕ) := (Fin k → ι) × (Fin k → Bool)

/-- Value of the left-hand side of an equation at `x`, in GF(2). -/
def evalEqn {k : ℕ} (q : Eqn ι k) (x : ι → Bool) : ZMod 2 :=
  ∑ l, bit (q.2 l) * bit (x (q.1 l))

theorem evalEqn_add {k : ℕ} (q : Eqn ι k) (x y : ι → Bool) :
    evalEqn q x + evalEqn q y = ∑ l, bit (q.2 l) * bit (x (q.1 l) != y (q.1 l)) := by
  unfold evalEqn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_add, bit_add_bit]

/-- Toggle coordinate `l₀` of a coefficient vector. -/
def toggle {k : ℕ} (l₀ : Fin k) (c : Fin k → Bool) : Fin k → Bool :=
  Function.update c l₀ (!c l₀)

theorem toggle_toggle {k : ℕ} (l₀ : Fin k) (c : Fin k → Bool) : toggle l₀ (toggle l₀ c) = c := by
  funext l
  by_cases h : l = l₀
  · subst h; simp [toggle]
  · simp [toggle, Function.update_of_ne h]

theorem sum_toggle {k : ℕ} (d : Fin k → ZMod 2) (l₀ : Fin k) (hd : d l₀ = 1) (c : Fin k → Bool) :
    ∑ l, bit (toggle l₀ c l) * d l = ∑ l, bit (c l) * d l + 1 := by
  have key : ∀ l, bit (toggle l₀ c l) * d l =
      bit (c l) * d l + (if l = l₀ then d l else 0) := by
    intro l
    by_cases h : l = l₀
    · subst h
      simp only [toggle, Function.update_self, bit_not, if_true]
      ring
    · simp [toggle, Function.update_of_ne h, h]
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ l₀ d, if_pos (Finset.mem_univ _), hd]

/-- If some coefficient is live, exactly half of all coefficient vectors give value 1. -/
theorem two_mul_card_odd {k : ℕ} (d : Fin k → ZMod 2) (h : ∃ l₀, d l₀ = 1) :
    2 * (univ.filter fun c : Fin k → Bool => ∑ l, bit (c l) * d l = 1).card = 2 ^ k := by
  obtain ⟨l₀, hl₀⟩ := h
  have hswap : (univ.filter fun c : Fin k → Bool => ∑ l, bit (c l) * d l = 1).card =
      (univ.filter fun c : Fin k → Bool => ¬ ∑ l, bit (c l) * d l = 1).card := by
    refine Finset.card_bij' (fun c _ => toggle l₀ c) (fun c _ => toggle l₀ c) ?_ ?_ ?_ ?_
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [sum_toggle d l₀ hl₀, hc.2, zmod2_one_add_one]
      exact fun h => absurd h (by decide)
    · intro c hc
      rw [Finset.mem_filter] at hc ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [sum_toggle d l₀ hl₀, zmod2_ne_one hc.2, zero_add]
    · intro c _; exact toggle_toggle l₀ c
    · intro c _; exact toggle_toggle l₀ c
  have htot := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin k → Bool)))
    (fun c => ∑ l, bit (c l) * d l = 1)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at htot
  omega

theorem card_odd_zero {k : ℕ} (d : Fin k → ZMod 2) (h : ∀ l, d l = 0) :
    (univ.filter fun c : Fin k → Bool => ∑ l, bit (c l) * d l = 1).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c _
  simp only [h, mul_zero, Finset.sum_const_zero]
  exact fun h => absurd h (by decide)

/-- Tuples avoiding a set `Δ`. -/
theorem card_tuples_avoiding {k : ℕ} (Δ : Finset ι) :
    (univ.filter fun j : Fin k → ι => ∀ l, j l ∉ Δ).card = (Fintype.card ι - Δ.card) ^ k := by
  have : (univ.filter fun j : Fin k → ι => ∀ l, j l ∉ Δ) =
      Fintype.piFinset (fun _ : Fin k => Δᶜ) := by
    ext j; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.card_compl]

/-- The set of coordinates where `x` and `y` differ. -/
def diffSet (x y : ι → Bool) : Finset ι := univ.filter fun i => x i ≠ y i

omit [DecidableEq ι] in
theorem card_diffSet (x y : ι → Bool) : (diffSet x y).card = hdist x y := rfl

theorem bit_bne (a b : Bool) : bit (a != b) = if a ≠ b then 1 else 0 := by
  cases a <;> cases b <;> rfl

/-- **Claim 4 (exact count).** The number of sparse equations separating `x` and `y`. -/
theorem two_mul_card_separating {k : ℕ} (x y : ι → Bool) :
    2 * (univ.filter fun q : Eqn ι k => evalEqn q x ≠ evalEqn q y).card =
      2 ^ k * (Fintype.card ι ^ k - (Fintype.card ι - hdist x y) ^ k) := by
  classical
  set d : (Fin k → ι) → Fin k → ZMod 2 := fun j l => bit (x (j l) != y (j l)) with hd
  have hsep : ∀ q : Eqn ι k, evalEqn q x ≠ evalEqn q y ↔ ∑ l, bit (q.2 l) * d q.1 l = 1 := by
    intro q
    rw [Ne, zmod2_eq_iff_add, evalEqn_add]
    constructor
    · intro h; rcases zmod2_cases (∑ l, bit (q.2 l) * d q.1 l) with h' | h'
      · exact absurd h' h
      · exact h'
    · intro h h0; rw [h] at h0; exact absurd h0 (by decide)
  simp_rw [hsep]
  have hbit : ∀ a b : Bool, bit (a != b) = 1 ↔ a ≠ b := by
    intro a b; cases a <;> cases b <;> decide
  have hd1 : ∀ j : Fin k → ι, (∃ l, d j l = 1) ↔ ¬ ∀ l, j l ∉ diffSet x y := by
    intro j
    simp only [hd, hbit, diffSet, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
      not_not]
  -- condition on the coordinate tuple
  have hsplit : (univ.filter fun q : Eqn ι k => ∑ l, bit (q.2 l) * d q.1 l = 1).card =
      ∑ j : Fin k → ι, (univ.filter fun c : Fin k → Bool => ∑ l, bit (c l) * d j l = 1).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_filter]
  rw [hsplit, Finset.mul_sum]
  have hterm : ∀ j : Fin k → ι,
      2 * (univ.filter fun c : Fin k → Bool => ∑ l, bit (c l) * d j l = 1).card =
        if ¬ ∀ l, j l ∉ diffSet x y then 2 ^ k else 0 := by
    intro j
    by_cases h : ∀ l, j l ∉ diffSet x y
    · rw [if_neg (not_not.2 h), card_odd_zero (d j)]
      intro l
      have : ¬ ∃ l, d j l = 1 := fun h' => (hd1 j).1 h' h
      push_neg at this
      exact zmod2_ne_one (this l)
    · rw [if_pos h]
      exact two_mul_card_odd (d j) ((hd1 j).2 h)
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_comm]
  congr 1
  have htot := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin k → ι)))
    (fun j => ∀ l, j l ∉ diffSet x y)
  rw [card_tuples_avoiding, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    card_diffSet] at htot
  omega

theorem card_eqn (k : ℕ) : Fintype.card (Eqn ι k) = Fintype.card ι ^ k * 2 ^ k := by
  simp [Eqn, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool]

/-- The number of equations on which `x, y` agree, doubled. -/
theorem two_mul_card_agree {k : ℕ} (x y : ι → Bool) :
    2 * (univ.filter fun q : Eqn ι k => evalEqn q x = evalEqn q y).card =
      2 ^ k * (Fintype.card ι ^ k + (Fintype.card ι - hdist x y) ^ k) := by
  have htot := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Eqn ι k)))
    (fun q => evalEqn q x = evalEqn q y)
  rw [Finset.card_univ, card_eqn] at htot
  have hsep := two_mul_card_separating (k := k) x y
  have hle : (Fintype.card ι - hdist x y) ^ k ≤ Fintype.card ι ^ k :=
    Nat.pow_le_pow_left (Nat.sub_le _ _) k
  simp only [ne_eq] at hsep
  have : 2 * (univ.filter fun q : Eqn ι k => evalEqn q x = evalEqn q y).card =
      2 * (Fintype.card ι ^ k * 2 ^ k) -
        2 * (univ.filter fun q : Eqn ι k => ¬ evalEqn q x = evalEqn q y).card := by omega
  rw [this, hsep]
  generalize (Fintype.card ι - hdist x y) ^ k = b at hle ⊢
  generalize Fintype.card ι ^ k = a at hle ⊢
  have h1 : 2 ^ k * b ≤ 2 ^ k * a := Nat.mul_le_mul_left _ hle
  have h2 : 2 ^ k * (a - b) ≤ 2 * (a * 2 ^ k) := by
    rw [Nat.mul_sub]
    calc 2 ^ k * a - 2 ^ k * b ≤ 2 ^ k * a := Nat.sub_le _ _
      _ ≤ 2 * (a * 2 ^ k) := by rw [mul_comm a (2 ^ k)]; omega
  rw [Nat.mul_sub] at h2 ⊢
  zify [h1, h2]
  ring

/-! ### Step I: systems of equations -/

/-- A system of `m` sparse equations. -/
abbrev Sys (ι : Type*) (k m : ℕ) := Fin m → Eqn ι k

def applySys {k m : ℕ} (A : Sys ι k m) (x : ι → Bool) : Fin m → ZMod 2 :=
  fun i => evalEqn (A i) x

theorem card_sys (k m : ℕ) : Fintype.card (Sys ι k m) = (Fintype.card ι ^ k * 2 ^ k) ^ m := by
  rw [Fintype.card_fun, card_eqn, Fintype.card_fin]

theorem card_sys_agree {k m : ℕ} (x y : ι → Bool) :
    (univ.filter fun A : Sys ι k m => applySys A x = applySys A y).card =
      (univ.filter fun q : Eqn ι k => evalEqn q x = evalEqn q y).card ^ m := by
  have : (univ.filter fun A : Sys ι k m => applySys A x = applySys A y) =
      Fintype.piFinset (fun _ : Fin m => univ.filter fun q : Eqn ι k => evalEqn q x = evalEqn q y) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    exact ⟨fun h i => congrFun h i, fun h => funext h⟩
  rw [this, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- For a far pair, `2^m` times the number of systems that do not separate it is at most `Q`. -/
theorem card_sys_agree_le {k m r : ℕ} (x y : ι → Bool) (hxy : r ≤ hdist x y) :
    2 ^ m * (univ.filter fun A : Sys ι k m => applySys A x = applySys A y).card ≤
      (2 ^ k * (Fintype.card ι ^ k + (Fintype.card ι - r) ^ k)) ^ m := by
  rw [card_sys_agree, ← Nat.mul_pow, two_mul_card_agree]
  refine Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left ?_ _)) m
  exact Nat.pow_le_pow_left (Nat.sub_le_sub_left hxy _) k

/-- `x` is semi-isolated by `A`: every point of `S` hashed with `x` is close to `x`. -/
def Good {k m : ℕ} (S : Finset (ι → Bool)) (r : ℕ) (A : Sys ι k m) (x : ι → Bool) : Prop :=
  ∀ y ∈ S, applySys A x = applySys A y → hdist x y < r

instance {k m : ℕ} (S : Finset (ι → Bool)) (r : ℕ) (A : Sys ι k m) (x : ι → Bool) :
    Decidable (Good S r A x) := by unfold Good; infer_instance

theorem two_mul_card_bad_le {k m r : ℕ} (S : Finset (ι → Bool)) (x : ι → Bool)
    (Hm : 2 * S.card * (2 ^ k * (Fintype.card ι ^ k + (Fintype.card ι - r) ^ k)) ^ m ≤
      2 ^ m * (Fintype.card ι ^ k * 2 ^ k) ^ m) :
    2 * (univ.filter fun A : Sys ι k m => ¬ Good S r A x).card ≤ Fintype.card (Sys ι k m) := by
  have hsub : (univ.filter fun A : Sys ι k m => ¬ Good S r A x) ⊆
      (S.filter fun y => r ≤ hdist x y).biUnion
        (fun y => univ.filter fun A : Sys ι k m => applySys A x = applySys A y) := by
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Good, not_forall, not_lt] at hA
    obtain ⟨y, hy, hagree, hfar⟩ := hA
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨y, ⟨hy, hfar⟩, hagree⟩
  have hle := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hsum : 2 ^ m * ∑ y ∈ S.filter (fun y => r ≤ hdist x y),
      (univ.filter fun A : Sys ι k m => applySys A x = applySys A y).card ≤
      S.card * (2 ^ k * (Fintype.card ι ^ k + (Fintype.card ι - r) ^ k)) ^ m := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun y hy => card_sys_agree_le x y (Finset.mem_filter.1 hy).2).trans ?_
    rw [Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))
  rw [card_sys]
  have h2m : 0 < 2 ^ m := pow_pos (by norm_num) _
  have : 2 ^ m * (2 * (univ.filter fun A : Sys ι k m => ¬ Good S r A x).card) ≤
      2 ^ m * (Fintype.card ι ^ k * 2 ^ k) ^ m := by
    calc 2 ^ m * (2 * (univ.filter fun A : Sys ι k m => ¬ Good S r A x).card)
        = 2 * (2 ^ m * (univ.filter fun A : Sys ι k m => ¬ Good S r A x).card) := by ring
      _ ≤ 2 * (2 ^ m * ∑ y ∈ S.filter (fun y => r ≤ hdist x y),
          (univ.filter fun A : Sys ι k m => applySys A x = applySys A y).card) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle)
      _ ≤ 2 * (S.card * (2 ^ k * (Fintype.card ι ^ k + (Fintype.card ι - r) ^ k)) ^ m) :=
          Nat.mul_le_mul_left _ hsum
      _ = 2 * S.card * (2 ^ k * (Fintype.card ι ^ k + (Fintype.card ι - r) ^ k)) ^ m := by ring
      _ ≤ _ := Hm
  exact Nat.le_of_mul_le_mul_left this h2m

theorem two_mul_card_good_ge {k m r : ℕ} (S : Finset (ι → Bool)) (x : ι → Bool)
    (Hm : 2 * S.card * (2 ^ k * (Fintype.card ι ^ k + (Fintype.card ι - r) ^ k)) ^ m ≤
      2 ^ m * (Fintype.card ι ^ k * 2 ^ k) ^ m) :
    Fintype.card (Sys ι k m) ≤ 2 * (univ.filter fun A : Sys ι k m => Good S r A x).card := by
  have hbad := two_mul_card_bad_le (k := k) (m := m) (r := r) S x Hm
  have htot := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Sys ι k m)))
    (fun A => Good S r A x)
  rw [Finset.card_univ] at htot
  omega

/-- Hamming-ball volume: the number of coordinate sets of size `< r`. -/
def ballVol (ι : Type*) [Fintype ι] (r : ℕ) : ℕ :=
  ((univ : Finset (Finset ι)).filter fun T => T.card < r).card

theorem diffSet_injective (x₀ : ι → Bool) : Function.Injective (diffSet x₀) := by
  intro x x' h
  funext i
  have hi := congrArg (fun T => i ∈ T) h
  simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at hi
  cases hx0 : x₀ i <;> cases hx : x i <;> cases hx' : x' i <;> simp_all

/-- Survivors that are semi-isolated, for a fixed hash `(A, b)`. -/
def survivors {k m : ℕ} (S : Finset (ι → Bool)) (r : ℕ) (A : Sys ι k m) (b : Fin m → ZMod 2) :
    Finset (ι → Bool) :=
  S.filter fun x => Good S r A x ∧ applySys A x = b

theorem card_survivors_le {k m r : ℕ} (S : Finset (ι → Bool)) (A : Sys ι k m)
    (b : Fin m → ZMod 2) : (survivors S r A b).card ≤ ballVol ι r := by
  rcases (survivors S r A b).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [h, Finset.card_empty]; exact Nat.zero_le _
  · simp only [survivors, Finset.mem_filter] at hx₀
    refine Finset.card_le_card_of_injOn (diffSet x₀) ?_ (fun x _ y _ h => diffSet_injective x₀ h)
    intro x hx
    simp only [survivors, Finset.coe_filter, Set.mem_setOf_eq] at hx
    simp only [ballVol, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rw [card_diffSet]
    exact hx₀.2.1 x hx.1 (hx₀.2.2.trans hx.2.2.symm)

/-- **Step I.** Many hashes `(A, b)` have a semi-isolated survivor. -/
theorem card_hash_nonempty {k m r : ℕ} (S : Finset (ι → Bool))
    (Hm : 2 * S.card * (2 ^ k * (Fintype.card ι ^ k + (Fintype.card ι - r) ^ k)) ^ m ≤
      2 ^ m * (Fintype.card ι ^ k * 2 ^ k) ^ m) :
    S.card * Fintype.card (Sys ι k m) ≤
      2 * ballVol ι r *
        (univ.filter fun p : Sys ι k m × (Fin m → ZMod 2) =>
          (survivors S r p.1 p.2).Nonempty).card := by
  classical
  -- double counting of (A, x) with x semi-isolated by A
  have hdouble : ∑ A : Sys ι k m, (S.filter fun x => Good S r A x).card =
      ∑ x ∈ S, (univ.filter fun A : Sys ι k m => Good S r A x).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hlow : S.card * Fintype.card (Sys ι k m) ≤
      2 * ∑ A : Sys ι k m, (S.filter fun x => Good S r A x).card := by
    rw [hdouble, Finset.mul_sum]
    calc S.card * Fintype.card (Sys ι k m) = ∑ _x ∈ S, Fintype.card (Sys ι k m) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun x _ => two_mul_card_good_ge S x Hm
  -- split each A by the value b = A x
  have hfiber : ∀ A : Sys ι k m, (S.filter fun x => Good S r A x).card =
      ∑ b : Fin m → ZMod 2, (survivors S r A b).card := by
    intro A
    rw [Finset.card_eq_sum_card_fiberwise (f := applySys A) (t := univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [survivors, Finset.filter_filter]
  have hball : ∀ A : Sys ι k m, ∑ b : Fin m → ZMod 2, (survivors S r A b).card ≤
      ballVol ι r * (univ.filter fun b : Fin m → ZMod 2 => (survivors S r A b).Nonempty).card := by
    intro A
    rw [Finset.card_eq_sum_ones, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_le_sum fun b _ => ?_
    split_ifs with h
    · rw [mul_one]; exact card_survivors_le S A b
    · rw [Finset.not_nonempty_iff_eq_empty.1 h, Finset.card_empty]
  have hprod : (univ.filter fun p : Sys ι k m × (Fin m → ZMod 2) =>
      (survivors S r p.1 p.2).Nonempty).card =
      ∑ A : Sys ι k m, (univ.filter fun b : Fin m → ZMod 2 => (survivors S r A b).Nonempty).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.card_filter]
  calc S.card * Fintype.card (Sys ι k m)
      ≤ 2 * ∑ A : Sys ι k m, (S.filter fun x => Good S r A x).card := hlow
    _ = 2 * ∑ A : Sys ι k m, ∑ b : Fin m → ZMod 2, (survivors S r A b).card := by
        simp_rw [hfiber]
    _ ≤ 2 * ∑ A : Sys ι k m, ballVol ι r *
          (univ.filter fun b : Fin m → ZMod 2 => (survivors S r A b).Nonempty).card :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun A _ => hball A)
    _ = _ := by
        rw [hprod, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun A _ => ?_
        ring

/-! ### Step II per hash, and the final count -/

/-- The full hash `(A, b, D, α)` leaves exactly one element of `S`. -/
def Isolates {k m : ℕ} (S : Finset (ι → Bool)) (A : Sys ι k m) (b : Fin m → ZMod 2)
    (D : Finset ι) (α : ι → Bool) : Prop :=
  (S.filter fun y => applySys A y = b ∧ ∀ i ∈ D, y i = α i).card = 1

instance {k m : ℕ} (S : Finset (ι → Bool)) (A : Sys ι k m) (b : Fin m → ZMod 2)
    (D : Finset ι) (α : ι → Bool) : Decidable (Isolates S A b D α) := by
  unfold Isolates; infer_instance

theorem card_agreeing (D : Finset ι) (u : ι → Bool) :
    (univ.filter fun α : ι → Bool => ∀ i ∈ D, α i = u i).card = 2 ^ (Fintype.card ι - D.card) := by
  have : (univ.filter fun α : ι → Bool => ∀ i ∈ D, α i = u i) =
      Fintype.piFinset (fun i => if i ∈ D then {u i} else univ) := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      split_ifs with hi
      · exact Finset.mem_singleton.2 (h i hi)
      · exact Finset.mem_univ _
    · intro h i hi
      have := h i
      rw [if_pos hi] at this
      exact Finset.mem_singleton.1 this
  rw [this, Fintype.card_piFinset]
  have hc : ∀ i, (if i ∈ D then ({u i} : Finset Bool) else univ).card = if i ∈ D then 1 else 2 := by
    intro i; split_ifs <;> simp
  simp_rw [hc]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun i => i ∈ D)
  rw [Finset.card_univ, Finset.filter_mem_eq_inter, Finset.univ_inter] at this
  omega

/-- **Step II for a fixed hash.** If `(A, b)` has a semi-isolated survivor, then at least
`2^(N−d)` choices of `(D, α)` with `|D| = d ≥ 2r` isolate exactly one element. -/
theorem card_isolating_DA {k m r d : ℕ} (S : Finset (ι → Bool)) (A : Sys ι k m)
    (b : Fin m → ZMod 2) (hne : (survivors S r A b).Nonempty) (hd : 2 * r ≤ d)
    (hdN : d ≤ Fintype.card ι) :
    2 ^ (Fintype.card ι - d) ≤
      ((Finset.univ.powersetCard d ×ˢ (univ : Finset (ι → Bool))).filter
        fun p => Isolates S A b p.1 p.2).card := by
  obtain ⟨x₀, hx₀⟩ := hne
  simp only [survivors, Finset.mem_filter] at hx₀
  set T := S.filter fun y => applySys A y = b with hT
  have hclose : ∀ a ∈ T, hdist x₀ a < r := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact hx₀.2.1 a ha.1 (hx₀.2.2.trans ha.2.symm)
  have hdiam : ∀ a ∈ T, ∀ c ∈ T, hdist a c < 2 * r := by
    intro a ha c hc
    have h1 := hclose a ha
    have h2 := hclose c hc
    rw [hdist_comm] at h1
    have := hdist_triangle a x₀ c
    omega
  have hTne : T.Nonempty := ⟨x₀, Finset.mem_filter.2 ⟨hx₀.1, hx₀.2.2⟩⟩
  obtain ⟨u, hu, D₀, hD₀, hiso⟩ := exists_isolating_set T hTne hdiam
  obtain ⟨D, hD₀D, -, hDcard⟩ := Finset.exists_subsuperset_card_eq (n := d)
    (Finset.subset_univ D₀) (by omega) (by rw [Finset.card_univ]; exact hdN)
  have hagr := card_agreeing D u
  rw [hDcard] at hagr
  rw [← hagr]
  refine Finset.card_le_card_of_injOn (fun α => (D, α)) ?_ (fun _ _ _ _ h => (Prod.mk.inj h).2)
  intro α hα
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hα
  simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_powersetCard,
    Finset.subset_univ, true_and, Finset.mem_univ, and_true, Set.mem_setOf_eq]
  refine ⟨hDcard, ?_⟩
  unfold Isolates
  have : (S.filter fun y => applySys A y = b ∧ ∀ i ∈ D, y i = α i) =
      T.filter fun y => ∀ i ∈ D, y i = u i := by
    rw [hT, Finset.filter_filter]
    refine Finset.filter_congr fun y _ => ?_
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi => (h2 i hi).trans (hα i hi)⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi => (h2 i hi).trans (hα i hi).symm⟩
  rw [this, hiso D hD₀D, Finset.card_singleton]

/-- **Isolation lemma (counting form).** Let `N = |ι|`, `S ⊆ {0,1}^ι`, and suppose `m`
equations of sparsity `k` satisfy the union-bound condition `Hm` at radius `r`. Then for every
`d` with `2r ≤ d ≤ N`, the fraction of hashes `(A, b, D, α)`, with `|D| = d`, that leave exactly
one element of `S` is at least

  `|S| · 2^(N−d) / (2 · V(r) · 2^m · C(N, d) · 2^N)  =  |S| / (2 · V(r) · 2^m · C(N, d) · 2^d)`,

where `V(r)` is the number of coordinate sets of size `< r`. -/
theorem isolation_count {k m r d : ℕ} (S : Finset (ι → Bool))
    (Hm : 2 * S.card * (2 ^ k * (Fintype.card ι ^ k + (Fintype.card ι - r) ^ k)) ^ m ≤
      2 ^ m * (Fintype.card ι ^ k * 2 ^ k) ^ m)
    (hd : 2 * r ≤ d) (hdN : d ≤ Fintype.card ι) :
    S.card * Fintype.card (Sys ι k m) * 2 ^ (Fintype.card ι - d) ≤
      2 * ballVol ι r *
        (((univ : Finset (Sys ι k m × (Fin m → ZMod 2))) ×ˢ
            (Finset.univ.powersetCard d ×ˢ (univ : Finset (ι → Bool)))).filter
          fun ω => Isolates S ω.1.1 ω.1.2 ω.2.1 ω.2.2).card := by
  classical
  have hsplit : (((univ : Finset (Sys ι k m × (Fin m → ZMod 2))) ×ˢ
      (Finset.univ.powersetCard d ×ˢ (univ : Finset (ι → Bool)))).filter
        fun ω => Isolates S ω.1.1 ω.1.2 ω.2.1 ω.2.2).card =
      ∑ p : Sys ι k m × (Fin m → ZMod 2),
        ((Finset.univ.powersetCard d ×ˢ (univ : Finset (ι → Bool))).filter
          fun q => Isolates S p.1 p.2 q.1 q.2).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.card_filter]
  have hlow : (univ.filter fun p : Sys ι k m × (Fin m → ZMod 2) =>
      (survivors S r p.1 p.2).Nonempty).card * 2 ^ (Fintype.card ι - d) ≤
      ∑ p : Sys ι k m × (Fin m → ZMod 2),
        ((Finset.univ.powersetCard d ×ˢ (univ : Finset (ι → Bool))).filter
          fun q => Isolates S p.1 p.2 q.1 q.2).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_le_sum fun p _ => ?_
    split_ifs with h
    · rw [one_mul]; exact card_isolating_DA S p.1 p.2 h hd hdN
    · exact Nat.zero_le _
  have hI := card_hash_nonempty (k := k) (m := m) (r := r) S Hm
  rw [hsplit]
  calc S.card * Fintype.card (Sys ι k m) * 2 ^ (Fintype.card ι - d)
      ≤ 2 * ballVol ι r * (univ.filter fun p : Sys ι k m × (Fin m → ZMod 2) =>
          (survivors S r p.1 p.2).Nonempty).card * 2 ^ (Fintype.card ι - d) :=
        Nat.mul_le_mul_right _ hI
    _ ≤ _ := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hlow

end EthFollowup.Isolation
