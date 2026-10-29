/-
# The vertex-balanced partition and the enumeration of the profiles (module A1, file 6)

`research/hc-degree-theorem.md` Lemma 4.1 and Lemma 3.3.

* `vbN n g v = v·g/n`, the blob of the vertex `v` (vertices in order, `g` blocks of consecutive
  vertices); `vertexBalanced n g : Fin n → Fin g` (for `g ≥ 1`); `card_blob_vb_le` :
  `#V_a ≤ n/g + 1`, hence `g·#V_a ≤ n + g`.
* Profiles are indexed by `y < Rd^{g·g}` (`nPrN Rd g`): the digit of `y` at the place `b + g·a`
  (`digN`) is `s_ab` for `a < b` (`profN`); the digits at the places with `b ≤ a` must vanish
  (`upperN`). `sum_profiles`: `∑_{y < Rd^{g·g}, upper y} F(prof y) = ∑_{s ∈ symProfiles Rd g} F s`,
  where `symProfiles Rd g` are the symmetric profiles with zero diagonal and entries `< Rd`.
* Polynomial time of `digN`, `profN`, `upperN` (`profN_polyT`, `upperN_polyT`).
-/
import EthFollowup.ExactHC.Blobs
import Mathlib.Algebra.BigOperators.Fin
import ToTuring.Poly.IsPoly
import ToTuring.Lib.List3
import ToTuring.Lib.Nat1b
import ToTuring.Closure.Cases

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset

namespace VB

/-! ### The partition -/

/-- The blob of the vertex `v`: `v·g/n`. -/
def vbN (n g v : ℕ) : ℕ := v * g / n

theorem vbN_lt {n g v : ℕ} (hv : v < n) (hg : 1 ≤ g) : vbN n g v < g := by
  unfold vbN
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  exact Nat.mul_lt_mul_of_pos_right hv (by omega) |>.trans_le (by rw [mul_comm])

/-- **The vertex-balanced partition** (Lemma 4.1). -/
def vertexBalanced (n g : ℕ) [NeZero g] (v : Fin n) : Fin g :=
  ⟨vbN n g v.val, vbN_lt v.2 (NeZero.one_le)⟩

theorem card_vb_le (n g a : ℕ) (hg : 1 ≤ g) :
    #((range n).filter fun v => vbN n g v = a) ≤ n / g + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set S := (range n).filter fun v => vbN n g v = a with hS
  rcases S.eq_empty_or_nonempty with h | hne
  · rw [h]; simp
  have hmem : ∀ v ∈ S, a * n ≤ v * g ∧ v * g < a * n + n := by
    intro v hv
    rw [hS, mem_filter] at hv
    have hva : v * g / n = a := hv.2
    constructor
    · have := Nat.div_mul_le_self (v * g) n
      rw [hva] at this; exact this
    · have := Nat.lt_div_mul_add (a := v * g) hn
      rw [hva] at this; exact this
  set v₀ := S.min' hne
  have hsub : S ⊆ Ico v₀ (v₀ + (n / g + 1)) := by
    intro v hv
    have h0 := S.min'_le v hv
    obtain ⟨-, h2⟩ := hmem v hv
    obtain ⟨h3, -⟩ := hmem v₀ (S.min'_mem hne)
    rw [mem_Ico]
    refine ⟨h0, ?_⟩
    by_contra hc
    have h5 : (v₀ + (n / g + 1)) * g ≤ v * g := Nat.mul_le_mul_right g (by omega)
    have h6 := Nat.lt_div_mul_add (a := n) (b := g) (by omega)
    rw [add_mul, add_mul, one_mul] at h5
    omega
  calc #S ≤ #(Ico v₀ (v₀ + (n / g + 1))) := card_le_card hsub
    _ = n / g + 1 := by rw [Nat.card_Ico, Nat.add_sub_cancel_left]

/-- **The blobs of the vertex-balanced partition have at most `n/g + 1` vertices.** -/
theorem card_blob_vb_le (n g : ℕ) [NeZero g] (a : Fin g) :
    #(blob (vertexBalanced n g) a) ≤ n / g + 1 := by
  refine le_trans ?_ (card_vb_le n g a.val (NeZero.one_le))
  have : (blob (vertexBalanced n g) a).map ⟨Fin.val, Fin.val_injective⟩ ⊆
      (range n).filter fun v => vbN n g v = a.val := by
    intro v hv
    simp only [mem_map, blob, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simp only [mem_filter, mem_range, w.2, true_and]
    rw [← hw]; rfl
  rw [← card_map]
  exact card_le_card this

theorem g_mul_card_blob_vb_le (n g : ℕ) [NeZero g] (a : Fin g) :
    g * #(blob (vertexBalanced n g) a) ≤ n + g := by
  have h1 := card_blob_vb_le n g a
  have h2 : g * (n / g) ≤ n := Nat.mul_div_le n g
  nlinarith

/-! ### The profiles -/

/-- The digit `i` of `y` in base `Rd`. -/
def digN (Rd y i : ℕ) : ℕ := y / Rd ^ i % Rd

/-- The profile entry `s_ab` of the index `y` (`a, b < g`): the digit at `b + g·a` for `a < b`. -/
def profN (Rd g y a b : ℕ) : ℕ :=
  if a < b then digN Rd y (b + g * a) else if b < a then digN Rd y (a + g * b) else 0

/-- The digits at the places `i = b + g·a` with `b ≤ a` vanish. -/
def upperN (Rd g y : ℕ) : Bool :=
  (List.range (g * g)).all fun i => !decide (i % g ≤ i / g) || decide (digN Rd y i = 0)

/-- The number of profile indices. -/
def nPrN (Rd g : ℕ) : ℕ := Rd ^ (g * g)

/-- The profile of the index `y`. -/
def prof (Rd g y : ℕ) (a b : Fin g) : ℕ := profN Rd g y a.val b.val

theorem prof_symm (Rd g y : ℕ) (a b : Fin g) : prof Rd g y a b = prof Rd g y b a := by
  unfold prof profN
  rcases lt_trichotomy a.val b.val with h | h | h
  · rw [if_pos h, if_neg (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [if_neg (by omega), if_pos h, if_pos h]

theorem prof_diag (Rd g y : ℕ) (a : Fin g) : prof Rd g y a a = 0 := by
  simp [prof, profN]

theorem upperN_iff (Rd g y : ℕ) :
    upperN Rd g y = true ↔ ∀ a b : Fin g, b ≤ a → digN Rd y (b.val + g * a.val) = 0 := by
  simp only [upperN, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, not_le, decide_eq_true_eq]
  constructor
  · intro h a b hab
    have hg : 0 < g := Fin.pos a
    have hi : b.val + g * a.val < g * g := by
      have := a.2; have := b.2; nlinarith
    have e1 : (b.val + g * a.val) % g = b.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.2]
    have e2 : (b.val + g * a.val) / g = a.val := by
      rw [Nat.add_mul_div_left _ _ hg, Nat.div_eq_of_lt b.2, zero_add]
    rcases h _ hi with h' | h'
    · rw [e1, e2] at h'; exact absurd (Fin.le_def.1 hab) (not_le.2 h')
    · exact h'
  · intro h i hi
    have hg : 0 < g := by
      rcases Nat.eq_zero_or_pos g with h0 | h0
      · subst h0; simp at hi
      · exact h0
    by_cases hab : i % g ≤ i / g
    · right
      have ha : i / g < g := Nat.div_lt_of_lt_mul hi
      have := h ⟨i / g, ha⟩ ⟨i % g, Nat.mod_lt _ hg⟩ (Fin.le_def.2 hab)
      simp only at this
      rwa [Nat.mod_add_div] at this
    · left; omega

/-- The symmetric profiles with zero diagonal and entries `< Rd`. -/
def symProfiles (Rd g : ℕ) : Finset (Fin g → Fin g → ℕ) :=
  (Fintype.piFinset fun _ : Fin g => Fintype.piFinset fun _ : Fin g => range Rd).filter
    fun s => (∀ a b, s a b = s b a) ∧ ∀ a, s a a = 0

theorem mem_symProfiles {Rd g : ℕ} {s : Fin g → Fin g → ℕ} :
    s ∈ symProfiles Rd g ↔ (∀ a b, s a b < Rd) ∧ (∀ a b, s a b = s b a) ∧ ∀ a, s a a = 0 := by
  simp [symProfiles, Fintype.mem_piFinset]

theorem digN_lt {Rd : ℕ} (hR : 1 ≤ Rd) (y i : ℕ) : digN Rd y i < Rd := Nat.mod_lt _ (by omega)

theorem prof_mem {Rd : ℕ} (hR : 1 ≤ Rd) (g y : ℕ) : prof Rd g y ∈ symProfiles Rd g := by
  rw [mem_symProfiles]
  refine ⟨fun a b => ?_, prof_symm Rd g y, prof_diag Rd g y⟩
  unfold prof profN
  split_ifs
  · exact digN_lt hR _ _
  · exact digN_lt hR _ _
  · omega

/-- **The enumeration of the profiles** (Lemma 3.3): a sum over the indices `y < Rd^{g·g}` with
vanishing lower digits is a sum over the symmetric profiles with zero diagonal and entries `< Rd`. -/
theorem sum_profiles {M : Type*} [AddCommMonoid M] {Rd : ℕ} (hR : 1 ≤ Rd) (g : ℕ)
    (F : (Fin g → Fin g → ℕ) → M) :
    ∑ y ∈ range (nPrN Rd g), (if upperN Rd g y = true then F (prof Rd g y) else 0) =
      ∑ s ∈ symProfiles Rd g, F s := by
  set N := g * g
  -- the digits of `y` as a function `Fin (g*g) → Fin Rd`
  have e1 : ∑ y ∈ range (nPrN Rd g), (if upperN Rd g y = true then F (prof Rd g y) else 0) =
      ∑ d : Fin N → Fin Rd, (if upperN Rd g (finFunctionFinEquiv d) = true then
        F (prof Rd g (finFunctionFinEquiv d)) else 0) := by
    unfold nPrN
    rw [Finset.sum_range]
    exact ((finFunctionFinEquiv (m := Rd) (n := N)).sum_comp
      (fun i => if upperN Rd g i = true then F (prof Rd g i) else 0)).symm
  have hdig : ∀ (d : Fin N → Fin Rd) (i : Fin N), digN Rd (finFunctionFinEquiv d) i = d i := by
    intro d i
    have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv d) i
    rw [Equiv.symm_apply_apply] at this
    rw [digN, ← this]
  rw [e1, ← sum_filter]
  -- the bijection with the profiles
  let ix : Fin g → Fin g → Fin N := fun a b => finProdFinEquiv (a, b)
  have hix : ∀ a b : Fin g, (ix a b : ℕ) = b.val + g * a.val := fun a b => finProdFinEquiv_apply_val _
  let toS : (Fin N → Fin Rd) → (Fin g → Fin g → ℕ) := fun d a b =>
    if a < b then d (ix a b) else if b < a then d (ix b a) else 0
  have htoS : ∀ d : Fin N → Fin Rd, prof Rd g (finFunctionFinEquiv d) = toS d := by
    intro d; funext a b
    simp only [prof, profN, toS, Fin.lt_def]
    split_ifs
    · rw [← hix, hdig]
    · rw [← hix, hdig]
    · rfl
  have hupper : ∀ d : Fin N → Fin Rd, upperN Rd g (finFunctionFinEquiv d) = true ↔
      ∀ a b : Fin g, b ≤ a → (d (ix a b) : ℕ) = 0 := by
    intro d
    rw [upperN_iff]
    refine forall_congr' fun a => forall_congr' fun b => imp_congr_right fun _ => ?_
    rw [← hix, hdig]
  let toD : (Fin g → Fin g → ℕ) → (Fin N → Fin Rd) := fun s i => show Fin Rd from
    if h : (finProdFinEquiv.symm i).1 < (finProdFinEquiv.symm i).2 ∧
        s (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 < Rd then
      ⟨s (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2, h.2⟩
    else ⟨(0 : ℕ), by omega⟩
  refine sum_nbij' toS toD ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [mem_filter] at hd
    rw [← htoS]; exact prof_mem hR g _
  · intro s _
    rw [mem_filter, hupper]
    refine ⟨mem_univ _, fun a b hab => ?_⟩
    simp only [toD, ix, Equiv.symm_apply_apply]
    rw [dif_neg (by intro h; exact absurd h.1 (not_lt.2 hab))]
  · intro d hd
    rw [mem_filter, hupper] at hd
    funext i
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective i
    simp only [toD, toS, Equiv.symm_apply_apply]
    by_cases hab : a < b
    · rw [dif_pos ⟨hab, by rw [if_pos hab]; exact (d (ix a b)).2⟩]
      simp [hab, ix]
    · rw [dif_neg (fun h => hab h.1)]
      exact Fin.ext (hd.2 a b (not_lt.1 hab)).symm
  · intro s hs
    rw [mem_symProfiles] at hs
    funext a b
    simp only [toS, toD, ix, Equiv.symm_apply_apply]
    split_ifs with h1 h2 h3 h4
    · rfl
    · exact absurd ⟨h1, hs.1 a b⟩ h2
    · exact (hs.2.1 a b).symm
    · exact absurd ⟨h3, hs.1 b a⟩ h4
    · have : a = b := le_antisymm (not_lt.1 h3) (not_lt.1 h1)
      subst this; exact (hs.2.2 a).symm
  · intro d _
    rw [htoS]

/-! ### Polynomial time -/

section Poly

open Groundwork

variable {α : Type} [Enc α]

@[fun_prop] theorem digN_polyT {Rd y i : α → ℕ} (hR : PolyT Rd) (hy : PolyT y) (hi : PolyT i) :
    PolyT fun x => digN (Rd x) (y x) (i x) := by
  unfold digN; fun_prop

@[fun_prop] theorem profN_polyT {Rd g y a b : α → ℕ} (hR : PolyT Rd) (hg : PolyT g) (hy : PolyT y)
    (ha : PolyT a) (hb : PolyT b) : PolyT fun x => profN (Rd x) (g x) (y x) (a x) (b x) := by
  unfold profN; fun_prop

theorem upperN_polyT {Rd g y : α → ℕ} (hR : PolyT Rd) (hg : Unary g) (hy : PolyT y) :
    PolyT fun x => upperN (Rd x) (g x) (y x) := by
  have hr : PolyT fun x => List.range (g x * g x) := PolyT.range (hg.mul hg)
  have hg' : PolyT fun p : α × ℕ => g p.1 := (hg.comp PolyT.id'.fst).poly
  have h1 : PolyT fun p : α × ℕ => Rd p.1 := hR.comp PolyT.id'.fst
  have h2 : PolyT fun p : α × ℕ => y p.1 := hy.comp PolyT.id'.fst
  have h3 : PolyT fun p : α × ℕ => p.2 := PolyT.id'.snd
  have hin : PolyT fun p : α × ℕ =>
      (!decide (p.2 % g p.1 ≤ p.2 / g p.1) || decide (digN (Rd p.1) (y p.1) p.2 = 0)) :=
    PolyT.or' (PolyT.not' (PolyT.decide_le (PolyT.mod h3 hg') (PolyT.div h3 hg')))
      (PolyT.decide_eq (digN_polyT h1 h2 h3) (PolyT.const 0))
  exact PolyT.all (f := fun x i => (!decide (i % g x ≤ i / g x) || decide (digN (Rd x) (y x) i = 0))) hin hr

end Poly

end VB

end EthFollowup.ExactHC
