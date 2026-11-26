import MC222.Reduce

/-!
# The helper set (Lemmas 4.2, 4.5, 4.6 of the paper, in the form used here)

For a circuit `g` computing the targets put `U g i = S g i + T`.  A gate `g i ∉ U g i` is a
*helper*.  Since `dim (A + T) = 13` and `dim S g 6 ≤ 15`, and each helper raises `dim U` by one,
there are at most two helpers; the first gate `lin α * lin β` is always one (rank argument,
checked by `bv_decide`).  So all helpers lie in `{0, h}` for some `h ∈ {1..5}`, and every other
gate lies in `W g h i = A + T + span{g j : j ∈ {0, h}, j < i}`.
-/

namespace MC222

open Submodule

set_option maxHeartbeats 0

/-- The targets indexed by `ℕ`: `cN (2i+j) = c i j`. -/
def cN (t : Nat) : Fn := if h : t < 4 then c ⟨t / 2, by omega⟩ ⟨t % 2, by omega⟩ else 0

/-- Generators of `W g h i`: `1`, inputs, targets, gate 0 if `0 < i`, gate `h` if `h < i`. -/
def witGensF (g : Fin 6 → Fn) (h i j : Nat) : Fn :=
  if j = 0 then 1 else if j < 9 then xN (j - 1) else if j < 13 then cN (j - 9)
  else if j = 13 then (if 0 < i then gN g 0 else 0)
  else if j = 14 then (if h < i then gN g h else 0) else 0

/-- Generators of `S g 6`: `1`, inputs, gates. -/
def outGensF (g : Fin 6 → Fn) (j : Nat) : Fn :=
  if j = 0 then 1 else if j < 9 then xN (j - 1) else if j < 15 then gN g (j - 9) else 0

def W (g : Fin 6 → Fn) (h i : Nat) : Submodule (ZMod 2) Fn :=
  span (ZMod 2) (Set.range (fun j : Fin 16 => witGensF g h i j))

def Tsp : Submodule (ZMod 2) Fn := span (ZMod 2) (Set.range (fun t : Fin 4 => cN t))

def U (g : Fin 6 → Fn) (i : Nat) : Submodule (ZMod 2) Fn := S g i ⊔ Tsp

/-! ## Truth tables of the generators -/

/-- The gate truth tables as used by the cubes. -/
def GT (g : Fin 6 → Fn) : Nat → TT :=
  gv (tt (g 0)) (tt (g 1)) (tt (g 2)) (tt (g 3)) (tt (g 4)) (tt (g 5))

theorem GT_eq (g : Fin 6 → Fn) (j : Nat) : GT g j = tt (gN g j) := by
  rcases (show j < 6 ∨ 6 ≤ j by omega) with h | h
  · interval_cases j <;> rfl
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 6 := ⟨j - 6, by omega⟩
    simp [GT, gv, gN, tt_zero]

theorem tt_cN (t : Nat) : tt (cN t) = C t := by
  rcases (show t < 4 ∨ 4 ≤ t by omega) with h | h
  · interval_cases t <;> simp [cN, tt_c]
  · obtain ⟨k, rfl⟩ : ∃ k, t = k + 4 := ⟨t - 4, by omega⟩
    simp [cN, C, tt_zero]

theorem XG_eq (j : Nat) (h : j < 8) : XG j = X j := by simp [XG, h]

theorem tt_gateGensF (g : Fin 6 → Fn) (i j : Nat) :
    tt (gateGensF g i j) = gateGens (GT g) i j := by
  unfold gateGensF gateGens
  split_ifs with h1 h2
  · rw [tt_xN, XG_eq j h1]
  · rw [GT_eq]
  · exact tt_zero

theorem tt_witGensF (g : Fin 6 → Fn) (h i j : Nat) :
    tt (witGensF g h i j) = witGens (GT g) 0 h i j := by
  unfold witGensF witGens
  split_ifs <;> first
    | exact tt_one | exact tt_zero | rw [GT_eq] | rw [tt_cN]
    | (rw [tt_xN, XG_eq]; omega)

theorem tt_outGensF (g : Fin 6 → Fn) (j : Nat) : tt (outGensF g j) = outGens (GT g) j := by
  unfold outGensF outGens
  split_ifs <;> first
    | exact tt_one | exact tt_zero | rw [GT_eq]
    | (rw [tt_xN, XG_eq]; omega)

/-! ## Spaces -/

theorem cN_mem (g : Fin 6 → Fn) (hc : Computes g) (t : Nat) : cN t ∈ S g 6 := by
  unfold cN; split
  · exact hc _ _
  · exact zero_mem _

theorem Tsp_le (M : Submodule (ZMod 2) Fn) (h : ∀ t < 4, cN t ∈ M) : Tsp ≤ M :=
  span_le.mpr (by rintro f ⟨t, rfl⟩; exact h t t.isLt)

theorem witGensF_mem_W (g : Fin 6 → Fn) (h i : Nat) (j : Nat) (hj : j < 16) :
    witGensF g h i j ∈ W g h i := subset_span ⟨⟨j, hj⟩, rfl⟩

theorem W_mono (g : Fin 6 → Fn) (h : Nat) {i i' : Nat} (hi : i ≤ i') : W g h i ≤ W g h i' := by
  refine span_le.mpr ?_
  rintro f ⟨j, rfl⟩
  have hj := j.isLt
  by_cases e : witGensF g h i j = witGensF g h i' j
  · rw [e]; exact witGensF_mem_W g h i' j hj
  · -- only the gate generators can differ, and then the one for `i` is zero
    unfold witGensF at e ⊢
    split_ifs at e ⊢ <;> first | exact zero_mem _ | (exfalso; omega) | (exfalso; exact e rfl)

theorem gN_val (g : Fin 6 → Fn) (j : Fin 6) : gN g j.val = g j := by simp [gN, j.isLt]

/-- If every gate outside `{0, h}` lies in `U`, then `U g i ≤ W g h i` for all `i`. -/
theorem U_le_W (g : Fin 6 → Fn) (h : Nat)
    (hH : ∀ j : Fin 6, j.val ≠ 0 → j.val ≠ h → g j ∈ U g j) : ∀ i, U g i ≤ W g h i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  refine sup_le ?_ (Tsp_le _ fun t ht => ?_)
  · refine S_le g i _ ?_ (fun k => ?_) (fun j hj => ?_)
    · have := witGensF_mem_W g h i 0 (by omega); simpa [witGensF] using this
    · have := witGensF_mem_W g h i (k.val + 1) (by omega)
      simpa [witGensF, show k.val + 1 < 9 by omega, xN, k.isLt] using this
    · by_cases h0 : j.val = 0
      · have := witGensF_mem_W g h i 13 (by omega)
        have e : witGensF g h i 13 = g j := by
          simp [witGensF, show 0 < i by omega, ← h0, gN_val]
        rwa [e] at this
      by_cases hh : j.val = h
      · have := witGensF_mem_W g h i 14 (by omega)
        have e : witGensF g h i 14 = g j := by
          simp [witGensF, show h < i by omega, ← hh, gN_val]
        rwa [e] at this
      · exact W_mono g h (le_of_lt hj) (ih j.val hj (hH j h0 hh))
  · have := witGensF_mem_W g h i (9 + t) (by omega)
    simpa [witGensF, show 9 + t ≠ 0 by omega, show ¬ 9 + t < 9 by omega, show 9 + t < 13 by omega]
      using this

end MC222
