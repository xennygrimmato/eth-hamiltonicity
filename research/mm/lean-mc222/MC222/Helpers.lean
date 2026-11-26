import MC222.Reduce
import MC222.BVLemmas

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
  by_cases j0 : j = 0
  · simp only [j0, ite_true, tt_one]; rfl
  simp only [j0, ite_false]
  by_cases j9 : j < 9
  · simp only [j9, ite_true, tt_xN, XG_eq _ (show j - 1 < 8 by omega)]
  simp only [j9, ite_false]
  by_cases j13 : j < 13
  · simp only [j13, ite_true, tt_cN]
  simp only [j13, ite_false]
  by_cases j13' : j = 13
  · simp only [j13', ite_true]; split <;> simp [GT_eq, tt_zero]
  simp only [j13', ite_false]
  by_cases j14 : j = 14
  · simp only [j14, ite_true]; split <;> simp [GT_eq, tt_zero]
  simp only [j14, ite_false, tt_zero]; rfl

theorem tt_outGensF (g : Fin 6 → Fn) (j : Nat) : tt (outGensF g j) = outGens (GT g) j := by
  unfold outGensF outGens
  by_cases j0 : j = 0
  · simp only [j0, ite_true, tt_one]; rfl
  simp only [j0, ite_false]
  by_cases j9 : j < 9
  · simp only [j9, ite_true, tt_xN, XG_eq _ (show j - 1 < 8 by omega)]
  simp only [j9, ite_false]
  by_cases j15 : j < 15
  · simp only [j15, ite_true, GT_eq]
  simp only [j15, ite_false, tt_zero]; rfl

/-! ## Spaces -/

theorem cN_mem (g : Fin 6 → Fn) (hc : Computes g) (t : Nat) : cN t ∈ S g 6 := by
  unfold cN; split
  · exact hc _ _
  · exact zero_mem _

theorem Tsp_le (M : Submodule (ZMod 2) Fn) (h : ∀ t < 4, cN t ∈ M) : Tsp ≤ M :=
  span_le.mpr (by rintro f ⟨t, rfl⟩; exact h t t.isLt)

theorem witGensF_mem_W (g : Fin 6 → Fn) (h i : Nat) (j : Nat) (hj : j < 16) :
    witGensF g h i j ∈ W g h i := subset_span ⟨⟨j, hj⟩, rfl⟩

theorem witGensF_mono (g : Fin 6 → Fn) (h : Nat) {i i' : Nat} (hi : i ≤ i') (j : Nat) :
    witGensF g h i j = witGensF g h i' j ∨ witGensF g h i j = 0 := by
  unfold witGensF
  by_cases j0 : j = 0
  · left; simp [j0]
  by_cases j9 : j < 9
  · left; simp [j0, j9]
  by_cases j13 : j < 13
  · left; simp [j0, j9, j13]
  by_cases j13' : j = 13
  · by_cases h0 : 0 < i
    · left; simp [j13', h0, show 0 < i' by omega]
    · right; simp [j13', h0]
  by_cases j14 : j = 14
  · by_cases h0 : h < i
    · left; simp [j14, h0, show h < i' by omega]
    · right; simp [j14, h0]
  left; simp [j0, j9, j13, j13', j14]

theorem W_mono (g : Fin 6 → Fn) (h : Nat) {i i' : Nat} (hi : i ≤ i') : W g h i ≤ W g h i' := by
  refine span_le.mpr ?_
  rintro f ⟨j, rfl⟩
  rcases witGensF_mono g h hi j with e | e
  · show witGensF g h i j ∈ W g h i'
    rw [e]; exact witGensF_mem_W g h i' j j.isLt
  · show witGensF g h i j ∈ W g h i'
    rw [e]; exact zero_mem _

theorem gN_val (g : Fin 6 → Fn) (j : Fin 6) : gN g j.val = g j := by simp [gN, j.isLt]

/-- If every gate before `i` outside `{0, h}` lies in `U`, then `U g i ≤ W g h i`. -/
theorem U_le_W (g : Fin 6 → Fn) (h : Nat) : ∀ i,
    (∀ j : Fin 6, j.val < i → j.val ≠ 0 → j.val ≠ h → g j ∈ U g j) → U g i ≤ W g h i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hH
  refine sup_le ?_ (Tsp_le _ fun t ht => ?_)
  · refine S_le g i _ ?_ (fun k => ?_) (fun j hj => ?_)
    · have := witGensF_mem_W g h i 0 (by omega); simpa [witGensF] using this
    · have := witGensF_mem_W g h i (k.val + 1) (by omega)
      simpa [witGensF, show k.val + 1 < 9 by omega, xN, k.isLt] using this
    · by_cases h0 : j.val = 0
      · have := witGensF_mem_W g h i 13 (by omega)
        have e : witGensF g h i 13 = g j := by
          rw [← gN_val g j, h0]; simp [witGensF, show 0 < i by omega]
        rwa [e] at this
      by_cases hh : j.val = h
      · have := witGensF_mem_W g h i 14 (by omega)
        have e : witGensF g h i 14 = g j := by
          rw [← gN_val g j, hh]; simp [witGensF, show h < i by omega]
        rwa [e] at this
      · exact W_mono g h (le_of_lt hj)
          (ih j.val hj (fun j' hj' => hH j' (lt_trans hj' hj)) (hH j hj h0 hh))
  · have := witGensF_mem_W g h i (9 + t) (by omega)
    simpa [witGensF, show 9 + t ≠ 0 by omega, show ¬ 9 + t < 9 by omega, show 9 + t < 13 by omega]
      using this

/-! ## Dimension count -/

theorem U_mono (g : Fin 6 → Fn) {i i' : Nat} (h : i ≤ i') : U g i ≤ U g i' :=
  sup_le_sup_right (S_mono g h) _

theorem W0_le_U0 (g : Fin 6 → Fn) (h : Nat) : W g h 0 ≤ U g 0 := by
  refine span_le.mpr ?_
  rintro f ⟨j, rfl⟩
  show witGensF g h 0 j ∈ U g 0
  unfold witGensF
  by_cases j0 : j.val = 0
  · simp only [j0, ite_true]; exact le_sup_left (a := S g 0) (one_mem_S g 0)
  simp only [j0, ite_false]
  by_cases j9 : j.val < 9
  · simp only [j9, ite_true]; exact le_sup_left (a := S g 0) (xN_mem_S g 0 _)
  simp only [j9, ite_false]
  by_cases j13 : j.val < 13
  · simp only [j13, ite_true]
    exact le_sup_right (b := Tsp) (by
      unfold cN; split
      · next hh => exact subset_span ⟨⟨j.val - 9, hh⟩, by simp [cN, hh]⟩
      · exact zero_mem _)
  simp only [j13, ite_false, Nat.lt_irrefl, Nat.not_lt_zero, ite_self]; exact zero_mem _

theorem U0_le_W0 (g : Fin 6 → Fn) (h : Nat) : U g 0 ≤ W g h 0 :=
  U_le_W g h 0 (fun j hj => absurd hj (Nat.not_lt_zero _))

theorem sum13_eq_combF (e : Fin 13 → ZMod 2) (v : Nat → Fn) :
    ∑ i : Fin 13, e i • v i =
      combF (ofPred 16 (fun j => if h : j < 13 then decide (e ⟨j, h⟩ = 1) else false)) v := by
  have h1 : ∑ i : Fin 13, e i • v i =
      ∑ i ∈ Finset.range 13, (if h : i < 13 then e ⟨i, h⟩ • v i else 0) := by
    rw [Finset.sum_range]; exact Finset.sum_congr rfl fun i _ => by simp [i.isLt]
  rw [h1, combF]
  conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [getLsbD_ofPred, show ¬ (13 < 13) by omega, show ¬ (14 < 13) by omega, show ¬ (15 < 13) by omega,
    dite_false, Bool.and_false, Bool.false_eq_true, ite_false, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < 13 := Finset.mem_range.mp hi
  simp only [hi', dite_true, show i < 16 by omega, decide_true, Bool.true_and]
  exact zmod_smul_eq _ _

theorem finrank_U0 (g : Fin 6 → Fn) : 13 ≤ Module.finrank (ZMod 2) (U g 0) := by
  let v : Fin 13 → Fn := fun j => witGensF g 0 0 j
  have hli : LinearIndependent (ZMod 2) v := by
    refine Fintype.linearIndependent_iff.mpr fun e he j => ?_
    rw [sum13_eq_combF] at he
    have h2 := congrArg tt he
    rw [tt_combF, tt_zero] at h2
    simp only [tt_witGensF] at h2
    have h3 := congrArg (fun w => BitVec.getLsbD w j.val) (AT_indep (GT g) 0 _ h2)
    have z : BitVec.getLsbD (0 : BitVec 16) j.val = false := by simp
    simp only [BitVec.getLsbD_and, getLsbD_ofPred, z] at h3
    have hj := j.isLt
    have h8191 : (8191#16).getLsbD j.val = true := by
      revert hj; generalize j.val = n; intro hn; interval_cases n <;> decide
    simp only [h8191, show j.val < 16 by omega, decide_true, Bool.true_and, Bool.and_true,
      j.isLt, dite_true, Fin.eta, decide_eq_false_iff_not] at h3
    rcases zmod2_cases (e j) with h | h
    · exact h
    · exact absurd h h3
  have hle : Submodule.span (ZMod 2) (Set.range v) ≤ U g 0 :=
    le_trans (span_le.mpr (by rintro f ⟨j, rfl⟩; exact witGensF_mem_W g 0 0 j (by omega)))
      (W0_le_U0 g 0)
  calc 13 = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) := by
        rw [finrank_span_eq_card hli]; simp
    _ ≤ _ := Submodule.finrank_mono hle

theorem finrank_U6 (g : Fin 6 → Fn) (hc : Computes g) : Module.finrank (ZMod 2) (U g 6) ≤ 15 := by
  let v : Fin 15 → Fn := fun j => outGensF g j
  have hS : S g 6 ≤ Submodule.span (ZMod 2) (Set.range v) :=
    S_le g 6 (Submodule.span (ZMod 2) (Set.range v)) (subset_span ⟨⟨0, by omega⟩, by simp [v, outGensF]⟩)
      (fun k => subset_span ⟨⟨k.val + 1, by omega⟩, by
        simp [v, outGensF, show k.val + 1 < 9 by omega, xN, k.isLt]⟩)
      (fun i _ => subset_span ⟨⟨i.val + 9, by omega⟩, by
        simp [v, outGensF, show ¬ i.val + 9 < 9 by omega, gN_val]⟩)
  have hle : U g 6 ≤ Submodule.span (ZMod 2) (Set.range v) :=
    sup_le hS (Tsp_le _ fun t _ => hS (cN_mem g hc t))
  calc Module.finrank (ZMod 2) (U g 6) ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin 15) := finrank_range_le_card v
    _ = 15 := by simp

theorem finrank_step (g : Fin 6 → Fn) (i : Fin 6) (hi : g i ∉ U g i) :
    Module.finrank (ZMod 2) (U g i) < Module.finrank (ZMod 2) (U g (i.val + 1)) := by
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (U_mono g (Nat.le_succ _)) ?_)
  intro e
  exact hi (e ▸ (le_sup_left : S g (i.val + 1) ≤ U g (i.val + 1)) (g_mem_S g i (Nat.lt_succ_self _)))

theorem finrank_U_mono (g : Fin 6 → Fn) {i i' : Nat} (h : i ≤ i') :
    Module.finrank (ZMod 2) (U g i) ≤ Module.finrank (ZMod 2) (U g i') :=
  Submodule.finrank_mono (U_mono g h)

/-- At most two helpers: if gate 0 and two further gates are helpers, the dimension of `U`
would exceed 15. -/
theorem three_helpers_false (g : Fin 6 → Fn) (hc : Computes g) (h0 : g 0 ∉ U g 0) (a b : Fin 6)
    (ha : 0 < a.val) (hab : a.val < b.val) (hga : g a ∉ U g a) (hgb : g b ∉ U g b) : False := by
  have e0 := finrank_U0 g
  have e1 := finrank_step g 0 h0
  have e2 := finrank_U_mono g (show 0 + 1 ≤ a.val by omega)
  have e3 := finrank_step g a hga
  have e4 := finrank_U_mono g (show a.val + 1 ≤ b.val by omega)
  have e5 := finrank_step g b hgb
  have e6 := finrank_U_mono g (show b.val + 1 ≤ 6 by omega)
  have e7 := finrank_U6 g hc
  simp only [Fin.val_zero] at e1
  omega

theorem lin_eq_comb (a : BitVec 16) (G : Nat → TT) : tt (lin a) = comb a (gateGens G 0) := by
  rw [tt_lin]; congr 1; funext j; by_cases h : j < 8 <;> simp [XG, gateGens, h]

/-- The first gate is a helper. -/
theorem first_not_U (g : Fin 6 → Fn) (α β : BitVec 16) (h1 : α &&& 255#16 ≠ 0)
    (h2 : β &&& 255#16 ≠ 0) (h3 : α &&& 255#16 ≠ β &&& 255#16) (h0 : g 0 = lin α * lin β) :
    g 0 ∉ U g 0 := by
  intro hm
  obtain ⟨w, hw⟩ := exists_combF (U0_le_W0 g 0 hm)
  have := congrArg tt hw
  rw [h0, tt_mul, lin_eq_comb α (GT g), lin_eq_comb β (GT g), tt_combF] at this
  simp only [tt_witGensF] at this
  exact first_helper (GT g) 0 α β w h1 h2 h3 this

/-- The helper set: all helpers lie in `{0, h}` for some `1 ≤ h ≤ 5`. -/
theorem helper_set (g : Fin 6 → Fn) (hc : Computes g) (α β : BitVec 16) (h1 : α &&& 255#16 ≠ 0)
    (h2 : β &&& 255#16 ≠ 0) (h3 : α &&& 255#16 ≠ β &&& 255#16) (h0 : g 0 = lin α * lin β) :
    ∃ h, 1 ≤ h ∧ h ≤ 5 ∧ ∀ j : Fin 6, j.val ≠ 0 → j.val ≠ h → g j ∈ U g j := by
  have hf := first_not_U g α β h1 h2 h3 h0
  by_contra hne
  push Not at hne
  obtain ⟨a, ha0, -, ha⟩ := hne 1 le_rfl (by omega)
  obtain ⟨b, hb0, hba, hb⟩ := hne a.val (by omega) (by omega)
  rcases lt_or_gt_of_ne hba with hlt | hlt
  · exact three_helpers_false g hc hf b a (by omega) hlt hb ha
  · exact three_helpers_false g hc hf a b (by omega) hlt ha hb

end MC222
