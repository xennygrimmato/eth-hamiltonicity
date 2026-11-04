/-
# ArithL, module 2b: wires, vertices, ends, clusters, checks, the canonical run

Template: `ModP/ArithParams.lean`, with every object (variable, product, chain, comparison) at its
level (`ArithLDesc`, shapes `ArithLShape`). Layout: kinds `κ` of objects `o`, each with its own box
(`LB.lay`, flattened into `ModP.Blocks`).

For a leveled description `L` at top length `n`:
* variable `v` has limbs `L v i`, `i < ℓ_{lv v}`;
* product `p` (level `k = lp p`) has operand copies `R p σ i` (`i < ℓ_k`), row/column transforms
  `A`, `F`, products `C`, inverse columns `Dd`, inverse rows `E`, all at shape `k`;
* chain `c` has offset carries `rr c j` (`j + 1 < Kc_{lc c}`), comparison `q` has states `st q j`;
* vertices: cells `cell k i` (level `k`, limb `i < ℓ_k`), `row p σ i2`, `col p σ s`, `mul p s t`,
  `icol p s`, `irow p u`, `carry c k`.
The copy `R p σ i` of a variable operand `w` is checked at `cell (lv w) i` if `i < ℓ_{lv w}`, and
against `0` (or a constant limb) at `cell (lp p) i` otherwise.

Standard axioms only.
-/
import EthFollowup.Primes.ArithLShape
import Mathlib.Tactic.IntervalCases

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Finset EthFollowup.Factoring EthFollowup.ModP EthFollowup.Factoring.MP

/-! ## Two-level layouts -/

namespace LB

/-- Kinds `κ` with `nO[κ]` objects, object `o` of kind `κ` with the box `bx κ o`. -/
def lay : List ℕ → (ℕ → ℕ → List ℕ) → List (List ℕ)
  | [], _ => []
  | c :: cs, bx => (List.range c).map (bx 0) ++ lay cs fun κ => bx (κ + 1)

/-- The family index of object `o` of kind `κ`. -/
def fidx (nO : List ℕ) (κ o : ℕ) : ℕ := Blocks.off nO κ + o

theorem length_lay : ∀ (nO : List ℕ) (bx : ℕ → ℕ → List ℕ), (lay nO bx).length = nO.sum
  | [], _ => rfl
  | c :: cs, bx => by simp [lay, length_lay cs]

theorem getD_lay : ∀ {nO : List ℕ} {bx : ℕ → ℕ → List ℕ} {κ o : ℕ}, o < nO.getD κ 0 →
    (lay nO bx).getD (fidx nO κ o) [] = bx κ o
  | [], _, _, _, h => by simp at h
  | c :: cs, bx, 0, o, h => by
    simp only [List.getD_cons_zero] at h
    simp only [lay, fidx, Blocks.off_zero, zero_add]
    rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  | c :: cs, bx, κ + 1, o, h => by
    simp only [List.getD_cons_succ] at h
    simp only [lay, fidx, Blocks.off_cons_succ]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_map, List.length_range]; omega),
      List.length_map, List.length_range,
      show c + Blocks.off cs κ + o - c = Blocks.off cs κ + o by omega]
    exact getD_lay (bx := fun κ => bx (κ + 1)) h

theorem fidx_lt {nO : List ℕ} {κ o : ℕ} (h : o < nO.getD κ 0) : fidx nO κ o < nO.sum :=
  Blocks.off_add_lt h

theorem fam_fidx {nO : List ℕ} {κ o : ℕ} (h : o < nO.getD κ 0) : Blocks.fam nO (fidx nO κ o) = κ :=
  Blocks.fam_off_add h

theorem loc_fidx {nO : List ℕ} {κ o : ℕ} (h : o < nO.getD κ 0) : Blocks.loc nO (fidx nO κ o) = o :=
  Blocks.loc_off_add h

theorem fidx_fam_loc (nO : List ℕ) (f : ℕ) : fidx nO (Blocks.fam nO f) (Blocks.loc nO f) = f :=
  Blocks.off_fam_add_loc nO f

end LB

/-- Lists of length `0 … 4` from their entries. -/
theorem list_eq0 {xs : List ℕ} (h : xs.length = 0) : [] = xs := by match xs, h with | [], _ => rfl

/-! ## Wires -/

/-- The wires of ArithL (object first, then coordinates). -/
inductive AWL where
  | L (v i : ℕ)
  | R (p σ i : ℕ)
  | A (p σ s i2 : ℕ)
  | F (p σ s t : ℕ)
  | C (p s t : ℕ)
  | Dd (p s u : ℕ)
  | E (p a u : ℕ)
  | rr (c j : ℕ)
  | st (q j : ℕ)
  deriving DecidableEq

def AWL.kind : AWL → ℕ
  | .L .. => 0 | .R .. => 1 | .A .. => 2 | .F .. => 3 | .C .. => 4 | .Dd .. => 5 | .E .. => 6
  | .rr .. => 7 | .st .. => 8

def AWL.obj : AWL → ℕ
  | .L v _ => v | .R p _ _ => p | .A p _ _ _ => p | .F p _ _ _ => p | .C p _ _ => p
  | .Dd p _ _ => p | .E p _ _ => p | .rr c _ => c | .st q _ => q

def AWL.co : AWL → List ℕ
  | .L _ i => [i]
  | .R _ σ i => [σ, i]
  | .A _ σ s i2 => [σ, s, i2]
  | .F _ σ s t => [σ, s, t]
  | .C _ s t => [s, t]
  | .Dd _ s u => [s, u]
  | .E _ a u => [a, u]
  | .rr _ j => [j]
  | .st _ j => [j]

def AWL.mk (κ o : ℕ) (xs : List ℕ) : AWL :=
  match κ with
  | 0 => .L o (xs.getD 0 0)
  | 1 => .R o (xs.getD 0 0) (xs.getD 1 0)
  | 2 => .A o (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0)
  | 3 => .F o (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0)
  | 4 => .C o (xs.getD 0 0) (xs.getD 1 0)
  | 5 => .Dd o (xs.getD 0 0) (xs.getD 1 0)
  | 6 => .E o (xs.getD 0 0) (xs.getD 1 0)
  | 7 => .rr o (xs.getD 0 0)
  | _ => .st o (xs.getD 0 0)

theorem AWL.mk_kind_obj_co (d : AWL) : AWL.mk d.kind d.obj d.co = d := by cases d <;> rfl

/-- The numbers of objects of the wire kinds. -/
def wObj (L : LDesc) : List ℕ :=
  [L.D.nV, L.D.nP, L.D.nP, L.D.nP, L.D.nP, L.D.nP, L.D.nP, L.D.nC, L.D.nQ]

/-- The box of object `o` of wire kind `κ`. -/
def wBox (n : ℕ) (L : LDesc) (κ o : ℕ) : List ℕ :=
  match κ with
  | 0 => [kl n (L.lv o)]
  | 1 => [2, kl n (L.lp o)]
  | 2 => [2, kL1 n (L.lp o), kl1 n (L.lp o)]
  | 3 => [2, kL1 n (L.lp o), kL1 n (L.lp o)]
  | 4 => [kL1 n (L.lp o), kL1 n (L.lp o)]
  | 5 => [kL1 n (L.lp o), kL1 n (L.lp o)]
  | 6 => [kL1 n (L.lp o), kL1 n (L.lp o)]
  | 7 => [kKc n (L.lc o) - 1]
  | _ => [kl n (L.lq o) - 1]

/-- The wire layout. -/
def wLay (n : ℕ) (L : LDesc) : List (List ℕ) := LB.lay (wObj L) (wBox n L)

theorem AWL.mk_spec {n : ℕ} {L : LDesc} {κ o : ℕ} {xs : List ℕ} {d : AWL} (hκ : κ < 9)
    (hl : xs.length = (wBox n L κ o).length) :
    AWL.mk κ o xs = d → d.kind = κ ∧ d.obj = o ∧ d.co = xs := by
  rintro rfl
  interval_cases κ <;> simp only [wBox, List.length_cons, List.length_nil] at hl <;>
    simp only [AWL.mk, AWL.kind, AWL.obj, AWL.co, true_and]
  · exact list_eq1 hl
  · exact list_eq2 hl
  · exact list_eq3 hl
  · exact list_eq3 hl
  · exact list_eq2 hl
  · exact list_eq2 hl
  · exact list_eq2 hl
  · exact list_eq1 hl
  · exact list_eq1 hl

theorem AWL.kind_lt (d : AWL) : d.kind < 9 := by cases d <;> simp [AWL.kind]

/-- The index ranges of the wires. -/
def AWL.Valid (n : ℕ) (L : LDesc) (d : AWL) : Prop :=
  d.obj < (wObj L).getD d.kind 0 ∧ Blocks.InBox (wBox n L d.kind d.obj) d.co

instance (n : ℕ) (L : LDesc) : DecidablePred (AWL.Valid n L) := fun d => by
  unfold AWL.Valid; infer_instance

section ValidW
variable {n : ℕ} {L : LDesc}
@[simp] theorem valid_L {v i : ℕ} : (AWL.L v i).Valid n L ↔ v < L.D.nV ∧ i < kl n (L.lv v) := by
  simp [AWL.Valid, wObj, wBox, AWL.kind, AWL.obj, AWL.co]
@[simp] theorem valid_R {p σ i : ℕ} : (AWL.R p σ i).Valid n L ↔ p < L.D.nP ∧ σ < 2 ∧ i < kl n (L.lp p) := by
  simp [AWL.Valid, wObj, wBox, AWL.kind, AWL.obj, AWL.co]
@[simp] theorem valid_A {p σ s i2 : ℕ} : (AWL.A p σ s i2).Valid n L ↔
    p < L.D.nP ∧ σ < 2 ∧ s < kL1 n (L.lp p) ∧ i2 < kl1 n (L.lp p) := by
  simp [AWL.Valid, wObj, wBox, AWL.kind, AWL.obj, AWL.co]
@[simp] theorem valid_F {p σ s t : ℕ} : (AWL.F p σ s t).Valid n L ↔
    p < L.D.nP ∧ σ < 2 ∧ s < kL1 n (L.lp p) ∧ t < kL1 n (L.lp p) := by
  simp [AWL.Valid, wObj, wBox, AWL.kind, AWL.obj, AWL.co]
@[simp] theorem valid_C {p s t : ℕ} : (AWL.C p s t).Valid n L ↔
    p < L.D.nP ∧ s < kL1 n (L.lp p) ∧ t < kL1 n (L.lp p) := by
  simp [AWL.Valid, wObj, wBox, AWL.kind, AWL.obj, AWL.co]
@[simp] theorem valid_Dd {p s u : ℕ} : (AWL.Dd p s u).Valid n L ↔
    p < L.D.nP ∧ s < kL1 n (L.lp p) ∧ u < kL1 n (L.lp p) := by
  simp [AWL.Valid, wObj, wBox, AWL.kind, AWL.obj, AWL.co]
@[simp] theorem valid_E {p a u : ℕ} : (AWL.E p a u).Valid n L ↔
    p < L.D.nP ∧ a < kL1 n (L.lp p) ∧ u < kL1 n (L.lp p) := by
  simp [AWL.Valid, wObj, wBox, AWL.kind, AWL.obj, AWL.co]
@[simp] theorem valid_rr {c j : ℕ} : (AWL.rr c j).Valid n L ↔ c < L.D.nC ∧ j + 1 < kKc n (L.lc c) := by
  simp only [AWL.Valid, wObj, wBox, AWL.kind, AWL.obj, AWL.co, List.getD_cons_succ, List.getD_cons_zero,
    Blocks.inBox_cons, Blocks.inBox_nil, and_true]
  have := one_le_kKc n (L.lc c); omega
@[simp] theorem valid_st {q j : ℕ} : (AWL.st q j).Valid n L ↔ q < L.D.nQ ∧ j + 1 < kl n (L.lq q) := by
  simp only [AWL.Valid, wObj, wBox, AWL.kind, AWL.obj, AWL.co, List.getD_cons_succ, List.getD_cons_zero,
    Blocks.inBox_cons, Blocks.inBox_nil, and_true]
  have := kl_pos n (L.lq q); omega
end ValidW

/-- The number of wires. -/
def numAW (n : ℕ) (L : LDesc) : ℕ := Blocks.total (wLay n L)
/-- The index of a wire. -/
def awIdx (n : ℕ) (L : LDesc) (d : AWL) : ℕ := Blocks.idx (wLay n L) (LB.fidx (wObj L) d.kind d.obj) d.co
/-- The wire with a given index. -/
def awOf (n : ℕ) (L : LDesc) (j : ℕ) : AWL :=
  AWL.mk (Blocks.fam (wObj L) (Blocks.fOf (wLay n L) j)) (Blocks.loc (wObj L) (Blocks.fOf (wLay n L) j))
    (Blocks.cOf (wLay n L) j)

theorem valid_blocks_w {n : ℕ} {L : LDesc} {d : AWL} (hd : d.Valid n L) :
    Blocks.Valid (wLay n L) (LB.fidx (wObj L) d.kind d.obj) d.co := by
  refine ⟨?_, ?_⟩
  · rw [wLay, LB.length_lay]; exact LB.fidx_lt hd.1
  · rw [wLay, LB.getD_lay hd.1]; exact hd.2

theorem awIdx_lt {n : ℕ} {L : LDesc} {d : AWL} (hd : d.Valid n L) : awIdx n L d < numAW n L :=
  Blocks.idx_lt (valid_blocks_w hd)

theorem awOf_awIdx {n : ℕ} {L : LDesc} {d : AWL} (hd : d.Valid n L) : awOf n L (awIdx n L d) = d := by
  unfold awOf awIdx
  rw [Blocks.fOf_idx (valid_blocks_w hd), Blocks.cOf_idx (valid_blocks_w hd), LB.fam_fidx hd.1,
    LB.loc_fidx hd.1, AWL.mk_kind_obj_co]

theorem awOf_spec {n : ℕ} {L : LDesc} {j : ℕ} (hj : j < numAW n L) :
    (awOf n L j).kind = Blocks.fam (wObj L) (Blocks.fOf (wLay n L) j) ∧
    (awOf n L j).obj = Blocks.loc (wObj L) (Blocks.fOf (wLay n L) j) ∧
    (awOf n L j).co = Blocks.cOf (wLay n L) j := by
  have hf : Blocks.fOf (wLay n L) j < (wObj L).sum := by
    have := Blocks.fOf_lt hj; rwa [wLay, LB.length_lay] at this
  have hκ := Blocks.fam_lt hf
  have ho := Blocks.loc_lt hf
  refine AWL.mk_spec (n := n) (L := L) (by have h9 : (wObj L).length = 9 := rfl; omega) ?_ rfl
  have e := LB.getD_lay (bx := wBox n L) ho
  rw [LB.fidx_fam_loc] at e
  rw [Blocks.length_cOf, show (wLay n L).getD (Blocks.fOf (wLay n L) j) [] = _ from e]

theorem awOf_valid {n : ℕ} {L : LDesc} {j : ℕ} (hj : j < numAW n L) : (awOf n L j).Valid n L := by
  obtain ⟨h1, h2, h3⟩ := awOf_spec hj
  have hv := Blocks.valid_fOf_cOf hj
  have hf : Blocks.fOf (wLay n L) j < (wObj L).sum := by
    have := Blocks.fOf_lt hj; rwa [wLay, LB.length_lay] at this
  have ho := Blocks.loc_lt hf
  refine ⟨by rw [h1, h2]; exact ho, ?_⟩
  rw [h1, h2, h3]
  have e := LB.getD_lay (bx := wBox n L) ho
  rw [LB.fidx_fam_loc] at e
  rw [← e]; exact hv.2

theorem awIdx_awOf {n : ℕ} {L : LDesc} {j : ℕ} (hj : j < numAW n L) : awIdx n L (awOf n L j) = j := by
  obtain ⟨h1, h2, h3⟩ := awOf_spec hj
  unfold awIdx; rw [h1, h2, h3, LB.fidx_fam_loc]; exact Blocks.idx_fOf_cOf hj

/-! ## Vertices -/

/-- The vertices (checks) of ArithL. -/
inductive AVL where
  | cell (k i : ℕ)
  | row (p σ i2 : ℕ)
  | col (p σ s : ℕ)
  | mul (p s t : ℕ)
  | icol (p s : ℕ)
  | irow (p u : ℕ)
  | carry (c k : ℕ)
  deriving DecidableEq

def AVL.kind : AVL → ℕ
  | .cell .. => 0 | .row .. => 1 | .col .. => 2 | .mul .. => 3 | .icol .. => 4 | .irow .. => 5
  | .carry .. => 6

def AVL.obj : AVL → ℕ
  | .cell k _ => k | .row p _ _ => p | .col p _ _ => p | .mul p _ _ => p | .icol p _ => p
  | .irow p _ => p | .carry c _ => c

def AVL.co : AVL → List ℕ
  | .cell _ i => [i]
  | .row _ σ i2 => [σ, i2]
  | .col _ σ s => [σ, s]
  | .mul _ s t => [s, t]
  | .icol _ s => [s]
  | .irow _ u => [u]
  | .carry _ k => [k]

def AVL.mk (κ o : ℕ) (xs : List ℕ) : AVL :=
  match κ with
  | 0 => .cell o (xs.getD 0 0)
  | 1 => .row o (xs.getD 0 0) (xs.getD 1 0)
  | 2 => .col o (xs.getD 0 0) (xs.getD 1 0)
  | 3 => .mul o (xs.getD 0 0) (xs.getD 1 0)
  | 4 => .icol o (xs.getD 0 0)
  | 5 => .irow o (xs.getD 0 0)
  | _ => .carry o (xs.getD 0 0)

theorem AVL.mk_kind_obj_co (v : AVL) : AVL.mk v.kind v.obj v.co = v := by cases v <;> rfl

/-- The numbers of objects of the vertex kinds (cells: one object per level). -/
def vObj (L : LDesc) : List ℕ := [L.nL, L.D.nP, L.D.nP, L.D.nP, L.D.nP, L.D.nP, L.D.nC]

/-- The box of object `o` of vertex kind `κ`. -/
def vBox (n : ℕ) (L : LDesc) (κ o : ℕ) : List ℕ :=
  match κ with
  | 0 => [kl n o]
  | 1 => [2, kl1 n (L.lp o)]
  | 2 => [2, kL1 n (L.lp o)]
  | 3 => [kL1 n (L.lp o), kL1 n (L.lp o)]
  | 4 => [kL1 n (L.lp o)]
  | 5 => [kL1 n (L.lp o)]
  | _ => [kKc n (L.lc o)]

/-- The vertex layout. -/
def vLay (n : ℕ) (L : LDesc) : List (List ℕ) := LB.lay (vObj L) (vBox n L)

theorem AVL.mk_spec {n : ℕ} {L : LDesc} {κ o : ℕ} {xs : List ℕ} {v : AVL} (hκ : κ < 7)
    (hl : xs.length = (vBox n L κ o).length) :
    AVL.mk κ o xs = v → v.kind = κ ∧ v.obj = o ∧ v.co = xs := by
  rintro rfl
  interval_cases κ <;> simp only [vBox, List.length_cons, List.length_nil] at hl <;>
    simp only [AVL.mk, AVL.kind, AVL.obj, AVL.co, true_and]
  · exact list_eq1 hl
  · exact list_eq2 hl
  · exact list_eq2 hl
  · exact list_eq2 hl
  · exact list_eq1 hl
  · exact list_eq1 hl
  · exact list_eq1 hl

theorem AVL.kind_lt (v : AVL) : v.kind < 7 := by cases v <;> simp [AVL.kind]

def AVL.Valid (n : ℕ) (L : LDesc) (v : AVL) : Prop :=
  v.obj < (vObj L).getD v.kind 0 ∧ Blocks.InBox (vBox n L v.kind v.obj) v.co

instance (n : ℕ) (L : LDesc) : DecidablePred (AVL.Valid n L) := fun v => by
  unfold AVL.Valid; infer_instance

section ValidV
variable {n : ℕ} {L : LDesc}
@[simp] theorem valid_cell {k i : ℕ} : (AVL.cell k i).Valid n L ↔ k < L.nL ∧ i < kl n k := by
  simp [AVL.Valid, vObj, vBox, AVL.kind, AVL.obj, AVL.co]
@[simp] theorem valid_row {p σ i2 : ℕ} : (AVL.row p σ i2).Valid n L ↔
    p < L.D.nP ∧ σ < 2 ∧ i2 < kl1 n (L.lp p) := by
  simp [AVL.Valid, vObj, vBox, AVL.kind, AVL.obj, AVL.co]
@[simp] theorem valid_col {p σ s : ℕ} : (AVL.col p σ s).Valid n L ↔
    p < L.D.nP ∧ σ < 2 ∧ s < kL1 n (L.lp p) := by
  simp [AVL.Valid, vObj, vBox, AVL.kind, AVL.obj, AVL.co]
@[simp] theorem valid_mul {p s t : ℕ} : (AVL.mul p s t).Valid n L ↔
    p < L.D.nP ∧ s < kL1 n (L.lp p) ∧ t < kL1 n (L.lp p) := by
  simp [AVL.Valid, vObj, vBox, AVL.kind, AVL.obj, AVL.co]
@[simp] theorem valid_icol {p s : ℕ} : (AVL.icol p s).Valid n L ↔ p < L.D.nP ∧ s < kL1 n (L.lp p) := by
  simp [AVL.Valid, vObj, vBox, AVL.kind, AVL.obj, AVL.co]
@[simp] theorem valid_irow {p u : ℕ} : (AVL.irow p u).Valid n L ↔ p < L.D.nP ∧ u < kL1 n (L.lp p) := by
  simp [AVL.Valid, vObj, vBox, AVL.kind, AVL.obj, AVL.co]
@[simp] theorem valid_carry {c k : ℕ} : (AVL.carry c k).Valid n L ↔ c < L.D.nC ∧ k < kKc n (L.lc c) := by
  simp [AVL.Valid, vObj, vBox, AVL.kind, AVL.obj, AVL.co]
end ValidV

def numAV (n : ℕ) (L : LDesc) : ℕ := Blocks.total (vLay n L)
def avIdx (n : ℕ) (L : LDesc) (v : AVL) : ℕ := Blocks.idx (vLay n L) (LB.fidx (vObj L) v.kind v.obj) v.co
def avOf (n : ℕ) (L : LDesc) (j : ℕ) : AVL :=
  AVL.mk (Blocks.fam (vObj L) (Blocks.fOf (vLay n L) j)) (Blocks.loc (vObj L) (Blocks.fOf (vLay n L) j))
    (Blocks.cOf (vLay n L) j)

theorem valid_blocks_v {n : ℕ} {L : LDesc} {v : AVL} (hv : v.Valid n L) :
    Blocks.Valid (vLay n L) (LB.fidx (vObj L) v.kind v.obj) v.co := by
  refine ⟨?_, ?_⟩
  · rw [vLay, LB.length_lay]; exact LB.fidx_lt hv.1
  · rw [vLay, LB.getD_lay hv.1]; exact hv.2

theorem avIdx_lt {n : ℕ} {L : LDesc} {v : AVL} (hv : v.Valid n L) : avIdx n L v < numAV n L :=
  Blocks.idx_lt (valid_blocks_v hv)

theorem avOf_avIdx {n : ℕ} {L : LDesc} {v : AVL} (hv : v.Valid n L) : avOf n L (avIdx n L v) = v := by
  unfold avOf avIdx
  rw [Blocks.fOf_idx (valid_blocks_v hv), Blocks.cOf_idx (valid_blocks_v hv), LB.fam_fidx hv.1,
    LB.loc_fidx hv.1, AVL.mk_kind_obj_co]

theorem avOf_spec {n : ℕ} {L : LDesc} {j : ℕ} (hj : j < numAV n L) :
    (avOf n L j).kind = Blocks.fam (vObj L) (Blocks.fOf (vLay n L) j) ∧
    (avOf n L j).obj = Blocks.loc (vObj L) (Blocks.fOf (vLay n L) j) ∧
    (avOf n L j).co = Blocks.cOf (vLay n L) j := by
  have hf : Blocks.fOf (vLay n L) j < (vObj L).sum := by
    have := Blocks.fOf_lt hj; rwa [vLay, LB.length_lay] at this
  have hκ := Blocks.fam_lt hf
  have ho := Blocks.loc_lt hf
  refine AVL.mk_spec (n := n) (L := L) (by have h9 : (vObj L).length = 7 := rfl; omega) ?_ rfl
  have e := LB.getD_lay (bx := vBox n L) ho
  rw [LB.fidx_fam_loc] at e
  rw [Blocks.length_cOf, show (vLay n L).getD (Blocks.fOf (vLay n L) j) [] = _ from e]

theorem avOf_valid {n : ℕ} {L : LDesc} {j : ℕ} (hj : j < numAV n L) : (avOf n L j).Valid n L := by
  obtain ⟨h1, h2, h3⟩ := avOf_spec hj
  have hv := Blocks.valid_fOf_cOf hj
  have hf : Blocks.fOf (vLay n L) j < (vObj L).sum := by
    have := Blocks.fOf_lt hj; rwa [vLay, LB.length_lay] at this
  have ho := Blocks.loc_lt hf
  refine ⟨by rw [h1, h2]; exact ho, ?_⟩
  rw [h1, h2, h3]
  have e := LB.getD_lay (bx := vBox n L) ho
  rw [LB.fidx_fam_loc] at e
  rw [← e]; exact hv.2

theorem avIdx_avOf {n : ℕ} {L : LDesc} {j : ℕ} (hj : j < numAV n L) : avIdx n L (avOf n L j) = j := by
  obtain ⟨h1, h2, h3⟩ := avOf_spec hj
  unfold avIdx; rw [h1, h2, h3, LB.fidx_fam_loc]; exact Blocks.idx_fOf_cOf hj

/-! ## The two ends of a wire -/

/-- The cell checking the copy `R p σ i`: the operand's own cell, or the product's cell (constant
operand, or limbs beyond the operand's level). -/
def cellR (n : ℕ) (L : LDesc) (p σ i : ℕ) : AVL :=
  match opnd L.D p σ with
  | .var w => if w < L.D.nV ∧ i < kl n (L.lv w) then .cell (L.lv w) i else .cell (L.lp p) i
  | .const _ => .cell (L.lp p) i

theorem cellR_valid {n : ℕ} {L : LDesc} {p σ i : ℕ} (hi : i < kl n (L.lp p)) :
    (cellR n L p σ i).Valid n L := by
  unfold cellR
  split
  · split_ifs with h
    · simp only [valid_cell]; exact ⟨L.lv_lt_nL _, h.2⟩
    · simp only [valid_cell]; exact ⟨L.lp_lt_nL _, hi⟩
  · simp only [valid_cell]; exact ⟨L.lp_lt_nL _, hi⟩

theorem cellR_eq (n : ℕ) (L : LDesc) (p σ i : ℕ) : ∃ k, cellR n L p σ i = .cell k i := by
  unfold cellR; split
  · split_ifs
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The two vertices a wire joins. -/
def aEnds (n : ℕ) (L : LDesc) : AWL → AVL × AVL
  | .L v i => (.cell (L.lv v) i, .cell (L.lv v) i)
  | .R p σ i => (cellR n L p σ i, .row p σ (i / kl1 n (L.lp p)))
  | .A p σ s i2 => (.row p σ i2, .col p σ s)
  | .F p σ s t => (.col p σ s, .mul p s t)
  | .C p s t => (.mul p s t, .icol p s)
  | .Dd p s u => (.icol p s, .irow p u)
  | .E p a u => if L.D.chainOf p < L.D.nC then (.irow p u, .carry (L.D.chainOf p) (a + kl1 n (L.lp p) * u))
      else (.irow p u, .irow p u)
  | .rr c j => (.carry c j, .carry c (j + 1))
  | .st q j => (.cell (L.lq q) (j + 1), .cell (L.lq q) j)

theorem aEnds_valid {n : ℕ} {L : LDesc} {d : AWL} (hd : d.Valid n L) :
    (aEnds n L d).1.Valid n L ∧ (aEnds n L d).2.Valid n L := by
  cases d with
  | L v i => simp only [valid_L] at hd; simp [aEnds, hd.2, L.lv_lt_nL]
  | R p σ i =>
    simp only [valid_R] at hd
    refine ⟨cellR_valid hd.2.2, ?_⟩
    simp only [aEnds, valid_row]
    exact ⟨hd.1, hd.2.1, (blk_dec (w := kl1 n (L.lp p)) (h := kl1 n (L.lp p)) hd.2.2).2⟩
  | A p σ s i2 => simp only [valid_A] at hd; simp only [aEnds, valid_row, valid_col]; omega
  | F p σ s t => simp only [valid_F] at hd; simp only [aEnds, valid_col, valid_mul]; omega
  | C p s t => simp only [valid_C] at hd; simp only [aEnds, valid_mul, valid_icol]; omega
  | Dd p s u => simp only [valid_Dd] at hd; simp only [aEnds, valid_icol, valid_irow]; omega
  | E p a u =>
    simp only [valid_E] at hd
    simp only [aEnds]
    split_ifs with h
    · simp only [valid_irow, valid_carry]
      exact ⟨⟨hd.1, hd.2.2⟩, h, Cc_pos_lt' n _ hd.2.1 hd.2.2⟩
    · simp only [valid_irow]; exact ⟨⟨hd.1, hd.2.2⟩, hd.1, hd.2.2⟩
  | rr c j => simp only [valid_rr] at hd; simp only [aEnds, valid_carry]; omega
  | st q j =>
    simp only [valid_st] at hd; simp only [aEnds, valid_cell]
    exact ⟨⟨L.lq_lt_nL _, hd.2⟩, L.lq_lt_nL _, by omega⟩

/-- Wire `d` is incident to vertex `v`. -/
def AWInc (n : ℕ) (L : LDesc) (v : AVL) (d : AWL) : Prop := (aEnds n L d).1 = v ∨ (aEnds n L d).2 = v

/-! ## Clusters -/

/-- The stage of a vertex: its family (one per object and kind). -/
def AVL.stage (L : LDesc) (v : AVL) : ℕ := LB.fidx (vObj L) v.kind v.obj
/-- The index of a vertex within its stage. -/
def AVL.idx (n : ℕ) (L : LDesc) (v : AVL) : ℕ := Blocks.enc (vBox n L v.kind v.obj) v.co
/-- The number of vertices of a stage. -/
def stSz (n : ℕ) (L : LDesc) (st : ℕ) : ℕ := (Blocks.sizes (vLay n L)).getD st 0

theorem stSz_stage {n : ℕ} {L : LDesc} {v : AVL} (hv : v.Valid n L) :
    stSz n L (v.stage L) = (vBox n L v.kind v.obj).prod := by
  unfold stSz AVL.stage
  rw [Blocks.sizes_getD (valid_blocks_v hv).1, vLay, LB.getD_lay hv.1]

theorem AVL.idx_lt {n : ℕ} {L : LDesc} {v : AVL} (hv : v.Valid n L) : v.idx n L < stSz n L (v.stage L) := by
  rw [stSz_stage hv]; exact Blocks.enc_lt hv.2

theorem avIdx_eq {n : ℕ} {L : LDesc} {v : AVL} (hv : v.Valid n L) :
    avIdx n L v = Blocks.off (Blocks.sizes (vLay n L)) (v.stage L) + v.idx n L := by
  unfold avIdx AVL.stage AVL.idx Blocks.idx
  rw [vLay, LB.getD_lay hv.1]

theorem stage_lt {n : ℕ} {L : LDesc} {v : AVL} (hv : v.Valid n L) : v.stage L < (vObj L).sum :=
  LB.fidx_lt hv.1

/-- **The cluster of a vertex**: each stage cut into `g` contiguous blocks. -/
def aClus (n : ℕ) (L : LDesc) (g : ℕ) (v : AVL) : ℕ := ExactHC.VB.vbN (stSz n L (v.stage L)) g (v.idx n L)

theorem aClus_lt {n : ℕ} {L : LDesc} {g : ℕ} {v : AVL} (hv : v.Valid n L) (hg : 1 ≤ g) : aClus n L g v < g :=
  ExactHC.VB.vbN_lt (AVL.idx_lt hv) hg

def aLo (n : ℕ) (L : LDesc) (g : ℕ) (d : AWL) : ℕ :=
  (lohi g (aClus n L g (aEnds n L d).1) (aClus n L g (aEnds n L d).2)).1
def aHi (n : ℕ) (L : LDesc) (g : ℕ) (d : AWL) : ℕ :=
  (lohi g (aClus n L g (aEnds n L d).1) (aClus n L g (aEnds n L d).2)).2

theorem aLo_lt_aHi {n : ℕ} {L : LDesc} {g : ℕ} {d : AWL} (hd : d.Valid n L) (hg : 2 ≤ g) :
    aLo n L g d < aHi n L g d :=
  (lohi_lt (aClus_lt (aEnds_valid hd).1 (by omega)) (aClus_lt (aEnds_valid hd).2 (by omega)) hg).1

theorem aHi_lt {n : ℕ} {L : LDesc} {g : ℕ} {d : AWL} (hd : d.Valid n L) (hg : 2 ≤ g) : aHi n L g d < g :=
  (lohi_lt (aClus_lt (aEnds_valid hd).1 (by omega)) (aClus_lt (aEnds_valid hd).2 (by omega)) hg).2

theorem aLo_lt {n : ℕ} {L : LDesc} {g : ℕ} {d : AWL} (hd : d.Valid n L) (hg : 2 ≤ g) : aLo n L g d < g :=
  (aLo_lt_aHi hd hg).trans (aHi_lt hd hg)

theorem aClus_ends_mem (n : ℕ) (L : LDesc) (g : ℕ) (d : AWL) :
    (aClus n L g (aEnds n L d).1 = aLo n L g d ∨ aClus n L g (aEnds n L d).1 = aHi n L g d) ∧
      (aClus n L g (aEnds n L d).2 = aLo n L g d ∨ aClus n L g (aEnds n L d).2 = aHi n L g d) := by
  have h := lohi_mem g (aClus n L g (aEnds n L d).1) (aClus n L g (aEnds n L d).2)
  unfold aLo aHi
  exact ⟨h.1.imp Eq.symm Eq.symm, h.2.imp Eq.symm Eq.symm⟩

/-! ## The checks -/

/-- Limb `i` of operand `σ` of product `p`, as read at the copy's cell. -/
def opLimbR (n : ℕ) (L : LDesc) (x : AWL → ℕ) (p σ i : ℕ) : ℕ :=
  match opnd L.D p σ with
  | .var w => if w < L.D.nV ∧ i < kl n (L.lv w) then x (.L w i) else 0
  | .const l => l.getD i 0

/-- Limb `i` of a comparison operand at level `k` (only variables of level `k` are read). -/
def opLimbC (L : LDesc) (x : AWL → ℕ) (k : ℕ) : Operand → ℕ → ℕ
  | .var w, i => if w < L.D.nV ∧ L.lv w = k then x (.L w i) else 0
  | .const l, i => l.getD i 0

/-- The comparison step of comparison `q` at limb `i`. -/
def cmpOK (n : ℕ) (L : LDesc) (x : AWL → ℕ) (q i : ℕ) : Bool :=
  cmpCell (L.D.cq q).rel (kl n (L.lq q)) (opLimbC L x (L.lq q) (.var (L.D.cq q).v))
    (opLimbC L x (L.lq q) (L.D.cq q).rhs) (fun j => x (.st q j)) i

/-- **The check of cell `(k, i)`**: ranges and patterns of the level-`k` variables, the copies
checked here, the comparison steps of level `k`. -/
def cellOK (n : ℕ) (L : LDesc) (x : AWL → ℕ) (k i : ℕ) : Bool :=
  ((List.range L.D.nV).all fun v => !(decide (L.lv v = k)) ||
    (decide (x (.L v i) < 2 ^ b n) && patOK n (L.D.pat.getD v []) i (x (.L v i)))) &&
  ((List.range L.D.nP).all fun p => (List.range 2).all fun σ =>
    !(decide (i < kl n (L.lp p) ∧ cellR n L p σ i = .cell k i)) || x (.R p σ i) == opLimbR n L x p σ i) &&
  ((List.range L.D.nQ).all fun q => !(decide (L.lq q = k)) || cmpOK n L x q i)

/-- The digit of term `t` at position `k` of chain `c`. -/
def tDig (n : ℕ) (L : LDesc) (x : AWL → ℕ) (c : ℕ) (t : Term) (k : ℕ) : ℕ :=
  match t.src with
  | .prod p => if p < L.D.nP ∧ L.D.chainOf p = c then convE (kP n (L.lc c)) (fun a u => x (.E p a u)) k else 0
  | .lin _ => 0
  | .const l => l.getD k 0

/-- The digit of one side of chain `c` at position `k`. -/
def sDig (n : ℕ) (L : LDesc) (x : AWL → ℕ) (c : ℕ) (ts : List Term) (k : ℕ) : ℕ :=
  (ts.map fun t => t.coeff * tDig n L x c t k).sum

/-- **The check of a vertex** on the wire values `x`. -/
def aChk (n : ℕ) (L : LDesc) (x : AWL → ℕ) : AVL → Bool
  | .cell k i => cellOK n L x k i
  | .row p σ i2 => (List.range (kL1 n (L.lp p))).all fun s =>
      x (.A p σ s i2) == rowE (kP n (L.lp p)) (fun i1 i2 => x (.R p σ (i1 + kl1 n (L.lp p) * i2))) s i2
  | .col p σ s => (List.range (kL1 n (L.lp p))).all fun t =>
      x (.F p σ s t) == colE (kP n (L.lp p)) (fun s i2 => x (.A p σ s i2)) s t
  | .mul p s t => x (.C p s t) == x (.F p 0 s t) * x (.F p 1 s t) % M n
  | .icol p s => (List.range (kL1 n (L.lp p))).all fun u =>
      x (.Dd p s u) == invColE (kP n (L.lp p)) (fun s t => x (.C p s t)) s u
  | .irow p u => (List.range (kL1 n (L.lp p))).all fun a =>
      x (.E p a u) == invRowE (kP n (L.lp p)) (fun s u => x (.Dd p s u)) a u
  | .carry c k => decide (carryChk (b n) (kKc n (L.lc c)) (aOFF n) (sDig n L x c (L.D.ch c).lhs)
      (sDig n L x c (L.D.ch c).rhs) (fun j => x (.rr c j)) k)

/-! ## Locality -/

theorem opLimbC_congr {L : LDesc} {x x' : AWL → ℕ} {k i : ℕ} (o : Operand)
    (h : ∀ w < L.D.nV, L.lv w = k → x (.L w i) = x' (.L w i)) : opLimbC L x k o i = opLimbC L x' k o i := by
  cases o with
  | var w => simp only [opLimbC]; split_ifs with hw; exacts [h w hw.1 hw.2, rfl]
  | const l => rfl

theorem rowE_congr' (n k : ℕ) {x x' : ℕ → ℕ → ℕ} {i2 : ℕ} (h : ∀ i1 < kl1 n k, x i1 i2 = x' i1 i2) (s : ℕ) :
    rowE (kP n k) x s i2 = rowE (kP n k) x' s i2 := by
  have e : ((List.range (kl1 n k)).map fun i1 => x i1 i2 * wq (kP n k) (i1 * s)) =
      (List.range (kl1 n k)).map fun i1 => x' i1 i2 * wq (kP n k) (i1 * s) :=
    List.map_congr_left fun i1 hi1 => by rw [h i1 (List.mem_range.1 hi1)]
  unfold rowE; rw [kP_rl1, e]

theorem colE_congr' (n k : ℕ) {A A' : ℕ → ℕ → ℕ} {s : ℕ} (h : ∀ i2 < kl1 n k, A s i2 = A' s i2) (t : ℕ) :
    colE (kP n k) A s t = colE (kP n k) A' s t := by
  have e : ((List.range (kl1 n k)).map fun i2 => A s i2 * wq (kP n k) (i2 * t)) =
      (List.range (kl1 n k)).map fun i2 => A' s i2 * wq (kP n k) (i2 * t) :=
    List.map_congr_left fun i2 hi2 => by rw [h i2 (List.mem_range.1 hi2)]
  unfold colE; rw [kP_rl2, e]

theorem invColE_congr' (n k : ℕ) {C C' : ℕ → ℕ → ℕ} {s : ℕ} (h : ∀ t < kL1 n k, C s t = C' s t) (u : ℕ) :
    invColE (kP n k) C s u = invColE (kP n k) C' s u := by
  have e : ((List.range (kL1 n k)).map fun t => C s t * wq (kP n k) (((kP n k).L2 - u) * t)) =
      (List.range (kL1 n k)).map fun t => C' s t * wq (kP n k) (((kP n k).L2 - u) * t) :=
    List.map_congr_left fun t ht => by rw [h t (List.mem_range.1 ht)]
  unfold invColE; rw [kP_rL2, e]

theorem invRowE_congr' (n k : ℕ) {E E' : ℕ → ℕ → ℕ} {u : ℕ} (h : ∀ s < kL1 n k, E s u = E' s u) (a : ℕ) :
    invRowE (kP n k) E a u = invRowE (kP n k) E' a u := by
  have e : ((List.range (kL1 n k)).map fun s => E s u * wq (kP n k) (((kP n k).L1 - a) * s)) =
      (List.range (kL1 n k)).map fun s => E' s u * wq (kP n k) (((kP n k).L1 - a) * s) :=
    List.map_congr_left fun s hs => by rw [h s (List.mem_range.1 hs)]
  unfold invRowE; rw [kP_rL1, e]

/-- **Locality**: the check of a valid vertex reads only the valid wires incident to it. -/
theorem aChk_agree {n : ℕ} {L : LDesc} {x x' : AWL → ℕ} {v : AVL} (hv : v.Valid n L)
    (h : ∀ d, d.Valid n L → AWInc n L v d → x d = x' d) : aChk n L x v = aChk n L x' v := by
  cases v with
  | cell k i =>
    simp only [valid_cell] at hv
    have hL : ∀ w < L.D.nV, L.lv w = k → x (.L w i) = x' (.L w i) := fun w hw hk =>
      h _ (by simp only [valid_L]; exact ⟨hw, hk ▸ hv.2⟩) (Or.inl (by simp [aEnds, hk]))
    have hst : ∀ q < L.D.nQ, L.lq q = k → cmpOK n L x q i = cmpOK n L x' q i := fun q hq hk =>
      cmpCell_congr (opLimbC_congr _ (by rw [hk]; exact hL)) (opLimbC_congr _ (by rw [hk]; exact hL))
        (fun h1 => h _ (by simp only [valid_st]; rw [hk] at h1 ⊢; omega) (Or.inr (by simp [aEnds, hk])))
        (fun h2 => h _ (by simp only [valid_st]; rw [hk]; omega)
          (Or.inl (by simp only [aEnds, hk]; congr 1; omega)))
    simp only [aChk, cellOK]
    congr 1; congr 1
    · exact all_range_congr fun w hw => by
        by_cases hk : L.lv w = k
        · simp only [hL w hw hk]
        · simp [hk]
    · refine all_range_congr fun p hp => all_range_congr fun σ hσ => ?_
      by_cases hc : i < kl n (L.lp p) ∧ cellR n L p σ i = .cell k i
      · have hR : x (.R p σ i) = x' (.R p σ i) := h _ (by simp [hp, hσ, hc.1]) (Or.inl hc.2)
        have hO : opLimbR n L x p σ i = opLimbR n L x' p σ i := by
          unfold opLimbR
          have hc2 := hc.2
          unfold cellR at hc2
          cases ho : opnd L.D p σ with
          | var w =>
            rw [ho] at hc2
            simp only at hc2 ⊢
            split_ifs at hc2 ⊢ with h1
            · simp only [AVL.cell.injEq] at hc2
              exact hL w h1.1 hc2.1
            · rfl
          | const l => rfl
        simp only [hc, decide_true, Bool.not_true, Bool.false_or, hR, hO]
      · simp [hc]
    · exact all_range_congr fun q hq => by
        by_cases hk : L.lq q = k
        · simp only [hst q hq hk]
        · simp [hk]
  | row p σ i2 =>
    simp only [valid_row] at hv
    simp only [aChk]
    refine all_range_congr fun s hs => ?_
    rw [h (.A p σ s i2) (by simp [hv, hs]) (Or.inl rfl),
      rowE_congr' n (L.lp p) (x := fun i1 i2 => x (.R p σ (i1 + kl1 n (L.lp p) * i2)))
        (x' := fun i1 i2 => x' (.R p σ (i1 + kl1 n (L.lp p) * i2))) (fun i1 hi1 =>
          h _ (by simp only [valid_R]; exact ⟨hv.1, hv.2.1, blk_lt hi1 hv.2.2⟩)
            (Or.inr (by simp only [aEnds, blk_div _ hi1])))]
  | col p σ s =>
    simp only [valid_col] at hv
    simp only [aChk]
    refine all_range_congr fun t ht => ?_
    rw [h (.F p σ s t) (by simp [hv, ht]) (Or.inl rfl),
      colE_congr' n (L.lp p) (A := fun s i2 => x (.A p σ s i2)) (A' := fun s i2 => x' (.A p σ s i2))
        (fun i2 hi2 => h _ (by simp [hv, hi2]) (Or.inr rfl))]
  | mul p s t =>
    simp only [valid_mul] at hv
    simp only [aChk, h (.C p s t) (by simp [hv]) (Or.inl rfl),
      h (.F p 0 s t) (by simp [hv]) (Or.inr rfl), h (.F p 1 s t) (by simp [hv]) (Or.inr rfl)]
  | icol p s =>
    simp only [valid_icol] at hv
    simp only [aChk]
    refine all_range_congr fun u hu => ?_
    rw [h (.Dd p s u) (by simp [hv, hu]) (Or.inl rfl),
      invColE_congr' n (L.lp p) (C := fun s t => x (.C p s t)) (C' := fun s t => x' (.C p s t))
        (fun t ht => h _ (by simp [hv, ht]) (Or.inr rfl))]
  | irow p u =>
    simp only [valid_irow] at hv
    simp only [aChk]
    refine all_range_congr fun a ha => ?_
    have hE : x (.E p a u) = x' (.E p a u) := h _ (by simp [hv, ha]) (Or.inl (by
      simp only [aEnds]; split_ifs <;> rfl))
    rw [hE, invRowE_congr' n (L.lp p) (E := fun s u => x (.Dd p s u)) (E' := fun s u => x' (.Dd p s u))
        (fun s hs => h _ (by simp [hv, hs]) (Or.inr rfl))]
  | carry c k =>
    simp only [valid_carry] at hv
    have hd : ∀ t : Term, tDig n L x c t k = tDig n L x' c t k := by
      rintro ⟨a, src⟩
      cases src with
      | prod p =>
        simp only [tDig]
        split_ifs with hp
        · have hlp : L.lp p = L.lc c := by unfold LDesc.lp; rw [hp.2]
          refine convE_congr n _ fun a ha u hu hk => h _ ?_ (Or.inr ?_)
          · simp only [valid_E]; rw [hlp]; exact ⟨hp.1, ha, hu⟩
          · simp only [aEnds, hp.2, if_pos hv.1, hlp, hk]
        · rfl
      | lin v => rfl
      | const l => rfl
    have hs : ∀ ts, sDig n L x c ts k = sDig n L x' c ts k := fun ts => by simp only [sDig, hd]
    simp only [aChk, decide_eq_decide]
    exact carryChk_congr (hs _) (hs _)
      (fun h1 => h _ (by simp [hv.1, h1]) (Or.inl rfl))
      (fun h2 => h _ (by simp only [valid_rr]; omega)
        (Or.inr (by simp only [aEnds]; congr 1; omega)))

/-! ## The checks as propositions -/

section ChkIff
variable {n : ℕ} {L : LDesc} {x : AWL → ℕ}

theorem aChk_cell_iff {k i : ℕ} : aChk n L x (.cell k i) = true ↔
    (∀ v < L.D.nV, L.lv v = k → x (.L v i) < 2 ^ b n ∧ patOK n (L.D.pat.getD v []) i (x (.L v i)) = true) ∧
    (∀ p < L.D.nP, ∀ σ < 2, i < kl n (L.lp p) → cellR n L p σ i = .cell k i →
      x (.R p σ i) = opLimbR n L x p σ i) ∧
    (∀ q < L.D.nQ, L.lq q = k → cmpOK n L x q i = true) := by
  simp only [aChk, cellOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, beq_iff_eq, not_and, and_imp]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun v hv hk => ?_, fun p hp σ hσ hi hc => ?_, fun q hq hk => ?_⟩
    · exact ((h1 v hv).resolve_left (not_not.2 hk))
    · exact ((h2 p hp σ hσ).resolve_left (fun h => h hi hc))
    · exact ((h3 q hq).resolve_left (not_not.2 hk))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun v hv => ?_, fun p hp σ hσ => ?_⟩, fun q hq => ?_⟩
    · by_cases hk : L.lv v = k
      · exact Or.inr (h1 v hv hk)
      · exact Or.inl hk
    · by_cases hc : i < kl n (L.lp p) ∧ cellR n L p σ i = .cell k i
      · exact Or.inr (h2 p hp σ hσ hc.1 hc.2)
      · exact Or.inl fun a b => hc ⟨a, b⟩
    · by_cases hk : L.lq q = k
      · exact Or.inr (h3 q hq hk)
      · exact Or.inl hk

theorem aChk_row_iff {p σ i2 : ℕ} : aChk n L x (.row p σ i2) = true ↔ ∀ s < kL1 n (L.lp p),
    x (.A p σ s i2) = rowE (kP n (L.lp p)) (fun i1 i2 => x (.R p σ (i1 + kl1 n (L.lp p) * i2))) s i2 := by
  simp [aChk, List.all_eq_true]

theorem aChk_col_iff {p σ s : ℕ} : aChk n L x (.col p σ s) = true ↔ ∀ t < kL1 n (L.lp p),
    x (.F p σ s t) = colE (kP n (L.lp p)) (fun s i2 => x (.A p σ s i2)) s t := by
  simp [aChk, List.all_eq_true]

theorem aChk_mul_iff {p s t : ℕ} : aChk n L x (.mul p s t) = true ↔
    x (.C p s t) = x (.F p 0 s t) * x (.F p 1 s t) % M n := by
  simp [aChk]

theorem aChk_icol_iff {p s : ℕ} : aChk n L x (.icol p s) = true ↔ ∀ u < kL1 n (L.lp p),
    x (.Dd p s u) = invColE (kP n (L.lp p)) (fun s t => x (.C p s t)) s u := by
  simp [aChk, List.all_eq_true]

theorem aChk_irow_iff {p u : ℕ} : aChk n L x (.irow p u) = true ↔ ∀ a < kL1 n (L.lp p),
    x (.E p a u) = invRowE (kP n (L.lp p)) (fun s u => x (.Dd p s u)) a u := by
  simp [aChk, List.all_eq_true]

theorem aChk_carry_iff {c k : ℕ} : aChk n L x (.carry c k) = true ↔
    carryChk (b n) (kKc n (L.lc c)) (aOFF n) (sDig n L x c (L.D.ch c).lhs) (sDig n L x c (L.D.ch c).rhs)
      (fun j => x (.rr c j)) k := by
  simp [aChk]

end ChkIff

/-! ## The canonical run -/

/-- The value of operand `σ` of product `p`. -/
def opVal (n : ℕ) (L : LDesc) (y : ℕ → ℕ) (p σ : ℕ) : ℕ := (opnd L.D p σ).eval (b n) y

/-- Limb `i` of a comparison operand at level `k`, from the variable values `y`. -/
def opLimbVC (n : ℕ) (L : LDesc) (y : ℕ → ℕ) (k : ℕ) : Operand → ℕ → ℕ
  | .var w, i => if w < L.D.nV ∧ L.lv w = k then limb (b n) (y w) i else 0
  | .const l, i => l.getD i 0

/-- The canonical digit of term `t` at position `k` of chain `c`. -/
def cDig (n : ℕ) (L : LDesc) (y : ℕ → ℕ) (c : ℕ) (t : Term) (k : ℕ) : ℕ :=
  match t.src with
  | .prod p => if p < L.D.nP ∧ L.D.chainOf p = c then kc n (L.lc c) (opVal n L y p 0) (opVal n L y p 1) k else 0
  | .lin _ => 0
  | .const l => l.getD k 0

/-- The canonical digit of one side of chain `c`. -/
def cSide (n : ℕ) (L : LDesc) (y : ℕ → ℕ) (c : ℕ) (ts : List Term) (k : ℕ) : ℕ :=
  (ts.map fun t => t.coeff * cDig n L y c t k).sum

/-- **The canonical wire values** of the variable values `y`. -/
def aRun (n : ℕ) (L : LDesc) (y : ℕ → ℕ) : AWL → ℕ
  | .L v i => limb (b n) (y v) i
  | .R p σ i => limb (b n) (opVal n L y p σ) i
  | .A p σ s i2 => kA n (L.lp p) (opVal n L y p σ) s i2
  | .F p σ s t => kF n (L.lp p) (opVal n L y p σ) s t
  | .C p s t => kC n (L.lp p) (opVal n L y p 0) (opVal n L y p 1) s t
  | .Dd p s u => kD n (L.lp p) (opVal n L y p 0) (opVal n L y p 1) s u
  | .E p a u => kE n (L.lp p) (opVal n L y p 0) (opVal n L y p 1) a u
  | .rr c j => sR (b n) (kKc n (L.lc c)) (aOFF n) (cSide n L y c (L.D.ch c).lhs) (cSide n L y c (L.D.ch c).rhs) (j + 1)
  | .st q j => cmpT (b n) (kl n (L.lq q)) (opLimbVC n L y (L.lq q) (.var (L.D.cq q).v))
      (opLimbVC n L y (L.lq q) (L.D.cq q).rhs) (j + 1)

section Run
variable (n : ℕ) (L : LDesc) (y : ℕ → ℕ)

theorem opLimbC_aRun (k : ℕ) (o : Operand) (i : ℕ) : opLimbC L (aRun n L y) k o i = opLimbVC n L y k o i := by
  cases o <;> rfl

theorem opLimbC_aRun' (k : ℕ) (o : Operand) : opLimbC L (aRun n L y) k o = opLimbVC n L y k o := by
  funext i; cases o <;> rfl

theorem tDig_aRun (c : ℕ) (t : Term) (k : ℕ) : tDig n L (aRun n L y) c t k = cDig n L y c t k := by
  obtain ⟨a, src⟩ := t
  cases src with
  | prod p =>
    simp only [tDig, cDig]
    split_ifs with hp
    · have hlp : L.lp p = L.lc c := by unfold LDesc.lp; rw [hp.2]
      simp only [aRun, hlp]; rfl
    · rfl
  | lin v => rfl
  | const l => rfl

theorem sDig_aRun (c : ℕ) (ts : List Term) : sDig n L (aRun n L y) c ts = cSide n L y c ts := by
  funext k; simp only [sDig, cSide, tDig_aRun]

theorem aChk_run_row (p σ i2 : ℕ) : aChk n L (aRun n L y) (.row p σ i2) = true :=
  aChk_row_iff.2 fun _ _ => rfl
theorem aChk_run_col (p σ s : ℕ) : aChk n L (aRun n L y) (.col p σ s) = true :=
  aChk_col_iff.2 fun _ _ => rfl
theorem aChk_run_mul (p s t : ℕ) : aChk n L (aRun n L y) (.mul p s t) = true :=
  aChk_mul_iff.2 rfl
theorem aChk_run_icol (p s : ℕ) : aChk n L (aRun n L y) (.icol p s) = true :=
  aChk_icol_iff.2 fun _ _ => rfl
theorem aChk_run_irow (p u : ℕ) : aChk n L (aRun n L y) (.irow p u) = true :=
  aChk_irow_iff.2 fun _ _ => rfl

theorem aChk_run_carry (c k : ℕ) : aChk n L (aRun n L y) (.carry c k) = true ↔
    carryChk (b n) (kKc n (L.lc c)) (aOFF n) (cSide n L y c (L.D.ch c).lhs) (cSide n L y c (L.D.ch c).rhs)
      (fun j => sR (b n) (kKc n (L.lc c)) (aOFF n) (cSide n L y c (L.D.ch c).lhs)
        (cSide n L y c (L.D.ch c).rhs) (j + 1)) k := by
  rw [aChk_carry_iff, sDig_aRun, sDig_aRun]; rfl

end Run

/-- Every canonical value except the carries fits in `Wa` bits. -/
theorem aRun_lt (n : ℕ) (L : LDesc) (y : ℕ → ℕ) (d : AWL) (hd : ∀ c j, d ≠ .rr c j) :
    aRun n L y d < 2 ^ Wa n := by
  have hM : M n < 2 ^ Wa n := by
    have := M_lt_two_pow_W n
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by unfold W Wa; omega))
  have hb : 2 ^ b n ≤ 2 ^ Wa n := Nat.pow_le_pow_right (by norm_num) (by unfold Wa; have := b_le_J n; omega)
  have h4 : 4 ≤ 2 ^ Wa n := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ Wa n := Nat.pow_le_pow_right (by norm_num) (by unfold Wa; omega)
  cases d with
  | rr c j => exact absurd rfl (hd c j)
  | L v i => exact lt_of_lt_of_le (limb_lt _ _ _) hb
  | R p σ i => exact lt_of_lt_of_le (limb_lt _ _ _) hb
  | A p σ s i2 => exact (rowE_lt n _ _ s i2).trans hM
  | F p σ s t => exact (colE_lt n _ _ s t).trans hM
  | C p s t => exact (Nat.mod_lt _ (by unfold M; positivity)).trans hM
  | Dd p s u => exact (invColE_lt n _ _ s u).trans hM
  | E p a u => exact (invRowE_lt n _ _ a u).trans hM
  | st q j => exact lt_of_le_of_lt (cmpN_le _ _) (by omega)

end EthFollowup.Primes
