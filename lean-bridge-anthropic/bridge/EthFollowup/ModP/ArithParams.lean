/-
# ArithNet, module L1: wires, vertices, ends, clusters, checks, the canonical run

`scratchpad/plans/modp-plan.md`, ADDENDUM §B; interface `modp-interface.md` (L1). Template:
`Factoring/Params.lean` (the parameter half is reused by import), with the index bookkeeping done
generically by `Blocks` (layouts `wDims`, `vDims`; no `if` chains).

For a description `D` (`ArithDesc`) at input length `n`:
* every product `p` gets two operand pipelines `σ = 0, 1` (operand `opnd D p σ`): limb copies
  `Lr p σ i`, row transforms `A p σ s i2`, column transforms `F p σ s t`; then the pointwise
  products `C p s t`, inverse columns `Dd p s u`, inverse rows `E p a u` (2D convolution coefficients);
* every variable `v` has its limbs `L v i`; every chain `c` gets copies `Lc c v i` of all variable
  limbs (read by its carry vertices for `.lin v` terms) and offset carries `rr c j`;
* every comparison `q` has top-down states `st q j` (`0/1/2`, Compare's `cmpCell`);
* vertices: ONE `cell i` per limb position (ranges, patterns, copies, comparison steps), `row p σ i2`,
  `col p σ s`, `mul p s t`, `icol p s`, `irow p u`, `carry c k` (one ℕ equation, SignedCarry's `carryChk`).
Wire width `Wa n = J n + 8`, offset `aOFF n = 2^(J n + 6)`.

Standard axioms only.
-/
import EthFollowup.Factoring.FermatBridge
import EthFollowup.ModP.Blocks
import EthFollowup.ModP.ArithDesc
import EthFollowup.ModP.SignedCarry
import EthFollowup.ModP.Compare
import Mathlib.Tactic.IntervalCases

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset EthFollowup.Factoring

/-! ## Parameters and the bridge forms of count and well-formedness -/

/-- The wire width of ArithNet: `J + 8` bits. -/
def Wa (n : ℕ) : ℕ := J n + 8
/-- The carry offset `2^(J+6)`. -/
def aOFF (n : ℕ) : ℕ := 2 ^ (J n + 6)

/-- Number of products, chains, comparisons. -/
abbrev Desc.nP (D : Desc) : ℕ := D.prods.length
abbrev Desc.nC (D : Desc) : ℕ := D.chains.length
abbrev Desc.nQ (D : Desc) : ℕ := D.cmps.length

/-- **The count** at input length `n`: `#{x ∈ [0, 2^{nB n})^{nV} : x satisfies D}`. -/
def Desc.count (n : ℕ) (D : Desc) : ℕ := D.countB (b n) (2 ^ nB n)

/-- **Well-formedness** at input length `n`. -/
def Desc.WF (n : ℕ) (D : Desc) : Prop := D.WFB (b n) (ℓ n) (nB n)

/-- Operand `σ` of product `p`: `σ = 0` the variable `u`, otherwise `w`. -/
def opnd (D : Desc) (p σ : ℕ) : Operand :=
  if σ = 0 then .var (D.prods.getD p default).u else (D.prods.getD p default).w

/-- Chain `c` of `D`. -/
abbrev Desc.ch (D : Desc) (c : ℕ) : ChainD := D.chains.getD c default
/-- Comparison `q` of `D`. -/
abbrev Desc.cq (D : Desc) (q : ℕ) : CmpD := D.cmps.getD q default

theorem one_le_Kc (n : ℕ) : 1 ≤ Kc n := Kc_pos n
theorem ℓ_le_Kc (n : ℕ) : ℓ n ≤ Kc n := by
  have := ℓ1L2_eq n; unfold Kc; omega

/-! ## Lists of a given length -/

theorem list_eq2 {xs : List ℕ} (h : xs.length = 2) : [xs.getD 0 0, xs.getD 1 0] = xs := by
  match xs, h with | [_, _], _ => rfl
theorem list_eq3 {xs : List ℕ} (h : xs.length = 3) : [xs.getD 0 0, xs.getD 1 0, xs.getD 2 0] = xs := by
  match xs, h with | [_, _, _], _ => rfl
theorem list_eq4 {xs : List ℕ} (h : xs.length = 4) :
    [xs.getD 0 0, xs.getD 1 0, xs.getD 2 0, xs.getD 3 0] = xs := by
  match xs, h with | [_, _, _, _], _ => rfl
theorem list_eq1 {xs : List ℕ} (h : xs.length = 1) : [xs.getD 0 0] = xs := by
  match xs, h with | [_], _ => rfl

/-! ## Wires -/

/-- The wires of ArithNet (all of width `Wa`). -/
inductive AW where
  | L (v i : ℕ)
  | Lc (c v i : ℕ)
  | Lr (p σ i : ℕ)
  | A (p σ s i2 : ℕ)
  | F (p σ s t : ℕ)
  | C (p s t : ℕ)
  | Dd (p s u : ℕ)
  | E (p a u : ℕ)
  | rr (c j : ℕ)
  | st (q j : ℕ)
  deriving DecidableEq

/-- The family of a wire. -/
def AW.fam : AW → ℕ
  | .L .. => 0 | .Lc .. => 1 | .Lr .. => 2 | .A .. => 3 | .F .. => 4
  | .C .. => 5 | .Dd .. => 6 | .E .. => 7 | .rr .. => 8 | .st .. => 9

/-- The coordinates of a wire. -/
def AW.co : AW → List ℕ
  | .L v i => [v, i]
  | .Lc c v i => [c, v, i]
  | .Lr p σ i => [p, σ, i]
  | .A p σ s i2 => [p, σ, s, i2]
  | .F p σ s t => [p, σ, s, t]
  | .C p s t => [p, s, t]
  | .Dd p s u => [p, s, u]
  | .E p a u => [p, a, u]
  | .rr c j => [c, j]
  | .st q j => [q, j]

/-- The wire of a family with given coordinates. -/
def AW.mk (f : ℕ) (xs : List ℕ) : AW :=
  match f with
  | 0 => .L (xs.getD 0 0) (xs.getD 1 0)
  | 1 => .Lc (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0)
  | 2 => .Lr (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0)
  | 3 => .A (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0) (xs.getD 3 0)
  | 4 => .F (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0) (xs.getD 3 0)
  | 5 => .C (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0)
  | 6 => .Dd (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0)
  | 7 => .E (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0)
  | 8 => .rr (xs.getD 0 0) (xs.getD 1 0)
  | _ => .st (xs.getD 0 0) (xs.getD 1 0)

theorem AW.mk_fam_co (d : AW) : AW.mk d.fam d.co = d := by cases d <;> rfl

/-- The wire layout: the box of each family. -/
def wDims (n : ℕ) (D : Desc) : List (List ℕ) :=
  [[D.nV, ℓ n], [D.nC, D.nV, ℓ n], [D.nP, 2, ℓ n], [D.nP, 2, L1 n, ℓ2 n], [D.nP, 2, L1 n, L2 n],
   [D.nP, L1 n, L2 n], [D.nP, L1 n, L2 n], [D.nP, L1 n, L2 n], [D.nC, Kc n - 1], [D.nQ, ℓ n - 1]]

theorem length_wDims (n : ℕ) (D : Desc) : (wDims n D).length = 10 := rfl

theorem AW.mk_spec {n : ℕ} {D : Desc} {f : ℕ} {xs : List ℕ} (hf : f < 10)
    (hl : xs.length = ((wDims n D).getD f []).length) : (AW.mk f xs).fam = f ∧ (AW.mk f xs).co = xs := by
  interval_cases f <;> simp only [wDims, List.getD_cons_zero, List.getD_cons_succ, List.length_cons,
    List.length_nil] at hl <;> simp only [AW.mk, AW.fam, AW.co, true_and]
  · exact list_eq2 hl
  · exact list_eq3 hl
  · exact list_eq3 hl
  · exact list_eq4 hl
  · exact list_eq4 hl
  · exact list_eq3 hl
  · exact list_eq3 hl
  · exact list_eq3 hl
  · exact list_eq2 hl
  · exact list_eq2 hl

/-- The index ranges of the wires. -/
def AW.Valid (n : ℕ) (D : Desc) (d : AW) : Prop := Blocks.Valid (wDims n D) d.fam d.co

instance (n : ℕ) (D : Desc) : DecidablePred (AW.Valid n D) := fun d => by
  unfold AW.Valid; infer_instance

section ValidW
variable {n : ℕ} {D : Desc}
@[simp] theorem valid_L {v i : ℕ} : (AW.L v i).Valid n D ↔ v < D.nV ∧ i < ℓ n := by
  simp [AW.Valid, Blocks.Valid, wDims, AW.fam, AW.co]
@[simp] theorem valid_Lc {c v i : ℕ} : (AW.Lc c v i).Valid n D ↔ c < D.nC ∧ v < D.nV ∧ i < ℓ n := by
  simp [AW.Valid, Blocks.Valid, wDims, AW.fam, AW.co]
@[simp] theorem valid_Lr {p σ i : ℕ} : (AW.Lr p σ i).Valid n D ↔ p < D.nP ∧ σ < 2 ∧ i < ℓ n := by
  simp [AW.Valid, Blocks.Valid, wDims, AW.fam, AW.co]
@[simp] theorem valid_A {p σ s i2 : ℕ} :
    (AW.A p σ s i2).Valid n D ↔ p < D.nP ∧ σ < 2 ∧ s < L1 n ∧ i2 < ℓ2 n := by
  simp [AW.Valid, Blocks.Valid, wDims, AW.fam, AW.co]
@[simp] theorem valid_F {p σ s t : ℕ} :
    (AW.F p σ s t).Valid n D ↔ p < D.nP ∧ σ < 2 ∧ s < L1 n ∧ t < L2 n := by
  simp [AW.Valid, Blocks.Valid, wDims, AW.fam, AW.co]
@[simp] theorem valid_C {p s t : ℕ} : (AW.C p s t).Valid n D ↔ p < D.nP ∧ s < L1 n ∧ t < L2 n := by
  simp [AW.Valid, Blocks.Valid, wDims, AW.fam, AW.co]
@[simp] theorem valid_Dd {p s u : ℕ} : (AW.Dd p s u).Valid n D ↔ p < D.nP ∧ s < L1 n ∧ u < L2 n := by
  simp [AW.Valid, Blocks.Valid, wDims, AW.fam, AW.co]
@[simp] theorem valid_E {p a u : ℕ} : (AW.E p a u).Valid n D ↔ p < D.nP ∧ a < L1 n ∧ u < L2 n := by
  simp [AW.Valid, Blocks.Valid, wDims, AW.fam, AW.co]
@[simp] theorem valid_rr {c j : ℕ} : (AW.rr c j).Valid n D ↔ c < D.nC ∧ j + 1 < Kc n := by
  simp only [AW.Valid, Blocks.Valid, wDims, AW.fam, AW.co, List.length_cons, List.length_nil,
    List.getD_cons_succ, List.getD_cons_zero, Blocks.inBox_cons, Blocks.inBox_nil, and_true]
  have := one_le_Kc n
  omega
@[simp] theorem valid_st {q j : ℕ} : (AW.st q j).Valid n D ↔ q < D.nQ ∧ j + 1 < ℓ n := by
  simp only [AW.Valid, Blocks.Valid, wDims, AW.fam, AW.co, List.length_cons, List.length_nil,
    List.getD_cons_succ, List.getD_cons_zero, Blocks.inBox_cons, Blocks.inBox_nil, and_true]
  have := ℓ_pos n
  omega
end ValidW

/-- The number of wires. -/
def numAW (n : ℕ) (D : Desc) : ℕ := Blocks.total (wDims n D)
/-- The index of a wire. -/
def awIdx (n : ℕ) (D : Desc) (d : AW) : ℕ := Blocks.idx (wDims n D) d.fam d.co
/-- The wire with a given index. -/
def awOf (n : ℕ) (D : Desc) (j : ℕ) : AW := AW.mk (Blocks.fOf (wDims n D) j) (Blocks.cOf (wDims n D) j)

theorem awIdx_lt {n : ℕ} {D : Desc} {d : AW} (hd : d.Valid n D) : awIdx n D d < numAW n D :=
  Blocks.idx_lt hd

theorem awOf_awIdx {n : ℕ} {D : Desc} {d : AW} (hd : d.Valid n D) : awOf n D (awIdx n D d) = d := by
  unfold awOf awIdx; rw [Blocks.fOf_idx hd, Blocks.cOf_idx hd, AW.mk_fam_co]

theorem awOf_spec {n : ℕ} {D : Desc} {j : ℕ} (hj : j < numAW n D) :
    (awOf n D j).fam = Blocks.fOf (wDims n D) j ∧ (awOf n D j).co = Blocks.cOf (wDims n D) j :=
  AW.mk_spec (by have := Blocks.fOf_lt hj; rwa [length_wDims] at this) (Blocks.length_cOf _ _)

theorem awOf_valid {n : ℕ} {D : Desc} {j : ℕ} (hj : j < numAW n D) : (awOf n D j).Valid n D := by
  unfold AW.Valid; rw [(awOf_spec hj).1, (awOf_spec hj).2]; exact Blocks.valid_fOf_cOf hj

theorem awIdx_awOf {n : ℕ} {D : Desc} {j : ℕ} (hj : j < numAW n D) : awIdx n D (awOf n D j) = j := by
  unfold awIdx; rw [(awOf_spec hj).1, (awOf_spec hj).2]; exact Blocks.idx_fOf_cOf hj

/-! ## Vertices -/

/-- The vertices (checks) of ArithNet. -/
inductive AV where
  | cell (i : ℕ)
  | row (p σ i2 : ℕ)
  | col (p σ s : ℕ)
  | mul (p s t : ℕ)
  | icol (p s : ℕ)
  | irow (p u : ℕ)
  | carry (c k : ℕ)
  deriving DecidableEq

def AV.fam : AV → ℕ
  | .cell .. => 0 | .row .. => 1 | .col .. => 2 | .mul .. => 3 | .icol .. => 4 | .irow .. => 5
  | .carry .. => 6

def AV.co : AV → List ℕ
  | .cell i => [i]
  | .row p σ i2 => [p, σ, i2]
  | .col p σ s => [p, σ, s]
  | .mul p s t => [p, s, t]
  | .icol p s => [p, s]
  | .irow p u => [p, u]
  | .carry c k => [c, k]

def AV.mk (f : ℕ) (xs : List ℕ) : AV :=
  match f with
  | 0 => .cell (xs.getD 0 0)
  | 1 => .row (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0)
  | 2 => .col (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0)
  | 3 => .mul (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0)
  | 4 => .icol (xs.getD 0 0) (xs.getD 1 0)
  | 5 => .irow (xs.getD 0 0) (xs.getD 1 0)
  | _ => .carry (xs.getD 0 0) (xs.getD 1 0)

theorem AV.mk_fam_co (v : AV) : AV.mk v.fam v.co = v := by cases v <;> rfl

/-- The vertex layout. -/
def vDims (n : ℕ) (D : Desc) : List (List ℕ) :=
  [[ℓ n], [D.nP, 2, ℓ2 n], [D.nP, 2, L1 n], [D.nP, L1 n, L2 n], [D.nP, L1 n], [D.nP, L2 n], [D.nC, Kc n]]

theorem length_vDims (n : ℕ) (D : Desc) : (vDims n D).length = 7 := rfl

theorem AV.mk_spec {n : ℕ} {D : Desc} {f : ℕ} {xs : List ℕ} (hf : f < 7)
    (hl : xs.length = ((vDims n D).getD f []).length) : (AV.mk f xs).fam = f ∧ (AV.mk f xs).co = xs := by
  interval_cases f <;> simp only [vDims, List.getD_cons_zero, List.getD_cons_succ, List.length_cons,
    List.length_nil] at hl <;> simp only [AV.mk, AV.fam, AV.co, true_and]
  · exact list_eq1 hl
  · exact list_eq3 hl
  · exact list_eq3 hl
  · exact list_eq3 hl
  · exact list_eq2 hl
  · exact list_eq2 hl
  · exact list_eq2 hl

def AV.Valid (n : ℕ) (D : Desc) (v : AV) : Prop := Blocks.Valid (vDims n D) v.fam v.co

instance (n : ℕ) (D : Desc) : DecidablePred (AV.Valid n D) := fun v => by
  unfold AV.Valid; infer_instance

section ValidV
variable {n : ℕ} {D : Desc}
@[simp] theorem valid_cell {i : ℕ} : (AV.cell i).Valid n D ↔ i < ℓ n := by
  simp [AV.Valid, Blocks.Valid, vDims, AV.fam, AV.co]
@[simp] theorem valid_row {p σ i2 : ℕ} : (AV.row p σ i2).Valid n D ↔ p < D.nP ∧ σ < 2 ∧ i2 < ℓ2 n := by
  simp [AV.Valid, Blocks.Valid, vDims, AV.fam, AV.co]
@[simp] theorem valid_col {p σ s : ℕ} : (AV.col p σ s).Valid n D ↔ p < D.nP ∧ σ < 2 ∧ s < L1 n := by
  simp [AV.Valid, Blocks.Valid, vDims, AV.fam, AV.co]
@[simp] theorem valid_mul {p s t : ℕ} : (AV.mul p s t).Valid n D ↔ p < D.nP ∧ s < L1 n ∧ t < L2 n := by
  simp [AV.Valid, Blocks.Valid, vDims, AV.fam, AV.co]
@[simp] theorem valid_icol {p s : ℕ} : (AV.icol p s).Valid n D ↔ p < D.nP ∧ s < L1 n := by
  simp [AV.Valid, Blocks.Valid, vDims, AV.fam, AV.co]
@[simp] theorem valid_irow {p u : ℕ} : (AV.irow p u).Valid n D ↔ p < D.nP ∧ u < L2 n := by
  simp [AV.Valid, Blocks.Valid, vDims, AV.fam, AV.co]
@[simp] theorem valid_carry {c k : ℕ} : (AV.carry c k).Valid n D ↔ c < D.nC ∧ k < Kc n := by
  simp [AV.Valid, Blocks.Valid, vDims, AV.fam, AV.co]
end ValidV

def numAV (n : ℕ) (D : Desc) : ℕ := Blocks.total (vDims n D)
def avIdx (n : ℕ) (D : Desc) (v : AV) : ℕ := Blocks.idx (vDims n D) v.fam v.co
def avOf (n : ℕ) (D : Desc) (j : ℕ) : AV := AV.mk (Blocks.fOf (vDims n D) j) (Blocks.cOf (vDims n D) j)

theorem avIdx_lt {n : ℕ} {D : Desc} {v : AV} (hv : v.Valid n D) : avIdx n D v < numAV n D :=
  Blocks.idx_lt hv

theorem avOf_avIdx {n : ℕ} {D : Desc} {v : AV} (hv : v.Valid n D) : avOf n D (avIdx n D v) = v := by
  unfold avOf avIdx; rw [Blocks.fOf_idx hv, Blocks.cOf_idx hv, AV.mk_fam_co]

theorem avOf_spec {n : ℕ} {D : Desc} {j : ℕ} (hj : j < numAV n D) :
    (avOf n D j).fam = Blocks.fOf (vDims n D) j ∧ (avOf n D j).co = Blocks.cOf (vDims n D) j :=
  AV.mk_spec (by have := Blocks.fOf_lt hj; rwa [length_vDims] at this) (Blocks.length_cOf _ _)

theorem avOf_valid {n : ℕ} {D : Desc} {j : ℕ} (hj : j < numAV n D) : (avOf n D j).Valid n D := by
  unfold AV.Valid; rw [(avOf_spec hj).1, (avOf_spec hj).2]; exact Blocks.valid_fOf_cOf hj

theorem avIdx_avOf {n : ℕ} {D : Desc} {j : ℕ} (hj : j < numAV n D) : avIdx n D (avOf n D j) = j := by
  unfold avIdx; rw [(avOf_spec hj).1, (avOf_spec hj).2]; exact Blocks.idx_fOf_cOf hj

/-! ## The two ends of a wire -/

/-- The two vertices a wire joins. A coefficient wire `E p a u` goes to the carry of the chain
using `p` (if any, else it stays at `irow p u`); a variable limb `L v i` stays at its cell. -/
def aEnds (n : ℕ) (D : Desc) : AW → AV × AV
  | .L _ i => (.cell i, .cell i)
  | .Lc c _ i => (.cell i, .carry c i)
  | .Lr p σ i => (.cell i, .row p σ (i / ℓ1 n))
  | .A p σ s i2 => (.row p σ i2, .col p σ s)
  | .F p σ s t => (.col p σ s, .mul p s t)
  | .C p s t => (.mul p s t, .icol p s)
  | .Dd p s u => (.icol p s, .irow p u)
  | .E p a u => if D.chainOf p < D.nC then (.irow p u, .carry (D.chainOf p) (a + ℓ1 n * u))
      else (.irow p u, .irow p u)
  | .rr c j => (.carry c j, .carry c (j + 1))
  | .st _ j => (.cell (j + 1), .cell j)

theorem aEnds_valid {n : ℕ} {D : Desc} {d : AW} (hd : d.Valid n D) :
    (aEnds n D d).1.Valid n D ∧ (aEnds n D d).2.Valid n D := by
  have hK := ℓ_le_Kc n
  cases d with
  | L v i => simp only [valid_L] at hd; simp [aEnds, hd.2]
  | Lc c v i => simp only [valid_Lc] at hd; simp only [aEnds, valid_cell, valid_carry]; omega
  | Lr p σ i =>
    simp only [valid_Lr] at hd
    simp only [aEnds, valid_cell, valid_row]
    exact ⟨hd.2.2, hd.1, hd.2.1, (blk_dec (w := ℓ1 n) (h := ℓ2 n) hd.2.2).2⟩
  | A p σ s i2 => simp only [valid_A] at hd; simp only [aEnds, valid_row, valid_col]; omega
  | F p σ s t => simp only [valid_F] at hd; simp only [aEnds, valid_col, valid_mul]; omega
  | C p s t => simp only [valid_C] at hd; simp only [aEnds, valid_mul, valid_icol]; omega
  | Dd p s u => simp only [valid_Dd] at hd; simp only [aEnds, valid_icol, valid_irow]; omega
  | E p a u =>
    simp only [valid_E] at hd
    simp only [aEnds]
    split_ifs with h
    · simp only [valid_irow, valid_carry]; exact ⟨⟨hd.1, hd.2.2⟩, h, Cc_pos_lt hd.2.1 hd.2.2⟩
    · simp only [valid_irow]; exact ⟨⟨hd.1, hd.2.2⟩, hd.1, hd.2.2⟩
  | rr c j => simp only [valid_rr] at hd; simp only [aEnds, valid_carry]; omega
  | st q j => simp only [valid_st] at hd; simp only [aEnds, valid_cell]; omega

/-- Wire `d` is incident to vertex `v`. -/
def AWInc (n : ℕ) (D : Desc) (v : AV) (d : AW) : Prop := (aEnds n D d).1 = v ∨ (aEnds n D d).2 = v

/-! ## Clusters -/

/-- The stage of a vertex (its family). -/
def AV.stage (v : AV) : ℕ := v.fam
/-- The index of a vertex within its stage. -/
def AV.idx (n : ℕ) (D : Desc) (v : AV) : ℕ := Blocks.enc ((vDims n D).getD v.fam []) v.co
/-- The number of vertices of a stage. -/
def stSz (n : ℕ) (D : Desc) (st : ℕ) : ℕ := (Blocks.sizes (vDims n D)).getD st 0

theorem AV.idx_lt {n : ℕ} {D : Desc} {v : AV} (hv : v.Valid n D) : v.idx n D < stSz n D v.stage := by
  unfold AV.idx stSz AV.stage; rw [Blocks.sizes_getD hv.1]; exact Blocks.enc_lt hv.2

theorem avIdx_eq (n : ℕ) (D : Desc) (v : AV) :
    avIdx n D v = Blocks.off (Blocks.sizes (vDims n D)) v.stage + v.idx n D := rfl

theorem stage_lt (v : AV) : v.stage < 7 := by cases v <;> simp [AV.stage, AV.fam]

/-- **The cluster of a vertex**: each stage cut into `g` contiguous blocks. -/
def aClus (n : ℕ) (D : Desc) (g : ℕ) (v : AV) : ℕ := ExactHC.VB.vbN (stSz n D v.stage) g (v.idx n D)

theorem aClus_lt {n : ℕ} {D : Desc} {g : ℕ} {v : AV} (hv : v.Valid n D) (hg : 1 ≤ g) : aClus n D g v < g :=
  ExactHC.VB.vbN_lt (AV.idx_lt hv) hg

/-- The lower node of a wire. -/
def aLo (n : ℕ) (D : Desc) (g : ℕ) (d : AW) : ℕ :=
  (lohi g (aClus n D g (aEnds n D d).1) (aClus n D g (aEnds n D d).2)).1
/-- The upper node of a wire. -/
def aHi (n : ℕ) (D : Desc) (g : ℕ) (d : AW) : ℕ :=
  (lohi g (aClus n D g (aEnds n D d).1) (aClus n D g (aEnds n D d).2)).2

theorem aLo_lt_aHi {n : ℕ} {D : Desc} {g : ℕ} {d : AW} (hd : d.Valid n D) (hg : 2 ≤ g) :
    aLo n D g d < aHi n D g d :=
  (lohi_lt (aClus_lt (aEnds_valid hd).1 (by omega)) (aClus_lt (aEnds_valid hd).2 (by omega)) hg).1

theorem aHi_lt {n : ℕ} {D : Desc} {g : ℕ} {d : AW} (hd : d.Valid n D) (hg : 2 ≤ g) : aHi n D g d < g :=
  (lohi_lt (aClus_lt (aEnds_valid hd).1 (by omega)) (aClus_lt (aEnds_valid hd).2 (by omega)) hg).2

theorem aLo_lt {n : ℕ} {D : Desc} {g : ℕ} {d : AW} (hd : d.Valid n D) (hg : 2 ≤ g) : aLo n D g d < g :=
  (aLo_lt_aHi hd hg).trans (aHi_lt hd hg)

theorem aClus_ends_mem (n : ℕ) (D : Desc) (g : ℕ) (d : AW) :
    (aClus n D g (aEnds n D d).1 = aLo n D g d ∨ aClus n D g (aEnds n D d).1 = aHi n D g d) ∧
      (aClus n D g (aEnds n D d).2 = aLo n D g d ∨ aClus n D g (aEnds n D d).2 = aHi n D g d) := by
  have h := lohi_mem g (aClus n D g (aEnds n D d).1) (aClus n D g (aEnds n D d).2)
  unfold aLo aHi
  exact ⟨h.1.imp Eq.symm Eq.symm, h.2.imp Eq.symm Eq.symm⟩

/-! ## The checks -/

/-- Limb `i` of an operand, read from the wire values `x` (variables `≥ nV` read as `0`). -/
def opLimb (D : Desc) (x : AW → ℕ) : Operand → ℕ → ℕ
  | .var v, i => if v < D.nV then x (.L v i) else 0
  | .const l, i => l.getD i 0

/-- The comparison step of comparison `q` at cell `i` (Compare's `cmpCell`). -/
def cmpOK (n : ℕ) (D : Desc) (x : AW → ℕ) (q i : ℕ) : Bool :=
  cmpCell (D.cq q).rel (ℓ n) (opLimb D x (.var (D.cq q).v)) (opLimb D x (D.cq q).rhs)
    (fun j => x (.st q j)) i

/-- **The check of cell `i`**: limb ranges and patterns of all variables, the chain copies, the
operand copies, the comparison steps. -/
def cellOK (n : ℕ) (D : Desc) (x : AW → ℕ) (i : ℕ) : Bool :=
  ((List.range D.nV).all fun v => decide (x (.L v i) < 2 ^ b n) && patOK n (D.pat.getD v []) i (x (.L v i))) &&
  ((List.range D.nC).all fun c => (List.range D.nV).all fun v => x (.Lc c v i) == x (.L v i)) &&
  ((List.range D.nP).all fun p => (List.range 2).all fun σ => x (.Lr p σ i) == opLimb D x (opnd D p σ) i) &&
  ((List.range D.nQ).all fun q => cmpOK n D x q i)

/-- The digit of term `t` at position `k` of chain `c` (a product is read only by its own chain). -/
def tDig (n : ℕ) (D : Desc) (x : AW → ℕ) (c : ℕ) (t : Term) (k : ℕ) : ℕ :=
  match t.src with
  | .prod p => if p < D.nP ∧ D.chainOf p = c then convCoeff n (fun a u => x (.E p a u)) k else 0
  | .lin v => if v < D.nV ∧ k < ℓ n then x (.Lc c v k) else 0
  | .const l => l.getD k 0

/-- The digit `Σ coeff · digit` of one side of chain `c` at position `k`. -/
def sDig (n : ℕ) (D : Desc) (x : AW → ℕ) (c : ℕ) (ts : List Term) (k : ℕ) : ℕ :=
  (ts.map fun t => t.coeff * tDig n D x c t k).sum

/-- **The check of a vertex** on the wire values `x`. -/
def aChk (n : ℕ) (D : Desc) (x : AW → ℕ) : AV → Bool
  | .cell i => cellOK n D x i
  | .row p σ i2 => (List.range (L1 n)).all fun s =>
      x (.A p σ s i2) == rowDFT n (fun i1 i2 => x (.Lr p σ (i1 + ℓ1 n * i2))) s i2
  | .col p σ s => (List.range (L2 n)).all fun t =>
      x (.F p σ s t) == colDFT n (fun s i2 => x (.A p σ s i2)) s t
  | .mul p s t => x (.C p s t) == x (.F p 0 s t) * x (.F p 1 s t) % M n
  | .icol p s => (List.range (L2 n)).all fun u =>
      x (.Dd p s u) == invCol n (fun s t => x (.C p s t)) s u
  | .irow p u => (List.range (L1 n)).all fun a =>
      x (.E p a u) == invRow n (fun s u => x (.Dd p s u)) a u
  | .carry c k => decide (carryChk (b n) (Kc n) (aOFF n) (sDig n D x c (D.ch c).lhs)
      (sDig n D x c (D.ch c).rhs) (fun j => x (.rr c j)) k)

/-! ## Locality -/

theorem cmpCell_congr {r : CmpRel} {L i : ℕ} {yl pl cy yl' pl' cy' : ℕ → ℕ} (hy : yl i = yl' i)
    (hp : pl i = pl' i) (h1 : i + 1 ≠ L → cy i = cy' i) (h2 : i ≠ 0 → cy (i - 1) = cy' (i - 1)) :
    cmpCell r L yl pl cy i = cmpCell r L yl' pl' cy' i := by
  have hs : (if i + 1 = L then 1 else cy i) = (if i + 1 = L then 1 else cy' i) := by
    split_ifs with h
    · rfl
    · exact h1 h
  unfold cmpCell
  rw [hy, hp, hs]
  by_cases h : i = 0
  · simp only [h, if_true]
  · simp only [h, if_false, h2 h]

theorem carryChk_congr {b K OFF k : ℕ} {c e rr c' e' rr' : ℕ → ℕ} (hc : c k = c' k) (he : e k = e' k)
    (h1 : k + 1 < K → rr k = rr' k) (h2 : k ≠ 0 → rr (k - 1) = rr' (k - 1)) :
    carryChk b K OFF c e rr k ↔ carryChk b K OFF c' e' rr' k := by
  have e1 : (if k + 1 < K then rr k else OFF) = (if k + 1 < K then rr' k else OFF) := by
    split_ifs with h
    · exact h1 h
    · rfl
  have e2 : (if k = 0 then OFF else rr (k - 1)) = (if k = 0 then OFF else rr' (k - 1)) := by
    split_ifs with h
    · rfl
    · exact h2 h
  unfold carryChk
  rw [hc, he, e1, e2]

/-- **Locality**: the check of a valid vertex reads only the valid wires incident to it. -/
theorem aChk_agree {n : ℕ} {D : Desc} {x x' : AW → ℕ} {v : AV} (hv : v.Valid n D)
    (h : ∀ d, d.Valid n D → AWInc n D v d → x d = x' d) : aChk n D x v = aChk n D x' v := by
  cases v with
  | cell i =>
    simp only [valid_cell] at hv
    have hL : ∀ w < D.nV, x (.L w i) = x' (.L w i) := fun w hw =>
      h _ (by simp [hw, hv]) (Or.inl rfl)
    have hop : ∀ o, opLimb D x o i = opLimb D x' o i := by
      intro o; cases o with
      | var w => simp only [opLimb]; split_ifs with hw; exacts [hL w hw, rfl]
      | const l => rfl
    have hst : ∀ q < D.nQ, cmpOK n D x q i = cmpOK n D x' q i := fun q hq =>
      cmpCell_congr (hop _) (hop _)
        (fun h1 => h _ (by simp only [valid_st]; omega) (Or.inr rfl))
        (fun h2 => h _ (by simp only [valid_st]; omega)
          (Or.inl (by simp only [aEnds]; congr 1; omega)))
    simp only [aChk, cellOK]
    congr 1; congr 1; congr 1
    · exact all_range_congr fun w hw => by simp only [hL w hw]
    · exact all_range_congr fun c hc => all_range_congr fun w hw => by
        simp only [hL w hw, h (.Lc c w i) (by simp [hc, hw, hv]) (Or.inl rfl)]
    · exact all_range_congr fun p hp => all_range_congr fun σ hσ => by
        simp only [hop, h (.Lr p σ i) (by simp [hp, hσ, hv]) (Or.inl rfl)]
    · exact all_range_congr fun q hq => hst q hq
  | row p σ i2 =>
    simp only [valid_row] at hv
    simp only [aChk]
    refine all_range_congr fun s hs => ?_
    rw [h (.A p σ s i2) (by simp [hv, hs]) (Or.inl rfl),
      rowDFT_congr n (x := fun i1 i2 => x (.Lr p σ (i1 + ℓ1 n * i2)))
        (x' := fun i1 i2 => x' (.Lr p σ (i1 + ℓ1 n * i2))) (fun i1 hi1 =>
          h _ (by simp only [valid_Lr]; exact ⟨hv.1, hv.2.1, blk_lt hi1 hv.2.2⟩)
            (Or.inr (by simp only [aEnds, blk_div _ hi1])))]
  | col p σ s =>
    simp only [valid_col] at hv
    simp only [aChk]
    refine all_range_congr fun t ht => ?_
    rw [h (.F p σ s t) (by simp [hv, ht]) (Or.inl rfl),
      colDFT_congr n (A := fun s i2 => x (.A p σ s i2)) (A' := fun s i2 => x' (.A p σ s i2))
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
      invCol_congr n (C := fun s t => x (.C p s t)) (C' := fun s t => x' (.C p s t))
        (fun t ht => h _ (by simp [hv, ht]) (Or.inr rfl))]
  | irow p u =>
    simp only [valid_irow] at hv
    simp only [aChk]
    refine all_range_congr fun a ha => ?_
    have hE : x (.E p a u) = x' (.E p a u) := h _ (by simp [hv, ha]) (Or.inl (by
      simp only [aEnds]; split_ifs <;> rfl))
    rw [hE, invRow_congr n (E := fun s u => x (.Dd p s u)) (E' := fun s u => x' (.Dd p s u))
        (fun s hs => h _ (by simp [hv, hs]) (Or.inr rfl))]
  | carry c k =>
    simp only [valid_carry] at hv
    have hd : ∀ t : Term, tDig n D x c t k = tDig n D x' c t k := by
      intro t
      unfold tDig
      split
      · split_ifs with hp
        · exact convCoeff_congr n fun a ha u hu hk => h _ (by simp [hp.1, ha, hu])
            (Or.inr (by simp only [aEnds, hp.2, if_pos hv.1, hk]))
        · rfl
      · split_ifs with hl
        · exact h _ (by simp [hv.1, hl.1, hl.2]) (Or.inr rfl)
        · rfl
      · rfl
    have hs : ∀ ts, sDig n D x c ts k = sDig n D x' c ts k := fun ts => by simp only [sDig, hd]
    simp only [aChk, decide_eq_decide]
    exact carryChk_congr (hs _) (hs _)
      (fun h1 => h _ (by simp [hv.1, h1]) (Or.inl rfl))
      (fun h2 => h _ (by simp only [valid_rr]; omega)
        (Or.inr (by simp only [aEnds]; congr 1; omega)))

/-! ## Degrees: a list containing every wire incident to a vertex -/

/-- A list containing all wires incident to a vertex (`mem_aInc`). -/
def aInc (n : ℕ) (D : Desc) : AV → List AW
  | .cell i => (List.range D.nV).map (fun v => .L v i) ++
      (List.range D.nC).flatMap (fun c => (List.range D.nV).map fun v => .Lc c v i) ++
      (List.range D.nP).flatMap (fun p => [.Lr p 0 i, .Lr p 1 i]) ++
      (List.range D.nQ).flatMap (fun q => [.st q i, .st q (i - 1)])
  | .row p σ i2 => (List.range (ℓ1 n)).map (fun i1 => .Lr p σ (i1 + ℓ1 n * i2)) ++
      (List.range (L1 n)).map (fun s => .A p σ s i2)
  | .col p σ s => (List.range (ℓ2 n)).map (fun i2 => .A p σ s i2) ++
      (List.range (L2 n)).map (fun t => .F p σ s t)
  | .mul p s t => [.F p 0 s t, .F p 1 s t, .C p s t]
  | .icol p s => (List.range (L2 n)).map (fun t => .C p s t) ++ (List.range (L2 n)).map (fun u => .Dd p s u)
  | .irow p u => (List.range (L1 n)).map (fun s => .Dd p s u) ++ (List.range (L1 n)).map (fun a => .E p a u)
  | .carry c k => (List.range D.nV).map (fun v => .Lc c v k) ++
      (List.range D.nP).flatMap (fun p => [.E p (k % ℓ1 n) (k / ℓ1 n), .E p (k % ℓ1 n + ℓ1 n) (k / ℓ1 n - 1)]) ++
      [.rr c (k - 1), .rr c k]

/-- The degree bound of a stage. -/
def degA (n : ℕ) (D : Desc) : ℕ → ℕ
  | 0 => D.nV + D.nC * D.nV + 2 * D.nP + 2 * D.nQ
  | 1 => ℓ1 n + L1 n
  | 2 => ℓ2 n + L2 n
  | 3 => 3
  | 4 => L2 n + L2 n
  | 5 => L1 n + L1 n
  | _ => D.nV + 2 * D.nP + 2

theorem length_aInc (n : ℕ) (D : Desc) (v : AV) : (aInc n D v).length = degA n D v.stage := by
  cases v <;> simp [aInc, degA, AV.stage, AV.fam, List.length_flatMap, List.map_const',
    List.sum_replicate] <;> ring

theorem two_cases {σ : ℕ} (h : σ < 2) : σ = 0 ∨ σ = 1 := by omega

/-- Every valid wire incident to `v` is in `aInc n D v`. -/
theorem mem_aInc {n : ℕ} {D : Desc} {d : AW} {v : AV} (hd : d.Valid n D) (he : AWInc n D v d) :
    d ∈ aInc n D v := by
  have hl1 := one_le_ℓ1 n
  cases d with
  | L w i =>
    simp only [valid_L] at hd
    rcases he with rfl | rfl <;> simp [aInc, aEnds, hd.1]
  | Lc c w i =>
    simp only [valid_Lc] at hd
    rcases he with rfl | rfl <;> simp only [aEnds]
    · simp only [aInc, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inr ⟨c, hd.1, w, hd.2.1, rfl⟩))
    · simp [aInc, hd.2.1]
  | Lr p σ i =>
    simp only [valid_Lr] at hd
    rcases he with rfl | rfl <;> simp only [aEnds]
    · simp only [aInc, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
        List.mem_nil_iff, or_false]
      refine Or.inl (Or.inr ⟨p, hd.1, ?_⟩)
      rcases two_cases hd.2.1 with rfl | rfl <;> simp
    · simp only [aInc, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨i % ℓ1 n, Nat.mod_lt _ (by omega), by rw [Nat.mod_add_div]⟩
  | A p σ s i2 =>
    simp only [valid_A] at hd
    rcases he with rfl | rfl <;> simp [aInc, aEnds, hd.2.2.1, hd.2.2.2]
  | F p σ s t =>
    simp only [valid_F] at hd
    rcases he with rfl | rfl <;> simp only [aEnds]
    · simp [aInc, hd.2.2.2]
    · rcases two_cases hd.2.1 with rfl | rfl <;> simp [aInc]
  | C p s t =>
    simp only [valid_C] at hd
    rcases he with rfl | rfl <;> simp [aInc, aEnds, hd.2.2]
  | Dd p s u =>
    simp only [valid_Dd] at hd
    rcases he with rfl | rfl <;> simp [aInc, aEnds, hd.2.1, hd.2.2]
  | E p a u =>
    simp only [valid_E] at hd
    have h1 : (aEnds n D (.E p a u)).1 = .irow p u := by simp only [aEnds]; split_ifs <;> rfl
    rcases he with he | he
    · rw [h1] at he; subst he; simp [aInc, hd.2.1]
    · simp only [aEnds] at he
      split_ifs at he with hc
      · subst he
        simp only [aInc, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
          List.mem_nil_iff, or_false]
        refine Or.inl (Or.inr ⟨p, hd.1, ?_⟩)
        have hL := L1_eq_two_mul n
        by_cases ha : a < ℓ1 n
        · left; rw [blk_mod _ ha, blk_div _ ha]
        · right
          have ha' : a - ℓ1 n < ℓ1 n := by omega
          have e : a + ℓ1 n * u = (a - ℓ1 n) + ℓ1 n * (u + 1) := by rw [mul_add]; omega
          rw [e, blk_mod _ ha', blk_div _ ha']
          simp only [AW.E.injEq, true_and]; omega
      · subst he; simp [aInc, hd.2.1]
  | rr c j =>
    simp only [valid_rr] at hd
    rcases he with rfl | rfl <;> simp [aInc, aEnds]
  | st q j =>
    simp only [valid_st] at hd
    rcases he with rfl | rfl <;> simp only [aEnds]
    · simp only [aInc, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
        List.mem_nil_iff, or_false]
      exact Or.inr ⟨q, hd.1, Or.inr (by simp)⟩
    · simp only [aInc, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
        List.mem_nil_iff, or_false]
      exact Or.inr ⟨q, hd.1, Or.inl rfl⟩

/-! ## The checks as propositions -/

section ChkIff

variable {n : ℕ} {D : Desc} {x : AW → ℕ}

theorem aChk_cell_iff {i : ℕ} : aChk n D x (.cell i) = true ↔
    (∀ v < D.nV, x (.L v i) < 2 ^ b n ∧ patOK n (D.pat.getD v []) i (x (.L v i)) = true) ∧
    (∀ c < D.nC, ∀ v < D.nV, x (.Lc c v i) = x (.L v i)) ∧
    (∀ p < D.nP, ∀ σ < 2, x (.Lr p σ i) = opLimb D x (opnd D p σ) i) ∧
    (∀ q < D.nQ, cmpOK n D x q i = true) := by
  simp [aChk, cellOK, List.all_eq_true, and_assoc]

theorem aChk_row_iff {p σ i2 : ℕ} : aChk n D x (.row p σ i2) = true ↔
    ∀ s < L1 n, x (.A p σ s i2) = rowDFT n (fun i1 i2 => x (.Lr p σ (i1 + ℓ1 n * i2))) s i2 := by
  simp [aChk, List.all_eq_true]

theorem aChk_col_iff {p σ s : ℕ} : aChk n D x (.col p σ s) = true ↔
    ∀ t < L2 n, x (.F p σ s t) = colDFT n (fun s i2 => x (.A p σ s i2)) s t := by
  simp [aChk, List.all_eq_true]

theorem aChk_mul_iff {p s t : ℕ} : aChk n D x (.mul p s t) = true ↔
    x (.C p s t) = x (.F p 0 s t) * x (.F p 1 s t) % M n := by
  simp [aChk]

theorem aChk_icol_iff {p s : ℕ} : aChk n D x (.icol p s) = true ↔
    ∀ u < L2 n, x (.Dd p s u) = invCol n (fun s t => x (.C p s t)) s u := by
  simp [aChk, List.all_eq_true]

theorem aChk_irow_iff {p u : ℕ} : aChk n D x (.irow p u) = true ↔
    ∀ a < L1 n, x (.E p a u) = invRow n (fun s u => x (.Dd p s u)) a u := by
  simp [aChk, List.all_eq_true]

theorem aChk_carry_iff {c k : ℕ} : aChk n D x (.carry c k) = true ↔
    carryChk (b n) (Kc n) (aOFF n) (sDig n D x c (D.ch c).lhs) (sDig n D x c (D.ch c).rhs)
      (fun j => x (.rr c j)) k := by
  simp [aChk]

end ChkIff

/-! ## The canonical run -/

/-- The value of operand `σ` of product `p` for the variable values `y`. -/
def opVal (n : ℕ) (D : Desc) (y : ℕ → ℕ) (p σ : ℕ) : ℕ := (opnd D p σ).eval (b n) y

/-- Limb `i` of an operand for the variable values `y` (variables `≥ nV` read as `0`). -/
def opLimbV (n : ℕ) (D : Desc) (y : ℕ → ℕ) : Operand → ℕ → ℕ
  | .var v, i => if v < D.nV then limb (b n) (y v) i else 0
  | .const l, i => l.getD i 0

/-- The canonical digit of term `t` at position `k` of chain `c`. -/
def cDig (n : ℕ) (D : Desc) (y : ℕ → ℕ) (c : ℕ) (t : Term) (k : ℕ) : ℕ :=
  match t.src with
  | .prod p => if p < D.nP ∧ D.chainOf p = c then stc n (opVal n D y p 0) (opVal n D y p 1) k else 0
  | .lin v => if v < D.nV ∧ k < ℓ n then limb (b n) (y v) k else 0
  | .const l => l.getD k 0

/-- The canonical digit of one side of chain `c`. -/
def cSide (n : ℕ) (D : Desc) (y : ℕ → ℕ) (c : ℕ) (ts : List Term) (k : ℕ) : ℕ :=
  (ts.map fun t => t.coeff * cDig n D y c t k).sum

/-- **The canonical wire values** of the variable values `y`: the pipeline stages of every
product, the canonical signed carries (`sR`) and comparison states (`cmpT`). -/
def aRun (n : ℕ) (D : Desc) (y : ℕ → ℕ) : AW → ℕ
  | .L v i => limb (b n) (y v) i
  | .Lc _ v i => limb (b n) (y v) i
  | .Lr p σ i => limb (b n) (opVal n D y p σ) i
  | .A p σ s i2 => stA n (opVal n D y p σ) s i2
  | .F p σ s t => stF n (opVal n D y p σ) s t
  | .C p s t => stC n (opVal n D y p 0) (opVal n D y p 1) s t
  | .Dd p s u => stD n (opVal n D y p 0) (opVal n D y p 1) s u
  | .E p a u => stE n (opVal n D y p 0) (opVal n D y p 1) a u
  | .rr c j => sR (b n) (Kc n) (aOFF n) (cSide n D y c (D.ch c).lhs) (cSide n D y c (D.ch c).rhs) (j + 1)
  | .st q j => cmpT (b n) (ℓ n) (opLimbV n D y (.var (D.cq q).v)) (opLimbV n D y (D.cq q).rhs) (j + 1)

section Run

variable (n : ℕ) (D : Desc) (y : ℕ → ℕ)

theorem opLimb_aRun (o : Operand) (i : ℕ) : opLimb D (aRun n D y) o i = opLimbV n D y o i := by
  cases o <;> rfl

theorem tDig_aRun (c : ℕ) (t : Term) (k : ℕ) : tDig n D (aRun n D y) c t k = cDig n D y c t k := by
  obtain ⟨a, src⟩ := t
  cases src <;> rfl

theorem sDig_aRun (c : ℕ) (ts : List Term) : sDig n D (aRun n D y) c ts = cSide n D y c ts := by
  funext k; simp only [sDig, cSide, tDig_aRun]

theorem aChk_run_row (p σ i2 : ℕ) : aChk n D (aRun n D y) (.row p σ i2) = true :=
  aChk_row_iff.2 fun _ _ => rfl
theorem aChk_run_col (p σ s : ℕ) : aChk n D (aRun n D y) (.col p σ s) = true :=
  aChk_col_iff.2 fun _ _ => rfl
theorem aChk_run_mul (p s t : ℕ) : aChk n D (aRun n D y) (.mul p s t) = true :=
  aChk_mul_iff.2 rfl
theorem aChk_run_icol (p s : ℕ) : aChk n D (aRun n D y) (.icol p s) = true :=
  aChk_icol_iff.2 fun _ _ => rfl
theorem aChk_run_irow (p u : ℕ) : aChk n D (aRun n D y) (.irow p u) = true :=
  aChk_irow_iff.2 fun _ _ => rfl

theorem aChk_run_carry (c k : ℕ) : aChk n D (aRun n D y) (.carry c k) = true ↔
    carryChk (b n) (Kc n) (aOFF n) (cSide n D y c (D.ch c).lhs) (cSide n D y c (D.ch c).rhs)
      (fun j => sR (b n) (Kc n) (aOFF n) (cSide n D y c (D.ch c).lhs) (cSide n D y c (D.ch c).rhs) (j + 1)) k := by
  rw [aChk_carry_iff, sDig_aRun, sDig_aRun]; rfl

theorem aChk_run_cell (i : ℕ) : aChk n D (aRun n D y) (.cell i) = true ↔
    (∀ v < D.nV, limb (b n) (y v) i < 2 ^ b n ∧ patOK n (D.pat.getD v []) i (limb (b n) (y v) i) = true) ∧
    (∀ p < D.nP, ∀ σ < 2, limb (b n) (opVal n D y p σ) i = opLimbV n D y (opnd D p σ) i) ∧
    (∀ q < D.nQ, cmpCell (D.cq q).rel (ℓ n) (opLimbV n D y (.var (D.cq q).v)) (opLimbV n D y (D.cq q).rhs)
      (fun j => cmpT (b n) (ℓ n) (opLimbV n D y (.var (D.cq q).v)) (opLimbV n D y (D.cq q).rhs) (j + 1)) i = true) := by
  rw [aChk_cell_iff]
  simp only [cmpOK, opLimb_aRun]
  constructor
  · rintro ⟨h1, -, h3, h4⟩; exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩; exact ⟨h1, fun _ _ _ _ => rfl, h3, h4⟩

end Run

/-- Every canonical value except the carries fits in `Wa` bits (states `≤ 2`). -/
theorem aRun_lt (n : ℕ) (D : Desc) (y : ℕ → ℕ) (d : AW) (hd : ∀ c j, d ≠ .rr c j) :
    aRun n D y d < 2 ^ Wa n := by
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
  | Lc c v i => exact lt_of_lt_of_le (limb_lt _ _ _) hb
  | Lr p σ i => exact lt_of_lt_of_le (limb_lt _ _ _) hb
  | A p σ s i2 => exact (rowDFT_lt n _ s i2).trans hM
  | F p σ s t => exact (colDFT_lt n _ s t).trans hM
  | C p s t => exact (pointwise_lt n _ _ s t).trans hM
  | Dd p s u => exact (invCol_lt n _ s u).trans hM
  | E p a u => exact (invRow_lt n _ a u).trans hM
  | st q j => exact lt_of_le_of_lt (cmpN_le _ _) (by omega)

end EthFollowup.ModP
