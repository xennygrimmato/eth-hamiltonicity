/-
Barriers / DecorrelatedRank.lean  (research/engine2-decorrelated.md, Theorem 1)

The finite tensor problem of engine2-algebraic.md §9.2, two rectangles in "configuration C"
(disjoint row pairs and disjoint column pairs), alphabet α (|α| = D = 2^λ), any field K.

A two-rectangle tensor T(x1,y1,u1,v1, x2,y2,u2,v2).  The identity is
  F⊗F = [x1=v1][y1=u1][x2=v2][y2=u2].
Row cut  (x1 y1 x2 y2 | u1 v1 u2 v2)  (rows a,c | rows b,d),
column cut (x1 u1 x2 u2 | y1 v1 y2 v2) (columns j,k | columns j',k').
A term evaluated in the row grouping is a network on the rows; its cost is ≥ log₂ of the rank of
`rowFlat` (the cut {a,c}|{b,d} is a union of row classes).  Likewise for columns.

Main theorem `rankSum_ge` (Lean-proved, general D, any field, any finite family of arbitrary terms):
  if  Σ_t T_t = F⊗F  then  D² ≤ Σ_t min (rank rowFlat T_t) (rank colFlat T_t).
Hence max_t min(cost_row, cost_col) ≥ 2λ − log₂ #terms: no correlated decomposition beats ρ = 1/2.
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option linter.unusedSectionVars false

namespace Decorrelated

open Matrix

variable {K : Type*} [Field K] {α : Type*} [Fintype α] [DecidableEq α]

/-- a tensor on the eight legs of two rectangles: x1 y1 u1 v1 x2 y2 u2 v2 -/
abbrev Tensor2 (K α : Type*) := α → α → α → α → α → α → α → α → K

/-- the global identity F ⊗ F -/
def FF : Tensor2 K α := fun x1 y1 u1 v1 x2 y2 u2 v2 =>
  if x1 = v1 ∧ y1 = u1 ∧ x2 = v2 ∧ y2 = u2 then 1 else 0

/-- row flattening: (x1,y1),(x2,y2) | (u1,v1),(u2,v2) -/
def rowFlat (T : Tensor2 K α) : Matrix ((α × α) × (α × α)) ((α × α) × (α × α)) K :=
  fun p q => T p.1.1 p.1.2 q.1.1 q.1.2 p.2.1 p.2.2 q.2.1 q.2.2

/-- column flattening: (x1,u1),(x2,u2) | (y1,v1),(y2,v2) -/
def colFlat (T : Tensor2 K α) : Matrix ((α × α) × (α × α)) ((α × α) × (α × α)) K :=
  fun p q => T p.1.1 q.1.1 p.1.2 q.1.2 p.2.1 q.2.1 p.2.2 q.2.2

/-- the diagonal-cut contraction: y = u = o in both rectangles, a matrix (x1,x2) | (v1,v2). -/
def contr (o : α) (T : Tensor2 K α) : Matrix (α × α) (α × α) K :=
  fun p q => T p.1 o o q.1 p.2 o o q.2

theorem contr_eq_row (o : α) (T : Tensor2 K α) :
    contr o T = (rowFlat T).submatrix (fun p => ((p.1, o), (p.2, o))) (fun q => ((o, q.1), (o, q.2))) := by
  ext p q; rfl

theorem contr_eq_col (o : α) (T : Tensor2 K α) :
    contr o T = (colFlat T).submatrix (fun p => ((p.1, o), (p.2, o))) (fun q => ((o, q.1), (o, q.2))) := by
  ext p q; rfl

theorem contr_rank_le_min (o : α) (T : Tensor2 K α) :
    (contr o T).rank ≤ min (rowFlat T).rank (colFlat T).rank := by
  refine le_min ?_ ?_
  · rw [contr_eq_row]; exact rank_submatrix_le _ _ _
  · rw [contr_eq_col]; exact rank_submatrix_le _ _ _

/-- subadditivity of matrix rank -/
theorem rank_add_le' {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n K) :
    (A + B).rank ≤ A.rank + B.rank := by
  have h : (A + B).mulVecLin = A.mulVecLin + B.mulVecLin := by
    ext v i; simp
  unfold Matrix.rank
  rw [h]
  calc Module.finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

theorem rank_sum_le {ι m n : Type*} [Fintype m] [Fintype n] (s : Finset ι) (A : ι → Matrix m n K) :
    (∑ t ∈ s, A t).rank ≤ ∑ t ∈ s, (A t).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rank_add_le' _ _).trans (by omega)

theorem contr_FF (o : α) : contr o (FF (K := K)) = (1 : Matrix (α × α) (α × α) K) := by
  ext p q
  simp only [contr, FF, Matrix.one_apply, Prod.ext_iff, and_true, true_and]

theorem contr_sum {ι : Type*} (o : α) (s : Finset ι) (T : ι → Tensor2 K α) :
    contr o (∑ t ∈ s, T t) = ∑ t ∈ s, contr o (T t) := by
  ext p q; simp [contr, Finset.sum_apply, Matrix.sum_apply]

/-- **Two-flattening rigidity, two rectangles (configuration C).**  For every finite family of
arbitrary terms summing to F ⊗ F:  D² ≤ Σ_t min(rank_row T_t, rank_col T_t). -/
theorem rankSum_ge [Nonempty α] {ι : Type*} (s : Finset ι) (T : ι → Tensor2 K α)
    (hsum : ∑ t ∈ s, T t = FF) :
    Fintype.card α ^ 2 ≤ ∑ t ∈ s, min (rowFlat (T t)).rank (colFlat (T t)).rank := by
  obtain ⟨o⟩ := (inferInstance : Nonempty α)
  have h1 : (contr o (FF (K := K))).rank = Fintype.card α ^ 2 := by
    rw [contr_FF, Matrix.rank_one, Fintype.card_prod, sq]
  calc Fintype.card α ^ 2 = (contr o (∑ t ∈ s, T t)).rank := by rw [hsum, h1]
    _ = (∑ t ∈ s, contr o (T t)).rank := by rw [contr_sum]
    _ ≤ ∑ t ∈ s, (contr o (T t)).rank := rank_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun t _ => contr_rank_le_min o (T t))

/-- the cost corollary: some term has min(rank_row, rank_col) ≥ D² / #terms. -/
theorem exists_expensive [Nonempty α] {ι : Type*} (s : Finset ι) (T : ι → Tensor2 K α)
    (hsum : ∑ t ∈ s, T t = FF) :
    ∃ t ∈ s, Fintype.card α ^ 2 ≤ s.card * min (rowFlat (T t)).rank (colFlat (T t)).rank := by
  by_contra hcon
  push Not at hcon
  have hs : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with h | h
    · subst h
      have := rankSum_ge (K := K) (∅ : Finset ι) T hsum
      simp at this
    · exact h
  have hge := rankSum_ge (K := K) s T hsum
  have : s.card * (∑ t ∈ s, min (rowFlat (T t)).rank (colFlat (T t)).rank)
      < s.card * Fintype.card α ^ 2 := by
    calc s.card * (∑ t ∈ s, min (rowFlat (T t)).rank (colFlat (T t)).rank)
        = ∑ t ∈ s, s.card * min (rowFlat (T t)).rank (colFlat (T t)).rank := by rw [Finset.mul_sum]
      _ < ∑ _t ∈ s, Fintype.card α ^ 2 := Finset.sum_lt_sum_of_nonempty hs (fun t ht => hcon t ht)
      _ = s.card * Fintype.card α ^ 2 := by simp
  have := Nat.mul_le_mul_left s.card hge
  omega

end Decorrelated
