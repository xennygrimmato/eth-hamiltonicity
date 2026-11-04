/-
Scratch / Decorrelated / Grid32.lean   (research/engine2-decorrelated.md §7)

The 3×2 grid: rows a, b, c; columns j, j'; three rectangles ab, ac, bc on the column pair (j, j').
Legs (12 of them), in this order:  x1 y1 u1 v1 (ab)  x2 y2 u2 v2 (ac)  x3 y3 u3 v3 (bc).
Nodes: (a,j) = {x1,x2}, (a,j') = {y1,y2}, (b,j) = {u1,x3}, (b,j') = {v1,y3},
       (c,j) = {u2,u3}, (c,j') = {v2,v3}.
Target  H = Π_q [x_q = v_q][y_q = u_q].

Cuts used:
  flatB  : row b | rows a,c      (u1 v1 x3 y3 | x1 y1 x2 y2 u2 v2 u3 v3)
  colFlat: column j | column j'   (x1 u1 x2 u2 x3 u3 | y1 v1 y2 v2 y3 v3)
A row-network has rank(flatB) ≤ d_ab·d_bc ≤ 2^cost, a column-network has rank(colFlat) ≤ 2^cost.

Main theorem `rankSum_ge` (general alphabet α, any field K, any finite family of arbitrary terms):
  Σ_t T_t = H  ⟹  |α|³ ≤ Σ_t min (rank flatB T_t) (rank colFlat T_t).
Proof: the *lossy contraction* M (pair x1 with x2 at node (a,j), fix y3 = u3 = o) is a matrix
(y1 y2 v2 v3 | u1 x3 u2 v1).  M H is a permutation matrix (rank |α|⁴), and for every tensor
rank (M T) ≤ |α|·rank (flatB T)  (one leg, u2, straddles: split the columns by its value) and
rank (M T) ≤ |α|·rank (colFlat T) (one leg, v1, straddles).

Second part (no-go for row-local / column-local functionals): H is a row-local leg relabelling
(swap x_q ↔ y_q in the top row of every rectangle) of `T0`, whose column flattening has rank ≤ 1,
and a column-local relabelling (swap x_q ↔ u_q) of `J`, whose row-b flattening has rank ≤ 1.
-/
import EthFollowup.Barriers.DecorrelatedRank

set_option linter.unusedSectionVars false

namespace Grid32

open Matrix

variable {K : Type*} [Field K] {α : Type*} [Fintype α] [DecidableEq α]

/-- a tensor on the 12 legs x1 y1 u1 v1 x2 y2 u2 v2 x3 y3 u3 v3 -/
abbrev Tensor3 (K α : Type*) := α → α → α → α → α → α → α → α → α → α → α → α → K

/-- the target: three crossing rectangles -/
def H : Tensor3 K α := fun x1 y1 u1 v1 x2 y2 u2 v2 x3 y3 u3 v3 =>
  if x1 = v1 ∧ y1 = u1 ∧ x2 = v2 ∧ y2 = u2 ∧ x3 = v3 ∧ y3 = u3 then 1 else 0

abbrev Q4 (α : Type*) := (α × α) × (α × α)

/-- row cut b | a c : rows ((u1,v1),(x3,y3)), columns (((x1,y1),(x2,y2)),((u2,v2),(u3,v3))) -/
def flatB (T : Tensor3 K α) : Matrix (Q4 α) (Q4 α × Q4 α) K := fun b c =>
  T c.1.1.1 c.1.1.2 b.1.1 b.1.2 c.1.2.1 c.1.2.2 c.2.1.1 c.2.1.2 b.2.1 b.2.2 c.2.2.1 c.2.2.2

/-- column cut j | j' : rows (((x1,u1),(x2,u2)),(x3,u3)), columns (((y1,v1),(y2,v2)),(y3,v3)) -/
def colFlat (T : Tensor3 K α) : Matrix (Q4 α × (α × α)) (Q4 α × (α × α)) K := fun o e =>
  T o.1.1.1 e.1.1.1 o.1.1.2 e.1.1.2 o.1.2.1 e.1.2.1 o.1.2.2 e.1.2.2 o.2.1 e.2.1 o.2.2 e.2.2

/-- the lossy contraction: rows ((y1,y2),(v2,v3)), columns ((u1,x3),(u2,v1)); x1 = x2 = z summed,
y3 = u3 = o. -/
def M (o : α) (T : Tensor3 K α) : Matrix (Q4 α) (Q4 α) K := fun p q =>
  ∑ z, T z p.1.1 q.1.1 q.2.2 z p.1.2 q.2.1 p.2.1 q.1.2 o o p.2.2

theorem M_sum {ι : Type*} (o : α) (s : Finset ι) (T : ι → Tensor3 K α) :
    M o (∑ t ∈ s, T t) = ∑ t ∈ s, M o (T t) := by
  ext p q
  simp only [M, Finset.sum_apply, Matrix.sum_apply]
  exact Finset.sum_comm

/-- the column permutation realising M H -/
def eY : Q4 α ≃ Q4 α where
  toFun q := ((q.1.1, q.2.1), (q.2.2, q.1.2))
  invFun p := ((p.1.1, p.2.2), (p.1.2, p.2.1))
  left_inv q := by simp
  right_inv p := by simp

theorem M_H (o : α) :
    M o (H (K := K)) = (1 : Matrix (Q4 α) (Q4 α) K).submatrix (Equiv.refl _) eY := by
  ext ⟨⟨y1, y2⟩, ⟨v2, v3⟩⟩ ⟨⟨u1, x3⟩, ⟨u2, v1⟩⟩
  simp only [M, H, eY, Equiv.coe_fn_mk, Equiv.refl_apply, submatrix_apply, one_apply]
  rw [Finset.sum_eq_single v1 (fun z _ hz => by simp [hz]) (by simp)]
  split_ifs with h1 h2 h2 <;> simp_all [Prod.ext_iff]

theorem rank_M_H (o : α) : (M o (H (K := K))).rank = Fintype.card α ^ 4 := by
  rw [M_H, rank_submatrix, rank_one]
  simp [Fintype.card_prod]; ring

/-- a "pairing contraction" of a matrix never has larger rank -/
theorem rank_pair_le {m n p q ι : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [Fintype ι] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n K) (f : ι → p → m) (g : q → n) :
    (Matrix.of fun i j => ∑ z, A (f z i) (g j)).rank ≤ A.rank := by
  let P : Matrix p m K := Matrix.of fun i r => ∑ z, if f z i = r then (1 : K) else 0
  let S : Matrix n q K := Matrix.of fun c j => if c = g j then (1 : K) else 0
  have h : (Matrix.of fun i j => ∑ z, A (f z i) (g j)) = P * A * S := by
    ext i j
    simp only [P, S, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  rw [h]
  exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- splitting the columns by the value of one coordinate -/
theorem rank_le_card_mul {m n β : Type*} [Fintype m] [Fintype n] [Fintype β] [DecidableEq n]
    [DecidableEq β] (A : Matrix m n K) (π : n → β) (N : β → Matrix m n K) (r : ℕ)
    (hN : ∀ w, (N w).rank ≤ r) (hA : ∀ i j, A i j = N (π j) i j) :
    A.rank ≤ Fintype.card β * r := by
  have h : A = ∑ w, N w * Matrix.diagonal (fun j => if π j = w then (1 : K) else 0) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_diagonal, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]; simp [hA]
  rw [h]
  calc _ ≤ ∑ w, (N w * Matrix.diagonal (fun j => if π j = w then (1 : K) else 0)).rank :=
        Decorrelated.rank_sum_le _ _
    _ ≤ ∑ _w : β, r := Finset.sum_le_sum (fun w _ => (rank_mul_le_left _ _).trans (hN w))
    _ = Fintype.card β * r := by simp

/-- index maps for the u2 = w block of M (a contraction of flatBᵀ) -/
def fB (o w z : α) (p : Q4 α) : Q4 α × Q4 α := (((z, p.1.1), (z, p.1.2)), ((w, p.2.1), (o, p.2.2)))
def gB (o : α) (q : Q4 α) : Q4 α := ((q.1.1, q.2.2), (q.1.2, o))
def NB (o w : α) (T : Tensor3 K α) : Matrix (Q4 α) (Q4 α) K :=
  Matrix.of fun p q => ∑ z, (flatB T).transpose (fB o w z p) (gB o q)

theorem M_eq_NB (o : α) (T : Tensor3 K α) (p q : Q4 α) : M o T p q = NB o q.2.1 T p q := by
  simp only [M, NB, Matrix.of_apply, Matrix.transpose_apply, flatB, fB, gB]

theorem rank_NB (o w : α) (T : Tensor3 K α) : (NB o w T).rank ≤ (flatB T).rank := by
  unfold NB
  exact (rank_pair_le _ (fB o w) (gB o)).trans (rank_transpose _).le

/-- rank (M T) ≤ |α| · rank (flatB T): only the leg u2 straddles the cut b | ac. -/
theorem rank_M_le_flatB (o : α) (T : Tensor3 K α) :
    (M o T).rank ≤ Fintype.card α * (flatB T).rank :=
  rank_le_card_mul (M o T) (fun q => q.2.1) (fun w => NB o w T) _ (fun w => rank_NB o w T)
    (fun p q => M_eq_NB o T p q)

/-- index maps for the v1 = w block of M (a contraction of colFlat) -/
def fC (o z : α) (q : Q4 α) : Q4 α × (α × α) := (((z, q.1.1), (z, q.2.1)), (q.1.2, o))
def gC (o w : α) (p : Q4 α) : Q4 α × (α × α) := (((p.1.1, w), (p.1.2, p.2.1)), (o, p.2.2))
def NC (o w : α) (T : Tensor3 K α) : Matrix (Q4 α) (Q4 α) K :=
  (Matrix.of fun q p => ∑ z, colFlat T (fC o z q) (gC o w p)).transpose

theorem M_eq_NC (o : α) (T : Tensor3 K α) (p q : Q4 α) : M o T p q = NC o q.2.2 T p q := by
  simp only [M, NC, Matrix.of_apply, Matrix.transpose_apply, colFlat, fC, gC]

theorem rank_NC (o w : α) (T : Tensor3 K α) : (NC o w T).rank ≤ (colFlat T).rank := by
  unfold NC
  rw [rank_transpose]
  exact rank_pair_le _ (fC o) (gC o w)

/-- rank (M T) ≤ |α| · rank (colFlat T): only the leg v1 straddles the cut j | j'. -/
theorem rank_M_le_col (o : α) (T : Tensor3 K α) :
    (M o T).rank ≤ Fintype.card α * (colFlat T).rank :=
  rank_le_card_mul (M o T) (fun q => q.2.2) (fun w => NC o w T) _ (fun w => rank_NC o w T)
    (fun p q => M_eq_NC o T p q)

/-- **ρ ≥ 1/2 for the 3×2 grid.**  For every finite family of arbitrary terms summing to H:
|α|³ ≤ Σ_t min (rank of the row-b cut) (rank of the column cut). -/
theorem rankSum_ge [Nonempty α] {ι : Type*} (s : Finset ι) (T : ι → Tensor3 K α)
    (hsum : ∑ t ∈ s, T t = H) :
    Fintype.card α ^ 3 ≤ ∑ t ∈ s, min (flatB (T t)).rank (colFlat (T t)).rank := by
  obtain ⟨o⟩ := (inferInstance : Nonempty α)
  have hpos : 0 < Fintype.card α := Fintype.card_pos
  have key : Fintype.card α ^ 4 ≤
      Fintype.card α * ∑ t ∈ s, min (flatB (T t)).rank (colFlat (T t)).rank := by
    calc Fintype.card α ^ 4 = (M o (∑ t ∈ s, T t)).rank := by rw [hsum, rank_M_H]
      _ = (∑ t ∈ s, M o (T t)).rank := by rw [M_sum]
      _ ≤ ∑ t ∈ s, (M o (T t)).rank := Decorrelated.rank_sum_le _ _
      _ ≤ ∑ t ∈ s, Fintype.card α * min (flatB (T t)).rank (colFlat (T t)).rank := by
          refine Finset.sum_le_sum (fun t _ => ?_)
          rcases le_total (flatB (T t)).rank (colFlat (T t)).rank with hm | hm
          · rw [min_eq_left hm]; exact rank_M_le_flatB o _
          · rw [min_eq_right hm]; exact rank_M_le_col o _
      _ = _ := by rw [Finset.mul_sum]
  have : Fintype.card α * Fintype.card α ^ 3 ≤
      Fintype.card α * ∑ t ∈ s, min (flatB (T t)).rank (colFlat (T t)).rank := by
    calc Fintype.card α * Fintype.card α ^ 3 = Fintype.card α ^ 4 := by ring
      _ ≤ _ := key
  exact Nat.le_of_mul_le_mul_left this hpos

/-- the cost corollary: some term has min(rank_b, rank_col) ≥ |α|³ / #terms. -/
theorem exists_expensive [Nonempty α] {ι : Type*} (s : Finset ι) (T : ι → Tensor3 K α)
    (hsum : ∑ t ∈ s, T t = H) :
    ∃ t ∈ s, Fintype.card α ^ 3 ≤ s.card * min (flatB (T t)).rank (colFlat (T t)).rank := by
  by_contra hcon
  push Not at hcon
  have hge := rankSum_ge (K := K) s T hsum
  rcases s.eq_empty_or_nonempty with h | hs
  · subst h; simp at hge
  · have : s.card * (∑ t ∈ s, min (flatB (T t)).rank (colFlat (T t)).rank)
        < s.card * Fintype.card α ^ 3 := by
      calc s.card * (∑ t ∈ s, min (flatB (T t)).rank (colFlat (T t)).rank)
          = ∑ t ∈ s, s.card * min (flatB (T t)).rank (colFlat (T t)).rank := by
            rw [Finset.mul_sum]
        _ < ∑ _t ∈ s, Fintype.card α ^ 3 := Finset.sum_lt_sum_of_nonempty hs hcon
        _ = s.card * Fintype.card α ^ 3 := by simp
    have := Nat.mul_le_mul_left s.card hge
    omega

/-! ### No-go: functionals invariant under row-local (or column-local) relabellings -/

/-- `T0 = Π_q [x_q = u_q][y_q = v_q]`: every equality lies inside one column. -/
def T0 : Tensor3 K α := fun x1 y1 u1 v1 x2 y2 u2 v2 x3 y3 u3 v3 =>
  if x1 = u1 ∧ y1 = v1 ∧ x2 = u2 ∧ y2 = v2 ∧ x3 = u3 ∧ y3 = v3 then 1 else 0

/-- H is T0 after swapping x_q ↔ y_q, i.e. after a permutation of legs inside the top row of every
rectangle (rows a, a, b): a row-local relabelling.  So every row cost of H equals that of T0. -/
theorem H_eq_rowTwist_T0 :
    (H (K := K) (α := α)) = fun x1 y1 u1 v1 x2 y2 u2 v2 x3 y3 u3 v3 =>
      T0 y1 x1 u1 v1 y2 x2 u2 v2 y3 x3 u3 v3 := by
  funext x1 y1 u1 v1 x2 y2 u2 v2 x3 y3 u3 v3
  simp only [H, T0]
  congr 1
  apply propext; tauto

/-- T0 is a column-network of cost 0. -/
theorem rank_colFlat_T0 : (colFlat (T0 (K := K) (α := α))).rank ≤ 1 := by
  have : colFlat (T0 (K := K) (α := α)) = vecMulVec
      (fun o : Q4 α × (α × α) => if o.1.1.1 = o.1.1.2 ∧ o.1.2.1 = o.1.2.2 ∧ o.2.1 = o.2.2
        then (1 : K) else 0)
      (fun e : Q4 α × (α × α) => if e.1.1.1 = e.1.1.2 ∧ e.1.2.1 = e.1.2.2 ∧ e.2.1 = e.2.2
        then (1 : K) else 0) := by
    ext o e
    simp only [colFlat, T0, vecMulVec_apply, ite_mul, one_mul, zero_mul]
    by_cases h1 : o.1.1.1 = o.1.1.2 <;> by_cases h2 : o.1.2.1 = o.1.2.2 <;>
      by_cases h3 : o.2.1 = o.2.2 <;> simp [h1, h2, h3]
  rw [this]; exact rank_vecMulVec_le _ _

/-- `J = Π_q [x_q = y_q][u_q = v_q]`: every equality lies inside one row. -/
def J : Tensor3 K α := fun x1 y1 u1 v1 x2 y2 u2 v2 x3 y3 u3 v3 =>
  if x1 = y1 ∧ u1 = v1 ∧ x2 = y2 ∧ u2 = v2 ∧ x3 = y3 ∧ u3 = v3 then 1 else 0

/-- H is J after swapping x_q ↔ u_q (a permutation inside column j): a column-local relabelling. -/
theorem H_eq_colTwist_J :
    (H (K := K) (α := α)) = fun x1 y1 u1 v1 x2 y2 u2 v2 x3 y3 u3 v3 =>
      J u1 y1 x1 v1 u2 y2 x2 v2 u3 y3 x3 v3 := by
  funext x1 y1 u1 v1 x2 y2 u2 v2 x3 y3 u3 v3
  simp only [H, J]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨h2.symm, h1, h4.symm, h3, h6.symm, h5⟩
  · rintro ⟨k1, k2, k3, k4, k5, k6⟩; exact ⟨k2, k1.symm, k4, k3.symm, k6, k5.symm⟩

/-- J is a row-network of cost 0 (here: rank 1 across the cut b | ac). -/
theorem rank_flatB_J : (flatB (J (K := K) (α := α))).rank ≤ 1 := by
  have : flatB (J (K := K) (α := α)) = vecMulVec
      (fun b : Q4 α => if b.1.1 = b.1.2 ∧ b.2.1 = b.2.2 then (1 : K) else 0)
      (fun c : Q4 α × Q4 α => if c.1.1.1 = c.1.1.2 ∧ c.1.2.1 = c.1.2.2 ∧ c.2.1.1 = c.2.1.2 ∧
        c.2.2.1 = c.2.2.2 then (1 : K) else 0) := by
    ext b c
    simp only [flatB, J, vecMulVec_apply, ite_mul, one_mul, zero_mul]
    by_cases h1 : b.1.1 = b.1.2 <;> by_cases h2 : b.2.1 = b.2.2 <;> simp [h1, h2]
  rw [this]; exact rank_vecMulVec_le _ _

end Grid32

#print axioms Grid32.rankSum_ge
#print axioms Grid32.exists_expensive
#print axioms Grid32.H_eq_rowTwist_T0
#print axioms Grid32.rank_colFlat_T0
#print axioms Grid32.H_eq_colTwist_J
#print axioms Grid32.rank_flatB_J
#check @Grid32.rankSum_ge
#check @Grid32.exists_expensive
