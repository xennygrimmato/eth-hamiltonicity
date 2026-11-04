/-
Scratch / Grid33 / Level.lean   (research/engine2-decorrelated.md §8: Theorem 5 at g = 3, Lean)
Self-contained: the general lossy lemma (namespace Lossy, also in Lossy.lean) is included so that the
file checks without a separate olean build.

The full 3×3 level.  Nodes (r,c) ∈ Fin 3 × Fin 3, 18 crossing edges (different row and different column),
legs L = Fin 18 × Bool (edge, end).  Target G = Π_edges [x_e,0 = x_e,1] (the graph tensor of K₃ × K₃).
Cuts:  Srow = legs in row 2 (row c | rows a,b),  Scol = legs in column 2 (column 3 | columns 1,2).
A row-network has rank (flat Srow) ≤ d_ac·d_bc ≤ 2^cost, a column-network has rank (flat Scol) ≤ 2^cost.

Main theorem `rankSum_ge`:  Σ_t T_t = G  ⟹  |α|⁸ ≤ Σ_t min (rank flat Srow T_t) (rank flat Scol T_t),
i.e. Σ_t 2^{cost_t} ≥ N⁸ for every decomposition into row- and column-networks (ρ ≥ 4/9 on this level).
Contraction: X = the 12 legs at the block {a,b}×{1,2} on edges leaving the block, Y = their partners;
the two edges inside the block and the four edges between {(a,3),(b,3)} and {(c,1),(c,2)} are fixed.
Straddlers: 4 legs at (a,3),(b,3) for the row cut, 4 legs at (c,1),(c,2) for the column cut.
-/
import EthFollowup.Barriers.DecorrelatedGrid32

set_option linter.unusedSectionVars false

namespace Lossy

open Matrix

variable {K : Type*} [Field K] {L : Type*} [Fintype L] [DecidableEq L]
  {α : Type*} [Fintype α] [DecidableEq α]

abbrev Tensor (K L α : Type*) := (L → α) → K

/-- flattening across the cut S | Sᶜ -/
def flat (S : Finset L) (T : Tensor K L α) : Matrix ({l // l ∈ S} → α) ({l // l ∉ S} → α) K :=
  fun p q => T (fun l => if h : l ∈ S then p ⟨l, h⟩ else q ⟨l, h⟩)

/-- the assignment of all legs given the kept-X values p, kept-Y values q, and the constant o -/
def merge (KX KY : Finset L) (o : α) (p : {l // l ∈ KX} → α) (q : {l // l ∈ KY} → α) : L → α :=
  fun l => if h : l ∈ KX then p ⟨l, h⟩ else if h' : l ∈ KY then q ⟨l, h'⟩ else o

/-- the contraction: keep KX (rows), KY (columns), fix the rest to o -/
def contr (KX KY : Finset L) (o : α) (T : Tensor K L α) :
    Matrix ({l // l ∈ KX} → α) ({l // l ∈ KY} → α) K :=
  fun p q => T (merge KX KY o p q)

theorem contr_sum {ι : Type*} (KX KY : Finset L) (o : α) (s : Finset ι) (T : ι → Tensor K L α) :
    contr KX KY o (∑ t ∈ s, T t) = ∑ t ∈ s, contr KX KY o (T t) := by
  ext p q; simp [contr, Finset.sum_apply, Matrix.sum_apply]

/-- splitting the rows by one coordinate (transpose of `Grid32.rank_le_card_mul`) -/
theorem rank_le_card_mul_rows {m n β : Type*} [Fintype m] [Fintype n] [Fintype β] [DecidableEq m]
    [DecidableEq β] (A : Matrix m n K) (π : m → β) (N : β → Matrix m n K) (r : ℕ)
    (hN : ∀ w, (N w).rank ≤ r) (hA : ∀ i j, A i j = N (π i) i j) :
    A.rank ≤ Fintype.card β * r := by
  rw [← rank_transpose]
  exact Grid32.rank_le_card_mul Aᵀ π (fun w => (N w)ᵀ) r
    (fun w => by rw [rank_transpose]; exact hN w) (fun j i => hA i j)

section lossy

variable (KX KY S : Finset L) (o : α) (T : Tensor K L α)

/-- the block of `contr` where the wrong-side legs are frozen at w (X-legs inside S) and w' (Y-legs
outside S); it is a submatrix of (flat S T)ᵀ. -/
def block (w : {l // l ∈ KX ∧ l ∈ S} → α) (w' : {l // l ∈ KY ∧ l ∉ S} → α) :
    Matrix ({l // l ∈ KX} → α) ({l // l ∈ KY} → α) K :=
  fun p q => flat S T
    (fun l => if h : l.1 ∈ KX then w ⟨l.1, h, l.2⟩ else if h' : l.1 ∈ KY then q ⟨l.1, h'⟩ else o)
    (fun l => if h : l.1 ∈ KX then p ⟨l.1, h⟩ else if h' : l.1 ∈ KY then w' ⟨l.1, h', l.2⟩ else o)

theorem rank_block_le (w : {l // l ∈ KX ∧ l ∈ S} → α) (w' : {l // l ∈ KY ∧ l ∉ S} → α) :
    (block KX KY S o T w w').rank ≤ (flat S T).rank := by
  have : block KX KY S o T w w' = (flat S T).transpose.submatrix
      (fun p : {l // l ∈ KX} → α => fun l : {l // l ∉ S} =>
        if h : l.1 ∈ KX then p ⟨l.1, h⟩ else if h' : l.1 ∈ KY then w' ⟨l.1, h', l.2⟩ else o)
      (fun q : {l // l ∈ KY} → α => fun l : {l // l ∈ S} =>
        if h : l.1 ∈ KX then w ⟨l.1, h, l.2⟩ else if h' : l.1 ∈ KY then q ⟨l.1, h'⟩ else o) := by
    ext p q; rfl
  rw [this]
  exact (rank_submatrix_le _ _ _).trans (rank_transpose _).le

/-- restriction of p to the X-legs inside S -/
def resX (p : {l // l ∈ KX} → α) : {l // l ∈ KX ∧ l ∈ S} → α := fun l => p ⟨l.1, l.2.1⟩
/-- restriction of q to the Y-legs outside S -/
def resY (q : {l // l ∈ KY} → α) : {l // l ∈ KY ∧ l ∉ S} → α := fun l => q ⟨l.1, l.2.1⟩

theorem contr_eq_block (p : {l // l ∈ KX} → α) (q : {l // l ∈ KY} → α) :
    contr KX KY o T p q = block KX KY S o T (resX KX S p) (resY KY S q) p q := by
  simp only [contr, block, flat, resX, resY]
  congr 1
  funext l
  simp only [merge]
  by_cases hS : l ∈ S <;> by_cases hX : l ∈ KX <;> by_cases hY : l ∈ KY <;> simp [hS, hX, hY]

/-- **lossy flattening lemma**: each kept leg on the wrong side of the cut S costs a factor |α|. -/
theorem rank_contr_le (hd : Disjoint KX KY) :
    (contr KX KY o T).rank ≤
      Fintype.card α ^ ((KX.filter (· ∈ S)).card + (KY.filter (· ∉ S)).card) * (flat S T).rank := by
  -- first split the columns by the wrong-side Y legs
  have h1 : ∀ w' : {l // l ∈ KY ∧ l ∉ S} → α,
      (Matrix.of fun p q => block KX KY S o T (resX KX S p) w' p q).rank ≤
        Fintype.card ({l // l ∈ KX ∧ l ∈ S} → α) * (flat S T).rank := by
    intro w'
    exact rank_le_card_mul_rows _ (resX KX S) (fun w => block KX KY S o T w w') _
      (fun w => rank_block_le KX KY S o T w w') (fun p q => rfl)
  have h2 := Grid32.rank_le_card_mul (contr KX KY o T) (resY KY S)
    (fun w' => Matrix.of fun p q => block KX KY S o T (resX KX S p) w' p q) _ h1
    (fun p q => by simp only [Matrix.of_apply]; exact contr_eq_block KX KY S o T p q)
  refine h2.trans (le_of_eq ?_)
  rw [Fintype.card_fun, Fintype.card_fun, ← mul_assoc, ← pow_add]
  congr 2
  · rw [add_comm]; congr 1
    · exact Fintype.card_subtype _ |>.trans (by congr 1; ext l; simp)
    · exact Fintype.card_subtype _ |>.trans (by congr 1; ext l; simp)

end lossy

section graph

/-- a graph tensor: `other l` is the other end of the edge at leg l; G x = 1 iff every edge is satisfied -/
def graphT (other : L → L) : Tensor K L α := fun x => if ∀ l, x l = x (other l) then 1 else 0

variable (KX KY : Finset L) (other : L → L) (o : α)

theorem contr_graph (hd : Disjoint KX KY) (hinv : ∀ l, other (other l) = l)
    (hXY : ∀ l ∈ KX, other l ∈ KY) (hYX : ∀ l ∈ KY, other l ∈ KX)
    (hfix : ∀ l, l ∉ KX → l ∉ KY → other l ∉ KX ∧ other l ∉ KY)
    (p : {l // l ∈ KX} → α) (q : {l // l ∈ KY} → α) :
    contr KX KY o (graphT other : Tensor K L α) p q =
      if (∀ l : {l // l ∈ KX}, p l = q ⟨other l.1, hXY l.1 l.2⟩) then 1 else 0 := by
  simp only [contr, graphT, merge]
  congr 1
  apply propext
  constructor
  · intro h l
    have := h l.1
    have hX := l.2
    have hY := hXY l.1 l.2
    have hnot : other l.1 ∉ KX := Finset.disjoint_right.mp hd hY
    simp [hX, hY, hnot] at this
    exact this
  · intro h l
    by_cases hX : l ∈ KX
    · have hY := hXY l hX
      have hnot : other l ∉ KX := Finset.disjoint_right.mp hd hY
      simp only [hX, dite_true, hnot, dite_false, hY]
      exact h ⟨l, hX⟩
    · by_cases hY : l ∈ KY
      · have hX' := hYX l hY
        have := h ⟨other l, hX'⟩
        simp only [hinv] at this
        simp only [hX, dite_false, hY, dite_true, hX']
        exact this.symm
      · obtain ⟨h1, h2⟩ := hfix l hX hY
        simp [hX, hY, h1, h2]

/-- the matching KX ≃ KY induced by `other` -/
def matchEquiv (hinv : ∀ l, other (other l) = l)
    (hXY : ∀ l ∈ KX, other l ∈ KY) (hYX : ∀ l ∈ KY, other l ∈ KX) :
    {l // l ∈ KX} ≃ {l // l ∈ KY} where
  toFun l := ⟨other l.1, hXY l.1 l.2⟩
  invFun l := ⟨other l.1, hYX l.1 l.2⟩
  left_inv l := by ext; simp [hinv]
  right_inv l := by ext; simp [hinv]

theorem rank_contr_graph (hd : Disjoint KX KY) (hinv : ∀ l, other (other l) = l)
    (hXY : ∀ l ∈ KX, other l ∈ KY) (hYX : ∀ l ∈ KY, other l ∈ KX)
    (hfix : ∀ l, l ∉ KX → l ∉ KY → other l ∉ KX ∧ other l ∉ KY) :
    (contr KX KY o (graphT other : Tensor K L α)).rank = Fintype.card α ^ KX.card := by
  have hm : contr KX KY o (graphT other : Tensor K L α) =
      (1 : Matrix ({l // l ∈ KX} → α) ({l // l ∈ KX} → α) K).submatrix (Equiv.refl _)
        (Equiv.arrowCongr (matchEquiv KX KY other hinv hXY hYX).symm (Equiv.refl α)) := by
    ext p q
    rw [contr_graph KX KY other o hd hinv hXY hYX hfix]
    simp only [submatrix_apply, one_apply, Equiv.coe_refl]
    congr 1
    apply propext
    constructor
    · intro h; funext l; exact h l
    · intro h l; exact congrFun h l
  rw [hm, rank_submatrix, rank_one, Fintype.card_fun, Fintype.card_coe]

end graph

end Lossy


namespace Grid33

open Matrix Lossy

abbrev Node := Fin 3 × Fin 3

/-- the 18 crossing edges of the 3×3 grid, (lower row end, upper row end) -/
def edges : Fin 18 → Node × Node := ![
  ((0,0),(1,1)), ((0,0),(1,2)), ((0,0),(2,1)), ((0,0),(2,2)),
  ((0,1),(1,0)), ((0,1),(1,2)), ((0,1),(2,0)), ((0,1),(2,2)),
  ((0,2),(1,0)), ((0,2),(1,1)), ((0,2),(2,0)), ((0,2),(2,1)),
  ((1,0),(2,1)), ((1,0),(2,2)), ((1,1),(2,0)), ((1,1),(2,2)),
  ((1,2),(2,0)), ((1,2),(2,1))]

abbrev L := Fin 18 × Bool

def node (l : L) : Node := if l.2 then (edges l.1).2 else (edges l.1).1
def other (l : L) : L := (l.1, !l.2)
def inBlock (v : Node) : Bool := decide (v.1 ≠ 2 ∧ v.2 ≠ 2)
/-- an edge is kept iff exactly one end lies in the block {a,b}×{1,2} -/
def kept (i : Fin 18) : Bool := inBlock (edges i).1 != inBlock (edges i).2

def KX : Finset L := Finset.univ.filter (fun l => kept l.1 ∧ inBlock (node l))
def KY : Finset L := Finset.univ.filter (fun l => kept l.1 ∧ ¬ inBlock (node l))
def Srow : Finset L := Finset.univ.filter (fun l => (node l).1 = 2)
def Scol : Finset L := Finset.univ.filter (fun l => (node l).2 = 2)

variable {K : Type*} [Field K] {α : Type*} [Fintype α] [DecidableEq α]

/-- the target: the graph tensor of the 18 edges -/
def G : Tensor K L α := graphT other

theorem hd : Disjoint KX KY := by decide
theorem hinv : ∀ l : L, other (other l) = l := by decide
theorem hXY : ∀ l ∈ KX, other l ∈ KY := by decide
theorem hYX : ∀ l ∈ KY, other l ∈ KX := by decide
theorem hfix : ∀ l : L, l ∉ KX → l ∉ KY → other l ∉ KX ∧ other l ∉ KY := by decide
theorem card_KX : KX.card = 12 := by decide
theorem exp_row : (KX.filter (· ∈ Srow)).card + (KY.filter (· ∉ Srow)).card = 4 := by decide
theorem exp_col : (KX.filter (· ∈ Scol)).card + (KY.filter (· ∉ Scol)).card = 4 := by decide

theorem rank_contr_G (o : α) : (contr KX KY o (G : Tensor K L α)).rank = Fintype.card α ^ 12 := by
  rw [G, rank_contr_graph KX KY other o hd hinv hXY hYX hfix, card_KX]

theorem rank_contr_le_row (o : α) (T : Tensor K L α) :
    (contr KX KY o T).rank ≤ Fintype.card α ^ 4 * (flat Srow T).rank := by
  have := rank_contr_le KX KY Srow o T hd
  rwa [exp_row] at this

theorem rank_contr_le_col (o : α) (T : Tensor K L α) :
    (contr KX KY o T).rank ≤ Fintype.card α ^ 4 * (flat Scol T).rank := by
  have := rank_contr_le KX KY Scol o T hd
  rwa [exp_col] at this

/-- **Theorem 5 at g = 3 (ρ ≥ 4/9 on the full 3×3 level).**  For every finite family of arbitrary
terms summing to G:  |α|⁸ ≤ Σ_t min (rank of the row-c cut) (rank of the column-3 cut). -/
theorem rankSum_ge [Nonempty α] {ι : Type*} (s : Finset ι) (T : ι → Tensor K L α)
    (hsum : ∑ t ∈ s, T t = G) :
    Fintype.card α ^ 8 ≤ ∑ t ∈ s, min (flat Srow (T t)).rank (flat Scol (T t)).rank := by
  obtain ⟨o⟩ := (inferInstance : Nonempty α)
  have hpos : 0 < Fintype.card α ^ 4 := pow_pos Fintype.card_pos _
  have key : Fintype.card α ^ 12 ≤
      Fintype.card α ^ 4 * ∑ t ∈ s, min (flat Srow (T t)).rank (flat Scol (T t)).rank := by
    calc Fintype.card α ^ 12 = (contr KX KY o (∑ t ∈ s, T t)).rank := by rw [hsum, rank_contr_G]
      _ = (∑ t ∈ s, contr KX KY o (T t)).rank := by rw [contr_sum]
      _ ≤ ∑ t ∈ s, (contr KX KY o (T t)).rank := Decorrelated.rank_sum_le _ _
      _ ≤ ∑ t ∈ s, Fintype.card α ^ 4 * min (flat Srow (T t)).rank (flat Scol (T t)).rank := by
          refine Finset.sum_le_sum (fun t _ => ?_)
          rcases le_total (flat Srow (T t)).rank (flat Scol (T t)).rank with hm | hm
          · rw [min_eq_left hm]; exact rank_contr_le_row o _
          · rw [min_eq_right hm]; exact rank_contr_le_col o _
      _ = _ := by rw [Finset.mul_sum]
  have : Fintype.card α ^ 4 * Fintype.card α ^ 8 ≤
      Fintype.card α ^ 4 * ∑ t ∈ s, min (flat Srow (T t)).rank (flat Scol (T t)).rank := by
    calc Fintype.card α ^ 4 * Fintype.card α ^ 8 = Fintype.card α ^ 12 := by ring
      _ ≤ _ := key
  exact Nat.le_of_mul_le_mul_left this hpos

/-- some term has min(rank_row-c, rank_col-3) ≥ |α|⁸ / #terms -/
theorem exists_expensive [Nonempty α] {ι : Type*} (s : Finset ι) (T : ι → Tensor K L α)
    (hsum : ∑ t ∈ s, T t = G) :
    ∃ t ∈ s, Fintype.card α ^ 8 ≤ s.card * min (flat Srow (T t)).rank (flat Scol (T t)).rank := by
  by_contra hcon
  push Not at hcon
  have hge := rankSum_ge (K := K) s T hsum
  rcases s.eq_empty_or_nonempty with h | hs
  · subst h; simp at hge
  · have : s.card * (∑ t ∈ s, min (flat Srow (T t)).rank (flat Scol (T t)).rank)
        < s.card * Fintype.card α ^ 8 := by
      calc s.card * (∑ t ∈ s, min (flat Srow (T t)).rank (flat Scol (T t)).rank)
          = ∑ t ∈ s, s.card * min (flat Srow (T t)).rank (flat Scol (T t)).rank := by
            rw [Finset.mul_sum]
        _ < ∑ _t ∈ s, Fintype.card α ^ 8 := Finset.sum_lt_sum_of_nonempty hs hcon
        _ = s.card * Fintype.card α ^ 8 := by simp
    have := Nat.mul_le_mul_left s.card hge
    omega

end Grid33

#print axioms Grid33.rankSum_ge
#print axioms Grid33.exists_expensive
#check @Grid33.rankSum_ge
