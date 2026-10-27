/-
# Reduced incidence matrices of `n − 1` edges (module M2, inside Lemma 3.3)

Vertices `Fin n`, a root `r : Fin n`. An edge `e = s(a, b)` with `a ≠ b` is oriented from its low
end to its high end: its incidence vector is `1_{min a b} − 1_{max a b}` (`inc`). A loop gets the
zero vector (loops never occur in the application; this convention removes a side condition).

The reduced incidence matrix `incMatrix F r` of an edge set `F` has rows `{u // u ≠ r}` and
columns `F`. Given any bijection `φ : {u // u ≠ r} ≃ F` (so `|F| = n − 1`), `redInc F r φ` is the
square matrix obtained by indexing the columns through `φ`. Main results:

* `det_redInc_sq_of_isTree`: if `(Fin n, F)` is a tree, `det (redInc F r φ) ^ 2 = 1`;
* `det_redInc_eq_zero_of_not_isTree`: otherwise `det (redInc F r φ) = 0`;
* `det_redInc_sq`, `det_redInc_sq_eq_zero_or_one`: the combined forms;
* `det_sq_mul_signs`: re-orienting edges (column signs `±1`) does not change `det ^ 2`;
* `sum_detSq_eq_card_spanningTreeSet`: for loop-free `X`,
  `Σ_{F ⊆ X, |F| = n − 1} det(B_F)^2 = #{T ⊆ X : (Fin n, T) is a tree}`.

The tree notion is `(SimpleGraph.fromEdgeSet (F : Set _)).IsTree`, which is definitionally
`(EthFollowup.Hamiltonian.graphOf F).IsTree`, and `spanningTreeSet` is defined by the same term as
`EthFollowup.Hamiltonian.spanningTrees`.

Proof. Disconnected: the rows of the vertices not reachable from `r` sum to zero. Tree: with the
parent-edge bijection `u ↦ s(u, parent u)` (parent = a neighbour closer to `r`), the matrix is
triangular with respect to the distance to `r`, with diagonal entries `±1`; any other bijection
permutes the columns, which changes `det` only by a sign.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace EthFollowup.ExactHC

open SimpleGraph Finset Matrix

variable {n : ℕ}

/-! ### Signed incidence -/

/-- Entry of the edge `s(a, b)` at vertex `u`: `+1` at the low end, `−1` at the high end, `0`
elsewhere and for loops. -/
def incAux (u a b : Fin n) : ℤ :=
  if a = b then 0 else (if u = min a b then 1 else 0) - (if u = max a b then 1 else 0)

theorem incAux_comm (u a b : Fin n) : incAux u a b = incAux u b a := by
  unfold incAux
  rw [min_comm, max_comm]
  by_cases h : a = b
  · simp [h]
  · simp [h, Ne.symm h]

/-- Signed incidence of the vertex `u` in the edge `e` (orientation from low end to high end). -/
def inc (e : Sym2 (Fin n)) (u : Fin n) : ℤ :=
  Sym2.lift ⟨fun a b => incAux u a b, fun a b => incAux_comm u a b⟩ e

@[simp] theorem inc_mk (a b u : Fin n) : inc s(a, b) u = incAux u a b := rfl

theorem inc_eq_zero_of_notMem {e : Sym2 (Fin n)} {u : Fin n} (hu : u ∉ e) : inc e u = 0 := by
  induction e using Sym2.ind with
  | _ a b =>
    have h1 : u ≠ min a b := by
      rcases min_choice a b with h | h <;> rw [h] <;> intro hc <;> exact hu (by simp [hc])
    have h2 : u ≠ max a b := by
      rcases max_choice a b with h | h <;> rw [h] <;> intro hc <;> exact hu (by simp [hc])
    simp [incAux, h1, h2]

theorem inc_sq_of_ne {a b : Fin n} (hab : a ≠ b) : inc s(a, b) a ^ 2 = 1 := by
  simp only [inc_mk, incAux, hab, ↓reduceIte]
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]; simp [hab]
  · rw [min_eq_right h, max_eq_left h]; simp [hab]

/-- Pairing a vertex function with an incidence column. -/
theorem sum_mul_inc (x : Fin n → ℤ) (a b : Fin n) :
    ∑ u, x u * inc s(a, b) u = if a = b then 0 else x (min a b) - x (max a b) := by
  by_cases hab : a = b
  · simp [incAux, hab]
  · simp only [inc_mk, incAux, hab, ↓reduceIte, mul_sub, mul_ite, mul_one, mul_zero,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]

/-! ### The reduced incidence matrix -/

/-- Reduced signed incidence matrix: rows `V ∖ {r}`, columns `F`. -/
def incMatrix (F : Finset (Sym2 (Fin n))) (r : Fin n) : Matrix {u : Fin n // u ≠ r} F ℤ :=
  Matrix.of fun u e => inc e.1 u.1

/-- The square reduced incidence matrix, columns indexed through a bijection `φ`. -/
def redInc (F : Finset (Sym2 (Fin n))) (r : Fin n) (φ : {u : Fin n // u ≠ r} ≃ F) :
    Matrix {u : Fin n // u ≠ r} {u : Fin n // u ≠ r} ℤ :=
  (incMatrix F r).submatrix id φ

@[simp] theorem redInc_apply (F : Finset (Sym2 (Fin n))) (r : Fin n)
    (φ : {u : Fin n // u ≠ r} ≃ F) (u w : {u : Fin n // u ≠ r}) :
    redInc F r φ u w = inc (φ w).1 u.1 := rfl

theorem card_ne_root (r : Fin n) : Fintype.card {u : Fin n // u ≠ r} = n - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]

/-! ### Disconnected case -/

theorem det_redInc_eq_zero_of_not_connected {F : Finset (Sym2 (Fin n))} {r : Fin n}
    (φ : {u : Fin n // u ≠ r} ≃ F)
    (hc : ¬ (fromEdgeSet (F : Set (Sym2 (Fin n)))).Connected) : (redInc F r φ).det = 0 := by
  classical
  set G := fromEdgeSet (F : Set (Sym2 (Fin n))) with hG
  have hv : ∃ v, ¬ G.Reachable r v := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hc ((connected_iff G).2 ⟨fun a b => (h a).symm.trans (h b), ⟨r⟩⟩)
  obtain ⟨v, hv⟩ := hv
  have hvr : v ≠ r := by rintro rfl; exact hv (Reachable.refl _)
  let x' : Fin n → ℤ := fun u => if G.Reachable r u then 0 else 1
  refine (exists_vecMul_eq_zero_iff).1 ⟨fun u => x' u.1, ?_, ?_⟩
  · intro h
    have := congrFun h ⟨v, hvr⟩
    simp [x', hv] at this
  · funext w
    simp only [vecMul, dotProduct, redInc_apply, Pi.zero_apply]
    have hsum : ∑ u : {u : Fin n // u ≠ r}, x' u.1 * inc (φ w).1 u.1 =
        ∑ u, x' u * inc (φ w).1 u := by
      rw [← Finset.sum_erase (s := Finset.univ) (a := r) (by simp [x'])]
      exact (Finset.sum_subtype _ (fun u => by simp) (fun u => x' u * inc (φ w).1 u)).symm
    rw [hsum]
    generalize φ w = f
    obtain ⟨e, he⟩ := f
    induction e using Sym2.ind with
    | _ a b =>
      rw [sum_mul_inc]
      split_ifs with hab
      · rfl
      · have hadj : G.Adj a b := by rw [hG, fromEdgeSet_adj]; exact ⟨he, hab⟩
        have hxab : x' a = x' b := by
          simp only [x']
          rw [show G.Reachable r a ↔ G.Reachable r b from
            ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩]
        have hmin : x' (min a b) = x' a := by
          rcases min_choice a b with h | h <;> rw [h]; exact hxab.symm
        have hmax : x' (max a b) = x' a := by
          rcases max_choice a b with h | h <;> rw [h]; exact hxab.symm
        rw [hmin, hmax, sub_self]

/-! ### Triangular determinants -/

/-- If every nonzero off-diagonal entry `M i j` has `d i < d j`, then `det M` is the product of
the diagonal entries. -/
theorem det_eq_prod_diag_of_lt {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (d : ι → ℕ) (h : ∀ i j, M i j ≠ 0 → i = j ∨ d i < d j) : M.det = ∏ i, M i i := by
  rw [det_apply, Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · simp
  · intro σ _ hσ
    have hp : ∏ i, M (σ i) i = 0 := by
      by_contra hne
      have hall : ∀ i, σ i = i ∨ d (σ i) < d i := fun i =>
        h _ _ (Finset.prod_ne_zero_iff.1 hne i (Finset.mem_univ i))
      obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
        by_contra hc
        simp only [not_exists, ne_eq, not_not] at hc
        exact hσ (Equiv.ext hc)
      have hlt : ∑ j, d (σ j) < ∑ j, d j := by
        apply Finset.sum_lt_sum
        · intro j _
          rcases hall j with hj | hj
          · rw [hj]
          · exact hj.le
        · exact ⟨i, Finset.mem_univ i, (hall i).resolve_left hi⟩
      rw [Equiv.sum_comp σ d] at hlt
      exact lt_irrefl _ hlt
    rw [hp, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Connected case -/

section Tree

variable {F : Finset (Sym2 (Fin n))} {r : Fin n}

/-- In a connected graph every vertex `u ≠ r` has a neighbour strictly closer to `r`. -/
theorem exists_parent (hc : (fromEdgeSet (F : Set (Sym2 (Fin n)))).Connected) (u : Fin n)
    (hu : u ≠ r) : ∃ w, s(u, w) ∈ F ∧ u ≠ w ∧
      (fromEdgeSet (F : Set (Sym2 (Fin n)))).dist w r <
        (fromEdgeSet (F : Set (Sym2 (Fin n)))).dist u r := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u r
  cases p with
  | nil => exact absurd rfl hu
  | cons h q =>
    rw [fromEdgeSet_adj] at h
    refine ⟨_, h.1, h.2, ?_⟩
    have := dist_le q
    rw [Walk.length_cons] at hp
    omega

/-- A parent of `u`: a neighbour closer to the root. -/
noncomputable def parent (hc : (fromEdgeSet (F : Set (Sym2 (Fin n)))).Connected)
    (u : {u : Fin n // u ≠ r}) : Fin n :=
  (exists_parent hc u.1 u.2).choose

theorem parent_spec (hc : (fromEdgeSet (F : Set (Sym2 (Fin n)))).Connected)
    (u : {u : Fin n // u ≠ r}) : s(u.1, parent hc u) ∈ F ∧ u.1 ≠ parent hc u ∧
      (fromEdgeSet (F : Set (Sym2 (Fin n)))).dist (parent hc u) r <
        (fromEdgeSet (F : Set (Sym2 (Fin n)))).dist u.1 r :=
  (exists_parent hc u.1 u.2).choose_spec

/-- The parent edge of `u`. -/
noncomputable def parentEdge (hc : (fromEdgeSet (F : Set (Sym2 (Fin n)))).Connected)
    (u : {u : Fin n // u ≠ r}) : F :=
  ⟨s(u.1, parent hc u), (parent_spec hc u).1⟩

theorem parentEdge_injective (hc : (fromEdgeSet (F : Set (Sym2 (Fin n)))).Connected) :
    Function.Injective (parentEdge (r := r) hc) := by
  intro u v huv
  have h : s(u.1, parent hc u) = s(v.1, parent hc v) := congrArg Subtype.val huv
  rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact Subtype.ext h1
  · exfalso
    have hu := (parent_spec hc u).2.2
    have hv := (parent_spec hc v).2.2
    rw [h2] at hu
    rw [← h1] at hv
    omega

/-- The parent-edge bijection (it exists as soon as some bijection `φ` does). -/
noncomputable def parentEquiv (hc : (fromEdgeSet (F : Set (Sym2 (Fin n)))).Connected)
    (φ : {u : Fin n // u ≠ r} ≃ F) : {u : Fin n // u ≠ r} ≃ F :=
  Equiv.ofBijective (parentEdge hc)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨parentEdge_injective hc, Fintype.card_congr φ⟩)

theorem det_redInc_parentEquiv_sq (hc : (fromEdgeSet (F : Set (Sym2 (Fin n)))).Connected)
    (φ : {u : Fin n // u ≠ r} ≃ F) : (redInc F r (parentEquiv hc φ)).det ^ 2 = 1 := by
  rw [det_eq_prod_diag_of_lt _ (fun u => (fromEdgeSet (F : Set (Sym2 (Fin n)))).dist u.1 r) ?_,
    ← Finset.prod_pow]
  · refine Finset.prod_eq_one fun w _ => ?_
    exact inc_sq_of_ne (parent_spec hc w).2.1
  · intro u w huw
    have hmem : u.1 ∈ s(w.1, parent hc w) := by
      by_contra hm
      exact huw (inc_eq_zero_of_notMem hm)
    rcases Sym2.mem_iff.1 hmem with h | h
    · exact Or.inl (Subtype.ext h)
    · right
      show _ < _
      rw [h]
      exact (parent_spec hc w).2.2

/-- Connected case: `det ^ 2 = 1` for every bijection `φ`. -/
theorem det_redInc_sq_of_connected (hc : (fromEdgeSet (F : Set (Sym2 (Fin n)))).Connected)
    (φ : {u : Fin n // u ≠ r} ≃ F) : (redInc F r φ).det ^ 2 = 1 := by
  have h : redInc F r φ =
      (redInc F r (parentEquiv hc φ)).submatrix id (φ.trans (parentEquiv hc φ).symm) := by
    ext u w
    simp [redInc_apply]
  rw [h, det_permute', mul_pow, det_redInc_parentEquiv_sq, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (φ.trans (parentEquiv hc φ).symm)) with h | h <;>
    rw [h] <;> simp

/-- With `n − 1` edges, connected implies tree. -/
theorem isTree_of_connected (φ : {u : Fin n // u ≠ r} ≃ F)
    (hc : (fromEdgeSet (F : Set (Sym2 (Fin n)))).Connected) :
    (fromEdgeSet (F : Set (Sym2 (Fin n)))).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨hc, le_antisymm ?_ hc.card_vert_le_card_edgeSet_add_one⟩
  have hF : F.card = n - 1 := by
    rw [← Fintype.card_coe, ← Fintype.card_congr φ, card_ne_root]
  have hn : 0 < n := Fin.pos r
  have hE : Nat.card (fromEdgeSet (F : Set (Sym2 (Fin n)))).edgeSet ≤ F.card := by
    rw [edgeSet_fromEdgeSet, Nat.card_coe_set_eq, ← Set.ncard_coe_finset F]
    exact Set.ncard_le_ncard (fun e he => he.1) (Finset.finite_toSet F)
  rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  omega

end Tree

/-! ### Main statements -/

section Main

variable {F : Finset (Sym2 (Fin n))} {r : Fin n}

/-- **Tree case.** If `(Fin n, F)` is a tree, `det(B_F)^2 = 1` for every bijection `φ`. -/
theorem det_redInc_sq_of_isTree (φ : {u : Fin n // u ≠ r} ≃ F)
    (ht : (fromEdgeSet (F : Set (Sym2 (Fin n)))).IsTree) : (redInc F r φ).det ^ 2 = 1 :=
  det_redInc_sq_of_connected ht.connected φ

/-- **Non-tree case.** If `(Fin n, F)` is not a tree, `det(B_F) = 0` for every bijection `φ`. -/
theorem det_redInc_eq_zero_of_not_isTree (φ : {u : Fin n // u ≠ r} ≃ F)
    (ht : ¬ (fromEdgeSet (F : Set (Sym2 (Fin n)))).IsTree) : (redInc F r φ).det = 0 :=
  det_redInc_eq_zero_of_not_connected φ fun hc => ht (isTree_of_connected φ hc)

open Classical in
/-- `det(B_F)^2 = [(Fin n, F) is a spanning tree]`, for every bijection `φ`. -/
theorem det_redInc_sq (φ : {u : Fin n // u ≠ r} ≃ F) :
    (redInc F r φ).det ^ 2 =
      if (fromEdgeSet (F : Set (Sym2 (Fin n)))).IsTree then 1 else 0 := by
  split_ifs with ht
  · exact det_redInc_sq_of_isTree φ ht
  · rw [det_redInc_eq_zero_of_not_isTree φ ht]
    norm_num

theorem det_redInc_sq_eq_zero_or_one (φ : {u : Fin n // u ≠ r} ≃ F) :
    (redInc F r φ).det ^ 2 = 0 ∨ (redInc F r φ).det ^ 2 = 1 := by
  by_cases ht : (fromEdgeSet (F : Set (Sym2 (Fin n)))).IsTree
  · exact Or.inr (det_redInc_sq_of_isTree φ ht)
  · left
    rw [det_redInc_eq_zero_of_not_isTree φ ht]
    norm_num

/-- Re-orienting columns (multiplying them by signs `±1`) does not change `det ^ 2`. -/
theorem det_sq_mul_signs {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (ε : ι → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (Matrix.of fun i j => M i j * ε j).det ^ 2 = M.det ^ 2 := by
  have h : (Matrix.of fun i j => M i j * ε j) = M * diagonal ε := by
    ext i j
    simp [mul_diagonal]
  rw [h, det_mul, det_diagonal, mul_pow, ← Finset.prod_pow, Finset.prod_eq_one, mul_one]
  intro i _
  rcases hε i with h | h <;> simp [h]

/-- The statement for an arbitrary orientation of the edges: column `w` is `± inc (φ w)`. -/
theorem det_sq_reoriented (φ : {u : Fin n // u ≠ r} ≃ F)
    (ε : {u : Fin n // u ≠ r} → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (Matrix.of fun u w => redInc F r φ u w * ε w).det ^ 2 = (redInc F r φ).det ^ 2 :=
  det_sq_mul_signs _ ε hε

end Main

/-! ### Summing over `(n − 1)`-subsets -/

/-- `det(B_F)^2` for an edge set `F`, using some bijection `{u // u ≠ r} ≃ F` (and `0` when
`|F| ≠ n − 1`). By `det_redInc_sq` the choice of bijection does not matter. -/
noncomputable def detSq (F : Finset (Sym2 (Fin n))) (r : Fin n) : ℤ :=
  if h : Fintype.card {u : Fin n // u ≠ r} = Fintype.card F then
    (redInc F r (Fintype.equivOfCardEq h)).det ^ 2
  else 0

open Classical in
theorem detSq_eq {F : Finset (Sym2 (Fin n))} {r : Fin n} (hF : F.card = n - 1) :
    detSq F r = if (fromEdgeSet (F : Set (Sym2 (Fin n)))).IsTree then 1 else 0 := by
  have h : Fintype.card {u : Fin n // u ≠ r} = Fintype.card F := by
    rw [card_ne_root, Fintype.card_coe, hF]
  unfold detSq
  split
  · exact det_redInc_sq _
  · contradiction

/-- Spanning trees inside `X` (the same term as `EthFollowup.Hamiltonian.spanningTrees`). -/
noncomputable def spanningTreeSet (X : Finset (Sym2 (Fin n))) :
    Finset (Finset (Sym2 (Fin n))) := by
  classical exact X.powerset.filter fun T => (fromEdgeSet (T : Set (Sym2 (Fin n)))).IsTree

theorem mem_spanningTreeSet {X T : Finset (Sym2 (Fin n))} :
    T ∈ spanningTreeSet X ↔ T ⊆ X ∧ (fromEdgeSet (T : Set (Sym2 (Fin n)))).IsTree := by
  classical
  simp [spanningTreeSet]

/-- A loop-free spanning tree on `Fin n` has `n − 1` edges. -/
theorem card_eq_of_isTree {T : Finset (Sym2 (Fin n))} (hl : ∀ e ∈ T, ¬ e.IsDiag)
    (ht : (fromEdgeSet (T : Set (Sym2 (Fin n)))).IsTree) : T.card = n - 1 := by
  have h := (isTree_iff_connected_and_card.1 ht).2
  have hE : Nat.card (fromEdgeSet (T : Set (Sym2 (Fin n)))).edgeSet = T.card := by
    rw [edgeSet_fromEdgeSet]
    have : (T : Set (Sym2 (Fin n))) \ Sym2.diagSet = T := by
      ext e
      exact ⟨fun h => h.1, fun h => ⟨h, fun hd => hl e h (Sym2.mem_diagSet.1 hd)⟩⟩
    rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hE, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

/-- **Sum form (inside Lemma 3.3).** For a loop-free `X`,
`Σ_{F ⊆ X, |F| = n − 1} det(B_F)^2 = #{spanning trees T ⊆ X}`. -/
theorem sum_detSq_eq_card_spanningTreeSet (X : Finset (Sym2 (Fin n))) (r : Fin n)
    (hl : ∀ e ∈ X, ¬ e.IsDiag) :
    ∑ F ∈ X.powersetCard (n - 1), detSq F r = ((spanningTreeSet X).card : ℤ) := by
  classical
  rw [Finset.sum_congr rfl fun F hF => detSq_eq (r := r) (Finset.mem_powersetCard.1 hF).2,
    Finset.sum_boole]
  congr 2
  ext T
  rw [Finset.mem_filter, Finset.mem_powersetCard, mem_spanningTreeSet]
  constructor
  · rintro ⟨⟨hTX, _⟩, ht⟩
    exact ⟨hTX, ht⟩
  · rintro ⟨hTX, ht⟩
    exact ⟨⟨hTX, card_eq_of_isTree (fun e he => hl e (hTX he)) ht⟩, ht⟩

end EthFollowup.ExactHC
