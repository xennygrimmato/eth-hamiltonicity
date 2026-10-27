/-
# Exact counting of Hamiltonian cycles via spanning trees of 2-factors

For a graph `G` on `Fin n`,

  `n · #HC(G) = Σ_{X 2-factor of G} τ(X)`                    (`n_mul_hamCycles_eq_sum`)

where `τ(X)` is the number of spanning trees of the spanning subgraph `(Fin n, X)`.
The key lemma (`card_spanningTrees_of_twoFactor`): for a loop-free 2-regular edge set `X`,
`τ(X) = n` if `(Fin n, X)` is connected (a Hamiltonian cycle, whose spanning trees are exactly
`X` minus one edge) and `τ(X) = 0` otherwise (a spanning tree of a subgraph would connect it).
No lower bound on `n` is needed: for `n ≤ 2` there are no loop-free 2-factors when `n ≥ 1`,
and for `n = 0` the empty 2-factor is disconnected (`Fin 0` is empty) and has no spanning tree.
-/
import EthFollowup.HamiltonianParity

-- `card_spanningTrees`: one tactic branch is dead on each of the two pinned Mathlib versions.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace EthFollowup.Hamiltonian

open SimpleGraph Finset

variable {n : ℕ}

/-- Spanning trees of `(Fin n, X)`: edge subsets `T ⊆ X` with `(Fin n, T)` a tree (connected and
acyclic on all `n` vertices). -/
noncomputable def spanningTrees (X : Finset (Sym2 (Fin n))) : Finset (Finset (Sym2 (Fin n))) := by
  classical exact X.powerset.filter fun T => (graphOf T).IsTree

theorem mem_spanningTrees {X T : Finset (Sym2 (Fin n))} :
    T ∈ spanningTrees X ↔ T ⊆ X ∧ (graphOf T).IsTree := by
  classical
  simp [spanningTrees]

/-- No edge of `X` is a loop. -/
def LoopFree (X : Finset (Sym2 (Fin n))) : Prop := ∀ e ∈ X, ¬ e.IsDiag

theorem LoopFree.mono {X Y : Finset (Sym2 (Fin n))} (hY : LoopFree Y) (h : X ⊆ Y) :
    LoopFree X := fun e he => hY e (h he)

theorem loopFree_of_mem_twoFactors (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {X : Finset (Sym2 (Fin n))} (hX : X ∈ twoFactors G) : LoopFree X := by
  intro e he
  simp only [twoFactors, Finset.mem_filter, Finset.mem_powerset] at hX
  exact G.not_isDiag_of_mem_edgeSet (by simpa using hX.1 he)

theorem nat_card_edgeSet_graphOf {X : Finset (Sym2 (Fin n))} (hl : LoopFree X) :
    Nat.card (graphOf X).edgeSet = X.card := by
  rw [edgeSet_fromEdgeSet]
  have : (X : Set (Sym2 (Fin n))) \ Sym2.diagSet = X := by
    ext e
    simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet, and_iff_left_iff_imp]
    exact hl e
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- In a loop-free edge set, the neighbourhood of `v` has as many elements as edges at `v`. -/
theorem ncard_neighborSet_graphOf {X : Finset (Sym2 (Fin n))} (hl : LoopFree X) (v : Fin n) :
    ((graphOf X).neighborSet v).ncard = (X.filter fun e => v ∈ e).card := by
  have hN : (graphOf X).neighborSet v =
      ((Finset.univ.filter fun w => s(v, w) ∈ X : Finset (Fin n)) : Set (Fin n)) := by
    ext w
    simp only [mem_neighborSet, fromEdgeSet_adj, Set.mem_ofPred_eq, Finset.coe_filter,
      Finset.mem_univ, true_and, Finset.mem_coe]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, fun hvw => hl _ h ?_⟩
      simp [hvw]
  have hF : (X.filter fun e => v ∈ e) =
      (Finset.univ.filter fun w => s(v, w) ∈ X).image (fun w => s(v, w)) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨he, rfl | rfl⟩
        · exact ⟨b, he, rfl⟩
        · exact ⟨a, by rwa [Sym2.eq_swap], Sym2.eq_swap⟩
      · rintro ⟨w, hw, hwe⟩
        have hv : v ∈ s(a, b) := hwe ▸ Sym2.mem_mk_left v w
        exact ⟨hwe ▸ hw, Sym2.mem_iff.1 hv⟩
  rw [hN, Set.ncard_coe_finset, hF, Finset.card_image_of_injective]
  intro a b h
  exact Sym2.congr_right.1 h

theorem isCycles_graphOf {X : Finset (Sym2 (Fin n))} (hX : TwoRegular X) (hl : LoopFree X) :
    (graphOf X).IsCycles := by
  intro v _
  rw [ncard_neighborSet_graphOf hl, hX v]

/-- A loop-free 2-regular edge set on `n` vertices has exactly `n` edges. -/
theorem card_eq_of_twoRegular {X : Finset (Sym2 (Fin n))} (hX : TwoRegular X)
    (hl : LoopFree X) : X.card = n := by
  have h1 : ∑ v : Fin n, (X.filter fun e => v ∈ e).card = 2 * n := by
    rw [Finset.sum_congr rfl (fun v _ => hX v)]
    simp [mul_comm]
  have h2 : ∑ v : Fin n, (X.filter fun e => v ∈ e).card =
      ∑ e ∈ X, (Finset.univ.filter fun v : Fin n => v ∈ e).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h3 : ∀ e ∈ X, (Finset.univ.filter fun v : Fin n => v ∈ e).card = 2 := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := fun h => hl _ he (by simp [h])
      have : (Finset.univ.filter fun v : Fin n => v ∈ s(a, b)) = {a, b} := by
        ext v; simp
      rw [this, Finset.card_pair hab]
  rw [h2, Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul] at h1
  omega

/-- Deleting one edge of a 2-factor. -/
theorem graphOf_erase (X : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    graphOf (X.erase e) = (graphOf X).deleteEdges {e} := by
  rw [deleteEdges, ← fromEdgeSet_sdiff]
  show fromEdgeSet ((X.erase e : Finset _) : Set (Sym2 (Fin n))) = _
  rw [Finset.coe_erase]

/-- Disconnected case: no spanning tree. -/
theorem spanningTrees_eq_empty_of_not_connected {X : Finset (Sym2 (Fin n))}
    (hc : ¬ (graphOf X).Connected) : spanningTrees X = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro T hT
  obtain ⟨hTX, htree⟩ := mem_spanningTrees.1 hT
  exact hc (htree.connected.mono (fromEdgeSet_mono (by exact_mod_cast hTX)))

/-- Connected case: the spanning trees are exactly `X` minus one edge. -/
theorem spanningTrees_eq_image_erase {X : Finset (Sym2 (Fin n))} (hX : TwoRegular X)
    (hl : LoopFree X) (hc : (graphOf X).Connected) :
    spanningTrees X = X.image fun e => X.erase e := by
  have hcard := card_eq_of_twoRegular hX hl
  ext T
  rw [mem_spanningTrees, Finset.mem_image]
  constructor
  · rintro ⟨hTX, htree⟩
    have hT := (isTree_iff_connected_and_card.1 htree).2
    rw [nat_card_edgeSet_graphOf (hl.mono hTX), Nat.card_eq_fintype_card,
      Fintype.card_fin] at hT
    have hsd := Finset.card_sdiff_add_card_eq_card hTX
    obtain ⟨e, he⟩ := Finset.card_eq_one.1 (show (X \ T).card = 1 by omega)
    have heX : e ∈ X \ T := by rw [he]; exact Finset.mem_singleton_self e
    refine ⟨e, (Finset.mem_sdiff.1 heX).1, ?_⟩
    ext x
    rw [Finset.mem_erase]
    constructor
    · rintro ⟨hxe, hxX⟩
      by_contra hxT
      have : x ∈ X \ T := Finset.mem_sdiff.2 ⟨hxX, hxT⟩
      rw [he, Finset.mem_singleton] at this
      exact hxe this
    · intro hxT
      refine ⟨?_, hTX hxT⟩
      rintro rfl
      exact (Finset.mem_sdiff.1 heX).2 hxT
  · rintro ⟨e, heX, rfl⟩
    refine ⟨Finset.erase_subset e X, ?_⟩
    rw [isTree_iff_connected_and_card, nat_card_edgeSet_graphOf (hl.mono (Finset.erase_subset e X)),
      Nat.card_eq_fintype_card, Fintype.card_fin, Finset.card_erase_of_mem heX, hcard]
    have hpos : 0 < n := hcard ▸ Finset.card_pos.2 ⟨e, heX⟩
    refine ⟨?_, by omega⟩
    rw [graphOf_erase]
    have hnb : ¬ (graphOf X).IsBridge e := by
      induction e using Sym2.ind with
      | _ u v =>
        have hadj : (graphOf X).Adj u v := by
          rw [fromEdgeSet_adj]
          exact ⟨heX, fun h => hl _ heX (by simp [h])⟩
        rw [isBridge_iff]
        exact fun h => h ((isCycles_graphOf hX hl).reachable_deleteEdges hadj)
    -- The name and hypotheses of this Mathlib lemma differ between the two pinned Mathlib versions.
    first
      | exact hc.preconnected.connected_deleteEdges_of_not_isBridge hnb
      | (induction e using Sym2.ind with
          | _ u v => exact hc.connected_delete_edge_of_not_isBridge hnb)

/-- Key lemma, connected case: a Hamiltonian cycle on `n` vertices has `n` spanning trees. -/
theorem card_spanningTrees_of_connected {X : Finset (Sym2 (Fin n))} (hX : TwoRegular X)
    (hl : LoopFree X) (hc : (graphOf X).Connected) : (spanningTrees X).card = n := by
  rw [spanningTrees_eq_image_erase hX hl hc, Finset.card_image_of_injOn,
    card_eq_of_twoRegular hX hl]
  intro e he e' he' h
  by_contra hne
  have : e ∈ X.erase e' := Finset.mem_erase.2 ⟨hne, he⟩
  simp only at h
  rw [← h] at this
  exact Finset.notMem_erase e X this

/-- Key lemma: for a loop-free 2-regular edge set `X` on `Fin n`, `τ(X) = n` if `(Fin n, X)` is
connected and `0` otherwise. -/
theorem card_spanningTrees_of_twoFactor {X : Finset (Sym2 (Fin n))} (hX : TwoRegular X)
    (hl : LoopFree X) :
    (spanningTrees X).card = if (graphOf X).Connected then n else 0 := by
  split_ifs with hc
  · exact card_spanningTrees_of_connected hX hl hc
  · rw [spanningTrees_eq_empty_of_not_connected hc, Finset.card_empty]

/-- The same, for a 2-factor of a simple graph `G`. -/
theorem card_spanningTrees_of_mem_twoFactors (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {X : Finset (Sym2 (Fin n))} (hX : X ∈ twoFactors G) :
    (spanningTrees X).card = if (graphOf X).Connected then n else 0 :=
  card_spanningTrees_of_twoFactor (Finset.mem_filter.1 hX).2 (loopFree_of_mem_twoFactors G hX)

/-- **Exact Hamiltonian-cycle counting identity.** `n · #HC(G) = Σ_{X 2-factor} τ(X)`. -/
theorem n_mul_hamCycles_eq_sum (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    n * (hamCycles G).card = ∑ X ∈ twoFactors G, (spanningTrees X).card := by
  rw [hamCycles, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun X hX => ?_
  rw [card_spanningTrees_of_mem_twoFactors G hX]
  split_ifs <;> simp

end EthFollowup.Hamiltonian
