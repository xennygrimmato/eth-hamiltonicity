/-
# Search to counting: the edge-deletion self-reduction

`cor:decision-search` of `paper/main.tex`, part *search*. Let `P` be a property of edge sets, and
`D 0, D 1, …` sets of edges to try to delete. Starting from `G`, at step `k` delete `D k` if and
only if the resulting graph still contains an edge set with `P` (`srStep`, `srSeq`). If `G`
contains one, and every edge `f` of `G` is tried alone at some step `k < K` (`f ∈ D k ⊆ {f}`),
then the graph after `K` steps *is* an edge set with `P` (`srSeq_correct`, `srSeq_final`):
every intermediate graph contains the final one, and an edge `f` of the final graph outside a
witness would have been deleted when it was tried.

`delSet n k` is the edge `s(u, w)` with `u·n + w = k` (the entry `k` of the adjacency matrix
written row by row); the steps `k < n²` try every edge alone (`cover_delSet`).

Mathlib only (beyond `EthFollowup.HamiltonianParity`, for `graphOf`).
-/
import EthFollowup.HamiltonianParity

namespace EthFollowup.ExactHC

open EthFollowup.Hamiltonian

section SelfReduction

variable {V : Type*}

open Classical in
/-- One step of the self-reduction: delete `D` if what is left still contains an edge set with
`P`. -/
noncomputable def srStep (P : Set (Sym2 V) → Prop) (H : SimpleGraph V) (D : Set (Sym2 V)) :
    SimpleGraph V :=
  if ∃ X, X ⊆ (H.deleteEdges D).edgeSet ∧ P X then H.deleteEdges D else H

/-- The graphs of the self-reduction: `srSeq P G D k` after `k` steps. -/
noncomputable def srSeq (P : Set (Sym2 V) → Prop) (G : SimpleGraph V) (D : ℕ → Set (Sym2 V)) :
    ℕ → SimpleGraph V
  | 0 => G
  | k + 1 => srStep P (srSeq P G D k) (D k)

variable {P : Set (Sym2 V) → Prop} {G H : SimpleGraph V} {D : ℕ → Set (Sym2 V)}

theorem srStep_pos {E : Set (Sym2 V)} (h : ∃ X, X ⊆ (H.deleteEdges E).edgeSet ∧ P X) :
    srStep P H E = H.deleteEdges E := by
  classical
  unfold srStep; simp only [h, ↓reduceIte]

theorem srStep_neg {E : Set (Sym2 V)} (h : ¬∃ X, X ⊆ (H.deleteEdges E).edgeSet ∧ P X) :
    srStep P H E = H := by
  classical
  unfold srStep; simp only [h, ↓reduceIte]

theorem srStep_le (E : Set (Sym2 V)) : srStep P H E ≤ H := by
  classical
  unfold srStep
  split_ifs
  · exact H.deleteEdges_le E
  · exact le_rfl

theorem srSeq_succ (k : ℕ) : srSeq P G D (k + 1) = srStep P (srSeq P G D k) (D k) := rfl

theorem srSeq_anti {k k' : ℕ} (h : k ≤ k') : srSeq P G D k' ≤ srSeq P G D k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (srStep_le _).trans ih

theorem srSeq_le (k : ℕ) : srSeq P G D k ≤ G := srSeq_anti (Nat.zero_le k)

/-- The invariant: an edge set with `P` survives every step. -/
theorem srSeq_inv (hG : ∃ X, X ⊆ G.edgeSet ∧ P X) (k : ℕ) :
    ∃ X, X ⊆ (srSeq P G D k).edgeSet ∧ P X := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    rw [srSeq_succ]
    by_cases h : ∃ X, X ⊆ ((srSeq P G D k).deleteEdges (D k)).edgeSet ∧ P X
    · rw [srStep_pos h]; exact h
    · rw [srStep_neg h]; exact ih

/-- **The self-reduction is correct**: the final graph is itself an edge set with `P`. -/
theorem srSeq_correct {K : ℕ} (hG : ∃ X, X ⊆ G.edgeSet ∧ P X)
    (hcov : ∀ f ∈ G.edgeSet, ∃ k < K, f ∈ D k ∧ D k ⊆ {f}) : P (srSeq P G D K).edgeSet := by
  obtain ⟨X, hXF, hPX⟩ := srSeq_inv (D := D) hG K
  suffices e : (srSeq P G D K).edgeSet = X by rw [e]; exact hPX
  refine Set.Subset.antisymm (fun f hf => ?_) hXF
  by_contra hfX
  have hfG : f ∈ G.edgeSet := SimpleGraph.edgeSet_subset_edgeSet.2 (srSeq_le K) hf
  obtain ⟨k, hk, hfD, hD⟩ := hcov f hfG
  have hXk : X ⊆ ((srSeq P G D k).deleteEdges (D k)).edgeSet := by
    intro x hx
    rw [SimpleGraph.edgeSet_deleteEdges]
    refine ⟨SimpleGraph.edgeSet_subset_edgeSet.2 (srSeq_anti hk.le) (hXF hx), fun hxD => ?_⟩
    have : x = f := hD hxD
    exact hfX (this ▸ hx)
  have e1 : srSeq P G D (k + 1) = (srSeq P G D k).deleteEdges (D k) := by
    rw [srSeq_succ, srStep_pos ⟨X, hXk, hPX⟩]
  have h2 : f ∈ (srSeq P G D (k + 1)).edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.2 (srSeq_anti (by omega)) hf
  rw [e1, SimpleGraph.edgeSet_deleteEdges] at h2
  exact h2.2 hfD

/-- An edge set given by a finset with the property `Q`. -/
def ofFin {n : ℕ} (Q : Finset (Sym2 (Fin n)) → Prop) (S : Set (Sym2 (Fin n))) : Prop :=
  ∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) = S ∧ Q X

theorem exists_ofFin_iff {n : ℕ} {Q : Finset (Sym2 (Fin n)) → Prop} {H : SimpleGraph (Fin n)} :
    (∃ S, S ⊆ H.edgeSet ∧ ofFin Q S) ↔ ∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ H.edgeSet ∧ Q X :=
  ⟨fun ⟨_, hS, X, hX, hQ⟩ => ⟨X, hX ▸ hS, hQ⟩, fun ⟨X, hX, hQ⟩ => ⟨X, hX, X, rfl, hQ⟩⟩

/-- **The final graph, for a property of finsets**: if `G` contains an edge set `X` with `Q`, the
final graph of the self-reduction is `graphOf X` for some such `X ⊆ E(G)`. -/
theorem srSeq_final {n K : ℕ} {Q : Finset (Sym2 (Fin n)) → Prop} {G : SimpleGraph (Fin n)}
    {D : ℕ → Set (Sym2 (Fin n))}
    (hG : ∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ Q X)
    (hcov : ∀ f ∈ G.edgeSet, ∃ k < K, f ∈ D k ∧ D k ⊆ {f}) :
    ∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ Q X ∧
      srSeq (ofFin Q) G D K = graphOf X := by
  obtain ⟨X, hX, hQ⟩ := srSeq_correct (exists_ofFin_iff.2 hG) hcov
  refine ⟨X, ?_, hQ, ?_⟩
  · rw [hX]; exact SimpleGraph.edgeSet_subset_edgeSet.2 (srSeq_le K)
  · rw [graphOf, hX, SimpleGraph.fromEdgeSet_edgeSet]

end SelfReduction

/-! ### The matrix entries as edges -/

section DelSet

variable {n : ℕ}

/-- The edge of the entry `k = u·n + w` of the adjacency matrix. -/
def delSet (n k : ℕ) : Set (Sym2 (Fin n)) := {e | ∃ u w : Fin n, (u : ℕ) * n + w = k ∧ e = s(u, w)}

theorem mem_delSet {k : ℕ} {i j : Fin n} :
    s(i, j) ∈ delSet n k ↔ (i : ℕ) * n + j = k ∨ (j : ℕ) * n + i = k := by
  constructor
  · rintro ⟨u, w, hk, he⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hk
    · exact Or.inr hk
  · rintro (h | h)
    · exact ⟨i, j, h, rfl⟩
    · exact ⟨j, i, h, Sym2.eq_swap⟩

theorem idx_inj {u w u' w' : Fin n} (h : (u' : ℕ) * n + w' = (u : ℕ) * n + w) : u' = u ∧ w' = w := by
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h0 => by subst h0; exact u.elim0)
  have hw : (w' : ℕ) = w := by
    have := congrArg (· % n) h
    simp only [add_comm _ (w' : ℕ), add_comm _ (w : ℕ), Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt w'.2, Nat.mod_eq_of_lt w.2] at this
    exact this
  have hu : (u' : ℕ) * n = u * n := by omega
  exact ⟨Fin.ext (Nat.eq_of_mul_eq_mul_right hn hu), Fin.ext hw⟩

/-- **Every edge is tried alone** at some step `k < n²`. -/
theorem cover_delSet (G : SimpleGraph (Fin n)) :
    ∀ f ∈ G.edgeSet, ∃ k < n * n, f ∈ delSet n k ∧ delSet n k ⊆ {f} := by
  intro f _
  induction f using Sym2.ind with
  | _ u w =>
  refine ⟨u * n + w, ?_, ⟨u, w, rfl, rfl⟩, ?_⟩
  · have h1 := u.2; have h2 := w.2
    calc (u : ℕ) * n + w < u * n + n := by omega
      _ = (u + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right _ h1
  · rintro e ⟨u', w', hk, rfl⟩
    obtain ⟨rfl, rfl⟩ := idx_inj hk
    rfl

end DelSet

end EthFollowup.ExactHC
