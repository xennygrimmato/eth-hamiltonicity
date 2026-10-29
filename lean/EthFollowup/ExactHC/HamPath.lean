/-
# Hamiltonian paths as Hamiltonian cycles of the apex graph

`cor:decision-search` of `paper/main.tex`, part *paths*. A Hamiltonian path of `G` on `Fin n` is
an edge set `X ⊆ E(G)` of a spanning path: `|X| + 1 = n`, every vertex meets at most two edges of
`X`, and `(Fin n, X)` is connected (a connected spanning graph with `n − 1` edges is a tree, and a
tree of maximum degree `≤ 2` is a path) (`IsHamPath`, `hamPaths`). `apex G` on `Fin (n+1)` is `G`
plus the vertex `n` adjacent to all of `Fin n`.

**Main result** (`card_hamPaths_eq`): for `n ≥ 2`, `#HP(G) = #HC(apex G)`, by the bijection
`X ↦ X ∪ {s(a, n), s(b, n)}` (`a`, `b` the two ends of the path; `plusE`) with inverse
`Y ↦ Y` minus the two edges at the apex (`minusE`). That the inverse is connected is a parity
argument: a vertex set closed in `Y − apex` that contains exactly one of the two neighbours of the
apex would have an odd degree sum.

Mathlib only (beyond `EthFollowup.HamiltonianParity`, for `hamCycles`).
-/
import EthFollowup.HamiltonianParity

namespace EthFollowup.ExactHC

open Finset EthFollowup.Hamiltonian

/-! ## Degrees in an edge set -/

section Deg

variable {m : ℕ}

/-- The number of edges of `X` at `v`. -/
def degX (X : Finset (Sym2 (Fin m))) (v : Fin m) : ℕ := (X.filter fun e => v ∈ e).card

theorem twoRegular_iff (X : Finset (Sym2 (Fin m))) : TwoRegular X ↔ ∀ v, degX X v = 2 := Iff.rfl

/-- Double counting of the incidences between `R` and `X`. -/
theorem sum_degX (X : Finset (Sym2 (Fin m))) (R : Finset (Fin m)) :
    ∑ v ∈ R, degX X v = ∑ e ∈ X, (R.filter fun v => v ∈ e).card := by
  simp only [degX, card_filter]
  exact Finset.sum_comm

theorem card_filter_mem_pair (R : Finset (Fin m)) {a b : Fin m} (_hab : a ≠ b) :
    (R.filter fun v => v ∈ s(a, b)) = R ∩ {a, b} := by
  ext v; simp [Sym2.mem_iff]

/-- The handshake lemma for a loop-free edge set. -/
theorem sum_degX_univ (X : Finset (Sym2 (Fin m))) (hX : ∀ e ∈ X, ¬e.IsDiag) :
    ∑ v, degX X v = 2 * X.card := by
  rw [sum_degX, card_eq_sum_ones, mul_sum]
  refine sum_congr rfl fun e he => ?_
  have hd := hX e he
  induction e using Sym2.ind with
  | _ a b =>
  have hab : a ≠ b := fun h => hd (Sym2.mk_isDiag_iff.2 h)
  rw [card_filter_mem_pair _ hab, univ_inter, card_pair hab, mul_one]

/-- In a connected edge set on at least two vertices, every vertex meets an edge. -/
theorem one_le_degX {X : Finset (Sym2 (Fin m))} (hc : (graphOf X).Connected) (hm : 2 ≤ m)
    (v : Fin m) : 1 ≤ degX X v := by
  obtain ⟨u, hu⟩ : ∃ u : Fin m, u ≠ v := by
    by_cases h : (v : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
    · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
  obtain ⟨p⟩ := hc.preconnected v u
  cases p with
  | nil => exact absurd rfl hu
  | cons h _ =>
    rw [SimpleGraph.fromEdgeSet_adj] at h
    exact card_pos.2 ⟨_, mem_filter.2 ⟨h.1, Sym2.mem_mk_left _ _⟩⟩

end Deg

/-! ## Hamiltonian paths -/

section Paths

variable {n : ℕ}

/-- The edge set of a Hamiltonian path: `n − 1` edges, maximum degree `≤ 2`, connected. -/
def IsHamPath (X : Finset (Sym2 (Fin n))) : Prop :=
  X.card + 1 = n ∧ (∀ v, degX X v ≤ 2) ∧ (graphOf X).Connected

instance (X : Finset (Sym2 (Fin n))) : Decidable (IsHamPath X) := by
  unfold IsHamPath; infer_instance

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The Hamiltonian paths of `G`, as edge sets. -/
def hamPaths : Finset (Finset (Sym2 (Fin n))) := G.edgeFinset.powerset.filter IsHamPath

variable {G}

theorem mem_hamPaths {X : Finset (Sym2 (Fin n))} : X ∈ hamPaths G ↔ X ⊆ G.edgeFinset ∧ IsHamPath X := by
  simp [hamPaths]

theorem mem_hamCycles_iff_sub {X : Finset (Sym2 (Fin n))} :
    X ∈ hamCycles G ↔ X ⊆ G.edgeFinset ∧ TwoRegular X ∧ (graphOf X).Connected := by
  simp [hamCycles, twoFactors, and_assoc]

theorem not_isDiag_of_sub {X : Finset (Sym2 (Fin n))} (h : X ⊆ G.edgeFinset) : ∀ e ∈ X, ¬e.IsDiag :=
  fun _ he => G.not_isDiag_of_mem_edgeSet (G.mem_edgeFinset.1 (h he))

/-- The ends of a path: the vertices of degree one. -/
def ends (X : Finset (Sym2 (Fin n))) : Finset (Fin n) := univ.filter fun v => degX X v = 1

/-- A Hamiltonian path on `n ≥ 2` vertices has exactly two ends, and degree `1` or `2` at every
vertex. -/
theorem card_ends {X : Finset (Sym2 (Fin n))} (hX : IsHamPath X) (hd : ∀ e ∈ X, ¬e.IsDiag)
    (hn : 2 ≤ n) : (ends X).card = 2 := by
  obtain ⟨hc, hle, hconn⟩ := hX
  have hs := sum_degX_univ X hd
  have h12 : ∀ v, degX X v = if degX X v = 1 then 1 else 2 := fun v => by
    have := one_le_degX hconn hn v
    have := hle v
    split_ifs <;> omega
  rw [sum_congr rfl fun v _ => h12 v, sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul] at hs
  have hcard : ∑ v : Fin n, (if degX X v = 1 then 1 else 1) = n := by simp
  rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul] at hcard
  unfold ends
  omega

end Paths

/-! ## The apex graph -/

section Apex

variable {n : ℕ}

/-- `G` plus the vertex `n`, adjacent to all of `Fin n`. -/
def apex (G : SimpleGraph (Fin n)) : SimpleGraph (Fin (n + 1)) where
  Adj u v := u ≠ v ∧ ((u : ℕ) = n ∨ (v : ℕ) = n ∨
    ∃ (hu : (u : ℕ) < n) (hv : (v : ℕ) < n), G.Adj ⟨u, hu⟩ ⟨v, hv⟩)
  symm := ⟨fun u v ⟨h, h'⟩ => ⟨h.symm, by
    rcases h' with h' | h' | ⟨hu, hv, ha⟩
    · exact Or.inr (Or.inl h')
    · exact Or.inl h'
    · exact Or.inr (Or.inr ⟨hv, hu, ha.symm⟩)⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

instance (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : DecidableRel (apex G).Adj := fun u v =>
  decidable_of_iff (u ≠ v ∧ ((u : ℕ) = n ∨ (v : ℕ) = n ∨
    ∃ (hu : (u : ℕ) < n) (hv : (v : ℕ) < n), G.Adj ⟨u, hu⟩ ⟨v, hv⟩)) Iff.rfl

variable {G : SimpleGraph (Fin n)}

theorem apex_adj_cs {u v : Fin n} : (apex G).Adj u.castSucc v.castSucc ↔ G.Adj u v := by
  change _ ∧ _ ↔ _
  simp only [Fin.val_castSucc, ne_eq, Fin.castSucc_inj]
  constructor
  · rintro ⟨-, h | h | ⟨_, _, h⟩⟩
    · exact absurd h (by omega)
    · exact absurd h (by omega)
    · exact h
  · intro h
    exact ⟨G.ne_of_adj h, Or.inr (Or.inr ⟨u.2, v.2, h⟩)⟩

theorem apex_adj_last (u : Fin n) : (apex G).Adj u.castSucc (Fin.last n) :=
  ⟨Fin.castSucc_ne_last u, Or.inr (Or.inl rfl)⟩

end Apex

/-! ## Gluing an edge set with edges to the apex -/

section Glue

variable {n : ℕ}

/-- `Sym2.map Fin.castSucc`. -/
abbrev mapc (e : Sym2 (Fin n)) : Sym2 (Fin (n + 1)) := Sym2.map Fin.castSucc e

theorem mapc_mk (x y : Fin n) : mapc s(x, y) = s(x.castSucc, y.castSucc) := rfl

theorem mapc_inj : Function.Injective (mapc (n := n)) := Sym2.map.injective (Fin.castSucc_injective n)

theorem last_not_mem_mapc (e : Sym2 (Fin n)) : Fin.last n ∉ mapc e := by
  rw [Sym2.mem_map]
  rintro ⟨y, -, hy⟩
  exact Fin.castSucc_ne_last y hy

theorem cs_mem_mapc {v : Fin n} {e : Sym2 (Fin n)} : v.castSucc ∈ mapc e ↔ v ∈ e := by
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨y, hy, h⟩; rwa [← Fin.castSucc_inj.1 h]
  · intro h; exact ⟨v, h, rfl⟩

/-- The edge from `a` to the apex. -/
abbrev toL (a : Fin n) : Sym2 (Fin (n + 1)) := s(a.castSucc, Fin.last n)

theorem toL_inj : Function.Injective (toL (n := n)) := by
  intro a b h
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Fin.castSucc_inj.1 h1
  · exact absurd h1 (Fin.castSucc_ne_last a)

theorem mapc_ne_toL (e : Sym2 (Fin n)) (a : Fin n) : mapc e ≠ toL a := fun h =>
  last_not_mem_mapc e (h ▸ Sym2.mem_mk_right _ _)

/-- `X` on `Fin n` together with the edges from `N` to the apex. -/
def glue (X : Finset (Sym2 (Fin n))) (N : Finset (Fin n)) : Finset (Sym2 (Fin (n + 1))) :=
  X.image mapc ∪ N.image toL

/-- The edges of `Y` that avoid the apex, on `Fin n`. -/
def minusE (Y : Finset (Sym2 (Fin (n + 1)))) : Finset (Sym2 (Fin n)) := univ.filter fun e => mapc e ∈ Y

/-- The neighbours of the apex in `Y`. -/
def nbr (Y : Finset (Sym2 (Fin (n + 1)))) : Finset (Fin n) := univ.filter fun a => toL a ∈ Y

theorem mapc_mem_glue {X : Finset (Sym2 (Fin n))} {N : Finset (Fin n)} {e : Sym2 (Fin n)} :
    mapc e ∈ glue X N ↔ e ∈ X := by
  simp only [glue, mem_union, mem_image]
  constructor
  · rintro (⟨e', he', h⟩ | ⟨a, -, h⟩)
    · rwa [← mapc_inj h]
    · exact absurd h.symm (mapc_ne_toL e a)
  · intro h; exact Or.inl ⟨e, h, rfl⟩

theorem toL_mem_glue {X : Finset (Sym2 (Fin n))} {N : Finset (Fin n)} {a : Fin n} :
    toL a ∈ glue X N ↔ a ∈ N := by
  simp only [glue, mem_union, mem_image]
  constructor
  · rintro (⟨e, -, h⟩ | ⟨b, hb, h⟩)
    · exact absurd h (mapc_ne_toL e a)
    · rwa [← toL_inj h]
  · intro h; exact Or.inr ⟨a, h, rfl⟩

theorem minusE_glue (X : Finset (Sym2 (Fin n))) (N : Finset (Fin n)) : minusE (glue X N) = X := by
  ext e; simp [minusE, mapc_mem_glue]

theorem nbr_glue (X : Finset (Sym2 (Fin n))) (N : Finset (Fin n)) : nbr (glue X N) = N := by
  ext a; simp [nbr, toL_mem_glue]

/-- Every loop-free edge set on `Fin (n+1)` is glued from its two parts. -/
theorem glue_minusE_nbr {Y : Finset (Sym2 (Fin (n + 1)))} (hY : ∀ e ∈ Y, ¬e.IsDiag) :
    glue (minusE Y) (nbr Y) = Y := by
  ext e
  constructor
  · intro h
    simp only [glue, mem_union, mem_image, minusE, nbr, mem_filter, mem_univ, true_and] at h
    rcases h with ⟨e', he', rfl⟩ | ⟨a, ha, rfl⟩
    · exact he'
    · exact ha
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
    rcases Fin.eq_castSucc_or_eq_last x with ⟨x', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last y with ⟨y', rfl⟩ | rfl
    · have : mapc s(x', y') ∈ Y := by simpa [mapc_mk] using he
      have h := (mapc_mem_glue (N := nbr Y)).2 (show s(x', y') ∈ minusE Y by simpa [minusE] using this)
      simpa [mapc_mk] using h
    · exact toL_mem_glue.2 (by simpa [nbr] using he)
    · have h := toL_mem_glue (X := minusE Y) (N := nbr Y) (a := y')
      rw [Sym2.eq_swap]
      exact h.2 (by simpa [nbr, Sym2.eq_swap] using he)
    · exact absurd (Sym2.mk_isDiag_iff.2 rfl) (hY _ he)

theorem disjoint_glue (X : Finset (Sym2 (Fin n))) (N : Finset (Fin n)) :
    Disjoint (X.image mapc) (N.image toL) := by
  rw [disjoint_left]
  intro e h1 h2
  obtain ⟨e', -, rfl⟩ := mem_image.1 h1
  obtain ⟨a, -, h⟩ := mem_image.1 h2
  exact mapc_ne_toL e' a h.symm

theorem card_glue (X : Finset (Sym2 (Fin n))) (N : Finset (Fin n)) :
    (glue X N).card = X.card + N.card := by
  rw [glue, card_union_of_disjoint (disjoint_glue X N), card_image_of_injective _ mapc_inj,
    card_image_of_injective _ toL_inj]

theorem degX_glue_cs (X : Finset (Sym2 (Fin n))) (N : Finset (Fin n)) (v : Fin n) :
    degX (glue X N) v.castSucc = degX X v + if v ∈ N then 1 else 0 := by
  unfold degX glue
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter (disjoint_glue X N)),
    filter_image, filter_image, card_image_of_injective _ mapc_inj,
    card_image_of_injective _ toL_inj]
  congr 1
  · congr 1; ext e; simp
  · have : (N.filter fun a => v.castSucc ∈ toL a) = if v ∈ N then {v} else ∅ := by
      ext a
      simp only [mem_filter, toL, Sym2.mem_iff, Fin.castSucc_inj]
      split_ifs with h
      · simp only [mem_singleton]
        constructor
        · rintro ⟨-, h' | h'⟩
          · exact h'.symm
          · exact absurd h' (Fin.castSucc_ne_last v)
        · rintro rfl; exact ⟨h, Or.inl rfl⟩
      · simp only [notMem_empty, iff_false, not_and]
        rintro ha (h' | h')
        · exact h (h' ▸ ha)
        · exact Fin.castSucc_ne_last v h'
    rw [this]; split_ifs <;> simp

theorem degX_glue_last (X : Finset (Sym2 (Fin n))) (N : Finset (Fin n)) :
    degX (glue X N) (Fin.last n) = N.card := by
  unfold degX glue
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter (disjoint_glue X N)),
    filter_image, filter_image, card_image_of_injective _ mapc_inj,
    card_image_of_injective _ toL_inj]
  rw [filter_false_of_mem (fun e _ => last_not_mem_mapc e), filter_true_of_mem
    (fun a _ => Sym2.mem_mk_right _ _)]
  simp

/-- The glued graph is connected if `X` is and the apex has a neighbour. -/
theorem connected_glue {X : Finset (Sym2 (Fin n))} {N : Finset (Fin n)} (hX : (graphOf X).Connected)
    (hN : N.Nonempty) : (graphOf (glue X N)).Connected := by
  obtain ⟨a, ha⟩ := hN
  have hom : ∀ {u v : Fin n}, (graphOf X).Adj u v → (graphOf (glue X N)).Adj u.castSucc v.castSucc := by
    intro u v h
    rw [SimpleGraph.fromEdgeSet_adj] at h ⊢
    refine ⟨?_, fun e => h.2 (Fin.castSucc_inj.1 e)⟩
    have := (mapc_mem_glue (N := N)).2 h.1
    simpa [mapc_mk] using this
  have hreach : ∀ v : Fin n, (graphOf (glue X N)).Reachable (Fin.last n) v.castSucc := by
    intro v
    have h1 : (graphOf (glue X N)).Adj (Fin.last n) a.castSucc := by
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨by rw [Sym2.eq_swap]; exact toL_mem_glue.2 ha, (Fin.castSucc_ne_last a).symm⟩
    obtain ⟨p⟩ := hX.preconnected a v
    have : ∀ {x y : Fin n}, (graphOf X).Walk x y → (graphOf (glue X N)).Reachable x.castSucc y.castSucc := by
      intro x y p
      induction p with
      | nil => exact SimpleGraph.Reachable.refl _
      | cons h _ ih => exact (hom h).reachable.trans ih
    exact h1.reachable.trans (this p)
  have hall : ∀ x : Fin (n + 1), (graphOf (glue X N)).Reachable (Fin.last n) x := by
    intro x
    rcases Fin.eq_castSucc_or_eq_last x with ⟨x', rfl⟩ | rfl
    · exact hreach x'
    · exact SimpleGraph.Reachable.refl _
  exact ⟨fun x y => (hall x).symm.trans (hall y)⟩

/-- The part of a connected glued graph on `Fin n` is connected if the apex has exactly two
neighbours and every vertex of `Fin n` has degree two in the glued graph. -/
theorem connected_of_glue {X : Finset (Sym2 (Fin n))} {N : Finset (Fin n)} (hn : 2 ≤ n)
    (hY : (graphOf (glue X N)).Connected) (hN : N.card = 2)
    (hdeg : ∀ v, degX X v + (if v ∈ N then 1 else 0) = 2) (hd : ∀ e ∈ X, ¬e.IsDiag) :
    (graphOf X).Connected := by
  -- every vertex reaches a neighbour of the apex
  have step1 : ∀ v : Fin n, ∃ a ∈ N, (graphOf X).Reachable v a := by
    intro v
    obtain ⟨p⟩ := hY.preconnected v.castSucc (Fin.last n)
    generalize hz : Fin.last n = z at p
    generalize hx : v.castSucc = x at p
    induction p generalizing v with
    | nil => exact absurd (hx.trans hz.symm) (Fin.castSucc_ne_last v)
    | @cons x y z h p ih =>
      subst hx
      rw [SimpleGraph.fromEdgeSet_adj] at h
      rcases Fin.eq_castSucc_or_eq_last y with ⟨y', rfl⟩ | rfl
      · obtain ⟨a, ha, r⟩ := ih y' hz rfl
        refine ⟨a, ha, SimpleGraph.Reachable.trans ?_ r⟩
        apply SimpleGraph.Adj.reachable
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨?_, fun e => h.2 (by rw [e])⟩
        have : mapc s(v, y') ∈ glue X N := by simpa [mapc_mk] using h.1
        exact mapc_mem_glue.1 this
      · exact ⟨v, toL_mem_glue.1 h.1, SimpleGraph.Reachable.refl _⟩
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hN
  -- the two neighbours of the apex are joined: parity
  have hab' : (graphOf X).Reachable a b := by
    by_contra hnr
    set R := univ.filter fun v => (graphOf X).Reachable a v with hR
    have heven : Even (∑ v ∈ R, degX X v) := by
      rw [sum_degX]
      refine Finset.even_sum _ fun e he => ?_
      have hde := hd e he
      induction e using Sym2.ind with
      | _ x y =>
      have hxy : x ≠ y := fun h => hde (Sym2.mk_isDiag_iff.2 h)
      have hadj : (graphOf X).Adj x y := by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨he, hxy⟩
      rw [card_filter_mem_pair _ hxy]
      by_cases hx : (graphOf X).Reachable a x
      · have hy : (graphOf X).Reachable a y := hx.trans hadj.reachable
        have : R ∩ {x, y} = {x, y} := by
          ext w; simp only [mem_inter, hR, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
          constructor
          · exact fun h => h.2
          · rintro (rfl | rfl)
            · exact ⟨hx, Or.inl rfl⟩
            · exact ⟨hy, Or.inr rfl⟩
        rw [this, card_pair hxy]; exact ⟨1, rfl⟩
      · have hy : ¬(graphOf X).Reachable a y := fun hy => hx (hy.trans hadj.symm.reachable)
        have : R ∩ {x, y} = ∅ := by
          ext w; simp only [mem_inter, hR, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
            notMem_empty, iff_false, not_and]
          rintro h (rfl | rfl)
          · exact hx h
          · exact hy h
        rw [this, card_empty]; exact ⟨0, rfl⟩
    have hsum : ∑ v ∈ R, degX X v + 1 = 2 * R.card := by
      have h1 : ∑ v ∈ R, (degX X v + if v ∈ ({a, b} : Finset (Fin n)) then 1 else 0) = 2 * R.card := by
        rw [sum_congr rfl fun v _ => hdeg v, sum_const, smul_eq_mul, mul_comm]
      rw [sum_add_distrib, ← card_filter] at h1
      have h2 : R.filter (fun v => v ∈ ({a, b} : Finset (Fin n))) = {a} := by
        ext w
        simp only [hR, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        constructor
        · rintro ⟨hw, rfl | rfl⟩
          · rfl
          · exact absurd hw hnr
        · rintro rfl; exact ⟨SimpleGraph.Reachable.refl _, Or.inl rfl⟩
      rw [h2, card_singleton] at h1
      exact h1
    obtain ⟨k, hk⟩ := heven
    omega
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨fun u v => ?_⟩
  obtain ⟨c, hc, hu⟩ := step1 u
  obtain ⟨d, hd', hv⟩ := step1 v
  have hcd : (graphOf X).Reachable c d := by
    simp only [mem_insert, mem_singleton] at hc hd'
    rcases hc with rfl | rfl <;> rcases hd' with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact hab'
    · exact hab'.symm
    · exact SimpleGraph.Reachable.refl _
  exact hu.trans (hcd.trans hv.symm)

end Glue

/-! ## The bijection -/

section Bij

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- A Hamiltonian path plus the two edges from its ends to the apex. -/
def plusE (X : Finset (Sym2 (Fin n))) : Finset (Sym2 (Fin (n + 1))) := glue X (ends X)

theorem glue_sub_apex {X : Finset (Sym2 (Fin n))} {N : Finset (Fin n)} (hX : X ⊆ G.edgeFinset) :
    glue X N ⊆ (apex G).edgeFinset := by
  intro e he
  rw [SimpleGraph.mem_edgeFinset]
  simp only [glue, mem_union, mem_image] at he
  rcases he with ⟨e', he', rfl⟩ | ⟨a, -, rfl⟩
  · have := hX he'
    rw [SimpleGraph.mem_edgeFinset] at this
    induction e' using Sym2.ind with
    | _ x y =>
    simp only [mapc_mk, SimpleGraph.mem_edgeSet] at this ⊢
    exact apex_adj_cs.2 this
  · exact apex_adj_last a

theorem minusE_sub {Y : Finset (Sym2 (Fin (n + 1)))} (hY : Y ⊆ (apex G).edgeFinset) :
    minusE Y ⊆ G.edgeFinset := by
  intro e he
  simp only [minusE, mem_filter, mem_univ, true_and] at he
  have := hY he
  rw [SimpleGraph.mem_edgeFinset] at this ⊢
  induction e using Sym2.ind with
  | _ x y =>
  simp only [mapc_mk, SimpleGraph.mem_edgeSet] at this ⊢
  exact apex_adj_cs.1 this

theorem plusE_mem {X : Finset (Sym2 (Fin n))} (hn : 2 ≤ n) (hX : X ∈ hamPaths G) :
    plusE X ∈ hamCycles (apex G) := by
  obtain ⟨hsub, hP⟩ := mem_hamPaths.1 hX
  have hd := not_isDiag_of_sub hsub
  have he := card_ends hP hd hn
  refine mem_hamCycles_iff_sub.2 ⟨glue_sub_apex hsub, fun x => ?_, connected_glue hP.2.2 ?_⟩
  · rcases Fin.eq_castSucc_or_eq_last x with ⟨v, rfl⟩ | rfl
    · change degX (glue X (ends X)) v.castSucc = 2
      rw [degX_glue_cs]
      have h1 := one_le_degX hP.2.2 hn v
      have h2 := hP.2.1 v
      simp only [ends, mem_filter, mem_univ, true_and]
      split_ifs <;> omega
    · change degX (glue X (ends X)) (Fin.last n) = 2
      rw [degX_glue_last, he]
  · exact card_pos.1 (by omega)

theorem minusE_mem {Y : Finset (Sym2 (Fin (n + 1)))} (hn : 2 ≤ n) (hY : Y ∈ hamCycles (apex G)) :
    minusE Y ∈ hamPaths G ∧ plusE (minusE Y) = Y := by
  obtain ⟨hsub, hreg, hconn⟩ := mem_hamCycles_iff_sub.1 hY
  have hdY := not_isDiag_of_sub hsub
  have hg := glue_minusE_nbr hdY
  set X := minusE Y
  set N := nbr Y
  have hN : N.card = 2 := by
    have := hreg (Fin.last n)
    rw [← hg] at this
    exact (degX_glue_last X N).symm.trans this
  have hdeg : ∀ v, degX X v + (if v ∈ N then 1 else 0) = 2 := fun v => by
    have := hreg v.castSucc
    rw [← hg] at this
    exact (degX_glue_cs X N v).symm.trans this
  have hcardY : Y.card = n + 1 := by
    have := sum_degX_univ Y hdY
    have h2 : ∀ x, degX Y x = 2 := hreg
    rw [sum_congr rfl fun x _ => h2 x, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at this
    omega
  have hXsub := minusE_sub hsub
  have hdX := not_isDiag_of_sub hXsub
  rw [← hg] at hconn
  have hends : ends X = N := by
    ext v
    simp only [ends, mem_filter, mem_univ, true_and]
    have := hdeg v
    split_ifs at this with h <;> simp only [h, iff_true, iff_false] <;> omega
  refine ⟨mem_hamPaths.2 ⟨hXsub, ?_, fun v => ?_, connected_of_glue hn hconn hN hdeg hdX⟩, ?_⟩
  · have := card_glue X N
    rw [hg, hcardY, hN] at this
    omega
  · have := hdeg v; omega
  · rw [plusE, hends, hg]

/-- **Hamiltonian paths = Hamiltonian cycles of the apex graph**, for `n ≥ 2`. -/
theorem card_hamPaths_eq (hn : 2 ≤ n) : (hamPaths G).card = (hamCycles (apex G)).card := by
  refine Finset.card_nbij' plusE minusE (fun X hX => plusE_mem hn hX)
    (fun Y hY => (minusE_mem hn hY).1) (fun X _ => ?_) (fun Y hY => (minusE_mem hn hY).2)
  exact minusE_glue X (ends X)

end Bij

end EthFollowup.ExactHC
