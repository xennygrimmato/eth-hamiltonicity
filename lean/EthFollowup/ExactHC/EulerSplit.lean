/-
# Edge splitting: Eulerian circuits as Hamiltonian cycles (Kotzig)

For a simple graph `G` on `Fin n` with edges `e₀, …, e_{m-1}` (the list `edgeList G`, pairs
`(u, v)` with `u < v` in lexicographic order), `eulerSplit G A` is the simple graph on `Fin (3m)`
with, for every edge `eᵢ = {u, v}` (`u < v`), three copies `lo = 3i` (the copy of `eᵢ` at `u`),
`mid = 3i + 1`, `hi = 3i + 2` (the copy at `v`), the two internal edges `{lo, mid}`, `{mid, hi}`,
and, for every vertex `x` and two distinct edges `eᵢ, eⱼ` at `x` whose transition at `x` is
allowed by `A x y z` (`y`, `z` the other ends of `eᵢ`, `eⱼ`), the edge between the copies of
`eᵢ` and `eⱼ` at `x`. With every transition allowed (`eulerSplitAll`) this is the line graph of
the double subdivision of `G`.

**Eulerian circuits** are counted through Kotzig's description (A. Kotzig, 1968): an Eulerian
circuit (a closed trail through every edge, up to rotation and reversal) is the same as a
*transition system* (a pairing of the edges at every vertex) whose transition graph is connected.
Here a transition system is a set `T` of clique edges of `eulerSplit G A` with exactly one edge at
every `lo` and every `hi` copy (`transSys`), and its transition graph is `phiE T = T ∪ intE`
(every copy of every edge, the internal edges, and the transitions); `eulerCircuits G A` are the
transition systems with connected transition graph. This is the definition of the number of
Eulerian circuits used in this file; it is the standard bijection (cf. Balaji–Datta–Ganesan,
arXiv 1510.04035, for the line graph of the double subdivision).

## Results
* `hamCycles_eulerSplit : hamCycles (eulerSplit G A) = (eulerCircuits G A).image (phiE G)`,
  `phiE` injective on transition systems, hence `card_hamCycles_eulerSplit`;
* `edgeFinset_eulerSplit`, `card_edgeFinset_eulerSplit_le : |E(G')| ≤ 2(Δ + 1)·m`;
* `length_edgeList : m = |E(G)|`;
* `mem_cliqueE_arith`, `adj_eulerSplitAll_iff`: the arithmetic description of the edges, used by
  the machine that writes the adjacency matrix of `eulerSplitAll G`.
-/
import EthFollowup.HamiltonianParity

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC.ESplit

open Finset EthFollowup.Hamiltonian

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-! ### The edge list -/

/-- The edges `(u, v)`, `u < v`, of `G` in lexicographic order. -/
def edgeList : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => decide (u < v ∧ G.Adj u v)).map fun v => (u, v)

theorem mem_edgeList_iff {p : Fin n × Fin n} : p ∈ edgeList G ↔ p.1 < p.2 ∧ G.Adj p.1 p.2 := by
  obtain ⟨u, v⟩ := p
  simp [edgeList]

theorem nodup_edgeList : (edgeList G).Nodup := by
  rw [edgeList, List.nodup_flatMap]
  refine ⟨fun u _ => ((List.nodup_finRange n).filter _).map fun a b h => (Prod.mk.inj h).2, ?_⟩
  refine (List.nodup_finRange n).imp fun {u w} huw => ?_
  intro p hp hq
  simp only [List.mem_map] at hp hq
  obtain ⟨_, _, rfl⟩ := hp
  obtain ⟨_, _, he⟩ := hq
  exact huw (congrArg Prod.fst he).symm

theorem edgeFinset_eq_image :
    G.edgeFinset = (edgeList G).toFinset.image fun p => s(p.1, p.2) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, mem_image, List.mem_toFinset,
      mem_edgeList_iff]
    constructor
    · intro h
      rcases lt_trichotomy x y with hxy | rfl | hxy
      · exact ⟨(x, y), ⟨hxy, h⟩, rfl⟩
      · exact absurd h (G.irrefl)
      · exact ⟨(y, x), ⟨hxy, h.symm⟩, Sym2.eq_swap⟩
    · rintro ⟨p, ⟨-, hp⟩, he⟩
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hp
      · exact hp.symm

/-- **The number of entries of the edge list is the number of edges.** -/
theorem length_edgeList : (edgeList G).length = G.edgeFinset.card := by
  rw [edgeFinset_eq_image, card_image_of_injOn, List.toFinset_card_of_nodup (nodup_edgeList G)]
  rintro ⟨a, b⟩ hp ⟨c, d⟩ hq he
  rw [Finset.mem_coe, List.mem_toFinset, mem_edgeList_iff] at hp hq
  rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · exfalso
    simp only at h1 h2 hp hq
    subst h1 h2
    exact lt_asymm hp.1 hq.1

/-- The number of edges, as the length of the edge list. -/
abbrev M : ℕ := (edgeList G).length

theorem M_le : M G ≤ n * n := by
  have := (nodup_edgeList G).length_le_card
  simpa using this

/-! ### Edges and copies -/

/-- The low end of edge `i`. -/
def eLo (i : Fin (M G)) : Fin n := ((edgeList G).get i).1
/-- The high end of edge `i`. -/
def eHi (i : Fin (M G)) : Fin n := ((edgeList G).get i).2

theorem mem_get (i : Fin (M G)) : (edgeList G).get i ∈ edgeList G := List.mem_iff_get.2 ⟨i, rfl⟩

theorem eLo_lt (i : Fin (M G)) : eLo G i < eHi G i := ((mem_edgeList_iff G).1 (mem_get G i)).1

theorem eAdj (i : Fin (M G)) : G.Adj (eLo G i) (eHi G i) := ((mem_edgeList_iff G).1 (mem_get G i)).2

theorem e_inj {i j : Fin (M G)} (h1 : eLo G i = eLo G j) (h2 : eHi G i = eHi G j) : i = j :=
  List.nodup_iff_injective_get.1 (nodup_edgeList G) (Prod.ext h1 h2)

/-- The copy of edge `i` at its low end. -/
def cLo (i : Fin (M G)) : Fin (3 * M G) := ⟨3 * i.val, by have := i.isLt; omega⟩
/-- The middle copy of edge `i`. -/
def cMid (i : Fin (M G)) : Fin (3 * M G) := ⟨3 * i.val + 1, by have := i.isLt; omega⟩
/-- The copy of edge `i` at its high end. -/
def cHi (i : Fin (M G)) : Fin (3 * M G) := ⟨3 * i.val + 2, by have := i.isLt; omega⟩

@[simp] theorem cLo_val (i : Fin (M G)) : (cLo G i).val = 3 * i.val := rfl
@[simp] theorem cMid_val (i : Fin (M G)) : (cMid G i).val = 3 * i.val + 1 := rfl
@[simp] theorem cHi_val (i : Fin (M G)) : (cHi G i).val = 3 * i.val + 2 := rfl

/-- The copy of edge `i` at the vertex `x` (meaningful when `x` is an end of `i`). -/
def copyAt (i : Fin (M G)) (x : Fin n) : Fin (3 * M G) := if eLo G i = x then cLo G i else cHi G i

/-- The other end of edge `i` (when `x` is an end of `i`). -/
def other (i : Fin (M G)) (x : Fin n) : Fin n := if eLo G i = x then eHi G i else eLo G i

theorem copyAt_val (i : Fin (M G)) (x : Fin n) :
    (copyAt G i x).val = 3 * i.val ∨ (copyAt G i x).val = 3 * i.val + 2 := by
  unfold copyAt; split_ifs <;> simp

/-- The edge of a copy. -/
def idx (x : Fin (3 * M G)) : Fin (M G) := ⟨x.val / 3, by have := x.isLt; omega⟩

@[simp] theorem idx_val (x : Fin (3 * M G)) : (idx G x).val = x.val / 3 := rfl

/-- The vertex at which the copy `x` sits (`x` not a middle copy). -/
def ptF (x : Fin (3 * M G)) : Fin n := if x.val % 3 = 0 then eLo G (idx G x) else eHi G (idx G x)

/-- The far end of the edge of the copy `x` (`x` not a middle copy). -/
def farF (x : Fin (3 * M G)) : Fin n := if x.val % 3 = 0 then eHi G (idx G x) else eLo G (idx G x)

/-- **The internal edges** `{lo, mid}`, `{mid, hi}`. -/
def intE : Finset (Sym2 (Fin (3 * M G))) :=
  univ.image (fun i => s(cLo G i, cMid G i)) ∪ univ.image (fun i => s(cMid G i, cHi G i))

/-- **The transition edges**: for distinct edges `i`, `j` at `x` whose transition at `x` is
allowed (`A x (other end of i) (other end of j)`), the edge between their copies at `x`. -/
def cliqueE (A : Fin n → Fin n → Fin n → Bool) : Finset (Sym2 (Fin (3 * M G))) :=
  (univ.filter fun t : Fin (M G) × Fin (M G) × Fin n => t.1 ≠ t.2.1 ∧
      (eLo G t.1 = t.2.2 ∨ eHi G t.1 = t.2.2) ∧ (eLo G t.2.1 = t.2.2 ∨ eHi G t.2.1 = t.2.2) ∧
      A t.2.2 (other G t.1 t.2.2) (other G t.2.1 t.2.2) = true).image
    fun t => s(copyAt G t.1 t.2.2, copyAt G t.2.1 t.2.2)

/-- **The split graph** `G'` on `Fin (3m)`. -/
abbrev eulerSplit (A : Fin n → Fin n → Fin n → Bool) : SimpleGraph (Fin (3 * M G)) :=
  graphOf (intE G ∪ cliqueE G A)

/-- The split graph with every transition allowed (the line graph of the double subdivision). -/
abbrev eulerSplitAll : SimpleGraph (Fin (3 * M G)) := eulerSplit G fun _ _ _ => true

/-- **Transition systems** (allowed by `A`): sets of transition edges with exactly one edge at every
`lo` and every `hi` copy. -/
def transSys (A : Fin n → Fin n → Fin n → Bool) : Finset (Finset (Sym2 (Fin (3 * M G)))) :=
  (cliqueE G A).powerset.filter fun T => ∀ i : Fin (M G),
    (T.filter fun e => cLo G i ∈ e).card = 1 ∧ (T.filter fun e => cHi G i ∈ e).card = 1

/-- The transition graph of `T` (with the internal edges). -/
def phiE (T : Finset (Sym2 (Fin (3 * M G)))) : Finset (Sym2 (Fin (3 * M G))) := T ∪ intE G

/-- **Eulerian circuits** (allowed by `A`), in Kotzig's description: transition systems whose
transition graph is connected. -/
def eulerCircuits (A : Fin n → Fin n → Fin n → Bool) : Finset (Finset (Sym2 (Fin (3 * M G)))) :=
  (transSys G A).filter fun T => (graphOf (phiE G T)).Connected

/-- **The Eulerian circuits of `G`** (Kotzig's description, every transition allowed). -/
abbrev eulerCircuitsAll : Finset (Finset (Sym2 (Fin (3 * M G)))) :=
  eulerCircuits G fun _ _ _ => true

/-- The edge list as pairs of numbers. -/
def edgesN : List (ℕ × ℕ) := (edgeList G).map fun p => (p.1.val, p.2.val)

/-! ### Which copies an edge contains -/

theorem mem_mk {k : ℕ} {a b c : Fin k} : a ∈ s(b, c) ↔ a.val = b.val ∨ a.val = c.val := by
  rw [Sym2.mem_iff, Fin.ext_iff, Fin.ext_iff]

theorem mid_not_mem_cliqueE {A : Fin n → Fin n → Fin n → Bool} {e : Sym2 (Fin (3 * M G))}
    (he : e ∈ cliqueE G A) (i : Fin (M G)) : cMid G i ∉ e := by
  obtain ⟨t, -, rfl⟩ := mem_image.1 he
  rw [mem_mk, cMid_val]
  rcases copyAt_val G t.1 t.2.2 with h1 | h1 <;> rcases copyAt_val G t.2.1 t.2.2 with h2 | h2 <;>
    omega

theorem mid_mem_of_mem_intE {e : Sym2 (Fin (3 * M G))} (he : e ∈ intE G) :
    ∃ j, cMid G j ∈ e := by
  simp only [intE, mem_union, mem_image, mem_univ, true_and] at he
  rcases he with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact ⟨j, Sym2.mem_mk_right _ _⟩
  · exact ⟨j, Sym2.mem_mk_left _ _⟩

theorem disjoint_intE_cliqueE (A : Fin n → Fin n → Fin n → Bool) :
    Disjoint (intE G) (cliqueE G A) := by
  rw [disjoint_left]
  intro e hi hc
  obtain ⟨j, hj⟩ := mid_mem_of_mem_intE G hi
  exact mid_not_mem_cliqueE G hc j hj

theorem intE_filter_lo (i : Fin (M G)) :
    (intE G).filter (fun e => cLo G i ∈ e) = {s(cLo G i, cMid G i)} := by
  ext e
  simp only [intE, mem_filter, mem_union, mem_image, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨⟨j, rfl⟩ | ⟨j, rfl⟩, h⟩ <;> rw [mem_mk] at h <;> simp only [cLo_val, cMid_val, cHi_val] at h
    · obtain rfl : j = i := Fin.ext (by omega)
      rfl
    · omega
  · rintro rfl
    exact ⟨Or.inl ⟨i, rfl⟩, Sym2.mem_mk_left _ _⟩

theorem intE_filter_hi (i : Fin (M G)) :
    (intE G).filter (fun e => cHi G i ∈ e) = {s(cMid G i, cHi G i)} := by
  ext e
  simp only [intE, mem_filter, mem_union, mem_image, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨⟨j, rfl⟩ | ⟨j, rfl⟩, h⟩ <;> rw [mem_mk] at h <;> simp only [cLo_val, cMid_val, cHi_val] at h
    · omega
    · obtain rfl : j = i := Fin.ext (by omega)
      rfl
  · rintro rfl
    exact ⟨Or.inr ⟨i, rfl⟩, Sym2.mem_mk_right _ _⟩

theorem intE_filter_mid (i : Fin (M G)) :
    (intE G).filter (fun e => cMid G i ∈ e) = {s(cLo G i, cMid G i), s(cMid G i, cHi G i)} := by
  ext e
  simp only [intE, mem_filter, mem_union, mem_image, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨j, rfl⟩ | ⟨j, rfl⟩, h⟩ <;> rw [mem_mk] at h <;> simp only [cLo_val, cMid_val, cHi_val] at h
    · obtain rfl : j = i := Fin.ext (by omega)
      exact Or.inl rfl
    · obtain rfl : j = i := Fin.ext (by omega)
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inl ⟨i, rfl⟩, Sym2.mem_mk_right _ _⟩
    · exact ⟨Or.inr ⟨i, rfl⟩, Sym2.mem_mk_left _ _⟩

theorem lm_ne_mh (i : Fin (M G)) : s(cLo G i, cMid G i) ≠ s(cMid G i, cHi G i) := by
  intro h
  have := Sym2.mem_mk_left (cLo G i) (cMid G i)
  rw [h, mem_mk] at this
  simp only [cLo_val, cMid_val, cHi_val] at this
  omega

theorem cases3 (x : Fin (3 * M G)) :
    x = cLo G (idx G x) ∨ x = cMid G (idx G x) ∨ x = cHi G (idx G x) := by
  simp only [Fin.ext_iff, cLo_val, cMid_val, cHi_val, idx_val]; omega

theorem card_union_disj {α : Type*} [DecidableEq α] {s t : Finset α} (h : Disjoint s t) :
    (s ∪ t).card = s.card + t.card := by
  have := card_union_add_card_inter s t
  rw [disjoint_iff_inter_eq_empty.1 h, card_empty, add_zero] at this
  exact this

/-! ### Degrees in the transition graph -/

section Degrees

variable {A : Fin n → Fin n → Fin n → Bool} {T : Finset (Sym2 (Fin (3 * M G)))}

theorem card_filter_phiE (hT : T ⊆ cliqueE G A) (x : Fin (3 * M G)) :
    ((phiE G T).filter fun e => x ∈ e).card =
      (T.filter fun e => x ∈ e).card + ((intE G).filter fun e => x ∈ e).card := by
  rw [phiE, filter_union]
  refine card_union_disj ?_
  exact disjoint_filter_filter (disjoint_of_subset_left hT (disjoint_intE_cliqueE G A).symm)

theorem filter_mid_eq (hT : T ⊆ cliqueE G A) (i : Fin (M G)) :
    T.filter (fun e => cMid G i ∈ e) = ∅ :=
  filter_eq_empty_iff.2 fun _ he => mid_not_mem_cliqueE G (hT he) i

/-- `phiE T` is 2-regular iff `T` has exactly one edge at every `lo` and every `hi` copy. -/
theorem twoRegular_phiE_iff (hT : T ⊆ cliqueE G A) :
    TwoRegular (phiE G T) ↔ ∀ i : Fin (M G),
      (T.filter fun e => cLo G i ∈ e).card = 1 ∧ (T.filter fun e => cHi G i ∈ e).card = 1 := by
  constructor
  · intro h i
    have h1 := h (cLo G i)
    have h2 := h (cHi G i)
    rw [card_filter_phiE G hT, intE_filter_lo, card_singleton] at h1
    rw [card_filter_phiE G hT, intE_filter_hi, card_singleton] at h2
    exact ⟨by omega, by omega⟩
  · intro h x
    rcases cases3 G x with hx | hx | hx <;> rw [hx, card_filter_phiE G hT]
    · rw [intE_filter_lo, card_singleton, (h _).1]
    · rw [intE_filter_mid, filter_mid_eq G hT, card_empty, card_insert_of_notMem (by
        rw [mem_singleton]; exact lm_ne_mh G _), card_singleton]
    · rw [intE_filter_hi, card_singleton, (h _).2]

end Degrees

/-! ### The bijection -/

section Bij

variable (A : Fin n → Fin n → Fin n → Bool)

theorem graphOf_adj' {k : ℕ} {Y : Finset (Sym2 (Fin k))} {u w : Fin k} :
    (graphOf Y).Adj u w ↔ s(u, w) ∈ Y ∧ u ≠ w := by
  simp [graphOf, SimpleGraph.fromEdgeSet_adj]

theorem copyAt_ne {i j : Fin (M G)} (h : i ≠ j) (x y : Fin n) : copyAt G i x ≠ copyAt G j y := by
  intro he
  have := congrArg Fin.val he
  have hij : i.val ≠ j.val := fun h' => h (Fin.ext h')
  rcases copyAt_val G i x with h1 | h1 <;> rcases copyAt_val G j y with h2 | h2 <;> omega

theorem not_mem_diag (x : Fin (3 * M G)) : s(x, x) ∉ intE G ∪ cliqueE G A := by
  rw [mem_union]
  rintro (h | h)
  · simp only [intE, mem_union, mem_image, mem_univ, true_and] at h
    rcases h with ⟨j, hj⟩ | ⟨j, hj⟩ <;> rcases Sym2.eq_iff.1 hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [← h2] at h1 <;> simp [Fin.ext_iff] at h1
  · obtain ⟨t, ht, he⟩ := mem_image.1 h
    simp only [mem_filter, mem_univ, true_and] at ht
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← h2] at h1
    all_goals exact copyAt_ne G ht.1 _ _ h1

theorem edgeFinset_eulerSplit [Fintype (eulerSplit G A).edgeSet] :
    (eulerSplit G A).edgeFinset = intE G ∪ cliqueE G A := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, graphOf_adj']
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rintro rfl
    exact not_mem_diag G A x h

theorem filter_EA_mid (j : Fin (M G)) :
    (intE G ∪ cliqueE G A).filter (fun e => cMid G j ∈ e) =
      {s(cLo G j, cMid G j), s(cMid G j, cHi G j)} := by
  rw [filter_union, filter_eq_empty_iff.2 fun e he => mid_not_mem_cliqueE G he j, union_empty,
    intE_filter_mid]

theorem filter_phiE {T : Finset (Sym2 (Fin (3 * M G)))} (hT : T ⊆ cliqueE G A) :
    (phiE G T).filter (· ∈ cliqueE G A) = T := by
  ext e
  simp only [phiE, mem_filter, mem_union]
  constructor
  · rintro ⟨h | h, hc⟩
    · exact h
    · exact absurd hc (disjoint_left.1 (disjoint_intE_cliqueE G A) h)
  · intro h
    exact ⟨Or.inl h, hT h⟩

/-- **The bijection**: the Hamiltonian cycles of `eulerSplit G A` are the transition graphs of the
Eulerian circuits of `G` allowed by `A`. -/
theorem hamCycles_eulerSplit : hamCycles (eulerSplit G A) = (eulerCircuits G A).image (phiE G) := by
  ext H
  simp only [hamCycles, twoFactors, eulerCircuits, transSys, mem_filter, mem_powerset, mem_image]
  rw [edgeFinset_eulerSplit]
  constructor
  · rintro ⟨⟨hHE, h2⟩, hc⟩
    set T := H.filter fun e => e ∈ cliqueE G A with hTd
    have hTs : T ⊆ cliqueE G A := fun e he => (mem_filter.1 he).2
    have hint : ∀ j, s(cLo G j, cMid G j) ∈ H ∧ s(cMid G j, cHi G j) ∈ H := by
      intro j
      have hsub : H.filter (fun e => cMid G j ∈ e) ⊆ (intE G ∪ cliqueE G A).filter (fun e => cMid G j ∈ e) :=
        filter_subset_filter _ hHE
      have hc2 : ((intE G ∪ cliqueE G A).filter (fun e => cMid G j ∈ e)).card = 2 := by
        rw [filter_EA_mid, card_insert_of_notMem (by rw [mem_singleton]; exact lm_ne_mh G _),
          card_singleton]
      have heq := eq_of_subset_of_card_le hsub (by rw [hc2, h2])
      have hi : s(cLo G j, cMid G j) ∈ (intE G ∪ cliqueE G A).filter (fun e => cMid G j ∈ e) := by
        rw [filter_EA_mid]; simp
      have ho : s(cMid G j, cHi G j) ∈ (intE G ∪ cliqueE G A).filter (fun e => cMid G j ∈ e) := by
        rw [filter_EA_mid]; simp
      rw [← heq] at hi ho
      exact ⟨(mem_filter.1 hi).1, (mem_filter.1 ho).1⟩
    have hTH : phiE G T = H := by
      ext e
      simp only [phiE, mem_union, hTd, mem_filter]
      constructor
      · rintro (⟨h, -⟩ | h)
        · exact h
        · simp only [intE, mem_union, mem_image, mem_univ, true_and] at h
          rcases h with ⟨j, rfl⟩ | ⟨j, rfl⟩
          · exact (hint j).1
          · exact (hint j).2
      · intro he
        rcases mem_union.1 (hHE he) with h | h
        · exact Or.inr h
        · exact Or.inl ⟨he, h⟩
    refine ⟨T, ⟨⟨hTs, ?_⟩, ?_⟩, hTH⟩
    · rw [← twoRegular_phiE_iff G hTs, hTH]; exact h2
    · rw [hTH]; exact hc
  · rintro ⟨T, ⟨⟨hTs, hdeg⟩, hc⟩, rfl⟩
    exact ⟨⟨union_subset (hTs.trans subset_union_right) subset_union_left,
      (twoRegular_phiE_iff G hTs).2 hdeg⟩, hc⟩

theorem phiE_injOn : Set.InjOn (phiE G) (eulerCircuits G A : Set (Finset (Sym2 (Fin (3 * M G))))) := by
  intro T₁ h₁ T₂ h₂ h
  have s₁ : T₁ ⊆ cliqueE G A := mem_powerset.1 (mem_filter.1 (mem_filter.1 (mem_coe.1 h₁)).1).1
  have s₂ : T₂ ⊆ cliqueE G A := mem_powerset.1 (mem_filter.1 (mem_filter.1 (mem_coe.1 h₂)).1).1
  rw [← filter_phiE G A s₁, h, filter_phiE G A s₂]

/-- **`#HC(eulerSplit G A) = #(Eulerian circuits of G allowed by A)`.** -/
theorem card_hamCycles_eulerSplit : (hamCycles (eulerSplit G A)).card = (eulerCircuits G A).card := by
  rw [hamCycles_eulerSplit, card_image_of_injOn (phiE_injOn G A)]

/-- **`#HC(G') = #Eulerian circuits of G`.** -/
theorem card_hamCycles_eulerSplitAll : (hamCycles (eulerSplitAll G)).card = (eulerCircuitsAll G).card :=
  card_hamCycles_eulerSplit G _

end Bij

/-! ### The number of edges of the split graph -/

theorem card_intE_le : (intE G).card ≤ 2 * M G := by
  refine (card_union_le _ _).trans ?_
  have h1 := card_image_le (s := (univ : Finset (Fin (M G)))) (f := fun i => s(cLo G i, cMid G i))
  have h2 := card_image_le (s := (univ : Finset (Fin (M G)))) (f := fun i => s(cMid G i, cHi G i))
  simp only [card_univ, Fintype.card_fin] at h1 h2
  omega

/-- At most `deg x` edges contain `x`. -/
theorem card_inc_le (x : Fin n) :
    (univ.filter fun j : Fin (M G) => eLo G j = x ∨ eHi G j = x).card ≤ G.degree x := by
  rw [← G.card_neighborFinset_eq_degree]
  refine card_le_card_of_injOn (other G · x) ?_ ?_
  · intro j hj
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hj
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
    unfold other
    by_cases h : eLo G j = x
    · rw [if_pos h, ← h]; exact eAdj G j
    · rw [if_neg h]
      rcases hj with hj | hj
      · exact absurd hj h
      · rw [← hj]; exact (eAdj G j).symm
  · intro j hj k hk hjk
    simp only [Finset.coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hj hk
    have lj := eLo_lt G j
    have lk := eLo_lt G k
    have key : eLo G j = eLo G k ∧ eHi G j = eHi G k := by
      simp only [other] at hjk
      split_ifs at hjk with h1 h2 h2
      all_goals rcases hj with hj | hj <;> rcases hk with hk | hk
      all_goals simp only [Fin.ext_iff, Fin.lt_def] at *
      all_goals omega
    exact e_inj G key.1 key.2

theorem card_cliqueE_le (A : Fin n → Fin n → Fin n → Bool) :
    (cliqueE G A).card ≤ 2 * G.maxDegree * M G := by
  set S := univ.filter fun t : Fin (M G) × Fin (M G) × Fin n => t.1 ≠ t.2.1 ∧
      (eLo G t.1 = t.2.2 ∨ eHi G t.1 = t.2.2) ∧ (eLo G t.2.1 = t.2.2 ∨ eHi G t.2.1 = t.2.2) ∧
      A t.2.2 (other G t.1 t.2.2) (other G t.2.1 t.2.2) = true with hS
  have hsub : S ⊆ univ.biUnion fun i : Fin (M G) =>
      ((univ.filter fun j => eLo G j = eLo G i ∨ eHi G j = eLo G i).image fun j => (i, j, eLo G i)) ∪
      ((univ.filter fun j => eLo G j = eHi G i ∨ eHi G j = eHi G i).image fun j => (i, j, eHi G i)) := by
    rintro ⟨i, j, x⟩ ht
    simp only [hS, mem_filter, mem_univ, true_and] at ht
    obtain ⟨-, hi, hj, -⟩ := ht
    simp only [mem_biUnion, mem_univ, true_and, mem_union, mem_image, mem_filter]
    refine ⟨i, ?_⟩
    rcases hi with hi | hi
    · exact Or.inl ⟨j, by rw [hi]; exact hj, by rw [hi]⟩
    · exact Or.inr ⟨j, by rw [hi]; exact hj, by rw [hi]⟩
  calc (cliqueE G A).card ≤ S.card := card_image_le
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ i : Fin (M G), (((univ.filter fun j => eLo G j = eLo G i ∨ eHi G j = eLo G i).image
          fun j => (i, j, eLo G i)) ∪
        ((univ.filter fun j => eLo G j = eHi G i ∨ eHi G j = eHi G i).image
          fun j => (i, j, eHi G i))).card := card_biUnion_le
    _ ≤ ∑ _i : Fin (M G), 2 * G.maxDegree := by
        refine sum_le_sum fun i _ => (card_union_le _ _).trans ?_
        have h1 : ((univ.filter fun j => eLo G j = eLo G i ∨ eHi G j = eLo G i).image
            fun j => (i, j, eLo G i)).card ≤ G.maxDegree :=
          card_image_le.trans ((card_inc_le G _).trans (G.degree_le_maxDegree _))
        have h2 : ((univ.filter fun j => eLo G j = eHi G i ∨ eHi G j = eHi G i).image
            fun j => (i, j, eHi G i)).card ≤ G.maxDegree :=
          card_image_le.trans ((card_inc_le G _).trans (G.degree_le_maxDegree _))
        omega
    _ = 2 * G.maxDegree * M G := by
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

/-- **`|E(G')| ≤ 2(Δ + 1)·m`.** -/
theorem card_edgeFinset_eulerSplit_le (A : Fin n → Fin n → Fin n → Bool)
    [Fintype (eulerSplit G A).edgeSet] :
    (eulerSplit G A).edgeFinset.card ≤ 2 * (G.maxDegree + 1) * M G := by
  rw [edgeFinset_eulerSplit]
  have h1 := card_intE_le G
  have h2 := card_cliqueE_le G A
  have := card_union_le (intE G) (cliqueE G A)
  nlinarith

/-! ### The edges in arithmetic form -/

theorem idx_cLo (i : Fin (M G)) : idx G (cLo G i) = i := Fin.ext (by simp only [idx_val, cLo_val]; omega)
theorem idx_cHi (i : Fin (M G)) : idx G (cHi G i) = i := Fin.ext (by simp only [idx_val, cHi_val]; omega)

theorem idx_copyAt (i : Fin (M G)) (x : Fin n) : idx G (copyAt G i x) = i := by
  unfold copyAt; split_ifs
  · exact idx_cLo G i
  · exact idx_cHi G i

theorem copyAt_mod (i : Fin (M G)) (x : Fin n) : (copyAt G i x).val % 3 ≠ 1 := by
  rcases copyAt_val G i x with h | h <;> rw [h] <;> omega

theorem ptF_copyAt {i : Fin (M G)} {x : Fin n} (hx : eLo G i = x ∨ eHi G i = x) :
    ptF G (copyAt G i x) = x := by
  unfold ptF copyAt
  by_cases h : eLo G i = x
  · rw [if_pos h, if_pos (by simp), idx_cLo, h]
  · rw [if_neg h, if_neg (by simp), idx_cHi]
    exact hx.resolve_left h

theorem farF_copyAt {i : Fin (M G)} {x : Fin n} (_hx : eLo G i = x ∨ eHi G i = x) :
    farF G (copyAt G i x) = other G i x := by
  unfold farF copyAt other
  by_cases h : eLo G i = x
  · rw [if_pos h, if_pos h, if_pos (by simp), idx_cLo]
  · rw [if_neg h, if_neg h, if_neg (by simp), idx_cHi]

theorem on_ptF (x : Fin (3 * M G)) : eLo G (idx G x) = ptF G x ∨ eHi G (idx G x) = ptF G x := by
  unfold ptF; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem copyAt_ptF {x : Fin (3 * M G)} (h : x.val % 3 ≠ 1) : copyAt G (idx G x) (ptF G x) = x := by
  unfold copyAt ptF
  by_cases h0 : x.val % 3 = 0
  · rw [if_pos h0, if_pos rfl]
    exact Fin.ext (by simp only [cLo_val, idx_val]; omega)
  · rw [if_neg h0, if_neg (ne_of_lt (eLo_lt G _))]
    exact Fin.ext (by simp only [cHi_val, idx_val]; omega)

theorem other_ptF (x : Fin (3 * M G)) : other G (idx G x) (ptF G x) = farF G x := by
  unfold other ptF farF
  by_cases h0 : x.val % 3 = 0
  · rw [if_pos h0, if_pos h0, if_pos rfl]
  · rw [if_neg h0, if_neg h0, if_neg (ne_of_lt (eLo_lt G _))]

theorem mem_intE_arith (x y : Fin (3 * M G)) :
    s(x, y) ∈ intE G ↔ x.val / 3 = y.val / 3 ∧ (x.val % 3 + y.val % 3 = 1 ∨ x.val % 3 + y.val % 3 = 3) := by
  simp only [intE, mem_union, mem_image, mem_univ, true_and]
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩) <;> rcases Sym2.eq_iff.1 hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      subst h1 h2 <;> simp only [cLo_val, cMid_val, cHi_val] <;> omega
  · rintro ⟨hq, hr⟩
    have hx3 : x.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hy3 : y.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : (x.val % 3 = 0 ∧ y.val % 3 = 1) ∨ (x.val % 3 = 1 ∧ y.val % 3 = 0) ∨
        (x.val % 3 = 1 ∧ y.val % 3 = 2) ∨ (x.val % 3 = 2 ∧ y.val % 3 = 1)) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨idx G x, Sym2.eq_iff.2 (Or.inl ⟨Fin.ext (by simp only [cLo_val, idx_val]; omega),
        Fin.ext (by simp only [cMid_val, idx_val]; omega)⟩)⟩
    · exact Or.inl ⟨idx G x, Sym2.eq_iff.2 (Or.inr ⟨Fin.ext (by simp only [cLo_val, idx_val]; omega),
        Fin.ext (by simp only [cMid_val, idx_val]; omega)⟩)⟩
    · exact Or.inr ⟨idx G x, Sym2.eq_iff.2 (Or.inl ⟨Fin.ext (by simp only [cMid_val, idx_val]; omega),
        Fin.ext (by simp only [cHi_val, idx_val]; omega)⟩)⟩
    · exact Or.inr ⟨idx G x, Sym2.eq_iff.2 (Or.inr ⟨Fin.ext (by simp only [cMid_val, idx_val]; omega),
        Fin.ext (by simp only [cHi_val, idx_val]; omega)⟩)⟩

/-- **The transition edges in arithmetic form**: `{x, y}` is a transition edge iff `x`, `y` are
end copies of distinct edges at the same vertex `z`, and the transition is allowed (in one of the
two orders). -/
theorem mem_cliqueE_arith (A : Fin n → Fin n → Fin n → Bool) (x y : Fin (3 * M G)) :
    s(x, y) ∈ cliqueE G A ↔ x.val / 3 ≠ y.val / 3 ∧ x.val % 3 ≠ 1 ∧ y.val % 3 ≠ 1 ∧
      ptF G x = ptF G y ∧
      (A (ptF G x) (farF G x) (farF G y) = true ∨ A (ptF G x) (farF G y) (farF G x) = true) := by
  constructor
  · intro h
    obtain ⟨⟨i, j, z⟩, ht, he⟩ := mem_image.1 h
    simp only [mem_filter, mem_univ, true_and] at ht he
    obtain ⟨hij, hi, hj, hA⟩ := ht
    have hv : i.val ≠ j.val := fun h' => hij (Fin.ext h')
    have ci := idx_copyAt G i z
    have cj := idx_copyAt G j z
    have vi : (copyAt G i z).val / 3 = i.val := by rw [← idx_val, ci]
    have vj : (copyAt G j z).val / 3 = j.val := by rw [← idx_val, cj]
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · refine ⟨by omega, copyAt_mod G _ _, copyAt_mod G _ _, by rw [ptF_copyAt G hi, ptF_copyAt G hj], ?_⟩
      left
      rw [ptF_copyAt G hi, farF_copyAt G hi, farF_copyAt G hj]
      exact hA
    · refine ⟨by omega, copyAt_mod G _ _, copyAt_mod G _ _, by rw [ptF_copyAt G hi, ptF_copyAt G hj], ?_⟩
      right
      rw [ptF_copyAt G hj, farF_copyAt G hi, farF_copyAt G hj]
      exact hA
  · rintro ⟨hq, h1, h2, hp, hA⟩
    have hne : idx G x ≠ idx G y := fun h => hq (by rw [← idx_val, h, idx_val])
    have ox := on_ptF G x
    have oy := on_ptF G y
    rw [← hp] at oy
    have ex := copyAt_ptF G h1
    have ey := copyAt_ptF G h2
    rw [← hp] at ey
    rcases hA with hA | hA
    · refine mem_image.2 ⟨(idx G x, idx G y, ptF G x), ?_, by simp only [ex, ey]⟩
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨hne, ox, oy, ?_⟩
      rw [other_ptF, ← farF_copyAt G oy, ey]
      exact hA
    · refine mem_image.2 ⟨(idx G y, idx G x, ptF G x), ?_, by simp only [ex, ey]; exact Sym2.eq_swap⟩
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨hne.symm, oy, ox, ?_⟩
      rw [other_ptF, ← farF_copyAt G oy, ey]
      exact hA

theorem getD_edgesN (i : Fin (M G)) :
    (edgesN G).getD i.val (0, 0) = ((eLo G i).val, (eHi G i).val) := by
  have hi : i.val < (edgesN G).length := by simp [edgesN]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp [edgesN, eLo, eHi]

/-- The vertex of a copy, in arithmetic form (from the edge list as numbers). -/
def ptN (E : List (ℕ × ℕ)) (x : ℕ) : ℕ :=
  if x % 3 = 0 then (E.getD (x / 3) (0, 0)).1 else (E.getD (x / 3) (0, 0)).2

/-- The far end of the edge of a copy, in arithmetic form. -/
def farN (E : List (ℕ × ℕ)) (x : ℕ) : ℕ :=
  if x % 3 = 0 then (E.getD (x / 3) (0, 0)).2 else (E.getD (x / 3) (0, 0)).1

theorem ptN_edgesN (x : Fin (3 * M G)) : ptN (edgesN G) x.val = (ptF G x).val := by
  have h := getD_edgesN G (idx G x)
  rw [idx_val] at h
  unfold ptN ptF
  split_ifs <;> rw [h]

theorem farN_edgesN (x : Fin (3 * M G)) : farN (edgesN G) x.val = (farF G x).val := by
  have h := getD_edgesN G (idx G x)
  rw [idx_val] at h
  unfold farN farF
  split_ifs <;> rw [h]

/-- The adjacency of the split graph (every transition allowed) in arithmetic form. -/
def eArith (E : List (ℕ × ℕ)) (x y : ℕ) : Prop :=
  (x / 3 = y / 3 ∧ (x % 3 + y % 3 = 1 ∨ x % 3 + y % 3 = 3)) ∨
    (x / 3 ≠ y / 3 ∧ x % 3 ≠ 1 ∧ y % 3 ≠ 1 ∧ ptN E x = ptN E y)

/-- **The adjacency of `eulerSplitAll G` in arithmetic form** (what the preprocessing machine
computes from the edge list). -/
theorem adj_eulerSplitAll_iff (x y : Fin (3 * M G)) :
    (eulerSplitAll G).Adj x y ↔ eArith (edgesN G) x.val y.val := by
  rw [graphOf_adj', mem_union, mem_intE_arith, mem_cliqueE_arith, eArith, ptN_edgesN, ptN_edgesN,
    Fin.val_inj]
  simp only [or_self, and_true]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rintro rfl
    rcases h with ⟨-, h⟩ | ⟨h, -⟩
    · omega
    · exact h rfl

end EthFollowup.ExactHC.ESplit
