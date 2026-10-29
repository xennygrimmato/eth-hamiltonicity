/-
# Vertex splitting: directed Hamiltonian cycles as undirected Hamiltonian cycles

For a digraph `A : Finset (Fin n × Fin n)` (loops allowed), `split A` is the simple graph on
`Fin (3 * n)` with, for every vertex `v`, the three copies `v_in = 3v`, `v_mid = 3v + 1`,
`v_out = 3v + 2`, the two internal edges `{v_in, v_mid}`, `{v_mid, v_out}`, and for every arc
`(u, v) ∈ A` the edge `{u_out, v_in}` (a loop `(v, v)` gives the edge `{v_out, v_in}`, which closes a
triangle and is used by a Hamiltonian cycle only for `n = 1`, exactly as the loop is used by a
directed Hamiltonian cycle only for `n = 1`). Its edge set is `phi A`, where for an arc set `X`

  `phi X = {u_out v_in : (u, v) ∈ X} ∪ {internal edges}`.

## Results (no restriction on `n`)
* `twoRegular_phi_iff`: `phi X` is 2-regular iff `X` is a cycle cover (`DirectedHamiltonian.CycleCover`);
* `connected_phi_iff`: `(Fin (3n), phi X)` is connected iff the underlying graph of `X` is;
* `hamCycles_split : hamCycles (split A) = (dirHamCycles A).image phi`, with `phi` injective, hence
  `card_hamCycles_split : #HC(split A) = #DHC(A)`;
* `edgeFinset_split : (split A).edgeFinset = phi A`, `card_edgeFinset_split_le : |E| ≤ |A| + 2n`;
* weights: `splitWt w` puts the arc weight `w (u, v)` on `{u_out, v_in}` and `0` on the internal
  edges; `wt_phi : wt (splitWt w) (phi X) = arcWt w X`, `splitWt_le`, and
  `tourCount_split : tourCount (split A) (splitWt w) j = dtourCount A w j`,
  `sum_hamCycles_split` (any function of the weight, summed over the tours);
* `mem_phi_iff_arith`: the arithmetic description of the edges, used by the machine that writes
  the adjacency matrix of `split A`.
-/
import EthFollowup.ExactHC.DirectedWeighted

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC.VSplit

open Finset EthFollowup.Hamiltonian EthFollowup.DirectedHamiltonian

variable {n : ℕ}

/-! ### The three copies of a vertex -/

def vIn (v : Fin n) : Fin (3 * n) := ⟨3 * v.val, by have := v.isLt; omega⟩
def vMid (v : Fin n) : Fin (3 * n) := ⟨3 * v.val + 1, by have := v.isLt; omega⟩
def vOut (v : Fin n) : Fin (3 * n) := ⟨3 * v.val + 2, by have := v.isLt; omega⟩

/-- The vertex of which `x` is a copy. -/
def orig (x : Fin (3 * n)) : Fin n := ⟨x.val / 3, by have := x.isLt; omega⟩

@[simp] theorem vIn_val (v : Fin n) : (vIn v).val = 3 * v.val := rfl
@[simp] theorem vMid_val (v : Fin n) : (vMid v).val = 3 * v.val + 1 := rfl
@[simp] theorem vOut_val (v : Fin n) : (vOut v).val = 3 * v.val + 2 := rfl

@[simp] theorem orig_vIn (v : Fin n) : orig (vIn v) = v := Fin.ext (by simp only [orig, vIn_val]; omega)
@[simp] theorem orig_vMid (v : Fin n) : orig (vMid v) = v :=
  Fin.ext (by simp only [orig, vMid_val]; omega)
@[simp] theorem orig_vOut (v : Fin n) : orig (vOut v) = v :=
  Fin.ext (by simp only [orig, vOut_val]; omega)

@[simp] theorem vIn_inj {u v : Fin n} : vIn u = vIn v ↔ u = v := by
  simp only [Fin.ext_iff, vIn_val]; omega
@[simp] theorem vMid_inj {u v : Fin n} : vMid u = vMid v ↔ u = v := by
  simp only [Fin.ext_iff, vMid_val]; omega
@[simp] theorem vOut_inj {u v : Fin n} : vOut u = vOut v ↔ u = v := by
  simp only [Fin.ext_iff, vOut_val]; omega

@[simp] theorem vIn_ne_vMid (u v : Fin n) : vIn u ≠ vMid v := by
  simp only [ne_eq, Fin.ext_iff, vIn_val, vMid_val]; omega
@[simp] theorem vIn_ne_vOut (u v : Fin n) : vIn u ≠ vOut v := by
  simp only [ne_eq, Fin.ext_iff, vIn_val, vOut_val]; omega
@[simp] theorem vMid_ne_vIn (u v : Fin n) : vMid u ≠ vIn v := by
  simp only [ne_eq, Fin.ext_iff, vIn_val, vMid_val]; omega
@[simp] theorem vMid_ne_vOut (u v : Fin n) : vMid u ≠ vOut v := by
  simp only [ne_eq, Fin.ext_iff, vMid_val, vOut_val]; omega
@[simp] theorem vOut_ne_vIn (u v : Fin n) : vOut u ≠ vIn v := by
  simp only [ne_eq, Fin.ext_iff, vIn_val, vOut_val]; omega
@[simp] theorem vOut_ne_vMid (u v : Fin n) : vOut u ≠ vMid v := by
  simp only [ne_eq, Fin.ext_iff, vMid_val, vOut_val]; omega

theorem cases3 (x : Fin (3 * n)) : x = vIn (orig x) ∨ x = vMid (orig x) ∨ x = vOut (orig x) := by
  simp only [Fin.ext_iff, vIn_val, vMid_val, vOut_val, orig]; omega

/-! ### The edges -/

/-- The edge of the arc `(u, v)`: `{u_out, v_in}`. -/
def arcE (a : Fin n × Fin n) : Sym2 (Fin (3 * n)) := s(vOut a.1, vIn a.2)
/-- The internal edge `{v_in, v_mid}`. -/
def inE (v : Fin n) : Sym2 (Fin (3 * n)) := s(vIn v, vMid v)
/-- The internal edge `{v_mid, v_out}`. -/
def outE (v : Fin n) : Sym2 (Fin (3 * n)) := s(vMid v, vOut v)

/-- The internal edges. -/
def intE : Finset (Sym2 (Fin (3 * n))) := univ.image inE ∪ univ.image outE

/-- The edge set of the split of an arc set `X`. -/
def phi (X : Finset (Fin n × Fin n)) : Finset (Sym2 (Fin (3 * n))) := X.image arcE ∪ intE

theorem arcE_injective : Function.Injective (arcE : Fin n × Fin n → Sym2 (Fin (3 * n))) := by
  intro a b h
  simp only [arcE, Sym2.eq_iff, vOut_inj, vIn_inj, vOut_ne_vIn, vIn_ne_vOut, false_and,
    or_false] at h
  exact Prod.ext h.1 h.2

@[simp] theorem arcE_inj {a b : Fin n × Fin n} : arcE a = arcE b ↔ a = b :=
  arcE_injective.eq_iff

@[simp] theorem arcE_ne_inE (a : Fin n × Fin n) (v : Fin n) : arcE a ≠ inE v := by
  simp [arcE, inE]
@[simp] theorem arcE_ne_outE (a : Fin n × Fin n) (v : Fin n) : arcE a ≠ outE v := by
  simp [arcE, outE]
@[simp] theorem inE_ne_arcE (a : Fin n × Fin n) (v : Fin n) : inE v ≠ arcE a :=
  (arcE_ne_inE a v).symm
@[simp] theorem outE_ne_arcE (a : Fin n × Fin n) (v : Fin n) : outE v ≠ arcE a :=
  (arcE_ne_outE a v).symm
@[simp] theorem inE_ne_outE (u v : Fin n) : inE u ≠ outE v := by
  simp [inE, outE]
@[simp] theorem outE_ne_inE (u v : Fin n) : outE u ≠ inE v := (inE_ne_outE v u).symm
@[simp] theorem inE_inj {u v : Fin n} : inE u = inE v ↔ u = v := by
  simp [inE]
@[simp] theorem outE_inj {u v : Fin n} : outE u = outE v ↔ u = v := by
  simp [outE]

theorem mem_phi {X : Finset (Fin n × Fin n)} {e : Sym2 (Fin (3 * n))} :
    e ∈ phi X ↔ (∃ a ∈ X, arcE a = e) ∨ (∃ v, inE v = e) ∨ (∃ v, outE v = e) := by
  simp [phi, intE]

@[simp] theorem arcE_mem_phi {X : Finset (Fin n × Fin n)} {a : Fin n × Fin n} :
    arcE a ∈ phi X ↔ a ∈ X := by
  rw [mem_phi]
  simp only [arcE_inj, exists_eq_right, inE_ne_arcE, outE_ne_arcE, exists_false, or_false]

@[simp] theorem inE_mem_phi (X : Finset (Fin n × Fin n)) (v : Fin n) : inE v ∈ phi X :=
  mem_phi.2 (Or.inr (Or.inl ⟨v, rfl⟩))

@[simp] theorem outE_mem_phi (X : Finset (Fin n × Fin n)) (v : Fin n) : outE v ∈ phi X :=
  mem_phi.2 (Or.inr (Or.inr ⟨v, rfl⟩))

theorem phi_injective : Function.Injective (phi : Finset (Fin n × Fin n) → _) := by
  intro X Y h
  ext a
  rw [← arcE_mem_phi (X := X), ← arcE_mem_phi (X := Y), h]

theorem phi_mono {X Y : Finset (Fin n × Fin n)} (h : X ⊆ Y) : phi X ⊆ phi Y :=
  union_subset_union (image_subset_image h) le_rfl

/-! ### Which copies an edge contains -/

@[simp] theorem vMid_mem_arcE (v : Fin n) (a : Fin n × Fin n) : vMid v ∉ arcE a := by
  simp [arcE, Sym2.mem_iff]
@[simp] theorem vMid_mem_inE {v u : Fin n} : vMid v ∈ inE u ↔ u = v := by
  simp [inE, Sym2.mem_iff, eq_comm]
@[simp] theorem vMid_mem_outE {v u : Fin n} : vMid v ∈ outE u ↔ u = v := by
  simp [outE, Sym2.mem_iff, eq_comm]
@[simp] theorem vIn_mem_arcE {v : Fin n} {a : Fin n × Fin n} : vIn v ∈ arcE a ↔ a.2 = v := by
  simp [arcE, Sym2.mem_iff, eq_comm]
@[simp] theorem vIn_mem_inE {v u : Fin n} : vIn v ∈ inE u ↔ u = v := by
  simp [inE, Sym2.mem_iff, eq_comm]
@[simp] theorem vIn_mem_outE (v u : Fin n) : vIn v ∉ outE u := by
  simp [outE, Sym2.mem_iff]
@[simp] theorem vOut_mem_arcE {v : Fin n} {a : Fin n × Fin n} : vOut v ∈ arcE a ↔ a.1 = v := by
  simp [arcE, Sym2.mem_iff, eq_comm]
@[simp] theorem vOut_mem_inE (v u : Fin n) : vOut v ∉ inE u := by
  simp [inE, Sym2.mem_iff]
@[simp] theorem vOut_mem_outE {v u : Fin n} : vOut v ∈ outE u ↔ u = v := by
  simp [outE, Sym2.mem_iff, eq_comm]

/-! ### Degrees -/

variable (X : Finset (Fin n × Fin n))

theorem filter_vMid (v : Fin n) :
    (phi X).filter (fun e => vMid v ∈ e) = {inE v, outE v} := by
  ext e
  simp only [mem_filter, mem_phi, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨a, -, rfl⟩ | ⟨u, rfl⟩ | ⟨u, rfl⟩, h⟩
    · exact absurd h (vMid_mem_arcE v a)
    · rw [vMid_mem_inE] at h; exact Or.inl (by rw [h])
    · rw [vMid_mem_outE] at h; exact Or.inr (by rw [h])
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inl ⟨v, rfl⟩), vMid_mem_inE.2 rfl⟩
    · exact ⟨Or.inr (Or.inr ⟨v, rfl⟩), vMid_mem_outE.2 rfl⟩

theorem filter_vIn (v : Fin n) :
    (phi X).filter (fun e => vIn v ∈ e) = insert (inE v) ((X.filter fun a => a.2 = v).image arcE) := by
  ext e
  simp only [mem_filter, mem_phi, mem_insert, mem_image]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩ | ⟨u, rfl⟩ | ⟨u, rfl⟩, h⟩
    · exact Or.inr ⟨a, ⟨ha, vIn_mem_arcE.1 h⟩, rfl⟩
    · rw [vIn_mem_inE] at h; exact Or.inl (by rw [h])
    · exact absurd h (vIn_mem_outE v u)
  · rintro (rfl | ⟨a, ⟨ha, h⟩, rfl⟩)
    · exact ⟨Or.inr (Or.inl ⟨v, rfl⟩), vIn_mem_inE.2 rfl⟩
    · exact ⟨Or.inl ⟨a, ha, rfl⟩, vIn_mem_arcE.2 h⟩

theorem filter_vOut (v : Fin n) :
    (phi X).filter (fun e => vOut v ∈ e) =
      insert (outE v) ((X.filter fun a => a.1 = v).image arcE) := by
  ext e
  simp only [mem_filter, mem_phi, mem_insert, mem_image]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩ | ⟨u, rfl⟩ | ⟨u, rfl⟩, h⟩
    · exact Or.inr ⟨a, ⟨ha, vOut_mem_arcE.1 h⟩, rfl⟩
    · exact absurd h (vOut_mem_inE v u)
    · rw [vOut_mem_outE] at h; exact Or.inl (by rw [h])
  · rintro (rfl | ⟨a, ⟨ha, h⟩, rfl⟩)
    · exact ⟨Or.inr (Or.inr ⟨v, rfl⟩), vOut_mem_outE.2 rfl⟩
    · exact ⟨Or.inl ⟨a, ha, rfl⟩, vOut_mem_arcE.2 h⟩

theorem card_filter_vMid (v : Fin n) : ((phi X).filter (fun e => vMid v ∈ e)).card = 2 := by
  rw [filter_vMid, card_insert_of_notMem (by simp), card_singleton]

theorem card_filter_vIn (v : Fin n) :
    ((phi X).filter (fun e => vIn v ∈ e)).card = (X.filter fun a => a.2 = v).card + 1 := by
  rw [filter_vIn, card_insert_of_notMem (by simp), card_image_of_injective _ arcE_injective]

theorem card_filter_vOut (v : Fin n) :
    ((phi X).filter (fun e => vOut v ∈ e)).card = (X.filter fun a => a.1 = v).card + 1 := by
  rw [filter_vOut, card_insert_of_notMem (by simp), card_image_of_injective _ arcE_injective]

/-- `phi X` is 2-regular iff `X` is a cycle cover. -/
theorem twoRegular_phi_iff : TwoRegular (phi X) ↔ CycleCover X := by
  constructor
  · intro h v
    have h1 := h (vOut v)
    have h2 := h (vIn v)
    rw [card_filter_vOut] at h1
    rw [card_filter_vIn] at h2
    exact ⟨by omega, by omega⟩
  · intro h x
    rcases cases3 x with hx | hx | hx <;> rw [hx]
    · rw [card_filter_vIn, (h _).2]
    · exact card_filter_vMid X _
    · rw [card_filter_vOut, (h _).1]

/-! ### Connectivity -/

theorem reach_of_adj {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} (f : V → V')
    (h : ∀ a b, G.Adj a b → G'.Reachable (f a) (f b)) {a b : V} (hab : G.Reachable a b) :
    G'.Reachable (f a) (f b) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hab
  induction hab with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hbc ih => exact ih.trans (h _ _ hbc)

theorem graphOf_adj {m : ℕ} {Y : Finset (Sym2 (Fin m))} {u w : Fin m} :
    (graphOf Y).Adj u w ↔ s(u, w) ∈ Y ∧ u ≠ w := by
  simp [graphOf, SimpleGraph.fromEdgeSet_adj]

theorem adj_of_mem {m : ℕ} {Y : Finset (Sym2 (Fin m))} {u w : Fin m} (h : s(u, w) ∈ Y)
    (hne : u ≠ w) : (graphOf Y).Reachable u w :=
  SimpleGraph.Adj.reachable (graphOf_adj.2 ⟨h, hne⟩)

theorem reach_arc {a : Fin n × Fin n} (ha : a ∈ X) :
    (graphOf (phi X)).Reachable (vMid a.1) (vMid a.2) := by
  have h1 : (graphOf (phi X)).Reachable (vMid a.1) (vOut a.1) :=
    adj_of_mem (outE_mem_phi X a.1) (vMid_ne_vOut _ _)
  have h2 : (graphOf (phi X)).Reachable (vOut a.1) (vIn a.2) :=
    adj_of_mem (arcE_mem_phi.2 ha) (vOut_ne_vIn _ _)
  have h3 : (graphOf (phi X)).Reachable (vIn a.2) (vMid a.2) :=
    adj_of_mem (inE_mem_phi X a.2) (vIn_ne_vMid _ _)
  exact h1.trans (h2.trans h3)

theorem reach_mid (x : Fin (3 * n)) : (graphOf (phi X)).Reachable x (vMid (orig x)) := by
  rcases cases3 x with hx | hx | hx
  · rw [hx, orig_vIn]; exact adj_of_mem (inE_mem_phi X _) (vIn_ne_vMid _ _)
  · rw [hx, orig_vMid]
  · rw [hx, orig_vOut]
    exact (adj_of_mem (outE_mem_phi X _) (vMid_ne_vOut _ _)).symm

theorem reach_orig {x y : Fin (3 * n)} (h : (graphOf (phi X)).Adj x y) :
    (graphOf (undirected X)).Reachable (orig x) (orig y) := by
  rw [graphOf_adj, mem_phi] at h
  obtain ⟨⟨a, ha, hae⟩ | ⟨u, hu⟩ | ⟨u, hu⟩, -⟩ := h
  · have hu : s(a.1, a.2) ∈ undirected X := mem_image.2 ⟨a, ha, rfl⟩
    have key : (graphOf (undirected X)).Reachable a.1 a.2 := by
      by_cases h12 : a.1 = a.2
      · rw [h12]
      · exact adj_of_mem hu h12
    rcases Sym2.eq_iff.1 hae with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2, orig_vOut, orig_vIn]; exact key
    · rw [← h1, ← h2, orig_vOut, orig_vIn]; exact key.symm
  · rcases Sym2.eq_iff.1 hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [← h1, ← h2] <;> simp only [orig_vIn, orig_vMid] <;> rfl
  · rcases Sym2.eq_iff.1 hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [← h1, ← h2] <;> simp only [orig_vOut, orig_vMid] <;> rfl

/-- `(Fin (3n), phi X)` is connected iff the underlying graph of `X` is. -/
theorem connected_phi_iff :
    (graphOf (phi X)).Connected ↔ (graphOf (undirected X)).Connected := by
  rw [SimpleGraph.connected_iff, SimpleGraph.connected_iff]
  constructor
  · rintro ⟨hp, ⟨x⟩⟩
    refine ⟨fun u v => ?_, ⟨orig x⟩⟩
    have := reach_of_adj orig (fun a b h => reach_orig X h) (hp (vMid u) (vMid v))
    simpa only [orig_vMid] using this
  · rintro ⟨hp, ⟨v⟩⟩
    refine ⟨fun x y => ?_, ⟨vIn v⟩⟩
    have hmid : ∀ u w, (graphOf (undirected X)).Adj u w →
        (graphOf (phi X)).Reachable (vMid u) (vMid w) := by
      intro u w h
      rw [graphOf_adj] at h
      obtain ⟨a, ha, hae⟩ := mem_image.1 h.1
      rcases Sym2.eq_iff.1 hae with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact reach_arc X ha
      · rw [← h1, ← h2]; exact (reach_arc X ha).symm
    exact (reach_mid X x).trans
      ((reach_of_adj vMid hmid (hp (orig x) (orig y))).trans (reach_mid X y).symm)

/-! ### The split graph -/

variable (A : Finset (Fin n × Fin n))

/-- **The split graph** of the digraph `A`, on `Fin (3 * n)`. -/
abbrev split : SimpleGraph (Fin (3 * n)) := graphOf (phi A)

theorem not_mem_phi_diag (x : Fin (3 * n)) : s(x, x) ∉ phi A := by
  intro h
  rw [mem_phi] at h
  rcases h with ⟨a, -, ha⟩ | ⟨u, hu⟩ | ⟨u, hu⟩
  · rcases Sym2.eq_iff.1 ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← h2] at h1 <;> simp at h1
  · rcases Sym2.eq_iff.1 hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← h2] at h1 <;> simp at h1
  · rcases Sym2.eq_iff.1 hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← h2] at h1 <;> simp at h1

theorem edgeFinset_split [Fintype (split A).edgeSet] : (split A).edgeFinset = phi A := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, graphOf_adj]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rintro rfl
    exact not_mem_phi_diag A x h

/-- `|E(split A)| ≤ |A| + 2n`. -/
theorem card_edgeFinset_split_le [Fintype (split A).edgeSet] : (split A).edgeFinset.card ≤ A.card + 2 * n := by
  rw [edgeFinset_split]
  refine (card_union_le _ _).trans ?_
  have h1 : (A.image arcE).card ≤ A.card := card_image_le
  have h2 : (intE : Finset (Sym2 (Fin (3 * n)))).card ≤ n + n := by
    refine (card_union_le _ _).trans ?_
    have := card_image_le (s := (univ : Finset (Fin n))) (f := inE)
    have := card_image_le (s := (univ : Finset (Fin n))) (f := outE)
    simp only [card_univ, Fintype.card_fin] at *
    omega
  omega

/-- **The bijection**: the Hamiltonian cycles of `split A` are the images under `phi` of the
directed Hamiltonian cycles of `A`. -/
theorem hamCycles_split : hamCycles (split A) = (dirHamCycles A).image phi := by
  ext H
  simp only [hamCycles, twoFactors, dirHamCycles, cycleCovers, mem_filter, mem_powerset,
    mem_image]
  rw [edgeFinset_split]
  constructor
  · rintro ⟨⟨hHA, h2⟩, hc⟩
    set X := A.filter fun a => arcE a ∈ H with hXd
    -- every internal edge is in `H`
    have hint : ∀ v, inE v ∈ H ∧ outE v ∈ H := by
      intro v
      have hsub : H.filter (fun e => vMid v ∈ e) ⊆ (phi A).filter (fun e => vMid v ∈ e) :=
        filter_subset_filter _ hHA
      have heq := eq_of_subset_of_card_le hsub (by rw [card_filter_vMid, h2])
      have hi : inE v ∈ (phi A).filter (fun e => vMid v ∈ e) := by rw [filter_vMid]; simp
      have ho : outE v ∈ (phi A).filter (fun e => vMid v ∈ e) := by rw [filter_vMid]; simp
      rw [← heq] at hi ho
      exact ⟨(mem_filter.1 hi).1, (mem_filter.1 ho).1⟩
    have hXH : phi X = H := by
      ext e
      rw [mem_phi]
      constructor
      · rintro (⟨a, ha, rfl⟩ | ⟨u, rfl⟩ | ⟨u, rfl⟩)
        · exact (mem_filter.1 ha).2
        · exact (hint u).1
        · exact (hint u).2
      · intro he
        rcases mem_phi.1 (hHA he) with ⟨a, ha, rfl⟩ | hu | hu
        · exact Or.inl ⟨a, mem_filter.2 ⟨ha, he⟩, rfl⟩
        · exact Or.inr (Or.inl hu)
        · exact Or.inr (Or.inr hu)
    refine ⟨X, ⟨⟨filter_subset _ _, ?_⟩, ?_⟩, hXH⟩
    · rw [← twoRegular_phi_iff, hXH]; exact h2
    · rw [← connected_phi_iff, hXH]; exact hc
  · rintro ⟨X, ⟨⟨hXA, hcc⟩, hc⟩, rfl⟩
    exact ⟨⟨phi_mono hXA, (twoRegular_phi_iff X).2 hcc⟩, (connected_phi_iff X).2 hc⟩

/-- **`#HC(split A) = #DHC(A)`.** -/
theorem card_hamCycles_split : (hamCycles (split A)).card = (dirHamCycles A).card := by
  rw [hamCycles_split, card_image_of_injective _ phi_injective]

/-! ### Weights -/

/-- The weight of the pair `(x, y)` of copies: `w (u, v)` for `(u_out, v_in)` (either order),
`0` otherwise. -/
def sw (w : Fin n × Fin n → ℕ) (x y : Fin (3 * n)) : ℕ :=
  if x.val % 3 = 2 ∧ y.val % 3 = 0 then w (orig x, orig y)
  else if x.val % 3 = 0 ∧ y.val % 3 = 2 then w (orig y, orig x) else 0

theorem sw_comm (w : Fin n × Fin n → ℕ) (x y : Fin (3 * n)) : sw w x y = sw w y x := by
  unfold sw
  split_ifs <;> first | rfl | omega

/-- **The edge weights of the split graph**: the arc weight on `{u_out, v_in}`, `0` on the internal
edges. -/
def splitWt (w : Fin n × Fin n → ℕ) : Sym2 (Fin (3 * n)) → ℕ :=
  Sym2.lift ⟨sw w, sw_comm w⟩

@[simp] theorem splitWt_mk (w : Fin n × Fin n → ℕ) (x y : Fin (3 * n)) :
    splitWt w s(x, y) = sw w x y := rfl

@[simp] theorem splitWt_arcE (w : Fin n × Fin n → ℕ) (a : Fin n × Fin n) :
    splitWt w (arcE a) = w a := by
  show sw w (vOut a.1) (vIn a.2) = w a
  unfold sw
  split_ifs with h1
  · simp only [orig_vOut, orig_vIn]
  · exfalso; simp only [vOut_val, vIn_val] at h1; omega
  · exfalso; simp only [vOut_val, vIn_val] at h1; omega

@[simp] theorem splitWt_inE (w : Fin n × Fin n → ℕ) (v : Fin n) : splitWt w (inE v) = 0 := by
  show sw w (vIn v) (vMid v) = 0
  unfold sw
  split_ifs with h1 h2 <;> (try simp only [vIn_val, vMid_val] at *) <;> omega

@[simp] theorem splitWt_outE (w : Fin n × Fin n → ℕ) (v : Fin n) : splitWt w (outE v) = 0 := by
  show sw w (vMid v) (vOut v) = 0
  unfold sw
  split_ifs with h1 h2 <;> (try simp only [vOut_val, vMid_val] at *) <;> omega

theorem splitWt_le {w : Fin n × Fin n → ℕ} {W : ℕ} (hw : ∀ a, w a ≤ W) (e : Sym2 (Fin (3 * n))) :
    splitWt w e ≤ W := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [splitWt_mk, sw]
    split_ifs
    · exact hw _
    · exact hw _
    · exact Nat.zero_le _

theorem disjoint_image_intE : Disjoint (X.image arcE) intE := by
  rw [disjoint_left]
  intro e he hi
  obtain ⟨a, -, rfl⟩ := mem_image.1 he
  simp only [intE, mem_union, mem_image, mem_univ, true_and] at hi
  rcases hi with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact arcE_ne_inE a v hv.symm
  · exact arcE_ne_outE a v hv.symm

/-- **The split preserves weights**: `w'(phi X) = w(X)`. -/
theorem wt_phi (w : Fin n × Fin n → ℕ) : wt (splitWt w) (phi X) = arcWt w X := by
  unfold wt phi arcWt
  rw [sum_union (disjoint_image_intE X), sum_image (fun a _ b _ h => arcE_injective h)]
  have h0 : ∑ e ∈ (intE : Finset (Sym2 (Fin (3 * n)))), splitWt w e = 0 := by
    refine sum_eq_zero fun e he => ?_
    simp only [intE, mem_union, mem_image, mem_univ, true_and] at he
    rcases he with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> simp
  rw [h0, add_zero]
  exact sum_congr rfl fun a _ => splitWt_arcE w a

/-- Any function of the tour weight, summed over the tours of `split A`, is the same sum over the
directed tours of `A`. -/
theorem sum_hamCycles_split {R : Type*} [AddCommMonoid R] (w : Fin n × Fin n → ℕ) (f : ℕ → R) :
    ∑ H ∈ hamCycles (split A), f (wt (splitWt w) H) = ∑ X ∈ dirHamCycles A, f (arcWt w X) := by
  rw [hamCycles_split, sum_image (fun X _ Y _ h => phi_injective h)]
  exact sum_congr rfl fun X _ => by rw [wt_phi]

/-- **Tours by weight are preserved**: `c_j(split A, w') = c_j(A, w)`. -/
theorem tourCount_split (w : Fin n × Fin n → ℕ) (j : ℕ) :
    tourCount (split A) (splitWt w) j = dtourCount A w j := by
  unfold tourCount dtourCount
  rw [hamCycles_split]
  have : (((dirHamCycles A).image phi).filter fun H => wt (splitWt w) H = j) =
      ((dirHamCycles A).filter fun X => arcWt w X = j).image phi := by
    ext H
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨X, hX, rfl⟩, hj⟩
      exact ⟨X, ⟨hX, by rwa [wt_phi] at hj⟩, rfl⟩
    · rintro ⟨X, ⟨hX, hj⟩, rfl⟩
      exact ⟨⟨X, hX, rfl⟩, by rwa [wt_phi]⟩
  rw [this, card_image_of_injective _ phi_injective]

/-! ### The edges in arithmetic form -/

/-- **The adjacency of `split A` in arithmetic form** (what the preprocessing machine computes):
`x ~ y` iff they are copies of the same vertex with residues `{0, 1}` or `{1, 2}`, or
`x = u_out`, `y = v_in` with `(u, v) ∈ A`, or the same with `x` and `y` exchanged. -/
theorem eq_vIn {x : Fin (3 * n)} (h : x.val % 3 = 0) : x = vIn (orig x) :=
  Fin.ext (by simp only [vIn_val, orig]; omega)
theorem eq_vMid {x : Fin (3 * n)} (h : x.val % 3 = 1) : x = vMid (orig x) :=
  Fin.ext (by simp only [vMid_val, orig]; omega)
theorem eq_vOut {x : Fin (3 * n)} (h : x.val % 3 = 2) : x = vOut (orig x) :=
  Fin.ext (by simp only [vOut_val, orig]; omega)

theorem mem_phi_iff_arith (x y : Fin (3 * n)) :
    s(x, y) ∈ phi A ↔
      (x.val / 3 = y.val / 3 ∧ (x.val % 3 + y.val % 3 = 1 ∨ x.val % 3 + y.val % 3 = 3)) ∨
      (x.val % 3 = 2 ∧ y.val % 3 = 0 ∧ (orig x, orig y) ∈ A) ∨
      (x.val % 3 = 0 ∧ y.val % 3 = 2 ∧ (orig y, orig x) ∈ A) := by
  rw [mem_phi]
  constructor
  · rintro (⟨a, ha, hae⟩ | ⟨u, hu⟩ | ⟨u, hu⟩)
    · rcases Sym2.eq_iff.1 hae with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1 h2
        refine Or.inr (Or.inl ⟨by simp only [vOut_val]; omega, by simp only [vIn_val]; omega, ?_⟩)
        simpa using ha
      · subst h1 h2
        refine Or.inr (Or.inr ⟨by simp only [vIn_val]; omega, by simp only [vOut_val]; omega, ?_⟩)
        simpa using ha
    · rcases Sym2.eq_iff.1 hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;>
        exact Or.inl ⟨by simp only [vIn_val, vMid_val]; omega, by simp only [vIn_val, vMid_val]; omega⟩
    · rcases Sym2.eq_iff.1 hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;>
        exact Or.inl ⟨by simp only [vOut_val, vMid_val]; omega,
          by simp only [vOut_val, vMid_val]; omega⟩
  · rintro (⟨hq, hr⟩ | ⟨h1, h2, ha⟩ | ⟨h1, h2, ha⟩)
    · have ho : orig x = orig y := Fin.ext hq
      have hx3 : x.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have hy3 : y.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
      rcases (by omega : (x.val % 3 = 0 ∧ y.val % 3 = 1) ∨ (x.val % 3 = 1 ∧ y.val % 3 = 0) ∨
          (x.val % 3 = 1 ∧ y.val % 3 = 2) ∨ (x.val % 3 = 2 ∧ y.val % 3 = 1)) with
        ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have ex := eq_vIn h1
        have ey := eq_vMid h2
        rw [ho] at ex
        exact Or.inr (Or.inl ⟨orig y, by rw [inE, ← ex, ← ey]⟩)
      · have ex := eq_vMid h1
        have ey := eq_vIn h2
        rw [ho] at ex
        exact Or.inr (Or.inl ⟨orig y, by rw [inE, ← ex, ← ey, Sym2.eq_swap]⟩)
      · have ex := eq_vMid h1
        have ey := eq_vOut h2
        rw [ho] at ex
        exact Or.inr (Or.inr ⟨orig y, by rw [outE, ← ex, ← ey]⟩)
      · have ex := eq_vOut h1
        have ey := eq_vMid h2
        rw [ho] at ex
        exact Or.inr (Or.inr ⟨orig y, by rw [outE, ← ex, ← ey, Sym2.eq_swap]⟩)
    · refine Or.inl ⟨(orig x, orig y), ha, ?_⟩
      have ex := eq_vOut h1
      have ey := eq_vIn h2
      show s(vOut (orig x), vIn (orig y)) = s(x, y)
      rw [← ex, ← ey]
    · refine Or.inl ⟨(orig y, orig x), ha, ?_⟩
      have ex := eq_vIn h1
      have ey := eq_vOut h2
      show s(vOut (orig y), vIn (orig x)) = s(x, y)
      rw [← ex, ← ey, Sym2.eq_swap]

end EthFollowup.ExactHC.VSplit
