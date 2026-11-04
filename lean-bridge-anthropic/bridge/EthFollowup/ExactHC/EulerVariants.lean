/-
# Eulerian circuits with forbidden transitions and of minimum cost, at Turing-machine level

Two variants of `theoremEuler` (`EulerTheorems.lean`), from the same edge splitting
(`EulerSplit.lean`; Eulerian circuits in Kotzig's description, `ESplit.eulerCircuits`: transition
systems with connected transition graph).

## Forbidden transitions
A transition table `A : Fin n → Fin n → Fin n → Bool` (`A x y z`: the transition at `x` between the
edges `xy` and `xz` is allowed; it is allowed if allowed in either order) is written after the code
of the graph as `n³` bits in row-major order (`eulerCodeA`). The split graph `eulerSplit G A` keeps
only the allowed transition edges, and `#HC(eulerSplit G A) = #(eulerCircuits G A)`
(`ESplit.card_hamCycles_eulerSplit`).
* `theoremEulerA`: for every `δ > 0` and `Δ`, one Turing machine writes `#(eulerCircuits G A)` in
  binary within `⌊C·(n+2)^C·2^{δm}⌋` steps on every graph of maximum degree `≤ Δ`.

## Minimum-cost circuits
Transition costs `c : Fin n → Fin n → Fin n → ℕ`, `c x y z ≤ W`, are written after the code of the
graph as `W` in unary and `n³` blocks of `W + 1` bits (`eulerCodeW`). The cost of a transition is
`min (c x y z) (c x z y)` (transitions are unordered; for a symmetric `c` this is `c x y z`), the
cost `ecost G c T` of an Eulerian circuit is the sum of the costs of its transitions
(`ecost_eq_sum`). These costs become edge weights of the split graph (`eWt`, weight `0` on the
internal edges), and the TSP machine (`Dir.tsp_stepped`) is run on it.
* `theoremEulerW`: the Kronecker integer `ekronNum G c = 3m · Σ_{T} 2^{bK(3m)·cost(T)}` within
  `⌊C·(n+2)^C·2^{δm}·(W+2)^C⌋` steps;
* `theoremEulerW_decode`: digit `j` (base `2^{bK(3m)}`) is `3m` times the number of Eulerian circuits
  of cost `j`; the minimum cost is the position of the lowest non-zero digit, and the number of
  optimal circuits is that digit divided by `3m`.

Standard axioms only.
-/
import EthFollowup.ExactHC.EulerSearch

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Groundwork Groundwork.Prog GraphProblems Asm Finset EthFollowup.Hamiltonian

namespace EulV

open ESplit Eul

variable {n : ℕ}

/-! ## Cubes of entries -/

/-- The `n³` entries `f x y z` in row-major order. -/
def cube {β : Type} (f : Fin n → Fin n → Fin n → β) : List β :=
  (List.finRange n).flatMap fun x => (List.finRange n).flatMap fun y => (List.finRange n).map fun z => f x y z

theorem length_cube {β : Type} (f : Fin n → Fin n → Fin n → β) : (cube f).length = n * (n * n) := by
  simp [cube, List.length_flatMap]

theorem getD_cube {β : Type} (f : Fin n → Fin n → Fin n → β) (d : β) (x y z : Fin n) :
    (cube f).getD ((x.val * n + y.val) * n + z.val) d = f x y z := by
  have hyz : y.val * n + z.val < n * n := by
    have := y.2; have := z.2; nlinarith
  rw [show (x.val * n + y.val) * n + z.val = x.val * (n * n) + (y.val * n + z.val) by ring, cube,
    Read.getD_flatMap _ (n * n) d hyz _ (fun _ _ => by simp [List.length_flatMap]) x.val,
    List.getElem?_eq_getElem (by simp : x.val < (List.finRange n).length)]
  simp only [List.getElem_finRange, Option.map_some, Option.getD_some]
  rw [Read.getD_flatMap _ n d z.2 _ (fun _ _ => by simp) y.val,
    List.getElem?_eq_getElem (by simp : y.val < (List.finRange n).length)]
  simp only [List.getElem_finRange, Option.map_some, Option.getD_some]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simp : z.val < (List.finRange n).length)]
  simp

theorem mem_cube {β : Type} {f : Fin n → Fin n → Fin n → β} {b : β} (h : b ∈ cube f) :
    ∃ x y z, f x y z = b := by
  simp only [cube, List.mem_flatMap, List.mem_map] at h
  obtain ⟨x, -, y, -, z, -, rfl⟩ := h
  exact ⟨x, y, z, rfl⟩

/-! ## Forbidden transitions: the input word and the preprocessing -/

section A

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Fin n → Fin n → Fin n → Bool)

/-- **The input word with a transition table**: `code G`, then the `n³` bits `A x y z` in row-major
order. -/
noncomputable def eulerCodeA : List Bool := code G ++ cube A

theorem length_eulerCodeA : (eulerCodeA G A).length = n + 1 + n * n + n * (n * n) := by
  rw [eulerCodeA, List.length_append, length_code stMatrixLength, length_cube]

/-- The input word as read by `read1`. -/
noncomputable def aOfA : GIn := (List.replicate n (), matrix G ++ cube A)

theorem read1_codeA : read1 (eulerCodeA G A) = aOfA G A := by
  rw [read1, eulerCodeA, code, List.append_assoc, Read.ones_unary_append, Read.rest_unary_append]; rfl

theorem adjW_aOfA {u v : ℕ} (hu : u < n) (hv : v < n) : adjW (aOfA G A) u v = adjW (aOf G) u v := by
  have hm : (matrix G).length = n * n := stMatrixLength n G
  have hi : u * n + v < (matrix G).length := by rw [hm]; nlinarith
  simp only [adjW, adjB, aOfA, aOf, List.length_replicate]
  rw [List.getD_append _ _ _ _ hi]

theorem edgeListW_aOfA : edgeListW (aOfA G A) = edgesN G := by
  rw [← edgeListW_aOf G]
  unfold edgeListW
  have h1 : (aOfA G A).1.length = n := by simp [aOfA]
  rw [h1, aOf_len]
  refine List.flatMap_congr fun u hu => ?_
  congr 1
  refine List.filter_congr fun v hv => ?_
  rw [adjW_aOfA G A (List.mem_range.1 hu) (List.mem_range.1 hv)]

theorem length_edgeListW_aOfA : (edgeListW (aOfA G A)).length = M G := by
  rw [edgeListW_aOfA, edgesN, List.length_map]

end A

/-- The bit `(x, y, z)` of the transition table, read from the word. -/
def aBit (a : GIn) (x y z : ℕ) : Bool :=
  a.2.getD (a.1.length * a.1.length + ((x * a.1.length + y) * a.1.length + z)) false

theorem aBit_aOfA (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Fin n → Fin n → Fin n → Bool)
    (x y z : Fin n) : aBit (aOfA G A) x.val y.val z.val = A x y z := by
  have hm : (matrix G).length = n * n := stMatrixLength n G
  have h1 : (aOfA G A).1.length = n := by simp [aOfA]
  rw [aBit, h1]
  simp only [aOfA]
  rw [List.getD_append_right _ _ _ _ (by rw [hm]; omega), hm, Nat.add_sub_cancel_left, getD_cube]

/-- The entry `(x, y)` of the adjacency matrix of `eulerSplit G A`, from the word. -/
def eAdjWA (a : GIn) (x y : ℕ) : Bool :=
  (decide (x / 3 = y / 3) && (decide (x % 3 + y % 3 = 1) || decide (x % 3 + y % 3 = 3))) ||
    (!decide (x / 3 = y / 3) && !decide (x % 3 = 1) && !decide (y % 3 = 1) &&
      decide (ptN (edgeListW a) x = ptN (edgeListW a) y) &&
      (aBit a (ptN (edgeListW a) x) (farN (edgeListW a) x) (farN (edgeListW a) y) ||
        aBit a (ptN (edgeListW a) x) (farN (edgeListW a) y) (farN (edgeListW a) x)))

/-- The adjacency matrix of `eulerSplit G A`, from the word. -/
def eMatrixA (a : GIn) : List Bool :=
  (List.range (3 * (edgeListW a).length)).flatMap fun x =>
    (List.range (3 * (edgeListW a).length)).map fun y => eAdjWA a x y

/-- The code of `eulerSplit G A`, from the word as read by `read1`. -/
def eSplitGA (a : GIn) : List Bool := GraphProblems.unary (3 * (edgeListW a).length) ++ eMatrixA a

/-- **The preprocessing of `theoremEulerA`.** -/
def eulAW (x : List Bool) : List Bool := eSplitGA (read1 x)

section A2

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Fin n → Fin n → Fin n → Bool)

theorem eAdjWA_aOfA (x y : Fin (3 * M G)) :
    eAdjWA (aOfA G A) x.val y.val = true ↔ (eulerSplit G A).Adj x y := by
  rw [graphOf_adj', mem_union, mem_intE_arith, mem_cliqueE_arith]
  have key : eAdjWA (aOfA G A) x.val y.val = true ↔
      (x.val / 3 = y.val / 3 ∧ (x.val % 3 + y.val % 3 = 1 ∨ x.val % 3 + y.val % 3 = 3)) ∨
      (x.val / 3 ≠ y.val / 3 ∧ x.val % 3 ≠ 1 ∧ y.val % 3 ≠ 1 ∧ ptF G x = ptF G y ∧
        (A (ptF G x) (farF G x) (farF G y) = true ∨ A (ptF G x) (farF G y) (farF G x) = true)) := by
    unfold eAdjWA
    rw [edgeListW_aOfA, ptN_edgesN, ptN_edgesN, farN_edgesN, farN_edgesN, aBit_aOfA, aBit_aOfA]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, ne_eq, Fin.val_inj, and_assoc]
  rw [key]
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rintro rfl
    rcases h with ⟨-, h⟩ | ⟨h, -⟩
    · omega
    · exact h rfl
  · exact fun h => h.1

/-- **The preprocessing maps the word of `(G, A)` to the code of `eulerSplit G A`.** -/
theorem eulAW_code : eulAW (eulerCodeA G A) = code (eulerSplit G A) := by
  rw [eulAW, read1_codeA]
  simp only [eSplitGA, code, length_edgeListW_aOfA]
  congr 1
  unfold eMatrixA GraphProblems.matrix
  rw [length_edgeListW_aOfA, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  refine List.flatMap_congr fun x _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun y _ => ?_
  simp only [Function.comp_apply]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  exact eAdjWA_aOfA G A x y

end A2

section PolyA

variable {α : Type} [Enc α]

theorem farN_polyT {E : α → List (ℕ × ℕ)} {x : α → ℕ} (hE : PolyT E) (hx : PolyT x) :
    PolyT fun t => farN (E t) (x t) := by
  have d3 : PolyT fun _ : α => (3 : ℕ) := PolyT.const 3
  have hxd := PolyT.div hx d3
  have hxm := PolyT.mod hx d3
  have hg : PolyT fun t => (E t).getD (x t / 3) (0, 0) := PolyT.getD hE hxd (PolyT.const _)
  unfold farN
  exact PolyT.ite' (PolyT.decide_eq hxm (PolyT.const 0)) (PolyT.snd hg) (PolyT.fst hg)

theorem aBit_polyT {a : α → GIn} {x y z : α → ℕ} (ha : PolyT a) (hx : PolyT x) (hy : PolyT y)
    (hz : PolyT z) : PolyT fun t => aBit (a t) (x t) (y t) (z t) := by
  have hl : PolyT fun t => (a t).1.length := by fun_prop
  have hi : PolyT fun t => (a t).1.length * (a t).1.length +
      ((x t * (a t).1.length + y t) * (a t).1.length + z t) :=
    PolyT.add (PolyT.mul hl hl)
      (PolyT.add (PolyT.mul (PolyT.add (PolyT.mul hx hl) hy) hl) hz)
  unfold aBit
  exact PolyT.getD (by fun_prop) hi (PolyT.const _)

theorem eAdjWA_polyT {a : α → GIn} {x y : α → ℕ} (ha : PolyT a) (hx : PolyT x) (hy : PolyT y) :
    PolyT fun t => eAdjWA (a t) (x t) (y t) := by
  have d3 : PolyT fun _ : α => (3 : ℕ) := PolyT.const 3
  have hxd := PolyT.div hx d3
  have hyd := PolyT.div hy d3
  have hxm := PolyT.mod hx d3
  have hym := PolyT.mod hy d3
  have hs := PolyT.add hxm hym
  have hE : PolyT fun t => edgeListW (a t) := PolyT.comp edgeListW_polyT ha
  have px := ptN_polyT hE hx
  have py := ptN_polyT hE hy
  have fx := farN_polyT hE hx
  have fy := farN_polyT hE hy
  unfold eAdjWA
  exact PolyT.or' (PolyT.and' (PolyT.decide_eq hxd hyd)
      (PolyT.or' (PolyT.decide_eq hs (PolyT.const 1)) (PolyT.decide_eq hs (PolyT.const 3))))
    (PolyT.and' (PolyT.and' (PolyT.and' (PolyT.and' (PolyT.not' (PolyT.decide_eq hxd hyd))
      (PolyT.not' (PolyT.decide_eq hxm (PolyT.const 1))))
      (PolyT.not' (PolyT.decide_eq hym (PolyT.const 1))))
      (PolyT.decide_eq px py))
      (PolyT.or' (aBit_polyT ha px fx fy) (aBit_polyT ha px fy fx)))

theorem eSplitGA_polyT : PolyT eSplitGA := by
  have h1 : PolyT fun a : GIn => List.range (3 * (edgeListW a).length) := PolyT.range three_m_unary
  have h2 : PolyT fun p : GIn × ℕ => List.range (3 * (edgeListW p.1).length) :=
    PolyT.comp h1 (g := fun p : GIn × ℕ => p.1) (by fun_prop)
  have h3 : PolyT fun p : (GIn × ℕ) × ℕ => eAdjWA p.1.1 p.1.2 p.2 :=
    eAdjWA_polyT (by fun_prop) (by fun_prop) (by fun_prop)
  have h4 : PolyT fun a : GIn => GraphProblems.unary (3 * (edgeListW a).length) := by
    have h : PolyT fun a : GIn =>
        (List.replicate (3 * (edgeListW a).length) ()).map (fun _ => true) ++ [false] := by
      have := three_m_unary; fun_prop
    refine h.congr fun a => ?_
    simp [GraphProblems.unary, List.map_replicate]
  unfold eSplitGA eMatrixA; fun_prop

theorem eulAW_polyT : PolyT eulAW :=
  (PolyT.comp eSplitGA_polyT stCertRead.1 : PolyT fun x => eSplitGA (read1 x))

end PolyA

/-- Small polynomial facts. -/
theorem cube_le (n : ℕ) : n * (n * n) ≤ (n + 2) ^ 4 := by
  have h1 : n * (n * n) ≤ (n + 2) * ((n + 2) * (n + 2)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
  have h2 : (n + 2) * ((n + 2) * (n + 2)) ≤ (n + 2) ^ 4 := by
    rw [show (n + 2) ^ 4 = (n + 2) * ((n + 2) * (n + 2)) * (n + 2) by ring]
    exact Nat.le_mul_of_pos_right _ (by omega)
  exact h1.trans h2

/-! ## Minimum-cost circuits: the costs -/

section Cost

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : Fin n → Fin n → Fin n → ℕ)

/-- The cost on the pair `(x, y)` of copies: `min (c z y' y'') (c z y'' y')` if `x`, `y` are end
copies of distinct edges `z y'`, `z y''` at the same vertex `z`, `0` otherwise. -/
def ew (x y : Fin (3 * M G)) : ℕ :=
  if x.val / 3 ≠ y.val / 3 ∧ x.val % 3 ≠ 1 ∧ y.val % 3 ≠ 1 ∧ ptF G x = ptF G y then
    min (c (ptF G x) (farF G x) (farF G y)) (c (ptF G x) (farF G y) (farF G x))
  else 0

theorem ew_comm (x y : Fin (3 * M G)) : ew G c x y = ew G c y x := by
  unfold ew
  by_cases h : x.val / 3 ≠ y.val / 3 ∧ x.val % 3 ≠ 1 ∧ y.val % 3 ≠ 1 ∧ ptF G x = ptF G y
  · have h' : y.val / 3 ≠ x.val / 3 ∧ y.val % 3 ≠ 1 ∧ x.val % 3 ≠ 1 ∧ ptF G y = ptF G x :=
      ⟨fun e => h.1 e.symm, h.2.2.1, h.2.1, h.2.2.2.symm⟩
    rw [if_pos h, if_pos h', h.2.2.2, min_comm]
  · have h' : ¬(y.val / 3 ≠ x.val / 3 ∧ y.val % 3 ≠ 1 ∧ x.val % 3 ≠ 1 ∧ ptF G y = ptF G x) :=
      fun h' => h ⟨fun e => h'.1 e.symm, h'.2.2.1, h'.2.1, h'.2.2.2.symm⟩
    rw [if_neg h, if_neg h']

/-- **The edge weights of the split graph**: the cost of the transition on a transition edge, `0` on
the internal edges. -/
def eWt : Sym2 (Fin (3 * M G)) → ℕ := Sym2.lift ⟨ew G c, ew_comm G c⟩

@[simp] theorem eWt_mk (x y : Fin (3 * M G)) : eWt G c s(x, y) = ew G c x y := rfl

theorem eWt_le {W : ℕ} (hc : ∀ x y z, c x y z ≤ W) (e : Sym2 (Fin (3 * M G))) : eWt G c e ≤ W := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [eWt_mk, ew]
    split_ifs
    · exact (min_le_left _ _).trans (hc _ _ _)
    · exact Nat.zero_le _

theorem eWt_intE {e : Sym2 (Fin (3 * M G))} (he : e ∈ intE G) : eWt G c e = 0 := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_intE_arith] at he
    rw [eWt_mk, ew, if_neg (fun h => h.1 he.1)]

/-- **The cost of an Eulerian circuit** `T` (Kotzig's description): the total weight of its
transition graph `phiE G T`, i.e. the sum of the costs of its transitions (`ecost_eq_sum`). -/
def ecost (T : Finset (Sym2 (Fin (3 * M G)))) : ℕ := wt (eWt G c) (phiE G T)

theorem ecost_eq_sum {T : Finset (Sym2 (Fin (3 * M G)))} (hT : T ∈ eulerCircuitsAll G) :
    ecost G c T = ∑ e ∈ T, eWt G c e := by
  have hs : T ⊆ cliqueE G fun _ _ _ => true :=
    mem_powerset.1 (mem_filter.1 (mem_filter.1 hT).1).1
  have hd : Disjoint T (intE G) :=
    disjoint_left.2 fun e he hi => disjoint_left.1 (disjoint_intE_cliqueE G _) hi (hs he)
  rw [ecost, wt, phiE, sum_union hd, sum_eq_zero fun e he => eWt_intE G c he, add_zero]

/-- **The Kronecker integer of the costs**: `3m · Σ_{T} 2^{bK(3m)·cost(T)}` over the Eulerian
circuits `T` of `G`. -/
def ekronNum : ℕ := (3 * M G) * ∑ T ∈ eulerCircuitsAll G, 2 ^ (bK (3 * M G) * ecost G c T)

/-- Digit `j` of the Kronecker integer of the costs, in base `2^{bK(3m)}`. -/
def ekronDigit (j : ℕ) : ℕ := ekronNum G c / 2 ^ (bK (3 * M G) * j) % 2 ^ bK (3 * M G)

/-- The number of Eulerian circuits of cost `j`. -/
def etourCount (j : ℕ) : ℕ := ((eulerCircuitsAll G).filter fun T => ecost G c T = j).card

/-- `k` is the minimum cost of an Eulerian circuit. -/
def IsMinECost (k : ℕ) : Prop :=
  (∃ T ∈ eulerCircuitsAll G, ecost G c T = k) ∧ ∀ T ∈ eulerCircuitsAll G, k ≤ ecost G c T

theorem kronNum_eul : kronNum (eulerSplitAll G) (eWt G c) = ekronNum G c := by
  unfold kronNum ekronNum
  rw [hamCycles_eulerSplit, sum_image (fun x hx y hy h => phiE_injOn G _ hx hy h)]
  rfl

theorem kronDigit_eul (j : ℕ) : kronDigit (eulerSplitAll G) (eWt G c) j = ekronDigit G c j := by
  unfold kronDigit ekronDigit
  rw [kronNum_eul]

theorem tourCount_eul (j : ℕ) : tourCount (eulerSplitAll G) (eWt G c) j = etourCount G c j := by
  unfold tourCount etourCount
  rw [hamCycles_eulerSplit, filter_image,
    card_image_of_injOn ((phiE_injOn G _).mono fun T hT => (mem_filter.1 hT).1)]
  rfl

theorem isMin_eul (k : ℕ) : IsMinTourWt (eulerSplitAll G) (eWt G c) k ↔ IsMinECost G c k := by
  unfold IsMinTourWt IsMinECost
  rw [hamCycles_eulerSplit]
  simp only [mem_image, ecost]
  constructor
  · rintro ⟨⟨H, ⟨T, hT, rfl⟩, hk⟩, h2⟩
    exact ⟨⟨T, hT, hk⟩, fun T hT => h2 _ ⟨T, hT, rfl⟩⟩
  · rintro ⟨⟨T, hT, hk⟩, h2⟩
    exact ⟨⟨_, ⟨T, hT, rfl⟩, hk⟩, fun H ⟨T, hT, hH⟩ => hH ▸ h2 T hT⟩

end Cost

/-! ## Minimum-cost circuits: the input word and the preprocessing -/

section WWord

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- **The input word with transition costs**: `code G`, `W` in unary, then the `n³` costs
`c x y z ≤ W` in row-major order as blocks of `W + 1` bits. -/
noncomputable def eulerCodeW (W : ℕ) (c : Fin n → Fin n → Fin n → ℕ) : List Bool :=
  code G ++ (GraphProblems.unary W ++ (cube fun x y z => wblock W (c x y z)).flatten)

theorem mem_cube_wblock {W : ℕ} {c : Fin n → Fin n → Fin n → ℕ} (hc : ∀ x y z, c x y z ≤ W) :
    ∀ b ∈ cube (fun x y z => wblock W (c x y z)), b.length = W + 1 := by
  intro b hb
  obtain ⟨x, y, z, rfl⟩ := mem_cube hb
  exact length_wblock (hc x y z)

theorem length_eulerCodeW {W : ℕ} {c : Fin n → Fin n → Fin n → ℕ} (hc : ∀ x y z, c x y z ≤ W) :
    (eulerCodeW G W c).length = n + 1 + n * n + (W + 1 + n * (n * n) * (W + 1)) := by
  have h : (cube fun x y z => wblock W (c x y z)).flatten.length = n * (n * n) * (W + 1) := by
    rw [List.length_flatten, List.map_congr_left fun b hb => mem_cube_wblock hc b hb,
      List.map_const', List.sum_replicate, smul_eq_mul, length_cube]
  simp only [eulerCodeW, List.length_append, length_code stMatrixLength, GraphProblems.unary,
    List.length_replicate, List.length_cons, List.length_nil, h]

/-- The context of the instance `(G, W, c)`. -/
noncomputable def cOfW (W : ℕ) (c : Fin n → Fin n → Fin n → ℕ) : TIn :=
  (aOf G, (List.replicate W (), (cube fun x y z => wblock W (c x y z)).flatten))

theorem readT_codeW (W : ℕ) (c : Fin n → Fin n → Fin n → ℕ) :
    readT (eulerCodeW G W c) = cOfW G W c := by
  have hm : (matrix G).length = n * n := stMatrixLength n G
  unfold readT eulerCodeW cOfW aOf code
  rw [List.append_assoc, Read.ones_unary_append, Read.rest_unary_append, List.take_left' hm,
    List.drop_left' hm, Read.ones_unary_append, Read.rest_unary_append]

end WWord

/-- The cost `(x, y, z)` read from the context. -/
def wgt3 (t : TIn) (x y z : ℕ) : ℕ :=
  ones (blk (t.2.1.length + 1) t.2.2 ((x * t.1.1.length + y) * t.1.1.length + z))

theorem wgt3_cOfW (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {W : ℕ}
    {c : Fin n → Fin n → Fin n → ℕ} (hc : ∀ x y z, c x y z ≤ W) (x y z : Fin n) :
    wgt3 (cOfW G W c) x.val y.val z.val = c x y z := by
  unfold wgt3 cOfW
  simp only [List.length_replicate, aOf_len]
  rw [blk_flatten (W + 1) _ (mem_cube_wblock hc), getD_cube, ones_wblock]

/-- The condition of a transition edge, read from the word. -/
def eCond (t : TIn) (x y : ℕ) : Bool :=
  !decide (x / 3 = y / 3) && !decide (x % 3 = 1) && !decide (y % 3 = 1) &&
    decide (ptN (edgeListW t.1) x = ptN (edgeListW t.1) y)

/-- The weight of the pair `(x, y)` of copies, read from the word. -/
def eWgtW (t : TIn) (x y : ℕ) : ℕ :=
  if eCond t x y then
    min (wgt3 t (ptN (edgeListW t.1) x) (farN (edgeListW t.1) x) (farN (edgeListW t.1) y))
      (wgt3 t (ptN (edgeListW t.1) x) (farN (edgeListW t.1) y) (farN (edgeListW t.1) x))
  else 0

/-- The weight blocks of the split graph. -/
def eBlocks (t : TIn) : List (List Bool) :=
  (List.range (3 * (edgeListW t.1).length)).flatMap fun x =>
    (List.range (3 * (edgeListW t.1).length)).map fun y => wblock t.2.1.length (eWgtW t x y)

/-- The word of the split graph with its weights, from the context. -/
def eSplitT (t : TIn) : List Bool :=
  eSplitG t.1 ++ (((t.2.1.map fun _ => true) ++ [false]) ++ (eBlocks t).flatten)

/-- **The preprocessing of `theoremEulerW`.** -/
def eulTW (x : List Bool) : List Bool := eSplitT (readT x)

section W2

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {W : ℕ} {c : Fin n → Fin n → Fin n → ℕ}

theorem eWgtW_cOfW (hc : ∀ x y z, c x y z ≤ W) (x y : Fin (3 * M G)) :
    eWgtW (cOfW G W c) x.val y.val = eWt G c s(x, y) := by
  have hE : edgeListW (cOfW G W c).1 = edgesN G := edgeListW_aOf G
  rw [eWt_mk, eWgtW, eCond, ew, hE, ptN_edgesN, ptN_edgesN, farN_edgesN, farN_edgesN,
    wgt3_cOfW G hc, wgt3_cOfW G hc]
  have hb : (!decide (x.val / 3 = y.val / 3) && !decide (x.val % 3 = 1) && !decide (y.val % 3 = 1) &&
      decide ((ptF G x).val = (ptF G y).val)) = true ↔
      (x.val / 3 ≠ y.val / 3 ∧ x.val % 3 ≠ 1 ∧ y.val % 3 ≠ 1 ∧ ptF G x = ptF G y) := by
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
      ne_eq, Fin.val_inj, and_assoc]
  by_cases h : x.val / 3 ≠ y.val / 3 ∧ x.val % 3 ≠ 1 ∧ y.val % 3 ≠ 1 ∧ ptF G x = ptF G y
  · rw [if_pos (hb.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hb.1 h')), if_neg h]

/-- **The preprocessing maps the word of `(G, W, c)` to the TSP word of the split graph with the
costs as edge weights.** -/
theorem eulTW_code (hc : ∀ x y z, c x y z ≤ W) :
    eulTW (eulerCodeW G W c) = tspCode (eulerSplitAll G) W (eWt G c) := by
  rw [eulTW, readT_codeW, eSplitT, tspCode]
  have hg : eSplitG (cOfW G W c).1 = code (eulerSplitAll G) := by
    rw [← eulW_code, eulW, read1_code]; rfl
  rw [hg]
  congr 2
  · simp [cOfW, GraphProblems.unary]
  · unfold wmat eBlocks wblocks
    congr 1
    have hl : (edgeListW (cOfW G W c).1).length = M G := length_edgeListW_aOf G
    simp only [hl]
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    refine List.flatMap_congr fun x _ => ?_
    rw [List.map_map]
    refine List.map_congr_left fun y _ => ?_
    simp only [Function.comp_apply]
    have := eWgtW_cOfW G hc x y
    simp only [cOfW, List.length_replicate] at this ⊢
    rw [this]

end W2

section PolyW

variable {α : Type} [Enc α]

theorem wgt3_unary {t : α → TIn} {x y z : α → ℕ} (ht : PolyT t) (hx : PolyT x) (hy : PolyT y)
    (hz : PolyT z) : Unary fun s => wgt3 (t s) (x s) (y s) (z s) := by
  unfold wgt3
  exact ones_unary (blk_polyT (by fun_prop) (by fun_prop) (by fun_prop))

theorem eWgtW_unary {t : α → TIn} {x y : α → ℕ} (ht : PolyT t) (hx : PolyT x) (hy : PolyT y) :
    Unary fun s => eWgtW (t s) (x s) (y s) := by
  have d3 : PolyT fun _ : α => (3 : ℕ) := PolyT.const 3
  have hxd := PolyT.div hx d3
  have hyd := PolyT.div hy d3
  have hxm := PolyT.mod hx d3
  have hym := PolyT.mod hy d3
  have hE : PolyT fun s => edgeListW (t s).1 := PolyT.comp edgeListW_polyT (by fun_prop)
  have px := ptN_polyT hE hx
  have py := ptN_polyT hE hy
  have fx := farN_polyT hE hx
  have fy := farN_polyT hE hy
  have h1 := wgt3_unary ht px fx fy
  have h2 := wgt3_unary ht px fy fx
  have hcnd : PolyT fun s => eCond (t s) (x s) (y s) := by
    unfold eCond
    exact PolyT.and' (PolyT.and' (PolyT.and' (PolyT.not' (PolyT.decide_eq hxd hyd))
      (PolyT.not' (PolyT.decide_eq hxm (PolyT.const 1))))
      (PolyT.not' (PolyT.decide_eq hym (PolyT.const 1)))) (PolyT.decide_eq px py)
  have hc' : PolyT fun s => decide (eCond (t s) (x s) (y s) = true) :=
    hcnd.congr fun s => by simp
  have hp : PolyT fun s => eWgtW (t s) (x s) (y s) := by
    unfold eWgtW
    exact PolyT.ite' hc' (PolyT.min' h1.poly h2.poly) (PolyT.const 0)
  refine Unary.of_le (h1.add h2) hp fun s => ?_
  unfold eWgtW
  split_ifs
  · exact (min_le_left _ _).trans (Nat.le_add_right _ _)
  · exact Nat.zero_le _

theorem eSplitT_polyT : PolyT eSplitT := by
  have hL : Unary fun p : (TIn × ℕ) × ℕ => p.1.1.2.1.length := Unary.of_length (by fun_prop)
  have hw : Unary fun p : (TIn × ℕ) × ℕ => eWgtW p.1.1 p.1.2 p.2 :=
    eWgtW_unary (by fun_prop) (by fun_prop) (by fun_prop)
  have h3 : PolyT fun p : (TIn × ℕ) × ℕ => wblock p.1.1.2.1.length (eWgtW p.1.1 p.1.2 p.2) :=
    Dir.wblock_polyT hL hw
  have h1 : PolyT fun t : TIn => List.range (3 * (edgeListW t.1).length) :=
    PolyT.comp (PolyT.range three_m_unary) (g := fun t : TIn => t.1) (by fun_prop)
  have h2 : PolyT fun p : TIn × ℕ => List.range (3 * (edgeListW p.1.1).length) :=
    PolyT.comp h1 (g := fun p : TIn × ℕ => p.1) (by fun_prop)
  have h0 : PolyT fun t : TIn => eSplitG t.1 :=
    PolyT.comp eSplitG_polyT (g := fun t : TIn => t.1) (by fun_prop)
  unfold eSplitT eBlocks; fun_prop

theorem eulTW_polyT : PolyT eulTW :=
  (PolyT.comp eSplitT_polyT readT_polyT : PolyT fun x => eSplitT (readT x))

end PolyW

end EulV

open Eul ESplit Dir EulS EulV in
/-- **Eulerian circuits with forbidden transitions: exact counting in time `2^{δm}` on graphs of
bounded degree, Turing-machine level, unconditional.** For every `δ > 0` and `Δ` there are a Turing
machine of Mathlib with finite alphabets and a constant `C` such that, on the word `eulerCodeA G A`
(the code of `G`, then the transition table `A` as `n³` bits) of any graph `G` with `n` vertices,
`m` edges and maximum degree `≤ Δ`, the machine halts within `⌊C·(n+2)^C·2^{δm}⌋` steps with the
number of Eulerian circuits of `G` using only transitions allowed by `A` (`ESplit.eulerCircuits G A`,
Kotzig's description) in binary. -/
theorem theoremEulerA (δ : ℝ) (hδ : 0 < δ) (Δ : ℕ) :
    ∃ (Mc : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (Mc.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Fin n → Fin n → Fin n → Bool),
        G.maxDegree ≤ Δ →
        GraphProblems.Outputs Mc (eulerCodeA G A) (Nat.bits (eulerCircuits G A).card)
          ⌊(C : ℝ) * ((n : ℝ) + 2) ^ C * (2 : ℝ) ^ (δ * (G.edgeFinset.card : ℝ))⌋₊ := by
  obtain ⟨Mh, ⟨inst⟩, A₀, hA₀⟩ := hc_stepped (δ / 3) (by positivity) (Δ + 1)
  have i1 : IsPolyT (Stepped.mapIn eulAW Mh) := IsPolyT.mapIn eulAW_polyT
  obtain ⟨TM, q, hfin, hM⟩ := out_of_runs (Stepped.mapIn eulAW Mh)
  refine ⟨TM, q * (bB A₀ + 1) * bB A₀ ^ q + bB A₀ + bB A₀ * q, hfin, fun n G _ A hΔ => ?_⟩
  have h := card_edgeFinset_eulerSplit_le G A
  have h' : 2 * (G.maxDegree + 1) * M G ≤ (Δ + 1) * (3 * M G) := by nlinarith
  obtain ⟨T, hr, hT⟩ := hA₀ (eulerSplit G A) (by convert Nat.le_trans h h')
  rw [← eulAW_code, card_hamCycles_eulerSplit] at hr
  have hr' := Stepped.mapIn_runs hr
  rw [← length_edgeList G, ← cast_n2]
  have hm := M_le G
  obtain ⟨s1, s2, s3, s4, s5⟩ := small hm
  have s6 := cube_le n
  rw [exp_three] at hT
  refine hM (bB A₀) _ _ _ _ (n + 2) ((2 : ℝ) ^ (δ * (M G : ℝ))) (by omega)
    (Real.one_le_rpow one_le_two (by positivity)) hr' ?_ (exp_part hδ (A := A₀) ?_ hT)
  · apply absorb hm
    rw [length_eulerCodeA]
    omega
  · exact (by have := le_bB A₀; omega : A₀ ≤ bB A₀).trans
      (Nat.le_mul_of_pos_right _ (by positivity))

open Eul ESplit Dir EulS EulV in
/-- **Minimum-cost Eulerian circuits in time `2^{δm}·poly(W)` on graphs of bounded degree,
Turing-machine level, unconditional.** For every `δ > 0` and `Δ` there are a Turing machine of
Mathlib with finite alphabets and a constant `C` such that, on the word `eulerCodeW G W c` (the code
of `G`, `W` in unary, the transition costs `c x y z ≤ W` as `n³` blocks of `W + 1` bits) of any graph
`G` with `n` vertices, `m` edges and maximum degree `≤ Δ`, the machine halts within
`⌊C·(n+2)^C·2^{δm}·(W+2)^C⌋` steps with the Kronecker integer
`ekronNum G c = 3m · Σ_{T} 2^{bK(3m)·cost(T)}` (over the Eulerian circuits `T`, Kotzig's
description; `cost(T)` the sum of the costs `min (c x y z) (c x z y)` of its transitions) in
binary. -/
theorem theoremEulerW (δ : ℝ) (hδ : 0 < δ) (Δ : ℕ) :
    ∃ (Mc : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (Mc.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ)
        (c : Fin n → Fin n → Fin n → ℕ), G.maxDegree ≤ Δ → (∀ x y z, c x y z ≤ W) →
        GraphProblems.Outputs Mc (eulerCodeW G W c) (Nat.bits (ekronNum G c))
          ⌊(C : ℝ) * ((n : ℝ) + 2) ^ C * (2 : ℝ) ^ (δ * (G.edgeFinset.card : ℝ)) *
            ((W : ℝ) + 2) ^ C⌋₊ := by
  obtain ⟨Mh, ⟨inst⟩, A₀, hA₀⟩ := tsp_stepped (δ / 3) (by positivity) (Δ + 1)
  have i1 : IsPolyT (Stepped.mapIn eulTW Mh) := IsPolyT.mapIn eulTW_polyT
  obtain ⟨TM, q, hfin, hM⟩ := out_of_runs (Stepped.mapIn eulTW Mh)
  refine ⟨TM, q * (bB A₀ + 1) * bB A₀ ^ q + bB A₀ + bB A₀ * q, hfin, fun n G _ W c hΔ hc => ?_⟩
  obtain ⟨T, hr, hT⟩ := hA₀ (eulerSplitAll G) W (eWt G c)
    (by convert card_edge_eulerSplitAll_le G hΔ) (eWt_le G c hc)
  rw [← eulTW_code G hc, kronNum_eul] at hr
  have hr' := Stepped.mapIn_runs hr
  rw [← length_edgeList G]
  have hm := M_le G
  set P := (n + 2) * (W + 2) with hPd
  have hP1 : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hn4 : (n + 2) ^ 4 ≤ P ^ 4 := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by omega)) _
  have hW4 : (W + 2) ^ 4 ≤ P ^ 4 := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (by omega)) _
  have hWP : W + 2 ≤ P := Nat.le_mul_of_pos_left _ (by omega)
  have hW1 : W + 1 ≤ (W + 2) ^ 4 := by
    have : W + 2 ≤ (W + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
    omega
  have hmP : M G ≤ P ^ 2 := by
    have h1 : n * n ≤ (n + 2) ^ 2 := by nlinarith
    have h2 : (n + 2) ^ 2 ≤ P ^ 2 := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by omega)) _
    omega
  obtain ⟨s1, s2, s3, s4, s5⟩ := small hm
  have s6 : n * (n * n) * (W + 1) ≤ P ^ 4 := by
    rw [hPd, mul_pow]; exact Nat.mul_le_mul (cube_le n) (hW1)
  have hNR : ((P : ℕ) : ℝ) = ((n : ℝ) + 2) * ((W : ℝ) + 2) := by rw [hPd]; push_cast; ring
  rw [exp_three] at hT
  have hT' : (T : ℝ) ≤ ((A₀ * (W + 2) ^ A₀ : ℕ) : ℝ) * (2 : ℝ) ^ (δ / 2 * (M G : ℝ)) := by
    push_cast; exact hT
  have key := hM (bB A₀) _ _ _ _ P ((2 : ℝ) ^ (δ * (M G : ℝ))) hP1
    (Real.one_le_rpow one_le_two (by positivity)) hr' ?_ (exp_part hδ ?_ hT')
  · rw [hNR, mul_pow] at key
    convert key using 2
    ring
  · apply absorbP hP1 hmP hWP
    rw [length_eulerCodeW G hc, show 3 * M G + W + 2 = 3 * M G + (W + 2) by ring]
    omega
  · have h1 : (W + 2) ^ A₀ ≤ P ^ A₀ := Nat.pow_le_pow_left hWP _
    have h2 : P ^ A₀ ≤ P ^ bB A₀ := Nat.pow_le_pow_right hP1 (by unfold bB; omega)
    have h3 : A₀ ≤ bB A₀ := by unfold bB; omega
    exact Nat.mul_le_mul h3 (h1.trans h2)

open Eul ESplit Dir EulS EulV in
/-- **Minimum-cost Eulerian circuits, with the decoding.** The machine of `theoremEulerW`, and, with
`m = M G = |E(G)|` (`ESplit.length_edgeList`): for every `j ≤ 3m·W`, digit `j` of the output (in base
`2^{bK(3m)}`) is `3m` times the number of Eulerian circuits of cost `j`; the minimum cost is the
position of the lowest non-zero digit; and the number of optimal circuits is that digit divided by
`3m`. -/
theorem theoremEulerW_decode (δ : ℝ) (hδ : 0 < δ) (Δ : ℕ) :
    ∃ (Mc : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (Mc.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ)
        (c : Fin n → Fin n → Fin n → ℕ), G.maxDegree ≤ Δ → (∀ x y z, c x y z ≤ W) →
        GraphProblems.Outputs Mc (eulerCodeW G W c) (Nat.bits (ekronNum G c))
          ⌊(C : ℝ) * ((n : ℝ) + 2) ^ C * (2 : ℝ) ^ (δ * (G.edgeFinset.card : ℝ)) *
            ((W : ℝ) + 2) ^ C⌋₊ ∧
        (∀ j ≤ 3 * M G * W, ekronDigit G c j = 3 * M G * etourCount G c j) ∧
        (0 < M G → ∀ k ≤ 3 * M G * W, IsMinECost G c k ↔
          ekronDigit G c k ≠ 0 ∧ ∀ j < k, ekronDigit G c j = 0) ∧
        (0 < M G → ∀ j ≤ 3 * M G * W, ekronDigit G c j / (3 * M G) = etourCount G c j) := by
  obtain ⟨Mc, C, hfin, hM⟩ := theoremEulerW δ hδ Δ
  refine ⟨Mc, C, hfin, fun n G _ W c hΔ hc => ⟨hM n G W c hΔ hc, fun j hj => ?_, fun hn k hk => ?_,
    fun hn j hj => ?_⟩⟩
  · rw [← kronDigit_eul, ← tourCount_eul]
    exact kronNum_digit (eulerSplitAll G) (eWt_le G c hc) hj
  · rw [← isMin_eul, ← kronDigit_eul]
    simp only [← kronDigit_eul]
    exact kronNum_min_iff (eulerSplitAll G) (by omega) (eWt_le G c hc) hk
  · rw [← kronDigit_eul, ← tourCount_eul]
    exact kronNum_digit_div (eulerSplitAll G) (by omega) (eWt_le G c hc) hj

end EthFollowup.ExactHC
