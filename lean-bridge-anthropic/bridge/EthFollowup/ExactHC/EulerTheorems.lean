/-
# Eulerian circuits at Turing-machine level, by edge splitting

The counting of Eulerian circuits is reduced to the verified exact counting of Hamiltonian cycles
by the edge splitting of `EulerSplit.lean`: a simple graph `G` with `m` edges becomes the graph
`eulerSplitAll G` on `Fin (3m)` (three copies per edge, the internal edges, and a clique on the
copies at every vertex: the line graph of the double subdivision), with
`#HC(eulerSplitAll G) = #(Eulerian circuits of G)` (`ESplit.card_hamCycles_eulerSplitAll`; Eulerian
circuits in Kotzig's description, `ESplit.eulerCircuitsAll`: transition systems with connected
transition graph) and `|E(eulerSplitAll G)| ≤ 2(Δ + 1)m`.

## The preprocessing
`eulW` maps `code G` (`n` in unary, the adjacency matrix row by row) to `code (eulerSplitAll G)`
(`eulW_code`): it lists the edges `(u, v)`, `u < v`, in lexicographic order (`edgeListW`), and writes
the adjacency matrix of the split graph from the arithmetic description `eAdjW` of its edges
(`ESplit.adj_eulerSplitAll_iff`). It is polynomial-time (`eulW_polyT`).

## Main results
* `theoremEuler`: for every `δ > 0` and `Δ`, one Turing machine of Mathlib writes the number of
  Eulerian circuits of every graph of maximum degree `≤ Δ` in binary within
  `⌊C·(n+2)^C·2^{δm}⌋` steps (`n` vertices, `m` edges; the factor `(n+2)^C` pays for reading the
  `n²`-bit input, which may consist mostly of isolated vertices);
* `theoremEuler_noIso`: the same within `⌊C·2^{δm}⌋` steps on graphs without isolated vertices;
* `theoremEuler_rate`: ONE machine and ONE `C` for all graphs, within
  `⌊C·(n+2)^C·2^{C·m·log₂(Δ+2)/√(log₂(m+2))}⌋` steps (`Δ` the maximum degree), from the machine of
  Theorem 3 (`T3.hcM3`, with the degree package `exists_dPackage`).

Standard axioms only.
-/
import EthFollowup.ExactHC.DirectedTheorems
import EthFollowup.ExactHC.DPackage
import EthFollowup.ExactHC.EulerSplit

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Groundwork Groundwork.Prog GraphProblems Asm Finset EthFollowup.Hamiltonian

namespace Eul

open ESplit

/-! ## The preprocessing: the code of the split graph -/

/-- The edges `(u, v)`, `u < v`, in lexicographic order, read from the adjacency matrix. -/
def edgeListW (a : GIn) : List (ℕ × ℕ) :=
  (List.range a.1.length).flatMap fun u =>
    ((List.range a.1.length).filter fun v => decide (u < v) && adjW a u v).map fun v => (u, v)

/-- The entry `(x, y)` of the adjacency matrix of the split graph. -/
def eAdjW (a : GIn) (x y : ℕ) : Bool :=
  (decide (x / 3 = y / 3) && (decide (x % 3 + y % 3 = 1) || decide (x % 3 + y % 3 = 3))) ||
    (!decide (x / 3 = y / 3) && !decide (x % 3 = 1) && !decide (y % 3 = 1) &&
      decide (ptN (edgeListW a) x = ptN (edgeListW a) y))

/-- The adjacency matrix of the split graph. -/
def eMatrix (a : GIn) : List Bool :=
  (List.range (3 * (edgeListW a).length)).flatMap fun x =>
    (List.range (3 * (edgeListW a).length)).map fun y => eAdjW a x y

/-- The code of the split graph, from the graph as read by `read1`. -/
def eSplitG (a : GIn) : List Bool := GraphProblems.unary (3 * (edgeListW a).length) ++ eMatrix a

/-- **The preprocessing of `theoremEuler`.** -/
def eulW (x : List Bool) : List Bool := eSplitG (read1 x)

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem edgeListW_aOf : edgeListW (aOf G) = edgesN G := by
  unfold edgeListW edgesN edgeList
  rw [aOf_len, ← List.map_coe_finRange_eq_range, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun u _ => ?_
  rw [List.filter_map, List.map_map, List.map_map]
  have hf : ∀ v ∈ List.finRange n,
      ((fun v : ℕ => decide (u.val < v) && adjW (aOf G) u.val v) ∘ Fin.val) v =
        decide (u < v ∧ G.Adj u v) := by
    intro v _
    simp only [Function.comp_apply]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, adjW_aOf G u.2 v.2, Fin.lt_def]
  rw [List.filter_congr hf]
  rfl

theorem length_edgeListW_aOf : (edgeListW (aOf G)).length = M G := by
  rw [edgeListW_aOf, edgesN, List.length_map]

theorem eAdjW_aOf (x y : Fin (3 * M G)) :
    eAdjW (aOf G) x.val y.val = true ↔ (eulerSplitAll G).Adj x y := by
  rw [adj_eulerSplitAll_iff, eAdjW, edgeListW_aOf, eArith]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, and_assoc, ne_eq]

/-- **The preprocessing maps the code of a graph to the code of its split graph.** -/
theorem eulW_code : eulW (code G) = code (eulerSplitAll G) := by
  rw [eulW, read1_code]
  simp only [eSplitG, code, length_edgeListW_aOf]
  congr 1
  unfold eMatrix GraphProblems.matrix
  rw [length_edgeListW_aOf, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  refine List.flatMap_congr fun x _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun y _ => ?_
  simp only [Function.comp_apply]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  exact eAdjW_aOf G x y

section Poly

variable {α : Type} [Enc α]

theorem edgeListW_polyT : PolyT edgeListW := by
  have h1 := range_polyT (α := GIn) (a := fun a => a) (by fun_prop)
  have h2 := range_polyT (α := GIn × ℕ) (a := fun p => p.1) (by fun_prop)
  unfold edgeListW; fun_prop

theorem ptN_polyT {E : α → List (ℕ × ℕ)} {x : α → ℕ} (hE : PolyT E) (hx : PolyT x) :
    PolyT fun t => ptN (E t) (x t) := by
  have d3 : PolyT fun _ : α => (3 : ℕ) := PolyT.const 3
  have hxd := PolyT.div hx d3
  have hxm := PolyT.mod hx d3
  have hg : PolyT fun t => (E t).getD (x t / 3) (0, 0) := PolyT.getD hE hxd (PolyT.const _)
  unfold ptN
  exact PolyT.ite' (PolyT.decide_eq hxm (PolyT.const 0)) (PolyT.fst hg) (PolyT.snd hg)

theorem eAdjW_polyT {a : α → GIn} {x y : α → ℕ} (ha : PolyT a) (hx : PolyT x) (hy : PolyT y) :
    PolyT fun t => eAdjW (a t) (x t) (y t) := by
  have d3 : PolyT fun _ : α => (3 : ℕ) := PolyT.const 3
  have hxd := PolyT.div hx d3
  have hyd := PolyT.div hy d3
  have hxm := PolyT.mod hx d3
  have hym := PolyT.mod hy d3
  have hs := PolyT.add hxm hym
  have hE : PolyT fun t => edgeListW (a t) := PolyT.comp edgeListW_polyT ha
  unfold eAdjW
  exact PolyT.or' (PolyT.and' (PolyT.decide_eq hxd hyd)
      (PolyT.or' (PolyT.decide_eq hs (PolyT.const 1)) (PolyT.decide_eq hs (PolyT.const 3))))
    (PolyT.and' (PolyT.and' (PolyT.and' (PolyT.not' (PolyT.decide_eq hxd hyd))
      (PolyT.not' (PolyT.decide_eq hxm (PolyT.const 1))))
      (PolyT.not' (PolyT.decide_eq hym (PolyT.const 1))))
      (PolyT.decide_eq (ptN_polyT hE hx) (ptN_polyT hE hy)))

theorem three_m_unary : Unary fun a : GIn => 3 * (edgeListW a).length :=
  (Unary.const 3).mul (Unary.of_length edgeListW_polyT)

theorem eSplitG_polyT : PolyT eSplitG := by
  have h1 : PolyT fun a : GIn => List.range (3 * (edgeListW a).length) := PolyT.range three_m_unary
  have h2 : PolyT fun p : GIn × ℕ => List.range (3 * (edgeListW p.1).length) :=
    PolyT.comp h1 (g := fun p : GIn × ℕ => p.1) (by fun_prop)
  have h3 : PolyT fun p : (GIn × ℕ) × ℕ => eAdjW p.1.1 p.1.2 p.2 :=
    eAdjW_polyT (by fun_prop) (by fun_prop) (by fun_prop)
  have h4 : PolyT fun a : GIn => GraphProblems.unary (3 * (edgeListW a).length) := by
    have h : PolyT fun a : GIn =>
        (List.replicate (3 * (edgeListW a).length) ()).map (fun _ => true) ++ [false] := by
      have := three_m_unary; fun_prop
    refine h.congr fun a => ?_
    simp [GraphProblems.unary, List.map_replicate]
  unfold eSplitG eMatrix; fun_prop

theorem eulW_polyT : PolyT eulW :=
  (PolyT.comp eSplitG_polyT stCertRead.1 : PolyT fun x => eSplitG (read1 x))

end Poly

/-- `|E(G')| ≤ (Δ + 1)·(3m)` when the maximum degree is `≤ Δ`. -/
theorem card_edge_eulerSplitAll_le [Fintype (eulerSplitAll G).edgeSet] {Δ : ℕ}
    (hΔ : G.maxDegree ≤ Δ) : (eulerSplitAll G).edgeFinset.card ≤ (Δ + 1) * (3 * M G) := by
  have h := card_edgeFinset_eulerSplit_le G (fun _ _ _ => true)
  have : 2 * (G.maxDegree + 1) * M G ≤ (Δ + 1) * (3 * M G) := by nlinarith
  exact h.trans this

end Eul

open Eul ESplit Dir in
/-- **Eulerian circuits: exact counting in time `2^{δm}` on graphs of bounded degree,
Turing-machine level, unconditional.** For every `δ > 0` and every `Δ` there are a Turing machine
of Mathlib with finite alphabets and a constant `C` such that, on the code of any graph `G` with `n`
vertices, `m` edges and maximum degree `≤ Δ`, the machine halts within `⌊C·(n+2)^C·2^{δm}⌋` steps
with the number of Eulerian circuits of `G` (`ESplit.eulerCircuitsAll`, Kotzig's description:
transition systems with connected transition graph) in binary. -/
theorem theoremEuler (δ : ℝ) (hδ : 0 < δ) (Δ : ℕ) :
    ∃ (Mc : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (Mc.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        GraphProblems.Outputs Mc (GraphProblems.code G) (Nat.bits (eulerCircuitsAll G).card)
          ⌊(C : ℝ) * ((n : ℝ) + 2) ^ C * (2 : ℝ) ^ (δ * (G.edgeFinset.card : ℝ))⌋₊ := by
  obtain ⟨Mh, ⟨inst⟩, A₀, hA₀⟩ := hc_stepped (δ / 3) (by positivity) (Δ + 1)
  have : IsPolyT (Stepped.mapIn eulW Mh) := IsPolyT.mapIn eulW_polyT
  obtain ⟨Mc, q, hfin, hM⟩ := CountKSat.exists_tmW (Stepped.mapIn eulW Mh)
  obtain ⟨K, hK⟩ : ∃ K, K = A₀ * 3 ^ A₀ + 1 := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = 2 * A₀ + 2 := ⟨_, rfl⟩
  refine ⟨Mc, q * (A₀ + 1) * K ^ q + e * q, hfin, fun n G _ hΔ => ?_⟩
  obtain ⟨T, hr, hT⟩ := hA₀ (eulerSplitAll G) (by convert card_edge_eulerSplitAll_le G hΔ)
  rw [← eulW_code, card_hamCycles_eulerSplitAll] at hr
  obtain ⟨ev⟩ := hM (GraphProblems.code G) T _ _ (Stepped.mapIn_runs hr)
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  rw [← length_edgeList G]
  set m := M G with hm
  set L := (GraphProblems.code G).length with hLd
  have hL : L = n + 1 + n * n := GraphProblems.length_code GraphProblems.stMatrixLength G
  have hMn : m ≤ n * n := M_le G
  have hLS : L + A₀ * (3 * m + 2) ^ A₀ + 1 ≤ K * (n + 2) ^ e := by
    have h1 : 3 * m + 2 ≤ 3 * (n + 2) ^ 2 := by nlinarith
    have h2 : (3 * m + 2) ^ A₀ ≤ 3 ^ A₀ * (n + 2) ^ (2 * A₀) := by
      calc (3 * m + 2) ^ A₀ ≤ (3 * (n + 2) ^ 2) ^ A₀ := Nat.pow_le_pow_left h1 _
        _ = 3 ^ A₀ * (n + 2) ^ (2 * A₀) := by rw [mul_pow, ← pow_mul]
    have h3 : (n + 2) ^ (2 * A₀) ≤ (n + 2) ^ e := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : (n + 2) ^ 2 ≤ (n + 2) ^ e := Nat.pow_le_pow_right (by omega) (by omega)
    have h5 : n + 1 + n * n + 1 ≤ (n + 2) ^ 2 := by nlinarith
    have h6 := Nat.mul_le_mul_left A₀ (h2.trans (Nat.mul_le_mul_left (3 ^ A₀) h3))
    calc L + A₀ * (3 * m + 2) ^ A₀ + 1 ≤ (n + 2) ^ e + A₀ * (3 ^ A₀ * (n + 2) ^ e) := by omega
      _ = K * (n + 2) ^ e := by rw [hK]; ring
  apply Nat.le_floor
  have hE : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * (m : ℝ)) := Real.one_le_rpow one_le_two (by positivity)
  rw [exp_three] at hT
  have h1 : (T : ℝ) + 1 ≤ ((A₀ : ℝ) + 1) * (2 : ℝ) ^ (δ / 2 * (m : ℝ)) := by nlinarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : ((L + A₀ * (3 * m + 2) ^ A₀ + 1 : ℕ) : ℝ) ^ q ≤ (K : ℝ) ^ q * ((n : ℝ) + 2) ^ (e * q) := by
    have h0 : ((L + A₀ * (3 * m + 2) ^ A₀ + 1 : ℕ) : ℝ) ≤ (K : ℝ) * ((n : ℝ) + 2) ^ e := by
      exact_mod_cast hLS
    calc ((L + A₀ * (3 * m + 2) ^ A₀ + 1 : ℕ) : ℝ) ^ q ≤ ((K : ℝ) * ((n : ℝ) + 2) ^ e) ^ q :=
          pow_le_pow_left₀ (by positivity) h0 q
      _ = (K : ℝ) ^ q * ((n : ℝ) + 2) ^ (e * q) := by rw [mul_pow, ← pow_mul]
  have h3 : ((n : ℝ) + 2) ^ (e * q) ≤ ((n : ℝ) + 2) ^ (q * (A₀ + 1) * K ^ q + e * q) :=
    pow_le_pow_right₀ hn1 (by omega)
  have h4 : (2 : ℝ) ^ (δ / 2 * (m : ℝ)) ≤ (2 : ℝ) ^ (δ * (m : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have h5 : ((q : ℝ) * ((A₀ : ℝ) + 1) * (K : ℝ) ^ q) ≤
      ((q * (A₀ + 1) * K ^ q + e * q : ℕ) : ℝ) := by
    have : q * (A₀ + 1) * K ^ q ≤ q * (A₀ + 1) * K ^ q + e * q := by omega
    exact_mod_cast this
  calc ((q * (T + 1) * (L + A₀ * (3 * m + 2) ^ A₀ + 1) ^ q : ℕ) : ℝ)
      = (q : ℝ) * ((T : ℝ) + 1) * ((L + A₀ * (3 * m + 2) ^ A₀ + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (((A₀ : ℝ) + 1) * (2 : ℝ) ^ (δ / 2 * (m : ℝ))) *
          ((K : ℝ) ^ q * ((n : ℝ) + 2) ^ (e * q)) := by gcongr
    _ = ((q : ℝ) * ((A₀ : ℝ) + 1) * (K : ℝ) ^ q) * ((n : ℝ) + 2) ^ (e * q) *
          (2 : ℝ) ^ (δ / 2 * (m : ℝ)) := by ring
    _ ≤ ((q * (A₀ + 1) * K ^ q + e * q : ℕ) : ℝ) *
          ((n : ℝ) + 2) ^ (q * (A₀ + 1) * K ^ q + e * q) * (2 : ℝ) ^ (δ * (m : ℝ)) := by
        gcongr

open Eul ESplit in
/-- **Eulerian circuits in time `2^{δm}` on graphs of bounded degree without isolated vertices.**
For every `δ > 0` and `Δ`: one Turing machine and one `C` such that on the code of every graph with
`m` edges, maximum degree `≤ Δ` and no isolated vertex, the machine halts within `⌊C·2^{δm}⌋`
steps with the number of Eulerian circuits in binary. -/
theorem theoremEuler_noIso (δ : ℝ) (hδ : 0 < δ) (Δ : ℕ) :
    ∃ (Mc : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (Mc.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (∀ v, 0 < G.degree v) →
        GraphProblems.Outputs Mc (GraphProblems.code G) (Nat.bits (eulerCircuitsAll G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * (G.edgeFinset.card : ℝ))⌋₊ := by
  obtain ⟨Mc, C, hfin, hM⟩ := theoremEuler (δ / 2) (by positivity) Δ
  obtain ⟨Cp, hCp⟩ := exists_pow_le C (show (0 : ℝ) < δ / 4 by positivity)
  refine ⟨Mc, C * Cp, hfin, fun n G _ hΔ hdeg => ?_⟩
  obtain ⟨ev⟩ := hM n G hΔ
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (Nat.floor_le_floor ?_)⟩⟩
  have hn : n ≤ 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    calc n = ∑ _v : Fin n, 1 := by simp
      _ ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => hdeg v
  have hnR : (n : ℝ) ≤ 2 * (G.edgeFinset.card : ℝ) := by exact_mod_cast hn
  have h1 := hCp n
  have h2 : (2 : ℝ) ^ (δ / 4 * (n : ℝ)) ≤ (2 : ℝ) ^ (δ / 2 * (G.edgeFinset.card : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by nlinarith)
  have h3 : (2 : ℝ) ^ (δ * (G.edgeFinset.card : ℝ)) =
      (2 : ℝ) ^ (δ / 2 * (G.edgeFinset.card : ℝ)) * (2 : ℝ) ^ (δ / 2 * (G.edgeFinset.card : ℝ)) := by
    rw [← Real.rpow_add two_pos]; congr 1; ring
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * (G.edgeFinset.card : ℝ)) := by positivity
  calc (C : ℝ) * ((n : ℝ) + 2) ^ C * (2 : ℝ) ^ (δ / 2 * (G.edgeFinset.card : ℝ))
      ≤ (C : ℝ) * ((Cp : ℝ) * (2 : ℝ) ^ (δ / 2 * (G.edgeFinset.card : ℝ))) *
          (2 : ℝ) ^ (δ / 2 * (G.edgeFinset.card : ℝ)) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
    _ = ((C * Cp : ℕ) : ℝ) * (2 : ℝ) ^ (δ * (G.edgeFinset.card : ℝ)) := by
        rw [h3]; push_cast; ring

open Eul ESplit T3 T2 Asm EthFollowup.Hamiltonian in
/-- **Eulerian circuits, one machine for all graphs, Turing-machine level, unconditional.** ONE
Turing machine of Mathlib with finite alphabets and ONE constant `C` such that, on the code of every
graph `G` with `n` vertices, `m` edges and maximum degree `Δ`, the machine halts within
`⌊C·(n+2)^C·2^{C·m·log₂(Δ+2)/√(log₂(m+2))}⌋` steps with the number of Eulerian circuits of `G`
(`ESplit.eulerCircuitsAll`) in binary. (The machine of Theorem 3, `T3.hcM3`, after the
preprocessing `eulW`; the split graph has `3m` vertices and at most `2(Δ+1)m` edges.) -/
theorem theoremEuler_rate :
    ∃ (Mc : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (Mc.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        GraphProblems.Outputs Mc (GraphProblems.code G) (Nat.bits (eulerCircuitsAll G).card)
          ⌊(C : ℝ) * ((n : ℝ) + 2) ^ C * (2 : ℝ) ^ ((C : ℝ) * (G.edgeFinset.card : ℝ) *
            Real.logb 2 ((G.maxDegree : ℝ) + 2) /
              Real.sqrt (Real.logb 2 ((G.edgeFinset.card : ℝ) + 2)))⌋₊ := by
  obtain ⟨c₀, ⟨pk⟩⟩ := exists_dPackage
  obtain ⟨c, x₀, C₀, D, Alg, -, -, -, -, -, he, hyp, -⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨C₁, hC₁⟩ := T2.geBody
  have hL := hyp.levels
  have hk := hyp.computesK
  obtain ⟨A, hA⟩ := hcM3_runs pk hC₁ hL hk _ hyp.solves (x₀ := x₀) fun l => he l
  obtain ⟨inst⟩ := hcM3_poly pk _ _ hL hk hyp.steps
  have : IsPolyT (Stepped.mapIn eulW (hcM3 pk (ExplicitCost.cliqueMachine (c + 2) x₀ Alg)
      (CliqueLevels.levelsUnder x₀) (Levels.Gen.K x₀ 0))) := IsPolyT.mapIn eulW_polyT
  obtain ⟨Mc, q, hfin, hM⟩ := CountKSat.exists_tmW (Stepped.mapIn eulW
    (hcM3 pk (ExplicitCost.cliqueMachine (c + 2) x₀ Alg) (CliqueLevels.levelsUnder x₀)
      (Levels.Gen.K x₀ 0)))
  obtain ⟨Af, hAf⟩ : ∃ Af, Af = q + (A + 1) + q * (A + 1) := ⟨_, rfl⟩
  refine ⟨Mc, 2 ^ (2 * Af) + 12 * Af + 2 * q, hfin, fun n G _ => ?_⟩
  obtain ⟨T, S, hrun, hT, hS⟩ := hA (eulerSplitAll G)
  rw [← eulW_code, card_hamCycles_eulerSplitAll] at hrun
  obtain ⟨ev⟩ := hM (GraphProblems.code G) T S _ (Stepped.mapIn_runs hrun)
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  have hmA : (@SimpleGraph.edgeFinset _ (eulerSplitAll G) (eulerSplitAll G).fintypeEdgeSet).card ≤
      2 * (G.maxDegree + 1) * M G := by convert card_edgeFinset_eulerSplit_le G (fun _ _ _ => true)
  generalize (@SimpleGraph.edgeFinset _ (eulerSplitAll G) (eulerSplitAll G).fintypeEdgeSet).card = m'
    at hT hS hmA
  rw [← length_edgeList G, show Real.sqrt (Real.logb 2 (((edgeList G).length : ℝ) + 2)) =
    T2.sq (M G) from rfl]
  set m := M G with hm
  set Δ := G.maxDegree with hΔd
  set Cc := 2 ^ (2 * Af) + 12 * Af + 2 * q with hCc
  set L := (GraphProblems.code G).length with hLd
  have hL : L = n + 1 + n * n := GraphProblems.length_code GraphProblems.stMatrixLength G
  -- the exponent
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hlogΔ : 1 ≤ Real.logb 2 ((Δ : ℝ) + 2) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity), Real.rpow_one]
    linarith [(Nat.cast_nonneg Δ : (0 : ℝ) ≤ Δ)]
  have hmR : (m' : ℝ) ≤ 2 * ((Δ : ℝ) + 1) * (m : ℝ) := by exact_mod_cast hmA
  have hratio : 2 * (m' : ℝ) / ((3 * m : ℕ) : ℝ) + 2 ≤ 2 * ((Δ : ℝ) + 2) := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0]; simp only [mul_zero, Nat.cast_zero, div_zero, zero_add]
      linarith [(Nat.cast_nonneg Δ : (0 : ℝ) ≤ Δ)]
    · have hp : (0 : ℝ) < ((3 * m : ℕ) : ℝ) := by positivity
      have : 2 * (m' : ℝ) / ((3 * m : ℕ) : ℝ) ≤ 2 * (Δ : ℝ) + 2 := by
        rw [div_le_iff₀ hp]; push_cast
        have : (0 : ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _
        nlinarith
      linarith
  have hlog : Real.logb 2 (2 * (m' : ℝ) / ((3 * m : ℕ) : ℝ) + 2) ≤
      2 * Real.logb 2 ((Δ : ℝ) + 2) := by
    have h1 := Real.logb_le_logb_of_le one_lt_two (by positivity) hratio
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one one_lt_two] at h1
    linarith
  have hMd := Md_add_le (3 * m) m'
  have hsq : T2.sq m ≤ T2.sq (3 * m) := by
    unfold T2.sq T2.Lam
    apply Real.sqrt_le_sqrt
    apply Real.logb_le_logb_of_le one_lt_two (by positivity)
    push_cast; linarith
  have hs0 := T2.sq_pos m
  have hexp : (Af : ℝ) * (((Md (3 * m) m' : ℕ) : ℝ) + ((3 * m : ℕ) : ℝ)) / T2.sq (3 * m) ≤
      (Cc : ℝ) * (m : ℝ) * Real.logb 2 ((Δ : ℝ) + 2) / T2.sq m := by
    have hnum : 0 ≤ (Af : ℝ) * (((Md (3 * m) m' : ℕ) : ℝ) + ((3 * m : ℕ) : ℝ)) := by positivity
    have h1 : ((Md (3 * m) m' : ℕ) : ℝ) + ((3 * m : ℕ) : ℝ) ≤
        12 * (m : ℝ) * Real.logb 2 ((Δ : ℝ) + 2) := by
      calc ((Md (3 * m) m' : ℕ) : ℝ) + ((3 * m : ℕ) : ℝ)
          ≤ 2 * ((3 * m : ℕ) : ℝ) * Real.logb 2 (2 * (m' : ℝ) / ((3 * m : ℕ) : ℝ) + 2) := hMd
        _ ≤ 2 * ((3 * m : ℕ) : ℝ) * (2 * Real.logb 2 ((Δ : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = 12 * (m : ℝ) * Real.logb 2 ((Δ : ℝ) + 2) := by push_cast; ring
    have hC : (12 * (Af : ℝ)) ≤ (Cc : ℝ) := by
      have : 12 * Af ≤ Cc := by
        rw [hCc]; exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
      exact_mod_cast this
    have hml : 0 ≤ (m : ℝ) * Real.logb 2 ((Δ : ℝ) + 2) := mul_nonneg hm0 (by linarith)
    calc (Af : ℝ) * (((Md (3 * m) m' : ℕ) : ℝ) + ((3 * m : ℕ) : ℝ)) / T2.sq (3 * m)
        ≤ (Af : ℝ) * (((Md (3 * m) m' : ℕ) : ℝ) + ((3 * m : ℕ) : ℝ)) / T2.sq m :=
          div_le_div_of_nonneg_left hnum hs0 hsq
      _ ≤ (Cc : ℝ) * (m : ℝ) * Real.logb 2 ((Δ : ℝ) + 2) / T2.sq m := by
          apply div_le_div_of_nonneg_right _ hs0.le
          calc (Af : ℝ) * (((Md (3 * m) m' : ℕ) : ℝ) + ((3 * m : ℕ) : ℝ))
              ≤ (Af : ℝ) * (12 * (m : ℝ) * Real.logb 2 ((Δ : ℝ) + 2)) :=
                mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
            _ = (12 * (Af : ℝ)) * ((m : ℝ) * Real.logb 2 ((Δ : ℝ) + 2)) := by ring
            _ ≤ (Cc : ℝ) * ((m : ℝ) * Real.logb 2 ((Δ : ℝ) + 2)) :=
                mul_le_mul_of_nonneg_right hC hml
            _ = (Cc : ℝ) * (m : ℝ) * Real.logb 2 ((Δ : ℝ) + 2) := by ring
  -- the running time
  apply Nat.le_floor
  have hT1 := add_one_le_Xp hT
  have hS1 := add_one_le_Xp hS
  have h3 := pow_le_Xp (by positivity) hS1 q
  have h4 : (q : ℝ) * ((T : ℝ) + 1) ≤ (2 : ℝ) ^ Xp (q + (A + 1)) (3 * m) (Md (3 * m) m') :=
    mul_le_Xp (Nat.cast_nonneg _) (const_le_Xp q _ _) hT1
  have h5 := mul_le_Xp (by positivity) h4 h3
  rw [show q + (A + 1) + q * (A + 1) = Af from hAf.symm] at h5
  have h6 := Xp_split Af (3 * m) (Md (3 * m) m')
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hL1 : (L : ℝ) + 1 ≤ ((n : ℝ) + 2) ^ 2 := by
    have : L + 1 ≤ (n + 2) ^ 2 := by rw [hL]; nlinarith
    exact_mod_cast this
  have hLS : ((L + S + 1 : ℕ) : ℝ) ≤ ((L : ℝ) + 1) * ((S : ℝ) + 1) := by
    push_cast
    have : (0 : ℝ) ≤ (L : ℝ) * (S : ℝ) := by positivity
    nlinarith
  have h7 : ((L + S + 1 : ℕ) : ℝ) ^ q ≤ ((n : ℝ) + 2) ^ (2 * q) * ((S : ℝ) + 1) ^ q := by
    calc ((L + S + 1 : ℕ) : ℝ) ^ q ≤ (((L : ℝ) + 1) * ((S : ℝ) + 1)) ^ q :=
          pow_le_pow_left₀ (by positivity) hLS q
      _ = ((L : ℝ) + 1) ^ q * ((S : ℝ) + 1) ^ q := mul_pow _ _ _
      _ ≤ (((n : ℝ) + 2) ^ 2) ^ q * ((S : ℝ) + 1) ^ q := by gcongr
      _ = ((n : ℝ) + 2) ^ (2 * q) * ((S : ℝ) + 1) ^ q := by rw [← pow_mul]
  have e2 : (2 : ℝ) ^ (2 * (Af : ℝ)) = ((2 ^ (2 * Af) : ℕ) : ℝ) := by
    rw [show (2 : ℝ) * (Af : ℝ) = ((2 * Af : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    push_cast; ring
  have hC2 : ((2 ^ (2 * Af) : ℕ) : ℝ) ≤ (Cc : ℝ) := by
    have : 2 ^ (2 * Af) ≤ Cc := by
      rw [hCc]; exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    exact_mod_cast this
  have hnC : ((n : ℝ) + 2) ^ (2 * q) ≤ ((n : ℝ) + 2) ^ Cc :=
    pow_le_pow_right₀ hn1 (by rw [hCc]; exact Nat.le_add_left _ _)
  have h8 : (2 : ℝ) ^ ((Af : ℝ) * (((Md (3 * m) m' : ℕ) : ℝ) + ((3 * m : ℕ) : ℝ)) / T2.sq (3 * m)) ≤
      (2 : ℝ) ^ ((Cc : ℝ) * (m : ℝ) * Real.logb 2 ((Δ : ℝ) + 2) / T2.sq m) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two hexp
  calc ((q * (T + 1) * (L + S + 1) ^ q : ℕ) : ℝ)
      = ((q : ℝ) * ((T : ℝ) + 1)) * ((L + S + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
    _ ≤ ((q : ℝ) * ((T : ℝ) + 1)) * (((n : ℝ) + 2) ^ (2 * q) * ((S : ℝ) + 1) ^ q) := by gcongr
    _ = ((n : ℝ) + 2) ^ (2 * q) * ((q : ℝ) * ((T : ℝ) + 1) * ((S : ℝ) + 1) ^ q) := by ring
    _ ≤ ((n : ℝ) + 2) ^ Cc * ((2 : ℝ) ^ (2 * (Af : ℝ)) *
          (2 : ℝ) ^ ((Af : ℝ) * (((Md (3 * m) m' : ℕ) : ℝ) + ((3 * m : ℕ) : ℝ)) / T2.sq (3 * m))) :=
        mul_le_mul hnC (h5.trans h6) (by positivity) (by positivity)
    _ ≤ ((n : ℝ) + 2) ^ Cc * ((Cc : ℝ) *
          (2 : ℝ) ^ ((Cc : ℝ) * (m : ℝ) * Real.logb 2 ((Δ : ℝ) + 2) / T2.sq m)) := by
        rw [e2]
        gcongr
    _ = (Cc : ℝ) * ((n : ℝ) + 2) ^ Cc *
          (2 : ℝ) ^ ((Cc : ℝ) * (m : ℝ) * Real.logb 2 ((Δ : ℝ) + 2) / T2.sq m) := by ring

end EthFollowup.ExactHC
