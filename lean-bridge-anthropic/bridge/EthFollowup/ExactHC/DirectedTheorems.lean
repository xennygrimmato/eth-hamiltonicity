/-
# Directed Hamiltonian cycles and ATSP at Turing-machine level, by vertex splitting

Instead of a directed machine stack, the directed problems are reduced to the verified undirected
ones (`theorem1`, `theoremTSP`) by the vertex splitting of `VertexSplit.lean`: a digraph
`A : Finset (Fin n × Fin n)` becomes the graph `split A` on `Fin (3n)` (copies `v_in, v_mid, v_out`,
internal edges `v_in v_mid`, `v_mid v_out`, an edge `u_out v_in` per arc), with
`#HC(split A) = #DHC(A)`, `|E(split A)| ≤ |A| + 2n`, and the arc weights carried to the edges
`u_out v_in` (`tourCount (split A) (splitWt w) j = dtourCount A w j`).

## The input words
* `dcode A`: `n` in unary, then the `n²` entries `(u, v) ∈ A` of the adjacency matrix, row by row
  (the word `GraphProblems.code` of a graph, for a digraph; loops allowed).
* `dtspCode A W w`: `dcode A`, then `W` in unary, then the `n²` arc weights `w (u, v)` in row-major
  order as blocks of `W + 1` bits (the word `tspCode` of `WeightedPackage.lean`, for a digraph).

## The machines
A polynomial-time preprocessing step (`splitW`, resp. `splitTW`) maps `dcode A` to
`code (split A)` (`splitW_dcode`), resp. `dtspCode A W w` to `tspCode (split A) W (splitWt w)`
(`splitTW_dtspCode`); it is composed (`Stepped.mapIn`, no extra step) with the `Stepped` machines
of Theorem 1 (`Asm.hcM`) and of TSP (`TSPAsm.tspM`), whose run lemmas are recalled with the
parameters of `theorem1_TM` / `theoremTSP_of_package` (`hc_stepped`, `tsp_stepped`); the result is
turned into a Turing machine of Mathlib by `GraphProblems.tm_of_stepped` / `CountKSat.stHostW`.
Since `split A` has `3n` vertices, Theorem 1 is used with `δ/3` and `D + 2`.

## Main results
* `theoremDHC`: for every `δ > 0` and `D`, one machine writes `#DHC(A)` in binary within
  `⌊C·2^{δn}⌋` steps on every digraph with at most `D·n` arcs.
* `theoremDHC_rate`: one machine and one `C` for all digraphs, time
  `⌊C·2^{C(m+n)/√(log₂(n+2))}⌋` (`m` = number of arcs), from the machine of Theorem 2 (`T2.hcM2`).
* `theoremATSP`: the directed Kronecker integer
  `dkronNum A w = 3n · Σ_{H ∈ DHC(A)} 2^{bK(3n)·w(H)}` within `⌊C·2^{δn}·(W+2)^C⌋` steps, arc weights
  `≤ W`; `theoremATSP_decode`: digit `j` (base `2^{bK(3n)}`) is `3n` times the number of directed
  tours of weight `j`, the minimum tour weight is the position of the lowest non-zero digit, and the
  number of tours of weight `j` (in particular of optimal tours) is that digit divided by `3n`.

Standard axioms only.
-/
import EthFollowup.ExactHC.Package
import EthFollowup.ExactHC.TSP
import EthFollowup.ExactHC.UPackage
import EthFollowup.ExactHC.VertexSplit

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Groundwork Groundwork.Prog GraphProblems Asm Finset EthFollowup.Hamiltonian VSplit

namespace Dir

/-! ## The stepped machines of Theorem 1 and of TSP -/

/-- **Theorem 1 at the level of `Stepped` machines** (the machine `Asm.hcM` with the parameters of
`theorem1_TM`, from `exists_labelPackage`): polynomial-time steps, `#HC(G)` within `A·2^{(δ/2)n}`
steps on states of size `≤ A(n+2)^A`, on every graph with `≤ Dn` edges. -/
theorem hc_stepped (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ M : Stepped (List Bool) (List Bool), Nonempty (IsPolyT M) ∧ ∃ A : ℕ,
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.card ≤ D * n →
        ∃ T : ℕ, M.Runs (code G) T (A * (n + 2) ^ A) (Nat.bits (hamCycles G).card) ∧
          (T : ℝ) ≤ A * (2 : ℝ) ^ (δ / 2 * n) := by
  obtain ⟨c₀, hpk'⟩ := exists_labelPackage
  have hpk : ∀ g : ℕ, 1 ≤ g → Nonempty (HCPackage g c₀) := fun g hg =>
    (hpk' g hg).map LabelPackage.toHCPackage
  set η : ℝ := min 1 (δ / (8 * (c₀ + 1) * (D + 1))) with hηd
  have hη : 0 < η := lt_min one_pos (by positivity)
  obtain ⟨K, hK0, hach⟩ := Given.stEveryEta η hη (⌈32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ⌉₊ + 2)
  obtain ⟨NM, C₁, hpoly, hNM⟩ := Printed.groupingLemma K η hach
  have hK1 : 1 ≤ K := by omega
  have hKg : K ≤ 3 * K ^ 8 := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 8 := Nat.pow_le_pow_right hK1 (by norm_num)
      _ ≤ 3 * K ^ 8 := Nat.le_mul_of_pos_left _ (by norm_num)
  obtain ⟨pk⟩ := hpk (3 * K ^ 8) (hK1.trans hKg)
  have he : η * c₀ * (D + 1) ≤ δ / 8 := by
    have h1 : η ≤ δ / (8 * (c₀ + 1) * (D + 1)) := min_le_right _ _
    have h2 : η * c₀ * (D + 1) ≤ η * (c₀ + 1) * (D + 1) := by gcongr; linarith
    have h3 : η * (c₀ + 1) * (D + 1) ≤ δ / (8 * (c₀ + 1) * (D + 1)) * (c₀ + 1) * (D + 1) := by
      gcongr
    have h4 : δ / (8 * (c₀ + 1) * (D + 1)) * (c₀ + 1) * (D + 1) = δ / 8 := by
      field_simp
    linarith
  have hKδ : 4 * (c₀ : ℝ) * (2 * D + 1) ≤ δ / 8 * K := by
    have h1 : 32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ ≤ K := by
      have := Nat.le_ceil (32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ)
      have h2 : ((⌈32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ⌉₊ : ℕ) : ℝ) ≤ K := by
        exact_mod_cast (by omega : ⌈32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ⌉₊ ≤ K)
      linarith
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  obtain ⟨A, hA⟩ := hcM_runs pk hNM hη.le (min_le_left _ _) hK1 hKg hδ he hKδ
  exact ⟨hcM (3 * K ^ 8) NM pk, hcM_poly NM pk hpoly, A, hA⟩

open TSPAsm in
/-- **TSP at the level of `Stepped` machines** (the machine `TSPAsm.tspM` with the parameters of
`theoremTSP_of_package`, from `exists_tspPackage`). -/
theorem tsp_stepped (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ M : Stepped (List Bool) (List Bool), Nonempty (IsPolyT M) ∧ ∃ A : ℕ,
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (W : ℕ) (w : Sym2 (Fin n) → ℕ),
        G.edgeFinset.card ≤ D * n → (∀ e, w e ≤ W) →
        ∃ T : ℕ, M.Runs (tspCode G W w) T (A * (n + W + 2) ^ A) (Nat.bits (kronNum G w)) ∧
          (T : ℝ) ≤ A * ((W : ℝ) + 2) ^ A * (2 : ℝ) ^ (δ / 2 * n) := by
  obtain ⟨c₀, hpk⟩ := exists_tspPackage
  set η : ℝ := min 1 (δ / (8 * (c₀ + 1) * (D + 1))) with hηd
  have hη : 0 < η := lt_min one_pos (by positivity)
  obtain ⟨K, hK0, hach⟩ := Given.stEveryEta η hη (⌈32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ⌉₊ + 2)
  obtain ⟨NM, C₁, hpoly, hNM⟩ := Printed.groupingLemma K η hach
  have hK1 : 1 ≤ K := by omega
  have hKg : K ≤ 3 * K ^ 8 := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 8 := Nat.pow_le_pow_right hK1 (by norm_num)
      _ ≤ 3 * K ^ 8 := Nat.le_mul_of_pos_left _ (by norm_num)
  obtain ⟨pk⟩ := hpk (3 * K ^ 8) (hK1.trans hKg)
  have he : η * c₀ * (D + 1) ≤ δ / 8 := by
    have h1 : η ≤ δ / (8 * (c₀ + 1) * (D + 1)) := min_le_right _ _
    have h2 : η * c₀ * (D + 1) ≤ η * (c₀ + 1) * (D + 1) := by gcongr; linarith
    have h3 : η * (c₀ + 1) * (D + 1) ≤ δ / (8 * (c₀ + 1) * (D + 1)) * (c₀ + 1) * (D + 1) := by
      gcongr
    have h4 : δ / (8 * (c₀ + 1) * (D + 1)) * (c₀ + 1) * (D + 1) = δ / 8 := by
      field_simp
    linarith
  have hKδ : 4 * (c₀ : ℝ) * (2 * D + 1) ≤ δ / 8 * K := by
    have h1 : 32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ ≤ K := by
      have := Nat.le_ceil (32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ)
      have h2 : ((⌈32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ⌉₊ : ℕ) : ℝ) ≤ K := by
        exact_mod_cast (by omega : ⌈32 * ((c₀ : ℝ) + 1) * (2 * D + 1) / δ⌉₊ ≤ K)
      linarith
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  obtain ⟨A, hA⟩ := tspM_runs pk hNM hη.le (min_le_left _ _) hK1 hKg hδ he hKδ
  exact ⟨tspM (3 * K ^ 8) NM pk, tspM_poly NM pk hpoly, A, hA⟩

/-! ## The input word of a digraph -/

variable {n : ℕ}

/-- The `n²` entries of the adjacency matrix of a digraph, row by row. -/
def dmatrix (A : Finset (Fin n × Fin n)) : List Bool :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => decide ((u, v) ∈ A)

/-- **A digraph as a word**: `n` in unary, then the adjacency matrix. -/
def dcode (A : Finset (Fin n × Fin n)) : List Bool := GraphProblems.unary n ++ dmatrix A

theorem length_dmatrix (A : Finset (Fin n × Fin n)) : (dmatrix A).length = n * n := by
  simp [dmatrix, List.length_flatMap]

theorem length_dcode (A : Finset (Fin n × Fin n)) : (dcode A).length = n + 1 + n * n := by
  simp only [dcode, List.length_append, length_dmatrix, GraphProblems.unary, List.length_replicate,
    List.length_cons, List.length_nil]

/-- The word `dcode A` as read by `read1`. -/
def daOf (A : Finset (Fin n × Fin n)) : GIn := (List.replicate n (), dmatrix A)

theorem read1_dcode (A : Finset (Fin n × Fin n)) : read1 (dcode A) = daOf A := by
  rw [read1, dcode, Read.ones_unary_append, Read.rest_unary_append]; rfl

@[simp] theorem daOf_len (A : Finset (Fin n × Fin n)) : (daOf A).1.length = n := by simp [daOf]

theorem adjW_daOf (A : Finset (Fin n × Fin n)) (u v : Fin n) :
    adjW (daOf A) u.val v.val = true ↔ (u, v) ∈ A := by
  rw [adjW, daOf_len, daOf, adjB, dmatrix, Read.getD_flatMap _ n false v.2 _ (by simp)]
  simp

/-! ## The preprocessing: the code of the split graph -/

/-- The entry `(x, y)` of the adjacency matrix of the split graph, computed from the digraph. -/
def sAdjW (a : GIn) (x y : ℕ) : Bool :=
  (decide (x / 3 = y / 3) && (decide (x % 3 + y % 3 = 1) || decide (x % 3 + y % 3 = 3))) ||
    (decide (x % 3 = 2) && decide (y % 3 = 0) && adjW a (x / 3) (y / 3)) ||
    (decide (x % 3 = 0) && decide (y % 3 = 2) && adjW a (y / 3) (x / 3))

/-- The adjacency matrix of the split graph. -/
def sMatrix (a : GIn) : List Bool :=
  (List.range (3 * a.1.length)).flatMap fun x => (List.range (3 * a.1.length)).map fun y => sAdjW a x y

/-- The code of the split graph, from the digraph as read by `read1`. -/
def splitG (a : GIn) : List Bool := GraphProblems.unary (3 * a.1.length) ++ sMatrix a

/-- **The preprocessing of `theoremDHC`.** -/
def splitW (x : List Bool) : List Bool := splitG (read1 x)

theorem sAdjW_daOf (A : Finset (Fin n × Fin n)) (x y : Fin (3 * n)) :
    sAdjW (daOf A) x.val y.val = true ↔ (split A).Adj x y := by
  have h1 := adjW_daOf A (orig x) (orig y)
  have h2 := adjW_daOf A (orig y) (orig x)
  simp only [orig] at h1 h2
  rw [graphOf_adj]
  have hd : s(x, y) ∈ phi A → x ≠ y := by
    rintro h rfl
    exact not_mem_phi_diag A x h
  rw [show (s(x, y) ∈ phi A ∧ x ≠ y) ↔ s(x, y) ∈ phi A from ⟨fun h => h.1, fun h => ⟨h, hd h⟩⟩,
    mem_phi_iff_arith]
  simp only [sAdjW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, h1, h2, orig, and_assoc,
    or_assoc]

/-- **The preprocessing maps the word of a digraph to the word of its split graph.** -/
theorem splitW_dcode (A : Finset (Fin n × Fin n)) : splitW (dcode A) = code (split A) := by
  rw [splitW, read1_dcode]
  simp only [splitG, code, daOf_len]
  congr 1
  unfold sMatrix GraphProblems.matrix
  simp only [daOf_len]
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  refine List.flatMap_congr fun x _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun y _ => ?_
  simp only [Function.comp_apply]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  exact sAdjW_daOf A x y

section Poly

variable {α : Type} [Enc α]

theorem sAdjW_polyT {a : α → GIn} {x y : α → ℕ} (ha : PolyT a) (hx : PolyT x) (hy : PolyT y) :
    PolyT fun t => sAdjW (a t) (x t) (y t) := by
  have d3 : PolyT fun _ : α => (3 : ℕ) := PolyT.const 3
  have hxd := PolyT.div hx d3
  have hyd := PolyT.div hy d3
  have hxm := PolyT.mod hx d3
  have hym := PolyT.mod hy d3
  have hs := PolyT.add hxm hym
  unfold sAdjW
  exact PolyT.or' (PolyT.or' (PolyT.and' (PolyT.decide_eq hxd hyd)
      (PolyT.or' (PolyT.decide_eq hs (PolyT.const 1)) (PolyT.decide_eq hs (PolyT.const 3))))
    (PolyT.and' (PolyT.and' (PolyT.decide_eq hxm (PolyT.const 2)) (PolyT.decide_eq hym (PolyT.const 0)))
      (adjW_polyT ha hxd hyd)))
    (PolyT.and' (PolyT.and' (PolyT.decide_eq hxm (PolyT.const 0)) (PolyT.decide_eq hym (PolyT.const 2)))
      (adjW_polyT ha hyd hxd))

theorem three_len_unary : Unary fun a : GIn => 3 * a.1.length :=
  (Unary.const 3).mul (Unary.of_length (by fun_prop))

theorem unary3_polyT : PolyT fun a : GIn => GraphProblems.unary (3 * a.1.length) := by
  have h : PolyT fun a : GIn => (List.replicate (3 * a.1.length) ()).map (fun _ => true) ++ [false] := by
    have := three_len_unary; fun_prop
  refine h.congr fun a => ?_
  simp [GraphProblems.unary, List.map_replicate]

theorem splitG_polyT : PolyT splitG := by
  have h1 : PolyT fun a : GIn => List.range (3 * a.1.length) := PolyT.range three_len_unary
  have h2 : PolyT fun p : GIn × ℕ => List.range (3 * p.1.1.length) :=
    PolyT.comp h1 (g := fun p : GIn × ℕ => p.1) (by fun_prop)
  have h3 : PolyT fun p : (GIn × ℕ) × ℕ => sAdjW p.1.1 p.1.2 p.2 :=
    sAdjW_polyT (by fun_prop) (by fun_prop) (by fun_prop)
  have h4 := unary3_polyT
  unfold splitG sMatrix; fun_prop

theorem splitW_polyT : PolyT splitW :=
  (PolyT.comp splitG_polyT stCertRead.1 : PolyT fun x => splitG (read1 x))

end Poly

/-! ## Theorem DHC -/

/-- `|E(split A)| ≤ (D + 2)·(3n)` when `|A| ≤ Dn`. -/
theorem card_edge_split_le {A : Finset (Fin n × Fin n)} [Fintype (split A).edgeSet] {D : ℕ}
    (hA : A.card ≤ D * n) :
    (split A).edgeFinset.card ≤ (D + 2) * (3 * n) := by
  have h := card_edgeFinset_split_le A
  have : (D + 2) * n ≤ (D + 2) * (3 * n) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- `A (3n + k + 2)^A ≤ c (n + k + 2)^c` for `c = A·3^A + A`. -/
theorem pow_three_le (A n k : ℕ) :
    A * (3 * n + k + 2) ^ A ≤ (A * 3 ^ A + A) * (n + k + 2) ^ (A * 3 ^ A + A) := by
  have h1 : (3 * n + k + 2) ^ A ≤ 3 ^ A * (n + k + 2) ^ A := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have h2 : (n + k + 2) ^ A ≤ (n + k + 2) ^ (A * 3 ^ A + A) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc A * (3 * n + k + 2) ^ A ≤ A * (3 ^ A * (n + k + 2) ^ (A * 3 ^ A + A)) :=
        Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _ h2))
    _ = (A * 3 ^ A) * (n + k + 2) ^ (A * 3 ^ A + A) := by ring
    _ ≤ (A * 3 ^ A + A) * (n + k + 2) ^ (A * 3 ^ A + A) := Nat.mul_le_mul_right _ (by omega)

theorem exp_three (δ : ℝ) (n : ℕ) : δ / 3 / 2 * ((3 * n : ℕ) : ℝ) = δ / 2 * n := by
  push_cast; ring

end Dir

open Dir in
/-- **Directed Hamiltonian cycles: exact counting in time `2^{δn}` on sparse digraphs,
Turing-machine level, unconditional.** For every `δ > 0` and every `D` there are a Turing machine
of Mathlib with finite alphabets and a constant `C` such that, on the word `dcode A` (`n` in unary,
then the adjacency matrix row by row) of any digraph `A` on `n` vertices with at most `D·n` arcs
(loops allowed), the machine halts within `⌊C·2^{δn}⌋` steps with `#DHC(A)` (the number of directed
Hamiltonian cycles, `DirectedHamiltonian.dirHamCycles`) in binary (`Nat.bits`). -/
theorem theoremDHC (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (A : Finset (Fin n × Fin n)), A.card ≤ D * n →
        GraphProblems.Outputs M (dcode A) (Nat.bits (DirectedHamiltonian.dirHamCycles A).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨M, ⟨inst⟩, A₀, hA₀⟩ := hc_stepped (δ / 3) (by positivity) (D + 2)
  have : IsPolyT (Stepped.mapIn splitW M) := IsPolyT.mapIn splitW_polyT
  set c := A₀ * 3 ^ A₀ + A₀ with hc
  obtain ⟨N, C, hfin, hN⟩ := GraphProblems.tm_of_stepped (Stepped.mapIn splitW M)
    (ι := Σ n : ℕ, {A : Finset (Fin n × Fin n) // A.card ≤ D * n})
    (fun x => dcode x.2.1) (fun x => Nat.bits (DirectedHamiltonian.dirHamCycles x.2.1).card)
    (fun x => x.1) hδ c 2 2
    (fun x => by
      simp only [length_dcode]
      nlinarith)
    (fun x => by
      obtain ⟨n, A, hAc⟩ := x
      obtain ⟨T, hr, hT⟩ := hA₀ (split A) (by convert card_edge_split_le hAc)
      rw [← splitW_dcode, card_hamCycles_split] at hr
      refine ⟨T, (Stepped.mapIn_runs hr).mono le_rfl ?_, ?_⟩
      · have := pow_three_le A₀ n 0
        simpa using this
      · rw [exp_three] at hT
        refine hT.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
        exact_mod_cast (by omega : A₀ ≤ c))
  exact ⟨N, C, hfin, fun n A hA => hN ⟨n, A, hA⟩⟩

namespace Dir

/-! ## The weighted input word of a digraph -/

variable {n : ℕ}

/-- The `n²` arc-weight blocks, in row-major order. -/
def dwblocks (W : ℕ) (w : Fin n × Fin n → ℕ) : List (List Bool) :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => wblock W (w (u, v))

/-- The weight part of the word. -/
def dwmat (W : ℕ) (w : Fin n × Fin n → ℕ) : List Bool := (dwblocks W w).flatten

/-- **The input word of the ATSP machine**: `dcode A`, `W` in unary, the `n²` arc weights as blocks
of `W + 1` bits in row-major order. -/
def dtspCode (A : Finset (Fin n × Fin n)) (W : ℕ) (w : Fin n × Fin n → ℕ) : List Bool :=
  dcode A ++ (GraphProblems.unary W ++ dwmat W w)

theorem length_dwblocks (W : ℕ) (w : Fin n × Fin n → ℕ) : (dwblocks W w).length = n * n := by
  simp [dwblocks, List.length_flatMap]

theorem mem_dwblocks_length {W : ℕ} {w : Fin n × Fin n → ℕ} (hw : ∀ a, w a ≤ W) :
    ∀ b ∈ dwblocks W w, b.length = W + 1 := by
  intro b hb
  simp only [dwblocks, List.mem_flatMap, List.mem_map] at hb
  obtain ⟨u, -, v, -, rfl⟩ := hb
  exact length_wblock (hw _)

theorem length_dwmat {W : ℕ} {w : Fin n × Fin n → ℕ} (hw : ∀ a, w a ≤ W) :
    (dwmat W w).length = n * n * (W + 1) := by
  unfold dwmat
  rw [List.length_flatten, List.map_congr_left fun b hb => mem_dwblocks_length hw b hb,
    List.map_const', List.sum_replicate, smul_eq_mul, length_dwblocks]

theorem length_dtspCode (A : Finset (Fin n × Fin n)) {W : ℕ} {w : Fin n × Fin n → ℕ}
    (hw : ∀ a, w a ≤ W) :
    (dtspCode A W w).length = n + 1 + n * n + (W + 1 + n * n * (W + 1)) := by
  simp only [dtspCode, List.length_append, length_dcode, GraphProblems.unary,
    List.length_replicate, List.length_cons, List.length_nil, length_dwmat hw]

/-- The context of the instance `(A, W, w)`. -/
def dcOf (A : Finset (Fin n × Fin n)) (W : ℕ) (w : Fin n × Fin n → ℕ) : TIn :=
  (daOf A, (List.replicate W (), dwmat W w))

theorem readT_dtspCode (A : Finset (Fin n × Fin n)) (W : ℕ) (w : Fin n × Fin n → ℕ) :
    readT (dtspCode A W w) = dcOf A W w := by
  have hm : (dmatrix A).length = n * n := length_dmatrix A
  unfold readT dtspCode dcOf daOf dcode
  rw [List.append_assoc, Read.ones_unary_append, Read.rest_unary_append, List.take_left' hm,
    List.drop_left' hm, Read.ones_unary_append, Read.rest_unary_append]

theorem wgt_dcOf (A : Finset (Fin n × Fin n)) {W : ℕ} {w : Fin n × Fin n → ℕ} (hw : ∀ a, w a ≤ W)
    (u v : Fin n) : wgt (dcOf A W w) u.val v.val = w (u, v) := by
  unfold wgt dcOf dwmat
  simp only [List.length_replicate, daOf_len]
  rw [blk_flatten (W + 1) _ (mem_dwblocks_length hw), dwblocks,
    Read.getD_flatMap _ n [] v.2 _ (fun _ _ => by simp) u.val]
  simp [List.getD_eq_getElem?_getD, ones_wblock]

/-! ## The preprocessing of ATSP -/

/-- The weight of the pair `(x, y)` of copies, read from the context. -/
def sWgt (c : TIn) (x y : ℕ) : ℕ :=
  if x % 3 = 2 ∧ y % 3 = 0 then wgt c (x / 3) (y / 3)
  else if x % 3 = 0 ∧ y % 3 = 2 then wgt c (y / 3) (x / 3) else 0

/-- The weight blocks of the split graph. -/
def sBlocks (c : TIn) : List (List Bool) :=
  (List.range (3 * c.1.1.length)).flatMap fun x =>
    (List.range (3 * c.1.1.length)).map fun y => wblock c.2.1.length (sWgt c x y)

/-- The word of the split graph with its weights, from the context of the digraph. -/
def splitT (c : TIn) : List Bool :=
  splitG c.1 ++ (((c.2.1.map fun _ => true) ++ [false]) ++ (sBlocks c).flatten)

/-- **The preprocessing of `theoremATSP`.** -/
def splitTW (x : List Bool) : List Bool := splitT (readT x)

theorem sWgt_dcOf (A : Finset (Fin n × Fin n)) {W : ℕ} {w : Fin n × Fin n → ℕ} (hw : ∀ a, w a ≤ W)
    (x y : Fin (3 * n)) : sWgt (dcOf A W w) x.val y.val = splitWt w s(x, y) := by
  rw [splitWt_mk, sWgt, sw]
  have h1 := wgt_dcOf A hw (orig x) (orig y)
  have h2 := wgt_dcOf A hw (orig y) (orig x)
  simp only [orig] at h1 h2
  split_ifs
  · exact h1
  · exact h2
  · rfl

/-- **The preprocessing maps the weighted word of a digraph to the weighted word of its split
graph.** -/
theorem splitTW_dtspCode (A : Finset (Fin n × Fin n)) {W : ℕ} {w : Fin n × Fin n → ℕ}
    (hw : ∀ a, w a ≤ W) :
    splitTW (dtspCode A W w) = tspCode (split A) W (splitWt w) := by
  rw [splitTW, readT_dtspCode, splitT, tspCode]
  have hg : splitG (dcOf A W w).1 = code (split A) := by
    rw [← splitW_dcode, splitW, read1_dcode]; rfl
  rw [hg]
  congr 2
  · simp [dcOf, GraphProblems.unary]
  · unfold wmat sBlocks wblocks
    congr 1
    simp only [dcOf, daOf_len, List.length_replicate]
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    refine List.flatMap_congr fun x _ => ?_
    rw [List.map_map]
    refine List.map_congr_left fun y _ => ?_
    simp only [Function.comp_apply]
    have := sWgt_dcOf A hw x y
    simp only [dcOf] at this
    rw [this]

section Poly

variable {α : Type} [Enc α]

theorem wblock_polyT {W k : α → ℕ} (hW : Unary W) (hk : Unary k) :
    PolyT fun t => wblock (W t) (k t) := by
  have h1 : Unary fun t => W t - k t :=
    Unary.of_le hW (PolyT.sub hW.poly hk.poly) (fun _ => Nat.sub_le _ _)
  have h : PolyT fun t => ((List.replicate (k t) ()).map (fun _ => true) ++ [false]) ++
      (List.replicate (W t - k t) ()).map (fun _ => false) := by fun_prop
  refine h.congr fun t => ?_
  simp [wblock, GraphProblems.unary, List.map_replicate]

theorem sWgt_unary {c : α → TIn} {x y : α → ℕ} (hc : PolyT c) (hx : PolyT x) (hy : PolyT y) :
    Unary fun t => sWgt (c t) (x t) (y t) := by
  have d3 : PolyT fun _ : α => (3 : ℕ) := PolyT.const 3
  have hxd := PolyT.div hx d3
  have hyd := PolyT.div hy d3
  have hxm := PolyT.mod hx d3
  have hym := PolyT.mod hy d3
  have h1 : Unary fun t => wgt (c t) (x t / 3) (y t / 3) := wgt_unary hc hxd hyd
  have h2 : Unary fun t => wgt (c t) (y t / 3) (x t / 3) := wgt_unary hc hyd hxd
  have c1 : PolyT fun t => decide (x t % 3 = 2 ∧ y t % 3 = 0) :=
    (PolyT.and' (PolyT.decide_eq hxm (PolyT.const 2)) (PolyT.decide_eq hym (PolyT.const 0))).congr
      fun t => (Bool.decide_and _ _).symm
  have c2 : PolyT fun t => decide (x t % 3 = 0 ∧ y t % 3 = 2) :=
    (PolyT.and' (PolyT.decide_eq hxm (PolyT.const 0)) (PolyT.decide_eq hym (PolyT.const 2))).congr
      fun t => (Bool.decide_and _ _).symm
  have hp : PolyT fun t => sWgt (c t) (x t) (y t) := by
    unfold sWgt
    exact PolyT.ite' c1 h1.poly (PolyT.ite' c2 h2.poly (PolyT.const 0))
  refine Unary.of_le (h1.add h2) hp fun t => ?_
  unfold sWgt
  split_ifs <;> omega

theorem splitT_polyT : PolyT splitT := by
  have hL : Unary fun p : (TIn × ℕ) × ℕ => p.1.1.2.1.length := Unary.of_length (by fun_prop)
  have hw : Unary fun p : (TIn × ℕ) × ℕ => sWgt p.1.1 p.1.2 p.2 :=
    sWgt_unary (by fun_prop) (by fun_prop) (by fun_prop)
  have h3 : PolyT fun p : (TIn × ℕ) × ℕ => wblock p.1.1.2.1.length (sWgt p.1.1 p.1.2 p.2) :=
    wblock_polyT hL hw
  have h1 : PolyT fun c : TIn => List.range (3 * c.1.1.length) :=
    PolyT.comp (PolyT.range three_len_unary) (g := fun c : TIn => c.1) (by fun_prop)
  have h2 : PolyT fun p : TIn × ℕ => List.range (3 * p.1.1.1.length) :=
    PolyT.comp h1 (g := fun p : TIn × ℕ => p.1) (by fun_prop)
  have h0 : PolyT fun c : TIn => splitG c.1 :=
    PolyT.comp splitG_polyT (g := fun c : TIn => c.1) (by fun_prop)
  unfold splitT sBlocks; fun_prop

theorem splitTW_polyT : PolyT splitTW :=
  (PolyT.comp splitT_polyT readT_polyT : PolyT fun x => splitT (readT x))

end Poly

/-! ## The directed Kronecker integer and its decoding -/

/-- **The directed Kronecker integer** `3n · Σ_{H ∈ DHC(A)} 2^{bK(3n) · w(H)}`, the output of the
ATSP machine (the Kronecker integer of the split graph). -/
def dkronNum (A : Finset (Fin n × Fin n)) (w : Fin n × Fin n → ℕ) : ℕ :=
  (3 * n) * ∑ H ∈ DirectedHamiltonian.dirHamCycles A, 2 ^ (bK (3 * n) * arcWt w H)

theorem kronNum_split (A : Finset (Fin n × Fin n)) (w : Fin n × Fin n → ℕ) :
    kronNum (split A) (splitWt w) = dkronNum A w := by
  rw [kronNum, dkronNum, sum_hamCycles_split A w (fun k => 2 ^ (bK (3 * n) * k))]

/-- Digit `j` of the directed Kronecker integer, in base `2^{bK(3n)}`. -/
def dkronDigit (A : Finset (Fin n × Fin n)) (w : Fin n × Fin n → ℕ) (j : ℕ) : ℕ :=
  dkronNum A w / 2 ^ (bK (3 * n) * j) % 2 ^ bK (3 * n)

variable (A : Finset (Fin n × Fin n)) {W : ℕ} {w : Fin n × Fin n → ℕ}

/-- **Digit `j` of the output is `3n` times the number of directed tours of weight `j`**, for every
`j ≤ n·W` (every directed tour has weight `≤ n·W`). -/
theorem dkronNum_digit (hw : ∀ a, w a ≤ W) {j : ℕ} (hj : j ≤ n * W) :
    dkronDigit A w j = 3 * n * dtourCount A w j := by
  have h := kronNum_digit (split A) (splitWt_le hw) (j := j) (by nlinarith)
  rw [kronDigit, kronNum_split, tourCount_split] at h
  exact h

/-- Digit `j` is non-zero iff some directed tour has weight `j`. -/
theorem dkronNum_digit_ne_zero_iff (hn : 0 < n) (hw : ∀ a, w a ≤ W) {j : ℕ} (hj : j ≤ n * W) :
    dkronDigit A w j ≠ 0 ↔ ∃ H ∈ DirectedHamiltonian.dirHamCycles A, arcWt w H = j := by
  rw [dkronNum_digit A hw hj, dtourCount, Nat.mul_ne_zero_iff, Finset.card_ne_zero,
    filter_nonempty_iff]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

/-- **The number of directed tours of weight `j`** is digit `j` divided by `3n`. -/
theorem dkronNum_digit_div (hn : 0 < n) (hw : ∀ a, w a ≤ W) {j : ℕ} (hj : j ≤ n * W) :
    dkronDigit A w j / (3 * n) = dtourCount A w j := by
  rw [dkronNum_digit A hw hj, Nat.mul_div_cancel_left _ (by omega)]

/-- `k` is the minimum weight of a directed tour. -/
def IsMinDTourWt (w : Fin n × Fin n → ℕ) (k : ℕ) : Prop :=
  (∃ H ∈ DirectedHamiltonian.dirHamCycles A, arcWt w H = k) ∧
    ∀ H ∈ DirectedHamiltonian.dirHamCycles A, k ≤ arcWt w H

/-- **The minimum weight of a directed tour is the position of the lowest non-zero digit** of the
output, and the number of optimal tours is that digit divided by `3n` (`dkronNum_digit_div`). -/
theorem dkronNum_min_iff (hn : 0 < n) (hw : ∀ a, w a ≤ W) {k : ℕ} (hk : k ≤ n * W) :
    IsMinDTourWt A w k ↔ dkronDigit A w k ≠ 0 ∧ ∀ j < k, dkronDigit A w j = 0 := by
  rw [IsMinDTourWt, dkronNum_digit_ne_zero_iff A hn hw hk]
  refine and_congr Iff.rfl ⟨fun h j hj => ?_, fun h H hH => ?_⟩
  · by_contra hne
    obtain ⟨H, hH, rfl⟩ := (dkronNum_digit_ne_zero_iff A hn hw (by omega)).1 hne
    exact absurd (h H hH) (by omega)
  · by_contra hlt
    have := h (arcWt w H) (by omega)
    exact (dkronNum_digit_ne_zero_iff A hn hw (arcWt_le_of_mem_dirHamCycles A hw hH)).2
      ⟨H, hH, rfl⟩ this

/-! ## The ATSP stepped machine -/

/-- The ATSP machine: the preprocessing, then the TSP machine, on every digraph with `≤ Dn` arcs. -/
theorem atsp_stepped (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ M : Stepped (List Bool) (List Bool), Nonempty (IsPolyT M) ∧ ∃ c : ℕ,
      ∀ {n : ℕ} (A : Finset (Fin n × Fin n)) (W : ℕ) (w : Fin n × Fin n → ℕ),
        A.card ≤ D * n → (∀ a, w a ≤ W) →
        ∃ T : ℕ, M.Runs (dtspCode A W w) T (c * (n + W + 2) ^ c) (Nat.bits (dkronNum A w)) ∧
          (T : ℝ) ≤ c * ((W : ℝ) + 2) ^ c * (2 : ℝ) ^ (δ / 2 * n) := by
  obtain ⟨M, ⟨inst⟩, A₀, hA₀⟩ := tsp_stepped (δ / 3) (by positivity) (D + 2)
  refine ⟨Stepped.mapIn splitTW M, ⟨IsPolyT.mapIn splitTW_polyT⟩, A₀ * 3 ^ A₀ + A₀,
    fun {n} A W w hAc hw => ?_⟩
  obtain ⟨T, hr, hT⟩ := hA₀ (split A) W (splitWt w) (by convert card_edge_split_le hAc) (splitWt_le hw)
  rw [← splitTW_dtspCode A hw, kronNum_split] at hr
  refine ⟨T, (Stepped.mapIn_runs hr).mono le_rfl (pow_three_le A₀ n W), ?_⟩
  rw [exp_three] at hT
  refine hT.trans ?_
  have hW1 : (1 : ℝ) ≤ (W : ℝ) + 2 := by linarith [(Nat.cast_nonneg W : (0 : ℝ) ≤ W)]
  have h1 : (A₀ : ℝ) ≤ ((A₀ * 3 ^ A₀ + A₀ : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have h2 : ((W : ℝ) + 2) ^ A₀ ≤ ((W : ℝ) + 2) ^ (A₀ * 3 ^ A₀ + A₀) :=
    pow_le_pow_right₀ hW1 (by omega)
  have : (0 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * n) := by positivity
  gcongr

end Dir

open Dir in
/-- **ATSP (the directed Kronecker integer of an arc-weighted digraph) at Turing-machine level,
unconditional.** For every `δ > 0` and every `D` there are a Turing machine of Mathlib with finite
alphabets and a constant `C` such that, on the word `dtspCode A W w` (`n` in unary, the adjacency
matrix, `W` in unary, the `n²` arc weights `w (u, v) ≤ W` as blocks of `W+1` bits in row-major
order) of any digraph `A` on `n` vertices with at most `D·n` arcs, the machine halts within
`⌊C · 2^{δn} · (W+2)^C⌋` steps with the directed Kronecker integer
`dkronNum A w = 3n · Σ_{H ∈ DHC(A)} 2^{bK(3n) · w(H)}` (`bK m = m² + m`) in binary. -/
theorem theoremATSP (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (A : Finset (Fin n × Fin n)) (W : ℕ) (w : Fin n × Fin n → ℕ),
        A.card ≤ D * n → (∀ a, w a ≤ W) →
        GraphProblems.Outputs M (dtspCode A W w) (Nat.bits (dkronNum A w))
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n) * ((W : ℝ) + 2) ^ C⌋₊ := by
  obtain ⟨Mst, ⟨inst⟩, A, hA⟩ := atsp_stepped δ hδ D
  obtain ⟨M, q, hfin, hM⟩ := CountKSat.stHostW Mst
  have hδ2 : (0 : ℝ) < δ / 2 := by positivity
  obtain ⟨Cp, hCp⟩ := exists_pow_le ((A + 3) * q) hδ2
  refine ⟨M, q * (A + 1) * (4 + A) ^ q * Cp + A + (A + 3) * q, hfin, fun n G W w hm hw => ?_⟩
  obtain ⟨T, hr, hT⟩ := hA G W w hm hw
  obtain ⟨ev⟩ := hM (dtspCode G W w) T _ _ hr
  set S := A * (n + W + 2) ^ A with hS
  set L := (dtspCode G W w).length with hL
  have hLv : L = n + 1 + n * n + (W + 1 + n * n * (W + 1)) := length_dtspCode G hw
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * n) := Real.one_le_rpow one_le_two (by positivity)
  -- L + S + 1 ≤ (4 + A) (n + W + 2)^(A + 3)
  have hLS : L + S + 1 ≤ (4 + A) * (n + W + 2) ^ (A + 3) := by
    have hL1 : L + 1 ≤ 4 * (n + W + 2) ^ 3 := by
      rw [hLv]
      set N := n + W with hN
      have h1 : n ≤ N := by omega
      have h2 : W ≤ N := by omega
      have e3 : (N + 2) ^ 3 = N * N * N + 6 * (N * N) + 12 * N + 8 := by ring
      have a1 : n * n ≤ N * N := Nat.mul_le_mul h1 h1
      have a2 : n * n * (W + 1) ≤ N * N * (N + 1) := Nat.mul_le_mul a1 (by omega)
      have a3 : N * N * (N + 1) = N * N * N + N * N := by ring
      rw [e3]
      omega
    have hp3 : (n + W + 2) ^ 3 ≤ (n + W + 2) ^ (A + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    have hpA : (n + W + 2) ^ A ≤ (n + W + 2) ^ (A + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 := Nat.mul_le_mul_left 4 hp3
    have h5 := Nat.mul_le_mul_left A hpA
    rw [add_mul]
    omega
  have hle : q * (T + 1) * (L + S + 1) ^ q ≤
      ⌊((q * (A + 1) * (4 + A) ^ q * Cp + A + (A + 3) * q : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n) *
        ((W : ℝ) + 2) ^ (q * (A + 1) * (4 + A) ^ q * Cp + A + (A + 3) * q)⌋₊ := by
    refine Nat.le_floor ?_
    have hW0 : (0 : ℝ) ≤ (W : ℝ) + 2 := by positivity
    have hW1 : (1 : ℝ) ≤ (W : ℝ) + 2 := by linarith [(Nat.cast_nonneg W : (0 : ℝ) ≤ W)]
    have h1 : ((T : ℝ) + 1) ≤ ((A : ℝ) + 1) * ((W : ℝ) + 2) ^ A * (2 : ℝ) ^ (δ / 2 * n) := by
      have : (1 : ℝ) ≤ ((W : ℝ) + 2) ^ A * (2 : ℝ) ^ (δ / 2 * n) :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ hW1) hE1
      nlinarith
    have h2 : (((L + S + 1 : ℕ) : ℝ)) ^ q ≤
        ((4 : ℝ) + A) ^ q * ((((n : ℝ) + 2) ^ ((A + 3) * q)) * ((W : ℝ) + 2) ^ ((A + 3) * q)) := by
      have h6 : (((L + S + 1 : ℕ) : ℝ)) ≤
          ((4 : ℝ) + A) * (((n : ℝ) + 2) ^ (A + 3) * ((W : ℝ) + 2) ^ (A + 3)) := by
        have := hLS.trans (Nat.mul_le_mul_left (4 + A) (TSPAsm.pow_add_le_mul n W (A + 3)))
        exact_mod_cast this
      calc (((L + S + 1 : ℕ) : ℝ)) ^ q ≤
            (((4 : ℝ) + A) * (((n : ℝ) + 2) ^ (A + 3) * ((W : ℝ) + 2) ^ (A + 3))) ^ q := by
              gcongr
        _ = ((4 : ℝ) + A) ^ q * ((((n : ℝ) + 2) ^ ((A + 3) * q)) * ((W : ℝ) + 2) ^ ((A + 3) * q)) := by
              rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    have h3 : ((n : ℝ) + 2) ^ ((A + 3) * q) ≤ Cp * (2 : ℝ) ^ (δ / 2 * n) := hCp n
    have h7 : (2 : ℝ) ^ (δ * n) = (2 : ℝ) ^ (δ / 2 * n) * (2 : ℝ) ^ (δ / 2 * n) := by
      rw [← Real.rpow_add two_pos]; congr 1; ring
    have hWexp : ((W : ℝ) + 2) ^ A * ((W : ℝ) + 2) ^ ((A + 3) * q) ≤
        ((W : ℝ) + 2) ^ (q * (A + 1) * (4 + A) ^ q * Cp + A + (A + 3) * q) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hW1 (by omega)
    have hpos1 : (0 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * n) := by positivity
    have hpos2 : (0 : ℝ) ≤ ((4 : ℝ) + A) ^ q := by positivity
    have hpos3 : (0 : ℝ) ≤ ((W : ℝ) + 2) ^ ((A + 3) * q) := by positivity
    have hpos4 : (0 : ℝ) ≤ ((W : ℝ) + 2) ^ A := by positivity
    have h2' : (((L + S + 1 : ℕ) : ℝ)) ^ q ≤
        ((4 : ℝ) + A) ^ q * ((Cp * (2 : ℝ) ^ (δ / 2 * n)) * ((W : ℝ) + 2) ^ ((A + 3) * q)) :=
      h2.trans (by gcongr)
    rw [h7]
    calc ((q * (T + 1) * (L + S + 1) ^ q : ℕ) : ℝ)
        = (q : ℝ) * ((T : ℝ) + 1) * (((L + S + 1 : ℕ) : ℝ)) ^ q := by push_cast; ring
      _ ≤ (q : ℝ) * (((A : ℝ) + 1) * ((W : ℝ) + 2) ^ A * (2 : ℝ) ^ (δ / 2 * n)) *
            (((4 : ℝ) + A) ^ q * ((Cp * (2 : ℝ) ^ (δ / 2 * n)) * ((W : ℝ) + 2) ^ ((A + 3) * q))) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2' (by positivity)
            (by positivity)
      _ = ((q : ℝ) * ((A : ℝ) + 1) * ((4 : ℝ) + A) ^ q * Cp) *
            ((2 : ℝ) ^ (δ / 2 * n) * (2 : ℝ) ^ (δ / 2 * n)) *
            (((W : ℝ) + 2) ^ A * ((W : ℝ) + 2) ^ ((A + 3) * q)) := by ring
      _ ≤ ((q * (A + 1) * (4 + A) ^ q * Cp + A + (A + 3) * q : ℕ) : ℝ) *
            ((2 : ℝ) ^ (δ / 2 * n) * (2 : ℝ) ^ (δ / 2 * n)) *
            ((W : ℝ) + 2) ^ (q * (A + 1) * (4 + A) ^ q * Cp + A + (A + 3) * q) := by
          gcongr
          · push_cast
            have : (0 : ℝ) ≤ ((A : ℝ) + 3) * q := by positivity
            have : (0 : ℝ) ≤ (A : ℝ) := by positivity
            linarith
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩

open Dir in
/-- **ATSP at Turing-machine level, with the decoding.** The machine of `theoremATSP`, and: for
every `j ≤ n·W`, digit `j` of its output (in base `2^{bK(3n)}`) is `3n` times the number of directed
tours of weight `j` (for `W = 0`, digit `0` is `3n·#DHC(A)`); the minimum weight of a directed tour
is the position of the lowest non-zero digit; and the number of directed tours of weight `j` (in
particular of optimal ones) is that digit divided by `3n`. -/
theorem theoremATSP_decode (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (A : Finset (Fin n × Fin n)) (W : ℕ) (w : Fin n × Fin n → ℕ),
        A.card ≤ D * n → (∀ a, w a ≤ W) →
        GraphProblems.Outputs M (dtspCode A W w) (Nat.bits (dkronNum A w))
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n) * ((W : ℝ) + 2) ^ C⌋₊ ∧
        (∀ j ≤ n * W, dkronDigit A w j = 3 * n * dtourCount A w j) ∧
        (0 < n → ∀ k ≤ n * W, IsMinDTourWt A w k ↔
          dkronDigit A w k ≠ 0 ∧ ∀ j < k, dkronDigit A w j = 0) ∧
        (0 < n → ∀ j ≤ n * W, dkronDigit A w j / (3 * n) = dtourCount A w j) := by
  obtain ⟨M, C, hfin, hM⟩ := theoremATSP δ hδ D
  refine ⟨M, C, hfin, fun n A W w hm hw => ⟨hM n A W w hm hw, fun j hj => dkronNum_digit A hw hj,
    fun hn k hk => dkronNum_min_iff A hn hw hk, fun hn j hj => dkronNum_digit_div A hn hw hj⟩⟩

open Dir T2 in
/-- **Directed Hamiltonian cycles, sharp rate, Turing-machine level, unconditional.** One Turing
machine of Mathlib with finite alphabets and one constant `C` such that, on the word `dcode A` of
every digraph `A` with `n` vertices and `m` arcs, the machine halts within
`⌊C·2^{C(m+n)/√(log₂(n+2))}⌋` steps with `#DHC(A)` in binary. (The machine of Theorem 2, `T2.hcM2`,
after the preprocessing `splitW`; the split graph has `3n` vertices and at most `m + 2n` edges.) -/
theorem theoremDHC_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (A : Finset (Fin n × Fin n)),
        GraphProblems.Outputs M (dcode A) (Nat.bits (DirectedHamiltonian.dirHamCycles A).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * ((A.card : ℝ) + n) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
  obtain ⟨c₀, ⟨pk'⟩⟩ := exists_ulabelPackage
  let pk := pk'.toUPackage
  obtain ⟨c, x₀, C₀, D, Alg, -, -, -, -, -, he, hyp, -⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨C₁, hC₁⟩ := geBody
  have hL := hyp.levels
  have hk := hyp.computesK
  obtain ⟨A, hA⟩ := hcM2_runs pk hC₁ hL hk _ hyp.solves (x₀ := x₀) fun l => he l
  obtain ⟨inst⟩ := hcM2_poly pk _ _ hL hk hyp.steps
  have : IsPolyT (Stepped.mapIn splitW (hcM2 pk (ExplicitCost.cliqueMachine (c + 2) x₀ Alg)
      (CliqueLevels.levelsUnder x₀) (Levels.Gen.K x₀ 0))) := IsPolyT.mapIn splitW_polyT
  obtain ⟨M, q, hfin, hM⟩ := CountKSat.exists_tmW (Stepped.mapIn splitW
    (hcM2 pk (ExplicitCost.cliqueMachine (c + 2) x₀ Alg) (CliqueLevels.levelsUnder x₀)
      (Levels.Gen.K x₀ 0)))
  have hQ : ∃ A, ∀ n, Pol A n (n + 1 + n * n) :=
    ⟨_, fun n => Pol.add (Pol.add Pol.id (Pol.const 1)) (Pol.mul Pol.id Pol.id)⟩
  obtain ⟨AL, hAL⟩ := hQ
  set c₁ := 30 * C₀ + 1
  set k₀ := Levels.Gen.K x₀ 0 ^ 30
  set Af := q + (A + 1) + q * (2 * AL * (c₁ ^ 2 * k₀) + A + 1 + 1) with hAf
  refine ⟨M, 5 * 2 ^ (2 * Af), hfin, fun n Ad => ?_⟩
  obtain ⟨T, S, hrun, hT, hS⟩ := hA (split Ad)
  rw [← splitW_dcode, card_hamCycles_split] at hrun
  obtain ⟨ev⟩ := hM (dcode Ad) T S _ (Stepped.mapIn_runs hrun)
  obtain ⟨l, hKl, hK2, hup, hlo⟩ := kfacts hL hk (aOf (split Ad)) (aOf_len (split Ad))
  rw [← hKl] at hK2 hup hlo
  have hmA : (@SimpleGraph.edgeFinset _ (split Ad) (split Ad).fintypeEdgeSet).card ≤
      Ad.card + 2 * n := by convert card_edgeFinset_split_le Ad
  generalize (@SimpleGraph.edgeFinset _ (split Ad) (split Ad).fintypeEdgeSet).card = m at hT hS hmA
  have hlen : (dcode Ad).length ≤ 3 * n + 1 + 3 * n * (3 * n) := by
    rw [length_dcode]; nlinarith
  have hLx : ((dcode Ad).length : ℝ) ≤ (2 : ℝ) ^ Xp (2 * AL * (c₁ ^ 2 * k₀)) (3 * n) m := by
    have h0 : ((dcode Ad).length : ℝ) ≤ ((3 * n + 1 + 3 * n * (3 * n) : ℕ) : ℝ) := by
      exact_mod_cast hlen
    exact h0.trans (pol_le_Xp hK2 hup hlo (hAL (3 * n)))
  have h1 : (T : ℝ) + 1 ≤ (2 : ℝ) ^ Xp (A + 1) (3 * n) m := add_one_le_Xp hT
  have h2 : ((dcode Ad).length : ℝ) + S + 1 ≤
      (2 : ℝ) ^ Xp (2 * AL * (c₁ ^ 2 * k₀) + A + 1 + 1) (3 * n) m :=
    add_one_le_Xp (add_le_Xp hLx hS)
  have h3 := pow_le_Xp (by positivity) h2 q
  have h4 : (q : ℝ) * ((T : ℝ) + 1) ≤ (2 : ℝ) ^ Xp (q + (A + 1)) (3 * n) m :=
    mul_le_Xp (Nat.cast_nonneg _) (const_le_Xp q (3 * n) m) h1
  have h5 := mul_le_Xp (by positivity) h4 h3
  rw [← hAf] at h5
  -- the exponent of the split graph is at most that of the digraph
  have hs0 := T2.sq_pos n
  have hsq : T2.sq n ≤ T2.sq (3 * n) := by
    unfold T2.sq T2.Lam
    apply Real.sqrt_le_sqrt
    apply Real.logb_le_logb_of_le one_lt_two (by positivity)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast; linarith
  have hAf2 : (Af : ℝ) ≤ ((2 ^ (2 * Af) : ℕ) : ℝ) := by
    have : Af ≤ 2 ^ (2 * Af) :=
      (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact_mod_cast this
  have hexp : (Af : ℝ) * ((m : ℝ) + ((3 * n : ℕ) : ℝ)) / T2.sq (3 * n) ≤
      ((5 * 2 ^ (2 * Af) : ℕ) : ℝ) * ((Ad.card : ℝ) + n) / T2.sq n := by
    have hm' : (m : ℝ) + ((3 * n : ℕ) : ℝ) ≤ 5 * ((Ad.card : ℝ) + n) := by
      have h0 : ((m : ℕ) : ℝ) ≤ ((Ad.card + 2 * n : ℕ) : ℝ) := Nat.cast_le.2 hmA
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h0
      rw [Nat.cast_mul, Nat.cast_ofNat]
      linarith
    have hnum : (0 : ℝ) ≤ (Af : ℝ) * ((m : ℝ) + ((3 * n : ℕ) : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    calc (Af : ℝ) * ((m : ℝ) + ((3 * n : ℕ) : ℝ)) / T2.sq (3 * n)
        ≤ (Af : ℝ) * ((m : ℝ) + ((3 * n : ℕ) : ℝ)) / T2.sq n :=
          div_le_div_of_nonneg_left hnum hs0 hsq
      _ ≤ ((5 * 2 ^ (2 * Af) : ℕ) : ℝ) * ((Ad.card : ℝ) + n) / T2.sq n := by
          apply div_le_div_of_nonneg_right _ hs0.le
          have hA0 : (0 : ℝ) ≤ (Ad.card : ℝ) + n := add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          have hAf0 : (0 : ℝ) ≤ Af := Nat.cast_nonneg _
          calc (Af : ℝ) * ((m : ℝ) + ((3 * n : ℕ) : ℝ)) ≤ (Af : ℝ) * (5 * ((Ad.card : ℝ) + n)) :=
                mul_le_mul_of_nonneg_left hm' hAf0
            _ ≤ ((2 ^ (2 * Af) : ℕ) : ℝ) * (5 * ((Ad.card : ℝ) + n)) :=
                mul_le_mul_of_nonneg_right hAf2 (mul_nonneg (by norm_num) hA0)
            _ = ((5 * 2 ^ (2 * Af) : ℕ) : ℝ) * ((Ad.card : ℝ) + n) := by push_cast; ring
  have hle : q * (T + 1) * ((dcode Ad).length + S + 1) ^ q ≤
      ⌊((5 * 2 ^ (2 * Af) : ℕ) : ℝ) * (2 : ℝ) ^ (((5 * 2 ^ (2 * Af) : ℕ) : ℝ) * ((Ad.card : ℝ) + n) /
        Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
    apply Nat.le_floor
    have e1 : ((q * (T + 1) * ((dcode Ad).length + S + 1) ^ q : ℕ) : ℝ) =
        (q : ℝ) * ((T : ℝ) + 1) * (((dcode Ad).length : ℝ) + S + 1) ^ q := by push_cast; ring
    rw [e1]
    refine h5.trans ((Xp_split Af (3 * n) m).trans ?_)
    have e2 : (2 : ℝ) ^ (2 * (Af : ℝ)) = ((2 ^ (2 * Af) : ℕ) : ℝ) := by
      rw [show (2 : ℝ) * (Af : ℝ) = ((2 * Af : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      push_cast; ring
    rw [e2, show Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) = T2.sq n from rfl]
    have hC : ((2 ^ (2 * Af) : ℕ) : ℝ) ≤ ((5 * 2 ^ (2 * Af) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ^ (2 * Af) ≤ 5 * 2 ^ (2 * Af))
    exact mul_le_mul hC (Real.rpow_le_rpow_of_exponent_le one_le_two hexp)
      (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _)
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩

end EthFollowup.ExactHC
