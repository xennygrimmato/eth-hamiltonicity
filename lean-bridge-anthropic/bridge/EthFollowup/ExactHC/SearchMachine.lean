/-
# Decision, search and paths: the stepped machines (generic in the counting machine)

`cor:decision-search` of `paper/main.tex`, at the level of Anthropic's stepped machines.

* `Srch.iterRange N M c₀`: a loop over `y < N a` whose body sees the current state `c` (the loops
  of `StepMachines/Prog/Range.lean` fold the results of a body that does not see the accumulator);
  `iterRange_runs` (steps `Σ (t y + 1)`), `IsPolyT.iterRange`.
* `Srch.searchS O`: the self-reduction of `SelfReduction.lean` with the oracle `O` (any machine on
  graph codes whose output is empty iff the graph has no edge set with the property `Q`): for
  `k < n²` it tries to delete the edge of the matrix entry `k`, keeping the deletion iff `O` says
  the rest still has one; at the end it runs `O` once more and outputs the adjacency matrix of the
  final graph, or the empty word. `searchS_runs`: on `G`, within `(n²+1)(T_O + 3)` steps, the output
  is `[]` if `G` has no such edge set and otherwise `matrix (graphOf X)` for one, `X ⊆ E(G)`.
  (`n²` oracle calls rather than `m`: non-edges are tried too; they are absorbed in the constant.)
* `Srch.decS O`: one call of `O` and the bit «output non-empty».
* `Srch.apexW`: `code G ↦ code (apex G)` (`apexW_code`), for Hamiltonian paths.

Standard axioms only.
-/
import EthFollowup.ExactHC.Assembly
import EthFollowup.ExactHC.SelfReduction
import EthFollowup.ExactHC.HamPath

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

namespace Srch

open Groundwork Groundwork.Prog GraphProblems Finset

/-! ## A loop whose body sees the state -/

section Iter

variable {α γ : Type}

/-- The point `y` of the loop with state `c`: the body starts on `(a, y, c)`, or the loop halts
with `c` if `y = N a`. -/
def iterGo [HasSize α] [HasSize γ] (N : α → ℕ) (M : Stepped (α × ℕ × γ) γ) (a : α) (y : ℕ) (c : γ) :
    (α × ℕ × M.σ) ⊕ γ :=
  if y < N a then .inl (a, y, M.init (a, y, c)) else .inr c

/-- The loop `c ↦ M (a, y, c)` for `y = 0, …, N a − 1`, from `c₀ a`. -/
def iterRange [HasSize α] [HasSize γ] (N : α → ℕ) (M : Stepped (α × ℕ × γ) γ) (c₀ : α → γ) :
    Stepped α γ where
  σ := (α × ℕ × M.σ) ⊕ γ
  init a := iterGo N M a 0 (c₀ a)
  step s := match s with
    | .inl p => match M.out p.2.2 with
      | some c => iterGo N M p.1 (p.2.1 + 1) c
      | none => .inl (p.1, p.2.1, M.step p.2.2)
    | .inr c => .inr c
  out s := match s with | .inl _ => none | .inr c => some c

variable [HasSize α] [HasSize γ] {N : α → ℕ} {M : Stepped (α × ℕ × γ) γ} {c₀ : α → γ}

theorem iter_body {a : α} {y : ℕ} {c r : γ} {s : M.σ} {t T Sm S : ℕ} (h : M.Reaches Sm c s t)
    (hS : size a + (size y + Sm) + 1 ≤ S)
    (hr : (iterRange N M c₀).Reaches S r (iterGo N M a (y + 1) c) T) :
    (iterRange N M c₀).Reaches S r (.inl (a, y, s)) (t + 1 + T) := by
  induction h with
  | @halt s t ho hs =>
    have e : (iterRange N M c₀).step (.inl (a, y, s)) = iterGo N M a (y + 1) c := by
      change (match M.out s with | some c => _ | none => _) = _
      rw [ho]
    have : (iterRange N M c₀).Reaches S r (.inl (a, y, s)) (T + 1) :=
      .step rfl (by change size a + (size y + size s) + 1 ≤ _; omega) (e ▸ hr)
    exact this.mono (by omega) le_rfl
  | @step s t ho hs _ ih =>
    have e : (iterRange N M c₀).step (.inl (a, y, s)) = .inl (a, y, M.step s) := by
      change (match M.out s with | some c => _ | none => _) = _
      rw [ho]
    have : (iterRange N M c₀).Reaches S r (.inl (a, y, s)) (t + 1 + T + 1) :=
      .step rfl (by change size a + (size y + size s) + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl

theorem iter_reaches (a : α) (cs : ℕ → γ) (t : ℕ → ℕ) (Sc Sm : ℕ)
    (hM : ∀ y < N a, M.Runs (a, y, cs y) (t y) Sm (cs (y + 1))) (hc : ∀ y ≤ N a, size (cs y) ≤ Sc) :
    ∀ k y, y + k = N a → (iterRange N M c₀).Reaches (size a + size (N a) + (Sc + Sm) + 1) (cs (N a))
      (iterGo N M a y (cs y)) (∑ j ∈ range k, (t (y + j) + 1)) := by
  intro k
  induction k with
  | zero =>
    intro y hy
    simp only [add_zero] at hy
    subst hy
    have e : iterGo N M a (N a) (cs (N a)) = .inr (cs (N a)) := by simp [iterGo]
    rw [e]
    have := hc (N a) le_rfl
    exact .halt rfl (by change size (cs (N a)) + 1 ≤ _; omega)
  | succ k ih =>
    intro y hy
    have hlt : y < N a := by omega
    have e : iterGo N M a y (cs y) = .inl (a, y, M.init (a, y, cs y)) := by simp [iterGo, hlt]
    rw [e, sum_range_succ']
    have hsy : size y ≤ size (N a) := by
      simp only [size_nat]; exact Nat.add_le_add_right (Nat.size_le_size hlt.le) 1
    have h1 := iter_body (c₀ := c₀) (hM y hlt) (S := size a + size (N a) + (Sc + Sm) + 1)
      (by omega) (ih (y + 1) (by omega))
    refine h1.mono (le_of_eq ?_) le_rfl
    simp only [add_zero]
    rw [add_comm (t y + 1)]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show y + 1 + j = y + (j + 1) by omega]

/-- **The loop**: steps `Σ_{y < N a} (t y + 1)`; result the state after the last point. -/
theorem iterRange_runs (a : α) (cs : ℕ → γ) (hcs : cs 0 = c₀ a) (t : ℕ → ℕ) (Sc Sm : ℕ)
    (hM : ∀ y < N a, M.Runs (a, y, cs y) (t y) Sm (cs (y + 1))) (hc : ∀ y ≤ N a, size (cs y) ≤ Sc) :
    (iterRange N M c₀).Runs a (∑ y ∈ range (N a), (t y + 1)) (size a + size (N a) + (Sc + Sm) + 1)
      (cs (N a)) := by
  have := iter_reaches (c₀ := c₀) a cs t Sc Sm hM hc (N a) 0 (by omega)
  simp only [zero_add] at this
  unfold Stepped.Runs
  change (iterRange N M c₀).Reaches _ _ (iterGo N M a 0 (c₀ a)) _
  rw [← hcs]
  exact this

end Iter

section IterPoly

variable {α γ : Type} [Enc α] [Enc γ] {N : α → ℕ} {M : Stepped (α × ℕ × γ) γ} [IsPolyT M] {c₀ : α → γ}

theorem iterGo_poly [HasSize α] [HasSize γ] (hN : PolyT N) :
    PolyT (fun p : α × ℕ × γ => iterGo N M p.1 p.2.1 p.2.2) := by
  have := IsPolyT.init (M := M)
  unfold iterGo; fun_prop

theorem iterRange_step [HasSize α] [HasSize γ] (hN : PolyT N) :
    PolyT (fun s : (α × ℕ × M.σ) ⊕ γ => match s with
      | .inl p => match M.out p.2.2 with
        | some c => iterGo N M p.1 (p.2.1 + 1) c
        | none => .inl (p.1, p.2.1, M.step p.2.2)
      | .inr c => .inr c) := by
  have h1 := IsPolyT.step (M := M)
  have h2 := IsPolyT.out (M := M)
  have h3 : PolyT fun q : (α × ℕ × M.σ) × γ => iterGo N M q.1.1 (q.1.2.1 + 1) q.2 :=
    PolyT.comp (g := fun q : (α × ℕ × M.σ) × γ => (q.1.1, q.1.2.1 + 1, q.2)) (iterGo_poly hN) (by fun_prop)
  have h4 : PolyT fun p : α × ℕ × M.σ => (M.out p.2.2).elim (.inl (p.1, p.2.1, M.step p.2.2) : (α × ℕ × M.σ) ⊕ γ)
      fun c => iterGo N M p.1 (p.2.1 + 1) c :=
    PolyT.optionElim (by fun_prop) (by fun_prop) h3
  have h5 : PolyT fun s : (α × ℕ × M.σ) ⊕ γ => s.elim
      (fun p => (M.out p.2.2).elim (.inl (p.1, p.2.1, M.step p.2.2) : (α × ℕ × M.σ) ⊕ γ)
        fun c => iterGo N M p.1 (p.2.1 + 1) c) fun c => .inr c :=
    PolyT.sumElim (by fun_prop) (PolyT.comp (g := fun q : ((α × ℕ × M.σ) ⊕ γ) × (α × ℕ × M.σ) => q.2) h4 (by fun_prop))
      (by fun_prop)
  refine h5.congr fun s => ?_
  rcases s with p | c
  · simp only [Sum.elim_inl]
    cases M.out p.2.2 <;> rfl
  · rfl

theorem iterRange_out :
    PolyT (fun s : (α × ℕ × M.σ) ⊕ γ => match s with | .inl _ => none | .inr c => some c) :=
  (by fun_prop : PolyT fun s : (α × ℕ × M.σ) ⊕ γ => s.elim (fun _ => none) fun c => some c).congr
    fun s => by cases s <;> rfl

variable [HasSize α] [HasSize γ] [Carried α] [Carried γ]

/-- The loop `iterRange` is `IsPolyT` if its body is and `N`, `c₀` are polynomial-time. -/
@[instance_reducible] def IsPolyT.iterRange (hN : PolyT N) (hc : PolyT c₀) : IsPolyT (iterRange N M c₀) where
  enc := (inferInstance : Enc ((α × ℕ × M.σ) ⊕ γ))
  carried := (inferInstance : Carried ((α × ℕ × M.σ) ⊕ γ))
  init := PolyT.comp (g := fun a => (a, 0, c₀ a)) (iterGo_poly (M := M) hN) (by fun_prop)
  step := iterRange_step hN
  out := iterRange_out

end IterPoly

/-! ## The words -/

section Words

/-- The `n × n` matrix `mat` without the edge of the entry `k` (both entries `(u, w)`, `(w, u)`). -/
def delM (n : ℕ) (mat : List Bool) (k : ℕ) : List Bool :=
  (List.range n).flatMap fun i => (List.range n).map fun j =>
    adjB n mat i j && !(decide (i * n + j = k) || decide (j * n + i = k))

/-- The input of one step of the search: the graph, the entry `k`, the current matrix. -/
abbrev SIn : Type := Asm.GIn × ℕ × List Bool

/-- The code of the current graph without the edge of the entry `k`. -/
def candW (p : SIn) : List Bool := GraphProblems.unary p.1.1.length ++ delM p.1.1.length p.2.2 p.2.1

/-- Keep the deletion iff the oracle's answer is non-empty. -/
def keepF (q : SIn × List Bool) : List Bool :=
  if q.2.length = 0 then q.1.2.2 else delM q.1.1.1.length q.1.2.2 q.1.2.1

/-- The code of the final graph. -/
def chkW (p : List Bool × List Bool) : List Bool := GraphProblems.unary (ones p.1) ++ p.2

/-- The final matrix if the oracle's answer on it is non-empty, else the empty word. -/
def chkF (q : (List Bool × List Bool) × List Bool) : List Bool := if q.2.length = 0 then [] else q.1.2

/-- The bit «the answer is non-empty». -/
def decF (q : List Bool × List Bool) : List Bool := [decide (q.2.length ≠ 0)]

/-- The apex graph's matrix: `G` on `Fin n`, and the vertex `n` adjacent to all others. -/
def apexM (n : ℕ) (mat : List Bool) : List Bool :=
  (List.range (n + 1)).flatMap fun i => (List.range (n + 1)).map fun j =>
    (decide (i < n) && decide (j < n) && adjB n mat i j) || (!decide (i = j) && (decide (i = n) || decide (j = n)))

/-- `code G ↦ code (apex G)`. -/
def apexW (x : List Bool) : List Bool := GraphProblems.unary (ones x + 1) ++ apexM (ones x) (rest x)

variable (O : Stepped (List Bool) (List Bool))

/-- One step of the search. -/
def bodyS : Stepped SIn (List Bool) := Stepped.bind (Stepped.mapIn candW O) (Stepped.ofFun keepF)

/-- The loop over the `n²` entries. -/
def loopS : Stepped Asm.GIn (List Bool) :=
  iterRange (fun a => a.1.length * a.1.length) (bodyS O) (fun a => a.2)

/-- The final call of the oracle. -/
def checkS : Stepped (List Bool × List Bool) (List Bool) :=
  Stepped.bind (Stepped.mapIn chkW O) (Stepped.ofFun chkF)

/-- **The search machine** with the oracle `O`. -/
def searchS : Stepped (List Bool) (List Bool) := Stepped.bind (Stepped.mapIn read1 (loopS O)) (checkS O)

/-- **The decision machine** with the oracle `O`. -/
def decS : Stepped (List Bool) (List Bool) := Stepped.bind O (Stepped.ofFun decF)

end Words

/-! ## Polynomial time -/

section Poly

theorem unary_polyT {α : Type} [Enc α] {f : α → List Unit} (hf : PolyT f) :
    PolyT fun x => GraphProblems.unary (f x).length := by
  have : PolyT fun x => (f x).map (fun _ => true) ++ [false] := by fun_prop
  refine this.congr fun x => ?_
  simp [GraphProblems.unary, List.map_const']

theorem delM_polyT : PolyT fun p : SIn => delM p.1.1.length p.2.2 p.2.1 := by
  have h1 := Asm.range_polyT (α := SIn) (a := fun p => p.1) (by fun_prop)
  have h2 := Asm.range_polyT (α := SIn × ℕ) (a := fun p => p.1.1) (by fun_prop)
  unfold delM; fun_prop

theorem candW_polyT : PolyT candW := by
  have h3 := unary_polyT (α := SIn) (f := fun p => p.1.1) (by fun_prop)
  have := delM_polyT
  unfold candW; fun_prop

theorem keepF_polyT : PolyT keepF := by
  have h : PolyT fun q : SIn × List Bool => delM q.1.1.1.length q.1.2.2 q.1.2.1 :=
    delM_polyT.comp PolyT.id'.fst
  unfold keepF; fun_prop

theorem chkW_polyT : PolyT chkW := by
  have h0 : PolyT fun p : List Bool × List Bool => List.replicate (ones p.1) () := ones_unary (by fun_prop)
  have h3 := unary_polyT h0
  simp only [List.length_replicate] at h3
  unfold chkW; fun_prop

theorem chkF_polyT : PolyT chkF := by unfold chkF; fun_prop

theorem decF_polyT : PolyT decF := by unfold decF; fun_prop

theorem apexW_polyT : PolyT apexW := by
  have h0 : PolyT fun x : List Bool => List.replicate (ones x) () := ones_unary PolyT.id'
  have hu : PolyT fun x : List Bool => List.replicate (ones x + 1) () :=
    (show PolyT fun x : List Bool => () :: List.replicate (ones x) () by fun_prop).congr
      fun x => by rw [List.replicate_succ]
  have h3 := unary_polyT hu
  simp only [List.length_replicate] at h3
  have h1 : PolyT fun x : List Bool => List.range (ones x + 1) := PolyT.range hu
  have h2 : PolyT fun p : List Bool × ℕ => List.range (ones p.1 + 1) := h1.comp PolyT.id'.fst
  have hn : PolyT fun x : List Bool => ones x := (ones_unary PolyT.id').poly
  unfold apexW apexM; fun_prop

variable (O : Stepped (List Bool) (List Bool)) [IsPolyT O]

theorem searchS_poly : Nonempty (IsPolyT (searchS O)) := by
  have : IsPolyT (Stepped.mapIn candW O) := IsPolyT.mapIn candW_polyT
  have : IsPolyT (Stepped.ofFun keepF) := IsPolyT.ofFun keepF_polyT
  have : IsPolyT (bodyS O) := IsPolyT.bind
  have : IsPolyT (loopS O) := IsPolyT.iterRange (by fun_prop) (by fun_prop)
  have : IsPolyT (Stepped.mapIn read1 (loopS O)) := IsPolyT.mapIn stCertRead.1
  have : IsPolyT (Stepped.mapIn chkW O) := IsPolyT.mapIn chkW_polyT
  have : IsPolyT (Stepped.ofFun chkF) := IsPolyT.ofFun chkF_polyT
  have : IsPolyT (checkS O) := IsPolyT.bind
  exact ⟨IsPolyT.bind⟩

theorem decS_poly : Nonempty (IsPolyT (decS O)) := by
  have : IsPolyT (Stepped.ofFun decF) := IsPolyT.ofFun decF_polyT
  exact ⟨IsPolyT.bind⟩

theorem apexS_poly : Nonempty (IsPolyT (Stepped.mapIn apexW O)) := ⟨IsPolyT.mapIn apexW_polyT⟩

end Poly

/-! ## The words of graphs -/

section Graphs

open EthFollowup.Hamiltonian

variable {n : ℕ}

theorem bits_eq_nil_iff (k : ℕ) : Nat.bits k = [] ↔ k = 0 := by
  constructor
  · intro h
    have : (Nat.bits k).length = 0 := by rw [h]; rfl
    rw [Nat.size_eq_bits_len] at this
    exact Nat.size_eq_zero.1 this
  · rintro rfl; exact Nat.zero_bits

theorem length_eq_zero_iff' {w : List Bool} : w.length = 0 ↔ w = [] :=
  ⟨fun h => by cases w with | nil => rfl | cons _ _ => simp at h, fun h => by rw [h]; rfl⟩

theorem delM_matrix (H : SimpleGraph (Fin n)) (k : ℕ) :
    delM n (matrix H) k = matrix (H.deleteEdges (delSet n k)) := by
  unfold delM
  conv_rhs => rw [GraphProblems.matrix]
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  refine List.flatMap_congr fun u _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun w _ => ?_
  simp only [Function.comp_apply]
  rw [Bool.eq_iff_iff]
  have hA := stAdj n H u w
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
    decide_eq_true_eq, SimpleGraph.deleteEdges_adj, mem_delSet, hA, not_or]

theorem candW_eq (H : SimpleGraph (Fin n)) (a : Asm.GIn) (ha : a.1.length = n) (k : ℕ) :
    candW (a, k, matrix H) = code (H.deleteEdges (delSet n k)) := by
  simp only [candW, ha, code, delM_matrix]

theorem chkW_eq (G H : SimpleGraph (Fin n)) : chkW (code G, matrix H) = code H := by
  simp only [chkW, code, GraphProblems.Read.ones_unary_append]

theorem size_matrix (H : SimpleGraph (Fin n)) : size (matrix H) = 2 * (n * n) + 1 := by
  rw [LabelSystem.size_word, stMatrixLength n H]

theorem size_code (H : SimpleGraph (Fin n)) : size (code H) = 2 * (n + 1 + n * n) + 1 := by
  rw [LabelSystem.size_word, length_code stMatrixLength]

theorem apex_adj_iff (G : SimpleGraph (Fin n)) (u w : Fin (n + 1)) :
    (apex G).Adj u w ↔ u ≠ w ∧ ((u : ℕ) = n ∨ (w : ℕ) = n ∨
      ∃ (hu : (u : ℕ) < n) (hw : (w : ℕ) < n), G.Adj ⟨u, hu⟩ ⟨w, hw⟩) := Iff.rfl

theorem apexM_matrix (G : SimpleGraph (Fin n)) : apexM n (matrix G) = matrix (apex G) := by
  unfold apexM
  conv_rhs => rw [GraphProblems.matrix]
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  refine List.flatMap_congr fun u _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun w _ => ?_
  simp only [Function.comp_apply]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not]
  rw [apex_adj_iff]
  by_cases hu : (u : ℕ) < n
  · by_cases hw : (w : ℕ) < n
    · have hA : adjB n (matrix G) u w = true ↔ G.Adj ⟨u, hu⟩ ⟨w, hw⟩ := stAdj n G ⟨u, hu⟩ ⟨w, hw⟩
      rw [hA]
      constructor
      · rintro (⟨-, h⟩ | ⟨-, h | h⟩)
        · refine ⟨fun e => G.ne_of_adj h (Fin.ext (by simp [e])), Or.inr (Or.inr ⟨hu, hw, h⟩)⟩
        · omega
        · omega
      · rintro ⟨-, h | h | ⟨_, _, h⟩⟩
        · omega
        · omega
        · exact Or.inl ⟨⟨hu, hw⟩, h⟩
    · have hn' : (u : ℕ) = n ∨ (w : ℕ) = n := by omega
      constructor
      · rintro (⟨⟨_, _⟩, _⟩ | ⟨hne, -⟩)
        · omega
        · exact ⟨fun e => hne (by rw [e]), Or.imp_right Or.inl hn'⟩
      · rintro ⟨hne, -⟩
        exact Or.inr ⟨fun e => hne (Fin.ext e), hn'⟩
  · have hn' : (u : ℕ) = n ∨ (w : ℕ) = n := by omega
    constructor
    · rintro (⟨⟨_, _⟩, _⟩ | ⟨hne, -⟩)
      · omega
      · exact ⟨fun e => hne (by rw [e]), Or.imp_right Or.inl hn'⟩
    · rintro ⟨hne, -⟩
      exact Or.inr ⟨fun e => hne (Fin.ext e), hn'⟩

theorem apexW_code (G : SimpleGraph (Fin n)) : apexW (code G) = code (apex G) := by
  simp only [apexW, code, GraphProblems.Read.ones_unary_append, GraphProblems.Read.rest_unary_append,
    apexM_matrix]

theorem card_hc_eq_zero_iff (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    (hamCycles H).card = 0 ↔ ¬∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ H.edgeSet ∧
      (TwoRegular X ∧ (graphOf X).Connected) := by
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  simp only [mem_hamCycles_iff_sub, not_exists, not_and]
  refine forall_congr' fun X => ?_
  rw [← SimpleGraph.coe_edgeFinset, Finset.coe_subset]

theorem card_hp_eq_zero_iff (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    (hamPaths H).card = 0 ↔ ¬∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ H.edgeSet ∧
      IsHamPath X := by
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  simp only [mem_hamPaths, not_exists, not_and]
  refine forall_congr' fun X => ?_
  rw [← SimpleGraph.coe_edgeFinset, Finset.coe_subset]

theorem mem_hc_iff {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {X : Finset (Sym2 (Fin n))} :
    X ∈ hamCycles G ↔ (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ (TwoRegular X ∧ (graphOf X).Connected) := by
  rw [mem_hamCycles_iff_sub, ← SimpleGraph.coe_edgeFinset, Finset.coe_subset]

theorem mem_hp_iff {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {X : Finset (Sym2 (Fin n))} :
    X ∈ hamPaths G ↔ (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ IsHamPath X := by
  rw [mem_hamPaths, ← SimpleGraph.coe_edgeFinset, Finset.coe_subset]

end Graphs

/-! ## The runs -/

section Runs

open EthFollowup.Hamiltonian

variable (O : Stepped (List Bool) (List Bool))

/-- **The decision machine**: one call of `O`, two more steps. -/
theorem decS_runs {x : List Bool} {T S : ℕ} {w : List Bool} (h : O.Runs x T S w) :
    (decS O).Runs x (T + 2) (size x + S + size w + 4) [decide (w.length ≠ 0)] := by
  have := Stepped.bind_runs h (Stepped.ofFun_runs decF (x, w))
  refine this.mono (by omega) ?_
  simp only [decF, size_prod, size_list, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, size_bool]
  simp only [max_def]; split_ifs <;> omega

variable {n : ℕ}

/-- **The search machine**, for an oracle `O` that answers, on every subgraph `H` of `G`, within
`To` steps on states of size `≤ So`, with a non-empty word iff `H` has an edge set with `Q`. -/
theorem searchS_runs (G : SimpleGraph (Fin n)) (Q : Finset (Sym2 (Fin n)) → Prop) (To So : ℕ)
    (hO : ∀ H : SimpleGraph (Fin n), H ≤ G → ∃ T w, O.Runs (code H) T So w ∧ T ≤ To ∧ size w ≤ So ∧
      (w = [] ↔ ¬∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ H.edgeSet ∧ Q X)) :
    ∃ T w, (searchS O).Runs (code G) T (So + 30 * (n * n) + 10 * n + 40) w ∧ T ≤ (n * n + 1) * (To + 3) ∧
      ((¬∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ Q X) → w = []) ∧
      ((∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ Q X) →
        ∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ Q X ∧ w = matrix (graphOf X)) := by
  set Hs : ℕ → SimpleGraph (Fin n) := srSeq (ofFin Q) G (delSet n) with hHs
  set cs : ℕ → List Bool := fun y => matrix (Hs y) with hcs
  have hle : ∀ y, (Hs y).deleteEdges (delSet n y) ≤ G := fun y =>
    ((Hs y).deleteEdges_le _).trans (srSeq_le y)
  choose tO wO hrun htO hsz hw using fun y => hO _ (hle y)
  -- one step
  have hbody : ∀ y < (Asm.aOf G).1.length * (Asm.aOf G).1.length,
      (bodyS O).Runs (Asm.aOf G, y, cs y) (tO y + 1 + 1) (So + 5 * (n * n) + 2 * n + 6) (cs (y + 1)) := by
    intro y hy
    rw [Asm.aOf_len] at hy
    have h1 : (Stepped.mapIn candW O).Runs (Asm.aOf G, y, cs y) (tO y) So (wO y) :=
      Stepped.mapIn_runs (by rw [hcs]; simp only; rw [candW_eq _ _ (Asm.aOf_len G)]; exact hrun y)
    have hval : keepF ((Asm.aOf G, y, cs y), wO y) = cs (y + 1) := by
      simp only [keepF, hcs, Asm.aOf_len, delM_matrix]
      rw [show Hs (y + 1) = srStep (ofFin Q) (Hs y) (delSet n y) from srSeq_succ y]
      by_cases h : wO y = []
      · rw [if_pos (by rw [h]; rfl), srStep_neg]
        rw [exists_ofFin_iff]; exact (hw y).1 h
      · rw [if_neg (fun h' => h (length_eq_zero_iff'.1 h')), srStep_pos]
        rw [exists_ofFin_iff]; exact not_not.1 (fun h' => h ((hw y).2 h'))
    have h2 := Stepped.ofFun_runs keepF ((Asm.aOf G, y, cs y), wO y)
    rw [hval] at h2
    refine (Stepped.bind_runs h1 h2).mono le_rfl ?_
    have hy1 : size y ≤ (n * n) := (Asm.size_nat_le' y).trans (by omega)
    have e1 : size (Asm.aOf G, y, cs y) = (2 * n + 1) + (2 * (n * n) + 1) + (size y + (2 * (n * n) + 1)) := by
      change size (Asm.aOf G) + (size y + size (matrix (Hs y))) = _
      rw [Asm.size_aOf, size_matrix]
    have e2 : size (cs (y + 1)) = 2 * (n * n) + 1 := size_matrix _
    have e3 : size ((Asm.aOf G, y, cs y), wO y) = size (Asm.aOf G, y, cs y) + size (wO y) := rfl
    have := hsz y
    rw [e3, e2, e1]
    simp only [max_def]; split_ifs <;> omega
  -- the loop
  have hloop := iterRange_runs (N := fun a : Asm.GIn => a.1.length * a.1.length) (M := bodyS O)
    (c₀ := fun a => a.2) (Asm.aOf G) cs rfl (fun y => tO y + 1 + 1) (2 * (n * n) + 1)
    (So + 5 * (n * n) + 2 * n + 6) hbody (fun y _ => (size_matrix _).le)
  simp only [Asm.aOf_len] at hloop
  have hL : (Stepped.mapIn read1 (loopS O)).Runs (code G) _ _ (cs (n * n)) :=
    Stepped.mapIn_runs (by rw [Asm.read1_code]; exact hloop)
  -- the final check
  have hF0 := hO (Hs (n * n)) (srSeq_le (n * n))
  obtain ⟨tF, wF, hrF, htF, hszF, hwF⟩ := hF0
  have hc1 : (Stepped.mapIn chkW O).Runs (code G, cs (n * n)) tF So wF :=
    Stepped.mapIn_runs (by rw [hcs]; simp only; rw [chkW_eq]; exact hrF)
  have hc2 := Stepped.ofFun_runs chkF ((code G, cs (n * n)), wF)
  have hC := Stepped.bind_runs hc1 hc2
  have hall := Stepped.bind_runs hL hC
  refine ⟨_, _, hall.mono le_rfl ?_, ?_, ?_, ?_⟩
  · -- the states
    have e1 : size (code G) = 2 * (n + 1 + (n * n)) + 1 := size_code G
    have e2 : size (cs (n * n)) = 2 * (n * n) + 1 := size_matrix _
    have e3 : size ((n * n)) ≤ (n * n) + 1 := Asm.size_nat_le' _
    have e4 : size (chkF ((code G, cs (n * n)), wF)) ≤ 2 * (n * n) + 1 := by
      unfold chkF; split_ifs
      · simp
      · exact e2.le
    have e5 : size ((code G, cs (n * n)), wF) = size (code G) + size (cs (n * n)) + size wF := rfl
    have e6 : size (code G, cs (n * n)) = size (code G) + size (cs (n * n)) := rfl
    have e7 : size (Asm.aOf G) = (2 * n + 1) + (2 * (n * n) + 1) := Asm.size_aOf G
    rw [e5, e6, e7] at *
    rw [e1, e2] at *
    simp only [max_def]; split_ifs <;> omega
  · -- the steps
    have hsum : ∑ y ∈ range (n * n), (tO y + 1 + 1 + 1) ≤ (n * n) * (To + 3) := by
      have := Finset.sum_le_sum (s := range (n * n)) (f := fun y => tO y + 1 + 1 + 1) (g := fun _ => To + 3)
        (fun y _ => by have := htO y; omega)
      simpa [sum_const, card_range, smul_eq_mul] using this
    have : ((n * n) + 1) * (To + 3) = (n * n) * (To + 3) + (To + 3) := by ring
    omega
  · -- no edge set with `Q`: the empty word
    intro hno
    have : wF = [] := (hwF).2 fun ⟨X, hX, hQ⟩ =>
      hno ⟨X, hX.trans (SimpleGraph.edgeSet_subset_edgeSet.2 (srSeq_le (n * n))), hQ⟩
    simp [chkF, this]
  · -- an edge set with `Q`: the matrix of the final graph
    intro hyes
    obtain ⟨X, hXG, hQX, hF⟩ := srSeq_final hyes (cover_delSet G) (K := (n * n))
    have hne : wF ≠ [] := fun h => (hwF.1 h)
      (exists_ofFin_iff.1 (srSeq_inv (exists_ofFin_iff.2 hyes) (n * n)))
    refine ⟨X, hXG, hQX, ?_⟩
    simp only [chkF, if_neg (fun h' => hne (length_eq_zero_iff'.1 h')), hcs]
    rw [← hF]

end Runs

end Srch

end EthFollowup.ExactHC
