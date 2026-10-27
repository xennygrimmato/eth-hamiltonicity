/-
# Parity of Hamiltonian cycles via the ETH-refuting #k-SAT machine

Cut&Count (Cygan, Nederlof, Pilipczuk, Pilipczuk, van Rooij, Wojtaszczyk, FOCS 2011) expresses
connectivity *modulo two* with local constraints. We build, for a graph `G` on `Fin n` and a root
vertex `r`, a CNF `cutCNF G r` on the variables `E(G) ⊕ V(G)`:

* every vertex has exactly two selected incident edges;
* a selected edge `uw` forces its endpoints to the same side of a cut `c : V → Bool`;
* the root is on side `false`.

Its models are pairs `(X, c)` with `X` a 2-factor (spanning 2-regular edge set) and `c` a cut
consistent with `X`. A disconnected `X` has an even number of consistent rooted cuts (flip a
component that avoids the root); a connected one has exactly one. Hence

  `#cutCNF G r ≡ #{Hamiltonian cycles of G}  (mod 2)`          (`count_cutCNF_mod_two`)

where a Hamiltonian cycle is a connected spanning 2-regular edge set (`hamCycles`). The CNF has
`|E| + n` variables and width `max Δ 3`, so the comparator theorem of openai/math at
`k = max Δ 3` gives a single machine computing the parity of the number of Hamiltonian cycles of
every graph of maximum degree `≤ Δ` in time `C (L+1)^d 2^{A ρ(|E|+n)}` and polynomial space
(`hamParity_subexponential`). The machine theorem is conditional on that upstream statement,
passed as a hypothesis; everything else here is proved outright.
-/
import EthFollowup.CNFKit

namespace EthFollowup.Hamiltonian

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open EthFollowup

section Graphs

variable {n : ℕ}

/-! ### Combinatorial objects -/

/-- Every vertex meets exactly two edges of `X`. -/
def TwoRegular (X : Finset (Sym2 (Fin n))) : Prop :=
  ∀ v : Fin n, (X.filter fun e => v ∈ e).card = 2

instance (X : Finset (Sym2 (Fin n))) : Decidable (TwoRegular X) := by
  unfold TwoRegular; infer_instance

/-- A cut `c` is consistent with `X` if no edge of `X` crosses it. -/
def Consistent (X : Finset (Sym2 (Fin n))) (c : Fin n → Bool) : Prop :=
  ∀ u w : Fin n, s(u, w) ∈ X → c u = c w

instance (X : Finset (Sym2 (Fin n))) (c : Fin n → Bool) : Decidable (Consistent X c) := by
  unfold Consistent; infer_instance

/-- The graph on `Fin n` whose edges are `X`. -/
abbrev graphOf (X : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (X : Set (Sym2 (Fin n)))

instance (X : Finset (Sym2 (Fin n))) : DecidableRel (graphOf X).Adj := fun u w =>
  decidable_of_iff (s(u, w) ∈ X ∧ u ≠ w) (by simp [SimpleGraph.fromEdgeSet_adj])

/-- Consistent cuts with the root on side `false`. -/
def cuts (X : Finset (Sym2 (Fin n))) (r : Fin n) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun c => Consistent X c ∧ c r = false

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- 2-factors of `G`: spanning 2-regular edge subsets. -/
def twoFactors : Finset (Finset (Sym2 (Fin n))) :=
  G.edgeFinset.powerset.filter TwoRegular

/-- Hamiltonian cycles of `G`, as edge sets: connected spanning 2-regular subgraphs. -/
def hamCycles : Finset (Finset (Sym2 (Fin n))) :=
  (twoFactors G).filter fun X => (graphOf X).Connected

/-! ### The Cut&Count CNF -/

/-- Edge variables. -/
abbrev EdgeVar := {e : Sym2 (Fin n) // e ∈ G.edgeFinset}

/-- All variables: one per edge, one per vertex. -/
abbrev Var := EdgeVar G ⊕ Fin n

theorem card_var : Fintype.card (Var G) = G.edgeFinset.card + n := by
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]

/-- Edge variables at a vertex. -/
def incidentScope (v : Fin n) : Finset (Var G) :=
  (Finset.univ.filter fun e : EdgeVar G => v ∈ (e : Sym2 (Fin n))).map
    ⟨Sum.inl, Sum.inl_injective⟩

/-- Ordered adjacent pairs. -/
def adjPairs : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => G.Adj p.1 p.2

/-- The edge variable of an adjacent pair. -/
def edgeVarOf (p : {p // p ∈ adjPairs G}) : EdgeVar G :=
  ⟨s(p.1.1, p.1.2), by
    have := p.2
    simp only [adjPairs, Finset.mem_filter, Finset.mem_univ, true_and] at this
    simpa using this⟩

def vertexCNF (v : Fin n) : SAT.CNF (Var G) :=
  constraintCNF (incidentScope G v) fun T => T.card = 2

def edgeScope (p : {p // p ∈ adjPairs G}) : Finset (Var G) :=
  {Sum.inl (edgeVarOf G p), Sum.inr p.1.1, Sum.inr p.1.2}

def edgeCNF (p : {p // p ∈ adjPairs G}) : SAT.CNF (Var G) :=
  constraintCNF (edgeScope G p) fun T =>
    Sum.inl (edgeVarOf G p) ∈ T → (Sum.inr p.1.1 ∈ T ↔ Sum.inr p.1.2 ∈ T)

def rootCNF (r : Fin n) : SAT.CNF (Var G) :=
  constraintCNF {Sum.inr r} fun T => T = ∅

/-- The Cut&Count formula of `G` rooted at `r`. -/
def cutCNF (r : Fin n) : SAT.CNF (Var G) :=
  rootCNF G r ∪ (Finset.univ.biUnion (vertexCNF G)) ∪
    ((adjPairs G).attach.biUnion (edgeCNF G))

/-! ### Semantics -/

/-- Selected edges of an assignment. -/
def edgesOf (a : SAT.Assignment (Var G)) : Finset (Sym2 (Fin n)) :=
  (Finset.univ.filter fun e : EdgeVar G => a (Sum.inl e) = true).map
    (Function.Embedding.subtype _)

/-- The cut of an assignment. -/
def cutOf (a : SAT.Assignment (Var G)) : Fin n → Bool := fun v => a (Sum.inr v)

theorem mem_edgesOf (a : SAT.Assignment (Var G)) (e : Sym2 (Fin n)) :
    e ∈ edgesOf G a ↔ ∃ h : e ∈ G.edgeFinset, a (Sum.inl ⟨e, h⟩) = true := by
  simp [edgesOf]

theorem edgesOf_subset (a : SAT.Assignment (Var G)) : edgesOf G a ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨h, -⟩ := (mem_edgesOf G a e).1 he
  exact h

theorem incident_filter_card (a : SAT.Assignment (Var G)) (v : Fin n) :
    ((incidentScope G v).filter fun x => a x = true).card =
      ((edgesOf G a).filter fun e => v ∈ e).card := by
  refine Finset.card_bij' (fun x _ => Sum.elim (fun e : EdgeVar G => (e : Sym2 (Fin n)))
      (fun _ => s(v, v)) x)
    (fun e he => Sum.inl ⟨e, edgesOf_subset G a (Finset.mem_filter.1 he).1⟩) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [incidentScope, Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hx
    obtain ⟨⟨e, hev, rfl⟩, ha⟩ := hx
    simp only [Sum.elim_inl, Finset.mem_filter, mem_edgesOf]
    exact ⟨⟨e.2, ha⟩, hev⟩
  · intro e he
    simp only [Finset.mem_filter, mem_edgesOf] at he
    obtain ⟨⟨h, ha⟩, hv⟩ := he
    simp only [incidentScope, Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    exact ⟨⟨⟨e, h⟩, hv, rfl⟩, ha⟩
  · intro x hx
    simp only [incidentScope, Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hx
    obtain ⟨⟨e, -, rfl⟩, -⟩ := hx
    rfl
  · intro e _
    rfl

theorem vertexCNF_eval (a : SAT.Assignment (Var G)) (v : Fin n) :
    SAT.CNF.eval a (vertexCNF G v) = true ↔ ((edgesOf G a).filter fun e => v ∈ e).card = 2 := by
  rw [vertexCNF, constraintCNF_eval, incident_filter_card]

theorem edgeCNF_eval (a : SAT.Assignment (Var G)) (p : {p // p ∈ adjPairs G}) :
    SAT.CNF.eval a (edgeCNF G p) = true ↔
      (a (Sum.inl (edgeVarOf G p)) = true → cutOf G a p.1.1 = cutOf G a p.1.2) := by
  rw [edgeCNF, constraintCNF_eval]
  simp only [edgeScope, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, true_or,
    or_true, true_and, cutOf]
  constructor
  · intro h ha
    have := h ha
    cases h1 : a (Sum.inr p.1.1) <;> cases h2 : a (Sum.inr p.1.2) <;> simp_all
  · intro h ha
    rw [h ha]

theorem rootCNF_eval (a : SAT.Assignment (Var G)) (r : Fin n) :
    SAT.CNF.eval a (rootCNF G r) = true ↔ cutOf G a r = false := by
  rw [rootCNF, constraintCNF_eval, Finset.filter_singleton]
  cases h : a (Sum.inr r) <;> simp [cutOf, h]

theorem edges_consistent_iff (a : SAT.Assignment (Var G)) :
    (∀ p ∈ (adjPairs G).attach, SAT.CNF.eval a (edgeCNF G p) = true) ↔
      Consistent (edgesOf G a) (cutOf G a) := by
  constructor
  · intro h u w huw
    obtain ⟨hmem, ha⟩ := (mem_edgesOf G a _).1 huw
    have hadj : G.Adj u w := by simpa using hmem
    have hp : (u, w) ∈ adjPairs G := by simp [adjPairs, hadj]
    exact (edgeCNF_eval G a ⟨(u, w), hp⟩).1 (h _ (Finset.mem_attach _ _)) ha
  · intro h p _
    rw [edgeCNF_eval]
    intro ha
    apply h
    exact (mem_edgesOf G a _).2 ⟨(edgeVarOf G p).2, ha⟩

theorem cutCNF_eval (r : Fin n) (a : SAT.Assignment (Var G)) :
    SAT.CNF.eval a (cutCNF G r) = true ↔
      TwoRegular (edgesOf G a) ∧ Consistent (edgesOf G a) (cutOf G a) ∧ cutOf G a r = false := by
  rw [cutCNF, CNF.eval_union, CNF.eval_union, CNF.eval_biUnion, CNF.eval_biUnion,
    edges_consistent_iff, rootCNF_eval]
  simp only [Finset.mem_univ, true_implies, vertexCNF_eval, TwoRegular]
  tauto

/-! ### Counting: models are (2-factor, rooted consistent cut) pairs -/

theorem count_cutCNF (r : Fin n) :
    SAT.count (cutCNF G r) = ∑ X ∈ twoFactors G, (cuts X r).card := by
  classical
  unfold SAT.count SAT.satisfyingAssignments
  rw [Finset.card_eq_sum_card_fiberwise (f := edgesOf G) (t := twoFactors G)]
  · refine Finset.sum_congr rfl fun X hX => ?_
    have hXsub : X ⊆ G.edgeFinset := Finset.mem_powerset.1 (Finset.mem_filter.1 hX).1
    have hXreg : TwoRegular X := (Finset.mem_filter.1 hX).2
    refine Finset.card_bij' (fun a _ => cutOf G a)
      (fun c _ => Sum.elim (fun e : EdgeVar G => decide ((e : Sym2 (Fin n)) ∈ X)) c)
      ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨hsat, rfl⟩ := ha
      obtain ⟨-, hcons, hroot⟩ := (cutCNF_eval G r a).1 hsat
      simp [cuts, hcons, hroot]
    · intro c hc
      simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      have hE : edgesOf G (Sum.elim (fun e : EdgeVar G => decide ((e : Sym2 (Fin n)) ∈ X)) c) =
          X := by
        ext e
        rw [mem_edgesOf]
        simp only [Sum.elim_inl, decide_eq_true_eq]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hXsub h, h⟩⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(cutCNF_eval G r _).2 ?_, hE⟩
      rw [hE]
      exact ⟨hXreg, hc.1, hc.2⟩
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨-, hX⟩ := ha
      funext x
      rcases x with e | v
      · simp only [Sum.elim_inl]
        rw [← hX]
        cases h : a (Sum.inl e)
        · simp only [decide_eq_false_iff_not, mem_edgesOf, not_exists]
          intro _ h'
          simp_all
        · simp only [decide_eq_true_eq, mem_edgesOf]
          exact ⟨e.2, h⟩
      · rfl
    · intro c _
      rfl
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
    obtain ⟨hreg, -, -⟩ := (cutCNF_eval G r a).1 ha
    simp only [twoFactors, Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq]
    exact ⟨edgesOf_subset G a, hreg⟩

end Graphs

/-! ### Parity of the number of consistent cuts -/

section Parity

variable {n : ℕ}

theorem consistent_of_reachable {X : Finset (Sym2 (Fin n))} {c : Fin n → Bool}
    (hc : Consistent X c) {u w : Fin n} (h : (graphOf X).Reachable u w) : c u = c w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hadj ih =>
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    exact ih.trans (hc _ _ (by simpa using hadj.1))

theorem cuts_card_of_connected {X : Finset (Sym2 (Fin n))} (r : Fin n)
    (hX : (graphOf X).Connected) : (cuts X r).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun _ => false, ?_⟩
  ext c
  simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hr⟩
    funext v
    rw [← hr]
    exact (consistent_of_reachable hc (hX.preconnected r v)).symm
  · rintro rfl
    exact ⟨fun _ _ _ => rfl, rfl⟩

/-- Flip the side of every vertex reachable from `v`. -/
def flip (X : Finset (Sym2 (Fin n))) (v : Fin n) (c : Fin n → Bool) : Fin n → Bool :=
  fun x => if (graphOf X).Reachable v x then !c x else c x

theorem cuts_even_of_not_connected {X : Finset (Sym2 (Fin n))} (r : Fin n)
    (hX : ¬ (graphOf X).Connected) : ((cuts X r).card : ZMod 2) = 0 := by
  have hv : ∃ v, ¬ (graphOf X).Reachable r v := by
    by_contra hall
    push_neg at hall
    apply hX
    rw [SimpleGraph.connected_iff]
    exact ⟨fun a b => (hall a).symm.trans (hall b), ⟨r⟩⟩
  obtain ⟨v, hv⟩ := hv
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_involution (fun c _ => flip X v c) ?_ ?_ ?_ ?_
  · intro _ _; decide
  · intro c _ _ hfix
    have := congrFun hfix v
    simp [flip, SimpleGraph.Reachable.refl] at this
  · intro c hc
    simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    refine ⟨fun u w huw => ?_, ?_⟩
    · have hcu := hc.1 u w huw
      by_cases huw' : u = w
      · subst huw'; rfl
      · have hadj : (graphOf X).Adj u w := by
          rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨huw, huw'⟩
        have hiff : (graphOf X).Reachable v u ↔ (graphOf X).Reachable v w :=
          ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.reachable.symm⟩
        simp only [flip, hiff, hcu]
    · have : ¬ (graphOf X).Reachable v r := fun h => hv h.symm
      simp [flip, this, hc.2]
  · intro c _
    funext x
    simp only [flip]
    split_ifs <;> simp

theorem cuts_card_mod_two (X : Finset (Sym2 (Fin n))) (r : Fin n) :
    ((cuts X r).card : ZMod 2) = if (graphOf X).Connected then 1 else 0 := by
  split_ifs with h
  · rw [cuts_card_of_connected r h]; rfl
  · exact cuts_even_of_not_connected r h

end Parity

/-! ### Main identity -/

section Main

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- **Cut&Count parity identity.** The model count of the Cut&Count CNF has the parity of the
number of Hamiltonian cycles. -/
theorem count_cutCNF_mod_two (r : Fin n) :
    (SAT.count (cutCNF G r) : ZMod 2) = ((hamCycles G).card : ZMod 2) := by
  rw [count_cutCNF, Nat.cast_sum]
  simp_rw [cuts_card_mod_two]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rfl

theorem incidentScope_card (v : Fin n) : (incidentScope G v).card = G.degree v := by
  rw [incidentScope, Finset.card_map, ← SimpleGraph.card_incidenceFinset_eq_degree]
  refine Finset.card_bij' (fun e _ => (e : Sym2 (Fin n)))
    (fun e he => ⟨e, ?_⟩) ?_ ?_ ?_ ?_
  · rw [SimpleGraph.mem_incidenceFinset] at he
    exact SimpleGraph.mem_edgeFinset.2 he.1
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨SimpleGraph.mem_edgeFinset.1 e.2, he⟩
  · intro e he
    rw [SimpleGraph.mem_incidenceFinset] at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact he.2
  · intro e _; rfl
  · intro e _; rfl

theorem cutCNF_width (r : Fin n) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) :
    SAT.WidthAtMost (max Δ 3) (cutCNF G r) := by
  refine width_union (width_union ?_ ?_) ?_
  · exact constraintCNF_width _ _ (by simp)
  · refine width_biUnion fun v _ => constraintCNF_width _ _ ?_
    rw [incidentScope_card]
    exact (hΔ v).trans (le_max_left _ _)
  · refine width_biUnion fun p _ => constraintCNF_width _ _ ?_
    exact Finset.card_le_three.trans (le_max_right _ _)

/-- The Cut&Count CNF on variables `Fin (|E| + n)`, the input format of the comparator.
(`noncomputable` only because Lean's `Fintype.equivFin` is; the relabeling is an explicit
enumeration of edges and vertices in any concrete implementation.) -/
noncomputable def cutCNFFin (r : Fin n) : SAT.CNF (Fin (Fintype.card (Var G))) :=
  CNF.relabel (Fintype.equivFin (Var G)) (cutCNF G r)

theorem count_cutCNFFin_mod_two (r : Fin n) :
    (SAT.count (cutCNFFin G r) : ZMod 2) = ((hamCycles G).card : ZMod 2) := by
  rw [cutCNFFin, CNF.relabel_count, count_cutCNF_mod_two]

end Main

/-! ### The machine -/

/-- **Parity of Hamiltonian cycles in subexponential time and polynomial space**, conditional on
openai/math's `exact_count_and_sat` at width `max Δ 3` (passed as `h`). One fixed machine, run on
the canonical encoding of `cutCNFFin G r` (which has `|E(G)| + n` variables), halts with a number
`N` on its count tape whose parity is the parity of the number of Hamiltonian cycles of `G`, for
every graph `G` of maximum degree `≤ Δ`, within the comparator's time bound in the variable count
`|E(G)| + n ≤ (1 + Δ/2) n`, and with polynomial visited space at every prefix. -/
theorem hamParity_subexponential (Δ : ℕ)
    (h : ExactCountAndSatStatement (max Δ 3) (le_max_of_le_right (by norm_num))) :
    ∃ (machine : Computation.PrimitiveMachine)
      (countTape : Fin machine.tapeCount) (C A S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : Fin n),
        (∀ v, G.degree v ≤ Δ) →
        ∃ (N time : ℕ) (final : LocatedCfg machine),
          Computation.Trace (locatedStep machine) time
            (locatedInit machine (Encoding.encodeCNF (cutCNFFin G r))) final ∧
          final.config.tapes countTape = Turing.Tape.mk₁ ((countWord N).map some) ∧
          BinaryArithmetic.toNat (countWord N) = N ∧
          (N : ZMod 2) = ((hamCycles G).card : ZMod 2) ∧
          Fintype.card (Var G) = G.edgeFinset.card + n ∧
          (time : ℝ) ≤ SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength (cutCNFFin G r)) (Fintype.card (Var G)) ∧
          ∀ (prefixSteps : ℕ) (intermediate : LocatedCfg machine),
            prefixSteps ≤ time →
            Computation.Trace (locatedStep machine) prefixSteps
              (locatedInit machine (Encoding.encodeCNF (cutCNFFin G r))) intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength (cutCNFFin G r) : ℝ) + 1) ^ e := by
  obtain ⟨machine, countTape, _answerTape, C, A, S, d, e, hC, hA, hS, hd, he, hrun⟩ := h
  refine ⟨machine, countTape, C, A, S, d, e, hC, hA, hS, hd, he, ?_⟩
  intro n G _ r hΔ
  have hw : SAT.WidthAtMost (max Δ 3) (cutCNFFin G r) :=
    CNF.relabel_width _ (cutCNF_width G r hΔ)
  obtain ⟨time, final, htrace, hcount, -, -, hdecode, -, htime, hspace⟩ :=
    hrun (Fintype.card (Var G)) (cutCNFFin G r) hw
  exact ⟨SAT.count (cutCNFFin G r), time, final, htrace, hcount, hdecode,
    count_cutCNFFin_mod_two G r, card_var G, htime, hspace⟩

end EthFollowup.Hamiltonian
