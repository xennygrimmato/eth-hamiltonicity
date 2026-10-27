/-
# Parity of directed Hamiltonian cycles

Directed analogue of `HamiltonianParity.lean`. A digraph is a finite set `A` of arcs
`(u, w) : Fin n × Fin n`. A loop, if present, can be selected by a cycle cover but then isolates
its vertex, so for `n ≥ 2` it never occurs in a connected cycle cover. Variables: one per arc and
one per vertex.
Constraints: every vertex has exactly one selected out-arc and exactly one selected in-arc; a
selected arc forces its endpoints to the same side of the cut; the root is on side `false`.

Models are pairs (cycle cover `X`, rooted cut consistent with `X`), and the parity lemma
`cuts_card_mod_two` from the undirected file applies to the underlying undirected edge set of `X`.
Hence `#dirCutCNF A r ≡ #{connected cycle covers} = #{directed Hamiltonian cycles} (mod 2)`.

Björklund and Husfeldt (FOCS 2013) compute this parity in `O(1.619^n)` for general digraphs; for
digraphs of maximum in- and out-degree `Δ` the comparator theorem gives
`C (L+1)^d 2^{A ρ(|A|+n)}`.
-/
import EthFollowup.HamiltonianParity

namespace EthFollowup.DirectedHamiltonian

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open EthFollowup EthFollowup.Hamiltonian

variable {n : ℕ} (A : Finset (Fin n × Fin n))

/-! ### Objects -/

/-- Every vertex has exactly one selected out-arc and one selected in-arc. -/
def CycleCover (X : Finset (Fin n × Fin n)) : Prop :=
  ∀ v : Fin n, (X.filter fun a => a.1 = v).card = 1 ∧ (X.filter fun a => a.2 = v).card = 1

instance (X : Finset (Fin n × Fin n)) : Decidable (CycleCover X) := by
  unfold CycleCover; infer_instance

/-- The underlying undirected edge set. -/
def undirected (X : Finset (Fin n × Fin n)) : Finset (Sym2 (Fin n)) :=
  X.image fun a => s(a.1, a.2)

def cycleCovers : Finset (Finset (Fin n × Fin n)) := A.powerset.filter CycleCover

/-- Directed Hamiltonian cycles: cycle covers whose underlying graph is connected. -/
def dirHamCycles : Finset (Finset (Fin n × Fin n)) :=
  (cycleCovers A).filter fun X => (graphOf (undirected X)).Connected

/-! ### CNF -/

abbrev ArcVar := {a : Fin n × Fin n // a ∈ A}
abbrev DVar := ArcVar A ⊕ Fin n

theorem card_dvar : Fintype.card (DVar A) = A.card + n := by
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]

def outScope (v : Fin n) : Finset (DVar A) :=
  (Finset.univ.filter fun a : ArcVar A => (a : Fin n × Fin n).1 = v).map
    ⟨Sum.inl, Sum.inl_injective⟩

def inScope (v : Fin n) : Finset (DVar A) :=
  (Finset.univ.filter fun a : ArcVar A => (a : Fin n × Fin n).2 = v).map
    ⟨Sum.inl, Sum.inl_injective⟩

def degCNF (v : Fin n) : SAT.CNF (DVar A) :=
  constraintCNF (outScope A v) (fun T => T.card = 1) ∪
    constraintCNF (inScope A v) (fun T => T.card = 1)

def arcScope (a : ArcVar A) : Finset (DVar A) :=
  {Sum.inl a, Sum.inr (a : Fin n × Fin n).1, Sum.inr (a : Fin n × Fin n).2}

def arcCNF (a : ArcVar A) : SAT.CNF (DVar A) :=
  constraintCNF (arcScope A a) fun T =>
    Sum.inl a ∈ T → (Sum.inr (a : Fin n × Fin n).1 ∈ T ↔ Sum.inr (a : Fin n × Fin n).2 ∈ T)

def rootCNF (r : Fin n) : SAT.CNF (DVar A) :=
  constraintCNF {Sum.inr r} fun T => T = ∅

def dirCutCNF (r : Fin n) : SAT.CNF (DVar A) :=
  rootCNF A r ∪ Finset.univ.biUnion (degCNF A) ∪ Finset.univ.biUnion (arcCNF A)

/-! ### Semantics -/

def arcsOf (a : SAT.Assignment (DVar A)) : Finset (Fin n × Fin n) :=
  (Finset.univ.filter fun e : ArcVar A => a (Sum.inl e) = true).map
    (Function.Embedding.subtype _)

def cutOf (a : SAT.Assignment (DVar A)) : Fin n → Bool := fun v => a (Sum.inr v)

theorem mem_arcsOf (a : SAT.Assignment (DVar A)) (e : Fin n × Fin n) :
    e ∈ arcsOf A a ↔ ∃ h : e ∈ A, a (Sum.inl ⟨e, h⟩) = true := by
  simp [arcsOf]

theorem arcsOf_subset (a : SAT.Assignment (DVar A)) : arcsOf A a ⊆ A := by
  intro e he
  obtain ⟨h, -⟩ := (mem_arcsOf A a e).1 he
  exact h

theorem scope_filter_card (a : SAT.Assignment (DVar A)) (p : Fin n × Fin n → Prop)
    [DecidablePred p] :
    (((Finset.univ.filter fun e : ArcVar A => p e).map
        ⟨Sum.inl, Sum.inl_injective⟩).filter fun x => a x = true).card =
      ((arcsOf A a).filter p).card := by
  refine Finset.card_bij' (fun x _ => Sum.elim (fun e : ArcVar A => (e : Fin n × Fin n))
      (fun v => (v, v)) x)
    (fun e he => Sum.inl ⟨e, arcsOf_subset A a (Finset.mem_filter.1 he).1⟩) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hx
    obtain ⟨⟨e, hp, rfl⟩, ha⟩ := hx
    simp only [Sum.elim_inl, Finset.mem_filter, mem_arcsOf]
    exact ⟨⟨e.2, ha⟩, hp⟩
  · intro e he
    simp only [Finset.mem_filter, mem_arcsOf] at he
    obtain ⟨⟨h, ha⟩, hp⟩ := he
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    exact ⟨⟨⟨e, h⟩, hp, rfl⟩, ha⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hx
    obtain ⟨⟨e, -, rfl⟩, -⟩ := hx
    rfl
  · intro e _
    rfl

theorem degCNF_eval (a : SAT.Assignment (DVar A)) (v : Fin n) :
    SAT.CNF.eval a (degCNF A v) = true ↔
      ((arcsOf A a).filter fun e => e.1 = v).card = 1 ∧
        ((arcsOf A a).filter fun e => e.2 = v).card = 1 := by
  rw [degCNF, CNF.eval_union, constraintCNF_eval, constraintCNF_eval, outScope, inScope,
    scope_filter_card A a (fun e => e.1 = v), scope_filter_card A a (fun e => e.2 = v)]

theorem arcCNF_eval (a : SAT.Assignment (DVar A)) (e : ArcVar A) :
    SAT.CNF.eval a (arcCNF A e) = true ↔
      (a (Sum.inl e) = true → cutOf A a (e : Fin n × Fin n).1 = cutOf A a (e : Fin n × Fin n).2) := by
  rw [arcCNF, constraintCNF_eval]
  simp only [arcScope, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, true_or,
    or_true, true_and, cutOf]
  constructor
  · intro h ha
    have := h ha
    cases h1 : a (Sum.inr (e : Fin n × Fin n).1) <;>
      cases h2 : a (Sum.inr (e : Fin n × Fin n).2) <;> simp_all
  · intro h ha
    rw [h ha]

theorem rootCNF_eval (a : SAT.Assignment (DVar A)) (r : Fin n) :
    SAT.CNF.eval a (rootCNF A r) = true ↔ cutOf A a r = false := by
  rw [rootCNF, constraintCNF_eval, Finset.filter_singleton]
  cases h : a (Sum.inr r) <;> simp [cutOf, h]

theorem consistent_undirected_iff (X : Finset (Fin n × Fin n)) (c : Fin n → Bool) :
    Consistent (undirected X) c ↔ ∀ e ∈ X, c e.1 = c e.2 := by
  constructor
  · intro h e he
    exact h e.1 e.2 (Finset.mem_image.2 ⟨e, he, rfl⟩)
  · intro h u w huw
    obtain ⟨e, he, hEq⟩ := Finset.mem_image.1 huw
    rcases Sym2.eq_iff.1 hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact h e he
    · rw [← h1, ← h2]; exact (h e he).symm

theorem dirCutCNF_eval (r : Fin n) (a : SAT.Assignment (DVar A)) :
    SAT.CNF.eval a (dirCutCNF A r) = true ↔
      CycleCover (arcsOf A a) ∧ (∀ e ∈ arcsOf A a, cutOf A a e.1 = cutOf A a e.2) ∧
        cutOf A a r = false := by
  rw [dirCutCNF, CNF.eval_union, CNF.eval_union, CNF.eval_biUnion, CNF.eval_biUnion,
    rootCNF_eval]
  simp only [Finset.mem_univ, true_implies, degCNF_eval, arcCNF_eval, CycleCover]
  have harcs : (∀ e : ArcVar A, a (Sum.inl e) = true →
      cutOf A a (e : Fin n × Fin n).1 = cutOf A a (e : Fin n × Fin n).2) ↔
      ∀ e ∈ arcsOf A a, cutOf A a e.1 = cutOf A a e.2 := by
    constructor
    · intro h e he
      obtain ⟨hA, ha⟩ := (mem_arcsOf A a e).1 he
      exact h ⟨e, hA⟩ ha
    · intro h e ha
      exact h e ((mem_arcsOf A a e).2 ⟨e.2, ha⟩)
  rw [harcs]
  tauto

/-! ### Counting -/

theorem count_dirCutCNF (r : Fin n) :
    SAT.count (dirCutCNF A r) = ∑ X ∈ cycleCovers A, (cuts (undirected X) r).card := by
  classical
  unfold SAT.count SAT.satisfyingAssignments
  rw [Finset.card_eq_sum_card_fiberwise (f := arcsOf A) (t := cycleCovers A)]
  · refine Finset.sum_congr rfl fun X hX => ?_
    have hXsub : X ⊆ A := Finset.mem_powerset.1 (Finset.mem_filter.1 hX).1
    have hXcov : CycleCover X := (Finset.mem_filter.1 hX).2
    refine Finset.card_bij' (fun a _ => cutOf A a)
      (fun c _ => Sum.elim (fun e : ArcVar A => decide ((e : Fin n × Fin n) ∈ X)) c)
      ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨hsat, rfl⟩ := ha
      obtain ⟨-, hcons, hroot⟩ := (dirCutCNF_eval A r a).1 hsat
      simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and,
        consistent_undirected_iff]
      exact ⟨hcons, hroot⟩
    · intro c hc
      simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and,
        consistent_undirected_iff] at hc
      have hE : arcsOf A (Sum.elim (fun e : ArcVar A => decide ((e : Fin n × Fin n) ∈ X)) c) =
          X := by
        ext e
        rw [mem_arcsOf]
        simp only [Sum.elim_inl, decide_eq_true_eq]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hXsub h, h⟩⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(dirCutCNF_eval A r _).2 ?_, hE⟩
      rw [hE]
      exact ⟨hXcov, hc.1, hc.2⟩
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨-, hX⟩ := ha
      funext x
      rcases x with e | v
      · simp only [Sum.elim_inl]
        rw [← hX]
        cases h : a (Sum.inl e)
        · simp only [decide_eq_false_iff_not, mem_arcsOf, not_exists]
          intro _ h'
          simp_all
        · simp only [decide_eq_true_eq, mem_arcsOf]
          exact ⟨e.2, h⟩
      · rfl
    · intro c _
      rfl
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
    obtain ⟨hcov, -, -⟩ := (dirCutCNF_eval A r a).1 ha
    simp only [cycleCovers, Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq]
    exact ⟨arcsOf_subset A a, hcov⟩

/-- **Directed Cut&Count parity identity.** -/
theorem count_dirCutCNF_mod_two (r : Fin n) :
    (SAT.count (dirCutCNF A r) : ZMod 2) = ((dirHamCycles A).card : ZMod 2) := by
  rw [count_dirCutCNF, Nat.cast_sum]
  simp_rw [cuts_card_mod_two]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rfl

theorem dirCutCNF_width (r : Fin n) {Δ : ℕ}
    (hout : ∀ v, (A.filter fun a => a.1 = v).card ≤ Δ)
    (hin : ∀ v, (A.filter fun a => a.2 = v).card ≤ Δ) :
    SAT.WidthAtMost (max Δ 3) (dirCutCNF A r) := by
  have hscope : ∀ (p : Fin n × Fin n → Prop) [DecidablePred p],
      ((Finset.univ.filter fun e : ArcVar A => p e).map
        (⟨Sum.inl, Sum.inl_injective⟩ : ArcVar A ↪ DVar A)).card = (A.filter p).card := by
    intro p _
    rw [Finset.card_map]
    refine Finset.card_bij' (fun e _ => (e : Fin n × Fin n)) (fun e he => ⟨e, (Finset.mem_filter.1 he).1⟩)
      ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact Finset.mem_filter.2 ⟨e.2, he⟩
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.1 he).2
    · intro e _; rfl
    · intro e _; rfl
  refine width_union (width_union ?_ ?_) ?_
  · exact constraintCNF_width _ _ (by simp)
  · refine width_biUnion fun v _ => width_union ?_ ?_
    · refine constraintCNF_width _ _ ?_
      rw [outScope, hscope (fun a => a.1 = v)]
      exact (hout v).trans (le_max_left _ _)
    · refine constraintCNF_width _ _ ?_
      rw [inScope, hscope (fun a => a.2 = v)]
      exact (hin v).trans (le_max_left _ _)
  · refine width_biUnion fun e _ => constraintCNF_width _ _ ?_
    exact Finset.card_le_three.trans (le_max_right _ _)

/-- The directed Cut&Count CNF on `Fin (|A| + n)`. -/
noncomputable def dirCutCNFFin (r : Fin n) : SAT.CNF (Fin (Fintype.card (DVar A))) :=
  CNF.relabel (Fintype.equivFin (DVar A)) (dirCutCNF A r)

/-- **Parity of directed Hamiltonian cycles in subexponential time**, for digraphs of maximum in-
and out-degree `≤ Δ`, conditional on the comparator statement at width `max Δ 3`. -/
theorem dirHamParity_subexponential (Δ : ℕ)
    (h : ExactCountAndSatStatement (max Δ 3) (le_max_of_le_right (by norm_num))) :
    ∃ (machine : Computation.PrimitiveMachine)
      (countTape : Fin machine.tapeCount) (C A' S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A' ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (A : Finset (Fin n × Fin n)) (r : Fin n),
        (∀ v, (A.filter fun a => a.1 = v).card ≤ Δ) →
        (∀ v, (A.filter fun a => a.2 = v).card ≤ Δ) →
        ∃ (N time : ℕ) (final : LocatedCfg machine),
          Computation.Trace (locatedStep machine) time
            (locatedInit machine (Encoding.encodeCNF (dirCutCNFFin A r))) final ∧
          final.config.tapes countTape = Turing.Tape.mk₁ ((countWord N).map some) ∧
          BinaryArithmetic.toNat (countWord N) = N ∧
          (N : ZMod 2) = ((dirHamCycles A).card : ZMod 2) ∧
          Fintype.card (DVar A) = A.card + n ∧
          (time : ℝ) ≤ SqrtLog.Statement.runtimeBound C A' d
            (Encoding.formulaBitLength (dirCutCNFFin A r)) (Fintype.card (DVar A)) ∧
          ∀ (prefixSteps : ℕ) (intermediate : LocatedCfg machine),
            prefixSteps ≤ time →
            Computation.Trace (locatedStep machine) prefixSteps
              (locatedInit machine (Encoding.encodeCNF (dirCutCNFFin A r))) intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength (dirCutCNFFin A r) : ℝ) + 1) ^ e := by
  obtain ⟨machine, countTape, _answerTape, C, A', S, d, e, hC, hA, hS, hd, he, hrun⟩ := h
  refine ⟨machine, countTape, C, A', S, d, e, hC, hA, hS, hd, he, ?_⟩
  intro n A r hout hin
  have hw : SAT.WidthAtMost (max Δ 3) (dirCutCNFFin A r) :=
    CNF.relabel_width _ (dirCutCNF_width A r hout hin)
  obtain ⟨time, final, htrace, hcount, -, -, hdecode, -, htime, hspace⟩ :=
    hrun (Fintype.card (DVar A)) (dirCutCNFFin A r) hw
  refine ⟨SAT.count (dirCutCNFFin A r), time, final, htrace, hcount, hdecode, ?_,
    card_dvar A, htime, hspace⟩
  rw [dirCutCNFFin, CNF.relabel_count, count_dirCutCNF_mod_two]

end EthFollowup.DirectedHamiltonian
