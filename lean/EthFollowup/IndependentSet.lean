/-
Counting independent sets and vertex covers via the OpenAI #k-SAT machine.

We encode a simple graph `G` on `Fin n` as the monotone 2-CNF
`⋀_{uv ∈ E} (¬x_u ∨ ¬x_v)` (resp. `⋀ (x_u ∨ x_v)`), prove that satisfying assignments are in
bijection with independent sets (resp. vertex covers), and derive from the comparator statement
`ExactCountAndSatStatement` (taken as a hypothesis, proved upstream in openai/math) that one fixed
machine counts independent sets of every graph in time
`C (L+1)^d 2^{A · n (log log(n+16))²/√log(n+16)}` and polynomial space.
-/
import EthFollowup.CNFKit

namespace EthFollowup

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {n : ℕ}

/-- The negative literal `¬x_v`. -/
def negLit (v : Fin n) : SAT.Literal (Fin n) := ⟨v, false⟩
/-- The positive literal `x_v`. -/
def posLit (v : Fin n) : SAT.Literal (Fin n) := ⟨v, true⟩

/-- Ordered adjacent pairs of `G`. -/
def adjPairs (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => G.Adj p.1 p.2

/-- The 2-CNF whose models are the independent sets of `G`: one clause `¬x_u ∨ ¬x_v` per edge. -/
def indepCNF (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : SAT.CNF (Fin n) :=
  (adjPairs G).image fun p => ({negLit p.1, negLit p.2} : SAT.Clause (Fin n))

/-- The 2-CNF whose models are the vertex covers of `G`: one clause `x_u ∨ x_v` per edge. -/
def coverCNF (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : SAT.CNF (Fin n) :=
  (adjPairs G).image fun p => ({posLit p.1, posLit p.2} : SAT.Clause (Fin n))

/-- Independent sets of `G`, as a `Finset` of vertex subsets. -/
def indepSets (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S => ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

/-- Vertex covers of `G`, as a `Finset` of vertex subsets. -/
def vertexCovers (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S => ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S

section Semantics

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem indepCNF_width : SAT.WidthAtMost 2 (indepCNF G) := by
  intro C hC
  simp only [indepCNF, Finset.mem_image] at hC
  obtain ⟨p, -, rfl⟩ := hC
  exact Finset.card_le_two

theorem coverCNF_width : SAT.WidthAtMost 2 (coverCNF G) := by
  intro C hC
  simp only [coverCNF, Finset.mem_image] at hC
  obtain ⟨p, -, rfl⟩ := hC
  exact Finset.card_le_two

@[simp] theorem negLit_eval (a : SAT.Assignment (Fin n)) (v : Fin n) :
    (negLit v).eval a = true ↔ a v = false := by
  simp [negLit, SAT.Literal.eval]

@[simp] theorem posLit_eval (a : SAT.Assignment (Fin n)) (v : Fin n) :
    (posLit v).eval a = true ↔ a v = true := by
  simp [posLit, SAT.Literal.eval]

theorem indepCNF_eval (a : SAT.Assignment (Fin n)) :
    (indepCNF G).eval a = true ↔ ∀ u v, G.Adj u v → a u = false ∨ a v = false := by
  rw [CNF.eval_iff]
  simp only [indepCNF, adjPairs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists, SAT.Clause.eval, decide_eq_true_eq, forall_exists_index, and_imp]
  constructor
  · intro h u v huv
    have := h _ u v huv rfl
    simpa [negLit, posLit, SAT.Literal.eval] using this
  · rintro h C u v huv rfl
    rcases h u v huv with h' | h'
    · exact ⟨negLit u, by simp, by simpa [negLit, posLit, SAT.Literal.eval] using h'⟩
    · exact ⟨negLit v, by simp, by simpa [negLit, posLit, SAT.Literal.eval] using h'⟩

theorem coverCNF_eval (a : SAT.Assignment (Fin n)) :
    (coverCNF G).eval a = true ↔ ∀ u v, G.Adj u v → a u = true ∨ a v = true := by
  rw [CNF.eval_iff]
  simp only [coverCNF, adjPairs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists, SAT.Clause.eval, decide_eq_true_eq, forall_exists_index, and_imp]
  constructor
  · intro h u v huv
    have := h _ u v huv rfl
    simpa [negLit, posLit, SAT.Literal.eval] using this
  · rintro h C u v huv rfl
    rcases h u v huv with h' | h'
    · exact ⟨posLit u, by simp, by simpa [negLit, posLit, SAT.Literal.eval] using h'⟩
    · exact ⟨posLit v, by simp, by simpa [negLit, posLit, SAT.Literal.eval] using h'⟩

/-- `#indepCNF G` is the number of independent sets of `G`. -/
theorem count_indepCNF : SAT.count (indepCNF G) = (indepSets G).card := by
  unfold SAT.count SAT.satisfyingAssignments indepSets
  refine Finset.card_bij' (fun a _ => Finset.univ.filter fun v => a v = true)
    (fun S _ => fun v => decide (v ∈ S)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [indepCNF_eval] at ha
    intro u hu v hv huv
    rcases ha u v huv with h | h <;> simp_all
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    rw [indepCNF_eval]
    intro u v huv
    by_contra hcon
    have hu : u ∈ S := by
      by_contra hu
      exact hcon (Or.inl (by simp [hu]))
    have hv : v ∈ S := by
      by_contra hv
      exact hcon (Or.inr (by simp [hv]))
    exact hS u hu v hv huv
  · intro a _
    funext v
    simp
  · intro S _
    ext v
    simp

/-- `#coverCNF G` is the number of vertex covers of `G`. -/
theorem count_coverCNF : SAT.count (coverCNF G) = (vertexCovers G).card := by
  unfold SAT.count SAT.satisfyingAssignments vertexCovers
  refine Finset.card_bij' (fun a _ => Finset.univ.filter fun v => a v = true)
    (fun S _ => fun v => decide (v ∈ S)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [coverCNF_eval] at ha
    intro u v huv
    rcases ha u v huv with h | h <;> simp_all
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    rw [coverCNF_eval]
    intro u v huv
    rcases hS u v huv with h | h <;> simp [h]
  · intro a _
    funext v
    simp
  · intro S _
    ext v
    simp

end Semantics

/-- **Counting independent sets in subexponential time**, conditional on the upstream theorem
`exact_count_and_sat` at `k = 2` (passed as `h`). One fixed machine, started on the canonical
encoding of `indepCNF G`, halts with the number of independent sets of `G` on its count tape,
within the comparator's time bound and with polynomial visited space at every prefix. -/
theorem indepSet_count_subexponential
    (h : ExactCountAndSatStatement 2 le_rfl) :
    ∃ (machine : Computation.PrimitiveMachine)
      (countTape : Fin machine.tapeCount) (C A S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ∃ (time : ℕ) (final : LocatedCfg machine),
          Computation.Trace (locatedStep machine) time
            (locatedInit machine (Encoding.encodeCNF (indepCNF G))) final ∧
          final.config.tapes countTape =
            Turing.Tape.mk₁ ((countWord (indepSets G).card).map some) ∧
          BinaryArithmetic.toNat (countWord (indepSets G).card) = (indepSets G).card ∧
          (time : ℝ) ≤ SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength (indepCNF G)) n ∧
          ∀ (prefixSteps : ℕ) (intermediate : LocatedCfg machine),
            prefixSteps ≤ time →
            Computation.Trace (locatedStep machine) prefixSteps
              (locatedInit machine (Encoding.encodeCNF (indepCNF G))) intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength (indepCNF G) : ℝ) + 1) ^ e := by
  obtain ⟨machine, countTape, _answerTape, C, A, S, d, e, hC, hA, hS, hd, he, hrun⟩ := h
  refine ⟨machine, countTape, C, A, S, d, e, hC, hA, hS, hd, he, ?_⟩
  intro n G _
  obtain ⟨time, final, htrace, hcount, -, -, hdecode, -, htime, hspace⟩ :=
    hrun n (indepCNF G) (indepCNF_width G)
  rw [count_indepCNF] at hcount hdecode
  exact ⟨time, final, htrace, hcount, hdecode, htime, hspace⟩

/-- The same for vertex covers. -/
theorem vertexCover_count_subexponential
    (h : ExactCountAndSatStatement 2 le_rfl) :
    ∃ (machine : Computation.PrimitiveMachine)
      (countTape : Fin machine.tapeCount) (C A S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ∃ (time : ℕ) (final : LocatedCfg machine),
          Computation.Trace (locatedStep machine) time
            (locatedInit machine (Encoding.encodeCNF (coverCNF G))) final ∧
          final.config.tapes countTape =
            Turing.Tape.mk₁ ((countWord (vertexCovers G).card).map some) ∧
          BinaryArithmetic.toNat (countWord (vertexCovers G).card) = (vertexCovers G).card ∧
          (time : ℝ) ≤ SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength (coverCNF G)) n ∧
          ∀ (prefixSteps : ℕ) (intermediate : LocatedCfg machine),
            prefixSteps ≤ time →
            Computation.Trace (locatedStep machine) prefixSteps
              (locatedInit machine (Encoding.encodeCNF (coverCNF G))) intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength (coverCNF G) : ℝ) + 1) ^ e := by
  obtain ⟨machine, countTape, _answerTape, C, A, S, d, e, hC, hA, hS, hd, he, hrun⟩ := h
  refine ⟨machine, countTape, C, A, S, d, e, hC, hA, hS, hd, he, ?_⟩
  intro n G _
  obtain ⟨time, final, htrace, hcount, -, -, hdecode, -, htime, hspace⟩ :=
    hrun n (coverCNF G) (coverCNF_width G)
  rw [count_coverCNF] at hcount hdecode
  exact ⟨time, final, htrace, hcount, hdecode, htime, hspace⟩

end EthFollowup
