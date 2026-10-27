/-
# Restricting the Cut&Count count by constraints on the edges

For any CNF `H` on the edge variables, adding `H` to the Cut&Count formula restricts the count to
Hamiltonian cycles whose edge-indicator satisfies `H` (`count_cutCNF_with_mod_two`):

  `#(cutCNF G r ∧ H) ≡ #{X ∈ hamCycles G : H(1_X)}  (mod 2)`.

This is the deterministic half of a decision procedure. The isolation lemma of Calabro,
Impagliazzo, Kabanets and Paturi (CCC 2003, Lemma 3) uses `m` random sparse GF(2) equations on
`k′ = ⌈(1/ε) ln(2/ε)⌉` coordinates, plus fixing `≤ 2εN` coordinates. Its proof uses only that the
solution set `S ⊆ {0,1}^N` is a set, so it applies to `S = hamCycles G ⊆ {0,1}^{E(G)}`. With
probability `≥ (32N)^{-1} 2^{-3h(2ε)N}`, exactly one Hamiltonian cycle survives. Encoding the
equations as a width-`k′` CNF `H` (`xorCNF`) and running the machine of `hamIso_subexponential`
gives an odd count with that probability, and always an even count when `G` has no Hamiltonian
cycle. The probabilistic lemma is cited, not formalised.
-/
import EthFollowup.HamiltonianParity

namespace EthFollowup.Hamiltonian

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open EthFollowup

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The edge-indicator assignment of an edge set. -/
def edgeIndicator (X : Finset (Sym2 (Fin n))) : SAT.Assignment (EdgeVar G) :=
  fun e => decide ((e : Sym2 (Fin n)) ∈ X)

/-- Cut&Count plus extra constraints on the edge variables. -/
def cutCNFWith (H : SAT.CNF (EdgeVar G)) (r : Fin n) : SAT.CNF (Var G) :=
  cutCNF G r ∪ CNF.map Sum.inl H

theorem edgeIndicator_edgesOf (a : SAT.Assignment (Var G)) :
    edgeIndicator G (edgesOf G a) = a ∘ Sum.inl := by
  funext e
  simp only [edgeIndicator, Function.comp]
  cases h : a (Sum.inl e)
  · simp only [decide_eq_false_iff_not, mem_edgesOf, not_exists]
    intro _ h'
    simp_all
  · simp only [decide_eq_true_eq, mem_edgesOf]
    exact ⟨e.2, h⟩

theorem cutCNFWith_eval (H : SAT.CNF (EdgeVar G)) (r : Fin n) (a : SAT.Assignment (Var G)) :
    SAT.CNF.eval a (cutCNFWith G H r) = true ↔
      (TwoRegular (edgesOf G a) ∧ Consistent (edgesOf G a) (cutOf G a) ∧ cutOf G a r = false) ∧
        SAT.CNF.eval (edgeIndicator G (edgesOf G a)) H = true := by
  rw [cutCNFWith, CNF.eval_union, CNF.map_eval, cutCNF_eval, edgeIndicator_edgesOf]

theorem count_cutCNFWith (H : SAT.CNF (EdgeVar G)) (r : Fin n) :
    SAT.count (cutCNFWith G H r) =
      ∑ X ∈ (twoFactors G).filter (fun X => SAT.CNF.eval (edgeIndicator G X) H = true),
        (cuts X r).card := by
  classical
  unfold SAT.count SAT.satisfyingAssignments
  rw [Finset.card_eq_sum_card_fiberwise (f := edgesOf G)
    (t := (twoFactors G).filter (fun X => SAT.CNF.eval (edgeIndicator G X) H = true))]
  · refine Finset.sum_congr rfl fun X hX => ?_
    obtain ⟨hX2, hXH⟩ := Finset.mem_filter.1 hX
    have hXsub : X ⊆ G.edgeFinset := Finset.mem_powerset.1 (Finset.mem_filter.1 hX2).1
    have hXreg : TwoRegular X := (Finset.mem_filter.1 hX2).2
    refine Finset.card_bij' (fun a _ => cutOf G a)
      (fun c _ => Sum.elim (fun e : EdgeVar G => decide ((e : Sym2 (Fin n)) ∈ X)) c)
      ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨hsat, rfl⟩ := ha
      obtain ⟨⟨-, hcons, hroot⟩, -⟩ := (cutCNFWith_eval G H r a).1 hsat
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
      refine ⟨(cutCNFWith_eval G H r _).2 ?_, hE⟩
      rw [hE]
      exact ⟨⟨hXreg, hc.1, hc.2⟩, hXH⟩
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨-, hX⟩ := ha
      funext x
      rcases x with e | v
      · simp only [Sum.elim_inl]
        rw [← hX]
        exact congrFun (edgeIndicator_edgesOf G a) e
      · rfl
    · intro c _
      rfl
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
    obtain ⟨⟨hreg, -, -⟩, hH⟩ := (cutCNFWith_eval G H r a).1 ha
    simp only [Finset.coe_filter, twoFactors, Finset.mem_filter, Finset.mem_powerset,
      Set.mem_ofPred_eq]
    exact ⟨⟨edgesOf_subset G a, hreg⟩, hH⟩

/-- **Restricted parity identity.** -/
theorem count_cutCNFWith_mod_two (H : SAT.CNF (EdgeVar G)) (r : Fin n) :
    (SAT.count (cutCNFWith G H r) : ZMod 2) =
      (((hamCycles G).filter fun X => SAT.CNF.eval (edgeIndicator G X) H = true).card : ZMod 2) := by
  rw [count_cutCNFWith, Nat.cast_sum]
  simp_rw [cuts_card_mod_two]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.filter_filter, hamCycles, Finset.filter_filter]
  congr 2
  ext X
  simp only [Finset.mem_filter]
  tauto

/-- If `G` has no Hamiltonian cycle, the restricted count is even for every `H`; if exactly one
Hamiltonian cycle satisfies `H`, it is odd. -/
theorem parity_of_unique (H : SAT.CNF (EdgeVar G)) (r : Fin n)
    (h1 : ((hamCycles G).filter fun X => SAT.CNF.eval (edgeIndicator G X) H = true).card = 1) :
    (SAT.count (cutCNFWith G H r) : ZMod 2) = 1 := by
  rw [count_cutCNFWith_mod_two, h1, Nat.cast_one]

theorem parity_of_none (H : SAT.CNF (EdgeVar G)) (r : Fin n) (h0 : hamCycles G = ∅) :
    (SAT.count (cutCNFWith G H r) : ZMod 2) = 0 := by
  rw [count_cutCNFWith_mod_two, h0, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]

/-! ### Sparse GF(2) equations as CNF -/

/-- The equation `Σ_{e ∈ R} x_e = b` over GF(2), as a CNF of width `|R|`. -/
def xorCNF (R : Finset (EdgeVar G)) (b : Bool) : SAT.CNF (EdgeVar G) :=
  constraintCNF R fun T => (T.card % 2 = 1 ↔ b = true)

theorem xorCNF_eval (R : Finset (EdgeVar G)) (b : Bool) (a : SAT.Assignment (EdgeVar G)) :
    SAT.CNF.eval a (xorCNF G R b) = true ↔
      ((R.filter fun e => a e = true).card % 2 = 1 ↔ b = true) :=
  constraintCNF_eval _ _ a

theorem xorCNF_width (R : Finset (EdgeVar G)) (b : Bool) {k : ℕ} (hk : R.card ≤ k) :
    SAT.WidthAtMost k (xorCNF G R b) :=
  constraintCNF_width _ _ hk

/-! ### The machine -/

noncomputable def cutCNFWithFin (H : SAT.CNF (EdgeVar G)) (r : Fin n) :
    SAT.CNF (Fin (Fintype.card (Var G))) :=
  CNF.relabel (Fintype.equivFin (Var G)) (cutCNFWith G H r)

/-- **Restricted Hamiltonian parity in subexponential time.** For each `Δ` and `k`, conditional
on the comparator at width `max Δ (max 3 k)`, one machine computes, for every graph of maximum
degree `≤ Δ` and every width-`k` CNF `H` on its edge variables, a number congruent mod 2 to the
number of Hamiltonian cycles satisfying `H`. -/
theorem hamIso_subexponential (Δ k : ℕ)
    (h : ExactCountAndSatStatement (max Δ (max 3 k))
      (le_max_of_le_right (le_max_of_le_left (by norm_num)))) :
    ∃ (machine : Computation.PrimitiveMachine)
      (countTape : Fin machine.tapeCount) (C A S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (H : SAT.CNF (EdgeVar G))
        (r : Fin n), (∀ v, G.degree v ≤ Δ) → SAT.WidthAtMost k H →
        ∃ (N time : ℕ) (final : LocatedCfg machine),
          Computation.Trace (locatedStep machine) time
            (locatedInit machine (Encoding.encodeCNF (cutCNFWithFin G H r))) final ∧
          final.config.tapes countTape = Turing.Tape.mk₁ ((countWord N).map some) ∧
          BinaryArithmetic.toNat (countWord N) = N ∧
          (N : ZMod 2) =
            (((hamCycles G).filter fun X => SAT.CNF.eval (edgeIndicator G X) H = true).card :
              ZMod 2) ∧
          (time : ℝ) ≤ SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength (cutCNFWithFin G H r)) (Fintype.card (Var G)) ∧
          ∀ (prefixSteps : ℕ) (intermediate : LocatedCfg machine),
            prefixSteps ≤ time →
            Computation.Trace (locatedStep machine) prefixSteps
              (locatedInit machine (Encoding.encodeCNF (cutCNFWithFin G H r))) intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength (cutCNFWithFin G H r) : ℝ) + 1) ^ e := by
  obtain ⟨machine, countTape, _answerTape, C, A, S, d, e, hC, hA, hS, hd, he, hrun⟩ := h
  refine ⟨machine, countTape, C, A, S, d, e, hC, hA, hS, hd, he, ?_⟩
  intro n G _ H r hΔ hH
  have hw : SAT.WidthAtMost (max Δ (max 3 k)) (cutCNFWithFin G H r) := by
    refine CNF.relabel_width _ (width_union ?_ (CNF.map_width _ ?_))
    · intro C hC
      exact (cutCNF_width G r hΔ C hC).trans (max_le_max le_rfl (le_max_left _ _))
    · intro C hC
      exact (hH C hC).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨time, final, htrace, hcount, -, -, hdecode, -, htime, hspace⟩ :=
    hrun (Fintype.card (Var G)) (cutCNFWithFin G H r) hw
  refine ⟨SAT.count (cutCNFWithFin G H r), time, final, htrace, hcount, hdecode, ?_, htime, hspace⟩
  rw [cutCNFWithFin, CNF.relabel_count, count_cutCNFWith_mod_two]

end EthFollowup.Hamiltonian
