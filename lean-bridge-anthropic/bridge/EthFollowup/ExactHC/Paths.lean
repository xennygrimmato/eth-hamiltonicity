/-
# Hamiltonian paths at Turing-machine level (`cor:decision-search`, part *paths*)

`paper/main.tex`, `cor:decision-search`: count, decide and find Hamiltonian paths, by the counting
machines of `theorem1`/`theorem2` run on the apex graph `apex G` (`n + 1` vertices, `m + n` edges;
`HamPath.lean`: `#HP(G) = #HC(apex G)` for `n ≥ 2`). The word map `code G ↦ code (apex G)`
(`Srch.apexW`) is put in front of the counting machine (`Stepped.mapIn`).

* `hamPaths_count_TM`, `hamPaths_decision_TM`, `hamPaths_search_TM`: fixed density, graphs with at
  most `D·n` edges, time `⌊C·2^{δn}⌋` (the counting machine of `theorem1` for `D + 1`);
* `hamPaths_count_TM_rate`, `hamPaths_decision_TM_rate`, `hamPaths_search_TM_rate`: all graphs,
  time `⌊C·2^{C(m+n)/√log₂(n+2)}⌋`.

All for `n ≥ 2`. The search outputs `[]` if `G` has no Hamiltonian path, and otherwise the adjacency
matrix of `(Fin n, X)` for a Hamiltonian path `X ∈ hamPaths G`.

Standard axioms only.
-/
import EthFollowup.ExactHC.Corollaries

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

namespace Cor

open Groundwork Groundwork.Prog GraphProblems Asm Finset EthFollowup.Hamiltonian

/-! ## The apex graph: edges, answers -/

section Apex

variable {n : ℕ}

theorem card_apex_edge_le (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (apex G).edgeFinset.card ≤ G.edgeFinset.card + n := by
  have hd := not_isDiag_of_sub (G := apex G) (subset_refl _)
  have hg := glue_minusE_nbr hd
  have h1 := card_glue (minusE (apex G).edgeFinset) (nbr (apex G).edgeFinset)
  rw [hg] at h1
  have h2 := card_le_card (minusE_sub (G := G) (subset_refl (apex G).edgeFinset))
  have h3 : (nbr (apex G).edgeFinset).card ≤ n := by
    have := card_le_univ (nbr (apex G).edgeFinset)
    rwa [Fintype.card_fin] at this
  omega

theorem apex_edge_le {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {D : ℕ}
    (hm : G.edgeFinset.card ≤ D * n) : (apex G).edgeFinset.card ≤ (D + 1) * (n + 1) := by
  have := card_apex_edge_le G
  nlinarith

theorem apexO_runs (Q : Stepped (List Bool) (List Bool)) (H : SimpleGraph (Fin n)) {T S : ℕ}
    {w : List Bool} (h : Q.Runs (code (apex H)) T S w) :
    (Stepped.mapIn Srch.apexW Q).Runs (code H) T S w :=
  Stepped.mapIn_runs (by rw [Srch.apexW_code]; exact h)

theorem bits_hp (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hn : 2 ≤ n) :
    Nat.bits (hamCycles (apex H)).card = Nat.bits (hamPaths H).card := by
  rw [card_hamPaths_eq hn]

theorem decide_hp (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hn : 2 ≤ n) :
    decide ((Nat.bits (hamCycles (apex H)).card).length ≠ 0) = decide (hamPaths H).Nonempty := by
  rw [bits_hp H hn, Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, bits_length_ne_zero_iff,
    ← Finset.card_pos]
  omega

/-- The answer of the counting machine on the apex graph is empty iff `H` has no Hamiltonian path
(and `n ≥ 2`). -/
theorem apex_nil_iff (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    Nat.bits (hamCycles (apex H)).card = [] ↔ ¬∃ X : Finset (Sym2 (Fin n)),
      (X : Set (Sym2 (Fin n))) ⊆ H.edgeSet ∧ (IsHamPath X ∧ 2 ≤ n) := by
  by_cases hn : 2 ≤ n
  · rw [bits_hp H hn, Srch.bits_eq_nil_iff, Srch.card_hp_eq_zero_iff]
    simp only [hn, and_true]
  · have : hamCycles (apex H) = ∅ := hamCycles_eq_empty (Or.inl (by omega))
    rw [this, card_empty, Nat.zero_bits]
    simp only [hn, and_false, not_exists, not_false_eq_true, implies_true]

theorem size_bits_hc_apex (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    size (Nat.bits (hamCycles (apex H)).card) ≤ 2 * ((n + 1) * (n + 1) + 1) + 1 :=
  size_bits_hc (apex H)

/-- The outputs of the search for Hamiltonian paths. -/
theorem search_out_hp (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {w : List Bool} (hn : 2 ≤ n)
    (h1 : (¬∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ (IsHamPath X ∧ 2 ≤ n)) → w = [])
    (h2 : (∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ (IsHamPath X ∧ 2 ≤ n)) →
      ∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ (IsHamPath X ∧ 2 ≤ n) ∧
        w = matrix (graphOf X)) :
    (hamPaths G = ∅ → w = []) ∧ ((hamPaths G).Nonempty → ∃ X ∈ hamPaths G, w = matrix (graphOf X)) := by
  refine ⟨fun he => h1 fun ⟨X, hX, hQ, _⟩ => ?_, fun ⟨X, hX⟩ => ?_⟩
  · have : X ∈ hamPaths G := Srch.mem_hp_iff.2 ⟨hX, hQ⟩
    rw [he] at this; exact absurd this (Finset.notMem_empty _)
  · obtain ⟨Y, hY, ⟨hQ, _⟩, hw⟩ := h2 ⟨X, (Srch.mem_hp_iff.1 hX).1, (Srch.mem_hp_iff.1 hX).2, hn⟩
    exact ⟨Y, Srch.mem_hp_iff.2 ⟨hY, hQ⟩, hw⟩

end Apex

/-! ## Real-number facts for `n + 1` vertices -/

section Real

open T2

theorem rpow_succ_le (A : ℕ) {ε : ℝ} (_hε : 0 ≤ ε) (n : ℕ) :
    (A : ℝ) * (2 : ℝ) ^ (ε * ((n + 1 : ℕ) : ℝ)) ≤ ((A * ⌈(2 : ℝ) ^ ε⌉₊ : ℕ) : ℝ) * (2 : ℝ) ^ (ε * n) := by
  have e : (2 : ℝ) ^ (ε * ((n + 1 : ℕ) : ℝ)) = (2 : ℝ) ^ ε * (2 : ℝ) ^ (ε * n) := by
    rw [← Real.rpow_add two_pos]; congr 1; push_cast; ring
  rw [e]
  have h1 : (2 : ℝ) ^ ε ≤ (⌈(2 : ℝ) ^ ε⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (ε * n) := by positivity
  push_cast
  have : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  calc (A : ℝ) * ((2 : ℝ) ^ ε * (2 : ℝ) ^ (ε * n)) = A * (2 : ℝ) ^ ε * (2 : ℝ) ^ (ε * n) := by ring
    _ ≤ A * (⌈(2 : ℝ) ^ ε⌉₊ : ℝ) * (2 : ℝ) ^ (ε * n) := by gcongr

theorem sq_mono' {n n' : ℕ} (h : n ≤ n') : T2.sq n ≤ T2.sq n' := by
  unfold T2.sq T2.Lam
  apply Real.sqrt_le_sqrt
  apply Real.logb_le_logb_of_le one_lt_two (by positivity)
  have : (n : ℝ) ≤ n' := by exact_mod_cast h
  linarith

/-- `n + 1` vertices and at most `m + n` edges: `Xp A (n+1) m' ≤ Xp (2A) n m`. -/
theorem Xp_succ_le {A n m m' : ℕ} (hm : m' ≤ m + n) : Xp A (n + 1) m' ≤ Xp (2 * A) n m := by
  unfold Xp
  have h1 := sq_mono' (Nat.le_succ n)
  have h0 := T2.sq_pos n
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hm' : (m' : ℝ) ≤ m + n := by exact_mod_cast hm
  calc (A : ℝ) * ((m' : ℝ) + ((n + 1 : ℕ) : ℝ) + 2) / T2.sq (n + 1)
      ≤ (A : ℝ) * ((m' : ℝ) + ((n + 1 : ℕ) : ℝ) + 2) / T2.sq n :=
        div_le_div_of_nonneg_left (by positivity) h0 h1
    _ ≤ ((2 * A : ℕ) : ℝ) * ((m : ℝ) + n + 2) / T2.sq n := by
        apply div_le_div_of_nonneg_right _ h0.le
        push_cast
        nlinarith

theorem le_Xp_succ {x : ℝ} {A n m m' : ℕ} (h : x ≤ (2 : ℝ) ^ Xp A (n + 1) m') (hm : m' ≤ m + n) :
    x ≤ (2 : ℝ) ^ Xp (2 * A) n m :=
  h.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_succ_le hm))

end Real

end Cor

/-! ## Fixed density -/

open Groundwork Cor Asm in
/-- **Counting Hamiltonian paths, fixed density** (`cor:decision-search` with `thm:main-delta`):
for every `δ > 0` and `D` a Turing machine of Mathlib with finite alphabets and a constant `C` such
that on the code of any graph with `n ≥ 2` vertices and at most `D·n` edges it halts within
`⌊C·2^{δn}⌋` steps with the number of Hamiltonian paths in binary. -/
theorem hamPaths_count_TM (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 2 ≤ n → G.edgeFinset.card ≤ D * n →
        GraphProblems.Outputs M (GraphProblems.code G) (Nat.bits (hamPaths G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨Q, iQ, A, hA⟩ := t1_core δ hδ (D + 1)
  obtain ⟨iP⟩ := Srch.apexS_poly Q
  obtain ⟨As, hAs⟩ : ∃ As, ∀ n, Pol As n (A * (n + 1 + 2) ^ A) :=
    ⟨_, fun n => Pol.mul (Pol.const A) (Pol.pow (Pol.add (Pol.add Pol.id (Pol.const 1)) (Pol.const 2)) A)⟩
  obtain ⟨M, C, hfin, hM⟩ := t1_tm (Stepped.mapIn Srch.apexW Q) D hδ
    (fun {n} G _ w => 2 ≤ n → w = Nat.bits (hamPaths G).card) As (A * ⌈(2 : ℝ) ^ (δ / 2)⌉₊)
    (fun {n} G _ hm => by
      obtain ⟨T, hR, hT⟩ := hA (apex G) (apex_edge_le hm)
      refine ⟨T, _, _, fun hn => bits_hp G hn, apexO_runs Q G hR, hAs n, ?_⟩
      exact hT.trans (rpow_succ_le A (by positivity) n))
  refine ⟨M, C, hfin, fun n G _ hn hm => ?_⟩
  obtain ⟨w, hw, hO⟩ := hM n G hm
  rwa [← hw hn]

open Groundwork Cor Asm in
/-- **Deciding the existence of a Hamiltonian path, fixed density.** -/
theorem hamPaths_decision_TM (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 2 ≤ n → G.edgeFinset.card ≤ D * n →
        GraphProblems.Outputs M (GraphProblems.code G) [decide (hamPaths G).Nonempty]
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨Q, iQ, A, hA⟩ := t1_core δ hδ (D + 1)
  obtain ⟨iP⟩ := Srch.apexS_poly Q
  obtain ⟨iD⟩ := Srch.decS_poly (Stepped.mapIn Srch.apexW Q)
  obtain ⟨As, hAs⟩ : ∃ As, ∀ n, Pol As n ((2 * (n + 1 + n * n) + 1) + A * (n + 1 + 2) ^ A +
      (2 * ((n + 1) * (n + 1) + 1) + 1) + 4) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.add Pol.id
      (Pol.const 1)) (Pol.mul Pol.id Pol.id))) (Pol.const 1))
      (Pol.mul (Pol.const A) (Pol.pow (Pol.add (Pol.add Pol.id (Pol.const 1)) (Pol.const 2)) A)))
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.mul (Pol.add Pol.id (Pol.const 1))
        (Pol.add Pol.id (Pol.const 1))) (Pol.const 1))) (Pol.const 1)))
      (Pol.const 4)⟩
  obtain ⟨M, C, hfin, hM⟩ := t1_tm (Srch.decS (Stepped.mapIn Srch.apexW Q)) D hδ
    (fun {n} G _ w => 2 ≤ n → w = [decide (hamPaths G).Nonempty]) As (A * ⌈(2 : ℝ) ^ (δ / 2)⌉₊ + 2)
    (fun {n} G _ hm => by
      obtain ⟨T, hR, hT⟩ := hA (apex G) (apex_edge_le hm)
      refine ⟨_, _, _, fun hn => by rw [decide_hp G hn], Srch.decS_runs _ (apexO_runs Q G hR), ?_,
        add_const_le (by positivity) (hT.trans (rpow_succ_le A (by positivity) n))⟩
      refine le_trans ?_ (hAs n)
      rw [Srch.size_code]
      have := size_bits_hc_apex G
      omega)
  refine ⟨M, C, hfin, fun n G _ hn hm => ?_⟩
  obtain ⟨w, hw, hO⟩ := hM n G hm
  rwa [← hw hn]

open Groundwork Cor Asm in
/-- **Finding a Hamiltonian path, fixed density**: the output is `[]` if `G` has no Hamiltonian
path, and otherwise the adjacency matrix of `(Fin n, X)` for some `X ∈ hamPaths G`. -/
theorem hamPaths_search_TM (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 2 ≤ n → G.edgeFinset.card ≤ D * n →
        ∃ w : List Bool, GraphProblems.Outputs M (GraphProblems.code G) w ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ ∧
          (hamPaths G = ∅ → w = []) ∧
          ((hamPaths G).Nonempty → ∃ X ∈ hamPaths G, w = GraphProblems.matrix (Hamiltonian.graphOf X)) := by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨Q, iQ, A, hA⟩ := t1_core (δ / 2) hδ2 (D + 1)
  obtain ⟨iP⟩ := Srch.apexS_poly Q
  obtain ⟨iS⟩ := Srch.searchS_poly (Stepped.mapIn Srch.apexW Q)
  obtain ⟨Cp, hCp⟩ := Groundwork.exists_pow_le 2 (show (0 : ℝ) < δ / 4 by positivity)
  set A' := A * ⌈(2 : ℝ) ^ (δ / 2 / 2)⌉₊ with hA'
  obtain ⟨As, hAs⟩ : ∃ As, ∀ n, Pol As n ((A * (n + 1 + 2) ^ A + (2 * ((n + 1) * (n + 1) + 1) + 1)) +
      30 * (n * n) + 10 * n + 40) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const A)
      (Pol.pow (Pol.add (Pol.add Pol.id (Pol.const 1)) (Pol.const 2)) A))
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.mul (Pol.add Pol.id (Pol.const 1))
        (Pol.add Pol.id (Pol.const 1))) (Pol.const 1))) (Pol.const 1)))
      (Pol.mul (Pol.const 30) (Pol.mul Pol.id Pol.id))) (Pol.mul (Pol.const 10) Pol.id)) (Pol.const 40)⟩
  obtain ⟨M, C, hfin, hM⟩ := t1_tm (Srch.searchS (Stepped.mapIn Srch.apexW Q)) D hδ
    (fun {n} G _ w => 2 ≤ n → (hamPaths G = ∅ → w = []) ∧ ((hamPaths G).Nonempty →
      ∃ X ∈ hamPaths G, w = GraphProblems.matrix (Hamiltonian.graphOf X)))
    As (Cp * (A' + 3)) (fun {n} G _ hm => by
      set To := ⌊(A' : ℝ) * (2 : ℝ) ^ (δ / 2 / 2 * n)⌋₊ with hTo
      set So := A * (n + 1 + 2) ^ A + (2 * ((n + 1) * (n + 1) + 1) + 1) with hSo
      have hO : ∀ H : SimpleGraph (Fin n), H ≤ G → ∃ T w,
          (Stepped.mapIn Srch.apexW Q).Runs (GraphProblems.code H) T So w ∧ T ≤ To ∧
          size w ≤ So ∧ (w = [] ↔ ¬∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ H.edgeSet ∧
            (IsHamPath X ∧ 2 ≤ n)) := by
        intro H hHG
        classical
        obtain ⟨T, hR, hT⟩ := hA (apex H) (apex_edge_le ((card_edge_mono hHG).trans hm))
        refine ⟨T, _, apexO_runs Q H (hR.mono le_rfl (by omega)),
          Nat.le_floor (hT.trans (rpow_succ_le A (by positivity) n)), ?_, apex_nil_iff H⟩
        have := size_bits_hc_apex H
        omega
      obtain ⟨T, w, hR, hT, h1, h2⟩ := Srch.searchS_runs _ G _ To So hO
      refine ⟨T, _, w, fun hn => search_out_hp G hn h1 h2, hR, hAs n, ?_⟩
      have hToR : (To : ℝ) ≤ A' * (2 : ℝ) ^ (δ / 2 / 2 * n) := Nat.floor_le (by positivity)
      have hn2 : ((n * n + 1 : ℕ) : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by push_cast; nlinarith
      have hCpn := hCp n
      have e : (2 : ℝ) ^ (δ / 2 * n) = (2 : ℝ) ^ (δ / 4 * n) * (2 : ℝ) ^ (δ / 2 / 2 * n) := by
        rw [← Real.rpow_add two_pos]; congr 1; ring
      have hE : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 / 2 * n) := Real.one_le_rpow one_le_two (by positivity)
      have hTR : (T : ℝ) ≤ ((n * n + 1 : ℕ) : ℝ) * ((To : ℝ) + 3) := by exact_mod_cast hT
      have h3 : (To : ℝ) + 3 ≤ ((A' : ℝ) + 3) * (2 : ℝ) ^ (δ / 2 / 2 * n) := by nlinarith
      calc (T : ℝ) ≤ ((n * n + 1 : ℕ) : ℝ) * ((To : ℝ) + 3) := hTR
        _ ≤ ((n : ℝ) + 2) ^ 2 * (((A' : ℝ) + 3) * (2 : ℝ) ^ (δ / 2 / 2 * n)) := by
            apply mul_le_mul hn2 h3 (by positivity) (by positivity)
        _ ≤ (Cp * (2 : ℝ) ^ (δ / 4 * n)) * (((A' : ℝ) + 3) * (2 : ℝ) ^ (δ / 2 / 2 * n)) := by
            apply mul_le_mul_of_nonneg_right hCpn (by positivity)
        _ = ((Cp * (A' + 3) : ℕ) : ℝ) * (2 : ℝ) ^ (δ / 2 * n) := by rw [e]; push_cast; ring)
  refine ⟨M, C, hfin, fun n G _ hn hm => ?_⟩
  obtain ⟨w, hw, hO⟩ := hM n G hm
  exact ⟨w, hO, (hw hn).1, (hw hn).2⟩

/-! ## Explicit rate -/

open Groundwork Cor Asm T2 in
/-- **Counting Hamiltonian paths, explicit rate** (`cor:decision-search` with `thm:main-rate`): one
Turing machine and one constant `C` such that on the code of any graph with `n ≥ 2` vertices and
`m` edges it halts within `⌊C·2^{C(m+n)/√log₂(n+2)}⌋` steps with `#HP(G)` in binary. -/
theorem hamPaths_count_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 2 ≤ n →
        GraphProblems.Outputs M (GraphProblems.code G) (Nat.bits (hamPaths G).card)
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * ((G.edgeFinset.card : ℝ) + n) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
  obtain ⟨Q, iQ, A, habs, hA⟩ := t2_core
  obtain ⟨iP⟩ := Srch.apexS_poly Q
  obtain ⟨M, C, hfin, hM⟩ := t2_tm (Stepped.mapIn Srch.apexW Q)
    (fun {n} G _ w => 2 ≤ n → w = Nat.bits (hamPaths G).card) (2 * A) habs (fun {n} G _ => by
      obtain ⟨T, S, hR, hT, hS⟩ := hA (apex G)
      have hm := card_apex_edge_le G
      exact ⟨T, S, _, fun hn => bits_hp G hn, apexO_runs Q G hR, le_Xp_succ hT hm, le_Xp_succ hS hm⟩)
  refine ⟨M, C, hfin, fun n G _ hn => ?_⟩
  obtain ⟨w, hw, hO⟩ := hM n G
  rwa [← hw hn]

open Groundwork Cor Asm T2 in
/-- **Deciding the existence of a Hamiltonian path, explicit rate.** -/
theorem hamPaths_decision_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 2 ≤ n →
        GraphProblems.Outputs M (GraphProblems.code G) [decide (hamPaths G).Nonempty]
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * ((G.edgeFinset.card : ℝ) + n) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
  obtain ⟨Q, iQ, A, habs, hA⟩ := t2_core
  obtain ⟨iP⟩ := Srch.apexS_poly Q
  obtain ⟨iD⟩ := Srch.decS_poly (Stepped.mapIn Srch.apexW Q)
  obtain ⟨kp, hkp⟩ : ∃ kp, ∀ n, Pol kp n ((2 * (n + 1 + n * n) + 1) + (2 * ((n + 1) * (n + 1) + 1) + 1) + 4) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.add Pol.id
      (Pol.const 1)) (Pol.mul Pol.id Pol.id))) (Pol.const 1))
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.mul (Pol.add Pol.id (Pol.const 1))
        (Pol.add Pol.id (Pol.const 1))) (Pol.const 1))) (Pol.const 1)))
      (Pol.const 4)⟩
  obtain ⟨Bp, hBp⟩ := habs kp
  obtain ⟨M, C, hfin, hM⟩ := t2_tm (Srch.decS (Stepped.mapIn Srch.apexW Q))
    (fun {n} G _ w => 2 ≤ n → w = [decide (hamPaths G).Nonempty]) (2 * A + Bp + 3) habs (fun {n} G _ => by
      obtain ⟨T, S, hR, hT, hS⟩ := hA (apex G)
      have hm := card_apex_edge_le G
      have hT' := le_Xp_succ hT hm
      have hS' := le_Xp_succ hS hm
      refine ⟨_, _, _, fun hn => by rw [decide_hp G hn], Srch.decS_runs _ (apexO_runs Q G hR), ?_, ?_⟩
      · have := add_le_Xp hT' (const_le_Xp 2 n G.edgeFinset.card)
        push_cast
        exact le_Xp_mono this (by omega)
      · have hp := hBp n G.edgeFinset.card _ (hkp n)
        have hsz : size (GraphProblems.code G) + S + size (Nat.bits (Hamiltonian.hamCycles (apex G)).card) + 4 ≤
            S + ((2 * (n + 1 + n * n) + 1) + (2 * ((n + 1) * (n + 1) + 1) + 1) + 4) := by
          rw [Srch.size_code]; have := size_bits_hc_apex G; omega
        have h1 := add_le_Xp hS' hp
        have hsz' : ((size (GraphProblems.code G) + S + size (Nat.bits (Hamiltonian.hamCycles (apex G)).card) + 4 : ℕ) : ℝ) ≤
            (S : ℝ) + (((2 * (n + 1 + n * n) + 1) + (2 * ((n + 1) * (n + 1) + 1) + 1) + 4 : ℕ) : ℝ) := by
          exact_mod_cast hsz
        exact hsz'.trans (le_Xp_mono h1 (by omega)))
  refine ⟨M, C, hfin, fun n G _ hn => ?_⟩
  obtain ⟨w, hw, hO⟩ := hM n G
  rwa [← hw hn]

open Groundwork Cor Asm T2 in
/-- **Finding a Hamiltonian path, explicit rate**: the output is `[]` if `G` has no Hamiltonian
path, and otherwise the adjacency matrix of `(Fin n, X)` for some `X ∈ hamPaths G`. -/
theorem hamPaths_search_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 2 ≤ n →
        ∃ w : List Bool, GraphProblems.Outputs M (GraphProblems.code G) w
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * ((G.edgeFinset.card : ℝ) + n) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ ∧
          (hamPaths G = ∅ → w = []) ∧
          ((hamPaths G).Nonempty → ∃ X ∈ hamPaths G, w = GraphProblems.matrix (Hamiltonian.graphOf X)) := by
  obtain ⟨Q, iQ, A, habs, hA⟩ := t2_core
  obtain ⟨iP⟩ := Srch.apexS_poly Q
  obtain ⟨iS⟩ := Srch.searchS_poly (Stepped.mapIn Srch.apexW Q)
  obtain ⟨k1, hk1⟩ : ∃ k, ∀ n, Pol k n (n * n + 1) :=
    ⟨_, fun n => Pol.add (Pol.mul Pol.id Pol.id) (Pol.const 1)⟩
  obtain ⟨k2, hk2⟩ : ∃ k, ∀ n, Pol k n ((2 * ((n + 1) * (n + 1) + 1) + 1) + 30 * (n * n) + 10 * n + 40) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.mul (Pol.add Pol.id (Pol.const 1))
        (Pol.add Pol.id (Pol.const 1))) (Pol.const 1))) (Pol.const 1))
      (Pol.mul (Pol.const 30) (Pol.mul Pol.id Pol.id))) (Pol.mul (Pol.const 10) Pol.id)) (Pol.const 40)⟩
  obtain ⟨B1, hB1⟩ := habs k1
  obtain ⟨B2, hB2⟩ := habs k2
  obtain ⟨M, C, hfin, hM⟩ := t2_tm (Srch.searchS (Stepped.mapIn Srch.apexW Q))
    (fun {n} G _ w => 2 ≤ n → (hamPaths G = ∅ → w = []) ∧ ((hamPaths G).Nonempty →
      ∃ X ∈ hamPaths G, w = GraphProblems.matrix (Hamiltonian.graphOf X)))
    (B1 + (2 * A + 3 + 1) + (2 * A + B2 + 1)) habs (fun {n} G _ => by
      set m := G.edgeFinset.card
      set To := ⌊(2 : ℝ) ^ Xp (2 * A) n m⌋₊ with hTo
      set So := To + (2 * ((n + 1) * (n + 1) + 1) + 1) with hSo
      have hO : ∀ H : SimpleGraph (Fin n), H ≤ G → ∃ T w,
          (Stepped.mapIn Srch.apexW Q).Runs (GraphProblems.code H) T So w ∧ T ≤ To ∧
          size w ≤ So ∧ (w = [] ↔ ¬∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ H.edgeSet ∧
            (IsHamPath X ∧ 2 ≤ n)) := by
        intro H hHG
        classical
        obtain ⟨T, S, hR, hT, hS⟩ := hA (apex H)
        have hmH : (apex H).edgeFinset.card ≤ m + n := (card_apex_edge_le H).trans
          (Nat.add_le_add_right (card_edge_mono hHG) n)
        have hS' : S ≤ To := Nat.le_floor (le_Xp_succ hS hmH)
        refine ⟨T, _, apexO_runs Q H (hR.mono le_rfl (by omega)), Nat.le_floor (le_Xp_succ hT hmH), ?_,
          apex_nil_iff H⟩
        have := size_bits_hc_apex H
        omega
      obtain ⟨T, w, hR, hT, h1, h2⟩ := Srch.searchS_runs _ G _ To So hO
      refine ⟨T, _, w, fun hn => search_out_hp G hn h1 h2, hR, ?_, ?_⟩
      · have hToR : (To : ℝ) ≤ (2 : ℝ) ^ Xp (2 * A) n m := Nat.floor_le (by positivity)
        have e3 : (To : ℝ) + 3 ≤ (2 : ℝ) ^ Xp (2 * A + 3 + 1) n m := add_le_Xp hToR (const_le_Xp 3 n m)
        have e1 : ((n * n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ Xp B1 n m := hB1 n m _ (hk1 n)
        have e4 := mul_le_Xp (by positivity) e1 e3
        have hTR : (T : ℝ) ≤ ((n * n + 1 : ℕ) : ℝ) * ((To : ℝ) + 3) := by exact_mod_cast hT
        exact le_Xp_mono (hTR.trans e4) (by omega)
      · have hToR : (To : ℝ) ≤ (2 : ℝ) ^ Xp (2 * A) n m := Nat.floor_le (by positivity)
        have hp := hB2 n m _ (hk2 n)
        have h3 := add_le_Xp hToR hp
        have hsz : ((So + 30 * (n * n) + 10 * n + 40 : ℕ) : ℝ) ≤ (To : ℝ) +
            (((2 * ((n + 1) * (n + 1) + 1) + 1) + 30 * (n * n) + 10 * n + 40 : ℕ) : ℝ) := by
          rw [hSo]; push_cast; linarith
        exact le_Xp_mono (hsz.trans h3) (by omega))
  refine ⟨M, C, hfin, fun n G _ hn => ?_⟩
  obtain ⟨w, hw, hO⟩ := hM n G
  exact ⟨w, hO, (hw hn).1, (hw hn).2⟩

end EthFollowup.ExactHC
