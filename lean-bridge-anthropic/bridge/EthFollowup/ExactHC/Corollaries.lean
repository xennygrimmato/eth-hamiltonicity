/-
# Decision and search for Hamiltonian cycles at Turing-machine level (`cor:decision-search`)

`paper/main.tex`, `cor:decision-search`, parts *decide* and *search*, in both forms of the
counting theorems: fixed density (`theorem1`, `|E| ≤ D·n`, time `C·2^{δn}`) and explicit rate
(`theorem2`, time `C·2^{C(m+n)/√log₂(n+2)}`).

* `Cor.t1_core`, `Cor.t2_core`: the stepped machines behind `theorem1` (`Asm.hcM`) and `theorem2`
  (`T2.hcM2`), with their step and size bounds (the packages `exists_labelPackage`,
  `exists_ulabelPackage`).
* `Cor.t1_tm`, `Cor.t2_tm`: from a stepped machine with such bounds to one of Mathlib's Turing
  machines (`GraphProblems.tm_of_stepped`, `CountKSat.exists_tmW`), for any specification `P` of
  the output.
* `decision_TM`, `decision_TM_rate`: the bit `[decide (hamCycles G).Nonempty]`;
* `search_TM`, `search_TM_rate`: the empty word if `G` has no Hamiltonian cycle, else the adjacency
  matrix `GraphProblems.matrix (graphOf X)` of a Hamiltonian cycle `X ∈ hamCycles G`.

The search machine (`Srch.searchS`) makes `n² + 1` calls of the counting machine on subgraphs of
`G` (it also tries the non-edges, `SearchMachine.lean`); the factor `n² + 1` (the paper says
`m + 1`, which an adjacency test in front of each call would give) is absorbed into the constant
`C` of the same two bounds.

Standard axioms only.
-/
import EthFollowup.ExactHC.UPackage
import EthFollowup.ExactHC.SearchMachine

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

namespace Cor

open Groundwork Groundwork.Prog GraphProblems Asm Finset EthFollowup.Hamiltonian

/-! ## Small facts -/

theorem size_bits_le {k b : ℕ} (h : k < 2 ^ b) : size (Nat.bits k) ≤ 2 * b + 1 := by
  rw [LabelSystem.size_word, Nat.size_eq_bits_len]
  have := Nat.size_le.2 h
  omega

theorem size_bits_hc {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    size (Nat.bits (hamCycles H).card) ≤ 2 * (n * n + 1) + 1 := by
  apply size_bits_le
  rw [pow_succ]
  have := card_hamCycles_le H
  have : 0 < 2 ^ (n * n) := by positivity
  omega

theorem bits_length_ne_zero_iff (k : ℕ) : (Nat.bits k).length ≠ 0 ↔ k ≠ 0 := by
  rw [Ne, Srch.length_eq_zero_iff', Srch.bits_eq_nil_iff]

theorem decide_hc {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    decide ((Nat.bits (hamCycles H).card).length ≠ 0) = decide (hamCycles H).Nonempty := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, bits_length_ne_zero_iff,
    ← Finset.card_pos]
  omega

theorem bits_hc_nil_iff {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    Nat.bits (hamCycles H).card = [] ↔ ¬∃ X : Finset (Sym2 (Fin n)),
      (X : Set (Sym2 (Fin n))) ⊆ H.edgeSet ∧ (TwoRegular X ∧ (graphOf X).Connected) := by
  rw [Srch.bits_eq_nil_iff, Srch.card_hc_eq_zero_iff]

theorem card_edge_mono {n : ℕ} {H G : SimpleGraph (Fin n)} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (h : H ≤ G) : H.edgeFinset.card ≤ G.edgeFinset.card :=
  card_le_card (SimpleGraph.edgeFinset_mono h)

/-- The outputs of the search for a property of the form `hamCycles`. -/
theorem search_out_hc {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {w : List Bool}
    (h1 : (¬∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧
      (TwoRegular X ∧ (graphOf X).Connected)) → w = [])
    (h2 : (∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧
      (TwoRegular X ∧ (graphOf X).Connected)) → ∃ X : Finset (Sym2 (Fin n)),
        (X : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ (TwoRegular X ∧ (graphOf X).Connected) ∧ w = matrix (graphOf X)) :
    (hamCycles G = ∅ → w = []) ∧ ((hamCycles G).Nonempty → ∃ X ∈ hamCycles G, w = matrix (graphOf X)) := by
  refine ⟨fun he => h1 fun ⟨X, hX, hQ⟩ => ?_, fun ⟨X, hX⟩ => ?_⟩
  · have : X ∈ hamCycles G := Srch.mem_hc_iff.2 ⟨hX, hQ⟩
    rw [he] at this; exact absurd this (Finset.notMem_empty _)
  · obtain ⟨Y, hY, hQ, hw⟩ := h2 ⟨X, Srch.mem_hc_iff.1 hX⟩
    exact ⟨Y, Srch.mem_hc_iff.2 ⟨hY, hQ⟩, hw⟩

/-! ## The fixed-density form (`theorem1`) -/

section T1

/-- **The machine of `theorem1`**, as a stepped machine with its bounds. -/
theorem t1_core (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (Q : Stepped (List Bool) (List Bool)) (_ : IsPolyT Q) (A : ℕ),
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.card ≤ D * n →
        ∃ T : ℕ, Q.Runs (code G) T (A * (n + 2) ^ A) (Nat.bits (hamCycles G).card) ∧
          (T : ℝ) ≤ A * (2 : ℝ) ^ (δ / 2 * n) := by
  obtain ⟨c₀, hpk0⟩ := exists_labelPackage
  have hpk : ∀ g : ℕ, 1 ≤ g → Nonempty (HCPackage g c₀) := fun g hg =>
    (hpk0 g hg).map LabelPackage.toHCPackage
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
  obtain ⟨inst⟩ := hcM_poly NM pk hpoly
  exact ⟨_, inst, A, fun G _ hm => hA G hm⟩

/-- From a stepped machine with a polynomial size bound and the step bound `A·2^{(δ/2) n}` on the
graphs with at most `D·n` edges, to a Turing machine within `C·2^{δn}` steps. -/
theorem t1_tm (M : Stepped (List Bool) (List Bool)) [IsPolyT M] (D : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (P : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], List Bool → Prop) (As At : ℕ)
    (h : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.card ≤ D * n →
      ∃ T S w, P G w ∧ M.Runs (code G) T S w ∧ S ≤ As * (n + 2) ^ As ∧
        (T : ℝ) ≤ At * (2 : ℝ) ^ (δ / 2 * n)) :
    ∃ (TM : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (TM.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.card ≤ D * n →
        ∃ w, P G w ∧ GraphProblems.Outputs TM (code G) w ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  classical
  have hx : ∀ x : (Σ n : ℕ, {G : SimpleGraph (Fin n) // G.edgeFinset.card ≤ D * n}),
      ∃ T S w, P x.2.1 w ∧ M.Runs (code x.2.1) T S w ∧ S ≤ As * (x.1 + 2) ^ As ∧
        (T : ℝ) ≤ At * (2 : ℝ) ^ (δ / 2 * x.1) := fun x => h x.2.1 x.2.2
  choose T S w hP hR hS hT using hx
  obtain ⟨TM, C, hfin, hM⟩ := GraphProblems.tm_of_stepped M
    (ι := Σ n : ℕ, {G : SimpleGraph (Fin n) // G.edgeFinset.card ≤ D * n})
    (fun x => code x.2.1) w (fun x => x.1) hδ (As + At) 2 2
    (fun x => by
      simp only [length_code stMatrixLength]
      nlinarith)
    (fun x => ⟨T x, (hR x).mono le_rfl ((hS x).trans (Nat.mul_le_mul (by omega)
        (Nat.pow_le_pow_right (by omega) (by omega)))), (hT x).trans (by
        have : (0 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 * x.1) := by positivity
        have : (At : ℝ) ≤ ((As + At : ℕ) : ℝ) := by exact_mod_cast (by omega : At ≤ As + At)
        nlinarith)⟩)
  refine ⟨TM, C, hfin, fun n G inst hm => ?_⟩
  obtain rfl : inst = fun a b => Classical.propDecidable (G.Adj a b) := Subsingleton.elim _ _
  exact ⟨w ⟨n, G, hm⟩, hP ⟨n, G, hm⟩, hM ⟨n, G, hm⟩⟩

theorem add_const_le {T A k : ℕ} {x : ℝ} (hx : 0 ≤ x) (h : (T : ℝ) ≤ A * (2 : ℝ) ^ x) :
    ((T + k : ℕ) : ℝ) ≤ ((A + k : ℕ) : ℝ) * (2 : ℝ) ^ x := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ x := Real.one_le_rpow one_le_two hx
  push_cast
  nlinarith

end T1

/-! ## The explicit-rate form (`theorem2`) -/

section T2

open T2

theorem Xp_mono_m {A n m m' : ℕ} (h : m ≤ m') : Xp A n m ≤ Xp A n m' := by
  unfold Xp
  apply div_le_div_of_nonneg_right _ (sq_pos n).le
  have : (m : ℝ) ≤ m' := by exact_mod_cast h
  have : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  nlinarith

theorem le_Xp_mono {x : ℝ} {A A' n m : ℕ} (h : x ≤ (2 : ℝ) ^ Xp A n m) (hA : A ≤ A') :
    x ≤ (2 : ℝ) ^ Xp A' n m :=
  h.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono hA))

theorem le_Xp_mono_m {x : ℝ} {A n m m' : ℕ} (h : x ≤ (2 : ℝ) ^ Xp A n m) (hm : m ≤ m') :
    x ≤ (2 : ℝ) ^ Xp A n m' :=
  h.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono_m hm))

/-- **The machine of `theorem2`**, as a stepped machine with its bounds, and the absorption of
polynomials into `2^{B(m+n+2)/√log₂(n+2)}`. -/
theorem t2_core :
    ∃ (Q : Stepped (List Bool) (List Bool)) (_ : IsPolyT Q) (A : ℕ),
      (∀ k : ℕ, ∃ B : ℕ, ∀ n m x : ℕ, Pol k n x → (x : ℝ) ≤ (2 : ℝ) ^ Xp B n m) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ T S : ℕ,
        Q.Runs (code G) T S (Nat.bits (hamCycles G).card) ∧
        (T : ℝ) ≤ (2 : ℝ) ^ Xp A n G.edgeFinset.card ∧ (S : ℝ) ≤ (2 : ℝ) ^ Xp A n G.edgeFinset.card := by
  obtain ⟨c₀, hpk⟩ := exists_ulabelPackage
  obtain ⟨pk⟩ := hpk.map ULabelPackage.toUPackage
  obtain ⟨c, x₀, C₀, D, Alg, -, -, -, -, -, he, hyp, -⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨C₁, hC₁⟩ := geBody
  have hL := hyp.levels
  have hk := hyp.computesK
  obtain ⟨A, hA⟩ := hcM2_runs pk hC₁ hL hk _ hyp.solves (x₀ := x₀) fun l => he l
  obtain ⟨inst⟩ := hcM2_poly pk _ _ hL hk hyp.steps
  refine ⟨_, inst, A, fun k => ⟨2 * k * ((30 * C₀ + 1) ^ 2 * (Levels.Gen.K x₀ 0 ^ 30)),
    fun n m x hx => ?_⟩, fun G _ => hA G⟩
  obtain ⟨l, -, hK2, hup, hlo⟩ := kfacts hL hk (n := n) (List.replicate n (), []) (by simp)
  exact pol_le_Xp hK2 hup hlo hx

/-- From a stepped machine with steps and sizes `≤ 2^{A(m+n+2)/√log₂(n+2)}` to a Turing machine
within `⌊C·2^{C(m+n)/√log₂(n+2)}⌋` steps (the end of the proof of `theorem2_TM`). -/
theorem t2_tm (M : Stepped (List Bool) (List Bool)) [IsPolyT M]
    (P : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], List Bool → Prop) (A : ℕ)
    (habs : ∀ k : ℕ, ∃ B : ℕ, ∀ n m x : ℕ, Pol k n x → (x : ℝ) ≤ (2 : ℝ) ^ Xp B n m)
    (h : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ T S w, P G w ∧ M.Runs (code G) T S w ∧
      (T : ℝ) ≤ (2 : ℝ) ^ Xp A n G.edgeFinset.card ∧ (S : ℝ) ≤ (2 : ℝ) ^ Xp A n G.edgeFinset.card) :
    ∃ (TM : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (TM.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ w, P G w ∧
        GraphProblems.Outputs TM (code G) w ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * ((G.edgeFinset.card : ℝ) + n) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
  obtain ⟨TM, q, hfin, hM⟩ := CountKSat.exists_tmW M
  obtain ⟨BL, hBL⟩ := habs 3
  set Af := q + (A + 1) + q * (BL + A + 1 + 1) with hAf
  refine ⟨TM, 2 ^ (2 * Af), hfin, fun n G _ => ?_⟩
  obtain ⟨T, S, w, hP, hrun, hT, hS⟩ := h G
  obtain ⟨ev⟩ := hM (code G) T S _ hrun
  refine ⟨w, hP, ?_⟩
  set m := G.edgeFinset.card
  have hlen : (code G).length = n + 1 + n * n := length_code stMatrixLength G
  have hLx : ((code G).length : ℝ) ≤ (2 : ℝ) ^ Xp BL n m := by
    rw [hlen]
    refine hBL n m _ ?_
    unfold Pol
    have : (n + 2) ^ 2 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  have h1 : (T : ℝ) + 1 ≤ (2 : ℝ) ^ Xp (A + 1) n m := add_one_le_Xp hT
  have h2 : ((code G).length : ℝ) + S + 1 ≤ (2 : ℝ) ^ Xp (BL + A + 1 + 1) n m :=
    add_one_le_Xp (add_le_Xp hLx hS)
  have h3 := pow_le_Xp (by positivity) h2 q
  have h4 : (q : ℝ) * ((T : ℝ) + 1) ≤ (2 : ℝ) ^ Xp (q + (A + 1)) n m :=
    mul_le_Xp (Nat.cast_nonneg _) (const_le_Xp q n m) h1
  have h5 := mul_le_Xp (by positivity) h4 h3
  rw [← hAf] at h5
  have hle : q * (T + 1) * ((code G).length + S + 1) ^ q ≤
      ⌊((2 ^ (2 * Af) : ℕ) : ℝ) * (2 : ℝ) ^ (((2 ^ (2 * Af) : ℕ) : ℝ) * ((m : ℝ) + n) /
        Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
    apply Nat.le_floor
    have e1 : ((q * (T + 1) * ((code G).length + S + 1) ^ q : ℕ) : ℝ) =
        (q : ℝ) * ((T : ℝ) + 1) * (((code G).length : ℝ) + S + 1) ^ q := by push_cast; ring
    rw [e1]
    refine h5.trans ((Xp_split Af n m).trans ?_)
    have hC : (Af : ℝ) ≤ ((2 ^ (2 * Af) : ℕ) : ℝ) := by
      have : Af ≤ 2 ^ (2 * Af) := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact_mod_cast this
    have e2 : (2 : ℝ) ^ (2 * (Af : ℝ)) = ((2 ^ (2 * Af) : ℕ) : ℝ) := by
      rw [show (2 : ℝ) * (Af : ℝ) = ((2 * Af : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]; push_cast; ring
    rw [e2, show Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) = T2.sq n from rfl]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have : (0 : ℝ) ≤ (m : ℝ) + n := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC this) (T2.sq_pos n).le
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩

end T2

end Cor

open Groundwork Cor Asm in
/-- **Deciding Hamiltonicity, fixed density** (`cor:decision-search`, with `thm:main-delta`): for
every `δ > 0` and `D` a Turing machine of Mathlib with finite alphabets and a constant `C` such
that on the code of any graph with at most `D·n` edges it halts within `⌊C·2^{δn}⌋` steps with the
one bit «`G` has a Hamiltonian cycle». -/
theorem decision_TM (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.card ≤ D * n →
        GraphProblems.Outputs M (GraphProblems.code G) [decide (Hamiltonian.hamCycles G).Nonempty]
          ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨Q, iQ, A, hA⟩ := t1_core δ hδ D
  obtain ⟨iD⟩ := Srch.decS_poly Q
  obtain ⟨As, hAs⟩ : ∃ As, ∀ n, Pol As n ((2 * (n + 1 + n * n) + 1) + A * (n + 2) ^ A +
      (2 * (n * n + 1) + 1) + 4) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.add Pol.id
      (Pol.const 1)) (Pol.mul Pol.id Pol.id))) (Pol.const 1)) (Pol.mul (Pol.const A) (Pol.pow_n A)))
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.mul Pol.id Pol.id) (Pol.const 1))) (Pol.const 1)))
      (Pol.const 4)⟩
  obtain ⟨M, C, hfin, hM⟩ := t1_tm (Srch.decS Q) D hδ
    (fun G _ w => w = [decide (Hamiltonian.hamCycles G).Nonempty]) As (A + 2) (fun {n} G _ hm => by
      obtain ⟨T, hR, hT⟩ := hA G hm
      refine ⟨_, _, _, ?_, Srch.decS_runs Q hR, ?_, add_const_le (by positivity) hT⟩
      · simp only [decide_hc]
      · refine le_trans ?_ (hAs n)
        rw [Srch.size_code]
        have := size_bits_hc G
        omega)
  refine ⟨M, C, hfin, fun n G _ hm => ?_⟩
  obtain ⟨w, rfl, hw⟩ := hM n G hm
  exact hw

open Groundwork Cor Asm in
/-- **Finding a Hamiltonian cycle, fixed density** (`cor:decision-search`, with `thm:main-delta`):
for every `δ > 0` and `D` a Turing machine of Mathlib with finite alphabets and a constant `C` such
that on the code of any graph `G` with at most `D·n` edges it halts within `⌊C·2^{δn}⌋` steps with
a word `w`: `w = []` if `G` has no Hamiltonian cycle, and otherwise `w` is the adjacency matrix
(`GraphProblems.matrix`, row by row) of the graph `(Fin n, X)` of a Hamiltonian cycle
`X ∈ hamCycles G`. -/
theorem search_TM (δ : ℝ) (hδ : 0 < δ) (D : ℕ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.card ≤ D * n →
        ∃ w : List Bool, GraphProblems.Outputs M (GraphProblems.code G) w ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ ∧
          (Hamiltonian.hamCycles G = ∅ → w = []) ∧
          ((Hamiltonian.hamCycles G).Nonempty →
            ∃ X ∈ Hamiltonian.hamCycles G, w = GraphProblems.matrix (Hamiltonian.graphOf X)) := by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨Q, iQ, A, hA⟩ := t1_core (δ / 2) hδ2 D
  obtain ⟨iS⟩ := Srch.searchS_poly Q
  obtain ⟨Cp, hCp⟩ := Groundwork.exists_pow_le 2 (show (0 : ℝ) < δ / 4 by positivity)
  obtain ⟨As, hAs⟩ : ∃ As, ∀ n, Pol As n ((A * (n + 2) ^ A + (2 * (n * n + 1) + 1)) +
      30 * (n * n) + 10 * n + 40) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const A) (Pol.pow_n A))
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.mul Pol.id Pol.id) (Pol.const 1))) (Pol.const 1)))
      (Pol.mul (Pol.const 30) (Pol.mul Pol.id Pol.id))) (Pol.mul (Pol.const 10) Pol.id)) (Pol.const 40)⟩
  obtain ⟨M, C, hfin, hM⟩ := t1_tm (Srch.searchS Q) D hδ
    (fun G _ w => (Hamiltonian.hamCycles G = ∅ → w = []) ∧ ((Hamiltonian.hamCycles G).Nonempty →
      ∃ X ∈ Hamiltonian.hamCycles G, w = GraphProblems.matrix (Hamiltonian.graphOf X)))
    As (Cp * (A + 3)) (fun {n} G _ hm => by
      set To := ⌊(A : ℝ) * (2 : ℝ) ^ (δ / 2 / 2 * n)⌋₊ with hTo
      set So := A * (n + 2) ^ A + (2 * (n * n + 1) + 1) with hSo
      have hO : ∀ H : SimpleGraph (Fin n), H ≤ G → ∃ T w, Q.Runs (GraphProblems.code H) T So w ∧ T ≤ To ∧
          size w ≤ So ∧ (w = [] ↔ ¬∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ H.edgeSet ∧
            (Hamiltonian.TwoRegular X ∧ (Hamiltonian.graphOf X).Connected)) := by
        intro H hHG
        classical
        obtain ⟨T, hR, hT⟩ := hA H ((card_edge_mono hHG).trans hm)
        refine ⟨T, _, hR.mono le_rfl (by omega), Nat.le_floor hT, ?_, bits_hc_nil_iff H⟩
        have := size_bits_hc H
        omega
      obtain ⟨T, w, hR, hT, h1, h2⟩ := Srch.searchS_runs Q G _ To So hO
      refine ⟨T, _, w, search_out_hc G h1 h2, hR, hAs n, ?_⟩
      -- the steps: `(n² + 1)(To + 3) ≤ Cp (A + 3) 2^{(δ/2) n}`
      have hE : (1 : ℝ) ≤ (2 : ℝ) ^ (δ / 2 / 2 * n) := Real.one_le_rpow one_le_two (by positivity)
      have hToR : (To : ℝ) ≤ A * (2 : ℝ) ^ (δ / 2 / 2 * n) := Nat.floor_le (by positivity)
      have hn2 : ((n * n + 1 : ℕ) : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by push_cast; nlinarith
      have hCpn := hCp n
      have e : (2 : ℝ) ^ (δ / 2 * n) = (2 : ℝ) ^ (δ / 4 * n) * (2 : ℝ) ^ (δ / 2 / 2 * n) := by
        rw [← Real.rpow_add two_pos]; congr 1; ring
      have hTR : (T : ℝ) ≤ ((n * n + 1 : ℕ) : ℝ) * ((To : ℝ) + 3) := by exact_mod_cast hT
      have h3 : (To : ℝ) + 3 ≤ ((A : ℝ) + 3) * (2 : ℝ) ^ (δ / 2 / 2 * n) := by nlinarith
      calc (T : ℝ) ≤ ((n * n + 1 : ℕ) : ℝ) * ((To : ℝ) + 3) := hTR
        _ ≤ ((n : ℝ) + 2) ^ 2 * (((A : ℝ) + 3) * (2 : ℝ) ^ (δ / 2 / 2 * n)) := by
            apply mul_le_mul hn2 h3 (by positivity) (by positivity)
        _ ≤ (Cp * (2 : ℝ) ^ (δ / 4 * n)) * (((A : ℝ) + 3) * (2 : ℝ) ^ (δ / 2 / 2 * n)) := by
            apply mul_le_mul_of_nonneg_right hCpn (by positivity)
        _ = ((Cp * (A + 3) : ℕ) : ℝ) * (2 : ℝ) ^ (δ / 2 * n) := by rw [e]; push_cast; ring)
  refine ⟨M, C, hfin, fun n G _ hm => ?_⟩
  obtain ⟨w, ⟨h1, h2⟩, hw⟩ := hM n G hm
  exact ⟨w, hw, h1, h2⟩

open Groundwork Cor Asm T2 in
/-- **Deciding Hamiltonicity, explicit rate** (`cor:decision-search`, with `thm:main-rate`): one
Turing machine of Mathlib with finite alphabets and one constant `C` such that on the code of ANY
graph `G` with `n` vertices and `m` edges it halts within `⌊C·2^{C(m+n)/√log₂(n+2)}⌋` steps with
the one bit «`G` has a Hamiltonian cycle». -/
theorem decision_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        GraphProblems.Outputs M (GraphProblems.code G) [decide (Hamiltonian.hamCycles G).Nonempty]
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * ((G.edgeFinset.card : ℝ) + n) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ := by
  obtain ⟨Q, iQ, A, habs, hA⟩ := t2_core
  obtain ⟨iD⟩ := Srch.decS_poly Q
  obtain ⟨kp, hkp⟩ : ∃ kp, ∀ n, Pol kp n ((2 * (n + 1 + n * n) + 1) + (2 * (n * n + 1) + 1) + 4) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.add Pol.id
      (Pol.const 1)) (Pol.mul Pol.id Pol.id))) (Pol.const 1))
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.mul Pol.id Pol.id) (Pol.const 1))) (Pol.const 1)))
      (Pol.const 4)⟩
  obtain ⟨Bp, hBp⟩ := habs kp
  obtain ⟨M, C, hfin, hM⟩ := t2_tm (Srch.decS Q)
    (fun G _ w => w = [decide (Hamiltonian.hamCycles G).Nonempty]) (A + Bp + 3) habs (fun {n} G _ => by
      obtain ⟨T, S, hR, hT, hS⟩ := hA G
      refine ⟨_, _, _, ?_, Srch.decS_runs Q hR, ?_, ?_⟩
      · simp only [decide_hc]
      · have := add_le_Xp hT (const_le_Xp 2 n G.edgeFinset.card)
        push_cast
        exact le_Xp_mono this (by omega)
      · have hp := hBp n G.edgeFinset.card _ (hkp n)
        have hsz : size (GraphProblems.code G) + S + size (Nat.bits (Hamiltonian.hamCycles G).card) + 4 ≤
            S + ((2 * (n + 1 + n * n) + 1) + (2 * (n * n + 1) + 1) + 4) := by
          rw [Srch.size_code]; have := size_bits_hc G; omega
        have h1 := add_le_Xp hS hp
        have hsz' : ((size (GraphProblems.code G) + S + size (Nat.bits (Hamiltonian.hamCycles G).card) + 4 : ℕ) : ℝ) ≤
            (S : ℝ) + (((2 * (n + 1 + n * n) + 1) + (2 * (n * n + 1) + 1) + 4 : ℕ) : ℝ) := by
          exact_mod_cast hsz
        exact hsz'.trans (le_Xp_mono h1 (by omega)))
  refine ⟨M, C, hfin, fun n G _ => ?_⟩
  obtain ⟨w, rfl, hw⟩ := hM n G
  exact hw

open Groundwork Cor Asm T2 in
/-- **Finding a Hamiltonian cycle, explicit rate** (`cor:decision-search`, with `thm:main-rate`):
one Turing machine of Mathlib with finite alphabets and one constant `C` such that on the code of
ANY graph `G` with `n` vertices and `m` edges it halts within `⌊C·2^{C(m+n)/√log₂(n+2)}⌋` steps
with a word `w`: `w = []` if `G` has no Hamiltonian cycle, and otherwise `w` is the adjacency
matrix of the graph `(Fin n, X)` of a Hamiltonian cycle `X ∈ hamCycles G`. -/
theorem search_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ∃ w : List Bool, GraphProblems.Outputs M (GraphProblems.code G) w
          ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * ((G.edgeFinset.card : ℝ) + n) /
            Real.sqrt (Real.logb 2 ((n : ℝ) + 2)))⌋₊ ∧
          (Hamiltonian.hamCycles G = ∅ → w = []) ∧
          ((Hamiltonian.hamCycles G).Nonempty →
            ∃ X ∈ Hamiltonian.hamCycles G, w = GraphProblems.matrix (Hamiltonian.graphOf X)) := by
  obtain ⟨Q, iQ, A, habs, hA⟩ := t2_core
  obtain ⟨iS⟩ := Srch.searchS_poly Q
  obtain ⟨k1, hk1⟩ : ∃ k, ∀ n, Pol k n (n * n + 1) :=
    ⟨_, fun n => Pol.add (Pol.mul Pol.id Pol.id) (Pol.const 1)⟩
  obtain ⟨k2, hk2⟩ : ∃ k, ∀ n, Pol k n ((2 * (n * n + 1) + 1) + 30 * (n * n) + 10 * n + 40) :=
    ⟨_, fun n => Pol.add (Pol.add (Pol.add
      (Pol.add (Pol.mul (Pol.const 2) (Pol.add (Pol.mul Pol.id Pol.id) (Pol.const 1))) (Pol.const 1))
      (Pol.mul (Pol.const 30) (Pol.mul Pol.id Pol.id))) (Pol.mul (Pol.const 10) Pol.id)) (Pol.const 40)⟩
  obtain ⟨B1, hB1⟩ := habs k1
  obtain ⟨B2, hB2⟩ := habs k2
  obtain ⟨M, C, hfin, hM⟩ := t2_tm (Srch.searchS Q)
    (fun G _ w => (Hamiltonian.hamCycles G = ∅ → w = []) ∧ ((Hamiltonian.hamCycles G).Nonempty →
      ∃ X ∈ Hamiltonian.hamCycles G, w = GraphProblems.matrix (Hamiltonian.graphOf X)))
    (B1 + (A + 3 + 1) + (A + B2 + 1)) habs (fun {n} G _ => by
      set m := G.edgeFinset.card
      set To := ⌊(2 : ℝ) ^ Xp A n m⌋₊ with hTo
      set So := To + (2 * (n * n + 1) + 1) with hSo
      have hO : ∀ H : SimpleGraph (Fin n), H ≤ G → ∃ T w, Q.Runs (GraphProblems.code H) T So w ∧ T ≤ To ∧
          size w ≤ So ∧ (w = [] ↔ ¬∃ X : Finset (Sym2 (Fin n)), (X : Set (Sym2 (Fin n))) ⊆ H.edgeSet ∧
            (Hamiltonian.TwoRegular X ∧ (Hamiltonian.graphOf X).Connected)) := by
        intro H hHG
        classical
        obtain ⟨T, S, hR, hT, hS⟩ := hA H
        have hmH := card_edge_mono hHG
        have hS' : S ≤ To := Nat.le_floor (le_Xp_mono_m hS hmH)
        refine ⟨T, _, hR.mono le_rfl (by omega), Nat.le_floor (le_Xp_mono_m hT hmH), ?_, bits_hc_nil_iff H⟩
        have := size_bits_hc H
        omega
      obtain ⟨T, w, hR, hT, h1, h2⟩ := Srch.searchS_runs Q G _ To So hO
      refine ⟨T, _, w, search_out_hc G h1 h2, hR, ?_, ?_⟩
      · have hToR : (To : ℝ) ≤ (2 : ℝ) ^ Xp A n m := Nat.floor_le (by positivity)
        have e3 : (To : ℝ) + 3 ≤ (2 : ℝ) ^ Xp (A + 3 + 1) n m := add_le_Xp hToR (const_le_Xp 3 n m)
        have e1 : ((n * n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ Xp B1 n m := hB1 n m _ (hk1 n)
        have e4 := mul_le_Xp (by positivity) e1 e3
        have hTR : (T : ℝ) ≤ ((n * n + 1 : ℕ) : ℝ) * ((To : ℝ) + 3) := by exact_mod_cast hT
        exact le_Xp_mono (hTR.trans e4) (by omega)
      · have hToR : (To : ℝ) ≤ (2 : ℝ) ^ Xp A n m := Nat.floor_le (by positivity)
        have hp := hB2 n m _ (hk2 n)
        have h3 := add_le_Xp hToR hp
        have hsz : ((So + 30 * (n * n) + 10 * n + 40 : ℕ) : ℝ) ≤ (To : ℝ) +
            (((2 * (n * n + 1) + 1) + 30 * (n * n) + 10 * n + 40 : ℕ) : ℝ) := by
          rw [hSo]; push_cast; linarith
        exact le_Xp_mono (hsz.trans h3) (by omega))
  refine ⟨M, C, hfin, fun n G _ => ?_⟩
  obtain ⟨w, ⟨h1, h2⟩, hw⟩ := hM n G
  exact ⟨w, hw, h1, h2⟩

end EthFollowup.ExactHC
