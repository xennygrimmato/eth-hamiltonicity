/-
# Randomized decision of directed Hamiltonicity

Directed analogue of `HamiltonianIsolation.lean`, `HamiltonianDecision.lean` and
`HamiltonianDecisionFraction.lean`. For any CNF `H` on the arc variables, the directed Cut&Count
count with `H` added is `≡ #{directed Hamiltonian cycles X : H(1_X)} (mod 2)`. With the isolation
lemma this gives a one-sided-error test with success `≥ exp(−δ|A|)` for every `δ > 0`, and one
machine per `(Δ, k)` for digraphs of maximum in- and out-degree `≤ Δ`.
-/
import EthFollowup.DirectedHamiltonianParity
import EthFollowup.HashCNF
import EthFollowup.IsolationAnalysis

namespace EthFollowup.DirectedHamiltonian

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open EthFollowup EthFollowup.Hamiltonian EthFollowup.Isolation
open Finset Real

variable {n : ℕ} (A : Finset (Fin n × Fin n))

def arcIndicator (X : Finset (Fin n × Fin n)) : SAT.Assignment (ArcVar A) :=
  fun e => decide ((e : Fin n × Fin n) ∈ X)

def dirCutCNFWith (H : SAT.CNF (ArcVar A)) (r : Fin n) : SAT.CNF (DVar A) :=
  dirCutCNF A r ∪ CNF.map Sum.inl H

theorem arcIndicator_arcsOf (a : SAT.Assignment (DVar A)) :
    arcIndicator A (arcsOf A a) = a ∘ Sum.inl := by
  funext e
  simp only [arcIndicator, Function.comp]
  cases h : a (Sum.inl e)
  · simp only [decide_eq_false_iff_not, mem_arcsOf, not_exists]
    intro _ h'
    simp_all
  · simp only [decide_eq_true_eq, mem_arcsOf]
    exact ⟨e.2, h⟩

theorem dirCutCNFWith_eval (H : SAT.CNF (ArcVar A)) (r : Fin n) (a : SAT.Assignment (DVar A)) :
    SAT.CNF.eval a (dirCutCNFWith A H r) = true ↔
      (CycleCover (arcsOf A a) ∧ (∀ e ∈ arcsOf A a, cutOf A a e.1 = cutOf A a e.2) ∧
        cutOf A a r = false) ∧ SAT.CNF.eval (arcIndicator A (arcsOf A a)) H = true := by
  rw [dirCutCNFWith, CNF.eval_union, CNF.map_eval, dirCutCNF_eval, arcIndicator_arcsOf]

theorem count_dirCutCNFWith (H : SAT.CNF (ArcVar A)) (r : Fin n) :
    SAT.count (dirCutCNFWith A H r) =
      ∑ X ∈ (cycleCovers A).filter (fun X => SAT.CNF.eval (arcIndicator A X) H = true),
        (cuts (undirected X) r).card := by
  classical
  unfold SAT.count SAT.satisfyingAssignments
  rw [Finset.card_eq_sum_card_fiberwise (f := arcsOf A)
    (t := (cycleCovers A).filter (fun X => SAT.CNF.eval (arcIndicator A X) H = true))]
  · refine Finset.sum_congr rfl fun X hX => ?_
    obtain ⟨hX2, hXH⟩ := Finset.mem_filter.1 hX
    have hXsub : X ⊆ A := Finset.mem_powerset.1 (Finset.mem_filter.1 hX2).1
    have hXcov : CycleCover X := (Finset.mem_filter.1 hX2).2
    refine Finset.card_bij' (fun a _ => cutOf A a)
      (fun c _ => Sum.elim (fun e : ArcVar A => decide ((e : Fin n × Fin n) ∈ X)) c)
      ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨hsat, rfl⟩ := ha
      obtain ⟨⟨-, hcons, hroot⟩, -⟩ := (dirCutCNFWith_eval A H r a).1 hsat
      simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and, consistent_undirected_iff]
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
      refine ⟨(dirCutCNFWith_eval A H r _).2 ?_, hE⟩
      rw [hE]
      exact ⟨⟨hXcov, hc.1, hc.2⟩, hXH⟩
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨-, hX⟩ := ha
      funext x
      rcases x with e | v
      · simp only [Sum.elim_inl]
        rw [← hX]
        exact congrFun (arcIndicator_arcsOf A a) e
      · rfl
    · intro c _
      rfl
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
    obtain ⟨⟨hcov, -, -⟩, hH⟩ := (dirCutCNFWith_eval A H r a).1 ha
    simp only [Finset.coe_filter, cycleCovers, Finset.mem_filter, Finset.mem_powerset,
      Set.mem_ofPred_eq]
    exact ⟨⟨arcsOf_subset A a, hcov⟩, hH⟩

theorem count_dirCutCNFWith_mod_two (H : SAT.CNF (ArcVar A)) (r : Fin n) :
    (SAT.count (dirCutCNFWith A H r) : ZMod 2) =
      (((dirHamCycles A).filter fun X => SAT.CNF.eval (arcIndicator A X) H = true).card :
        ZMod 2) := by
  rw [count_dirCutCNFWith, Nat.cast_sum]
  simp_rw [cuts_card_mod_two]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.filter_filter, dirHamCycles, Finset.filter_filter]
  congr 2
  ext X
  simp only [Finset.mem_filter]
  tauto

/-! ### Isolation -/

def dhcPoints : Finset (ArcVar A → Bool) := (dirHamCycles A).image (arcIndicator A)

theorem arcIndicator_injOn : Set.InjOn (arcIndicator A) (dirHamCycles A : Set _) := by
  intro X hX Y hY h
  have hXs : X ⊆ A := Finset.mem_powerset.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hX).1).1
  have hYs : Y ⊆ A := Finset.mem_powerset.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hY).1).1
  ext e
  constructor
  · intro he
    have := congrFun h ⟨e, hXs he⟩
    simp only [arcIndicator, he, decide_true] at this
    exact of_decide_eq_true this.symm
  · intro he
    have := congrFun h ⟨e, hYs he⟩
    simp only [arcIndicator, he, decide_true] at this
    exact of_decide_eq_true this

theorem card_dhcPoints : (dhcPoints A).card = (dirHamCycles A).card :=
  Finset.card_image_of_injOn (arcIndicator_injOn A)

theorem dir_restricted_count_eq {k m : ℕ} (As : Sys (ArcVar A) k m) (b : Fin m → ZMod 2)
    (D : Finset (ArcVar A)) (α : ArcVar A → Bool) :
    ((dirHamCycles A).filter fun X =>
        SAT.CNF.eval (arcIndicator A X) (hashCNF As b D α) = true).card =
      ((dhcPoints A).filter fun y => applySys As y = b ∧ ∀ e ∈ D, y e = α e).card := by
  rw [dhcPoints, Finset.filter_image, Finset.card_image_of_injOn]
  · congr 1
    ext X
    simp only [Finset.mem_filter, Function.comp, hashCNF_eval]
  · exact (arcIndicator_injOn A).mono (Finset.coe_subset.2 (Finset.filter_subset _ _))

/-- **Soundness.** -/
theorem dir_decision_sound {k m : ℕ} (r : Fin n) (h0 : dirHamCycles A = ∅)
    (As : Sys (ArcVar A) k m) (b : Fin m → ZMod 2) (D : Finset (ArcVar A)) (α : ArcVar A → Bool) :
    (SAT.count (dirCutCNFWith A (hashCNF As b D α) r) : ZMod 2) = 0 := by
  rw [count_dirCutCNFWith_mod_two, h0, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]

/-- **Completeness with an explicit fraction.** -/
theorem dir_decision_complete {k m rad d : ℕ} (r : Fin n)
    (Hm : 2 * (dirHamCycles A).card * (2 ^ k * (A.card ^ k + (A.card - rad) ^ k)) ^ m ≤
      2 ^ m * (A.card ^ k * 2 ^ k) ^ m)
    (hd : 2 * rad ≤ d) (hdN : d ≤ A.card) :
    (dirHamCycles A).card * Fintype.card (Sys (ArcVar A) k m) * 2 ^ (A.card - d) ≤
      2 * ballVol (ArcVar A) rad *
        (((univ : Finset (Sys (ArcVar A) k m × (Fin m → ZMod 2))) ×ˢ
            ((univ : Finset (ArcVar A)).powersetCard d ×ˢ (univ : Finset (ArcVar A → Bool)))).filter
          fun ω => (SAT.count (dirCutCNFWith A (hashCNF ω.1.1 ω.1.2 ω.2.1 ω.2.2) r) : ZMod 2) = 1).card := by
  have hN : Fintype.card (ArcVar A) = A.card := Fintype.card_coe _
  have hiso := isolation_count (ι := ArcVar A) (k := k) (m := m) (r := rad) (d := d)
    (dhcPoints A) (by rw [card_dhcPoints, hN]; exact Hm) hd (by rw [hN]; exact hdN)
  rw [card_dhcPoints, hN] at hiso
  refine hiso.trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
  intro ω hω
  rw [Finset.mem_filter] at hω ⊢
  refine ⟨hω.1, ?_⟩
  rw [count_dirCutCNFWith_mod_two, dir_restricted_count_eq, hω.2, Nat.cast_one]

/-- **Completeness with success `exp(−δ|A|)`.** -/
theorem dirHamDecision_fraction {δ : ℝ} (hδ : 0 < δ) :
    ∃ k N₀ : ℕ, ∀ (n : ℕ) (A : Finset (Fin n × Fin n)) (r₀ : Fin n),
      (dirHamCycles A).Nonempty → N₀ ≤ A.card →
      ∃ m d : ℕ,
        exp (-(δ * A.card)) *
            (((univ : Finset (Sys (ArcVar A) k m × (Fin m → ZMod 2))) ×ˢ
              ((univ : Finset (ArcVar A)).powersetCard d ×ˢ (univ : Finset (ArcVar A → Bool)))).card : ℝ) ≤
          ((((univ : Finset (Sys (ArcVar A) k m × (Fin m → ZMod 2))) ×ˢ
              ((univ : Finset (ArcVar A)).powersetCard d ×ˢ (univ : Finset (ArcVar A → Bool)))).filter
            fun ω => (SAT.count (dirCutCNFWith A (hashCNF ω.1.1 ω.1.2 ω.2.1 ω.2.2) r₀) : ZMod 2) = 1).card
            : ℝ) := by
  obtain ⟨k, N₀, hfrac⟩ := isolation_fraction.{0} hδ
  refine ⟨k, N₀, fun n A r₀ hne hN => ?_⟩
  have hNc : Fintype.card (ArcVar A) = A.card := Fintype.card_coe _
  have hSne : (dhcPoints A).Nonempty := by
    obtain ⟨X, hX⟩ := hne; exact ⟨_, Finset.mem_image_of_mem _ hX⟩
  obtain ⟨m, rad, d, hd, hdN, Hm, hest⟩ :=
    hfrac (ArcVar A) (dhcPoints A) hSne (by rw [hNc]; exact hN)
  refine ⟨m, d, ?_⟩
  rw [card_dhcPoints, hNc] at Hm hest
  rw [hNc] at hdN
  have hcomp := dir_decision_complete A r₀ Hm hd hdN
  rw [card_hashSpace, hNc]
  set odd := ((((univ : Finset (Sys (ArcVar A) k m × (Fin m → ZMod 2))) ×ˢ
      ((univ : Finset (ArcVar A)).powersetCard d ×ˢ (univ : Finset (ArcVar A → Bool)))).filter
        fun ω => (SAT.count (dirCutCNFWith A (hashCNF ω.1.1 ω.1.2 ω.2.1 ω.2.2) r₀) : ZMod 2) = 1).card)
  set N := A.card
  set V := ballVol (ArcVar A) rad
  set Sy := Fintype.card (Sys (ArcVar A) k m)
  set s := (dirHamCycles A).card
  have hs : 1 ≤ s := hne.card_pos
  have hcompR : (s : ℝ) * Sy * 2 ^ (N - d) ≤ 2 * V * odd := by exact_mod_cast hcomp
  have hV : (0 : ℝ) < V := by
    rcases Nat.eq_zero_or_pos V with h0 | h0
    · exfalso
      have hle : (s : ℝ) * Sy * 2 ^ (N - d) ≤ 0 := by rw [h0] at hcompR; simpa using hcompR
      have hE : Nonempty (ArcVar A) := by
        obtain ⟨X, hX⟩ := hne
        have hX2 := (Finset.mem_filter.1 hX).1
        have hcov : CycleCover X := (Finset.mem_filter.1 hX2).2
        have hsub : X ⊆ A := Finset.mem_powerset.1 (Finset.mem_filter.1 hX2).1
        obtain ⟨e, he⟩ : (X.filter fun e => e.1 = r₀).Nonempty :=
          Finset.card_pos.1 (by rw [(hcov r₀).1]; norm_num)
        exact ⟨⟨e, hsub (Finset.mem_filter.1 he).1⟩⟩
      have hSy : (0 : ℝ) < Sy := by
        have : 0 < Sy := Fintype.card_pos_iff.2 ⟨fun _ => (fun _ => Classical.arbitrary _, fun _ => true)⟩
        exact_mod_cast this
      have : (0 : ℝ) < (s : ℝ) * Sy * 2 ^ (N - d) := by
        have : (1 : ℝ) ≤ s := by exact_mod_cast hs
        positivity
      linarith
    · exact_mod_cast h0
  push_cast at hest ⊢
  have h2 : (2 : ℝ) ^ d * 2 ^ (N - d) = 2 ^ N := by rw [← pow_add, Nat.add_sub_cancel' hdN]
  have hkey : 2 * V * (exp (-(δ * N)) * (Sy * 2 ^ m * N.choose d * 2 ^ N)) ≤ 2 * V * odd := by
    calc 2 * V * (exp (-(δ * N)) * (Sy * 2 ^ m * N.choose d * 2 ^ N))
        = exp (-(δ * N)) * (2 * V * 2 ^ m * N.choose d * 2 ^ d) * (Sy * 2 ^ (N - d)) := by
          rw [← h2]; ring
      _ ≤ s * (Sy * 2 ^ (N - d)) := mul_le_mul_of_nonneg_right hest (by positivity)
      _ = s * Sy * 2 ^ (N - d) := by ring
      _ ≤ 2 * V * odd := hcompR
  exact le_of_mul_le_mul_left hkey (by positivity)

/-! ### The machine -/

noncomputable def dirCutCNFWithFin (H : SAT.CNF (ArcVar A)) (r : Fin n) :
    SAT.CNF (Fin (Fintype.card (DVar A))) :=
  CNF.relabel (Fintype.equivFin (DVar A)) (dirCutCNFWith A H r)

/-- **The directed decision machine.** -/
theorem dirHamDecision_subexponential (Δ k : ℕ)
    (h : ExactCountAndSatStatement (max Δ (max 3 (max k 1)))
      (le_max_of_le_right (le_max_of_le_left (by norm_num)))) :
    ∃ (machine : Computation.PrimitiveMachine)
      (countTape : Fin machine.tapeCount) (C A' S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A' ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (A : Finset (Fin n × Fin n)) (r : Fin n) (m : ℕ)
        (As : Sys (ArcVar A) k m) (b : Fin m → ZMod 2) (D : Finset (ArcVar A))
        (α : ArcVar A → Bool),
        (∀ v, (A.filter fun a => a.1 = v).card ≤ Δ) →
        (∀ v, (A.filter fun a => a.2 = v).card ≤ Δ) →
        ∃ (N time : ℕ) (final : LocatedCfg machine),
          Computation.Trace (locatedStep machine) time
            (locatedInit machine (Encoding.encodeCNF (dirCutCNFWithFin A (hashCNF As b D α) r)))
            final ∧
          final.config.tapes countTape = Turing.Tape.mk₁ ((countWord N).map some) ∧
          BinaryArithmetic.toNat (countWord N) = N ∧
          (N : ZMod 2) = (SAT.count (dirCutCNFWith A (hashCNF As b D α) r) : ZMod 2) ∧
          (time : ℝ) ≤ SqrtLog.Statement.runtimeBound C A' d
            (Encoding.formulaBitLength (dirCutCNFWithFin A (hashCNF As b D α) r))
            (Fintype.card (DVar A)) ∧
          ∀ (prefixSteps : ℕ) (intermediate : LocatedCfg machine),
            prefixSteps ≤ time →
            Computation.Trace (locatedStep machine) prefixSteps
              (locatedInit machine
                (Encoding.encodeCNF (dirCutCNFWithFin A (hashCNF As b D α) r))) intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength (dirCutCNFWithFin A (hashCNF As b D α) r) : ℝ) + 1) ^ e := by
  obtain ⟨machine, countTape, _answerTape, C, A', S, d, e, hC, hA, hS, hd, he, hrun⟩ := h
  refine ⟨machine, countTape, C, A', S, d, e, hC, hA, hS, hd, he, ?_⟩
  intro n A r m As b D α hout hin
  have hw : SAT.WidthAtMost (max Δ (max 3 (max k 1)))
      (dirCutCNFWithFin A (hashCNF As b D α) r) := by
    refine CNF.relabel_width _ (width_union ?_ (CNF.map_width _ ?_))
    · intro C hC
      exact (dirCutCNF_width A r hout hin C hC).trans (max_le_max le_rfl (le_max_left _ _))
    · intro C hC
      exact (hashCNF_width As b D α C hC).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨time, final, htrace, hcount, -, -, hdecode, -, htime, hspace⟩ :=
    hrun (Fintype.card (DVar A)) (dirCutCNFWithFin A (hashCNF As b D α) r) hw
  exact ⟨SAT.count (dirCutCNFWithFin A (hashCNF As b D α) r), time, final, htrace, hcount,
    hdecode, by rw [dirCutCNFWithFin, CNF.relabel_count], htime, hspace⟩

end EthFollowup.DirectedHamiltonian
