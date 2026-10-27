/-
# Randomized decision of Hamiltonicity via isolation and parity

Each hash `ω = (A, b, D, α)` of `IsolationLemma.lean` becomes a CNF `hashCNF ω` on the edge
variables of `G`, of width `max k 1` (`hashCNF_width`). Two facts combine:

* `decision_sound`: if `G` has no Hamiltonian cycle, the Cut&Count count with `hashCNF ω` added
  is even for **every** `ω`;
* `decision_complete`: at least the fraction `|HC(G)| / (2 · V(r) · 2^m · C(|E|, d) · 2^d)` of all
  hashes `ω` make that count odd, whenever the union-bound condition holds for `S = HC(G)`.

With `hamIso_subexponential` (one machine per `(Δ, k)` computing that parity), this gives a
one-sided-error randomized decision procedure for Hamiltonicity of graphs of maximum degree
`≤ Δ`, depending only on the comparator statement `exact_count_and_sat`. The algorithm
does not know `|HC(G)|`, so it tries every `m ≤ |E| + 1`; the condition holds for some such `m`.
The asymptotic estimate turning the fraction into `2^{−δ|E|}` (binary-entropy bounds on `V(r)`
and `C(|E|, d)`) is not formalised; see `hamiltonicity.md`, §5a.
-/
import EthFollowup.HamiltonianIsolation
import EthFollowup.IsolationLemma
import EthFollowup.HashCNF

namespace EthFollowup.Hamiltonian

open OAI.Algorithms.SubexponentialSAT
open EthFollowup EthFollowup.Isolation
open Finset

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-! ### Soundness and completeness -/

/-- Hamiltonian cycles as points of `{0,1}^{E(G)}`. -/
def hcPoints : Finset (EdgeVar G → Bool) := (hamCycles G).image (edgeIndicator G)

theorem edgeIndicator_injOn : Set.InjOn (edgeIndicator G) (hamCycles G : Set _) := by
  intro X hX Y hY h
  have hXs : X ⊆ G.edgeFinset := Finset.mem_powerset.1
    (Finset.mem_filter.1 (Finset.mem_filter.1 hX).1).1
  have hYs : Y ⊆ G.edgeFinset := Finset.mem_powerset.1
    (Finset.mem_filter.1 (Finset.mem_filter.1 hY).1).1
  ext e
  constructor
  · intro he
    have := congrFun h ⟨e, hXs he⟩
    simp only [edgeIndicator, he, decide_true] at this
    exact of_decide_eq_true this.symm
  · intro he
    have := congrFun h ⟨e, hYs he⟩
    simp only [edgeIndicator, he, decide_true] at this
    exact of_decide_eq_true this

theorem card_hcPoints : (hcPoints G).card = (hamCycles G).card :=
  Finset.card_image_of_injOn (edgeIndicator_injOn G)

theorem restricted_count_eq {k m : ℕ} (A : Sys (EdgeVar G) k m) (b : Fin m → ZMod 2)
    (D : Finset (EdgeVar G)) (α : EdgeVar G → Bool) :
    ((hamCycles G).filter fun X =>
        SAT.CNF.eval (edgeIndicator G X) (hashCNF A b D α) = true).card =
      ((hcPoints G).filter fun y => applySys A y = b ∧ ∀ e ∈ D, y e = α e).card := by
  rw [hcPoints, Finset.filter_image, Finset.card_image_of_injOn]
  · congr 1
    ext X
    simp only [Finset.mem_filter, Function.comp, hashCNF_eval]
  · exact (edgeIndicator_injOn G).mono (Finset.coe_subset.2 (Finset.filter_subset _ _))

/-- **Soundness.** Without Hamiltonian cycles, every hash gives an even count. -/
theorem decision_sound {k m : ℕ} (r : Fin n) (h0 : hamCycles G = ∅) (A : Sys (EdgeVar G) k m)
    (b : Fin m → ZMod 2) (D : Finset (EdgeVar G)) (α : EdgeVar G → Bool) :
    (SAT.count (cutCNFWith G (hashCNF A b D α) r) : ZMod 2) = 0 :=
  parity_of_none G _ r h0

/-- **Completeness.** Every isolating hash gives an odd count, and isolating hashes are a
non-negligible fraction. -/
theorem decision_complete {k m rad d : ℕ} (r : Fin n)
    (Hm : 2 * (hamCycles G).card *
        (2 ^ k * (G.edgeFinset.card ^ k + (G.edgeFinset.card - rad) ^ k)) ^ m ≤
      2 ^ m * (G.edgeFinset.card ^ k * 2 ^ k) ^ m)
    (hd : 2 * rad ≤ d) (hdN : d ≤ G.edgeFinset.card) :
    (hamCycles G).card * Fintype.card (Sys (EdgeVar G) k m) * 2 ^ (G.edgeFinset.card - d) ≤
      2 * ballVol (EdgeVar G) rad *
        (((univ : Finset (Sys (EdgeVar G) k m × (Fin m → ZMod 2))) ×ˢ
            (Finset.univ.powersetCard d ×ˢ (univ : Finset (EdgeVar G → Bool)))).filter
          fun ω => (SAT.count (cutCNFWith G (hashCNF ω.1.1 ω.1.2 ω.2.1 ω.2.2) r) : ZMod 2) = 1).card := by
  have hN : Fintype.card (EdgeVar G) = G.edgeFinset.card := Fintype.card_coe _
  have hiso := isolation_count (ι := EdgeVar G) (k := k) (m := m) (r := rad) (d := d)
    (hcPoints G) (by rw [card_hcPoints, hN]; exact Hm) hd (by rw [hN]; exact hdN)
  rw [card_hcPoints, hN] at hiso
  refine hiso.trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
  intro ω hω
  rw [Finset.mem_filter] at hω ⊢
  refine ⟨hω.1, ?_⟩
  apply parity_of_unique G _ r
  rw [restricted_count_eq]
  exact hω.2

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace in
/-- **The decision machine.** For each `Δ` and sparsity `k`, conditional on the comparator at
width `max Δ (max 3 (max k 1))`, one machine computes, for every graph `G` of maximum degree
`≤ Δ` and every hash `(A, b, D, α)`, a number with the parity of the hashed Cut&Count count, in
time `C (L+1)^d 2^{A ρ(|E|+n)}` and polynomial space. With `decision_sound` (even for all hashes
when `G` has no Hamiltonian cycle) and `decision_complete` (odd for the stated fraction of hashes
when it has one), this is a one-sided-error randomized decision procedure. -/
theorem hamDecision_subexponential (Δ k : ℕ)
    (h : ExactCountAndSatStatement (max Δ (max 3 (max k 1)))
      (le_max_of_le_right (le_max_of_le_left (by norm_num)))) :
    ∃ (machine : Computation.PrimitiveMachine)
      (countTape : Fin machine.tapeCount) (C A' S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A' ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : Fin n) (m : ℕ)
        (A : Sys (EdgeVar G) k m) (b : Fin m → ZMod 2) (D : Finset (EdgeVar G))
        (α : EdgeVar G → Bool), (∀ v, G.degree v ≤ Δ) →
        ∃ (N time : ℕ) (final : LocatedCfg machine),
          Computation.Trace (locatedStep machine) time
            (locatedInit machine (Encoding.encodeCNF (cutCNFWithFin G (hashCNF A b D α) r)))
            final ∧
          final.config.tapes countTape = Turing.Tape.mk₁ ((countWord N).map some) ∧
          BinaryArithmetic.toNat (countWord N) = N ∧
          (N : ZMod 2) = (SAT.count (cutCNFWith G (hashCNF A b D α) r) : ZMod 2) ∧
          (time : ℝ) ≤ SqrtLog.Statement.runtimeBound C A' d
            (Encoding.formulaBitLength (cutCNFWithFin G (hashCNF A b D α) r))
            (Fintype.card (Var G)) ∧
          ∀ (prefixSteps : ℕ) (intermediate : LocatedCfg machine),
            prefixSteps ≤ time →
            Computation.Trace (locatedStep machine) prefixSteps
              (locatedInit machine
                (Encoding.encodeCNF (cutCNFWithFin G (hashCNF A b D α) r))) intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength (cutCNFWithFin G (hashCNF A b D α) r) : ℝ) + 1) ^ e := by
  obtain ⟨machine, countTape, C, A', S, d, e, hC, hA, hS, hd, he, hrun⟩ :=
    hamIso_subexponential Δ (max k 1) h
  refine ⟨machine, countTape, C, A', S, d, e, hC, hA, hS, hd, he, ?_⟩
  intro n G _ r m A b D α hΔ
  obtain ⟨N, time, final, htrace, htape, hdec, hpar, htime, hspace⟩ :=
    hrun n G (hashCNF A b D α) r hΔ (hashCNF_width A b D α)
  exact ⟨N, time, final, htrace, htape, hdec, by rw [hpar, count_cutCNFWith_mod_two], htime, hspace⟩

end EthFollowup.Hamiltonian
