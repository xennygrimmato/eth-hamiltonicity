/-
# Success probability `exp(−δ|E|)` for the randomized Hamiltonicity test

Combines `decision_complete` with the analytic estimate `isolation_fraction`. For every
`δ > 0` there are a sparsity `k` and a threshold `N₀` such that, for every graph `G` with at
least `N₀` edges and at least one Hamiltonian cycle, some parameters `(m, d)` make at least an
`exp(−δ|E|)` fraction of all hashes `(A, b, D, α)` produce an odd Cut&Count count. By
`decision_sound`, no hash ever produces an odd count when `G` has no Hamiltonian cycle.
-/
import EthFollowup.HamiltonianDecision
import EthFollowup.IsolationAnalysis

namespace EthFollowup.Hamiltonian

open OAI.Algorithms.SubexponentialSAT
open EthFollowup EthFollowup.Isolation
open Finset Real

/-- **Completeness with success `exp(−δ|E|)`.** -/
theorem hamDecision_fraction {δ : ℝ} (hδ : 0 < δ) :
    ∃ k N₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r₀ : Fin n),
      (hamCycles G).Nonempty → N₀ ≤ G.edgeFinset.card →
      ∃ m d : ℕ,
        exp (-(δ * G.edgeFinset.card)) *
            (((univ : Finset (Sys (EdgeVar G) k m × (Fin m → ZMod 2))) ×ˢ
              ((univ : Finset (EdgeVar G)).powersetCard d ×ˢ (univ : Finset (EdgeVar G → Bool)))).card : ℝ) ≤
          ((((univ : Finset (Sys (EdgeVar G) k m × (Fin m → ZMod 2))) ×ˢ
              ((univ : Finset (EdgeVar G)).powersetCard d ×ˢ (univ : Finset (EdgeVar G → Bool)))).filter
            fun ω => (SAT.count (cutCNFWith G (hashCNF ω.1.1 ω.1.2 ω.2.1 ω.2.2) r₀) : ZMod 2) = 1).card
            : ℝ) := by
  obtain ⟨k, N₀, hfrac⟩ := isolation_fraction.{0} hδ
  refine ⟨k, N₀, fun n G _ r₀ hne hN => ?_⟩
  have hNc : Fintype.card (EdgeVar G) = G.edgeFinset.card := Fintype.card_coe _
  have hSne : (hcPoints G).Nonempty := by
    obtain ⟨X, hX⟩ := hne; exact ⟨_, Finset.mem_image_of_mem _ hX⟩
  obtain ⟨m, rad, d, hd, hdN, Hm, hest⟩ :=
    hfrac (EdgeVar G) (hcPoints G) hSne (by rw [hNc]; exact hN)
  refine ⟨m, d, ?_⟩
  rw [card_hcPoints, hNc] at Hm hest
  rw [hNc] at hdN
  have hcomp := decision_complete G r₀ Hm hd hdN
  rw [card_hashSpace, hNc]
  set odd := ((((univ : Finset (Sys (EdgeVar G) k m × (Fin m → ZMod 2))) ×ˢ
      ((univ : Finset (EdgeVar G)).powersetCard d ×ˢ (univ : Finset (EdgeVar G → Bool)))).filter
        fun ω => (SAT.count (cutCNFWith G (hashCNF ω.1.1 ω.1.2 ω.2.1 ω.2.2) r₀) : ZMod 2) = 1).card)
  set N := G.edgeFinset.card
  set V := ballVol (EdgeVar G) rad
  set Sy := Fintype.card (Sys (EdgeVar G) k m)
  set s := (hamCycles G).card
  have hs : 1 ≤ s := hne.card_pos
  have hcompR : (s : ℝ) * Sy * 2 ^ (N - d) ≤ 2 * V * odd := by exact_mod_cast hcomp
  have hV : (0 : ℝ) < V := by
    rcases Nat.eq_zero_or_pos V with h0 | h0
    · exfalso
      have : (s : ℝ) * Sy * 2 ^ (N - d) ≤ 0 := by rw [h0] at hcompR; simpa using hcompR
      have hE : Nonempty (EdgeVar G) := by
        obtain ⟨X, hX⟩ := hne
        have hX2 := (Finset.mem_filter.1 hX).1
        have hreg : TwoRegular X := (Finset.mem_filter.1 hX2).2
        have hsub : X ⊆ G.edgeFinset := Finset.mem_powerset.1 (Finset.mem_filter.1 hX2).1
        obtain ⟨e, he⟩ : (X.filter fun e => r₀ ∈ e).Nonempty :=
          Finset.card_pos.1 (by rw [hreg r₀]; norm_num)
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

end EthFollowup.Hamiltonian
