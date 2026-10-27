/-
# Exact #HC: the mathematical layer, assembled

This combines M6 (`Blobs.lean`, blob factorisation down to `fermionSum`) with M5
(`MatrixTree.lean`, `fermionSum G r = n·#HC(G)`). Write-up: `research/exact-hc-theorem.md`,
Theorem 4.6.

For every graph `G` on `Fin n`, every root `r`, every partition `β : Fin n → Fin g` into blobs, and
every crossing order `X`:

  `Σ_{ℓ ∈ L^m} Π_a σ_a(ℓ) · χ_a(ℓ, P(ℓ)) · I_a(ℓ) = n · #HC(G)`.

Every factor depends only on the labels at blob `a` (and on the copy bits it holds); see the
locality lemmas in `Blobs.lean`. This is the identity behind the network of §5. The same identity
with the explicit sign `ε(ℓ)` is `blob_factorisation_eps`.
-/
import EthFollowup.ExactHC.Blobs
import EthFollowup.ExactHC.MatrixTree

namespace EthFollowup.ExactHC

open Finset

variable {n g m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}

/-- **Blob factorisation of `n·#HC`** (Theorem 4.6, both equalities, combined with Lemma 3.3 and
Corollary 3.4). -/
theorem blob_factorisation (X : Crossing G β m) (r : Fin n) :
    ∑ ℓ : Fin m → Label, ∏ a, X.chords.sigma (labelPar ℓ) a *
        X.chords.chi (labelPar ℓ) a (fun p => X.chords.P (labelPar ℓ) p.1 p.2) * X.I r ℓ a =
      n * (Hamiltonian.hamCycles G).card := by
  rw [X.sum_sigma_chi_I r, fermionSum_eq]

/-- The same, with the global sign `ε(ℓ)`. -/
theorem blob_factorisation_eps (X : Crossing G β m) (r : Fin n) :
    ∑ ℓ : Fin m → Label, X.eps ℓ * ∏ a, X.I r ℓ a = n * (Hamiltonian.hamCycles G).card := by
  rw [X.sum_eps_prod_I r, fermionSum_eq]

/-- For every graph, root and partition there is a crossing order, so the factorisation always
applies. -/
theorem exists_blob_factorisation (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (β : Fin n → Fin g) (r : Fin n) :
    ∃ (m : ℕ) (X : Crossing G β m),
      ∑ ℓ : Fin m → Label, ∏ a, X.chords.sigma (labelPar ℓ) a *
          X.chords.chi (labelPar ℓ) a (fun p => X.chords.P (labelPar ℓ) p.1 p.2) * X.I r ℓ a =
        n * (Hamiltonian.hamCycles G).card :=
  ⟨_, Crossing.canonical G β, blob_factorisation _ r⟩

end EthFollowup.ExactHC
