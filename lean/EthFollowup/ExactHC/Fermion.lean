/-
# Shared fermion definitions for the exact-#HC formalisation (blueprint M5/M6 interface)

Write-up reference: `research/exact-hc-theorem.md`, §3 ("Generators") and §4.

Generators live in `Fin (2 * n)`: `ψ̄_v` is index `2v` and `ψ_v` is index `2v + 1`. The root `r`'s
generators exist in the type but are never used. `psibar r v` and `psi r v` are `0` for `v = r`,
which matches the write-up's convention ψ̄_r = ψ_r := 0.

* `psibar r v`, `psi r v`, `omega r v = psibar r v * psi r v`.
* `qPair r i j = (ψ̄_i − ψ̄_j)(ψ_i − ψ_j)`, and `qEdge r e` is its value on an unordered edge
  `e : Sym2 (Fin n)` (it is symmetric).
* `genSet r S`: the generators of the vertices of `S \ {r}`, i.e. Γ_S. `genSet r univ` is Γ.
* `OmegaOf r l`: the ordered product of `omega r v` over a list `l` of vertices.
  `OmegaSet r S := OmegaOf r ((S.erase r).sort (· ≤ ·))` is Ω_S. The ordering of the factors does
  not matter mathematically (they are even and central); proving that is part of M5/M6.
* `edgeProd r X`: Π_{e∈X} (1 + q_e), as an ordered product along `X.toList`. The factors are even,
  so the order does not matter; again M5/M6 prove what they need.
* `topV r x = [Ω_V](x)`, the top coefficient relative to `Ω_V = OmegaSet r univ`.
* `fermionSum G r = Σ_{X ∈ twoFactors G} [Ω_V] Π_{e∈X}(1 + q_e)`.
  **M5 target:** `fermionSum G r = n * #(hamCycles G)` (Lemma 3.3 + Corollary 3.4 + Lemma 3.1).
  **M6 target:** the blob sum of Theorem 4.6 equals `fermionSum G r`.
-/
import EthFollowup.ExactHC.Grassmann
import EthFollowup.HamiltonianParity

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset

noncomputable section

variable {n : ℕ}

/-- Generator index of `ψ̄_v`. -/
def gbarIdx (v : Fin n) : Fin (2 * n) := ⟨2 * v.val, by omega⟩

/-- Generator index of `ψ_v`. -/
def gIdx (v : Fin n) : Fin (2 * n) := ⟨2 * v.val + 1, by omega⟩

/-- `ψ̄_v`, with `ψ̄_r = 0`. -/
def psibar (r v : Fin n) : Grass (Fin (2 * n)) := if v = r then 0 else Grass.gen (gbarIdx v)

/-- `ψ_v`, with `ψ_r = 0`. -/
def psi (r v : Fin n) : Grass (Fin (2 * n)) := if v = r then 0 else Grass.gen (gIdx v)

/-- `ω_v = ψ̄_v ψ_v`. -/
def omega (r v : Fin n) : Grass (Fin (2 * n)) := psibar r v * psi r v

/-- `q_{ij} = (ψ̄_i − ψ̄_j)(ψ_i − ψ_j)`. -/
def qPair (r i j : Fin n) : Grass (Fin (2 * n)) :=
  (psibar r i - psibar r j) * (psi r i - psi r j)

theorem qPair_comm (r i j : Fin n) : qPair r i j = qPair r j i := by
  unfold qPair
  rw [show psibar r j - psibar r i = -(psibar r i - psibar r j) by abel,
    show psi r j - psi r i = -(psi r i - psi r j) by abel, neg_mul_neg]

/-- `q_e` for an unordered edge `e`. -/
def qEdge (r : Fin n) (e : Sym2 (Fin n)) : Grass (Fin (2 * n)) :=
  Sym2.lift ⟨fun i j => qPair r i j, fun i j => qPair_comm r i j⟩ e

@[simp] theorem qEdge_mk (r i j : Fin n) : qEdge r s(i, j) = qPair r i j := rfl

/-- `Γ_S`: the generators of the vertices of `S \ {r}`. -/
def genSet (r : Fin n) (S : Finset (Fin n)) : Finset (Fin (2 * n)) :=
  (S.erase r).biUnion fun v => {gbarIdx v, gIdx v}

/-- Ordered product of `ω_v` over a list of vertices. -/
def OmegaOf (r : Fin n) (l : List (Fin n)) : Grass (Fin (2 * n)) := (l.map (omega r)).prod

/-- `Ω_S`, the product of the `ω_v` for `v ∈ S \ {r}` in increasing order. -/
def OmegaSet (r : Fin n) (S : Finset (Fin n)) : Grass (Fin (2 * n)) :=
  OmegaOf r ((S.erase r).sort (· ≤ ·))

/-- `Π_{e∈X} (1 + q_e)`, ordered along `X.toList`. -/
def edgeProd (r : Fin n) (X : Finset (Sym2 (Fin n))) : Grass (Fin (2 * n)) :=
  (X.toList.map fun e => 1 + qEdge r e).prod

/-- `[Ω_V](x)`. -/
def topV (r : Fin n) (x : Grass (Fin (2 * n))) : ℤ :=
  Grass.topCoeff (genSet r univ) (OmegaSet r univ) x

/-- `Σ_{X 2-factor} [Ω_V] Π_{e∈X}(1 + q_e)`. -/
def fermionSum (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : Fin n) : ℤ :=
  ∑ X ∈ Hamiltonian.twoFactors G, topV r (edgeProd r X)

end

end EthFollowup.ExactHC
