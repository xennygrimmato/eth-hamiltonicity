/-
Unconditional versions of this repo's theorems: the comparator hypothesis is discharged by
openai/math's `exact_count_and_sat` (built from source in this workspace).
-/
import EthFollowup.IndependentSet
import EthFollowup.HamiltonianAllGraphs
import EthFollowup.DirectedHamiltonianParity
import EthFollowup.HamiltonianIsolation
import EthFollowup.HamiltonianDecision
import EthFollowup.HamiltonianDecisionFraction
import EthFollowup.DirectedHamiltonianDecision

-- `def` rather than `theorem` only so the (long) statements can be inferred from the proofs.
namespace EthFollowup

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- One machine counts independent sets of every graph in subexponential time and polynomial
space. -/
def indepSet_count_subexponential_unconditional :=
  indepSet_count_subexponential (exactCountAndSat_holds 2 le_rfl)

/-- One machine computes the parity of the number of Hamiltonian cycles of every graph `G` on
`n` vertices in time `C (L+1)^d 2^{A ρ(5|E| + 3n)}` and polynomial space. -/
def hamParity_allGraphs_unconditional :=
  Hamiltonian.hamParity_allGraphs (exactCountAndSat_holds 5 (by norm_num))

/-- For each `Δ`, one machine computes the parity of the number of Hamiltonian cycles of graphs
of maximum degree `≤ Δ` in time `C (L+1)^d 2^{A ρ(|E| + n)}`. -/
def hamParity_unconditional (Δ : ℕ) :=
  Hamiltonian.hamParity_subexponential Δ
    (exactCountAndSat_holds (max Δ 3) (le_max_of_le_right (by norm_num)))

/-- Directed analogue for maximum in- and out-degree `≤ Δ`. -/
def dirHamParity_unconditional (Δ : ℕ) :=
  DirectedHamiltonian.dirHamParity_subexponential Δ
    (exactCountAndSat_holds (max Δ 3) (le_max_of_le_right (by norm_num)))

/-- Restricted parity: for every graph of maximum degree `≤ Δ` and every width-`k` CNF on its
edges, the parity of the number of Hamiltonian cycles satisfying it. -/
def hamIso_unconditional (Δ k : ℕ) :=
  Hamiltonian.hamIso_subexponential Δ k
    (exactCountAndSat_holds (max Δ (max 3 k))
      (le_max_of_le_right (le_max_of_le_left (by norm_num))))

/-- The randomized decision machine for Hamiltonicity (see `decision_sound`,
`decision_complete`). -/
def hamDecision_unconditional (Δ k : ℕ) :=
  Hamiltonian.hamDecision_subexponential Δ k
    (exactCountAndSat_holds (max Δ (max 3 (max k 1)))
      (le_max_of_le_right (le_max_of_le_left (by norm_num))))

/-- The randomized decision machine for directed Hamiltonicity. -/
def dirHamDecision_unconditional (Δ k : ℕ) :=
  DirectedHamiltonian.dirHamDecision_subexponential Δ k
    (exactCountAndSat_holds (max Δ (max 3 (max k 1)))
      (le_max_of_le_right (le_max_of_le_left (by norm_num))))

end EthFollowup

#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat
#print axioms EthFollowup.indepSet_count_subexponential_unconditional
#print axioms EthFollowup.hamParity_allGraphs_unconditional
#print axioms EthFollowup.hamParity_unconditional
#print axioms EthFollowup.dirHamParity_unconditional
#print axioms EthFollowup.hamIso_unconditional
#print axioms EthFollowup.hamDecision_unconditional
#print axioms EthFollowup.dirHamDecision_unconditional
