/- Sanity checks, not part of the default build. Run with
    `lake env lean EthFollowup/Examples.lean`
  Expected output: (3, 3, 3), (5, 3, 4), (1, 1, 1), (6, 6, 6), (2, 2, 2), (12, 6, 9) =
  (#cutCNF, #hamCycles, #twoFactors) for K4, the triangular prism, C5, K33, then the directed
  analogues for the complete digraphs on 3 and 4 vertices. -/
import EthFollowup.HamiltonianParity
import EthFollowup.DirectedHamiltonianParity
open EthFollowup.Hamiltonian OAI.Algorithms.SubexponentialSAT

def K4 : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun a b => a ≠ b
instance : DecidableRel K4.Adj := fun a b => by unfold K4; infer_instance
def K33 : SimpleGraph (Fin 6) := SimpleGraph.fromRel fun a b => a.val < 3 ∧ 3 ≤ b.val
instance : DecidableRel K33.Adj := fun a b => by unfold K33; infer_instance
/-- triangular prism: triangles {0,1,2},{3,4,5} plus matching i -- i+3 -/
def prism : SimpleGraph (Fin 6) := SimpleGraph.fromRel fun a b =>
  (a.val < 3 ∧ b.val < 3) ∨ (3 ≤ a.val ∧ 3 ≤ b.val) ∨ (a.val + 3 = b.val)
instance : DecidableRel prism.Adj := fun a b => by unfold prism; infer_instance
/-- 4-cycle plus a chord-free pendant? use C5 (one HC) -/
def C5 : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun a b => b.val = (a.val + 1) % 5
instance : DecidableRel C5.Adj := fun a b => by unfold C5; infer_instance

#eval (SAT.count (cutCNF K4 0), (hamCycles K4).card, (twoFactors K4).card)
#eval (SAT.count (cutCNF prism 0), (hamCycles prism).card, (twoFactors prism).card)
#eval (SAT.count (cutCNF C5 0), (hamCycles C5).card, (twoFactors C5).card)
#eval (SAT.count (cutCNF K33 0), (hamCycles K33).card, (twoFactors K33).card)

open EthFollowup.DirectedHamiltonian in
/-- complete digraph without loops -/
def Kdir (m : ℕ) : Finset (Fin m × Fin m) := Finset.univ.filter fun a => a.1 ≠ a.2

open EthFollowup.DirectedHamiltonian in
-- expected (2, 2, 2) and (12, 6, 9): (#dirCutCNF, #dirHamCycles, #cycleCovers)
#eval (SAT.count (dirCutCNF (Kdir 3) 0), (dirHamCycles (Kdir 3)).card, (cycleCovers (Kdir 3)).card)
open EthFollowup.DirectedHamiltonian in
#eval (SAT.count (dirCutCNF (Kdir 4) 0), (dirHamCycles (Kdir 4)).card, (cycleCovers (Kdir 4)).card)
