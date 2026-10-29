import EthFollowup.ExactHC.Package
import EthFollowup.ExactHC.UPackage
import EthFollowup.ExactHC.TSP
import EthFollowup.ExactHC.DPackage
import EthFollowup.ExactHC.Corollaries
import EthFollowup.ExactHC.Paths
import EthFollowup.ExactHC.DirectedTheorems
import EthFollowup.ExactHC.DirectedNetwork
import EthFollowup.AnthropicUnconditional

/-!
# Axiom audit of every Turing-machine theorem built on Anthropic's development

`leanchecker --fresh EthFollowup.ExactHC.AuditAll` replays the whole import closure of this file, i.e.
of every theorem below. Each line must print exactly `[propext, Classical.choice, Quot.sound]`.
-/

open EthFollowup.ExactHC

-- Exact #HC
#print axioms theorem1
#print axioms theorem2
#print axioms theorem3
#print axioms theorem3_maxdeg
-- Decision, search, Hamiltonian paths
#print axioms decision_TM
#print axioms search_TM
#print axioms decision_TM_rate
#print axioms search_TM_rate
#print axioms hamPaths_count_TM
#print axioms hamPaths_decision_TM
#print axioms hamPaths_search_TM
#print axioms hamPaths_count_TM_rate
#print axioms hamPaths_decision_TM_rate
#print axioms hamPaths_search_TM_rate
-- TSP, directed HC, ATSP
#print axioms theoremTSP
#print axioms theoremTSP_decode
#print axioms theoremDHC
#print axioms theoremDHC_rate
#print axioms theoremATSP
#print axioms theoremATSP_decode
#print axioms DCrossing.dNetW_value
-- Parity (earlier result)
#print axioms EthFollowup.Anthropic.hamParity_allGraphs_unconditional
