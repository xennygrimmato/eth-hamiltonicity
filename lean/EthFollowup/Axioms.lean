import EthFollowup.ExactHC.Main
import EthFollowup.IndependentSet
import EthFollowup.HamiltonianParity
import EthFollowup.DirectedHamiltonianParity
import EthFollowup.HamiltonianAllGraphs
import EthFollowup.HamiltonianIsolation
import EthFollowup.HamiltonianDecision
import EthFollowup.HamiltonianDecisionFraction
import EthFollowup.DirectedHamiltonianDecision
import EthFollowup.AnthropicHamiltonian
import EthFollowup.ExactHC

/-! Axiom audit for the theorems proved in this project. Expected: only `propext`,
`Classical.choice`, `Quot.sound` (no `sorryAx`). -/

#print axioms EthFollowup.count_indepCNF
#print axioms EthFollowup.count_coverCNF
#print axioms EthFollowup.indepSet_count_subexponential
#print axioms EthFollowup.vertexCover_count_subexponential
#print axioms EthFollowup.constraintCNF_eval
#print axioms EthFollowup.CNF.relabel_count
#print axioms EthFollowup.Hamiltonian.count_cutCNF
#print axioms EthFollowup.Hamiltonian.count_cutCNF_mod_two
#print axioms EthFollowup.Hamiltonian.cutCNF_width
#print axioms EthFollowup.Hamiltonian.hamParity_subexponential
#print axioms EthFollowup.DirectedHamiltonian.count_dirCutCNF_mod_two
#print axioms EthFollowup.DirectedHamiltonian.dirHamParity_subexponential
#print axioms EthFollowup.Hamiltonian.count_bigCNF
#print axioms EthFollowup.Hamiltonian.bigCNF_width
#print axioms EthFollowup.Hamiltonian.card_bvar
#print axioms EthFollowup.Hamiltonian.hamParity_allGraphs
#print axioms EthFollowup.Hamiltonian.count_cutCNFWith_mod_two
#print axioms EthFollowup.Hamiltonian.hamIso_subexponential
#print axioms EthFollowup.Isolation.isolation_count
#print axioms EthFollowup.Hamiltonian.decision_sound
#print axioms EthFollowup.Hamiltonian.decision_complete
#print axioms EthFollowup.Hamiltonian.hamDecision_subexponential
#print axioms EthFollowup.Isolation.sum_choose_le_exp
#print axioms EthFollowup.Isolation.isolation_fraction
#print axioms EthFollowup.Hamiltonian.hamDecision_fraction
#print axioms EthFollowup.DirectedHamiltonian.dir_decision_sound
#print axioms EthFollowup.DirectedHamiltonian.dirHamDecision_fraction
#print axioms EthFollowup.DirectedHamiltonian.dirHamDecision_subexponential
#print axioms EthFollowup.Anthropic.numSat_cnfToList
#print axioms EthFollowup.Anthropic.numSat_pad
#print axioms EthFollowup.Anthropic.pad_nodup
#print axioms EthFollowup.Anthropic.pad_allOccur
#print axioms EthFollowup.Anthropic.timeMin_le_expM
#print axioms EthFollowup.Anthropic.card_bigCNF_le
#print axioms EthFollowup.Anthropic.length_hamCNF_le
#print axioms EthFollowup.Anthropic.numSat_hamCNF
#print axioms EthFollowup.Anthropic.hamParity_allGraphs_anthropic
#print axioms EthFollowup.Hamiltonian.card_spanningTrees_of_twoFactor
#print axioms EthFollowup.Hamiltonian.card_spanningTrees_of_connected
#print axioms EthFollowup.Hamiltonian.n_mul_hamCycles_eq_sum

-- Exact #HC, mathematical layer
#print axioms EthFollowup.ExactHC.blob_factorisation
#print axioms EthFollowup.ExactHC.exists_blob_factorisation
#print axioms EthFollowup.ExactHC.fermionSum_eq
