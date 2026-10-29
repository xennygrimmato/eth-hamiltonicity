import EthFollowup.ExactHC.DirectedWeighted
import EthFollowup.ExactHC.VertexSplit
import EthFollowup.ExactHC.HamPath
import EthFollowup.ExactHC.SelfReduction
import EthFollowup.Barriers.ColouringBarrier
import EthFollowup.Barriers.ColouringBarrierGraph
import EthFollowup.Barriers.RankBounds
import EthFollowup.Barriers.RowCut
import EthFollowup.Barriers.TriangularRank
import EthFollowup.Barriers.SpreadLemma
import EthFollowup.Barriers.Derand
import EthFollowup.Barriers.AlgebraRank
import EthFollowup.Barriers.PermModP

/-!
# Axiom audit for the modules added on 29 Oct 2026

Every line below must print exactly `[propext, Classical.choice, Quot.sound]`. The Turing-machine
theorems built on Anthropic's development (`theorem3`, `theoremDHC`, `theoremATSP`, `decision_TM`,
…) live in `lean-bridge-anthropic/` and are audited there (see its README).
-/

-- Directed HC / ATSP, mathematical layer
#print axioms EthFollowup.ExactHC.card_dirHamCycles_eq_sum
#print axioms EthFollowup.ExactHC.dblob_factorisation_w
#print axioms EthFollowup.ExactHC.atsp_blob_factorisation
#print axioms EthFollowup.ExactHC.VSplit.card_hamCycles_split

-- Self-reduction and Hamiltonian paths
#print axioms EthFollowup.ExactHC.srSeq_correct
#print axioms EthFollowup.ExactHC.card_hamPaths_eq

-- Barrier lemmas
#print axioms EthFollowup.Barriers.Colouring.colouring_barrier
#print axioms EthFollowup.Barriers.ColouringGraph.colouring_barrier_graph
#print axioms EthFollowup.Barriers.Rank.modelR_bound_nlogn
#print axioms EthFollowup.Barriers.RowCut.rowCut_rank
#print axioms EthFollowup.Barriers.Triangular.triangular_rank_bound_hamming
#print axioms EthFollowup.Barriers.Spread.spread_lemma
#print axioms EthFollowup.Barriers.Derand.tp_le_log
#print axioms EthFollowup.Barriers.AlgebraRank.algebra_rank_half
#print axioms EthFollowup.Barriers.PermModP.permanent_eq_zero_of_low_rank
