/-
Unconditional form of `hamParity_allGraphs_anthropic`: the hypothesis `MainResults.MainTheorem`
is discharged by Anthropic's own proof `MainResults.mainTheorem` (anthropics/formal-math, eth/).
-/
import EthFollowup.AnthropicHamiltonian
import Solution

namespace EthFollowup.Anthropic

/-- Parity of the number of Hamiltonian cycles of every graph, by one machine with an absolute
constant, within `2^{C·5m/√lg m}` steps, `m ≤ 85|E|+11n+2` — with no hypothesis. -/
def hamParity_allGraphs_unconditional := hamParity_allGraphs_anthropic MainResults.mainTheorem

#check @hamParity_allGraphs_unconditional
#print axioms hamParity_allGraphs_unconditional

end EthFollowup.Anthropic
