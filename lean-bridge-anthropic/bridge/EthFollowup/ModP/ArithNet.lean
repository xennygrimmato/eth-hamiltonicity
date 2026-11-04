/-
# ArithNet (umbrella, module L2)

`import EthFollowup.ModP.ArithNet` gets the whole network layer: `ArithParams` (wires, vertices,
checks, run), `ArithNetDefs` (the label system `arithSys`), `ArithNetParsimony` (`arithNet_value`),
`ArithNetCount` (`arithSys_U_le`, `arithSys_is`).
-/
import EthFollowup.ModP.ArithNetParsimony
import EthFollowup.ModP.ArithNetCount
