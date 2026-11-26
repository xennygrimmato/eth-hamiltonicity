import MC222.Main

/-!
Prints the statement of the main theorem and the axioms it depends on.
This file is not part of the library; run it after `lake build` with
`lake env lean CheckAxioms.lean`, or use `./check_axioms.sh`, which also checks the list.
-/

#check @MC222.mc_eq_seven
#print axioms MC222.hasCircuit_seven
#print axioms MC222.mc_eq_seven
