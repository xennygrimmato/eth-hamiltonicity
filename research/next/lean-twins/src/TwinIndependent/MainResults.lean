import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Prime.Defs

/-!
# Independent statement of exact twin-prime counting

This file imports Mathlib alone. It contains definitions, not proofs.

`twinPrimeCount N` is the number of primes `p ≤ N` such that `p + 2` is also prime
(the partner `p + 2` may exceed `N`; so `(3,5)` is counted for `N = 3`).
Inputs and outputs use Mathlib's `Nat.bits` (least significant bit first; zero is
the empty list).

The machine model, the output relation and the time bound are copied verbatim from
J. Ni's `PrimeIndependent.MainResults` (release v0.1-verified): Mathlib's
deterministic multi-stack Turing machine with finite stack alphabets, Mathlib's timed
halting relation `TM2OutputsInTime`, and the complete running time
`floor(C * 2^(C*b/sqrt(log_2(b+2))))` with `b` the binary length of the input.
One machine and one constant are chosen before `N`; every natural input is covered.
-/

namespace TwinIndependent

/-- The number of primes `p ≤ N` with `p + 2` prime. -/
def twinPrimeCount (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun p => Nat.Prime p ∧ Nat.Prime (p + 2)).card

/-- The common form of the complete machine time bound (as in Ni's statements). -/
noncomputable def timeBound (C N : ℕ) : ℕ :=
  ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * (Nat.bits N).length /
    Real.sqrt (Real.logb 2 ((Nat.bits N).length + 2)))⌋₊

/-- Started with x, halt within t steps with exactly y on the output stack. -/
def Outputs (M : Turing.TM2ComputableAux Bool Bool)
    (x y : List Bool) (t : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
    (some (y.map M.outputAlphabet.invFun)) t)

/-- One fixed deterministic finite-alphabet machine computes the twin-prime count. -/
def ExactTwinPrimeCounting : Prop :=
  ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ N : ℕ, Outputs M (Nat.bits N) (Nat.bits (twinPrimeCount N)) (timeBound C N)

end TwinIndependent
