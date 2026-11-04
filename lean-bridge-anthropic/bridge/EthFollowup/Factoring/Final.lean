/-
# Factoring: the unconditional results

`MulPackage.mulPackage_nonempty` (F3/F4) discharges the hypothesis `∃ c₀, Nonempty (MulPackage c₀)`
of `Statement.lean` (F6b).

* `minFac_TM_rate`: one Mathlib `TM2ComputableAux` machine with finite alphabets and one `C`, outputting
  `encodeNat (minFac N)` on `encodeNat N` within `⌊C · 2^{C n / √(log₂(n+2))}⌋₊` steps (`n = |encodeNat N|`);
* `sqrtLogLog : RR.Factoring.SqrtLogLogConjecture`;
* `RR.Factoring.subexponentialRate`: RR's headline statement, verbatim.

Standard axioms only.
-/
import EthFollowup.Factoring.Statement
import EthFollowup.Factoring.MulPackage

namespace EthFollowup.Factoring

theorem minFac_TM_rate :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ N : ℕ, GraphProblems.Outputs M (Computability.encodeNat N) (Computability.encodeNat (Nat.minFac N))
        ⌊(C : ℝ) * 2 ^ ((C : ℝ) * (Computability.encodeNat N).length /
          Real.sqrt (Real.logb 2 ((Computability.encodeNat N).length + 2)))⌋₊ :=
  minFac_TM_rate_of_pkg mulPackage_nonempty

theorem sqrtLogLog : RR.Factoring.SqrtLogLogConjecture := sqrtLogLog_of_pkg mulPackage_nonempty

end EthFollowup.Factoring

namespace RR.Factoring

/-- **The result** (RR's statement, verbatim). -/
theorem subexponentialRate :
    ∃ M : FactoringMachine, ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ,
      FactorsWithin M (fun n => C * 2 ^ (n / k)) :=
  EthFollowup.Factoring.subexponentialRate_of_pkg EthFollowup.Factoring.mulPackage_nonempty

end RR.Factoring
