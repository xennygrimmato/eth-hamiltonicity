import TwinIndependent.MainResults
import TwinAlgorithm.TwinMachine

/-! The twin-prime machine discharges the independent Mathlib-only specification. -/

namespace TwinIndependent

theorem twinPrimeCount_eq (N : ℕ) : twinPrimeCount N = TwinAlgorithm.TwinFormula.twinCount N := rfl

/-- **Exact twin-prime counting** in time `⌊C · 2^(C·b/√log₂(b+2))⌋` on one deterministic,
finite-alphabet Turing machine (Mathlib's model), for every natural input. -/
theorem twinPrimeCounting_time : ExactTwinPrimeCounting := by
  obtain ⟨M, C, hfinite, hrun⟩ := TwinAlgorithm.TwinMachine.twinCount_TM_all_inputs
  exact ⟨M, C, hfinite, fun N => hrun N⟩

end TwinIndependent
