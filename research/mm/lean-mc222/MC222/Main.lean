import MC222.Final
import MC222.Upper
import MC222.AllCubes

/-!
# Main theorem: the multiplicative complexity of the 2×2 matrix product over `F₂` is 7
-/

namespace MC222

/-- No XOR-AND circuit with 6 AND gates computes the 2×2 matrix product over `F₂`. -/
theorem not_hasCircuit_six : ¬ HasCircuit 6 := lower_of_cubes all_cubes

/-- No circuit with at most 6 AND gates. -/
theorem not_hasCircuit_le_six (k : ℕ) (hk : k ≤ 6) : ¬ HasCircuit k := fun h =>
  not_hasCircuit_six (h.mono hk)

/-- `MC = 7`: Strassen's 7 gates suffice, 6 do not. -/
theorem mc_eq_seven : MC = 7 := by
  unfold MC
  refine le_antisymm (Nat.sInf_le hasCircuit_seven) (le_csInf ⟨7, hasCircuit_seven⟩ ?_)
  intro k hk
  by_contra hlt
  exact not_hasCircuit_le_six k (by omega) hk

end MC222
