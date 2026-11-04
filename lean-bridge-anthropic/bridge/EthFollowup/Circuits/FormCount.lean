/-
# The check formula has at most 4·Nv + 1 clauses

Anthropic's `CircuitLowerBound.StForm` (InterfacesPolyT.lean) bounds the number of variables Nv of the
formula «some clause of the table is violated by the circuit», but not the number of its clauses. The
rate engine is measured in clauses, so we re-prove `StForm` for Anthropic's own formula `Form.F B`
(Circ/Form.lean: Tseitin, four clauses per gate, plus one unit clause, deduplicated) with the extra
bound ψ.length ≤ 4·Nv + 1 (`stFormCount`). The proof of the old part is the proof of `stForm_of`.
-/
import CircuitLowerBound.Closed

set_option linter.unusedSectionVars false

namespace EthFollowup.Circuits

open ENP Groundwork CircuitLowerBound CircuitLowerBound.Form

/-- Tseitin has four clauses per gate. -/
theorem length_tseitin (n : ℕ) (K : List GateD) : (tseitin n K).length = 4 * K.length := by
  unfold tseitin
  rw [List.length_flatMap]
  simp [gateCl, List.map_const', List.sum_replicate, Nat.mul_comm]

/-- Anthropic's formula has at most 4·Nv + 1 clauses, for every input. -/
theorem length_F_le (B : MCode × List Unit × ℕ → List GateD × List ℕ) (q : (MCode × List Unit × ℕ) × List GateD) :
    (F B q).2.length ≤ 4 * (F B q).1.length + 1 := by
  simp only [F, List.length_replicate]
  refine (List.dedup_sublist _).length_le.trans ?_
  rw [List.length_append, length_tseitin]
  simp only [List.length_singleton]
  omega

/-- `StForm` with the bound on the number of clauses. -/
def StFormCount : Prop := ∃ (a₀ : ℕ) (g : MCode → ℕ) (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf), PolyT F ∧
  Alg.FormOK a₀ g F ∧ ∀ q, (F q).2.length ≤ 4 * (F q).1.length + 1

/-- Proof as `stForm_of stClauseCirc`, plus `length_F_le`. -/
theorem stFormCount : StFormCount := by
  obtain ⟨a₀, g, B, hB, hspec⟩ := stClauseCirc
  refine ⟨a₀ + 1, fun e => g e + rb e + 5, F B, F_polyT B hB, fun e L P C hFit hC => ?_, length_F_le B⟩
  obtain ⟨hG, hlen, ho, hoN, hval⟩ := hspec e L P hFit
  have hs := form_spec hFit hG ho hoN hval hC
  have hn := nF_eq hFit
  have hle : nb e L ≤ rb e + L := hn ▸ min_le_right _ _
  simp only [F, cK, List.length_replicate, hn]
  refine ⟨hs.1, ?_, hs.2⟩
  rw [length_check, Nat.add_mul, Nat.one_mul]
  omega

end EthFollowup.Circuits
