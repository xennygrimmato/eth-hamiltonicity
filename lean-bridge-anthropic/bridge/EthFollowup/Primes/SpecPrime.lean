/-
# The one-query specifications of π(x) mod 2 and π([A, B]) mod 2 (Executor P, step P2)

`scratchpad/plans/primes-plan.md`. One query (the empty prefix `[]`, `q1 = q2`), no small case;
the output is the count mod 2.

* `specPi : GR.QuerySpec` (`fin = Nat.bits (c₁ % 2)`), PolyT of its fields;
* `specPi_answer`: the answer is `Nat.bits (Q w [] % 2)`; `specPi_answer_eq`: if `Q w [] % 2 = r % 2`,
  then the answer is `encodeNat (r % 2)`;
* `specPi_length`: the answer has length `≤ 1·(|w| + 2)`.

Standard axioms only.
-/
import EthFollowup.ModP.SpecSq
import EthFollowup.Primes.PrimeDesc

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Groundwork EthFollowup.ModP

/-- **The query specification**: one query `[]`, output `count mod 2`. -/
def specPi : GR.QuerySpec where
  pre _ := false
  small _ := []
  q1 _ := []
  q2 _ := []
  fin q := Nat.bits (q.2.1 % 2)

theorem specPi_pre_polyT : PolyT specPi.pre := by
  show PolyT fun _ : List Bool => false; fun_prop

theorem specPi_small_polyT : PolyT specPi.small := by
  show PolyT fun _ : List Bool => ([] : List Bool); fun_prop

theorem specPi_q1_polyT : PolyT specPi.q1 := by
  show PolyT fun _ : List Bool => ([] : List Bool); fun_prop

theorem specPi_q2_polyT : PolyT specPi.q2 := by
  show PolyT fun _ : List Bool => ([] : List Bool); fun_prop

theorem specPi_fin_polyT : PolyT specPi.fin := by
  show PolyT fun q : List Bool × ℕ × ℕ => Nat.bits (q.2.1 % 2); fun_prop

theorem specPi_answer {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) :
    GR.answerQ pk specPi w = Nat.bits (pk.Q w [] % 2) := by
  unfold GR.answerQ
  rfl

/-- **The answer**: if the count of the query is `≡ r (mod 2)`, the answer is `encodeNat (r % 2)`. -/
theorem specPi_answer_eq {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) {r : ℕ}
    (h : pk.Q w [] % 2 = r % 2) : GR.answerQ pk specPi w = Computability.encodeNat (r % 2) := by
  rw [specPi_answer, h, bits_eq_encodeNat]

theorem specPi_length {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) :
    (GR.answerQ pk specPi w).length ≤ 1 * (w.length + 2) := by
  rw [specPi_answer]
  have : pk.Q w [] % 2 < 2 ^ 1 := by have := Nat.mod_lt (pk.Q w []) (by norm_num : 0 < 2); simpa using this
  have := bits_length_le this
  omega

end EthFollowup.Primes
