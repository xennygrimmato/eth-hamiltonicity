/-
# The two-query specification of (E) class numbers and its answer (B6)

`scratchpad/plans/modp-plan.md`, ADDENDUM §B (E). On the input `w` (`N := ofWord w`): `N = 0`
directly (`hForm 0 = 1`), else the two counts `Q w [0]` (query 1: `b ≥ 0`) and `Q w [1]`
(query 2: `b < 0`, negated) and their sum.

* `specE : GR.QuerySpec`; PolyT of its fields (`specE_*_polyT`);
* **`specE_answer`**: if the package's counts are `hQ1 B N` and `hQ2 B N` (`N < B`), the answer is
  `Nat.bits (hForm (-N))`; **`specE_answer_encodeNat`**: on `encodeNat N`, `encodeNat (hForm (-N))`;
* `specE_length`: the answer has length `≤ (qb + 2)·(|w| + 2)` (from `CntPackage.Q_lt`).

Standard axioms only.
-/
import EthFollowup.ModP.SpecSq
import EthFollowup.ModP.ClassForms

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork EthFollowup.Factoring

/-- **The queries of (E)**: query 1 is the word `[0]`, query 2 the word `[1]`; the answer is the sum. -/
def specE : GR.QuerySpec where
  pre w := decide (Groundwork.ofWord w = 0)
  small _ := [true]
  q1 _ := [false]
  q2 _ := [true]
  fin q := Nat.bits (q.2.1 + q.2.2)

theorem specE_pre_polyT : PolyT specE.pre := by
  show PolyT fun w : List Bool => decide (Groundwork.ofWord w = 0); fun_prop

theorem specE_small_polyT : PolyT specE.small := by
  show PolyT fun _ : List Bool => [true]; fun_prop

theorem specE_q1_polyT : PolyT specE.q1 := by
  show PolyT fun _ : List Bool => [false]; fun_prop

theorem specE_q2_polyT : PolyT specE.q2 := by
  show PolyT fun _ : List Bool => [true]; fun_prop

theorem specE_fin_polyT : PolyT specE.fin := by
  show PolyT fun q : List Bool × ℕ × ℕ => Nat.bits (q.2.1 + q.2.2); fun_prop

theorem hForm_zero : hForm (-((0 : ℕ) : ℤ)) = 1 := by decide +kernel

/-- **(E) on any word**: with the counts `hQ1 B N`, `hQ2 B N` (`N = ofWord w < B`), the answer is
`hForm (-N)`. -/
theorem specE_answer {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) {B : ℕ}
    (hB : Groundwork.ofWord w < B)
    (h1 : 0 < Groundwork.ofWord w → pk.Q w [false] = hQ1 B (Groundwork.ofWord w))
    (h2 : 0 < Groundwork.ofWord w → pk.Q w [true] = hQ2 B (Groundwork.ofWord w)) :
    GR.answerQ pk specE w = Nat.bits (hForm (-(Groundwork.ofWord w : ℤ))) := by
  unfold GR.answerQ
  by_cases h0 : Groundwork.ofWord w = 0
  · have : specE.pre w = true := by simp only [specE, decide_eq_true_eq]; exact h0
    rw [if_pos this, h0, hForm_zero]; rfl
  · have : specE.pre w = false := by simp only [specE, decide_eq_false_iff_not]; exact h0
    rw [if_neg (by simp [this])]
    show Nat.bits (pk.Q w [false] + pk.Q w [true]) = _
    rw [h1 (by omega), h2 (by omega), hForm_split _ (by omega) hB]

/-- **(E)**: on `encodeNat N` the answer is `encodeNat (hForm (-N))`. -/
theorem specE_answer_encodeNat {c₀ : ℕ} (pk : CntPackage c₀) (N : ℕ) {B : ℕ} (hB : N < B)
    (h1 : 0 < N → pk.Q (Computability.encodeNat N) [false] = hQ1 B N)
    (h2 : 0 < N → pk.Q (Computability.encodeNat N) [true] = hQ2 B N) :
    GR.answerQ pk specE (Computability.encodeNat N) = Computability.encodeNat (hForm (-(N : ℤ))) := by
  have h := specE_answer pk (Computability.encodeNat N) (B := B) (by rwa [gofWord_encodeNat])
    (by rw [gofWord_encodeNat]; exact h1) (by rw [gofWord_encodeNat]; exact h2)
  rw [h, gofWord_encodeNat, bits_eq_encodeNat]

/-- The answer length (for `GR.queryM_TM`), from `Q_lt` on the two queries. -/
theorem specE_length {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool)
    (hOk : specE.pre w = false → pk.Ok w) (hR : specE.pre w = false → 1 ≤ pk.R w) :
    (GR.answerQ pk specE w).length ≤ (pk.qb + 2) * (w.length + 2) := by
  unfold GR.answerQ
  split_ifs with h
  · show [true].length ≤ _; simp; nlinarith
  · have hf : specE.pre w = false := by simpa using h
    have e1 := pk.Q_lt w [false] (hOk hf) (by simpa using hR hf)
    have e2 := pk.Q_lt w [true] (hOk hf) (by simpa using hR hf)
    show (Nat.bits (pk.Q w [false] + pk.Q w [true])).length ≤ _
    have hs : pk.Q w [false] + pk.Q w [true] < 2 ^ (pk.qb * (w.length + 2) + 1) := by
      rw [pow_succ]; omega
    refine (bits_length_le hs).trans ?_
    nlinarith

end EthFollowup.ModP
