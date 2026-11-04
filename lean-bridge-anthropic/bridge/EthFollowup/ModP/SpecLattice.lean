/-
# The one-query specifications of (F) divisor sums, Σσ and the Gauss circle, and their answers (B6)

`scratchpad/plans/modp-plan.md`, ADDENDUM §B (F). On the input `w` (`x := ofWord w`): `x = 0`
directly, else one count `Q w []` and the output.

* `specDiv`, `specSig` (output the count), `specCirc` (output `4·count + 1`) : `GR.QuerySpec`;
  PolyT of their fields;
* **`specDiv_answer`**: with the count `divQ B x` (`x < B`) the answer is `Nat.bits (divSum x)`;
  **`specCirc_answer`**: with `circQ B x`, `Nat.bits (circ x)`; **`specSig_answer`**: with `sigQ B x`,
  `Nat.bits (sigSum x)`; the `encodeNat` forms `spec*_answer_encodeNat`;
* `specDiv_length`, `specSig_length`, `specCirc_length` (from `CntPackage.Q_lt`).

Standard axioms only.
-/
import EthFollowup.ModP.SpecSq
import EthFollowup.ModP.Lattice

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork EthFollowup.Factoring

/-- **The query of the divisor sum**: the count of the word `[]`. -/
def specDiv : GR.QuerySpec where
  pre w := decide (Groundwork.ofWord w = 0)
  small _ := []
  q1 _ := []
  q2 _ := []
  fin q := Nat.bits q.2.1

/-- **The query of Σσ**: the count of the word `[]`. -/
def specSig : GR.QuerySpec where
  pre w := decide (Groundwork.ofWord w = 0)
  small _ := []
  q1 _ := []
  q2 _ := []
  fin q := Nat.bits q.2.1

/-- **The query of the circle**: `4·count + 1`. -/
def specCirc : GR.QuerySpec where
  pre w := decide (Groundwork.ofWord w = 0)
  small _ := [true]
  q1 _ := []
  q2 _ := []
  fin q := Nat.bits (4 * q.2.1 + 1)

theorem pre0_polyT : PolyT fun w : List Bool => decide (Groundwork.ofWord w = 0) := by fun_prop

theorem nil_polyT : PolyT fun _ : List Bool => ([] : List Bool) := by fun_prop

theorem specDiv_pre_polyT : PolyT specDiv.pre := pre0_polyT
theorem specDiv_small_polyT : PolyT specDiv.small := nil_polyT
theorem specDiv_q1_polyT : PolyT specDiv.q1 := nil_polyT
theorem specDiv_q2_polyT : PolyT specDiv.q2 := nil_polyT
theorem specDiv_fin_polyT : PolyT specDiv.fin := by
  show PolyT fun q : List Bool × ℕ × ℕ => Nat.bits q.2.1; fun_prop

theorem specSig_pre_polyT : PolyT specSig.pre := pre0_polyT
theorem specSig_small_polyT : PolyT specSig.small := nil_polyT
theorem specSig_q1_polyT : PolyT specSig.q1 := nil_polyT
theorem specSig_q2_polyT : PolyT specSig.q2 := nil_polyT
theorem specSig_fin_polyT : PolyT specSig.fin := by
  show PolyT fun q : List Bool × ℕ × ℕ => Nat.bits q.2.1; fun_prop

theorem specCirc_pre_polyT : PolyT specCirc.pre := pre0_polyT
theorem specCirc_small_polyT : PolyT specCirc.small := by
  show PolyT fun _ : List Bool => [true]; fun_prop
theorem specCirc_q1_polyT : PolyT specCirc.q1 := nil_polyT
theorem specCirc_q2_polyT : PolyT specCirc.q2 := nil_polyT
theorem specCirc_fin_polyT : PolyT specCirc.fin := by
  show PolyT fun q : List Bool × ℕ × ℕ => Nat.bits (4 * q.2.1 + 1); fun_prop

theorem divSum_zero : divSum 0 = 0 := rfl
theorem sigSum_zero : sigSum 0 = 0 := rfl
theorem circ_zero : circ 0 = 1 := by decide +kernel

/-- **Divisor sum on any word**: with the count `divQ B x` (`x = ofWord w < B`), the answer is
`Σ_{m ≤ x} τ(m)`. -/
theorem specDiv_answer {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) {B : ℕ}
    (hB : Groundwork.ofWord w < B)
    (hQ : 0 < Groundwork.ofWord w → pk.Q w [] = divQ B (Groundwork.ofWord w)) :
    GR.answerQ pk specDiv w = Nat.bits (divSum (Groundwork.ofWord w)) := by
  unfold GR.answerQ
  by_cases h0 : Groundwork.ofWord w = 0
  · have : specDiv.pre w = true := by simp only [specDiv, decide_eq_true_eq]; exact h0
    rw [if_pos this, h0, divSum_zero]; rfl
  · have : specDiv.pre w = false := by simp only [specDiv, decide_eq_false_iff_not]; exact h0
    rw [if_neg (by simp [this])]
    show Nat.bits (pk.Q w []) = _
    rw [hQ (by omega), divQ_eq hB]

/-- **Σσ on any word**: with the count `sigQ B x`, the answer is `Σ_{m ≤ x} σ(m)`. -/
theorem specSig_answer {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) {B : ℕ}
    (hB : Groundwork.ofWord w < B)
    (hQ : 0 < Groundwork.ofWord w → pk.Q w [] = sigQ B (Groundwork.ofWord w)) :
    GR.answerQ pk specSig w = Nat.bits (sigSum (Groundwork.ofWord w)) := by
  unfold GR.answerQ
  by_cases h0 : Groundwork.ofWord w = 0
  · have : specSig.pre w = true := by simp only [specSig, decide_eq_true_eq]; exact h0
    rw [if_pos this, h0, sigSum_zero]; rfl
  · have : specSig.pre w = false := by simp only [specSig, decide_eq_false_iff_not]; exact h0
    rw [if_neg (by simp [this])]
    show Nat.bits (pk.Q w []) = _
    rw [hQ (by omega), sigQ_eq hB]

/-- **Gauss circle on any word**: with the count `circQ B x`, the answer is `circ x`. -/
theorem specCirc_answer {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool) {B : ℕ}
    (hB : Groundwork.ofWord w < B)
    (hQ : 0 < Groundwork.ofWord w → pk.Q w [] = circQ B (Groundwork.ofWord w)) :
    GR.answerQ pk specCirc w = Nat.bits (circ (Groundwork.ofWord w)) := by
  unfold GR.answerQ
  by_cases h0 : Groundwork.ofWord w = 0
  · have : specCirc.pre w = true := by simp only [specCirc, decide_eq_true_eq]; exact h0
    rw [if_pos this, h0, circ_zero]; rfl
  · have : specCirc.pre w = false := by simp only [specCirc, decide_eq_false_iff_not]; exact h0
    rw [if_neg (by simp [this])]
    show Nat.bits (4 * pk.Q w [] + 1) = _
    rw [hQ (by omega), circ_eq hB]

theorem specDiv_answer_encodeNat {c₀ : ℕ} (pk : CntPackage c₀) (x : ℕ) {B : ℕ} (hB : x < B)
    (hQ : 0 < x → pk.Q (Computability.encodeNat x) [] = divQ B x) :
    GR.answerQ pk specDiv (Computability.encodeNat x) =
      Computability.encodeNat (∑ m ∈ Finset.Icc 1 x, (Nat.divisors m).card) := by
  have h := specDiv_answer pk (Computability.encodeNat x) (B := B) (by rwa [gofWord_encodeNat])
    (by rw [gofWord_encodeNat]; exact hQ)
  rw [h, gofWord_encodeNat, bits_eq_encodeNat]; rfl

theorem specSig_answer_encodeNat {c₀ : ℕ} (pk : CntPackage c₀) (x : ℕ) {B : ℕ} (hB : x < B)
    (hQ : 0 < x → pk.Q (Computability.encodeNat x) [] = sigQ B x) :
    GR.answerQ pk specSig (Computability.encodeNat x) =
      Computability.encodeNat (∑ m ∈ Finset.Icc 1 x, ∑ d ∈ Nat.divisors m, d) := by
  have h := specSig_answer pk (Computability.encodeNat x) (B := B) (by rwa [gofWord_encodeNat])
    (by rw [gofWord_encodeNat]; exact hQ)
  rw [h, gofWord_encodeNat, bits_eq_encodeNat]; rfl

theorem specCirc_answer_encodeNat {c₀ : ℕ} (pk : CntPackage c₀) (x : ℕ) {B : ℕ} (hB : x < B)
    (hQ : 0 < x → pk.Q (Computability.encodeNat x) [] = circQ B x) :
    GR.answerQ pk specCirc (Computability.encodeNat x) = Computability.encodeNat
      (((Finset.Icc (-(x : ℤ)) x ×ˢ Finset.Icc (-(x : ℤ)) x).filter fun q : ℤ × ℤ =>
        q.1 ^ 2 + q.2 ^ 2 ≤ x).card) := by
  have h := specCirc_answer pk (Computability.encodeNat x) (B := B) (by rwa [gofWord_encodeNat])
    (by rw [gofWord_encodeNat]; exact hQ)
  rw [h, gofWord_encodeNat, bits_eq_encodeNat]; rfl

/-! ## Answer lengths (for `GR.queryM_TM`) -/

theorem specDiv_length {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool)
    (hOk : specDiv.pre w = false → pk.Ok w) :
    (GR.answerQ pk specDiv w).length ≤ (pk.qb + 2) * (w.length + 2) := by
  unfold GR.answerQ
  split_ifs with h
  · show ([] : List Bool).length ≤ _; simp
  · have hf : specDiv.pre w = false := by simpa using h
    have e := pk.Q_lt w [] (hOk hf) (by simp)
    show (Nat.bits (pk.Q w [])).length ≤ _
    exact (bits_length_le e).trans (by nlinarith)

theorem specSig_length {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool)
    (hOk : specSig.pre w = false → pk.Ok w) :
    (GR.answerQ pk specSig w).length ≤ (pk.qb + 2) * (w.length + 2) := by
  unfold GR.answerQ
  split_ifs with h
  · show ([] : List Bool).length ≤ _; simp
  · have hf : specSig.pre w = false := by simpa using h
    have e := pk.Q_lt w [] (hOk hf) (by simp)
    show (Nat.bits (pk.Q w [])).length ≤ _
    exact (bits_length_le e).trans (by nlinarith)

theorem specCirc_length {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool)
    (hOk : specCirc.pre w = false → pk.Ok w) :
    (GR.answerQ pk specCirc w).length ≤ (pk.qb + 3) * (w.length + 2) := by
  unfold GR.answerQ
  split_ifs with h
  · show [true].length ≤ _; simp; nlinarith
  · have hf : specCirc.pre w = false := by simpa using h
    have e := pk.Q_lt w [] (hOk hf) (by simp)
    show (Nat.bits (4 * pk.Q w [] + 1)).length ≤ _
    have hs : 4 * pk.Q w [] + 1 < 2 ^ (pk.qb * (w.length + 2) + 3) := by
      rw [pow_add]; norm_num; omega
    exact (bits_length_le hs).trans (by nlinarith)

end EthFollowup.ModP
