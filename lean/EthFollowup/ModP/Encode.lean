/-
# Input encoding of the pair `(m, a)` for the square-root problem (module M4, pure Mathlib)

* `padR n l := l ++ replicate (n - |l|) false` (right padding: keeps the little-endian value);
  `encodePair m a`: both `encodeNat m` and `encodeNat a` padded to the common length
  `pairLen m a := max |encodeNat m| |encodeNat a|`, concatenated.
* `leVal`: the little-endian value of a word (same equations as Anthropic's `Groundwork.ofWord`:
  `leVal [] = 0`, `leVal (b :: w) = b.toNat + 2 * leVal w`); `leVal_encodeNat`, `leVal_padR`,
  `leVal_lt`, `leVal_append`.
* `length_padR`, `encodePair_length` (`= 2 * pairLen m a`), `encodePair_take`/`encodePair_drop`
  (the halves are the padded encodings), `leVal_take_half`/`leVal_drop_half` (the reader for (A)
  splitting the word in halves recovers `m` and `a`), `lt_two_pow_half` (`m, a < 2^(|w|/2)`).

Standard axioms only.
-/
import Mathlib.Computability.Encoding
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Computability

/-- Right padding with `false` to length `n`. -/
def padR (n : ℕ) (l : List Bool) : List Bool := l ++ List.replicate (n - l.length) false

/-- The input word of the pair `(m, a)`. -/
def encodePair (m a : ℕ) : List Bool :=
  padR (max (encodeNat m).length (encodeNat a).length) (encodeNat m) ++
    padR (max (encodeNat m).length (encodeNat a).length) (encodeNat a)

/-- The common half length. -/
def pairLen (m a : ℕ) : ℕ := max (encodeNat m).length (encodeNat a).length

/-- Little-endian value of a word (lowest bit first). -/
def leVal : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * leVal w

@[simp] theorem leVal_nil : leVal [] = 0 := rfl

theorem leVal_cons (b : Bool) (w : List Bool) : leVal (b :: w) = b.toNat + 2 * leVal w := rfl

theorem leVal_lt (w : List Bool) : leVal w < 2 ^ w.length := by
  induction w with
  | nil => simp
  | cons b w ih =>
    have : b.toNat ≤ 1 := Bool.toNat_le b
    simp only [leVal_cons, List.length_cons, pow_succ]
    omega

theorem leVal_append (u v : List Bool) : leVal (u ++ v) = leVal u + 2 ^ u.length * leVal v := by
  induction u with
  | nil => simp
  | cons b u ih => simp only [List.cons_append, leVal_cons, ih, List.length_cons, pow_succ]; ring

theorem leVal_replicate_false (k : ℕ) : leVal (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, leVal_cons, ih]; rfl

theorem leVal_padR (n : ℕ) (l : List Bool) : leVal (padR n l) = leVal l := by
  rw [padR, leVal_append, leVal_replicate_false, mul_zero, add_zero]

theorem length_padR (n : ℕ) (l : List Bool) : (padR n l).length = max n l.length := by
  simp only [padR, List.length_append, List.length_replicate]; omega

theorem length_padR_of_le {n : ℕ} {l : List Bool} (h : l.length ≤ n) : (padR n l).length = n := by
  rw [length_padR]; omega

theorem leVal_encodePosNum (p : PosNum) : leVal (encodePosNum p) = (p : ℕ) := by
  induction p with
  | one => rfl
  | bit1 p ih =>
    simp only [encodePosNum, leVal_cons, ih, PosNum.cast_bit1]; simp; ring
  | bit0 p ih =>
    simp only [encodePosNum, leVal_cons, ih, PosNum.cast_bit0]; simp; ring

theorem leVal_encodeNat (N : ℕ) : leVal (encodeNat N) = N := by
  have hN := Num.to_of_nat N
  unfold encodeNat
  cases h : (N : Num) with
  | zero => rw [h] at hN; simp [encodeNum, ← hN]
  | pos p => rw [h] at hN; simp only [encodeNum]; rw [leVal_encodePosNum, ← hN]; rfl

theorem pairLen_le_left (m a : ℕ) : (encodeNat m).length ≤ pairLen m a := le_max_left _ _

theorem pairLen_le_right (m a : ℕ) : (encodeNat a).length ≤ pairLen m a := le_max_right _ _

theorem encodePair_eq (m a : ℕ) :
    encodePair m a = padR (pairLen m a) (encodeNat m) ++ padR (pairLen m a) (encodeNat a) := rfl

theorem length_padR_left (m a : ℕ) : (padR (pairLen m a) (encodeNat m)).length = pairLen m a :=
  length_padR_of_le (pairLen_le_left m a)

theorem length_padR_right (m a : ℕ) : (padR (pairLen m a) (encodeNat a)).length = pairLen m a :=
  length_padR_of_le (pairLen_le_right m a)

theorem encodePair_length (m a : ℕ) : (encodePair m a).length = 2 * pairLen m a := by
  rw [encodePair_eq, List.length_append, length_padR_left, length_padR_right]; ring

theorem encodePair_half (m a : ℕ) : (encodePair m a).length / 2 = pairLen m a := by
  rw [encodePair_length]; omega

theorem encodePair_take (m a : ℕ) :
    (encodePair m a).take ((encodePair m a).length / 2) = padR (pairLen m a) (encodeNat m) := by
  rw [encodePair_half, encodePair_eq, List.take_left' (length_padR_left m a)]

theorem encodePair_drop (m a : ℕ) :
    (encodePair m a).drop ((encodePair m a).length / 2) = padR (pairLen m a) (encodeNat a) := by
  rw [encodePair_half, encodePair_eq, List.drop_left' (length_padR_left m a)]

/-- The reader's first half is `m`. -/
theorem leVal_take_half (m a : ℕ) :
    leVal ((encodePair m a).take ((encodePair m a).length / 2)) = m := by
  rw [encodePair_take, leVal_padR, leVal_encodeNat]

/-- The reader's second half is `a`. -/
theorem leVal_drop_half (m a : ℕ) :
    leVal ((encodePair m a).drop ((encodePair m a).length / 2)) = a := by
  rw [encodePair_drop, leVal_padR, leVal_encodeNat]

theorem length_take_half (w : List Bool) : (w.take (w.length / 2)).length = w.length / 2 := by
  rw [List.length_take]; omega

/-- On any word, the first half's value is `< 2^(|w|/2)`. -/
theorem leVal_take_half_lt (w : List Bool) : leVal (w.take (w.length / 2)) < 2 ^ (w.length / 2) := by
  have := leVal_lt (w.take (w.length / 2))
  rwa [length_take_half] at this

theorem lt_two_pow_half_left (m a : ℕ) : m < 2 ^ ((encodePair m a).length / 2) := by
  have := leVal_take_half_lt (encodePair m a)
  rwa [leVal_take_half] at this

theorem lt_two_pow_half_right (m a : ℕ) : a < 2 ^ ((encodePair m a).length / 2) := by
  have := leVal_lt (padR (pairLen m a) (encodeNat a))
  rwa [leVal_padR, leVal_encodeNat, length_padR_right, ← encodePair_half] at this

/-! ## Sanity checks -/

example : encodePair 7 2 = [true, true, true, false, true, false] := by decide
example : leVal [true, false, true] = 5 := rfl

end EthFollowup.ModP
