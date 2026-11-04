/-
# The top-down comparison chain (module M2, identity (I-D) of the ModP plan; generic for ArithNet)

Pure Mathlib; compiles in both toolchains.

Limbs `yl i`, `pl i` (`i < L`, each `< 2^b`) of `Y = Σ yl i 2^(bi)` and `P = Σ pl i 2^(bi)`
(this sum is `Factoring.ofLimbs b yl L` of Params.lean, definitionally). The comparison states are
`0` (lt), `1` (eq), `2` (gt) (`cmpN`). The state wire `cy j` (`j + 1 < L`) runs from cell `j+1` to
cell `j`; cell `i` computes `s_out := cmpStep s_in (yl i) (pl i)` from
`s_in := if i + 1 = L then 1 else cy i` (i.e. `i = L − 1` for `i < L`) and checks
`cy (i−1) = s_out` if `0 < i`, and at `i = 0` that the final state satisfies the relation
`r : CmpRel` (`lt`: state 0, `le`: ≠ 2, `eq`: 1, `ge`: ≠ 0, `gt`: 2; `CmpRel.test`) (`cmpCell r`, a `Bool`).
The right operand `P` is arbitrary limbs: a variable's limbs or a constant's.

* `cmpChain_iff`: for `0 < L`, some state wires pass all cells iff `r.Holds Y P`
  (`lt`: `Y < P`, `le`: `Y ≤ P`, `eq`: `Y = P`, `ge`: `P ≤ Y`, `gt`: `P < Y`);
* `cmpChain_unique`: passing state wires are the canonical ones,
  `cy j = cmpN (hsuf yl (j+1)) (hsuf pl (j+1))` (`hsuf f j = Σ_{i<L−j} f (j+i) 2^(bi)`, the value of
  the limbs `≥ j`); `cmpCell_canon`: the canonical wires pass every cell iff `Y < P`;
* `hsuf_limb`: with the limbs of a number `y < 2^(bL)`, `hsuf … j = y / 2^(bj)`; `cmpChain_iff_limb`.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset

/-- Comparison state: `0` if `u < v`, `1` if `u = v`, `2` if `u > v`. -/
def cmpN (u v : ℕ) : ℕ := if u < v then 0 else if u = v then 1 else 2

/-- One top-down step: a decided state (`≠ 1`) propagates, `eq` is refined by the current limbs. -/
def cmpStep (s y p : ℕ) : ℕ := if s ≠ 1 then s else cmpN y p

/-- The five relations of a comparison `Y r P`. -/
inductive CmpRel | lt | le | eq | ge | gt
  deriving DecidableEq, Repr

/-- The relation as a test on the final comparison state. -/
def CmpRel.test : CmpRel → ℕ → Bool
  | .lt, s => s == 0
  | .le, s => s != 2
  | .eq, s => s == 1
  | .ge, s => s != 0
  | .gt, s => s == 2

/-- The relation on numbers. -/
def CmpRel.Holds : CmpRel → ℕ → ℕ → Prop
  | .lt, u, v => u < v
  | .le, u, v => u ≤ v
  | .eq, u, v => u = v
  | .ge, u, v => v ≤ u
  | .gt, u, v => v < u

instance (r : CmpRel) (u v : ℕ) : Decidable (r.Holds u v) := by
  cases r <;> unfold CmpRel.Holds <;> infer_instance

theorem CmpRel.test_cmpN (r : CmpRel) (u v : ℕ) : r.test (cmpN u v) = true ↔ r.Holds u v := by
  cases r <;> unfold CmpRel.test CmpRel.Holds cmpN <;> split_ifs <;> simp <;> omega

/-- The comparison part of cell `i` (of `L` cells) for the relation `r`; `cy` reads the state wires. -/
def cmpCell (r : CmpRel) (L : ℕ) (yl pl cy : ℕ → ℕ) (i : ℕ) : Bool :=
  if i = 0 then r.test (cmpStep (if i + 1 = L then 1 else cy i) (yl i) (pl i))
  else cy (i - 1) == cmpStep (if i + 1 = L then 1 else cy i) (yl i) (pl i)

/-- The value of the limbs `≥ j`: `Σ_{i < L−j} f (j+i) 2^(bi)`. -/
def hsuf (b L : ℕ) (f : ℕ → ℕ) (j : ℕ) : ℕ := ∑ i ∈ range (L - j), f (j + i) * 2 ^ (b * i)

theorem hsuf_zero (b L : ℕ) (f : ℕ → ℕ) : hsuf b L f 0 = ∑ i ∈ range L, f i * 2 ^ (b * i) := by
  simp [hsuf]

theorem hsuf_self (b L : ℕ) (f : ℕ → ℕ) : hsuf b L f L = 0 := by simp [hsuf]

theorem hsuf_step (b L : ℕ) (f : ℕ → ℕ) {j : ℕ} (hj : j < L) :
    hsuf b L f j = f j + 2 ^ b * hsuf b L f (j + 1) := by
  unfold hsuf
  rw [show L - j = (L - (j + 1)) + 1 by omega, sum_range_succ', mul_sum]
  simp only [add_zero, mul_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [show j + (i + 1) = j + 1 + i by omega, mul_add, mul_one, pow_add]; ring

theorem lex_lt {B a a' u u' : ℕ} (ha : a < B) (hu : u < u') : a + B * u < a' + B * u' := by
  have : B * (u + 1) ≤ B * u' := Nat.mul_le_mul_left B hu
  rw [mul_add, mul_one] at this
  omega

/-- Lexicographic comparison of two-digit numbers. -/
theorem cmpN_digit {B a a' u u' : ℕ} (ha : a < B) (ha' : a' < B) :
    cmpN (a + B * u) (a' + B * u') = cmpStep (cmpN u u') a a' := by
  rcases lt_trichotomy u u' with h | rfl | h
  · have := lex_lt (a' := a') ha h
    simp [cmpN, cmpStep, h, this]
  · simp only [cmpStep, cmpN, lt_irrefl, if_false, ne_eq]
    simp
  · have := lex_lt (a' := a) ha' h
    have h1 : ¬ u < u' := by omega
    have h2 : ¬ u = u' := by omega
    have h3 : ¬ a + B * u < a' + B * u' := by omega
    have h4 : ¬ a + B * u = a' + B * u' := by omega
    simp [cmpN, cmpStep, h1, h2, h3, h4]

/-- The canonical state below cell `j−1`: comparison of the limbs `≥ j`. -/
def cmpT (b L : ℕ) (yl pl : ℕ → ℕ) (j : ℕ) : ℕ := cmpN (hsuf b L yl j) (hsuf b L pl j)

theorem cmpT_self (b L : ℕ) (yl pl : ℕ → ℕ) : cmpT b L yl pl L = 1 := by
  simp [cmpT, hsuf_self, cmpN]

theorem cmpT_step {b L : ℕ} {yl pl : ℕ → ℕ} (hyl : ∀ i < L, yl i < 2 ^ b) (hpl : ∀ i < L, pl i < 2 ^ b)
    {j : ℕ} (hj : j < L) : cmpT b L yl pl j = cmpStep (cmpT b L yl pl (j + 1)) (yl j) (pl j) := by
  unfold cmpT
  rw [hsuf_step b L yl hj, hsuf_step b L pl hj]
  exact cmpN_digit (hyl j hj) (hpl j hj)

theorem cmpT_zero_test_iff (r : CmpRel) (b L : ℕ) (yl pl : ℕ → ℕ) :
    r.test (cmpT b L yl pl 0) = true ↔
      r.Holds (∑ i ∈ range L, yl i * 2 ^ (b * i)) (∑ i ∈ range L, pl i * 2 ^ (b * i)) := by
  unfold cmpT
  rw [hsuf_zero, hsuf_zero, CmpRel.test_cmpN]

/-- Along passing state wires, the input state of every cell is the canonical one. -/
theorem cmpChain_sin {r : CmpRel} {b L : ℕ} {yl pl cy : ℕ → ℕ} (hyl : ∀ i < L, yl i < 2 ^ b)
    (hpl : ∀ i < L, pl i < 2 ^ b) (h : ∀ i < L, cmpCell r L yl pl cy i = true) :
    ∀ d i, i + d + 1 = L → (if i + 1 = L then 1 else cy i) = cmpT b L yl pl (i + 1)
  | 0, i, hi => by rw [if_pos (by omega), show i + 1 = L by omega, cmpT_self]
  | d + 1, i, hi => by
    have ih := cmpChain_sin hyl hpl h d (i + 1) (by omega)
    have hc := h (i + 1) (by omega)
    simp only [cmpCell, show i + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel, beq_iff_eq] at hc
    rw [if_neg (by omega), hc, ih, ← cmpT_step hyl hpl (by omega)]

/-- (I-D), uniqueness: passing state wires are the canonical ones. -/
theorem cmpChain_unique {r : CmpRel} {b L : ℕ} {yl pl cy : ℕ → ℕ} (hyl : ∀ i < L, yl i < 2 ^ b)
    (hpl : ∀ i < L, pl i < 2 ^ b) (h : ∀ i < L, cmpCell r L yl pl cy i = true) :
    ∀ j, j + 1 < L → cy j = cmpT b L yl pl (j + 1) := by
  intro j hj
  have := cmpChain_sin hyl hpl h (L - j - 1) j (by omega)
  rwa [if_neg (by omega)] at this

/-- The canonical state wires `cy j = cmpT (j+1)` pass cell `i` iff (`i = 0` →) `r.Holds Y P`. -/
theorem cmpCell_canon (r : CmpRel) {b L : ℕ} {yl pl : ℕ → ℕ} (hyl : ∀ i < L, yl i < 2 ^ b)
    (hpl : ∀ i < L, pl i < 2 ^ b) {i : ℕ} (hi : i < L) :
    cmpCell r L yl pl (fun j => cmpT b L yl pl (j + 1)) i = true ↔
      (i = 0 → r.Holds (∑ i ∈ range L, yl i * 2 ^ (b * i)) (∑ i ∈ range L, pl i * 2 ^ (b * i))) := by
  have hs : (if i + 1 = L then 1 else cmpT b L yl pl (i + 1)) = cmpT b L yl pl (i + 1) := by
    split_ifs with h1
    · rw [h1, cmpT_self]
    · rfl
  unfold cmpCell
  rw [hs, ← cmpT_step hyl hpl hi]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp [cmpT_zero_test_iff]
  · simp [show i ≠ 0 by omega, show i - 1 + 1 = i by omega]

/-- (I-D): for `0 < L` and limbs `< 2^b`, some state wires pass all cells iff `r.Holds Y P`. -/
theorem cmpChain_iff (r : CmpRel) {b L : ℕ} {yl pl : ℕ → ℕ} (hL : 0 < L) (hyl : ∀ i < L, yl i < 2 ^ b)
    (hpl : ∀ i < L, pl i < 2 ^ b) :
    (∃ cy : ℕ → ℕ, ∀ i < L, cmpCell r L yl pl cy i = true) ↔
      r.Holds (∑ i ∈ range L, yl i * 2 ^ (b * i)) (∑ i ∈ range L, pl i * 2 ^ (b * i)) := by
  constructor
  · rintro ⟨cy, h⟩
    have hs := cmpChain_sin hyl hpl h (L - 1) 0 (by omega)
    have hc := h 0 hL
    simp only [cmpCell, if_true] at hc
    rw [hs, ← cmpT_step hyl hpl hL] at hc
    exact (cmpT_zero_test_iff r b L yl pl).1 hc
  · intro hlt
    exact ⟨_, fun i hi => (cmpCell_canon r hyl hpl hi).2 fun _ => hlt⟩

/-! ## Limbs of a number -/

/-- With the limbs `y / 2^(bi) % 2^b` of `y < 2^(bL)`, `hsuf j = y / 2^(bj)` (`j ≤ L`). -/
theorem hsuf_limb (b L y : ℕ) (hy : y < 2 ^ (b * L)) :
    ∀ d j, j + d = L → hsuf b L (fun i => y / 2 ^ (b * i) % 2 ^ b) j = y / 2 ^ (b * j)
  | 0, j, hj => by
    rw [show j = L by omega, hsuf_self, Nat.div_eq_of_lt hy]
  | d + 1, j, hj => by
    rw [hsuf_step b L _ (by omega), hsuf_limb b L y hy d (j + 1) (by omega)]
    have e : 2 ^ (b * (j + 1)) = 2 ^ (b * j) * 2 ^ b := by rw [mul_add, mul_one, pow_add]
    rw [e, ← Nat.div_div_eq_div_mul]
    exact Nat.mod_add_div _ _

theorem sum_limb (b L y : ℕ) (hy : y < 2 ^ (b * L)) :
    ∑ i ∈ range L, y / 2 ^ (b * i) % 2 ^ b * 2 ^ (b * i) = y := by
  have := hsuf_limb b L y hy L 0 (by omega)
  rw [hsuf_zero] at this
  simpa using this

/-- (I-D) with the limbs of numbers `y, p < 2^(bL)`. -/
theorem cmpChain_iff_limb (r : CmpRel) {b L y p : ℕ} (hL : 0 < L) (hy : y < 2 ^ (b * L))
    (hp : p < 2 ^ (b * L)) :
    (∃ cy : ℕ → ℕ, ∀ i < L, cmpCell r L (fun i => y / 2 ^ (b * i) % 2 ^ b)
      (fun i => p / 2 ^ (b * i) % 2 ^ b) cy i = true) ↔ r.Holds y p := by
  rw [cmpChain_iff r hL (fun i _ => Nat.mod_lt _ (by positivity)) (fun i _ => Nat.mod_lt _ (by positivity)),
    sum_limb b L y hy, sum_limb b L p hp]

/-- The canonical states for the limbs of numbers: `cmpT (j+1) = cmpN (y / 2^(b(j+1))) (p / 2^(b(j+1)))`. -/
theorem cmpT_limb {b L y p : ℕ} (hy : y < 2 ^ (b * L)) (hp : p < 2 ^ (b * L)) {j : ℕ} (hj : j ≤ L) :
    cmpT b L (fun i => y / 2 ^ (b * i) % 2 ^ b) (fun i => p / 2 ^ (b * i) % 2 ^ b) j =
      cmpN (y / 2 ^ (b * j)) (p / 2 ^ (b * j)) := by
  unfold cmpT
  rw [hsuf_limb b L y hy (L - j) j (by omega), hsuf_limb b L p hp (L - j) j (by omega)]

theorem cmpN_le (u v : ℕ) : cmpN u v ≤ 2 := by unfold cmpN; split_ifs <;> omega

end EthFollowup.ModP
