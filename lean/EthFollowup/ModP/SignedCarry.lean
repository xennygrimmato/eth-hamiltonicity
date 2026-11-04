/-
# The signed carry chain (module M1, identity (I-C) of the ModP plan; generic for ArithNet)

Pure Mathlib; compiles in both toolchains.

Generic form (ArithNet carry vertex): left digits `c k` (e.g. `Σ_lhs coeff·value` at position `k`), right
digits `e k` (`Σ_rhs coeff·value`), offset carries `R k = r k + OFF` (`r k` the signed carry). The check at
position `k < K` is the single ℕ equation
`R (k+1) * 2^b + e k + OFF = c k + R k + OFF * 2^b`  (i.e. `c k + r k = e k + 2^b r (k+1)`);
`SChain` adds `R 0 = OFF` and `R K = OFF`.

* `schain_inv`: `R k · 2^(bk) = OFF · 2^(bk) + Σ_{j<k} (c j − e j) 2^(bj)` in ℤ;
* `schain_sum` / `schain_of_sum` / `schain_iff`: a valid chain exists iff `Σ_{k<K} c k 2^(bk) = Σ_{k<K} e k 2^(bk)`
  (← under `c k, e k ≤ OFF (2^b − 1)`);
* `schain_unique`, `schain_eq_sR`: the carries are determined (`R k = sR … k`, no bounds needed);
* `schain_range`: `0 < R k < 2 OFF` (same bounds, `0 < OFF`), i.e. `|r k| < OFF`;
* wire form (`RofW`, `carryChk`, `schainW_iff`, `carryChk_iff`, `carryChk_sR`, `carryChk_unique`,
  `carryChk_range`): `Rin := if k = 0 then OFF else rr (k−1)`, `Rout := if k + 1 < K then rr k else OFF`;
* linear combinations (`sum_lin`, `lin_le`, `mass_le_OFF`): with coefficient mass `≤ 32` and values
  `≤ 2^(J+1)`, the digits are `≤ OFF (2^b − 1)` for `OFF = 2^(J+6)`, `1 ≤ b`; then `R < 2^(J+7)`;
* the three-digit form of the first plan (`SChainOK … c c' x`, equation `R (k+1) 2^b + c' k + x k + OFF =
  c k + R k + OFF 2^b`): `schainOK_iff_schain`, `schainOK_iff`, `schainOK_unique`, `schainOK_range`.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset

/-- A valid signed (offset) carry chain of length `K`. -/
def SChain (b K OFF : ℕ) (c e R : ℕ → ℕ) : Prop :=
  R 0 = OFF ∧ R K = OFF ∧
    ∀ k < K, R (k + 1) * 2 ^ b + e k + OFF = c k + R k + OFF * 2 ^ b

/-- The signed digit `c k − e k`. -/
def sdig (c e : ℕ → ℕ) (k : ℕ) : ℤ := (c k : ℤ) - e k

/-- Signed partial sums `A k = Σ_{j<k} sdig j 2^(bj)`. -/
def spre (b : ℕ) (c e : ℕ → ℕ) (k : ℕ) : ℤ := ∑ j ∈ range k, sdig c e j * 2 ^ (b * j)

/-- Signed suffix sums `S k = Σ_{i < K−k} sdig (k+i) 2^(bi)`. -/
def ssuf (b K : ℕ) (c e : ℕ → ℕ) (k : ℕ) : ℤ :=
  ∑ i ∈ range (K - k), sdig c e (k + i) * 2 ^ (b * i)

/-- The canonical offset carry `R k = OFF − S k` (`= OFF + A k / 2^(bk)` when the sums agree). -/
def sR (b K OFF : ℕ) (c e : ℕ → ℕ) (k : ℕ) : ℕ := ((OFF : ℤ) - ssuf b K c e k).toNat

theorem spre_succ (b : ℕ) (c e : ℕ → ℕ) (k : ℕ) :
    spre b c e (k + 1) = spre b c e k + sdig c e k * 2 ^ (b * k) := by
  simp [spre, sum_range_succ]

theorem ssuf_self (b K : ℕ) (c e : ℕ → ℕ) : ssuf b K c e K = 0 := by simp [ssuf]

theorem ssuf_zero (b K : ℕ) (c e : ℕ → ℕ) : ssuf b K c e 0 = spre b c e K := by
  simp [ssuf, spre]

/-- `S k = sdig k + 2^b S (k+1)` for `k < K`. -/
theorem ssuf_step (b K : ℕ) (c e : ℕ → ℕ) {k : ℕ} (hk : k < K) :
    ssuf b K c e k = sdig c e k + 2 ^ b * ssuf b K c e (k + 1) := by
  unfold ssuf
  rw [show K - k = (K - (k + 1)) + 1 by omega, sum_range_succ', mul_sum]
  simp only [add_zero, mul_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [show k + (i + 1) = k + 1 + i by omega, mul_add, mul_one, pow_add]; ring

/-- `A K = A k + 2^(bk) S k` for `k ≤ K`. -/
theorem spre_split (b K : ℕ) (c e : ℕ → ℕ) {k : ℕ} (hk : k ≤ K) :
    spre b c e K = spre b c e k + 2 ^ (b * k) * ssuf b K c e k := by
  unfold spre ssuf
  conv_lhs => rw [show K = k + (K - k) by omega, sum_range_add]
  rw [mul_sum]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [mul_add, pow_add]; ring

/-- The signed digit sum vanishes iff the two digit sums agree. -/
theorem spre_eq_zero_iff (b K : ℕ) (c e : ℕ → ℕ) :
    spre b c e K = 0 ↔
      ∑ k ∈ range K, c k * 2 ^ (b * k) = ∑ k ∈ range K, e k * 2 ^ (b * k) := by
  have eq0 : spre b c e K = ((∑ k ∈ range K, c k * 2 ^ (b * k) : ℕ) : ℤ) -
      ((∑ k ∈ range K, e k * 2 ^ (b * k) : ℕ) : ℤ) := by
    unfold spre sdig
    rw [Nat.cast_sum, Nat.cast_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => by push_cast; ring
  rw [eq0, sub_eq_zero]
  exact Nat.cast_inj

/-- The chain invariant (no bounds needed). -/
theorem schain_inv {b K OFF : ℕ} {c e R : ℕ → ℕ} (h : SChain b K OFF c e R) :
    ∀ k ≤ K, (R k : ℤ) * 2 ^ (b * k) = OFF * 2 ^ (b * k) + spre b c e k
  | 0, _ => by simp [spre, h.1]
  | k + 1, hk => by
    have ih := schain_inv h k (by omega)
    have hs := h.2.2 k (by omega)
    have hs' : (R (k + 1) : ℤ) * 2 ^ b = c k + R k + OFF * 2 ^ b - e k - OFF := by
      have : ((R (k + 1) * 2 ^ b + e k + OFF : ℕ) : ℤ) = ((c k + R k + OFF * 2 ^ b : ℕ) : ℤ) := by
        rw [hs]
      push_cast at this
      linarith
    rw [spre_succ, show b * (k + 1) = b * k + b by ring, pow_add]
    calc (R (k + 1) : ℤ) * (2 ^ (b * k) * 2 ^ b) = (R (k + 1) * 2 ^ b) * 2 ^ (b * k) := by ring
      _ = _ := by rw [hs']; unfold sdig; linear_combination ih

/-- A valid chain gives equal digit sums. -/
theorem schain_sum {b K OFF : ℕ} {c e R : ℕ → ℕ} (h : SChain b K OFF c e R) :
    ∑ k ∈ range K, c k * 2 ^ (b * k) = ∑ k ∈ range K, e k * 2 ^ (b * k) := by
  have hi := schain_inv h K le_rfl
  rw [h.2.1] at hi
  exact (spre_eq_zero_iff b K c e).1 (by linarith)

/-- The carries of a valid chain are the canonical ones (no bounds needed). -/
theorem schain_eq_sR {b K OFF : ℕ} {c e R : ℕ → ℕ} (h : SChain b K OFF c e R) :
    ∀ k ≤ K, R k = sR b K OFF c e k := by
  intro k hk
  have hi := schain_inv h k hk
  have h0 : spre b c e K = 0 := (spre_eq_zero_iff b K c e).2 (schain_sum h)
  have hsp := spre_split b K c e hk
  rw [h0] at hsp
  have hpos : (0 : ℤ) < 2 ^ (b * k) := by positivity
  have eq0 : (R k : ℤ) = OFF - ssuf b K c e k := by
    have : ((R k : ℤ) - (OFF - ssuf b K c e k)) * 2 ^ (b * k) = 0 := by linear_combination hi - hsp
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd h1 hpos.ne'
  unfold sR
  rw [← eq0, Int.toNat_natCast]

/-- Uniqueness of the carries. -/
theorem schain_unique {b K OFF : ℕ} {c e R R' : ℕ → ℕ} (h : SChain b K OFF c e R)
    (h' : SChain b K OFF c e R') : ∀ k ≤ K, R k = R' k := fun k hk => by
  rw [schain_eq_sR h k hk, schain_eq_sR h' k hk]

/-- Geometric bound: digits `≤ OFF (2^b − 1)` give `Σ_{j<k} f j 2^(bj) ≤ OFF (2^(bk) − 1)`. -/
theorem geo_bound {b OFF : ℕ} {f : ℕ → ℕ} :
    ∀ k, (∀ j < k, f j ≤ OFF * (2 ^ b - 1)) →
      (∑ j ∈ range k, (f j : ℤ) * 2 ^ (b * j)) ≤ OFF * (2 ^ (b * k) - 1)
  | 0, _ => by simp
  | k + 1, hf => by
    have ih := geo_bound k fun j hj => hf j (by omega)
    have hk : (f k : ℤ) ≤ OFF * (2 ^ b - 1) := by
      have h1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      have := hf k (by omega)
      have : ((f k : ℕ) : ℤ) ≤ ((OFF * (2 ^ b - 1) : ℕ) : ℤ) := by exact_mod_cast this
      push_cast [Nat.cast_sub h1] at this
      exact this
    rw [sum_range_succ, show b * (k + 1) = b * k + b by ring, pow_add]
    have hp : (0 : ℤ) ≤ 2 ^ (b * k) := by positivity
    nlinarith

/-- Bounds on the signed partial sums. -/
theorem spre_abs_le {b OFF : ℕ} {c e : ℕ → ℕ} {k : ℕ}
    (hc : ∀ j < k, c j ≤ OFF * (2 ^ b - 1)) (he : ∀ j < k, e j ≤ OFF * (2 ^ b - 1)) :
    -(OFF * (2 ^ (b * k) - 1) : ℤ) ≤ spre b c e k ∧ spre b c e k ≤ OFF * (2 ^ (b * k) - 1) := by
  have h1 := geo_bound (f := c) k hc
  have h2 := geo_bound (f := fun j => e j) k he
  have hnn1 : (0 : ℤ) ≤ ∑ j ∈ range k, (c j : ℤ) * 2 ^ (b * j) := sum_nonneg fun _ _ => by positivity
  have hnn2 : (0 : ℤ) ≤ ∑ j ∈ range k, ((e j : ℕ) : ℤ) * 2 ^ (b * j) :=
    sum_nonneg fun _ _ => by positivity
  have eq0 : spre b c e k = ∑ j ∈ range k, (c j : ℤ) * 2 ^ (b * j) -
      ∑ j ∈ range k, ((e j : ℕ) : ℤ) * 2 ^ (b * j) := by
    unfold spre sdig
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => by push_cast; ring
  rw [eq0]
  constructor <;> linarith

/-- Under the digit bounds and equal sums, `0 ≤ OFF − S k ≤ 2 OFF` (strict if `0 < OFF`). -/
theorem ssuf_bounds {b K OFF : ℕ} {c e : ℕ → ℕ}
    (hc : ∀ k < K, c k ≤ OFF * (2 ^ b - 1)) (he : ∀ k < K, e k ≤ OFF * (2 ^ b - 1))
    (hs : ∑ k ∈ range K, c k * 2 ^ (b * k) = ∑ k ∈ range K, e k * 2 ^ (b * k))
    {k : ℕ} (hk : k ≤ K) :
    ((0 : ℤ) ≤ OFF - ssuf b K c e k ∧ (OFF : ℤ) - ssuf b K c e k ≤ 2 * OFF) ∧
      (0 < OFF → (0 : ℤ) < OFF - ssuf b K c e k ∧ (OFF : ℤ) - ssuf b K c e k < 2 * OFF) := by
  have h0 : spre b c e K = 0 := (spre_eq_zero_iff b K c e).2 hs
  have hsp := spre_split b K c e hk
  rw [h0] at hsp
  obtain ⟨hl, hu⟩ := spre_abs_le (k := k) (fun j hj => hc j (by omega)) (fun j hj => he j (by omega))
  have hpos : (0 : ℤ) < 2 ^ (b * k) := by positivity
  set P : ℤ := 2 ^ (b * k)
  set S := ssuf b K c e k
  have hA : spre b c e k = -(P * S) := by linarith
  rw [hA] at hl hu
  have hO : (0 : ℤ) ≤ OFF := by positivity
  -- hl : P S ≤ OFF P − OFF,  hu : −P S ≤ OFF P − OFF
  have k1 : S ≤ OFF := by
    by_contra hcon
    have := mul_lt_mul_of_pos_left (lt_of_not_ge hcon) hpos
    nlinarith
  have k2 : -S ≤ OFF := by
    by_contra hcon
    have := mul_lt_mul_of_pos_left (lt_of_not_ge hcon) hpos
    nlinarith
  refine ⟨⟨by linarith, by linarith⟩, fun hO' => ⟨?_, ?_⟩⟩
  · by_contra hcon
    have h3 : (OFF : ℤ) ≤ S := by linarith
    have := mul_le_mul_of_nonneg_left h3 hpos.le
    have : (0 : ℤ) < OFF := by exact_mod_cast hO'
    nlinarith
  · by_contra hcon
    have h3 : (OFF : ℤ) ≤ -S := by linarith
    have := mul_le_mul_of_nonneg_left h3 hpos.le
    have : (0 : ℤ) < OFF := by exact_mod_cast hO'
    nlinarith

/-- Conversely, equal digit sums give a valid chain (the canonical one), under the digit bounds. -/
theorem schain_of_sum {b K OFF : ℕ} {c e : ℕ → ℕ}
    (hc : ∀ k < K, c k ≤ OFF * (2 ^ b - 1)) (he : ∀ k < K, e k ≤ OFF * (2 ^ b - 1))
    (hs : ∑ k ∈ range K, c k * 2 ^ (b * k) = ∑ k ∈ range K, e k * 2 ^ (b * k)) :
    SChain b K OFF c e (sR b K OFF c e) := by
  have h0 : spre b c e K = 0 := (spre_eq_zero_iff b K c e).2 hs
  have cast_sR : ∀ k ≤ K, (sR b K OFF c e k : ℤ) = OFF - ssuf b K c e k := fun k hk =>
    Int.toNat_of_nonneg (ssuf_bounds hc he hs hk).1.1
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · unfold sR; rw [ssuf_zero, h0, sub_zero, Int.toNat_natCast]
  · unfold sR; rw [ssuf_self, sub_zero, Int.toNat_natCast]
  · have e1 := cast_sR (k + 1) hk
    have e0 := cast_sR k hk.le
    have hst := ssuf_step b K c e hk
    have : ((sR b K OFF c e (k + 1) * 2 ^ b + e k + OFF : ℕ) : ℤ) =
        ((c k + sR b K OFF c e k + OFF * 2 ^ b : ℕ) : ℤ) := by
      push_cast
      rw [e1, e0, hst]
      unfold sdig
      ring
    exact_mod_cast this

/-- (I-C): under the digit bounds, a valid signed chain exists iff the digit sums agree. -/
theorem schain_iff {b K OFF : ℕ} {c e : ℕ → ℕ}
    (hc : ∀ k < K, c k ≤ OFF * (2 ^ b - 1)) (he : ∀ k < K, e k ≤ OFF * (2 ^ b - 1)) :
    (∃ R, SChain b K OFF c e R) ↔
      ∑ k ∈ range K, c k * 2 ^ (b * k) = ∑ k ∈ range K, e k * 2 ^ (b * k) :=
  ⟨fun ⟨_, h⟩ => schain_sum h, fun hs => ⟨_, schain_of_sum hc he hs⟩⟩

/-- Range of the canonical carries: `0 < sR k < 2 OFF` for `k ≤ K` (`0 < OFF`). -/
theorem sR_range {b K OFF : ℕ} {c e : ℕ → ℕ}
    (hc : ∀ k < K, c k ≤ OFF * (2 ^ b - 1)) (he : ∀ k < K, e k ≤ OFF * (2 ^ b - 1))
    (hs : ∑ k ∈ range K, c k * 2 ^ (b * k) = ∑ k ∈ range K, e k * 2 ^ (b * k))
    (hO : 0 < OFF) {k : ℕ} (hk : k ≤ K) : 0 < sR b K OFF c e k ∧ sR b K OFF c e k < 2 * OFF := by
  obtain ⟨h1, h2⟩ := (ssuf_bounds hc he hs hk).2 hO
  have eq0 : (sR b K OFF c e k : ℤ) = OFF - ssuf b K c e k := Int.toNat_of_nonneg h1.le
  constructor
  · have : (0 : ℤ) < sR b K OFF c e k := by rw [eq0]; exact h1
    exact_mod_cast this
  · have : (sR b K OFF c e k : ℤ) < ((2 * OFF : ℕ) : ℤ) := by rw [eq0]; push_cast; exact h2
    exact_mod_cast this

/-- (I-C) range: the carries of any valid chain satisfy `0 < R k < 2 OFF`, i.e. `|r k| < OFF`. -/
theorem schain_range {b K OFF : ℕ} {c e R : ℕ → ℕ} (h : SChain b K OFF c e R)
    (hc : ∀ k < K, c k ≤ OFF * (2 ^ b - 1)) (he : ∀ k < K, e k ≤ OFF * (2 ^ b - 1))
    (hO : 0 < OFF) : ∀ k ≤ K, 0 < R k ∧ R k < 2 * OFF := fun k hk => by
  rw [schain_eq_sR h k hk]; exact sR_range hc he (schain_sum h) hO hk

/-! ## Wire form: `R k` from the wires `rr j = R (j+1)`, `j + 1 < K` -/

/-- The offset carries read from the wires: `R 0 = OFF`, `R k = rr (k−1)` for `0 < k < K`, `R K = OFF`. -/
def RofW (K OFF : ℕ) (rr : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k = 0 then OFF else if k < K then rr (k - 1) else OFF

/-- The §3 carry check at position `k` (one ℕ equation). -/
def carryChk (b K OFF : ℕ) (c e rr : ℕ → ℕ) (k : ℕ) : Prop :=
  (if k + 1 < K then rr k else OFF) * 2 ^ b + e k + OFF =
    c k + (if k = 0 then OFF else rr (k - 1)) + OFF * 2 ^ b

instance (b K OFF : ℕ) (c e rr : ℕ → ℕ) (k : ℕ) : Decidable (carryChk b K OFF c e rr k) := by
  unfold carryChk; infer_instance

theorem schainW_iff (b K OFF : ℕ) (c e rr : ℕ → ℕ) :
    (∀ k < K, carryChk b K OFF c e rr k) ↔ SChain b K OFF c e (RofW K OFF rr) := by
  have h0 : RofW K OFF rr 0 = OFF := by simp [RofW]
  have hK : RofW K OFF rr K = OFF := by unfold RofW; split_ifs <;> first | rfl | omega
  have hstep : ∀ k < K, RofW K OFF rr (k + 1) = (if k + 1 < K then rr k else OFF) ∧
      RofW K OFF rr k = (if k = 0 then OFF else rr (k - 1)) := fun k hk => by
    unfold RofW
    refine ⟨by simp, ?_⟩
    split_ifs <;> rfl
  unfold SChain carryChk
  refine ⟨fun h => ⟨h0, hK, fun k hk => ?_⟩, fun h k hk => ?_⟩
  · rw [(hstep k hk).1, (hstep k hk).2]; exact h k hk
  · rw [← (hstep k hk).1, ← (hstep k hk).2]; exact h.2.2 k hk

/-- (I-C), wire form: the §3 carry checks pass for some wire values iff the digit sums agree. -/
theorem carryChk_iff {b K OFF : ℕ} {c e : ℕ → ℕ}
    (hc : ∀ k < K, c k ≤ OFF * (2 ^ b - 1)) (he : ∀ k < K, e k ≤ OFF * (2 ^ b - 1)) :
    (∃ rr, ∀ k < K, carryChk b K OFF c e rr k) ↔
      ∑ k ∈ range K, c k * 2 ^ (b * k) = ∑ k ∈ range K, e k * 2 ^ (b * k) := by
  constructor
  · rintro ⟨rr, h⟩; exact schain_sum ((schainW_iff b K OFF c e rr).1 h)
  · intro hs
    refine ⟨fun j => sR b K OFF c e (j + 1), (schainW_iff b K OFF c e _).2 ?_⟩
    have hch := schain_of_sum hc he hs
    have eq0 : ∀ k ≤ K, RofW K OFF (fun j => sR b K OFF c e (j + 1)) k = sR b K OFF c e k := by
      intro k hk
      unfold RofW
      split_ifs with h1 h2
      · rw [h1, hch.1]
      · simp only; congr 1; omega
      · rw [show k = K by omega, hch.2.1]
    refine ⟨?_, ?_, fun k hk => ?_⟩
    · rw [eq0 0 (Nat.zero_le _)]; exact hch.1
    · rw [eq0 K le_rfl]; exact hch.2.1
    · rw [eq0 (k + 1) hk, eq0 k hk.le]; exact hch.2.2 k hk

/-- The canonical wire values pass every carry check (given equal sums and the digit bounds). -/
theorem carryChk_sR {b K OFF : ℕ} {c e : ℕ → ℕ}
    (hc : ∀ k < K, c k ≤ OFF * (2 ^ b - 1)) (he : ∀ k < K, e k ≤ OFF * (2 ^ b - 1))
    (hs : ∑ k ∈ range K, c k * 2 ^ (b * k) = ∑ k ∈ range K, e k * 2 ^ (b * k)) :
    ∀ k < K, carryChk b K OFF c e (fun j => sR b K OFF c e (j + 1)) k := by
  have hch := schain_of_sum hc he hs
  have eq0 : ∀ k ≤ K, RofW K OFF (fun j => sR b K OFF c e (j + 1)) k = sR b K OFF c e k := by
    intro k hk
    unfold RofW
    split_ifs with h1 h2
    · rw [h1, hch.1]
    · simp only; congr 1; omega
    · rw [show k = K by omega, hch.2.1]
  refine (schainW_iff b K OFF c e _).2 ⟨?_, ?_, fun k hk => ?_⟩
  · rw [eq0 0 (Nat.zero_le _)]; exact hch.1
  · rw [eq0 K le_rfl]; exact hch.2.1
  · rw [eq0 (k + 1) hk, eq0 k hk.le]; exact hch.2.2 k hk

/-- Uniqueness, wire form: passing wire values are the canonical ones, `rr j = sR (j+1)` for `j + 1 < K`. -/
theorem carryChk_unique {b K OFF : ℕ} {c e rr : ℕ → ℕ} (h : ∀ k < K, carryChk b K OFF c e rr k) :
    ∀ j, j + 1 < K → rr j = sR b K OFF c e (j + 1) := by
  intro j hj
  have hch := (schainW_iff b K OFF c e rr).1 h
  have := schain_eq_sR hch (j + 1) hj.le
  unfold RofW at this
  simpa [hj] using this

/-- Range, wire form: passing wire values satisfy `0 < rr j < 2 OFF` for `j + 1 < K`. -/
theorem carryChk_range {b K OFF : ℕ} {c e rr : ℕ → ℕ} (h : ∀ k < K, carryChk b K OFF c e rr k)
    (hc : ∀ k < K, c k ≤ OFF * (2 ^ b - 1)) (he : ∀ k < K, e k ≤ OFF * (2 ^ b - 1))
    (hO : 0 < OFF) : ∀ j, j + 1 < K → 0 < rr j ∧ rr j < 2 * OFF := by
  intro j hj
  have := schain_range ((schainW_iff b K OFF c e rr).1 h) hc he hO (j + 1) hj.le
  unfold RofW at this
  simpa [hj] using this

/-! ## Linear combinations of values (ArithNet chains) -/

/-- Exchanging the position sum with a linear combination over a list of terms. -/
theorem sum_lin {α : Type*} (l : List α) (a : α → ℕ) (f : α → ℕ → ℕ) (b K : ℕ) :
    ∑ k ∈ range K, (l.map fun t => a t * f t k).sum * 2 ^ (b * k) =
      (l.map fun t => a t * ∑ k ∈ range K, f t k * 2 ^ (b * k)).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, sum_add_distrib, ih, mul_sum, mul_assoc]

/-- A linear combination of values `≤ B` is at most (coefficient mass) · `B`. -/
theorem lin_le {α : Type*} (l : List α) (a f : α → ℕ) {B : ℕ} (h : ∀ t ∈ l, f t ≤ B) :
    (l.map fun t => a t * f t).sum ≤ (l.map a).sum * B := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons, add_mul]
    have h1 := Nat.mul_le_mul_left (a t) (h t (by simp))
    have h2 := ih fun u hu => h u (by simp [hu])
    omega

/-- Mass `≤ 32` and values `≤ 2^(J+1)` give digits `≤ OFF (2^b − 1)` for `OFF = 2^(J+6)`, `1 ≤ b`. -/
theorem mass_le_OFF {J b d m : ℕ} (hb : 1 ≤ b) (hm : m ≤ 32) (hd : d ≤ m * 2 ^ (J + 1)) :
    d ≤ 2 ^ (J + 6) * (2 ^ b - 1) := by
  have h1 : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have h2 : m * 2 ^ (J + 1) ≤ 32 * 2 ^ (J + 1) := Nat.mul_le_mul_right _ hm
  have h3 : 32 * 2 ^ (J + 1) = 2 ^ (J + 6) := by rw [show J + 6 = (J + 1) + 5 by omega, pow_add]; ring
  have h4 : 2 ^ (J + 6) * 1 ≤ 2 ^ (J + 6) * (2 ^ b - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Carries in `(0, 2 OFF)` fit the wire width `W' = J + 8` (with room: `2 · 2^(J+6) = 2^(J+7)`). -/
theorem two_OFF_eq (J : ℕ) : 2 * 2 ^ (J + 6) = 2 ^ (J + 7) := by rw [pow_succ]; ring

theorem two_OFF_lt (J : ℕ) : 2 * 2 ^ (J + 6) < 2 ^ (J + 8) := by
  rw [two_OFF_eq]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ## The three-digit form of the first plan -/

/-- A valid signed chain with right digits `c' k + x k` (the §3 shape). -/
def SChainOK (b K OFF : ℕ) (c c' x R : ℕ → ℕ) : Prop :=
  R 0 = OFF ∧ R K = OFF ∧
    ∀ k < K, R (k + 1) * 2 ^ b + c' k + x k + OFF = c k + R k + OFF * 2 ^ b

theorem schainOK_iff_schain (b K OFF : ℕ) (c c' x R : ℕ → ℕ) :
    SChainOK b K OFF c c' x R ↔ SChain b K OFF c (fun k => c' k + x k) R := by
  simp only [SChainOK, SChain, add_assoc]

/-- (I-C), three-digit form. -/
theorem schainOK_iff {b K OFF : ℕ} {c c' x : ℕ → ℕ}
    (hc : ∀ k < K, c k ≤ OFF * (2 ^ b - 1)) (he : ∀ k < K, c' k + x k ≤ OFF * (2 ^ b - 1)) :
    (∃ R, SChainOK b K OFF c c' x R) ↔
      ∑ k ∈ range K, c k * 2 ^ (b * k) = ∑ k ∈ range K, (c' k + x k) * 2 ^ (b * k) := by
  simp only [schainOK_iff_schain]
  exact schain_iff (e := fun k => c' k + x k) hc he

theorem schainOK_unique {b K OFF : ℕ} {c c' x R R' : ℕ → ℕ} (h : SChainOK b K OFF c c' x R)
    (h' : SChainOK b K OFF c c' x R') : ∀ k ≤ K, R k = R' k :=
  schain_unique ((schainOK_iff_schain ..).1 h) ((schainOK_iff_schain ..).1 h')

theorem schainOK_range {b K OFF : ℕ} {c c' x R : ℕ → ℕ} (h : SChainOK b K OFF c c' x R)
    (hc : ∀ k < K, c k ≤ OFF * (2 ^ b - 1)) (he : ∀ k < K, c' k + x k ≤ OFF * (2 ^ b - 1))
    (hO : 0 < OFF) : ∀ k ≤ K, 0 < R k ∧ R k < 2 * OFF :=
  schain_range ((schainOK_iff_schain ..).1 h) (e := fun k => c' k + x k) hc he hO

end EthFollowup.ModP
