/-
# ArithNet helpers (part of L1, E1): relations, constants, coefficient and carry-digit bounds

Bridge file (anth-build; imports `FermatBridge`), independent of `ArithParams` so that `ArithParams` and later
modules can import it.

* (ArithDesc now uses Compare's `CmpRel` directly, so no relation map is needed);
* constants given by limbs: `limbsVal_eq_ofLimbs`, `limbsVal_lt`, `limbsVal_lt_nB`, `limb_limbsVal`, `pA_limbsVal`;
  operands: `Operand.eval_lt`;
* `stE_le_pred : stE ≤ 2^J − 1` (in range), `stc_le_pow : stc ≤ 2^(J+1)`, `limb_le_pow : limb ≤ 2^(J+1)`;
* `side_le_OFF`: a chain side with coefficient mass `≤ 32` and values `≤ 2^(J+1)` has digit `≤ 2^(J+6) (2^b − 1)`,
  the hypothesis of `SignedCarry.schain_iff` / `carryChk_iff` with `OFF = aOFF n = 2^(J n + 6)`;
* positional sums: `sum_limb_pad` (a variable's limbs padded by zeros to `Kc` positions sum to it),
  `ofLimbs_stc` (= `pipeline_eq_mul`: a product's coefficients sum to the product).

Standard axioms only.
-/
import EthFollowup.Factoring.FermatBridge
import EthFollowup.ModP.ArithDesc
import EthFollowup.ModP.Compare
import EthFollowup.ModP.SignedCarry

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset
open EthFollowup.Factoring

/-! ## Constants given by limbs -/

theorem limbsVal_eq_ofLimbs (b : ℕ) (l : List ℕ) {k : ℕ} (hk : l.length ≤ k) :
    limbsVal b l = ofLimbs b (fun i => l.getD i 0) k := by
  induction k with
  | zero =>
    have : l.length = 0 := by omega
    simp [limbsVal, ofLimbs, this]
  | succ k ih =>
    rcases Nat.lt_or_ge k l.length with h | h
    · have : l.length = k + 1 := by omega
      rw [limbsVal, this]; rfl
    · rw [ofLimbs_succ, ← ih h, List.getD_eq_default _ _ h, zero_mul, add_zero]

theorem getD_lt {b : ℕ} {l : List ℕ} (hl : ∀ y ∈ l, y < 2 ^ b) (i : ℕ) : l.getD i 0 < 2 ^ b := by
  rcases Nat.lt_or_ge i l.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact hl _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]; positivity

theorem limbsVal_lt {b : ℕ} {l : List ℕ} (hl : ∀ y ∈ l, y < 2 ^ b) {k : ℕ} (hk : l.length ≤ k) :
    limbsVal b l < 2 ^ (b * k) := by
  rw [limbsVal_eq_ofLimbs b l hk]; exact ofLimbs_lt b _ k fun i _ => getD_lt hl i

theorem limbsVal_lt_nB {n : ℕ} {l : List ℕ} (hl : ∀ y ∈ l, y < 2 ^ b n) (hk : l.length ≤ ℓ n) :
    limbsVal (b n) l < 2 ^ nB n := by
  have := limbsVal_lt hl hk; rwa [show b n * ℓ n = nB n by unfold nB; ring] at this

theorem limb_limbsVal {b : ℕ} {l : List ℕ} (hl : ∀ y ∈ l, y < 2 ^ b) {k : ℕ} (hk : l.length ≤ k) {i : ℕ}
    (hi : i < k) : limb b (limbsVal b l) i = l.getD i 0 := by
  rw [limbsVal_eq_ofLimbs b l hk]; exact limb_ofLimbs b _ k (fun j _ => getD_lt hl j) i hi

theorem idx_lt_ℓ {n i1 i2 : ℕ} (h1 : i1 < ℓ1 n) (h2 : i2 < ℓ2 n) : i1 + ℓ1 n * i2 < ℓ n := by
  unfold ℓ
  have : ℓ1 n * (i2 + 1) ≤ ℓ1 n * ℓ2 n := Nat.mul_le_mul_left _ h2
  rw [mul_add, mul_one] at this; omega

theorem pA_limbsVal {n : ℕ} {l : List ℕ} (hl : ∀ y ∈ l, y < 2 ^ b n) (hk : l.length ≤ ℓ n) {i1 i2 : ℕ}
    (h1 : i1 < ℓ1 n) (h2 : i2 < ℓ2 n) : pA n (limbsVal (b n) l) i1 i2 = l.getD (i1 + ℓ1 n * i2) 0 :=
  limb_limbsVal hl hk (idx_lt_ℓ h1 h2)

/-- Operand values stay in the box `[0, 2^nB)`. -/
theorem Operand.eval_lt {n nV : ℕ} {w : Operand} (hw : w.OK (b n) (ℓ n) nV) {x : ℕ → ℕ}
    (hx : ∀ v < nV, x v < 2 ^ nB n) : w.eval (b n) x < 2 ^ nB n := by
  cases w with
  | var v => exact hx v hw
  | const l => exact limbsVal_lt_nB hw.2 hw.1

/-! ## Coefficient bounds -/

/-- **`stE_le_pred`**: the convolution coefficients are at most `2^J − 1`. -/
theorem stE_le_pred (n p q : ℕ) {a u : ℕ} (ha : a < L1 n) (hu : u < L2 n) : stE n p q a u ≤ 2 ^ J n - 1 := by
  rw [stE_eq_aconv2 n p q a ha u hu]
  have hB : ∀ (x i1 i2 : ℕ), pA n x i1 i2 ≤ 2 ^ b n - 1 := fun x i1 i2 => by
    have := limb_lt (b n) x (i1 + ℓ1 n * i2); unfold pA; omega
  refine le_trans (Factoring.Fermat.aconv2_le (B := 2 ^ b n - 1) _ _ (hB p) (hB q) a u) ?_
  have h1 : 1 ≤ 2 ^ b n := Nat.one_le_two_pow
  have h2 : (2 ^ b n - 1) * (2 ^ b n - 1) < 2 ^ b n * 2 ^ b n := Nat.mul_lt_mul'' (by omega) (by omega)
  have h3 : ℓ n * ((2 ^ b n - 1) * (2 ^ b n - 1)) < ℓ n * (2 ^ b n * 2 ^ b n) :=
    Nat.mul_lt_mul_of_pos_left h2 (ℓ_pos n)
  have h4 := ℓ_mul_pow_le n
  rw [show 2 * b n = b n + b n by ring, pow_add] at h4
  have : ℓ1 n * ℓ2 n * ((2 ^ b n - 1) * (2 ^ b n - 1)) = ℓ n * ((2 ^ b n - 1) * (2 ^ b n - 1)) := rfl
  omega

theorem two_pow_J_succ (n : ℕ) : 2 * 2 ^ J n = 2 ^ (J n + 1) := by rw [pow_succ]; ring

/-- Product coefficients at a carry position: `stc ≤ 2^(J+1)`. -/
theorem stc_le_pow (n p q k : ℕ) : stc n p q k ≤ 2 ^ (J n + 1) := by
  rw [← two_pow_J_succ]; exact stc_le n p q k

/-- Limbs (variables, constants) at a carry position: `≤ 2^(J+1)`. -/
theorem limb_le_pow (n x i : ℕ) : limb (b n) x i ≤ 2 ^ (J n + 1) := by
  have h1 := limb_lt (b n) x i
  have h2 : 2 ^ b n ≤ 2 ^ (J n + 1) := Nat.pow_le_pow_right (by norm_num) (by have := b_le_J n; omega)
  omega

theorem getD_le_pow {n : ℕ} {l : List ℕ} (hl : ∀ y ∈ l, y < 2 ^ b n) (i : ℕ) : l.getD i 0 ≤ 2 ^ (J n + 1) := by
  have h1 := getD_lt hl i
  have h2 : 2 ^ b n ≤ 2 ^ (J n + 1) := Nat.pow_le_pow_right (by norm_num) (by have := b_le_J n; omega)
  omega

/-- **Carry-digit bound**: a chain side (coefficient mass `≤ 32`, values `≤ 2^(J+1)`) has digit
`≤ 2^(J+6) (2^b − 1)`, the hypothesis of `schain_iff`/`carryChk_iff` with `OFF = 2^(J n + 6)`. -/
theorem side_le_OFF {α : Type*} (n : ℕ) (ts : List α) (coeff val : α → ℕ) (hm : (ts.map coeff).sum ≤ 32)
    (hv : ∀ t ∈ ts, val t ≤ 2 ^ (J n + 1)) :
    (ts.map fun t => coeff t * val t).sum ≤ 2 ^ (J n + 6) * (2 ^ b n - 1) :=
  mass_le_OFF (one_le_b n) hm (lin_le ts coeff val hv)

/-- The ArithDesc form: mass `≤ 32` of a list of `Term`s. -/
theorem side_le_OFF_terms (n : ℕ) (ts : List Term) (val : Term → ℕ) (hm : (ts.map Term.coeff).sum ≤ 32)
    (hv : ∀ t ∈ ts, val t ≤ 2 ^ (J n + 1)) :
    (ts.map fun t => t.coeff * val t).sum ≤ 2 ^ (J n + 6) * (2 ^ b n - 1) :=
  side_le_OFF n ts Term.coeff val hm hv

/-- Offset carries in `(0, 2·2^(J+6))` fit the width `J + 8`. -/
theorem carry_lt_Wa (n r : ℕ) (h : r < 2 * 2 ^ (J n + 6)) : r < 2 ^ (J n + 8) :=
  lt_trans h (two_OFF_lt (J n))

/-! ## Positional sums over the `Kc` carry positions -/

/-- The limbs of `x < 2^nB`, padded with zeros from `ℓ` to `Kc` positions, sum to `x`. -/
theorem sum_limb_pad (n x : ℕ) (hx : x < 2 ^ nB n) :
    ∑ k ∈ range (Kc n), (if k < ℓ n then limb (b n) x k else 0) * 2 ^ (b n * k) = x := by
  have hK : ℓ n ≤ Kc n := by have := ℓ1L2_eq n; unfold Kc; omega
  rw [show Kc n = ℓ n + (Kc n - ℓ n) by omega, sum_range_add]
  have h2 : ∑ k ∈ range (Kc n - ℓ n), (if ℓ n + k < ℓ n then limb (b n) x (ℓ n + k) else 0) *
      2 ^ (b n * (ℓ n + k)) = 0 := sum_eq_zero fun k _ => by simp
  rw [h2, add_zero]
  have h1 : ∑ k ∈ range (ℓ n), (if k < ℓ n then limb (b n) x k else 0) * 2 ^ (b n * k) =
      ofLimbs (b n) (limb (b n) x) (ℓ n) :=
    sum_congr rfl fun k hk => by rw [if_pos (mem_range.1 hk)]
  rw [h1]; exact ofLimbs_limb (b n) x (ℓ n) (by rwa [show b n * ℓ n = nB n by unfold nB; ring])

/-- The same with the limbs written as a function that vanishes from `ℓ` on. -/
theorem sum_pad_eq (n : ℕ) (f : ℕ → ℕ) (hf : ∀ k, ℓ n ≤ k → f k = 0) :
    ∑ k ∈ range (Kc n), f k * 2 ^ (b n * k) = ofLimbs (b n) f (ℓ n) := by
  have hK : ℓ n ≤ Kc n := by have := ℓ1L2_eq n; unfold Kc; omega
  rw [show Kc n = ℓ n + (Kc n - ℓ n) by omega, sum_range_add]
  have h2 : ∑ k ∈ range (Kc n - ℓ n), f (ℓ n + k) * 2 ^ (b n * (ℓ n + k)) = 0 :=
    sum_eq_zero fun k _ => by rw [hf _ (by omega), zero_mul]
  rw [h2, add_zero]; rfl

/-- A product's coefficients sum to the product (`pipeline_eq_mul`). -/
theorem ofLimbs_stc (n p q : ℕ) (hp : p < 2 ^ nB n) (hq : q < 2 ^ nB n) :
    ∑ k ∈ range (Kc n), stc n p q k * 2 ^ (b n * k) = p * q :=
  pipeline_eq_mul n p q hp hq

end EthFollowup.ModP
