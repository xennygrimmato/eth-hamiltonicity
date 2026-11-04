/-
# Arithmetic in the Fermat ring `ZMod (2^J + 1)` (module F1 of the factoring plan, part 1)

Pure Mathlib; compiles in both toolchains (Lean 4.33.1 / 4.34.1).

* §1 Orthogonality of powers of a "half-root" `ω` (`ω^(2^m) = -1`) in any commutative ring, proved by
  induction on `m` (no domain / primitivity theory): `sum_pow_mul_eq_zero`, `orth_half`.
* §2 The data needed by a length-`L` Fourier transform, packaged as `Root R`.
* §3 The Fermat ring `ZMod (2^J+1)`: `two_pow_J`, `two_pow_two_J`, `two_mul_two_pow_inv`,
  `omega_pow_half`, and the root `fermatRoot J m` with `ω = 2^(2J/2^m)`, `L⁻¹ = 2^(2J-m)`.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false

namespace Factoring.Fermat

open Finset

/-! ## §1 Orthogonality for a half-root -/

section Ring
variable {R : Type*} [CommRing R]

/-- Doubling a geometric sum of length `2^m`. -/
theorem geom_two_pow_succ (y : R) (m : ℕ) :
    ∑ t ∈ range (2 ^ (m + 1)), y ^ t = (1 + y ^ (2 ^ m)) * ∑ t ∈ range (2 ^ m), y ^ t := by
  rw [pow_succ, mul_two, sum_range_add, add_mul, one_mul, mul_sum]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  rw [pow_add]

/-- If `ω^(2^m) = -1` and `2^(m+1) ∤ e` then `Σ_{t<2^(m+1)} ω^(e t) = 0`. -/
theorem sum_pow_mul_eq_zero (m : ℕ) :
    ∀ (ω : R) (e : ℕ), ω ^ (2 ^ m) = -1 → ¬ 2 ^ (m + 1) ∣ e →
      ∑ t ∈ range (2 ^ (m + 1)), ω ^ (e * t) = 0 := by
  induction m with
  | zero =>
    intro ω e hω he
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' e
    · exact absurd (Dvd.intro k rfl : 2 ^ (0 + 1) ∣ 2 * k) he
    · simp only [pow_zero, pow_one] at hω
      simp [sum_range_succ, hω, pow_succ, pow_mul]
  | succ m ih =>
    intro ω e hω he
    simp_rw [pow_mul]
    rw [geom_two_pow_succ]
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' e
    · -- e = 2k: use the induction hypothesis for ω² and k
      have hk : ¬ 2 ^ (m + 1) ∣ k := by
        intro h; apply he; rw [pow_succ']; exact Nat.mul_dvd_mul_left 2 h
      have hω2 : (ω ^ 2) ^ (2 ^ m) = -1 := by rw [← pow_mul, ← pow_succ']; exact hω
      have := ih (ω ^ 2) k hω2 hk
      simp_rw [pow_mul] at this
      rw [pow_mul, this, mul_zero]
    · -- e odd: (ω^e)^(2^(m+1)) = -1
      have : (ω ^ (2 * k + 1)) ^ (2 ^ (m + 1)) = -1 := by
        rw [← pow_mul, mul_comm, pow_mul, hω, Odd.neg_one_pow ⟨k, rfl⟩]
      rw [this, add_neg_cancel, zero_mul]

/-- Orthogonality: if `ω^(2^m) = -1`, then `Σ_{t<2^(m+1)} ω^(e t)` is `2^(m+1)` when `2^(m+1) ∣ e`
and `0` otherwise. -/
theorem orth_half (m : ℕ) (ω : R) (hω : ω ^ (2 ^ m) = -1) (e : ℕ) :
    ∑ t ∈ range (2 ^ (m + 1)), ω ^ (e * t) = if 2 ^ (m + 1) ∣ e then ((2 ^ (m + 1) : ℕ) : R) else 0 := by
  split_ifs with h
  · obtain ⟨c, rfl⟩ := h
    have h1 : ω ^ (2 ^ (m + 1)) = 1 := by rw [pow_succ, pow_mul, hω]; norm_num
    have : ∀ t, ω ^ (2 ^ (m + 1) * c * t) = 1 := fun t => by rw [mul_assoc, pow_mul, h1, one_pow]
    simp only [this, sum_const, card_range, nsmul_eq_mul, mul_one]
  · exact sum_pow_mul_eq_zero m ω e hω h

end Ring

/-! ## §2 Root data for a transform of length `L` -/

/-- A length-`L` root of unity `ω` with the orthogonality relations and an inverse of `L`. -/
structure Root (R : Type*) [CommRing R] where
  L : ℕ
  ω : R
  Linv : R
  inv : (L : R) * Linv = 1
  pow_L : ω ^ L = 1
  orth : ∀ e : ℕ, ∑ t ∈ range L, ω ^ (e * t) = if L ∣ e then (L : R) else 0


/-- For `x ∈ (0, 2L)`, `L ∣ x` forces `x = L`. -/
theorem eq_of_dvd_of_lt {L x : ℕ} (h : L ∣ x) (h0 : 0 < x) (h2 : x < 2 * L) : x = L := by
  obtain ⟨c, rfl⟩ := h
  rcases c with _ | _ | c
  · simp at h0
  · simp
  · nlinarith

namespace Root
variable {R : Type*} [CommRing R] (ρ : Root R)

/-- `ω^e = ω^(e % L)`. -/
theorem pow_mod (e : ℕ) : ρ.ω ^ e = ρ.ω ^ (e % ρ.L) := by
  conv_lhs => rw [← Nat.div_add_mod e ρ.L, pow_add, pow_mul, ρ.pow_L, one_pow, one_mul]

/-- The shifted orthogonality relation used by the inverse transform: for `u < L`,
`L⁻¹ Σ_{t<L} ω^((x + (L-u)) t) = [x % L = u]`. -/
theorem orth_shift (x u : ℕ) (hu : u < ρ.L) :
    ρ.Linv * ∑ t ∈ range ρ.L, ρ.ω ^ ((x + (ρ.L - u)) * t) = if x % ρ.L = u then 1 else 0 := by
  rw [ρ.orth]
  have hL : 0 < ρ.L := by omega
  have key : ρ.L ∣ x + (ρ.L - u) ↔ x % ρ.L = u := by
    have hx := Nat.div_add_mod x ρ.L
    have hr := Nat.mod_lt x hL
    have e1 : x + (ρ.L - u) = ρ.L * (x / ρ.L) + (x % ρ.L + (ρ.L - u)) := by omega
    rw [e1, Nat.dvd_add_right (dvd_mul_right _ _)]
    constructor
    · intro h
      have := eq_of_dvd_of_lt h (by omega) (by omega)
      omega
    · intro h; rw [h, Nat.add_sub_cancel' hu.le]
  by_cases h : x % ρ.L = u
  · simp only [key.2 h, h, ↓reduceIte]; rw [mul_comm, ρ.inv]
  · simp only [mt key.1 h, h, ↓reduceIte, mul_zero]

end Root

/-! ## §3 The Fermat ring `ZMod (2^J + 1)` -/

section Fermat
variable (J : ℕ)

/-- `2^J = -1` in `ZMod (2^J+1)`. -/
theorem two_pow_J : (2 : ZMod (2 ^ J + 1)) ^ J = -1 := by
  have h : (((2 ^ J + 1 : ℕ)) : ZMod (2 ^ J + 1)) = 0 := ZMod.natCast_self _
  push_cast at h
  exact eq_neg_of_add_eq_zero_left h

/-- `2^(2J) = 1` in `ZMod (2^J+1)`. -/
theorem two_pow_two_J : (2 : ZMod (2 ^ J + 1)) ^ (2 * J) = 1 := by
  rw [pow_mul', two_pow_J]; norm_num

/-- `2` is a unit with inverse `2^(2J-1)` (for `J ≥ 1`). -/
theorem two_mul_two_pow_inv (hJ : 1 ≤ J) : (2 : ZMod (2 ^ J + 1)) * 2 ^ (2 * J - 1) = 1 := by
  rw [← pow_succ', show 2 * J - 1 + 1 = 2 * J by omega, two_pow_two_J]

/-- `2^m` is a unit with inverse `2^(2J-m)` (for `m ≤ 2J`). -/
theorem two_pow_mul_inv (m : ℕ) (hm : m ≤ 2 * J) :
    (2 : ZMod (2 ^ J + 1)) ^ m * 2 ^ (2 * J - m) = 1 := by
  rw [← pow_add, Nat.add_sub_cancel' hm, two_pow_two_J]

/-- For `L = 2^m` with `m ≥ 1` and `L ∣ 2J`, `ω = 2^(2J/L)` satisfies `ω^(L/2) = -1`. -/
theorem omega_pow_half (m : ℕ) (hm : 1 ≤ m) (hL : 2 ^ m ∣ 2 * J) :
    ((2 : ZMod (2 ^ J + 1)) ^ (2 * J / 2 ^ m)) ^ (2 ^ (m - 1)) = -1 := by
  rw [← pow_mul]
  obtain ⟨d, hd⟩ := hL
  have hpos : 0 < 2 ^ m := by positivity
  have h1 : 2 * J / 2 ^ m = d := by rw [hd]; exact Nat.mul_div_cancel_left d hpos
  have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have h3 : d * 2 ^ (m - 1) = J := by
    have : 2 * J = 2 * (d * 2 ^ (m - 1)) := by rw [hd, h2]; ring
    omega
  rw [h1, h3, two_pow_J]

/-- The Fourier root of the Fermat ring: `L = 2^m`, `ω = 2^(2J/2^m)`, `L⁻¹ = 2^(2J-m)`. -/
def fermatRoot (m : ℕ) (hm : 1 ≤ m) (hL : 2 ^ m ∣ 2 * J) (hJ : 0 < J) : Root (ZMod (2 ^ J + 1)) where
  L := 2 ^ m
  ω := 2 ^ (2 * J / 2 ^ m)
  Linv := 2 ^ (2 * J - m)
  inv := by
    have : m ≤ 2 * J := by
      have h1 := Nat.le_of_dvd (by omega) hL
      have h2 := Nat.lt_two_pow_self (n := m)
      omega
    push_cast
    exact two_pow_mul_inv J m this
  pow_L := by
    have h := omega_pow_half J m hm hL
    have h2 : 2 ^ m = 2 ^ (m - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    have h3 : ∀ x : ZMod (2 ^ J + 1), x ^ 2 ^ m = (x ^ 2 ^ (m - 1)) ^ 2 := fun x => by
      rw [← pow_mul, ← h2]
    show ((2 : ZMod (2 ^ J + 1)) ^ (2 * J / 2 ^ m)) ^ 2 ^ m = 1
    rw [h3, h]; norm_num
  orth := by
    have h := orth_half (m - 1) _ (omega_pow_half J m hm hL)
    have hm' : m - 1 + 1 = m := by omega
    rw [hm'] at h
    exact h

@[simp] theorem fermatRoot_L (m hm hL hJ) : (fermatRoot J m hm hL hJ).L = 2 ^ m := rfl
@[simp] theorem fermatRoot_ω (m hm hL hJ) :
    (fermatRoot J m hm hL hJ).ω = 2 ^ (2 * J / 2 ^ m) := rfl
@[simp] theorem fermatRoot_Linv (m hm hL hJ) :
    (fermatRoot J m hm hL hJ).Linv = 2 ^ (2 * J - m) := rfl

end Fermat

end Factoring.Fermat
