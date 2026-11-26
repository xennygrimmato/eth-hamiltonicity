import Mathlib

/-!
# W5, K_{2,3}, and the checkable parts of the hull lemma

Sources: `research/ports/ideas-ports.md` Ad.2; `research/ports/hull/notes.md` §1.

Parties are `Fin 5`: `0,1,2 = v₁,v₂,v₃`, `3,4 = u₁,u₂`.
Supply S = the six wires `u_i v_j`; demand T = `v₁v₂, v₂v₃, v₁v₃, u₁u₂`.
-/

namespace PortsLean.W5

open Real Finset

/-! ## 1. The ratio `6√(ℓ²+h²)/(6ℓ+2h)` -/

/-- `√(9/10)·(6ℓ+2h) ≤ 6√(ℓ²+h²)` whenever `6ℓ+2h ≥ 0`: it is `4(ℓ−3h)² ≥ 0`. -/
theorem ratio_lower (ℓ h : ℝ) (hpos : 0 ≤ 6 * ℓ + 2 * h) :
    √(9 / 10) * (6 * ℓ + 2 * h) ≤ 6 * √(ℓ ^ 2 + h ^ 2) := by
  have lhs0 : 0 ≤ √(9 / 10) * (6 * ℓ + 2 * h) := mul_nonneg (Real.sqrt_nonneg _) hpos
  rw [← Real.sqrt_sq lhs0, show (6 : ℝ) * √(ℓ ^ 2 + h ^ 2) = √(36 * (ℓ ^ 2 + h ^ 2)) by
    rw [Real.sqrt_mul (by norm_num), show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  nlinarith [sq_nonneg (ℓ - 3 * h)]

/-- The minimum: `R = √(9/10)` exactly at `h = ℓ/3`. -/
theorem ratio_at_third (ℓ : ℝ) (hℓ : 0 < ℓ) :
    6 * √(ℓ ^ 2 + (ℓ / 3) ^ 2) / (6 * ℓ + 2 * (ℓ / 3)) = √(9 / 10) := by
  have e : ℓ ^ 2 + (ℓ / 3) ^ 2 = (ℓ / 3) ^ 2 * 10 := by ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), div_eq_iff (by positivity)]
  have : √(9 / 10) = 3 / √10 := by
    rw [Real.sqrt_div (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [this]
  have h10 : (0 : ℝ) < √10 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring

/-- And it is a strict minimum: `R(h) > √(9/10)` for `h ≠ ℓ/3`. -/
theorem ratio_strict (ℓ h : ℝ) (hpos : 0 < 6 * ℓ + 2 * h) (hne : h ≠ ℓ / 3) :
    √(9 / 10) < 6 * √(ℓ ^ 2 + h ^ 2) / (6 * ℓ + 2 * h) := by
  rw [lt_div_iff₀ hpos]
  have lhs0 : 0 ≤ √(9 / 10) * (6 * ℓ + 2 * h) := mul_nonneg (Real.sqrt_nonneg _) hpos.le
  rw [← Real.sqrt_sq lhs0, show (6 : ℝ) * √(ℓ ^ 2 + h ^ 2) = √(36 * (ℓ ^ 2 + h ^ 2)) by
    rw [Real.sqrt_mul (by norm_num), show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_lt_sqrt (sq_nonneg _)
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have : 0 < (ℓ - 3 * h) ^ 2 := by
    apply pow_pos_of_ne_zero' ; intro h0; apply hne; linarith
  nlinarith

/-! ## 2. The five-point metric W5 (ℓ = 3, h = 1, i.e. h = ℓ/3) -/

def isV (i : Fin 5) : Prop := i.val < 3

instance (i : Fin 5) : Decidable (isV i) := by unfold isV; infer_instance

/-- W5(3,1): `|v_iv_j| = 6`, `|v_iu_k| = √10`, `|u₁u₂| = 2`. -/
noncomputable def w5 (i j : Fin 5) : ℝ :=
  if i = j then 0 else if isV i ∧ isV j then 6 else if isV i ∨ isV j then √10 else 2

/-- The demand and supply indicator. -/
def demand (i j : Fin 5) : Bool := i < j ∧ ((isV i ∧ isV j) ∨ (¬ isV i ∧ ¬ isV j))
def supply (i j : Fin 5) : Bool := i < j ∧ ¬ ((isV i ∧ isV j) ∨ (¬ isV i ∧ ¬ isV j))

def sumT (d : Fin 5 → Fin 5 → ℝ) : ℝ := ∑ i, ∑ j, if demand i j then d i j else 0
def sumS (d : Fin 5 → Fin 5 → ℝ) : ℝ := ∑ i, ∑ j, if supply i j then d i j else 0

lemma sqrt10_bounds : (3 : ℝ) < √10 ∧ √10 < 10 / 3 := by
  constructor
  · rw [show (3 : ℝ) = √(3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [show (10 / 3 : ℝ) = √((10 / 3) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem w5_sums : sumT w5 = 20 ∧ sumS w5 = 6 * √10 := by
  constructor <;>
  · simp only [sumT, sumS, Fin.sum_univ_five, w5, demand, supply, isV]
    norm_num
    ring

/-- `R(W5) = 6√10/20 = 3/√10 = √(9/10) < 1`. -/
theorem w5_ratio : sumS w5 / sumT w5 = √(9 / 10) ∧ sumS w5 < sumT w5 := by
  obtain ⟨hT, hS⟩ := w5_sums
  refine ⟨?_, ?_⟩
  · rw [hT, hS, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 10)]
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h10 : (0 : ℝ) < √10 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  · rw [hT, hS]; linarith [sqrt10_bounds.2]

/-- W5 is a metric: symmetric, zero on the diagonal, positive off it, triangle inequality. -/
theorem w5_metric :
    (∀ i j, w5 i j = w5 j i) ∧ (∀ i, w5 i i = 0) ∧ (∀ i j, i ≠ j → 0 < w5 i j) ∧
      ∀ i j k, w5 i k ≤ w5 i j + w5 j k := by
  obtain ⟨h3, h4⟩ := sqrt10_bounds
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [w5, isV]
  · intro i; simp [w5]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [w5, isV] <;> linarith
  · intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [w5, isV] <;> linarith

/-! ## 3. Cuts: every cut metric has `Σ_S ≥ Σ_T`; hence W5 is not in the cut cone -/

/-- The cut metric of `A ⊆ Fin 5`, with values in `ℕ`. -/
def cutN (A : Finset (Fin 5)) (i j : Fin 5) : ℕ := if (i ∈ A ↔ j ∈ A) then 0 else 1

def sumTN (A : Finset (Fin 5)) : ℕ := ∑ i, ∑ j, if demand i j then cutN A i j else 0
def sumSN (A : Finset (Fin 5)) : ℕ := ∑ i, ∑ j, if supply i j then cutN A i j else 0

theorem cutN_ineq : ∀ A : Finset (Fin 5), sumTN A ≤ sumSN A := by decide

/-- The cut metric as a real function. -/
def cut (A : Finset (Fin 5)) (i j : Fin 5) : ℝ := (cutN A i j : ℝ)

/-- The separating inequality `Σ_S d − Σ_T d ≥ 0` holds for every cut (all 32 checked). -/
theorem cut_ineq (A : Finset (Fin 5)) : sumT (cut A) ≤ sumS (cut A) := by
  have h := cutN_ineq A
  have eT : sumT (cut A) = (sumTN A : ℝ) := by
    simp only [sumT, sumTN, cut]; push_cast; rfl
  have eS : sumS (cut A) = (sumSN A : ℝ) := by
    simp only [sumS, sumSN, cut]; push_cast; rfl
  rw [eT, eS]; exact_mod_cast h

/-- Hence for every nonnegative combination of cut metrics `Σ_S ≥ Σ_T`, while W5 has `Σ_S < Σ_T`:
**W5 is not a nonnegative combination of cut metrics** (not ℓ₁-embeddable). -/
theorem w5_not_cut_combination (c : Finset (Fin 5) → ℝ) (hc : ∀ A, 0 ≤ c A) :
    w5 ≠ fun i j => ∑ A, c A * cut A i j := by
  intro h
  have lin : ∀ (f : Finset (Fin 5) → Fin 5 → Fin 5 → ℝ) (P : Fin 5 → Fin 5 → Bool),
      (∑ i, ∑ j, if P i j then ∑ A, c A * f A i j else 0) = ∑ A, c A * ∑ i, ∑ j, if P i j then f A i j else 0 := by
    intro f P
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hT : sumT w5 = ∑ A, c A * sumT (cut A) := by rw [h]; exact lin _ _
  have hS : sumS w5 = ∑ A, c A * sumS (cut A) := by rw [h]; exact lin _ _
  have : sumT w5 ≤ sumS w5 := by
    rw [hT, hS]; exact Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (cut_ineq A) (hc A)
  linarith [w5_ratio.2]

/-- The cut `{v₁}` attains ratio 1, so the cut upper bound for the rate is exactly 1. -/
theorem cut_v1 : sumTN {0} = 2 ∧ sumSN {0} = 2 := by decide

/-! ## 4. Flow lower bound 3/4: `3 Σ_T d ≤ 4 Σ_S d` for every pseudometric -/

/-- Routing `v_iv_j` through `u₁,u₂` (half each) and `u₁u₂` through `v₁,v₂,v₃` (a third each). -/
theorem flow_bound (d : Fin 5 → Fin 5 → ℝ) (hsymm : ∀ i j, d i j = d j i)
    (htri : ∀ i j k, d i k ≤ d i j + d j k) : 3 * sumT d ≤ 4 * sumS d := by
  simp only [sumT, sumS, Fin.sum_univ_five, demand, supply, isV]
  norm_num
  have t := htri
  have s := hsymm
  linarith [t 0 3 1, t 0 4 1, t 1 3 2, t 1 4 2, t 0 3 2, t 0 4 2, t 3 0 4, t 3 1 4, t 3 2 4,
    s 3 0, s 3 1, s 3 2, s 4 0, s 4 1, s 4 2, s 1 3, s 2 3, s 2 4, s 1 4]

end PortsLean.W5
