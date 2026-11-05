/-
# Representation numbers of integral quadratic forms: definitions and the box bound (R0)

`scratchpad/repnum-plan.md`, §1 and §5.

For `A : Matrix (Fin k) (Fin k) ℤ` the form is `qf A x = x ⬝ᵥ A *ᵥ x` and the representation number
is `repNum A n = #{x ∈ ℤ^k : xᵀ A x = n}` (`Set.ncard`, box-free).

* `cs`: Cauchy–Schwarz for a positive-definite integer matrix (proof adapted from Mathlib's
  `Matrix.PosDef.star_dotProduct_mulVec_mul_le`, which exists only in the newer Mathlib);
* `posDef_sq_le`: the classical algebraic box bound `x_j² ≤ |adj(A)_jj| · Q(x)` (Cauchy–Schwarz
  applied to `y = adj(A) e_j`, using `A · adj(A) = det A • 1` and `det A ≠ 0`);
* `posDef_coercive`: `Coercive A (cQ A)` with `cQ A = Σ_j |adj(A)_jj|`;
* `repNum_eq_card_box`: under `Coercive A c` all solutions lie in `[-(cn), cn]^k`;
* `card_shift`, `shift_bounds`: the shift `u = x + B` (`cn < B`) is a bijection between the solutions
  and the vectors `u ∈ [0, Bx)^k` with `Q(u − B) = n`, all of which lie in `[1, 2B)^k`;
* diagonal forms, Tunnell's ternary forms `tForm` and the test value `tunnellTest`.

Pure Mathlib; compiles in both toolchains. Standard axioms only.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Matrix Finset

/-- The form `xᵀ A x`. -/
def qf {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (x : Fin k → ℤ) : ℤ := x ⬝ᵥ A *ᵥ x

/-- `Σ_j |adj(A)_jj|`: the coercivity constant. -/
def cQ {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) : ℕ := ∑ j, (A.adjugate j j).natAbs

/-- `x_i² ≤ c · Q(x)` for every integer vector. -/
def Coercive {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (c : ℕ) : Prop :=
  ∀ (x : Fin k → ℤ) (i : Fin k), x i ^ 2 ≤ c * qf A x

/-- **The representation number** `#{x ∈ ℤ^k : xᵀ A x = n}`. -/
noncomputable def repNum {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (n : ℕ) : ℕ :=
  Set.ncard {x : Fin k → ℤ | x ⬝ᵥ A *ᵥ x = n}

/-- The solutions in the box `[-(c n), c n]^k`. -/
def sols {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (c n : ℕ) : Finset (Fin k → ℤ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.Icc (-((c * n : ℕ) : ℤ)) ((c * n : ℕ) : ℤ)).filter
    fun x => x ⬝ᵥ A *ᵥ x = n

variable {k : ℕ}

/-! ## Cauchy–Schwarz and the adjugate box bound -/

theorem star_int (x : Fin k → ℤ) : star x = x := funext fun _ => star_trivial _

/-- A positive-definite integer matrix is symmetric as a bilinear form. -/
theorem posDef_symm {A : Matrix (Fin k) (Fin k) ℤ} (hA : A.PosDef) (x y : Fin k → ℤ) :
    x ⬝ᵥ A *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  have hT : Aᵀ = A := by
    have h := hA.isHermitian
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
    exact h
  calc x ⬝ᵥ A *ᵥ y = x ᵥ* A ⬝ᵥ y := dotProduct_mulVec x A y
    _ = y ⬝ᵥ x ᵥ* A := dotProduct_comm _ _
    _ = y ⬝ᵥ Aᵀ *ᵥ x := by rw [mulVec_transpose]
    _ = y ⬝ᵥ A *ᵥ x := by rw [hT]

theorem posDef_qf_nonneg {A : Matrix (Fin k) (Fin k) ℤ} (hA : A.PosDef) (x : Fin k → ℤ) :
    0 ≤ x ⬝ᵥ A *ᵥ x := by
  have h := hA.posSemidef.dotProduct_mulVec_nonneg x
  rwa [star_int] at h

theorem posDef_qf_pos {A : Matrix (Fin k) (Fin k) ℤ} (hA : A.PosDef) {x : Fin k → ℤ}
    (hx : x ≠ 0) : 0 < x ⬝ᵥ A *ᵥ x := by
  have h := hA.dotProduct_mulVec_pos hx
  rwa [star_int] at h

/-- **Cauchy–Schwarz** for a positive-definite integer matrix. -/
theorem cs {A : Matrix (Fin k) (Fin k) ℤ} (hA : A.PosDef) (x y : Fin k → ℤ) :
    (x ⬝ᵥ A *ᵥ y) ^ 2 ≤ (x ⬝ᵥ A *ᵥ x) * (y ⬝ᵥ A *ᵥ y) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have h0 := posDef_qf_nonneg hA ((y ⬝ᵥ A *ᵥ y) • x - (x ⬝ᵥ A *ᵥ y) • y)
  have hpos := posDef_qf_pos hA hy
  simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul] at h0
  rw [posDef_symm hA y x] at h0
  by_contra hlt
  push Not at hlt
  nlinarith

theorem posDef_det_ne_zero {A : Matrix (Fin k) (Fin k) ℤ} (hA : A.PosDef) : A.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have := posDef_qf_pos hA hv
  rw [hAv, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- **The box bound** `x_j² ≤ |adj(A)_jj| · Q(x)`. -/
theorem posDef_sq_le {A : Matrix (Fin k) (Fin k) ℤ} (hA : A.PosDef) (x : Fin k → ℤ) (j : Fin k) :
    x j ^ 2 ≤ ((A.adjugate j j).natAbs : ℤ) * (x ⬝ᵥ A *ᵥ x) := by
  set y : Fin k → ℤ := A.adjugate *ᵥ Pi.single j 1 with hy
  have hAy : A *ᵥ y = A.det • Pi.single j 1 := by
    rw [hy, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
  have h1 : x ⬝ᵥ A *ᵥ y = A.det * x j := by
    rw [hAy, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one]
  have hyj : y j = A.adjugate j j := by
    rw [hy]; simp [mulVec, dotProduct, Pi.single_apply]
  have h2 : y ⬝ᵥ A *ᵥ y = A.det * A.adjugate j j := by
    rw [hAy, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hyj]
  have hcs := cs hA x y
  rw [h1, h2] at hcs
  have hd := posDef_det_ne_zero hA
  have hQ := posDef_qf_nonneg hA x
  rw [Int.natCast_natAbs]
  set d := A.det
  set a := A.adjugate j j
  set Q := x ⬝ᵥ A *ᵥ x
  have hd1 : 1 ≤ |d| := Int.one_le_abs hd
  have hdd : |d| ≤ d ^ 2 := by
    rw [← sq_abs]; nlinarith
  have hle : d * a ≤ |d| * |a| := by
    rw [← abs_mul]; exact le_abs_self _
  by_contra hlt
  push Not at hlt
  have hA0 : 0 ≤ |a| * Q := mul_nonneg (abs_nonneg _) hQ
  have hd2 : 0 < d ^ 2 := by positivity
  have e1 : d ^ 2 * (|a| * Q) < d ^ 2 * x j ^ 2 := mul_lt_mul_of_pos_left hlt hd2
  have e2 : |d| * (|a| * Q) ≤ d ^ 2 * (|a| * Q) := mul_le_mul_of_nonneg_right hdd hA0
  have e3 : d * a * Q ≤ |d| * |a| * Q := mul_le_mul_of_nonneg_right hle hQ
  nlinarith

/-- A positive-definite form is coercive with constant `cQ A`. -/
theorem posDef_coercive {A : Matrix (Fin k) (Fin k) ℤ} (hA : A.PosDef) : Coercive A (cQ A) := by
  intro x i
  have h := posDef_sq_le hA x i
  have hQ := posDef_qf_nonneg hA x
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hQ)
  unfold cQ
  rw [Nat.cast_sum]
  exact Finset.single_le_sum (f := fun j => ((A.adjugate j j).natAbs : ℤ))
    (fun j _ => by positivity) (Finset.mem_univ i)

/-! ## The box -/

theorem mem_box_of_coercive {A : Matrix (Fin k) (Fin k) ℤ} {c n : ℕ} (hc : Coercive A c)
    {x : Fin k → ℤ} (hx : x ⬝ᵥ A *ᵥ x = n) (i : Fin k) :
    -((c * n : ℕ) : ℤ) ≤ x i ∧ x i ≤ ((c * n : ℕ) : ℤ) := by
  have h1 : ((x i).natAbs : ℤ) ≤ x i ^ 2 := Int.natAbs_le_self_sq _
  have h2 := hc x i
  unfold qf at h2
  rw [hx] at h2
  have h4 : ((x i).natAbs : ℤ) ≤ ((c * n : ℕ) : ℤ) := by rw [Nat.cast_mul]; linarith
  have h3 : |x i| ≤ ((c * n : ℕ) : ℤ) := by rw [Int.abs_eq_natAbs]; exact h4
  exact abs_le.mp h3

theorem repNum_eq_card_box {A : Matrix (Fin k) (Fin k) ℤ} {c : ℕ} (hc : Coercive A c) (n : ℕ) :
    repNum A n = (sols A c n).card := by
  unfold repNum
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, sols, coe_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  exact ⟨fun hx => ⟨fun i => mem_box_of_coercive hc hx i, hx⟩, fun h => h.2⟩

theorem repNum_zero_of_posDef {A : Matrix (Fin k) (Fin k) ℤ} (hA : A.PosDef) : repNum A 0 = 1 := by
  unfold repNum
  have : {x : Fin k → ℤ | x ⬝ᵥ A *ᵥ x = ((0 : ℕ) : ℤ)} = {0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Nat.cast_zero]
    constructor
    · intro hx
      by_contra h0
      exact (posDef_qf_pos hA h0).ne' hx
    · rintro rfl; simp
  rw [this, Set.ncard_singleton]

theorem repNum_zero_k (A : Matrix (Fin 0) (Fin 0) ℤ) (n : ℕ) :
    repNum A n = if n = 0 then 1 else 0 := by
  unfold repNum
  have h0 : ∀ x : Fin 0 → ℤ, x ⬝ᵥ A *ᵥ x = 0 := fun x => by simp [dotProduct]
  split_ifs with hn
  · subst hn
    have : {x : Fin 0 → ℤ | x ⬝ᵥ A *ᵥ x = ((0 : ℕ) : ℤ)} = Set.univ := by
      ext x; simp
    rw [this, Set.ncard_univ, Nat.card_unique]
  · have : {x : Fin 0 → ℤ | x ⬝ᵥ A *ᵥ x = (n : ℤ)} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, h0 x]
      exact_mod_cast Ne.symm hn
    rw [this, Set.ncard_empty]

/-! ## The shift `u = x + B` onto `[1, 2B)^k` -/

/-- Every shifted solution lies in `[1, 2B)^k`. -/
theorem shift_bounds {A : Matrix (Fin k) (Fin k) ℤ} {c n B : ℕ} (hc : Coercive A c)
    (hB : c * n < B) (u : Fin k → ℕ)
    (hu : (fun i => (u i : ℤ) - B) ⬝ᵥ A *ᵥ (fun i => (u i : ℤ) - B) = n) (i : Fin k) :
    1 ≤ u i ∧ u i < 2 * B := by
  have h := mem_box_of_coercive hc hu i
  push_cast at h
  have hB' : (c : ℤ) * n < B := by exact_mod_cast hB
  constructor
  · have : (1 : ℤ) ≤ u i := by linarith [h.1]
    exact_mod_cast this
  · have : (u i : ℤ) < 2 * B := by linarith [h.2]
    exact_mod_cast this

/-- **The shift bijection.** For `c n < B` and `B + c n < Bx`, `x ↦ x + B` is a bijection between
the solutions `sols A c n` and the `u ∈ [0, Bx)^k` with `Q(u − B) = n`. -/
theorem card_shift {A : Matrix (Fin k) (Fin k) ℤ} {c n B Bx : ℕ} (hc : Coercive A c)
    (hB : c * n < B) (hBx : B + c * n < Bx) :
    ((Fintype.piFinset fun _ : Fin k => Finset.range Bx).filter fun u : Fin k → ℕ =>
        (fun i => (u i : ℤ) - B) ⬝ᵥ A *ᵥ (fun i => (u i : ℤ) - B) = n).card =
      (sols A c n).card := by
  refine Finset.card_bij' (fun u _ => fun i => (u i : ℤ) - B)
    (fun x _ => fun i => (x i + B).toNat) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hu
    simp only [sols, mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
    exact ⟨fun i => mem_box_of_coercive hc hu.2 i, hu.2⟩
  · intro x hx
    simp only [sols, mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hx
    simp only [mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    have hxB : ∀ i, (((x i + B).toNat : ℕ) : ℤ) - B = x i := fun i => by
      have := (hx.1 i).1
      push_cast at this
      rw [Int.toNat_of_nonneg (by linarith)]; ring
    refine ⟨fun i => ?_, ?_⟩
    · have h2 := (hx.1 i).2
      push_cast at h2
      have : (x i + B).toNat < Bx := by
        have : x i + B < Bx := by
          have : ((B + c * n : ℕ) : ℤ) < Bx := by exact_mod_cast hBx
          push_cast at this; linarith
        omega
      exact this
    · have : (fun i => (((x i + B).toNat : ℕ) : ℤ) - B) = x := funext hxB
      rw [this]; exact hx.2
  · intro u _
    funext i
    simp
  · intro x hx
    simp only [sols, mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hx
    funext i
    have := (hx.1 i).1
    push_cast at this
    simp only
    rw [Int.toNat_of_nonneg (by linarith)]; ring

/-- The shift bijection with `B = c n + 1` and any box `Bx ≥ 2B`. -/
theorem card_shift_two {A : Matrix (Fin k) (Fin k) ℤ} {c n Bx : ℕ} (hc : Coercive A c)
    (hBx : 2 * (c * n + 1) ≤ Bx) :
    ((Fintype.piFinset fun _ : Fin k => Finset.range Bx).filter fun u : Fin k → ℕ =>
        (fun i => (u i : ℤ) - ((c * n + 1 : ℕ) : ℤ)) ⬝ᵥ A *ᵥ
          (fun i => (u i : ℤ) - ((c * n + 1 : ℕ) : ℤ)) = n).card =
      (sols A c n).card :=
  card_shift hc (Nat.lt_succ_self _) (by omega)

/-! ## Diagonal forms and Tunnell's ternary forms -/

theorem diag_qf (d x : Fin k → ℤ) : x ⬝ᵥ Matrix.diagonal d *ᵥ x = ∑ i, d i * x i ^ 2 := by
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem repNum_diag (d : Fin k → ℤ) (n : ℕ) :
    repNum (Matrix.diagonal d) n = Set.ncard {x : Fin k → ℤ | ∑ i, d i * x i ^ 2 = n} := by
  unfold repNum
  simp only [diag_qf]

theorem posDef_diagonal_of_pos {d : Fin k → ℤ} (hd : ∀ i, 0 < d i) : (Matrix.diagonal d).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_diagonal d, fun x hx => ?_⟩
  rw [star_int, diag_qf]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  refine Finset.sum_pos' (fun j _ => mul_nonneg (hd j).le (sq_nonneg _)) ⟨i, mem_univ _, ?_⟩
  exact mul_pos (hd i) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi)))

/-- Diagonal forms with all coefficients `≥ 1` are coercive with constant `1`. -/
theorem coercive_diagonal {d : Fin k → ℤ} (hd : ∀ i, 1 ≤ d i) : Coercive (Matrix.diagonal d) 1 := by
  intro x i
  unfold qf
  rw [diag_qf, Nat.cast_one, one_mul]
  calc x i ^ 2 ≤ d i * x i ^ 2 := le_mul_of_one_le_left (sq_nonneg _) (hd i)
    _ ≤ ∑ j, d j * x j ^ 2 :=
      Finset.single_le_sum (f := fun j => d j * x j ^ 2)
        (fun j _ => mul_nonneg (by linarith [hd j]) (sq_nonneg _)) (mem_univ i)

/-- Tunnell's ternary forms `a x² + b y² + c z²`. -/
def tForm (a b c : ℕ) : Matrix (Fin 3) (Fin 3) ℤ := Matrix.diagonal ![(a : ℤ), b, c]

theorem repNum_tForm (a b c n : ℕ) :
    repNum (tForm a b c) n =
      Set.ncard {x : Fin 3 → ℤ | a * x 0 ^ 2 + b * x 1 ^ 2 + c * x 2 ^ 2 = n} := by
  rw [tForm, repNum_diag]
  simp [Fin.sum_univ_three]

theorem tForm_posDef {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (tForm a b c).PosDef := by
  refine posDef_diagonal_of_pos fun i => ?_
  fin_cases i <;> simp <;> omega

/-- Tunnell's test value: `A_n = 2 B_n` (n odd), `C_n = 2 D_n` (n even). -/
noncomputable def tunnellTest (n : ℕ) : Bool :=
  if n % 2 = 1 then decide (repNum (tForm 1 2 8) n = 2 * repNum (tForm 1 2 32) n)
  else decide (repNum (tForm 8 2 16) n = 2 * repNum (tForm 8 2 64) n)

theorem tunnellTest_zero : tunnellTest 0 = false := by
  unfold tunnellTest
  simp only [Nat.zero_mod, zero_ne_one, ↓reduceIte]
  rw [repNum_zero_of_posDef (tForm_posDef (by norm_num) (by norm_num) (by norm_num)),
    repNum_zero_of_posDef (tForm_posDef (by norm_num) (by norm_num) (by norm_num))]
  decide

end EthFollowup.ModP
