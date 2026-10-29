/-
# Clifford+T circuits: semantics, exact amplitudes, the merged path sum (math layer of Theorem Q1)

`research/quantum-circuits.md` §2–3. Mathlib only; compiles in both toolchains.

## What a reader must trust (§1)
* `ω = exp(iπ/4)`; the single-qubit gates `G1.mat` (H, T, T†, S, S†, X, Z) and two-qubit gates `G2.mat`
  (CNOT, CZ, CS, SWAP, CH; basis index `2·b₁ + b₂`, `b₁` the first qubit, the control) as complex
  matrices written out entry by entry;
* `Gate n` (a gate and the qubits it acts on, two distinct qubits for a two-qubit gate), `Gate.op`
  (the gate on `n` qubits: the gate matrix on its qubits, identity on the others),
  `circuitOp C` (the product `U_m ⋯ U_1`, first gate applied first) and
  `amplitude C x y = ⟨y|C|x⟩ = circuitOp C y x`;
* `hcount C`: the number of `H` and `CH` gates (the exponent `k` of `√2` in the denominator).

## The rest (proved)
* §2 Gate codes `(u, q₁, q₂) : ℕ × ℕ × ℕ` and their matrices over any commutative ring (`Interp`,
  `opC`, `cmat`); the numerators `num1`, `num2` over `ℤ[X]` (`X ↦ ω`); `amplitude_eq`:
  `⟨y|C|x⟩ = (1/√2)^k · P(ω)` with `P = cmat num (codes C) y x ∈ ℤ[X]`.
* §3 The ℓ¹ norm of integer polynomials, `l1_cmat_le`: `‖P‖₁ ≤ (2·2ⁿ)^m` (m = number of gates).
* §4 Kronecker substitution modulo `M_b = 2^{4b} + 1` (`X ↦ 2^b`, a ring map since
  `2^{4b} ≡ -1`): the reduced coefficients `red P j` (`P(ω) = Σ_{j<4} red P j · ωʲ`), and the decoder
  `decodeK` (`decodeK_eq`: from `P(2^b) mod M_b` it returns `red P` when `‖P‖₁ < 2^{b-1}`).
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Bits

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Matrix Finset Polynomial

/-! ## §1 Semantics -/

/-- `ω = e^{iπ/4}`. -/
noncomputable def ω : ℂ := Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- `1/√2`. -/
noncomputable def r2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The single-qubit gates. -/
inductive G1 | H | T | Tdg | S | Sdg | X | Z
  deriving DecidableEq

/-- The two-qubit gates (the first qubit is the control of CNOT, CZ, CS, CH). -/
inductive G2 | CNOT | CZ | CS | SWAP | CH
  deriving DecidableEq

/-- The matrices of the single-qubit gates (`T† = diag(1, ω̄)`, `S = diag(1, i)`). -/
noncomputable def G1.mat : G1 → Matrix (Fin 2) (Fin 2) ℂ
  | .H => !![r2, r2; r2, -r2]
  | .T => !![1, 0; 0, ω]
  | .Tdg => !![1, 0; 0, star ω]
  | .S => !![1, 0; 0, Complex.I]
  | .Sdg => !![1, 0; 0, -Complex.I]
  | .X => !![0, 1; 1, 0]
  | .Z => !![1, 0; 0, -1]

/-- The matrices of the two-qubit gates, basis `|b₁b₂⟩` at index `2·b₁ + b₂`. -/
noncomputable def G2.mat : G2 → Matrix (Fin 4) (Fin 4) ℂ
  | .CNOT => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | .CZ => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]
  | .CS => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, Complex.I]
  | .SWAP => !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]
  | .CH => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, r2, r2; 0, 0, r2, -r2]

/-- A gate of a circuit on `n` qubits. -/
inductive Gate (n : ℕ)
  | one (u : G1) (q : Fin n)
  | two (u : G2) (q₁ q₂ : Fin n) (h : q₁ ≠ q₂)

/-- Computational basis states of `n` qubits. -/
abbrev Basis (n : ℕ) := Fin n → Bool

/-- The index of a bit. -/
def bit (b : Bool) : Fin 2 := if b then 1 else 0

/-- The index `2·b₁ + b₂`. -/
def bit2 (b₁ b₂ : Bool) : Fin 4 := ⟨2 * b₁.toNat + b₂.toNat, by cases b₁ <;> cases b₂ <;> decide⟩

/-- **A gate on `n` qubits**: `⟨s'|op|s⟩` is the gate entry on its qubits if `s'` and `s` agree on all
other qubits, and `0` otherwise. -/
noncomputable def Gate.op {n : ℕ} : Gate n → Matrix (Basis n) (Basis n) ℂ
  | .one u q => Matrix.of fun s' s =>
      if ∀ p, p ≠ q → s' p = s p then u.mat (bit (s' q)) (bit (s q)) else 0
  | .two u q₁ q₂ _ => Matrix.of fun s' s =>
      if ∀ p, p ≠ q₁ → p ≠ q₂ → s' p = s p then u.mat (bit2 (s' q₁) (s' q₂)) (bit2 (s q₁) (s q₂)) else 0

/-- **The matrix of a circuit**, the first gate of the list applied first: `U_m ⋯ U_2 U_1`. -/
noncomputable def circuitOp {n : ℕ} (C : List (Gate n)) : Matrix (Basis n) (Basis n) ℂ :=
  C.foldl (fun M g => g.op * M) 1

/-- **The amplitude** `⟨y|C|x⟩`. -/
noncomputable def amplitude {n : ℕ} (C : List (Gate n)) (x y : Basis n) : ℂ := circuitOp C y x

/-- The `√2`-exponent of a gate: `1` for `H` and `CH`. -/
def Gate.kappa {n : ℕ} : Gate n → ℕ
  | .one .H _ => 1
  | .two .CH _ _ _ => 1
  | _ => 0

/-- The number of `H` and `CH` gates. -/
def hcount {n : ℕ} (C : List (Gate n)) : ℕ := (C.map Gate.kappa).sum

/-- The number of two-qubit gates. -/
def Gate.isTwo {n : ℕ} : Gate n → Bool
  | .one _ _ => false
  | .two _ _ _ _ => true

def twoCount {n : ℕ} (C : List (Gate n)) : ℕ := (C.filter Gate.isTwo).length

/-! ### Facts about `ω` -/

theorem sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem sqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero]; positivity

theorem ω_eq : ω = ((Real.sqrt 2 : ℝ) : ℂ) / 2 * (1 + Complex.I) := by
  rw [ω, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  push_cast; ring

theorem ω_sq : ω ^ 2 = Complex.I := by
  rw [ω_eq]
  linear_combination (1 / 4 * (1 + Complex.I) ^ 2) * sqrt2_sq + (1 / 2 : ℂ) * Complex.I_sq

theorem ω_four : ω ^ 4 = -1 := by
  rw [show ω ^ 4 = (ω ^ 2) ^ 2 by ring, ω_sq, Complex.I_sq]

theorem ω_sub_cube : ω - ω ^ 3 = ((Real.sqrt 2 : ℝ) : ℂ) := by
  rw [show ω ^ 3 = ω * ω ^ 2 by ring, ω_sq, ω_eq]
  linear_combination (-((Real.sqrt 2 : ℝ) : ℂ) / 2) * Complex.I_sq

theorem star_ω : star ω = -ω ^ 3 := by
  rw [show ω ^ 3 = ω * ω ^ 2 by ring, ω_sq, ω_eq]
  have h : star (((Real.sqrt 2 : ℝ) : ℂ) / 2 * (1 + Complex.I)) =
      ((Real.sqrt 2 : ℝ) : ℂ) / 2 * (1 - Complex.I) := by
    simp only [Complex.star_def, map_mul, map_div₀, Complex.conj_ofReal, map_add, map_one,
      Complex.conj_I, map_ofNat]
    ring
  rw [h]
  linear_combination (((Real.sqrt 2 : ℝ) : ℂ) / 2) * Complex.I_sq

theorem r2_mul_sqrt2 : r2 * ((Real.sqrt 2 : ℝ) : ℂ) = 1 := inv_mul_cancel₀ sqrt2_ne

/-! ## §2 Gate codes and their matrices over a commutative ring -/

/-- A gate code `(u, q₁, q₂)`: `u < 7` a single-qubit gate on `q₁`, `7 ≤ u` a two-qubit gate. -/
abbrev GC := ℕ × ℕ × ℕ

def G1.idx : G1 → ℕ
  | .H => 0 | .T => 1 | .Tdg => 2 | .S => 3 | .Sdg => 4 | .X => 5 | .Z => 6

def G2.idx : G2 → ℕ
  | .CNOT => 7 | .CZ => 8 | .CS => 9 | .SWAP => 10 | .CH => 11

/-- The code of a gate. -/
def Gate.code {n : ℕ} : Gate n → GC
  | .one u q => (u.idx, q.val, q.val)
  | .two u q₁ q₂ _ => (u.idx, q₁.val, q₂.val)

/-- The value of qubit `q` (a number) in a basis state. -/
def vq {n : ℕ} (s : Basis n) (q : ℕ) : Bool := if h : q < n then s ⟨q, h⟩ else false

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A single-qubit matrix on qubit `q`. -/
def op1 (A : Matrix (Fin 2) (Fin 2) R) (q : ℕ) : Matrix (Basis n) (Basis n) R :=
  Matrix.of fun s' s => if ∀ p : Fin n, p.val ≠ q → s' p = s p then A (bit (vq s' q)) (bit (vq s q)) else 0

/-- A two-qubit matrix on qubits `q₁, q₂`. -/
def op2 (A : Matrix (Fin 4) (Fin 4) R) (q₁ q₂ : ℕ) : Matrix (Basis n) (Basis n) R :=
  Matrix.of fun s' s => if ∀ p : Fin n, p.val ≠ q₁ → p.val ≠ q₂ → s' p = s p then
    A (bit2 (vq s' q₁) (vq s' q₂)) (bit2 (vq s q₁) (vq s q₂)) else 0

/-- An interpretation of the gate codes by matrices. -/
structure Interp (R : Type*) [CommRing R] where
  γ : ℕ → Matrix (Fin 2) (Fin 2) R
  Γ : ℕ → Matrix (Fin 4) (Fin 4) R

/-- The matrix of a gate code. -/
def opC (I : Interp R) (c : GC) : Matrix (Basis n) (Basis n) R :=
  if c.1 < 7 then op1 (I.γ c.1) c.2.1 else op2 (I.Γ c.1) c.2.1 c.2.2

/-- The matrix of a list of gate codes, the first applied first. -/
def cmat (I : Interp R) (cs : List GC) : Matrix (Basis n) (Basis n) R :=
  cs.foldl (fun M c => opC I c * M) 1

variable {S : Type*} [CommRing S]

/-- The image of an interpretation under a ring map. -/
def Interp.map (I : Interp R) (f : R →+* S) : Interp S := ⟨fun u => (I.γ u).map f, fun u => (I.Γ u).map f⟩

theorem op1_map (A : Matrix (Fin 2) (Fin 2) R) (q : ℕ) (f : R →+* S) :
    (op1 (n := n) (A.map f) q) = (op1 A q).map f := by
  ext s' s; simp only [op1, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp

theorem op2_map (A : Matrix (Fin 4) (Fin 4) R) (q₁ q₂ : ℕ) (f : R →+* S) :
    (op2 (n := n) (A.map f) q₁ q₂) = (op2 A q₁ q₂).map f := by
  ext s' s; simp only [op2, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp

theorem opC_map (I : Interp R) (f : R →+* S) (c : GC) :
    opC (n := n) (I.map f) c = (opC I c).map f := by
  unfold opC; split_ifs
  · exact op1_map _ _ f
  · exact op2_map _ _ _ f

theorem foldl_cmat_map (I : Interp R) (f : R →+* S) :
    ∀ (cs : List GC) (M : Matrix (Basis n) (Basis n) R),
      cs.foldl (fun M c => opC (I.map f) c * M) (M.map f) = (cs.foldl (fun M c => opC I c * M) M).map f
  | [], _ => rfl
  | c :: cs, M => by
    simp only [List.foldl_cons]
    rw [← foldl_cmat_map I f cs, opC_map, ← Matrix.map_mul]

/-- `cmat` commutes with ring maps. -/
theorem cmat_map (I : Interp R) (f : R →+* S) (cs : List GC) :
    cmat (n := n) (I.map f) cs = (cmat I cs).map f := by
  unfold cmat
  rw [← foldl_cmat_map, Matrix.map_one _ f.map_zero f.map_one]

end Ring

/-! ### The numerators over `ℤ[X]` (`X ↦ ω`) -/

/-- The numerators of the single-qubit gates (`H` has denominator `√2`). -/
noncomputable def num1 : ℕ → Matrix (Fin 2) (Fin 2) ℤ[X]
  | 0 => !![1, 1; 1, -1]
  | 1 => !![1, 0; 0, X]
  | 2 => !![1, 0; 0, -X ^ 3]
  | 3 => !![1, 0; 0, X ^ 2]
  | 4 => !![1, 0; 0, -X ^ 2]
  | 5 => !![0, 1; 1, 0]
  | 6 => !![1, 0; 0, -1]
  | _ => 1

/-- The numerators of the two-qubit gates (`CH` has denominator `√2`; `√2 = ω - ω³`). -/
noncomputable def num2 : ℕ → Matrix (Fin 4) (Fin 4) ℤ[X]
  | 7 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | 8 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]
  | 9 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, X ^ 2]
  | 10 => !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]
  | 11 => !![X - X ^ 3, 0, 0, 0; 0, X - X ^ 3, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1]
  | _ => 1

/-- The numerator interpretation. -/
noncomputable def numI : Interp ℤ[X] := ⟨num1, num2⟩

/-- Evaluation `X ↦ z` as a ring map `ℤ[X] → S`. -/
noncomputable def evR {S : Type*} [CommRing S] (z : S) : ℤ[X] →+* S := eval₂RingHom (Int.castRingHom S) z

@[simp] theorem evR_X {S : Type*} [CommRing S] (z : S) : evR z X = z := eval₂_X _ _

/-- The single-qubit gates are `(1/√2)^κ` times their numerators at `ω`. -/
theorem G1.mat_eq (u : G1) :
    u.mat = r2 ^ (Gate.kappa (Gate.one u (0 : Fin 1))) • (num1 u.idx).map (evR ω) := by
  have h3 := star_ω
  ext i j
  cases u <;> fin_cases i <;> fin_cases j <;>
    simp [G1.mat, num1, G1.idx, Gate.kappa, Matrix.smul_apply, h3, ω_sq]

/-- The two-qubit gates are `(1/√2)^κ` times their numerators at `ω`. -/
theorem G2.mat_eq (u : G2) {n : ℕ} (q₁ q₂ : Fin n) (h : q₁ ≠ q₂) :
    u.mat = r2 ^ (Gate.kappa (Gate.two u q₁ q₂ h)) • (num2 u.idx).map (evR ω) := by
  have h1 := ω_sub_cube
  have h2 := r2_mul_sqrt2
  ext i j
  cases u <;> fin_cases i <;> fin_cases j <;>
    simp [G2.mat, num2, G2.idx, Gate.kappa, Matrix.smul_apply, h1, h2, ω_sq]

theorem vq_val {n : ℕ} (s : Basis n) (q : Fin n) : vq s q.val = s q := by simp [vq]

theorem Gate.op_eq {n : ℕ} (g : Gate n) :
    g.op = r2 ^ g.kappa • opC (n := n) (numI.map (evR ω)) g.code := by
  cases g with
  | one u q =>
    have hu : u.idx < 7 := by cases u <;> decide
    have e := G1.mat_eq u
    ext s' s
    simp only [Gate.op, opC, Gate.code, hu, ↓reduceIte, op1, Interp.map, numI, Matrix.of_apply,
      Matrix.smul_apply, vq_val, Fin.val_ne_iff]
    have hk : (Gate.one u q).kappa = (Gate.one u (0 : Fin 1)).kappa := by cases u <;> rfl
    rw [hk]
    split_ifs
    · rw [e]; rfl
    · simp
  | two u q₁ q₂ h =>
    have hu : ¬ u.idx < 7 := by cases u <;> decide
    have e := G2.mat_eq u q₁ q₂ h
    ext s' s
    simp only [Gate.op, opC, Gate.code, hu, ↓reduceIte, op2, Interp.map, numI, Matrix.of_apply,
      Matrix.smul_apply, vq_val, Fin.val_ne_iff]
    split_ifs
    · rw [e]; rfl
    · simp

/-- The gate codes of a circuit. -/
def codes {n : ℕ} (C : List (Gate n)) : List GC := C.map Gate.code

theorem foldl_op_eq {n : ℕ} : ∀ (C : List (Gate n)) (c : ℂ) (M : Matrix (Basis n) (Basis n) ℂ),
    C.foldl (fun M g => g.op * M) (c • M) =
      (c * r2 ^ hcount C) • (codes C).foldl (fun M g => opC (numI.map (evR ω)) g * M) M
  | [], c, M => by simp [hcount, codes]
  | g :: C, c, M => by
    simp only [List.foldl_cons, codes, List.map_cons]
    rw [Gate.op_eq g, smul_mul_smul_comm, foldl_op_eq C]
    simp only [hcount, List.map_cons, List.sum_cons, pow_add, codes]
    congr 1; ring

/-- The polynomial `P = ⟨y| cmat num |x⟩ ∈ ℤ[X]` of a circuit. -/
noncomputable def ampPoly {n : ℕ} (C : List (Gate n)) (x y : Basis n) : ℤ[X] := cmat numI (codes C) y x

/-- **`⟨y|C|x⟩ = (1/√2)^k · P(ω)`** with `k` the number of `H` and `CH` gates. -/
theorem amplitude_eq {n : ℕ} (C : List (Gate n)) (x y : Basis n) :
    amplitude C x y = r2 ^ hcount C * evR ω (ampPoly C x y) := by
  have h := foldl_op_eq C 1 1
  rw [one_smul, one_mul] at h
  unfold amplitude circuitOp ampPoly
  rw [h, Matrix.smul_apply, smul_eq_mul]
  congr 1
  have := cmat_map (n := n) numI (evR ω) (codes C)
  unfold cmat at this
  rw [this]; rfl

/-! ## §3 The ℓ¹ norm of integer polynomials -/

/-- `‖p‖₁ = Σ |coefficients|`. -/
def l1 (p : ℤ[X]) : ℕ := p.support.sum fun i => (p.coeff i).natAbs

theorem l1_eq_sum (p : ℤ[X]) {s : Finset ℕ} (hs : p.support ⊆ s) :
    l1 p = s.sum fun i => (p.coeff i).natAbs := by
  unfold l1
  refine Finset.sum_subset hs fun i _ hi => ?_
  rw [Polynomial.notMem_support_iff.1 hi]; rfl

theorem l1_add (p q : ℤ[X]) : l1 (p + q) ≤ l1 p + l1 q := by
  rw [l1_eq_sum (p + q) (s := p.support ∪ q.support) Polynomial.support_add,
    l1_eq_sum p (s := p.support ∪ q.support) Finset.subset_union_left,
    l1_eq_sum q (s := p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Polynomial.coeff_add]; exact Int.natAbs_add_le _ _

theorem l1_zero : l1 0 = 0 := by simp [l1]

theorem l1_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) : l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (l1_add _ _).trans (Nat.add_le_add_left ih _)

theorem l1_monomial (k : ℕ) (c : ℤ) : l1 (monomial k c) = c.natAbs := by
  by_cases hc : c = 0
  · subst hc; simp [l1]
  · rw [l1_eq_sum _ (s := {k}) (by rw [Polynomial.support_monomial k hc])]
    simp

theorem l1_neg (p : ℤ[X]) : l1 (-p) = l1 p := by
  unfold l1; rw [Polynomial.support_neg]; simp

theorem l1_mul (p q : ℤ[X]) : l1 (p * q) ≤ l1 p * l1 q := by
  have hp : p * q = ∑ i ∈ p.support, ∑ j ∈ q.support, monomial (i + j) (p.coeff i * q.coeff j) := by
    conv_lhs => rw [Polynomial.as_sum_support p, Polynomial.as_sum_support q]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.monomial_mul_monomial]
  rw [hp]
  refine (l1_sum _ _).trans ?_
  unfold l1
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (l1_sum _ _).trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [l1_monomial, Int.natAbs_mul]

theorem natAbs_coeff_le (p : ℤ[X]) (i : ℕ) : (p.coeff i).natAbs ≤ l1 p := by
  by_cases hi : i ∈ p.support
  · exact Finset.single_le_sum (f := fun i => (p.coeff i).natAbs) (fun _ _ => Nat.zero_le _) hi
  · rw [Polynomial.notMem_support_iff.1 hi]; exact Nat.zero_le _

theorem l1_one : l1 1 = 1 := by
  rw [show (1 : ℤ[X]) = monomial 0 1 from rfl, l1_monomial]; rfl

theorem l1_X_pow (k : ℕ) : l1 (X ^ k : ℤ[X]) = 1 := by
  rw [← Polynomial.monomial_one_right_eq_X_pow, l1_monomial]; rfl

theorem l1_X : l1 (X : ℤ[X]) = 1 := by rw [← pow_one X, l1_X_pow]

/-! ### The entries of a circuit have small ℓ¹ norm -/

section Bound

variable {n : ℕ}

/-- All entries of a matrix have ℓ¹ norm `≤ α`. -/
def EntBd {ι κ : Type*} (A : Matrix ι κ ℤ[X]) (α : ℕ) : Prop := ∀ i j, l1 (A i j) ≤ α

theorem entBd_mul {ι κ μ : Type*} [Fintype κ] {A : Matrix ι κ ℤ[X]} {B : Matrix κ μ ℤ[X]} {α β : ℕ}
    (hA : EntBd A α) (hB : EntBd B β) : EntBd (A * B) (Fintype.card κ * (α * β)) := by
  intro i j
  rw [Matrix.mul_apply]
  refine (l1_sum _ _).trans ?_
  rw [← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_le_sum fun k _ => (l1_mul _ _).trans (Nat.mul_le_mul (hA i k) (hB k j))

theorem entBd_num1 (u : ℕ) : EntBd (num1 u) 1 := by
  intro i j
  rcases u with _ | _ | _ | _ | _ | _ | _ | u <;> fin_cases i <;> fin_cases j <;>
    simp [num1, l1_one, l1_zero, l1_neg, l1_X_pow, l1_X]

theorem l1_sqrt2 : l1 (X - X ^ 3 : ℤ[X]) ≤ 2 := by
  rw [sub_eq_add_neg]
  refine (l1_add _ _).trans ?_
  rw [l1_neg, l1_X_pow, show (X : ℤ[X]) = X ^ 1 from (pow_one X).symm, l1_X_pow]

theorem entBd_num2 (u : ℕ) : EntBd (num2 u) 2 := by
  have h := l1_sqrt2
  intro i j
  rcases u with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | u <;> fin_cases i <;> fin_cases j <;>
    simp [num2, l1_one, l1_zero, l1_neg, l1_X_pow, l1_X, h]

theorem entBd_op1 {A : Matrix (Fin 2) (Fin 2) ℤ[X]} {α : ℕ} (h : EntBd A α) (q : ℕ) :
    EntBd (op1 (n := n) A q) α := by
  intro s' s; simp only [op1, Matrix.of_apply]; split_ifs
  · exact h _ _
  · rw [l1_zero]; exact Nat.zero_le _

theorem entBd_op2 {A : Matrix (Fin 4) (Fin 4) ℤ[X]} {α : ℕ} (h : EntBd A α) (q₁ q₂ : ℕ) :
    EntBd (op2 (n := n) A q₁ q₂) α := by
  intro s' s; simp only [op2, Matrix.of_apply]; split_ifs
  · exact h _ _
  · rw [l1_zero]; exact Nat.zero_le _

theorem entBd_opC (c : GC) : EntBd (opC (n := n) numI c) 2 := by
  unfold opC; split_ifs
  · exact fun i j => (entBd_op1 (entBd_num1 c.1) c.2.1 i j).trans (by norm_num)
  · exact entBd_op2 (entBd_num2 c.1) _ _

theorem entBd_one : EntBd (1 : Matrix (Basis n) (Basis n) ℤ[X]) 1 := by
  intro i j; rw [Matrix.one_apply]; split_ifs
  · rw [l1_one]
  · rw [l1_zero]; exact Nat.zero_le _

theorem entBd_mono {ι κ : Type*} {A : Matrix ι κ ℤ[X]} {α β : ℕ} (h : EntBd A α) (hab : α ≤ β) :
    EntBd A β := fun i j => (h i j).trans hab

theorem entBd_foldl : ∀ (cs : List GC) (M : Matrix (Basis n) (Basis n) ℤ[X]) (α : ℕ), EntBd M α →
    EntBd (cs.foldl (fun M c => opC numI c * M) M) ((2 * 2 ^ n) ^ cs.length * α)
  | [], M, α, h => by simpa using h
  | c :: cs, M, α, h => by
    simp only [List.foldl_cons, List.length_cons]
    have h1 : EntBd (opC numI c * M) ((2 * 2 ^ n) * α) := by
      have := entBd_mul (entBd_opC (n := n) c) h
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
      exact entBd_mono this (by rw [show 2 ^ n * (2 * α) = 2 * 2 ^ n * α by ring])
    have := entBd_foldl cs _ _ h1
    exact entBd_mono this (by rw [pow_succ]; ring_nf; exact le_rfl)

/-- **The coefficient bound**: `‖⟨y|cmat num|x⟩‖₁ ≤ (2·2ⁿ)^m`. -/
theorem l1_cmat_le (cs : List GC) (x y : Basis n) :
    l1 (cmat (n := n) numI cs y x) ≤ (2 * 2 ^ n) ^ cs.length := by
  have := entBd_foldl cs 1 1 entBd_one y x
  rwa [mul_one] at this

end Bound

/-! ## §4 Kronecker substitution modulo `2^{4b} + 1` -/

/-- The modulus `M_b = 2^{4b} + 1`. -/
def Mb (b : ℕ) : ℕ := 2 ^ (4 * b) + 1

/-- The reduced coefficients: `P mod (X⁴ + 1) = Σ_{j<4} red P j · Xʲ`. -/
noncomputable def red (P : ℤ[X]) (j : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), if i % 4 = j then (-1) ^ (i / 4) * P.coeff i else 0

theorem pow_reduce {S : Type*} [CommRing S] {z : S} (hz : z ^ 4 = -1) (i : ℕ) :
    z ^ i = (-1) ^ (i / 4) * z ^ (i % 4) := by
  conv_lhs => rw [← Nat.div_add_mod i 4, pow_add, pow_mul, hz]

theorem sum_red {S : Type*} [CommRing S] {z : S} (hz : z ^ 4 = -1) (P : ℤ[X]) :
    evR z P = ∑ j ∈ Finset.range 4, (red P j : S) * z ^ j := by
  show eval₂ (Int.castRingHom S) z P = _
  rw [Polynomial.eval₂_eq_sum_range]
  unfold red
  simp only [Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (i % 4)]
  · rw [if_pos rfl, pow_reduce hz i, Int.coe_castRingHom]; push_cast; ring
  · intro j _ hj; rw [if_neg (Ne.symm hj)]; simp
  · intro h; exact absurd (Finset.mem_range.2 (Nat.mod_lt i (by norm_num))) h

theorem abs_red_le (P : ℤ[X]) (j : ℕ) : (red P j).natAbs ≤ l1 P := by
  unfold red
  refine (Int.natAbs_sum_le _ _).trans ?_
  have : ∀ i ∈ Finset.range (P.natDegree + 1),
      (if i % 4 = j then (-1) ^ (i / 4) * P.coeff i else 0 : ℤ).natAbs ≤ (P.coeff i).natAbs := by
    intro i _
    split_ifs
    · simp [Int.natAbs_mul, Int.natAbs_pow]
    · exact Nat.zero_le _
  refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
  exact (l1_eq_sum P (fun i hi => Finset.mem_range.2 (Nat.lt_succ_of_le
    (Polynomial.le_natDegree_of_mem_supp i hi)))).symm

theorem two_pow_four_mb (b : ℕ) : ((2 : ZMod (Mb b)) ^ b) ^ 4 = -1 := by
  have h : ((Mb b : ℕ) : ZMod (Mb b)) = 0 := ZMod.natCast_self _
  have e : ((Mb b : ℕ) : ZMod (Mb b)) = (2 : ZMod (Mb b)) ^ (4 * b) + 1 := by
    unfold Mb; push_cast; rfl
  rw [e] at h
  rw [← pow_mul, mul_comm b 4]; exact eq_neg_of_add_eq_zero_left h

/-- The offset `Σ_{j<4} 2^{b-1}·2^{bj}` that makes the balanced digits non-negative. -/
def offK (b : ℕ) : ℕ := ∑ j ∈ Finset.range 4, 2 ^ (b - 1) * 2 ^ (b * j)

/-- **The decoder**: from the residue `r = Z mod M_b` the four balanced base-`2^b` digits. -/
def decodeK (b r : ℕ) (j : ℕ) : ℤ := ((r + offK b) % Mb b / 2 ^ (b * j) % 2 ^ b : ℕ) - 2 ^ (b - 1)

theorem digits4 (b : ℕ) (d : ℕ → ℕ) (hd : ∀ j, d j < 2 ^ b) (j : ℕ) (hj : j < 4) :
    (∑ i ∈ Finset.range 4, d i * 2 ^ (b * i)) / 2 ^ (b * j) % 2 ^ b = d j := by
  have hb : 0 < 2 ^ b := by positivity
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, pow_zero, mul_one]
  have e1 : 2 ^ (b * 2) = 2 ^ b * 2 ^ b := by rw [mul_two, pow_add]
  have e2 : 2 ^ (b * 3) = 2 ^ b * 2 ^ b * 2 ^ b := by
    rw [show b * 3 = b + b + b by ring, pow_add, pow_add]
  have e0 : 2 ^ (b * 1) = 2 ^ b := by rw [mul_one]
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  · simp only [mul_zero, pow_zero, Nat.div_one, e0, e1, e2]
    rw [show d 0 + d 1 * 2 ^ b + d 2 * (2 ^ b * 2 ^ b) + d 3 * (2 ^ b * 2 ^ b * 2 ^ b) =
      d 0 + 2 ^ b * (d 1 + d 2 * 2 ^ b + d 3 * (2 ^ b * 2 ^ b)) by ring, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (hd 0)
  · simp only [e0, e1, e2]
    rw [show d 0 + d 1 * 2 ^ b + d 2 * (2 ^ b * 2 ^ b) + d 3 * (2 ^ b * 2 ^ b * 2 ^ b) =
      d 0 + 2 ^ b * (d 1 + 2 ^ b * (d 2 + d 3 * 2 ^ b)) by ring, Nat.add_mul_div_left _ _ hb,
      Nat.div_eq_of_lt (hd 0), zero_add, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (hd 1)
  · simp only [e0, e1, e2]
    rw [show d 0 + d 1 * 2 ^ b + d 2 * (2 ^ b * 2 ^ b) + d 3 * (2 ^ b * 2 ^ b * 2 ^ b) =
      (d 0 + d 1 * 2 ^ b) + (2 ^ b * 2 ^ b) * (d 2 + 2 ^ b * d 3) by ring,
      Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt (by nlinarith [hd 0, hd 1]), zero_add, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (hd 2)
  · simp only [e0, e1, e2]
    rw [show d 0 + d 1 * 2 ^ b + d 2 * (2 ^ b * 2 ^ b) + d 3 * (2 ^ b * 2 ^ b * 2 ^ b) =
      (d 0 + d 1 * 2 ^ b + d 2 * (2 ^ b * 2 ^ b)) + (2 ^ b * 2 ^ b * 2 ^ b) * d 3 by ring,
      Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt (by nlinarith [hd 0, hd 1, hd 2]), zero_add]
    exact Nat.mod_eq_of_lt (hd 3)

/-- **Decoding.** If `r < M_b`, `r ≡ Σ_{j<4} a_j 2^{bj}` modulo `M_b` and every `|a_j| < 2^{b-1}`,
then `decodeK b r j = a_j`. -/
theorem decodeK_eq {b : ℕ} (hb : 1 ≤ b) (a : ℕ → ℤ) (ha : ∀ j, (a j).natAbs < 2 ^ (b - 1)) {r : ℕ}
    (hr : r < Mb b) (hcong : (r : ZMod (Mb b)) = ∑ j ∈ Finset.range 4, (a j : ZMod (Mb b)) * ((2 : ZMod (Mb b)) ^ b) ^ j)
    (j : ℕ) (hj : j < 4) : decodeK b r j = a j := by
  have hb2 : (2 : ℕ) ^ b = 2 * 2 ^ (b - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hc : ((2 : ℤ) ^ (b - 1)) = ((2 ^ (b - 1) : ℕ) : ℤ) := by push_cast; rfl
  -- the non-negative digits
  set d : ℕ → ℕ := fun j => ((a j + 2 ^ (b - 1) : ℤ)).toNat with hd
  have hd0 : ∀ j, ((d j : ℕ) : ℤ) = a j + 2 ^ (b - 1) := fun j => by
    have := ha j
    simp only [hd]; rw [Int.toNat_of_nonneg (by rw [hc]; omega)]
  have hdlt : ∀ j, d j < 2 ^ b := fun j => by
    have h1 := hd0 j; have h2 := ha j
    have : ((d j : ℕ) : ℤ) < ((2 ^ b : ℕ) : ℤ) := by
      rw [h1, hb2, hc, Nat.cast_mul, Nat.cast_ofNat]; omega
    exact_mod_cast this
  set N := ∑ i ∈ Finset.range 4, d i * 2 ^ (b * i) with hN
  have hNlt : N < Mb b := by
    have : N < 2 ^ (4 * b) := by
      have h4 : ∀ i ∈ Finset.range 4, d i * 2 ^ (b * i) ≤ (2 ^ b - 1) * 2 ^ (b * i) := fun i _ =>
        Nat.mul_le_mul_right _ (by have := hdlt i; omega)
      refine lt_of_le_of_lt (Finset.sum_le_sum h4) ?_
      have hb0 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, pow_zero, mul_one]
      have e1 : 2 ^ (b * 2) = 2 ^ b * 2 ^ b := by rw [mul_two, pow_add]
      have e2 : 2 ^ (b * 3) = 2 ^ b * 2 ^ b * 2 ^ b := by
        rw [show b * 3 = b + b + b by ring, pow_add, pow_add]
      have e3 : 2 ^ (4 * b) = 2 ^ b * 2 ^ b * 2 ^ b * 2 ^ b := by
        rw [show 4 * b = b + b + b + b by ring, pow_add, pow_add, pow_add]
      rw [e1, e2, e3]
      set t := 2 ^ b
      zify [hb0]
      nlinarith
    unfold Mb; omega
  -- `N` is the residue of `r + offK b`
  have hNcast : ((N : ℕ) : ℤ) = ∑ i ∈ Finset.range 4, (a i + 2 ^ (b - 1)) * 2 ^ (b * i) := by
    rw [hN]; push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd0 i]
  have hres : (r + offK b) % Mb b = N := by
    rw [← Nat.mod_eq_of_lt hNlt]
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).1
    push_cast
    rw [hcong]
    have hN' : ((N : ℕ) : ZMod (Mb b)) = ∑ i ∈ Finset.range 4,
        ((a i : ZMod (Mb b)) + 2 ^ (b - 1)) * 2 ^ (b * i) := by
      have := congrArg (fun z : ℤ => (z : ZMod (Mb b))) hNcast
      push_cast at this
      exact this
    rw [hN']
    unfold offK
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul]; ring
  unfold decodeK
  rw [hres, hN, digits4 b d hdlt j hj, hd0 j]
  ring

/-! ## §5 The merged path sum

A forward scan over the gate codes merges every run of single-qubit gates into the next two-qubit
gate on its qubit (`pend`: the gates since the last two-qubit gate, per qubit), and records for
every two-qubit gate ("block") where its two inputs come from (`Src`: `none` = the input `x`,
`some (t, i)` = output leg `i` of block `t`). The runs after the last two-qubit gate of a qubit are
the "tails". **`cmat_eq_pathSum`**: `⟨s|cmat|x⟩ = Σ_o Π_blocks M_t[o_t, in_t(o)] · Π_q tail_q[s_q, ·]`,
one bit per output leg of each block. -/

/-- Where an input comes from: `none` = the circuit input, `some (t, i)` = output leg `i` of block
`t`. -/
abbrev Src := Option (ℕ × Bool)

/-- A block: `(u, (q₁, q₂), (src₁, src₂), (run₁, run₂))`. -/
abbrev Blk := ℕ × (ℕ × ℕ) × (Src × Src) × (List ℕ × List ℕ)

/-- The scan state: blocks, pending runs per qubit, current source per qubit. -/
abbrev SS := List Blk × (List (List ℕ) × List Src)

/-- One gate of the scan. -/
def scanStep (st : SS) (c : GC) : SS :=
  if c.1 < 7 then (st.1, (st.2.1.set c.2.1 (st.2.1.getD c.2.1 [] ++ [c.1]), st.2.2))
  else (st.1 ++ [(c.1, (c.2.1, c.2.2), (st.2.2.getD c.2.1 none, st.2.2.getD c.2.2 none),
      (st.2.1.getD c.2.1 [], st.2.1.getD c.2.2 []))],
    ((st.2.1.set c.2.1 []).set c.2.2 [],
      (st.2.2.set c.2.1 (some (st.1.length, false))).set c.2.2 (some (st.1.length, true))))

def scanInit (n : ℕ) : SS := ([], (List.replicate n [], List.replicate n none))

/-- **The scan** of a list of gate codes on `n` qubits. -/
def scan (n : ℕ) (cs : List GC) : SS := cs.foldl scanStep (scanInit n)

section PathSum

variable {R : Type*} [CommRing R] (I : Interp R) {n : ℕ}

/-- The product of a run of single-qubit gates, the first applied first. -/
def prodL (r : List ℕ) : Matrix (Fin 2) (Fin 2) R := r.foldl (fun A u => I.γ u * A) 1

def hiF (i : Fin 4) : Fin 2 := ⟨i.val / 2, by omega⟩
def loF (i : Fin 4) : Fin 2 := ⟨i.val % 2, by omega⟩

/-- `A ⊗ B` on two qubits (index `2·b₁ + b₂`). -/
def k22 (A B : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j => A (hiF i) (hiF j) * B (loF i) (loF j)

/-- The merged matrix of a block: the gate after the two runs. -/
def blkM (blk : Blk) : Matrix (Fin 4) (Fin 4) R := I.Γ blk.1 * k22 (prodL I blk.2.2.2.1) (prodL I blk.2.2.2.2)

/-- The output legs of block `t`. -/
def rd {k : ℕ} (o : Fin k → Bool × Bool) (t : ℕ) : Bool × Bool := if h : t < k then o ⟨t, h⟩ else (false, false)

/-- The bit carried by a source. -/
def sv {k : ℕ} (x : Basis n) (o : Fin k → Bool × Bool) (q : ℕ) : Src → Bool
  | none => vq x q
  | some (t, i) => if i then (rd o t).2 else (rd o t).1

/-- The factor of block `t`. -/
def blockF {k : ℕ} (x : Basis n) (o : Fin k → Bool × Bool) (t : ℕ) (blk : Blk) : R :=
  blkM I blk (bit2 (rd o t).1 (rd o t).2) (bit2 (sv x o blk.2.1.1 blk.2.2.1.1) (sv x o blk.2.1.2 blk.2.2.1.2))

/-- The product of the block factors, blocks numbered from `t`. -/
def Wp {k : ℕ} (x : Basis n) (o : Fin k → Bool × Bool) : ℕ → List Blk → R
  | _, [] => 1
  | t, blk :: bs => blockF I x o t blk * Wp x o (t + 1) bs

/-- The tail factor of qubit `q` at the output `s`. -/
def tailF {k : ℕ} (x : Basis n) (o : Fin k → Bool × Bool) (st : SS) (s : Basis n) (q : Fin n) : R :=
  prodL I (st.2.1.getD q.val []) (bit (s q)) (bit (sv x o q.val (st.2.2.getD q.val none)))

/-- **The merged path sum** of a scan state with `k` blocks, at the output `s`. -/
def pathSum (x : Basis n) (st : SS) (k : ℕ) (s : Basis n) : R :=
  ∑ o : Fin k → Bool × Bool, Wp I x o 0 st.1 * ∏ q : Fin n, tailF I x o st s q

/-- Sources below `k`. -/
def SrcLt (k : ℕ) (s : Src) : Prop := ∀ t i, s = some (t, i) → t < k

/-- The invariant of the scan. -/
structure Good (n k : ℕ) (st : SS) : Prop where
  len : st.1.length = k
  plen : st.2.1.length = n
  clen : st.2.2.length = n
  bsrc : ∀ blk ∈ st.1, SrcLt k blk.2.2.1.1 ∧ SrcLt k blk.2.2.1.2
  csrc : ∀ q, SrcLt k (st.2.2.getD q none)

/-- A valid gate code on `n` qubits. -/
def ValidC (n : ℕ) (c : GC) : Prop := c.2.1 < n ∧ c.2.2 < n ∧ (7 ≤ c.1 → c.2.1 ≠ c.2.2)

/-! ### Sums over basis states -/

theorem bit_true : bit true = 1 := rfl
theorem bit_false : bit false = 0 := rfl

theorem sum_bool_mul (A B : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    ∑ c : Bool, A i (bit c) * B (bit c) j = (A * B) i j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_bool, bit_true, bit_false, add_comm]

theorem filter_agree1 (s : Basis n) (q : Fin n) :
    (Finset.univ.filter fun s' : Basis n => ∀ p : Fin n, p.val ≠ q.val → s p = s' p) =
      (Finset.univ : Finset Bool).image (Function.update s q) := by
  ext s'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    refine ⟨s' q, funext fun p => ?_⟩
    by_cases hp : p = q
    · subst hp; simp
    · rw [Function.update_of_ne hp]; exact h p (Fin.val_ne_iff.2 hp)
  · rintro ⟨c, rfl⟩ p hp
    exact (Function.update_of_ne (fun h => hp (congrArg Fin.val h)) _ _).symm

theorem op1_mul_apply (A : Matrix (Fin 2) (Fin 2) R) (q : Fin n) (M : Matrix (Basis n) (Basis n) R)
    (s x : Basis n) :
    (op1 (n := n) A q.val * M : Matrix (Basis n) (Basis n) R) s x = ∑ c : Bool, A (bit (s q)) (bit c) * M (Function.update s q c) x := by
  rw [Matrix.mul_apply]
  simp only [op1, Matrix.of_apply, vq_val, ite_mul, zero_mul]
  rw [← Finset.sum_filter, filter_agree1, Finset.sum_image (fun c _ c' _ h => by
    simpa using congrFun h q)]
  simp

theorem filter_agree2 (s : Basis n) (q₁ q₂ : Fin n) (hq : q₁ ≠ q₂) :
    (Finset.univ.filter fun s' : Basis n => ∀ p : Fin n, p.val ≠ q₁.val → p.val ≠ q₂.val → s p = s' p) =
      (Finset.univ : Finset (Bool × Bool)).image fun c => Function.update (Function.update s q₁ c.1) q₂ c.2 := by
  ext s'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.exists]
  constructor
  · intro h
    refine ⟨s' q₁, s' q₂, funext fun p => ?_⟩
    by_cases hp2 : p = q₂
    · subst hp2; simp
    · rw [Function.update_of_ne hp2]
      by_cases hp1 : p = q₁
      · subst hp1; simp
      · rw [Function.update_of_ne hp1]
        exact h p (Fin.val_ne_iff.2 hp1) (Fin.val_ne_iff.2 hp2)
  · rintro ⟨c₁, c₂, rfl⟩ p hp1 hp2
    rw [Function.update_of_ne (fun h => hp2 (congrArg Fin.val h)),
      Function.update_of_ne (fun h => hp1 (congrArg Fin.val h))]

theorem op2_mul_apply (A : Matrix (Fin 4) (Fin 4) R) (q₁ q₂ : Fin n) (hq : q₁ ≠ q₂)
    (M : Matrix (Basis n) (Basis n) R) (s x : Basis n) :
    (op2 (n := n) A q₁.val q₂.val * M : Matrix (Basis n) (Basis n) R) s x = ∑ c : Bool × Bool, A (bit2 (s q₁) (s q₂)) (bit2 c.1 c.2) *
      M (Function.update (Function.update s q₁ c.1) q₂ c.2) x := by
  rw [Matrix.mul_apply]
  simp only [op2, Matrix.of_apply, vq_val, ite_mul, zero_mul]
  rw [← Finset.sum_filter, filter_agree2 s q₁ q₂ hq, Finset.sum_image (fun c _ c' _ h => by
    have h1 := congrFun h q₁
    have h2 := congrFun h q₂
    simp only [Function.update_self, Function.update_of_ne hq] at h1 h2
    exact Prod.ext h1 h2)]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [Function.update_of_ne hq, Function.update_of_ne hq.symm]

theorem sum_k22 (U : Matrix (Fin 4) (Fin 4) R) (C D : Matrix (Fin 2) (Fin 2) R) (i : Fin 4)
    (j₁ j₂ : Bool) :
    ∑ c : Bool × Bool, U i (bit2 c.1 c.2) * (C (bit c.1) (bit j₁) * D (bit c.2) (bit j₂)) =
      (U * k22 C D) i (bit2 j₁ j₂) := by
  rw [Matrix.mul_apply, Fin.sum_univ_four, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
    Fintype.sum_bool]
  cases j₁ <;> cases j₂ <;> simp [k22, bit2, bit, hiF, loF] <;> ring

/-! ### Assignments of one more block -/

/-- `(Fin k → β) × β ≃ (Fin (k+1) → β)` by `Fin.snoc`. -/
def snocE (k : ℕ) (β : Type*) : (Fin k → β) × β ≃ (Fin (k + 1) → β) where
  toFun p := Fin.snoc (α := fun _ => β) p.1 p.2
  invFun o := (Fin.init o, o (Fin.last k))
  left_inv p := by simp
  right_inv o := by simp

theorem sum_snoc {k : ℕ} {β M : Type*} [Fintype β] [AddCommMonoid M] (f : (Fin (k + 1) → β) → M) :
    ∑ o, f o = ∑ o : Fin k → β, ∑ c : β, f (Fin.snoc (α := fun _ => β) o c) := by
  rw [← Fintype.sum_prod_type' (f := fun o c => f (Fin.snoc (α := fun _ => β) o c))]
  exact (Fintype.sum_equiv (snocE k β) _ _ fun p => rfl).symm

theorem rd_snoc_lt {k : ℕ} (o : Fin k → Bool × Bool) (c : Bool × Bool) {t : ℕ} (ht : t < k) :
    rd (Fin.snoc (α := fun _ => Bool × Bool) o c) t = rd o t := by
  have : (⟨t, by omega⟩ : Fin (k + 1)) = Fin.castSucc ⟨t, ht⟩ := rfl
  simp only [rd, dif_pos ht, dif_pos (show t < k + 1 by omega), this, Fin.snoc_castSucc]

theorem rd_snoc_last {k : ℕ} (o : Fin k → Bool × Bool) (c : Bool × Bool) :
    rd (Fin.snoc (α := fun _ => Bool × Bool) o c) k = c := by
  have : (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k := rfl
  simp only [rd, dif_pos (show k < k + 1 by omega), this, Fin.snoc_last]

theorem sv_congr {k k' : ℕ} (x : Basis n) {o : Fin k → Bool × Bool} {o' : Fin k' → Bool × Bool}
    (h : ∀ t < k, rd o' t = rd o t) (q : ℕ) {s : Src} (hs : SrcLt k s) : sv x o' q s = sv x o q s := by
  rcases s with _ | ⟨t, i⟩
  · rfl
  · simp only [sv, h t (hs t i rfl)]

theorem Wp_congr {k k' : ℕ} (x : Basis n) {o : Fin k → Bool × Bool} {o' : Fin k' → Bool × Bool}
    (h : ∀ t < k, rd o' t = rd o t) :
    ∀ (bs : List Blk) (t : ℕ), t + bs.length ≤ k → (∀ blk ∈ bs, SrcLt k blk.2.2.1.1 ∧ SrcLt k blk.2.2.1.2) →
      Wp I x o' t bs = Wp I x o t bs
  | [], _, _, _ => rfl
  | blk :: bs, t, hl, hb => by
    simp only [List.length_cons] at hl
    have hb0 := hb blk List.mem_cons_self
    simp only [Wp, blockF, h t (by omega), sv_congr x h _ hb0.1, sv_congr x h _ hb0.2]
    rw [Wp_congr x h bs (t + 1) (by omega) fun b hb' => hb b (List.mem_cons_of_mem _ hb')]

theorem Wp_append {k : ℕ} (x : Basis n) (o : Fin k → Bool × Bool) :
    ∀ (bs : List Blk) (t : ℕ) (blk : Blk), Wp I x o t (bs ++ [blk]) = Wp I x o t bs * blockF I x o (t + bs.length) blk
  | [], t, blk => by simp [Wp]
  | b :: bs, t, blk => by
    simp only [List.cons_append, Wp, List.length_cons]
    rw [Wp_append x o bs (t + 1) blk, mul_assoc, show t + 1 + bs.length = t + (bs.length + 1) by ring]

/-! ### The steps of the scan -/

theorem prodL_append (r : List ℕ) (u : ℕ) : prodL I (r ++ [u]) = I.γ u * prodL I r := by
  simp [prodL, List.foldl_append]

theorem getD_set_eq {α : Type*} (l : List α) (i : ℕ) (a d : α) (hi : i < l.length) : (l.set i a).getD i d = a := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_set_ne {α : Type*} (l : List α) {i j : ℕ} (a d : α) (h : i ≠ j) : (l.set i a).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem getD_set_cases {α : Type*} (l : List α) (i j : ℕ) (a d : α) :
    (l.set i a).getD j d = a ∨ (l.set i a).getD j d = l.getD j d := by
  by_cases h : i = j
  · subst h
    by_cases hi : i < l.length
    · exact Or.inl (getD_set_eq _ _ _ _ hi)
    · right
      simp [List.getD_eq_getElem?_getD, List.getElem?_set, hi,
        List.getElem?_eq_none (show l.length ≤ i by omega)]
  · exact Or.inr (getD_set_ne _ _ _ h)

theorem bit_inj {a b : Bool} : bit a = bit b ↔ a = b := by
  cases a <;> cases b <;> simp [bit]

theorem one_bit (a b : Bool) : (1 : Matrix (Fin 2) (Fin 2) R) (bit a) (bit b) = if a = b then 1 else 0 := by
  cases a <;> cases b <;> simp [bit]

theorem step_one (x : Basis n) {k : ℕ} {st : SS} (hg : Good n k st) (u : ℕ) (hu : u < 7) (q : Fin n)
    (M : Matrix (Basis n) (Basis n) R) (hM : ∀ s, M s x = pathSum I x st k s) (s : Basis n) :
    (opC (n := n) I (u, q.val, q.val) * M : Matrix (Basis n) (Basis n) R) s x =
      pathSum I x (scanStep st (u, q.val, q.val)) k s := by
  have hq : q.val < st.2.1.length := by rw [hg.plen]; exact q.2
  simp only [opC, hu, ↓reduceIte]
  rw [op1_mul_apply]
  simp only [hM, pathSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hL : ∀ c : Bool, I.γ u (bit (s q)) (bit c) *
      (Wp I x o 0 st.1 * ∏ p, tailF I x o st (Function.update s q c) p) =
      Wp I x o 0 st.1 * (∏ p ∈ {q}ᶜ, tailF I x o st s p) * (I.γ u (bit (s q)) (bit c) *
        prodL I (st.2.1.getD q.val []) (bit c) (bit (sv x o q.val (st.2.2.getD q.val none)))) := by
    intro c
    rw [Fintype.prod_eq_mul_prod_compl q]
    have hrest : ∏ p ∈ {q}ᶜ, tailF I x o st (Function.update s q c) p = ∏ p ∈ {q}ᶜ, tailF I x o st s p :=
      Finset.prod_congr rfl fun p hp => by
        have : p ≠ q := by simpa using hp
        simp only [tailF, Function.update_of_ne this]
    rw [hrest]
    simp only [tailF, Function.update_self]
    ring
  rw [Finset.sum_congr rfl fun c _ => hL c, ← Finset.mul_sum, sum_bool_mul]
  simp only [scanStep, hu, ↓reduceIte]
  rw [Fintype.prod_eq_mul_prod_compl q]
  have hrest' : ∏ p ∈ {q}ᶜ, tailF I x o (st.1, (st.2.1.set q.val (st.2.1.getD q.val [] ++ [u]), st.2.2)) s p =
      ∏ p ∈ {q}ᶜ, tailF I x o st s p := Finset.prod_congr rfl fun p hp => by
    have : p.val ≠ q.val := by simpa [Fin.val_ne_iff] using hp
    simp only [tailF, getD_set_ne _ _ _ (Ne.symm this)]
  rw [hrest']
  simp only [tailF, getD_set_eq _ _ _ _ hq, prodL_append]
  ring

theorem good_one {k : ℕ} {st : SS} (hg : Good n k st) (u : ℕ) (hu : u < 7) (q : ℕ) :
    Good n k (scanStep st (u, q, q)) := by
  simp only [scanStep, hu, ↓reduceIte]
  exact ⟨hg.len, by simp [hg.plen], hg.clen, hg.bsrc, hg.csrc⟩

/-- The block made by a two-qubit gate code. -/
def mkBlk (st : SS) (u q₁ q₂ : ℕ) : Blk :=
  (u, (q₁, q₂), (st.2.2.getD q₁ none, st.2.2.getD q₂ none), (st.2.1.getD q₁ [], st.2.1.getD q₂ []))

theorem scanStep_two (st : SS) (u q₁ q₂ : ℕ) (hu : ¬ u < 7) :
    scanStep st (u, q₁, q₂) = (st.1 ++ [mkBlk st u q₁ q₂], ((st.2.1.set q₁ []).set q₂ [],
      (st.2.2.set q₁ (some (st.1.length, false))).set q₂ (some (st.1.length, true)))) := by
  simp [scanStep, hu, mkBlk]

theorem sum_ite_and (a b : Bool) (f : Bool × Bool → R) :
    ∑ c : Bool × Bool, (if a = c.1 ∧ b = c.2 then f c else 0) = f (a, b) := by
  rw [Fintype.sum_eq_single (a, b)]
  · simp
  · intro c hc
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hc (Prod.ext h1.symm h2.symm)

theorem step_two (x : Basis n) {k : ℕ} {st : SS} (hg : Good n k st) (u : ℕ) (hu : ¬ u < 7)
    (q₁ q₂ : Fin n) (hq : q₁ ≠ q₂)
    (M : Matrix (Basis n) (Basis n) R) (hM : ∀ s, M s x = pathSum I x st k s) (s : Basis n) :
    (opC (n := n) I (u, q₁.val, q₂.val) * M : Matrix (Basis n) (Basis n) R) s x =
      pathSum I x (scanStep st (u, q₁.val, q₂.val)) (k + 1) s := by
  have hqv : q₁.val ≠ q₂.val := Fin.val_ne_iff.2 hq
  have hp1 : q₁.val < st.2.1.length := by rw [hg.plen]; exact q₁.2
  have hp2 : q₂.val < st.2.1.length := by rw [hg.plen]; exact q₂.2
  have hc1 : q₁.val < st.2.2.length := by rw [hg.clen]; exact q₁.2
  have hc2 : q₂.val < st.2.2.length := by rw [hg.clen]; exact q₂.2
  have hsplit : ∀ (F : Fin n → R), ∏ p, F p = F q₁ * (F q₂ * ∏ p ∈ (Finset.univ.erase q₁).erase q₂, F p) := by
    intro F
    rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ q₁),
      ← Finset.mul_prod_erase _ F (Finset.mem_erase.2 ⟨hq.symm, Finset.mem_univ q₂⟩)]
  have hmem : ∀ p ∈ (Finset.univ.erase q₁).erase q₂, p ≠ q₁ ∧ p ≠ q₂ := fun p hp => by
    simp only [Finset.mem_erase] at hp; exact ⟨hp.2.1, hp.1⟩
  simp only [opC, hu, ↓reduceIte]
  rw [op2_mul_apply _ _ _ hq]
  simp only [hM, pathSum, Finset.mul_sum]
  rw [Finset.sum_comm, sum_snoc]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hagree : ∀ c, ∀ t < k, rd (Fin.snoc (α := fun _ => Bool × Bool) o c) t = rd o t :=
    fun c t ht => rd_snoc_lt o c ht
  have hL : ∀ c : Bool × Bool, I.Γ u (bit2 (s q₁) (s q₂)) (bit2 c.1 c.2) *
      (Wp I x o 0 st.1 * ∏ p, tailF I x o st (Function.update (Function.update s q₁ c.1) q₂ c.2) p) =
      Wp I x o 0 st.1 * (∏ p ∈ (Finset.univ.erase q₁).erase q₂, tailF I x o st s p) *
        (I.Γ u (bit2 (s q₁) (s q₂)) (bit2 c.1 c.2) *
          (prodL I (st.2.1.getD q₁.val []) (bit c.1) (bit (sv x o q₁.val (st.2.2.getD q₁.val none))) *
           prodL I (st.2.1.getD q₂.val []) (bit c.2) (bit (sv x o q₂.val (st.2.2.getD q₂.val none))))) := by
    intro c
    rw [hsplit]
    have e1 : tailF I x o st (Function.update (Function.update s q₁ c.1) q₂ c.2) q₁ =
        prodL I (st.2.1.getD q₁.val []) (bit c.1) (bit (sv x o q₁.val (st.2.2.getD q₁.val none))) := by
      simp only [tailF, Function.update_of_ne hq, Function.update_self]
    have e2 : tailF I x o st (Function.update (Function.update s q₁ c.1) q₂ c.2) q₂ =
        prodL I (st.2.1.getD q₂.val []) (bit c.2) (bit (sv x o q₂.val (st.2.2.getD q₂.val none))) := by
      simp only [tailF, Function.update_self]
    have e3 : ∏ p ∈ (Finset.univ.erase q₁).erase q₂,
        tailF I x o st (Function.update (Function.update s q₁ c.1) q₂ c.2) p =
        ∏ p ∈ (Finset.univ.erase q₁).erase q₂, tailF I x o st s p :=
      Finset.prod_congr rfl fun p hp => by
        simp only [tailF, Function.update_of_ne (hmem p hp).1, Function.update_of_ne (hmem p hp).2]
    rw [e1, e2, e3]; ring
  have hR : ∀ c : Bool × Bool,
      Wp I x (Fin.snoc (α := fun _ => Bool × Bool) o c) 0 (scanStep st (u, q₁.val, q₂.val)).1 *
        ∏ p, tailF I x (Fin.snoc (α := fun _ => Bool × Bool) o c) (scanStep st (u, q₁.val, q₂.val)) s p =
      Wp I x o 0 st.1 * (∏ p ∈ (Finset.univ.erase q₁).erase q₂, tailF I x o st s p) *
        (if s q₁ = c.1 ∧ s q₂ = c.2 then blkM I (mkBlk st u q₁.val q₂.val) (bit2 c.1 c.2)
          (bit2 (sv x o q₁.val (st.2.2.getD q₁.val none)) (sv x o q₂.val (st.2.2.getD q₂.val none))) else 0) := by
    intro c
    rw [scanStep_two _ _ _ _ hu, Wp_append, Wp_congr I x (hagree c) st.1 0 (by rw [hg.len]; omega) hg.bsrc,
      zero_add, hg.len, hsplit]
    have eB : blockF I x (Fin.snoc (α := fun _ => Bool × Bool) o c) k (mkBlk st u q₁.val q₂.val) =
        blkM I (mkBlk st u q₁.val q₂.val) (bit2 c.1 c.2)
          (bit2 (sv x o q₁.val (st.2.2.getD q₁.val none)) (sv x o q₂.val (st.2.2.getD q₂.val none))) := by
      simp only [blockF, rd_snoc_last, mkBlk, sv_congr x (hagree c) _ (hg.csrc _)]
    have e1 : tailF I x (Fin.snoc (α := fun _ => Bool × Bool) o c) (st.1 ++ [mkBlk st u q₁.val q₂.val],
        ((st.2.1.set q₁.val []).set q₂.val [],
          (st.2.2.set q₁.val (some (k, false))).set q₂.val (some (k, true)))) s q₁ =
        if s q₁ = c.1 then 1 else 0 := by
      simp only [tailF, getD_set_ne _ _ _ (Ne.symm hqv), getD_set_eq _ _ _ _ hp1, getD_set_eq _ _ _ _ hc1,
        prodL, List.foldl_nil, sv, Bool.false_eq_true, ↓reduceIte, rd_snoc_last, one_bit]
    have e2 : tailF I x (Fin.snoc (α := fun _ => Bool × Bool) o c) (st.1 ++ [mkBlk st u q₁.val q₂.val],
        ((st.2.1.set q₁.val []).set q₂.val [],
          (st.2.2.set q₁.val (some (k, false))).set q₂.val (some (k, true)))) s q₂ =
        if s q₂ = c.2 then 1 else 0 := by
      have h1 : q₂.val < (st.2.1.set q₁.val []).length := by simpa using hp2
      have h2 : q₂.val < (st.2.2.set q₁.val (some (k, false))).length := by simpa using hc2
      simp only [tailF, getD_set_eq _ _ _ _ h1, getD_set_eq _ _ _ _ h2,
        prodL, List.foldl_nil, sv, ↓reduceIte, rd_snoc_last, one_bit]
    have e3 : ∏ p ∈ (Finset.univ.erase q₁).erase q₂, tailF I x (Fin.snoc (α := fun _ => Bool × Bool) o c)
        (st.1 ++ [mkBlk st u q₁.val q₂.val], ((st.2.1.set q₁.val []).set q₂.val [],
          (st.2.2.set q₁.val (some (k, false))).set q₂.val (some (k, true)))) s p =
        ∏ p ∈ (Finset.univ.erase q₁).erase q₂, tailF I x o st s p :=
      Finset.prod_congr rfl fun p hp => by
        have h1 : q₁.val ≠ p.val := Fin.val_ne_iff.2 (hmem p hp).1.symm
        have h2 : q₂.val ≠ p.val := Fin.val_ne_iff.2 (hmem p hp).2.symm
        simp only [tailF, getD_set_ne _ _ _ h1, getD_set_ne _ _ _ h2]
        rw [sv_congr x (hagree c) _ (hg.csrc _)]
    rw [eB, e1, e2, e3]
    by_cases h1 : s q₁ = c.1 <;> by_cases h2 : s q₂ = c.2
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]; ring
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]; ring
    · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1)]; ring
    · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.1)]; ring
  rw [Finset.sum_congr rfl fun c _ => hL c, Finset.sum_congr rfl fun c _ => hR c, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_k22, sum_ite_and]
  rfl

theorem good_two {k : ℕ} {st : SS} (hg : Good n k st) (u : ℕ) (hu : ¬ u < 7) (q₁ q₂ : ℕ) :
    Good n (k + 1) (scanStep st (u, q₁, q₂)) := by
  rw [scanStep_two _ _ _ _ hu]
  have mono : ∀ s : Src, SrcLt k s → SrcLt (k + 1) s := fun s h t i hs => (h t i hs).trans (by omega)
  refine ⟨by simp [hg.len], by simp [hg.plen], by simp [hg.clen], ?_, ?_⟩
  · intro blk hb
    rcases List.mem_append.1 hb with hb | hb
    · exact ⟨mono _ (hg.bsrc blk hb).1, mono _ (hg.bsrc blk hb).2⟩
    · rw [List.mem_singleton.1 hb]
      exact ⟨mono _ (hg.csrc _), mono _ (hg.csrc _)⟩
  · intro p
    have hk : SrcLt (k + 1) (some (st.1.length, true)) := fun t i h => by simp [hg.len] at h; omega
    have hk' : SrcLt (k + 1) (some (st.1.length, false)) := fun t i h => by simp [hg.len] at h; omega
    rcases getD_set_cases ((st.2.2.set q₁ (some (st.1.length, false)))) q₂ p (some (st.1.length, true)) none
      with h | h <;> rw [h]
    · exact hk
    · rcases getD_set_cases st.2.2 q₁ p (some (st.1.length, false)) none with h' | h' <;> rw [h']
      · exact hk'
      · exact mono _ (hg.csrc p)

theorem good_init : Good n 0 (scanInit n) :=
  ⟨rfl, by simp [scanInit], by simp [scanInit], by simp [scanInit],
    fun q t i h => by
      simp only [scanInit, List.getD_eq_getElem?_getD, List.getElem?_replicate] at h
      split_ifs at h <;> simp at h⟩

theorem pathSum_init (x s : Basis n) : pathSum I x (scanInit n) 0 s = (1 : Matrix (Basis n) (Basis n) R) s x := by
  have hE : ∀ q : Fin n, (scanInit n).2.1.getD q.val [] = [] := fun q => by
    simp [scanInit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  have hC : ∀ q : Fin n, (scanInit n).2.2.getD q.val none = none := fun q => by
    simp [scanInit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  have h0 : (scanInit n).1 = [] := rfl
  simp only [pathSum, Finset.univ_unique, Finset.sum_singleton, h0, Wp, one_mul, tailF, hE, hC, prodL,
    List.foldl_nil, sv, vq_val, one_bit, Matrix.one_apply]
  by_cases h : s = x
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨q, hq⟩ : ∃ q, s q ≠ x q := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq, bit_inj])

theorem foldl_good (x : Basis n) : ∀ (cs : List GC), (∀ c ∈ cs, ValidC n c) → ∀ (k : ℕ) (st : SS)
    (M : Matrix (Basis n) (Basis n) R), Good n k st → (∀ s, M s x = pathSum I x st k s) →
    ∃ k', Good n k' (cs.foldl scanStep st) ∧
      ∀ s, (cs.foldl (fun M c => opC I c * M) M) s x = pathSum I x (cs.foldl scanStep st) k' s
  | [], _, k, st, M, hg, hM => ⟨k, hg, hM⟩
  | c :: cs, hv, k, st, M, hg, hM => by
    obtain ⟨u, q₁, q₂⟩ := c
    obtain ⟨h1, h2, h3⟩ := hv _ List.mem_cons_self
    have hv' : ∀ c ∈ cs, ValidC n c := fun c hc => hv c (List.mem_cons_of_mem _ hc)
    simp only [List.foldl_cons]
    by_cases hu : u < 7
    · have e : (u, q₁, q₂) = (u, q₁, q₁) ∨ True := Or.inr trivial
      -- single-qubit codes act on `q₁` only
      have hstep : scanStep st (u, q₁, q₂) = scanStep st (u, q₁, q₁) := by simp [scanStep, hu]
      have hop : opC (n := n) I (u, q₁, q₂) = opC I (u, q₁, q₁) := by simp [opC, hu]
      rw [hstep, hop]
      exact foldl_good x cs hv' k _ _ (good_one hg u hu q₁)
        (step_one I x hg u hu ⟨q₁, h1⟩ M hM)
    · exact foldl_good x cs hv' (k + 1) _ _ (good_two hg u hu q₁ q₂)
        (step_two I x hg u hu ⟨q₁, h1⟩ ⟨q₂, h2⟩ (fun h => h3 (by omega) (congrArg Fin.val h)) M hM)

/-- **The merged path sum** (Markov–Shi form, single-qubit runs merged into blocks): for valid gate
codes, `⟨s| cmat I cs |x⟩ = pathSum I x (scan n cs) G s` with `G` the number of blocks. -/
theorem cmat_eq_pathSum (cs : List GC) (hv : ∀ c ∈ cs, ValidC n c) (x s : Basis n) :
    cmat (n := n) I cs s x = pathSum I x (scan n cs) (scan n cs).1.length s := by
  obtain ⟨k', hg, h⟩ := foldl_good I x cs hv 0 (scanInit n) 1 good_init fun s => (pathSum_init I x s).symm
  unfold cmat scan
  rw [h s, hg.len]

theorem good_scan (cs : List GC) (hv : ∀ c ∈ cs, ValidC n c) :
    Good n (scan n cs).1.length (scan n cs) := by
  obtain ⟨k', hg, -⟩ := foldl_good (R := ℤ) ⟨fun _ => 1, fun _ => 1⟩ (fun _ => false) cs hv 0 (scanInit n) 1
    good_init fun s => (pathSum_init _ _ s).symm
  unfold scan; rw [hg.len]; exact hg

end PathSum

/-! ## §7 The input and output words, and decoding the amplitude -/

/-- The four low bits of a number, lowest first. -/
def bits4 (k : ℕ) : List Bool := (List.range 4).map k.testBit

/-- `q` among `n` positions, one-hot. -/
def oneHot (n q : ℕ) : List Bool := (List.range n).map fun p => decide (p = q)

/-- **The word of a gate**: the gate number (`G1.idx`, `G2.idx`) in 4 bits, then its qubits one-hot
(the qubit twice for a single-qubit gate). -/
def gateWord {n : ℕ} : Gate n → List Bool
  | .one u q => bits4 u.idx ++ oneHot n q.val ++ oneHot n q.val
  | .two u q₁ q₂ _ => bits4 u.idx ++ oneHot n q₁.val ++ oneHot n q₂.val

/-- **The input word**: `n` in unary, the bits of `x`, the bits of `y`, then the gates in order. -/
def circCode {n : ℕ} (C : List (Gate n)) (x y : Basis n) : List Bool :=
  List.replicate n true ++ [false] ++ List.ofFn x ++ List.ofFn y ++ C.flatMap gateWord

/-- A natural number, self-delimited: each binary digit (lowest first) as `1d`, then `0`. -/
def natWord (k : ℕ) : List Bool := (Nat.bits k).flatMap (fun b => [true, b]) ++ [false]

/-- An integer: its sign bit (`true` if negative), then its absolute value. -/
def intWord (z : ℤ) : List Bool := decide (z < 0) :: natWord z.natAbs

/-- **The output word** of `(a₀, a₁, a₂, a₃, k)`. -/
def outWord (a : Fin 4 → ℤ) (k : ℕ) : List Bool :=
  intWord (a 0) ++ intWord (a 1) ++ intWord (a 2) ++ intWord (a 3) ++ natWord k

/-- The Kronecker precision `b = (n+1)·m + 2` for `m` gates on `n` qubits. -/
def bK (n m : ℕ) : ℕ := (n + 1) * m + 2

theorem two_pow_le_bK (n m : ℕ) : (2 * 2 ^ n) ^ m < 2 ^ (bK n m - 1) := by
  rw [← pow_succ', ← pow_mul, bK, show (n + 1) * m + 2 - 1 = (n + 1) * m + 1 by omega]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem length_codes {n : ℕ} (C : List (Gate n)) : (codes C).length = C.length := by simp [codes]

/-- **The amplitude from the residue of the Kronecker value.** If `Z ≡ P(2^b)` modulo
`M_b = 2^{4b} + 1` (`P = ampPoly C x y`, `b = bK n |C|`), then `⟨y|C|x⟩ = (Σ_{j<4} a_j ωʲ)/√2^k`
with `a_j = decodeK b (Z mod M_b) j` and `k` the number of `H` and `CH` gates. -/
theorem amplitude_of_residue {n : ℕ} (C : List (Gate n)) (x y : Basis n) (Z : ℤ)
    (hZ : (Z : ZMod (Mb (bK n C.length))) = evR ((2 : ZMod (Mb (bK n C.length))) ^ bK n C.length) (ampPoly C x y)) :
    amplitude C x y = (∑ j : Fin 4, (decodeK (bK n C.length) (Z % Mb (bK n C.length)).toNat j : ℂ) * ω ^ (j : ℕ)) /
      ((Real.sqrt 2 : ℝ) : ℂ) ^ hcount C := by
  set b := bK n C.length with hb
  set P := ampPoly C x y with hP
  have hb1 : 1 ≤ b := by rw [hb, bK]; omega
  have hM : (0 : ℤ) < Mb b := by unfold Mb; positivity
  have hl : l1 P < 2 ^ (b - 1) := by
    have := l1_cmat_le (n := n) (codes C) x y
    rw [length_codes] at this
    exact lt_of_le_of_lt this (two_pow_le_bK n C.length)
  have hdec : ∀ j < 4, decodeK b (Z % Mb b).toNat j = red P j := by
    intro j hj
    refine decodeK_eq hb1 (red P) (fun j => lt_of_le_of_lt (abs_red_le P j) hl) ?_ ?_ j hj
    · have h1 := Int.emod_lt_of_pos Z hM
      have h2 := Int.emod_nonneg Z hM.ne'
      omega
    · have h2 := Int.emod_nonneg Z hM.ne'
      have e : (((Z % Mb b).toNat : ℕ) : ZMod (Mb b)) = (Z : ZMod (Mb b)) := by
        rw [show (((Z % Mb b).toNat : ℕ) : ZMod (Mb b)) = (((Z % Mb b : ℤ)) : ZMod (Mb b)) by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg h2]]
        exact ZMod.intCast_mod Z (Mb b)
      rw [e, hZ, sum_red (two_pow_four_mb b)]
  rw [amplitude_eq, sum_red ω_four, ← Finset.sum_range (fun j => ((decodeK b (Z % Mb b).toNat j : ℤ) : ℂ) * ω ^ j)]
  rw [Finset.sum_congr rfl fun j hj => by rw [← hP, ← hdec j (Finset.mem_range.1 hj)], r2, inv_pow,
    div_eq_inv_mul]

end EthFollowup.Quantum
