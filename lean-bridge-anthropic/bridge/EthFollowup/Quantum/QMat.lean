/-
# Theorem Q1, bridge part 1: the merged gate matrices as lists of residues

The node tables of the circuit network are computed with natural numbers modulo `M = 2^{4b} + 1`
(Kronecker substitution `X ↦ 2^b`, `Circuit.lean` §4). Matrices are lists of residues in row-major
order (`2 × 2`: 4 entries, `4 × 4`: 16 entries).

* `m2mul`, `m4mul`, `k22N`: products and the two-qubit tensor product; `toM2`, `toM4` read a list as a
  matrix over `ZMod M`; `toM2_m2mul`, `toM4_m4mul`, `toM4_k22N`.
* `g1N`, `g2N`: the gate numerators at `X = 2^b` (`toM2_g1N`, `toM4_g2N`); `prodLN` (a run of
  single-qubit gates), `blkEntN` (a block): `toM2_prodLN`, `toM4_blkEntN`.
-/
import EthFollowup.Quantum.Paths

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Polynomial

/-! ### Products of matrices given as lists -/

def m2mul (M : ℕ) (A B : List ℕ) : List ℕ :=
  (List.range 4).map fun e =>
    (A.getD (2 * (e / 2)) 0 * B.getD (e % 2) 0 + A.getD (2 * (e / 2) + 1) 0 * B.getD (2 + e % 2) 0) % M

def m4mul (M : ℕ) (A B : List ℕ) : List ℕ :=
  (List.range 16).map fun e => ((List.range 4).map fun j => A.getD (4 * (e / 4) + j) 0 * B.getD (4 * j + e % 4) 0).sum % M

def k22N (M : ℕ) (A B : List ℕ) : List ℕ :=
  (List.range 16).map fun e => A.getD (2 * (e / 8) + e % 4 / 2) 0 * B.getD (2 * (e / 4 % 2) + e % 2) 0 % M

/-- A list of residues as a `2 × 2` matrix. -/
def toM2 (M : ℕ) (A : List ℕ) : Matrix (Fin 2) (Fin 2) (ZMod M) :=
  Matrix.of fun i j => (A.getD (2 * i.val + j.val) 0 : ZMod M)

/-- A list of residues as a `4 × 4` matrix. -/
def toM4 (M : ℕ) (A : List ℕ) : Matrix (Fin 4) (Fin 4) (ZMod M) :=
  Matrix.of fun i j => (A.getD (4 * i.val + j.val) 0 : ZMod M)

theorem getD_map_range {β : Type*} (f : ℕ → β) {k i : ℕ} (hi : i < k) (d : β) :
    ((List.range k).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem toM2_m2mul (M : ℕ) (A B : List ℕ) : toM2 M (m2mul M A B) = toM2 M A * toM2 M B := by
  ext i j
  simp only [toM2, m2mul, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two]
  rw [getD_map_range _ (by omega)]
  have h1 : (2 * i.val + j.val) / 2 = i.val := by omega
  have h2 : (2 * i.val + j.val) % 2 = j.val := by omega
  rw [h1, h2]
  push_cast
  simp only [ZMod.natCast_mod]
  simp [Fin.val_zero, Fin.val_one]

theorem toM4_m4mul (M : ℕ) (A B : List ℕ) : toM4 M (m4mul M A B) = toM4 M A * toM4 M B := by
  ext i j
  simp only [toM4, m4mul, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four]
  rw [getD_map_range _ (by omega)]
  have h1 : (4 * i.val + j.val) / 4 = i.val := by omega
  have h2 : (4 * i.val + j.val) % 4 = j.val := by omega
  rw [h1, h2, ZMod.natCast_mod]
  simp [List.range_succ, Fin.val_zero, Fin.val_one, Fin.val_two]
  ring_nf

theorem toM4_k22N (M : ℕ) (A B : List ℕ) : toM4 M (k22N M A B) = k22 (toM2 M A) (toM2 M B) := by
  ext i j
  simp only [toM4, k22N, k22, toM2, Matrix.of_apply, hiF, loF]
  rw [getD_map_range _ (by omega), ZMod.natCast_mod]
  push_cast
  congr 3 <;> omega

/-! ### The gate numerators at `X = 2^b` -/

/-- `-x` modulo `M`. -/
def negN (M x : ℕ) : ℕ := (M - x % M) % M

theorem cast_negN (M x : ℕ) [NeZero M] : (negN M x : ZMod M) = -(x : ZMod M) := by
  unfold negN
  rw [ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt _ (NeZero.pos M)).le, ZMod.natCast_self, ZMod.natCast_mod,
    zero_sub]

/-- Single-qubit numerators (codes `0 … 6`; identity otherwise), `z₁ = 2^b`, `z₂ = 2^{2b}`,
`z₃ = 2^{3b}` modulo `M`. -/
def g1N (M z₁ z₂ z₃ : ℕ) (u : ℕ) : List ℕ :=
  if u = 0 then [1, 1, 1, negN M 1] else if u = 1 then [1, 0, 0, z₁]
  else if u = 2 then [1, 0, 0, negN M z₃] else if u = 3 then [1, 0, 0, z₂]
  else if u = 4 then [1, 0, 0, negN M z₂] else if u = 5 then [0, 1, 1, 0]
  else if u = 6 then [1, 0, 0, negN M 1] else [1, 0, 0, 1]

/-- The diagonal `4 × 4` matrix with last entry `d`. -/
def diag4 (d : ℕ) : List ℕ := [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, d]

/-- Two-qubit numerators (codes `7 … 11`; identity otherwise). -/
def g2N (M z₁ z₂ z₃ : ℕ) (u : ℕ) : List ℕ :=
  if u = 7 then [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0]
  else if u = 8 then diag4 (negN M 1) else if u = 9 then diag4 z₂
  else if u = 10 then [1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
  else if u = 11 then [(z₁ + negN M z₃) % M, 0, 0, 0, 0, (z₁ + negN M z₃) % M, 0, 0, 0, 0, 1, 1, 0, 0, 1, negN M 1]
  else diag4 1

/-- The residues of `2^b, 2^{2b}, 2^{3b}`. -/
structure ZP (M b z₁ z₂ z₃ : ℕ) : Prop where
  h1 : (z₁ : ZMod M) = 2 ^ b
  h2 : (z₂ : ZMod M) = (2 ^ b) ^ 2
  h3 : (z₃ : ZMod M) = (2 ^ b) ^ 3

/-- The numerator interpretation in `ZMod M` at `X = 2^b`. -/
noncomputable def IM (M b : ℕ) : Interp (ZMod M) := numI.map (evR ((2 : ZMod M) ^ b))

theorem toM2_g1N {M b z₁ z₂ z₃ : ℕ} [NeZero M] (hz : ZP M b z₁ z₂ z₃) (u : ℕ) :
    toM2 M (g1N M z₁ z₂ z₃ u) = (IM M b).γ u := by
  have c1 := cast_negN M 1
  have c2 := cast_negN M z₂
  have c3 := cast_negN M z₃
  ext i j
  simp only [IM, Interp.map, numI, Matrix.map_apply, toM2, Matrix.of_apply]
  rcases u with _ | _ | _ | _ | _ | _ | _ | u <;> fin_cases i <;> fin_cases j <;>
    simp [g1N, num1, c1, c2, c3, hz.h1, hz.h2, hz.h3, Matrix.one_apply]

theorem toM4_g2N {M b z₁ z₂ z₃ : ℕ} [NeZero M] (hz : ZP M b z₁ z₂ z₃) (u : ℕ) :
    toM4 M (g2N M z₁ z₂ z₃ u) = (IM M b).Γ u := by
  have c1 := cast_negN M 1
  have c2 := cast_negN M z₂
  have c3 := cast_negN M z₃
  ext i j
  simp only [IM, Interp.map, numI, Matrix.map_apply, toM4, Matrix.of_apply]
  by_cases h7 : u = 7
  · subst h7; fin_cases i <;> fin_cases j <;> simp [g2N, num2]
  by_cases h8 : u = 8
  · subst h8; fin_cases i <;> fin_cases j <;> simp [g2N, num2, diag4, c1]
  by_cases h9 : u = 9
  · subst h9; fin_cases i <;> fin_cases j <;> simp [g2N, num2, diag4, hz.h2]
  by_cases h10 : u = 10
  · subst h10; fin_cases i <;> fin_cases j <;> simp [g2N, num2]
  by_cases h11 : u = 11
  · subst h11; fin_cases i <;> fin_cases j <;> simp [g2N, num2, c1, c3, hz.h1, hz.h3, ZMod.natCast_mod] <;> ring
  have e : num2 u = 1 := by
    rcases u with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | u <;> simp_all [num2]
  rw [e]
  fin_cases i <;> fin_cases j <;> simp [g2N, h7, h8, h9, h10, h11, diag4, Matrix.one_apply]

/-- A run of single-qubit gates. -/
def prodLN (M z₁ z₂ z₃ : ℕ) (r : List ℕ) : List ℕ :=
  r.foldl (fun A u => m2mul M (g1N M z₁ z₂ z₃ u) A) [1, 0, 0, 1]

/-- The 16 residues of a block. -/
def blkEntN (M z₁ z₂ z₃ : ℕ) (blk : Blk) : List ℕ :=
  m4mul M (g2N M z₁ z₂ z₃ blk.1) (k22N M (prodLN M z₁ z₂ z₃ blk.2.2.2.1) (prodLN M z₁ z₂ z₃ blk.2.2.2.2))

theorem toM2_one (M : ℕ) : toM2 M [1, 0, 0, 1] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toM2, Matrix.one_apply]

theorem toM2_prodLN {M b z₁ z₂ z₃ : ℕ} [NeZero M] (hz : ZP M b z₁ z₂ z₃) (r : List ℕ) :
    toM2 M (prodLN M z₁ z₂ z₃ r) = prodL (IM M b) r := by
  unfold prodLN prodL
  suffices h : ∀ (A : List ℕ) (B : Matrix (Fin 2) (Fin 2) (ZMod M)), toM2 M A = B →
      toM2 M (r.foldl (fun A u => m2mul M (g1N M z₁ z₂ z₃ u) A) A) = r.foldl (fun A u => (IM M b).γ u * A) B from
    h _ _ (toM2_one M)
  induction r with
  | nil => intro A B h; exact h
  | cons u r ih =>
    intro A B h
    simp only [List.foldl_cons]
    exact ih _ _ (by rw [toM2_m2mul, toM2_g1N hz, h])

theorem toM4_blkEntN {M b z₁ z₂ z₃ : ℕ} [NeZero M] (hz : ZP M b z₁ z₂ z₃) (blk : Blk) :
    toM4 M (blkEntN M z₁ z₂ z₃ blk) = blkM (IM M b) blk := by
  rw [blkEntN, toM4_m4mul, toM4_g2N hz, toM4_k22N, toM2_prodLN hz, toM2_prodLN hz]; rfl

end EthFollowup.Quantum
