import Mathlib

/-!
# The model (Definition 2.1 of the paper) and the statement

Boolean functions `F₂⁸ → F₂` form the commutative `F₂`-algebra `Fn` under pointwise
operations.  The coordinates are `x 0, …, x 7 = a11 a12 a21 a22 b11 b12 b21 b22`.
A circuit with `k` gates is a sequence `g 0, …, g (k-1)` such that each `g i` is a product
`u * v` of two elements of `S g i = span{1, x 0..7, g 0..g (i-1)}`; it computes the targets
if all four `c i j` lie in `S g k`.  XOR and constants are free; nothing restricts the degree.
-/

namespace MC222

/-- Points of `F₂⁸`. -/
abbrev Pt := Fin 8 → ZMod 2
/-- Boolean functions `F₂⁸ → F₂` (pointwise ring and `F₂`-module structure). -/
abbrev Fn := Pt → ZMod 2

/-- The coordinate functions `x 0..7 = a11 a12 a21 a22 b11 b12 b21 b22`. -/
def x (k : Fin 8) : Fn := fun p => p k
/-- `a i k` is the entry of `A` in row `i`, column `k` (0-based). -/
def a (i k : Fin 2) : Fn := x ⟨2 * i.val + k.val, by omega⟩
/-- `b k j` is the entry of `B` in row `k`, column `j` (0-based). -/
def b (k j : Fin 2) : Fn := x ⟨4 + 2 * k.val + j.val, by omega⟩
/-- The targets `c i j = a i 0 * b 0 j + a i 1 * b 1 j`, entries of the product `AB`. -/
def c (i j : Fin 2) : Fn := a i 0 * b 0 j + a i 1 * b 1 j

/-- `S g j = span{1, x 0, …, x 7, g 0, …, g (j-1)}`. -/
def S {k : ℕ} (g : Fin k → Fn) (j : ℕ) : Submodule (ZMod 2) Fn :=
  Submodule.span (ZMod 2) (insert 1 (Set.range x ∪ {f | ∃ i : Fin k, i.val < j ∧ g i = f}))

/-- `g` is a circuit: every gate is a product of two elements of the span of the constant,
the inputs and the earlier gates. -/
def IsCircuit {k : ℕ} (g : Fin k → Fn) : Prop :=
  ∀ i : Fin k, ∃ u ∈ S g i, ∃ v ∈ S g i, g i = u * v

/-- `g` computes the four entries of the matrix product. -/
def Computes {k : ℕ} (g : Fin k → Fn) : Prop :=
  ∀ i j : Fin 2, c i j ∈ S g k

/-- Some circuit with `k` AND gates computes the 2×2 matrix product. -/
def HasCircuit (k : ℕ) : Prop := ∃ g : Fin k → Fn, IsCircuit g ∧ Computes g

/-- The multiplicative complexity of the 2×2 matrix product over `F₂`. -/
noncomputable def MC : ℕ := sInf {k | HasCircuit k}

end MC222
