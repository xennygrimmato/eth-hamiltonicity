/-
# Fourier transforms and cyclic convolutions over a `Root` (module F1, part 2)

Pure Mathlib; compiles in both toolchains.

For root data `ρ : Root R` (length `L`, root `ω`, `L⁻¹`):
* 1D: `dft n f s = Σ_{i<n} f i ω^(i s)`, `idft F u = L⁻¹ Σ_{t<L} F t ω^((L-u) t)`;
  inversion `idft_dft`; cyclic convolution theorem `idft_dft_mul` (`idft (dft f · dft g) = f ⊛ g`);
  acyclic embedding `cconv_eq_aconv` (inputs of length `n` with `2n ≤ L`).
* 2D, separable (rows then columns, no twiddles): `rowT`, `colT`, `dft2 = colT ∘ rowT`,
  `icol`, `irow`; `dft2_eq` (it is the 2D DFT), `idft2_dft2` (inversion),
  `idft2_dft2_mul` (2D cyclic convolution theorem) and `cconv2_eq_aconv2` (acyclic embedding).
-/
import EthFollowup.Factoring.FermatRing

set_option linter.unusedSectionVars false

namespace Factoring.Fermat

open Finset

section Acyclic
variable {R : Type*} [CommSemiring R]

/-- Acyclic convolution of two `n`-term inputs, at `u`. -/
def aconv (n : ℕ) (f g : ℕ → R) (u : ℕ) : R :=
  ∑ i ∈ range n, ∑ j ∈ range n, if i + j = u then f i * g j else 0

/-- 2D acyclic convolution of `n1 × n2` inputs. -/
def aconv2 (n1 n2 : ℕ) (f g : ℕ → ℕ → R) (a u : ℕ) : R :=
  ∑ i2 ∈ range n2, ∑ j2 ∈ range n2,
    if i2 + j2 = u then aconv n1 (fun i1 => f i1 i2) (fun j1 => g j1 j2) a else 0

end Acyclic

namespace Root
variable {R : Type*} [CommRing R] (ρ : Root R)

/-! ## 1D transforms -/

/-- Forward transform of an `n`-term input: `dft n f s = Σ_{i<n} f i · ω^(i s)`. -/
def dft (n : ℕ) (f : ℕ → R) (s : ℕ) : R := ∑ i ∈ range n, f i * ρ.ω ^ (i * s)

/-- Inverse transform: `idft F u = L⁻¹ · Σ_{t<L} F t · ω^((L-u) t)`. -/
def idft (F : ℕ → R) (u : ℕ) : R := ρ.Linv * ∑ t ∈ range ρ.L, F t * ρ.ω ^ ((ρ.L - u) * t)

theorem idft_sum {ι : Type*} (S : Finset ι) (F : ι → ℕ → R) (u : ℕ) :
    ρ.idft (fun t => ∑ x ∈ S, F x t) u = ∑ x ∈ S, ρ.idft (F x) u := by
  simp only [idft, sum_mul, mul_sum]; rw [sum_comm]

theorem idft_mul_left (c : R) (F : ℕ → R) (u : ℕ) :
    ρ.idft (fun t => c * F t) u = c * ρ.idft F u := by
  simp only [idft, mul_sum]; exact sum_congr rfl fun _ _ => by ring

theorem idft_zero (u : ℕ) : ρ.idft (fun _ => 0) u = 0 := by simp [idft]

theorem idft_ite (P : Prop) [Decidable P] (F : ℕ → R) (u : ℕ) :
    ρ.idft (fun t => if P then F t else 0) u = if P then ρ.idft F u else 0 := by
  split_ifs <;> simp [idft]

theorem idft_congr {F G : ℕ → R} (h : ∀ t < ρ.L, F t = G t) (u : ℕ) : ρ.idft F u = ρ.idft G u := by
  simp only [idft]; congr 1; exact sum_congr rfl fun t ht => by rw [h t (mem_range.1 ht)]

/-- The inverse transform of a pure power: `idft (ω^(x ·)) u = [x % L = u]`. -/
theorem idft_pow (x : ℕ) {u : ℕ} (hu : u < ρ.L) :
    ρ.idft (fun t => ρ.ω ^ (x * t)) u = if x % ρ.L = u then 1 else 0 := by
  rw [← ρ.orth_shift x u hu]; simp only [idft]; congr 1
  exact sum_congr rfl fun t _ => by rw [← pow_add, add_mul]

/-- Inverse transform of a finite combination of powers. -/
theorem idft_comb {ι : Type*} (S : Finset ι) (c : ι → R) (x : ι → ℕ) {u : ℕ} (hu : u < ρ.L) :
    ρ.idft (fun t => ∑ y ∈ S, c y * ρ.ω ^ (x y * t)) u =
      ∑ y ∈ S, if x y % ρ.L = u then c y else 0 := by
  rw [idft_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [idft_mul_left, idft_pow _ _ hu]; split_ifs <;> simp

/-- Inversion theorem. -/
theorem idft_dft (f : ℕ → R) {u : ℕ} (hu : u < ρ.L) : ρ.idft (ρ.dft ρ.L f) u = f u := by
  have : ρ.dft ρ.L f = fun t => ∑ i ∈ range ρ.L, f i * ρ.ω ^ (i * t) := rfl
  rw [this, idft_comb _ _ _ _ hu]
  have : ∀ i ∈ range ρ.L, (if i % ρ.L = u then f i else 0) = if i = u then f i else 0 := by
    intro i hi; rw [Nat.mod_eq_of_lt (mem_range.1 hi)]
  rw [sum_congr rfl this, sum_ite_eq']; simp [hu]

/-- Cyclic convolution of two `n`-term inputs, at `u`. -/
def cconv (n : ℕ) (f g : ℕ → R) (u : ℕ) : R :=
  ∑ i ∈ range n, ∑ j ∈ range n, if (i + j) % ρ.L = u then f i * g j else 0

theorem dft_mul (n : ℕ) (f g : ℕ → R) (t : ℕ) :
    ρ.dft n f t * ρ.dft n g t =
      ∑ i ∈ range n, ∑ j ∈ range n, (f i * g j) * ρ.ω ^ ((i + j) * t) := by
  simp only [dft]; rw [sum_mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [add_mul, pow_add]; ring

/-- 1D cyclic convolution theorem: `idft (dft f · dft g) = f ⊛ g`. -/
theorem idft_dft_mul (n : ℕ) (f g : ℕ → R) {u : ℕ} (hu : u < ρ.L) :
    ρ.idft (fun t => ρ.dft n f t * ρ.dft n g t) u = ρ.cconv n f g u := by
  simp only [dft_mul, cconv]
  rw [idft_sum]
  exact sum_congr rfl fun i _ => by rw [idft_comb _ _ _ _ hu]

/-- Acyclic embedding: for `n`-term inputs with `2n ≤ L`, cyclic = acyclic convolution. -/
theorem cconv_eq_aconv {n : ℕ} (hn : 2 * n ≤ ρ.L) (f g : ℕ → R) (u : ℕ) :
    ρ.cconv n f g u = aconv n f g u := by
  simp only [cconv, aconv]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  rw [mem_range] at hi hj
  rw [Nat.mod_eq_of_lt (by omega)]

/-! ## 2D transforms (rows then columns) -/

/-- Row transforms: `rowT n1 f s i2 = Σ_{i1<n1} f i1 i2 ω^(i1 s)`. -/
def rowT (n1 : ℕ) (f : ℕ → ℕ → R) (s i2 : ℕ) : R := ρ.dft n1 (fun i1 => f i1 i2) s

/-- Column transforms: `colT n2 A s t = Σ_{i2<n2} A s i2 ω^(i2 t)`. -/
def colT (n2 : ℕ) (A : ℕ → ℕ → R) (s t : ℕ) : R := ρ.dft n2 (fun i2 => A s i2) t

/-- The separable 2D transform: rows, then columns. -/
def dft2 (n1 n2 : ℕ) (f : ℕ → ℕ → R) : ℕ → ℕ → R := ρ.colT n2 (ρ.rowT n1 f)

/-- Inverse column transforms: `icol C s u = L⁻¹ Σ_{t<L} C s t ω^((L-u) t)`. -/
def icol (C : ℕ → ℕ → R) (s u : ℕ) : R := ρ.idft (fun t => C s t) u

/-- Inverse row transforms: `irow D a u = L⁻¹ Σ_{s<L} D s u ω^((L-a) s)`. -/
def irow (D : ℕ → ℕ → R) (a u : ℕ) : R := ρ.idft (fun s => D s u) a

/-- The separable transform is the 2D DFT (no twiddle factors). -/
theorem dft2_eq (n1 n2 : ℕ) (f : ℕ → ℕ → R) (s t : ℕ) :
    ρ.dft2 n1 n2 f s t =
      ∑ i1 ∈ range n1, ∑ i2 ∈ range n2, f i1 i2 * (ρ.ω ^ (i1 * s) * ρ.ω ^ (i2 * t)) := by
  simp only [dft2, colT, rowT, dft, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- 2D inversion theorem. -/
theorem idft2_dft2 (f : ℕ → ℕ → R) {a u : ℕ} (ha : a < ρ.L) (hu : u < ρ.L) :
    ρ.irow (ρ.icol (ρ.dft2 ρ.L ρ.L f)) a u = f a u := by
  simp only [irow, icol, dft2, colT]
  rw [show (fun s => ρ.idft (fun t => ρ.dft ρ.L (fun i2 => ρ.rowT ρ.L f s i2) t) u) =
      fun s => ρ.rowT ρ.L f s u from funext fun s => ρ.idft_dft _ hu]
  exact ρ.idft_dft (fun i1 => f i1 u) ha

/-- 2D cyclic convolution of `n1 × n2` inputs (cyclic in both coordinates). -/
def cconv2 (n1 n2 : ℕ) (f g : ℕ → ℕ → R) (a u : ℕ) : R :=
  ∑ i2 ∈ range n2, ∑ j2 ∈ range n2,
    if (i2 + j2) % ρ.L = u then ρ.cconv n1 (fun i1 => f i1 i2) (fun j1 => g j1 j2) a else 0

/-- 2D cyclic convolution theorem: rows, columns, pointwise product, inverse columns, inverse rows. -/
theorem idft2_dft2_mul (n1 n2 : ℕ) (f g : ℕ → ℕ → R) {a u : ℕ} (ha : a < ρ.L) (hu : u < ρ.L) :
    ρ.irow (ρ.icol (fun s t => ρ.dft2 n1 n2 f s t * ρ.dft2 n1 n2 g s t)) a u =
      ρ.cconv2 n1 n2 f g a u := by
  have hcol : ∀ s, ρ.icol (fun s t => ρ.dft2 n1 n2 f s t * ρ.dft2 n1 n2 g s t) s u =
      ∑ i2 ∈ range n2, ∑ j2 ∈ range n2,
        if (i2 + j2) % ρ.L = u then ρ.rowT n1 f s i2 * ρ.rowT n1 g s j2 else 0 := by
    intro s
    exact ρ.idft_dft_mul n2 (fun i2 => ρ.rowT n1 f s i2) (fun j2 => ρ.rowT n1 g s j2) hu
  simp only [irow, hcol]
  rw [idft_sum]
  refine sum_congr rfl fun i2 _ => ?_
  rw [idft_sum]
  refine sum_congr rfl fun j2 _ => ?_
  rw [idft_ite]
  congr 1
  exact ρ.idft_dft_mul n1 (fun i1 => f i1 i2) (fun j1 => g j1 j2) ha

/-- Acyclic embedding in 2D: for `2 n1 ≤ L`, `2 n2 ≤ L`, cyclic = acyclic. -/
theorem cconv2_eq_aconv2 {n1 n2 : ℕ} (h1 : 2 * n1 ≤ ρ.L) (h2 : 2 * n2 ≤ ρ.L) (f g : ℕ → ℕ → R)
    (a u : ℕ) : ρ.cconv2 n1 n2 f g a u = aconv2 n1 n2 f g a u := by
  simp only [cconv2, aconv2]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  rw [mem_range] at hi hj
  rw [Nat.mod_eq_of_lt (by omega), ρ.cconv_eq_aconv h1]

end Root

end Factoring.Fermat
