/-
# A concrete exterior (Grassmann) algebra over `ℤ`  (module M1 of the exact-#HC blueprint)

Write-up reference: `research/exact-hc-theorem.md`, §2 and §3 (Lemma 3.2, step 2).

Throughout, `Γ` is a finite linearly ordered type of *generators*
(`[Fintype Γ] [LinearOrder Γ]`).

## Main definitions
* `invCount S T` : `#{(s,t) ∈ S × T : t < s}`;  `mergeSign S T = (-1)^(invCount S T)`.
* `structConst S T U` : `mergeSign S T` if `S, T` are disjoint with `S ∪ T = U`, else `0`.
* `Grass Γ` : the exterior algebra `Λ(Γ)`; an element is a coefficient function `Finset Γ → ℤ`.
  `Grass.coeff x S` is the coefficient of `e_S`, `Grass.ofCoeff f` builds an element;
  `Grass.ext` is extensionality. `Grass Γ` is a `Ring` (`instRing`), hence a `ℤ`-algebra.
* `Grass.e S` : the basis element `e_S`;  `Grass.gen γ = e {γ}`;  `1 = e ∅`.
* `Grass.IsHomog p x` : every `S` with `coeff x S ≠ 0` has `S.card ≡ p [MOD 2]`.
* `Grass.koszulExp p σ = Σ_{s<t, σ⁻¹ t < σ⁻¹ s} p s * p t`.
* `Grass.SuppIn A x` : every `S` with `coeff x S ≠ 0` satisfies `S ⊆ A`  (`x ∈ Λ(A)`).
* `Grass.IsSignedBasis A ω` : `ω = e A ∨ ω = -e A`.
* `Grass.topCoeff A ω x = coeff x A * coeff ω A` : the coefficient `[ω](x)` of the write-up
  (for `IsSignedBasis A ω` and `SuppIn A x`: `x - [ω](x) • ω` has zero `A`-coefficient).
* `Grass.linForm g b = Σ u, b u • g u`;  `Grass.theta b = linForm gen b`.

## Main results
* `coeff_mul`, `e_mul_e`, `e_mul_e_comm`, `gen_mul_gen` (anticommute), `gen_mul_self` (`= 0`),
  `e_eq_prod_sort` (`e S = ((S.sort (· ≤ ·)).map gen).prod`), `sum_coeff_smul_e`.
* Fact 2.1: `IsHomog.mul_comm_sign` (`x * y = (-1)^(p*q) • (y * x)`), `IsHomog.anticomm`,
  `IsHomog.commute_of_even` (even elements are central), `IsHomog.mul_self_eq_zero` (odd).
* Lemma 2.2 (Koszul): `koszul`.
* Lemma 2.3: `coeff_mul_of_suppIn`, `coeff_prod_ofFn_blocks`, `topCoeff_prod_ofFn_blocks`
  (`[Ω](x_1 ⋯ x_g) = Π_a [ω_a](x_a)` with `Ω = ω_1 ⋯ ω_g`), `isSignedBasis_prod_ofFn`.
* Lemma 3.2 step 2: `prod_linForm_eq_det`, `prod_linForm_gen_eq_det`
  (`Π_k θ(b_k) = det B • Π_u ψ_u`, all products ordered along `Fin N`).
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset

-- `if_pos`/`if_neg` are deprecated in recent Mathlib but are kept for portability.
set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset

/-! ### Merge signs -/

section Sign

variable {Γ : Type*} [LinearOrder Γ]

/-- Inversion count `#{(s,t) ∈ S × T : t < s}`. -/
def invCount (S T : Finset Γ) : ℕ := ((S ×ˢ T).filter fun p => p.2 < p.1).card

/-- The merge sign `(-1)^{#{(s,t) ∈ S × T : t < s}}`. -/
def mergeSign (S T : Finset Γ) : ℤ := (-1) ^ invCount S T

theorem invCount_union_left {S T R : Finset Γ} (h : Disjoint S T) :
    invCount (S ∪ T) R = invCount S R + invCount T R := by
  unfold invCount
  rw [union_product, filter_union, card_union_of_disjoint]
  exact disjoint_filter_filter (disjoint_product.2 (Or.inl h))

theorem invCount_union_right {S T R : Finset Γ} (h : Disjoint T R) :
    invCount S (T ∪ R) = invCount S T + invCount S R := by
  unfold invCount
  rw [product_union, filter_union, card_union_of_disjoint]
  exact disjoint_filter_filter (disjoint_product.2 (Or.inr h))

theorem invCount_add_invCount {S T : Finset Γ} (h : Disjoint S T) :
    invCount S T + invCount T S = S.card * T.card := by
  have h1 : invCount T S = ((S ×ˢ T).filter fun p => ¬ p.2 < p.1).card := by
    unfold invCount
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_coe, mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, not_lt.2 hp.2.le⟩
    · intro p hp
      simp only [mem_coe, mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      have hne : p.1 ≠ p.2 := fun e => Finset.disjoint_left.1 h hp.1.1 (e ▸ hp.1.2)
      exact ⟨⟨hp.1.2, hp.1.1⟩, lt_of_le_of_ne (not_lt.1 hp.2) hne⟩
    · intro p _
      exact Prod.swap_swap p
    · intro p _
      exact Prod.swap_swap p
  rw [h1]
  unfold invCount
  rw [card_filter_add_card_filter_not, card_product]

theorem mergeSign_swap {S T : Finset Γ} (h : Disjoint S T) :
    mergeSign S T = (-1) ^ (S.card * T.card) * mergeSign T S := by
  unfold mergeSign
  rw [← invCount_add_invCount h, pow_add]
  rcases neg_one_pow_eq_or ℤ (invCount T S) with h' | h' <;> rw [h'] <;> ring

theorem mergeSign_assoc {S T R : Finset Γ} (hST : Disjoint S T) (hTR : Disjoint T R) :
    mergeSign S T * mergeSign (S ∪ T) R = mergeSign T R * mergeSign S (T ∪ R) := by
  unfold mergeSign
  rw [invCount_union_left hST, invCount_union_right hTR, pow_add, pow_add]
  ring

theorem mergeSign_empty_left (T : Finset Γ) : mergeSign ∅ T = 1 := by
  simp [mergeSign, invCount]

theorem mergeSign_empty_right (S : Finset Γ) : mergeSign S ∅ = 1 := by
  simp [mergeSign, invCount]

theorem mergeSign_eq_or (S T : Finset Γ) : mergeSign S T = 1 ∨ mergeSign S T = -1 :=
  neg_one_pow_eq_or ℤ _

/-- Structure constants: `e_S e_T = Σ_U structConst S T U • e_U`. -/
def structConst (S T U : Finset Γ) : ℤ :=
  if Disjoint S T ∧ S ∪ T = U then mergeSign S T else 0

theorem structConst_swap (S T U : Finset Γ) :
    structConst S T U = (-1) ^ (S.card * T.card) * structConst T S U := by
  unfold structConst
  by_cases h : Disjoint S T ∧ S ∪ T = U
  · rw [if_pos h, if_pos ⟨h.1.symm, by rw [union_comm]; exact h.2⟩, mergeSign_swap h.1]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, by rw [union_comm]; exact h'.2⟩), mul_zero]

end Sign

/-- `(-1)^a` only depends on `a` mod 2. -/
theorem neg_one_pow_congr {a b : ℕ} (h : a ≡ b [MOD 2]) : (-1 : ℤ) ^ a = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two (R := ℤ) a, neg_one_pow_eq_pow_mod_two (R := ℤ) b]
  rw [show a % 2 = b % 2 from h]

/-! ### The algebra -/

/-- The exterior algebra `Λ(Γ)` over `ℤ`, as coefficient functions on the basis `e_S`. -/
def Grass (Γ : Type*) : Type _ := Finset Γ → ℤ

namespace Grass

variable {Γ : Type*}

instance : AddCommGroup (Grass Γ) := inferInstanceAs (AddCommGroup (Finset Γ → ℤ))

/-- The coefficient of `e_S` in `x`. -/
def coeff (x : Grass Γ) (S : Finset Γ) : ℤ := x S

/-- The element with the given coefficients. -/
def ofCoeff (f : Finset Γ → ℤ) : Grass Γ := f

@[ext] theorem ext {x y : Grass Γ} (h : ∀ S, x.coeff S = y.coeff S) : x = y := funext h

@[simp] theorem coeff_ofCoeff (f : Finset Γ → ℤ) (S : Finset Γ) : (ofCoeff f).coeff S = f S :=
  rfl

@[simp] theorem coeff_zero (S : Finset Γ) : (0 : Grass Γ).coeff S = 0 := rfl

@[simp] theorem coeff_add (x y : Grass Γ) (S : Finset Γ) :
    (x + y).coeff S = x.coeff S + y.coeff S := rfl

@[simp] theorem coeff_neg (x : Grass Γ) (S : Finset Γ) : (-x).coeff S = -x.coeff S := rfl

@[simp] theorem coeff_sub (x y : Grass Γ) (S : Finset Γ) :
    (x - y).coeff S = x.coeff S - y.coeff S := rfl

@[simp] theorem coeff_zsmul (n : ℤ) (x : Grass Γ) (S : Finset Γ) :
    (n • x).coeff S = n * x.coeff S := rfl

@[simp] theorem coeff_nsmul (n : ℕ) (x : Grass Γ) (S : Finset Γ) :
    (n • x).coeff S = n * x.coeff S := by
  show n • x S = _
  rw [nsmul_eq_mul]
  rfl

@[simp] theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → Grass Γ) (S : Finset Γ) :
    (∑ i ∈ s, f i).coeff S = ∑ i ∈ s, (f i).coeff S := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [sum_insert ha, sum_insert ha, coeff_add, ih]

variable [Fintype Γ] [LinearOrder Γ]

instance : Mul (Grass Γ) :=
  ⟨fun x y => ofCoeff fun U => ∑ S, ∑ T, structConst S T U * (x.coeff S * y.coeff T)⟩

theorem coeff_mul (x y : Grass Γ) (U : Finset Γ) :
    (x * y).coeff U = ∑ S, ∑ T, structConst S T U * (x.coeff S * y.coeff T) := rfl

/-- The basis element `e_S`. -/
def e (S : Finset Γ) : Grass Γ := ofCoeff fun U => if S = U then 1 else 0

theorem coeff_e (S U : Finset Γ) : (e S).coeff U = if S = U then 1 else 0 := rfl

@[simp] theorem coeff_e_self (S : Finset Γ) : (e S).coeff S = 1 := by simp [coeff_e]

theorem coeff_e_of_ne {S U : Finset Γ} (h : S ≠ U) : (e S).coeff U = 0 := by simp [coeff_e, h]

instance : One (Grass Γ) := ⟨e ∅⟩

theorem one_def : (1 : Grass Γ) = e ∅ := rfl

/-- Every element is the sum of its coefficients times basis elements. -/
theorem sum_coeff_smul_e (x : Grass Γ) : ∑ S, x.coeff S • e S = x := by
  ext U
  simp [coeff_e]

/-! #### Ring axioms -/

private theorem mul_add' (x y z : Grass Γ) : x * (y + z) = x * y + x * z := by
  ext U; simp only [coeff_mul, coeff_add, mul_add, Finset.sum_add_distrib]

private theorem add_mul' (x y z : Grass Γ) : (x + y) * z = x * z + y * z := by
  ext U; simp only [coeff_mul, coeff_add, add_mul, mul_add, Finset.sum_add_distrib]

private theorem zero_mul' (x : Grass Γ) : 0 * x = 0 := by
  ext U; simp [coeff_mul]

private theorem mul_zero' (x : Grass Γ) : x * 0 = 0 := by
  ext U; simp [coeff_mul]

private theorem zsmul_mul' (n : ℤ) (x y : Grass Γ) : (n • x) * y = n • (x * y) := by
  ext U
  simp only [coeff_mul, coeff_zsmul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => by ring

private theorem mul_zsmul' (n : ℤ) (x y : Grass Γ) : x * (n • y) = n • (x * y) := by
  ext U
  simp only [coeff_mul, coeff_zsmul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => by ring

private theorem sum_mul' {ι : Type*} (s : Finset ι) (f : ι → Grass Γ) (y : Grass Γ) :
    (∑ i ∈ s, f i) * y = ∑ i ∈ s, f i * y := by
  classical
  refine Finset.induction_on s (by simp [zero_mul']) ?_
  intro a s ha ih
  rw [sum_insert ha, sum_insert ha, add_mul', ih]

private theorem mul_sum' {ι : Type*} (s : Finset ι) (f : ι → Grass Γ) (y : Grass Γ) :
    y * (∑ i ∈ s, f i) = ∑ i ∈ s, y * f i := by
  classical
  refine Finset.induction_on s (by simp [mul_zero']) ?_
  intro a s ha ih
  rw [sum_insert ha, sum_insert ha, mul_add', ih]

theorem coeff_e_mul_e (S T U : Finset Γ) : (e S * e T).coeff U = structConst S T U := by
  rw [coeff_mul, Finset.sum_eq_single S, Finset.sum_eq_single T]
  · simp
  · intro T' _ hT'; simp [coeff_e_of_ne (Ne.symm hT')]
  · simp
  · intro S' _ hS'; simp [coeff_e_of_ne (Ne.symm hS')]
  · simp

/-- The multiplication rule on basis elements. -/
theorem e_mul_e (S T : Finset Γ) :
    e S * e T = if Disjoint S T then mergeSign S T • e (S ∪ T) else 0 := by
  ext U
  rw [coeff_e_mul_e, structConst]
  by_cases h : Disjoint S T
  · by_cases hU : S ∪ T = U
    · simp [h, hU]
    · simp [h, hU, coeff_e_of_ne hU]
  · simp [h]

private theorem e_mul_e_mul_e (S T R : Finset Γ) : e S * e T * e R = e S * (e T * e R) := by
  by_cases hST : Disjoint S T
  · by_cases hTR : Disjoint T R
    · by_cases hSR : Disjoint S R
      · have h1 : Disjoint (S ∪ T) R := disjoint_union_left.2 ⟨hSR, hTR⟩
        have h2 : Disjoint S (T ∪ R) := disjoint_union_right.2 ⟨hST, hSR⟩
        rw [e_mul_e S T, if_pos hST, zsmul_mul', e_mul_e, if_pos h1, e_mul_e T R, if_pos hTR,
          mul_zsmul', e_mul_e, if_pos h2, smul_smul, smul_smul, union_assoc,
          mergeSign_assoc hST hTR]
      · have h1 : ¬ Disjoint (S ∪ T) R := fun h => hSR (disjoint_union_left.1 h).1
        have h2 : ¬ Disjoint S (T ∪ R) := fun h => hSR (disjoint_union_right.1 h).2
        rw [e_mul_e S T, if_pos hST, zsmul_mul', e_mul_e, if_neg h1, e_mul_e T R, if_pos hTR,
          mul_zsmul', e_mul_e, if_neg h2, smul_zero, smul_zero]
    · have h1 : ¬ Disjoint (S ∪ T) R := fun h => hTR (disjoint_union_left.1 h).2
      rw [e_mul_e S T, if_pos hST, zsmul_mul', e_mul_e, if_neg h1, e_mul_e T R, if_neg hTR,
        mul_zero', smul_zero]
  · rw [e_mul_e S T, if_neg hST, zero_mul']
    by_cases hTR : Disjoint T R
    · have h2 : ¬ Disjoint S (T ∪ R) := fun h => hST (disjoint_union_right.1 h).1
      rw [e_mul_e T R, if_pos hTR, mul_zsmul', e_mul_e, if_neg h2, smul_zero]
    · rw [e_mul_e T R, if_neg hTR, mul_zero']

private theorem mul_assoc' (x y z : Grass Γ) : x * y * z = x * (y * z) := by
  rw [← sum_coeff_smul_e x, ← sum_coeff_smul_e y, ← sum_coeff_smul_e z]
  simp only [sum_mul', mul_sum', zsmul_mul', mul_zsmul', e_mul_e_mul_e]

private theorem one_mul' (x : Grass Γ) : 1 * x = x := by
  rw [← sum_coeff_smul_e x, mul_sum', one_def]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [mul_zsmul', e_mul_e, if_pos (disjoint_empty_left S), mergeSign_empty_left, one_smul,
    empty_union]

private theorem mul_one' (x : Grass Γ) : x * 1 = x := by
  rw [← sum_coeff_smul_e x, sum_mul', one_def]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [zsmul_mul', e_mul_e, if_pos (disjoint_empty_right S), mergeSign_empty_right, one_smul,
    union_empty]

instance instRing : Ring (Grass Γ) :=
  { (inferInstance : AddCommGroup (Grass Γ)) with
    mul := (· * ·)
    one := 1
    left_distrib := mul_add'
    right_distrib := add_mul'
    zero_mul := zero_mul'
    mul_zero := mul_zero'
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := mul_one' }

@[simp] theorem coeff_one (U : Finset Γ) : (1 : Grass Γ).coeff U = if ∅ = U then 1 else 0 :=
  rfl

@[simp] theorem coeff_one_empty : (1 : Grass Γ).coeff ∅ = 1 := rfl

theorem e_empty : e (∅ : Finset Γ) = 1 := rfl

/-- `e_S e_T = (-1)^{|S||T|} e_T e_S` (also when `S, T` meet: then both sides vanish). -/
theorem e_mul_e_comm (S T : Finset Γ) :
    e S * e T = (-1 : ℤ) ^ (S.card * T.card) • (e T * e S) := by
  ext U
  rw [coeff_e_mul_e, coeff_zsmul, coeff_e_mul_e, structConst_swap]

/-! #### Generators -/

/-- The generator `γ = e_{{γ}}`. -/
def gen (γ : Γ) : Grass Γ := e {γ}

theorem gen_mul_self (γ : Γ) : gen γ * gen γ = 0 := by
  rw [gen, e_mul_e, if_neg]
  simp

theorem gen_mul_gen (a b : Γ) : gen a * gen b = -(gen b * gen a) := by
  rw [gen, gen, e_mul_e_comm]
  simp

/-- `e_S` is the product of its generators in increasing order (for any increasing list). -/
theorem prod_map_gen_of_pairwise :
    ∀ l : List Γ, l.Pairwise (· < ·) → (l.map gen).prod = e l.toFinset
  | [], _ => by simp [e_empty]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons, prod_map_gen_of_pairwise l (List.Pairwise.of_cons h),
      gen, e_mul_e, List.toFinset_cons]
    have hlt : ∀ b ∈ l.toFinset, a < b := fun b hb =>
      List.rel_of_pairwise_cons h (List.mem_toFinset.1 hb)
    have hd : Disjoint {a} l.toFinset :=
      disjoint_singleton_left.2 (fun ha => lt_irrefl a (hlt a ha))
    have hinv : invCount {a} l.toFinset = 0 := by
      unfold invCount
      rw [card_eq_zero, filter_eq_empty_iff]
      intro p hp
      rw [mem_product, mem_singleton] at hp
      rw [hp.1]
      exact not_lt.2 (hlt _ hp.2).le
    rw [if_pos hd, mergeSign, hinv, pow_zero, one_smul, insert_eq]

/-- `e_S` is the ordered product of the generators in `S`. -/
theorem e_eq_prod_sort (S : Finset Γ) : e S = ((S.sort (· ≤ ·)).map gen).prod := by
  have h : (S.sort (· ≤ ·)).Pairwise (· < ·) :=
    ((S.pairwise_sort (· ≤ ·)).and (S.sort_nodup (· ≤ ·))).imp fun h => lt_of_le_of_ne h.1 h.2
  rw [prod_map_gen_of_pairwise _ h, sort_toFinset]

/-! ### Parity and graded commutativity (Fact 2.1) -/

/-- `x` is homogeneous of parity `p`: all its basis sets have cardinality `≡ p (mod 2)`. -/
def IsHomog (p : ℕ) (x : Grass Γ) : Prop := ∀ S, x.coeff S ≠ 0 → S.card ≡ p [MOD 2]

theorem isHomog_zero (p : ℕ) : IsHomog p (0 : Grass Γ) := fun _ h => absurd rfl h

theorem IsHomog.congr {p p' : ℕ} {x : Grass Γ} (hx : IsHomog p x) (h : p ≡ p' [MOD 2]) :
    IsHomog p' x := fun S hS => (hx S hS).trans h

theorem IsHomog.add {p : ℕ} {x y : Grass Γ} (hx : IsHomog p x) (hy : IsHomog p y) :
    IsHomog p (x + y) := by
  intro S hS
  rw [coeff_add] at hS
  by_cases h : x.coeff S = 0
  · exact hy S (by rw [h, zero_add] at hS; exact hS)
  · exact hx S h

theorem IsHomog.neg {p : ℕ} {x : Grass Γ} (hx : IsHomog p x) : IsHomog p (-x) :=
  fun S hS => hx S (by rw [coeff_neg] at hS; exact neg_ne_zero.1 hS)

theorem IsHomog.zsmul {p : ℕ} {x : Grass Γ} (hx : IsHomog p x) (n : ℤ) : IsHomog p (n • x) :=
  fun S hS => hx S (by rw [coeff_zsmul] at hS; exact right_ne_zero_of_mul hS)

theorem IsHomog.sub {p : ℕ} {x y : Grass Γ} (hx : IsHomog p x) (hy : IsHomog p y) :
    IsHomog p (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem isHomog_sum {ι : Type*} {p : ℕ} (s : Finset ι) (f : ι → Grass Γ)
    (h : ∀ i ∈ s, IsHomog p (f i)) : IsHomog p (∑ i ∈ s, f i) := by
  intro S hS
  rw [coeff_sum] at hS
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  exact h i hi S hne

theorem isHomog_e (S : Finset Γ) : IsHomog S.card (e S) := by
  intro T hT
  by_cases h : S = T
  · rw [h]
  · exact absurd (coeff_e_of_ne h) hT

theorem isHomog_gen (γ : Γ) : IsHomog 1 (gen γ) := by
  have := isHomog_e ({γ} : Finset Γ)
  rwa [card_singleton] at this

theorem isHomog_one : IsHomog 0 (1 : Grass Γ) := by
  have := isHomog_e (∅ : Finset Γ)
  rwa [card_empty] at this

theorem IsHomog.mul {p q : ℕ} {x y : Grass Γ} (hx : IsHomog p x) (hy : IsHomog q y) :
    IsHomog (p + q) (x * y) := by
  intro U hU
  rw [coeff_mul] at hU
  obtain ⟨S, -, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hU
  obtain ⟨T, -, hT⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  have hc : structConst S T U ≠ 0 := left_ne_zero_of_mul hT
  have hxy := right_ne_zero_of_mul hT
  have h1 := hx S (left_ne_zero_of_mul hxy)
  have h2 := hy T (right_ne_zero_of_mul hxy)
  unfold structConst at hc
  split_ifs at hc with h
  · rw [← h.2, card_union_of_disjoint h.1]; exact h1.add h2
  · exact absurd rfl hc

/-- A product of homogeneous elements is homogeneous, of the summed parity. -/
theorem isHomog_prod_ofFn : ∀ {M : ℕ} (y : Fin M → Grass Γ) (p : Fin M → ℕ)
    (_ : ∀ i, IsHomog (p i) (y i)), IsHomog (∑ i, p i) (List.ofFn y).prod
  | 0, _, _, _ => by simpa using isHomog_one
  | M + 1, y, p, hy => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact (hy 0).mul (isHomog_prod_ofFn (fun i => y i.succ) (fun i => p i.succ)
      fun i => hy i.succ)

/-- **Fact 2.1** (graded commutativity). -/
theorem IsHomog.mul_comm_sign {p q : ℕ} {x y : Grass Γ} (hx : IsHomog p x) (hy : IsHomog q y) :
    x * y = (-1 : ℤ) ^ (p * q) • (y * x) := by
  ext U
  rw [coeff_zsmul, coeff_mul, coeff_mul, Finset.sum_comm (s := (univ : Finset (Finset Γ)))
    (t := (univ : Finset (Finset Γ))) (f := fun T S => structConst T S U * (y.coeff T * x.coeff S)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hxS : x.coeff S = 0
  · simp [hxS]
  by_cases hyT : y.coeff T = 0
  · simp [hyT]
  rw [structConst_swap, neg_one_pow_congr ((hx S hxS).mul (hy T hyT))]
  ring

/-- Odd elements anticommute. -/
theorem IsHomog.anticomm {x y : Grass Γ} (hx : IsHomog 1 x) (hy : IsHomog 1 y) :
    x * y = -(y * x) := by
  rw [hx.mul_comm_sign hy]; simp

/-- Even elements are central (Fact 2.1). -/
theorem IsHomog.commute_of_even {x : Grass Γ} (hx : IsHomog 0 x) (y : Grass Γ) :
    x * y = y * x := by
  ext U
  rw [coeff_mul, coeff_mul, Finset.sum_comm (s := (univ : Finset (Finset Γ)))
    (t := (univ : Finset (Finset Γ))) (f := fun T S => structConst T S U * (y.coeff T * x.coeff S))]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
  by_cases hxS : x.coeff S = 0
  · simp [hxS]
  rw [structConst_swap, neg_one_pow_congr ((hx S hxS).mul_right T.card)]
  simp only [zero_mul, pow_zero, one_mul]
  ring

/-- Odd elements square to zero. -/
theorem IsHomog.mul_self_eq_zero {x : Grass Γ} (hx : IsHomog 1 x) : x * x = 0 := by
  have h := hx.anticomm hx
  ext S
  have h' := congrArg (fun z : Grass Γ => z.coeff S) h
  simp only [coeff_neg] at h'
  rw [coeff_zero]
  omega

/-! ### Koszul sign rule (Lemma 2.2) -/

section Koszul

variable {ι : Type*} [LinearOrder ι]

/-- Weighted inversion count of a list: `Σ_{i<j, l_j < l_i} p(l_i) p(l_j)`. -/
def wInv (p : ι → ℕ) : List ι → ℕ
  | [] => 0
  | a :: l => (l.map fun b => if b < a then p a * p b else 0).sum + wInv p l

private theorem sum_map_ite_eq_zero (p : ι → ℕ) (a : ι) :
    ∀ L : List ι, (∀ c ∈ L, a ≤ c) → (L.map fun b => if b < a then p a * p b else 0).sum = 0
  | [], _ => rfl
  | c :: L, h => by
    rw [List.map_cons, List.sum_cons, if_neg (not_lt.2 (h c (by simp))),
      sum_map_ite_eq_zero p a L (fun d hd => h d (by simp [hd])), zero_add]

theorem prod_orderedInsert (y : ι → Grass Γ) (p : ι → ℕ) (hy : ∀ i, IsHomog (p i) (y i))
    (a : ι) : ∀ L : List ι, L.Pairwise (· ≤ ·) →
      y a * (L.map y).prod = (-1 : ℤ) ^ (L.map fun b => if b < a then p a * p b else 0).sum •
        ((L.orderedInsert (· ≤ ·) a).map y).prod
  | [], _ => by simp
  | b :: L, hL => by
    rw [List.orderedInsert_cons]
    by_cases hab : a ≤ b
    · rw [if_pos hab, sum_map_ite_eq_zero p a (b :: L) ?_, pow_zero, one_smul]
      · simp
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hab
        · exact hab.trans (List.rel_of_pairwise_cons hL hc)
    · rw [if_neg hab]
      have hba : b < a := lt_of_not_ge hab
      simp only [List.map_cons, List.prod_cons, List.sum_cons, if_pos hba]
      rw [← mul_assoc, (hy a).mul_comm_sign (hy b), smul_mul_assoc, mul_assoc,
        prod_orderedInsert y p hy a L (List.Pairwise.of_cons hL), mul_smul_comm, smul_smul,
        ← pow_add]

theorem prod_map_eq_insertionSort (y : ι → Grass Γ) (p : ι → ℕ)
    (hy : ∀ i, IsHomog (p i) (y i)) : ∀ l : List ι,
    (l.map y).prod = (-1 : ℤ) ^ wInv p l • ((l.insertionSort (· ≤ ·)).map y).prod
  | [] => by simp [wInv]
  | a :: l => by
    rw [List.map_cons, List.prod_cons, prod_map_eq_insertionSort y p hy l, mul_smul_comm,
      prod_orderedInsert y p hy a _ (List.pairwise_insertionSort _ _), smul_smul, ← pow_add,
      List.insertionSort_cons, wInv,
      ((List.perm_insertionSort (· ≤ ·) l).map (fun b => if b < a then p a * p b else 0)).sum_eq,
      add_comm]

theorem wInv_ofFn (p : ι → ℕ) : ∀ {M : ℕ} (f : Fin M → ι),
    wInv p (List.ofFn f) = ∑ i, ∑ j, if i < j ∧ f j < f i then p (f i) * p (f j) else 0
  | 0, f => by simp [wInv]
  | M + 1, f => by
    rw [List.ofFn_succ, wInv, wInv_ofFn p (fun i => f i.succ), List.map_ofFn, List.sum_ofFn,
      Fin.sum_univ_succ]
    simp [Fin.sum_univ_succ, Fin.succ_lt_succ_iff, Fin.succ_pos]

end Koszul

/-- The Koszul exponent `N(σ) = Σ_{s<t, σ⁻¹ s > σ⁻¹ t} p_s p_t`. -/
def koszulExp {M : ℕ} (p : Fin M → ℕ) (σ : Equiv.Perm (Fin M)) : ℕ :=
  ∑ s, ∑ t, if s < t ∧ σ⁻¹ t < σ⁻¹ s then p s * p t else 0

/-- **Lemma 2.2 (Koszul sign rule).**
`y_{σ 0} ⋯ y_{σ (M-1)} = (-1)^{N(σ)} y_0 ⋯ y_{M-1}` for homogeneous `y_i` of parities `p_i`. -/
theorem koszul {M : ℕ} (y : Fin M → Grass Γ) (p : Fin M → ℕ) (hy : ∀ i, IsHomog (p i) (y i))
    (σ : Equiv.Perm (Fin M)) :
    (List.ofFn (y ∘ σ)).prod = (-1 : ℤ) ^ koszulExp p σ • (List.ofFn y).prod := by
  have h1 : List.ofFn (y ∘ σ) = (List.ofFn σ).map y := by rw [List.map_ofFn]
  have h2 : (List.ofFn σ).insertionSort (· ≤ ·) = List.finRange M := by
    refine List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ _)
      (List.pairwise_le_finRange M) ?_
    refine (List.perm_insertionSort _ _).trans ?_
    have := Equiv.Perm.ofFn_comp_perm σ id
    rwa [List.ofFn_id] at this
  have h3 : wInv p (List.ofFn σ) = koszulExp p σ := by
    rw [wInv_ofFn, koszulExp]
    conv_lhs => rw [Finset.sum_comm]
    rw [← Equiv.sum_comp σ (fun s => ∑ t, if s < t ∧ σ⁻¹ t < σ⁻¹ s then p s * p t else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Equiv.sum_comp σ (fun t => if σ j < t ∧ σ⁻¹ t < σ⁻¹ (σ j) then p (σ j) * p t else 0)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hσ : ∀ z, σ⁻¹ (σ z) = z := fun z => by simp
    simp only [hσ]
    by_cases h : i < j ∧ σ j < σ i
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩, mul_comm]
    · rw [if_neg h, if_neg fun h' => h ⟨h'.2, h'.1⟩]
  rw [h1, prod_map_eq_insertionSort y p hy, h2, h3, ← List.ofFn_eq_map]

/-! ### Supports and block factorisation (Lemma 2.3) -/

/-- `x ∈ Λ(A)`: every basis set in the support of `x` is contained in `A`. -/
def SuppIn (A : Finset Γ) (x : Grass Γ) : Prop := ∀ S, x.coeff S ≠ 0 → S ⊆ A

theorem suppIn_zero (A : Finset Γ) : SuppIn A (0 : Grass Γ) := fun _ h => absurd rfl h

theorem SuppIn.mono {A B : Finset Γ} {x : Grass Γ} (hx : SuppIn A x) (h : A ⊆ B) :
    SuppIn B x := fun S hS => (hx S hS).trans h

theorem SuppIn.add {A : Finset Γ} {x y : Grass Γ} (hx : SuppIn A x) (hy : SuppIn A y) :
    SuppIn A (x + y) := by
  intro S hS
  rw [coeff_add] at hS
  by_cases h : x.coeff S = 0
  · exact hy S (by rw [h, zero_add] at hS; exact hS)
  · exact hx S h

theorem SuppIn.neg {A : Finset Γ} {x : Grass Γ} (hx : SuppIn A x) : SuppIn A (-x) :=
  fun S hS => hx S (by rw [coeff_neg] at hS; exact neg_ne_zero.1 hS)

theorem SuppIn.zsmul {A : Finset Γ} {x : Grass Γ} (hx : SuppIn A x) (n : ℤ) :
    SuppIn A (n • x) :=
  fun S hS => hx S (by rw [coeff_zsmul] at hS; exact right_ne_zero_of_mul hS)

theorem SuppIn.sub {A : Finset Γ} {x y : Grass Γ} (hx : SuppIn A x) (hy : SuppIn A y) :
    SuppIn A (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem suppIn_sum {ι : Type*} {A : Finset Γ} (s : Finset ι) (f : ι → Grass Γ)
    (h : ∀ i ∈ s, SuppIn A (f i)) : SuppIn A (∑ i ∈ s, f i) := by
  intro S hS
  rw [coeff_sum] at hS
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  exact h i hi S hne

theorem suppIn_e {S A : Finset Γ} (h : S ⊆ A) : SuppIn A (e S) := by
  intro T hT
  by_cases h' : S = T
  · rw [← h']; exact h
  · exact absurd (coeff_e_of_ne h') hT

theorem suppIn_e_self (S : Finset Γ) : SuppIn S (e S) := suppIn_e subset_rfl

theorem suppIn_gen {γ : Γ} {A : Finset Γ} (h : γ ∈ A) : SuppIn A (gen γ) :=
  suppIn_e (singleton_subset_iff.2 h)

theorem suppIn_one (A : Finset Γ) : SuppIn A (1 : Grass Γ) := suppIn_e (empty_subset A)

theorem SuppIn.mul_union {A B : Finset Γ} {x y : Grass Γ} (hx : SuppIn A x) (hy : SuppIn B y) :
    SuppIn (A ∪ B) (x * y) := by
  intro U hU
  rw [coeff_mul] at hU
  obtain ⟨S, -, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hU
  obtain ⟨T, -, hT⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  have hc : structConst S T U ≠ 0 := left_ne_zero_of_mul hT
  have hxy := right_ne_zero_of_mul hT
  have h1 := hx S (left_ne_zero_of_mul hxy)
  have h2 := hy T (right_ne_zero_of_mul hxy)
  unfold structConst at hc
  split_ifs at hc with h
  · rw [← h.2]; exact union_subset_union h1 h2
  · exact absurd rfl hc

theorem SuppIn.mul {A : Finset Γ} {x y : Grass Γ} (hx : SuppIn A x) (hy : SuppIn A y) :
    SuppIn A (x * y) := by
  have := hx.mul_union hy
  rwa [union_self] at this

theorem suppIn_list_prod {A : Finset Γ} (l : List (Grass Γ)) (h : ∀ x ∈ l, SuppIn A x) :
    SuppIn A l.prod :=
  List.prod_induction (SuppIn A) (fun _ _ ha hb => ha.mul hb) (suppIn_one A) h

theorem suppIn_prod_ofFn {g : ℕ} (A : Fin g → Finset Γ) (x : Fin g → Grass Γ)
    (hx : ∀ a, SuppIn (A a) (x a)) : SuppIn (univ.biUnion A) (List.ofFn x).prod := by
  refine suppIn_list_prod _ fun z hz => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hz
  exact (hx a).mono (subset_biUnion_of_mem A (mem_univ a))

private theorem eq_of_union_eq {S T A B : Finset Γ} (hS : S ⊆ A) (hT : T ⊆ B)
    (hAB : Disjoint A B) (h : S ∪ T = A ∪ B) : S = A ∧ T = B := by
  constructor
  · refine Subset.antisymm hS fun a ha => ?_
    have : a ∈ S ∪ T := h ▸ mem_union_left _ ha
    rcases mem_union.1 this with h' | h'
    · exact h'
    · exact absurd (hT h') (disjoint_left.1 hAB ha)
  · refine Subset.antisymm hT fun a ha => ?_
    have : a ∈ S ∪ T := h ▸ mem_union_right _ ha
    rcases mem_union.1 this with h' | h'
    · exact absurd (hS h') (disjoint_right.1 hAB ha)
    · exact h'

/-- Product of elements supported in disjoint sets: the coefficient of `e_{A ∪ B}`. -/
theorem coeff_mul_of_suppIn {A B : Finset Γ} {x y : Grass Γ} (hx : SuppIn A x) (hy : SuppIn B y)
    (hAB : Disjoint A B) :
    (x * y).coeff (A ∪ B) = mergeSign A B * (x.coeff A * y.coeff B) := by
  rw [coeff_mul, Finset.sum_eq_single A, Finset.sum_eq_single B]
  · simp [structConst, hAB]
  · intro T _ hT
    by_cases hyT : y.coeff T = 0
    · simp [hyT]
    have : structConst A T (A ∪ B) = 0 := by
      unfold structConst
      rw [if_neg]
      rintro ⟨-, hu⟩
      exact hT (eq_of_union_eq subset_rfl (hy T hyT) hAB hu).2
    simp [this]
  · simp
  · intro S _ hS
    refine Finset.sum_eq_zero fun T _ => ?_
    by_cases hxS : x.coeff S = 0
    · simp [hxS]
    by_cases hyT : y.coeff T = 0
    · simp [hyT]
    have : structConst S T (A ∪ B) = 0 := by
      unfold structConst
      rw [if_neg]
      rintro ⟨-, hu⟩
      exact hS (eq_of_union_eq (hx S hxS) (hy T hyT) hAB hu).1
    simp [this]
  · simp

theorem biUnion_fin_succ {g : ℕ} (A : Fin (g + 1) → Finset Γ) :
    univ.biUnion A = A 0 ∪ univ.biUnion (fun i : Fin g => A i.succ) := by
  ext a
  simp [Fin.exists_fin_succ]

private theorem disjoint_zero_biUnion_succ {g : ℕ} (A : Fin (g + 1) → Finset Γ)
    (hA : Pairwise fun a b => Disjoint (A a) (A b)) :
    Disjoint (A 0) (univ.biUnion fun i : Fin g => A i.succ) := by
  rw [disjoint_biUnion_right]
  intro i _
  exact hA (Fin.succ_ne_zero i).symm

private theorem pairwise_succ {g : ℕ} (A : Fin (g + 1) → Finset Γ)
    (hA : Pairwise fun a b => Disjoint (A a) (A b)) :
    Pairwise fun a b : Fin g => Disjoint (A a.succ) (A b.succ) :=
  fun _ _ h => hA ((Fin.succ_injective _).ne h)

/-- **Lemma 2.3** (block factorisation), raw form: for pairwise disjoint blocks `A a` and
`x a ∈ Λ(A a)`, the coefficient of `e_{⋃ A}` in `x_0 ⋯ x_{g-1}` is the block sign
`[e_{⋃A}](e_{A 0} ⋯ e_{A (g-1)})` times `Π_a [e_{A a}](x a)`. -/
theorem coeff_prod_ofFn_blocks : ∀ {g : ℕ} (A : Fin g → Finset Γ)
    (_ : Pairwise fun a b => Disjoint (A a) (A b)) (x : Fin g → Grass Γ)
    (_ : ∀ a, SuppIn (A a) (x a)),
    (List.ofFn x).prod.coeff (univ.biUnion A) =
      (List.ofFn fun a => e (A a)).prod.coeff (univ.biUnion A) * ∏ a, (x a).coeff (A a)
  | 0, A, _, x, _ => by simp
  | g + 1, A, hA, x, hx => by
    have hd := disjoint_zero_biUnion_succ A hA
    rw [biUnion_fin_succ, List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons,
      coeff_mul_of_suppIn (hx 0) (suppIn_prod_ofFn _ _ fun i => hx i.succ) hd,
      coeff_mul_of_suppIn (suppIn_e_self _)
        (suppIn_prod_ofFn _ _ fun i => suppIn_e_self (A i.succ)) hd,
      coeff_prod_ofFn_blocks (fun i => A i.succ) (pairwise_succ A hA) (fun i => x i.succ)
        (fun i => hx i.succ), Fin.prod_univ_succ, coeff_e_self]
    ring

/-- `ω = ±e_A`. -/
def IsSignedBasis (A : Finset Γ) (ω : Grass Γ) : Prop := ω = e A ∨ ω = -e A

theorem isSignedBasis_e (A : Finset Γ) : IsSignedBasis A (e A) := Or.inl rfl

theorem IsSignedBasis.suppIn {A : Finset Γ} {ω : Grass Γ} (h : IsSignedBasis A ω) :
    SuppIn A ω := by
  rcases h with rfl | rfl
  · exact suppIn_e_self A
  · exact (suppIn_e_self A).neg

theorem IsSignedBasis.coeff_mul_self {A : Finset Γ} {ω : Grass Γ} (h : IsSignedBasis A ω) :
    ω.coeff A * ω.coeff A = 1 := by
  rcases h with rfl | rfl <;> simp

theorem IsSignedBasis.neg {A : Finset Γ} {ω : Grass Γ} (h : IsSignedBasis A ω) :
    IsSignedBasis A (-ω) := by
  rcases h with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg _)

theorem IsSignedBasis.mul {A B : Finset Γ} {ω ω' : Grass Γ} (h : IsSignedBasis A ω)
    (h' : IsSignedBasis B ω') (hAB : Disjoint A B) : IsSignedBasis (A ∪ B) (ω * ω') := by
  have key : IsSignedBasis (A ∪ B) (e A * e B) := by
    rw [e_mul_e, if_pos hAB]
    rcases mergeSign_eq_or A B with hs | hs <;> rw [hs]
    · exact Or.inl (one_smul _ _)
    · exact Or.inr (by rw [neg_smul, one_smul])
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl
  · exact key
  · rw [mul_neg]; exact key.neg
  · rw [neg_mul]; exact key.neg
  · rw [neg_mul_neg]; exact key

theorem isSignedBasis_prod_ofFn : ∀ {g : ℕ} (A : Fin g → Finset Γ)
    (_ : Pairwise fun a b => Disjoint (A a) (A b)) (ω : Fin g → Grass Γ)
    (_ : ∀ a, IsSignedBasis (A a) (ω a)),
    IsSignedBasis (univ.biUnion A) (List.ofFn ω).prod
  | 0, A, _, ω, _ => by
    simp only [univ_eq_empty, biUnion_empty, List.ofFn_zero, List.prod_nil]
    exact isSignedBasis_e ∅
  | g + 1, A, hA, ω, hω => by
    rw [biUnion_fin_succ, List.ofFn_succ, List.prod_cons]
    exact (hω 0).mul (isSignedBasis_prod_ofFn (fun i => A i.succ) (pairwise_succ A hA)
      (fun i => ω i.succ) fun i => hω i.succ) (disjoint_zero_biUnion_succ A hA)

/-- The top coefficient `[ω](x)` relative to `ω = ±e_A`: `coeff x A * coeff ω A`. -/
def topCoeff (A : Finset Γ) (ω x : Grass Γ) : ℤ := x.coeff A * ω.coeff A

theorem topCoeff_add (A : Finset Γ) (ω x y : Grass Γ) :
    topCoeff A ω (x + y) = topCoeff A ω x + topCoeff A ω y := by
  simp [topCoeff, add_mul]

theorem topCoeff_zsmul (A : Finset Γ) (ω x : Grass Γ) (n : ℤ) :
    topCoeff A ω (n • x) = n * topCoeff A ω x := by
  rw [topCoeff, topCoeff, coeff_zsmul, mul_assoc]

theorem topCoeff_self {A : Finset Γ} {ω : Grass Γ} (h : IsSignedBasis A ω) :
    topCoeff A ω ω = 1 := h.coeff_mul_self

/-- `x - [ω](x) • ω` has zero `A`-coefficient, i.e. lies in `span{e_S : S ⊊ A}` when
`x ∈ Λ(A)`. -/
theorem coeff_sub_topCoeff_smul {A : Finset Γ} {ω : Grass Γ} (h : IsSignedBasis A ω)
    (x : Grass Γ) : (x - topCoeff A ω x • ω).coeff A = 0 := by
  rw [coeff_sub, coeff_zsmul, topCoeff, mul_assoc, h.coeff_mul_self, mul_one, sub_self]

/-- Uniqueness of `[ω](x)`: if `x - c • ω` has zero `A`-coefficient then `c = [ω](x)`. -/
theorem topCoeff_eq_of_coeff_sub {A : Finset Γ} {ω : Grass Γ} (h : IsSignedBasis A ω)
    {x : Grass Γ} {c : ℤ} (hc : (x - c • ω).coeff A = 0) : topCoeff A ω x = c := by
  rw [coeff_sub, coeff_zsmul, sub_eq_zero] at hc
  rw [topCoeff, hc, mul_assoc, h.coeff_mul_self, mul_one]

/-- **Lemma 2.3 (block factorisation of the top coefficient).** Blocks `A a` pairwise disjoint,
`ω a = ±e_{A a}`, `x a ∈ Λ(A a)`, `Ω = ω_0 ⋯ ω_{g-1}` (which is `±e_{⋃ A}`,
`isSignedBasis_prod_ofFn`). Then `[Ω](x_0 ⋯ x_{g-1}) = Π_a [ω_a](x_a)`. -/
theorem topCoeff_prod_ofFn_blocks {g : ℕ} (A : Fin g → Finset Γ)
    (hA : Pairwise fun a b => Disjoint (A a) (A b)) (ω : Fin g → Grass Γ)
    (hω : ∀ a, IsSignedBasis (A a) (ω a)) (x : Fin g → Grass Γ)
    (hx : ∀ a, SuppIn (A a) (x a)) :
    topCoeff (univ.biUnion A) (List.ofFn ω).prod (List.ofFn x).prod =
      ∏ a, topCoeff (A a) (ω a) (x a) := by
  unfold topCoeff
  rw [coeff_prod_ofFn_blocks A hA x hx, coeff_prod_ofFn_blocks A hA ω (fun a => (hω a).suppIn),
    Finset.prod_mul_distrib]
  have hs := (isSignedBasis_prod_ofFn A hA (fun a => e (A a))
    (fun a => isSignedBasis_e (A a))).coeff_mul_self
  rw [show ∀ s P Q : ℤ, s * P * (s * Q) = (s * s) * (P * Q) from fun _ _ _ => by ring, hs,
    one_mul]

/-- Lemma 2.3 when the blocks cover all generators: `[Ω](x_0 ⋯ x_{g-1}) = Π_a [ω_a](x_a)` with
`Ω = ±e_Γ`. -/
theorem topCoeff_prod_ofFn_blocks_univ {g : ℕ} (A : Fin g → Finset Γ)
    (hA : Pairwise fun a b => Disjoint (A a) (A b)) (hcover : univ.biUnion A = univ)
    (ω : Fin g → Grass Γ) (hω : ∀ a, IsSignedBasis (A a) (ω a)) (x : Fin g → Grass Γ)
    (hx : ∀ a, SuppIn (A a) (x a)) :
    topCoeff univ (List.ofFn ω).prod (List.ofFn x).prod = ∏ a, topCoeff (A a) (ω a) (x a) := by
  rw [← hcover]; exact topCoeff_prod_ofFn_blocks A hA ω hω x hx

/-! ### Linear forms and determinants (Lemma 3.2, step 2) -/

/-- The linear form `Σ_u b u • g u`. -/
def linForm {ι : Type*} [Fintype ι] (g : ι → Grass Γ) (b : ι → ℤ) : Grass Γ := ∑ u, b u • g u

/-- `θ(b) = Σ_γ b γ • γ`. -/
def theta (b : Γ → ℤ) : Grass Γ := linForm gen b

theorem isHomog_linForm {ι : Type*} [Fintype ι] {g : ι → Grass Γ} (hg : ∀ u, IsHomog 1 (g u))
    (b : ι → ℤ) : IsHomog 1 (linForm g b) :=
  isHomog_sum _ _ fun u _ => (hg u).zsmul (b u)

theorem isHomog_theta (b : Γ → ℤ) : IsHomog 1 (theta b) := isHomog_linForm isHomog_gen b

/-- `h · Π_k (a_k + c_k h) = h · Π_k a_k` for odd `h, a_k`. -/
theorem mul_prod_ofFn_absorb (h : Grass Γ) (hh : IsHomog 1 h) : ∀ {K : ℕ}
    (a : Fin K → Grass Γ) (_ : ∀ k, IsHomog 1 (a k)) (c : Fin K → ℤ),
    h * (List.ofFn fun k => a k + c k • h).prod = h * (List.ofFn a).prod
  | 0, _, _, _ => by simp
  | K + 1, a, ha, c => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ (f := a), List.prod_cons, ← mul_assoc,
      mul_add, mul_smul_comm, hh.mul_self_eq_zero, smul_zero, add_zero, hh.anticomm (ha 0),
      neg_mul, mul_assoc,
      mul_prod_ofFn_absorb h hh (fun k => a k.succ) (fun k => ha k.succ) (fun k => c k.succ)]
    conv_rhs => rw [← mul_assoc, hh.anticomm (ha 0), neg_mul, mul_assoc]

/-- Moving `g_i` into position `i`: `g_i · Π_{j ≠ i} g_j = (-1)^i Π_j g_j` for odd `g_j`. -/
theorem mul_prod_ofFn_succAbove : ∀ {K : ℕ} (g : Fin (K + 1) → Grass Γ)
    (_ : ∀ u, IsHomog 1 (g u)) (i : Fin (K + 1)),
    g i * (List.ofFn fun j => g (i.succAbove j)).prod = (-1 : ℤ) ^ (i : ℕ) • (List.ofFn g).prod
  | 0, g, _, i => by
    obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
    simp [List.ofFn_succ]
  | K + 1, g, hg, i => by
    cases i using Fin.cases with
    | zero => simp
    | succ i' =>
      rw [List.ofFn_succ, Fin.succ_succAbove_zero]
      simp only [Fin.succ_succAbove_succ]
      rw [List.prod_cons, ← mul_assoc, (hg _).anticomm (hg 0), neg_mul, mul_assoc,
        mul_prod_ofFn_succAbove (fun j => g j.succ) (fun j => hg j.succ) i',
        List.ofFn_succ (f := g), List.prod_cons, Fin.val_succ, pow_succ, mul_smul_comm,
        mul_neg_one, neg_smul]

/-- **Lemma 3.2, step 2.** For odd `g_0, …, g_{N-1}` (e.g. generators) and an `N × N` integer
matrix `B`, `θ_0 ⋯ θ_{N-1} = det B • g_0 ⋯ g_{N-1}`, where `θ_k = Σ_u B u k • g_u` (the columns
of `B` are the coefficient vectors of the forms). -/
theorem prod_linForm_eq_det : ∀ {N : ℕ} (g : Fin N → Grass Γ) (_ : ∀ u, IsHomog 1 (g u))
    (B : Matrix (Fin N) (Fin N) ℤ),
    (List.ofFn fun k => linForm g fun u => B u k).prod = B.det • (List.ofFn g).prod
  | 0, g, _, B => by simp [Matrix.det_isEmpty]
  | N + 1, g, hg, B => by
    rw [List.ofFn_succ, List.prod_cons, Matrix.det_succ_column_zero, Finset.sum_smul]
    conv_lhs => rw [linForm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc]
    have hsplit : ∀ k : Fin N, (linForm g fun u => B u k.succ) =
        (linForm (fun j => g (i.succAbove j)) fun j => B (i.succAbove j) k.succ) +
          B i k.succ • g i := fun k => by
      rw [linForm, linForm, Fin.sum_univ_succAbove _ i, add_comm]
    simp only [hsplit]
    rw [mul_prod_ofFn_absorb (g i) (hg i) _ (fun k => isHomog_linForm (fun j => hg _) _) _]
    have IH := prod_linForm_eq_det (fun j => g (i.succAbove j)) (fun j => hg _)
      (B.submatrix i.succAbove Fin.succ)
    simp only [Matrix.submatrix_apply] at IH
    rw [IH, mul_smul_comm, mul_prod_ofFn_succAbove g hg i, smul_smul, smul_smul]
    congr 1
    ring

/-- Lemma 3.2 step 2 for generators `ψ_u = gen (ψ u)`, `u : Fin N`:
`Π_k (Σ_u B u k • ψ_u) = det B • ψ_0 ⋯ ψ_{N-1}`. -/
theorem prod_linForm_gen_eq_det {N : ℕ} (ψ : Fin N → Γ) (B : Matrix (Fin N) (Fin N) ℤ) :
    (List.ofFn fun k => linForm (fun u => gen (ψ u)) fun u => B u k).prod =
      B.det • (List.ofFn fun u => gen (ψ u)).prod :=
  prod_linForm_eq_det _ (fun _ => isHomog_gen _) B

end Grass

end EthFollowup.ExactHC
