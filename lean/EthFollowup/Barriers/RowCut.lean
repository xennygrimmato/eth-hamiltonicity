/-
# The row cut of the permanent (`research/permanent/barrier.md` Lemma 3.2)

Source (`barrier.md` §3):

> **Lemma 3.2 (row cut).** Let I ⊆ [n], |I| = k, and let M_I be the matrix indexed by
> X ∈ {0,1}^{I×[n]} (rows I of A) and Y ∈ {0,1}^{([n]∖I)×[n]} with M_I[X,Y] := per(A), A = (X;Y).
> Then rank M_I = C(n,k).
>
> *Proof.* Laplace expansion along the rows I: per(A) = Σ_{S⊆[n], |S|=k} per(X[I,S])·per(Y[I^c,S^c]).
> The functions u_S : X ↦ per(X[I,S]) (|S| = k) are linearly independent: at X = a matching matrix
> of I onto S₀ (one 1 per row, columns S₀), u_S(X) = [S = S₀]. …
>
> Remark. Only the matrices with exactly one 1 per row were used for the lower bound, so Lemma 3.2
> holds for the matrix restricted to that family 𝓕₁ (on which per(A) = [A is a permutation matrix]).

Formalised over an arbitrary field `K` (the source works over ℚ; nothing else is used), with
`[n]` an arbitrary finite type `ι` and Mathlib's `Matrix.permanent`:

* `permanent_joinMat` — the Laplace expansion along the rows `I`, in the form
  `per(A) = Σ_{|S| = k} U_S(X) · V_S(Y)` (with `U_S(X) = per X[I,S]` written as a sum over
  injections `I → ι` with image `S`, and `V_S` likewise over injections `Iᶜ → ι` avoiding `S`);
* `permanent_joinMat_graph` — on one-1-per-row matrices, `per(A) = [A is a permutation matrix]`;
* `rowCut_rank` — **Lemma 3.2 as stated**: `rank M_I = C(n, k)`;
* `rowCut_rank_oneHot` — the Remark: the same rank on the family `𝓕₁`.
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Fintype.Powerset

set_option linter.unusedSectionVars false

namespace EthFollowup.Barriers.RowCut

open Matrix Finset

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] (I : Finset ι)

/-- `A = (X; Y)`: rows in `I` are read from `X`, the other rows from `Y` (0/1 entries). -/
def joinMat (X : {i // i ∈ I} → ι → Bool) (Y : {i // i ∉ I} → ι → Bool) : Matrix ι ι K :=
  fun i j => if h : i ∈ I then (if X ⟨i, h⟩ j then 1 else 0) else (if Y ⟨i, h⟩ j then 1 else 0)

/-- The row-cut matrix `M_I[X,Y] = per(X;Y)` of `barrier.md` Lemma 3.2. -/
noncomputable def rowCutMatrix :
    Matrix ({i // i ∈ I} → ι → Bool) ({i // i ∉ I} → ι → Bool) K :=
  Matrix.of fun X Y => (joinMat (K := K) I X Y).permanent

/-- Gluing `f` on `I` and `g` off `I`. -/
def glue (f : {i // i ∈ I} → ι) (g : {i // i ∉ I} → ι) : ι → ι :=
  fun i => if h : i ∈ I then f ⟨i, h⟩ else g ⟨i, h⟩

/-- `U_S(X) = per X[I,S]`, as a sum over the bijections `I → S`. -/
noncomputable def uS (S : Finset ι) (X : {i // i ∈ I} → ι → Bool) : K :=
  ∑ f : {i // i ∈ I} → ι, if Function.Injective f ∧ univ.image f = S then
    ∏ a, (if X a (f a) then (1 : K) else 0) else 0

/-- `V_S(Y) = per Y[Iᶜ, Sᶜ]`, as a sum over the injections `Iᶜ → ι` avoiding `S`. -/
noncomputable def vS (S : Finset ι) (Y : {i // i ∉ I} → ι → Bool) : K :=
  ∑ g : {i // i ∉ I} → ι, if Function.Injective g ∧ ∀ b, g b ∉ S then
    ∏ b, (if Y b (g b) then (1 : K) else 0) else 0

theorem injective_glue_iff (f : {i // i ∈ I} → ι) (g : {i // i ∉ I} → ι) :
    Function.Injective (glue I f g) ↔
      Function.Injective f ∧ Function.Injective g ∧ ∀ a b, f a ≠ g b := by
  constructor
  · intro h
    refine ⟨fun a a' e => ?_, fun b b' e => ?_, fun a b e => ?_⟩
    · have := @h a a' (by simpa [glue, a.2, a'.2] using e)
      exact Subtype.ext this
    · have := @h b b' (by simpa [glue, b.2, b'.2] using e)
      exact Subtype.ext this
    · have := @h a b (by simpa [glue, a.2, b.2] using e)
      exact b.2 (this ▸ a.2)
  · rintro ⟨hf, hg, hfg⟩ i i' e
    by_cases hi : i ∈ I <;> by_cases hi' : i' ∈ I <;> simp only [glue, hi, hi', dite_true,
      dite_false] at e
    · exact congrArg Subtype.val (hf e)
    · exact absurd e (hfg _ _)
    · exact absurd e.symm (hfg _ _)
    · exact congrArg Subtype.val (hg e)

/-- The indicator of injectivity of the glued map splits over the image `S` of the `I`-part. -/
theorem indicator_injective_glue (f : {i // i ∈ I} → ι) (g : {i // i ∉ I} → ι) :
    (if Function.Injective (glue I f g) then (1 : K) else 0) =
      ∑ S ∈ powersetCard I.card (univ : Finset ι),
        (if Function.Injective f ∧ univ.image f = S then (1 : K) else 0) *
          (if Function.Injective g ∧ ∀ b, g b ∉ S then (1 : K) else 0) := by
  by_cases hf : Function.Injective f
  · have hcard : (univ.image f).card = I.card := by
      rw [card_image_of_injective _ hf, card_univ, Fintype.card_coe]
    rw [Finset.sum_eq_single (univ.image f)]
    · simp only [hf, true_and, ite_true, one_mul, injective_glue_iff]
      congr 1
      apply propext
      constructor
      · rintro ⟨hg, hfg⟩; exact ⟨hg, fun b hb => by
          obtain ⟨a, _, ha⟩ := mem_image.1 hb; exact hfg a b ha⟩
      · rintro ⟨hg, hb⟩; exact ⟨hg, fun a b e => hb b (e ▸ mem_image_of_mem f (mem_univ a))⟩
    · intro S _ hS
      rw [ite_eq_right (fun h => hS h.2.symm), zero_mul]
    · intro h; exact absurd (mem_powersetCard.2 ⟨subset_univ _, hcard⟩) h
  · rw [ite_eq_right (fun h => hf ((injective_glue_iff I f g).1 h).1)]
    simp [hf]

/-- Mathlib's permanent (`Σ_σ Π_i M (σ i) i`) as a sum over injective self-maps, row form. -/
theorem permanent_eq_sum_injective (A : Matrix ι ι K) :
    A.permanent = ∑ h : ι → ι, if Function.Injective h then ∏ i, A i (h i) else 0 := by
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  simp only [Matrix.transpose_apply]
  rw [← Finset.sum_filter]
  let e : Equiv.Perm ι ≃ {h : ι → ι // Function.Injective h} :=
    { toFun := fun σ => ⟨σ, σ.injective⟩
      invFun := fun h => Equiv.ofBijective h.1 (Finite.injective_iff_bijective.1 h.2)
      left_inv := fun σ => by ext; rfl
      right_inv := fun h => by ext; rfl }
  rw [Finset.sum_subtype (univ.filter Function.Injective) (p := fun h : ι → ι => Function.Injective h)
    (f := fun h => ∏ i, A i (h i)) (fun h => by simp)]
  exact Fintype.sum_equiv e _ _ (fun σ => rfl)

/-- **Laplace expansion along the rows `I`** (`barrier.md` Lemma 3.2, proof):
`per(X;Y) = Σ_{S ⊆ ι, |S| = |I|} U_S(X) · V_S(Y)`. -/
theorem permanent_joinMat (X : {i // i ∈ I} → ι → Bool) (Y : {i // i ∉ I} → ι → Bool) :
    (joinMat (K := K) I X Y).permanent =
      ∑ S ∈ powersetCard I.card (univ : Finset ι), uS (K := K) I S X * vS (K := K) I S Y := by
  rw [permanent_eq_sum_injective]
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ I) (fun _ => ι)
  rw [← Fintype.sum_equiv e.symm (fun p => if Function.Injective (glue I p.1 p.2) then
    ∏ i, joinMat (K := K) I X Y i (glue I p.1 p.2 i) else 0) _ (fun p => rfl)]
  rw [Fintype.sum_prod_type]
  have hprod : ∀ f g, ∏ i, joinMat (K := K) I X Y i (glue I f g i) =
      (∏ a, if X a (f a) then (1 : K) else 0) * ∏ b, if Y b (g b) then (1 : K) else 0 := by
    intro f g
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ I)]
    congr 1
    · refine Finset.prod_congr (by ext; simp) fun a _ => ?_
      simp [joinMat, glue, a.2]
    · refine Finset.prod_congr (by ext; simp) fun b _ => ?_
      simp [joinMat, glue, b.2]
  have hterm : ∀ f g, (if Function.Injective (glue I f g) then
      ∏ i, joinMat (K := K) I X Y i (glue I f g i) else 0) =
      ∑ S ∈ powersetCard I.card (univ : Finset ι),
        (if Function.Injective f ∧ univ.image f = S then
          ∏ a, (if X a (f a) then (1 : K) else 0) else 0) *
        (if Function.Injective g ∧ ∀ b, g b ∉ S then
          ∏ b, (if Y b (g b) then (1 : K) else 0) else 0) := by
    intro f g
    rw [hprod]
    calc _ = (if Function.Injective (glue I f g) then (1 : K) else 0) *
          ((∏ a, if X a (f a) then (1 : K) else 0) * ∏ b, if Y b (g b) then (1 : K) else 0) := by
            split_ifs <;> simp
      _ = _ := by
        rw [indicator_injective_glue, Finset.sum_mul]
        refine Finset.sum_congr rfl fun S _ => ?_
        split_ifs <;> simp
  simp_rw [hterm]
  simp only [uS, vS, Finset.sum_mul_sum]
  exact (Finset.sum_congr rfl fun f _ => Finset.sum_comm).trans Finset.sum_comm

/-! ### One-1-per-row matrices -/

/-- The 0/1 matrix with a single `1` per row, at column `f a` (a "matching matrix" when `f` is
injective). -/
def graphB {α : Type*} (f : α → ι) : α → ι → Bool := fun a j => decide (f a = j)

theorem prod_graphB {α : Type*} [Fintype α] (f f' : α → ι) :
    (∏ a, if graphB f a (f' a) then (1 : K) else 0) = if f' = f then 1 else 0 := by
  simp only [graphB, decide_eq_true_eq]
  rw [Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h; funext a; exact (h a).symm
  · rintro rfl a; rfl

theorem uS_graph (S : Finset ι) (f : {i // i ∈ I} → ι) :
    uS (K := K) I S (graphB f) = if Function.Injective f ∧ univ.image f = S then 1 else 0 := by
  unfold uS
  simp_rw [prod_graphB]
  rw [Finset.sum_eq_single f]
  · by_cases h : Function.Injective f ∧ univ.image f = S <;> simp only [h, ite_true, ite_false]
  · intro f' _ hf'; simp [hf']
  · simp

theorem vS_graph (S : Finset ι) (g : {i // i ∉ I} → ι) :
    vS (K := K) I S (graphB g) = if Function.Injective g ∧ ∀ b, g b ∉ S then 1 else 0 := by
  unfold vS
  simp_rw [prod_graphB]
  rw [Finset.sum_eq_single g]
  · by_cases h : Function.Injective g ∧ ∀ b, g b ∉ S <;> simp only [h, ite_true, ite_false]
  · intro g' _ hg'; simp [hg']
  · simp

/-- The Remark of `barrier.md` Lemma 3.2: on one-1-per-row matrices,
`per(A) = [A is a permutation matrix]`. -/
theorem permanent_joinMat_graph (f : {i // i ∈ I} → ι) (g : {i // i ∉ I} → ι) :
    (joinMat (K := K) I (graphB f) (graphB g)).permanent =
      if Function.Injective (glue I f g) then 1 else 0 := by
  rw [permanent_joinMat, indicator_injective_glue]
  simp_rw [uS_graph, vS_graph]

/-! ### The witnesses: matching matrices of `I` onto `S` and of `Iᶜ` onto `Sᶜ` -/

/-- The `k`-subsets of `ι`, `k = |I|`. -/
abbrev Ksub := {S : Finset ι // S ∈ powersetCard I.card (univ : Finset ι)}

theorem card_Ksub : Fintype.card (Ksub I) = (Fintype.card ι).choose I.card := by
  rw [Fintype.card_coe, card_powersetCard, card_univ]

theorem card_in_eq (S : Ksub I) : Fintype.card {i // i ∈ I} = Fintype.card {j // j ∈ S.1} := by
  rw [Fintype.card_coe, Fintype.card_coe, (mem_powersetCard.1 S.2).2]

theorem card_out_eq (S : Ksub I) :
    Fintype.card {i // i ∉ I} = Fintype.card {j // j ∉ S.1} := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_coe,
    (mem_powersetCard.1 S.2).2]

/-- A bijection `I → S`. -/
noncomputable def fS (S : Ksub I) : {i // i ∈ I} → ι :=
  fun a => (Fintype.equivOfCardEq (card_in_eq I S) a).1

/-- A bijection `Iᶜ → Sᶜ`. -/
noncomputable def gS (S : Ksub I) : {i // i ∉ I} → ι :=
  fun b => (Fintype.equivOfCardEq (card_out_eq I S) b).1

theorem fS_injective (S : Ksub I) : Function.Injective (fS I S) :=
  fun _ _ h => (Fintype.equivOfCardEq (card_in_eq I S)).injective (Subtype.ext h)

theorem gS_injective (S : Ksub I) : Function.Injective (gS I S) :=
  fun _ _ h => (Fintype.equivOfCardEq (card_out_eq I S)).injective (Subtype.ext h)

theorem fS_mem (S : Ksub I) (a) : fS I S a ∈ S.1 :=
  (Fintype.equivOfCardEq (card_in_eq I S) a).2

theorem fS_surj (S : Ksub I) {j : ι} (hj : j ∈ S.1) : ∃ a, fS I S a = j :=
  ⟨(Fintype.equivOfCardEq (card_in_eq I S)).symm ⟨j, hj⟩, by simp [fS]⟩

theorem gS_not_mem (S : Ksub I) (b) : gS I S b ∉ S.1 :=
  (Fintype.equivOfCardEq (card_out_eq I S) b).2

theorem gS_surj (S : Ksub I) {j : ι} (hj : j ∉ S.1) : ∃ b, gS I S b = j :=
  ⟨(Fintype.equivOfCardEq (card_out_eq I S)).symm ⟨j, hj⟩, by simp [gS]⟩

theorem injective_glue_witness_iff (S S' : Ksub I) :
    Function.Injective (glue I (fS I S) (gS I S')) ↔ S = S' := by
  rw [injective_glue_iff]
  simp only [fS_injective, gS_injective, true_and]
  constructor
  · intro h
    have hsub : S.1 ⊆ S'.1 := by
      intro j hj
      by_contra hj'
      obtain ⟨a, ha⟩ := fS_surj I S hj
      obtain ⟨b, hb⟩ := gS_surj I S' hj'
      exact h a b (ha.trans hb.symm)
    refine Subtype.ext (Finset.eq_of_subset_of_card_le hsub ?_)
    rw [(mem_powersetCard.1 S.2).2, (mem_powersetCard.1 S'.2).2]
  · rintro rfl a b e
    exact gS_not_mem I S b (e ▸ fS_mem I S a)

/-! ### Lemma 3.2 -/

/-- Local copy of the cut lemma (`RankBounds.rank_le_card_of_eq_sum_mul'`), kept here so that
this file does not depend on another new module. -/
theorem rank_le_card_of_eq_sum_mul_finset {X Y Θ : Type*} [Fintype Y] (s : Finset Θ)
    (M : Matrix X Y K) (F : X → Θ → K) (G : Θ → Y → K)
    (h : ∀ x y, M x y = ∑ θ ∈ s, F x θ * G θ y) : M.rank ≤ s.card := by
  have hM : M = Matrix.of (fun x (θ : s) => F x θ) * Matrix.of (fun (θ : s) y => G θ y) := by
    ext x y; simp [Matrix.mul_apply, h, ← Finset.sum_coe_sort s]
  rw [hM]
  exact (rank_mul_le_left _ _).trans ((rank_le_card_width _).trans (by simp))

/-- The identity submatrix: `M_I[X_S, Y_{S'}] = [S = S']` at the matching matrices. -/
theorem rowCutMatrix_witness (S S' : Ksub I) :
    rowCutMatrix (K := K) I (graphB (fS I S)) (graphB (gS I S')) = if S = S' then 1 else 0 := by
  simp only [rowCutMatrix, Matrix.of_apply, permanent_joinMat_graph, injective_glue_witness_iff]

/-- **`barrier.md` Lemma 3.2 (row cut)**: `rank M_I = C(n, k)` with `n = |ι|`, `k = |I|`. -/
theorem rowCut_rank : (rowCutMatrix (K := K) I).rank = (Fintype.card ι).choose I.card := by
  apply le_antisymm
  · have := rank_le_card_of_eq_sum_mul_finset (powersetCard I.card (univ : Finset ι))
      (rowCutMatrix (K := K) I) (fun X S => uS I S X) (fun S Y => vS I S Y)
      (fun X Y => by simp only [rowCutMatrix, Matrix.of_apply, permanent_joinMat])
    rwa [card_powersetCard, card_univ] at this
  · have hsub : (rowCutMatrix (K := K) I).submatrix (fun S : Ksub I => graphB (fS I S))
        (fun S : Ksub I => graphB (gS I S)) = 1 := by
      ext S S'
      rw [Matrix.submatrix_apply, rowCutMatrix_witness, Matrix.one_apply]
    rw [← card_Ksub I, ← Matrix.rank_one (R := K) (n := Ksub I), ← hsub]
    exact Matrix.rank_submatrix_le _ _ _

/-- The matrix of the Remark: `M_I` restricted to the family `𝓕₁` of one-1-per-row matrices,
indexed by the maps `f : I → ι`, `g : Iᶜ → ι` giving the positions of the `1`s. -/
noncomputable def rowCutMatrixOneHot : Matrix ({i // i ∈ I} → ι) ({i // i ∉ I} → ι) K :=
  Matrix.of fun f g => (joinMat (K := K) I (graphB f) (graphB g)).permanent

/-- **`barrier.md` Lemma 3.2, Remark**: the rank is still `C(n, k)` on `𝓕₁`. -/
theorem rowCut_rank_oneHot :
    (rowCutMatrixOneHot (K := K) I).rank = (Fintype.card ι).choose I.card := by
  apply le_antisymm
  · have : rowCutMatrixOneHot (K := K) I = (rowCutMatrix (K := K) I).submatrix graphB graphB := by
      ext f g; rfl
    rw [this, ← rowCut_rank (K := K) I]
    exact Matrix.rank_submatrix_le _ _ _
  · have hsub : (rowCutMatrixOneHot (K := K) I).submatrix (fun S : Ksub I => fS I S)
        (fun S : Ksub I => gS I S) = 1 := by
      ext S S'
      rw [Matrix.submatrix_apply, Matrix.one_apply]
      exact rowCutMatrix_witness I S S'
    rw [← card_Ksub I, ← Matrix.rank_one (R := K) (n := Ksub I), ← hsub]
    exact Matrix.rank_submatrix_le _ _ _

end EthFollowup.Barriers.RowCut
