/-
# The directed fermionic matrix-tree theorem (TSP-2, `research/tsp-theorem.md` §3.1)

A digraph is a finite set `A : Finset (Fin n × Fin n)` of arcs `(i, j) = i → j`, as in
`EthFollowup/DirectedHamiltonianParity.lean`, whose `CycleCover`, `cycleCovers` and `dirHamCycles`
(cycle covers whose underlying undirected graph is connected) are used unchanged. Loops are
allowed throughout (they never lie on a directed Hamiltonian cycle when `n ≥ 2`, and every
statement below holds with them). The generators are those of `Fermion.lean` (`ψ̄_r = ψ_r = 0`).

## Definitions
* `pArc r a = ψ̄_i (ψ_i − ψ_j)` for `a = (i, j)`; `arcProd r F = Π_{a∈F}(1 + p_a)` (ordered along
  `F.toList`; the factors are even, so the order is irrelevant, `arcProd_eq_coe_prod`).
* `outArcs F v` (arcs with tail `v`), `lapOut F = D_out − A_F` (the out-degree Laplacian, row `i`:
  out-degree on the diagonal, `−1` in column `j` for the arc `i → j`), `lapOutRed F r` its reduced
  form (row and column `r` deleted).
* `IsInArb r F`: every `v ≠ r` has exactly one out-arc in `F`, `r` has none, and every vertex
  reaches `r` along arcs of `F` (an in-arborescence towards `r`); `inArbs r F` the in-arborescences
  contained in `F`.
* `arcWt w X = Σ_{a∈X} w a`.

## Results
* `MatrixTree.berezin₂`, `berezin₂_topV` (**Lemma 3.1**, two-matrix Berezin form):
  `[Ω_V](θ̄(b_1)θ(c_1) ⋯ θ̄(b_N)θ(c_N)) = det B · det C`.
* `topV_arcProd_eq_det`: `[Ω_V] Π_{a∈F}(1 + p_a) = det L_out(F)^{(r)}` (Berezin form of the
  Laplacian determinant; proved by grouping the arcs by their tail, which needs no
  Cauchy–Binet).
* `det_lapOutRed_of_card`: for `|F| = n − 1`, `det L_out(F)^{(r)} = [F is an in-arborescence]`.
* `topV_arcProd` and `det_lapOutRed_eq_card_inArbs` (**Lemma 3.2**):
  `[Ω_V] Π_{a∈F}(1 + p_a) = det L_out(F)^{(r)} = #{in-arborescences towards r contained in F}`.
* `card_inArbs_of_connected`, `card_inArbs_of_not_connected`, `det_lapOutRed_cycleCover`
  (**Lemma 3.3**, first part): for a cycle cover `X`, the count is `1` if `X` is a directed
  Hamiltonian cycle and `0` otherwise.
* `sum_dirHamCycles_pow_eq`, `sum_dirHamCycles_pow_eq_det`, `card_dirHamCycles_eq_sum`
  (**Lemma 3.3**): `Σ_{H ∈ DHC(A)} z^{w(H)} = Σ_{X cycle cover} z^{w(X)} [Ω_V] Π_{a∈X}(1 + p_a)
  = Σ_X z^{w(X)} det L_out(X)^{(r)}`, with no factor `n`.
-/
import EthFollowup.ExactHC.MatrixTree
import EthFollowup.DirectedHamiltonianParity

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset Grass MatrixTree

/-! ### Lemma 3.1: the two-matrix Berezin form -/

namespace MatrixTree

section Berezin₂

variable {Γ : Type*} [Fintype Γ] [LinearOrder Γ]

/-- **Lemma 3.1 (two-matrix Berezin form)**, algebraic form: for odd `ḡ_u, g_u` (`u : Fin N`)
and integer matrices `B, C` with columns `b_k, c_k`,
`Π_k θ̄(b_k) θ(c_k) = (det B · det C) • Π_u ḡ_u g_u`. -/
theorem berezin₂ {N : ℕ} (gb g : Fin N → Grass Γ) (hgb : ∀ u, IsHomog 1 (gb u))
    (hg : ∀ u, IsHomog 1 (g u)) (B C : Matrix (Fin N) (Fin N) ℤ) :
    (List.ofFn fun k => linForm gb (fun u => B u k) * linForm g (fun u => C u k)).prod =
      (B.det * C.det) • (List.ofFn fun u => gb u * g u).prod := by
  rw [prod_mul_pairs _ _ (fun k => isHomog_linForm hgb _) (fun k => isHomog_linForm hg _),
    prod_linForm_eq_det gb hgb B, prod_linForm_eq_det g hg C, prod_mul_pairs gb g hgb hg,
    smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

end Berezin₂

end MatrixTree

noncomputable section

variable {n : ℕ}

/-- **Lemma 3.1** for the fermion generators: enumerate `V ∖ {r}` by any
`ν : Fin (n - 1) ≃ {u // u ≠ r}`; then
`[Ω_V](θ̄(b_1)θ(c_1) ⋯ θ̄(b_N)θ(c_N)) = det B · det C`. -/
theorem berezin₂_topV (r : Fin n) (ν : Fin (n - 1) ≃ {u : Fin n // u ≠ r})
    (B C : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ) :
    topV r (List.ofFn fun k => linForm (fun j => psibar r (ν j)) (fun j => B j k) *
      linForm (fun j => psi r (ν j)) (fun j => C j k)).prod = B.det * C.det := by
  rw [berezin₂ _ _ (fun _ => mt_isHomog_psibar _ _) (fun _ => mt_isHomog_psi _ _) B C, topV_zsmul,
    show (List.ofFn fun u => psibar r (ν u) * psi r (ν u)) = List.ofFn fun u => omega r (ν u)
      from rfl, prod_ofFn_omega_eq_OmegaSet, topV_OmegaSet, mul_one]

/-! ### Arc factors -/

/-- `p_a = ψ̄_i (ψ_i − ψ_j)` for the arc `a = (i, j)`. -/
def pArc (r : Fin n) (a : Fin n × Fin n) : Grass (Fin (2 * n)) :=
  psibar r a.1 * (psi r a.1 - psi r a.2)

theorem isDeg_pArc (r : Fin n) (a : Fin n × Fin n) : IsDeg 2 (pArc r a) :=
  (isDeg_psibar r a.1).mul ((isDeg_psi r a.1).sub (isDeg_psi r a.2))

/-- `p_a` as an element of the centre. -/
noncomputable def pC (r : Fin n) (a : Fin n × Fin n) : Subring.center (Grass (Fin (2 * n))) :=
  ⟨pArc r a, mem_center_of_even (isHomog_even_of_isDeg_two (isDeg_pArc r a))⟩

@[simp] theorem coe_pC (r : Fin n) (a : Fin n × Fin n) :
    (pC r a : Grass (Fin (2 * n))) = pArc r a := rfl

/-- `Π_{a∈F} (1 + p_a)`, ordered along `F.toList`. -/
def arcProd (r : Fin n) (F : Finset (Fin n × Fin n)) : Grass (Fin (2 * n)) :=
  (F.toList.map fun a => 1 + pArc r a).prod

/-- `Π_{a∈F}(1 + p_a)` is a product in the commutative centre: the order does not matter. -/
theorem arcProd_eq_coe_prod (r : Fin n) (F : Finset (Fin n × Fin n)) :
    arcProd r F = ((∏ a ∈ F, (1 + pC r a) : Subring.center (Grass (Fin (2 * n))))) := by
  rw [arcProd, ← Finset.prod_map_toList, coe_list_prod_map]
  rfl

/-- `p_a = 0` for an arc with tail `r`. -/
theorem pArc_of_tail_root (r : Fin n) {a : Fin n × Fin n} (h : a.1 = r) : pArc r a = 0 := by
  rw [pArc, h, psibar_root, zero_mul]

/-- `p_a p_b = 0` for two arcs with the same tail (`ψ̄_i² = 0`). -/
theorem pArc_mul_pArc_of_tail_eq (r : Fin n) {a b : Fin n × Fin n} (h : a.1 = b.1) :
    pArc r a * pArc r b = 0 := by
  unfold pArc
  rw [h]
  have hψ := mt_isHomog_psibar r b.1
  have hx : IsHomog 1 (psi r b.1 - psi r a.2) := (mt_isHomog_psi _ _).sub (mt_isHomog_psi _ _)
  have e1 : psibar r b.1 * (psi r b.1 - psi r a.2) * (psibar r b.1 * (psi r b.1 - psi r b.2)) =
      psibar r b.1 * ((psi r b.1 - psi r a.2) * psibar r b.1) * (psi r b.1 - psi r b.2) := by
    simp only [mul_assoc]
  rw [e1, hx.anticomm hψ, mul_neg, neg_mul, ← mul_assoc, hψ.mul_self_eq_zero, zero_mul, zero_mul,
    neg_zero]

/-- In a commutative ring, `Π_{a∈s}(1 + f a) = 1 + Σ_{a∈s} f a` if all products `f a f b` vanish. -/
theorem prod_one_add_of_mul_eq_zero {R ι : Type*} [CommRing R] [DecidableEq ι] (s : Finset ι)
    (f : ι → R) (h : ∀ a ∈ s, ∀ b ∈ s, f a * f b = 0) :
    ∏ a ∈ s, (1 + f a) = 1 + ∑ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
    rw [prod_insert hc, sum_insert hc,
      ih (fun a ha b hb => h a (mem_insert_of_mem ha) b (mem_insert_of_mem hb))]
    have : f c * ∑ a ∈ s, f a = 0 := by
      rw [mul_sum]
      exact sum_eq_zero fun b hb => h c (mem_insert_self c s) b (mem_insert_of_mem hb)
    linear_combination this

/-! ### The out-degree Laplacian -/

/-- The arcs of `F` with tail `v`. -/
def outArcs (F : Finset (Fin n × Fin n)) (v : Fin n) : Finset (Fin n × Fin n) :=
  F.filter fun a => a.1 = v

theorem mem_outArcs {F : Finset (Fin n × Fin n)} {v : Fin n} {a : Fin n × Fin n} :
    a ∈ outArcs F v ↔ a ∈ F ∧ a.1 = v := mem_filter

/-- The out-degree Laplacian `L_out(F) = D_out − A_F`. -/
def lapOut (F : Finset (Fin n × Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    (if i = j then ((outArcs F i).card : ℤ) else 0) - (if (i, j) ∈ F then 1 else 0)

/-- The reduced Laplacian `L_out(F)^{(r)}` (row and column `r` deleted). -/
def lapOutRed (F : Finset (Fin n × Fin n)) (r : Fin n) :
    Matrix {u : Fin n // u ≠ r} {u : Fin n // u ≠ r} ℤ :=
  (lapOut F).submatrix Subtype.val Subtype.val

@[simp] theorem lapOutRed_apply (F : Finset (Fin n × Fin n)) (r : Fin n)
    (u v : {u : Fin n // u ≠ r}) : lapOutRed F r u v = lapOut F u.1 v.1 := rfl

/-- Row `i` of `L_out(F)` applied to a vector: `Σ_j L_{ij} g_j = Σ_{a=(i,j)∈F} (g_i − g_j)`. -/
theorem sum_lapOut_smul {M : Type*} [AddCommGroup M] (F : Finset (Fin n × Fin n)) (i : Fin n)
    (g : Fin n → M) : ∑ j, lapOut F i j • g j = ∑ a ∈ outArcs F i, (g i - g a.2) := by
  have h2 : ∑ a ∈ outArcs F i, g a.2 = ∑ j ∈ univ.filter (fun j => (i, j) ∈ F), g j := by
    rw [← Finset.sum_image (s := outArcs F i) (g := Prod.snd) (f := g)]
    · congr 1
      ext j
      simp only [mem_image, mem_outArcs, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨a, ⟨ha, rfl⟩, rfl⟩
        exact ha
      · intro h
        exact ⟨(i, j), ⟨h, rfl⟩, rfl⟩
    · intro a ha b hb hab
      exact Prod.ext ((mem_outArcs.1 ha).2.trans (mem_outArcs.1 hb).2.symm) hab
  simp only [lapOut, Matrix.of_apply, sub_smul, ite_smul, zero_smul, one_smul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, sum_const, h2,
    sum_filter, natCast_zsmul]

/-! ### Lemma 3.2, Laplacian form: `[Ω_V] Π_{a∈F}(1 + p_a) = det L_out(F)^{(r)}` -/

/-- `ℓ_i = Σ_{a=(i,j)∈F} (ψ_i − ψ_j)`. -/
def ellOut (r : Fin n) (F : Finset (Fin n × Fin n)) (i : Fin n) : Grass (Fin (2 * n)) :=
  ∑ a ∈ outArcs F i, (psi r i - psi r a.2)

theorem isDeg_ellOut (r : Fin n) (F : Finset (Fin n × Fin n)) (i : Fin n) :
    IsDeg 1 (ellOut r F i) :=
  isDeg_sum _ _ fun a _ => (isDeg_psi r i).sub (isDeg_psi r a.2)

/-- `Σ_{a ∈ outArcs F i} p_a`, in the centre. -/
noncomputable def yC (r : Fin n) (F : Finset (Fin n × Fin n)) (i : Fin n) :
    Subring.center (Grass (Fin (2 * n))) :=
  ∑ a ∈ outArcs F i, pC r a

theorem coe_yC (r : Fin n) (F : Finset (Fin n × Fin n)) (i : Fin n) :
    (yC r F i : Grass (Fin (2 * n))) = psibar r i * ellOut r F i := by
  rw [yC, coe_finset_sum, ellOut, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [coe_pC, pArc, (mem_outArcs.1 ha).2]

theorem isDeg_yC (r : Fin n) (F : Finset (Fin n × Fin n)) (i : Fin n) :
    IsDeg 2 (yC r F i : Grass (Fin (2 * n))) := by
  rw [coe_yC]
  exact (isDeg_psibar r i).mul (isDeg_ellOut r F i)

theorem yC_root (r : Fin n) (F : Finset (Fin n × Fin n)) : yC r F r = 0 :=
  Subtype.ext (by rw [coe_yC, psibar_root, zero_mul]; rfl)

/-- Grouping the arcs by their tail: `Π_{a∈F}(1 + p_a) = Π_i (1 + ψ̄_i ℓ_i)`. -/
theorem arcProd_eq_prod_yC (r : Fin n) (F : Finset (Fin n × Fin n)) :
    arcProd r F = ((∏ i, (1 + yC r F i) : Subring.center (Grass (Fin (2 * n))))) := by
  rw [arcProd_eq_coe_prod, ← prod_fiberwise F (fun a => a.1)]
  congr 1
  refine prod_congr rfl fun i _ => prod_one_add_of_mul_eq_zero _ _ fun a ha b hb => ?_
  apply Subtype.ext
  rw [Subring.coe_mul, coe_pC, coe_pC]
  exact pArc_mul_pArc_of_tail_eq r ((mem_filter.1 ha).2.trans (mem_filter.1 hb).2.symm)

/-- **Berezin form of the reduced Laplacian determinant**:
`[Ω_V] Π_{a∈F}(1 + p_a) = det L_out(F)^{(r)}`. -/
theorem topV_arcProd_eq_det (r : Fin n) (F : Finset (Fin n × Fin n)) :
    topV r (arcProd r F) = (lapOutRed F r).det := by
  classical
  let ν : Fin (n - 1) ≃ {u : Fin n // u ≠ r} := (Fintype.equivFinOfCardEq (card_ne_root r)).symm
  -- drop the root factor and expand
  rw [arcProd_eq_prod_yC, ← prod_erase univ (a := r) (by rw [yC_root, add_zero]),
    Finset.prod_one_add, coe_finset_sum, topV_sum,
    Finset.sum_eq_single (univ.erase r)]
  rotate_left
  · intro t ht hne
    have hdeg := isDeg_coe_prod t (yC r F) (fun i => isDeg_yC r F i)
    have hlt : t.card < n - 1 := by
      have h1 := card_lt_card (lt_of_le_of_ne (mem_powerset.1 ht) hne)
      rwa [card_erase_of_mem (mem_univ r), card_univ, Fintype.card_fin] at h1
    unfold topV topCoeff
    rw [hdeg.coeff_eq_zero (by rw [card_genSet_univ]; omega), zero_mul]
  · intro h
    exact absurd (mem_powerset.2 subset_rfl) h
  -- the full term
  let C : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ := ((lapOutRed F r).submatrix ν ν).transpose
  have hC : C.det = (lapOutRed F r).det := by
    rw [Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
  have hprod : ((∏ i ∈ univ.erase r, yC r F i : Subring.center (Grass (Fin (2 * n)))) :
      Grass (Fin (2 * n))) = (List.ofFn fun k =>
        linForm (fun j => psibar r (ν j)) (fun j => (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ) j k) *
        linForm (fun j => psi r (ν j)) (fun j => C j k)).prod := by
    rw [Finset.prod_subtype (univ.erase r) (p := fun u => u ≠ r) (fun u => by simp),
      ← Equiv.prod_comp ν, coe_prod_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    rw [coe_yC]
    congr 1
    · simp only [linForm, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        sum_ite_eq', mem_univ, if_true]
    · rw [ellOut, ← sum_lapOut_smul F (ν k).1 (psi r),
        sum_smul_eq_sum_fin r ν _ _ (psi_root r)]
      rfl
  rw [hprod, berezin₂_topV, Matrix.det_one, one_mul, hC]

/-! ### Subsets of size `n − 1` -/

/-- `Π_{a∈S} p_a`, a product in the centre. -/
noncomputable def pProd (r : Fin n) (S : Finset (Fin n × Fin n)) : Grass (Fin (2 * n)) :=
  ((∏ a ∈ S, pC r a : Subring.center (Grass (Fin (2 * n)))))

theorem topV_pProd_of_card_ne (r : Fin n) {S : Finset (Fin n × Fin n)} (hS : S.card ≠ n - 1) :
    topV r (pProd r S) = 0 := by
  have hdeg : IsDeg (S.card * 2) (pProd r S) := isDeg_coe_prod S (pC r) fun a => isDeg_pArc r a
  unfold topV topCoeff
  rw [hdeg.coeff_eq_zero (by rw [card_genSet_univ]; omega), zero_mul]

/-- Only the subsets of size `n − 1` contribute: `[Ω_V] Π_{a∈F}(1 + p_a) = Σ_{|S| = n−1} [Ω_V] Π_S p_a`. -/
theorem topV_arcProd_eq_sum (r : Fin n) (F : Finset (Fin n × Fin n)) :
    topV r (arcProd r F) = ∑ S ∈ F.powersetCard (n - 1), topV r (pProd r S) := by
  rw [arcProd_eq_coe_prod, Finset.prod_one_add, coe_finset_sum, topV_sum]
  exact (Finset.sum_subset (fun t ht => mem_powerset.2 (mem_powersetCard.1 ht).1)
    (fun t ht ht' => topV_pProd_of_card_ne r fun hc =>
      ht' (mem_powersetCard.2 ⟨mem_powerset.1 ht, hc⟩))).symm

theorem topV_pProd_eq_det (r : Fin n) {S : Finset (Fin n × Fin n)} (hS : S.card = n - 1) :
    topV r (pProd r S) = (lapOutRed S r).det := by
  rw [← topV_arcProd_eq_det, topV_arcProd_eq_sum, ← hS, powersetCard_self, sum_singleton]

/-! ### In-arborescences -/

/-- `F` is an in-arborescence towards `r`: every `v ≠ r` has exactly one out-arc in `F`, `r` has
none, and every vertex reaches `r` along arcs of `F`. -/
def IsInArb (r : Fin n) (F : Finset (Fin n × Fin n)) : Prop :=
  (∀ v, v ≠ r → (outArcs F v).card = 1) ∧ (∀ a ∈ F, a.1 ≠ r) ∧
    ∀ v, Relation.ReflTransGen (fun u w => (u, w) ∈ F) v r

/-- The in-arborescences towards `r` contained in `F`. -/
noncomputable def inArbs (r : Fin n) (F : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n × Fin n)) := by
  classical exact F.powerset.filter (IsInArb r)

theorem mem_inArbs {r : Fin n} {F T : Finset (Fin n × Fin n)} :
    T ∈ inArbs r F ↔ T ⊆ F ∧ IsInArb r T := by
  classical
  simp [inArbs]

/-- `Σ_v outdeg(v) = |F|`. -/
theorem sum_card_outArcs (F : Finset (Fin n × Fin n)) : ∑ v, (outArcs F v).card = F.card :=
  (card_eq_sum_card_fiberwise (f := fun a : Fin n × Fin n => a.1) (s := F) (t := univ)
    (fun _ _ => mem_univ _)).symm

theorem card_of_isInArb {r : Fin n} {F : Finset (Fin n × Fin n)} (h : IsInArb r F) :
    F.card = n - 1 := by
  have h0 : (outArcs F r).card = 0 :=
    card_eq_zero.2 (filter_eq_empty_iff.2 fun a ha => h.2.1 a ha)
  rw [← sum_card_outArcs, ← add_sum_erase _ _ (mem_univ r), h0, zero_add,
    sum_congr rfl fun v hv => h.1 v (ne_of_mem_erase hv), sum_const, smul_eq_mul, mul_one,
    card_erase_of_mem (mem_univ r), card_univ, Fintype.card_fin]

section Functional

variable {r : Fin n} {S : Finset (Fin n × Fin n)}

/-- With `n − 1` arcs and an out-arc at every `v ≠ r`: exactly one at each `v ≠ r`, none at `r`. -/
theorem functional_of_card (hS : S.card = n - 1) (h : ∀ v, v ≠ r → (outArcs S v).card ≠ 0) :
    (∀ v, v ≠ r → (outArcs S v).card = 1) ∧ ∀ a ∈ S, a.1 ≠ r := by
  have hsum := sum_card_outArcs S
  rw [← add_sum_erase _ _ (mem_univ r), hS] at hsum
  have hge : ∑ v ∈ univ.erase r, 1 ≤ ∑ v ∈ univ.erase r, (outArcs S v).card :=
    sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.2 (h v (ne_of_mem_erase hv))
  have hcard : ∑ v ∈ univ.erase r, 1 = n - 1 := by
    rw [sum_const, smul_eq_mul, mul_one, card_erase_of_mem (mem_univ r), card_univ,
      Fintype.card_fin]
  have hr : (outArcs S r).card = 0 := by omega
  have heq : ∑ v ∈ univ.erase r, 1 = ∑ v ∈ univ.erase r, (outArcs S v).card := by omega
  refine ⟨fun v hv => ?_, fun a ha har => ?_⟩
  · exact ((sum_eq_sum_iff_of_le fun v hv =>
      Nat.one_le_iff_ne_zero.2 (h v (ne_of_mem_erase hv))).1 heq v (mem_erase.2 ⟨hv, mem_univ v⟩)).symm
  · have : a ∈ outArcs S r := mem_outArcs.2 ⟨ha, har⟩
    rw [card_eq_zero.1 hr] at this
    exact notMem_empty a this

variable (hf : ∀ v, v ≠ r → (outArcs S v).card = 1)
include hf

theorem exists_out_of_functional {v : Fin n} (hv : v ≠ r) : ∃ w, (v, w) ∈ S := by
  obtain ⟨a, ha⟩ := card_pos.1 (by rw [hf v hv]; exact one_pos)
  obtain ⟨ha1, ha2⟩ := mem_outArcs.1 ha
  exact ⟨a.2, by rw [← ha2]; exact ha1⟩

theorem out_unique_of_functional {v w w' : Fin n} (hv : v ≠ r) (h : (v, w) ∈ S)
    (h' : (v, w') ∈ S) : w = w' := by
  have := card_le_one.1 (hf v hv).le (v, w) (mem_outArcs.2 ⟨h, rfl⟩) (v, w')
    (mem_outArcs.2 ⟨h', rfl⟩)
  exact (Prod.ext_iff.1 this).2

omit hf in
/-- The parent of `v`: the head of its out-arc (and `r` for `r` and for vertices without one). -/
noncomputable def par (S : Finset (Fin n × Fin n)) (r v : Fin n) : Fin n := by
  classical exact if h : v ≠ r ∧ ∃ w, (v, w) ∈ S then h.2.choose else r

theorem par_mem {v : Fin n} (hv : v ≠ r) : (v, par S r v) ∈ S := by
  classical
  have h : v ≠ r ∧ ∃ w, (v, w) ∈ S := ⟨hv, exists_out_of_functional hf hv⟩
  unfold par
  rw [dif_pos h]
  exact h.2.choose_spec

theorem eq_par {v w : Fin n} (hv : v ≠ r) (h : (v, w) ∈ S) : w = par S r v :=
  out_unique_of_functional hf hv h (par_mem hf hv)

theorem lapOut_functional {v : Fin n} (hv : v ≠ r) (u : Fin n) :
    lapOut S v u = (if v = u then 1 else 0) - (if u = par S r v then 1 else 0) := by
  simp only [lapOut, Matrix.of_apply, hf v hv, Nat.cast_one]
  congr 1
  by_cases hu : u = par S r v
  · rw [if_pos hu, if_pos (hu ▸ par_mem hf hv)]
  · rw [if_neg hu, if_neg fun h => hu (eq_par hf hv h)]

/-- Reaching the root, for a functional arc set: `v` reaches `r` iff its parent does (`v ≠ r`). -/
theorem reach_iff_par {v : Fin n} (hv : v ≠ r) :
    Relation.ReflTransGen (fun u w => (u, w) ∈ S) v r ↔
      Relation.ReflTransGen (fun u w => (u, w) ∈ S) (par S r v) r := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, hcr⟩
    · exact absurd h hv
    · rwa [← eq_par hf hv hc]
  · exact Relation.ReflTransGen.head (par_mem hf hv)

theorem iterate_par_of_reach (har : ∀ a ∈ S, a.1 ≠ r) {v : Fin n}
    (h : Relation.ReflTransGen (fun u w => (u, w) ∈ S) v r) : ∃ k, (par S r)^[k] v = r := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hac _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, ?_⟩
    rw [Function.iterate_succ_apply, ← eq_par hf (har _ hac) hac]
    exact hk

end Functional

section DetEval

variable {r : Fin n} {S : Finset (Fin n × Fin n)}

/-- Triangular case: an in-arborescence has `det L_out^{(r)} = 1`. -/
theorem det_lapOutRed_of_isInArb (h : IsInArb r S) : (lapOutRed S r).det = 1 := by
  classical
  obtain ⟨hf, har, hreach⟩ := h
  have hex : ∀ v, ∃ k, (par S r)^[k] v = r := fun v => iterate_par_of_reach hf har (hreach v)
  let d : Fin n → ℕ := fun v => Nat.find (hex v)
  have hd : ∀ v, v ≠ r → d (par S r v) < d v := by
    intro v hv
    have hk := Nat.find_spec (hex v)
    have h0 : Nat.find (hex v) ≠ 0 := by
      intro h0
      rw [h0, Function.iterate_zero, id] at hk
      exact hv hk
    obtain ⟨k, hk'⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [hk', Function.iterate_succ_apply] at hk
    show Nat.find (hex _) < Nat.find (hex v)
    rw [hk']
    exact Nat.lt_succ_of_le (Nat.find_min' _ hk)
  rw [← Matrix.det_transpose, det_eq_prod_diag_of_lt _ (fun u => d u.1)]
  · refine prod_eq_one fun u _ => ?_
    rw [Matrix.transpose_apply, lapOutRed_apply, lapOut_functional hf u.2, if_pos rfl,
      if_neg fun h' => (hd u.1 u.2).ne (by rw [← h'])]
    rfl
  · intro u w huw
    rw [Matrix.transpose_apply, lapOutRed_apply, lapOut_functional hf w.2] at huw
    by_cases h1 : w = u
    · exact Or.inl h1.symm
    · right
      rw [if_neg (fun h' => h1 (Subtype.ext h'))] at huw
      have h2 : u.1 = par S r w.1 := by
        by_contra h2
        rw [if_neg h2] at huw
        exact huw rfl
      show d u.1 < d w.1
      rw [h2]
      exact hd w.1 w.2

/-- Kernel case: a functional arc set in which some vertex does not reach `r` has
`det L_out^{(r)} = 0`. -/
theorem det_lapOutRed_of_not_reach (hf : ∀ v, v ≠ r → (outArcs S v).card = 1)
    (har : ∀ a ∈ S, a.1 ≠ r) {v₀ : Fin n}
    (h₀ : ¬ Relation.ReflTransGen (fun u w => (u, w) ∈ S) v₀ r) : (lapOutRed S r).det = 0 := by
  classical
  let x' : Fin n → ℤ := fun u => if Relation.ReflTransGen (fun u w => (u, w) ∈ S) u r then 0 else 1
  have hv₀ : v₀ ≠ r := by rintro rfl; exact h₀ Relation.ReflTransGen.refl
  refine (Matrix.exists_mulVec_eq_zero_iff).1 ⟨fun u => x' u.1, ?_, ?_⟩
  · intro h
    have := congrFun h ⟨v₀, hv₀⟩
    simp [x', h₀] at this
  · funext v
    simp only [Matrix.mulVec, dotProduct, lapOutRed_apply, Pi.zero_apply]
    have hsum : ∑ u : {u : Fin n // u ≠ r}, lapOut S v.1 u.1 * x' u.1 =
        ∑ u, lapOut S v.1 u * x' u := by
      rw [← Finset.sum_erase (s := Finset.univ) (a := r)
        (by simp [x', Relation.ReflTransGen.refl])]
      exact (Finset.sum_subtype _ (fun u => by simp) (fun u => lapOut S v.1 u * x' u)).symm
    rw [hsum]
    simp only [lapOut_functional hf v.2, sub_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', mem_univ, if_true]
    simp only [x']
    rw [if_congr (reach_iff_par hf v.2) rfl rfl, sub_self]

open Classical in
/-- **`det L_out^{(r)}` of `n − 1` arcs**: `1` for an in-arborescence towards `r`, `0` otherwise. -/
theorem det_lapOutRed_of_card (hS : S.card = n - 1) :
    (lapOutRed S r).det = if IsInArb r S then 1 else 0 := by
  classical
  by_cases h0 : ∃ v, v ≠ r ∧ (outArcs S v).card = 0
  · obtain ⟨v, hv, hc⟩ := h0
    rw [if_neg fun h => by rw [h.1 v hv] at hc; exact one_ne_zero hc]
    refine Matrix.det_eq_zero_of_row_eq_zero ⟨v, hv⟩ fun u => ?_
    have hnot : (v, u.1) ∉ S := fun h =>
      notMem_empty _ (by rw [← card_eq_zero.1 hc]; exact mem_outArcs.2 ⟨h, rfl⟩)
    simp [lapOut, hc, hnot]
  · simp only [not_exists, not_and] at h0
    obtain ⟨hf, har⟩ := functional_of_card hS h0
    by_cases hr : ∀ v, Relation.ReflTransGen (fun u w => (u, w) ∈ S) v r
    · rw [if_pos ⟨hf, har, hr⟩, det_lapOutRed_of_isInArb ⟨hf, har, hr⟩]
    · obtain ⟨v₀, h₀⟩ := not_forall.1 hr
      rw [if_neg fun h => h₀ (h.2.2 v₀), det_lapOutRed_of_not_reach hf har h₀]

end DetEval

/-! ### Lemma 3.2 -/

/-- **Lemma 3.2 (directed fermionic matrix-tree theorem)**, Berezin side:
`[Ω_V] Π_{a∈F}(1 + p_a) = #{in-arborescences towards r contained in F}`. -/
theorem topV_arcProd (r : Fin n) (F : Finset (Fin n × Fin n)) :
    topV r (arcProd r F) = ((inArbs r F).card : ℤ) := by
  classical
  rw [topV_arcProd_eq_sum, sum_congr rfl fun S hS =>
    (topV_pProd_eq_det r (mem_powersetCard.1 hS).2).trans
      (det_lapOutRed_of_card (mem_powersetCard.1 hS).2), sum_boole]
  congr 2
  ext T
  rw [mem_filter, mem_powersetCard, mem_inArbs]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, card_of_isInArb h2⟩, h2⟩

/-- **Lemma 3.2 (directed matrix-tree theorem)**:
`det L_out(F)^{(r)} = #{in-arborescences towards r contained in F}`. -/
theorem det_lapOutRed_eq_card_inArbs (r : Fin n) (F : Finset (Fin n × Fin n)) :
    (lapOutRed F r).det = ((inArbs r F).card : ℤ) := by
  rw [← topV_arcProd_eq_det, topV_arcProd]

/-! ### Cycle covers (Lemma 3.3) -/

section CycleCover

open DirectedHamiltonian

variable {X : Finset (Fin n × Fin n)}

theorem reflTransGen_mono {α : Type*} {R R' : α → α → Prop} (hR : ∀ a b, R a b → R' a b)
    {a b : α} (h : Relation.ReflTransGen R a b) : Relation.ReflTransGen R' a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hR _ _ hbc)

/-- The relation "is an arc of `X`". -/
abbrev Arc (X : Finset (Fin n × Fin n)) (u w : Fin n) : Prop := (u, w) ∈ X

theorem cc_out_card (hX : CycleCover X) (v : Fin n) : (outArcs X v).card = 1 := (hX v).1

theorem cc_out_exists (hX : CycleCover X) (v : Fin n) : ∃ w, (v, w) ∈ X := by
  obtain ⟨a, ha⟩ := card_pos.1 (by rw [cc_out_card hX v]; exact one_pos)
  obtain ⟨ha1, ha2⟩ := mem_outArcs.1 ha
  exact ⟨a.2, by rw [← ha2]; exact ha1⟩

theorem cc_out_unique (hX : CycleCover X) {v w w' : Fin n} (h : (v, w) ∈ X) (h' : (v, w') ∈ X) :
    w = w' := by
  have := card_le_one.1 (cc_out_card hX v).le (v, w) (mem_outArcs.2 ⟨h, rfl⟩) (v, w')
    (mem_outArcs.2 ⟨h', rfl⟩)
  exact (Prod.ext_iff.1 this).2

theorem cc_in_unique (hX : CycleCover X) {u u' w : Fin n} (h : (u, w) ∈ X) (h' : (u', w) ∈ X) :
    u = u' := by
  have := card_le_one.1 (hX w).2.le (u, w) (mem_filter.2 ⟨h, rfl⟩) (u', w)
    (mem_filter.2 ⟨h', rfl⟩)
  exact (Prod.ext_iff.1 this).1

/-- The successor of `v` in the cycle cover. -/
noncomputable def ccSucc (hX : CycleCover X) (v : Fin n) : Fin n := (cc_out_exists hX v).choose

theorem ccSucc_mem (hX : CycleCover X) (v : Fin n) : (v, ccSucc hX v) ∈ X :=
  (cc_out_exists hX v).choose_spec

theorem ccSucc_injective (hX : CycleCover X) : Function.Injective (ccSucc hX) := fun u u' h =>
  cc_in_unique hX (ccSucc_mem hX u) (h ▸ ccSucc_mem hX u')

/-- The successor permutation of a cycle cover. -/
noncomputable def ccPerm (hX : CycleCover X) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (ccSucc_injective hX))

theorem ccPerm_apply (hX : CycleCover X) (v : Fin n) : ccPerm hX v = ccSucc hX v := rfl

theorem reach_ccPerm_pow (hX : CycleCover X) (x : Fin n) :
    ∀ j : ℕ, Relation.ReflTransGen (Arc X) x ((ccPerm hX ^ j) x)
  | 0 => by rw [pow_zero, Equiv.Perm.one_apply]
  | j + 1 => by
    rw [pow_succ', Equiv.Perm.mul_apply, ccPerm_apply]
    exact (reach_ccPerm_pow hX x j).tail (ccSucc_mem hX _)

/-- In a cycle cover every arc can be travelled back: `u → w` implies that `w` reaches `u`. -/
theorem reach_back (hX : CycleCover X) {u w : Fin n} (h : (u, w) ∈ X) :
    Relation.ReflTransGen (Arc X) w u := by
  have hw : w = ccPerm hX u := cc_out_unique hX h (ccSucc_mem hX u)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (orderOf_pos (ccPerm hX)).ne'
  have h1 := pow_orderOf_eq_one (ccPerm hX)
  rw [hk, pow_succ] at h1
  have h2 : (ccPerm hX ^ k) w = u := by
    rw [hw, ← Equiv.Perm.mul_apply, h1, Equiv.Perm.one_apply]
  exact h2 ▸ reach_ccPerm_pow hX w k

theorem reach_iff_of_adj (hX : CycleCover X) (r : Fin n) {u w : Fin n}
    (h : (Hamiltonian.graphOf (undirected X)).Adj u w) :
    Relation.ReflTransGen (Arc X) u r ↔ Relation.ReflTransGen (Arc X) w r := by
  rw [SimpleGraph.fromEdgeSet_adj] at h
  obtain ⟨a, ha, hae⟩ := mem_image.1 (mem_coe.1 h.1)
  rcases Sym2.eq_iff.1 hae with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have huw : (u, w) ∈ X := by rw [← h1, ← h2]; exact ha
    exact ⟨fun hu => (reach_back hX huw).trans hu, fun hw => Relation.ReflTransGen.head huw hw⟩
  · have hwu : (w, u) ∈ X := by rw [← h1, ← h2]; exact ha
    exact ⟨fun hu => Relation.ReflTransGen.head hwu hu, fun hw => (reach_back hX hwu).trans hw⟩

theorem reach_iff_of_walk (hX : CycleCover X) (r : Fin n) {u v : Fin n} :
    (Hamiltonian.graphOf (undirected X)).Walk u v →
      (Relation.ReflTransGen (Arc X) u r ↔ Relation.ReflTransGen (Arc X) v r)
  | .nil => Iff.rfl
  | .cons h p => (reach_iff_of_adj hX r h).trans (reach_iff_of_walk hX r p)

theorem reachable_of_reach {u v : Fin n} (h : Relation.ReflTransGen (Arc X) u v) :
    (Hamiltonian.graphOf (undirected X)).Reachable u v := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
    refine ih.trans ?_
    by_cases hb : b = c
    · rw [hb]
    · refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨mem_coe.2 (mem_image.2 ⟨(b, c), hbc, rfl⟩), hb⟩

/-- A cycle cover is a directed Hamiltonian cycle iff every vertex reaches `r` along its arcs. -/
theorem connected_iff_reach (hX : CycleCover X) (r : Fin n) :
    (Hamiltonian.graphOf (undirected X)).Connected ↔
      ∀ v, Relation.ReflTransGen (Arc X) v r := by
  constructor
  · intro hc v
    obtain ⟨p⟩ := hc.preconnected v r
    exact (reach_iff_of_walk hX r p).2 Relation.ReflTransGen.refl
  · intro h
    exact (SimpleGraph.connected_iff _).2
      ⟨fun u v => (reachable_of_reach (h u)).trans (reachable_of_reach (h v)).symm, ⟨r⟩⟩

/-- The only candidate in-arborescence inside a cycle cover: drop the out-arc of `r`. -/
theorem inArbs_cycleCover_subset (hX : CycleCover X) (r : Fin n) :
    inArbs r X ⊆ {X.filter fun a => a.1 ≠ r} := by
  intro T hT
  obtain ⟨hTX, hf, har, -⟩ := mem_inArbs.1 hT
  rw [mem_singleton]
  ext a
  rw [mem_filter]
  constructor
  · intro ha
    exact ⟨hTX ha, har a ha⟩
  · rintro ⟨ha, hr⟩
    obtain ⟨b, hb⟩ := card_pos.1 (by rw [hf a.1 hr]; exact one_pos)
    obtain ⟨hbT, hb1⟩ := mem_outArcs.1 hb
    have : a = b := card_le_one.1 (cc_out_card hX a.1).le a (mem_outArcs.2 ⟨ha, rfl⟩) b
      (mem_outArcs.2 ⟨hTX hbT, hb1⟩)
    rw [this]
    exact hbT

theorem isInArb_cycleCover_iff (hX : CycleCover X) (r : Fin n) :
    IsInArb r (X.filter fun a => a.1 ≠ r) ↔ ∀ v, Relation.ReflTransGen (Arc X) v r := by
  constructor
  · intro h v
    exact reflTransGen_mono (fun u w huw => (mem_filter.1 huw).1) (h.2.2 v)
  · intro h
    refine ⟨fun v hv => ?_, fun a ha => (mem_filter.1 ha).2, fun v => ?_⟩
    · have : outArcs (X.filter fun a => a.1 ≠ r) v = outArcs X v := by
        ext a
        simp only [mem_outArcs, mem_filter]
        constructor
        · rintro ⟨⟨ha, -⟩, h1⟩
          exact ⟨ha, h1⟩
        · rintro ⟨ha, h1⟩
          exact ⟨⟨ha, h1 ▸ hv⟩, h1⟩
      rw [this, cc_out_card hX v]
    · induction h v using Relation.ReflTransGen.head_induction_on with
      | refl => exact Relation.ReflTransGen.refl
      | @head a c hac _ ih =>
        by_cases har : a = r
        · rw [har]
        · exact Relation.ReflTransGen.head (mem_filter.2 ⟨hac, har⟩) ih

/-- **Lemma 3.3, first part**: a directed Hamiltonian cycle contains exactly one
in-arborescence towards `r`, ... -/
theorem card_inArbs_of_connected (hX : CycleCover X) (r : Fin n)
    (hc : (Hamiltonian.graphOf (undirected X)).Connected) : (inArbs r X).card = 1 := by
  have hmem : (X.filter fun a => a.1 ≠ r) ∈ inArbs r X :=
    mem_inArbs.2 ⟨filter_subset _ _,
      (isInArb_cycleCover_iff hX r).2 ((connected_iff_reach hX r).1 hc)⟩
  rw [eq_singleton_iff_unique_mem.2 ⟨hmem, fun T hT => mem_singleton.1
    (inArbs_cycleCover_subset hX r hT)⟩, card_singleton]

/-- ... and a cycle cover with at least two cycles contains none. -/
theorem card_inArbs_of_not_connected (hX : CycleCover X) (r : Fin n)
    (hc : ¬ (Hamiltonian.graphOf (undirected X)).Connected) : (inArbs r X).card = 0 := by
  refine card_eq_zero.2 (eq_empty_of_forall_notMem fun T hT => hc ?_)
  have hT' := inArbs_cycleCover_subset hX r hT
  rw [mem_singleton] at hT'
  rw [hT'] at hT
  exact (connected_iff_reach hX r).2 ((isInArb_cycleCover_iff hX r).1 (mem_inArbs.1 hT).2)

open Classical in
/-- **Lemma 3.3, first part**, determinant form: for a cycle cover `X`,
`det L_out(X)^{(r)} = 1` if `X` is a directed Hamiltonian cycle and `0` otherwise. -/
theorem det_lapOutRed_cycleCover (hX : CycleCover X) (r : Fin n) :
    (lapOutRed X r).det = if (Hamiltonian.graphOf (undirected X)).Connected then 1 else 0 := by
  rw [det_lapOutRed_eq_card_inArbs]
  split_ifs with hc
  · rw [card_inArbs_of_connected hX r hc, Nat.cast_one]
  · rw [card_inArbs_of_not_connected hX r hc, Nat.cast_zero]

end CycleCover

/-! ### Lemma 3.3: the directed identity -/

/-- The weight `w(X) = Σ_{a∈X} w a` of an arc set. -/
def arcWt (w : Fin n × Fin n → ℕ) (X : Finset (Fin n × Fin n)) : ℕ := ∑ a ∈ X, w a

/-- **Lemma 3.3 (the directed identity)**, Berezin form: for every digraph `A`, root `r`,
integer `z` and arc weights `w`,
`Σ_{H ∈ DHC(A)} z^{w(H)} = Σ_{X cycle cover of A} z^{w(X)} · [Ω_V] Π_{a∈X}(1 + p_a)`.
There is no factor `n`. -/
theorem sum_dirHamCycles_pow_eq (A : Finset (Fin n × Fin n)) (r : Fin n) (z : ℤ)
    (w : Fin n × Fin n → ℕ) :
    ∑ H ∈ DirectedHamiltonian.dirHamCycles A, z ^ arcWt w H =
      ∑ X ∈ DirectedHamiltonian.cycleCovers A, z ^ arcWt w X * topV r (arcProd r X) := by
  rw [DirectedHamiltonian.dirHamCycles, sum_filter]
  refine sum_congr rfl fun X hX => ?_
  have hcc := (mem_filter.1 hX).2
  rw [topV_arcProd]
  split_ifs with hc
  · rw [card_inArbs_of_connected hcc r hc, Nat.cast_one, mul_one]
  · rw [card_inArbs_of_not_connected hcc r hc, Nat.cast_zero, mul_zero]

/-- **Lemma 3.3**, determinant form:
`Σ_{H ∈ DHC(A)} z^{w(H)} = Σ_{X cycle cover of A} z^{w(X)} · det L_out(X)^{(r)}`. -/
theorem sum_dirHamCycles_pow_eq_det (A : Finset (Fin n × Fin n)) (r : Fin n) (z : ℤ)
    (w : Fin n × Fin n → ℕ) :
    ∑ H ∈ DirectedHamiltonian.dirHamCycles A, z ^ arcWt w H =
      ∑ X ∈ DirectedHamiltonian.cycleCovers A, z ^ arcWt w X * (lapOutRed X r).det := by
  rw [sum_dirHamCycles_pow_eq A r z w]
  refine sum_congr rfl fun X _ => ?_
  rw [topV_arcProd_eq_det]

/-- **Lemma 3.3**, counting form: `#DHC(A) = Σ_{X cycle cover of A} [Ω_V] Π_{a∈X}(1 + p_a)`. -/
theorem card_dirHamCycles_eq_sum (A : Finset (Fin n × Fin n)) (r : Fin n) :
    ((DirectedHamiltonian.dirHamCycles A).card : ℤ) =
      ∑ X ∈ DirectedHamiltonian.cycleCovers A, topV r (arcProd r X) := by
  have h := sum_dirHamCycles_pow_eq A r 1 (fun _ => 0)
  simp only [one_pow, one_mul, sum_const, nsmul_eq_mul, mul_one] at h
  exact h

end

end EthFollowup.ExactHC
