/-
# The fermionic matrix-tree theorem (module M5 of the exact-#HC blueprint)

Write-up reference: `research/exact-hc-theorem.md`, §3: Lemma 3.2 (Berezin form of
Cauchy–Binet), Lemma 3.3 (fermionic matrix-tree theorem) and Corollary 3.4.

## Main results
* `MatrixTree.berezin`: for odd `ḡ_u, g_u` and an `N × N` integer matrix `B`,
  `Π_k θ̄(b_k) θ(b_k) = det(B)² • Π_u ḡ_u g_u`, where `b_k` is the `k`-th column of `B`.
* `berezin_topV` (**Lemma 3.2**): `[Ω_V] Π_k θ̄(b_k) θ(b_k) = det(B)²`, with the vertices of
  `V ∖ {r}` enumerated by any `ν : Fin (n - 1) ≃ {u // u ≠ r}`.
* `mt_isSignedBasis_OmegaSet`: `Ω_S = ±e_{Γ_S}`; `OmegaSet_eq_coe_prod` and `edgeProd_eq_coe_prod`:
  `Ω_S` and `Π_{e∈X}(1 + q_e)` are products in the (commutative) centre, so they do not depend
  on the order of the factors.
* `topV_edgeProd` (**Lemma 3.3**): for loop-free `X`,
  `[Ω_V] Π_{e∈X}(1 + q_e) = τ(V, X) = #(spanningTrees X)`.
* `fermionSum_eq` (**Corollary 3.4** with Lemma 3.1): `fermionSum G r = n · #HC(G)`;
  `n_mul_hamCycles_eq_sum_topV` is the form `Σ_{X ⊆ E} [X 2-regular] · [Ω_V] Π_{e∈X}(1 + q_e)`.

No hypothesis on `n` is needed (the root `r : Fin n` forces `n ≥ 1`).
-/
import EthFollowup.ExactHC.Fermion
import EthFollowup.ExactHC.Incidence
import EthFollowup.ExactHC
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Subring.Basic

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset Grass

namespace MatrixTree

/-! ### Degrees -/

section Degree

variable {Γ : Type*} [Fintype Γ] [LinearOrder Γ]

/-- `x` is homogeneous of degree `d`: every basis set in its support has `d` elements. -/
def IsDeg (d : ℕ) (x : Grass Γ) : Prop := ∀ S, x.coeff S ≠ 0 → S.card = d

theorem isDeg_zero (d : ℕ) : IsDeg d (0 : Grass Γ) := fun _ h => absurd rfl h

theorem IsDeg.add {d : ℕ} {x y : Grass Γ} (hx : IsDeg d x) (hy : IsDeg d y) :
    IsDeg d (x + y) := by
  intro S hS
  rw [coeff_add] at hS
  by_cases h : x.coeff S = 0
  · exact hy S (by rw [h, zero_add] at hS; exact hS)
  · exact hx S h

theorem IsDeg.neg {d : ℕ} {x : Grass Γ} (hx : IsDeg d x) : IsDeg d (-x) :=
  fun S hS => hx S (by rw [coeff_neg] at hS; exact neg_ne_zero.1 hS)

theorem IsDeg.sub {d : ℕ} {x y : Grass Γ} (hx : IsDeg d x) (hy : IsDeg d y) :
    IsDeg d (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem IsDeg.zsmul {d : ℕ} {x : Grass Γ} (hx : IsDeg d x) (c : ℤ) : IsDeg d (c • x) :=
  fun S hS => hx S (by rw [coeff_zsmul] at hS; exact right_ne_zero_of_mul hS)

theorem isDeg_sum {ι : Type*} {d : ℕ} (s : Finset ι) (f : ι → Grass Γ)
    (h : ∀ i ∈ s, IsDeg d (f i)) : IsDeg d (∑ i ∈ s, f i) := by
  intro S hS
  rw [coeff_sum] at hS
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  exact h i hi S hne

theorem isDeg_e (S : Finset Γ) : IsDeg S.card (e S) := by
  intro T hT
  by_cases h : S = T
  · rw [h]
  · exact absurd (coeff_e_of_ne h) hT

theorem isDeg_gen (γ : Γ) : IsDeg 1 (gen γ) := by
  have := isDeg_e ({γ} : Finset Γ)
  rwa [card_singleton] at this

theorem isDeg_one : IsDeg 0 (1 : Grass Γ) := by
  have := isDeg_e (∅ : Finset Γ)
  rwa [card_empty] at this

theorem IsDeg.mul {p q : ℕ} {x y : Grass Γ} (hx : IsDeg p x) (hy : IsDeg q y) :
    IsDeg (p + q) (x * y) := by
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
  · rw [← h.2, card_union_of_disjoint h.1, h1, h2]
  · exact absurd rfl hc

theorem IsDeg.isHomog {d : ℕ} {x : Grass Γ} (hx : IsDeg d x) : IsHomog d x :=
  fun S hS => by rw [hx S hS]

theorem isDeg_list_prod {d : ℕ} : ∀ (l : List (Grass Γ)) (_ : ∀ x ∈ l, IsDeg d x),
    IsDeg (l.length * d) l.prod
  | [], _ => by simpa using (isDeg_one : IsDeg 0 (1 : Grass Γ))
  | x :: l, h => by
    rw [List.prod_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact (h x List.mem_cons_self).mul (isDeg_list_prod l fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- If `x` has degree `d ≠ |A|`, its `A`-coefficient vanishes. -/
theorem IsDeg.coeff_eq_zero {d : ℕ} {x : Grass Γ} (hx : IsDeg d x) {A : Finset Γ}
    (hA : A.card ≠ d) : x.coeff A = 0 := by
  by_contra h
  exact hA (hx A h)

end Degree

/-! ### The centre: even elements commute -/

section Centre

variable {Γ : Type*} [Fintype Γ] [LinearOrder Γ]

theorem mem_center_of_even {x : Grass Γ} (hx : IsHomog 0 x) : x ∈ Subring.center (Grass Γ) :=
  Subring.mem_center_iff.2 fun g => (hx.commute_of_even g).symm

theorem coe_list_prod_map {α : Type*} (l : List α) (f : α → Subring.center (Grass Γ)) :
    (((l.map f).prod : Subring.center (Grass Γ)) : Grass Γ) = (l.map fun a => (f a : Grass Γ)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.prod_cons, Subring.coe_mul, ih, List.map_cons,
      List.prod_cons]

theorem coe_prod_ofFn {N : ℕ} (f : Fin N → Subring.center (Grass Γ)) :
    (((∏ k, f k : Subring.center (Grass Γ))) : Grass Γ) = (List.ofFn fun k => (f k : Grass Γ)).prod := by
  rw [← List.prod_ofFn, ← List.map_id (List.ofFn f), coe_list_prod_map, List.map_ofFn]
  rfl

theorem coe_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Subring.center (Grass Γ)) :
    (((∑ i ∈ s, f i : Subring.center (Grass Γ))) : Grass Γ) = ∑ i ∈ s, (f i : Grass Γ) :=
  map_sum (Subring.center (Grass Γ)).subtype f s

theorem isDeg_coe_prod {ι : Type*} (F : Finset ι) (f : ι → Subring.center (Grass Γ)) {d : ℕ}
    (h : ∀ i, IsDeg d (f i : Grass Γ)) :
    IsDeg (F.card * d) (((∏ i ∈ F, f i : Subring.center (Grass Γ))) : Grass Γ) := by
  classical
  refine Finset.induction_on F ?_ ?_
  · simpa using (isDeg_one : IsDeg 0 (1 : Grass Γ))
  · intro a s ha ih
    rw [prod_insert ha, Subring.coe_mul, card_insert_of_notMem ha, Nat.succ_mul, Nat.add_comm]
    exact (h a).mul ih

end Centre

/-! ### Products of pairs and the Berezin–Cauchy–Binet identity (Lemma 3.2) -/

section Berezin

variable {Γ : Type*} [Fintype Γ] [LinearOrder Γ]

/-- The sign `(-1)^{N(N-1)/2}` of step 1 of Lemma 3.2, defined recursively. -/
def pairSign : ℕ → ℤ
  | 0 => 1
  | N + 1 => (-1) ^ N * pairSign N

/-- Step 1 of Lemma 3.2: `Π_k a_k b_k = s_N • (Π_k a_k)(Π_k b_k)` for odd `a_k, b_k`. -/
theorem prod_mul_pairs : ∀ {N : ℕ} (a b : Fin N → Grass Γ) (_ : ∀ k, IsHomog 1 (a k))
    (_ : ∀ k, IsHomog 1 (b k)),
    (List.ofFn fun k => a k * b k).prod = pairSign N • ((List.ofFn a).prod * (List.ofFn b).prod)
  | 0, _, _, _, _ => by simp [pairSign]
  | N + 1, a, b, ha, hb => by
    rw [List.ofFn_succ, List.prod_cons,
      prod_mul_pairs (fun k => a k.succ) (fun k => b k.succ) (fun k => ha _) (fun k => hb _),
      List.ofFn_succ (f := a), List.prod_cons, List.ofFn_succ (f := b), List.prod_cons]
    have hA : IsHomog N (List.ofFn fun k => a k.succ).prod := by
      have := isHomog_prod_ofFn (fun k => a k.succ) (fun _ => 1) (fun k => ha _)
      simpa using this
    have hc := (hb 0).mul_comm_sign hA
    rw [one_mul] at hc
    have key : b 0 * ((List.ofFn fun k => a k.succ).prod * (List.ofFn fun k => b k.succ).prod) =
        (-1 : ℤ) ^ N • ((List.ofFn fun k => a k.succ).prod *
          (b 0 * (List.ofFn fun k => b k.succ).prod)) := by
      rw [← mul_assoc, hc, smul_mul_assoc, mul_assoc]
    rw [mul_smul_comm, mul_assoc (a 0), key, mul_smul_comm, smul_smul, pairSign, mul_comm,
      ← mul_assoc (a 0)]

/-- **Lemma 3.2 (Berezin form of Cauchy–Binet)**, algebraic form: for odd `ḡ_u, g_u`
(`u : Fin N`) and `B : Matrix (Fin N) (Fin N) ℤ` with columns `b_k`,
`Π_k θ̄(b_k) θ(b_k) = det(B)² • Π_u ḡ_u g_u`. -/
theorem berezin {N : ℕ} (gb g : Fin N → Grass Γ) (hgb : ∀ u, IsHomog 1 (gb u))
    (hg : ∀ u, IsHomog 1 (g u)) (B : Matrix (Fin N) (Fin N) ℤ) :
    (List.ofFn fun k => linForm gb (fun u => B u k) * linForm g (fun u => B u k)).prod =
      (B.det ^ 2) • (List.ofFn fun u => gb u * g u).prod := by
  rw [prod_mul_pairs _ _ (fun k => isHomog_linForm hgb _) (fun k => isHomog_linForm hg _),
    prod_linForm_eq_det gb hgb B, prod_linForm_eq_det g hg B, prod_mul_pairs gb g hgb hg,
    smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

end Berezin

/-! ### The fermion generators -/

section Fermion

variable {n : ℕ}

theorem isDeg_psibar (r v : Fin n) : IsDeg 1 (psibar r v) := by
  unfold psibar
  split_ifs
  · exact isDeg_zero 1
  · exact isDeg_gen _

theorem isDeg_psi (r v : Fin n) : IsDeg 1 (psi r v) := by
  unfold psi
  split_ifs
  · exact isDeg_zero 1
  · exact isDeg_gen _

theorem isDeg_omega (r v : Fin n) : IsDeg 2 (omega r v) :=
  (isDeg_psibar r v).mul (isDeg_psi r v)

theorem isDeg_qEdge (r : Fin n) (e : Sym2 (Fin n)) : IsDeg 2 (qEdge r e) := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [qEdge_mk, qPair]
    exact ((isDeg_psibar r a).sub (isDeg_psibar r b)).mul ((isDeg_psi r a).sub (isDeg_psi r b))

theorem isHomog_even_of_isDeg_two {Γ : Type*} [Fintype Γ] [LinearOrder Γ] {x : Grass Γ}
    (hx : IsDeg 2 x) : IsHomog 0 x :=
  hx.isHomog.congr rfl

/-- `ω_v` as an element of the centre. -/
noncomputable def omegaC (r v : Fin n) : Subring.center (Grass (Fin (2 * n))) :=
  ⟨omega r v, mem_center_of_even (isHomog_even_of_isDeg_two (isDeg_omega r v))⟩

/-- `q_e` as an element of the centre. -/
noncomputable def qC (r : Fin n) (e : Sym2 (Fin n)) : Subring.center (Grass (Fin (2 * n))) :=
  ⟨qEdge r e, mem_center_of_even (isHomog_even_of_isDeg_two (isDeg_qEdge r e))⟩

@[simp] theorem coe_omegaC (r v : Fin n) : (omegaC r v : Grass (Fin (2 * n))) = omega r v := rfl

@[simp] theorem coe_qC (r : Fin n) (e : Sym2 (Fin n)) :
    (qC r e : Grass (Fin (2 * n))) = qEdge r e := rfl

end Fermion

end MatrixTree

open MatrixTree

variable {n : ℕ}

/-! ### Order independence -/

/-- `Ω_S` is the product of the `ω_v` (`v ∈ S ∖ {r}`) in the commutative centre: the order of
the factors does not matter. -/
theorem OmegaSet_eq_coe_prod (r : Fin n) (S : Finset (Fin n)) :
    OmegaSet r S = ((∏ v ∈ S.erase r, omegaC r v : Subring.center (Grass (Fin (2 * n))))) := by
  rw [OmegaSet, OmegaOf, Finset.prod_eq_multiset_prod, ← Finset.sort_eq (S.erase r) (· ≤ ·),
    Multiset.map_coe, Multiset.prod_coe, coe_list_prod_map]
  rfl

/-- `Π_{e∈X}(1 + q_e)` is a product in the commutative centre: the order of the factors does not
matter. -/
theorem edgeProd_eq_coe_prod (r : Fin n) (X : Finset (Sym2 (Fin n))) :
    edgeProd r X = ((∏ e ∈ X, (1 + qC r e) : Subring.center (Grass (Fin (2 * n))))) := by
  rw [edgeProd, ← Finset.prod_map_toList, coe_list_prod_map]
  rfl

/-- Any ordering of `V ∖ {r}` gives `Ω_V`. -/
theorem prod_ofFn_omega_eq_OmegaSet (r : Fin n) {N : ℕ} (ν : Fin N ≃ {u : Fin n // u ≠ r}) :
    (List.ofFn fun j => omega r (ν j)).prod = OmegaSet r univ := by
  rw [OmegaSet_eq_coe_prod, Finset.prod_subtype (univ.erase r) (p := fun u => u ≠ r)
    (fun u => by simp), ← Equiv.prod_comp ν, coe_prod_ofFn]
  rfl

/-! ### `Ω_S = ±e_{Γ_S}` -/

theorem mt_gbarIdx_ne_gIdx (v : Fin n) : gbarIdx v ≠ gIdx v := by
  simp only [gbarIdx, gIdx, ne_eq, Fin.ext_iff]
  omega

theorem disjoint_blocks {v w : Fin n} (h : v ≠ w) :
    Disjoint ({gbarIdx v, gIdx v} : Finset (Fin (2 * n))) {gbarIdx w, gIdx w} := by
  have h' : v.val ≠ w.val := fun h'' => h (Fin.ext h'')
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
  rcases hx with rfl | rfl <;> rcases hx' with h1 | h1 <;>
    simp only [gbarIdx, gIdx, Fin.ext_iff] at h1 <;> omega

theorem isSignedBasis_omega {r v : Fin n} (hv : v ≠ r) :
    IsSignedBasis {gbarIdx v, gIdx v} (omega r v) := by
  have h := (isSignedBasis_e ({gbarIdx v} : Finset (Fin (2 * n)))).mul
    (isSignedBasis_e ({gIdx v} : Finset (Fin (2 * n))))
    (Finset.disjoint_singleton.2 (mt_gbarIdx_ne_gIdx v))
  rw [← Finset.insert_eq] at h
  unfold omega psibar psi
  rw [if_neg hv, if_neg hv]
  exact h

theorem mt_isSignedBasis_OmegaOf (r : Fin n) : ∀ (l : List (Fin n)), l.Nodup → (∀ v ∈ l, v ≠ r) →
    IsSignedBasis (l.toFinset.biUnion fun v => {gbarIdx v, gIdx v}) (OmegaOf r l)
  | [], _, _ => by
    simp only [List.toFinset_nil, Finset.biUnion_empty, OmegaOf, List.map_nil, List.prod_nil]
    exact isSignedBasis_e ∅
  | v :: l, hnd, hr => by
    rw [List.toFinset_cons, Finset.biUnion_insert, OmegaOf, List.map_cons, List.prod_cons]
    refine (isSignedBasis_omega (hr v List.mem_cons_self)).mul
      (mt_isSignedBasis_OmegaOf r l (List.nodup_cons.1 hnd).2
        fun w hw => hr w (List.mem_cons_of_mem _ hw)) ?_
    rw [Finset.disjoint_biUnion_right]
    intro w hw
    refine disjoint_blocks fun h => (List.nodup_cons.1 hnd).1 ?_
    rw [h]
    exact List.mem_toFinset.1 hw

/-- `Ω_S = ±e_{Γ_S}`. -/
theorem mt_isSignedBasis_OmegaSet (r : Fin n) (S : Finset (Fin n)) :
    IsSignedBasis (genSet r S) (OmegaSet r S) := by
  have h := mt_isSignedBasis_OmegaOf r ((S.erase r).sort (· ≤ ·)) (Finset.sort_nodup _ _)
    fun v hv => (Finset.mem_erase.1 ((Finset.mem_sort _).1 hv)).1
  rwa [Finset.sort_toFinset] at h

theorem topV_OmegaSet (r : Fin n) : topV r (OmegaSet r univ) = 1 :=
  topCoeff_self (mt_isSignedBasis_OmegaSet r univ)

theorem topV_zsmul (r : Fin n) (c : ℤ) (x : Grass (Fin (2 * n))) :
    topV r (c • x) = c * topV r x :=
  topCoeff_zsmul _ _ _ _

theorem topV_sum (r : Fin n) {ι : Type*} (s : Finset ι) (f : ι → Grass (Fin (2 * n))) :
    topV r (∑ i ∈ s, f i) = ∑ i ∈ s, topV r (f i) := by
  unfold topV topCoeff
  rw [coeff_sum, Finset.sum_mul]

/-- `|Γ| = 2(n − 1)`. -/
theorem card_genSet_univ (r : Fin n) : (genSet r univ).card = 2 * (n - 1) := by
  let ν := (Fintype.equivFinOfCardEq (card_ne_root r)).symm
  have hdeg : IsDeg ((List.ofFn fun j => omega r (ν j)).length * 2)
      (List.ofFn fun j => omega r (ν j)).prod :=
    isDeg_list_prod _ fun x hx => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact isDeg_omega r _
  rw [prod_ofFn_omega_eq_OmegaSet, List.length_ofFn] at hdeg
  have hne : (OmegaSet r univ).coeff (genSet r univ) ≠ 0 := by
    intro h0
    have := (mt_isSignedBasis_OmegaSet r univ).coeff_mul_self
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  rw [hdeg _ hne, mul_comm]

/-! ### Lemma 3.2 for the fermion generators -/

/-- `q_e = θ̄(b_e) θ(b_e)` with `b_e` the signed incidence vector of `e` (any orientation; the
root's generators are `0`). -/
theorem qEdge_eq_inc (r : Fin n) (e : Sym2 (Fin n)) :
    qEdge r e = (∑ u, inc e u • psibar r u) * (∑ u, inc e u • psi r u) := by
  have hsum : ∀ (g : Fin n → Grass (Fin (2 * n))) (a b : Fin n), a ≠ b →
      ∑ u, inc s(a, b) u • g u = g (min a b) - g (max a b) := by
    intro g a b hab
    simp only [inc_mk, incAux, if_neg hab, sub_smul, ite_smul, one_smul, zero_smul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  induction e using Sym2.ind with
  | _ a b =>
    by_cases hab : a = b
    · subst hab
      simp [qPair, incAux]
    · rw [qEdge_mk, hsum _ a b hab, hsum _ a b hab]
      rcases le_total a b with h | h
      · rw [min_eq_left h, max_eq_right h]; rfl
      · rw [min_eq_right h, max_eq_left h, qPair_comm]; rfl

/-- Dropping the root from a linear form (its generator is `0`). -/
theorem sum_smul_eq_sum_fin (r : Fin n) {N : ℕ} (ν : Fin N ≃ {u : Fin n // u ≠ r})
    (c : Fin n → ℤ) (g : Fin n → Grass (Fin (2 * n))) (hg : g r = 0) :
    ∑ u, c u • g u = linForm (fun j => g (ν j)) fun j => c (ν j) := by
  rw [linForm, ← Finset.sum_erase univ (a := r) (by simp [hg]),
    Finset.sum_subtype (univ.erase r) (p := fun u => u ≠ r) (fun u => by simp),
    ← Equiv.sum_comp ν]

theorem psibar_root (r : Fin n) : psibar r r = 0 := if_pos rfl

theorem psi_root (r : Fin n) : psi r r = 0 := if_pos rfl

theorem mt_isHomog_psibar (r v : Fin n) : IsHomog 1 (psibar r v) := (isDeg_psibar r v).isHomog

theorem mt_isHomog_psi (r v : Fin n) : IsHomog 1 (psi r v) := (isDeg_psi r v).isHomog

/-- **Lemma 3.2 (Berezin form of Cauchy–Binet).** Enumerate `V ∖ {r}` by any
`ν : Fin (n - 1) ≃ {u // u ≠ r}` and let `B` be an `(n−1) × (n−1)` integer matrix with columns
`b_k`, `θ̄(b) = Σ_j b_j ψ̄_{ν j}`, `θ(b) = Σ_j b_j ψ_{ν j}`. Then
`[Ω_V](θ̄(b_1)θ(b_1) ⋯ θ̄(b_N)θ(b_N)) = det(B)²`. -/
theorem berezin_topV (r : Fin n) (ν : Fin (n - 1) ≃ {u : Fin n // u ≠ r})
    (B : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ) :
    topV r (List.ofFn fun k => linForm (fun j => psibar r (ν j)) (fun j => B j k) *
      linForm (fun j => psi r (ν j)) (fun j => B j k)).prod = B.det ^ 2 := by
  rw [berezin _ _ (fun _ => mt_isHomog_psibar _ _) (fun _ => mt_isHomog_psi _ _) B, topV_zsmul,
    show (List.ofFn fun u => psibar r (ν u) * psi r (ν u)) = List.ofFn fun u => omega r (ν u)
      from rfl, prod_ofFn_omega_eq_OmegaSet, topV_OmegaSet, mul_one]

/-! ### Lemma 3.3 -/

/-- `Π_{e∈F} q_e`, a product in the centre. -/
noncomputable def qProd (r : Fin n) (F : Finset (Sym2 (Fin n))) : Grass (Fin (2 * n)) :=
  ((∏ e ∈ F, qC r e : Subring.center (Grass (Fin (2 * n)))))

/-- Only `|F| = n − 1` contributes to the top coefficient. -/
theorem topV_qProd_of_card_ne (r : Fin n) {F : Finset (Sym2 (Fin n))} (hF : F.card ≠ n - 1) :
    topV r (qProd r F) = 0 := by
  have hdeg : IsDeg (F.card * 2) (qProd r F) := isDeg_coe_prod F (qC r) fun e => isDeg_qEdge r e
  unfold topV topCoeff
  rw [hdeg.coeff_eq_zero (by rw [card_genSet_univ]; omega), zero_mul]

/-- For `|F| = n − 1`: `[Ω_V] Π_{e∈F} q_e = det(B_F)²` (Lemma 3.2), for any bijection
`φ : V ∖ {r} ≃ F` indexing the columns of the reduced incidence matrix. -/
theorem topV_qProd (r : Fin n) {F : Finset (Sym2 (Fin n))} (φ : {u : Fin n // u ≠ r} ≃ F) :
    topV r (qProd r F) = (redInc F r φ).det ^ 2 := by
  let ν : Fin (n - 1) ≃ {u : Fin n // u ≠ r} := (Fintype.equivFinOfCardEq (card_ne_root r)).symm
  let B : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ := (redInc F r φ).submatrix ν ν
  have hB : B.det = (redInc F r φ).det := Matrix.det_submatrix_equiv_self ν _
  have hq : qProd r F = (List.ofFn fun k => linForm (fun j => psibar r (ν j)) (fun j => B j k) *
      linForm (fun j => psi r (ν j)) (fun j => B j k)).prod := by
    rw [qProd, ← Finset.prod_coe_sort F, ← Equiv.prod_comp φ, ← Equiv.prod_comp ν, coe_prod_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    rw [coe_qC, qEdge_eq_inc, sum_smul_eq_sum_fin r ν _ _ (psibar_root r),
      sum_smul_eq_sum_fin r ν _ _ (psi_root r)]
    rfl
  rw [hq, berezin_topV, hB]

/-- **Lemma 3.3 (fermionic matrix-tree theorem).** For a loop-free edge set `X`,
`[Ω_V] Π_{e∈X}(1 + q_e) = τ(V, X)`. -/
theorem topV_edgeProd (r : Fin n) (X : Finset (Sym2 (Fin n))) (hl : ∀ e ∈ X, ¬ e.IsDiag) :
    topV r (edgeProd r X) = ((Hamiltonian.spanningTrees X).card : ℤ) := by
  rw [edgeProd_eq_coe_prod, Finset.prod_one_add, coe_finset_sum, topV_sum]
  change ∑ t ∈ X.powerset, topV r (qProd r t) = _
  rw [← Finset.sum_subset (s₁ := X.powersetCard (n - 1)) (s₂ := X.powerset)
    (fun t ht => Finset.mem_powerset.2 (Finset.mem_powersetCard.1 ht).1)
    (fun t ht ht' => topV_qProd_of_card_ne r fun hc =>
      ht' (Finset.mem_powersetCard.2 ⟨Finset.mem_powerset.1 ht, hc⟩))]
  have h := sum_detSq_eq_card_spanningTreeSet X r hl
  rw [show spanningTreeSet X = Hamiltonian.spanningTrees X from rfl] at h
  rw [← h]
  refine Finset.sum_congr rfl fun F hF => ?_
  have hc : Fintype.card {u : Fin n // u ≠ r} = Fintype.card F := by
    rw [card_ne_root, Fintype.card_coe, (Finset.mem_powersetCard.1 hF).2]
  unfold detSq
  rw [dif_pos hc]
  exact topV_qProd r _

/-! ### Corollary 3.4 -/

/-- **Corollary 3.4** (with Lemma 3.1): `Σ_{X 2-factor} [Ω_V] Π_{e∈X}(1 + q_e) = n · #HC(G)`. -/
theorem fermionSum_eq (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : Fin n) :
    fermionSum G r = n * (Hamiltonian.hamCycles G).card := by
  rw [fermionSum, Finset.sum_congr rfl fun X hX =>
      topV_edgeProd r X (Hamiltonian.loopFree_of_mem_twoFactors G hX),
    ← Nat.cast_sum, ← Hamiltonian.n_mul_hamCycles_eq_sum, Nat.cast_mul]

/-- **Corollary 3.4**, written as a sum over all `X ⊆ E`:
`n · #HC(G) = Σ_{X ⊆ E} [every vertex has degree 2 in X] · [Ω_V] Π_{e∈X}(1 + q_e)`. -/
theorem n_mul_hamCycles_eq_sum_topV (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : Fin n) :
    (n * (Hamiltonian.hamCycles G).card : ℤ) =
      ∑ X ∈ G.edgeFinset.powerset,
        (if Hamiltonian.TwoRegular X then 1 else 0) * topV r (edgeProd r X) := by
  rw [← fermionSum_eq G r, fermionSum, Hamiltonian.twoFactors, Finset.sum_filter]
  refine Finset.sum_congr rfl fun X _ => ?_
  split_ifs <;> simp

end EthFollowup.ExactHC
