/-
# Blobs, pieces and the sign rule (module M6; `exact-hc-theorem.md` §4)

## Setup
* `Crossing G β m`: the crossing edges of `G` for the partition `β : Fin n → Fin g`, listed in the
  crossing order of `Fin m` as `e_k = s(s k, t k)` with `β (s k) < β (t k)`; injective and
  exhaustive. `Crossing.canonical G β` builds one. `X.chords : Chords g m` is the M3 chord data.
* `Label = {N, l0, l1, l2, l3}`, `Label.par` (π), `labelPar ℓ : Fin m → ZMod 2`.
* `pieceA r s ℓ = α_ℓ`, `pieceB r t ℓ = β_ℓ` (the table), `X.piece r ℓ k a`, `X.Gam r ℓ a = Γ_a(ℓ)`,
  `X.eps ℓ = ε(ℓ)`.
* `blob β a = V_a`, `Eint G β a = E_int(a)`, `deg`, `X.degL ℓ a v = deg_ℓ(v)`,
  `X.I r ℓ a = I_a(ℓ)` (sum over `x ⊆ E_int(a)`, top coefficient relative to `ω_a = Ω_{V_a}`).
* `evenSubring Γ = Λ⁰` with its `CommRing` instance (Fact 2.1), used for the bookkeeping.

## Results
* Lemma 4.1: `isHomog_pieceA/B`, `suppIn_pieceA/B`, `pieceA_mul_pieceB_N`,
  `sum_pieceA_mul_pieceB` / `Crossing.sum_pieces_edge` (`Σ_{ℓ≠N} α_ℓ β_ℓ = 1 + q_e`).
* Proposition 4.2: `Crossing.sign_rule`.
* Theorem 4.6: `Crossing.sum_eps_prod_I` (`Σ_ℓ ε(ℓ) Π_a I_a(ℓ) = fermionSum G r`) and
  `Crossing.sum_sigma_chi_I` (`Σ_ℓ Π_a σ_a χ_a(P) I_a = fermionSum G r`).
* Locality: `Crossing.sigma_congr`, `chi_congr`, `P_congr`, `Gam_congr`, `degL_congr`, `I_congr`
  (and generic `Chords.sigma_congr`, `chi_congr`, `P_congr_left/right`).
-/
import EthFollowup.ExactHC.Fermion
import EthFollowup.ExactHC.SignRule
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Prod.Lex

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset

noncomputable section

namespace Grass

variable {Γ : Type*} [Fintype Γ] [LinearOrder Γ]

/-- The even part `Λ⁰`, a subring. -/
def evenSubring (Γ : Type*) [Fintype Γ] [LinearOrder Γ] : Subring (Grass Γ) where
  carrier := {x | IsHomog 0 x}
  mul_mem' {x y} hx hy := (IsHomog.mul hx hy : IsHomog (0 + 0) (x * y))
  one_mem' := isHomog_one
  add_mem' hx hy := IsHomog.add hx hy
  zero_mem' := isHomog_zero 0
  neg_mem' hx := IsHomog.neg hx

/-- `Λ⁰` is commutative (Fact 2.1). -/
instance : CommRing ↥(evenSubring Γ) :=
  { (evenSubring Γ).toRing with
    mul_comm := fun x y => Subtype.ext (IsHomog.commute_of_even x.2 y) }

theorem mem_evenSubring {x : Grass Γ} : x ∈ evenSubring Γ ↔ IsHomog 0 x := Iff.rfl

theorem coe_list_prod_even (l : List (evenSubring Γ)) :
    ((l.prod : evenSubring Γ) : Grass Γ) = (l.map (↑)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih, Subring.coe_mul]

theorem coe_finset_prod_even {ι : Type*} (s : Finset ι) (f : ι → evenSubring Γ) (l : List ι)
    (hl : l.Nodup) (hs : ∀ i, i ∈ l ↔ i ∈ s) :
    ((∏ i ∈ s, f i : evenSubring Γ) : Grass Γ) = (l.map fun i => (f i : Grass Γ)).prod := by
  classical
  have : s = l.toFinset := by ext i; simp [hs]
  subst this
  rw [List.prod_toFinset _ hl, coe_list_prod_even, List.map_map]
  rfl

end Grass

/-! ### Generators: parity and support -/

open Grass

variable {n : ℕ}

theorem isHomog_psibar (r v : Fin n) : IsHomog 1 (psibar r v) := by
  unfold psibar; split_ifs
  · exact isHomog_zero 1
  · exact isHomog_gen _

theorem isHomog_psi (r v : Fin n) : IsHomog 1 (psi r v) := by
  unfold psi; split_ifs
  · exact isHomog_zero 1
  · exact isHomog_gen _

theorem gbarIdx_mem_genSet {r v : Fin n} {S : Finset (Fin n)} (hv : v ∈ S) (hr : v ≠ r) :
    gbarIdx v ∈ genSet r S := by
  simp only [genSet, mem_biUnion, mem_erase, mem_insert, mem_singleton]
  exact ⟨v, ⟨hr, hv⟩, Or.inl rfl⟩

theorem gIdx_mem_genSet {r v : Fin n} {S : Finset (Fin n)} (hv : v ∈ S) (hr : v ≠ r) :
    gIdx v ∈ genSet r S := by
  simp only [genSet, mem_biUnion, mem_erase, mem_insert, mem_singleton]
  exact ⟨v, ⟨hr, hv⟩, Or.inr rfl⟩

theorem suppIn_psibar {r v : Fin n} {S : Finset (Fin n)} (hv : v ∈ S) :
    SuppIn (genSet r S) (psibar r v) := by
  unfold psibar; split_ifs with h
  · exact suppIn_zero _
  · exact suppIn_gen (gbarIdx_mem_genSet hv h)

theorem suppIn_psi {r v : Fin n} {S : Finset (Fin n)} (hv : v ∈ S) :
    SuppIn (genSet r S) (psi r v) := by
  unfold psi; split_ifs with h
  · exact suppIn_zero _
  · exact suppIn_gen (gIdx_mem_genSet hv h)

theorem isHomog_omega (r v : Fin n) : IsHomog 0 (omega r v) :=
  ((isHomog_psibar r v).mul (isHomog_psi r v)).congr (by decide)

theorem isHomog_qPair (r i j : Fin n) : IsHomog 0 (qPair r i j) :=
  (((isHomog_psibar r i).sub (isHomog_psibar r j)).mul
    ((isHomog_psi r i).sub (isHomog_psi r j))).congr (by decide)

theorem isHomog_qEdge (r : Fin n) (e : Sym2 (Fin n)) : IsHomog 0 (qEdge r e) := by
  induction e using Sym2.ind with
  | _ i j => exact isHomog_qPair r i j

theorem suppIn_qPair {r i j : Fin n} {S : Finset (Fin n)} (hi : i ∈ S) (hj : j ∈ S) :
    SuppIn (genSet r S) (qPair r i j) :=
  ((suppIn_psibar hi).sub (suppIn_psibar hj)).mul ((suppIn_psi hi).sub (suppIn_psi hj))

theorem suppIn_qEdge {r : Fin n} {S : Finset (Fin n)} {e : Sym2 (Fin n)} (he : e ∈ S.sym2) :
    SuppIn (genSet r S) (qEdge r e) := by
  induction e using Sym2.ind with
  | _ i j =>
    rw [mem_sym2_iff] at he
    exact suppIn_qPair (he i (Sym2.mem_mk_left i j)) (he j (Sym2.mem_mk_right i j))

/-- `1 + q_e` as an element of `Λ⁰`. -/
def oneQ (r : Fin n) (e : Sym2 (Fin n)) : evenSubring (Fin (2 * n)) :=
  ⟨1 + qEdge r e, isHomog_one.add (isHomog_qEdge r e)⟩

/-- `edgeProd` as a (commutative) product in `Λ⁰`. -/
theorem edgeProd_eq (r : Fin n) (X : Finset (Sym2 (Fin n))) :
    edgeProd r X = ((∏ e ∈ X, oneQ r e : evenSubring (Fin (2 * n))) : Grass (Fin (2 * n))) := by
  rw [coe_finset_prod_even X (oneQ r) X.toList (nodup_toList X) (fun _ => mem_toList)]
  rfl

theorem isHomog_edgeProd (r : Fin n) (X : Finset (Sym2 (Fin n))) : IsHomog 0 (edgeProd r X) := by
  rw [edgeProd_eq]; exact Subtype.property _

theorem suppIn_edgeProd {r : Fin n} {S : Finset (Fin n)} {X : Finset (Sym2 (Fin n))}
    (hX : ∀ e ∈ X, e ∈ S.sym2) : SuppIn (genSet r S) (edgeProd r X) := by
  refine suppIn_list_prod _ fun x hx => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  exact (suppIn_one _).add (suppIn_qEdge (hX e (mem_toList.1 he)))

/-! ### Labels and pieces (the table of §4) -/

/-- The label alphabet `L = {N, 0, 1, 2, 3}`. -/
inductive Label
  | N
  | l0
  | l1
  | l2
  | l3
  deriving DecidableEq

namespace Label

instance : Fintype Label :=
  ⟨{N, l0, l1, l2, l3}, fun x => by cases x <;> simp⟩

/-- The parity `π(ℓ) = [ℓ ∈ {2,3}]`. -/
def par : Label → ℕ
  | l2 => 1
  | l3 => 1
  | _ => 0

/-- The parity in `ZMod 2`. -/
def parZ (ℓ : Label) : ZMod 2 := (ℓ.par : ZMod 2)

end Label

/-- `α_ℓ` for a crossing edge with low end `s`. -/
def pieceA (r s : Fin n) : Label → Grass (Fin (2 * n))
  | .N => 1
  | .l0 => 1
  | .l1 => psibar r s * psi r s
  | .l2 => psibar r s
  | .l3 => psi r s

/-- `β_ℓ` for a crossing edge with high end `t`. -/
def pieceB (r t : Fin n) : Label → Grass (Fin (2 * n))
  | .N => 1
  | .l0 => 1 + psibar r t * psi r t
  | .l1 => 1
  | .l2 => -psi r t
  | .l3 => psibar r t

/-- **Lemma 4.1(a)** for `α`. -/
theorem isHomog_pieceA (r s : Fin n) (ℓ : Label) : IsHomog ℓ.par (pieceA r s ℓ) := by
  cases ℓ
  · exact isHomog_one
  · exact isHomog_one
  · exact isHomog_omega r s
  · exact isHomog_psibar r s
  · exact isHomog_psi r s

/-- **Lemma 4.1(a)** for `β`. -/
theorem isHomog_pieceB (r t : Fin n) (ℓ : Label) : IsHomog ℓ.par (pieceB r t ℓ) := by
  cases ℓ
  · exact isHomog_one
  · exact isHomog_one.add (isHomog_omega r t)
  · exact isHomog_one
  · exact (isHomog_psi r t).neg
  · exact isHomog_psibar r t

theorem suppIn_pieceA {r s : Fin n} {S : Finset (Fin n)} (hs : s ∈ S) (ℓ : Label) :
    SuppIn (genSet r S) (pieceA r s ℓ) := by
  cases ℓ
  · exact suppIn_one _
  · exact suppIn_one _
  · exact (suppIn_psibar hs).mul (suppIn_psi hs)
  · exact suppIn_psibar hs
  · exact suppIn_psi hs

theorem suppIn_pieceB {r t : Fin n} {S : Finset (Fin n)} (ht : t ∈ S) (ℓ : Label) :
    SuppIn (genSet r S) (pieceB r t ℓ) := by
  cases ℓ
  · exact suppIn_one _
  · exact (suppIn_one _).add ((suppIn_psibar ht).mul (suppIn_psi ht))
  · exact suppIn_one _
  · exact (suppIn_psi ht).neg
  · exact suppIn_psibar ht

theorem isHomog_pieceA_mul_pieceB (r s t : Fin n) (ℓ : Label) :
    IsHomog 0 (pieceA r s ℓ * pieceB r t ℓ) :=
  ((isHomog_pieceA r s ℓ).mul (isHomog_pieceB r t ℓ)).congr
    (by rw [← two_mul]; exact (Nat.mul_mod_right 2 _))

/-- `α_ℓ β_ℓ ∈ Λ⁰`. -/
def pieceAB (r s t : Fin n) (ℓ : Label) : evenSubring (Fin (2 * n)) :=
  ⟨pieceA r s ℓ * pieceB r t ℓ, isHomog_pieceA_mul_pieceB r s t ℓ⟩

/-- **Lemma 4.1(b)**, first part: `α_N β_N = 1`. -/
theorem pieceA_mul_pieceB_N (r s t : Fin n) : pieceA r s .N * pieceB r t .N = 1 := mul_one 1

/-- **Lemma 4.1(b)**: `Σ_{ℓ ≠ N} α_ℓ β_ℓ = 1 + q_{st}`. -/
theorem sum_pieceA_mul_pieceB (r s t : Fin n) :
    ∑ ℓ ∈ univ.erase Label.N, pieceA r s ℓ * pieceB r t ℓ = 1 + qPair r s t := by
  have huniv : univ.erase Label.N = {Label.l0, Label.l1, Label.l2, Label.l3} := by decide
  rw [huniv, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_singleton]
  simp only [pieceA, pieceB, qPair]
  have h := (isHomog_psi r s).anticomm (isHomog_psibar r t)
  rw [h]
  noncomm_ring

/-! ### List helpers -/

section ListHelpers

variable {α : Type*}

theorem flatten_ofFn_succ {M : ℕ} (f : Fin (M + 1) → List α) :
    (List.ofFn f).flatten = f 0 ++ (List.ofFn fun i => f i.succ).flatten := by
  rw [List.ofFn_succ, List.flatten_cons]

theorem prod_map_flatten {R : Type*} [Monoid R] (y : α → R) :
    ∀ L : List (List α), (L.flatten.map y).prod = (L.map fun l => (l.map y).prod).prod
  | [] => rfl
  | l :: L => by
    rw [List.flatten_cons, List.map_append, List.prod_append, prod_map_flatten y L,
      List.map_cons, List.prod_cons]

theorem sum_map_flatten_pairs {M : ℕ} (u v : Fin M → α) (h : α → ℕ) :
    (((List.ofFn fun k => [u k, v k]).flatten).map h).sum = ∑ k, (h (u k) + h (v k)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [flatten_ofFn_succ, List.map_append, List.sum_append, ih (fun k => u k.succ)
      (fun k => v k.succ), Fin.sum_univ_succ]
    simp

theorem mem_flatten_ofFn {M : ℕ} (f : Fin M → List α) (x : α) :
    x ∈ (List.ofFn f).flatten ↔ ∃ i, x ∈ f i := by
  simp only [List.mem_flatten, List.mem_ofFn]
  constructor
  · rintro ⟨l, ⟨i, rfl⟩, hx⟩; exact ⟨i, hx⟩
  · rintro ⟨i, hx⟩; exact ⟨f i, ⟨i, rfl⟩, hx⟩

theorem pairwise_flatten_ofFn {M : ℕ} {R : α → α → Prop} (f : Fin M → List α)
    (h1 : ∀ i, (f i).Pairwise R) (h2 : ∀ i j, i < j → ∀ x ∈ f i, ∀ y ∈ f j, R x y) :
    (List.ofFn f).flatten.Pairwise R := by
  rw [List.pairwise_flatten]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
    exact h1 i
  · rw [List.pairwise_ofFn]
    exact h2

variable [LinearOrder α]

theorem wInv_append (p : α → ℕ) : ∀ l₁ l₂ : List α,
    Grass.wInv p (l₁ ++ l₂) = Grass.wInv p l₁ + Grass.wInv p l₂ +
      (l₁.map fun a => (l₂.map fun b => if b < a then p a * p b else 0).sum).sum
  | [], l₂ => by simp [Grass.wInv]
  | a :: l₁, l₂ => by
    rw [List.cons_append, Grass.wInv, Grass.wInv, wInv_append p l₁ l₂, List.map_append,
      List.sum_append, List.map_cons, List.sum_cons]
    ring

/-- The weighted inversion count of the list `u 0, v 0, u 1, v 1, …`. -/
theorem wInv_flatten_pairs (p : α → ℕ) {M : ℕ} (u v : Fin M → α) :
    Grass.wInv p ((List.ofFn fun k => [u k, v k]).flatten) =
      (∑ k, if v k < u k then p (u k) * p (v k) else 0) +
      ∑ k, ∑ l, if k < l then
        ((if u l < u k then p (u k) * p (u l) else 0) +
          (if v l < u k then p (u k) * p (v l) else 0)) +
        ((if u l < v k then p (v k) * p (u l) else 0) +
          (if v l < v k then p (v k) * p (v l) else 0)) else 0 := by
  induction M with
  | zero => simp [Grass.wInv]
  | succ M ih =>
    rw [flatten_ofFn_succ, wInv_append, ih (fun k => u k.succ) (fun k => v k.succ)]
    simp only [Grass.wInv, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      sum_map_flatten_pairs, Fin.sum_univ_succ, Fin.succ_lt_succ_iff,
      if_false, Fin.succ_pos, if_true, not_lt_zero', add_zero, zero_add]
    simp only [sum_add_distrib]
    ring

end ListHelpers

/-! ### Blobs, their generators and `Ω` -/

section BlobAlg

variable {g : ℕ}

/-- The blob `V_a = β⁻¹(a)`. -/
def blob (β : Fin n → Fin g) (a : Fin g) : Finset (Fin n) := univ.filter fun v => β v = a

@[simp] theorem mem_blob {β : Fin n → Fin g} {a : Fin g} {v : Fin n} : v ∈ blob β a ↔ β v = a := by
  unfold blob; rw [mem_filter]; simp

theorem gbarIdx_inj {v w : Fin n} (h : gbarIdx v = gbarIdx w) : v = w := by
  simp only [gbarIdx, Fin.ext_iff] at h; ext; omega

theorem gIdx_inj {v w : Fin n} (h : gIdx v = gIdx w) : v = w := by
  simp only [gIdx, Fin.ext_iff] at h; ext; omega

theorem gbarIdx_ne_gIdx (v w : Fin n) : gbarIdx v ≠ gIdx w := by
  simp only [gbarIdx, gIdx, ne_eq, Fin.ext_iff]; omega

theorem mem_genSet {r : Fin n} {S : Finset (Fin n)} {γ : Fin (2 * n)} :
    γ ∈ genSet r S ↔ ∃ v ∈ S, v ≠ r ∧ (γ = gbarIdx v ∨ γ = gIdx v) := by
  simp only [genSet, mem_biUnion, mem_erase, mem_insert, mem_singleton]
  constructor
  · rintro ⟨v, ⟨h1, h2⟩, h3⟩; exact ⟨v, h2, h1, h3⟩
  · rintro ⟨v, h2, h1, h3⟩; exact ⟨v, ⟨h1, h2⟩, h3⟩

theorem genSet_univ_eq (r : Fin n) (β : Fin n → Fin g) :
    genSet r univ = univ.biUnion fun a => genSet r (blob β a) := by
  ext γ
  simp only [mem_biUnion, mem_univ, true_and, mem_genSet, mem_blob]
  constructor
  · rintro ⟨v, h⟩; exact ⟨β v, v, rfl, h⟩
  · rintro ⟨a, v, -, h⟩; exact ⟨v, h⟩

theorem genSet_disjoint (r : Fin n) (β : Fin n → Fin g) :
    Pairwise fun a b => Disjoint (genSet r (blob β a)) (genSet r (blob β b)) := by
  intro a b hab
  rw [disjoint_left]
  intro γ ha hb
  rw [mem_genSet] at ha hb
  obtain ⟨v, hv, -, hv'⟩ := ha
  obtain ⟨w, hw, -, hw'⟩ := hb
  rw [mem_blob] at hv hw
  have : v = w := by
    rcases hv' with rfl | rfl <;> rcases hw' with h | h
    · exact gbarIdx_inj h
    · exact absurd h (gbarIdx_ne_gIdx v w)
    · exact absurd h.symm (gbarIdx_ne_gIdx w v)
    · exact gIdx_inj h
  subst this
  exact hab (hv.symm.trans hw)

theorem isSignedBasis_OmegaOf (r : Fin n) : ∀ l : List (Fin n), l.Nodup → (∀ v ∈ l, v ≠ r) →
    IsSignedBasis (l.toFinset.biUnion fun v => {gbarIdx v, gIdx v}) (OmegaOf r l)
  | [], _, _ => by
    simp only [List.toFinset_nil, biUnion_empty, OmegaOf, List.map_nil, List.prod_nil]
    exact isSignedBasis_e ∅
  | v :: l, hnd, hr => by
    rw [List.toFinset_cons, biUnion_insert]
    have hv : v ≠ r := hr v List.mem_cons_self
    have h1 : IsSignedBasis {gbarIdx v, gIdx v} (omega r v) := by
      unfold omega psibar psi
      rw [if_neg hv, if_neg hv, insert_eq]
      exact (isSignedBasis_e _).mul (isSignedBasis_e _)
        (disjoint_singleton.2 (gbarIdx_ne_gIdx v v))
    have hl := isSignedBasis_OmegaOf r l (List.nodup_cons.1 hnd).2
      (fun w hw => hr w (List.mem_cons_of_mem _ hw))
    have hd : Disjoint ({gbarIdx v, gIdx v} : Finset (Fin (2 * n)))
        (l.toFinset.biUnion fun v => {gbarIdx v, gIdx v}) := by
      rw [disjoint_left]
      intro γ hγ hγ'
      simp only [mem_biUnion, List.mem_toFinset, mem_insert, mem_singleton] at hγ hγ'
      obtain ⟨w, hw, hγw⟩ := hγ'
      have : v = w := by
        rcases hγ with rfl | rfl <;> rcases hγw with h | h
        · exact gbarIdx_inj h
        · exact absurd h (gbarIdx_ne_gIdx v w)
        · exact absurd h.symm (gbarIdx_ne_gIdx w v)
        · exact gIdx_inj h
      subst this
      exact (List.nodup_cons.1 hnd).1 hw
    have := h1.mul hl hd
    simpa only [OmegaOf, List.map_cons, List.prod_cons] using this

/-- `Ω_S = ±e_{Γ_S}`. -/
theorem isSignedBasis_OmegaSet (r : Fin n) (S : Finset (Fin n)) :
    IsSignedBasis (genSet r S) (OmegaSet r S) := by
  have := isSignedBasis_OmegaOf r ((S.erase r).sort (· ≤ ·)) ((S.erase r).sort_nodup (· ≤ ·))
    (fun v hv => ((mem_erase.1 ((mem_sort (· ≤ ·)).1 hv)).1))
  rwa [sort_toFinset] at this

/-- `ω_v ∈ Λ⁰`. -/
def omegaE (r v : Fin n) : evenSubring (Fin (2 * n)) := ⟨omega r v, isHomog_omega r v⟩

theorem OmegaSet_eq_prod (r : Fin n) (S : Finset (Fin n)) :
    OmegaSet r S = ((∏ v ∈ S.erase r, omegaE r v : evenSubring (Fin (2 * n))) :
      Grass (Fin (2 * n))) := by
  rw [coe_finset_prod_even (S.erase r) (omegaE r) ((S.erase r).sort (· ≤ ·))
    ((S.erase r).sort_nodup (· ≤ ·)) (fun _ => mem_sort (· ≤ ·))]
  rfl

theorem coe_prod_ofFn_even {M : ℕ} (f : Fin M → evenSubring (Fin (2 * n))) :
    (List.ofFn fun i => (f i : Grass (Fin (2 * n)))).prod =
      ((∏ i, f i : evenSubring (Fin (2 * n))) : Grass (Fin (2 * n))) := by
  rw [← Fin.prod_ofFn, coe_list_prod_even, List.map_ofFn]
  rfl

/-- `Ω_V = ω_0 ⋯ ω_{g-1}` with `ω_a = Ω_{V_a}`. -/
theorem OmegaSet_univ_eq (r : Fin n) (β : Fin n → Fin g) :
    OmegaSet r univ = (List.ofFn fun a => OmegaSet r (blob β a)).prod := by
  simp only [OmegaSet_eq_prod]
  rw [coe_prod_ofFn_even, ← prod_fiberwise (univ.erase r) β (omegaE r)]
  congr 2
  funext a
  congr 1
  ext v
  simp [mem_erase, mem_filter, mem_blob, and_comm]

/-- **Lemma 2.3** for the blob partition: `[Ω_V](x_0 ⋯ x_{g-1}) = Π_a [ω_a](x_a)`. -/
theorem topV_prod_blocks (r : Fin n) (β : Fin n → Fin g) (x : Fin g → Grass (Fin (2 * n)))
    (hx : ∀ a, SuppIn (genSet r (blob β a)) (x a)) :
    topV r (List.ofFn x).prod =
      ∏ a, topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a)) (x a) := by
  unfold topV
  rw [genSet_univ_eq r β, OmegaSet_univ_eq r β]
  exact topCoeff_prod_ofFn_blocks _ (genSet_disjoint r β) _
    (fun a => isSignedBasis_OmegaSet r _) x hx

theorem prod_ofFn_mul_of_even : ∀ {M : ℕ} (F H : Fin M → Grass (Fin (2 * n)))
    (_ : ∀ i, IsHomog 0 (F i)),
    (List.ofFn fun i => F i * H i).prod = (List.ofFn F).prod * (List.ofFn H).prod
  | 0, _, _, _ => by simp
  | M + 1, F, H, hF => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ (f := F), List.prod_cons,
      List.ofFn_succ (f := H), List.prod_cons,
      prod_ofFn_mul_of_even (fun i => F i.succ) (fun i => H i.succ) (fun i => hF i.succ)]
    have hc : IsHomog 0 (List.ofFn fun i => F i.succ).prod := by
      have := isHomog_prod_ofFn (fun i => F i.succ) (fun _ => 0) (fun i => hF i.succ)
      simpa using this
    rw [mul_assoc (F 0) (List.ofFn fun i => F i.succ).prod, ← mul_assoc _ (H 0),
      hc.commute_of_even (H 0)]
    simp only [mul_assoc]

theorem topCoeff_sum {ι : Type*} (A : Finset (Fin (2 * n))) (ω : Grass (Fin (2 * n)))
    (s : Finset ι) (f : ι → Grass (Fin (2 * n))) :
    topCoeff A ω (∑ i ∈ s, f i) = ∑ i ∈ s, topCoeff A ω (f i) := by
  unfold topCoeff; rw [coeff_sum, sum_mul]

end BlobAlg


/-! ### Locality of the sign factors (generic chord data) -/

namespace Chords

variable {g m : ℕ} (C : Chords g m)

theorem E_subset_delta_left (x y : Fin g) : C.E x y ⊆ C.delta x := by
  intro k hk
  simp only [E, delta, mem_filter, mem_univ, true_and] at hk ⊢
  exact Or.inl hk.1

theorem E_subset_delta_right (x y : Fin g) : C.E x y ⊆ C.delta y := by
  intro k hk
  simp only [E, delta, mem_filter, mem_univ, true_and] at hk ⊢
  exact Or.inr hk.2

/-- `σ_x` depends only on the parities on `δ(x)`. -/
theorem sigma_congr {π π' : Fin m → ZMod 2} {x : Fin g} (h : ∀ k ∈ C.delta x, π k = π' k) :
    C.sigma π x = C.sigma π' x := by
  unfold sigma
  congr 1
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  split_ifs with hkl
  · obtain ⟨-, hm, hs⟩ := hkl
    have hk : k ∈ C.delta x := hs ▸ C.mem_delta_shared_left k l
    have hl : l ∈ C.delta x := hs ▸ C.mem_delta_shared_right hm
    rw [h k hk, h l hl]
  · rfl

/-- `P_{xy}` depends only on the parities on `δ(x)`. -/
theorem P_congr_left {π π' : Fin m → ZMod 2} {x : Fin g} (h : ∀ k ∈ C.delta x, π k = π' k)
    (y : Fin g) : C.P π x y = C.P π' x y :=
  sum_congr rfl fun k hk => h k (C.E_subset_delta_left x y hk)

/-- `P_{xy}` depends only on the parities on `δ(y)`. -/
theorem P_congr_right {π π' : Fin m → ZMod 2} {y : Fin g} (h : ∀ k ∈ C.delta y, π k = π' k)
    (x : Fin g) : C.P π x y = C.P π' x y :=
  sum_congr rfl fun k hk => h k (C.E_subset_delta_right x y hk)

/-- `χ_x(y)` depends only on the parities on `δ(x)` and on the copies `y` on `Q_x`. -/
theorem chi_congr {π π' : Fin m → ZMod 2} {x : Fin g} (h : ∀ k ∈ C.delta x, π k = π' k)
    {y y' : Fin g × Fin g → ZMod 2} (hy : ∀ p ∈ Q x, y p = y' p) :
    C.chi π x y = C.chi π' x y' := by
  unfold chi
  congr 1
  refine sum_congr rfl fun p hp => ?_
  rw [hy p hp]
  congr 1
  exact sum_congr rfl fun b _ => C.P_congr_left h b

end Chords

/-! ### Crossing edges -/

/-- The parities `π_k = π(ℓ_k)` of a labelling. -/
def labelPar {m : ℕ} (ℓ : Fin m → Label) : Fin m → ZMod 2 := fun k => (ℓ k).parZ

/-- The crossing edges of `G` for the partition `β`, listed as `e_0, …, e_{m-1}` in the
crossing order of `Fin m`: `e_k = {s k, t k}` with low end `s k` and high end `t k`
(`β (s k) < β (t k)`); every crossing edge is listed exactly once. -/
structure Crossing {g : ℕ} (G : SimpleGraph (Fin n)) (β : Fin n → Fin g) (m : ℕ) where
  /-- Low end `s_k`. -/
  s : Fin m → Fin n
  /-- High end `t_k`. -/
  t : Fin m → Fin n
  lt : ∀ k, β (s k) < β (t k)
  adj : ∀ k, G.Adj (s k) (t k)
  inj : ∀ k l, s k = s l → t k = t l → k = l
  exhaust : ∀ u v, G.Adj u v → β u < β v → ∃ k, s k = u ∧ t k = v

namespace Crossing

variable {g m : ℕ} {G : SimpleGraph (Fin n)} {β : Fin n → Fin g} (X : Crossing G β m)
  (r : Fin n)

/-- The chord data `a_k = β(s_k) < b_k = β(t_k)` (M3). -/
def chords : Chords g m := ⟨fun k => β (X.s k), fun k => β (X.t k), X.lt⟩

@[simp] theorem chords_a (k : Fin m) : X.chords.a k = β (X.s k) := rfl
@[simp] theorem chords_b (k : Fin m) : X.chords.b k = β (X.t k) := rfl

theorem mem_delta {a : Fin g} {k : Fin m} :
    k ∈ X.chords.delta a ↔ β (X.s k) = a ∨ β (X.t k) = a := by
  unfold Chords.delta
  rw [mem_filter]
  simp

/-- The edge `e_k = {s_k, t_k}`. -/
def edge (k : Fin m) : Sym2 (Fin n) := s(X.s k, X.t k)

/-- `ε(ℓ)`. -/
def eps (ℓ : Fin m → Label) : ℤ := X.chords.eps (labelPar ℓ)

/-- The piece `γ_{k,a}(ℓ)` of `k` at blob `a`: `α_{ℓ_k}(k)` if `a = a_k`, else `β_{ℓ_k}(k)`. -/
def piece (ℓ : Fin m → Label) (k : Fin m) (a : Fin g) : Grass (Fin (2 * n)) :=
  if β (X.s k) = a then pieceA r (X.s k) (ℓ k) else pieceB r (X.t k) (ℓ k)

/-- `Γ_a(ℓ)`: the product of the pieces at `a`, in increasing crossing order. -/
def Gam (ℓ : Fin m → Label) (a : Fin g) : Grass (Fin (2 * n)) :=
  (((X.chords.delta a).sort (· ≤ ·)).map fun k => X.piece r ℓ k a).prod

theorem isHomog_piece (ℓ : Fin m → Label) (k : Fin m) (a : Fin g) :
    IsHomog (ℓ k).par (X.piece r ℓ k a) := by
  unfold piece; split_ifs
  · exact isHomog_pieceA _ _ _
  · exact isHomog_pieceB _ _ _

/-- **Proposition 4.2 (sign rule).**
`Π_k α_{ℓ_k}(k) β_{ℓ_k}(k) = ε(ℓ) · Γ_0(ℓ) ⋯ Γ_{g-1}(ℓ)`. -/
theorem sign_rule (ℓ : Fin m → Label) :
    (List.ofFn fun k => pieceA r (X.s k) (ℓ k) * pieceB r (X.t k) (ℓ k)).prod =
      X.eps ℓ • (List.ofFn fun a => X.Gam r ℓ a).prod := by
  classical
  -- keys `(blob, k)`, ordered lexicographically
  let y : Lex (Fin g × Fin m) → Grass (Fin (2 * n)) :=
    fun x => X.piece r ℓ (ofLex x).2 (ofLex x).1
  let p : Lex (Fin g × Fin m) → ℕ := fun x => (ℓ (ofLex x).2).par
  have hy : ∀ x, IsHomog (p x) (y x) := fun x => X.isHomog_piece r ℓ _ _
  let u : Fin m → Lex (Fin g × Fin m) := fun k => toLex (β (X.s k), k)
  let v : Fin m → Lex (Fin g × Fin m) := fun k => toLex (β (X.t k), k)
  let l₁ := (List.ofFn fun k => [u k, v k]).flatten
  let L₂ := (List.ofFn fun a =>
    ((X.chords.delta a).sort (· ≤ ·)).map fun k => (toLex (a, k) : Lex (Fin g × Fin m))).flatten
  have hne : ∀ k, β (X.s k) ≠ β (X.t k) := fun k => (X.lt k).ne
  -- the left side is the product along `l₁`
  have hl₁ : (List.ofFn fun k => pieceA r (X.s k) (ℓ k) * pieceB r (X.t k) (ℓ k)).prod =
      (l₁.map y).prod := by
    rw [prod_map_flatten, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    simp [y, u, v, piece, hne k]
  -- the sorted list is `L₂`, whose product is `Γ_0 ⋯ Γ_{g-1}`
  have hL₂ : (L₂.map y).prod = (List.ofFn fun a => X.Gam r ℓ a).prod := by
    rw [prod_map_flatten, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun a => ?_)
    simp only [Function.comp_apply, List.map_map, Gam]
    rfl
  have hsort : l₁.insertionSort (· ≤ ·) = L₂ := by
    have hL₂lt : L₂.Pairwise (· < ·) := by
      refine pairwise_flatten_ofFn _ (fun a => ?_) (fun a b hab x hx z hz => ?_)
      · rw [List.pairwise_map]
        refine ((X.chords.delta a).pairwise_sort (· ≤ ·)).imp₂ (fun k l hkl hne' => ?_)
          ((X.chords.delta a).sort_nodup (· ≤ ·))
        rw [Prod.Lex.toLex_lt_toLex]
        exact Or.inr ⟨rfl, lt_of_le_of_ne hkl hne'⟩
      · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hz
        rw [Prod.Lex.toLex_lt_toLex]
        exact Or.inl hab
    have hl₁ne : l₁.Pairwise (· ≠ ·) := by
      refine pairwise_flatten_ofFn _ (fun k => ?_) (fun k l hkl x hx z hz => ?_)
      · refine List.Pairwise.cons (fun z hz => ?_) (List.pairwise_singleton _ _)
        rw [List.mem_singleton] at hz
        subst hz
        intro h
        exact hne k (congrArg (fun z => (ofLex z).1) h)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hz
        intro h
        have : (ofLex x).2 = (ofLex z).2 := by rw [h]
        rcases hx with rfl | rfl <;> rcases hz with rfl | rfl <;>
          exact hkl.ne this
    have hperm : List.Perm l₁ L₂ := by
      refine List.perm_of_nodup_nodup_toFinset_eq hl₁ne (hL₂lt.imp ne_of_lt) ?_
      ext x
      simp only [List.mem_toFinset, l₁, L₂, mem_flatten_ofFn, List.mem_cons, List.not_mem_nil,
        or_false, List.mem_map, mem_sort, mem_delta, u, v]
      constructor
      · rintro ⟨k, rfl | rfl⟩
        · exact ⟨_, k, Or.inl rfl, rfl⟩
        · exact ⟨_, k, Or.inr rfl, rfl⟩
      · rintro ⟨a, k, hk | hk, rfl⟩
        · exact ⟨k, Or.inl (by rw [hk])⟩
        · exact ⟨k, Or.inr (by rw [hk])⟩
    exact ((List.perm_insertionSort _ l₁).trans hperm).eq_of_pairwise'
      (List.pairwise_insertionSort _ _) (hL₂lt.imp le_of_lt)
  -- the Koszul sign is `ε`
  have hw : Grass.wInv p l₁ =
      ∑ k, ∑ l, if k < l then (ℓ k).par * (ℓ l).par * X.chords.cross k l else 0 := by
    rw [wInv_flatten_pairs]
    have h0 : ∀ k, ¬ v k < u k := fun k h => by
      rw [Prod.Lex.toLex_lt_toLex] at h
      rcases h with h | h
      · exact lt_asymm h (X.lt k)
      · exact lt_irrefl _ h.2
    simp only [h0, if_false, sum_const_zero, zero_add]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    by_cases hkl : k < l
    · rw [if_pos hkl, if_pos hkl]
      have key : ∀ (c d : Fin g), (toLex (d, l) : Lex (Fin g × Fin m)) < toLex (c, k) ↔ d < c :=
        fun c d => by
          rw [Prod.Lex.toLex_lt_toLex]
          constructor
          · rintro (h | ⟨-, h⟩)
            · exact h
            · exact absurd h (lt_asymm hkl)
          · exact Or.inl
      simp only [u, v, key, p, ofLex_toLex]
      rw [Chords.cross_eq]
      simp only [mul_add, mul_ite, mul_one, mul_zero, add_assoc]
      rfl
    · rw [if_neg hkl, if_neg hkl]
  rw [hl₁, Grass.prod_map_eq_insertionSort y p hy, hsort, hL₂, hw, eps]
  congr 1
  exact (Chords.eps_eq_neg_one_pow X.chords (fun k => (ℓ k).par)).symm

/-! ### Edges: internal and crossing -/

section Edges

variable [DecidableRel G.Adj]

omit X r in
/-- `E_int(a)`: the edges of `G` with both ends in `V_a`. -/
def Eint (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (β : Fin n → Fin g) (a : Fin g) :
    Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter fun e => e ∈ (blob β a).sym2

omit X r in
theorem mem_Eint {a : Fin g} {e : Sym2 (Fin n)} :
    e ∈ Eint G β a ↔ e ∈ G.edgeFinset ∧ ∀ v ∈ e, β v = a := by
  unfold Eint; rw [mem_filter, mem_sym2_iff]; simp only [mem_blob]

omit X r in
theorem Eint_subset (a : Fin g) : Eint G β a ⊆ G.edgeFinset := fun _ he => (mem_Eint.1 he).1

omit X r in
theorem Eint_disjoint : Pairwise fun a b => Disjoint (Eint G β a) (Eint G β b) := by
  intro a b hab
  rw [disjoint_left]
  intro e ha hb
  induction e using Sym2.ind with
  | _ u w =>
    exact hab (((mem_Eint.1 ha).2 u (Sym2.mem_mk_left u w)).symm.trans
      ((mem_Eint.1 hb).2 u (Sym2.mem_mk_left u w)))

theorem edge_mem_edgeFinset (k : Fin m) : X.edge k ∈ G.edgeFinset := by
  rw [edge, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact X.adj k

theorem edge_not_mem_Eint (k : Fin m) (a : Fin g) : X.edge k ∉ Eint G β a := by
  intro h
  have h1 := (mem_Eint.1 h).2 (X.s k) (Sym2.mem_mk_left _ _)
  have h2 := (mem_Eint.1 h).2 (X.t k) (Sym2.mem_mk_right _ _)
  exact (X.lt k).ne (h1.trans h2.symm)

theorem edge_injective : Function.Injective X.edge := by
  intro k l h
  rw [edge, edge, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact X.inj k l h1 h2
  · have hk := X.lt k
    have hl := X.lt l
    rw [h1, h2] at hk
    exact absurd (lt_trans hk hl) (lt_irrefl _)

theorem mem_edge {k : Fin m} {v : Fin n} : v ∈ X.edge k ↔ X.s k = v ∨ X.t k = v := by
  rw [edge, Sym2.mem_iff]; constructor <;> rintro (h | h) <;> simp [h]

/-- Every edge is internal to a blob or is a listed crossing edge. -/
theorem edge_cases {e : Sym2 (Fin n)} (he : e ∈ G.edgeFinset) :
    (∃ a, e ∈ Eint G β a) ∨ ∃ k, X.edge k = e := by
  induction e using Sym2.ind with
  | _ u w =>
    have hadj : G.Adj u w := by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases lt_trichotomy (β u) (β w) with h | h | h
    · obtain ⟨k, hs, ht⟩ := X.exhaust u w hadj h
      exact Or.inr ⟨k, by rw [edge, hs, ht]⟩
    · refine Or.inl ⟨β u, mem_Eint.2 ⟨he, fun v hv => ?_⟩⟩
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · rfl
      · exact h.symm
    · obtain ⟨k, hs, ht⟩ := X.exhaust w u hadj.symm h
      exact Or.inr ⟨k, by rw [edge, hs, ht, Sym2.eq_swap]⟩

end Edges

/-! ### Blob sums -/

section BlobSums

variable [DecidableRel G.Adj]

omit X r in
/-- `deg_x(v)`: the number of edges of `x` at `v`. -/
def deg (x : Finset (Sym2 (Fin n))) (v : Fin n) : ℕ := (x.filter fun e => v ∈ e).card

/-- `deg_ℓ(v) = #{k ∈ δ(a) : v ∈ {s_k, t_k}, ℓ_k ≠ N}`. -/
def degL (ℓ : Fin m → Label) (a : Fin g) (v : Fin n) : ℕ :=
  ((X.chords.delta a).filter fun k => ℓ k ≠ Label.N ∧ (X.s k = v ∨ X.t k = v)).card

/-- The degree indicator `Π_{v ∈ V_a} [deg_x(v) + deg_ℓ(v) = 2]`. -/
def degInd (ℓ : Fin m → Label) (a : Fin g) (x : Finset (Sym2 (Fin n))) : ℤ :=
  if ∀ v ∈ blob β a, deg x v + X.degL ℓ a v = 2 then 1 else 0

/-- The blob sum `I_a(ℓ) = Σ_{x ⊆ E_int(a)} Π_{v∈V_a}[deg_x(v) + deg_ℓ(v) = 2] · [ω_a](F_a(x) Γ_a(ℓ))`,
with `ω_a = Ω_{V_a}` and `F_a(x) = Π_{e ∈ x} (1 + q_e)`. -/
def I (ℓ : Fin m → Label) (a : Fin g) : ℤ :=
  ∑ x ∈ (Eint G β a).powerset, X.degInd ℓ a x *
    topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a)) (edgeProd r x * X.Gam r ℓ a)

end BlobSums

/-! ### Theorem 4.6 -/

section Factorisation

variable [DecidableRel G.Adj]

theorem suppIn_piece {ℓ : Fin m → Label} {k : Fin m} {a : Fin g} (hk : k ∈ X.chords.delta a) :
    SuppIn (genSet r (blob β a)) (X.piece r ℓ k a) := by
  unfold piece
  split_ifs with h
  · exact suppIn_pieceA (mem_blob.2 h) _
  · have : β (X.t k) = a := ((X.mem_delta).1 hk).resolve_left h
    exact suppIn_pieceB (mem_blob.2 this) _

theorem suppIn_Gam (ℓ : Fin m → Label) (a : Fin g) :
    SuppIn (genSet r (blob β a)) (X.Gam r ℓ a) := by
  refine suppIn_list_prod _ fun z hz => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hz
  exact X.suppIn_piece r ((mem_sort (· ≤ ·)).1 hk)

theorem suppIn_blobTerm (ℓ : Fin m → Label) {a : Fin g} {x : Finset (Sym2 (Fin n))}
    (hx : x ⊆ Eint G β a) :
    SuppIn (genSet r (blob β a)) (edgeProd r x * X.Gam r ℓ a) :=
  (suppIn_edgeProd fun e he => by
    rw [mem_sym2_iff]; exact fun v hv => mem_blob.2 ((mem_Eint.1 (hx he)).2 v hv)).mul
    (X.suppIn_Gam r ℓ a)

/-- Steps 1–4 of the proof of Theorem 4.6: expand `Π_a I_a`, apply Lemma 2.3, pull the even
`F_a` to the front and apply the sign rule. -/
theorem eps_mul_prod_I (ℓ : Fin m → Label) :
    X.eps ℓ * ∏ a, X.I r ℓ a =
      ∑ xs ∈ Fintype.piFinset (fun a => (Eint G β a).powerset),
        (∏ a, X.degInd ℓ a (xs a)) *
          topV r ((List.ofFn fun a => edgeProd r (xs a)).prod *
            (List.ofFn fun k => pieceA r (X.s k) (ℓ k) * pieceB r (X.t k) (ℓ k)).prod) := by
  unfold I
  rw [prod_univ_sum, mul_sum]
  refine sum_congr rfl fun xs hxs => ?_
  rw [Fintype.mem_piFinset] at hxs
  have hsub : ∀ a, xs a ⊆ Eint G β a := fun a => mem_powerset.1 (hxs a)
  rw [prod_mul_distrib, ← topV_prod_blocks r β _ (fun a => X.suppIn_blobTerm r ℓ (hsub a)),
    prod_ofFn_mul_of_even _ _ (fun a => isHomog_edgeProd r (xs a)), X.sign_rule r ℓ,
    mul_smul_comm]
  unfold topV
  rw [topCoeff_zsmul]
  ring

/-- The support `{k : ℓ_k ≠ N}` of a labelling. -/
def supp (ℓ : Fin m → Label) : Finset (Fin m) := univ.filter fun k => ℓ k ≠ Label.N

/-- `deg_T(v) = #{k ∈ δ(a) ∩ T : v ∈ {s_k, t_k}}`. -/
def degT (T : Finset (Fin m)) (a : Fin g) (v : Fin n) : ℕ :=
  ((X.chords.delta a).filter fun k => k ∈ T ∧ (X.s k = v ∨ X.t k = v)).card

/-- The degree indicator of all blobs, as a function of the support `T`. -/
def indT (xs : Fin g → Finset (Sym2 (Fin n))) (T : Finset (Fin m)) : ℤ :=
  ∏ a, if ∀ v ∈ blob β a, deg (xs a) v + X.degT T a v = 2 then 1 else 0

theorem prod_degInd (ℓ : Fin m → Label) (xs : Fin g → Finset (Sym2 (Fin n))) :
    ∏ a, X.degInd ℓ a (xs a) = X.indT xs (supp ℓ) := by
  have h : ∀ a v, X.degL ℓ a v = X.degT (supp ℓ) a v := fun a v => by
    unfold degL degT supp
    congr 1
    ext k
    simp
  unfold indT degInd
  simp only [h]

theorem coe_finset_sum_even {ι : Type*} (s : Finset ι) (f : ι → evenSubring (Fin (2 * n))) :
    ((∑ i ∈ s, f i : evenSubring (Fin (2 * n))) : Grass (Fin (2 * n))) =
      ∑ i ∈ s, (f i : Grass (Fin (2 * n))) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, Subring.coe_add, ih]

/-- Steps 5–6: summing the pieces over the labellings with support `T` gives
`Π_{k ∈ T} (1 + q_{e_k})` (Lemma 4.1(b) and distributivity). -/
theorem sum_fiber_pieces (T : Finset (Fin m)) :
    ∑ ℓ ∈ univ.filter (fun ℓ : Fin m → Label => supp ℓ = T),
        (List.ofFn fun k => pieceA r (X.s k) (ℓ k) * pieceB r (X.t k) (ℓ k)).prod =
      ((∏ k ∈ T, oneQ r (X.edge k) : evenSubring (Fin (2 * n))) : Grass (Fin (2 * n))) := by
  classical
  let S : Fin m → Finset Label := fun k => if k ∈ T then univ.erase Label.N else {Label.N}
  have hfib : univ.filter (fun ℓ : Fin m → Label => supp ℓ = T) = Fintype.piFinset S := by
    ext ℓ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, S]
    constructor
    · rintro rfl k
      by_cases h : ℓ k = Label.N <;> simp [supp, h]
    · intro h
      ext k
      have hk := h k
      by_cases hT : k ∈ T
      · simp only [hT, if_true, mem_erase] at hk
        simp [supp, hk.1, hT]
      · simp only [hT, if_false, mem_singleton] at hk
        simp [supp, hk, hT]
  have hpt : ∀ ℓ : Fin m → Label,
      (List.ofFn fun k => pieceA r (X.s k) (ℓ k) * pieceB r (X.t k) (ℓ k)).prod =
        ((∏ k, pieceAB r (X.s k) (X.t k) (ℓ k) : evenSubring (Fin (2 * n))) :
          Grass (Fin (2 * n))) := fun ℓ => by
    rw [← coe_prod_ofFn_even]; rfl
  simp only [hpt]
  rw [← coe_finset_sum_even, hfib, ← prod_univ_sum,
    show (∏ k ∈ T, oneQ r (X.edge k)) = ∏ k, if k ∈ T then oneQ r (X.edge k) else 1 by
      rw [prod_ite_mem, univ_inter]]
  congr 1
  refine prod_congr rfl fun k _ => ?_
  apply Subtype.ext
  by_cases hT : k ∈ T
  · simp only [S, hT, if_true]
    rw [coe_finset_sum_even]
    exact (sum_pieceA_mul_pieceB r (X.s k) (X.t k))
  · simp only [S, hT, if_false, sum_singleton]
    exact pieceA_mul_pieceB_N r (X.s k) (X.t k)

/-- Steps 5–6 for a fixed choice `xs` of internal edges. -/
theorem sum_labels_fixed (xs : Fin g → Finset (Sym2 (Fin n))) :
    ∑ ℓ : Fin m → Label, (∏ a, X.degInd ℓ a (xs a)) *
        topV r ((List.ofFn fun a => edgeProd r (xs a)).prod *
          (List.ofFn fun k => pieceA r (X.s k) (ℓ k) * pieceB r (X.t k) (ℓ k)).prod) =
      ∑ T : Finset (Fin m), X.indT xs T *
        topV r ((List.ofFn fun a => edgeProd r (xs a)).prod *
          ((∏ k ∈ T, oneQ r (X.edge k) : evenSubring (Fin (2 * n))) : Grass (Fin (2 * n)))) := by
  rw [← sum_fiberwise univ supp]
  refine sum_congr rfl fun T _ => ?_
  rw [← X.sum_fiber_pieces r T, mul_sum, topV, topCoeff_sum, mul_sum]
  refine sum_congr rfl fun ℓ hℓ => ?_
  have h := X.prod_degInd ℓ xs
  rw [(mem_filter.1 hℓ).2] at h
  rw [h]
  rfl

/-- The edge set `x_int ∪ {e_k : k ∈ T}` determined by internal edges `xs` and support `T`. -/
def unionEdges (xs : Fin g → Finset (Sym2 (Fin n))) (T : Finset (Fin m)) :
    Finset (Sym2 (Fin n)) :=
  (univ.biUnion xs) ∪ T.image X.edge

theorem mem_unionEdges {xs : Fin g → Finset (Sym2 (Fin n))} {T : Finset (Fin m)}
    {e : Sym2 (Fin n)} :
    e ∈ X.unionEdges xs T ↔ (∃ a, e ∈ xs a) ∨ ∃ k ∈ T, X.edge k = e := by
  simp [unionEdges]

theorem deg_unionEdges {xs : Fin g → Finset (Sym2 (Fin n))} (hxs : ∀ a, xs a ⊆ Eint G β a)
    (T : Finset (Fin m)) {a : Fin g} {v : Fin n} (hv : β v = a) :
    deg (X.unionEdges xs T) v = deg (xs a) v + X.degT T a v := by
  have hfil : (X.unionEdges xs T).filter (fun e => v ∈ e) =
      (xs a).filter (fun e => v ∈ e) ∪ (T.filter fun k => v ∈ X.edge k).image X.edge := by
    ext e
    simp only [mem_filter, mem_union, mem_image, X.mem_unionEdges]
    constructor
    · rintro ⟨⟨b, hb⟩ | ⟨k, hk, rfl⟩, hve⟩
      · have : b = a := ((mem_Eint.1 (hxs b hb)).2 v hve).symm.trans hv
        subst this
        exact Or.inl ⟨hb, hve⟩
      · exact Or.inr ⟨k, ⟨hk, hve⟩, rfl⟩
    · rintro (⟨hb, hve⟩ | ⟨k, ⟨hk, hve⟩, rfl⟩)
      · exact ⟨Or.inl ⟨a, hb⟩, hve⟩
      · exact ⟨Or.inr ⟨k, hk, rfl⟩, hve⟩
  have hdisj : Disjoint ((xs a).filter (fun e => v ∈ e))
      ((T.filter fun k => v ∈ X.edge k).image X.edge) := by
    rw [disjoint_left]
    intro e he he'
    obtain ⟨k, -, rfl⟩ := mem_image.1 he'
    exact X.edge_not_mem_Eint k a (hxs a (mem_filter.1 he).1)
  unfold deg
  rw [hfil, card_union_of_disjoint hdisj, card_image_of_injective _ X.edge_injective]
  congr 1
  unfold degT
  congr 1
  ext k
  simp only [mem_filter, X.mem_edge, X.mem_delta]
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨?_, hk, h⟩
    rcases h with h | h
    · exact Or.inl (h ▸ hv)
    · exact Or.inr (h ▸ hv)
  · rintro ⟨-, hk, h⟩
    exact ⟨hk, h⟩

theorem twoRegular_unionEdges_iff {xs : Fin g → Finset (Sym2 (Fin n))}
    (hxs : ∀ a, xs a ⊆ Eint G β a) (T : Finset (Fin m)) :
    Hamiltonian.TwoRegular (X.unionEdges xs T) ↔
      ∀ a, ∀ v ∈ blob β a, deg (xs a) v + X.degT T a v = 2 := by
  constructor
  · intro h a v hv
    rw [← X.deg_unionEdges hxs T (mem_blob.1 hv)]
    exact h v
  · intro h v
    have := h (β v) v (mem_blob.2 rfl)
    rw [← X.deg_unionEdges hxs T rfl] at this
    exact this

theorem edgeProd_unionEdges {xs : Fin g → Finset (Sym2 (Fin n))} (hxs : ∀ a, xs a ⊆ Eint G β a)
    (T : Finset (Fin m)) :
    edgeProd r (X.unionEdges xs T) = (List.ofFn fun a => edgeProd r (xs a)).prod *
      ((∏ k ∈ T, oneQ r (X.edge k) : evenSubring (Fin (2 * n))) : Grass (Fin (2 * n))) := by
  have hdisj : Disjoint (univ.biUnion xs) (T.image X.edge) := by
    rw [disjoint_left]
    intro e he he'
    obtain ⟨a, -, hea⟩ := mem_biUnion.1 he
    obtain ⟨k, -, rfl⟩ := mem_image.1 he'
    exact X.edge_not_mem_Eint k a (hxs a hea)
  have hpd : ((univ : Finset (Fin g)) : Set (Fin g)).PairwiseDisjoint xs :=
    fun a _ b _ hab => (Eint_disjoint hab).mono (hxs a) (hxs b)
  simp only [edgeProd_eq]
  rw [coe_prod_ofFn_even, ← Subring.coe_mul, unionEdges, prod_union hdisj, prod_biUnion hpd,
    prod_image (fun k _ l _ h => X.edge_injective h)]

/-- Step 7: regrouping by the edge set `x = x_int ∪ 1_T` gives the 2-factor sum. -/
theorem sum_internal_crossing :
    ∑ xs ∈ Fintype.piFinset (fun a => (Eint G β a).powerset), ∑ T : Finset (Fin m),
        X.indT xs T * topV r ((List.ofFn fun a => edgeProd r (xs a)).prod *
          ((∏ k ∈ T, oneQ r (X.edge k) : evenSubring (Fin (2 * n))) : Grass (Fin (2 * n)))) =
      fermionSum G r := by
  classical
  unfold fermionSum Hamiltonian.twoFactors
  rw [sum_filter, ← sum_product']
  refine sum_nbij' (fun p => X.unionEdges p.1 p.2)
    (fun Y => (fun a => Y.filter (· ∈ Eint G β a), univ.filter fun k => X.edge k ∈ Y))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨xs, T⟩ hp
    have hxs : ∀ a, xs a ⊆ Eint G β a := fun a =>
      mem_powerset.1 (Fintype.mem_piFinset.1 (mem_product.1 hp).1 a)
    rw [mem_powerset]
    intro e he
    rcases X.mem_unionEdges.1 he with ⟨a, ha⟩ | ⟨k, -, rfl⟩
    · exact Eint_subset a (hxs a ha)
    · exact X.edge_mem_edgeFinset k
  · intro Y _
    rw [mem_product, Fintype.mem_piFinset]
    exact ⟨fun a => mem_powerset.2 fun e he => (mem_filter.1 he).2, mem_univ _⟩
  · rintro ⟨xs, T⟩ hp
    have hxs : ∀ a, xs a ⊆ Eint G β a := fun a =>
      mem_powerset.1 (Fintype.mem_piFinset.1 (mem_product.1 hp).1 a)
    refine Prod.ext (funext fun a => ?_) ?_
    · ext e
      simp only [mem_filter, X.mem_unionEdges]
      constructor
      · rintro ⟨⟨b, hb⟩ | ⟨k, -, rfl⟩, he⟩
        · by_cases hab : a = b
          · exact hab ▸ hb
          · exact absurd he (disjoint_left.1 (Eint_disjoint (Ne.symm hab)) (hxs b hb))
        · exact absurd he (X.edge_not_mem_Eint k a)
      · intro he
        exact ⟨Or.inl ⟨a, he⟩, hxs a he⟩
    · ext k
      simp only [mem_filter, mem_univ, true_and, X.mem_unionEdges]
      constructor
      · rintro (⟨b, hb⟩ | ⟨l, hl, hlk⟩)
        · exact absurd (hxs b hb) (X.edge_not_mem_Eint k b)
        · exact X.edge_injective hlk ▸ hl
      · intro hk
        exact Or.inr ⟨k, hk, rfl⟩
  · intro Y hY
    have hY' : Y ⊆ G.edgeFinset := mem_powerset.1 hY
    ext e
    simp only [X.mem_unionEdges, mem_filter, mem_univ, true_and]
    constructor
    · rintro (⟨a, he, -⟩ | ⟨k, hk, rfl⟩)
      · exact he
      · exact hk
    · intro he
      rcases X.edge_cases (hY' he) with ⟨a, ha⟩ | ⟨k, rfl⟩
      · exact Or.inl ⟨a, he, ha⟩
      · exact Or.inr ⟨k, he, rfl⟩
  · rintro ⟨xs, T⟩ hp
    have hxs : ∀ a, xs a ⊆ Eint G β a := fun a =>
      mem_powerset.1 (Fintype.mem_piFinset.1 (mem_product.1 hp).1 a)
    simp only
    rw [← X.edgeProd_unionEdges r hxs T, indT, prod_boole]
    by_cases h : ∀ a, ∀ v ∈ blob β a, deg (xs a) v + X.degT T a v = 2
    · rw [if_pos (fun a _ => h a), if_pos ((X.twoRegular_unionEdges_iff hxs T).2 h), one_mul]
    · rw [if_neg (fun h' => h fun a => h' a (mem_univ a)),
        if_neg (fun h' => h ((X.twoRegular_unionEdges_iff hxs T).1 h')), zero_mul]

/-- **Theorem 4.6 (blob factorisation), first equality** (up to Lemma 3.3 / Cor. 3.4, which turn
`fermionSum G r` into `n · #HC(G)`): `Σ_{ℓ ∈ L^m} ε(ℓ) Π_a I_a(ℓ) = Σ_{X 2-factor} [Ω_V] Π_{e∈X}(1+q_e)`. -/
theorem sum_eps_prod_I :
    ∑ ℓ : Fin m → Label, X.eps ℓ * ∏ a, X.I r ℓ a = fermionSum G r := by
  simp only [X.eps_mul_prod_I r]
  rw [sum_comm]
  rw [← X.sum_internal_crossing r]
  refine sum_congr rfl fun xs _ => ?_
  exact X.sum_labels_fixed r xs

/-- **Theorem 4.6, second equality**: with `π_k = π(ℓ_k)` and correct parity copies
`y_{cd} = P_{cd}(ℓ)`, `Σ_ℓ Π_a σ_a(ℓ) χ_a(ℓ, P(ℓ)) I_a(ℓ) = fermionSum G r`. -/
theorem sum_sigma_chi_I :
    ∑ ℓ : Fin m → Label, ∏ a, X.chords.sigma (labelPar ℓ) a *
        X.chords.chi (labelPar ℓ) a (fun p => X.chords.P (labelPar ℓ) p.1 p.2) * X.I r ℓ a =
      fermionSum G r := by
  rw [← X.sum_eps_prod_I r]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [prod_mul_distrib, eps,
    X.chords.eps_eq_prod_sigma_chi (labelPar ℓ) (fun _ p => X.chords.P (labelPar ℓ) p.1 p.2)
      (fun _ _ _ => rfl)]

end Factorisation

/-! ### Locality (what the network of §5 needs) -/

section Locality

variable [DecidableRel G.Adj]

theorem labelPar_congr {ℓ ℓ' : Fin m → Label} {a : Fin g}
    (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k) :
    ∀ k ∈ X.chords.delta a, labelPar ℓ k = labelPar ℓ' k := fun k hk => by
  simp only [labelPar, h k hk]

/-- `σ_a(ℓ)` depends only on `ℓ|δ(a)`. -/
theorem sigma_congr {ℓ ℓ' : Fin m → Label} {a : Fin g} (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k) :
    X.chords.sigma (labelPar ℓ) a = X.chords.sigma (labelPar ℓ') a :=
  X.chords.sigma_congr (X.labelPar_congr h)

/-- `χ_a(ℓ, y)` depends only on `ℓ|δ(a)` and on the copy bits `y|Q_a`. -/
theorem chi_congr {ℓ ℓ' : Fin m → Label} {a : Fin g} (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k)
    {y y' : Fin g × Fin g → ZMod 2} (hy : ∀ p ∈ Chords.Q a, y p = y' p) :
    X.chords.chi (labelPar ℓ) a y = X.chords.chi (labelPar ℓ') a y' :=
  X.chords.chi_congr (X.labelPar_congr h) hy

/-- `P_{cd}(ℓ)` depends only on `ℓ|δ(c)` (node `c` computes the parities it sends). -/
theorem P_congr {ℓ ℓ' : Fin m → Label} {c : Fin g} (h : ∀ k ∈ X.chords.delta c, ℓ k = ℓ' k)
    (d : Fin g) : X.chords.P (labelPar ℓ) c d = X.chords.P (labelPar ℓ') c d :=
  X.chords.P_congr_left (X.labelPar_congr h) d

theorem Gam_congr {ℓ ℓ' : Fin m → Label} {a : Fin g} (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k) :
    X.Gam r ℓ a = X.Gam r ℓ' a := by
  unfold Gam
  congr 1
  refine List.map_congr_left fun k hk => ?_
  unfold piece
  rw [h k ((mem_sort (· ≤ ·)).1 hk)]

theorem degL_congr {ℓ ℓ' : Fin m → Label} {a : Fin g} (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k)
    (v : Fin n) : X.degL ℓ a v = X.degL ℓ' a v := by
  unfold degL
  congr 1
  refine filter_congr fun k hk => ?_
  rw [h k hk]

/-- `I_a(ℓ)` depends only on `ℓ|δ(a)`. -/
theorem I_congr {ℓ ℓ' : Fin m → Label} {a : Fin g} (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k) :
    X.I r ℓ a = X.I r ℓ' a := by
  unfold I degInd
  simp only [X.degL_congr h, X.Gam_congr r h]

end Locality

/-- **Lemma 4.1(b)** for the crossing edge `e_k`. -/
theorem sum_pieces_edge (k : Fin m) :
    ∑ ℓ ∈ univ.erase Label.N, pieceA r (X.s k) ℓ * pieceB r (X.t k) ℓ = 1 + qEdge r (X.edge k) :=
  sum_pieceA_mul_pieceB r (X.s k) (X.t k)

end Crossing

/-! ### Existence of a crossing order -/

/-- The ordered crossing pairs `(u, v)` with `G.Adj u v` and `β u < β v`. -/
def crossPairs {g : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (β : Fin n → Fin g) :
    Finset (Fin n × Fin n) :=
  univ.filter fun p => G.Adj p.1 p.2 ∧ β p.1 < β p.2

/-- A crossing order always exists: enumerate `crossPairs G β`. -/
def Crossing.canonical {g : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (β : Fin n → Fin g) : Crossing G β (crossPairs G β).card where
  s k := ((crossPairs G β).equivFin.symm k).1.1
  t k := ((crossPairs G β).equivFin.symm k).1.2
  lt k := ((mem_filter.1 ((crossPairs G β).equivFin.symm k).2).2).2
  adj k := ((mem_filter.1 ((crossPairs G β).equivFin.symm k).2).2).1
  inj k l h1 h2 := (crossPairs G β).equivFin.symm.injective (Subtype.ext (Prod.ext h1 h2))
  exhaust u v huv hlt := by
    have hp : (u, v) ∈ crossPairs G β := mem_filter.2 ⟨mem_univ _, huv, hlt⟩
    refine ⟨(crossPairs G β).equivFin ⟨(u, v), hp⟩, ?_, ?_⟩ <;> simp

end

end EthFollowup.ExactHC
