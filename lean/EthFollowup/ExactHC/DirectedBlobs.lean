/-
# Directed pieces and the directed blob factorisation (TSP-2, `research/tsp-theorem.md` §3.2)

The directed analogue of `Blobs.lean` + `Weighted.lean`, for a digraph `A : Finset (Fin n × Fin n)`
with arc weights `w : Fin n × Fin n → ℕ` and an integer `z` (the Kronecker substitution `z = 2^b`
of §3.2; `z = 1` counts directed Hamiltonian cycles).

## Setup
* `DLabel = {N, d0, d2}` (the alphabet `L_d` of §3.2), parity `π(d2) = 1`, `π(N) = π(d0) = 0`.
* `arcOf tl s t`: the arc with low end `s` and high end `t`, oriented `s → t` if `tl` ("tail is
  the low end") and `t → s` otherwise.
* `dpieceA r tl s ℓ = α_ℓ`, `dpieceB r tl t ℓ = β_ℓ`: the table of §3.2 (without the scalar
  `Y^{w_a}`, which is carried by the blob of the low end, as in `Weighted.lean`):

  |        | tail low (`tl`)          | head low (`¬tl`)          |
  |--------|--------------------------|---------------------------|
  | `d0`   | `α = 1 + ψ̄_sψ_s, β = 1`  | `α = 1, β = 1 + ψ̄_tψ_t`   |
  | `d2`   | `α = ψ̄_s, β = −ψ_t`      | `α = ψ_s, β = ψ̄_t`        |

  and `α_N = β_N = 1`.
* `DCrossing A β m`: the crossing arcs of `A` for `β : Fin n → Fin g`, listed in a crossing order
  as `arcOf (tl k) (s k) (t k)` with `β (s k) < β (t k)`; injective and exhaustive
  (`DCrossing.canonical` builds one).
* `X.Iw r z w ℓ a`: the weighted directed blob sum
  `z^{w_ℓ(a)} Σ_{x ⊆ A_int(a)} Π_{v∈V_a}[out = in = 1] z^{w(x)} [ω_a](F_a(x) Γ_a(ℓ))`,
  `F_a(x) = Π_{a∈x}(1 + p_a)`, the degrees counting the arcs of `x` and the crossing arcs with
  label `≠ N`.

## Results
* **Lemma 3.4**: `isHomog_dpieceA/B` (Π1), `dpieceA_mul_dpieceB_N` and `sum_dpieces`
  (Π2: `Σ_{ℓ≠N} α_ℓβ_ℓ = 1 + p_a`, both orientations; root ends are included because
  `ψ̄_r = ψ_r = 0`).
* `Chords.sign_rule_gen`: the sign rule (Proposition 1.1) for arbitrary homogeneous pieces;
  `DCrossing.sign_rule` its directed instance.
* **Theorem 1.2 for the directed data**: `DCrossing.sum_eps_prod_Iw`, `DCrossing.sum_sigma_chi_Iw`
  and `dblob_factorisation_w`:
  `Σ_{ℓ ∈ L_d^m} Π_a σ_a(ℓ) χ_a(ℓ,P(ℓ)) I^w_a(ℓ) = Σ_{H ∈ DHC(A)} z^{w(H)}`;
  `dblob_factorisation` (`z = 1`): `= #DHC(A)`.
* Locality (`DCrossing.Iw_congr`, `sigma_congr`, `chi_congr`, `P_congr`) and the size bound
  `DCrossing.wtL_le`, as needed by a network layer.
-/
import EthFollowup.ExactHC.DirectedMatrixTree
import EthFollowup.ExactHC.Blobs

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset Grass

noncomputable section

/-! ### The generic sign rule -/

namespace Chords

variable {g m : ℕ} (C : Chords g m)

theorem mem_delta_iff {x : Fin g} {k : Fin m} : k ∈ C.delta x ↔ C.a k = x ∨ C.b k = x := by
  unfold delta
  rw [mem_filter]
  simp

/-- **Sign rule (Proposition 1.1)** for arbitrary pieces: if every piece `pc k x` is homogeneous of
parity `p k`, then `Π_k pc_k(a_k) pc_k(b_k) = ε(p) · Γ_0 ⋯ Γ_{g-1}`, where `Γ_x` is the product
of the pieces at `x` in increasing crossing order. -/
theorem sign_rule_gen {Γ : Type*} [Fintype Γ] [LinearOrder Γ] (pc : Fin m → Fin g → Grass Γ)
    (p : Fin m → ℕ) (hp : ∀ k x, IsHomog (p k) (pc k x)) :
    (List.ofFn fun k => pc k (C.a k) * pc k (C.b k)).prod =
      C.eps (fun k => (p k : ZMod 2)) •
        (List.ofFn fun x => (((C.delta x).sort (· ≤ ·)).map fun k => pc k x).prod).prod := by
  classical
  let y : Lex (Fin g × Fin m) → Grass Γ := fun x => pc (ofLex x).2 (ofLex x).1
  let q : Lex (Fin g × Fin m) → ℕ := fun x => p (ofLex x).2
  have hy : ∀ x, IsHomog (q x) (y x) := fun x => hp _ _
  let u : Fin m → Lex (Fin g × Fin m) := fun k => toLex (C.a k, k)
  let v : Fin m → Lex (Fin g × Fin m) := fun k => toLex (C.b k, k)
  let l₁ := (List.ofFn fun k => [u k, v k]).flatten
  let L₂ := (List.ofFn fun x =>
    ((C.delta x).sort (· ≤ ·)).map fun k => (toLex (x, k) : Lex (Fin g × Fin m))).flatten
  have hne : ∀ k, C.a k ≠ C.b k := fun k => (C.a_lt_b k).ne
  have hl₁ : (List.ofFn fun k => pc k (C.a k) * pc k (C.b k)).prod = (l₁.map y).prod := by
    rw [prod_map_flatten, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    simp [y, u, v]
  have hL₂ : (L₂.map y).prod =
      (List.ofFn fun x => (((C.delta x).sort (· ≤ ·)).map fun k => pc k x).prod).prod := by
    rw [prod_map_flatten, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun x => ?_)
    simp only [Function.comp_apply, List.map_map]
    rfl
  have hsort : l₁.insertionSort (· ≤ ·) = L₂ := by
    have hL₂lt : L₂.Pairwise (· < ·) := by
      refine pairwise_flatten_ofFn _ (fun x => ?_) (fun x z hxz e he f hf => ?_)
      · rw [List.pairwise_map]
        refine ((C.delta x).pairwise_sort (· ≤ ·)).imp₂ (fun k l hkl hne' => ?_)
          ((C.delta x).sort_nodup (· ≤ ·))
        rw [Prod.Lex.toLex_lt_toLex]
        exact Or.inr ⟨rfl, lt_of_le_of_ne hkl hne'⟩
      · obtain ⟨k, -, rfl⟩ := List.mem_map.1 he
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hf
        rw [Prod.Lex.toLex_lt_toLex]
        exact Or.inl hxz
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
        or_false, List.mem_map, mem_sort, C.mem_delta_iff, u, v]
      constructor
      · rintro ⟨k, rfl | rfl⟩
        · exact ⟨_, k, Or.inl rfl, rfl⟩
        · exact ⟨_, k, Or.inr rfl, rfl⟩
      · rintro ⟨x, k, hk | hk, rfl⟩
        · exact ⟨k, Or.inl (by rw [hk])⟩
        · exact ⟨k, Or.inr (by rw [hk])⟩
    exact ((List.perm_insertionSort _ l₁).trans hperm).eq_of_pairwise'
      (List.pairwise_insertionSort _ _) (hL₂lt.imp le_of_lt)
  have hw : Grass.wInv q l₁ = ∑ k, ∑ l, if k < l then p k * p l * C.cross k l else 0 := by
    rw [wInv_flatten_pairs]
    have h0 : ∀ k, ¬ v k < u k := fun k h => by
      rw [Prod.Lex.toLex_lt_toLex] at h
      rcases h with h | h
      · exact lt_asymm h (C.a_lt_b k)
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
      simp only [u, v, key, q, ofLex_toLex]
      rw [Chords.cross_eq]
      simp only [mul_add, mul_ite, mul_one, mul_zero, add_assoc]
    · rw [if_neg hkl, if_neg hkl]
  rw [hl₁, Grass.prod_map_eq_insertionSort y q hy, hsort, hL₂, hw]
  congr 1
  exact (C.eps_eq_neg_one_pow p).symm

end Chords

variable {n : ℕ}

/-! ### Arc factors in `Λ⁰` -/

theorem isHomog_pArc (r : Fin n) (a : Fin n × Fin n) : IsHomog 0 (pArc r a) :=
  ((isHomog_psibar r a.1).mul ((isHomog_psi r a.1).sub (isHomog_psi r a.2))).congr (by decide)

theorem suppIn_pArc {r : Fin n} {S : Finset (Fin n)} {a : Fin n × Fin n} (h1 : a.1 ∈ S)
    (h2 : a.2 ∈ S) : SuppIn (genSet r S) (pArc r a) :=
  (suppIn_psibar h1).mul ((suppIn_psi h1).sub (suppIn_psi h2))

/-- `1 + p_a ∈ Λ⁰`. -/
def oneP (r : Fin n) (a : Fin n × Fin n) : evenSubring (Fin (2 * n)) :=
  ⟨1 + pArc r a, isHomog_one.add (isHomog_pArc r a)⟩

theorem arcProd_eq (r : Fin n) (X : Finset (Fin n × Fin n)) :
    arcProd r X = ((∏ a ∈ X, oneP r a : evenSubring (Fin (2 * n))) : Grass (Fin (2 * n))) := by
  rw [coe_finset_prod_even X (oneP r) X.toList (nodup_toList X) (fun _ => mem_toList)]
  rfl

theorem isHomog_arcProd (r : Fin n) (X : Finset (Fin n × Fin n)) : IsHomog 0 (arcProd r X) := by
  rw [arcProd_eq]; exact Subtype.property _

theorem suppIn_arcProd {r : Fin n} {S : Finset (Fin n)} {X : Finset (Fin n × Fin n)}
    (hX : ∀ a ∈ X, a.1 ∈ S ∧ a.2 ∈ S) : SuppIn (genSet r S) (arcProd r X) := by
  refine suppIn_list_prod _ fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  have h := hX a (mem_toList.1 ha)
  exact (suppIn_one _).add (suppIn_pArc h.1 h.2)

/-! ### Directed labels and pieces (the table of §3.2) -/

/-- The directed label alphabet `L_d = {N, 0, 2}`. -/
inductive DLabel
  | N
  | d0
  | d2
  deriving DecidableEq

namespace DLabel

instance : Fintype DLabel :=
  ⟨{N, d0, d2}, fun x => by cases x <;> simp⟩

/-- The parity `π(2) = 1`, `π(N) = π(0) = 0`. -/
def par : DLabel → ℕ
  | d2 => 1
  | _ => 0

end DLabel

/-- The parities `π_k = π(ℓ_k)` of a directed labelling. -/
def dlabelPar {m : ℕ} (ℓ : Fin m → DLabel) : Fin m → ZMod 2 := fun k => ((ℓ k).par : ZMod 2)

/-- The arc with low end `s` and high end `t`: `s → t` if the tail is the low end (`tl`), else
`t → s`. -/
def arcOf (tl : Bool) (s t : Fin n) : Fin n × Fin n := if tl then (s, t) else (t, s)

/-- `α_ℓ` at the low end `s`. -/
def dpieceA (r : Fin n) (tl : Bool) (s : Fin n) : DLabel → Grass (Fin (2 * n))
  | .N => 1
  | .d0 => if tl then 1 + psibar r s * psi r s else 1
  | .d2 => if tl then psibar r s else psi r s

/-- `β_ℓ` at the high end `t`. -/
def dpieceB (r : Fin n) (tl : Bool) (t : Fin n) : DLabel → Grass (Fin (2 * n))
  | .N => 1
  | .d0 => if tl then 1 else 1 + psibar r t * psi r t
  | .d2 => if tl then -psi r t else psibar r t

/-- **Lemma 3.4 (Π1)** for `α`. -/
theorem isHomog_dpieceA (r : Fin n) (tl : Bool) (s : Fin n) (ℓ : DLabel) :
    IsHomog ℓ.par (dpieceA r tl s ℓ) := by
  cases ℓ <;> cases tl
  · exact isHomog_one
  · exact isHomog_one
  · exact isHomog_one
  · exact isHomog_one.add (isHomog_omega r s)
  · exact isHomog_psi r s
  · exact isHomog_psibar r s

/-- **Lemma 3.4 (Π1)** for `β`. -/
theorem isHomog_dpieceB (r : Fin n) (tl : Bool) (t : Fin n) (ℓ : DLabel) :
    IsHomog ℓ.par (dpieceB r tl t ℓ) := by
  cases ℓ <;> cases tl
  · exact isHomog_one
  · exact isHomog_one
  · exact isHomog_one.add (isHomog_omega r t)
  · exact isHomog_one
  · exact isHomog_psibar r t
  · exact (isHomog_psi r t).neg

theorem suppIn_dpieceA {r s : Fin n} {S : Finset (Fin n)} (hs : s ∈ S) (tl : Bool) (ℓ : DLabel) :
    SuppIn (genSet r S) (dpieceA r tl s ℓ) := by
  cases ℓ <;> cases tl
  · exact suppIn_one _
  · exact suppIn_one _
  · exact suppIn_one _
  · exact (suppIn_one _).add ((suppIn_psibar hs).mul (suppIn_psi hs))
  · exact suppIn_psi hs
  · exact suppIn_psibar hs

theorem suppIn_dpieceB {r t : Fin n} {S : Finset (Fin n)} (ht : t ∈ S) (tl : Bool) (ℓ : DLabel) :
    SuppIn (genSet r S) (dpieceB r tl t ℓ) := by
  cases ℓ <;> cases tl
  · exact suppIn_one _
  · exact suppIn_one _
  · exact (suppIn_one _).add ((suppIn_psibar ht).mul (suppIn_psi ht))
  · exact suppIn_one _
  · exact suppIn_psibar ht
  · exact (suppIn_psi ht).neg

theorem isHomog_dpieceA_mul_dpieceB (r : Fin n) (tl : Bool) (s t : Fin n) (ℓ : DLabel) :
    IsHomog 0 (dpieceA r tl s ℓ * dpieceB r tl t ℓ) :=
  ((isHomog_dpieceA r tl s ℓ).mul (isHomog_dpieceB r tl t ℓ)).congr
    (by rw [← two_mul]; exact (Nat.mul_mod_right 2 _))

/-- `α_ℓ β_ℓ ∈ Λ⁰`. -/
def dpieceAB (r : Fin n) (tl : Bool) (s t : Fin n) (ℓ : DLabel) : evenSubring (Fin (2 * n)) :=
  ⟨dpieceA r tl s ℓ * dpieceB r tl t ℓ, isHomog_dpieceA_mul_dpieceB r tl s t ℓ⟩

/-- **Lemma 3.4 (Π2)**, first part: `α_N β_N = 1`. -/
theorem dpieceA_mul_dpieceB_N (r : Fin n) (tl : Bool) (s t : Fin n) :
    dpieceA r tl s .N * dpieceB r tl t .N = 1 := mul_one 1

/-- **Lemma 3.4 (Π2)**: `Σ_{ℓ≠N} α_ℓ β_ℓ = 1 + p_a` for the arc `a = arcOf tl s t`, in both
orientations (and with root ends, since `ψ̄_r = ψ_r = 0`). -/
theorem sum_dpieces (r : Fin n) (tl : Bool) (s t : Fin n) :
    ∑ ℓ ∈ univ.erase DLabel.N, dpieceA r tl s ℓ * dpieceB r tl t ℓ = 1 + pArc r (arcOf tl s t) := by
  have huniv : univ.erase DLabel.N = {DLabel.d0, DLabel.d2} := by decide
  rw [huniv, sum_insert (by decide), sum_singleton]
  cases tl
  · simp only [dpieceA, dpieceB, arcOf, pArc, Bool.false_eq_true, if_false]
    have h := (isHomog_psi r s).anticomm (isHomog_psibar r t)
    rw [h]
    noncomm_ring
  · simp only [dpieceA, dpieceB, arcOf, pArc, if_true]
    noncomm_ring

/-! ### Directed crossing orders -/

/-- The crossing arcs of `A` for `β`, listed in the crossing order of `Fin m`: arc `k` is
`arcOf (tl k) (s k) (t k)`, with low end `s k` and high end `t k` (`β (s k) < β (t k)`); every
crossing arc is listed exactly once. -/
structure DCrossing {g : ℕ} (A : Finset (Fin n × Fin n)) (β : Fin n → Fin g) (m : ℕ) where
  /-- Low end `s_k`. -/
  s : Fin m → Fin n
  /-- High end `t_k`. -/
  t : Fin m → Fin n
  /-- Whether the tail of the arc is its low end. -/
  tl : Fin m → Bool
  lt : ∀ k, β (s k) < β (t k)
  mem : ∀ k, arcOf (tl k) (s k) (t k) ∈ A
  inj : Function.Injective fun k => arcOf (tl k) (s k) (t k)
  exhaust : ∀ e ∈ A, β e.1 ≠ β e.2 → ∃ k, arcOf (tl k) (s k) (t k) = e

namespace DCrossing

variable {g m : ℕ} {A : Finset (Fin n × Fin n)} {β : Fin n → Fin g} (X : DCrossing A β m)
  (r : Fin n)

/-- The chord data `a_k = β(s_k) < b_k = β(t_k)`. -/
def chords : Chords g m := ⟨fun k => β (X.s k), fun k => β (X.t k), X.lt⟩

@[simp] theorem chords_a (k : Fin m) : X.chords.a k = β (X.s k) := rfl
@[simp] theorem chords_b (k : Fin m) : X.chords.b k = β (X.t k) := rfl

theorem mem_delta {a : Fin g} {k : Fin m} :
    k ∈ X.chords.delta a ↔ β (X.s k) = a ∨ β (X.t k) = a := X.chords.mem_delta_iff

/-- The crossing arc `k`. -/
def arc (k : Fin m) : Fin n × Fin n := arcOf (X.tl k) (X.s k) (X.t k)

theorem arc_ends (k : Fin m) :
    ((X.arc k).1 = X.s k ∧ (X.arc k).2 = X.t k) ∨ ((X.arc k).1 = X.t k ∧ (X.arc k).2 = X.s k) := by
  unfold arc arcOf
  cases X.tl k <;> simp

theorem arc_injective : Function.Injective X.arc := X.inj

theorem arc_mem (k : Fin m) : X.arc k ∈ A := X.mem k

/-- `ε(ℓ)`. -/
def eps (ℓ : Fin m → DLabel) : ℤ := X.chords.eps (dlabelPar ℓ)

/-- The piece of arc `k` at blob `a`: `α_{ℓ_k}` if `a` holds the low end, else `β_{ℓ_k}`. -/
def piece (ℓ : Fin m → DLabel) (k : Fin m) (a : Fin g) : Grass (Fin (2 * n)) :=
  if β (X.s k) = a then dpieceA r (X.tl k) (X.s k) (ℓ k) else dpieceB r (X.tl k) (X.t k) (ℓ k)

/-- `Γ_a(ℓ)`: the product of the pieces at `a`, in increasing crossing order. -/
def Gam (ℓ : Fin m → DLabel) (a : Fin g) : Grass (Fin (2 * n)) :=
  (((X.chords.delta a).sort (· ≤ ·)).map fun k => X.piece r ℓ k a).prod

theorem isHomog_piece (ℓ : Fin m → DLabel) (k : Fin m) (a : Fin g) :
    IsHomog (ℓ k).par (X.piece r ℓ k a) := by
  unfold piece; split_ifs
  · exact isHomog_dpieceA _ _ _ _
  · exact isHomog_dpieceB _ _ _ _

/-- **Sign rule** for the directed pieces:
`Π_k α_{ℓ_k}(k) β_{ℓ_k}(k) = ε(ℓ) · Γ_0(ℓ) ⋯ Γ_{g-1}(ℓ)`. -/
theorem sign_rule (ℓ : Fin m → DLabel) :
    (List.ofFn fun k => dpieceA r (X.tl k) (X.s k) (ℓ k) * dpieceB r (X.tl k) (X.t k) (ℓ k)).prod =
      X.eps ℓ • (List.ofFn fun a => X.Gam r ℓ a).prod := by
  have h := X.chords.sign_rule_gen (fun k a => X.piece r ℓ k a) (fun k => (ℓ k).par)
    (fun k a => X.isHomog_piece r ℓ k a)
  have hne : ∀ k, β (X.s k) ≠ β (X.t k) := fun k => (X.lt k).ne
  simp only [chords_a, chords_b, piece, if_true, hne, if_false] at h
  exact h

/-! ### Arcs: internal and crossing -/

omit X r in
/-- `A_int(a)`: the arcs of `A` with both ends in `V_a`. -/
def Aint (A : Finset (Fin n × Fin n)) (β : Fin n → Fin g) (a : Fin g) : Finset (Fin n × Fin n) :=
  A.filter fun e => β e.1 = a ∧ β e.2 = a

omit X r in
theorem mem_Aint {a : Fin g} {e : Fin n × Fin n} :
    e ∈ Aint A β a ↔ e ∈ A ∧ β e.1 = a ∧ β e.2 = a := mem_filter

omit X r in
theorem Aint_subset (a : Fin g) : Aint A β a ⊆ A := fun _ he => (mem_Aint.1 he).1

omit X r in
theorem Aint_disjoint : Pairwise fun a b => Disjoint (Aint A β a) (Aint A β b) := by
  intro a b hab
  rw [disjoint_left]
  intro e ha hb
  exact hab ((mem_Aint.1 ha).2.1.symm.trans (mem_Aint.1 hb).2.1)

theorem arc_not_mem_Aint (k : Fin m) (a : Fin g) : X.arc k ∉ Aint A β a := by
  intro h
  obtain ⟨-, h1, h2⟩ := mem_Aint.1 h
  rcases X.arc_ends k with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1] at h1; rw [e2] at h2; exact (X.lt k).ne (h1.trans h2.symm)
  · rw [e1] at h1; rw [e2] at h2; exact (X.lt k).ne (h2.trans h1.symm)

/-- Every arc is internal to a blob or is a listed crossing arc. -/
theorem arc_cases {e : Fin n × Fin n} (he : e ∈ A) :
    (∃ a, e ∈ Aint A β a) ∨ ∃ k, X.arc k = e := by
  by_cases h : β e.1 = β e.2
  · exact Or.inl ⟨β e.1, mem_Aint.2 ⟨he, rfl, h.symm⟩⟩
  · obtain ⟨k, hk⟩ := X.exhaust e he h
    exact Or.inr ⟨k, hk⟩

/-- If an end of the crossing arc `k` lies in `V_a`, then `k ∈ δ(a)`. -/
theorem mem_delta_of_end {k : Fin m} {a : Fin g} {v : Fin n} (hv : β v = a)
    (h : (X.arc k).1 = v ∨ (X.arc k).2 = v) : k ∈ X.chords.delta a := by
  rw [mem_delta]
  rcases X.arc_ends k with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases h with h | h
  · exact Or.inl (by rw [← e1, h, hv])
  · exact Or.inr (by rw [← e2, h, hv])
  · exact Or.inr (by rw [← e1, h, hv])
  · exact Or.inl (by rw [← e2, h, hv])

/-! ### Degrees and blob sums -/

omit X r in
/-- The degree `#{e ∈ x : proj e = v}` (`proj = Prod.fst`: out-degree, `Prod.snd`: in-degree). -/
def pdeg (proj : Fin n × Fin n → Fin n) (x : Finset (Fin n × Fin n)) (v : Fin n) : ℕ :=
  (x.filter fun e => proj e = v).card

/-- The labelled degree `#{k ∈ δ(a) : ℓ_k ≠ N, proj(arc k) = v}`. -/
def pdegL (proj : Fin n × Fin n → Fin n) (ℓ : Fin m → DLabel) (a : Fin g) (v : Fin n) : ℕ :=
  ((X.chords.delta a).filter fun k => ℓ k ≠ DLabel.N ∧ proj (X.arc k) = v).card

/-- The constraint `Π_{v ∈ V_a} [out_x(v) + out_ℓ(v) = 1 ∧ in_x(v) + in_ℓ(v) = 1]`. -/
def degInd (ℓ : Fin m → DLabel) (a : Fin g) (x : Finset (Fin n × Fin n)) : ℤ :=
  if ∀ v ∈ blob β a, pdeg Prod.fst x v + X.pdegL Prod.fst ℓ a v = 1 ∧
      pdeg Prod.snd x v + X.pdegL Prod.snd ℓ a v = 1 then 1 else 0

variable (z : ℤ) (w : Fin n × Fin n → ℕ)

/-- `w_ℓ(a)`: the weight of the crossing arcs with low end in `V_a` and label `≠ N`. -/
def wtL (ℓ : Fin m → DLabel) (a : Fin g) : ℕ :=
  ∑ k ∈ (X.chords.delta a).filter (fun k => β (X.s k) = a ∧ ℓ k ≠ DLabel.N), w (X.arc k)

/-- The weight `Σ_{k ∈ T} w(arc k)` of a set of crossing arcs. -/
def wtT (T : Finset (Fin m)) : ℕ := ∑ k ∈ T, w (X.arc k)

/-- **The weighted directed blob sum**
`I^w_a(ℓ) = z^{w_ℓ(a)} Σ_{x ⊆ A_int(a)} Π_{v∈V_a}[out = in = 1] z^{w(x)} [ω_a](F_a(x) Γ_a(ℓ))`. -/
def Iw (ℓ : Fin m → DLabel) (a : Fin g) : ℤ :=
  z ^ X.wtL w ℓ a * ∑ x ∈ (Aint A β a).powerset, X.degInd ℓ a x * z ^ arcWt w x *
    topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a)) (arcProd r x * X.Gam r ℓ a)

/-! ### Locality and size -/

theorem dlabelPar_congr {ℓ ℓ' : Fin m → DLabel} {a : Fin g}
    (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k) :
    ∀ k ∈ X.chords.delta a, dlabelPar ℓ k = dlabelPar ℓ' k := fun k hk => by
  simp only [dlabelPar, h k hk]

/-- `σ_a(ℓ)` depends only on `ℓ|δ(a)`. -/
theorem sigma_congr {ℓ ℓ' : Fin m → DLabel} {a : Fin g}
    (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k) :
    X.chords.sigma (dlabelPar ℓ) a = X.chords.sigma (dlabelPar ℓ') a :=
  X.chords.sigma_congr (X.dlabelPar_congr h)

/-- `χ_a(ℓ, y)` depends only on `ℓ|δ(a)` and on the copy bits `y|Q_a`. -/
theorem chi_congr {ℓ ℓ' : Fin m → DLabel} {a : Fin g} (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k)
    {y y' : Fin g × Fin g → ZMod 2} (hy : ∀ p ∈ Chords.Q a, y p = y' p) :
    X.chords.chi (dlabelPar ℓ) a y = X.chords.chi (dlabelPar ℓ') a y' :=
  X.chords.chi_congr (X.dlabelPar_congr h) hy

/-- `P_{cd}(ℓ)` depends only on `ℓ|δ(c)`. -/
theorem P_congr {ℓ ℓ' : Fin m → DLabel} {c : Fin g} (h : ∀ k ∈ X.chords.delta c, ℓ k = ℓ' k)
    (d : Fin g) : X.chords.P (dlabelPar ℓ) c d = X.chords.P (dlabelPar ℓ') c d :=
  X.chords.P_congr_left (X.dlabelPar_congr h) d

theorem Gam_congr {ℓ ℓ' : Fin m → DLabel} {a : Fin g} (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k) :
    X.Gam r ℓ a = X.Gam r ℓ' a := by
  unfold Gam
  congr 1
  refine List.map_congr_left fun k hk => ?_
  unfold piece
  rw [h k ((mem_sort (· ≤ ·)).1 hk)]

theorem pdegL_congr (proj : Fin n × Fin n → Fin n) {ℓ ℓ' : Fin m → DLabel} {a : Fin g}
    (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k) (v : Fin n) :
    X.pdegL proj ℓ a v = X.pdegL proj ℓ' a v := by
  unfold pdegL
  congr 1
  refine filter_congr fun k hk => ?_
  rw [h k hk]

theorem wtL_congr {ℓ ℓ' : Fin m → DLabel} {a : Fin g} (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k) :
    X.wtL w ℓ a = X.wtL w ℓ' a := by
  unfold wtL
  congr 1
  refine filter_congr fun k hk => ?_
  rw [h k hk]

/-- `I^w_a(ℓ)` depends only on `ℓ|δ(a)`. -/
theorem Iw_congr {ℓ ℓ' : Fin m → DLabel} {a : Fin g} (h : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k) :
    X.Iw r z w ℓ a = X.Iw r z w ℓ' a := by
  unfold Iw degInd
  simp only [X.wtL_congr w h, X.pdegL_congr Prod.fst h, X.pdegL_congr Prod.snd h, X.Gam_congr r h]

theorem wtL_le {W : ℕ} (hw : ∀ e, w e ≤ W) (ℓ : Fin m → DLabel) (a : Fin g) :
    X.wtL w ℓ a ≤ (X.chords.delta a).card * W := by
  unfold wtL
  have h1 := sum_le_card_nsmul ((X.chords.delta a).filter
    (fun k => β (X.s k) = a ∧ ℓ k ≠ DLabel.N)) (fun k => w (X.arc k)) W fun k _ => hw _
  rw [smul_eq_mul] at h1
  exact h1.trans (Nat.mul_le_mul_right W (card_filter_le _ _))

/-! ### Steps 1–4: expand the product of the blob sums -/

section Factorisation

theorem suppIn_piece {ℓ : Fin m → DLabel} {k : Fin m} {a : Fin g} (hk : k ∈ X.chords.delta a) :
    SuppIn (genSet r (blob β a)) (X.piece r ℓ k a) := by
  unfold piece
  split_ifs with h
  · exact suppIn_dpieceA (mem_blob.2 h) _ _
  · have : β (X.t k) = a := ((X.mem_delta).1 hk).resolve_left h
    exact suppIn_dpieceB (mem_blob.2 this) _ _

theorem suppIn_Gam (ℓ : Fin m → DLabel) (a : Fin g) :
    SuppIn (genSet r (blob β a)) (X.Gam r ℓ a) := by
  refine suppIn_list_prod _ fun z hz => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hz
  exact X.suppIn_piece r ((mem_sort (· ≤ ·)).1 hk)

theorem suppIn_blobTerm (ℓ : Fin m → DLabel) {a : Fin g} {x : Finset (Fin n × Fin n)}
    (hx : x ⊆ Aint A β a) :
    SuppIn (genSet r (blob β a)) (arcProd r x * X.Gam r ℓ a) :=
  (suppIn_arcProd fun e he => by
    obtain ⟨-, h1, h2⟩ := mem_Aint.1 (hx he)
    exact ⟨mem_blob.2 h1, mem_blob.2 h2⟩).mul (X.suppIn_Gam r ℓ a)

/-- `ε(ℓ) Π_a [ω_a](F_a(x_a) Γ_a(ℓ)) = [Ω_V](Π_a F_a(x_a) · Π_k α_{ℓ_k} β_{ℓ_k})`. -/
theorem eps_mul_prod_topCoeff (ℓ : Fin m → DLabel) (xs : Fin g → Finset (Fin n × Fin n))
    (hxs : ∀ a, xs a ⊆ Aint A β a) :
    X.eps ℓ * ∏ a, topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a))
        (arcProd r (xs a) * X.Gam r ℓ a) =
      topV r ((List.ofFn fun a => arcProd r (xs a)).prod *
        (List.ofFn fun k => dpieceA r (X.tl k) (X.s k) (ℓ k) *
          dpieceB r (X.tl k) (X.t k) (ℓ k)).prod) := by
  rw [← topV_prod_blocks r β _ (fun a => X.suppIn_blobTerm r ℓ (hxs a)),
    prod_ofFn_mul_of_even _ _ (fun a => isHomog_arcProd r (xs a)), X.sign_rule r ℓ,
    mul_smul_comm]
  unfold topV
  rw [topCoeff_zsmul]

theorem eps_mul_prod_Iw (ℓ : Fin m → DLabel) :
    X.eps ℓ * ∏ a, X.Iw r z w ℓ a =
      ∑ xs ∈ Fintype.piFinset (fun a => (Aint A β a).powerset),
        z ^ (∑ a, arcWt w (xs a)) * ((∏ a, X.degInd ℓ a (xs a)) * z ^ (∑ a, X.wtL w ℓ a) *
          topV r ((List.ofFn fun a => arcProd r (xs a)).prod *
            (List.ofFn fun k => dpieceA r (X.tl k) (X.s k) (ℓ k) *
              dpieceB r (X.tl k) (X.t k) (ℓ k)).prod)) := by
  unfold Iw
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, prod_univ_sum]
  simp only [mul_sum]
  refine sum_congr rfl fun xs hxs => ?_
  rw [Fintype.mem_piFinset] at hxs
  have hsub : ∀ a, xs a ⊆ Aint A β a := fun a => mem_powerset.1 (hxs a)
  rw [prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum,
    ← X.eps_mul_prod_topCoeff r ℓ xs hsub]
  ring

/-! ### Steps 5–6: sum over the labellings with a given support -/

/-- The support `{k : ℓ_k ≠ N}` of a labelling. -/
def supp (ℓ : Fin m → DLabel) : Finset (Fin m) := univ.filter fun k => ℓ k ≠ DLabel.N

/-- `#{k ∈ δ(a) ∩ T : proj(arc k) = v}`. -/
def pdegT (proj : Fin n × Fin n → Fin n) (T : Finset (Fin m)) (a : Fin g) (v : Fin n) : ℕ :=
  ((X.chords.delta a).filter fun k => k ∈ T ∧ proj (X.arc k) = v).card

/-- The constraint of all blobs, as a function of the support `T`. -/
def indT (xs : Fin g → Finset (Fin n × Fin n)) (T : Finset (Fin m)) : ℤ :=
  ∏ a, if ∀ v ∈ blob β a, pdeg Prod.fst (xs a) v + X.pdegT Prod.fst T a v = 1 ∧
      pdeg Prod.snd (xs a) v + X.pdegT Prod.snd T a v = 1 then 1 else 0

theorem prod_degInd (ℓ : Fin m → DLabel) (xs : Fin g → Finset (Fin n × Fin n)) :
    ∏ a, X.degInd ℓ a (xs a) = X.indT xs (supp ℓ) := by
  have h : ∀ proj a v, X.pdegL proj ℓ a v = X.pdegT proj (supp ℓ) a v := fun proj a v => by
    unfold pdegL pdegT supp
    congr 1
    ext k
    simp
  unfold indT degInd
  simp only [h]

/-- Summing the pieces over the labellings with support `T` gives `Π_{k ∈ T} (1 + p_{arc k})`. -/
theorem sum_fiber_pieces (T : Finset (Fin m)) :
    ∑ ℓ ∈ univ.filter (fun ℓ : Fin m → DLabel => supp ℓ = T),
        (List.ofFn fun k => dpieceA r (X.tl k) (X.s k) (ℓ k) *
          dpieceB r (X.tl k) (X.t k) (ℓ k)).prod =
      ((∏ k ∈ T, oneP r (X.arc k) : evenSubring (Fin (2 * n))) : Grass (Fin (2 * n))) := by
  classical
  let S : Fin m → Finset DLabel := fun k => if k ∈ T then univ.erase DLabel.N else {DLabel.N}
  have hfib : univ.filter (fun ℓ : Fin m → DLabel => supp ℓ = T) = Fintype.piFinset S := by
    ext ℓ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, S]
    constructor
    · rintro rfl k
      by_cases h : ℓ k = DLabel.N <;> simp [supp, h]
    · intro h
      ext k
      have hk := h k
      by_cases hT : k ∈ T
      · simp only [hT, if_true, mem_erase] at hk
        simp [supp, hk.1, hT]
      · simp only [hT, if_false, mem_singleton] at hk
        simp [supp, hk, hT]
  have hpt : ∀ ℓ : Fin m → DLabel,
      (List.ofFn fun k => dpieceA r (X.tl k) (X.s k) (ℓ k) *
          dpieceB r (X.tl k) (X.t k) (ℓ k)).prod =
        ((∏ k, dpieceAB r (X.tl k) (X.s k) (X.t k) (ℓ k) : evenSubring (Fin (2 * n))) :
          Grass (Fin (2 * n))) := fun ℓ => by
    rw [← coe_prod_ofFn_even]; rfl
  simp only [hpt]
  rw [← Crossing.coe_finset_sum_even, hfib, ← prod_univ_sum,
    show (∏ k ∈ T, oneP r (X.arc k)) = ∏ k, if k ∈ T then oneP r (X.arc k) else 1 by
      rw [prod_ite_mem, univ_inter]]
  congr 1
  refine prod_congr rfl fun k _ => ?_
  apply Subtype.ext
  by_cases hT : k ∈ T
  · simp only [S, hT, if_true]
    rw [Crossing.coe_finset_sum_even]
    exact sum_dpieces r (X.tl k) (X.s k) (X.t k)
  · simp only [S, hT, if_false, sum_singleton]
    exact dpieceA_mul_dpieceB_N r (X.tl k) (X.s k) (X.t k)

/-- `Σ_a w_ℓ(a) = Σ_{k : ℓ_k ≠ N} w(arc k)`: every selected crossing arc is weighted once. -/
theorem sum_wtL (ℓ : Fin m → DLabel) : ∑ a, X.wtL w ℓ a = X.wtT w (supp ℓ) := by
  unfold wtL wtT
  rw [← sum_fiberwise (supp ℓ) (fun k => β (X.s k))]
  refine sum_congr rfl fun a _ => ?_
  congr 1
  ext k
  simp only [mem_filter, X.mem_delta, supp, mem_univ, true_and]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨Or.inl h1, h1, h2⟩

/-- Steps 5–6 for a fixed choice `xs` of internal arcs. -/
theorem sum_labels_fixed_w (xs : Fin g → Finset (Fin n × Fin n)) :
    ∑ ℓ : Fin m → DLabel, (∏ a, X.degInd ℓ a (xs a)) * z ^ (∑ a, X.wtL w ℓ a) *
        topV r ((List.ofFn fun a => arcProd r (xs a)).prod *
          (List.ofFn fun k => dpieceA r (X.tl k) (X.s k) (ℓ k) *
            dpieceB r (X.tl k) (X.t k) (ℓ k)).prod) =
      ∑ T : Finset (Fin m), X.indT xs T * z ^ X.wtT w T *
        topV r ((List.ofFn fun a => arcProd r (xs a)).prod *
          ((∏ k ∈ T, oneP r (X.arc k) : evenSubring (Fin (2 * n))) : Grass (Fin (2 * n)))) := by
  rw [← sum_fiberwise univ supp]
  refine sum_congr rfl fun T _ => ?_
  rw [← X.sum_fiber_pieces r T, mul_sum, topV, topCoeff_sum, mul_sum]
  refine sum_congr rfl fun ℓ hℓ => ?_
  have hT := (mem_filter.1 hℓ).2
  have h := X.prod_degInd ℓ xs
  rw [hT] at h
  rw [h, X.sum_wtL w ℓ, hT]
  rfl

/-! ### Step 7: regroup by the arc set -/

/-- The arc set `x_int ∪ {arc k : k ∈ T}`. -/
def unionArcs (xs : Fin g → Finset (Fin n × Fin n)) (T : Finset (Fin m)) :
    Finset (Fin n × Fin n) :=
  (univ.biUnion xs) ∪ T.image X.arc

theorem mem_unionArcs {xs : Fin g → Finset (Fin n × Fin n)} {T : Finset (Fin m)}
    {e : Fin n × Fin n} :
    e ∈ X.unionArcs xs T ↔ (∃ a, e ∈ xs a) ∨ ∃ k ∈ T, X.arc k = e := by
  simp [unionArcs]

theorem pdeg_unionArcs (proj : Fin n × Fin n → Fin n) (hproj : ∀ e, proj e = e.1 ∨ proj e = e.2)
    {xs : Fin g → Finset (Fin n × Fin n)} (hxs : ∀ a, xs a ⊆ Aint A β a)
    (T : Finset (Fin m)) {a : Fin g} {v : Fin n} (hv : β v = a) :
    pdeg proj (X.unionArcs xs T) v = pdeg proj (xs a) v + X.pdegT proj T a v := by
  have hb : ∀ {b : Fin g} {e : Fin n × Fin n}, e ∈ Aint A β b → proj e = v → b = a := by
    intro b e he hpe
    obtain ⟨-, h1, h2⟩ := mem_Aint.1 he
    rcases hproj e with h | h
    · rw [← h1, ← hv, ← hpe, h]
    · rw [← h2, ← hv, ← hpe, h]
  have hfil : (X.unionArcs xs T).filter (fun e => proj e = v) =
      (xs a).filter (fun e => proj e = v) ∪ (T.filter fun k => proj (X.arc k) = v).image X.arc := by
    ext e
    simp only [mem_filter, mem_union, mem_image, X.mem_unionArcs]
    constructor
    · rintro ⟨⟨b, hb'⟩ | ⟨k, hk, rfl⟩, hve⟩
      · have : b = a := hb (hxs b hb') hve
        subst this
        exact Or.inl ⟨hb', hve⟩
      · exact Or.inr ⟨k, ⟨hk, hve⟩, rfl⟩
    · rintro (⟨hb', hve⟩ | ⟨k, ⟨hk, hve⟩, rfl⟩)
      · exact ⟨Or.inl ⟨a, hb'⟩, hve⟩
      · exact ⟨Or.inr ⟨k, hk, rfl⟩, hve⟩
  have hdisj : Disjoint ((xs a).filter (fun e => proj e = v))
      ((T.filter fun k => proj (X.arc k) = v).image X.arc) := by
    rw [disjoint_left]
    intro e he he'
    obtain ⟨k, -, rfl⟩ := mem_image.1 he'
    exact X.arc_not_mem_Aint k a (hxs a (mem_filter.1 he).1)
  unfold pdeg
  rw [hfil, card_union_of_disjoint hdisj, card_image_of_injective _ X.arc_injective]
  congr 1
  unfold pdegT
  congr 1
  ext k
  simp only [mem_filter]
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨X.mem_delta_of_end hv ?_, hk, h⟩
    rcases hproj (X.arc k) with h' | h'
    · exact Or.inl (h'.symm.trans h)
    · exact Or.inr (h'.symm.trans h)
  · rintro ⟨-, hk, h⟩
    exact ⟨hk, h⟩

theorem cycleCover_unionArcs_iff {xs : Fin g → Finset (Fin n × Fin n)}
    (hxs : ∀ a, xs a ⊆ Aint A β a) (T : Finset (Fin m)) :
    DirectedHamiltonian.CycleCover (X.unionArcs xs T) ↔
      ∀ a, ∀ v ∈ blob β a, pdeg Prod.fst (xs a) v + X.pdegT Prod.fst T a v = 1 ∧
        pdeg Prod.snd (xs a) v + X.pdegT Prod.snd T a v = 1 := by
  have h1 := fun {a} {v} (hv : β v = a) =>
    X.pdeg_unionArcs Prod.fst (fun e => Or.inl rfl) hxs T hv
  have h2 := fun {a} {v} (hv : β v = a) =>
    X.pdeg_unionArcs Prod.snd (fun e => Or.inr rfl) hxs T hv
  constructor
  · intro h a v hv
    rw [← h1 (mem_blob.1 hv), ← h2 (mem_blob.1 hv)]
    exact h v
  · intro h v
    have := h (β v) v (mem_blob.2 rfl)
    rw [← h1 rfl, ← h2 rfl] at this
    exact this

theorem arcProd_unionArcs {xs : Fin g → Finset (Fin n × Fin n)} (hxs : ∀ a, xs a ⊆ Aint A β a)
    (T : Finset (Fin m)) :
    arcProd r (X.unionArcs xs T) = (List.ofFn fun a => arcProd r (xs a)).prod *
      ((∏ k ∈ T, oneP r (X.arc k) : evenSubring (Fin (2 * n))) : Grass (Fin (2 * n))) := by
  have hdisj : Disjoint (univ.biUnion xs) (T.image X.arc) := by
    rw [disjoint_left]
    intro e he he'
    obtain ⟨a, -, hea⟩ := mem_biUnion.1 he
    obtain ⟨k, -, rfl⟩ := mem_image.1 he'
    exact X.arc_not_mem_Aint k a (hxs a hea)
  have hpd : ((univ : Finset (Fin g)) : Set (Fin g)).PairwiseDisjoint xs :=
    fun a _ b _ hab => (Aint_disjoint hab).mono (hxs a) (hxs b)
  simp only [arcProd_eq]
  rw [coe_prod_ofFn_even, ← Subring.coe_mul, unionArcs, prod_union hdisj, prod_biUnion hpd,
    prod_image (fun k _ l _ h => X.arc_injective h)]

theorem wt_unionArcs {xs : Fin g → Finset (Fin n × Fin n)} (hxs : ∀ a, xs a ⊆ Aint A β a)
    (T : Finset (Fin m)) :
    arcWt w (X.unionArcs xs T) = (∑ a, arcWt w (xs a)) + X.wtT w T := by
  have hdisj : Disjoint (univ.biUnion xs) (T.image X.arc) := by
    rw [disjoint_left]
    intro e he he'
    obtain ⟨a, -, hea⟩ := mem_biUnion.1 he
    obtain ⟨k, -, rfl⟩ := mem_image.1 he'
    exact X.arc_not_mem_Aint k a (hxs a hea)
  have hpd : ((univ : Finset (Fin g)) : Set (Fin g)).PairwiseDisjoint xs :=
    fun a _ b _ hab => (Aint_disjoint hab).mono (hxs a) (hxs b)
  unfold arcWt wtT unionArcs
  rw [sum_union hdisj, sum_biUnion hpd, sum_image (fun k _ l _ h => X.arc_injective h)]

/-- Step 7 for an arbitrary function `F` of the arc set: regrouping by `x = x_int ∪ 1_T` gives
the sum over the cycle covers of `A`. -/
theorem sum_internal_crossing_gen (F : Finset (Fin n × Fin n) → ℤ) :
    ∑ xs ∈ Fintype.piFinset (fun a => (Aint A β a).powerset), ∑ T : Finset (Fin m),
        X.indT xs T * F (X.unionArcs xs T) =
      ∑ Y ∈ DirectedHamiltonian.cycleCovers A, F Y := by
  classical
  unfold DirectedHamiltonian.cycleCovers
  rw [sum_filter, ← sum_product']
  refine sum_nbij' (fun p => X.unionArcs p.1 p.2)
    (fun Y => (fun a => Y.filter (· ∈ Aint A β a), univ.filter fun k => X.arc k ∈ Y))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨xs, T⟩ hp
    have hxs : ∀ a, xs a ⊆ Aint A β a := fun a =>
      mem_powerset.1 (Fintype.mem_piFinset.1 (mem_product.1 hp).1 a)
    rw [mem_powerset]
    intro e he
    rcases X.mem_unionArcs.1 he with ⟨a, ha⟩ | ⟨k, -, rfl⟩
    · exact Aint_subset a (hxs a ha)
    · exact X.arc_mem k
  · intro Y _
    rw [mem_product, Fintype.mem_piFinset]
    exact ⟨fun a => mem_powerset.2 fun e he => (mem_filter.1 he).2, mem_univ _⟩
  · rintro ⟨xs, T⟩ hp
    have hxs : ∀ a, xs a ⊆ Aint A β a := fun a =>
      mem_powerset.1 (Fintype.mem_piFinset.1 (mem_product.1 hp).1 a)
    refine Prod.ext (funext fun a => ?_) ?_
    · ext e
      simp only [mem_filter, X.mem_unionArcs]
      constructor
      · rintro ⟨⟨b, hb⟩ | ⟨k, -, rfl⟩, he⟩
        · by_cases hab : a = b
          · exact hab ▸ hb
          · exact absurd he (disjoint_left.1 (Aint_disjoint (Ne.symm hab)) (hxs b hb))
        · exact absurd he (X.arc_not_mem_Aint k a)
      · intro he
        exact ⟨Or.inl ⟨a, he⟩, hxs a he⟩
    · ext k
      simp only [mem_filter, mem_univ, true_and, X.mem_unionArcs]
      constructor
      · rintro (⟨b, hb⟩ | ⟨l, hl, hlk⟩)
        · exact absurd (hxs b hb) (X.arc_not_mem_Aint k b)
        · exact X.arc_injective hlk ▸ hl
      · intro hk
        exact Or.inr ⟨k, hk, rfl⟩
  · intro Y hY
    have hY' : Y ⊆ A := mem_powerset.1 hY
    ext e
    simp only [X.mem_unionArcs, mem_filter, mem_univ, true_and]
    constructor
    · rintro (⟨a, he, -⟩ | ⟨k, hk, rfl⟩)
      · exact he
      · exact hk
    · intro he
      rcases X.arc_cases (hY' he) with ⟨a, ha⟩ | ⟨k, rfl⟩
      · exact Or.inl ⟨a, he, ha⟩
      · exact Or.inr ⟨k, he, rfl⟩
  · rintro ⟨xs, T⟩ hp
    have hxs : ∀ a, xs a ⊆ Aint A β a := fun a =>
      mem_powerset.1 (Fintype.mem_piFinset.1 (mem_product.1 hp).1 a)
    simp only
    rw [indT, prod_boole]
    by_cases h : ∀ a, ∀ v ∈ blob β a, pdeg Prod.fst (xs a) v + X.pdegT Prod.fst T a v = 1 ∧
        pdeg Prod.snd (xs a) v + X.pdegT Prod.snd T a v = 1
    · rw [if_pos (fun a _ => h a), if_pos ((X.cycleCover_unionArcs_iff hxs T).2 h), one_mul]
    · rw [if_neg (fun h' => h fun a => h' a (mem_univ a)),
        if_neg (fun h' => h ((X.cycleCover_unionArcs_iff hxs T).1 h')), zero_mul]

end Factorisation

end DCrossing

/-- The weighted directed fermion sum `Σ_{X cycle cover} z^{w(X)} [Ω_V] Π_{a∈X}(1 + p_a)`. -/
def dfermionSumW (A : Finset (Fin n × Fin n)) (r : Fin n) (z : ℤ) (w : Fin n × Fin n → ℕ) : ℤ :=
  ∑ X ∈ DirectedHamiltonian.cycleCovers A, z ^ arcWt w X * topV r (arcProd r X)

theorem dfermionSumW_eq (A : Finset (Fin n × Fin n)) (r : Fin n) (z : ℤ)
    (w : Fin n × Fin n → ℕ) :
    dfermionSumW A r z w = ∑ H ∈ DirectedHamiltonian.dirHamCycles A, z ^ arcWt w H :=
  (sum_dirHamCycles_pow_eq A r z w).symm

namespace DCrossing

variable {g m : ℕ} {A : Finset (Fin n × Fin n)} {β : Fin n → Fin g} (X : DCrossing A β m)
  (r : Fin n) (z : ℤ) (w : Fin n × Fin n → ℕ)

/-- **Directed Theorem 1.2, first equality**:
`Σ_{ℓ ∈ L_d^m} ε(ℓ) Π_a I^w_a(ℓ) = Σ_{X cycle cover} z^{w(X)} [Ω_V] Π_{a∈X}(1 + p_a)`. -/
theorem sum_eps_prod_Iw :
    ∑ ℓ : Fin m → DLabel, X.eps ℓ * ∏ a, X.Iw r z w ℓ a = dfermionSumW A r z w := by
  simp only [X.eps_mul_prod_Iw r z w]
  rw [sum_comm]
  unfold dfermionSumW
  rw [← X.sum_internal_crossing_gen (fun Y => z ^ arcWt w Y * topV r (arcProd r Y))]
  refine sum_congr rfl fun xs hxs => ?_
  rw [Fintype.mem_piFinset] at hxs
  have hsub : ∀ a, xs a ⊆ Aint A β a := fun a => mem_powerset.1 (hxs a)
  rw [← mul_sum, X.sum_labels_fixed_w r z w xs, mul_sum]
  refine sum_congr rfl fun T _ => ?_
  rw [X.wt_unionArcs w hsub T, X.arcProd_unionArcs r hsub T, pow_add]
  ring

/-- **Directed Theorem 1.2, second equality**: with correct parity copies,
`Σ_ℓ Π_a σ_a(ℓ) χ_a(ℓ, P(ℓ)) I^w_a(ℓ) = Σ_{X cycle cover} z^{w(X)} [Ω_V] Π_{a∈X}(1 + p_a)`. -/
theorem sum_sigma_chi_Iw :
    ∑ ℓ : Fin m → DLabel, ∏ a, X.chords.sigma (dlabelPar ℓ) a *
        X.chords.chi (dlabelPar ℓ) a (fun p => X.chords.P (dlabelPar ℓ) p.1 p.2) *
        X.Iw r z w ℓ a =
      dfermionSumW A r z w := by
  rw [← X.sum_eps_prod_Iw r z w]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [prod_mul_distrib, eps,
    X.chords.eps_eq_prod_sigma_chi (dlabelPar ℓ) (fun _ p => X.chords.P (dlabelPar ℓ) p.1 p.2)
      (fun _ _ _ => rfl)]

end DCrossing

/-! ### Existence of a crossing order -/

/-- The crossing arcs of `A` for `β`. -/
def crossArcs {g : ℕ} (A : Finset (Fin n × Fin n)) (β : Fin n → Fin g) : Finset (Fin n × Fin n) :=
  A.filter fun e => β e.1 ≠ β e.2

/-- Whether the tail of `e` is its low end. -/
def tlOf {g : ℕ} (β : Fin n → Fin g) (e : Fin n × Fin n) : Bool := decide (β e.1 < β e.2)

/-- The low end of `e`. -/
def lowOf {g : ℕ} (β : Fin n → Fin g) (e : Fin n × Fin n) : Fin n :=
  if β e.1 < β e.2 then e.1 else e.2

/-- The high end of `e`. -/
def highOf {g : ℕ} (β : Fin n → Fin g) (e : Fin n × Fin n) : Fin n :=
  if β e.1 < β e.2 then e.2 else e.1

theorem arcOf_ofArc {g : ℕ} (β : Fin n → Fin g) (e : Fin n × Fin n) :
    arcOf (tlOf β e) (lowOf β e) (highOf β e) = e := by
  unfold arcOf tlOf lowOf highOf
  by_cases h : β e.1 < β e.2 <;> simp [h]

theorem lowOf_lt_highOf {g : ℕ} (β : Fin n → Fin g) {e : Fin n × Fin n} (h : β e.1 ≠ β e.2) :
    β (lowOf β e) < β (highOf β e) := by
  unfold lowOf highOf
  by_cases h' : β e.1 < β e.2
  · simp [h']
  · simp only [h', if_false]
    exact lt_of_le_of_ne (not_lt.1 h') (Ne.symm h)

/-- A crossing order always exists: enumerate `crossArcs A β`. -/
def DCrossing.canonical {g : ℕ} (A : Finset (Fin n × Fin n)) (β : Fin n → Fin g) :
    DCrossing A β (crossArcs A β).card where
  s k := lowOf β ((crossArcs A β).equivFin.symm k).1
  t k := highOf β ((crossArcs A β).equivFin.symm k).1
  tl k := tlOf β ((crossArcs A β).equivFin.symm k).1
  lt k := lowOf_lt_highOf β (mem_filter.1 ((crossArcs A β).equivFin.symm k).2).2
  mem k := by
    rw [arcOf_ofArc]
    exact (mem_filter.1 ((crossArcs A β).equivFin.symm k).2).1
  inj k l h := by
    simp only [arcOf_ofArc] at h
    exact (crossArcs A β).equivFin.symm.injective (Subtype.ext h)
  exhaust e he hne := by
    have hp : e ∈ crossArcs A β := mem_filter.2 ⟨he, hne⟩
    refine ⟨(crossArcs A β).equivFin ⟨e, hp⟩, ?_⟩
    simp only [Equiv.symm_apply_apply, arcOf_ofArc]

/-! ### The directed blob factorisation, assembled -/

variable {g m : ℕ} {A : Finset (Fin n × Fin n)} {β : Fin n → Fin g}

/-- **Directed blob factorisation** (ATSP via Kronecker substitution, Theorem 1.2 for the directed
data of §3.2 combined with Lemma 3.3): for every digraph `A` on `Fin n`, root `r`, partition `β`,
crossing order `X`, integer `z` and arc weights `w`,
`Σ_{ℓ ∈ L_d^m} Π_a σ_a(ℓ) χ_a(ℓ, P(ℓ)) I^w_a(ℓ) = Σ_{H ∈ DHC(A)} z^{w(H)}`. -/
theorem dblob_factorisation_w (X : DCrossing A β m) (r : Fin n) (z : ℤ)
    (w : Fin n × Fin n → ℕ) :
    ∑ ℓ : Fin m → DLabel, ∏ a, X.chords.sigma (dlabelPar ℓ) a *
        X.chords.chi (dlabelPar ℓ) a (fun p => X.chords.P (dlabelPar ℓ) p.1 p.2) *
        X.Iw r z w ℓ a =
      ∑ H ∈ DirectedHamiltonian.dirHamCycles A, z ^ arcWt w H := by
  rw [X.sum_sigma_chi_Iw r z w, dfermionSumW_eq]

/-- The same, with the global sign `ε(ℓ)`. -/
theorem dblob_factorisation_w_eps (X : DCrossing A β m) (r : Fin n) (z : ℤ)
    (w : Fin n × Fin n → ℕ) :
    ∑ ℓ : Fin m → DLabel, X.eps ℓ * ∏ a, X.Iw r z w ℓ a =
      ∑ H ∈ DirectedHamiltonian.dirHamCycles A, z ^ arcWt w H := by
  rw [X.sum_eps_prod_Iw r z w, dfermionSumW_eq]

/-- **Directed blob factorisation of `#DHC`** (`z = 1`). -/
theorem dblob_factorisation (X : DCrossing A β m) (r : Fin n) (w : Fin n × Fin n → ℕ) :
    ∑ ℓ : Fin m → DLabel, ∏ a, X.chords.sigma (dlabelPar ℓ) a *
        X.chords.chi (dlabelPar ℓ) a (fun p => X.chords.P (dlabelPar ℓ) p.1 p.2) *
        X.Iw r 1 w ℓ a =
      (DirectedHamiltonian.dirHamCycles A).card := by
  rw [dblob_factorisation_w]
  simp

/-- A crossing order always exists, so the directed factorisation always applies. -/
theorem exists_dblob_factorisation_w (A : Finset (Fin n × Fin n)) (β : Fin n → Fin g) (r : Fin n)
    (z : ℤ) (w : Fin n × Fin n → ℕ) :
    ∃ (m : ℕ) (X : DCrossing A β m),
      ∑ ℓ : Fin m → DLabel, ∏ a, X.chords.sigma (dlabelPar ℓ) a *
          X.chords.chi (dlabelPar ℓ) a (fun p => X.chords.P (dlabelPar ℓ) p.1 p.2) *
          X.Iw r z w ℓ a =
        ∑ H ∈ DirectedHamiltonian.dirHamCycles A, z ^ arcWt w H :=
  ⟨_, DCrossing.canonical A β, dblob_factorisation_w _ r z w⟩

end

end EthFollowup.ExactHC
