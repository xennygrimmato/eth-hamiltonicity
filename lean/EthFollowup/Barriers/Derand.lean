/-
# Restrictions, support and `t_q` (`research/derandomization.md` §2)

Sources (`derandomization.md` §2), with `c_T = #{H ∈ HC(G) : T ⊆ H}`:

> **Lemma 1 (duality) [Proved].** For any q, the following three quantities are equal:
> `min{|D| : #HC(G−D) ≢ 0 mod q}`; `min{|T| : c_T ≢ 0 mod q}`;
> `min{|F|+|D| : #HC(G; F forced, D deleted) ≢ 0 mod q}`. Call the common value `t_q(G)`.
>
> *Proof.* Inclusion–exclusion gives `#HC(G; F, D) = Σ_{T⊆D} (−1)^{|T|} c_{F∪T}`. In the other
> direction, `c_T = Σ_{D⊆T} (−1)^{|D|} #HC(G−D)`, by Möbius inversion. …
>
> **Lemma 2 (support) [Proved].** Suppose a query has the form `Σ_H f(H ∩ S) mod q` with
> `|S| < t_q`. … Such a query returns 0. *Proof.* `#{H : H ∩ S = A} = Σ_{A⊆T⊆S} (−1)^{|T∖A|} c_T ≡ 0`.
>
> **Theorem 1 [Proved].** For every prime p, `t_p(G) ≤ log₂ #HC(G)`. For composite q, `t_q ≤ t_p`
> whenever p | q.
>
> *Proof.* Fix a Hamiltonian cycle H₀. For each H let `D_H = H₀ ∖ H`, and let
> `v(D) = #{H : D_H = D} mod p` for D ⊆ H₀. Then v(∅) = 1 … So v … is orthogonal over F_p to every
> multilinear monomial of degree < t. Over any field this orthogonal complement is exactly
> `{(−1)^{|x|} g(x) : deg g ≤ n−t}`. … A nonzero multilinear g of degree ≤ n−t is nonzero on at
> least `2^t` points of the cube. Hence there are at least 2^t distinct sets D_H, so `#HC ≥ 2^t`. ∎

## What is formalised

Everything is stated for an arbitrary finite family `S : Finset (Finset E)` in place of `HC(G)`
(`G − D` keeps the members disjoint from `D`; forcing `F` keeps those containing `F`); the proofs
use nothing else about Hamiltonian cycles. The step "`v(∅) = 1`, because only `H₀` has
`D_H = ∅`" needs that no member of `S` strictly contains `H₀`; for Hamiltonian cycles this holds
because all have `n` edges (`tp_le_log_of_card_eq`), and for an arbitrary nonempty family one
takes `H₀` inclusion-maximal (`tp_le_log_of_nonempty`), so Theorem 1 holds for all set systems.

* `forcedDeleted_eq_sum` / `cnt_eq_sum` — the two inclusion–exclusion identities (over `ℤ`);
* `duality_deleted_iff_contains`, `duality_contains_iff_forcedDeleted`, `tq_deleted_eq_contains`,
  `tq_contains_eq_forcedDeleted` — Lemma 1 (equality of the three minima, as `sInf`s);
* `support_query_eq_zero` — Lemma 2;
* `support_card_ge` — the support bound used in Theorem 1: `v ≠ 0` with `Σ_{D ⊇ S} v(D) = 0` for
  all `|S| < t` has at least `2^t` nonzero values (proved directly by induction on the ground set;
  this replaces the source's "orthogonal complement is exactly …" dimension count, whose `⊇`
  direction is `alternating_mul_satisfies` and is all that is needed);
* `multilinear_nonzero_points` — "a nonzero multilinear g of degree ≤ n−t is nonzero on at least
  2^t points of the cube";
* `two_pow_le_card_of_contains_zero`, `tp_le_log`, `tp_le_log_of_card_eq`, `tp_le_log_of_nonempty`
  — Theorem 1 (the last one for an arbitrary nonempty family, choosing `H₀` maximal);
* `contains_ne_zero_of_dvd`, `tq_le_tp` — the composite-modulus remark.
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Order.Preorder.Finite

set_option linter.unusedSectionVars false

namespace EthFollowup.Barriers.Derand

open Finset

variable {E : Type*} [DecidableEq E]

/-! ### Counts -/

/-- `c_T = #{H ∈ S : T ⊆ H}`. -/
def cnt (S : Finset (Finset E)) (T : Finset E) : ℕ := #{H ∈ S | T ⊆ H}

/-- `#HC(G − D) = #{H ∈ S : H ∩ D = ∅}`. -/
def deleted (S : Finset (Finset E)) (D : Finset E) : ℕ := #{H ∈ S | Disjoint H D}

/-- `#HC(G; F forced, D deleted)`. -/
def forcedDeleted (S : Finset (Finset E)) (F D : Finset E) : ℕ := #{H ∈ S | F ⊆ H ∧ Disjoint H D}

theorem sum_powerset_filter_neg_one (D H : Finset E) :
    ∑ T ∈ D.powerset, (if T ⊆ H then (-1 : ℤ) ^ T.card else 0) = if Disjoint H D then 1 else 0 := by
  rw [← Finset.sum_filter]
  have : D.powerset.filter (· ⊆ H) = (D ∩ H).powerset := by
    ext T; simp [Finset.subset_inter_iff]
  rw [this, Finset.sum_powerset_neg_one_pow_card]
  congr 1
  apply propext
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]

/-- Inclusion–exclusion: `#HC(G; F, D) = Σ_{T⊆D} (−1)^{|T|} c_{F∪T}`. -/
theorem forcedDeleted_eq_sum (S : Finset (Finset E)) (F D : Finset E) :
    (forcedDeleted S F D : ℤ) = ∑ T ∈ D.powerset, (-1 : ℤ) ^ T.card * cnt S (F ∪ T) := by
  simp only [cnt, forcedDeleted, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun H _ => ?_
  have : ∀ T : Finset E, (-1 : ℤ) ^ T.card * (if F ∪ T ⊆ H then 1 else 0) =
      if F ⊆ H then (if T ⊆ H then (-1 : ℤ) ^ T.card else 0) else 0 := by
    intro T
    simp only [Finset.union_subset_iff]
    by_cases hF : F ⊆ H <;> by_cases hT : T ⊆ H <;> simp [hF, hT]
  simp_rw [this]
  by_cases hF : F ⊆ H
  · simp only [hF, ite_true, true_and]
    exact (sum_powerset_filter_neg_one D H).symm
  · simp [hF]

/-- `#HC(G − D) = Σ_{T⊆D} (−1)^{|T|} c_T`. -/
theorem deleted_eq_sum (S : Finset (Finset E)) (D : Finset E) :
    (deleted S D : ℤ) = ∑ T ∈ D.powerset, (-1 : ℤ) ^ T.card * cnt S T := by
  have := forcedDeleted_eq_sum S ∅ D
  simp only [Finset.empty_union] at this
  rw [← this]
  simp [deleted, forcedDeleted]

/-- Möbius inversion: `c_T = Σ_{D⊆T} (−1)^{|D|} #HC(G − D)`. -/
theorem cnt_eq_sum (S : Finset (Finset E)) (T : Finset E) :
    (cnt S T : ℤ) = ∑ D ∈ T.powerset, (-1 : ℤ) ^ D.card * deleted S D := by
  simp only [cnt, deleted, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [← Finset.sum_filter]
  have : T.powerset.filter (fun D => Disjoint H D) = (T \ H).powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_sdiff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
  rw [this, Finset.sum_powerset_neg_one_pow_card]
  simp [Finset.sdiff_eq_empty_iff_subset]

/-! ### Lemma 1 (duality) -/

variable (q : ℕ)

theorem exists_small_of_sum_ne_zero {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (h : ((∑ i ∈ s, f i : ℤ) : ZMod q) ≠ 0) : ∃ i ∈ s, ((f i : ℤ) : ZMod q) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  push_cast
  exact Finset.sum_eq_zero hcon

/-- Lemma 1, first equality (as a statement about every threshold `t`). -/
theorem duality_deleted_iff_contains (S : Finset (Finset E)) (t : ℕ) :
    (∃ D : Finset E, D.card ≤ t ∧ (deleted S D : ZMod q) ≠ 0) ↔
      (∃ T : Finset E, T.card ≤ t ∧ (cnt S T : ZMod q) ≠ 0) := by
  constructor
  · rintro ⟨D, hD, hne⟩
    have h : (((deleted S D : ℤ)) : ZMod q) ≠ 0 := by exact_mod_cast hne
    rw [deleted_eq_sum] at h
    obtain ⟨T, hT, hT'⟩ := exists_small_of_sum_ne_zero q _ _ h
    refine ⟨T, (Finset.card_le_card (Finset.mem_powerset.1 hT)).trans hD, fun h0 => hT' ?_⟩
    push_cast; rw [h0, mul_zero]
  · rintro ⟨T, hT, hne⟩
    have h : (((cnt S T : ℤ)) : ZMod q) ≠ 0 := by exact_mod_cast hne
    rw [cnt_eq_sum] at h
    obtain ⟨D, hD, hD'⟩ := exists_small_of_sum_ne_zero q _ _ h
    refine ⟨D, (Finset.card_le_card (Finset.mem_powerset.1 hD)).trans hT, fun h0 => hD' ?_⟩
    push_cast; rw [h0, mul_zero]

/-- Lemma 1, second equality. -/
theorem duality_contains_iff_forcedDeleted (S : Finset (Finset E)) (t : ℕ) :
    (∃ T : Finset E, T.card ≤ t ∧ (cnt S T : ZMod q) ≠ 0) ↔
      (∃ F D : Finset E, F.card + D.card ≤ t ∧ (forcedDeleted S F D : ZMod q) ≠ 0) := by
  constructor
  · rintro ⟨T, hT, hne⟩
    refine ⟨T, ∅, by simpa using hT, ?_⟩
    simpa [forcedDeleted, cnt] using hne
  · rintro ⟨F, D, hFD, hne⟩
    have h : (((forcedDeleted S F D : ℤ)) : ZMod q) ≠ 0 := by exact_mod_cast hne
    rw [forcedDeleted_eq_sum] at h
    obtain ⟨T, hT, hT'⟩ := exists_small_of_sum_ne_zero q _ _ h
    refine ⟨F ∪ T, ?_, fun h0 => hT' ?_⟩
    · exact (Finset.card_union_le _ _).trans
        ((Nat.add_le_add_left (Finset.card_le_card (Finset.mem_powerset.1 hT)) _).trans hFD)
    · push_cast; rw [h0, mul_zero]

theorem sInf_le_of_imp {α β : Type*} (A : Set α) (B : Set β) (wa : α → ℕ) (wb : β → ℕ)
    (hB : B.Nonempty) (h : ∀ t, (∃ b ∈ B, wb b ≤ t) → (∃ a ∈ A, wa a ≤ t)) :
    sInf (wa '' A) ≤ sInf (wb '' B) := by
  obtain ⟨b, hb, hbm⟩ := Nat.sInf_mem (hB.image wb)
  obtain ⟨a, ha, hle⟩ := h _ ⟨b, hb, hbm.le⟩
  exact (Nat.sInf_le (Set.mem_image_of_mem wa ha)).trans hle

/-- Equal "threshold predicates" give equal minima (`sInf`). -/
theorem sInf_eq_of_forall_iff {α β : Type*} (A : Set α) (B : Set β) (wa : α → ℕ) (wb : β → ℕ)
    (h : ∀ t, (∃ a ∈ A, wa a ≤ t) ↔ (∃ b ∈ B, wb b ≤ t)) : sInf (wa '' A) = sInf (wb '' B) := by
  by_cases hA : A.Nonempty
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb, -⟩ := (h (wa a)).1 ⟨a, ha, le_rfl⟩
    exact le_antisymm (sInf_le_of_imp A B wa wb ⟨b, hb⟩ fun t => (h t).2)
      (sInf_le_of_imp B A wb wa ⟨a, ha⟩ fun t => (h t).1)
  · have hA' : A = ∅ := Set.not_nonempty_iff_eq_empty.1 hA
    have hB' : B = ∅ := by
      by_contra hB
      obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.2 hB
      obtain ⟨a, ha, -⟩ := (h (wb b)).2 ⟨b, hb, le_rfl⟩
      exact hA ⟨a, ha⟩
    simp [hA', hB']

/-- `min{|D| : #HC(G−D) ≢ 0 mod q}`. -/
noncomputable def tqDeleted (S : Finset (Finset E)) : ℕ :=
  sInf ((fun D : Finset E => D.card) '' {D | (deleted S D : ZMod q) ≠ 0})

/-- `t_q = min{|T| : c_T ≢ 0 mod q}`. -/
noncomputable def tq (S : Finset (Finset E)) : ℕ :=
  sInf ((fun T : Finset E => T.card) '' {T | (cnt S T : ZMod q) ≠ 0})

/-- `min{|F| + |D| : #HC(G; F, D) ≢ 0 mod q}`. -/
noncomputable def tqForcedDeleted (S : Finset (Finset E)) : ℕ :=
  sInf ((fun FD : Finset E × Finset E => FD.1.card + FD.2.card) ''
    {FD | (forcedDeleted S FD.1 FD.2 : ZMod q) ≠ 0})

/-- **Lemma 1**, first equality of minima. -/
theorem tq_deleted_eq_contains (S : Finset (Finset E)) : tqDeleted q S = tq q S :=
  sInf_eq_of_forall_iff _ _ _ _ fun t => by
    simpa [and_comm] using duality_deleted_iff_contains q S t

/-- **Lemma 1**, second equality of minima. -/
theorem tq_contains_eq_forcedDeleted (S : Finset (Finset E)) : tq q S = tqForcedDeleted q S :=
  sInf_eq_of_forall_iff _ _ _ _ fun t => by
    rw [show (∃ b ∈ {FD : Finset E × Finset E | (forcedDeleted S FD.1 FD.2 : ZMod q) ≠ 0},
        b.1.card + b.2.card ≤ t) ↔
        ∃ F D : Finset E, F.card + D.card ≤ t ∧ (forcedDeleted S F D : ZMod q) ≠ 0 from
      ⟨fun ⟨⟨F, D⟩, h1, h2⟩ => ⟨F, D, h2, h1⟩, fun ⟨F, D, h2, h1⟩ => ⟨⟨F, D⟩, h1, h2⟩⟩]
    simpa [and_comm] using duality_contains_iff_forcedDeleted q S t

/-! ### Lemma 2 (support) -/

theorem inter_eq_iff {H S₀ A : Finset E} (hA : A ⊆ S₀) :
    H ∩ S₀ = A ↔ A ⊆ H ∧ Disjoint H (S₀ \ A) := by
  constructor
  · rintro rfl
    refine ⟨Finset.inter_subset_left, Finset.disjoint_left.2 fun x hxH hx => ?_⟩
    rw [Finset.mem_sdiff] at hx
    exact hx.2 (Finset.mem_inter.2 ⟨hxH, hx.1⟩)
  · rintro ⟨hAH, hdis⟩
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hxH, hxS⟩
      by_contra hxA
      exact Finset.disjoint_left.1 hdis hxH (Finset.mem_sdiff.2 ⟨hxS, hxA⟩)
    · intro hxA; exact ⟨hAH hxA, hA hxA⟩

/-- `#{H : H ∩ S₀ = A} ≡ 0` when `|S₀| < t` and all `c_T` with `|T| < t` vanish mod `q`. -/
theorem fiber_count_eq_zero (S : Finset (Finset E)) (t : ℕ)
    (hc : ∀ T : Finset E, T.card < t → (cnt S T : ZMod q) = 0) (S₀ : Finset E)
    (hS₀ : S₀.card < t) (A : Finset E) : (#{H ∈ S | H ∩ S₀ = A} : ZMod q) = 0 := by
  by_cases hA : A ⊆ S₀
  · have : #{H ∈ S | H ∩ S₀ = A} = forcedDeleted S A (S₀ \ A) := by
      unfold forcedDeleted
      congr 1
      exact Finset.filter_congr fun H _ => inter_eq_iff hA
    rw [this]
    have h := forcedDeleted_eq_sum S A (S₀ \ A)
    have h' : ((forcedDeleted S A (S₀ \ A) : ℤ) : ZMod q) = 0 := by
      rw [h]
      push_cast
      refine Finset.sum_eq_zero fun T hT => ?_
      have hsub : A ∪ T ⊆ S₀ :=
        Finset.union_subset hA ((Finset.mem_powerset.1 hT).trans Finset.sdiff_subset)
      have := hc (A ∪ T) (lt_of_le_of_lt (Finset.card_le_card hsub) hS₀)
      rw [this, mul_zero]
    exact_mod_cast h'
  · have : #{H ∈ S | H ∩ S₀ = A} = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro H - rfl
      exact hA Finset.inter_subset_right
    rw [this, Nat.cast_zero]

/-- **Lemma 2 (support)**: a query `Σ_H f(H ∩ S₀) mod q` with `|S₀| < t_q` returns `0`. -/
theorem support_query_eq_zero (S : Finset (Finset E)) (t : ℕ)
    (hc : ∀ T : Finset E, T.card < t → (cnt S T : ZMod q) = 0) (S₀ : Finset E)
    (hS₀ : S₀.card < t) (f : Finset E → ZMod q) : ∑ H ∈ S, f (H ∩ S₀) = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := S₀.powerset) (g := fun H => H ∩ S₀)
    (fun H _ => Finset.mem_powerset.2 Finset.inter_subset_right)]
  refine Finset.sum_eq_zero fun A _ => ?_
  rw [Finset.sum_congr rfl (fun H hH => by rw [(Finset.mem_filter.1 hH).2]), Finset.sum_const,
    nsmul_eq_mul, fiber_count_eq_zero q S t hc S₀ hS₀ A, zero_mul]

/-- `t_q` (as `tq`) really is a threshold: all `c_T` with `|T| < t_q` vanish mod `q`. -/
theorem cnt_eq_zero_of_lt_tq (S : Finset (Finset E)) (T : Finset E) (hT : T.card < tq q S) :
    (cnt S T : ZMod q) = 0 := by
  by_contra h
  exact absurd (Nat.sInf_le (Set.mem_image_of_mem (fun T : Finset E => T.card)
    (show T ∈ {T : Finset E | (cnt S T : ZMod q) ≠ 0} from h))) (not_le.2 hT)

/-! ### The cube: splitting the powerset at one element -/

section Cube

variable {α : Type*} [DecidableEq α]

theorem sum_powerset_insert' {M : Type*} [AddCommMonoid M] {x : α} {X : Finset α} (hx : x ∉ X)
    (g : Finset α → M) :
    ∑ D ∈ (insert x X).powerset, g D = ∑ D ∈ X.powerset, g D + ∑ D ∈ X.powerset, g (insert x D) := by
  rw [Finset.powerset_insert, Finset.sum_union, Finset.sum_image]
  · intro D hD D' hD' e
    have h1 : x ∉ D := fun h => hx (Finset.mem_powerset.1 hD h)
    have h2 : x ∉ D' := fun h => hx (Finset.mem_powerset.1 hD' h)
    rw [← Finset.erase_insert h1, ← Finset.erase_insert h2]
    exact congrArg (fun s => Finset.erase s x) e
  · rw [Finset.disjoint_left]
    intro D hD hD'
    obtain ⟨D', -, rfl⟩ := Finset.mem_image.1 hD'
    exact hx (Finset.mem_powerset.1 hD (Finset.mem_insert_self x D'))

theorem card_filter_powerset_insert {x : α} {X : Finset α} (hx : x ∉ X) (P : Finset α → Prop)
    [DecidablePred P] :
    #((insert x X).powerset.filter P) =
      #(X.powerset.filter P) + #(X.powerset.filter fun D => P (insert x D)) := by
  simp only [Finset.card_filter]
  exact sum_powerset_insert' hx _

variable {F : Type*} [Field F] [DecidableEq F]

/-- The support bound behind `derandomization.md` Theorem 1: a function `v` on the subsets of `X`,
not identically `0`, with `Σ_{S ⊆ D ⊆ X} v(D) = 0` for every `S ⊆ X` with `|S| < t`, is nonzero on
at least `2^t` subsets. -/
theorem support_card_ge : ∀ (X : Finset α) (t : ℕ) (v : Finset α → F),
    (∀ S ⊆ X, S.card < t → ∑ D ∈ X.powerset, (if S ⊆ D then v D else 0) = 0) →
    (∃ D ∈ X.powerset, v D ≠ 0) → 2 ^ t ≤ #(X.powerset.filter fun D => v D ≠ 0) := by
  intro X
  induction X using Finset.induction_on with
  | empty =>
    intro t v hS hne
    obtain ⟨D, hD, hv⟩ := hne
    have hD0 : D = ∅ := Finset.subset_empty.1 (Finset.mem_powerset.1 hD)
    subst hD0
    rcases t with _ | t
    · simpa using Finset.card_pos.2 ⟨∅, Finset.mem_filter.2 ⟨hD, hv⟩⟩
    · exfalso
      have := hS ∅ (Finset.empty_subset _) (Nat.succ_pos t)
      simp at this
      exact hv this
  | insert x X hx ih =>
    intro t v hS hne
    rcases t with _ | t
    · simpa using Finset.card_pos.2 ⟨_, Finset.mem_filter.2 ⟨hne.choose_spec.1, hne.choose_spec.2⟩⟩
    have hxS : ∀ S ⊆ X, x ∉ S := fun S hS h => hx (hS h)
    -- the two halves
    have hw : ∀ S ⊆ X, S.card < t + 1 →
        ∑ D ∈ X.powerset, (if S ⊆ D then v D + v (insert x D) else 0) = 0 := by
      intro S hSX hcard
      have := hS S (hSX.trans (Finset.subset_insert x X)) hcard
      rw [sum_powerset_insert' hx, ← Finset.sum_add_distrib] at this
      refine (Finset.sum_congr rfl fun D _ => ?_).trans this
      simp only [Finset.subset_insert_iff_of_notMem (hxS S hSX)]
      split_ifs <;> simp
    have hv1 : ∀ S ⊆ X, S.card < t →
        ∑ D ∈ X.powerset, (if S ⊆ D then v (insert x D) else 0) = 0 := by
      intro S hSX hcard
      have hsub : insert x S ⊆ insert x X := Finset.insert_subset_insert x hSX
      have := hS (insert x S) hsub (by rw [Finset.card_insert_of_notMem (hxS S hSX)]; omega)
      rw [sum_powerset_insert' hx] at this
      have h0 : ∑ D ∈ X.powerset, (if insert x S ⊆ D then v D else 0) = 0 := by
        refine Finset.sum_eq_zero fun D hD => ?_
        rw [ite_eq_right]
        intro h
        exact hx (Finset.mem_powerset.1 hD (h (Finset.mem_insert_self x S)))
      rw [h0, zero_add] at this
      refine (Finset.sum_congr rfl fun D hD => ?_).trans this
      have hxD : x ∉ D := fun h => hx (Finset.mem_powerset.1 hD h)
      have : insert x S ⊆ insert x D ↔ S ⊆ D := by
        rw [Finset.insert_subset_iff, Finset.subset_insert_iff_of_notMem (hxS S hSX)]
        simp
      simp only [this]
    have hcount := card_filter_powerset_insert hx (fun D => v D ≠ 0)
    rw [hcount]
    by_cases hw0 : ∃ D ∈ X.powerset, v D + v (insert x D) ≠ 0
    · have h1 := ih (t + 1) (fun D => v D + v (insert x D)) hw hw0
      have h2 : (X.powerset.filter fun D => v D + v (insert x D) ≠ 0) ⊆
          (X.powerset.filter fun D => v D ≠ 0) ∪ (X.powerset.filter fun D => v (insert x D) ≠ 0) := by
        intro D hD
        rw [Finset.mem_filter] at hD
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        by_contra hcon
        push Not at hcon
        exact hD.2 (by rw [hcon.1 hD.1, hcon.2 hD.1, add_zero])
      exact h1.trans ((Finset.card_le_card h2).trans (Finset.card_union_le _ _))
    · push Not at hw0
      have hv1ne : ∃ D ∈ X.powerset, v (insert x D) ≠ 0 := by
        obtain ⟨D, hD, hvD⟩ := hne
        rw [Finset.powerset_insert, Finset.mem_union] at hD
        rcases hD with hD | hD
        · refine ⟨D, hD, fun h0 => hvD ?_⟩
          have := hw0 D hD
          rw [h0, add_zero] at this
          exact this
        · obtain ⟨D', hD', rfl⟩ := Finset.mem_image.1 hD
          exact ⟨D', hD', hvD⟩
      have h1 := ih t (fun D => v (insert x D)) hv1 hv1ne
      have heq : (X.powerset.filter fun D => v D ≠ 0) =
          (X.powerset.filter fun D => v (insert x D) ≠ 0) := by
        refine Finset.filter_congr fun D hD => ?_
        have := hw0 D hD
        rw [add_eq_zero_iff_eq_neg] at this
        rw [this, neg_ne_zero]
      rw [heq, pow_succ]
      omega

/-- `Σ_{B ⊆ D ⊆ X} (−1)^{|D|} = 0` for `B ⊊ X`. -/
theorem alt_sum_eq_zero {X B : Finset α} (hBX : B ⊆ X) (hne : B ≠ X) :
    ∑ D ∈ X.powerset, (if B ⊆ D then (-1 : F) ^ D.card else 0) = 0 := by
  obtain ⟨y, hyX, hyB⟩ : ∃ y ∈ X, y ∉ B := by
    by_contra h
    push Not at h
    exact hne (Finset.Subset.antisymm hBX h)
  have hy' : y ∉ X.erase y := Finset.notMem_erase y X
  rw [← Finset.insert_erase hyX, sum_powerset_insert' hy', ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun D hD => ?_
  have hyD : y ∉ D := fun h => hy' (Finset.mem_powerset.1 hD h)
  simp only [Finset.subset_insert_iff_of_notMem hyB, Finset.card_insert_of_notMem hyD]
  split_ifs <;> ring

/-- The `⊇` half of "this orthogonal complement is exactly `{(−1)^{|x|} g(x) : deg g ≤ n−t}`":
for `g(x) = Σ_{M ⊆ x} a_M` of degree `≤ |X| − t`, the function `(−1)^{|D|} g(D)` is orthogonal
to every monomial of degree `< t`. -/
theorem alternating_mul_satisfies (X : Finset α) (t : ℕ) (a : Finset α → F)
    (hdeg : ∀ M ∈ X.powerset, a M ≠ 0 → M.card + t ≤ X.card) (S : Finset α) (hSX : S ⊆ X)
    (hS : S.card < t) :
    ∑ D ∈ X.powerset, (if S ⊆ D then (-1 : F) ^ D.card * ∑ M ∈ D.powerset, a M else 0) = 0 := by
  have h1 : ∀ D ∈ X.powerset, ∑ M ∈ D.powerset, a M =
      ∑ M ∈ X.powerset, if M ⊆ D then a M else 0 := by
    intro D hD
    rw [← Finset.sum_filter]
    congr 1
    ext M
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun h => ⟨h.trans (Finset.mem_powerset.1 hD), h⟩, fun h => h.2⟩
  rw [Finset.sum_congr rfl fun D hD => by rw [h1 D hD]]
  have h2 : ∀ D, (if S ⊆ D then (-1 : F) ^ D.card * ∑ M ∈ X.powerset, (if M ⊆ D then a M else 0)
      else 0) = ∑ M ∈ X.powerset, a M * (if S ∪ M ⊆ D then (-1 : F) ^ D.card else 0) := by
    intro D
    split_ifs with hSD
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun M _ => ?_
      by_cases hM : M ⊆ D <;> simp [hM, hSD, Finset.union_subset_iff, mul_comm]
    · symm
      refine Finset.sum_eq_zero fun M _ => ?_
      simp [Finset.union_subset_iff, hSD]
  rw [Finset.sum_congr rfl fun D _ => h2 D, Finset.sum_comm]
  refine Finset.sum_eq_zero fun M hM => ?_
  rw [← Finset.mul_sum]
  by_cases ha : a M = 0
  · rw [ha, zero_mul]
  have hc := hdeg M hM ha
  have hsub : S ∪ M ⊆ X := Finset.union_subset hSX (Finset.mem_powerset.1 hM)
  have hne : S ∪ M ≠ X := by
    intro h
    have := Finset.card_union_le S M
    rw [h] at this
    omega
  rw [alt_sum_eq_zero hsub hne, mul_zero]

/-- "A nonzero multilinear g of degree ≤ n−t is nonzero on at least `2^t` points of the cube."
Points of the cube `{0,1}^X` are subsets `x ⊆ X`; `g(x) = Σ_{M ⊆ x} a_M` is the value at the
indicator of `x` of `Σ_M a_M Π_{i∈M} x_i`; the degree bound is `a_M ≠ 0 ⇒ |M| ≤ |X| − t`. -/
theorem multilinear_nonzero_points (X : Finset α) (t : ℕ) (a : Finset α → F)
    (hdeg : ∀ M ∈ X.powerset, a M ≠ 0 → M.card + t ≤ X.card)
    (hne : ∃ x ∈ X.powerset, ∑ M ∈ x.powerset, a M ≠ 0) :
    2 ^ t ≤ #(X.powerset.filter fun x => ∑ M ∈ x.powerset, a M ≠ 0) := by
  have hsgn : ∀ k : ℕ, (-1 : F) ^ k ≠ 0 := fun k => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have := support_card_ge X t (fun D => (-1 : F) ^ D.card * ∑ M ∈ D.powerset, a M)
    (fun S hSX hS => alternating_mul_satisfies X t a hdeg S hSX hS)
    (by obtain ⟨x, hx, h⟩ := hne; exact ⟨x, hx, mul_ne_zero (hsgn _) h⟩)
  convert this using 2
  refine Finset.filter_congr fun x _ => ?_
  rw [ne_eq, ne_eq, mul_eq_zero, not_or]
  exact ⟨fun h => ⟨hsgn _, h⟩, fun h => h.2⟩

end Cube

/-! ### Theorem 1: `t_p(G) ≤ log₂ #HC(G)` -/

theorem sum_fiber_eq (S : Finset (Finset E)) (H₀ S' : Finset E) :
    ∑ D ∈ H₀.powerset, (if S' ⊆ D then #{H ∈ S | H₀ \ H = D} else 0) = #{H ∈ S | S' ⊆ H₀ \ H} := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun H => H₀ \ H) (t := H₀.powerset)
    (fun H _ => Finset.mem_powerset.2 Finset.sdiff_subset)]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [Finset.filter_filter]
  split_ifs with h
  · congr 1
    exact Finset.filter_congr fun H _ => ⟨fun e => ⟨e ▸ h, e⟩, fun h' => h'.2⟩
  · symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro H - ⟨h1, rfl⟩
    exact h h1

/-- **`derandomization.md` Theorem 1**, core form: let `H₀ ∈ S` be such that no other member of
`S` contains `H₀` (true for Hamiltonian cycles, which all have `n` edges). If `c_T ≡ 0 (mod p)`
for every `|T| < t` (i.e. `t ≤ t_p`), then `#S ≥ 2^t`. -/
theorem two_pow_le_card_of_contains_zero (p : ℕ) [Fact p.Prime] (S : Finset (Finset E))
    (H₀ : Finset E) (hH₀ : H₀ ∈ S) (hmax : ∀ H ∈ S, H₀ ⊆ H → H = H₀) (t : ℕ)
    (hc : ∀ T : Finset E, T.card < t → (cnt S T : ZMod p) = 0) : 2 ^ t ≤ S.card := by
  let v : Finset E → ZMod p := fun D => ((#{H ∈ S | H₀ \ H = D} : ℕ) : ZMod p)
  have hcond : ∀ S' ⊆ H₀, S'.card < t →
      ∑ D ∈ H₀.powerset, (if S' ⊆ D then v D else 0) = 0 := by
    intro S' hS'H hS'
    have e1 : ∑ D ∈ H₀.powerset, (if S' ⊆ D then v D else 0) =
        ((∑ D ∈ H₀.powerset, (if S' ⊆ D then #{H ∈ S | H₀ \ H = D} else 0) : ℕ) : ZMod p) := by
      push_cast
      exact Finset.sum_congr rfl fun D _ => by split_ifs <;> simp [v]
    rw [e1, sum_fiber_eq]
    have e2 : #{H ∈ S | S' ⊆ H₀ \ H} = deleted S S' := by
      unfold deleted
      congr 1
      refine Finset.filter_congr fun H _ => ?_
      rw [Finset.subset_sdiff]
      exact ⟨fun h => h.2.symm, fun h => ⟨hS'H, h.symm⟩⟩
    rw [e2]
    have h' : ((deleted S S' : ℤ) : ZMod p) = 0 := by
      rw [deleted_eq_sum]
      push_cast
      refine Finset.sum_eq_zero fun T hT => ?_
      rw [hc T (lt_of_le_of_lt (Finset.card_le_card (Finset.mem_powerset.1 hT)) hS'), mul_zero]
    exact_mod_cast h'
  have hv0 : v ∅ ≠ 0 := by
    have : #{H ∈ S | H₀ \ H = ∅} = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨H₀, ?_⟩
      ext H
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.sdiff_eq_empty_iff_subset]
      constructor
      · rintro ⟨hH, hsub⟩; exact hmax H hH hsub
      · rintro rfl; exact ⟨hH₀, Finset.Subset.refl _⟩
    show ((#{H ∈ S | H₀ \ H = ∅} : ℕ) : ZMod p) ≠ 0
    rw [this, Nat.cast_one]
    exact one_ne_zero
  have hsupp := support_card_ge H₀ t v hcond ⟨∅, Finset.empty_mem_powerset _, hv0⟩
  have hsub : (H₀.powerset.filter fun D => v D ≠ 0) ⊆ S.image (fun H => H₀ \ H) := by
    intro D hD
    have hvD := (Finset.mem_filter.1 hD).2
    have : (S.filter fun H => H₀ \ H = D).Nonempty := by
      rw [← Finset.card_pos]
      by_contra h0
      apply hvD
      simp [v, Nat.le_zero.1 (not_lt.1 h0)]
    obtain ⟨H, hH⟩ := this
    exact Finset.mem_image.2 ⟨H, (Finset.mem_filter.1 hH).1, (Finset.mem_filter.1 hH).2⟩
  exact hsupp.trans ((Finset.card_le_card hsub).trans Finset.card_image_le)

/-- **`derandomization.md` Theorem 1**: `t_p ≤ log₂ #S` for every prime `p` (with `H₀ ∈ S` not
strictly contained in another member of `S`). -/
theorem tp_le_log (p : ℕ) [Fact p.Prime] (S : Finset (Finset E)) (H₀ : Finset E) (hH₀ : H₀ ∈ S)
    (hmax : ∀ H ∈ S, H₀ ⊆ H → H = H₀) : tq p S ≤ Nat.log 2 S.card :=
  Nat.le_log_of_pow_le (by norm_num)
    (two_pow_le_card_of_contains_zero p S H₀ hH₀ hmax _ fun T hT => cnt_eq_zero_of_lt_tq p S T hT)

/-- Theorem 1 for a family of equal-size sets (e.g. the Hamiltonian cycles of a graph, all of
size `n`): `t_p ≤ log₂ #S` whenever `S ≠ ∅`. -/
theorem tp_le_log_of_card_eq (p : ℕ) [Fact p.Prime] (S : Finset (Finset E)) (hS : S.Nonempty)
    (k : ℕ) (hk : ∀ H ∈ S, H.card = k) : tq p S ≤ Nat.log 2 S.card := by
  obtain ⟨H₀, hH₀⟩ := hS
  exact tp_le_log p S H₀ hH₀ fun H hH hsub =>
    (Finset.eq_of_subset_of_card_le hsub (by rw [hk H hH, hk H₀ hH₀])).symm

/-- Theorem 1 for **every** nonempty family (no antichain hypothesis needed: take `H₀` maximal
for inclusion). -/
theorem tp_le_log_of_nonempty (p : ℕ) [Fact p.Prime] (S : Finset (Finset E)) (hS : S.Nonempty) :
    tq p S ≤ Nat.log 2 S.card := by
  obtain ⟨H₀, hH₀, hmax⟩ := Finset.exists_maximal hS
  exact tp_le_log p S H₀ hH₀ fun H hH hsub => Finset.Subset.antisymm (hmax hH hsub) hsub

/-- The composite-modulus remark: if `p ∣ q` then `c_T ≢ 0 (mod p)` implies `c_T ≢ 0 (mod q)`. -/
theorem contains_ne_zero_of_dvd {p : ℕ} (hpq : p ∣ q) (x : ℕ) (h : (x : ZMod p) ≠ 0) :
    (x : ZMod q) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff] at h ⊢
  exact fun hq => h (hpq.trans hq)

/-- "For composite q, `t_q ≤ t_p` whenever p | q" (for `t_p` finite, i.e. some `c_T ≢ 0 mod p`). -/
theorem tq_le_tp {p : ℕ} (hpq : p ∣ q) (S : Finset (Finset E))
    (hfin : ∃ T : Finset E, (cnt S T : ZMod p) ≠ 0) : tq q S ≤ tq p S := by
  obtain ⟨T₀, hT₀⟩ := hfin
  exact sInf_le_of_imp _ _ _ _ ⟨T₀, hT₀⟩ fun t ⟨T, hT, hle⟩ =>
    ⟨T, contains_ne_zero_of_dvd q hpq _ hT, hle⟩

end EthFollowup.Barriers.Derand
