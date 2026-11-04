/-
# Cut rank of the product indicator (research/iterated-product.md §2.1)

* `rank_eq_card_of_disjoint_rows`: a matrix whose nonzero rows have pairwise disjoint supports has
  rank = number of nonzero rows (over any field).
* `prodMat A B C`: rows u ∈ A (product of the factors on one side of the cut), columns (v, m) ∈ B × C
  (other side's product and the *label* m), entry [u·v = m].  `rank_prodMat`: rank = #{u ∈ A realised};
  with 1 ∈ B and A ⊆ C this is |A| (`rank_prodMat_full`), i.e. 2^{bits(S)} for A = [1, 2^{bits S}].
  So a cut separating the factors S from the label m needs ≥ bits(S) crossing bits.
* `prodMatFixed A B m`: m hard-wired; `rank_prodMatFixed_le`: rank ≤ τ(m).  So with m fixed no cut can
  be forced above log τ(m) ≤ (1+o(1)) n/log n.
-/
import EthFollowup.Barriers.RankBounds
import Mathlib.NumberTheory.Divisors

set_option linter.unusedSectionVars false

namespace EthFollowup.IterProd

open Matrix Finset EthFollowup.Barriers.Rank

variable {K : Type*} [Field K] {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]

/-- the nonzero rows of `M` -/
abbrev NZ (M : Matrix X Y K) := {x : X // ∃ y, M x y ≠ 0}

noncomputable instance instFintypeNZ (M : Matrix X Y K) : Fintype (NZ M) := Fintype.ofFinite _

/-- Rows with pairwise disjoint supports: `rank M = #nonzero rows`. -/
theorem rank_eq_card_of_disjoint_rows (M : Matrix X Y K)
    (hdisj : ∀ x x' y, x ≠ x' → M x y * M x' y = 0) :
    M.rank = Fintype.card (NZ M) := by
  classical
  let u : NZ M → X → K := fun t x => if x = t.1 then 1 else 0
  let v : NZ M → Y → K := fun t y => M t.1 y
  have hu : LinearIndependent K u := by
    have h := (Pi.basisFun K X).linearIndependent
    have h2 : LinearIndependent K (fun t : NZ M => Pi.basisFun K X t.1) :=
      h.comp (fun t : NZ M => t.1) Subtype.val_injective
    convert h2 using 2 with t
    funext x
    simp [u, Pi.basisFun_apply, Pi.single_apply]
  have hv : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t
    obtain ⟨y, hy⟩ := t.2
    have := congrFun hc y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [Finset.sum_eq_single t] at this
    · simp only [v] at this
      exact (mul_eq_zero.mp this).resolve_right hy
    · intro t' _ htt'
      have hne : t'.1 ≠ t.1 := fun h => htt' (Subtype.ext h)
      have h0 := hdisj t'.1 t.1 y hne
      rcases mul_eq_zero.mp h0 with h0 | h0
      · simp [v, h0]
      · exact absurd h0 hy
    · intro h; exact absurd (Finset.mem_univ t) h
  refine rank_eq_card_of_linearIndependent u v hu hv M fun x y => ?_
  by_cases hx : ∃ y, M x y ≠ 0
  · rw [Finset.sum_eq_single ⟨x, hx⟩]
    · simp [u, v]
    · intro t _ ht
      have : x ≠ t.1 := fun h => ht (Subtype.ext h.symm)
      simp [u, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [not_exists, not_not] at hx
    rw [hx y]
    symm
    apply Finset.sum_eq_zero
    intro t _
    have : x ≠ t.1 := fun h => by
      obtain ⟨y', hy'⟩ := t.2; exact hy' (h ▸ hx y')
    simp [u, this]

/-! ### The product indicator with `m` a label -/

/-- `[u · v = m]` with rows `u ∈ A`, columns `(v, m) ∈ B × C`. -/
def prodMat (A B C : Finset ℕ) : Matrix A (B × C) ℚ :=
  fun u vm => if u.1 * vm.1.1 = vm.2.1 then 1 else 0

theorem prodMat_disjoint (A B C : Finset ℕ) (hB : ∀ v ∈ B, 0 < v) :
    ∀ x x' y, x ≠ x' → prodMat A B C x y * prodMat A B C x' y = 0 := by
  intro x x' y hne
  simp only [prodMat]
  split_ifs with h1 h2
  · exfalso
    apply hne; apply Subtype.ext
    have hv := hB y.1.1 y.1.2
    exact Nat.eq_of_mul_eq_mul_right hv (h1.trans h2.symm)
  all_goals simp

/-- rank = number of `u ∈ A` that have some partner `(v, m)` with `u v = m`. -/
theorem rank_prodMat (A B C : Finset ℕ) (hB : ∀ v ∈ B, 0 < v) :
    (prodMat A B C).rank = Fintype.card (NZ (prodMat A B C)) :=
  rank_eq_card_of_disjoint_rows _ (prodMat_disjoint A B C hB)

/-- Full rank `|A|` when every `u ∈ A` is realised (e.g. `1 ∈ B`, `A ⊆ C`). -/
theorem rank_prodMat_full (A B C : Finset ℕ) (hB : ∀ v ∈ B, 0 < v) (h1 : 1 ∈ B) (hAC : A ⊆ C) :
    (prodMat A B C).rank = A.card := by
  rw [rank_prodMat A B C hB]
  have : ∀ x : A, ∃ y, prodMat A B C x y ≠ 0 := fun x =>
    ⟨(⟨1, h1⟩, ⟨x.1, hAC x.2⟩), by simp [prodMat]⟩
  rw [Fintype.card_of_subtype Finset.univ (fun x => by simp [this x]), Finset.card_univ,
    Fintype.card_coe]

/-- The cut of §2.1(a): `A = [1, 2^a]`, `B = [1, 2^b]`, `C = [1, 2^(a+b)]`: rank `= 2^a`. -/
theorem rank_prodMat_pow (a b : ℕ) :
    (prodMat (Icc 1 (2 ^ a)) (Icc 1 (2 ^ b)) (Icc 1 (2 ^ (a + b)))).rank = 2 ^ a := by
  rw [rank_prodMat_full]
  · simp
  · intro v hv; exact (Finset.mem_Icc.mp hv).1
  · exact Finset.mem_Icc.mpr ⟨le_rfl, Nat.one_le_two_pow⟩
  · intro u hu
    have := Finset.mem_Icc.mp hu
    exact Finset.mem_Icc.mpr ⟨this.1, this.2.trans (Nat.pow_le_pow_right (by norm_num) (by omega))⟩

/-! ### The product indicator with `m` hard-wired -/

/-- `[u · v = m]`, rows `u ∈ A`, columns `v ∈ B`, `m` fixed. -/
def prodMatFixed (A B : Finset ℕ) (m : ℕ) : Matrix A B ℚ :=
  fun u v => if u.1 * v.1 = m then 1 else 0

/-- With `m` fixed the cut rank is at most `τ(m)`. -/
theorem rank_prodMatFixed_le (A B : Finset ℕ) (m : ℕ) (hm : m ≠ 0) :
    (prodMatFixed A B m).rank ≤ (Nat.divisors m).card := by
  apply rank_le_card_of_eq_sum_mul' (Nat.divisors m) (prodMatFixed A B m)
    (fun u d => if u.1 = d then 1 else 0) (fun d v => if d * v.1 = m then 1 else 0)
  intro u v
  simp only [prodMatFixed]
  by_cases h : u.1 * v.1 = m
  · rw [if_pos h, Finset.sum_eq_single u.1]
    · simp [h]
    · intro d _ hd; simp [Ne.symm hd]
    · intro hu; exact absurd (Nat.mem_divisors.mpr ⟨Dvd.intro _ h, hm⟩) hu
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro d _
    by_cases hd : u.1 = d
    · subst hd; simp [h]
    · simp [hd]

end EthFollowup.IterProd

#print axioms EthFollowup.IterProd.rank_eq_card_of_disjoint_rows
#print axioms EthFollowup.IterProd.rank_prodMat_pow
#print axioms EthFollowup.IterProd.rank_prodMatFixed_le
