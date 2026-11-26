import Mathlib

/-!
# Toeplitz hashing is pairwise independent

Indexing (matches `c1d1/notes.md`, C1.2): for `a : Fin (n + k - 1) → F` and `z : Fin n → F`,
`(T_a z)_j = ∑_i a_{(n-1-i)+j} * z_i`, i.e. `(T_a)_{j,i} = a_{n-1+j-i}` (`0 ≤ j < k`, `0 ≤ i < n`).
The hash is `h_{a,b}(x) = T_a x + b`.

Surjectivity of `a ↦ T_a z` (for `z ≠ 0`) is proved in dual form: a functional `w` on `F^k`
vanishing on the range satisfies `∑_{j,i : n-1-i+j = l} w_j z_i = 0` for every `l`; taking
`j*` = largest index with `w_{j*} ≠ 0` and `i*` = least index with `z_{i*} ≠ 0`, the equation
at `l = n-1-i*+j*` has the single surviving term `w_{j*} z_{i*} ≠ 0` (triangularity).
This works over any field.
-/

open Finset

namespace IsoLean

variable {F : Type*} [Field F]

/-- The index `(n-1-i)+j` into `a : Fin (n+k-1) → F`. -/
def tIdx (n k : ℕ) (j : Fin k) (i : Fin n) : Fin (n + k - 1) :=
  ⟨n - 1 - i + j, by have := i.isLt; have := j.isLt; omega⟩

/-- `(T_a z)_j = ∑_i a_{n-1-i+j} z_i`. -/
def toeplitzMul (n k : ℕ) (a : Fin (n + k - 1) → F) (z : Fin n → F) : Fin k → F :=
  fun j => ∑ i, a (tIdx n k j i) * z i

lemma toeplitzMul_sub (n k : ℕ) (a : Fin (n + k - 1) → F) (x y : Fin n → F) :
    toeplitzMul n k a (x - y) = toeplitzMul n k a x - toeplitzMul n k a y := by
  ext j; simp [toeplitzMul, mul_sub, sum_sub_distrib]

/-- `a ↦ T_a z` as an `F`-linear map. -/
def toeplitzLin (n k : ℕ) (z : Fin n → F) : (Fin (n + k - 1) → F) →ₗ[F] (Fin k → F) where
  toFun a := toeplitzMul n k a z
  map_add' a b := by ext j; simp [toeplitzMul, add_mul, sum_add_distrib]
  map_smul' c a := by ext j; simp [toeplitzMul, mul_sum, mul_assoc]

@[simp] lemma toeplitzLin_apply (n k : ℕ) (z : Fin n → F) (a : Fin (n + k - 1) → F) :
    toeplitzLin n k z a = toeplitzMul n k a z := rfl

/-- A linear map into `F^k` is surjective if no nonzero `w` is orthogonal to its range. -/
lemma surjective_of_orth {V : Type*} [AddCommGroup V] [Module F V] {k : ℕ}
    (f : V →ₗ[F] (Fin k → F))
    (h : ∀ w : Fin k → F, (∀ v, ∑ j, w j * f v j = 0) → w = 0) : Function.Surjective f := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  apply hφ
  have hw : (fun j => φ (fun l => if j = l then (1 : F) else 0)) = 0 := by
    apply h
    intro v
    have : φ (f v) = 0 := hle ⟨v, rfl⟩
    rw [LinearMap.pi_apply_eq_sum_univ φ (f v)] at this
    simpa [smul_eq_mul, mul_comm] using this
  apply LinearMap.ext
  intro y
  rw [LinearMap.pi_apply_eq_sum_univ φ y]
  simp only [LinearMap.zero_apply]
  apply sum_eq_zero
  intro j _
  have := congrFun hw j
  simp only [Pi.zero_apply] at this
  rw [this, smul_zero]

/-- The triangular (dual) argument. -/
theorem toeplitz_orth_eq_zero (n k : ℕ) (z : Fin n → F) (hz : z ≠ 0) (w : Fin k → F)
    (hw : ∀ a : Fin (n + k - 1) → F, ∑ j, w j * toeplitzMul n k a z j = 0) : w = 0 := by
  classical
  by_contra hw0
  obtain ⟨j0, hj0⟩ : ∃ j, w j ≠ 0 := by
    by_contra hc; push Not at hc; exact hw0 (funext hc)
  obtain ⟨i0, hi0⟩ : ∃ i, z i ≠ 0 := by
    by_contra hc; push Not at hc; exact hz (funext hc)
  obtain ⟨js, hjs, hjmax⟩ := exists_max_image (univ.filter (fun j => w j ≠ 0)) (fun j => j.val)
    ⟨j0, by simp [hj0]⟩
  obtain ⟨is, his, himin⟩ := exists_min_image (univ.filter (fun i => z i ≠ 0)) (fun i => i.val)
    ⟨i0, by simp [hi0]⟩
  simp only [mem_filter_univ] at hjs his hjmax himin
  set l := tIdx n k js is with hl
  have key := hw (Pi.single l 1)
  simp only [toeplitzMul, Pi.single_apply] at key
  rw [sum_eq_single js] at key
  · rw [sum_eq_single is] at key
    · rw [if_pos rfl, one_mul] at key
      exact mul_ne_zero hjs his key
    · intro i _ hne
      rw [if_neg, zero_mul]
      intro heq
      apply hne
      simp only [hl, tIdx, Fin.ext_iff] at heq
      have := i.isLt; have := is.isLt
      exact Fin.ext (by omega)
    · simp
  · intro j _ hne
    by_cases hwj : w j = 0
    · simp [hwj]
    have hjle := hjmax j hwj
    have hjlt : j.val < js.val := lt_of_le_of_ne hjle (fun h => hne (Fin.ext h))
    rw [sum_eq_zero, mul_zero]
    intro i _
    by_cases heq : tIdx n k j i = l
    · rw [if_pos heq]
      have hzi : z i = 0 := by
        by_contra hzi
        have := himin i hzi
        simp only [hl, tIdx, Fin.ext_iff] at heq
        have := i.isLt; have := is.isLt
        omega
      simp [hzi]
    · rw [if_neg heq, zero_mul]
  · simp

/-- **Key step.** For `z ≠ 0`, `a ↦ T_a z` is surjective. -/
theorem toeplitz_surjective (n k : ℕ) (z : Fin n → F) (hz : z ≠ 0) :
    Function.Surjective (toeplitzLin (F := F) n k z) :=
  surjective_of_orth _ (fun w hw => toeplitz_orth_eq_zero n k z hz w (fun a => hw a))

/-- Every fibre of a surjective additive homomorphism of finite groups has `|V| / |W|` elements. -/
lemma card_fiber_mul_card {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Fintype V] [Fintype W]
    [DecidableEq W] (f : V →+ W) (hf : Function.Surjective f) (s : W) :
    (univ.filter (fun v => f v = s)).card * Fintype.card W = Fintype.card V := by
  classical
  have hfib : ∀ t : W, (univ.filter (fun v => f v = t)).card =
      (univ.filter (fun v => f v = s)).card := by
    intro t
    obtain ⟨vt, hvt⟩ := hf t
    obtain ⟨vs, hvs⟩ := hf s
    refine card_bij' (fun v _ => v - vt + vs) (fun v _ => v - vs + vt) ?_ ?_ ?_ ?_
    · intro v hv; simp only [mem_filter_univ] at hv ⊢
      rw [map_add, map_sub, hv, hvt, hvs]; abel
    · intro v hv; simp only [mem_filter_univ] at hv ⊢
      rw [map_add, map_sub, hv, hvt, hvs]; abel
    · intro v _; abel
    · intro v _; abel
  have := card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ) (fun _ _ => mem_univ _)
  rw [card_univ] at this
  rw [this, sum_congr rfl (fun t _ => hfib t), sum_const, card_univ, smul_eq_mul, mul_comm]

/-- Fibre size of `a ↦ T_a z` for `z ≠ 0` over a finite field. -/
theorem toeplitz_fiber_card [Fintype F] [DecidableEq F] (n k : ℕ) (z : Fin n → F) (hz : z ≠ 0)
    (s : Fin k → F) :
    (univ.filter (fun a : Fin (n + k - 1) → F => toeplitzMul n k a z = s)).card
      * Fintype.card F ^ k = Fintype.card F ^ (n + k - 1) := by
  have := card_fiber_mul_card (toeplitzLin (F := F) n k z).toAddMonoidHom
    (toeplitz_surjective n k z hz) s
  simp only [Fintype.card_fun, Fintype.card_fin, LinearMap.toAddMonoidHom_coe,
    toeplitzLin_apply] at this
  convert this using 3
  ext a
  set_option pp.explicit true in trace_state
  sorry

/-- The Toeplitz hash `h_{a,b}(x) = T_a x + b`, keyed by `p = (a, b)`. -/
def hash (n k : ℕ) (p : (Fin (n + k - 1) → F) × (Fin k → F)) (x : Fin n → F) : Fin k → F :=
  toeplitzMul n k p.1 x + p.2

/-- Uniform marginals: `#{(a,b) : h(x) = s} * q^k = q^(n+k-1) * q^k`. -/
theorem hash_uniform [Fintype F] [DecidableEq F] (n k : ℕ) (x : Fin n → F) (s : Fin k → F) :
    (univ.filter (fun p => hash n k p x = s)).card * Fintype.card F ^ k
      = Fintype.card F ^ (n + k - 1) * Fintype.card F ^ k := by
  congr 1
  have : (univ.filter (fun p => hash n k p x = s)).card
      = (univ : Finset (Fin (n + k - 1) → F)).card := by
    refine card_bij' (fun p _ => p.1) (fun a _ => (a, s - toeplitzMul n k a x)) ?_ ?_ ?_ ?_
    · intro p _; exact mem_univ _
    · intro a _; rw [mem_filter_univ]; simp [hash]
    · intro p hp
      rw [mem_filter_univ] at hp
      simp only [hash] at hp
      ext <;> simp [← hp]
    · intro a _; rfl
  rw [this, card_univ, Fintype.card_fun, Fintype.card_fin]

/-- **Pairwise independence.** For `x ≠ y` and any targets `s, t`:
`#{(a,b) : h(x) = s ∧ h(y) = t} * (q^k)^2 = q^(n+k-1) * q^k`. -/
theorem hash_pairwise [Fintype F] [DecidableEq F] (n k : ℕ) (x y : Fin n → F) (hxy : x ≠ y)
    (s t : Fin k → F) :
    (univ.filter (fun p => hash n k p x = s ∧ hash n k p y = t)).card * (Fintype.card F ^ k) ^ 2
      = Fintype.card F ^ (n + k - 1) * Fintype.card F ^ k := by
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hc : (univ.filter (fun p => hash n k p x = s ∧ hash n k p y = t)).card
      = (univ.filter (fun a : Fin (n + k - 1) → F => toeplitzMul n k a (x - y) = s - t)).card := by
    refine card_bij' (fun p _ => p.1) (fun a _ => (a, s - toeplitzMul n k a x)) ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_filter_univ] at hp ⊢
      simp only [hash] at hp
      rw [toeplitzMul_sub, ← hp.1, ← hp.2]; abel
    · intro a ha
      rw [mem_filter_univ] at ha ⊢
      simp only [hash]
      rw [toeplitzMul_sub] at ha
      refine ⟨by abel, ?_⟩
      rw [← sub_eq_zero] at ha ⊢
      rw [← neg_eq_zero, ← ha]; abel
    · intro p hp
      rw [mem_filter_univ] at hp
      simp only [hash] at hp
      ext <;> simp [← hp.1]
    · intro a _; rfl
  rw [hc, sq, ← mul_assoc, toeplitz_fiber_card n k _ hz]

/-- The statement requested for `F₂`: count `= 2^((n+k-1)+k) / 4^k`, stated without division. -/
theorem hash_pairwise_F2 (n k : ℕ) (x y : Fin n → ZMod 2) (hxy : x ≠ y) (s t : Fin k → ZMod 2) :
    (univ.filter (fun p => hash n k p x = s ∧ hash n k p y = t)).card * 4 ^ k
      = 2 ^ ((n + k - 1) + k) := by
  have := hash_pairwise n k x y hxy s t
  rw [ZMod.card, ← pow_mul, mul_comm k 2, pow_mul, ← pow_add] at this
  norm_num at this
  exact this

/-- Equivalently, the count is exactly `2^(n-1)` (for `x ≠ y` to exist, `n ≥ 1`). -/
theorem hash_pairwise_F2' (n k : ℕ) (x y : Fin n → ZMod 2) (hxy : x ≠ y)
    (s t : Fin k → ZMod 2) :
    (univ.filter (fun p => hash n k p x = s ∧ hash n k p y = t)).card = 2 ^ (n - 1) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd (Subsingleton.elim x y) hxy
    · exact h
  have h := hash_pairwise_F2 n k x y hxy s t
  have e : (n + k - 1) + k = (n - 1) + 2 * k := by omega
  rw [e, pow_add, pow_mul] at h
  norm_num at h
  exact h

end IsoLean
