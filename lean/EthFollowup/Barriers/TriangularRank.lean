/-
# The triangular rank bound (`research/permanent/parity-barrier.md` Theorem 1)

Source (`parity-barrier.md` §2):

> **Theorem 1 [P].** Let B be any finite coordinate set with schedules a, d : B → [r]^Q and let M
> satisfy (T2). For every function φ : [r]^Q → ℝ that is 1-Lipschitz for the Hamming metric,
>
>   rank(I − M) ≥ #{u ∈ B : φ(d_u) − φ(a_u) ≥ R}.
>
> *Proof.* Let U be the set on the right, ordered u₁, u₂, … by non-increasing φ(a_u). For i ≤ j,
> φ(d_{u_i}) − φ(a_{u_j}) ≥ φ(d_{u_i}) − φ(a_{u_i}) ≥ R, hence d_H(d_{u_i}, a_{u_j}) ≥ R and
> M[u_i,u_j] = 0 by (T2). So (I − M)[U,U] is lower triangular with unit diagonal. ∎
>
> Special case (independent sets): if d_H(A,B') ≥ R then rank(I − M) ≥ #{u : d_u ∈ A, a_u ∈ B'}
> ((I − M)[U,U] = I_U).

with (T2) "support: M₀[u,w] ≠ 0 ⇒ |E_{u,w}| ≤ R − 1", `E_{u,w} = {t : a_w(t) ≠ d_u(t)}`, i.e.
`d_H(d_u, a_w) ≤ R − 1`.

Formalised over any field, with `M ∈ K^{B×B}`:
* `card_le_rank_one_sub_of_triangular` — the linear-algebra core: if `M[u,w] = 0` whenever
  `u, w ∈ U` and `ψ(w) ≤ ψ(u)`, then `|U| ≤ rank(1 − M)`;
* `triangular_rank_bound` — Theorem 1 for an arbitrary "distance" `dist` and any `φ` with
  `φ x − φ y ≤ dist x y` (which is what 1-Lipschitz is used for), (T2) as
  `M[u,w] ≠ 0 → dist (d u) (a w) < R`;
* `triangular_rank_bound_hamming` — Theorem 1 verbatim: labels `Fin Q → Fin r`, Hamming
  distance, (T2) as `d_H(d_u, a_w) + 1 ≤ R` (i.e. `≤ R − 1`), `φ` 1-Lipschitz;
* `independent_sets_rank_bound` — the special case.
Corollary 1.1 (the binomial estimate) is not formalised.
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.InformationTheory.Hamming
import Mathlib.Basic.Real.Basic

set_option linter.unusedSectionVars false

namespace EthFollowup.Barriers.Triangular

open Matrix Finset

variable {K : Type*} [Field K] {B : Type*} [Fintype B] [DecidableEq B]

/-- Linear-algebra core: a set `U` on which `1 − M` is "triangular with unit diagonal" for the
preorder `ψ` (`M[u,w] = 0` whenever `ψ w ≤ ψ u`, including `u = w`) gives `|U| ≤ rank(1 − M)`. -/
theorem card_le_rank_one_sub_of_triangular (M : Matrix B B K) (U : Finset B) (ψ : B → ℝ)
    (h : ∀ u ∈ U, ∀ w ∈ U, ψ w ≤ ψ u → M u w = 0) : U.card ≤ (1 - M).rank := by
  classical
  let A : Matrix U U K := (1 - M).submatrix Subtype.val Subtype.val
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have hsupp : (univ.filter fun w => v w ≠ 0).Nonempty := by
      by_contra hne
      apply hv0
      funext w
      by_contra hw
      exact hne ⟨w, by simpa using hw⟩
    obtain ⟨w₀, hw₀, hmax⟩ := Finset.exists_max_image _ (fun w : U => ψ w.1) hsupp
    have hrow := congrFun hv w₀
    have : (A *ᵥ v) w₀ = v w₀ := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single w₀]
      · simp [A, Matrix.sub_apply, h w₀.1 w₀.2 w₀.1 w₀.2 le_rfl]
      · intro w _ hw
        by_cases hvw : v w = 0
        · simp [hvw]
        · have hle : ψ w.1 ≤ ψ w₀.1 := hmax w (by simp [hvw])
          have hM0 := h w₀.1 w₀.2 w.1 w.2 hle
          have hne : w₀.1 ≠ w.1 := fun e => hw (Subtype.ext e).symm
          simp [A, Matrix.sub_apply, hne, hM0]
      · simp
    rw [this] at hrow
    exact (Finset.mem_filter.1 hw₀).2 hrow
  have hA : A.rank = U.card := by
    rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_coe]
  rw [← hA]
  exact Matrix.rank_submatrix_le _ _ _

/-- `parity-barrier.md` Theorem 1, for an arbitrary distance `dist` on the labels: if
`φ x − φ y ≤ dist x y` and `M[u,w] ≠ 0 ⇒ dist(d_u, a_w) < R` (T2), then
`rank(1 − M) ≥ #{u : φ(d_u) − φ(a_u) ≥ R}`. -/
theorem triangular_rank_bound {Lab : Type*} (dist : Lab → Lab → ℝ) (a d : B → Lab)
    (φ : Lab → ℝ) (hφ : ∀ x y, φ x - φ y ≤ dist x y) (R : ℝ) (M : Matrix B B K)
    (hM : ∀ u w, M u w ≠ 0 → dist (d u) (a w) < R) :
    (univ.filter fun u => R ≤ φ (d u) - φ (a u)).card ≤ (1 - M).rank := by
  refine card_le_rank_one_sub_of_triangular M _ (fun u => φ (a u)) ?_
  intro u hu w _ hle
  by_contra hne
  have h1 := hM u w hne
  have h2 := (Finset.mem_filter.1 hu).2
  have h3 := hφ (d u) (a w)
  linarith

/-- `parity-barrier.md` Theorem 1 verbatim: labels in `[r]^Q`, Hamming distance, (T2) in the
form `M[u,w] ≠ 0 ⇒ d_H(d_u, a_w) ≤ R − 1`, `φ` 1-Lipschitz for the Hamming metric. -/
theorem triangular_rank_bound_hamming {Q r : ℕ} (a d : B → (Fin Q → Fin r))
    (φ : (Fin Q → Fin r) → ℝ) (hφ : ∀ x y, |φ x - φ y| ≤ hammingDist x y) (R : ℕ)
    (M : Matrix B B K) (hM : ∀ u w, M u w ≠ 0 → hammingDist (d u) (a w) + 1 ≤ R) :
    (univ.filter fun u => (R : ℝ) ≤ φ (d u) - φ (a u)).card ≤ (1 - M).rank := by
  refine triangular_rank_bound (fun x y => (hammingDist x y : ℝ)) a d φ
    (fun x y => (le_abs_self _).trans (hφ x y)) R M (fun u w hne => ?_)
  have := hM u w hne
  have : (hammingDist (d u) (a w) : ℝ) + 1 ≤ R := by exact_mod_cast this
  linarith

/-- The special case (independent sets): if `dist(x, y) ≥ R` for all `x ∈ A`, `y ∈ B'`, then
`rank(1 − M) ≥ #{u : d_u ∈ A, a_u ∈ B'}` (there `(1 − M)[U,U] = I_U`). -/
theorem independent_sets_rank_bound {Lab : Type*} (dist : Lab → Lab → ℝ) (a d : B → Lab)
    (A B' : Set Lab) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B')] (R : ℝ)
    (hAB : ∀ x ∈ A, ∀ y ∈ B', R ≤ dist x y) (M : Matrix B B K)
    (hM : ∀ u w, M u w ≠ 0 → dist (d u) (a w) < R) :
    (univ.filter fun u => d u ∈ A ∧ a u ∈ B').card ≤ (1 - M).rank := by
  refine card_le_rank_one_sub_of_triangular M _ (fun _ => 0) ?_
  intro u hu w hw _
  by_contra hne
  have h1 := hM u w hne
  have h2 := hAB _ (Finset.mem_filter.1 hu).2.1 _ (Finset.mem_filter.1 hw).2.2
  linarith

end EthFollowup.Barriers.Triangular
