/-
Exploratory file (`research/next/v3`).  Not imported by the root module and not a claimed result.

A *book* is three flat half-planes ("pages") glued along a line (the "spine") so that every two pages form a
flat plane; it is `tripod × line`.  Here: the only two steps of the argument
"a price geometry that contains a book forces `ω ≥ 3/√2`" that are not quoted from the literature.

Inputs quoted (OpenAI, `Euclidean geometry in the asymptotic spectrum of tensors`, 24 Nov 2026): the shared-label
rate `δ` is monotone and submodular on intersecting sets; on a convex Euclidean piece it is the mean width
(half the perimeter in a plane); and, for any three sites, `perimeter ≤ ω · δ` because the triangle of three
binary wires is the `2 × 2` matrix multiplication tensor.
-/
import EthFollowup.Spectral.DiagRate

namespace EthFollowup.Spectral

namespace DiagRate

variable {S : Type*} [DecidableEq S] (R : DiagRate S)

/-- **Book bound.**  For tips `p, q, r` and any finite set `s` of further sites,
`δ {p,q,r} ≤ δ ({p,q} ∪ s) + δ ({q,r} ∪ s) - δ ({q} ∪ s)`.
When `s` lies on the spine, the three sets on the right lie in flat planes. -/
theorem book_bound (p q r : S) (s : Finset S) :
    R.δ {p, q, r} ≤
      R.δ (insert p (insert q s)) + R.δ (insert q (insert r s)) - R.δ (insert q s) := by
  have hI : ((insert p (insert q s)) ∩ (insert q (insert r s))).Nonempty :=
    ⟨q, by simp⟩
  have h1 := R.submod hI
  have h2 : R.δ {p, q, r} ≤ R.δ ((insert p (insert q s)) ∪ (insert q (insert r s))) :=
    R.mono ⟨p, by simp⟩ (by
      intro x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto)
  have h3 : R.δ (insert q s) ≤ R.δ ((insert p (insert q s)) ∩ (insert q (insert r s))) :=
    R.mono ⟨q, by simp⟩ (by
      intro x
      simp only [Finset.mem_inter, Finset.mem_insert]
      tauto)
  linarith

/-- Tips at distance 1 from the spine and two spine sites `u, d` at heights `± 1/√8`.  In the plane of two
pages the sites `p, q, u, d` are the corners of a rhombus with half-diagonals `1` and `1/√8`, of half-perimeter
`2 · 3/√8 = 3√2/2`; the sites `q, u, d` form a triangle of half-perimeter `3/√8 + 1/√8 = √2`.
Hence `δ {p,q,r} ≤ 2√2`. -/
theorem book_two_spine_sites (p q r u d : S) {w : ℝ}
    (hpq : R.δ (insert p (insert q {u, d})) = 3 * w / 2)
    (hqr : R.δ (insert q (insert r {u, d})) = 3 * w / 2)
    (hq : R.δ (insert q {u, d}) = w) :
    R.δ {p, q, r} ≤ 2 * w := by
  have h := R.book_bound p q r {u, d}
  rw [hpq, hqr, hq] at h
  linarith

end DiagRate

/-- If three sites have perimeter `6`, shared-label rate at most `2√2`, and `perimeter ≤ ω · δ`,
then `ω ≥ 3/√2`, that is `ω² ≥ 9/2`. -/
theorem omega_sq_ge_of_book {ω δ₃ : ℝ} (hω : 0 ≤ ω) (hper : 6 ≤ ω * δ₃) (hδ : δ₃ ≤ 2 * Real.sqrt 2) :
    9 / 2 ≤ ω ^ 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h1 : 3 ≤ ω * Real.sqrt 2 := by nlinarith [mul_le_mul_of_nonneg_left hδ hω]
  nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 3) h1]

/-- The same with a general upper bound `U` for the rate: `ω ≥ 6 / U`. -/
theorem omega_ge_of_rate_bound {ω δ₃ U : ℝ} (hω : 0 ≤ ω) (hU : 0 < U) (hper : 6 ≤ ω * δ₃) (hδ : δ₃ ≤ U) :
    6 / U ≤ ω := by
  rw [div_le_iff₀ hU]
  nlinarith [mul_le_mul_of_nonneg_left hδ hω]

end EthFollowup.Spectral
