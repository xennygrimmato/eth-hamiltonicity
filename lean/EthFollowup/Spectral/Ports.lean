/-
Exploratory file (24–26 Nov 2026 round, `research/next/v2`).  Not imported by the root module and not a
claimed result in the sense of the top-level README.

Subject: the "ports" question of OpenAI's `Circuit lower bounds for Hamiltonian cycle and the permanent`
(24 Nov 2026).  A class of metric spaces admits ports when bounded-degree graphs of unbounded order satisfy a
uniform Poincaré inequality for squared distances under every placement of their vertices in a space of the
class.  Here we record, for a finite vertex set, the elementary transfer principle:

  a Poincaré inequality for Euclidean placements passes to any geometry that maps to Euclidean space by a
  1-Lipschitz map losing at most a constant factor in the *mean* squared distance.

Consequences proved below: stars (cones over finitely many points) lose a factor 2, and a Euclidean cone loses
exactly the factor by which a positive-definite kernel on its link approximates the truncated cosine.
-/
import Mathlib

namespace EthFollowup.Spectral

open Finset BigOperators

variable {V : Type*} [Fintype V]

/-- Poincaré inequality with constant `γ` for a table `q` of squared distances and nonnegative edge weights `G`:
`(1/|V|²) ∑ q ≤ γ · (1/|V|) ∑ G q`, written without divisions. -/
def Poincare (G : V → V → ℝ) (γ : ℝ) (q : V → V → ℝ) : Prop :=
  ∑ i, ∑ j, q i j ≤ γ * (Fintype.card V : ℝ) * ∑ i, ∑ j, G i j * q i j

/-- **Transfer by average distortion.**  If `e ≤ q` entrywise (the comparison map is 1-Lipschitz) and
`∑ q ≤ D · ∑ e` (it keeps the mean squared distance up to `D`), then a Poincaré inequality for `e` gives one
for `q` with constant `γ · D`. -/
theorem Poincare.of_avgDistortion {G : V → V → ℝ} {γ D : ℝ} {q e : V → V → ℝ}
    (hG : ∀ i j, 0 ≤ G i j) (hγ : 0 ≤ γ) (hD : 0 ≤ D)
    (hle : ∀ i j, e i j ≤ q i j) (havg : ∑ i, ∑ j, q i j ≤ D * ∑ i, ∑ j, e i j)
    (he : Poincare G γ e) : Poincare G (γ * D) q := by
  unfold Poincare at *
  have hmono : ∑ i, ∑ j, G i j * e i j ≤ ∑ i, ∑ j, G i j * q i j :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hle i j) (hG i j)
  have hcard : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  calc ∑ i, ∑ j, q i j ≤ D * ∑ i, ∑ j, e i j := havg
    _ ≤ D * (γ * (Fintype.card V : ℝ) * ∑ i, ∑ j, G i j * e i j) :=
        mul_le_mul_of_nonneg_left he hD
    _ ≤ D * (γ * (Fintype.card V : ℝ) * ∑ i, ∑ j, G i j * q i j) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmono (mul_nonneg hγ hcard)) hD
    _ = γ * D * (Fintype.card V : ℝ) * ∑ i, ∑ j, G i j * q i j := by ring

/-- Pointwise version: `e ≤ q ≤ D · e` entrywise. -/
theorem Poincare.of_distortion {G : V → V → ℝ} {γ D : ℝ} {q e : V → V → ℝ}
    (hG : ∀ i j, 0 ≤ G i j) (hγ : 0 ≤ γ) (hD : 0 ≤ D)
    (hle : ∀ i j, e i j ≤ q i j) (hge : ∀ i j, q i j ≤ D * e i j)
    (he : Poincare G γ e) : Poincare G (γ * D) q := by
  refine Poincare.of_avgDistortion hG hγ hD hle ?_ he
  calc ∑ i, ∑ j, q i j ≤ ∑ i, ∑ j, D * e i j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hge i j
    _ = D * ∑ i, ∑ j, e i j := by
        simp only [Finset.mul_sum]

/-! ### General comparison inequalities

Both the Poincaré inequality of the ports question and the contracting hypothesis of Anthropic's
`VP ≠ VNP over every field` (mean squared distance at rank `μ` at most `s²` times that at rank one, on
`Mat_μ(𝔽₂)`) compare two nonnegatively weighted sums of squared distances.  Any such inequality passes from a
table `e` to a table `q` with `e ≤ q ≤ D · e` at the cost of the factor `D`. -/

/-- `∑ W q ≤ γ ∑ U q`. -/
def Compare (W U : V → V → ℝ) (γ : ℝ) (q : V → V → ℝ) : Prop :=
  ∑ i, ∑ j, W i j * q i j ≤ γ * ∑ i, ∑ j, U i j * q i j

theorem Compare.of_distortion {W U : V → V → ℝ} {γ D : ℝ} {q e : V → V → ℝ}
    (hW : ∀ i j, 0 ≤ W i j) (hU : ∀ i j, 0 ≤ U i j) (hγ : 0 ≤ γ) (hD : 0 ≤ D)
    (hle : ∀ i j, e i j ≤ q i j) (hge : ∀ i j, q i j ≤ D * e i j)
    (he : Compare W U γ e) : Compare W U (γ * D) q := by
  unfold Compare at *
  have h1 : ∑ i, ∑ j, W i j * q i j ≤ D * ∑ i, ∑ j, W i j * e i j := by
    calc ∑ i, ∑ j, W i j * q i j ≤ ∑ i, ∑ j, D * (W i j * e i j) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            have := mul_le_mul_of_nonneg_left (hge i j) (hW i j); linarith
      _ = D * ∑ i, ∑ j, W i j * e i j := by simp only [Finset.mul_sum]
  have h2 : ∑ i, ∑ j, U i j * e i j ≤ ∑ i, ∑ j, U i j * q i j :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hle i j) (hU i j)
  calc ∑ i, ∑ j, W i j * q i j ≤ D * ∑ i, ∑ j, W i j * e i j := h1
    _ ≤ D * (γ * ∑ i, ∑ j, U i j * e i j) := mul_le_mul_of_nonneg_left he hD
    _ ≤ D * (γ * ∑ i, ∑ j, U i j * q i j) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hγ) hD
    _ = γ * D * ∑ i, ∑ j, U i j * q i j := by ring

/-- The contracting inequality `∑ W q ≤ s² ∑ U q` holds for `q` with `s² · D < μ` as soon as it holds for a
Hilbert comparison table `e` with `e ≤ q ≤ D · e` and constant `sH`, provided `sH · D < μ`. -/
theorem Compare.contracting_of_distortion {W U : V → V → ℝ} {sH D μ : ℝ} {q e : V → V → ℝ}
    (hW : ∀ i j, 0 ≤ W i j) (hU : ∀ i j, 0 ≤ U i j) (hs : 0 ≤ sH) (hD : 0 ≤ D)
    (hle : ∀ i j, e i j ≤ q i j) (hge : ∀ i j, q i j ≤ D * e i j)
    (he : Compare W U sH e) (hμ : sH * D < μ) :
    ∃ s2 : ℝ, s2 < μ ∧ Compare W U s2 q :=
  ⟨sH * D, hμ, Compare.of_distortion hW hU hs hD hle hge he⟩

/-! ### Stars

A star has legs indexed by `ι`; a point is a leg and a radius.  Two points on the same leg are at distance
`|r - s|`, on different legs at distance `r + s`.  Sending `(a, r)` to `r • e_a` is 1-Lipschitz and at most
halves squared distances. -/

/-- Squared distance in a star. -/
def starSq {ι : Type*} [DecidableEq ι] (p q : ι × ℝ) : ℝ :=
  if p.1 = q.1 then (p.2 - q.2) ^ 2 else (p.2 + q.2) ^ 2

/-- Squared distance of the images `r • e_a` in Euclidean space. -/
def spokeSq {ι : Type*} [DecidableEq ι] (p q : ι × ℝ) : ℝ :=
  if p.1 = q.1 then (p.2 - q.2) ^ 2 else p.2 ^ 2 + q.2 ^ 2

theorem spokeSq_le_starSq {ι : Type*} [DecidableEq ι] (p q : ι × ℝ) (hp : 0 ≤ p.2) (hq : 0 ≤ q.2) :
    spokeSq p q ≤ starSq p q := by
  unfold spokeSq starSq
  split_ifs
  · exact le_refl _
  · nlinarith [mul_nonneg hp hq]

theorem starSq_le_two_spokeSq {ι : Type*} [DecidableEq ι] (p q : ι × ℝ) :
    starSq p q ≤ 2 * spokeSq p q := by
  unfold spokeSq starSq
  split_ifs
  · nlinarith [sq_nonneg (p.2 - q.2)]
  · nlinarith [sq_nonneg (p.2 - q.2)]

/-- A graph that satisfies the Poincaré inequality for the spoke (Euclidean) model of every placement in a star
satisfies it for the star itself with twice the constant. -/
theorem Poincare.star {ι : Type*} [DecidableEq ι] {G : V → V → ℝ} {γ : ℝ}
    (hG : ∀ i j, 0 ≤ G i j) (hγ : 0 ≤ γ) (x : V → ι × ℝ) (hx : ∀ i, 0 ≤ (x i).2)
    (he : Poincare G γ fun i j => spokeSq (x i) (x j)) :
    Poincare G (γ * 2) fun i j => starSq (x i) (x j) :=
  Poincare.of_distortion hG hγ (by norm_num)
    (fun i j => spokeSq_le_starSq _ _ (hx i) (hx j)) (fun i j => starSq_le_two_spokeSq _ _) he

/-! ### Euclidean cones

A point of the cone over a link is a radius `r ≥ 0` and a direction.  If `c` is the cosine of the truncated
angle between two directions, the squared distance is `r² + s² - 2 r s c`.  If unit vectors `u, v` in a Hilbert
space have inner product `k`, then `‖r u - s v‖² = r² + s² - 2 r s k`.  So the distortion of the whole cone is
governed by how well `1 - k` approximates `1 - c` on the link. -/

/-- Squared distance from radii and a cosine. -/
def coneSq (r s c : ℝ) : ℝ := r ^ 2 + s ^ 2 - 2 * r * s * c

theorem coneSq_eq (r s c : ℝ) : coneSq r s c = (r - s) ^ 2 + 2 * r * s * (1 - c) := by
  unfold coneSq; ring

/-- If `a (1 - c) ≤ 1 - k ≤ b (1 - c)` with `a ≤ 1 ≤ b`, the two cones agree up to the factors `a`, `b`. -/
theorem coneSq_bounds {r s c k a b : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    (hlo : a * (1 - c) ≤ 1 - k) (hhi : 1 - k ≤ b * (1 - c)) :
    a * coneSq r s c ≤ coneSq r s k ∧ coneSq r s k ≤ b * coneSq r s c := by
  have hrs : 0 ≤ r * s := mul_nonneg hr hs
  rw [coneSq_eq, coneSq_eq]
  constructor
  · nlinarith [sq_nonneg (r - s), mul_le_mul_of_nonneg_left hlo hrs]
  · nlinarith [sq_nonneg (r - s), mul_le_mul_of_nonneg_left hhi hrs]

end EthFollowup.Spectral
