import Mathlib
import PortsLean.FivePoint

/-!
# The weighted two-bimedian inequality and convexity of the metric, from (CN_t) instances

Source: `research/sat3/attain-notes.md` §5.3 (Lemma S, steps (i), (iii) and the last inequality of
the chain) and `research/sat3/notes.md` Prop. 3.1 (two bimedians, `t = 1/2` and general `t`).

Setting, in the style of `PortsLean/FivePoint.lean`: a pseudometric space `X`, no CAT(0) class.
A point `m` "at fraction `t` on a geodesic from `x` to `y`" enters only through instances of the
weighted CN inequality against named test points `z`:

  (CN_t)  `|z m|² ≤ (1−t)|z x|² + t|z y|² − t(1−t)|x y|²`   (`CN t x y m z`).

In a CAT(0) space every point of a geodesic satisfies (CN_t) against every `z` (BH II.1.9 / the
note's C.4(a)); `cn_of_cmp` derives (CN_t) from the project's arclength comparison `CMP`.

Contents:
* `CN`, `CN.symm` (reversal `t ↦ 1−t`), `cn_of_cmp` (bridge from `FivePoint.CMP`);
* `bimedian_weighted` (**weighted two-bimedian inequality**, six CN instances) and
  `bimedian_half` (`t = 1/2`, notes.md Prop. 3.1);
* `dist_interp_common` (common start point, three CN instances) and
  `dist_interp_le` (**convexity of the metric along two geodesics**, six CN instances and one
  auxiliary point `m = γ_t(x₁,y₂)`): this part did *not* have to be assumed;
* `IsCNInterp γ` (a global interpolation map satisfying (CN_t) against every point) and the
  corresponding corollaries `bimedian_of_interp`, `geoConvex_of_interp`;
* inner product spaces: `cn_inner_eq` ((CN_t) is an equality for `γ_t(x,y) = (1−t)•x + t•y`),
  `isCNInterp_inner`, `bimedian_inner_eq` (the bimedian inequality is an equality there).
-/

namespace PortsLean.Bimedian

open Real

variable {X : Type*} [PseudoMetricSpace X]

/-- The weighted CN inequality (CN_t) for the point `m` (meant to be `γ_t(x,y)`) against the test
point `z`: `|z m|² ≤ (1−t)|z x|² + t|z y|² − t(1−t)|x y|²`. -/
def CN (t : ℝ) (x y m z : X) : Prop :=
  dist z m ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2

/-- Reversing the geodesic: (CN_t) for `(x, y)` is (CN_{1−t}) for `(y, x)`. -/
lemma CN.symm {t : ℝ} {x y m z : X} (h : CN t x y m z) : CN (1 - t) y x m z := by
  unfold CN at *; rw [dist_comm y x]; linarith

/-- Bridge from the project's arclength comparison hypothesis: if `CMP u₁ u₂ c v` and
`|u₁u₂| > 0`, then the point `c(t·|u₁u₂|)` satisfies (CN_t) against `v`, for `t ∈ [0,1]`. -/
theorem cn_of_cmp {u1 u2 v : X} {c : ℝ → X} (h : PortsLean.FivePoint.CMP u1 u2 c v)
    (hD : 0 < dist u1 u2) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    CN t u1 u2 (c (t * dist u1 u2)) v := by
  have := h (t * dist u1 u2) (by positivity) (by nlinarith)
  have e : t * dist u1 u2 / dist u1 u2 = t := by field_simp
  rw [e] at this
  unfold CN
  have : t * dist u1 u2 * (dist u1 u2 - t * dist u1 u2) = t * (1 - t) * dist u1 u2 ^ 2 := by ring
  linarith

/-- **Weighted two-bimedian inequality** (attain-notes §5.3; notes.md Prop. 3.1 for general `t`).

Let `t ∈ [0,1]` and `β_x = γ_t(o,w)`, `β_v = γ_t(o′,w′)`, `β_y = γ_t(o,w′)`, `β_u = γ_t(o′,w)`, where
each point enters only through the following six instances of (CN_t):
`β_v` against `o` and `w`; `β_x` against `β_v`; `β_u` against `o` and `w′`; `β_y` against `β_u`.
Then `|β_xβ_v|² + |β_yβ_u|² ≤ 2(1−t)²|oo′|² + 2t²|ww′|²`. -/
theorem bimedian_weighted {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {o w o' w' βx βv βy βu : X}
    (hv_o : CN t o' w' βv o) (hv_w : CN t o' w' βv w) (hx_v : CN t o w βx βv)
    (hu_o : CN t o' w βu o) (hu_w' : CN t o' w βu w') (hy_u : CN t o w' βy βu) :
    dist βx βv ^ 2 + dist βy βu ^ 2
      ≤ 2 * (1 - t) ^ 2 * dist o o' ^ 2 + 2 * t ^ 2 * dist w w' ^ 2 := by
  unfold CN at *
  have e1 := mul_le_mul_of_nonneg_left hv_o (by linarith : (0:ℝ) ≤ 1 - t)
  have e2 := mul_le_mul_of_nonneg_left hv_w ht0
  have e3 := mul_le_mul_of_nonneg_left hu_o (by linarith : (0:ℝ) ≤ 1 - t)
  have e4 := mul_le_mul_of_nonneg_left hu_w' ht0
  rw [dist_comm βv βx] at hx_v
  rw [dist_comm βu βy] at hy_u
  rw [dist_comm βv o, dist_comm βv w] at hx_v
  rw [dist_comm βu o, dist_comm βu w'] at hy_u
  rw [dist_comm w o'] at e2
  rw [dist_comm w' o', dist_comm w' w] at e4
  linarith

/-- **Two bimedians** (notes.md Prop. 3.1, `t = 1/2`): the squared bimedians of the quadrilateral
`o, w, o′, w′` add up to at most half the sum of the squared diagonals `|oo′|², |ww′|²`. -/
theorem bimedian_half {o w o' w' βx βv βy βu : X}
    (hv_o : CN (1/2) o' w' βv o) (hv_w : CN (1/2) o' w' βv w) (hx_v : CN (1/2) o w βx βv)
    (hu_o : CN (1/2) o' w βu o) (hu_w' : CN (1/2) o' w βu w') (hy_u : CN (1/2) o w' βy βu) :
    dist βx βv ^ 2 + dist βy βu ^ 2 ≤ (dist o o' ^ 2 + dist w w' ^ 2) / 2 := by
  have := bimedian_weighted (by norm_num) (by norm_num) hv_o hv_w hx_v hu_o hu_w' hy_u
  linarith

/-- **Common start point.** If `m_a = γ_t(p,a)`, `m_b = γ_t(p,b)` with the three instances
(CN_t) of `m_a` against `p` and `b`, and of `m_b` against `m_a`, then `|m_a m_b| ≤ t|ab|`. -/
theorem dist_interp_common {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {p a b ma mb : X}
    (ha_p : CN t p a ma p) (ha_b : CN t p a ma b) (hb_a : CN t p b mb ma) :
    dist ma mb ≤ t * dist a b := by
  unfold CN at *
  rw [dist_self] at ha_p
  rw [dist_comm ma p] at hb_a
  rw [dist_comm b p, dist_comm b a, dist_comm b ma] at ha_b
  have e1 := mul_le_mul_of_nonneg_left ha_p (by linarith : (0:ℝ) ≤ 1 - t)
  have e2 := mul_le_mul_of_nonneg_left ha_b ht0
  have key : dist ma mb ^ 2 ≤ (t * dist a b) ^ 2 := by linarith
  have h0 : 0 ≤ t * dist a b := mul_nonneg ht0 dist_nonneg
  nlinarith [dist_nonneg (x := ma) (y := mb)]

/-- **Convexity of the metric along two geodesics**, derived from (CN_t) instances.

Let `x_t = γ_t(x₁,x₂)`, `y_t = γ_t(y₁,y₂)` and the auxiliary point `m = γ_t(x₁,y₂)`, entering only
through six instances of (CN_t): `x_t` against `x₁`, `y₂`; `m` against `x_t`, `y₂`, `y₁`; `y_t`
against `m`. Then `|x_t y_t| ≤ (1−t)|x₁y₁| + t|x₂y₂|`. (Proof: `|x_t m| ≤ t|x₂y₂|` and
`|m y_t| ≤ (1−t)|x₁y₁|` by `dist_interp_common`, then the triangle inequality.) -/
theorem dist_interp_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {x1 x2 y1 y2 xt yt m : X}
    (hx_x1 : CN t x1 x2 xt x1) (hx_y2 : CN t x1 x2 xt y2) (hm_x : CN t x1 y2 m xt)
    (hm_y2 : CN t x1 y2 m y2) (hm_y1 : CN t x1 y2 m y1) (hy_m : CN t y1 y2 yt m) :
    dist xt yt ≤ (1 - t) * dist x1 y1 + t * dist x2 y2 := by
  have hA := dist_interp_common ht0 ht1 hx_x1 hx_y2 hm_x
  have hB := dist_interp_common (t := 1 - t) (by linarith) (by linarith)
    hm_y2.symm hm_y1.symm hy_m.symm
  have := dist_triangle xt m yt
  linarith

/-- A global interpolation map `γ` satisfying (CN_t) against every point, for every `t ∈ [0,1]`.
Every CAT(0) space has one (the geodesic map); `isCNInterp_inner` gives it for inner product
spaces. (Mathlib has no CAT(0) class, so this is the most one can say here.) -/
def IsCNInterp (γ : ℝ → X → X → X) : Prop :=
  ∀ t, 0 ≤ t → t ≤ 1 → ∀ x y z : X, CN t x y (γ t x y) z

/-- The weighted two-bimedian inequality for a global (CN_t) interpolation map. -/
theorem bimedian_of_interp {γ : ℝ → X → X → X} (hγ : IsCNInterp γ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (o w o' w' : X) :
    dist (γ t o w) (γ t o' w') ^ 2 + dist (γ t o w') (γ t o' w) ^ 2
      ≤ 2 * (1 - t) ^ 2 * dist o o' ^ 2 + 2 * t ^ 2 * dist w w' ^ 2 :=
  bimedian_weighted ht0 ht1 (hγ t ht0 ht1 _ _ _) (hγ t ht0 ht1 _ _ _) (hγ t ht0 ht1 _ _ _)
    (hγ t ht0 ht1 _ _ _) (hγ t ht0 ht1 _ _ _) (hγ t ht0 ht1 _ _ _)

/-- Convexity of the metric for a global (CN_t) interpolation map. -/
theorem geoConvex_of_interp {γ : ℝ → X → X → X} (hγ : IsCNInterp γ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (x1 x2 y1 y2 : X) :
    dist (γ t x1 x2) (γ t y1 y2) ≤ (1 - t) * dist x1 y1 + t * dist x2 y2 :=
  dist_interp_le (m := γ t x1 y2) ht0 ht1 (hγ t ht0 ht1 _ _ _) (hγ t ht0 ht1 _ _ _)
    (hγ t ht0 ht1 _ _ _) (hγ t ht0 ht1 _ _ _) (hγ t ht0 ht1 _ _ _) (hγ t ht0 ht1 _ _ _)

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine interpolation `γ_t(x,y) = (1−t)•x + t•y` of a real inner product space. -/
def lerp (t : ℝ) (x y : E) : E := (1 - t) • x + t • y

/-- In a real inner product space (CN_t) is an **equality** for `γ_t(x,y) = (1−t)•x + t•y`, for every
real `t` (no range restriction). -/
theorem cn_inner_eq (t : ℝ) (x y z : E) :
    dist z (lerp t x y) ^ 2
      = (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2 := by
  simp only [dist_eq_norm, lerp]
  have e1 : z - ((1 - t) • x + t • y) = (z - x) - t • (y - x) := by
    rw [sub_smul, one_smul, smul_sub]; abel
  have e2 : z - y = (z - x) - (y - x) := by abel
  rw [e1, e2, PortsLean.FivePoint.interp_id, norm_sub_rev x y]

theorem isCNInterp_inner : IsCNInterp (lerp : ℝ → E → E → E) := by
  intro t _ _ x y z
  unfold CN; rw [cn_inner_eq]

/-- In a real inner product space the weighted two-bimedian inequality is an **equality**
(for every real `t`). -/
theorem bimedian_inner_eq (t : ℝ) (o w o' w' : E) :
    dist (lerp t o w) (lerp t o' w') ^ 2 + dist (lerp t o w') (lerp t o' w) ^ 2
      = 2 * (1 - t) ^ 2 * dist o o' ^ 2 + 2 * t ^ 2 * dist w w' ^ 2 := by
  have hx_v := cn_inner_eq t o w (lerp t o' w')
  have hv_o := cn_inner_eq t o' w' o
  have hv_w := cn_inner_eq t o' w' w
  have hy_u := cn_inner_eq t o w' (lerp t o' w)
  have hu_o := cn_inner_eq t o' w o
  have hu_w' := cn_inner_eq t o' w w'
  rw [dist_comm (lerp t o' w') (lerp t o w), dist_comm (lerp t o' w') o,
    dist_comm (lerp t o' w') w] at hx_v
  rw [dist_comm (lerp t o' w) (lerp t o w'), dist_comm (lerp t o' w) o,
    dist_comm (lerp t o' w) w'] at hy_u
  rw [dist_comm w o'] at hv_w
  rw [dist_comm w' o', dist_comm w' w] at hu_w'
  rw [hx_v, hy_u, hv_o, hv_w, hu_o, hu_w']
  ring

/-- Convexity of the metric along two segments in a real inner product space. -/
theorem geoConvex_inner {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x1 x2 y1 y2 : E) :
    dist (lerp t x1 x2) (lerp t y1 y2) ≤ (1 - t) * dist x1 y1 + t * dist x2 y2 :=
  geoConvex_of_interp isCNInterp_inner ht0 ht1 x1 x2 y1 y2

end Inner

end PortsLean.Bimedian
