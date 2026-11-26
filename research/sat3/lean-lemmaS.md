# Lemma S in Lean: the metric core (attain-notes §5.3, notes.md Prop. 3.1)

Files: `research/ports/lean/PortsLean/Bimedian.lean` and `research/ports/lean/PortsLean/LemmaS.lean`. Both are
imported from `PortsLean.lean`. `lake build` succeeds (18288 jobs, Mathlib taken from the cache, not rebuilt).
There is no `sorry`, no new axiom and no `native_decide`. Every theorem below prints
`[propext, Classical.choice, Quot.sound]` under `#print axioms`.

The setting follows `FivePoint.lean`: an arbitrary `PseudoMetricSpace X` with no CAT(0) class. A point
"γ_t(x,y)" enters only through instances of the weighted CN inequality against named test points.

## Statements (verbatim)

```lean
def CN (t : ℝ) (x y m z : X) : Prop :=
  dist z m ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2

theorem cn_of_cmp {u1 u2 v : X} {c : ℝ → X} (h : PortsLean.FivePoint.CMP u1 u2 c v)
    (hD : 0 < dist u1 u2) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    CN t u1 u2 (c (t * dist u1 u2)) v

theorem bimedian_weighted {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {o w o' w' βx βv βy βu : X}
    (hv_o : CN t o' w' βv o) (hv_w : CN t o' w' βv w) (hx_v : CN t o w βx βv)
    (hu_o : CN t o' w βu o) (hu_w' : CN t o' w βu w') (hy_u : CN t o w' βy βu) :
    dist βx βv ^ 2 + dist βy βu ^ 2
      ≤ 2 * (1 - t) ^ 2 * dist o o' ^ 2 + 2 * t ^ 2 * dist w w' ^ 2

theorem bimedian_half {o w o' w' βx βv βy βu : X}
    (hv_o : CN (1/2) o' w' βv o) (hv_w : CN (1/2) o' w' βv w) (hx_v : CN (1/2) o w βx βv)
    (hu_o : CN (1/2) o' w βu o) (hu_w' : CN (1/2) o' w βu w') (hy_u : CN (1/2) o w' βy βu) :
    dist βx βv ^ 2 + dist βy βu ^ 2 ≤ (dist o o' ^ 2 + dist w w' ^ 2) / 2

theorem dist_interp_common {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {p a b ma mb : X}
    (ha_p : CN t p a ma p) (ha_b : CN t p a ma b) (hb_a : CN t p b mb ma) :
    dist ma mb ≤ t * dist a b

theorem dist_interp_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {x1 x2 y1 y2 xt yt m : X}
    (hx_x1 : CN t x1 x2 xt x1) (hx_y2 : CN t x1 x2 xt y2) (hm_x : CN t x1 y2 m xt)
    (hm_y2 : CN t x1 y2 m y2) (hm_y1 : CN t x1 y2 m y1) (hy_m : CN t y1 y2 yt m) :
    dist xt yt ≤ (1 - t) * dist x1 y1 + t * dist x2 y2

def IsCNInterp (γ : ℝ → X → X → X) : Prop :=
  ∀ t, 0 ≤ t → t ≤ 1 → ∀ x y z : X, CN t x y (γ t x y) z
-- bimedian_of_interp, geoConvex_of_interp: the two results above for such a γ

-- inner product spaces, lerp t x y = (1 - t) • x + t • y
theorem cn_inner_eq (t : ℝ) (x y z : E) :
    dist z (lerp t x y) ^ 2
      = (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2
theorem isCNInterp_inner : IsCNInterp (lerp : ℝ → E → E → E)
theorem bimedian_inner_eq (t : ℝ) (o w o' w' : E) :
    dist (lerp t o w) (lerp t o' w') ^ 2 + dist (lerp t o w') (lerp t o' w) ^ 2
      = 2 * (1 - t) ^ 2 * dist o o' ^ 2 + 2 * t ^ 2 * dist w w' ^ 2
```

```lean
def Nc (v rest p q : ℝ) (a b c d o o' : X) : ℝ :=
  v - rest - (p * dist a o + q * dist b o + p * dist c o' + q * dist d o')
def Nb (v rest p q : ℝ) (a b c d w w' : X) : ℝ :=
  v - rest - (p * dist a w + q * dist d w + q * dist b w' + p * dist c w')

theorem Nc_le {v rest p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {a b c d o o' : X}
    (h_parent : v ≤ rest + p * dist a c + q * dist b d) :
    Nc v rest p q a b c d o o' ≤ (p + q) * dist o o'          -- also Nb_le
theorem Nc_nonpos_of_dist_eq_zero {v rest p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {a b c d o o' : X}
    (h_parent : v ≤ rest + p * dist a c + q * dist b d) (h0 : dist o o' = 0) :
    Nc v rest p q a b c d o o' ≤ 0                             -- also Nb_nonpos_of_dist_eq_zero

theorem lemmaS_core {p q v a₁ a₂ rest1 rest2 restT t : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ha1 : 0 ≤ a₁) (ha2 : 0 ≤ a₂) (_ha : a₁ ≠ 0 ∨ a₂ ≠ 0)
    {a1 b1 c1 d1 o o' a2 b2 c2 d2 w w' aT bT cT dT βx βv βy βu : X}
    (_hD1 : 0 < dist o o') (_hD2 : 0 < dist w w')
    (ht : t = a₂ / dist w w' / (a₁ / dist o o' + a₂ / dist w w'))
    (h_rest : restT ≤ (1 - t) * rest1 + t * rest2)
    (h_parent : v ≤ restT + p * dist aT cT + q * dist bT dT)
    (hca : dist aT βx ≤ (1 - t) * dist a1 o + t * dist a2 w)
    (hcb : dist bT βy ≤ (1 - t) * dist b1 o + t * dist b2 w')
    (hcc : dist cT βv ≤ (1 - t) * dist c1 o' + t * dist c2 w')
    (hcd : dist dT βu ≤ (1 - t) * dist d1 o' + t * dist d2 w)
    (h_bim : dist βx βv ^ 2 + dist βy βu ^ 2
      ≤ 2 * (1 - t) ^ 2 * dist o o' ^ 2 + 2 * t ^ 2 * dist w w' ^ 2) :
    a₁ * Nc v rest1 p q a1 b1 c1 d1 o o' / dist o o'
      + a₂ * Nb v rest2 p q a2 b2 c2 d2 w w' / dist w w'
      ≤ √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2)
-- lemmaS_core' : the same without _ha, _hD1, _hD2

theorem lemmaS_interp {γ : ℝ → X → X → X} (hγ : IsCNInterp γ)
    {p q v a₁ a₂ rest1 rest2 restT : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ha1 : 0 ≤ a₁) (ha2 : 0 ≤ a₂)
    (a1 b1 c1 d1 o o' a2 b2 c2 d2 w w' : X)
    (h_rest : let t := a₂ / dist w w' / (a₁ / dist o o' + a₂ / dist w w')
      restT ≤ (1 - t) * rest1 + t * rest2)
    (h_parent : let t := a₂ / dist w w' / (a₁ / dist o o' + a₂ / dist w w')
      v ≤ restT + p * dist (γ t a1 a2) (γ t c1 c2) + q * dist (γ t b1 b2) (γ t d1 d2)) :
    a₁ * Nc v rest1 p q a1 b1 c1 d1 o o' / dist o o'
      + a₂ * Nb v rest2 p q a2 b2 c2 d2 w w' / dist w w'
      ≤ √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2)
-- lemmaS_inner : the same in a real inner product space with γ = lerp (no hγ)

theorem circle_of_linear {p q rc rb : ℝ} (hc : 0 ≤ rc) (hb : 0 ≤ rb)
    (h : ∀ a₁ a₂ : ℝ, 0 ≤ a₁ → 0 ≤ a₂ →
      a₁ * rc + a₂ * rb ≤ √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2)) :
    rc ^ 2 + rb ^ 2 ≤ 2 * (p ^ 2 + q ^ 2)

theorem circle_of_sSup {p q : ℝ} {Rc Rb : Set ℝ} (hc : Rc.Nonempty) (hb : Rb.Nonempty)
    (h : ∀ x ∈ Rc, ∀ y ∈ Rb, ∀ a₁ a₂ : ℝ, 0 ≤ a₁ → 0 ≤ a₂ →
      a₁ * x + a₂ * y ≤ √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2)) :
    (max 0 (sSup Rc)) ^ 2 + (max 0 (sSup Rb)) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2)
```

## Hypotheses and proved results

- **Prop. 3.1, weighted.** Proved from six (CN_t) instances: β_v against o and w, β_x against β_v, β_u against o
  and w′, β_y against β_u. The symmetric choice (β_x against o′, w′ and so on) works as well. Six is the number the
  paper proof uses, three for each bimedian. In an inner product space the inequality is an **equality** for every
  real t (`bimedian_inner_eq`).
- **Convexity of the metric (step (iii), and step (i) for each wire).** This is **proved, not assumed**. It follows
  from six (CN_t) instances, provided the auxiliary point m = γ_t(x₁,y₂) exists. First |γ_t(p,a) γ_t(p,b)| ≤ t|ab|,
  using three instances: (1−t)·t²|pa|² + t·[(1−t)|pb|² + t|ab|² − t(1−t)|pa|²] − t(1−t)|pb|² = t²|ab|². Then the
  same with the parameter reversed, and the triangle inequality through m. So `GeoConvex` did not have to be a
  hypothesis. In `lemmaS_core` the four convexity inequalities are still explicit hypotheses, so that the core
  applies in any space where they hold. `lemmaS_interp` discharges them.
- **Remaining hypotheses** in `lemmaS_interp`:
  - `h_rest` (step (i)). `rest` is abstracted as a real number, so the convexity of the other wires stays a
    hypothesis. Each such wire is an instance of `geoConvex_of_interp`.
  - `h_parent` (step (ii)): the interpolated positions form a parent configuration. This holds when v is the
    parent's Steiner value.
  - `IsCNInterp γ`: (CN_t) against every point, for every t ∈ [0,1]. CAT(0) gives this with γ the geodesic.
    Mathlib has no CAT(0) class. `cn_of_cmp` derives the instances from the project's arclength `CMP`.
- **Lemma S core.** Proved. `lemmaS_inner` is the fully discharged instance (non-vacuity check) in every real inner
  product space.
- **Bound r ≤ p+q, and the degenerate case.** `Nc_le` and `Nb_le` give N ≤ (p+q)|hub hub′|. Coincident hubs give
  N ≤ 0. Both need `h_parent` for the child's own positions, which the paper uses implicitly in
  "N₁ ≤ p|a¹c¹| + q|b¹d¹| − (…)".
- **Corollary.** `circle_of_linear` is the version stated in the brief. `circle_of_sSup` is the paper's version with
  suprema: r_c = max(0, sup of N₁/|oo′|), "negative suprema replaced by 0". It needs only non-emptiness. The
  hypothesis itself bounds the sets.

## Where the formal statement differs from the informal one

1. In Lean, (a₁,a₂) ≠ 0, |oo′| > 0 and |ww′| > 0 are **not needed** (`lemmaS_core'`), because Lean defines x/0 = 0.
   If λ₁ = λ₂ = 0 the left-hand side is 0. If |oo′| = 0, then λ₁ = 0 and only (λ₁|oo′|)² ≤ a₁² is used. The version
   with the informal hypotheses (`lemmaS_core`) carries them unused. The informal content is the D > 0 case only.
2. The hypotheses p, q ≥ 0 are used: they multiply the convexity and triangle inequalities. a₁, a₂ ≥ 0 are used:
   they keep Λ ≥ 0 and t ∈ [0,1]. v ≥ 0 is not used.
3. Weighted (CN_t) for general t is stronger than the midpoint CN of `Hull.lean`'s `CNProp`. In CAT(0) both hold.
   In the project's pseudometric style it is a separate hypothesis family.
4. Not formalised: the identification r_c = sup N₁/|oo′|, i.e. "the least bond for which the child value is
   ≥ v(W)". This involves the Steiner value as an infimum over positions. Also not formalised: the reduction of
   `h_rest` to wire-by-wire convexity.

## Paper proof steps that did not go through as written

None. Every step of §5.3 (i)–(iv), the algebra λ₁N₁ + λ₂N₂ = Λ[(1−t)N₁ + tN₂], Cauchy–Schwarz,
Λ²·(2(1−t)²|oo′|² + 2t²|ww′|²) = 2(a₁² + a₂²), and the proof of Prop. 3.1 (the brackets cancel) checked
as written. The only gap is the implicit use of `h_parent` for the child itself in r_c ≤ p+q (above).
