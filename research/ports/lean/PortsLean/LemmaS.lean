import Mathlib
import PortsLean.Bimedian

/-!
# Lemma S (Steiner crossing inequality): the metric core

Source: `research/sat3/attain-notes.md` §5.3 (Lemma S and its proof, steps (i)–(iv) and the final
chain of inequalities), using `notes.md` Prop. 3.1 (formalised in `PortsLean/Bimedian.lean`).

The Steiner problem is abstracted so that no infimum over configurations appears in the core
statement. A *c-child configuration* `Z¹` consists of ends `a¹ b¹ c¹ d¹`, hubs `o o′` and the
length `rest¹` of the other wires; its deficit is
  `N₁ = v − rest¹ − (p|a¹o| + q|b¹o| + p|c¹o′| + q|d¹o′|)`   (`Nc`).
A *b-child configuration* `Z²` has ends `a² b² c² d²`, hubs `w w′`, `rest²`, and deficit
  `N₂ = v − rest² − (p|a²w| + q|d²w| + q|b²w′| + p|c²w′|)`   (`Nb`).
With `λ₁ = a₁/|oo′|`, `λ₂ = a₂/|ww′|`, `t = λ₂/(λ₁+λ₂)` and interpolated points
`aT bT cT dT β_x β_v β_y β_u`, the hypotheses of the paper's steps (i)–(iii) and of Prop. 3.1 give
  `a₁N₁/|oo′| + a₂N₂/|ww′| ≤ √(2(p²+q²))·√(a₁²+a₂²)`.

Contents:
* `Nc`, `Nb` (deficits); `Nc_le`, `Nb_le` (`N ≤ (p+q)·|hub hub′|` from the parent hypothesis for the
  child itself, hence `r_c, r_b ≤ p+q`), `Nc_nonpos_of_dist_eq_zero`, `Nb_nonpos_of_dist_eq_zero`
  (degenerate case: coincident hubs);
* `lemmaS_core'` (no positivity of `|oo′|`, `|ww′|` needed; Lean's `x/0 = 0`), `lemmaS_core`
  (the statement with `|oo′|, |ww′| > 0`), `lemmaS_interp` (all metric hypotheses discharged from a
  global (CN_t) interpolation map: only `h_rest` and `h_parent` remain), `lemmaS_inner`
  (inner product spaces);
* `circle_of_linear` (the corollary `r_c² + r_b² ≤ 2(p²+q²)`), `circle_of_sSup` (the same for the
  suprema `r_c = max(0, sup N₁/|oo′|)`, `r_b = max(0, sup N₂/|ww′|)`).
-/

namespace PortsLean.LemmaS

open Real PortsLean.Bimedian

variable {X : Type*} [PseudoMetricSpace X]

/-- Deficit of a c-child configuration (hubs `o` joining `a, b` and `o′` joining `c, d`):
`N₁ = v − rest − (p|ao| + q|bo| + p|co′| + q|do′|)`. -/
def Nc (v rest p q : ℝ) (a b c d o o' : X) : ℝ :=
  v - rest - (p * dist a o + q * dist b o + p * dist c o' + q * dist d o')

/-- Deficit of a b-child configuration (hubs `w` joining `a, d` and `w′` joining `b, c`):
`N₂ = v − rest − (p|aw| + q|dw| + q|bw′| + p|cw′|)`. -/
def Nb (v rest p q : ℝ) (a b c d w w' : X) : ℝ :=
  v - rest - (p * dist a w + q * dist d w + q * dist b w' + p * dist c w')

/-- A c-child configuration is bounded by its hub distance, provided the same positions form a
parent configuration (`rest + p|ac| + q|bd| ≥ v`, which holds for the Steiner value `v` of the
parent): `N₁ ≤ (p+q)|oo′|`. This gives `r_c ≤ p+q`. -/
theorem Nc_le {v rest p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {a b c d o o' : X}
    (h_parent : v ≤ rest + p * dist a c + q * dist b d) :
    Nc v rest p q a b c d o o' ≤ (p + q) * dist o o' := by
  unfold Nc
  have h1 : dist a c ≤ dist a o + dist o o' + dist c o' := by
    have := dist_triangle4 a o o' c; rw [dist_comm o' c] at this; linarith
  have h2 : dist b d ≤ dist b o + dist o o' + dist d o' := by
    have := dist_triangle4 b o o' d; rw [dist_comm o' d] at this; linarith
  linarith [mul_le_mul_of_nonneg_left h1 hp, mul_le_mul_of_nonneg_left h2 hq]

/-- The b-child analogue: `N₂ ≤ (p+q)|ww′|`. -/
theorem Nb_le {v rest p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {a b c d w w' : X}
    (h_parent : v ≤ rest + p * dist a c + q * dist b d) :
    Nb v rest p q a b c d w w' ≤ (p + q) * dist w w' := by
  unfold Nb
  have h1 : dist a c ≤ dist a w + dist w w' + dist c w' := by
    have := dist_triangle4 a w w' c; rw [dist_comm w' c] at this; linarith
  have h2 : dist b d ≤ dist b w' + dist w w' + dist d w := by
    have := dist_triangle4 b w' w d; rw [dist_comm w d, dist_comm w' w] at this; linarith
  linarith [mul_le_mul_of_nonneg_left h1 hp, mul_le_mul_of_nonneg_left h2 hq]

/-- **Degenerate case** `|oo′| = 0`: a c-child configuration with coincident hubs is a parent
configuration, so `N₁ ≤ 0`. -/
theorem Nc_nonpos_of_dist_eq_zero {v rest p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {a b c d o o' : X}
    (h_parent : v ≤ rest + p * dist a c + q * dist b d) (h0 : dist o o' = 0) :
    Nc v rest p q a b c d o o' ≤ 0 := by
  have := Nc_le (o := o) (o' := o') hp hq h_parent; rw [h0, mul_zero] at this; exact this

/-- **Degenerate case** `|ww′| = 0`: `N₂ ≤ 0`. -/
theorem Nb_nonpos_of_dist_eq_zero {v rest p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {a b c d w w' : X}
    (h_parent : v ≤ rest + p * dist a c + q * dist b d) (h0 : dist w w' = 0) :
    Nb v rest p q a b c d w w' ≤ 0 := by
  have := Nb_le (w := w) (w' := w') hp hq h_parent; rw [h0, mul_zero] at this; exact this

/-- Cauchy–Schwarz in the form used: `pS + qU ≤ √((p²+q²)(S²+U²))`. -/
lemma cs2 (p q S U : ℝ) : p * S + q * U ≤ √((p ^ 2 + q ^ 2) * (S ^ 2 + U ^ 2)) := by
  rcases le_or_gt (p * S + q * U) 0 with h | h
  · exact h.trans (sqrt_nonneg _)
  · apply le_sqrt_of_sq_le
    nlinarith [sq_nonneg (p * U - q * S)]

/-- `(λD)² ≤ a²` for `λ = a/D`, `a ≥ 0`, any `D ≥ 0` (equality if `D > 0`; `λ = 0` if `D = 0`). -/
lemma div_mul_sq_le {a D : ℝ} : (a / D * D) ^ 2 ≤ a ^ 2 := by
  rcases eq_or_ne D 0 with h | h
  · simp [h, sq_nonneg]
  · rw [div_mul_cancel₀ a h]

/-- The real-number part of Lemma S: from `(1−t)N₁ + tN₂ ≤ pS + qU` (steps (i)–(iv)) and
`S² + U² ≤ 2(1−t)²D₁² + 2t²D₂²` (Prop. 3.1), with `t = λ₂/(λ₁+λ₂)`, `λ_i = a_i/D_i`:
`a₁N₁/D₁ + a₂N₂/D₂ ≤ √(2(p²+q²))·√(a₁²+a₂²)`. -/
lemma lemmaS_real {p q a₁ a₂ D1 D2 N1 N2 S U t : ℝ}
    (ha1 : 0 ≤ a₁) (ha2 : 0 ≤ a₂) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (ht : t = a₂ / D2 / (a₁ / D1 + a₂ / D2))
    (K : (1 - t) * N1 + t * N2 ≤ p * S + q * U)
    (h_bim : S ^ 2 + U ^ 2 ≤ 2 * (1 - t) ^ 2 * D1 ^ 2 + 2 * t ^ 2 * D2 ^ 2) :
    a₁ * N1 / D1 + a₂ * N2 / D2 ≤ √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2) := by
  obtain ⟨l1, hl1⟩ : ∃ l, l = a₁ / D1 := ⟨_, rfl⟩
  obtain ⟨l2, hl2⟩ : ∃ l, l = a₂ / D2 := ⟨_, rfl⟩
  have hl1n : 0 ≤ l1 := hl1 ▸ div_nonneg ha1 hD1
  have hl2n : 0 ≤ l2 := hl2 ▸ div_nonneg ha2 hD2
  have hLHS : a₁ * N1 / D1 + a₂ * N2 / D2 = l1 * N1 + l2 * N2 := by
    rw [hl1, hl2]; ring
  rw [hLHS]
  rw [← hl1, ← hl2] at ht
  have hR0 : 0 ≤ √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2) := by positivity
  rcases (show 0 ≤ l1 + l2 by linarith).lt_or_eq with hLp | hL0
  swap
  · have e1 : l1 = 0 := by linarith
    have e2 : l2 = 0 := by linarith
    rw [e1, e2]; simpa using hR0
  -- main case `Λ = λ₁ + λ₂ > 0`
  have htL : (l1 + l2) * t = l2 := by rw [ht]; field_simp
  have htL' : (l1 + l2) * (1 - t) = l1 := by linarith
  set B := 2 * (1 - t) ^ 2 * D1 ^ 2 + 2 * t ^ 2 * D2 ^ 2 with hB
  have CS : p * S + q * U ≤ √((p ^ 2 + q ^ 2) * B) :=
    (cs2 p q S U).trans (sqrt_le_sqrt (mul_le_mul_of_nonneg_left h_bim (by positivity)))
  have hsplit : l1 * N1 + l2 * N2 = (l1 + l2) * ((1 - t) * N1 + t * N2) := by
    linear_combination (-N1) * htL' - N2 * htL
  rw [hsplit]
  have step : (l1 + l2) * ((1 - t) * N1 + t * N2) ≤ (l1 + l2) * √((p ^ 2 + q ^ 2) * B) :=
    mul_le_mul_of_nonneg_left (K.trans CS) hLp.le
  refine step.trans ?_
  -- `Λ·√((p²+q²)B) = √((p²+q²)·Λ²B)` and `Λ²B = 2((λ₁D₁)² + (λ₂D₂)²) ≤ 2(a₁²+a₂²)`
  have hLB : (l1 + l2) ^ 2 * B = 2 * (l1 * D1) ^ 2 + 2 * (l2 * D2) ^ 2 := by
    rw [hB]; linear_combination (2 * D1 ^ 2 * ((l1 + l2) * (1 - t) + l1)) * htL'
      + (2 * D2 ^ 2 * ((l1 + l2) * t + l2)) * htL
  have e1 : (l1 * D1) ^ 2 ≤ a₁ ^ 2 := hl1 ▸ div_mul_sq_le
  have e2 : (l2 * D2) ^ 2 ≤ a₂ ^ 2 := hl2 ▸ div_mul_sq_le
  calc (l1 + l2) * √((p ^ 2 + q ^ 2) * B) = √((p ^ 2 + q ^ 2) * ((l1 + l2) ^ 2 * B)) := by
        rw [show (p ^ 2 + q ^ 2) * ((l1 + l2) ^ 2 * B) = (l1 + l2) ^ 2 * ((p ^ 2 + q ^ 2) * B)
          by ring, sqrt_mul (sq_nonneg _), sqrt_sq hLp.le]
    _ ≤ √((2 * (p ^ 2 + q ^ 2)) * (a₁ ^ 2 + a₂ ^ 2)) := by
        apply sqrt_le_sqrt; rw [hLB]; nlinarith [sq_nonneg p, sq_nonneg q]
    _ = √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2) := sqrt_mul (by positivity) _

/-- **Lemma S, core inequality**, in the form that needs no positivity of the hub distances
(Lean's convention `x/0 = 0` makes the corresponding term vanish; for the informal statement see
`lemmaS_core`).

Data: `p, q ≥ 0`, `a₁, a₂ ≥ 0`; child configurations `(a1,b1,c1,d1,o,o′,rest1)` (c-child) and
`(a2,b2,c2,d2,w,w′,rest2)` (b-child); `t = λ₂/(λ₁+λ₂)` with `λ₁ = a₁/|oo′|`, `λ₂ = a₂/|ww′|`;
interpolated points `aT bT cT dT β_x β_v β_y β_u` and `restT`. Hypotheses:
* `h_rest` (step (i)): `restT ≤ (1−t) rest1 + t rest2`;
* `h_parent` (step (ii)): `restT + p|aT cT| + q|bT dT| ≥ v`;
* `hca … hcd` (step (iii)): `|aT β_x| ≤ (1−t)|a1 o| + t|a2 w|`, `|bT β_y| ≤ (1−t)|b1 o| + t|b2 w′|`,
  `|cT β_v| ≤ (1−t)|c1 o′| + t|c2 w′|`, `|dT β_u| ≤ (1−t)|d1 o′| + t|d2 w|`;
* `h_bim` (Prop. 3.1): `|β_xβ_v|² + |β_yβ_u|² ≤ 2(1−t)²|oo′|² + 2t²|ww′|²`.
Conclusion: `a₁N₁/|oo′| + a₂N₂/|ww′| ≤ √(2(p²+q²))·√(a₁²+a₂²)`. -/
theorem lemmaS_core' {p q v a₁ a₂ rest1 rest2 restT t : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ha1 : 0 ≤ a₁) (ha2 : 0 ≤ a₂)
    {a1 b1 c1 d1 o o' a2 b2 c2 d2 w w' aT bT cT dT βx βv βy βu : X}
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
      ≤ √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2) := by
  apply lemmaS_real ha1 ha2 dist_nonneg dist_nonneg ht _ h_bim
  -- the chain `(1−t)N₁ + tN₂ ≤ p|β_xβ_v| + q|β_yβ_u|` (steps (i)–(iv))
  have tri1 : dist aT cT ≤ dist aT βx + dist βx βv + dist cT βv := by
    have := dist_triangle4 aT βx βv cT; rw [dist_comm βv cT] at this; linarith
  have tri2 : dist bT dT ≤ dist bT βy + dist βy βu + dist dT βu := by
    have := dist_triangle4 bT βy βu dT; rw [dist_comm βu dT] at this; linarith
  unfold Nc Nb
  linarith [mul_le_mul_of_nonneg_left hca hp, mul_le_mul_of_nonneg_left hcb hq,
    mul_le_mul_of_nonneg_left hcc hp, mul_le_mul_of_nonneg_left hcd hq,
    mul_le_mul_of_nonneg_left tri1 hp, mul_le_mul_of_nonneg_left tri2 hq]

/-- **Lemma S, core inequality** (attain-notes §5.3), with the informal hypotheses
`|oo′| > 0`, `|ww′| > 0` and `(a₁, a₂) ≠ 0` (the latter two are not used; see `lemmaS_core'`).
`a₁N₁/|oo′| + a₂N₂/|ww′| ≤ √(2(p²+q²))·√(a₁²+a₂²)`. -/
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
      ≤ √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2) :=
  lemmaS_core' hp hq ha1 ha2 ht h_rest h_parent hca hcb hcc hcd h_bim

/-- `t = λ₂/(λ₁+λ₂) ∈ [0,1]` for `λ₁, λ₂ ≥ 0`. -/
lemma t_mem {l1 l2 : ℝ} (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) :
    0 ≤ l2 / (l1 + l2) ∧ l2 / (l1 + l2) ≤ 1 := by
  refine ⟨div_nonneg h2 (by linarith), ?_⟩
  rcases (show 0 ≤ l1 + l2 by linarith).lt_or_eq with h | h
  · rw [div_le_one h]; linarith
  · rw [← h, div_zero]; norm_num

/-- **Lemma S, core inequality, for a global (CN_t) interpolation map** `γ` (e.g. the geodesic map
of a CAT(0) space): the interpolated points are `aT = γ_t(a1,a2)`, …, `β_x = γ_t(o,w)`,
`β_v = γ_t(o′,w′)`, `β_y = γ_t(o,w′)`, `β_u = γ_t(o′,w)`. Convexity (step (iii)) and Prop. 3.1 are
*proved* from (CN_t); only `h_rest` (step (i), which concerns the other wires) and `h_parent`
(step (ii), the definition of `v`) remain hypotheses. -/
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
      ≤ √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2) := by
  set t := a₂ / dist w w' / (a₁ / dist o o' + a₂ / dist w w') with ht
  obtain ⟨ht0, ht1⟩ := t_mem (div_nonneg ha1 (dist_nonneg (x := o) (y := o')))
    (div_nonneg ha2 (dist_nonneg (x := w) (y := w')))
  exact lemmaS_core' (aT := γ t a1 a2) (bT := γ t b1 b2) (cT := γ t c1 c2) (dT := γ t d1 d2)
    (βx := γ t o w) (βv := γ t o' w') (βy := γ t o w') (βu := γ t o' w)
    hp hq ha1 ha2 ht h_rest h_parent
    (geoConvex_of_interp hγ ht0 ht1 _ _ _ _) (geoConvex_of_interp hγ ht0 ht1 _ _ _ _)
    (geoConvex_of_interp hγ ht0 ht1 _ _ _ _) (geoConvex_of_interp hγ ht0 ht1 _ _ _ _)
    (bimedian_of_interp hγ ht0 ht1 o w o' w')

/-- **Lemma S core in a real inner product space** (non-vacuity check), with
`γ_t(x,y) = (1−t)•x + t•y`. -/
theorem lemmaS_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p q v a₁ a₂ rest1 rest2 restT : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ha1 : 0 ≤ a₁) (ha2 : 0 ≤ a₂)
    (a1 b1 c1 d1 o o' a2 b2 c2 d2 w w' : E)
    (h_rest : let t := a₂ / dist w w' / (a₁ / dist o o' + a₂ / dist w w')
      restT ≤ (1 - t) * rest1 + t * rest2)
    (h_parent : let t := a₂ / dist w w' / (a₁ / dist o o' + a₂ / dist w w')
      v ≤ restT + p * dist (lerp t a1 a2) (lerp t c1 c2) + q * dist (lerp t b1 b2) (lerp t d1 d2)) :
    a₁ * Nc v rest1 p q a1 b1 c1 d1 o o' / dist o o'
      + a₂ * Nb v rest2 p q a2 b2 c2 d2 w w' / dist w w'
      ≤ √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2) :=
  lemmaS_interp isCNInterp_inner hp hq ha1 ha2 _ _ _ _ _ _ _ _ _ _ _ _ h_rest h_parent

/-- **Corollary (the circle).** If `r_c, r_b ≥ 0` and `a₁r_c + a₂r_b ≤ √(2(p²+q²))·√(a₁²+a₂²)`
for all `a₁, a₂ ≥ 0`, then `r_c² + r_b² ≤ 2(p²+q²)`. -/
theorem circle_of_linear {p q rc rb : ℝ} (hc : 0 ≤ rc) (hb : 0 ≤ rb)
    (h : ∀ a₁ a₂ : ℝ, 0 ≤ a₁ → 0 ≤ a₂ →
      a₁ * rc + a₂ * rb ≤ √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2)) :
    rc ^ 2 + rb ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by
  have h1 := h rc rb hc hb
  set C := √(2 * (p ^ 2 + q ^ 2))
  set s := √(rc ^ 2 + rb ^ 2)
  have hs2 : s ^ 2 = rc ^ 2 + rb ^ 2 := sq_sqrt (by positivity)
  have hC2 : C ^ 2 = 2 * (p ^ 2 + q ^ 2) := sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hC0 : 0 ≤ C := sqrt_nonneg _
  have : s * s ≤ C * s := by nlinarith
  rcases hs0.lt_or_eq with hpos | hzero
  · have hsC : s ≤ C := le_of_mul_le_mul_right this hpos
    nlinarith
  · have : rc ^ 2 + rb ^ 2 = 0 := by rw [← hs2, ← hzero]; ring
    rw [this]; positivity

/-- Passing to suprema in one variable: if `a x + b ≤ c` for all `x ∈ S` (`S` nonempty, `a ≥ 0`),
then `a·max(0, sup S) + b ≤ c`, provided also `b ≤ c`. -/
lemma lin_sSup {S : Set ℝ} (hne : S.Nonempty) {a b c : ℝ} (ha : 0 ≤ a)
    (h : ∀ x ∈ S, a * x + b ≤ c) (h0 : b ≤ c) : a * max 0 (sSup S) + b ≤ c := by
  rcases ha.lt_or_eq with ha | ha
  · rcases le_total (sSup S) 0 with hs | hs
    · rw [max_eq_left hs]; simpa using h0
    · rw [max_eq_right hs]
      have : sSup S ≤ (c - b) / a := by
        apply csSup_le hne; intro x hx; rw [le_div_iff₀ ha]; linarith [h x hx]
      rw [le_div_iff₀ ha] at this; linarith
  · rw [← ha]; simpa using h0

/-- **Lemma S, supremum form.** Let `Rc`, `Rb` be nonempty sets of reals (the ratios `N₁/|oo′|`
over c-child configurations with `o ≠ o′`, resp. `N₂/|ww′|` over b-child configurations) such
that for every `x ∈ Rc`, `y ∈ Rb` and `a₁, a₂ ≥ 0`: `a₁x + a₂y ≤ √(2(p²+q²))·√(a₁²+a₂²)` (which is
what `lemmaS_core` gives for each pair of configurations). Then with
`r_c = max(0, sup Rc)`, `r_b = max(0, sup Rb)` (negative suprema replaced by 0):
`r_c² + r_b² ≤ 2(p²+q²)`. (For an unbounded set Lean's `sSup` is `0`; but the hypothesis itself
bounds `Rc` and `Rb` by `√(2(p²+q²))`.) -/
theorem circle_of_sSup {p q : ℝ} {Rc Rb : Set ℝ} (hc : Rc.Nonempty) (hb : Rb.Nonempty)
    (h : ∀ x ∈ Rc, ∀ y ∈ Rb, ∀ a₁ a₂ : ℝ, 0 ≤ a₁ → 0 ≤ a₂ →
      a₁ * x + a₂ * y ≤ √(2 * (p ^ 2 + q ^ 2)) * √(a₁ ^ 2 + a₂ ^ 2)) :
    (max 0 (sSup Rc)) ^ 2 + (max 0 (sSup Rb)) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by
  set C := √(2 * (p ^ 2 + q ^ 2))
  have hC0 : 0 ≤ C := sqrt_nonneg _
  -- each element is bounded by `C` (take `(a₁,a₂) = (1,0)`, resp. `(0,1)`)
  obtain ⟨y0, hy0⟩ := hb
  obtain ⟨x0, hx0⟩ := hc
  have bx : ∀ x ∈ Rc, x ≤ C := by
    intro x hx; have := h x hx y0 hy0 1 0 zero_le_one le_rfl; simpa using this
  have by' : ∀ y ∈ Rb, y ≤ C := by
    intro y hy; have := h x0 hx0 y hy 0 1 le_rfl zero_le_one; simpa using this
  apply circle_of_linear (le_max_left _ _) (le_max_left _ _)
  intro a₁ a₂ h1 h2
  have hR : 0 ≤ C * √(a₁ ^ 2 + a₂ ^ 2) := by positivity
  have ha1C : a₁ * C ≤ C * √(a₁ ^ 2 + a₂ ^ 2) := by
    rw [mul_comm]; apply mul_le_mul_of_nonneg_left _ hC0
    exact le_sqrt_of_sq_le (by nlinarith)
  have ha2C : a₂ * C ≤ C * √(a₁ ^ 2 + a₂ ^ 2) := by
    rw [mul_comm]; apply mul_le_mul_of_nonneg_left _ hC0
    exact le_sqrt_of_sq_le (by nlinarith)
  -- first pass to the supremum in `y`, for each fixed `x`, then in `x`
  have stepY : ∀ x ∈ Rc, a₂ * max 0 (sSup Rb) + a₁ * x ≤ C * √(a₁ ^ 2 + a₂ ^ 2) := by
    intro x hx
    apply lin_sSup ⟨y0, hy0⟩ h2
    · intro y hy; have := h x hx y hy a₁ a₂ h1 h2; linarith
    · rcases le_total x 0 with hx0' | hx0'
      · nlinarith
      · nlinarith [bx x hx, mul_le_mul_of_nonneg_left (bx x hx) h1]
  have := lin_sSup ⟨x0, hx0⟩ h1 (b := a₂ * max 0 (sSup Rb)) (c := C * √(a₁ ^ 2 + a₂ ^ 2))
    (fun x hx => by linarith [stepY x hx]) ?_
  · linarith
  · -- `a₂ · max(0, sup Rb) ≤ C|a|`
    have hsb : max 0 (sSup Rb) ≤ C := max_le hC0 (csSup_le ⟨y0, hy0⟩ by')
    nlinarith [mul_le_mul_of_nonneg_left hsb h2]

end PortsLean.LemmaS
