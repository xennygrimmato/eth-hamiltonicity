import Mathlib

/-!
# Algebra behind 9/4 (`research/mm/why-nine-fourths.md` §5.2–5.3, §7, §15.1)

The tripod inequality `D ≥ Σa − 1/Σ(1/a)` itself is a statement about all spectral points (OA,
Prop. 8.1/9.2) and is NOT proved here; what is proved is all the algebra the note derives from it.
-/

namespace PortsLean.NineFourths

open Real

/-- Thomson's principle, lower bound: for positive arms and any split `f` with `Σ f = 1`,
`Σ a_i f_i² ≥ 1/Σ(1/a_i)`. -/
theorem thomson_le (a b c f g h : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : f + g + h = 1) :
    1 / (1 / a + 1 / b + 1 / c) ≤ a * f ^ 2 + b * g ^ 2 + c * h ^ 2 := by
  have hS : 0 < 1 / a + 1 / b + 1 / c := by positivity
  rw [div_le_iff₀ hS]
  -- Cauchy–Schwarz: (f+g+h)² ≤ (a f² + b g² + c h²)(1/a+1/b+1/c)
  have key : (a * f ^ 2 + b * g ^ 2 + c * h ^ 2) * (1 / a + 1 / b + 1 / c) - (f + g + h) ^ 2 =
      (a * f - b * g) ^ 2 / (a * b) + (b * g - c * h) ^ 2 / (b * c) + (c * h - a * f) ^ 2 / (c * a) := by
    field_simp; ring
  have : 0 ≤ (a * f - b * g) ^ 2 / (a * b) + (b * g - c * h) ^ 2 / (b * c) + (c * h - a * f) ^ 2 / (c * a) := by
    positivity
  rw [hs] at key
  nlinarith

/-- ... with equality at `f_i ∝ 1/a_i` (current divides inversely to resistance). -/
theorem thomson_eq (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    let S := 1 / a + 1 / b + 1 / c
    a * (1 / a / S) ^ 2 + b * (1 / b / S) ^ 2 + c * (1 / c / S) ^ 2 = 1 / S := by
  intro S
  have hS : 0 < S := by positivity
  simp only [S]
  field_simp

/-- AM–HM: the discount is at most one ninth of the total, `1/Σ(1/a) ≤ Σa/9`. -/
theorem discount_le_ninth (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (1 / a + 1 / b + 1 / c) ≤ (a + b + c) / 9 := by
  have := thomson_le a b c (1 / 3) (1 / 3) (1 / 3) ha hb hc (by norm_num)
  linarith

/-- §5.3: at label rate 1, `Σa − 1/Σ(1/a) ≤ 1` forces perimeter `2Σa ≤ 9/4`. -/
theorem perimeter_le_nine_fourths (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (htri : (a + b + c) - 1 / (1 / a + 1 / b + 1 / c) ≤ 1) : 2 * (a + b + c) ≤ 9 / 4 := by
  have := discount_le_ninth a b c ha hb hc
  linarith

/-- Equality is attained at equal arms `3/8` (perimeter exactly `9/4`, `D* = 1`). -/
theorem equal_arms : let a : ℝ := 3 / 8
    (a + a + a) - 1 / (1 / a + 1 / a + 1 / a) = 1 ∧ 2 * (a + a + a) = 9 / 4 := by
  norm_num

/-- The unit tripod: `D*(1,1,1) = 3 − 1/3 = 8/3`, exponent `6/D* = 9/4`. -/
theorem unit_tripod : (1 + 1 + 1 : ℝ) - 1 / (1 / 1 + 1 / 1 + 1 / 1) = 8 / 3 ∧
    (6 : ℝ) / (8 / 3) = 9 / 4 := by norm_num

/-- §15.1, team-size form: with `x = qr, y = rp, z = pq`,
`(xy + yz + zx)² / (4xyz) = (p+q+r)²/4`. -/
theorem team_size (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    let x := q * r; let y := r * p; let z := p * q
    (x * y + y * z + z * x) ^ 2 / (4 * x * y * z) = (p + q + r) ^ 2 / 4 := by
  intro x y z
  simp only [x, y, z]
  field_simp
  ring

/-- §7: the rectangular formula `Σ_k √(1 − c_k/ω) = 1` (with `c_k` the sum of the two thicknesses at
site `k`) is solved by `ω = (xy+yz+zx)²/(4xyz)` in the interior `1/z ≤ 1/x + 1/y` etc.
Key identity: `S² − 4xyz(x+y) = (xy − z(x+y))²`, `S = xy+yz+zx`. -/
theorem rectangular_formula (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h3 : x * y ≤ z * x + z * y) (h1 : y * z ≤ x * y + x * z) (h2 : z * x ≤ y * z + y * x) :
    let S := x * y + y * z + z * x
    let ω := S ^ 2 / (4 * x * y * z)
    √(1 - (x + y) / ω) + √(1 - (y + z) / ω) + √(1 - (z + x) / ω) = 1 := by
  intro S ω
  have hS : 0 < S := by positivity
  have hxyz : 0 < 4 * x * y * z := by positivity
  have e : ∀ u v w : ℝ, u * v ≤ w * u + w * v → 0 < u → 0 < v → 0 < w →
      u * v + v * w + w * u = S → u * v * w = x * y * z →
      √(1 - (u + v) / ω) = (w * u + w * v - u * v) / S := by
    intro u v w huv hu hv hw hSu hp
    have hω : (u + v) / ω = 4 * x * y * z * (u + v) / S ^ 2 := by
      simp only [ω]; field_simp
    have hprod : 4 * x * y * z = 4 * u * v * w := by
      rw [show 4 * x * y * z = 4 * (x * y * z) by ring, ← hp]; ring
    rw [hω, hprod]
    have hsq : 1 - 4 * u * v * w * (u + v) / S ^ 2 = ((w * u + w * v - u * v) / S) ^ 2 := by
      rw [← hSu]; field_simp; try ring
    rw [hsq, Real.sqrt_sq (div_nonneg (by linarith) hS.le)]
  rw [e x y z h3 hx hy hz (by simp only [S]; try ring) (by ring), e y z x h1 hy hz hx (by simp only [S]; try ring) (by ring),
    e z x y h2 hz hx hy (by simp only [S]; try ring) (by ring)]
  field_simp
  simp only [S]; ring

/-- The square case `x = y = z = 1`: `3√(1 − 2/ω) = 1` at `ω = 9/4`. -/
theorem square_case : 3 * √(1 - 2 / (9 / 4 : ℝ)) = 1 := by
  rw [show (1 : ℝ) - 2 / (9 / 4) = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

end PortsLean.NineFourths
