/-
Exploratory file (`research/next/v3`).  Not imported by the root module and not a claimed result in the sense
of the top-level README.

Subject: the rank metric `ρ₂(a, b)² = rk (a - b)` on the sixteen `2 × 2` matrices over `𝔽₂`.  By Anthropic's
`VP ≠ VNP over every field`, Theorem D.2 (proof, Steps 1–7) and `research/vpvnp/c1`, the contracting hypothesis
fails exactly when the rank metrics are prices.  This file checks, by exhaustion, the finite facts used in
`research/next/v3/notebook.md`:

* around every invertible `V` the six rank-one `W` with `rk (V - W) = 1` form a hexagon (a 6-cycle under
  "difference of rank one"); opposite cells are `W` and `V - W`;
* the nine rank-one matrices are a `3 × 3` grid with `rk (W - W') = [rows differ] + [columns differ]`;
* the point `0` with the nine rank-one matrices, and the eight points `0`, `I` and the hexagon of `I`, have the
  squared-distance tables of explicit points of `tripod × tripod × line`.

A matrix `(a b; c d)` is the quadruple `(a, b, c, d)` of bits; addition is `xor`.  The rank is defined by
"`0` for the zero matrix, `2` when the determinant is `1`, else `1`".
-/
import Mathlib

namespace EthFollowup.Spectral.RankTwo

/-- `2 × 2` matrices over `𝔽₂`. -/
abbrev M2 := Bool × Bool × Bool × Bool

def add (x y : M2) : M2 := (xor x.1 y.1, xor x.2.1 y.2.1, xor x.2.2.1 y.2.2.1, xor x.2.2.2 y.2.2.2)
def det (x : M2) : Bool := xor (x.1 && x.2.2.2) (x.2.1 && x.2.2.1)
def zero : M2 := (false, false, false, false)
def one : M2 := (true, false, false, true)

/-- Rank of a `2 × 2` matrix over `𝔽₂`. -/
def rk (x : M2) : ℕ := if x = zero then 0 else if det x then 2 else 1

theorem rk_counts :
    (Finset.univ.filter fun x : M2 => rk x = 1).card = 9 ∧
    (Finset.univ.filter fun x : M2 => rk x = 2).card = 6 := by decide

/-- The rank of a difference is a metric (it is the graph distance of the bilinear forms graph). -/
theorem rk_add_le : ∀ x y : M2, rk (add x y) ≤ rk x + rk y := by decide

theorem rk_add_self : ∀ x : M2, rk (add x x) = 0 := by decide

/-- `W` lies on the hexagon of `V`: both `W` and `V - W` have rank one. -/
def Hex (V W : M2) : Prop := rk W = 1 ∧ rk (add V W) = 1

instance (V W : M2) : Decidable (Hex V W) := by unfold Hex; infer_instance

/-- Six rank-one matrices at rank-distance one from an invertible matrix. -/
theorem hex_card : ∀ V : M2, rk V = 2 → (Finset.univ.filter fun W : M2 => Hex V W).card = 6 := by decide

/-- The opposite cell of `W` is `V - W`, at rank-distance two. -/
theorem hex_opposite : ∀ V W : M2, rk V = 2 → Hex V W → Hex V (add V W) ∧ rk (add W (add V W)) = 2 := by
  decide

/-- Every cell of the hexagon has exactly two neighbours at rank-distance one in it. -/
theorem hex_two_neighbours : ∀ V W : M2, rk V = 2 → Hex V W →
    (Finset.univ.filter fun U : M2 => Hex V U ∧ rk (add W U) = 1).card = 2 := by decide

/-- The two neighbours of a cell are not neighbours of each other, so the hexagon is one 6-cycle and not two
triangles: the sum of two neighbouring cells is a rank-one matrix outside the hexagon, and a third cell at
rank-distance one from both would have to be that sum. -/
theorem hex_sum_outside : ∀ V W U : M2, rk V = 2 → Hex V W → Hex V U → rk (add W U) = 1 →
    ¬ Hex V (add W U) := by decide

/-- Three rank-one matrices pairwise at rank-distance one lie on a line of the grid: the third is the sum of the
other two. -/
theorem line_third : ∀ W U U' : M2, rk W = 1 → rk U = 1 → rk U' = 1 →
    rk (add W U) = 1 → rk (add W U') = 1 → rk (add U U') = 1 → U' = add W U := by decide

/-- The hexagon contains no triangle, so it is a single 6-cycle. -/
theorem hex_no_triangle (V W U U' : M2) (hV : rk V = 2) (hW : Hex V W) (hU : Hex V U) (hU' : Hex V U')
    (h1 : rk (add W U) = 1) (h2 : rk (add W U') = 1) (h3 : rk (add U U') = 1) : False := by
  have h := line_third W U U' hW.1 hU.1 hU'.1 h1 h2 h3
  subst h
  exact hex_sum_outside V W U hV hW hU h1 hU'

/-! ### The grid of rank-one matrices and the pieces inside `tripod × tripod × line` -/

/-- The three nonzero vectors `x₀, x₁, x₂` of `𝔽₂²`. -/
def vec : Fin 3 → Bool × Bool
  | 0 => (true, false) | 1 => (false, true) | 2 => (true, true)

/-- `y j` is the nonzero functional vanishing on `x j`. -/
def dual : Fin 3 → Bool × Bool
  | 0 => (false, true) | 1 => (true, false) | 2 => (true, true)

/-- The rank-one matrix `x i · (y j)ᵀ`. -/
def cell (i j : Fin 3) : M2 :=
  ((vec i).1 && (dual j).1, (vec i).1 && (dual j).2, (vec i).2 && (dual j).1, (vec i).2 && (dual j).2)

theorem cell_rk : ∀ i j i' j' : Fin 3,
    rk (add (cell i j) (cell i' j')) = (if i = i' then 0 else 1) + (if j = j' then 0 else 1) := by decide

theorem cell_one : ∀ i j : Fin 3, rk (add one (cell i j)) = if i = j then 2 else 1 := by decide

/-- Sites: `none` is the identity, `some none` is zero, `some (some (i, j))` is the cell `(i, j)`. -/
abbrev Site := Option (Option (Fin 3 × Fin 3))

def mat : Site → M2
  | none => one
  | some none => zero
  | some (some (i, j)) => cell i j

/-- A point of a tripod with doubled radius: `(leg, 2 · radius)`. -/
abbrev TPoint := Fin 3 × ℤ

/-- Four times the squared distance in a tripod. -/
def tripodSq (p q : TPoint) : ℤ :=
  if p.1 = q.1 ∨ p.2 = 0 ∨ q.2 = 0 then (p.2 - q.2) ^ 2 else (p.2 + q.2) ^ 2

/-- Position in `tripod × tripod × line`: tripod radii are halves of the integers given, and the last
coordinate is in units of `1/√2`. -/
def pos : Site → TPoint × TPoint × ℤ
  | none => ((0, 0), (0, 0), 1)
  | some none => ((0, 0), (0, 0), -1)
  | some (some (i, j)) => ((i, 1), (j, 1), 0)

/-- Four times the squared `ℓ₂` product distance. -/
def distSq4 (P Q : TPoint × TPoint × ℤ) : ℤ :=
  tripodSq P.1 Q.1 + tripodSq P.2.1 Q.2.1 + 2 * (P.2.2 - Q.2.2) ^ 2

/-- `0` and the nine rank-one matrices sit in `tripod × tripod × line` with their rank metric. -/
theorem apex_embeds : ∀ s t : Option (Fin 3 × Fin 3),
    distSq4 (pos (some s)) (pos (some t)) = 4 * (rk (add (mat (some s)) (mat (some t))) : ℤ) := by decide

/-- The eight points `0`, `I` and the hexagon of `I`. -/
def inH8 : Site → Bool
  | some (some (i, j)) => i != j
  | _ => true

theorem H8_card : (Finset.univ.filter fun s : Site => inH8 s).card = 8 := by decide

/-- `H₈` sits in `tripod × tripod × line` with its rank metric. -/
theorem H8_embeds : ∀ s t : Site, inH8 s → inH8 t →
    distSq4 (pos s) (pos t) = 4 * (rk (add (mat s) (mat t)) : ℤ) := by decide

/-- The embedding does not extend to the three remaining rank-one matrices: they are at squared distance 2 from
`I`, but the positions of `apex_embeds` are at squared distance 1 from the position of `I`. -/
theorem diag_cells_misplaced : ∀ i : Fin 3,
    distSq4 (pos none) (pos (some (some (i, i)))) = 4 ∧ rk (add one (cell i i)) = 2 := by decide

end EthFollowup.Spectral.RankTwo
