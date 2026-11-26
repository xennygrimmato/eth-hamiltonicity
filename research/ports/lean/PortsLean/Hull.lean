import Mathlib

/-!
# Hull lemma (`research/ports/hull/notes.md`): the checkable parts

(a) rank table in `Mat₂(F₂)`; (b) equality in the quadrilateral inequality for the four squares
`(n, t_i, s, t_j)`; (c) the model `tripod × ℝ`; (d) the rigidity statement the informal proof
uses, as explicit hypotheses, and the glue "N5 price ⇒ W5 price" proved from them.
-/

namespace PortsLean.Hull

open Matrix Real

abbrev M2 := Matrix (Fin 2) (Fin 2) (ZMod 2)

def n0 : M2 := 0
def s0 : M2 := 1
def t1 : M2 := !![1, 0; 0, 0]
def t2 : M2 := !![0, 0; 1, 1]
def t3 : M2 := !![0, 1; 0, 1]

/-! ## (a) Ranks -/

lemma rank_pos_of_ne_zero {A : M2} (hA : A ≠ 0) : 0 < A.rank := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  apply hA
  have h1 : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
  have h2 : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp h1
  have h3 : Matrix.toLin' A = Matrix.toLin' 0 := by
    rw [Matrix.toLin'_apply', h2]; ext; simp
  exact Matrix.toLin'.injective h3

lemma rank_one_of {A : M2} (u x : Fin 2 → ZMod 2) (hA : A = vecMulVec u x) (h0 : A ≠ 0) :
    A.rank = 1 := by
  have := rank_pos_of_ne_zero h0
  have := hA ▸ Matrix.rank_vecMulVec_le u x
  omega

lemma rank_two_of {A : M2} (hdet : A.det ≠ 0) : A.rank = 2 := by
  have : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (Ne.isUnit hdet)
  simpa using Matrix.rank_of_isUnit A this

/-- All rank-one entries of the table, with explicit factorisations `u xᵀ`. -/
theorem ranks_one :
    t1.rank = 1 ∧ t2.rank = 1 ∧ t3.rank = 1 ∧
      (s0 - t1).rank = 1 ∧ (s0 - t2).rank = 1 ∧ (s0 - t3).rank = 1 := by
  refine ⟨rank_one_of ![1, 0] ![1, 0] ?_ ?_, rank_one_of ![0, 1] ![1, 1] ?_ ?_,
    rank_one_of ![1, 1] ![0, 1] ?_ ?_, rank_one_of ![0, 1] ![0, 1] ?_ ?_,
    rank_one_of ![1, 1] ![1, 0] ?_ ?_, rank_one_of ![1, 0] ![1, 1] ?_ ?_⟩ <;>
  first
  | (ext i j; fin_cases i <;> fin_cases j <;> decide)
  | (intro h; have := congrFun (congrFun h 0) 0; revert this; decide)
  | (intro h; have := congrFun (congrFun h 1) 1; revert this; decide)
  | (intro h; have := congrFun (congrFun h 1) 0; revert this; decide)

/-- All rank-two entries: `t_i − t_j` (i ≠ j) and `s − n = 1`. -/
theorem ranks_two :
    (t1 - t2).rank = 2 ∧ (t1 - t3).rank = 2 ∧ (t2 - t3).rank = 2 ∧ (s0 - n0).rank = 2 := by
  refine ⟨rank_two_of ?_, rank_two_of ?_, rank_two_of ?_, rank_two_of ?_⟩ <;>
  · rw [Matrix.det_fin_two]; decide

/-! ## (b) Equality in the quadrilateral inequality -/

/-- In characteristic 2, `a − b = b − a`. -/
lemma sub_comm2 (a b : M2) : a - b = b - a := by
  ext i j
  simp only [Matrix.sub_apply]
  generalize a i j = x
  generalize b i j = y
  revert x y; decide

/-- The √rank metric. -/
noncomputable def rho (a b : M2) : ℝ := √((a - b).rank)

/-- In the √rk metric each quadrilateral `(n, t_i, s, t_j)` has sides 1, diagonals √2,
so `|n s|² + |t_i t_j|² = |n t_i|² + |t_i s|² + |s t_j|² + |t_j n|²` (= 4). -/
theorem quad_equality (ti tj : M2) (hi : ti.rank = 1 ∧ (s0 - ti).rank = 1)
    (hj : tj.rank = 1 ∧ (s0 - tj).rank = 1) (hij : (ti - tj).rank = 2) :
    rho n0 s0 ^ 2 + rho ti tj ^ 2 = rho n0 ti ^ 2 + rho ti s0 ^ 2 + rho s0 tj ^ 2 + rho tj n0 ^ 2 := by
  have r1 : (n0 - s0).rank = 2 := by rw [sub_comm2]; exact ranks_two.2.2.2
  have r2 : (n0 - ti).rank = 1 := by rw [sub_comm2]; simpa [n0] using hi.1
  have r3 : (ti - s0).rank = 1 := by rw [sub_comm2]; exact hi.2
  have r4 : (tj - n0).rank = 1 := by simpa [n0] using hj.1
  simp only [rho, r1, r2, r3, r4, hij, hj.2]
  norm_num

/-- The CAT(0) quadrilateral inequality, as an explicit hypothesis on a metric space
(AN `lem_toolkit`, second conjunct, `Paper/Toolkit.lean` l.467–471). -/
def QuadIneq (Y : Type) [MetricSpace Y] : Prop :=
  ∀ x v y u : Y, dist x v ^ 2 + dist y u ^ 2 ≤ dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2

/-- Any placement of N5 into such a space with the √rk distances is an equality case of the
quadrilateral inequality for each square `(n, t_i, s, t_j)`: the hypothesis of AN C.4(f). -/
theorem n5_equality_case {Y : Type} [MetricSpace Y] (_hq : QuadIneq Y) (g : M2 → Y)
    (hg : ∀ a b, dist (g a) (g b) = rho a b) (ti tj : M2) (hi : ti.rank = 1 ∧ (s0 - ti).rank = 1)
    (hj : tj.rank = 1 ∧ (s0 - tj).rank = 1) (hij : (ti - tj).rank = 2) :
    dist (g n0) (g s0) ^ 2 + dist (g ti) (g tj) ^ 2 =
      dist (g n0) (g ti) ^ 2 + dist (g ti) (g s0) ^ 2 + dist (g s0) (g tj) ^ 2 + dist (g tj) (g n0) ^ 2 := by
  simp only [hg]; exact quad_equality ti tj hi hj hij

/-! ## (c) The model `tripod × ℝ` -/

/-- A point: (leg, distance from the hub `r ≥ 0`, height `σ`). -/
abbrev TP := Fin 3 × ℝ × ℝ

/-- Tripod distance of `(i,r)`, `(j,r')` (`r, r' ≥ 0`). -/
noncomputable def dTri (p q : TP) : ℝ := if p.1 = q.1 then |p.2.1 - q.2.1| else p.2.1 + q.2.1

/-- ℓ₂ product metric on `tripod × ℝ`. -/
noncomputable def dTP (p q : TP) : ℝ := √(dTri p q ^ 2 + (p.2.2 - q.2.2) ^ 2)

noncomputable def c : ℝ := 1 / √2

lemma c_sq : c ^ 2 = 1 / 2 := by
  rw [c, div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma c_pos : 0 < c := by unfold c; positivity

noncomputable def nP : TP := (0, 0, -c)
noncomputable def sP : TP := (0, 0, c)
noncomputable def tP (i : Fin 3) : TP := (i, c, 0)

/-- The model points have exactly the N5 distances: `|ns| = |t_it_j| = √2`, `|nt_i| = |st_i| = 1`. -/
theorem model_n5 :
    dTP nP sP = √2 ∧ (∀ i j, i ≠ j → dTP (tP i) (tP j) = √2) ∧
      (∀ i, dTP nP (tP i) = 1) ∧ (∀ i, dTP sP (tP i) = 1) := by
  have hc := c_sq
  have hc0 := c_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [dTP, dTri, nP, sP, if_true, sub_self, abs_zero]
    congr 1; nlinarith
  · intro i j hij
    simp only [dTP, dTri, tP, if_neg hij, sub_self]
    congr 1; nlinarith
  · intro i
    simp only [dTP, dTri, nP, tP]
    split_ifs <;> · rw [show (1 : ℝ) = √1 by simp]; congr 1; simp [abs_of_pos hc0]; nlinarith
  · intro i
    simp only [dTP, dTri, sP, tP]
    split_ifs <;> · rw [show (1 : ℝ) = √1 by simp]; congr 1; simp [abs_of_pos hc0]; nlinarith

/-- The diamond `D = {|ξ o| + |σ| ≤ 1/√2}`. -/
def inDiamond (p : TP) : Prop := 0 ≤ p.2.1 ∧ p.2.1 + |p.2.2| ≤ c

noncomputable def vP (ℓ : ℝ) (i : Fin 3) : TP := (i, ℓ, 0)
noncomputable def uP (ℓ : ℝ) (sgn : ℝ) : TP := (0, 0, sgn * (ℓ / 3))

/-- W5(ℓ, ℓ/3) lies in the diamond for `0 ≤ ℓ ≤ 1/√2`, with the W5 distances. -/
theorem w5_in_diamond (ℓ : ℝ) (h0 : 0 ≤ ℓ) (hℓ : ℓ ≤ c) :
    (∀ i, inDiamond (vP ℓ i)) ∧ inDiamond (uP ℓ 1) ∧ inDiamond (uP ℓ (-1)) ∧
      (∀ i j, i ≠ j → dTP (vP ℓ i) (vP ℓ j) = 2 * ℓ) ∧
      (∀ i, dTP (vP ℓ i) (uP ℓ 1) = √(ℓ ^ 2 + (ℓ / 3) ^ 2)) ∧
      (∀ i, dTP (vP ℓ i) (uP ℓ (-1)) = √(ℓ ^ 2 + (ℓ / 3) ^ 2)) ∧
      dTP (uP ℓ 1) (uP ℓ (-1)) = 2 * (ℓ / 3) := by
  refine ⟨fun i => ⟨h0, by simp [vP]; linarith⟩, ⟨le_rfl, ?_⟩, ⟨le_rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [uP, one_mul]; rw [abs_of_nonneg (by linarith)]; linarith
  · simp only [uP, neg_one_mul, abs_neg]; rw [abs_of_nonneg (by linarith)]; linarith
  · intro i j hij
    simp only [dTP, dTri, vP, if_neg hij, sub_self]
    rw [show (ℓ + ℓ) ^ 2 + (0:ℝ) ^ 2 = (2 * ℓ) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  · intro i
    simp only [dTP, dTri, vP, uP]
    split_ifs <;> · congr 1; simp [abs_of_nonneg h0] <;> ring
  · intro i
    simp only [dTP, dTri, vP, uP]
    split_ifs <;> · congr 1; simp [abs_of_nonneg h0] <;> ring
  · simp only [dTP, dTri, uP, if_true, sub_self, abs_zero]
    rw [show (0:ℝ) ^ 2 + (1 * (ℓ / 3) - -1 * (ℓ / 3)) ^ 2 = (2 * (ℓ / 3)) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]

/-! ## (d) The rigidity step, as explicit hypotheses -/

/-- AN's `Cat.CN` (`Nc/Cat/Core.lean` l.22): complete, with midpoints satisfying the CN inequality.
Lemma H MUST assume this (not just `QuadIneq`): the five-point space N5 itself satisfies `QuadIneq`
(any subset of a CAT(0) space does) but contains no diamond, so a version of Lemma H assuming only
`QuadIneq` would be false and would make the glue theorem vacuous. -/
def CNProp (X : Type) [MetricSpace X] : Prop :=
  CompleteSpace X ∧ ∀ x v : X, ∃ m : X, ∀ z : X,
    dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4

/-- The statements the informal proof of "N5 a price ⇒ W5 a price" uses, made explicit.
`IsPrice` is AN's `Nc.Price.IsPrice K` (abstract here). -/
structure HullHyps (IsPrice : {Y : Type} → (Y → Y → ℝ) → Prop) where
  /-- AN `prop_space` (`Paper/Curvature.lean` l.211): every price is the pull-back of the metric of a
  CAT(0) space `X` **whose whole metric is a price**. -/
  prop_space : ∀ {V : Type} (w : V → V → ℝ), IsPrice w →
    ∃ (X : Type) (_ : MetricSpace X) (f : V → X), CNProp X ∧ QuadIneq X ∧ IsPrice (fun a b : X => dist a b) ∧
      ∀ a b, dist (f a) (f b) = w a b
  /-- Def. A.4: pull-backs of prices are prices. -/
  pullback : ∀ {X V : Type} (d : X → X → ℝ) (g : V → X), IsPrice d → IsPrice (fun a b => d (g a) (g b))
  /-- **Lemma H (the gap; NOT proved here).** In a complete CN space, five points with the N5
  distances span an isometric copy of the diamond `D`, sending hub heights `∓c` to `n, s` and the leg
  tips to the `t_i`. The informal proof (notes §1.3) uses: unique geodesics (C.4(a)); the flat
  rectangle formula C.4(f) applied twice per square (solid squares); that an isometric copy of a
  nondegenerate Euclidean triangle in a uniquely geodesic space is determined by its vertices; and
  gluing three flat triangles along `[n,s]`. Mathlib has no CAT(0) theory to check this. -/
  lemmaH : ∀ (X : Type) [MetricSpace X], CNProp X → QuadIneq X → ∀ (g : M2 → X),
    (∀ a ∈ ({n0, s0, t1, t2, t3} : Set M2), ∀ b ∈ ({n0, s0, t1, t2, t3} : Set M2),
      dist (g a) (g b) = rho a b) →
    ∃ Ψ : TP → X, ∀ p q, inDiamond p → inDiamond q → dist (Ψ p) (Ψ q) = dTP p q

/-- **Glue (proved from the hypotheses).** If ρ₂ is a price, then the five points W5(ℓ,ℓ/3)
(`ℓ ≤ 1/√2`), with their model distances, form a price. No "convex hull of prices" statement is
needed: AN's `prop_space` already says the WHOLE metric of the price space is a price, so any points
of it (hull points included) pull back to prices. The only gap is `lemmaH`. -/
theorem w5_price_of_rho_price (IsPrice : {Y : Type} → (Y → Y → ℝ) → Prop) (H : HullHyps IsPrice)
    (hρ : IsPrice rho) (P : Fin 5 → TP) (hP : ∀ i, inDiamond (P i)) :
    IsPrice (fun i j => dTP (P i) (P j)) := by
  obtain ⟨X, _, f, hcn, hq, hX, hf⟩ := H.prop_space rho hρ
  obtain ⟨Ψ, hΨ⟩ := H.lemmaH X hcn hq f (fun a _ b _ => hf a b)
  have := H.pullback (fun a b : X => dist a b) (fun i => Ψ (P i)) hX
  have e : (fun i j => dist (Ψ (P i)) (Ψ (P j))) = fun i j => dTP (P i) (P j) := by
    funext i j; exact hΨ _ _ (hP i) (hP j)
  simpa [e] using this

end PortsLean.Hull
