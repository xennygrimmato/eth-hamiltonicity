import Mathlib
import PortsLean.ThmAArith

/-!
# Theorem A skeleton: contracting ⇒ ports

Everything imported from the two releases is an explicit hypothesis of `theorem_A`
(no `axiom`). Sources (read, not built):

* OA = openai/math, `lean/OAI/...`
* AN = anthropics/formal-math, `vp-vnp/...`

## The objects

* **OA definitions copied verbatim** (they only need Mathlib): `walkEnergy`
  (`OAI/Computability/VPVNP/WalkEnergy.lean` l.24), `HasPoincareBound` (same file l.195),
  `normalizeArcs` (`OAI/Computability/VPVNP/GraphRounding.lean` l.75).
* **OA spectral targets** (`OAI/Computability/MultitapeWeakETH/Cloud.lean` l.12,
  `structure SpectralTarget`: complete, nonempty, `HasFractions`,
  `RealizableConfigurations (AlgebraicClosure ℚ)`) are abstracted as metric spaces
  satisfying an opaque predicate `Good`. `PortZero` (`.../MultitapeWeakETH/Price.lean` l.28)
  is an opaque `Prop`; `PriceZero := ¬ PortZero` (l.38).
* **AN prices**: `Nc.Price.IsPrice K` (`vp-vnp/Nc/Price/Basic.lean` l.74) is an opaque
  predicate `IsPrice` on functions `Y → Y → ℝ`, for every `Y : Type`. AN's `Contracting K`
  (`vp-vnp/Paper/Alternative.lean` l.45) is an opaque `Prop`.
* **U_h(F₂)** (`vp-vnp/Nc/Tower/UT.lean` l.27, generators `x` l.83) is an abstract family of
  finite groups `U h` with elements `x h j`, `j : Fin (h-1)`.

OA targets and AN prices are *different types*: the only bridge is `contain`
(OA ⇒ AN), so the skeleton cannot use the false converse.
-/

namespace PortsLean.ThmA

open Finset

section OADefs
variable {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]

/-- Verbatim from OA `WalkEnergy.lean` l.24. -/
noncomputable def walkEnergy (A : Matrix ι ι ℝ) (x : ι → X) : ℝ :=
  ∑ i, ∑ j, A i j * dist (x j) (x i) ^ 2

/-- Verbatim from OA `WalkEnergy.lean` l.195. -/
def HasPoincareBound (X : Type*) [PseudoMetricSpace X] (A : Matrix ι ι ℝ) (γ : ℝ) : Prop :=
  ∀ x : ι → X, (∑ i, ∑ j, dist (x i) (x j) ^ 2) / Fintype.card ι ≤ γ * walkEnergy A x

/-- Verbatim from OA `GraphRounding.lean` l.75. -/
noncomputable def normalizeArcs (M : Matrix ι ι ℕ) (h : ℕ) : Matrix ι ι ℝ :=
  fun i j ↦ (M i j : ℝ) / h

end OADefs

/-- Abstract OA spectral target (mirrors `structure SpectralTarget`, Cloud.lean l.12). -/
structure Target (Good : (X : Type) → MetricSpace X → Prop) where
  carrier : Type
  [metric : MetricSpace carrier]
  good : Good carrier metric

attribute [instance] Target.metric

/-! ## Hypotheses -/

variable
  -- OA side
  (Good : (X : Type) → MetricSpace X → Prop)
  (PortZero : Prop)
  -- AN side
  (U : ℕ → Type) [∀ h, Group (U h)] [∀ h, Fintype (U h)] (x : (h : ℕ) → Fin (h - 1) → U h)
  (IsPrice : {Y : Type} → (Y → Y → ℝ) → Prop)
  (Contracting : Prop)

/-- (i) AN Theorem F.6, `thm_poincare`, `vp-vnp/Paper/Groups.lean` l.1085–1088, with exactly
its quantifier order `∃ u ≥ 2, ∃ C₀ ≥ 0, ∀ l ≥ 2, ∀ price w on U_{l u}`. -/
def F6Statement : Prop :=
  Contracting →
    ∃ u : ℕ, 2 ≤ u ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ l : ℕ, 2 ≤ l → ∀ w : U (l * u) → U (l * u) → ℝ,
      IsPrice w →
      (∑ g, ∑ k, w k (g * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ) ^ 2 ≤
        C₀ * ∑ j, (∑ k, w k (x (l * u) j * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ)

/-- (ii) OA `exists_logarithmic_placement`, Cloud.lean l.83–89, with hypotheses
`price : PriceZero`, `large`, `symm`, `rows`, `scalar` and the threshold `s/(10000(e+3))`. -/
def LogPlacementStatement : Prop :=
  ¬ PortZero → ∀ (s e : ℕ), 10000 * (e + 3) ≤ s →
    ∀ (H : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℕ), (∀ i j, H i j = H j i) →
      (∀ i, ∑ j, H i j = 2 ^ e) →
      HasPoincareBound ℝ (normalizeArcs H (2 ^ e)) ((s : ℝ) / (10000 * (e + 3))) →
      ∃ X : Target Good, ∃ place : Fin (2 ^ s) → X.carrier,
        ((s : ℝ) / (10000 * (e + 3))) * walkEnergy (normalizeArcs H (2 ^ e)) place <
          (∑ i, ∑ j, dist (place i) (place j) ^ 2) / Fintype.card (Fin (2 ^ s))

/-- (iii) Containment, one direction only: every placement into an OA spectral target pulls
back to an AN price (referee §1; for the field: k = ℚ needs no Lemma 2.3, AlgebraicClosure ℚ
restricts to ℚ). -/
def ContainStatement : Prop :=
  ∀ (X : Target Good) (Y : Type) (p : Y → X.carrier), IsPrice (fun a b => dist (p a) (p b))

/-- (iv) Finite subsets of the real line are AN prices (AN Prop. C.3 + Lemma C.4(a) per our
b2 notes; also OA EG Thm 1.1). Needed ONLY to discharge OA's `scalar` hypothesis. -/
def LineStatement : Prop :=
  ∀ (Y : Type) (f : Y → ℝ), IsPrice (fun a b => dist (f a) (f b))

/-! ## The padded Cayley graph -/

section Graph

variable {U x}
variable {h N : ℕ} (σ : U h ≃ Fin N) (L : ℕ)

/-- Arc multiplicities: one arc `a → x_j a` for each `j`, plus `L` loops at each vertex. -/
def arcs (h : ℕ) (x : Fin (h - 1) → U h) (σ : U h ≃ Fin N) (L : ℕ) : Matrix (Fin N) (Fin N) ℕ :=
  fun i j => (∑ j' : Fin (h - 1), if j = σ (x j' * σ.symm i) then 1 else 0) + if i = j then L else 0

omit [∀ h, Fintype (U h)] in
lemma arcs_symm (hx : ∀ j, x h j * x h j = 1) (i j : Fin N) :
    arcs h (x h) σ L i j = arcs h (x h) σ L j i := by
  unfold arcs
  congr 1
  · refine Finset.sum_congr rfl fun j' _ => ?_
    have : (j = σ (x h j' * σ.symm i)) ↔ (i = σ (x h j' * σ.symm j)) := by
      constructor
      · rintro rfl; simp [← mul_assoc, hx]
      · rintro rfl; simp [← mul_assoc, hx]
    simp only [this]
  · by_cases hij : i = j <;> simp [hij, eq_comm]

omit [∀ h, Fintype (U h)] in
lemma arcs_rows (i : Fin N) : ∑ j, arcs h (x h) σ L i j = (h - 1) + L := by
  unfold arcs
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp

/-- The translation of F.6 into OA's normalisation for one placement. -/
lemma core {Z : Type} [PseudoMetricSpace Z] (C₀ e : ℕ → ℝ) (hC : 0 ≤ C₀ h)
    (hcard : Fintype.card (U h) = N) (hN : 0 < N)
    (hF : ∀ w : U h → U h → ℝ, IsPrice w →
      (∑ g, ∑ k, w k (g * k) ^ 2) / (Fintype.card (U h) : ℝ) ^ 2 ≤
        C₀ h * ∑ j, (∑ k, w k (x h j * k) ^ 2) / (Fintype.card (U h) : ℝ))
    (D : ℕ) (hD : 0 < D)
    (place : Fin N → Z) (hp : IsPrice (fun a b => dist (place (σ a)) (place (σ b)))) :
    (∑ i, ∑ j, dist (place i) (place j) ^ 2) / Fintype.card (Fin N) ≤
      (C₀ h * D) * walkEnergy (normalizeArcs (arcs h (x h) σ L) D) place := by
  have hFp := hF _ hp
  -- left side
  have hL : (∑ g, ∑ k, dist (place (σ k)) (place (σ (g * k))) ^ 2) =
      ∑ i, ∑ j, dist (place i) (place j) ^ 2 := by
    rw [Finset.sum_comm]
    have : ∀ k, (∑ g, dist (place (σ k)) (place (σ (g * k))) ^ 2) =
        ∑ b, dist (place (σ k)) (place (σ b)) ^ 2 := fun k =>
      Fintype.sum_equiv (Equiv.mulRight k) _ _ (fun _ => rfl)
    simp only [this]
    rw [← Equiv.sum_comp σ.symm]
    simp only [Equiv.apply_symm_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp σ.symm]
    simp
  -- walk energy
  have hW : (D : ℝ) * walkEnergy (normalizeArcs (arcs h (x h) σ L) D) place =
      ∑ j, ∑ k, dist (place (σ k)) (place (σ (x h j * k))) ^ 2 := by
    unfold walkEnergy normalizeArcs arcs
    rw [Finset.mul_sum]
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have : ∀ i, (D : ℝ) * ∑ j, ((((∑ j' : Fin (h - 1), if j = σ (x h j' * σ.symm i) then 1 else 0) +
        if i = j then L else 0 : ℕ) : ℝ) / D) * dist (place j) (place i) ^ 2 =
        ∑ j' : Fin (h - 1), dist (place (σ (x h j' * σ.symm i))) (place i) ^ 2 := by
      intro i
      rw [Finset.mul_sum]
      simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      have : ∀ j, (D : ℝ) * (((∑ j' : Fin (h - 1), if j = σ (x h j' * σ.symm i) then (1 : ℝ) else 0) +
          if i = j then (L : ℝ) else 0) / D * dist (place j) (place i) ^ 2) =
          (∑ j' : Fin (h - 1), if j = σ (x h j' * σ.symm i) then dist (place j) (place i) ^ 2 else 0) +
          (if i = j then (L : ℝ) * dist (place j) (place i) ^ 2 else 0) := by
        intro j
        field_simp
        rw [add_mul, Finset.sum_mul]
        congr 1
        · refine Finset.sum_congr rfl fun j' _ => ?_
          split_ifs <;> try simp
        · split_ifs <;> simp [mul_comm]
      simp only [this, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      simp
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [dist_comm]
  rw [hL, ← Finset.sum_div, ← hW] at hFp
  have hn : (0 : ℝ) < Fintype.card (U h) := by rw [hcard]; exact_mod_cast hN
  rw [Fintype.card_fin]
  have hc : (Fintype.card (U h) : ℝ) = N := by exact_mod_cast hcard
  rw [hc] at hFp hn
  set Q := ∑ i, ∑ j, dist (place i) (place j) ^ 2
  set WE := walkEnergy (normalizeArcs (arcs h (x h) σ L) D) place
  rw [div_le_iff₀ (by positivity)] at hFp
  rw [div_le_iff₀ hn]
  calc Q ≤ C₀ h * ((D : ℝ) * WE / (N : ℝ)) * (N : ℝ) ^ 2 := hFp
    _ = C₀ h * D * WE * (N : ℝ) := by field_simp

end Graph

omit [∀ h, Fintype (U h)] in
lemma walkEnergy_nonneg {ι Z : Type} [Fintype ι] [PseudoMetricSpace Z] (M : Matrix ι ι ℕ) (D : ℕ)
    (p : ι → Z) : 0 ≤ walkEnergy (normalizeArcs M D) p := by
  unfold walkEnergy normalizeArcs
  positivity

/-! ## Theorem A -/

/-- **Theorem A (skeleton).** Contracting ⇒ PortZero, from (i) F.6, (ii) OA's logarithmic
placement theorem, (iii) containment OA-target ⇒ AN-price, (iv) lines are AN prices, and two
facts about U_h(F₂): its order is `2^{h(h−1)/2}` and the generators are involutions. -/
theorem theorem_A
    (F6 : F6Statement U x IsPrice Contracting)
    (LP : LogPlacementStatement Good PortZero)
    (contain : ContainStatement Good IsPrice)
    (line : LineStatement IsPrice)
    (card_U : ∀ h, Fintype.card (U h) = 2 ^ ordExp h)
    (x_invol : ∀ h j, x h j * x h j = 1) :
    Contracting → PortZero := by
  intro hK
  by_contra hP
  obtain ⟨u, hu, C₀, hC, hF⟩ := F6 hK
  obtain ⟨l, hl, hlarge, hbeats⟩ := exists_good_multiple C₀ hC u (by omega)
  set h := l * u with hh
  have h2 : 2 ≤ h := by rw [hh]; nlinarith
  set s := ordExp h
  set e := degExp h
  let σ : U h ≃ Fin (2 ^ s) := Fintype.equivFinOfCardEq (card_U h)
  let L := 2 ^ e - (h - 1)
  let H := arcs h (x h) σ L
  have hrows : ∀ i, ∑ j, H i j = 2 ^ e := by
    intro i
    have := degExp_lt h
    show ∑ j, arcs h (x h) σ (2 ^ e - (h - 1)) i j = 2 ^ e
    rw [arcs_rows]; exact Nat.add_sub_cancel' this.le
  have hsymm : ∀ i j, H i j = H j i := arcs_symm σ L (x_invol h)
  have hN : 0 < 2 ^ s := by positivity
  have hD : 0 < 2 ^ e := by positivity
  have hcore := fun (Z : Type) [PseudoMetricSpace Z] (place : Fin (2 ^ s) → Z)
      (hp : IsPrice (fun a b => dist (place (σ a)) (place (σ b)))) =>
    core (U := U) (x := x) (IsPrice := IsPrice) σ L (fun _ => C₀) hC (card_U h) hN
      hF (2 ^ e) hD place hp
  set thr : ℝ := (s : ℝ) / (10000 * (e + 3))
  have hupgrade : ∀ (Z : Type) [PseudoMetricSpace Z] (place : Fin (2 ^ s) → Z),
      IsPrice (fun a b => dist (place (σ a)) (place (σ b))) →
      (∑ i, ∑ j, dist (place i) (place j) ^ 2) / Fintype.card (Fin (2 ^ s)) ≤
        thr * walkEnergy (normalizeArcs H (2 ^ e)) place := by
    intro Z _ place hp
    refine (hcore Z place hp).trans ?_
    have := walkEnergy_nonneg (U := U) H (2 ^ e) place
    push_cast
    exact mul_le_mul_of_nonneg_right hbeats this
  have hscalar : HasPoincareBound ℝ (normalizeArcs H (2 ^ e)) thr := fun y =>
    hupgrade ℝ y (line (U h) (fun a => y (σ a)))
  obtain ⟨X, place, hlt⟩ := LP hP s e hlarge H hsymm hrows hscalar
  have := hupgrade X.carrier place (contain X (U h) (fun a => place (σ a)))
  linarith

end PortsLean.ThmA
