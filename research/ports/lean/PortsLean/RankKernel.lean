import Mathlib

/-!
# Rank kernel and the spectral inequality (`research/ports/middle/notes.md` §4)

(a) `card_ker_mul_two_pow_rank`: for `c : Matrix (Fin m) (Fin n) (ZMod 2)`,
    `#{x | c x = 0} · 2^{rank c} = 2^n`.
(b) `rankKernel_psd`: `Σ_{i,j} w_i w_j 2^{-rank(a_i - a_j)} ≥ 0`, and the `k`-th power version
    `rankKernel_pow_psd`; both through an explicit feature map (`rankKernel_eq_feature`).
(c) `spectral_ineq`: abstract form of Proposition S, and `propS_rank` / `propS_rank_pow`, the
    statement for rank placements.

Normalisation (as in the notes): `E_pairs w = n⁻² Σ_{u,v} w(u,v)` (ordered pairs, `u = v` included),
`E_edges w = n⁻¹ Σ_{u,v} A_{uv} w(u,v)` with `A` the normalised adjacency matrix.
-/

namespace PortsLean.RankKernel

open Finset Matrix

/-! ## (a) Kernel cardinality -/

theorem card_ker_mul_two_pow_rank {m n : ℕ} (c : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (univ.filter (fun x : Fin n → ZMod 2 => c.mulVec x = 0)).card * 2 ^ c.rank = 2 ^ n := by
  classical
  have hrn := LinearMap.finrank_range_add_finrank_ker c.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  have hcard : (univ.filter (fun x : Fin n → ZMod 2 => c.mulVec x = 0)).card
      = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker c.mulVecLin) := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker c.mulVecLin)
    rw [ZMod.card] at h1
    rw [← h1, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp [LinearMap.mem_ker]))
  rw [hcard, ← pow_add, Matrix.rank, add_comm, hrn]

/-! ## (b) Feature-map kernels, the rank kernel, and positivity -/

/-- The kernel `K(u,v) = ⟨φ_u, φ_v⟩` of a feature map `φ : V → (ι → ℝ)` (finite `ι`). This is the
form of "positive semidefinite" used below. -/
def featK {V ι : Type*} [Fintype ι] (φ : V → ι → ℝ) (u v : V) : ℝ := ∑ c, φ u c * φ v c

/-- Feature-map kernels are positive semidefinite, for every finite family of points and weights. -/
theorem featK_psd {V ι J : Type*} [Fintype ι] (φ : V → ι → ℝ) (s : Finset J) (p : J → V)
    (w : J → ℝ) : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * featK φ (p i) (p j) := by
  have h : ∑ i ∈ s, ∑ j ∈ s, w i * w j * featK φ (p i) (p j)
      = ∑ c, (∑ i ∈ s, w i * φ (p i) c) ^ 2 := by
    calc ∑ i ∈ s, ∑ j ∈ s, w i * w j * featK φ (p i) (p j)
        = ∑ i ∈ s, ∑ j ∈ s, ∑ c, (w i * φ (p i) c) * (w j * φ (p j) c) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [featK, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ = ∑ i ∈ s, ∑ c, ∑ j ∈ s, (w i * φ (p i) c) * (w j * φ (p j) c) := by
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ c, ∑ i ∈ s, ∑ j ∈ s, (w i * φ (p i) c) * (w j * φ (p j) c) := Finset.sum_comm
      _ = ∑ c, (∑ i ∈ s, w i * φ (p i) c) ^ 2 := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [sq, Finset.sum_mul_sum]
  rw [h]
  exact Finset.sum_nonneg fun c _ => sq_nonneg _

/-- Product features: the `k`-th Schur power of a feature-map kernel is again one. -/
def featPow {V ι : Type*} (φ : V → ι → ℝ) (k : ℕ) : V → (Fin k → ι) → ℝ :=
  fun u p => ∏ l, φ u (p l)

theorem featK_featPow {V ι : Type*} [Fintype ι] [DecidableEq ι] (φ : V → ι → ℝ) (k : ℕ)
    (u v : V) : featK (featPow φ k) u v = featK φ u v ^ k := by
  unfold featK featPow
  calc ∑ p : Fin k → ι, (∏ l, φ u (p l)) * ∏ l, φ v (p l)
      = ∑ p : Fin k → ι, ∏ l, (φ u (p l) * φ v (p l)) := by
        exact Finset.sum_congr rfl fun p _ => (Finset.prod_mul_distrib).symm
    _ = ∏ _l : Fin k, ∑ c, φ u c * φ v c :=
        (Fintype.prod_sum (fun (_ : Fin k) (c : ι) => φ u c * φ v c)).symm
    _ = (∑ c, φ u c * φ v c) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Feature map of the rank kernel: index `(x, y)`, value `2^{-n/2}·1[a x = y]`. -/
noncomputable def rankFeat {m n : ℕ} (a : Matrix (Fin m) (Fin n) (ZMod 2))
    (p : (Fin n → ZMod 2) × (Fin m → ZMod 2)) : ℝ :=
  if a.mulVec p.1 = p.2 then Real.sqrt (((2 : ℝ) ^ n)⁻¹) else 0

/-- `2^{-rank(a-b)} = 2^{-n}·#{x | a x = b x} = ⟨φ_a, φ_b⟩`. -/
theorem rankKernel_eq_feature {m n : ℕ} (a b : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (2 : ℝ) ^ (-((a - b).rank : ℤ)) = featK rankFeat a b := by
  classical
  set r : ℝ := Real.sqrt (((2 : ℝ) ^ n)⁻¹) with hr
  have hrr : r * r = ((2 : ℝ) ^ n)⁻¹ := Real.mul_self_sqrt (by positivity)
  have hinner : ∀ x : Fin n → ZMod 2,
      ∑ y : Fin m → ZMod 2, rankFeat a (x, y) * rankFeat b (x, y)
        = if a.mulVec x = b.mulVec x then r * r else 0 := by
    intro x
    simp only [rankFeat, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true, mul_ite, mul_zero]
    by_cases h : a.mulVec x = b.mulVec x
    · simp only [h, ite_true]; rfl
    · simp only [h, Ne.symm h, ite_false]
  have hsum : featK rankFeat a b
      = r * r * ((univ.filter (fun x : Fin n → ZMod 2 => (a - b).mulVec x = 0)).card : ℝ) := by
    unfold featK
    rw [Fintype.sum_prod_type]
    simp only [hinner]
    rw [← Finset.sum_boole, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : (a.mulVec x = b.mulVec x) ↔ ((a - b).mulVec x = 0) := by
      rw [Matrix.sub_mulVec, sub_eq_zero]
    by_cases h : a.mulVec x = b.mulVec x
    · simp [h, this.mp h]
    · have h' : ¬ (a - b).mulVec x = 0 := fun h' => h (this.mpr h')
      simp [h, h']
  have hcard := card_ker_mul_two_pow_rank (a - b)
  have hcardR : ((univ.filter (fun x : Fin n → ZMod 2 => (a - b).mulVec x = 0)).card : ℝ)
      * (2 : ℝ) ^ (a - b).rank = (2 : ℝ) ^ n := by exact_mod_cast hcard
  rw [hsum, hrr, _root_.zpow_neg, zpow_natCast]
  have h2 : (0 : ℝ) < 2 ^ (a - b).rank := by positivity
  have h3 : (0 : ℝ) < 2 ^ n := by positivity
  field_simp
  linarith [hcardR]

/-- **Lemma K, k = 1.** `Σ_{i,j} w_i w_j 2^{-rank(a_i - a_j)} ≥ 0`. -/
theorem rankKernel_psd {m n : ℕ} {J : Type*} (s : Finset J)
    (a : J → Matrix (Fin m) (Fin n) (ZMod 2)) (w : J → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * (2 : ℝ) ^ (-((a i - a j).rank : ℤ)) := by
  simp only [rankKernel_eq_feature]
  exact featK_psd rankFeat s a w

/-- `2^{-k·rank(a-b)}` as a feature-map kernel. -/
theorem rankKernel_pow_eq_feature {m n : ℕ} (k : ℕ) (a b : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (2 : ℝ) ^ (-((k * (a - b).rank : ℕ) : ℤ)) = featK (featPow rankFeat k) a b := by
  classical
  rw [featK_featPow, ← rankKernel_eq_feature, ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast
  ring

/-- **Lemma K, every integer k ≥ 0.** `Σ_{i,j} w_i w_j 2^{-k·rank(a_i - a_j)} ≥ 0`. -/
theorem rankKernel_pow_psd {m n : ℕ} {J : Type*} (k : ℕ) (s : Finset J)
    (a : J → Matrix (Fin m) (Fin n) (ZMod 2)) (w : J → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * (2 : ℝ) ^ (-((k * (a i - a j).rank : ℕ) : ℤ)) := by
  classical
  simp only [rankKernel_pow_eq_feature]
  exact featK_psd (featPow rankFeat k) s a w

/-! ## (c) The spectral inequality -/

/-- One coordinate of the feature map. With `N = |V|` and `s = Σ g`:
`Σ_{u,v} A_{uv} g_u g_v ≤ λ (Σ g² − s²/N) + s²/N`. -/
theorem coord_bound {V : Type*} [Fintype V] [Nonempty V] (A : V → V → ℝ)
    (hrow : ∀ u, ∑ v, A u v = 1) (hcol : ∀ v, ∑ u, A u v = 1) (lam : ℝ)
    (hgap : ∀ g : V → ℝ, ∑ u, g u = 0 → ∑ u, ∑ v, A u v * g u * g v ≤ lam * ∑ u, g u ^ 2)
    (g : V → ℝ) :
    ∑ u, ∑ v, A u v * g u * g v
      ≤ lam * (∑ u, g u ^ 2 - (∑ u, g u) ^ 2 / (Fintype.card V : ℝ))
        + (∑ u, g u) ^ 2 / (Fintype.card V : ℝ) := by
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set S := ∑ u, g u with hS
  set m := S / N with hm
  set h : V → ℝ := fun u => g u - m with hh
  have hg : ∀ u, g u = h u + m := fun u => by simp [hh]
  have hsumh : ∑ u, h u = 0 := by
    simp only [hh, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hS, ← hN, hm]
    field_simp
    ring
  have t1 : ∑ u, ∑ v, A u v * h u = 0 := by
    calc ∑ u, ∑ v, A u v * h u = ∑ u, h u * ∑ v, A u v := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ = 0 := by simp only [hrow, mul_one]; exact hsumh
  have t2 : ∑ u, ∑ v, A u v * h v = 0 := by
    rw [Finset.sum_comm]
    calc ∑ v, ∑ u, A u v * h v = ∑ v, h v * ∑ u, A u v := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun u _ => by ring
      _ = 0 := by simp only [hcol, mul_one]; exact hsumh
  have t3 : ∑ u, ∑ v, A u v = N := by
    simp only [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact hN.symm
  have E1 : ∑ u, ∑ v, A u v * g u * g v
      = ∑ u, ∑ v, A u v * h u * h v + m ^ 2 * N := by
    calc ∑ u, ∑ v, A u v * g u * g v
        = ∑ u, ∑ v, (A u v * h u * h v + m * (A u v * h u) + m * (A u v * h v)
            + m ^ 2 * A u v) := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
          rw [hg u, hg v]; ring
      _ = ∑ u, ∑ v, A u v * h u * h v + m * ∑ u, ∑ v, A u v * h u
            + m * ∑ u, ∑ v, A u v * h v + m ^ 2 * ∑ u, ∑ v, A u v := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ u, ∑ v, A u v * h u * h v + m ^ 2 * N := by rw [t1, t2, t3]; ring
  have E2 : ∑ u, g u ^ 2 = ∑ u, h u ^ 2 + m ^ 2 * N := by
    calc ∑ u, g u ^ 2 = ∑ u, (h u ^ 2 + 2 * m * h u + m ^ 2) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [hg u]; ring
      _ = ∑ u, h u ^ 2 + 2 * m * ∑ u, h u + m ^ 2 * N := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          ring
      _ = ∑ u, h u ^ 2 + m ^ 2 * N := by rw [hsumh]; ring
  have hmN : m ^ 2 * N = S ^ 2 / N := by
    rw [hm]; field_simp
  have hb := hgap h hsumh
  rw [E1, E2, ← hmN]
  have : ∑ u, ∑ v, A u v * h u * h v ≤ lam * ∑ u, h u ^ 2 := hb
  linarith

/-- **Proposition S, abstract form.** `A` is a real matrix on a finite set `V` with all row and
column sums `1` (e.g. the normalised adjacency matrix of a regular multigraph), and
`⟨g, A g⟩ ≤ λ ⟨g, g⟩` for every `g ⊥ 1`. Let `K(u,v) = ⟨φ_u, φ_v⟩` be a feature-map kernel with
`K(u,u) = 1`. Then, with `N = |V|`,
`N⁻¹ Σ_{u,v} A_{uv} K(u,v) ≤ λ + (1 − λ) · N⁻² Σ_{u,v} K(u,v)`,
i.e. `E_edges K ≤ λ + (1 − λ) E_pairs K` in the normalisation of the notes. -/
theorem spectral_ineq {V ι : Type*} [Fintype V] [Nonempty V] [Fintype ι] (A : V → V → ℝ)
    (hrow : ∀ u, ∑ v, A u v = 1) (hcol : ∀ v, ∑ u, A u v = 1) (lam : ℝ)
    (hgap : ∀ g : V → ℝ, ∑ u, g u = 0 → ∑ u, ∑ v, A u v * g u * g v ≤ lam * ∑ u, g u ^ 2)
    (φ : V → ι → ℝ) (hdiag : ∀ u, featK φ u u = 1) :
    (1 / (Fintype.card V : ℝ)) * ∑ u, ∑ v, A u v * featK φ u v
      ≤ lam + (1 - lam) * ((1 / (Fintype.card V : ℝ) ^ 2) * ∑ u, ∑ v, featK φ u v) := by
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set s : ι → ℝ := fun c => ∑ u, φ u c with hs
  have hedge : ∑ u, ∑ v, A u v * featK φ u v = ∑ c, ∑ u, ∑ v, A u v * φ u c * φ v c := by
    calc ∑ u, ∑ v, A u v * featK φ u v = ∑ u, ∑ v, ∑ c, A u v * φ u c * φ v c := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
          rw [featK, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ = ∑ u, ∑ c, ∑ v, A u v * φ u c * φ v c :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ c, ∑ u, ∑ v, A u v * φ u c * φ v c := Finset.sum_comm
  have hpair : ∑ u, ∑ v, featK φ u v = ∑ c, s c ^ 2 := by
    calc ∑ u, ∑ v, featK φ u v = ∑ u, ∑ v, ∑ c, φ u c * φ v c := rfl
      _ = ∑ u, ∑ c, ∑ v, φ u c * φ v c := Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ c, ∑ u, ∑ v, φ u c * φ v c := Finset.sum_comm
      _ = ∑ c, s c ^ 2 := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hs, sq, Finset.sum_mul_sum]
  have hdiagsum : ∑ c, ∑ u, φ u c ^ 2 = N := by
    rw [Finset.sum_comm]
    have : ∀ u, ∑ c, φ u c ^ 2 = 1 := fun u => by
      rw [← hdiag u, featK]; exact Finset.sum_congr rfl fun c _ => sq _
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hN]
  have hle : ∑ c, ∑ u, ∑ v, A u v * φ u c * φ v c
      ≤ ∑ c, (lam * (∑ u, φ u c ^ 2 - s c ^ 2 / N) + s c ^ 2 / N) :=
    Finset.sum_le_sum fun c _ => coord_bound A hrow hcol lam hgap (fun u => φ u c)
  have hrhs : ∑ c, (lam * (∑ u, φ u c ^ 2 - s c ^ 2 / N) + s c ^ 2 / N)
      = lam * (N - (∑ c, s c ^ 2) / N) + (∑ c, s c ^ 2) / N := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      ← Finset.sum_div, hdiagsum]
  rw [hedge, hpair]
  set P := ∑ c, s c ^ 2
  have key : ∑ c, ∑ u, ∑ v, A u v * φ u c * φ v c ≤ lam * (N - P / N) + P / N := hrhs ▸ hle
  calc (1 / N) * ∑ c, ∑ u, ∑ v, A u v * φ u c * φ v c
      ≤ (1 / N) * (lam * (N - P / N) + P / N) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = lam + (1 - lam) * ((1 / N ^ 2) * P) := by field_simp; ring

/-- **Proposition S for rank placements.** For `f : V → Mat_{m×n}(F₂)` and `A` as in
`spectral_ineq`: `E_edges 2^{-D_f} ≤ λ + (1 − λ) E_pairs 2^{-D_f}`, `D_f(u,v) = rank(f u − f v)`. -/
theorem propS_rank {V : Type*} [Fintype V] [Nonempty V] {m n : ℕ} (A : V → V → ℝ)
    (hrow : ∀ u, ∑ v, A u v = 1) (hcol : ∀ v, ∑ u, A u v = 1) (lam : ℝ)
    (hgap : ∀ g : V → ℝ, ∑ u, g u = 0 → ∑ u, ∑ v, A u v * g u * g v ≤ lam * ∑ u, g u ^ 2)
    (f : V → Matrix (Fin m) (Fin n) (ZMod 2)) :
    (1 / (Fintype.card V : ℝ)) * ∑ u, ∑ v, A u v * (2 : ℝ) ^ (-((f u - f v).rank : ℤ))
      ≤ lam + (1 - lam) * ((1 / (Fintype.card V : ℝ) ^ 2) *
          ∑ u, ∑ v, (2 : ℝ) ^ (-((f u - f v).rank : ℤ))) := by
  simp only [rankKernel_eq_feature]
  refine spectral_ineq A hrow hcol lam hgap (fun u => rankFeat (f u)) (fun u => ?_)
  show featK rankFeat (f u) (f u) = 1
  rw [← rankKernel_eq_feature, sub_self, Matrix.rank_zero]
  simp

/-- **Proposition S, k-th power.** Same with `2^{-k·D_f}`. -/
theorem propS_rank_pow {V : Type*} [Fintype V] [Nonempty V] {m n : ℕ} (k : ℕ) (A : V → V → ℝ)
    (hrow : ∀ u, ∑ v, A u v = 1) (hcol : ∀ v, ∑ u, A u v = 1) (lam : ℝ)
    (hgap : ∀ g : V → ℝ, ∑ u, g u = 0 → ∑ u, ∑ v, A u v * g u * g v ≤ lam * ∑ u, g u ^ 2)
    (f : V → Matrix (Fin m) (Fin n) (ZMod 2)) :
    (1 / (Fintype.card V : ℝ)) * ∑ u, ∑ v, A u v * (2 : ℝ) ^ (-((k * (f u - f v).rank : ℕ) : ℤ))
      ≤ lam + (1 - lam) * ((1 / (Fintype.card V : ℝ) ^ 2) *
          ∑ u, ∑ v, (2 : ℝ) ^ (-((k * (f u - f v).rank : ℕ) : ℤ))) := by
  classical
  simp only [rankKernel_pow_eq_feature]
  refine spectral_ineq A hrow hcol lam hgap (fun u => featPow rankFeat k (f u)) (fun u => ?_)
  show featK (featPow rankFeat k) (f u) (f u) = 1
  rw [← rankKernel_pow_eq_feature, sub_self, Matrix.rank_zero]
  simp

end PortsLean.RankKernel
