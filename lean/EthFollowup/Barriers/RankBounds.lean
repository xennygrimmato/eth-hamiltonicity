/-
# Rank bounds behind the permanent barriers

Sources (all in `research/permanent/` unless stated):

* `barrier.md` Lemma 3.1 (cut lemma): "`value(N) = Σ_{θ∈Θ} F_L(θ) F_R(θ)` … So whenever the data of
  the nodes in L is a function of a part A_L of the input and the data of the nodes in R of a part
  A_R, the matrix M[A_L, A_R] := value(N(A)) has rank ≤ 2^{w(L,R)} as a matrix indexed by
  (A_L, A_R) (it is Σ_θ u_θ v_θ^T with u_θ = F_L(·,θ), v_θ = F_R(·,θ))."
  Formalised in its rank form: `rank_le_card_of_eq_sum_mul`, `rank_le_two_pow_of_eq_sum_mul`
  (the network-level exchange of sums is not restated; the input is the factorisation).
* `barrier.md` proof of Lemma 3.2: "A bilinear form Σ_S u_S ⊗ v_S with both families independent
  has rank exactly the number of terms (it is UV^T with U, V of full column rank)."
  → `rank_eq_card_of_linearIndependent`.
* `barrier.md` Theorem 6.2 Step 2 / `vertex-local-bound.md` Theorem 3.1: "rank
  Σ_i C(k,i)C(k′,i) = C(k + k′, k) (Vandermonde)" → `sum_choose_mul_choose`.
* `barrier.md` Theorem 6.1 (Model R): "`U ≥ Σ_{j=1}^{t} log C(n, |V_j|) ≥ n · log(n/s)`", with the
  proof steps "2^{w_j} ≥ rank M_{V_j} = C(n, |V_j|)", "Σ_j w_j ≤ Σ_{(a,b): a≠b} c_{a,b} = U" and
  "C(n,k) ≥ (n/k)^k gives log C(n,k_j) ≥ k_j log(n/k_j) ≥ k_j log(n/s), and Σ_j k_j = n".
  → `sum_crossing_le_total`, `modelR_bound`, `pow_div_le_choose`, `modelR_bound_nlogn`.
  The rank input `C(n,k_j) ≤ 2^{w_j}` is a hypothesis (it is Lemma 3.1 + Lemma 3.2, the latter
  proved in `RowCut.lean`).
* `vertex-local-bound.md` Theorem 3.1 (tree skeletons): "`U ≥ 2 · Σ_{e ∈ E(T)} log C(k_e + k′_e,
  k_e)`" — the same summation argument with "U = 2 Σ_e c_e" → `treeSkeleton_bound`.
* `clique-evaluation.md` §4.3: "Subadditivity: 2^{2λ} = rank_row F ≤ Σ_s 2^{c^row_s}, so some s_r
  has c^row_{s_r} ≥ 2λ − o(λ)" → `rank_sum_le`, `exists_rank_ge_of_sum`, `exists_logb_rank_ge`.
* `pieces.md` (2.1): "Contract y with β and u with a. For F this gives ⟨β|a⟩·I_N on (x,v). For any
  piece T the contracted x|v matrix has rank ≤ min(rank T, OSR T). So Σ_i min(r_i, o_i) ≥ N. Hence
  some piece has both r_i and o_i ≥ N/|I|" → `pieces_trivial_lower_bound`,
  `pieces_exists_large_piece`.
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Vandermonde

set_option linter.unusedSectionVars false

namespace EthFollowup.Barriers.Rank

open Matrix Finset

variable {K : Type*} [Field K]

/-! ### The cut lemma in rank form -/

/-- `barrier.md` Lemma 3.1, rank form: a matrix `M[x,y] = Σ_{θ∈Θ} F(x,θ) G(θ,y)` has rank
`≤ |Θ|`. -/
theorem rank_le_card_of_eq_sum_mul {X Y Θ : Type*} [Fintype Y] [Fintype Θ]
    (M : Matrix X Y K) (F : X → Θ → K) (G : Θ → Y → K) (h : ∀ x y, M x y = ∑ θ, F x θ * G θ y) :
    M.rank ≤ Fintype.card Θ := by
  have hM : M = Matrix.of F * Matrix.of G := by
    ext x y; simp [Matrix.mul_apply, h]
  rw [hM]
  exact (rank_mul_le_left _ _).trans (rank_le_card_width _)

/-- Finset-indexed version of the cut lemma. -/
theorem rank_le_card_of_eq_sum_mul' {X Y Θ : Type*} [Fintype Y] (s : Finset Θ)
    (M : Matrix X Y K) (F : X → Θ → K) (G : Θ → Y → K)
    (h : ∀ x y, M x y = ∑ θ ∈ s, F x θ * G θ y) : M.rank ≤ s.card := by
  have := rank_le_card_of_eq_sum_mul (Θ := s) M (fun x θ => F x θ) (fun θ y => G θ y)
    (fun x y => by rw [h, ← Finset.sum_coe_sort s])
  simpa using this

/-- `barrier.md` Lemma 3.1 with `Θ = {0,1}^w` (the `w` crossing bits): rank `≤ 2^w`. -/
theorem rank_le_two_pow_of_eq_sum_mul {X Y : Type*} [Fintype Y] (w : ℕ)
    (M : Matrix X Y K) (F : X → (Fin w → Bool) → K) (G : (Fin w → Bool) → Y → K)
    (h : ∀ x y, M x y = ∑ θ, F x θ * G θ y) : M.rank ≤ 2 ^ w := by
  simpa using rank_le_card_of_eq_sum_mul M F G h

/-- The crossing-bit set of `barrier.md` Lemma 3.1, `Θ = Π_{p} {0,1}^{c_p}`, has `2^{Σ_p c_p}`
elements. -/
theorem card_crossingBits {P : Type*} [Fintype P] [DecidableEq P] (c : P → ℕ) :
    Fintype.card ((p : P) → Fin (c p) → Bool) = 2 ^ ∑ p, c p := by
  simp [Fintype.card_pi, Finset.prod_pow_eq_pow_sum]

/-! ### Rank of a bilinear form with independent families -/

/-- `barrier.md` proof of Lemma 3.2: `Σ_{t∈T} u_t ⊗ v_t` with both families linearly
independent has rank exactly `|T|`. -/
theorem rank_eq_card_of_linearIndependent {T X Y : Type*} [Fintype T] [Fintype X] [Fintype Y]
    [DecidableEq T] (u : T → X → K) (v : T → Y → K) (hu : LinearIndependent K u)
    (hv : LinearIndependent K v) (M : Matrix X Y K) (hM : ∀ x y, M x y = ∑ t, u t x * v t y) :
    M.rank = Fintype.card T := by
  set U : Matrix X T K := Matrix.of fun x t => u t x
  set V : Matrix T Y K := Matrix.of v
  have hMUV : M = U * V := by ext x y; simp [U, V, Matrix.mul_apply, hM]
  have hinj : Function.Injective U.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [Fintype.linearIndependent_iff] at hu
    funext t
    refine hu c (funext fun x => ?_) t
    have := congrFun hc x
    simpa [U, Matrix.mulVec, dotProduct, mul_comm] using this
  have hr : V.rank = Fintype.card T := LinearIndependent.rank_matrix hv
  rw [hMUV, ← hr, Matrix.rank, Matrix.rank, Matrix.mulVecLin_mul, LinearMap.range_comp]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)).symm

/-- Chu–Vandermonde in the form used in `barrier.md` Thm 6.2 and `vertex-local-bound.md`
Thm 3.1: `Σ_i C(k,i) C(k′,i) = C(k + k′, k)`. -/
theorem sum_choose_mul_choose (k k' : ℕ) :
    ∑ i ∈ range (k + 1), k.choose i * k'.choose i = (k + k').choose k := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => k.choose i * k'.choose j)]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i < k + 1 := Finset.mem_range.1 hi
  rw [Nat.choose_symm_of_eq_add (by omega : k = (k + 1 - 1 - i) + (k - (k + 1 - 1 - i)))]
  congr 2; omega

/-! ### Rank subadditivity -/

/-- `rank (A + B) ≤ rank A + rank B`. -/
theorem rank_add_le {X Y : Type*} [Fintype Y] (A B : Matrix X Y K) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- `rank (Σ_{s∈I} A_s) ≤ Σ_{s∈I} rank A_s`. -/
theorem rank_sum_le {X Y ι : Type*} [Fintype Y] (I : Finset ι) (A : ι → Matrix X Y K) :
    (∑ s ∈ I, A s).rank ≤ ∑ s ∈ I, (A s).rank := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert a I ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- Pigeonhole: if `N ≤ Σ_{i∈I} f i` then some `i ∈ I` has `N ≤ |I| · f i`. -/
theorem exists_le_card_mul_of_le_sum {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (f : ι → ℕ)
    (N : ℕ) (h : N ≤ ∑ i ∈ I, f i) : ∃ i ∈ I, N ≤ I.card * f i := by
  by_contra hcon
  push Not at hcon
  have h2 : I.card * ∑ s ∈ I, f s < I.card * N := by
    rw [Finset.mul_sum]
    calc ∑ s ∈ I, I.card * f s < ∑ _s ∈ I, N := Finset.sum_lt_sum_of_nonempty hI hcon
      _ = I.card * N := by simp
  have h3 := Nat.mul_le_mul_left I.card h
  omega

/-- Pigeonhole on subadditivity (`clique-evaluation.md` §4.3): some summand has
`|I| · rank A_s ≥ rank (Σ_s A_s)`. -/
theorem exists_rank_ge_of_sum {X Y ι : Type*} [Fintype Y] (I : Finset ι) (hI : I.Nonempty)
    (A : ι → Matrix X Y K) : ∃ s ∈ I, (∑ t ∈ I, A t).rank ≤ I.card * (A s).rank :=
  exists_le_card_mul_of_le_sum I hI _ _ (rank_sum_le I A)

/-- `clique-evaluation.md` §4.3: if `rank (Σ_{s∈I} A_s) = 2^{2λ}` then some piece has
`c_s := log₂ rank A_s ≥ 2λ − log₂ |I|`. -/
theorem exists_logb_rank_ge {X Y ι : Type*} [Fintype Y] (I : Finset ι) (hI : I.Nonempty)
    (A : ι → Matrix X Y K) (lam : ℕ) (hF : (∑ t ∈ I, A t).rank = 2 ^ (2 * lam)) :
    ∃ s ∈ I, (2 * lam : ℝ) - Real.logb 2 I.card ≤ Real.logb 2 (A s).rank := by
  obtain ⟨s, hs, hle⟩ := exists_rank_ge_of_sum I hI A
  refine ⟨s, hs, ?_⟩
  rw [hF] at hle
  have hcard : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
  have hpos : 0 < (A s).rank := by
    rcases Nat.eq_zero_or_pos (A s).rank with h | h
    · rw [h, mul_zero] at hle; exact absurd hle (Nat.not_le.2 (by positivity))
    · exact h
  have hle' : ((2 : ℝ) ^ (2 * lam)) ≤ (I.card : ℝ) * (A s).rank := by exact_mod_cast hle
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hle'
  rw [Real.logb_mul hcard.ne' (by exact_mod_cast hpos.ne'), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)] at this
  push_cast at this
  linarith

/-! ### The summation step of `barrier.md` Thm 6.1 and `vertex-local-bound.md` Thm 3.1 -/

/-- If `r_j ≤ 2^{w_j}` for each `j`, then `Σ_j log₂ r_j ≤ Σ_j w_j`. -/
theorem sum_logb_le_of_le_two_pow {J : Type*} (s : Finset J) (r w : J → ℕ)
    (h : ∀ j ∈ s, r j ≤ 2 ^ w j) : ∑ j ∈ s, Real.logb 2 (r j) ≤ ∑ j ∈ s, (w j : ℝ) := by
  refine Finset.sum_le_sum fun j hj => ?_
  rcases Nat.eq_zero_or_pos (r j) with h0 | hpos
  · simp [h0]
  · have : (r j : ℝ) ≤ (2 : ℝ) ^ w j := by exact_mod_cast h j hj
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast hpos) this
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this

/-- The pair count of `barrier.md` Thm 6.1: with nodes `a` assigned to clusters `cl a : Option J`
(`none` = routing node) and crossing bits `c a b`, put
`w_j := Σ_{a : cl a = j, b : cl b ≠ j} c a b`. Then `Σ_j w_j ≤ U := Σ_{a ≠ b} c a b`
("the ordered pair (a,b) with j(a) = j, j(b) ≠ j (or b routing) is counted in w_j and in no other
w_{j′}"). -/
theorem sum_crossing_le_total {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
    (cl : V → Option J) (c : V → V → ℕ) (s : Finset J) :
    ∑ j ∈ s, ∑ a, ∑ b, (if cl a = some j ∧ cl b ≠ some j then c a b else 0)
      ≤ ∑ a, ∑ b, (if a ≠ b then c a b else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun b _ => ?_
  rcases hca : cl a with _ | j₀
  · simp
  · by_cases hab : a = b
    · subst hab; simp [hca]
    · simp only [Option.some.injEq, hab, ne_eq, not_false_eq_true, ite_true]
      calc ∑ j ∈ s, (if j₀ = j ∧ cl b ≠ some j then c a b else 0)
          ≤ ∑ j ∈ s, (if j₀ = j then c a b else 0) :=
            Finset.sum_le_sum fun j _ => by split_ifs <;> simp_all
        _ ≤ c a b := by rw [Finset.sum_ite_eq]; split_ifs <;> simp

/-- `barrier.md` Theorem 6.1, first inequality, abstract form: if every cluster `j` has
`C(n, k_j) ≤ 2^{w_j}` (Lemma 3.1 + Lemma 3.2) and `Σ_j w_j ≤ U`, then
`U ≥ Σ_j log₂ C(n, k_j)`. -/
theorem modelR_bound {J : Type*} (s : Finset J) (n U : ℕ) (k w : J → ℕ)
    (hrank : ∀ j ∈ s, n.choose (k j) ≤ 2 ^ w j) (hU : ∑ j ∈ s, w j ≤ U) :
    ∑ j ∈ s, Real.logb 2 (n.choose (k j)) ≤ U := by
  refine (sum_logb_le_of_le_two_pow s _ w hrank).trans ?_
  exact_mod_cast hU

/-- `(n/k)^k ≤ C(n,k)` (used in `barrier.md` Thm 6.1), in the form `n^k ≤ C(n,k) · k^k`. -/
theorem pow_le_choose_mul_pow {n k : ℕ} (hk : k ≤ n) : n ^ k ≤ n.choose k * k ^ k := by
  have e1 : n ^ k * k.factorial = ∏ i ∈ range k, (n * (k - i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  have e2 : n.descFactorial k * k ^ k = ∏ i ∈ range k, ((n - i) * k) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      ← Nat.descFactorial_eq_prod_range]
  have h1 : n ^ k * k.factorial ≤ n.descFactorial k * k ^ k := by
    rw [e1, e2]
    refine Finset.prod_le_prod fun i hi => ?_
    have hik : i * k ≤ n * i := by rw [mul_comm n i]; exact Nat.mul_le_mul_left i hk
    rw [Nat.mul_sub, Nat.sub_mul]
    exact Nat.sub_le_sub_left hik _
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  have hf : 0 < k.factorial := Nat.factorial_pos k
  refine Nat.le_of_mul_le_mul_right ?_ hf
  calc n ^ k * k.factorial ≤ k.factorial * n.choose k * k ^ k := h1
    _ = n.choose k * k ^ k * k.factorial := by ring

/-- `log₂ C(n,k) ≥ k · log₂ (n/s)` whenever `1 ≤ k ≤ s` and `k ≤ n`. -/
theorem mul_logb_le_logb_choose {n k s : ℕ} (hk1 : 1 ≤ k) (hks : k ≤ s) (hkn : k ≤ n) :
    (k : ℝ) * Real.logb 2 ((n : ℝ) / s) ≤ Real.logb 2 (n.choose k) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hk1 hkn)
  have hk : (0 : ℝ) < k := by exact_mod_cast hk1
  have hs : (0 : ℝ) < s := by exact_mod_cast (lt_of_lt_of_le hk1 hks)
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have h1 : ((n : ℝ) / k) ^ k ≤ n.choose k := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    exact_mod_cast pow_le_choose_mul_pow hkn
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
  rw [Real.logb_pow] at h2
  have h3 : Real.logb 2 ((n : ℝ) / s) ≤ Real.logb 2 ((n : ℝ) / k) := by
    refine Real.logb_le_logb_of_le (by norm_num) (by positivity) ?_
    exact div_le_div_of_nonneg_left hn.le hk (by exact_mod_cast hks)
  calc (k : ℝ) * Real.logb 2 ((n : ℝ) / s) ≤ k * Real.logb 2 ((n : ℝ) / k) :=
        mul_le_mul_of_nonneg_left h3 hk.le
    _ ≤ _ := h2

/-- `barrier.md` Theorem 6.1, both inequalities: clusters `j ∈ cls` with `k_j` rows each,
`1 ≤ k_j ≤ s`, `Σ_j k_j = n` (every row lies in a cluster), the rank input
`C(n, k_j) ≤ 2^{w_j}` and the pair count `Σ_j w_j ≤ U` give
`U ≥ Σ_j log₂ C(n, k_j) ≥ n · log₂ (n/s)`. -/
theorem modelR_bound_nlogn {J : Type*} (cls : Finset J) (n s U : ℕ) (k w : J → ℕ)
    (hk1 : ∀ j ∈ cls, 1 ≤ k j) (hks : ∀ j ∈ cls, k j ≤ s) (hsum : ∑ j ∈ cls, k j = n)
    (hrank : ∀ j ∈ cls, n.choose (k j) ≤ 2 ^ w j) (hU : ∑ j ∈ cls, w j ≤ U) :
    (n : ℝ) * Real.logb 2 ((n : ℝ) / s) ≤ ∑ j ∈ cls, Real.logb 2 (n.choose (k j)) ∧
      ∑ j ∈ cls, Real.logb 2 (n.choose (k j)) ≤ U := by
  refine ⟨?_, modelR_bound cls n U k w hrank hU⟩
  have hn : (n : ℝ) = ∑ j ∈ cls, (k j : ℝ) := by exact_mod_cast hsum.symm
  rw [hn, Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hkn : k j ≤ n := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
  rw [← hn]
  exact mul_logb_le_logb_choose (hk1 j hj) (hks j hj) hkn

/-- `vertex-local-bound.md` Theorem 3.1 (tree skeletons), summation step: if every tree edge `e`
carries `c_e` bits with `C(k_e + k′_e, k_e) ≤ 2^{c_e}` (B-Lemma 3.1 + the vertex-cut rank) and
`U = 2 Σ_e c_e`, then `U ≥ 2 Σ_e log₂ C(k_e + k′_e, k_e)`. -/
theorem treeSkeleton_bound {E : Type*} (edges : Finset E) (U : ℕ) (c k k' : E → ℕ)
    (hU : U = 2 * ∑ e ∈ edges, c e) (hrank : ∀ e ∈ edges, (k e + k' e).choose (k e) ≤ 2 ^ c e) :
    2 * ∑ e ∈ edges, Real.logb 2 ((k e + k' e).choose (k e)) ≤ U := by
  have := sum_logb_le_of_le_two_pow edges _ c hrank
  rw [hU]; push_cast
  linarith

/-! ### `pieces.md` (2.1): the contraction bound -/

section Pieces

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The row flattening `(xy | uv)` of a four-index tensor `T x y u v`. -/
def rowFlat (T : L → L → L → L → K) : Matrix (L × L) (L × L) K :=
  Matrix.of fun p q => T p.1 p.2 q.1 q.2

/-- The column flattening `(xu | yv)` (operator Schmidt rank `OSR`). -/
def colFlat (T : L → L → L → L → K) : Matrix (L × L) (L × L) K :=
  Matrix.of fun p q => T p.1 q.1 p.2 q.2

/-- Contract `y` with `β` and `u` with `a`. -/
def contract (β a : L → K) (T : L → L → L → L → K) : Matrix L L K :=
  Matrix.of fun x v => ∑ y, ∑ u, β y * T x y u v * a u

theorem contract_eq_row (β a : L → K) (T : L → L → L → L → K) :
    contract β a T = (Matrix.of fun (x : L) (p : L × L) => if x = p.1 then β p.2 else 0) *
      rowFlat T * (Matrix.of fun (q : L × L) (v : L) => if v = q.2 then a q.1 else 0) := by
  ext x v
  simp only [contract, rowFlat, Matrix.of_apply]
  symm
  simp only [Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_eq_single x (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
  simp only [↓reduceIte]
  rw [Finset.sum_comm]

theorem contract_eq_col (β a : L → K) (T : L → L → L → L → K) :
    contract β a T = (Matrix.of fun (x : L) (p : L × L) => if x = p.1 then a p.2 else 0) *
      colFlat T * (Matrix.of fun (q : L × L) (v : L) => if v = q.2 then β q.1 else 0) := by
  ext x v
  simp only [contract, colFlat, Matrix.of_apply]
  symm
  simp only [Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_eq_single x (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
  simp only [↓reduceIte]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- "For any piece T the contracted x|v matrix has rank ≤ min(rank T, OSR T)." -/
theorem rank_contract_le (β a : L → K) (T : L → L → L → L → K) :
    (contract β a T).rank ≤ min (rowFlat T).rank (colFlat T).rank := by
  refine le_min ?_ ?_
  · rw [contract_eq_row]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · rw [contract_eq_col]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- `pieces.md` (2.1): if pieces `T_i` (`i ∈ I`) sum to `d · F`, `F(x,y,u,v) = [x = v][y = u]`,
`d ≠ 0`, then `Σ_i min(rank_row T_i, OSR T_i) ≥ N = |L|`. -/
theorem pieces_trivial_lower_bound {ι : Type*} (I : Finset ι) (T : ι → L → L → L → L → K)
    (d : K) (hd : d ≠ 0)
    (hsum : ∀ x y u v, ∑ i ∈ I, T i x y u v = d * if x = v ∧ y = u then 1 else 0) :
    Fintype.card L ≤ ∑ i ∈ I, min (rowFlat (T i)).rank (colFlat (T i)).rank := by
  rcases isEmpty_or_nonempty L with hL | ⟨⟨y₀⟩⟩
  · simp
  let δ : L → K := fun y => if y = y₀ then 1 else 0
  have hF : (∑ i ∈ I, contract δ δ (T i)) = d • (1 : Matrix L L K) := by
    ext x v
    simp only [Matrix.sum_apply, contract, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [δ, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hsum]
    by_cases hxv : x = v <;> simp [hxv]
  have hrank : (d • (1 : Matrix L L K)).rank = Fintype.card L := by
    rw [Matrix.rank_of_isUnit]
    exact (Matrix.isUnit_iff_isUnit_det _).2 (by simp [hd])
  calc Fintype.card L = (∑ i ∈ I, contract δ δ (T i)).rank := by rw [hF, hrank]
    _ ≤ ∑ i ∈ I, (contract δ δ (T i)).rank := rank_sum_le I _
    _ ≤ _ := Finset.sum_le_sum fun i _ => rank_contract_le δ δ (T i)

/-- `pieces.md` (2.1), last step: "some piece has both r_i and o_i ≥ N/|I|". -/
theorem pieces_exists_large_piece {ι : Type*} (I : Finset ι) (hI : I.Nonempty)
    (T : ι → L → L → L → L → K) (d : K) (hd : d ≠ 0)
    (hsum : ∀ x y u v, ∑ i ∈ I, T i x y u v = d * if x = v ∧ y = u then 1 else 0) :
    ∃ i ∈ I, Fintype.card L ≤ I.card * (rowFlat (T i)).rank ∧
      Fintype.card L ≤ I.card * (colFlat (T i)).rank := by
  obtain ⟨i, hi, h⟩ := exists_le_card_mul_of_le_sum I hI _ _
    (pieces_trivial_lower_bound I T d hd hsum)
  exact ⟨i, hi, h.trans (Nat.mul_le_mul_left _ (min_le_left _ _)),
    h.trans (Nat.mul_le_mul_left _ (min_le_right _ _))⟩

end Pieces

end EthFollowup.Barriers.Rank
