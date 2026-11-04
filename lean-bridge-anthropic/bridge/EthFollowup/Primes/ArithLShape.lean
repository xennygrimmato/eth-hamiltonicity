/-
# ArithL, module 2a: the shapes of the levels and their multiplication pipelines

`scratchpad/plans/primes-plan.md` (Executor L), design note in `primes-interface.md`.

All levels share the limb width `b n`, the modulus `M n = 2^{J n} + 1` and the wire width `Wa n`
of the top level `n`. Shape `j < m n` has `ℓ1_j = 2^{m−j−1}` row limbs (as many column limbs),
transform length `L1_j = 2^{m−j}` and root `ω_j = 2^{2J/L1_j}`; level `k` uses shape
`sh n k = min (k/2) (m n − 1)`. The pipeline functions are `Factoring.MP.rowE …` on the per-level
parameter tuple `kP n k : Prm`, and the Fermat-ring lemmas (`Factoring.Fermat.stages_eq_aconv2`)
give the 2D convolution, hence `kc_eval : Σ_{k'<Kc_k} c_{k'} 2^{b k'} = x·y`.

Standard axioms only.
-/
import EthFollowup.Factoring.MulProcs
import EthFollowup.Factoring.FermatBridge
import EthFollowup.ModP.ArithBounds
import EthFollowup.ModP.ArithParams
import EthFollowup.Primes.ArithLDesc

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Finset EthFollowup.Factoring EthFollowup.ModP EthFollowup.Factoring.MP

/-! ## Shapes -/

/-- The shape of level `k`. -/
def sh (n k : ℕ) : ℕ := min (k / 2) (m n - 1)
/-- Row limbs at level `k` (as many column limbs). -/
def kl1 (n k : ℕ) : ℕ := 2 ^ (m n - sh n k - 1)
/-- Transform length at level `k`. -/
def kL1 (n k : ℕ) : ℕ := 2 ^ (m n - sh n k)
/-- Number of limbs at level `k`. -/
def kl (n k : ℕ) : ℕ := kl1 n k * kl1 n k
/-- Number of carry positions at level `k`. -/
def kKc (n k : ℕ) : ℕ := kL1 n k + kl1 n k * kL1 n k
/-- The inverse of `L1_k` modulo `M`. -/
def kiL (n k : ℕ) : ℕ := 2 ^ (2 * J n - (m n - sh n k))
/-- The table of `ω_k^e`, `e < L1_k`. -/
def wTabK (n k : ℕ) : List ℕ := (List.range (kL1 n k)).map fun e => 2 ^ (2 * J n / kL1 n k * e)
/-- The box of a level-`k` variable: `2^{b·ℓ_k}`. -/
def lbox (n k : ℕ) : ℕ := 2 ^ (b n * kl n k)

/-- **The parameter tuple of level `k`** (for `Factoring.MP`'s pipeline functions). -/
def kP (n k : ℕ) : Prm :=
  (((kl1 n k, kl1 n k), (kL1 n k, kL1 n k)), ((b n, 2 ^ b n), (M n, kiL n k)),
    (List.replicate (Wa n) (), wTabK n k),
    ((List.range (kl1 n k), List.range (kl1 n k)), (List.range (kL1 n k), List.range (kL1 n k))),
    (List.range (b n), ([], [])))

section KP
variable (n k : ℕ)
@[simp] theorem kP_l1 : (kP n k).l1 = kl1 n k := rfl
@[simp] theorem kP_l2 : (kP n k).l2 = kl1 n k := rfl
@[simp] theorem kP_L1 : (kP n k).L1 = kL1 n k := rfl
@[simp] theorem kP_L2 : (kP n k).L2 = kL1 n k := rfl
@[simp] theorem kP_b : (kP n k).b = b n := rfl
@[simp] theorem kP_pb : (kP n k).pb = 2 ^ b n := rfl
@[simp] theorem kP_M : (kP n k).M = M n := rfl
@[simp] theorem kP_iL : (kP n k).iL = kiL n k := rfl
@[simp] theorem kP_wT : (kP n k).wT = wTabK n k := rfl
@[simp] theorem kP_rl1 : (kP n k).rl1 = List.range (kl1 n k) := rfl
@[simp] theorem kP_rl2 : (kP n k).rl2 = List.range (kl1 n k) := rfl
@[simp] theorem kP_rL1 : (kP n k).rL1 = List.range (kL1 n k) := rfl
@[simp] theorem kP_rL2 : (kP n k).rL2 = List.range (kL1 n k) := rfl
end KP

/-! ## Facts about the shapes -/

section Facts
variable (n k : ℕ)

theorem sh_lt : sh n k < m n := by have := one_le_m n; unfold sh; omega
theorem sh_le : sh n k ≤ k / 2 := min_le_left _ _

theorem kL1_eq : kL1 n k = 2 * kl1 n k := by
  have := sh_lt n k
  unfold kL1 kl1
  rw [← pow_succ']; congr 1; omega

theorem one_le_kl1 : 1 ≤ kl1 n k := Nat.one_le_two_pow
theorem two_le_kL1 : 2 ≤ kL1 n k := by have := one_le_kl1 n k; rw [kL1_eq]; omega
theorem kl_pos : 0 < kl n k := Nat.mul_pos (one_le_kl1 n k) (one_le_kl1 n k)
theorem one_le_kKc : 1 ≤ kKc n k := by have := two_le_kL1 n k; unfold kKc; omega

theorem kl1_le : kl1 n k ≤ ℓ1 n := Nat.pow_le_pow_right (by norm_num) (by omega)
theorem kL1_le : kL1 n k ≤ L1 n := Nat.pow_le_pow_right (by norm_num) (by omega)
theorem kl_le : kl n k ≤ ℓ n := by
  unfold kl ℓ; rw [ℓ2_eq_ℓ1]; exact Nat.mul_le_mul (kl1_le n k) (kl1_le n k)

theorem kl_le_kKc : kl n k ≤ kKc n k := by
  unfold kl kKc; rw [kL1_eq]; nlinarith [one_le_kl1 n k]

theorem two_kl_le_kKc : 2 * kl n k ≤ kKc n k := by
  unfold kl kKc; rw [kL1_eq]; nlinarith [one_le_kl1 n k]

theorem kL1_dvd : kL1 n k ∣ 2 * J n :=
  (Nat.pow_dvd_pow 2 (by omega : m n - sh n k ≤ m n)).trans (L1_dvd_two_J n)

theorem kl_mul_pow_le : kl1 n k * kl1 n k * 2 ^ (2 * b n) ≤ 2 ^ J n :=
  le_trans (Nat.mul_le_mul_right _ (kl_le n k)) (ℓ_mul_pow_le n)

theorem kL1_two_pow : kL1 n k = 2 ^ (m n - sh n k) := rfl

theorem kiL_eq : kiL n k = 2 ^ (2 * J n - (m n - sh n k)) := rfl

/-- The shapes shrink with the level. -/
theorem kl1_anti {k k' : ℕ} (h : k ≤ k') : kl1 n k' ≤ kl1 n k := by
  have : sh n k ≤ sh n k' := by unfold sh; omega
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem kl_anti {k k' : ℕ} (h : k ≤ k') : kl n k' ≤ kl n k :=
  Nat.mul_le_mul (kl1_anti n h) (kl1_anti n h)

theorem kKc_anti {k k' : ℕ} (h : k ≤ k') : kKc n k' ≤ kKc n k := by
  unfold kKc; rw [kL1_eq, kL1_eq]
  have := kl1_anti n h
  nlinarith

/-- The level boxes contain the `2^k`-th roots of numbers below `2^n`. -/
theorem lbox_spec {y : ℕ} (hy : y ^ 2 ^ k < 2 ^ n) : y < lbox n k := by
  by_contra hc
  rw [not_lt] at hc
  have h1 : n ≤ 2 ^ k * (b n * kl n k) := by
    have hnB := lt_nB n
    have hsh := sh_le n k
    -- ℓ = 4^(m-1) ≤ 4^sh · ℓ_k ≤ 2^k ℓ_k
    have hℓ : ℓ n = 2 ^ (2 * sh n k) * kl n k := by
      unfold ℓ kl kl1; rw [ℓ2_eq_ℓ1]; unfold ℓ1
      rw [← pow_add, ← pow_add, ← pow_add]; congr 1; have := sh_lt n k; omega
    have h2 : 2 ^ (2 * sh n k) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold nB at hnB
    rw [hℓ] at hnB
    have : 2 ^ (2 * sh n k) * kl n k * b n ≤ 2 ^ k * (b n * kl n k) := by
      calc 2 ^ (2 * sh n k) * kl n k * b n ≤ 2 ^ k * kl n k * b n :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
        _ = 2 ^ k * (b n * kl n k) := by ring
    omega
  have h3 : 2 ^ n ≤ y ^ 2 ^ k :=
    calc 2 ^ n ≤ 2 ^ (2 ^ k * (b n * kl n k)) := Nat.pow_le_pow_right (by norm_num) h1
      _ = (2 ^ (b n * kl n k)) ^ 2 ^ k := by rw [← pow_mul, mul_comm]
      _ ≤ y ^ 2 ^ k := Nat.pow_le_pow_left hc _
  omega

end Facts

/-! ## The pipeline at level `k` -/

/-- The limb array of `x` at level `k`. -/
def pAk (n k x : ℕ) (i1 i2 : ℕ) : ℕ := limb (b n) x (i1 + kl1 n k * i2)
/-- Row transforms. -/
def kA (n k x : ℕ) : ℕ → ℕ → ℕ := rowE (kP n k) (pAk n k x)
/-- Column transforms. -/
def kF (n k x : ℕ) : ℕ → ℕ → ℕ := colE (kP n k) (kA n k x)
/-- Pointwise products. -/
def kC (n k x y : ℕ) (s t : ℕ) : ℕ := kF n k x s t * kF n k y s t % M n
/-- Inverse columns. -/
def kD (n k x y : ℕ) : ℕ → ℕ → ℕ := invColE (kP n k) (kC n k x y)
/-- Inverse rows (the 2D convolution). -/
def kE (n k x y : ℕ) : ℕ → ℕ → ℕ := invRowE (kP n k) (kD n k x y)
/-- The collapsed coefficients. -/
def kc (n k x y : ℕ) : ℕ → ℕ := convE (kP n k) (kE n k x y)

theorem wq_kP (n k e : ℕ) : wq (kP n k) e = 2 ^ (2 * J n / kL1 n k * (e % kL1 n k)) := by
  unfold wq md
  rw [kP_wT, kP_L1, wTabK, getD_map_range' _ (Nat.mod_lt _ (by have := two_le_kL1 n k; omega))]

theorem md_lt_M (n a : ℕ) : md a (M n) < M n := Nat.mod_lt _ (by unfold M; positivity)

theorem rowE_lt (n k : ℕ) (x : ℕ → ℕ → ℕ) (s i2 : ℕ) : rowE (kP n k) x s i2 < M n := md_lt_M n _
theorem colE_lt (n k : ℕ) (x : ℕ → ℕ → ℕ) (s i2 : ℕ) : colE (kP n k) x s i2 < M n := md_lt_M n _
theorem invColE_lt (n k : ℕ) (x : ℕ → ℕ → ℕ) (s i2 : ℕ) : invColE (kP n k) x s i2 < M n := md_lt_M n _
theorem invRowE_lt (n k : ℕ) (x : ℕ → ℕ → ℕ) (s i2 : ℕ) : invRowE (kP n k) x s i2 < M n := md_lt_M n _

/-- **The level-`k` pipeline computes the 2D acyclic convolution.** -/
theorem kE_eq_aconv2 (n k x y : ℕ) : ∀ a < kL1 n k, ∀ u < kL1 n k,
    kE n k x y a u = Factoring.Fermat.aconv2 (kl1 n k) (kl1 n k) (pAk n k x) (pAk n k y) a u := by
  have hm : 1 ≤ m n - sh n k := by have := sh_lt n k; omega
  have h1 : 2 * kl1 n k ≤ 2 ^ (m n - sh n k) := (kL1_eq n k).symm.le
  have hJ : 0 < J n := one_le_J n
  have e1 : ∀ e, wq (kP n k) e = 2 ^ (2 * J n / 2 ^ (m n - sh n k) * (e % 2 ^ (m n - sh n k))) :=
    fun e => wq_kP n k e
  have hL : (2 : ℕ) ^ (m n - sh n k) = kL1 n k := rfl
  refine Factoring.Fermat.stages_eq_aconv2 hm (kL1_dvd n k) hJ h1 h1 (kl_mul_pow_le n k)
    (pAk n k x) (pAk n k y) (kA n k x) (kA n k y) (kF n k x) (kF n k y) (kC n k x y) (kD n k x y)
    (kE n k x y) (fun _ _ => limb_lt _ _ _) (fun _ _ => limb_lt _ _ _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s _ i2 _; simp only [kA, rowE, md, kP_rl1, kP_M, e1, sum_range_list]; rfl
  · intro s _ i2 _; simp only [kA, rowE, md, kP_rl1, kP_M, e1, sum_range_list]; rfl
  · intro s _ t _; simp only [kF, colE, md, kP_rl2, kP_M, e1, sum_range_list]; rfl
  · intro s _ t _; simp only [kF, colE, md, kP_rl2, kP_M, e1, sum_range_list]; rfl
  · intro s _ t _; rfl
  · intro s _ u _; simp only [kD, invColE, md, kP_rL2, kP_M, kP_iL, kP_L2, e1, sum_range_list, kiL_eq]; rfl
  · intro a _ u _; simp only [kE, invRowE, md, kP_rL1, kP_M, kP_iL, kP_L1, e1, sum_range_list, kiL_eq]; rfl

theorem kE_le (n k x y a u : ℕ) : kE n k x y a u ≤ 2 ^ J n := by
  have := invRowE_lt n k (kD n k x y) a u
  unfold M at this; unfold kE; omega

theorem convE_kP (n k : ℕ) (C : ℕ → ℕ → ℕ) (k' : ℕ) : convE (kP n k) C k' =
    ∑ a ∈ range (kL1 n k), ∑ u ∈ range (kL1 n k), if a + kl1 n k * u = k' then C a u else 0 := by
  unfold convE; rw [kP_rL1, kP_rL2, kP_l1]; simp only [sum_range_list]

theorem convE_congr (n k : ℕ) {C C' : ℕ → ℕ → ℕ} {k' : ℕ}
    (h : ∀ a < kL1 n k, ∀ u < kL1 n k, a + kl1 n k * u = k' → C a u = C' a u) :
    convE (kP n k) C k' = convE (kP n k) C' k' := by
  rw [convE_kP, convE_kP]
  refine sum_congr rfl fun a ha => sum_congr rfl fun u hu => ?_
  split_ifs with hk
  · exact h a (mem_range.1 ha) u (mem_range.1 hu) hk
  · rfl

/-- A position collects at most two coefficients: `c ≤ 2^{J+1}`. -/
theorem kc_le (n k x y k' : ℕ) : kc n k x y k' ≤ 2 ^ (J n + 1) := by
  unfold kc; rw [convE_kP]
  have := Factoring.Fermat.convCoeff_le (L' := kL1 n k) (one_le_kl1 n k) (kL1_eq n k).le (kE n k x y)
    (fun a _ u _ => kE_le n k x y a u) k'
  rw [pow_succ]; omega

theorem Cc_pos_lt' (n k : ℕ) {a u : ℕ} (ha : a < kL1 n k) (hu : u < kL1 n k) :
    a + kl1 n k * u < kKc n k := by
  unfold kKc; rw [kL1_eq] at ha hu ⊢
  have h := Nat.mul_le_mul_left (kl1 n k) (show u + 1 ≤ 2 * kl1 n k by omega)
  rw [mul_add, mul_one] at h
  omega

/-- **The level-`k` pipeline multiplies**: `Σ_{k' < Kc_k} c_{k'} 2^{b k'} = x y` for `x, y < 2^{b ℓ_k}`. -/
theorem kc_eval (n k x y : ℕ) (hx : x < lbox n k) (hy : y < lbox n k) :
    ∑ k' ∈ range (kKc n k), kc n k x y k' * 2 ^ (b n * k') = x * y := by
  unfold kc
  simp only [convE_kP]
  rw [Factoring.Fermat.convCoeff_eval (kE n k x y) (fun a ha u hu => Cc_pos_lt' n k ha hu)]
  unfold lbox kl at hx hy
  exact Factoring.Fermat.stages_eval_mul (L := kL1 n k) (kL1_eq n k).symm.le (kL1_eq n k).symm.le
    hx hy (kE n k x y) (kE_eq_aconv2 n k x y)

end EthFollowup.Primes
