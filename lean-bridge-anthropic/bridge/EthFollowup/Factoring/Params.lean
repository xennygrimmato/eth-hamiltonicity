/-
# Factoring, module F0: parameters, pipeline functions, layout, checks, the package shape

`scratchpad/plans/factoring-plan.md` §0, §2, §4 (row F0); interface `facM-interface.md`.

2D (bivariate Kronecker) Schönhage–Strassen multiplication as a counting network: `p`, `q` are
`ℓ1 × ℓ2` arrays of `b`-bit limbs (`i = i1 + ℓ1·i2`), the 2D cyclic convolution of size `L1 × L2`
is computed over `ℤ/(2^J+1)` with `ω = 2^{2J/L1}` (row transforms, column transforms, pointwise
product, inverse columns, inverse rows, all multiplied by `2^{2J−m} = L1⁻¹`), then the coefficients
are collapsed (`a + ℓ1·u = k`) and checked against the limbs of `N` with a carry chain.

* Parameters (power-of-two, from `ν = ⌊log₂(n+2)⌋`): `m, L1, L2, ℓ1, ℓ2, ℓ, b, nB, J, W, M, Kc,
  dg`; `ω^e = 2^{wE n e}` (`wP`), `iL = 2^{2J−m}`.
* Limbs: `limb`, `ofLimbs` (`ofLimbs_limb`, `limb_ofLimbs`, `ofLimbs_lt`); `pA` (the 2D array).
* The prefix pattern: `bev` (big-endian value), `patBit`, `pat`, `patOK`; the count `D`.
* The pipeline as plain `ℕ` functions with `% M n`: `rowDFT`, `colDFT`, `pointwise`, `invCol`,
  `invRow`, `convCoeff`, `carryChain`; the canonical stages `stA … stR` and `run`.
* Wires `WD`, vertices `VD`; index ranges `wireIdx/wireOf/numWires`, `vertIdx/vertOf/numVerts`
  (round trips); `ends`; clusters `clus` (contiguous per stage, `VB.vbN`), `wLo`, `wHi`.
* The checks `chk` and `structure MulPackage`.
* Parameter facts: `L1_dvd_two_J`, `J_ge`, `lt_nB`, `ℓ_mul_W_le`, `L1L2W_le`, `numWires_le`,
  `numWires_mul_W_le`, `deg_le`, `dg_pow_le`, `L1_mul_iL_mod`, `two_pow_two_J_mod`, `wE_lt`, …
* Locality and degree: `incW` (the wires a vertex reads), `chk_local`, `mem_incW`, `incW_spec`,
  `length_incW_le`, `card_ends_le` (at most `2·L1` wires end at a vertex); congruence lemmas of the
  pipeline functions; `convCoeff_le` (at most two coefficients per carry position).
* `patOK_iff`: the pattern cells of all limbs of `p < 2^{nB}` hold iff `p / 2^{n−|π|} = bev π`.
* `chk_*_iff` (the checks as propositions), `chk_run_*` (the canonical values pass every check but
  the pattern cells and the carries, which reduce to `patOK` and `carryOK`), `run_lt`.

Standard axioms only.
-/
import EthFollowup.ExactHC.LabelNetwork
import EthFollowup.ExactHC.VertexBalanced
import PrintedStatement

set_option linter.unusedSectionVars false

namespace EthFollowup.Factoring

open Finset Groundwork

/-! ## Parameters -/

/-- `ν = ⌊log₂(n+2)⌋`. -/
def ν (n : ℕ) : ℕ := Nat.log 2 (n + 2)
/-- `m = ⌊ν/4⌋ + 1`; the transform length is `2^m`. -/
def m (n : ℕ) : ℕ := ν n / 4 + 1
/-- Row transform length. -/
def L1 (n : ℕ) : ℕ := 2 ^ m n
/-- Column transform length (equal to `L1`). -/
def L2 (n : ℕ) : ℕ := 2 ^ m n
/-- Limbs per row. -/
def ℓ1 (n : ℕ) : ℕ := 2 ^ (m n - 1)
/-- Limbs per column. -/
def ℓ2 (n : ℕ) : ℕ := 2 ^ (m n - 1)
/-- Number of limbs. -/
def ℓ (n : ℕ) : ℕ := ℓ1 n * ℓ2 n
/-- Limb width. -/
def b (n : ℕ) : ℕ := n / ℓ n + 1
/-- `n' = ℓ·b ≥ n`: the factors range over `[0, 2^{n'})`. -/
def nB (n : ℕ) : ℕ := ℓ n * b n
/-- The Fermat exponent: arithmetic modulo `2^J + 1`. -/
def J (n : ℕ) : ℕ := 2 ^ (ν n / 2 + 7)
/-- The width of every wire. -/
def W (n : ℕ) : ℕ := J n + 2
/-- The modulus `2^J + 1`. -/
def M (n : ℕ) : ℕ := 2 ^ J n + 1
/-- `ω^e = 2^{wE n e}` with `ω = 2^{2J/L1}`; the exponent `e` is reduced mod `L1` (`wE < 2J`). -/
def wE (n e : ℕ) : ℕ := 2 * J n / L1 n * (e % L1 n)
/-- `ω^e` as a natural number (not reduced mod `M`). -/
def wP (n e : ℕ) : ℕ := 2 ^ wE n e
/-- `2^{2J−m}`, the inverse of `L1 = 2^m` modulo `M`. -/
def iL (n : ℕ) : ℕ := 2 ^ (2 * J n - m n)
/-- The number of carry positions `k < Kc`. -/
def Kc (n : ℕ) : ℕ := L1 n + ℓ1 n * L2 n
/-- The block sizes `L1·ℓ2` and `L1·L2`. -/
def nA (n : ℕ) : ℕ := L1 n * ℓ2 n
def nF (n : ℕ) : ℕ := L1 n * L2 n
/-- A bound on the number of bits incident to one vertex. -/
def dg (n : ℕ) : ℕ := 2 ^ (3 * ν n / 4 + 11)

theorem L2_eq_L1 (n : ℕ) : L2 n = L1 n := rfl
theorem ℓ2_eq_ℓ1 (n : ℕ) : ℓ2 n = ℓ1 n := rfl

/-! ### Elementary facts -/

theorem two_pow_ν_le (n : ℕ) : 2 ^ ν n ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)

theorem lt_two_pow_ν (n : ℕ) : n + 2 < 2 ^ (ν n + 1) := Nat.lt_pow_succ_log_self (by norm_num) _

theorem one_le_m (n : ℕ) : 1 ≤ m n := by unfold m; omega

theorem L1_eq_two_mul (n : ℕ) : L1 n = 2 * ℓ1 n := by
  have := one_le_m n
  unfold L1 ℓ1
  rw [← pow_succ', Nat.sub_add_cancel this]

theorem one_le_ℓ1 (n : ℕ) : 1 ≤ ℓ1 n := Nat.one_le_two_pow
theorem one_le_ℓ2 (n : ℕ) : 1 ≤ ℓ2 n := Nat.one_le_two_pow
theorem two_le_L1 (n : ℕ) : 2 ≤ L1 n := by rw [L1_eq_two_mul]; have := one_le_ℓ1 n; omega
theorem two_le_L2 (n : ℕ) : 2 ≤ L2 n := two_le_L1 n
theorem ℓ_pos (n : ℕ) : 0 < ℓ n := Nat.mul_pos (one_le_ℓ1 n) (one_le_ℓ2 n)
theorem one_le_b (n : ℕ) : 1 ≤ b n := Nat.le_add_left 1 _
theorem Kc_pos (n : ℕ) : 0 < Kc n := by unfold Kc; have := two_le_L1 n; omega
theorem one_le_J (n : ℕ) : 1 ≤ J n := Nat.one_le_two_pow

/-- The shape of the parameters: `ℓ1 = ℓ2 = y`, `L1 = L2 = 2y`, `J = 128 Z` with `y² ≤ Z`,
`Z² ≤ n + 2`, `n + 2 < 16 y⁴`, `log₂ y < y`. -/
theorem shape (n : ℕ) : ∃ y Z a : ℕ, ℓ1 n = y ∧ ℓ2 n = y ∧ L1 n = 2 * y ∧ L2 n = 2 * y ∧
    J n = 128 * Z ∧ y * y ≤ Z ∧ Z * Z ≤ n + 2 ∧ n + 2 < 16 * (y * y * (y * y)) ∧ 1 ≤ y ∧
    m n = a + 1 ∧ a < y ∧ y = 2 ^ a ∧ Z = 2 ^ (ν n / 2) := by
  refine ⟨2 ^ (ν n / 4), 2 ^ (ν n / 2), ν n / 4, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, Nat.one_le_two_pow,
    rfl, Nat.lt_two_pow_self, rfl, rfl⟩
  · rw [L1_eq_two_mul]; rfl
  · rw [L2_eq_L1, L1_eq_two_mul]; rfl
  · unfold J; rw [pow_add]; ring
  · rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [← pow_add]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (two_pow_ν_le n)
  · refine lt_of_lt_of_le (lt_two_pow_ν n) ?_
    simp only [← pow_add]
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem ℓ_eq (n : ℕ) : ℓ n = 2 ^ (2 * (m n - 1)) := by
  unfold ℓ ℓ1 ℓ2; rw [← pow_add]; congr 1; omega

theorem two_mul_J (n : ℕ) : 2 * J n = 2 ^ (ν n / 2 + 8) := by
  unfold J; rw [← pow_succ']

/-- **`L1 ∣ 2J`.** -/
theorem L1_dvd_two_J (n : ℕ) : L1 n ∣ 2 * J n := by
  rw [two_mul_J]; unfold L1 m
  exact Nat.pow_dvd_pow 2 (by omega)

theorem two_J_div_mul (n : ℕ) : 2 * J n / L1 n * L1 n = 2 * J n := Nat.div_mul_cancel (L1_dvd_two_J n)

theorem one_le_two_J_div (n : ℕ) : 1 ≤ 2 * J n / L1 n := by
  have h := two_J_div_mul n
  have : 0 < 2 * J n := by have := one_le_J n; omega
  rcases Nat.eq_zero_or_pos (2 * J n / L1 n) with h0 | h0
  · rw [h0, zero_mul] at h; omega
  · exact h0

/-- `ω^e` has exponent `< 2J`. -/
theorem wE_lt (n e : ℕ) : wE n e < 2 * J n := by
  unfold wE
  have h1 := Nat.mod_lt e (show 0 < L1 n by have := two_le_L1 n; omega)
  have h2 := one_le_two_J_div n
  calc 2 * J n / L1 n * (e % L1 n) < 2 * J n / L1 n * L1 n := Nat.mul_lt_mul_of_pos_left h1 h2
    _ = 2 * J n := two_J_div_mul n

/-- `ω^{L1} = 2^{2J}`. -/
theorem wE_L1_mul (n : ℕ) : 2 * J n / L1 n * L1 n = 2 * J n := two_J_div_mul n

theorem m_le_two_J (n : ℕ) : m n ≤ 2 * J n := by
  obtain ⟨y, Z, a, -, -, -, -, hJ, hyZ, -, -, hy, hm, ha, -, -⟩ := shape n
  rw [hm, hJ]; nlinarith

theorem two_pow_m_mul_iL (n : ℕ) : 2 ^ m n * iL n = 2 ^ (2 * J n) := by
  unfold iL; rw [← pow_add]; congr 1; have := m_le_two_J n; omega

theorem L1_mul_iL (n : ℕ) : L1 n * iL n = 2 ^ (2 * J n) := two_pow_m_mul_iL n

theorem two_pow_J_sq (n : ℕ) : 2 ^ (2 * J n) = (M n) * (2 ^ J n - 1) + 1 := by
  unfold M
  have h1 : 1 ≤ 2 ^ J n := Nat.one_le_two_pow
  rw [mul_comm 2, pow_mul]
  obtain ⟨X, hX⟩ : ∃ X, 2 ^ J n = X + 1 := ⟨2 ^ J n - 1, by omega⟩
  rw [hX, Nat.add_sub_cancel]; ring

theorem one_lt_M (n : ℕ) : 1 < M n := by unfold M; have : 1 ≤ 2 ^ J n := Nat.one_le_two_pow; omega

/-- `2^{2J} ≡ 1 (mod M)`. -/
theorem two_pow_two_J_mod (n : ℕ) : 2 ^ (2 * J n) % M n = 1 := by
  rw [two_pow_J_sq, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (one_lt_M n)

/-- `L1 · iL ≡ 1 (mod M)`. -/
theorem L1_mul_iL_mod (n : ℕ) : L1 n * iL n % M n = 1 := by rw [L1_mul_iL, two_pow_two_J_mod]

/-- `2^J ≡ −1 (mod M)`. -/
theorem two_pow_J_add_one (n : ℕ) : (2 ^ J n + 1) % M n = 0 := Nat.mod_self _

/-- **`J ≥ 2b + 2m + 1`.** -/
theorem J_ge (n : ℕ) : 2 * b n + 2 * m n + 1 ≤ J n := by
  obtain ⟨y, Z, a, h1, h2, -, -, hJ, hyZ, -, hlo, hy, hm, ha, -, -⟩ := shape n
  have hℓ : ℓ n = y * y := by unfold ℓ; rw [h1, h2]
  have hb : n / ℓ n < 16 * (y * y) := by
    rw [hℓ, Nat.div_lt_iff_lt_mul (by positivity)]; nlinarith
  unfold b; rw [hm, hJ]
  nlinarith

theorem b_le_J (n : ℕ) : b n ≤ J n := by have := J_ge n; omega

/-- The coefficient bound `ℓ · 2^{2b} ≤ 2^J`. -/
theorem ℓ_mul_pow_le (n : ℕ) : ℓ n * 2 ^ (2 * b n) ≤ 2 ^ J n := by
  rw [ℓ_eq, ← pow_add]
  have := J_ge n
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **`ℓ·b > n`.** -/
theorem lt_nB (n : ℕ) : n < nB n := Nat.lt_mul_div_succ n (ℓ_pos n)

theorem le_nB (n : ℕ) : n ≤ nB n := (lt_nB n).le

/-- **`ℓ·W ≤ 2^8 (n+2)`.** -/
theorem ℓ_mul_W_le (n : ℕ) : ℓ n * W n ≤ 2 ^ 8 * (n + 2) := by
  obtain ⟨y, Z, a, h1, h2, -, -, hJ, hyZ, hZ, -, hy, -, -, -, -⟩ := shape n
  have hℓ : ℓ n = y * y := by unfold ℓ; rw [h1, h2]
  unfold W; rw [hℓ, hJ]
  have hZ1 : 1 ≤ Z := le_trans (by nlinarith) hyZ
  nlinarith

/-- **`L1·L2·W ≤ 2^10 (n+2)`.** -/
theorem L1L2W_le (n : ℕ) : L1 n * L2 n * W n ≤ 2 ^ 10 * (n + 2) := by
  obtain ⟨y, Z, a, -, -, h3, h4, hJ, hyZ, hZ, -, hy, -, -, -, -⟩ := shape n
  unfold W; rw [h3, h4, hJ]
  have hZ1 : 1 ≤ Z := le_trans (by nlinarith) hyZ
  nlinarith

theorem M_le_two_pow_W (n : ℕ) : M n ≤ 2 ^ W n := by
  unfold M W; rw [pow_add]; have : 1 ≤ 2 ^ J n := Nat.one_le_two_pow; omega

theorem M_lt_two_pow_W (n : ℕ) : M n < 2 ^ W n := by
  unfold M W; rw [pow_add]; have : 1 ≤ 2 ^ J n := Nat.one_le_two_pow; omega

theorem two_pow_b_le_M (n : ℕ) : 2 ^ b n ≤ M n := by
  unfold M; have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (b_le_J n); omega

theorem clog_W (n : ℕ) : Nat.clog 2 (2 ^ W n - 1 + 1) = W n := by
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, Nat.clog_pow 2 _ (by norm_num)]

/-- A carry step stays below `2^W = 2^{J+2}`. -/
theorem carryStep_lt (n c r N' : ℕ) (hc : c ≤ 2 * 2 ^ J n) (hr : r < 2 ^ W n) :
    (c + r - N') / 2 ^ b n < 2 ^ W n := by
  have h2 : 2 ≤ 2 ^ b n := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (one_le_b n); simpa using this
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  unfold W at *
  rw [pow_add] at *
  have h3 : c + r - N' ≤ c + r := Nat.sub_le _ _
  have h4 := Nat.mul_le_mul_left (2 ^ J n * 2 ^ 2) h2
  have h5 : 1 ≤ 2 ^ J n := Nat.one_le_two_pow
  nlinarith

/-- **The degree bound** `2·L1·W ≤ dg n`. -/
theorem deg_le (n : ℕ) : 2 * L1 n * W n ≤ dg n := by
  obtain ⟨y, Z, a, -, -, h3, -, hJ, hyZ, -, -, hy, hm, -, hya, hZ⟩ := shape n
  have hm' : m n = ν n / 4 + 1 := rfl
  have hyZ' : y * Z ≤ 2 ^ (3 * ν n / 4) := by
    rw [hya, hZ, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hZ1 : 1 ≤ Z := le_trans (by nlinarith) hyZ
  unfold dg W; rw [h3, hJ, pow_add]
  nlinarith

theorem dg_pow_le (n : ℕ) : dg n ^ 4 ≤ 2 ^ 44 * (n + 2) ^ 3 := by
  unfold dg
  rw [← pow_mul]
  calc 2 ^ ((3 * ν n / 4 + 11) * 4) ≤ 2 ^ (44 + ν n * 3) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ 44 * (2 ^ ν n) ^ 3 := by rw [pow_add, pow_mul]
    _ ≤ 2 ^ 44 * (n + 2) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (two_pow_ν_le n) 3)

/-! ## Limbs -/

/-- Limb `i` of `x` in base `2^b`. -/
def limb (b x i : ℕ) : ℕ := x / 2 ^ (b * i) % 2 ^ b

/-- The number with the limbs `f 0, …, f (k−1)` in base `2^b`. -/
def ofLimbs (b : ℕ) (f : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ range k, f i * 2 ^ (b * i)

theorem limb_lt (b x i : ℕ) : limb b x i < 2 ^ b := Nat.mod_lt _ (by positivity)

theorem ofLimbs_succ (b : ℕ) (f : ℕ → ℕ) (k : ℕ) :
    ofLimbs b f (k + 1) = ofLimbs b f k + f k * 2 ^ (b * k) := Finset.sum_range_succ _ _

theorem ofLimbs_limb_mod (b x k : ℕ) : ofLimbs b (limb b x) k = x % 2 ^ (b * k) := by
  induction k with
  | zero => simp [ofLimbs, Nat.mod_one]
  | succ k ih =>
    rw [ofLimbs_succ, ih, mul_add, mul_one, pow_add, Nat.mod_mul]
    unfold limb; ring

/-- **The limbs of `x < 2^{bk}` give back `x`.** -/
theorem ofLimbs_limb (b x k : ℕ) (h : x < 2 ^ (b * k)) : ofLimbs b (limb b x) k = x := by
  rw [ofLimbs_limb_mod, Nat.mod_eq_of_lt h]

theorem ofLimbs_lt (b : ℕ) (f : ℕ → ℕ) (k : ℕ) (hf : ∀ i < k, f i < 2 ^ b) :
    ofLimbs b f k < 2 ^ (b * k) := by
  induction k with
  | zero => simp [ofLimbs]
  | succ k ih =>
    rw [ofLimbs_succ, mul_add, mul_one, pow_add]
    have h1 := ih fun i hi => hf i (by omega)
    have h2 : f k + 1 ≤ 2 ^ b := hf k (by omega)
    calc ofLimbs b f k + f k * 2 ^ (b * k) < 2 ^ (b * k) + f k * 2 ^ (b * k) := by omega
      _ = (f k + 1) * 2 ^ (b * k) := by ring
      _ ≤ 2 ^ b * 2 ^ (b * k) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (b * k) * 2 ^ b := by ring

theorem ofLimbs_congr (b : ℕ) {f f' : ℕ → ℕ} (k : ℕ) (h : ∀ i < k, f i = f' i) :
    ofLimbs b f k = ofLimbs b f' k :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

/-- **The limbs of `ofLimbs`** (limbs `< 2^b`). -/
theorem limb_ofLimbs (b : ℕ) (f : ℕ → ℕ) (k : ℕ) (hf : ∀ i < k, f i < 2 ^ b) (i : ℕ) (hi : i < k) :
    limb b (ofLimbs b f k) i = f i := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [ofLimbs_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
    · have hlt : ofLimbs b f k < 2 ^ (b * k) := ofLimbs_lt b f k fun j hj => hf j (by omega)
      have e : ofLimbs b f k + f k * 2 ^ (b * k) = ofLimbs b f k + 2 ^ (b * (i + 1)) *
          (f k * 2 ^ (b * k - b * (i + 1))) := by
        rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (Nat.mul_le_mul_left b hi')]
      have hr := ofLimbs_limb_mod b (ofLimbs b f k + f k * 2 ^ (b * k)) (i + 1)
      have hr2 := ofLimbs_limb_mod b (ofLimbs b f k) (i + 1)
      have hm : (ofLimbs b f k + f k * 2 ^ (b * k)) % 2 ^ (b * (i + 1)) =
          ofLimbs b f k % 2 ^ (b * (i + 1)) := by
        rw [e, Nat.add_mul_mod_self_left]
      rw [hm, ← hr2] at hr
      have hsucc := ofLimbs_succ b (limb b (ofLimbs b f k + f k * 2 ^ (b * k))) i
      have hsucc2 := ofLimbs_succ b (limb b (ofLimbs b f k)) i
      have hlow : ofLimbs b (limb b (ofLimbs b f k + f k * 2 ^ (b * k))) i =
          ofLimbs b (limb b (ofLimbs b f k)) i := by
        rw [ofLimbs_limb_mod, ofLimbs_limb_mod]
        have e2 : ofLimbs b f k + f k * 2 ^ (b * k) = ofLimbs b f k + 2 ^ (b * i) *
            (f k * 2 ^ (b * k - b * i)) := by
          rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (Nat.mul_le_mul_left b (by omega))]
        rw [e2, Nat.add_mul_mod_self_left]
      rw [hsucc, hsucc2, hlow] at hr
      have hli : limb b (ofLimbs b f k + f k * 2 ^ (b * k)) i = limb b (ofLimbs b f k) i := by
        have hp : 0 < 2 ^ (b * i) := by positivity
        exact Nat.eq_of_mul_eq_mul_right hp (by omega)
      rw [hli]
      exact ih (fun j hj => hf j (by omega)) hi'
    · have hlt : ofLimbs b f i < 2 ^ (b * i) := ofLimbs_lt b f i fun j hj => hf j (by omega)
      unfold limb
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add,
        Nat.mod_eq_of_lt (hf i hi)]

/-- The 2D limb array of `x`: entry `(i1, i2)` is limb `i1 + ℓ1·i2`. -/
def pA (n x : ℕ) (i1 i2 : ℕ) : ℕ := limb (b n) x (i1 + ℓ1 n * i2)

/-- Limb `k` of `N`. -/
def Nk (n N k : ℕ) : ℕ := limb (b n) N k

/-! ## The prefix pattern and the count `D` -/

/-- The big-endian value of a word (`π[0]` is the top bit). -/
def bev (π : List Bool) : ℕ := π.foldl (fun a x => 2 * a + x.toNat) 0

theorem bev_append_singleton (π : List Bool) (x : Bool) : bev (π ++ [x]) = 2 * bev π + x.toNat := by
  unfold bev; rw [List.foldl_append]; rfl

theorem bev_nil : bev [] = 0 := rfl

/-- Bit `j` (lowest first) of the first factor `p`: fixed to `0` at `j ≥ n`, to the prefix bit
`π.reverse[j − (n − t)]` (= `π[n−1−j]`) at `n − t ≤ j < n`, free below (`t = π.length`). -/
def patBit (n : ℕ) (π : List Bool) (j : ℕ) : Option Bool :=
  if n ≤ j then some false
  else if n - π.length ≤ j then some (π.reverse.getD (j - (n - π.length)) false) else none

/-- The pattern of the `nB n` bits of `p`. -/
def pat (n : ℕ) (π : List Bool) : List (Option Bool) := (List.range (nB n)).map (patBit n π)

theorem length_pat (n : ℕ) (π : List Bool) : (pat n π).length = nB n := by simp [pat]

theorem pat_getD (n : ℕ) (π : List Bool) {j : ℕ} (hj : j < nB n) : (pat n π).getD j none = patBit n π j := by
  simp [pat, List.getD_eq_getElem?_getD, hj]

/-- A bit `x` agrees with a pattern entry (`none` = free). -/
def obit : Option Bool → Bool → Bool
  | none, _ => true
  | some v, x => x == v

/-- Limb `i` with value `x` matches the pattern `pt` on its `b` bits. -/
def patOK (n : ℕ) (pt : List (Option Bool)) (i x : ℕ) : Bool :=
  (List.range (b n)).all fun j => obit (pt.getD (b n * i + j) none) (x.testBit j)

/-- The count over a box `[0, 2^{n'})²`: pairs with `p·q = N` whose first factor has the prefix `π`
(`p / 2^{n−t} = bev π`). -/
def Dw (n' N n : ℕ) (π : List Bool) : ℕ :=
  ((range (2 ^ n') ×ˢ range (2 ^ n')).filter
    fun pq => pq.1 * pq.2 = N ∧ pq.1 / 2 ^ (n - π.length) = bev π).card

/-- **`D(N, n, π)`**: the value of the multiplication network. -/
def D (N n : ℕ) (π : List Bool) : ℕ := Dw (nB n) N n π

/-! ## The pipeline (plain `ℕ`, residues mod `M`) -/

/-- Row transforms: `A(s, i2) = Σ_{i1<ℓ1} x(i1, i2) ω^{i1 s} mod M`, `s < L1`. -/
def rowDFT (n : ℕ) (x : ℕ → ℕ → ℕ) (s i2 : ℕ) : ℕ := (∑ i1 ∈ range (ℓ1 n), x i1 i2 * wP n (i1 * s)) % M n

/-- Column transforms: `F(s, t) = Σ_{i2<ℓ2} A(s, i2) ω^{i2 t} mod M`, `t < L2`. -/
def colDFT (n : ℕ) (A : ℕ → ℕ → ℕ) (s t : ℕ) : ℕ := (∑ i2 ∈ range (ℓ2 n), A s i2 * wP n (i2 * t)) % M n

/-- Pointwise product mod `M`. -/
def pointwise (n : ℕ) (P Q : ℕ → ℕ → ℕ) (s t : ℕ) : ℕ := P s t * Q s t % M n

/-- Inverse column transforms: `D(s, u) = L1⁻¹ Σ_{t<L2} C(s, t) ω^{(L2−u) t} mod M`. -/
def invCol (n : ℕ) (C : ℕ → ℕ → ℕ) (s u : ℕ) : ℕ :=
  (iL n * ∑ t ∈ range (L2 n), C s t * wP n ((L2 n - u) * t)) % M n

/-- Inverse row transforms: `E(a, u) = L1⁻¹ Σ_{s<L1} D(s, u) ω^{(L1−a) s} mod M`. -/
def invRow (n : ℕ) (E : ℕ → ℕ → ℕ) (a u : ℕ) : ℕ :=
  (iL n * ∑ s ∈ range (L1 n), E s u * wP n ((L1 n - a) * s)) % M n

/-- The Kronecker collapse `c_k = Σ_{a + ℓ1 u = k} C(a, u)` (`a < L1`, `u < L2`). -/
def convCoeff (n : ℕ) (C : ℕ → ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ a ∈ range (L1 n), ∑ u ∈ range (L2 n), if a + ℓ1 n * u = k then C a u else 0

/-- The carry chain: `r 0 = 0`, `r (k+1) = (c k + r k − N_k) / 2^b`. -/
def carryChain (n : ℕ) (c Nl : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (c k + carryChain n c Nl k - Nl k) / 2 ^ b n

theorem carryChain_zero (n : ℕ) (c Nl : ℕ → ℕ) : carryChain n c Nl 0 = 0 := rfl
theorem carryChain_succ (n : ℕ) (c Nl : ℕ → ℕ) (k : ℕ) :
    carryChain n c Nl (k + 1) = (c k + carryChain n c Nl k - Nl k) / 2 ^ b n := rfl

/-! ### The canonical stages of `(p, q)` -/

def stA (n x : ℕ) : ℕ → ℕ → ℕ := rowDFT n (pA n x)
def stF (n x : ℕ) : ℕ → ℕ → ℕ := colDFT n (stA n x)
def stC (n p q : ℕ) : ℕ → ℕ → ℕ := pointwise n (stF n p) (stF n q)
def stD (n p q : ℕ) : ℕ → ℕ → ℕ := invCol n (stC n p q)
def stE (n p q : ℕ) : ℕ → ℕ → ℕ := invRow n (stD n p q)
/-- The collapsed coefficients `c_k`. -/
def stc (n p q : ℕ) : ℕ → ℕ := convCoeff n (stE n p q)
/-- The carries `r_k`. -/
def stR (n N p q : ℕ) : ℕ → ℕ := carryChain n (stc n p q) (Nk n N)

/-! ## Wires and vertices -/

/-- The wires (all of width `W`): limbs `pL, qL (i1, i2)`; row transforms `Ap, Aq (s, i2)`; column
transforms `Pf, Qf (s, t)`; pointwise products `Cf (s, t)`; inverse columns `Dc (s, u)`; inverse
rows `Cc (a, u)` (the 2D convolution coefficients); carries `rr j = r_{j+1}` (from position `j` to
`j + 1`, `j + 1 < Kc`). -/
inductive WD where
  | pL (i1 i2 : ℕ)
  | qL (i1 i2 : ℕ)
  | Ap (s i2 : ℕ)
  | Aq (s i2 : ℕ)
  | Pf (s t : ℕ)
  | Qf (s t : ℕ)
  | Cf (s t : ℕ)
  | Dc (s u : ℕ)
  | Cc (a u : ℕ)
  | rr (j : ℕ)
  deriving DecidableEq

/-- The index ranges of the wires. -/
def WD.Valid (n : ℕ) : WD → Prop
  | .pL i1 i2 => i1 < ℓ1 n ∧ i2 < ℓ2 n
  | .qL i1 i2 => i1 < ℓ1 n ∧ i2 < ℓ2 n
  | .Ap s i2 => s < L1 n ∧ i2 < ℓ2 n
  | .Aq s i2 => s < L1 n ∧ i2 < ℓ2 n
  | .Pf s t => s < L1 n ∧ t < L2 n
  | .Qf s t => s < L1 n ∧ t < L2 n
  | .Cf s t => s < L1 n ∧ t < L2 n
  | .Dc s u => s < L1 n ∧ u < L2 n
  | .Cc a u => a < L1 n ∧ u < L2 n
  | .rr j => j + 1 < Kc n

instance (n : ℕ) : DecidablePred (WD.Valid n) := fun d => by
  cases d <;> unfold WD.Valid <;> infer_instance

/-- The vertices (checks): pattern/range cells, row/column transforms of `p` and `q`, pointwise
products, inverse columns, inverse rows, carry positions. -/
inductive VD where
  | cellP (i1 i2 : ℕ)
  | cellQ (i1 i2 : ℕ)
  | rowP (i2 : ℕ)
  | rowQ (i2 : ℕ)
  | colP (s : ℕ)
  | colQ (s : ℕ)
  | mul (s t : ℕ)
  | icol (s : ℕ)
  | irow (u : ℕ)
  | carry (k : ℕ)
  deriving DecidableEq

/-- The index ranges of the vertices. -/
def VD.Valid (n : ℕ) : VD → Prop
  | .cellP i1 i2 => i1 < ℓ1 n ∧ i2 < ℓ2 n
  | .cellQ i1 i2 => i1 < ℓ1 n ∧ i2 < ℓ2 n
  | .rowP i2 => i2 < ℓ2 n
  | .rowQ i2 => i2 < ℓ2 n
  | .colP s => s < L1 n
  | .colQ s => s < L1 n
  | .mul s t => s < L1 n ∧ t < L2 n
  | .icol s => s < L1 n
  | .irow u => u < L2 n
  | .carry k => k < Kc n

instance (n : ℕ) : DecidablePred (VD.Valid n) := fun v => by
  cases v <;> unfold VD.Valid <;> infer_instance

/-! ### Index ranges -/

theorem blk_lt {x y w h : ℕ} (hx : x < w) (hy : y < h) : x + w * y < w * h :=
  calc x + w * y < w + w * y := by omega
    _ = w * (y + 1) := by ring
    _ ≤ w * h := Nat.mul_le_mul_left _ hy

theorem blk_mod {x w : ℕ} (y : ℕ) (hx : x < w) : (x + w * y) % w = x := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem blk_div {x w : ℕ} (y : ℕ) (hx : x < w) : (x + w * y) / w = y := by
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hx, zero_add]

theorem blk_dec {j w h : ℕ} (hj : j < w * h) : j % w < w ∧ j / w < h := by
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · simp at hj
    · exact hw
  exact ⟨Nat.mod_lt _ hw, (Nat.div_lt_iff_lt_mul hw).2 (by rw [mul_comm]; exact hj)⟩

/-- The number of wires: `2ℓ + 2·L1·ℓ2 + 5·L1·L2 + (Kc − 1)`. -/
def numWires (n : ℕ) : ℕ := 2 * ℓ n + 2 * nA n + 5 * nF n + (Kc n - 1)

/-- The index of a wire. -/
def wireIdx (n : ℕ) : WD → ℕ
  | .pL i1 i2 => i1 + ℓ1 n * i2
  | .qL i1 i2 => ℓ n + (i1 + ℓ1 n * i2)
  | .Ap s i2 => 2 * ℓ n + (s + L1 n * i2)
  | .Aq s i2 => 2 * ℓ n + nA n + (s + L1 n * i2)
  | .Pf s t => 2 * ℓ n + 2 * nA n + (s + L1 n * t)
  | .Qf s t => 2 * ℓ n + 2 * nA n + nF n + (s + L1 n * t)
  | .Cf s t => 2 * ℓ n + 2 * nA n + 2 * nF n + (s + L1 n * t)
  | .Dc s u => 2 * ℓ n + 2 * nA n + 3 * nF n + (s + L1 n * u)
  | .Cc a u => 2 * ℓ n + 2 * nA n + 4 * nF n + (a + L1 n * u)
  | .rr j => 2 * ℓ n + 2 * nA n + 5 * nF n + j

/-- The wire with a given index. -/
def wireOf (n j : ℕ) : WD :=
  if j < ℓ n then .pL (j % ℓ1 n) (j / ℓ1 n)
  else if j < 2 * ℓ n then .qL ((j - ℓ n) % ℓ1 n) ((j - ℓ n) / ℓ1 n)
  else if j < 2 * ℓ n + nA n then .Ap ((j - 2 * ℓ n) % L1 n) ((j - 2 * ℓ n) / L1 n)
  else if j < 2 * ℓ n + 2 * nA n then
    .Aq ((j - (2 * ℓ n + nA n)) % L1 n) ((j - (2 * ℓ n + nA n)) / L1 n)
  else if j < 2 * ℓ n + 2 * nA n + nF n then
    .Pf ((j - (2 * ℓ n + 2 * nA n)) % L1 n) ((j - (2 * ℓ n + 2 * nA n)) / L1 n)
  else if j < 2 * ℓ n + 2 * nA n + 2 * nF n then
    .Qf ((j - (2 * ℓ n + 2 * nA n + nF n)) % L1 n) ((j - (2 * ℓ n + 2 * nA n + nF n)) / L1 n)
  else if j < 2 * ℓ n + 2 * nA n + 3 * nF n then
    .Cf ((j - (2 * ℓ n + 2 * nA n + 2 * nF n)) % L1 n) ((j - (2 * ℓ n + 2 * nA n + 2 * nF n)) / L1 n)
  else if j < 2 * ℓ n + 2 * nA n + 4 * nF n then
    .Dc ((j - (2 * ℓ n + 2 * nA n + 3 * nF n)) % L1 n) ((j - (2 * ℓ n + 2 * nA n + 3 * nF n)) / L1 n)
  else if j < 2 * ℓ n + 2 * nA n + 5 * nF n then
    .Cc ((j - (2 * ℓ n + 2 * nA n + 4 * nF n)) % L1 n) ((j - (2 * ℓ n + 2 * nA n + 4 * nF n)) / L1 n)
  else .rr (j - (2 * ℓ n + 2 * nA n + 5 * nF n))

theorem wireOf_valid {n j : ℕ} (hj : j < numWires n) : (wireOf n j).Valid n := by
  have hl : ℓ n = ℓ1 n * ℓ2 n := rfl
  have hA : nA n = L1 n * ℓ2 n := rfl
  have hF : nF n = L1 n * L2 n := rfl
  unfold numWires at hj
  unfold wireOf
  split_ifs <;> simp only [WD.Valid] <;> first
    | exact blk_dec (by rw [← hl]; omega)
    | exact blk_dec (by rw [← hA]; omega)
    | exact blk_dec (by rw [← hF]; omega)
    | omega

theorem wireIdx_lt {n : ℕ} {d : WD} (hd : d.Valid n) : wireIdx n d < numWires n := by
  have hK := Kc_pos n
  unfold numWires
  cases d <;> simp only [WD.Valid] at hd <;> simp only [wireIdx]
  all_goals first
    | (have := blk_lt (w := ℓ1 n) hd.1 hd.2; change _ < ℓ n at this; omega)
    | (have := blk_lt (w := L1 n) hd.1 hd.2; change _ < nA n at this; omega)
    | (have := blk_lt (w := L1 n) hd.1 hd.2; change _ < nF n at this; omega)
    | omega

theorem wireIdx_wireOf (n j : ℕ) : wireIdx n (wireOf n j) = j := by
  unfold wireOf
  split_ifs <;> simp only [wireIdx, Nat.mod_add_div] <;> omega

theorem wireOf_wireIdx {n : ℕ} {d : WD} (hd : d.Valid n) : wireOf n (wireIdx n d) = d := by
  cases d <;> simp only [WD.Valid] at hd <;> simp only [wireIdx, wireOf]
  case pL i1 i2 =>
    have h := blk_lt (w := ℓ1 n) hd.1 hd.2; change _ < ℓ n at h
    simp only [show i1 + ℓ1 n * i2 < ℓ n by omega, ↓reduceIte, blk_mod _ hd.1, blk_div _ hd.1]
  case qL i1 i2 =>
    have h := blk_lt (w := ℓ1 n) hd.1 hd.2; change _ < ℓ n at h
    simp only [show ¬ (ℓ n + (i1 + ℓ1 n * i2) < ℓ n) by omega, show ℓ n + (i1 + ℓ1 n * i2) < 2 * ℓ n by omega, ↓reduceIte, Nat.add_sub_cancel_left, blk_mod _ hd.1, blk_div _ hd.1]
  case Ap s i2 =>
    have h := blk_lt (w := L1 n) hd.1 hd.2; change _ < nA n at h
    simp only [show ¬ (2 * ℓ n + (s + L1 n * i2) < ℓ n) by omega, show ¬ (2 * ℓ n + (s + L1 n * i2) < 2 * ℓ n) by omega, show 2 * ℓ n + (s + L1 n * i2) < 2 * ℓ n + nA n by omega, ↓reduceIte, Nat.add_sub_cancel_left, blk_mod _ hd.1, blk_div _ hd.1]
  case Aq s i2 =>
    have h := blk_lt (w := L1 n) hd.1 hd.2; change _ < nA n at h
    simp only [show ¬ (2 * ℓ n + nA n + (s + L1 n * i2) < ℓ n) by omega, show ¬ (2 * ℓ n + nA n + (s + L1 n * i2) < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + nA n + (s + L1 n * i2) < 2 * ℓ n + nA n) by omega, show 2 * ℓ n + nA n + (s + L1 n * i2) < 2 * ℓ n + 2 * nA n by omega, ↓reduceIte, Nat.add_sub_cancel_left, blk_mod _ hd.1, blk_div _ hd.1]
  case Pf s t =>
    have h := blk_lt (w := L1 n) hd.1 hd.2; change _ < nF n at h
    simp only [show ¬ (2 * ℓ n + 2 * nA n + (s + L1 n * t) < ℓ n) by omega, show ¬ (2 * ℓ n + 2 * nA n + (s + L1 n * t) < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + 2 * nA n + (s + L1 n * t) < 2 * ℓ n + nA n) by omega, show ¬ (2 * ℓ n + 2 * nA n + (s + L1 n * t) < 2 * ℓ n + 2 * nA n) by omega, show 2 * ℓ n + 2 * nA n + (s + L1 n * t) < 2 * ℓ n + 2 * nA n + nF n by omega, ↓reduceIte, Nat.add_sub_cancel_left, blk_mod _ hd.1, blk_div _ hd.1]
  case Qf s t =>
    have h := blk_lt (w := L1 n) hd.1 hd.2; change _ < nF n at h
    simp only [show ¬ (2 * ℓ n + 2 * nA n + nF n + (s + L1 n * t) < ℓ n) by omega, show ¬ (2 * ℓ n + 2 * nA n + nF n + (s + L1 n * t) < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + 2 * nA n + nF n + (s + L1 n * t) < 2 * ℓ n + nA n) by omega, show ¬ (2 * ℓ n + 2 * nA n + nF n + (s + L1 n * t) < 2 * ℓ n + 2 * nA n) by omega, show ¬ (2 * ℓ n + 2 * nA n + nF n + (s + L1 n * t) < 2 * ℓ n + 2 * nA n + nF n) by omega, show 2 * ℓ n + 2 * nA n + nF n + (s + L1 n * t) < 2 * ℓ n + 2 * nA n + 2 * nF n by omega, ↓reduceIte, Nat.add_sub_cancel_left, blk_mod _ hd.1, blk_div _ hd.1]
  case Cf s t =>
    have h := blk_lt (w := L1 n) hd.1 hd.2; change _ < nF n at h
    simp only [show ¬ (2 * ℓ n + 2 * nA n + 2 * nF n + (s + L1 n * t) < ℓ n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 2 * nF n + (s + L1 n * t) < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 2 * nF n + (s + L1 n * t) < 2 * ℓ n + nA n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 2 * nF n + (s + L1 n * t) < 2 * ℓ n + 2 * nA n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 2 * nF n + (s + L1 n * t) < 2 * ℓ n + 2 * nA n + nF n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 2 * nF n + (s + L1 n * t) < 2 * ℓ n + 2 * nA n + 2 * nF n) by omega, show 2 * ℓ n + 2 * nA n + 2 * nF n + (s + L1 n * t) < 2 * ℓ n + 2 * nA n + 3 * nF n by omega, ↓reduceIte, Nat.add_sub_cancel_left, blk_mod _ hd.1, blk_div _ hd.1]
  case Dc s u =>
    have h := blk_lt (w := L1 n) hd.1 hd.2; change _ < nF n at h
    simp only [show ¬ (2 * ℓ n + 2 * nA n + 3 * nF n + (s + L1 n * u) < ℓ n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 3 * nF n + (s + L1 n * u) < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 3 * nF n + (s + L1 n * u) < 2 * ℓ n + nA n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 3 * nF n + (s + L1 n * u) < 2 * ℓ n + 2 * nA n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 3 * nF n + (s + L1 n * u) < 2 * ℓ n + 2 * nA n + nF n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 3 * nF n + (s + L1 n * u) < 2 * ℓ n + 2 * nA n + 2 * nF n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 3 * nF n + (s + L1 n * u) < 2 * ℓ n + 2 * nA n + 3 * nF n) by omega, show 2 * ℓ n + 2 * nA n + 3 * nF n + (s + L1 n * u) < 2 * ℓ n + 2 * nA n + 4 * nF n by omega, ↓reduceIte, Nat.add_sub_cancel_left, blk_mod _ hd.1, blk_div _ hd.1]
  case Cc a u =>
    have h := blk_lt (w := L1 n) hd.1 hd.2; change _ < nF n at h
    simp only [show ¬ (2 * ℓ n + 2 * nA n + 4 * nF n + (a + L1 n * u) < ℓ n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 4 * nF n + (a + L1 n * u) < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 4 * nF n + (a + L1 n * u) < 2 * ℓ n + nA n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 4 * nF n + (a + L1 n * u) < 2 * ℓ n + 2 * nA n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 4 * nF n + (a + L1 n * u) < 2 * ℓ n + 2 * nA n + nF n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 4 * nF n + (a + L1 n * u) < 2 * ℓ n + 2 * nA n + 2 * nF n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 4 * nF n + (a + L1 n * u) < 2 * ℓ n + 2 * nA n + 3 * nF n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 4 * nF n + (a + L1 n * u) < 2 * ℓ n + 2 * nA n + 4 * nF n) by omega, show 2 * ℓ n + 2 * nA n + 4 * nF n + (a + L1 n * u) < 2 * ℓ n + 2 * nA n + 5 * nF n by omega, ↓reduceIte, Nat.add_sub_cancel_left, blk_mod _ hd.1, blk_div _ hd.1]
  case rr j =>
    simp only [show ¬ (2 * ℓ n + 2 * nA n + 5 * nF n + j < ℓ n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 5 * nF n + j < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 5 * nF n + j < 2 * ℓ n + nA n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 5 * nF n + j < 2 * ℓ n + 2 * nA n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 5 * nF n + j < 2 * ℓ n + 2 * nA n + nF n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 5 * nF n + j < 2 * ℓ n + 2 * nA n + 2 * nF n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 5 * nF n + j < 2 * ℓ n + 2 * nA n + 3 * nF n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 5 * nF n + j < 2 * ℓ n + 2 * nA n + 4 * nF n) by omega, show ¬ (2 * ℓ n + 2 * nA n + 5 * nF n + j < 2 * ℓ n + 2 * nA n + 5 * nF n) by omega, ↓reduceIte, Nat.add_sub_cancel_left]

/-- The number of vertices: `2ℓ + 2ℓ2 + 3·L1 + L1·L2 + L2 + Kc`. -/
def numVerts (n : ℕ) : ℕ := 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n + Kc n

/-- The index of a vertex. -/
def vertIdx (n : ℕ) : VD → ℕ
  | .cellP i1 i2 => i1 + ℓ1 n * i2
  | .cellQ i1 i2 => ℓ n + (i1 + ℓ1 n * i2)
  | .rowP i2 => 2 * ℓ n + i2
  | .rowQ i2 => 2 * ℓ n + ℓ2 n + i2
  | .colP s => 2 * ℓ n + 2 * ℓ2 n + s
  | .colQ s => 2 * ℓ n + 2 * ℓ2 n + L1 n + s
  | .mul s t => 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + (s + L1 n * t)
  | .icol s => 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n + s
  | .irow u => 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + u
  | .carry k => 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n + k

/-- The vertex with a given index. -/
def vertOf (n j : ℕ) : VD :=
  if j < ℓ n then .cellP (j % ℓ1 n) (j / ℓ1 n)
  else if j < 2 * ℓ n then .cellQ ((j - (ℓ n)) % ℓ1 n) ((j - (ℓ n)) / ℓ1 n)
  else if j < 2 * ℓ n + ℓ2 n then .rowP (j - (2 * ℓ n))
  else if j < 2 * ℓ n + 2 * ℓ2 n then .rowQ (j - (2 * ℓ n + ℓ2 n))
  else if j < 2 * ℓ n + 2 * ℓ2 n + L1 n then .colP (j - (2 * ℓ n + 2 * ℓ2 n))
  else if j < 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n then .colQ (j - (2 * ℓ n + 2 * ℓ2 n + L1 n))
  else if j < 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n then .mul ((j - (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n)) % L1 n) ((j - (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n)) / L1 n)
  else if j < 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n then .icol (j - (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n))
  else if j < 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n then .irow (j - (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n))
  else .carry (j - (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n))

theorem vertOf_valid {n j : ℕ} (hj : j < numVerts n) : (vertOf n j).Valid n := by
  have hl : ℓ n = ℓ1 n * ℓ2 n := rfl
  have hF : nF n = L1 n * L2 n := rfl
  unfold numVerts at hj
  unfold vertOf
  split_ifs <;> simp only [VD.Valid] <;> first
    | exact blk_dec (by rw [← hl]; omega)
    | exact blk_dec (by rw [← hF]; omega)
    | omega

theorem vertIdx_lt {n : ℕ} {v : VD} (hv : v.Valid n) : vertIdx n v < numVerts n := by
  unfold numVerts
  cases v <;> simp only [VD.Valid] at hv <;> simp only [vertIdx]
  all_goals first
    | (have := blk_lt (w := ℓ1 n) hv.1 hv.2; change _ < ℓ n at this; omega)
    | (have := blk_lt (w := L1 n) hv.1 hv.2; change _ < nF n at this; omega)
    | omega

theorem vertIdx_vertOf (n j : ℕ) : vertIdx n (vertOf n j) = j := by
  unfold vertOf
  split_ifs <;> simp only [vertIdx, Nat.mod_add_div] <;> omega

theorem vertOf_vertIdx {n : ℕ} {v : VD} (hv : v.Valid n) : vertOf n (vertIdx n v) = v := by
  cases v <;> simp only [VD.Valid] at hv <;> simp only [vertIdx, vertOf]
  case cellP i1 i2 =>
    have h := blk_lt (w := ℓ1 n) hv.1 hv.2; change _ < ℓ n at h
    simp only [show i1 + ℓ1 n * i2 < ℓ n by omega, ↓reduceIte, blk_mod _ hv.1, blk_div _ hv.1]
  case cellQ i1 i2 =>
    have h := blk_lt (w := ℓ1 n) hv.1 hv.2; change _ < ℓ n at h
    simp only [show ¬ (ℓ n + (i1 + ℓ1 n * i2) < ℓ n) by omega, show ℓ n + (i1 + ℓ1 n * i2) < 2 * ℓ n by omega, ↓reduceIte, Nat.add_sub_cancel_left, blk_mod _ hv.1, blk_div _ hv.1]
  case rowP i2 =>
    simp only [show ¬ (2 * ℓ n + i2 < ℓ n) by omega, show ¬ (2 * ℓ n + i2 < 2 * ℓ n) by omega, show 2 * ℓ n + i2 < 2 * ℓ n + ℓ2 n by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  case rowQ i2 =>
    simp only [show ¬ (2 * ℓ n + ℓ2 n + i2 < ℓ n) by omega, show ¬ (2 * ℓ n + ℓ2 n + i2 < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + ℓ2 n + i2 < 2 * ℓ n + ℓ2 n) by omega, show 2 * ℓ n + ℓ2 n + i2 < 2 * ℓ n + 2 * ℓ2 n by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  case colP s =>
    simp only [show ¬ (2 * ℓ n + 2 * ℓ2 n + s < ℓ n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + s < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + s < 2 * ℓ n + ℓ2 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + s < 2 * ℓ n + 2 * ℓ2 n) by omega, show 2 * ℓ n + 2 * ℓ2 n + s < 2 * ℓ n + 2 * ℓ2 n + L1 n by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  case colQ s =>
    simp only [show ¬ (2 * ℓ n + 2 * ℓ2 n + L1 n + s < ℓ n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + L1 n + s < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + L1 n + s < 2 * ℓ n + ℓ2 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + L1 n + s < 2 * ℓ n + 2 * ℓ2 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + L1 n + s < 2 * ℓ n + 2 * ℓ2 n + L1 n) by omega, show 2 * ℓ n + 2 * ℓ2 n + L1 n + s < 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  case mul s t =>
    have h := blk_lt (w := L1 n) hv.1 hv.2; change _ < nF n at h
    simp only [show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + (s + L1 n * t) < ℓ n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + (s + L1 n * t) < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + (s + L1 n * t) < 2 * ℓ n + ℓ2 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + (s + L1 n * t) < 2 * ℓ n + 2 * ℓ2 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + (s + L1 n * t) < 2 * ℓ n + 2 * ℓ2 n + L1 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + (s + L1 n * t) < 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n) by omega, show 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + (s + L1 n * t) < 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n by omega, ↓reduceIte, Nat.add_sub_cancel_left, blk_mod _ hv.1, blk_div _ hv.1]
  case icol s =>
    simp only [show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n + s < ℓ n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n + s < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n + s < 2 * ℓ n + ℓ2 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n + s < 2 * ℓ n + 2 * ℓ2 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n + s < 2 * ℓ n + 2 * ℓ2 n + L1 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n + s < 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n + s < 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n) by omega, show 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n + s < 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  case irow u =>
    simp only [show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + u < ℓ n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + u < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + u < 2 * ℓ n + ℓ2 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + u < 2 * ℓ n + 2 * ℓ2 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + u < 2 * ℓ n + 2 * ℓ2 n + L1 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + u < 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + u < 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + u < 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n) by omega, show 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + u < 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  case carry k =>
    simp only [show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n + k < ℓ n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n + k < 2 * ℓ n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n + k < 2 * ℓ n + ℓ2 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n + k < 2 * ℓ n + 2 * ℓ2 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n + k < 2 * ℓ n + 2 * ℓ2 n + L1 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n + k < 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n + k < 2 * ℓ n + 2 * ℓ2 n + 2 * L1 n + nF n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n + k < 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n) by omega, show ¬ (2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n + k < 2 * ℓ n + 2 * ℓ2 n + 3 * L1 n + nF n + L2 n) by omega, ↓reduceIte, Nat.add_sub_cancel_left]

/-! ### The two ends of a wire -/

/-- The two vertices a wire joins (producer, consumer). -/
def ends (n : ℕ) : WD → VD × VD
  | .pL i1 i2 => (.cellP i1 i2, .rowP i2)
  | .qL i1 i2 => (.cellQ i1 i2, .rowQ i2)
  | .Ap s i2 => (.rowP i2, .colP s)
  | .Aq s i2 => (.rowQ i2, .colQ s)
  | .Pf s t => (.colP s, .mul s t)
  | .Qf s t => (.colQ s, .mul s t)
  | .Cf s t => (.mul s t, .icol s)
  | .Dc s u => (.icol s, .irow u)
  | .Cc a u => (.irow u, .carry (a + ℓ1 n * u))
  | .rr j => (.carry j, .carry (j + 1))

theorem Cc_pos_lt {n a u : ℕ} (ha : a < L1 n) (hu : u < L2 n) : a + ℓ1 n * u < Kc n := by
  have := Nat.mul_lt_mul_of_pos_left hu (one_le_ℓ1 n)
  unfold Kc; omega

theorem ends_valid {n : ℕ} {d : WD} (hd : d.Valid n) : (ends n d).1.Valid n ∧ (ends n d).2.Valid n := by
  cases d <;> simp only [WD.Valid] at hd <;> simp only [ends, VD.Valid]
  case pL => exact ⟨hd, hd.2⟩
  case qL => exact ⟨hd, hd.2⟩
  case Ap => exact ⟨hd.2, hd.1⟩
  case Aq => exact ⟨hd.2, hd.1⟩
  case Pf => exact ⟨hd.1, hd⟩
  case Qf => exact ⟨hd.1, hd⟩
  case Cf => exact ⟨hd, hd.1⟩
  case Dc => exact ⟨hd.1, hd.2⟩
  case Cc a u => exact ⟨hd.2, Cc_pos_lt hd.1 hd.2⟩
  case rr j => omega

/-! ## Clusters -/

/-- The stage of a vertex. -/
def VD.stage : VD → ℕ
  | .cellP _ _ => 0
  | .cellQ _ _ => 1
  | .rowP _ => 2
  | .rowQ _ => 3
  | .colP _ => 4
  | .colQ _ => 5
  | .mul _ _ => 6
  | .icol _ => 7
  | .irow _ => 8
  | .carry _ => 9

/-- The index of a vertex within its stage. -/
def VD.idx (n : ℕ) : VD → ℕ
  | .cellP i1 i2 => i1 + ℓ1 n * i2
  | .cellQ i1 i2 => i1 + ℓ1 n * i2
  | .rowP i2 => i2
  | .rowQ i2 => i2
  | .colP s => s
  | .colQ s => s
  | .mul s t => s + L1 n * t
  | .icol s => s
  | .irow u => u
  | .carry k => k

/-- The number of vertices of a stage. -/
def stSize (n : ℕ) : ℕ → ℕ
  | 0 => ℓ n
  | 1 => ℓ n
  | 2 => ℓ2 n
  | 3 => ℓ2 n
  | 4 => L1 n
  | 5 => L1 n
  | 6 => nF n
  | 7 => L1 n
  | 8 => L2 n
  | _ => Kc n

theorem VD.idx_lt {n : ℕ} {v : VD} (hv : v.Valid n) : v.idx n < stSize n v.stage := by
  cases v <;> simp only [VD.Valid] at hv <;> simp only [VD.idx, VD.stage, stSize]
  all_goals first | exact blk_lt hv.1 hv.2 | exact hv

/-- **The cluster of a vertex**: each stage is cut into `g` contiguous blocks (`VB.vbN`). -/
def clus (n g : ℕ) (v : VD) : ℕ := ExactHC.VB.vbN (stSize n v.stage) g (v.idx n)

theorem clus_lt {n g : ℕ} {v : VD} (hv : v.Valid n) (hg : 1 ≤ g) : clus n g v < g :=
  ExactHC.VB.vbN_lt (VD.idx_lt hv) hg

/-- The pair of nodes of an item whose ends lie in the clusters `a`, `c`: `(min, max)` if `a ≠ c`;
if `a = c`: `(a, a+1)` when `a + 1 < g`, else `(0, a)`. -/
def lohi (g a c : ℕ) : ℕ × ℕ :=
  if a < c then (a, c) else if c < a then (c, a) else if a + 1 < g then (a, a + 1) else (0, a)

theorem lohi_lt {g a c : ℕ} (ha : a < g) (hc : c < g) (hg : 2 ≤ g) :
    (lohi g a c).1 < (lohi g a c).2 ∧ (lohi g a c).2 < g := by
  unfold lohi; split_ifs <;> simp only <;> omega

theorem lohi_mem (g a c : ℕ) :
    ((lohi g a c).1 = a ∨ (lohi g a c).2 = a) ∧ ((lohi g a c).1 = c ∨ (lohi g a c).2 = c) := by
  unfold lohi; split_ifs <;> (try simp) <;> omega

/-- The lower node of a wire. -/
def wLo (n g : ℕ) (d : WD) : ℕ := (lohi g (clus n g (ends n d).1) (clus n g (ends n d).2)).1
/-- The upper node of a wire. -/
def wHi (n g : ℕ) (d : WD) : ℕ := (lohi g (clus n g (ends n d).1) (clus n g (ends n d).2)).2

theorem wLo_lt_wHi {n g : ℕ} {d : WD} (hd : d.Valid n) (hg : 2 ≤ g) : wLo n g d < wHi n g d :=
  (lohi_lt (clus_lt (ends_valid hd).1 (by omega)) (clus_lt (ends_valid hd).2 (by omega)) hg).1

theorem wHi_lt {n g : ℕ} {d : WD} (hd : d.Valid n) (hg : 2 ≤ g) : wHi n g d < g :=
  (lohi_lt (clus_lt (ends_valid hd).1 (by omega)) (clus_lt (ends_valid hd).2 (by omega)) hg).2

theorem wLo_lt {n g : ℕ} {d : WD} (hd : d.Valid n) (hg : 2 ≤ g) : wLo n g d < g :=
  (wLo_lt_wHi hd hg).trans (wHi_lt hd hg)

/-- Both ends of a wire lie in clusters that are nodes of its pair. -/
theorem clus_ends_mem (n g : ℕ) (d : WD) :
    (clus n g (ends n d).1 = wLo n g d ∨ clus n g (ends n d).1 = wHi n g d) ∧
      (clus n g (ends n d).2 = wLo n g d ∨ clus n g (ends n d).2 = wHi n g d) := by
  have h := lohi_mem g (clus n g (ends n d).1) (clus n g (ends n d).2)
  unfold wLo wHi
  exact ⟨h.1.imp Eq.symm Eq.symm, h.2.imp Eq.symm Eq.symm⟩

/-! ## The checks -/

/-- The carry check at one position: `N_k ≤ c + r_in`, `2^b ∣ c + r_in − N_k`,
`r_out = (c + r_in − N_k) / 2^b`. -/
def carryOK (n Nl c rin rout : ℕ) : Bool :=
  decide (Nl ≤ c + rin) && decide ((c + rin - Nl) % 2 ^ b n = 0) && rout == (c + rin - Nl) / 2 ^ b n

/-- **The check of a vertex** on the wire values `x` (context: `n`, `N`, the pattern `pt`). -/
def chk (n N : ℕ) (pt : List (Option Bool)) (x : WD → ℕ) : VD → Bool
  | .cellP i1 i2 => decide (x (.pL i1 i2) < 2 ^ b n) && patOK n pt (i1 + ℓ1 n * i2) (x (.pL i1 i2))
  | .cellQ i1 i2 => decide (x (.qL i1 i2) < 2 ^ b n)
  | .rowP i2 => (List.range (L1 n)).all fun s =>
      x (.Ap s i2) == rowDFT n (fun i1 i2 => x (.pL i1 i2)) s i2
  | .rowQ i2 => (List.range (L1 n)).all fun s =>
      x (.Aq s i2) == rowDFT n (fun i1 i2 => x (.qL i1 i2)) s i2
  | .colP s => (List.range (L2 n)).all fun t =>
      x (.Pf s t) == colDFT n (fun s i2 => x (.Ap s i2)) s t
  | .colQ s => (List.range (L2 n)).all fun t =>
      x (.Qf s t) == colDFT n (fun s i2 => x (.Aq s i2)) s t
  | .mul s t => x (.Cf s t) == pointwise n (fun s t => x (.Pf s t)) (fun s t => x (.Qf s t)) s t
  | .icol s => (List.range (L2 n)).all fun u =>
      x (.Dc s u) == invCol n (fun s t => x (.Cf s t)) s u
  | .irow u => (List.range (L1 n)).all fun a =>
      x (.Cc a u) == invRow n (fun s u => x (.Dc s u)) a u
  | .carry k => carryOK n (Nk n N k) (convCoeff n (fun a u => x (.Cc a u)) k)
      (if k = 0 then 0 else x (.rr (k - 1))) (if k + 1 < Kc n then x (.rr k) else 0)

/-- The canonical wire values of `(p, q)`: the stages of the pipeline. -/
def run (n N p q : ℕ) : WD → ℕ
  | .pL i1 i2 => pA n p i1 i2
  | .qL i1 i2 => pA n q i1 i2
  | .Ap s i2 => stA n p s i2
  | .Aq s i2 => stA n q s i2
  | .Pf s t => stF n p s t
  | .Qf s t => stF n q s t
  | .Cf s t => stC n p q s t
  | .Dc s u => stD n p q s u
  | .Cc a u => stE n p q a u
  | .rr j => stR n N p q (j + 1)

/-! ## The package -/

open Eight.SecNetworks in
/-- **A uniform multiplication-network package** with the absolute constant `c₀` (the hypothesis
of the factoring rate theorem; modelled on `T2.UPackage`). ONE context type, ONE set of procedures,
ONE polynomial-time reader `prep : (g in unary, (w, π)) ↦ context`, ONE constant `q`; for every
`g ≥ 2`, every input word `w` with `N = ofWord w ≥ 1` and every prefix `π` with `|π| ≤ |w| = n`:
the network `net g w π` is a network with parameters `P, B, τ, S` given by `Np`, its value is
`D(N, n, π)`, `U ≤ c₀(n+2)`, `P ≤ c₀((n+2)/g + dg n)`, `B, τ, S + size(prep …) ≤ q(n+g+2)^q`. -/
structure MulPackage (c₀ : ℕ) : Type 1 where
  Ctx : Type
  [encCtx : Enc Ctx]
  [sizeCtx : HasSize Ctx]
  [carriedCtx : Carried Ctx]
  Np : Procs Ctx
  keeps : Np.Keeps
  P_unary : Unary Np.P
  B_unary : Unary Np.B
  /-- The reader: `(g in unary, (input word, prefix)) ↦ context`. -/
  prep : List Unit × (List Bool × List Bool) → Ctx
  prep_poly : PolyT prep
  q : ℕ
  net : ∀ g : ℕ, List Bool → List Bool → Net g
  P : ℕ → List Bool → List Bool → ℕ
  B : ℕ → List Bool → List Bool → ℕ
  τ : ℕ → List Bool → List Bool → ℕ
  S : ℕ → List Bool → List Bool → ℕ
  isNet : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → 1 ≤ ofWord w → π.length ≤ w.length →
    IsNetwork Np (prep (Printed.unary g, (w, π))) (net g w π) (P g w π) (B g w π) (τ g w π) (S g w π)
  value : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → 1 ≤ ofWord w → π.length ≤ w.length →
    (net g w π).value = (D (ofWord w) w.length π : ℤ)
  U_le : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → 1 ≤ ofWord w → π.length ≤ w.length →
    (net g w π).U ≤ c₀ * (w.length + 2)
  P_le : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → 1 ≤ ofWord w → π.length ≤ w.length →
    P g w π ≤ c₀ * ((w.length + 2) / g + dg w.length)
  B_le : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → 1 ≤ ofWord w → π.length ≤ w.length →
    B g w π ≤ q * (w.length + g + 2) ^ q
  τ_le : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → 1 ≤ ofWord w → π.length ≤ w.length →
    τ g w π ≤ q * (w.length + g + 2) ^ q
  S_le : ∀ (g : ℕ) (w π : List Bool), 2 ≤ g → 1 ≤ ofWord w → π.length ≤ w.length →
    S g w π + size (prep (Printed.unary g, (w, π))) ≤ q * (w.length + g + 2) ^ q

attribute [instance] MulPackage.encCtx MulPackage.sizeCtx MulPackage.carriedCtx

/-! ## Counting facts -/

theorem nA_eq (n : ℕ) : nA n = 2 * ℓ n := by
  unfold nA ℓ; rw [L1_eq_two_mul]; ring

theorem ℓ1L2_eq (n : ℕ) : ℓ1 n * L2 n = 2 * ℓ n := by
  unfold ℓ; rw [L2_eq_L1, L1_eq_two_mul, ℓ2_eq_ℓ1]; ring

theorem nF_eq (n : ℕ) : nF n = 4 * ℓ n := by
  unfold nF ℓ; rw [L2_eq_L1, L1_eq_two_mul, ℓ2_eq_ℓ1]; ring

theorem L1_le_ℓ (n : ℕ) : L1 n ≤ 2 * ℓ n := by
  rw [L1_eq_two_mul]; unfold ℓ; have := one_le_ℓ2 n; nlinarith

/-- **The number of wires.** -/
theorem numWires_le (n : ℕ) : numWires n ≤ 2 * ℓ n + 8 * (L1 n * L2 n) + 2 * (ℓ1 n * L2 n) + 2 := by
  have h1 := nA_eq n; have h2 := nF_eq n; have h3 := ℓ1L2_eq n; have h4 := L1_le_ℓ n
  have h5 : L1 n * L2 n = nF n := rfl
  unfold numWires Kc; omega

theorem numWires_le_ℓ (n : ℕ) : numWires n ≤ 30 * ℓ n := by
  have h1 := nA_eq n; have h2 := nF_eq n; have h3 := ℓ1L2_eq n; have h4 := L1_le_ℓ n
  unfold numWires Kc; omega

/-- **`numWires · W ≤ 2^14 (n+2)`** (so `U = 2·numWires·W = O(n)`). -/
theorem numWires_mul_W_le (n : ℕ) : numWires n * W n ≤ 2 ^ 14 * (n + 2) :=
  calc numWires n * W n ≤ 30 * ℓ n * W n := Nat.mul_le_mul_right _ (numWires_le_ℓ n)
    _ = 30 * (ℓ n * W n) := by ring
    _ ≤ 30 * (2 ^ 8 * (n + 2)) := Nat.mul_le_mul_left _ (ℓ_mul_W_le n)
    _ ≤ 2 ^ 14 * (n + 2) := by omega

theorem numVerts_le (n : ℕ) : numVerts n ≤ 24 * ℓ n := by
  have h2 := nF_eq n; have h3 := ℓ1L2_eq n; have h4 := L1_le_ℓ n
  have h5 : ℓ2 n ≤ ℓ n := by unfold ℓ; have := one_le_ℓ1 n; nlinarith
  have h6 : L2 n = L1 n := rfl
  unfold numVerts Kc; omega

/-! ## Locality: the wires a vertex reads -/

/-- The wires incident to a vertex. -/
def incW (n : ℕ) : VD → List WD
  | .cellP i1 i2 => [.pL i1 i2]
  | .cellQ i1 i2 => [.qL i1 i2]
  | .rowP i2 => (List.range (ℓ1 n)).map (fun i1 => .pL i1 i2) ++ (List.range (L1 n)).map (fun s => .Ap s i2)
  | .rowQ i2 => (List.range (ℓ1 n)).map (fun i1 => .qL i1 i2) ++ (List.range (L1 n)).map (fun s => .Aq s i2)
  | .colP s => (List.range (ℓ2 n)).map (fun i2 => .Ap s i2) ++ (List.range (L2 n)).map (fun t => .Pf s t)
  | .colQ s => (List.range (ℓ2 n)).map (fun i2 => .Aq s i2) ++ (List.range (L2 n)).map (fun t => .Qf s t)
  | .mul s t => [.Pf s t, .Qf s t, .Cf s t]
  | .icol s => (List.range (L2 n)).map (fun t => .Cf s t) ++ (List.range (L2 n)).map (fun u => .Dc s u)
  | .irow u => (List.range (L1 n)).map (fun s => .Dc s u) ++ (List.range (L1 n)).map (fun a => .Cc a u)
  | .carry k =>
      (List.range (L1 n)).filterMap (fun a =>
        if a ≤ k ∧ (k - a) % ℓ1 n = 0 ∧ (k - a) / ℓ1 n < L2 n then some (.Cc a ((k - a) / ℓ1 n)) else none) ++
      (if k = 0 then [] else [.rr (k - 1)]) ++ (if k + 1 < Kc n then [.rr k] else [])

theorem Cc_mem_incW {n a u k : ℕ} (ha : a < L1 n) (hu : u < L2 n) (hk : a + ℓ1 n * u = k) :
    WD.Cc a u ∈ incW n (.carry k) := by
  subst hk
  have h1 : a + ℓ1 n * u - a = ℓ1 n * u := Nat.add_sub_cancel_left a _
  have h2 : ℓ1 n * u / ℓ1 n = u := Nat.mul_div_cancel_left u (one_le_ℓ1 n)
  have h3 : a ≤ a + ℓ1 n * u ∧ (a + ℓ1 n * u - a) % ℓ1 n = 0 ∧ (a + ℓ1 n * u - a) / ℓ1 n < L2 n :=
    ⟨by omega, by rw [h1, Nat.mul_mod_right], by rw [h1, h2]; exact hu⟩
  simp only [incW, List.mem_append, List.mem_filterMap, List.mem_range]
  left; left
  exact ⟨a, ha, by rw [if_pos h3, h1, h2]⟩

/-- Every valid wire with an end at `v` is read by `v`. -/
theorem mem_incW {n : ℕ} {d : WD} {v : VD} (hd : d.Valid n) (he : (ends n d).1 = v ∨ (ends n d).2 = v) :
    d ∈ incW n v := by
  cases d <;> simp only [WD.Valid] at hd <;> simp only [ends] at he <;> rcases he with rfl | rfl
  case Cc.inr a u => exact Cc_mem_incW hd.1 hd.2 rfl
  case rr.inl j =>
    simp only [incW, List.mem_append]; right; rw [if_pos hd]; exact List.mem_singleton_self _
  case rr.inr j =>
    simp only [incW, List.mem_append]; left; right
    rw [if_neg (by omega), Nat.add_sub_cancel]; exact List.mem_singleton_self _
  all_goals simp [incW, hd.1, hd.2]

/-- The wires read by a valid vertex are valid and have an end at it. -/
theorem incW_spec {n : ℕ} {v : VD} {d : WD} (hv : v.Valid n) (hd : d ∈ incW n v) :
    d.Valid n ∧ ((ends n d).1 = v ∨ (ends n d).2 = v) := by
  cases v <;> simp only [VD.Valid] at hv
  case carry k =>
    simp only [incW, List.mem_append, List.mem_filterMap, List.mem_range] at hd
    rcases hd with (⟨a, ha, h⟩ | h) | h
    · split_ifs at h with hc
      · cases h
        obtain ⟨h1, h2, h3⟩ := hc
        refine ⟨⟨ha, h3⟩, Or.inr ?_⟩
        simp only [ends]
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h2)]
        congr 1; omega
    · split_ifs at h with hk
      · simp at h
      · rw [List.mem_singleton] at h; subst h
        refine ⟨by simp only [WD.Valid]; omega, Or.inr ?_⟩
        simp only [ends]; congr 1; omega
    · split_ifs at h with hk
      · rw [List.mem_singleton] at h; subst h
        exact ⟨hk, Or.inl rfl⟩
      · simp at h
  all_goals
    simp only [incW, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hd
    first
      | (rcases hd with rfl; exact ⟨hv, Or.inl rfl⟩)
      | (rcases hd with rfl | rfl | rfl <;> simp [WD.Valid, ends, hv.1, hv.2])
      | (rcases hd with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;> simp [WD.Valid, ends, hi, hv])

theorem length_incW_le {n : ℕ} {v : VD} (hv : v.Valid n) : (incW n v).length ≤ 2 * L1 n := by
  have h1 := two_le_L1 n
  have h2 : ℓ1 n ≤ L1 n := by rw [L1_eq_two_mul]; omega
  have h3 : L2 n = L1 n := rfl
  have h4 : ℓ2 n = ℓ1 n := rfl
  cases v <;> simp only [incW, List.length_append, List.length_map, List.length_range, List.length_cons,
    List.length_nil]
  case carry k =>
    have h5 := List.length_filterMap_le (fun a =>
        if a ≤ k ∧ (k - a) % ℓ1 n = 0 ∧ (k - a) / ℓ1 n < L2 n then some (WD.Cc a ((k - a) / ℓ1 n)) else none)
      (List.range (L1 n))
    rw [List.length_range] at h5
    split_ifs <;> simp only [List.length_nil, List.length_singleton] <;> omega
  all_goals omega

/-- **At most `2·L1` wires end at a vertex.** -/
theorem card_ends_le (n : ℕ) {v : VD} (hv : v.Valid n) :
    ((range (numWires n)).filter fun j => (ends n (wireOf n j)).1 = v ∨ (ends n (wireOf n j)).2 = v).card ≤
      2 * L1 n := by
  refine le_trans (card_le_card (t := ((incW n v).map (wireIdx n)).toFinset) ?_)
    (le_trans (List.toFinset_card_le _) (by rw [List.length_map]; exact length_incW_le hv))
  intro j hj
  rw [mem_filter, mem_range] at hj
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨wireOf n j, mem_incW (wireOf_valid hj.1) hj.2, wireIdx_wireOf n j⟩

/-! ### Congruence of the pipeline functions -/

theorem all_range_congr {k : ℕ} {f f' : ℕ → Bool} (h : ∀ s < k, f s = f' s) :
    (List.range k).all f = (List.range k).all f' := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range]
  exact ⟨fun H s hs => by rw [← h s hs]; exact H s hs, fun H s hs => by rw [h s hs]; exact H s hs⟩

theorem rowDFT_congr (n : ℕ) {x x' : ℕ → ℕ → ℕ} {i2 : ℕ} (h : ∀ i1 < ℓ1 n, x i1 i2 = x' i1 i2) (s : ℕ) :
    rowDFT n x s i2 = rowDFT n x' s i2 := by
  unfold rowDFT; rw [Finset.sum_congr rfl fun i1 hi1 => by rw [h i1 (Finset.mem_range.1 hi1)]]

theorem colDFT_congr (n : ℕ) {A A' : ℕ → ℕ → ℕ} {s : ℕ} (h : ∀ i2 < ℓ2 n, A s i2 = A' s i2) (t : ℕ) :
    colDFT n A s t = colDFT n A' s t := by
  unfold colDFT; rw [Finset.sum_congr rfl fun i2 hi2 => by rw [h i2 (Finset.mem_range.1 hi2)]]

theorem invCol_congr (n : ℕ) {C C' : ℕ → ℕ → ℕ} {s : ℕ} (h : ∀ t < L2 n, C s t = C' s t) (u : ℕ) :
    invCol n C s u = invCol n C' s u := by
  unfold invCol; rw [Finset.sum_congr rfl fun t ht => by rw [h t (Finset.mem_range.1 ht)]]

theorem invRow_congr (n : ℕ) {E E' : ℕ → ℕ → ℕ} {u : ℕ} (h : ∀ s < L1 n, E s u = E' s u) (a : ℕ) :
    invRow n E a u = invRow n E' a u := by
  unfold invRow; rw [Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.1 hs)]]

theorem convCoeff_congr (n : ℕ) {C C' : ℕ → ℕ → ℕ} {k : ℕ}
    (h : ∀ a < L1 n, ∀ u < L2 n, a + ℓ1 n * u = k → C a u = C' a u) :
    convCoeff n C k = convCoeff n C' k := by
  unfold convCoeff
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun u hu => ?_
  split_ifs with hk
  · exact h a (Finset.mem_range.1 ha) u (Finset.mem_range.1 hu) hk
  · rfl

/-- **The check of `v` reads only the wires of `incW n v`.** -/
theorem chk_local (n N : ℕ) (pt : List (Option Bool)) {x x' : WD → ℕ} (v : VD)
    (h : ∀ d ∈ incW n v, x d = x' d) : chk n N pt x v = chk n N pt x' v := by
  cases v
  case cellP i1 i2 => simp only [chk, h (.pL i1 i2) (by simp [incW])]
  case cellQ i1 i2 => simp only [chk, h (.qL i1 i2) (by simp [incW])]
  case rowP i2 =>
    simp only [chk]
    refine all_range_congr fun s hs => ?_
    rw [h (.Ap s i2) (by simp [incW, hs]),
      rowDFT_congr n (x := fun i1 i2 => x (.pL i1 i2)) (x' := fun i1 i2 => x' (.pL i1 i2))
        (fun i1 hi1 => h (.pL i1 i2) (by simp [incW, hi1]))]
  case rowQ i2 =>
    simp only [chk]
    refine all_range_congr fun s hs => ?_
    rw [h (.Aq s i2) (by simp [incW, hs]),
      rowDFT_congr n (x := fun i1 i2 => x (.qL i1 i2)) (x' := fun i1 i2 => x' (.qL i1 i2))
        (fun i1 hi1 => h (.qL i1 i2) (by simp [incW, hi1]))]
  case colP s =>
    simp only [chk]
    refine all_range_congr fun t ht => ?_
    rw [h (.Pf s t) (by simp [incW, ht]),
      colDFT_congr n (A := fun s i2 => x (.Ap s i2)) (A' := fun s i2 => x' (.Ap s i2))
        (fun i2 hi2 => h (.Ap s i2) (by simp [incW, hi2]))]
  case colQ s =>
    simp only [chk]
    refine all_range_congr fun t ht => ?_
    rw [h (.Qf s t) (by simp [incW, ht]),
      colDFT_congr n (A := fun s i2 => x (.Aq s i2)) (A' := fun s i2 => x' (.Aq s i2))
        (fun i2 hi2 => h (.Aq s i2) (by simp [incW, hi2]))]
  case mul s t =>
    simp only [chk, pointwise, h (.Pf s t) (by simp [incW]), h (.Qf s t) (by simp [incW]),
      h (.Cf s t) (by simp [incW])]
  case icol s =>
    simp only [chk]
    refine all_range_congr fun u hu => ?_
    rw [h (.Dc s u) (by simp [incW, hu]),
      invCol_congr n (C := fun s t => x (.Cf s t)) (C' := fun s t => x' (.Cf s t))
        (fun t ht => h (.Cf s t) (by simp [incW, ht]))]
  case irow u =>
    simp only [chk]
    refine all_range_congr fun a ha => ?_
    rw [h (.Cc a u) (by simp [incW, ha]),
      invRow_congr n (E := fun s u => x (.Dc s u)) (E' := fun s u => x' (.Dc s u))
        (fun s hs => h (.Dc s u) (by simp [incW, hs]))]
  case carry k =>
    simp only [chk]
    rw [convCoeff_congr n (C := fun a u => x (.Cc a u)) (C' := fun a u => x' (.Cc a u))
        (fun a ha u hu hk => h (.Cc a u) (Cc_mem_incW ha hu hk))]
    congr 1
    · split_ifs with hk
      · rfl
      · exact h _ (by simp only [incW, List.mem_append]; left; right; rw [if_neg hk]; exact List.mem_singleton_self _)
    · split_ifs with hk
      · exact h _ (by simp only [incW, List.mem_append]; right; rw [if_pos hk]; exact List.mem_singleton_self _)
      · rfl

/-! ## The pattern cells enforce the prefix -/

theorem bev_eq_ofWord (π : List Bool) : bev π = ofWord π.reverse := by
  induction π using List.reverseRecOn with
  | nil => rfl
  | append_singleton π x ih =>
    rw [bev_append_singleton, List.reverse_append, List.reverse_singleton, List.singleton_append, ofWord, ih]
    ring

theorem testBit_ofWord (w : List Bool) (i : ℕ) : (ofWord w).testBit i = w.getD i false := by
  induction w generalizing i with
  | nil => simp [ofWord]
  | cons x w ih =>
    cases i with
    | zero => cases x <;> simp [ofWord, Nat.testBit_zero]
    | succ i =>
      rw [Nat.testBit_succ, List.getD_cons_succ, ← ih]
      congr 1
      have : x.toNat ≤ 1 := Bool.toNat_le x
      simp only [ofWord]; omega

theorem bev_lt (π : List Bool) : bev π < 2 ^ π.length := by
  rw [bev_eq_ofWord, ← List.length_reverse]; exact ofWord_lt _

theorem testBit_limb (b x i j : ℕ) (hj : j < b) : (limb b x i).testBit j = x.testBit (j + b * i) := by
  unfold limb
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hj]

/-- The pattern cells of all limbs ⟺ all bits of `p` below `nB n` agree with `patBit`. -/
theorem patOK_all_iff (n : ℕ) (π : List Bool) (p : ℕ) :
    (∀ i < ℓ n, patOK n (pat n π) i (limb (b n) p i) = true) ↔
      ∀ j < nB n, obit (patBit n π j) (p.testBit j) = true := by
  have hb := one_le_b n
  constructor
  · intro h j hj
    have hj' : j < b n * ℓ n := by unfold nB at hj; rw [mul_comm]; exact hj
    obtain ⟨h1, h2⟩ := blk_dec hj'
    have := h (j / b n) h2
    simp only [patOK, List.all_eq_true, List.mem_range] at this
    have e := this (j % b n) h1
    rw [testBit_limb _ _ _ _ h1, Nat.mod_add_div, add_comm, Nat.mod_add_div, pat_getD n π hj] at e
    exact e
  · intro h i hi
    simp only [patOK, List.all_eq_true, List.mem_range]
    intro j hj
    have hlt : j + b n * i < b n * ℓ n := blk_lt hj hi
    have hlt' : b n * i + j < nB n := by unfold nB; rw [mul_comm (ℓ n)]; omega
    rw [pat_getD n π hlt', testBit_limb _ _ _ _ hj, show j + b n * i = b n * i + j by ring]
    exact h _ hlt'

theorem bits_iff_div (n : ℕ) (π : List Bool) (hπ : π.length ≤ n) (p : ℕ) (hp : p < 2 ^ nB n) :
    (∀ j < nB n, obit (patBit n π j) (p.testBit j) = true) ↔ p / 2 ^ (n - π.length) = bev π := by
  have hn := le_nB n
  rw [bev_eq_ofWord]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, testBit_ofWord]
    by_cases hi : i < π.length
    · have h1 := h (i + (n - π.length)) (by omega)
      simp only [patBit, if_neg (show ¬ n ≤ i + (n - π.length) by omega),
        if_pos (show n - π.length ≤ i + (n - π.length) by omega), Nat.add_sub_cancel, obit,
        beq_iff_eq] at h1
      exact h1
    · rw [List.getD_eq_default _ _ (by rw [List.length_reverse]; omega)]
      by_cases hj : i + (n - π.length) < nB n
      · have h1 := h (i + (n - π.length)) hj
        simp only [patBit, if_pos (show n ≤ i + (n - π.length) by omega), obit, beq_iff_eq] at h1
        exact h1
      · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · intro h j hj
    have hb : ∀ i, p.testBit (i + (n - π.length)) = π.reverse.getD i false := by
      intro i; rw [← Nat.testBit_div_two_pow, h, testBit_ofWord]
    unfold patBit
    split_ifs with h1 h2
    · have := hb (j - (n - π.length))
      rw [Nat.sub_add_cancel (by omega), List.getD_eq_default _ _ (by rw [List.length_reverse]; omega)] at this
      simp [obit, this]
    · have := hb (j - (n - π.length))
      rw [Nat.sub_add_cancel h2] at this
      simp [obit, this]
    · rfl

/-- **The pattern cells enforce the prefix**: for `p < 2^{nB n}` and `|π| ≤ n`, all limbs of `p`
match `pat n π` iff `p / 2^{n−|π|} = bev π`. -/
theorem patOK_iff {n : ℕ} {π : List Bool} (hπ : π.length ≤ n) {p : ℕ} (hp : p < 2 ^ nB n) :
    (∀ i < ℓ n, patOK n (pat n π) i (limb (b n) p i) = true) ↔ p / 2 ^ (n - π.length) = bev π :=
  (patOK_all_iff n π p).trans (bits_iff_div n π hπ p hp)

/-! ## The checks as propositions; the canonical values -/

section ChkIff

variable {n N : ℕ} {pt : List (Option Bool)} {x : WD → ℕ}

theorem carryOK_iff {Nl c rin rout : ℕ} : carryOK n Nl c rin rout = true ↔
    Nl ≤ c + rin ∧ (c + rin - Nl) % 2 ^ b n = 0 ∧ rout = (c + rin - Nl) / 2 ^ b n := by
  simp [carryOK, and_assoc]

theorem chk_cellP_iff {i1 i2 : ℕ} : chk n N pt x (.cellP i1 i2) = true ↔
    x (.pL i1 i2) < 2 ^ b n ∧ patOK n pt (i1 + ℓ1 n * i2) (x (.pL i1 i2)) = true := by
  simp [chk]

theorem chk_cellQ_iff {i1 i2 : ℕ} : chk n N pt x (.cellQ i1 i2) = true ↔ x (.qL i1 i2) < 2 ^ b n := by
  simp [chk]

theorem chk_rowP_iff {i2 : ℕ} : chk n N pt x (.rowP i2) = true ↔
    ∀ s < L1 n, x (.Ap s i2) = rowDFT n (fun i1 i2 => x (.pL i1 i2)) s i2 := by
  simp [chk, List.all_eq_true]

theorem chk_rowQ_iff {i2 : ℕ} : chk n N pt x (.rowQ i2) = true ↔
    ∀ s < L1 n, x (.Aq s i2) = rowDFT n (fun i1 i2 => x (.qL i1 i2)) s i2 := by
  simp [chk, List.all_eq_true]

theorem chk_colP_iff {s : ℕ} : chk n N pt x (.colP s) = true ↔
    ∀ t < L2 n, x (.Pf s t) = colDFT n (fun s i2 => x (.Ap s i2)) s t := by
  simp [chk, List.all_eq_true]

theorem chk_colQ_iff {s : ℕ} : chk n N pt x (.colQ s) = true ↔
    ∀ t < L2 n, x (.Qf s t) = colDFT n (fun s i2 => x (.Aq s i2)) s t := by
  simp [chk, List.all_eq_true]

theorem chk_mul_iff {s t : ℕ} : chk n N pt x (.mul s t) = true ↔
    x (.Cf s t) = x (.Pf s t) * x (.Qf s t) % M n := by
  simp [chk, pointwise]

theorem chk_icol_iff {s : ℕ} : chk n N pt x (.icol s) = true ↔
    ∀ u < L2 n, x (.Dc s u) = invCol n (fun s t => x (.Cf s t)) s u := by
  simp [chk, List.all_eq_true]

theorem chk_irow_iff {u : ℕ} : chk n N pt x (.irow u) = true ↔
    ∀ a < L1 n, x (.Cc a u) = invRow n (fun s u => x (.Dc s u)) a u := by
  simp [chk, List.all_eq_true]

theorem chk_carry_iff {k : ℕ} : chk n N pt x (.carry k) = true ↔
    carryOK n (Nk n N k) (convCoeff n (fun a u => x (.Cc a u)) k)
      (if k = 0 then 0 else x (.rr (k - 1))) (if k + 1 < Kc n then x (.rr k) else 0) = true := by
  simp only [chk]

end ChkIff

section Run

variable (n N p q : ℕ) (pt : List (Option Bool))

theorem chk_run_cellP (i1 i2 : ℕ) :
    chk n N pt (run n N p q) (.cellP i1 i2) = patOK n pt (i1 + ℓ1 n * i2) (pA n p i1 i2) := by
  simp [chk, run, pA, limb_lt]

theorem chk_run_cellQ (i1 i2 : ℕ) : chk n N pt (run n N p q) (.cellQ i1 i2) = true := by
  simp [chk, run, pA, limb_lt]

theorem chk_run_rowP (i2 : ℕ) : chk n N pt (run n N p q) (.rowP i2) = true :=
  chk_rowP_iff.2 fun _ _ => rfl
theorem chk_run_rowQ (i2 : ℕ) : chk n N pt (run n N p q) (.rowQ i2) = true :=
  chk_rowQ_iff.2 fun _ _ => rfl
theorem chk_run_colP (s : ℕ) : chk n N pt (run n N p q) (.colP s) = true :=
  chk_colP_iff.2 fun _ _ => rfl
theorem chk_run_colQ (s : ℕ) : chk n N pt (run n N p q) (.colQ s) = true :=
  chk_colQ_iff.2 fun _ _ => rfl
theorem chk_run_mul (s t : ℕ) : chk n N pt (run n N p q) (.mul s t) = true :=
  chk_mul_iff.2 rfl
theorem chk_run_icol (s : ℕ) : chk n N pt (run n N p q) (.icol s) = true :=
  chk_icol_iff.2 fun _ _ => rfl
theorem chk_run_irow (u : ℕ) : chk n N pt (run n N p q) (.irow u) = true :=
  chk_irow_iff.2 fun _ _ => rfl

theorem chk_run_carry (k : ℕ) : chk n N pt (run n N p q) (.carry k) =
    carryOK n (Nk n N k) (stc n p q k) (stR n N p q k) (if k + 1 < Kc n then stR n N p q (k + 1) else 0) := by
  simp only [chk, run, stc]
  congr 1
  rcases k with _ | k
  · rfl
  · simp

end Run

theorem rowDFT_lt (n : ℕ) (x : ℕ → ℕ → ℕ) (s i2 : ℕ) : rowDFT n x s i2 < M n :=
  Nat.mod_lt _ (by have := one_lt_M n; omega)
theorem colDFT_lt (n : ℕ) (A : ℕ → ℕ → ℕ) (s t : ℕ) : colDFT n A s t < M n :=
  Nat.mod_lt _ (by have := one_lt_M n; omega)
theorem pointwise_lt (n : ℕ) (P Q : ℕ → ℕ → ℕ) (s t : ℕ) : pointwise n P Q s t < M n :=
  Nat.mod_lt _ (by have := one_lt_M n; omega)
theorem invCol_lt (n : ℕ) (C : ℕ → ℕ → ℕ) (s u : ℕ) : invCol n C s u < M n :=
  Nat.mod_lt _ (by have := one_lt_M n; omega)
theorem invRow_lt (n : ℕ) (E : ℕ → ℕ → ℕ) (a u : ℕ) : invRow n E a u < M n :=
  Nat.mod_lt _ (by have := one_lt_M n; omega)

/-- The canonical values fit in `W` bits, except possibly the carries. -/
theorem run_lt (n N p q : ℕ) (d : WD) (hd : ∀ j, d ≠ .rr j) : run n N p q d < 2 ^ W n := by
  have hM := M_lt_two_pow_W n
  have hb : 2 ^ b n ≤ 2 ^ W n := Nat.pow_le_pow_right (by norm_num) (by unfold W; have := b_le_J n; omega)
  cases d
  case rr j => exact absurd rfl (hd j)
  case pL i1 i2 => exact lt_of_lt_of_le (limb_lt _ _ _) hb
  case qL i1 i2 => exact lt_of_lt_of_le (limb_lt _ _ _) hb
  case Ap s i2 => exact (rowDFT_lt n (pA n p) s i2).trans hM
  case Aq s i2 => exact (rowDFT_lt n (pA n q) s i2).trans hM
  case Pf s t => exact (colDFT_lt n (stA n p) s t).trans hM
  case Qf s t => exact (colDFT_lt n (stA n q) s t).trans hM
  case Cf s t => exact (pointwise_lt n (stF n p) (stF n q) s t).trans hM
  case Dc s u => exact (invCol_lt n (stC n p q) s u).trans hM
  case Cc a u => exact (invRow_lt n (stD n p q) a u).trans hM

/-! ## At most two coefficients per carry position -/

/-- **`c_k` collects at most two coefficients**: if all `C a u ≤ B` then `convCoeff n C k ≤ 2B`. -/
theorem convCoeff_le (n : ℕ) (C : ℕ → ℕ → ℕ) (k B : ℕ) (hC : ∀ a < L1 n, ∀ u < L2 n, C a u ≤ B) :
    convCoeff n C k ≤ 2 * B := by
  have hl := one_le_ℓ1 n
  unfold convCoeff
  have inner : ∀ a ∈ range (L1 n), (∑ u ∈ range (L2 n), if a + ℓ1 n * u = k then C a u else 0) ≤
      if a % ℓ1 n = k % ℓ1 n then B else 0 := by
    intro a ha
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hS : ((range (L2 n)).filter fun u => a + ℓ1 n * u = k).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro u hu u' hu'
      simp only [mem_filter] at hu hu'
      exact Nat.eq_of_mul_eq_mul_left hl (by omega)
    split_ifs with hk
    · calc ∑ u ∈ (range (L2 n)).filter (fun u => a + ℓ1 n * u = k), C a u
          ≤ ∑ u ∈ (range (L2 n)).filter (fun u => a + ℓ1 n * u = k), B :=
            Finset.sum_le_sum fun u hu => hC a (mem_range.1 ha) u (mem_range.1 (mem_filter.1 hu).1)
        _ = ((range (L2 n)).filter fun u => a + ℓ1 n * u = k).card * B := by rw [sum_const, smul_eq_mul]
        _ ≤ 1 * B := Nat.mul_le_mul_right _ hS
        _ = B := one_mul B
    · have : (range (L2 n)).filter (fun u => a + ℓ1 n * u = k) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro u hu
        simp only [mem_filter] at hu
        apply hk; rw [← hu.2, Nat.add_mul_mod_self_left]
      rw [this, sum_empty]
  have hcard : ((range (L1 n)).filter fun a => a % ℓ1 n = k % ℓ1 n).card ≤ 2 := by
    have := card_le_card_of_injOn (t := range 2) (fun a => a / ℓ1 n) (s := (range (L1 n)).filter
      fun a => a % ℓ1 n = k % ℓ1 n) ?_ ?_
    · simpa using this
    · intro a ha
      simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at ha
      simp only [coe_range, Set.mem_Iio]
      rw [Nat.div_lt_iff_lt_mul hl]; rw [L1_eq_two_mul] at ha; linarith [ha.1]
    · intro a ha a' ha' h
      simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at ha ha'
      have e1 := Nat.mod_add_div a (ℓ1 n)
      have e2 := Nat.mod_add_div a' (ℓ1 n)
      simp only at h
      rw [← e1, ← e2, ha.2, ha'.2, h]
  calc _ ≤ ∑ a ∈ range (L1 n), (if a % ℓ1 n = k % ℓ1 n then B else 0) := sum_le_sum inner
    _ = ((range (L1 n)).filter fun a => a % ℓ1 n = k % ℓ1 n).card * B := by
        rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul]
    _ ≤ 2 * B := Nat.mul_le_mul_right _ hcard

end EthFollowup.Factoring
