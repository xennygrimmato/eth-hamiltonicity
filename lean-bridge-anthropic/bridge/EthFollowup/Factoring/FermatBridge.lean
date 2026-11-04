/-
# The factoring pipeline multiplies (module F1, Phase 2 bridge: `pipeline_eq_mul`)

Connects the Nat-level pipeline of `Params` (`stA … stE`, `stc`, `stR`, residues `% M n`) with the
pure-math layer `Factoring.Fermat` (`Pipeline.lean`, via casts into `ZMod (2^J+1)`):
* `stE_eq_aconv2`: the inverse-row stage is the 2D acyclic convolution of the limb arrays;
* `pipeline_eq_mul`: `ofLimbs b (stc n p q) Kc = p q` for `p, q < 2^{n'}`;
* `carry_checks_iff`: the carry conditions of the canonical run hold iff `p q = N`;
* bounds `stE_le`, `stc_le` (`c_k ≤ 2·2^J`), `stR_le`, `stR_lt` (`r_k < 2^W`);
* `carryChain_eq`: `carryChain n = Fermat.carry (b n)`.

Anthropic workspace only (imports `Params`). Standard axioms only.
-/
import EthFollowup.Factoring.Params
import EthFollowup.Factoring.Pipeline

set_option linter.unusedSectionVars false

namespace EthFollowup.Factoring

open Finset

/-- The recursive carry of `Params` is the carry of `Fermat.Carry`. -/
theorem carryChain_eq (n : ℕ) (c Nl : ℕ → ℕ) : carryChain n c Nl = Factoring.Fermat.carry (b n) c Nl := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih => rw [carryChain_succ, Factoring.Fermat.carry_succ, ih]

/-- **The pipeline computes the 2D acyclic convolution**: for `a < L1`, `u < L2`, the inverse-row
stage `stE n p q a u` equals `Σ_{i1+j1=a, i2+j2=u} pA p (i1,i2) · pA q (j1,j2)` (for all `p, q`). -/
theorem stE_eq_aconv2 (n p q : ℕ) : ∀ a < L1 n, ∀ u < L2 n,
    stE n p q a u = Factoring.Fermat.aconv2 (ℓ1 n) (ℓ2 n) (pA n p) (pA n q) a u := by
  have h1 : 2 * ℓ1 n ≤ 2 ^ m n := (L1_eq_two_mul n).symm.le
  have hJ : 0 < J n := one_le_J n
  exact Factoring.Fermat.stages_eq_aconv2 (one_le_m n) (L1_dvd_two_J n) hJ h1 h1 (ℓ_mul_pow_le n)
    (pA n p) (pA n q) (stA n p) (stA n q) (stF n p) (stF n q) (stC n p q) (stD n p q) (stE n p q)
    (fun _ _ => limb_lt _ _ _) (fun _ _ => limb_lt _ _ _)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

/-- Every stage-`E` value is a residue: `stE ≤ 2^J`. -/
theorem stE_le (n p q a u : ℕ) : stE n p q a u ≤ 2 ^ J n := by
  have : stE n p q a u < M n := Nat.mod_lt _ (by unfold M; positivity)
  unfold M at this; omega

/-- A carry position collects at most two coefficients: `c_k ≤ 2 · 2^J`. -/
theorem stc_le (n p q k : ℕ) : stc n p q k ≤ 2 * 2 ^ J n :=
  Factoring.Fermat.convCoeff_le (one_le_ℓ1 n) (L1_eq_two_mul n).le (stE n p q)
    (fun a _ u _ => stE_le n p q a u) k

/-- The carries stay below `2 · 2^J` (`< 2^W`). -/
theorem stR_le (n N p q k : ℕ) : stR n N p q k ≤ 2 * 2 ^ J n := by
  unfold stR; rw [carryChain_eq]
  exact Factoring.Fermat.carry_le (one_le_b n) (stc_le n p q) k

theorem stR_lt (n N p q k : ℕ) : stR n N p q k < 2 ^ W n := by
  have := stR_le n N p q k
  have : 2 ^ W n = 4 * 2 ^ J n := by unfold W; rw [pow_add]; ring
  have : 1 ≤ 2 ^ J n := Nat.one_le_two_pow
  omega

theorem b_mul_ℓ (n : ℕ) : b n * (ℓ1 n * ℓ2 n) = nB n := by unfold nB ℓ; ring

theorem nB_le_b_mul_Kc (n : ℕ) : nB n ≤ b n * Kc n := by
  rw [← b_mul_ℓ]; apply Nat.mul_le_mul_left; unfold Kc; rw [L2_eq_L1, ℓ2_eq_ℓ1, L1_eq_two_mul]
  nlinarith

/-- **`pipeline_eq_mul`**: for `p, q < 2^{n'}` (`n' = ℓ·b`), the collapsed convolution coefficients
`c_k = stc n p q k` of the Nat pipeline evaluate to `p · q`: `Σ_{k<Kc} c_k 2^{b k} = p q`. -/
theorem pipeline_eq_mul (n p q : ℕ) (hp : p < 2 ^ nB n) (hq : q < 2 ^ nB n) :
    ofLimbs (b n) (stc n p q) (Kc n) = p * q := by
  unfold ofLimbs stc convCoeff
  rw [Factoring.Fermat.convCoeff_eval (stE n p q) (fun a ha u hu => by
    have := Nat.mul_le_mul_left (ℓ1 n) hu.le
    unfold Kc; omega)]
  rw [← b_mul_ℓ] at hp hq
  exact Factoring.Fermat.stages_eval_mul (L := L1 n) (L1_eq_two_mul n).symm.le
    (L1_eq_two_mul n).symm.le hp hq (stE n p q) (stE_eq_aconv2 n p q)

/-- **The carry check of the canonical run**: for `p, q, N < 2^{n'}`, the carry conditions at
every position `k < Kc` (the outgoing carry being `0` at the last position) hold for the carries
`stR` iff `p q = N`. -/
theorem carry_checks_iff (n N p q : ℕ) (hp : p < 2 ^ nB n) (hq : q < 2 ^ nB n)
    (hN : N < 2 ^ nB n) :
    (∀ k < Kc n, Nk n N k ≤ stc n p q k + stR n N p q k ∧
      (stc n p q k + stR n N p q k - Nk n N k) % 2 ^ b n = 0 ∧
      (if k + 1 < Kc n then stR n N p q (k + 1) else 0) =
        (stc n p q k + stR n N p q k - Nk n N k) / 2 ^ b n) ↔ p * q = N := by
  have hN' : N < 2 ^ (b n * Kc n) :=
    lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) (nB_le_b_mul_Kc n))
  rw [← pipeline_eq_mul n p q hp hq]
  have key := Factoring.Fermat.chain_iff_carry hN' (stc n p q)
  have hR : stR n N p q = Factoring.Fermat.carry (b n) (stc n p q)
      (fun k => N / 2 ^ (b n * k) % 2 ^ b n) := carryChain_eq _ _ _
  unfold ofLimbs
  rw [← key, ← hR]
  have hK := Kc_pos n
  constructor
  · intro h
    refine ⟨rfl, ?_, fun k hk => ⟨(h k hk).1, (h k hk).2.1, rfl⟩⟩
    have := (h (Kc n - 1) (by omega)).2.2
    rw [if_neg (by omega)] at this
    have e : Kc n = Kc n - 1 + 1 := by omega
    rw [e]; exact this.symm
  · rintro ⟨-, hlast, hstep⟩ k hk
    refine ⟨(hstep k hk).1, (hstep k hk).2.1, ?_⟩
    split_ifs with h
    · rfl
    · have hk' : k = Kc n - 1 := by omega
      have : stR n N p q (Kc n - 1 + 1) = 0 := by rw [show Kc n - 1 + 1 = Kc n by omega]; exact hlast
      rw [hk']; exact this.symm

end EthFollowup.Factoring
