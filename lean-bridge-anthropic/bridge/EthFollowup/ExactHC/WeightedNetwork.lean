/-
# The weighted (TSP) Hamiltonian-cycle network in Anthropic's `Net g` format

Write-up: `research/exact-extensions.md`, row 2 (TSP via Kronecker substitution). This mirrors
`HCNetwork.lean` (M7) with the weighted tables of `Weighted.lean`: the node table of blob `a` is
`T_a(ℓ, y) = σ_a(ℓ) · χ_a(ℓ, y^{(a)}) · I^w_a(ℓ)`, where `I^w_a` carries the factor `z^{w_e}` for
every selected edge `e` (internal edges of `a`, and crossing edges whose low end is in `a`).

For a graph `G` on `Fin n`, a root `r`, a partition `β : Fin n → Fin g`, a crossing order
`X : Crossing G β m`, an integer `z` (the Kronecker point, `z = 2^b`) and weights
`w : Sym2 (Fin n) → ℕ`:

* `X.hcSystemW r z w : LabelSystem g (Fin m) (CopyIdx g) Label` (same items, copy bits and codes
  as `X.hcSystem r`; only the tables change).
* **Value** `hcNetW_value : ((X.hcSystemW r z w).net C).value = n · Σ_{H ∈ HC(G)} z^{w(H)}` for every
  code `C`, and `hcNetW_value_labelCode`.
* **Size of the tables**: `abs_Iw_le : |I^w_a(ℓ)| ≤ 2^{bW(|δ(a)| + |E_int(a)|)} · 6^{|E_int(a)|} 2^{|δ(a)|}`
  when `|z| ≤ 2^b` and all weights are `≤ W`; `abs_hcTW_lt : |T_a| < 2^{bWμ + 2μ + 1}` when
  `μ_a ≤ μ`.
* **Definition 2 bounds** `hcNetW_is : Is (q·μ + g² + 1) (b·W·μ + 2μ + 1)` for a `q`-bit label code,
  `hcNetW_is_labelCode : Is (3μ + g² + 1) (bWμ + 2μ + 1)`, and the Kronecker specialisation
  `hcNetW_is_kron` (`z = 2^b`). With weights given in binary (`W < 2^β`) and `b = O(n·β)` bits of
  precision, `B` is polynomial in the input size, as needed for Theorem A(b).
* `hcNetW_U : U = 2(m·q + #CopyIdx g)`, `hcNetW_U_le`.
-/
import EthFollowup.ExactHC.HCNetwork
import EthFollowup.ExactHC.Weighted

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset Grass Hamiltonian

noncomputable section

/-- `|z^k| ≤ 2^{bK}` when `|z| ≤ 2^b` and `k ≤ K`. -/
theorem abs_pow_le_two_pow {z : ℤ} {b k K : ℕ} (hz : |z| ≤ 2 ^ b) (hk : k ≤ K) :
    |z ^ k| ≤ 2 ^ (b * K) := by
  rw [abs_pow]
  calc |z| ^ k ≤ (2 ^ b) ^ k := pow_le_pow_left₀ (abs_nonneg z) hz k
    _ = 2 ^ (b * k) := by rw [← pow_mul]
    _ ≤ 2 ^ (b * K) := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left b hk)

namespace Crossing

variable {n g m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}
  (X : Crossing G β m) (r : Fin n) (z : ℤ) (w : Sym2 (Fin n) → ℕ)

/-! ### The size of the weighted blob sum -/

/-- **The size of the weighted blob sum**: with `|z| ≤ 2^b` and all weights `≤ W`,
`|I^w_a(ℓ)| ≤ 2^{bW(|δ(a)| + |E_int(a)|)} · 6^{|E_int(a)|} · 2^{|δ(a)|}`. -/
theorem abs_Iw_le {W b : ℕ} (hw : ∀ e, w e ≤ W) (hz : |z| ≤ 2 ^ b) (ℓ : Fin m → Label)
    (a : Fin g) :
    |X.Iw r z w ℓ a| ≤
      2 ^ (b * (W * ((X.chords.delta a).card + (Eint G β a).card))) *
        (6 ^ (Eint G β a).card * 2 ^ (X.chords.delta a).card) := by
  unfold Iw
  rw [abs_mul]
  have hA : |z ^ X.wtL w ℓ a| ≤ 2 ^ (b * ((X.chords.delta a).card * W)) :=
    abs_pow_le_two_pow hz (X.wtL_le w hw ℓ a)
  have hB : |∑ x ∈ (Eint G β a).powerset, X.degInd ℓ a x * z ^ wt w x *
        topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a)) (edgeProd r x * X.Gam r ℓ a)| ≤
      2 ^ (b * ((Eint G β a).card * W)) *
        (6 ^ (Eint G β a).card * 2 ^ (X.chords.delta a).card) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x ∈ (Eint G β a).powerset, |X.degInd ℓ a x * z ^ wt w x *
          topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a)) (edgeProd r x * X.Gam r ℓ a)|
        ≤ ∑ x ∈ (Eint G β a).powerset, (2 : ℤ) ^ (b * ((Eint G β a).card * W)) *
            ((5 : ℤ) ^ x.card * 2 ^ (X.chords.delta a).card) := by
          refine sum_le_sum fun x hx => ?_
          rw [abs_mul, abs_mul]
          have h1 : |X.degInd ℓ a x| ≤ 1 := by unfold degInd; split_ifs <;> simp
          have h2 : |z ^ wt w x| ≤ 2 ^ (b * ((Eint G β a).card * W)) :=
            abs_pow_le_two_pow hz (wt_le_of_subset hw (mem_powerset.1 hx))
          have h3 := (abs_topCoeff_le (isSignedBasis_OmegaSet r (blob β a)) _).trans
            ((norm1_mul_le _ _).trans (mul_le_mul (norm1_edgeProd_le r x) (X.norm1_Gam_le r ℓ a)
              (norm1_nonneg _) (by positivity)))
          calc |X.degInd ℓ a x| * |z ^ wt w x| * |topCoeff (genSet r (blob β a))
                (OmegaSet r (blob β a)) (edgeProd r x * X.Gam r ℓ a)|
              ≤ 1 * 2 ^ (b * ((Eint G β a).card * W)) *
                  ((5 : ℤ) ^ x.card * 2 ^ (X.chords.delta a).card) :=
                mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) h3 (abs_nonneg _)
                  (by positivity)
            _ = _ := by ring
      _ = 2 ^ (b * ((Eint G β a).card * W)) *
            (6 ^ (Eint G β a).card * 2 ^ (X.chords.delta a).card) := by
          rw [← mul_sum, ← sum_mul]
          congr 2
          have := sum_pow_mul_eq_add_pow (5 : ℤ) 1 (Eint G β a)
          simp only [one_pow, mul_one] at this
          rw [this]; norm_num
  calc |z ^ X.wtL w ℓ a| * |∑ x ∈ (Eint G β a).powerset, X.degInd ℓ a x * z ^ wt w x *
        topCoeff (genSet r (blob β a)) (OmegaSet r (blob β a)) (edgeProd r x * X.Gam r ℓ a)|
      ≤ 2 ^ (b * ((X.chords.delta a).card * W)) * (2 ^ (b * ((Eint G β a).card * W)) *
          (6 ^ (Eint G β a).card * 2 ^ (X.chords.delta a).card)) :=
        mul_le_mul hA hB (abs_nonneg _) (by positivity)
    _ = _ := by
        rw [show b * (W * ((X.chords.delta a).card + (Eint G β a).card)) =
          b * ((X.chords.delta a).card * W) + b * ((Eint G β a).card * W) by ring, pow_add]
        ring

/-! ### The weighted label system -/

/-- **The weighted Hamiltonian network**: the label system of `HCNetwork.lean` with the node
tables `T_a(ℓ, y) = σ_a(ℓ) · χ_a(ℓ, y^{(a)}) · I^w_a(ℓ)`. -/
def hcSystemW : LabelSystem g (Fin m) (CopyIdx g) Label :=
  { X.hcSystem r with
    T := fun a ℓ y => X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a (copyVec a y) *
      X.Iw r z w ℓ a
    T_local := fun a ℓ ℓ' y y' hℓ hy => by
      have hd : ∀ k ∈ X.chords.delta a, ℓ k = ℓ' k := fun k hk => hℓ k (X.mem_delta.1 hk)
      have hc : ∀ p ∈ Chords.Q a, copyVec a y p = copyVec a y' p := by
        intro p hp
        simp only [Chords.Q, mem_filter, mem_univ, true_and] at hp
        simp only [copyVec, dif_pos hp]
        rw [hy _ rfl]
      rw [X.sigma_congr hd, X.chi_congr hd hc, X.Iw_congr r z w hd] }

@[simp] theorem hcSystemW_T (a : Fin g) (ℓ : Fin m → Label) (y : CopyIdx g → Bool) :
    (X.hcSystemW r z w).T a ℓ y =
      X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a (copyVec a y) *
        X.Iw r z w ℓ a := rfl

/-- The node table fed the correct copy bits is `σ_a χ_a(P) I^w_a`. -/
theorem hcSystemW_T_par (a : Fin g) (ℓ : Fin m → Label) :
    (X.hcSystemW r z w).T a ℓ (fun j => (X.hcSystemW r z w).par j ℓ) =
      X.chords.sigma (labelPar ℓ) a *
        X.chords.chi (labelPar ℓ) a (fun p => X.chords.P (labelPar ℓ) p.1 p.2) *
        X.Iw r z w ℓ a := by
  rw [hcSystemW_T]
  congr 2
  refine X.chi_congr (fun _ _ => rfl) fun p hp => ?_
  simp only [Chords.Q, mem_filter, mem_univ, true_and] at hp
  simp only [copyVec, dif_pos hp]
  exact boolToZ_zToBool _

variable {q : ℕ} (C : LabelCode Label q)

/-- **The value of the weighted network** is `n · Σ_{H ∈ HC(G)} z^{w(H)}`. -/
theorem hcNetW_value :
    ((X.hcSystemW r z w).net C).value = n * ∑ H ∈ hamCycles G, z ^ wt w H := by
  rw [LabelSystem.value_net, ← blob_factorisation_w X r z w]
  exact sum_congr rfl fun ℓ _ => prod_congr rfl fun a _ => X.hcSystemW_T_par r z w a ℓ

/-- The value for the 3-bit code. -/
theorem hcNetW_value_labelCode :
    ((X.hcSystemW r z w).net labelCode).value = n * ∑ H ∈ hamCycles G, z ^ wt w H :=
  X.hcNetW_value r z w labelCode

/-! ### The parameters -/

/-- `|T_a(ℓ, y)| ≤ 2^{bW(|δ(a)| + |E_int(a)|) + 3|E_int(a)| + |δ(a)|}`. -/
theorem abs_hcTW_le {W b : ℕ} (hw : ∀ e, w e ≤ W) (hz : |z| ≤ 2 ^ b) (a : Fin g)
    (ℓ : Fin m → Label) (y : CopyIdx g → Bool) :
    |(X.hcSystemW r z w).T a ℓ y| ≤
      2 ^ (b * (W * ((X.chords.delta a).card + (Eint G β a).card)) +
        (3 * (Eint G β a).card + (X.chords.delta a).card)) := by
  rw [hcSystemW_T, abs_mul, abs_mul]
  have hs : ∀ x : ZMod 2, |sgn x| = 1 := fun x => by
    rcases sgn_eq_one_or_neg_one x with h | h <;> simp [h]
  rw [Chords.sigma, Chords.chi, hs, hs, one_mul, one_mul, pow_add]
  refine (X.abs_Iw_le r z w hw hz ℓ a).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [pow_add, pow_mul]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
    (by positivity)

/-- **The bound `B = bWμ + 2μ + 1`**: `|T_a(ℓ, y)| < 2^{bWμ + 2μ + 1}` for `μ ≥ max_a μ_a`. -/
theorem abs_hcTW_lt (μ W b : ℕ) (hμ : ∀ a, mu G β a ≤ μ) (hw : ∀ e, w e ≤ W)
    (hz : |z| ≤ 2 ^ b) (a : Fin g) (ℓ : Fin m → Label) (y : CopyIdx g → Bool) :
    |(X.hcSystemW r z w).T a ℓ y| < 2 ^ (b * W * μ + 2 * μ + 1) := by
  refine (X.abs_hcTW_le r z w hw hz a ℓ y).trans_lt (pow_lt_pow_right₀ (by norm_num) ?_)
  have h1 := X.two_Eint_add_delta_le a
  have h2 := hμ a
  have h3 : b * (W * ((X.chords.delta a).card + (Eint G β a).card)) ≤ b * W * μ := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have h4 : 3 * (Eint G β a).card + (X.chords.delta a).card < 2 * μ + 1 := by omega
  linarith

/-- The items incident to `a` are the crossing edges `δ(a)`. -/
theorem hcSystemW_card_inc (a : Fin g) :
    #(univ.filter ((X.hcSystemW r z w).Inc a)) = (X.chords.delta a).card := rfl

/-- The copy bits touching `a` number at most `g²` (same copy bits as `hcSystem`). -/
theorem hcSystemW_card_touch_le (a : Fin g) :
    #(univ.filter ((X.hcSystemW r z w).Touch a)) ≤ g ^ 2 :=
  X.hcSystem_card_touch_le r a

/-- **Definition 2 for the weighted network**: `Is (q·μ + g² + 1) (b·W·μ + 2μ + 1)` for a `q`-bit
label code, `μ ≥ max_a μ_a`, weights `≤ W` and `|z| ≤ 2^b`. -/
theorem hcNetW_is (μ W b : ℕ) (hμ : ∀ a, mu G β a ≤ μ) (hw : ∀ e, w e ≤ W)
    (hz : |z| ≤ 2 ^ b) :
    ((X.hcSystemW r z w).net C).Is (q * μ + g ^ 2 + 1) (b * W * μ + 2 * μ + 1) :=
  (X.hcSystemW r z w).net_is C (by omega) (by omega)
    (fun a => by
      rw [hcSystemW_card_inc]
      have h2 := X.hcSystemW_card_touch_le r z w a
      have h3 := Nat.mul_le_mul_right q ((X.card_delta_le_mu a).trans (hμ a))
      linarith)
    fun a ℓ y => X.abs_hcTW_lt r z w μ W b hμ hw hz a ℓ y

/-- **Definition 2** for the 3-bit label code: `Is (3μ + g² + 1) (bWμ + 2μ + 1)`. -/
theorem hcNetW_is_labelCode (μ W b : ℕ) (hμ : ∀ a, mu G β a ≤ μ) (hw : ∀ e, w e ≤ W)
    (hz : |z| ≤ 2 ^ b) :
    ((X.hcSystemW r z w).net labelCode).Is (3 * μ + g ^ 2 + 1) (b * W * μ + 2 * μ + 1) :=
  X.hcNetW_is r z w labelCode μ W b hμ hw hz

/-- The Kronecker point `z = 2^b` satisfies `|z| ≤ 2^b`. -/
theorem abs_two_pow_le (b : ℕ) : |(2 : ℤ) ^ b| ≤ 2 ^ b :=
  (abs_of_nonneg (by positivity)).le

/-- **Kronecker substitution** `z = 2^b`: value `n · Σ_H 2^{b·w(H)}` and
`Is (q·μ + g² + 1) (bWμ + 2μ + 1)`. -/
theorem hcNetW_kron (μ W b : ℕ) (hμ : ∀ a, mu G β a ≤ μ) (hw : ∀ e, w e ≤ W) :
    ((X.hcSystemW r (2 ^ b) w).net C).value = n * ∑ H ∈ hamCycles G, 2 ^ (b * wt w H) ∧
      ((X.hcSystemW r (2 ^ b) w).net C).Is (q * μ + g ^ 2 + 1) (b * W * μ + 2 * μ + 1) := by
  refine ⟨?_, X.hcNetW_is r (2 ^ b) w C μ W b hμ hw (abs_two_pow_le b)⟩
  rw [X.hcNetW_value r (2 ^ b) w C]
  simp only [← pow_mul]

/-- The value at the Kronecker point is (the cast of) the natural number
`n · Σ_H 2^{b·w(H)}` whose base-`2^b` digits `Hamiltonian.kronecker_decode` reads off. -/
theorem hcNetW_kron_value_natCast (b : ℕ) :
    ((X.hcSystemW r (2 ^ b) w).net C).value =
      ((n * ∑ H ∈ hamCycles G, 2 ^ (b * wt w H) : ℕ) : ℤ) := by
  rw [X.hcNetW_value r (2 ^ b) w C]
  push_cast
  simp only [pow_mul]

/-- The total `U = 2(q·m + #copy bits)` (unchanged by the weights). -/
theorem hcNetW_U : ((X.hcSystemW r z w).net C).U = 2 * (m * q + Fintype.card (CopyIdx g)) := by
  rw [LabelSystem.U_eq, Fintype.card_fin]

theorem hcNetW_U_le : ((X.hcSystemW r z w).net C).U ≤ 2 * (m * q + g ^ 3) := by
  rw [hcNetW_U]; have := card_copyIdx_le g; omega

end Crossing

end

end EthFollowup.ExactHC
