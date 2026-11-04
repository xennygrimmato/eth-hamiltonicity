/-
# Factoring, module F2 (part 2): parsimony and the value of the multiplication network

`scratchpad/plans/factoring-plan.md` §2 (Value, Parsimony); interface `facM-interface.md` (F2).

* `pOf n x`, `qOf n x`: the factors read off the limb wires.
* Stage induction (`eq_run`): if all checks pass on the wire values `x`, then `x` is the canonical
  assignment `run n N (pOf n x) (qOf n x)` on every valid wire.
* `run_all_iff`: for `p, q, N < 2^{nB}`, the canonical assignment passes all checks iff
  `p q = N` and every limb of `p` matches the pattern (`carry_checks_iff`, `chk_run_*`).
* `runL`: the canonical labelling; `mulNet_card`: the labellings passing all checks are in bijection
  with the pairs counted by `D`; **`mulNet_value`**: the value of `mulSys n N (pat n π) g` is
  `D N n π` of `Params` (`mulNet_value_search`: F6a's `Search.D N (nB n) n π`, `D_eq_search_D`).

Standard axioms only.
-/
import EthFollowup.Factoring.MulNetDefs

set_option linter.unusedSectionVars false

namespace EthFollowup.Factoring

open Finset EthFollowup.ExactHC

/-- The first factor read off the limb wires `pL` (limb `i` on the wire `pL (i % ℓ1) (i / ℓ1)`). -/
def pOf (n : ℕ) (x : WD → ℕ) : ℕ := ofLimbs (b n) (fun i => x (.pL (i % ℓ1 n) (i / ℓ1 n))) (ℓ n)

/-- The second factor read off the limb wires `qL`. -/
def qOf (n : ℕ) (x : WD → ℕ) : ℕ := ofLimbs (b n) (fun i => x (.qL (i % ℓ1 n) (i / ℓ1 n))) (ℓ n)

theorem pA_mod_div (n x i : ℕ) : pA n x (i % ℓ1 n) (i / ℓ1 n) = limb (b n) x i := by
  unfold pA; rw [Nat.mod_add_div]

/-! ## Stage induction: all checks force the canonical assignment -/

section Stages

variable {n N : ℕ} {pt : List (Option Bool)} {x : WD → ℕ}

theorem pL_lt_of_all (hall : ∀ v, v.Valid n → chk n N pt x v = true) :
    ∀ i < ℓ n, x (.pL (i % ℓ1 n) (i / ℓ1 n)) < 2 ^ b n := fun _ hi =>
  (chk_cellP_iff.1 (hall _ (show VD.Valid n (.cellP _ _) from blk_dec hi))).1

theorem qL_lt_of_all (hall : ∀ v, v.Valid n → chk n N pt x v = true) :
    ∀ i < ℓ n, x (.qL (i % ℓ1 n) (i / ℓ1 n)) < 2 ^ b n := fun _ hi =>
  chk_cellQ_iff.1 (hall _ (show VD.Valid n (.cellQ _ _) from blk_dec hi))

theorem pOf_lt (hall : ∀ v, v.Valid n → chk n N pt x v = true) : pOf n x < 2 ^ nB n := by
  have := ofLimbs_lt (b n) _ (ℓ n) (pL_lt_of_all hall)
  rwa [mul_comm] at this

theorem qOf_lt (hall : ∀ v, v.Valid n → chk n N pt x v = true) : qOf n x < 2 ^ nB n := by
  have := ofLimbs_lt (b n) _ (ℓ n) (qL_lt_of_all hall)
  rwa [mul_comm] at this

theorem limb_pOf (hall : ∀ v, v.Valid n → chk n N pt x v = true) {i1 i2 : ℕ} (h1 : i1 < ℓ1 n)
    (h2 : i2 < ℓ2 n) : pA n (pOf n x) i1 i2 = x (.pL i1 i2) := by
  unfold pA pOf
  rw [limb_ofLimbs _ _ _ (pL_lt_of_all hall) _ (blk_lt h1 h2)]
  simp only [blk_mod _ h1, blk_div _ h1]

theorem limb_qOf (hall : ∀ v, v.Valid n → chk n N pt x v = true) {i1 i2 : ℕ} (h1 : i1 < ℓ1 n)
    (h2 : i2 < ℓ2 n) : pA n (qOf n x) i1 i2 = x (.qL i1 i2) := by
  unfold pA qOf
  rw [limb_ofLimbs _ _ _ (qL_lt_of_all hall) _ (blk_lt h1 h2)]
  simp only [blk_mod _ h1, blk_div _ h1]

theorem eq_Ap (hall : ∀ v, v.Valid n → chk n N pt x v = true) {s i2 : ℕ} (hs : s < L1 n)
    (h2 : i2 < ℓ2 n) : x (.Ap s i2) = stA n (pOf n x) s i2 := by
  rw [(chk_rowP_iff.1 (hall _ (show VD.Valid n (.rowP i2) from h2))) s hs]
  exact rowDFT_congr n (fun i1 hi1 => (limb_pOf hall hi1 h2).symm) s

theorem eq_Aq (hall : ∀ v, v.Valid n → chk n N pt x v = true) {s i2 : ℕ} (hs : s < L1 n)
    (h2 : i2 < ℓ2 n) : x (.Aq s i2) = stA n (qOf n x) s i2 := by
  rw [(chk_rowQ_iff.1 (hall _ (show VD.Valid n (.rowQ i2) from h2))) s hs]
  exact rowDFT_congr n (fun i1 hi1 => (limb_qOf hall hi1 h2).symm) s

theorem eq_Pf (hall : ∀ v, v.Valid n → chk n N pt x v = true) {s t : ℕ} (hs : s < L1 n)
    (ht : t < L2 n) : x (.Pf s t) = stF n (pOf n x) s t := by
  rw [(chk_colP_iff.1 (hall _ (show VD.Valid n (.colP s) from hs))) t ht]
  exact colDFT_congr n (fun i2 hi2 => eq_Ap hall hs hi2) t

theorem eq_Qf (hall : ∀ v, v.Valid n → chk n N pt x v = true) {s t : ℕ} (hs : s < L1 n)
    (ht : t < L2 n) : x (.Qf s t) = stF n (qOf n x) s t := by
  rw [(chk_colQ_iff.1 (hall _ (show VD.Valid n (.colQ s) from hs))) t ht]
  exact colDFT_congr n (fun i2 hi2 => eq_Aq hall hs hi2) t

theorem eq_Cf (hall : ∀ v, v.Valid n → chk n N pt x v = true) {s t : ℕ} (hs : s < L1 n)
    (ht : t < L2 n) : x (.Cf s t) = stC n (pOf n x) (qOf n x) s t := by
  rw [chk_mul_iff.1 (hall _ (show VD.Valid n (.mul s t) from ⟨hs, ht⟩)), eq_Pf hall hs ht,
    eq_Qf hall hs ht]
  rfl

theorem eq_Dc (hall : ∀ v, v.Valid n → chk n N pt x v = true) {s u : ℕ} (hs : s < L1 n)
    (hu : u < L2 n) : x (.Dc s u) = stD n (pOf n x) (qOf n x) s u := by
  rw [(chk_icol_iff.1 (hall _ (show VD.Valid n (.icol s) from hs))) u hu]
  exact invCol_congr n (fun t ht => eq_Cf hall hs ht) u

theorem eq_Cc (hall : ∀ v, v.Valid n → chk n N pt x v = true) {a u : ℕ} (ha : a < L1 n)
    (hu : u < L2 n) : x (.Cc a u) = stE n (pOf n x) (qOf n x) a u := by
  rw [(chk_irow_iff.1 (hall _ (show VD.Valid n (.irow u) from hu))) a ha]
  exact invRow_congr n (fun s hs => eq_Dc hall hs hu) a

theorem eq_conv (hall : ∀ v, v.Valid n → chk n N pt x v = true) (k : ℕ) :
    convCoeff n (fun a u => x (.Cc a u)) k = stc n (pOf n x) (qOf n x) k :=
  convCoeff_congr n fun _ ha _ hu _ => eq_Cc hall ha hu

theorem eq_rr (hall : ∀ v, v.Valid n → chk n N pt x v = true) {j : ℕ} (hj : j + 1 < Kc n) :
    x (.rr j) = stR n N (pOf n x) (qOf n x) (j + 1) := by
  let r : ℕ → ℕ := fun k => if k = 0 then 0 else x (.rr (k - 1))
  have hrec : ∀ k < Kc n - 1, r (k + 1) =
      (stc n (pOf n x) (qOf n x) k + r k - Nk n N k) / 2 ^ b n := by
    intro k hk
    have h := carryOK_iff.1 (chk_carry_iff.1 (hall _ (show VD.Valid n (.carry k) from
      show k < Kc n by omega)))
    rw [eq_conv hall, if_pos (show k + 1 < Kc n by omega)] at h
    show (if k + 1 = 0 then 0 else x (.rr (k + 1 - 1))) = _
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
    exact h.2.2
  have key := Factoring.Fermat.eq_carry_of_rec (K := Kc n - 1) (r := r) (by simp [r]) hrec (j + 1)
    (by omega)
  have e : stR n N (pOf n x) (qOf n x) (j + 1) =
      Factoring.Fermat.carry (b n) (stc n (pOf n x) (qOf n x)) (Nk n N) (j + 1) := by
    unfold stR; rw [carryChain_eq]
  rw [e, ← key]
  simp [r]

/-- **Stage induction**: if every check passes on `x`, then `x` is the canonical assignment of
the factors read off its limb wires, on every valid wire. -/
theorem eq_run (hall : ∀ v, v.Valid n → chk n N pt x v = true) :
    ∀ d, d.Valid n → x d = run n N (pOf n x) (qOf n x) d := by
  intro d hd
  cases d with
  | pL i1 i2 => exact (limb_pOf hall hd.1 hd.2).symm
  | qL i1 i2 => exact (limb_qOf hall hd.1 hd.2).symm
  | Ap s i2 => exact eq_Ap hall hd.1 hd.2
  | Aq s i2 => exact eq_Aq hall hd.1 hd.2
  | Pf s t => exact eq_Pf hall hd.1 hd.2
  | Qf s t => exact eq_Qf hall hd.1 hd.2
  | Cf s t => exact eq_Cf hall hd.1 hd.2
  | Dc s u => exact eq_Dc hall hd.1 hd.2
  | Cc a u => exact eq_Cc hall hd.1 hd.2
  | rr j => exact eq_rr hall hd

end Stages

/-! ## The canonical assignment passes all checks iff `p q = N` and the pattern holds -/

/-- **Parsimony, canonical direction**: for `p, q, N < 2^{nB}`, the canonical assignment of
`(p, q)` passes every check iff `p q = N` and every limb of `p` matches the pattern `pt`. -/
theorem run_all_iff {n N p q : ℕ} (pt : List (Option Bool)) (hp : p < 2 ^ nB n) (hq : q < 2 ^ nB n)
    (hN : N < 2 ^ nB n) :
    (∀ v, v.Valid n → chk n N pt (run n N p q) v = true) ↔
      p * q = N ∧ ∀ i < ℓ n, patOK n pt i (limb (b n) p i) = true := by
  constructor
  · intro h
    refine ⟨(carry_checks_iff n N p q hp hq hN).1 fun k hk => ?_, fun i hi => ?_⟩
    · have := h (.carry k) hk
      rw [chk_run_carry, carryOK_iff] at this
      exact this
    · have := h (.cellP (i % ℓ1 n) (i / ℓ1 n)) (blk_dec hi)
      rw [chk_run_cellP, pA_mod_div, Nat.mod_add_div] at this
      exact this
  · rintro ⟨hpq, hpat⟩ v hv
    cases v with
    | cellP i1 i2 =>
      rw [chk_run_cellP]
      exact hpat _ (blk_lt hv.1 hv.2)
    | cellQ i1 i2 => exact chk_run_cellQ n N p q pt i1 i2
    | rowP i2 => exact chk_run_rowP n N p q pt i2
    | rowQ i2 => exact chk_run_rowQ n N p q pt i2
    | colP s => exact chk_run_colP n N p q pt s
    | colQ s => exact chk_run_colQ n N p q pt s
    | mul s t => exact chk_run_mul n N p q pt s t
    | icol s => exact chk_run_icol n N p q pt s
    | irow u => exact chk_run_irow n N p q pt u
    | carry k =>
      rw [chk_run_carry, carryOK_iff]
      exact (carry_checks_iff n N p q hp hq hN).2 hpq k hv

/-! ## The canonical labelling -/

/-- Every canonical wire value fits in `W` bits. -/
theorem run_lt_W (n N p q : ℕ) (d : WD) : run n N p q d < 2 ^ W n := by
  by_cases h : ∃ j, d = .rr j
  · obtain ⟨j, rfl⟩ := h
    exact stR_lt n N p q (j + 1)
  · exact run_lt n N p q d fun j hj => h ⟨j, hj⟩

/-- **The canonical labelling** of `(p, q)`: item `k` carries `run n N p q (wireOf n k)`. -/
def runL (n N p q : ℕ) : Fin (numWires n) → Lab n := fun k =>
  ⟨run n N p q (wireOf n k.val), by rw [two_pow_W_sub_add]; exact run_lt_W n N p q _⟩

theorem val_runL {n N p q : ℕ} {d : WD} (hd : d.Valid n) : val n (runL n N p q) d = run n N p q d := by
  rw [val_of_valid _ hd]
  show run n N p q (wireOf n (wireIdx n d)) = _
  rw [wireOf_wireIdx hd]

theorem chk_runL {n N p q : ℕ} (pt : List (Option Bool)) {v : VD} (hv : v.Valid n) :
    chk n N pt (val n (runL n N p q)) v = chk n N pt (run n N p q) v :=
  chk_agree hv fun _ hd _ => val_runL hd

theorem pOf_runL (n N p q : ℕ) (hp : p < 2 ^ nB n) : pOf n (val n (runL n N p q)) = p := by
  unfold pOf
  rw [ofLimbs_congr (b n) (f' := limb (b n) p) (ℓ n) fun i hi => by
    rw [val_runL (show WD.Valid n (.pL _ _) from blk_dec hi)]; exact pA_mod_div n p i]
  exact ofLimbs_limb _ _ _ (by rwa [mul_comm])

theorem qOf_runL (n N p q : ℕ) (hq : q < 2 ^ nB n) : qOf n (val n (runL n N p q)) = q := by
  unfold qOf
  rw [ofLimbs_congr (b n) (f' := limb (b n) q) (ℓ n) fun i hi => by
    rw [val_runL (show WD.Valid n (.qL _ _) from blk_dec hi)]; exact pA_mod_div n q i]
  exact ofLimbs_limb _ _ _ (by rwa [mul_comm])

/-- A labelling passing all checks is the canonical labelling of the factors it carries. -/
theorem runL_of_all {n N : ℕ} {pt : List (Option Bool)} {ℓ : Fin (numWires n) → Lab n}
    (hall : ∀ v, v.Valid n → chk n N pt (val n ℓ) v = true) :
    runL n N (pOf n (val n ℓ)) (qOf n (val n ℓ)) = ℓ := by
  funext k
  apply Fin.ext
  show run n N _ _ (wireOf n k.val) = _
  rw [← eq_run hall _ (wireOf_valid k.2), val_wireOf]

/-! ## The value -/

/-- `D` of `Params` is F6a's count `Search.D` (same formula). -/
theorem D_eq_search_D (N n : ℕ) (π : List Bool) : D N n π = Search.D N (nB n) n π := rfl

/-- **Parsimony**: the labellings passing every check are in bijection with the pairs counted by
`D(N, n, π)` (`1 ≤ N < 2^n`, `|π| ≤ n`). -/
theorem mulNet_card {n N : ℕ} {π : List Bool} (hNn : N < 2 ^ n) (ht : π.length ≤ n) :
    #(univ.filter fun ℓ : Fin (numWires n) → Lab n => allOK n N (pat n π) (val n ℓ) = true) =
      D N n π := by
  have hN : N < 2 ^ nB n := lt_of_lt_of_le hNn (Nat.pow_le_pow_right (by norm_num) (le_nB n))
  unfold D Dw
  symm
  refine card_nbij' (fun pq => runL n N pq.1 pq.2)
    (fun ℓ => (pOf n (val n ℓ), qOf n (val n ℓ))) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hpq
    simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hpq
    obtain ⟨⟨hp, hq⟩, hmul, hpre⟩ := hpq
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    refine allOK_iff.2 fun v hv => ?_
    rw [chk_runL _ hv]
    exact (run_all_iff _ hp hq hN).2 ⟨hmul, (patOK_iff ht hp).2 hpre⟩ v hv
  · intro ℓ hℓ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hℓ
    have hall := allOK_iff.1 hℓ
    have hp := pOf_lt hall
    have hq := qOf_lt hall
    have hrun : ∀ v, v.Valid n →
        chk n N (pat n π) (run n N (pOf n (val n ℓ)) (qOf n (val n ℓ))) v = true := fun v hv => by
      rw [← chk_agree hv fun d hd _ => eq_run hall d hd]; exact hall v hv
    obtain ⟨hmul, hpat⟩ := (run_all_iff _ hp hq hN).1 hrun
    simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq]
    exact ⟨⟨hp, hq⟩, hmul, (patOK_iff ht hp).1 hpat⟩
  · rintro ⟨p, q⟩ hpq
    simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hpq
    simp only [pOf_runL n N p q hpq.1.1, qOf_runL n N p q hpq.1.2]
  · intro ℓ hℓ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hℓ
    exact runL_of_all (allOK_iff.1 hℓ)

/-- **The value of the multiplication network** (F6a's form): for `g ≥ 2`, `1 ≤ N < 2^n` and
`|π| ≤ n`, the network `mulSys n N (pat n π) g` has value `Search.D N (nB n) n π` =
`#{(p, q) ∈ [0, 2^{nB n})² : p q = N ∧ p / 2^{n−|π|} = ofWord π}`. -/
theorem mulNet_value_search {n N g : ℕ} {π : List Bool} (hg : 2 ≤ g) (hNn : N < 2 ^ n)
    (ht : π.length ≤ n) :
    ((mulSys n N (pat n π) g hg).net (labCode n)).value = (Search.D N (nB n) n π : ℤ) := by
  rw [mulSys_value', mulNet_card hNn ht, D_eq_search_D]

/-- **The value of the multiplication network** (`Params.D` form, as in `MulPackage.value`). -/
theorem mulNet_value {n N g : ℕ} {π : List Bool} (hg : 2 ≤ g) (hNn : N < 2 ^ n)
    (ht : π.length ≤ n) :
    ((mulSys n N (pat n π) g hg).net (labCode n)).value = (D N n π : ℤ) := by
  rw [mulSys_value', mulNet_card hNn ht]

end EthFollowup.Factoring
