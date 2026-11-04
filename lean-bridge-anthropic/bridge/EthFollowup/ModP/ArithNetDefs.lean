/-
# ArithNet, module L2 (part 1): the arithmetic-constraint network as a label system

`scratchpad/plans/modp-plan.md`, ADDENDUM §B; interface `modp-interface.md` (L2). Template:
`Factoring/MulNetDefs.lean`.

* Labels `ALab n = Fin (2^Wa − 1 + 1)`, code `aLabCode n` of width `Wa n` (`clog_Wa`).
* `aVal n D ℓ : AW → ℕ`: the wire values of a labelling `ℓ : Fin (numAW n D) → ALab n`.
* `aAllOK`, `aClusOK`, the table `arithT a ℓ = [aClusOK a (aVal ℓ)]`, `arithT_local`.
* `arithSys n D g hg : LabelSystem g (Fin (numAW n D)) Empty (ALab n)`; `arithSys_value'`: the value
  is the number of labellings passing every check.

Standard axioms only.
-/
import EthFollowup.ModP.ArithParams

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset EthFollowup.ExactHC EthFollowup.Factoring

/-! ## Labels and wire values -/

/-- The label alphabet `Fin 2^Wa`. -/
abbrev ALab (n : ℕ) : Type := Fin (2 ^ Wa n - 1 + 1)

/-- The code of the labels: `Wa n` bits (`clog_Wa`). -/
def aLabCode (n : ℕ) : LabelCode (ALab n) (Nat.clog 2 (2 ^ Wa n - 1 + 1)) := finCode (2 ^ Wa n - 1)

theorem two_pow_Wa_sub_add (n : ℕ) : 2 ^ Wa n - 1 + 1 = 2 ^ Wa n := Nat.sub_add_cancel Nat.one_le_two_pow

theorem clog_Wa (n : ℕ) : Nat.clog 2 (2 ^ Wa n - 1 + 1) = Wa n := by
  rw [two_pow_Wa_sub_add, Nat.clog_pow 2 _ (by norm_num)]

/-- The wire values of a labelling (`0` off the valid wires). -/
def aVal (n : ℕ) (D : Desc) (ℓ : Fin (numAW n D) → ALab n) (d : AW) : ℕ :=
  if h : awIdx n D d < numAW n D then (ℓ ⟨awIdx n D d, h⟩).val else 0

theorem aVal_of_valid {n : ℕ} {D : Desc} (ℓ : Fin (numAW n D) → ALab n) {d : AW} (hd : d.Valid n D) :
    aVal n D ℓ d = (ℓ ⟨awIdx n D d, awIdx_lt hd⟩).val := by
  unfold aVal; rw [dif_pos (awIdx_lt hd)]

theorem aVal_awOf {n : ℕ} {D : Desc} (ℓ : Fin (numAW n D) → ALab n) (k : Fin (numAW n D)) :
    aVal n D ℓ (awOf n D k.val) = (ℓ k).val := by
  have h : awIdx n D (awOf n D k.val) < numAW n D := by rw [awIdx_awOf k.2]; exact k.2
  rw [aVal, dif_pos h]
  exact congrArg (fun i => (ℓ i).val) (Fin.ext (awIdx_awOf k.2))

/-! ## The cluster tables -/

/-- All checks pass (vertices enumerated by index). -/
def aAllOK (n : ℕ) (D : Desc) (x : AW → ℕ) : Bool :=
  (List.range (numAV n D)).all fun j => aChk n D x (avOf n D j)

theorem aAllOK_iff {n : ℕ} {D : Desc} {x : AW → ℕ} :
    aAllOK n D x = true ↔ ∀ v, v.Valid n D → aChk n D x v = true := by
  unfold aAllOK
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro H v hv
    have := H _ (avIdx_lt hv)
    rwa [avOf_avIdx hv] at this
  · intro H j hj
    exact H _ (avOf_valid hj)

/-- All checks of the vertices of cluster `a` pass. -/
def aClusOK (n : ℕ) (D : Desc) (g a : ℕ) (x : AW → ℕ) : Bool :=
  (List.range (numAV n D)).all fun j => !(decide (aClus n D g (avOf n D j) = a)) || aChk n D x (avOf n D j)

theorem aClusOK_iff {n : ℕ} {D : Desc} {g a : ℕ} {x : AW → ℕ} :
    aClusOK n D g a x = true ↔ ∀ v, v.Valid n D → aClus n D g v = a → aChk n D x v = true := by
  unfold aClusOK
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · intro H v hv hc
    have := H _ (avIdx_lt hv)
    rw [avOf_avIdx hv] at this
    exact this.resolve_left (not_not.2 hc)
  · intro H j hj
    by_cases hc : aClus n D g (avOf n D j) = a
    · exact Or.inr (H _ (avOf_valid hj) hc)
    · exact Or.inl hc

theorem forall_aClusOK_iff {n : ℕ} {D : Desc} {g : ℕ} (hg : 1 ≤ g) (x : AW → ℕ) :
    (∀ a : Fin g, aClusOK n D g a.val x = true) ↔ aAllOK n D x = true := by
  rw [aAllOK_iff]
  constructor
  · intro H v hv
    exact aClusOK_iff.1 (H ⟨aClus n D g v, aClus_lt hv hg⟩) v hv rfl
  · intro H a
    exact aClusOK_iff.2 fun v hv _ => H v hv

/-- **The table of node `a`**: `1` if all checks of cluster `a` pass, else `0`. -/
def arithT (n : ℕ) (D : Desc) (g : ℕ) (a : Fin g) (ℓ : Fin (numAW n D) → ALab n) : ℤ :=
  if aClusOK n D g a.val (aVal n D ℓ) = true then 1 else 0

/-- **The table of node `a` reads only the items incident to `a`.** -/
theorem arithT_local {n : ℕ} {D : Desc} {g : ℕ} (a : Fin g) (ℓ ℓ' : Fin (numAW n D) → ALab n)
    (h : ∀ k : Fin (numAW n D), (aLo n D g (awOf n D k.val) = a.val ∨ aHi n D g (awOf n D k.val) = a.val) →
      ℓ k = ℓ' k) :
    arithT n D g a ℓ = arithT n D g a ℓ' := by
  have key : aClusOK n D g a.val (aVal n D ℓ) = aClusOK n D g a.val (aVal n D ℓ') := by
    rw [Bool.eq_iff_iff, aClusOK_iff, aClusOK_iff]
    refine forall_congr' fun v => forall_congr' fun hv => forall_congr' fun hc => ?_
    rw [aChk_agree hv fun d hd hvd => ?_]
    rw [aVal_of_valid ℓ hd, aVal_of_valid ℓ' hd]
    refine congrArg Fin.val (h _ ?_)
    simp only [awOf_awIdx hd]
    have hm := aClus_ends_mem n D g d
    rcases hvd with e | e <;> rw [e, hc] at hm
    · exact hm.1.imp Eq.symm Eq.symm
    · exact hm.2.imp Eq.symm Eq.symm
  unfold arithT; rw [key]

/-! ## The label system -/

/-- **The arithmetic-constraint network** (for `g ≥ 2` nodes): items are the wires
`Fin (numAW n D)`, item `k` on the pair `aLo < aHi` of the wire `awOf n D k`; labels `ALab n`; no
copy bits; node `a` has the table `arithT a` (all checks of its cluster). -/
def arithSys (n : ℕ) (D : Desc) (g : ℕ) (hg : 2 ≤ g) :
    LabelSystem g (Fin (numAW n D)) Empty (ALab n) where
  kord := List.finRange _
  kord_nodup := List.nodup_finRange _
  mem_kord := List.mem_finRange
  rord := []
  rord_nodup := List.nodup_nil
  mem_rord j := j.elim
  lo k := ⟨aLo n D g (awOf n D k.val), aLo_lt (awOf_valid k.2) hg⟩
  hi k := ⟨aHi n D g (awOf n D k.val), aHi_lt (awOf_valid k.2) hg⟩
  lo_lt k := Fin.mk_lt_mk.2 (aLo_lt_aHi (awOf_valid k.2) hg)
  holder j := j.elim
  source j := j.elim
  holder_ne j := j.elim
  dflt := 0
  par j _ := j.elim
  T a ℓ _ := arithT n D g a ℓ
  par_local j := j.elim
  T_local a ℓ ℓ' _ _ hℓ _ := arithT_local a ℓ ℓ' fun k hk =>
    hℓ k (hk.imp (fun e => Fin.ext e) (fun e => Fin.ext e))

theorem arithSys_T {n : ℕ} {D : Desc} {g : ℕ} (hg : 2 ≤ g) (a : Fin g)
    (ℓ : Fin (numAW n D) → ALab n) (y : Empty → Bool) :
    (arithSys n D g hg).T a ℓ y = arithT n D g a ℓ := by
  simp only [arithSys]

theorem arithSys_inc {n : ℕ} {D : Desc} {g : ℕ} (hg : 2 ≤ g) (a : Fin g) (k : Fin (numAW n D)) :
    (arithSys n D g hg).Inc a k ↔ aLo n D g (awOf n D k.val) = a.val ∨ aHi n D g (awOf n D k.val) = a.val := by
  simp only [LabelSystem.Inc, arithSys, Fin.ext_iff]

/-- **The value of the network**: the number of labellings passing every check. -/
theorem arithSys_value' {n : ℕ} {D : Desc} {g : ℕ} (hg : 2 ≤ g) :
    ((arithSys n D g hg).net (aLabCode n)).value =
      (#(univ.filter fun ℓ : Fin (numAW n D) → ALab n => aAllOK n D (aVal n D ℓ) = true) : ℤ) := by
  rw [LabelSystem.value_net, Finset.natCast_card_filter]
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [arithSys_T, arithT]
  rw [Finset.prod_boole]
  have := forall_aClusOK_iff (n := n) (D := D) (by omega : 1 ≤ g) (aVal n D ℓ)
  simp only [mem_univ, true_implies] at *
  by_cases h : aAllOK n D (aVal n D ℓ) = true
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h]

end EthFollowup.ModP
