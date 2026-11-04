/-
# ArithL, module 3a: the leveled network as a label system

Template: `ModP/ArithNetDefs.lean` (labels `ALab n`, code `aLabCode n` of width `Wa n` reused).
* `aVal n L ℓ : AWL → ℕ`, `aAllOK`, `aClusOK`, the table `arithT a ℓ = [aClusOK a (aVal ℓ)]`, `arithT_local`;
* `arithSys n L g hg : LabelSystem g (Fin (numAW n L)) Empty (ALab n)`; `arithSys_value'`.

Standard axioms only.
-/
import EthFollowup.Primes.ArithLParams
import EthFollowup.ModP.ArithNetDefs

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Finset EthFollowup.ExactHC EthFollowup.Factoring EthFollowup.ModP

/-- The wire values of a labelling (`0` off the valid wires). -/
def aVal (n : ℕ) (L : LDesc) (ℓ : Fin (numAW n L) → ALab n) (d : AWL) : ℕ :=
  if h : awIdx n L d < numAW n L then (ℓ ⟨awIdx n L d, h⟩).val else 0

theorem aVal_of_valid {n : ℕ} {L : LDesc} (ℓ : Fin (numAW n L) → ALab n) {d : AWL} (hd : d.Valid n L) :
    aVal n L ℓ d = (ℓ ⟨awIdx n L d, awIdx_lt hd⟩).val := by
  unfold aVal; rw [dif_pos (awIdx_lt hd)]

theorem aVal_awOf {n : ℕ} {L : LDesc} (ℓ : Fin (numAW n L) → ALab n) (k : Fin (numAW n L)) :
    aVal n L ℓ (awOf n L k.val) = (ℓ k).val := by
  have h : awIdx n L (awOf n L k.val) < numAW n L := by rw [awIdx_awOf k.2]; exact k.2
  rw [aVal, dif_pos h]
  exact congrArg (fun i => (ℓ i).val) (Fin.ext (awIdx_awOf k.2))

/-! ## The cluster tables -/

/-- All checks pass (vertices enumerated by index). -/
def aAllOK (n : ℕ) (L : LDesc) (x : AWL → ℕ) : Bool :=
  (List.range (numAV n L)).all fun j => aChk n L x (avOf n L j)

theorem aAllOK_iff {n : ℕ} {L : LDesc} {x : AWL → ℕ} :
    aAllOK n L x = true ↔ ∀ v, v.Valid n L → aChk n L x v = true := by
  unfold aAllOK
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro H v hv
    have := H _ (avIdx_lt hv)
    rwa [avOf_avIdx hv] at this
  · intro H j hj
    exact H _ (avOf_valid hj)

/-- All checks of the vertices of cluster `a` pass. -/
def aClusOK (n : ℕ) (L : LDesc) (g a : ℕ) (x : AWL → ℕ) : Bool :=
  (List.range (numAV n L)).all fun j => !(decide (aClus n L g (avOf n L j) = a)) || aChk n L x (avOf n L j)

theorem aClusOK_iff {n : ℕ} {L : LDesc} {g a : ℕ} {x : AWL → ℕ} :
    aClusOK n L g a x = true ↔ ∀ v, v.Valid n L → aClus n L g v = a → aChk n L x v = true := by
  unfold aClusOK
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · intro H v hv hc
    have := H _ (avIdx_lt hv)
    rw [avOf_avIdx hv] at this
    exact this.resolve_left (not_not.2 hc)
  · intro H j hj
    by_cases hc : aClus n L g (avOf n L j) = a
    · exact Or.inr (H _ (avOf_valid hj) hc)
    · exact Or.inl hc

theorem forall_aClusOK_iff {n : ℕ} {L : LDesc} {g : ℕ} (hg : 1 ≤ g) (x : AWL → ℕ) :
    (∀ a : Fin g, aClusOK n L g a.val x = true) ↔ aAllOK n L x = true := by
  rw [aAllOK_iff]
  constructor
  · intro H v hv
    exact aClusOK_iff.1 (H ⟨aClus n L g v, aClus_lt hv hg⟩) v hv rfl
  · intro H a
    exact aClusOK_iff.2 fun v hv _ => H v hv

/-- **The table of node `a`**: `1` if all checks of cluster `a` pass, else `0`. -/
def arithT (n : ℕ) (L : LDesc) (g : ℕ) (a : Fin g) (ℓ : Fin (numAW n L) → ALab n) : ℤ :=
  if aClusOK n L g a.val (aVal n L ℓ) = true then 1 else 0

/-- **The table of node `a` reads only the items incident to `a`.** -/
theorem arithT_local {n : ℕ} {L : LDesc} {g : ℕ} (a : Fin g) (ℓ ℓ' : Fin (numAW n L) → ALab n)
    (h : ∀ k : Fin (numAW n L), (aLo n L g (awOf n L k.val) = a.val ∨ aHi n L g (awOf n L k.val) = a.val) →
      ℓ k = ℓ' k) :
    arithT n L g a ℓ = arithT n L g a ℓ' := by
  have key : aClusOK n L g a.val (aVal n L ℓ) = aClusOK n L g a.val (aVal n L ℓ') := by
    rw [Bool.eq_iff_iff, aClusOK_iff, aClusOK_iff]
    refine forall_congr' fun v => forall_congr' fun hv => forall_congr' fun hc => ?_
    rw [aChk_agree hv fun d hd hvd => ?_]
    rw [aVal_of_valid ℓ hd, aVal_of_valid ℓ' hd]
    refine congrArg Fin.val (h _ ?_)
    simp only [awOf_awIdx hd]
    have hm := aClus_ends_mem n L g d
    rcases hvd with e | e <;> rw [e, hc] at hm
    · exact hm.1.imp Eq.symm Eq.symm
    · exact hm.2.imp Eq.symm Eq.symm
  unfold arithT; rw [key]

/-! ## The label system -/

/-- **The arithmetic-constraint network** (for `g ≥ 2` nodes): items are the wires
`Fin (numAW n L)`, item `k` on the pair `aLo < aHi` of the wire `awOf n L k`; labels `ALab n`; no
copy bits; node `a` has the table `arithT a` (all checks of its cluster). -/
def arithSys (n : ℕ) (L : LDesc) (g : ℕ) (hg : 2 ≤ g) :
    LabelSystem g (Fin (numAW n L)) Empty (ALab n) where
  kord := List.finRange _
  kord_nodup := List.nodup_finRange _
  mem_kord := List.mem_finRange
  rord := []
  rord_nodup := List.nodup_nil
  mem_rord j := j.elim
  lo k := ⟨aLo n L g (awOf n L k.val), aLo_lt (awOf_valid k.2) hg⟩
  hi k := ⟨aHi n L g (awOf n L k.val), aHi_lt (awOf_valid k.2) hg⟩
  lo_lt k := Fin.mk_lt_mk.2 (aLo_lt_aHi (awOf_valid k.2) hg)
  holder j := j.elim
  source j := j.elim
  holder_ne j := j.elim
  dflt := 0
  par j _ := j.elim
  T a ℓ _ := arithT n L g a ℓ
  par_local j := j.elim
  T_local a ℓ ℓ' _ _ hℓ _ := arithT_local a ℓ ℓ' fun k hk =>
    hℓ k (hk.imp (fun e => Fin.ext e) (fun e => Fin.ext e))

theorem arithSys_T {n : ℕ} {L : LDesc} {g : ℕ} (hg : 2 ≤ g) (a : Fin g)
    (ℓ : Fin (numAW n L) → ALab n) (y : Empty → Bool) :
    (arithSys n L g hg).T a ℓ y = arithT n L g a ℓ := by
  simp only [arithSys]

theorem arithSys_inc {n : ℕ} {L : LDesc} {g : ℕ} (hg : 2 ≤ g) (a : Fin g) (k : Fin (numAW n L)) :
    (arithSys n L g hg).Inc a k ↔ aLo n L g (awOf n L k.val) = a.val ∨ aHi n L g (awOf n L k.val) = a.val := by
  simp only [LabelSystem.Inc, arithSys, Fin.ext_iff]

/-- **The value of the network**: the number of labellings passing every check. -/
theorem arithSys_value' {n : ℕ} {L : LDesc} {g : ℕ} (hg : 2 ≤ g) :
    ((arithSys n L g hg).net (aLabCode n)).value =
      (#(univ.filter fun ℓ : Fin (numAW n L) → ALab n => aAllOK n L (aVal n L ℓ) = true) : ℤ) := by
  rw [LabelSystem.value_net, Finset.natCast_card_filter]
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [arithSys_T, arithT]
  rw [Finset.prod_boole]
  have := forall_aClusOK_iff (n := n) (L := L) (by omega : 1 ≤ g) (aVal n L ℓ)
  simp only [mem_univ, true_implies] at *
  by_cases h : aAllOK n L (aVal n L ℓ) = true
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h]

end EthFollowup.Primes
