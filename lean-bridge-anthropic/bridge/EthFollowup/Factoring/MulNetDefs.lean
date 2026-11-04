/-
# Factoring, module F2 (part 1): the multiplication network as a label system

`scratchpad/plans/factoring-plan.md` §2; interface `facM-interface.md` (F0 = `Params`, F2).

* Labels: `Lab n = Fin (2^W − 1 + 1)` (`= Fin 2^W`), code `labCode n = finCode (2^W − 1)` of width
  `Nat.clog 2 (2^W − 1 + 1) = W n` (`clog_W`).
* `val n ℓ : WD → ℕ`: the wire values of a labelling `ℓ : Fin (numWires n) → Lab n` (wire `d` is item
  `wireIdx n d`; `0` off the valid wires).
* Locality: `chk_agree` (from `Params.chk_local`) — the check of a valid vertex `v` reads only the valid wires incident to `v`.
* `clusOK n N pt g a x`: all checks of the vertices of cluster `a`; the table
  `mulT a ℓ = [clusOK a (val ℓ)]` (`0/1`), `mulT_local`.
* `mulSys n N pt g hg : LabelSystem g (Fin (numWires n)) Empty (Lab n)`: item `k` sits on the pair
  `wLo < wHi` of the wire `wireOf n k`; no copy bits.
* `mulSys_value'`: the value is the number of labellings passing every check (`allOK`).

Standard axioms only.
-/
import EthFollowup.Factoring.FermatBridge
import EthFollowup.Factoring.Search

set_option linter.unusedSectionVars false

namespace EthFollowup.Factoring

open Finset EthFollowup.ExactHC

/-! ## Labels and wire values -/

/-- The label alphabet `Fin 2^W` (written `Fin (2^W − 1 + 1)` for `finCode`). -/
abbrev Lab (n : ℕ) : Type := Fin (2 ^ W n - 1 + 1)

/-- The code of the labels: `W n` bits (`clog_W`). -/
def labCode (n : ℕ) : LabelCode (Lab n) (Nat.clog 2 (2 ^ W n - 1 + 1)) := finCode (2 ^ W n - 1)

theorem two_pow_W_sub_add (n : ℕ) : 2 ^ W n - 1 + 1 = 2 ^ W n := Nat.sub_add_cancel Nat.one_le_two_pow

/-- The wire values of a labelling: wire `d` carries the label of item `wireIdx n d`
(`0` if `d` is not a wire). -/
def val (n : ℕ) (ℓ : Fin (numWires n) → Lab n) (d : WD) : ℕ :=
  if h : wireIdx n d < numWires n then (ℓ ⟨wireIdx n d, h⟩).val else 0

theorem val_of_valid {n : ℕ} (ℓ : Fin (numWires n) → Lab n) {d : WD} (hd : d.Valid n) :
    val n ℓ d = (ℓ ⟨wireIdx n d, wireIdx_lt hd⟩).val := by
  unfold val; rw [dif_pos (wireIdx_lt hd)]

theorem val_wireOf {n : ℕ} (ℓ : Fin (numWires n) → Lab n) (k : Fin (numWires n)) :
    val n ℓ (wireOf n k.val) = (ℓ k).val := by
  have h : wireIdx n (wireOf n k.val) < numWires n := by rw [wireIdx_wireOf]; exact k.2
  rw [val, dif_pos h]
  exact congrArg (fun i => (ℓ i).val) (Fin.ext (wireIdx_wireOf n k.val))

/-! ## Locality of the checks -/

/-- Wire `d` is incident to the vertex `v`. -/
def WInc (n : ℕ) (v : VD) (d : WD) : Prop := (ends n d).1 = v ∨ (ends n d).2 = v

/-- `x` and `x'` agree on the valid wires incident to `v`. -/
def Agree (n : ℕ) (x x' : WD → ℕ) (v : VD) : Prop :=
  ∀ d, d.Valid n → WInc n v d → x d = x' d

/-- **Locality** (from `Params.chk_local`): the check of a valid vertex reads only the valid wires
incident to it. -/
theorem chk_agree {n N : ℕ} {pt : List (Option Bool)} {x x' : WD → ℕ} {v : VD} (hv : v.Valid n)
    (h : Agree n x x' v) : chk n N pt x v = chk n N pt x' v :=
  chk_local n N pt v fun d hd => h d (incW_spec hv hd).1 (incW_spec hv hd).2

/-! ## The cluster tables -/

/-- All checks pass (vertices enumerated by index). -/
def allOK (n N : ℕ) (pt : List (Option Bool)) (x : WD → ℕ) : Bool :=
  (List.range (numVerts n)).all fun j => chk n N pt x (vertOf n j)

theorem allOK_iff {n N : ℕ} {pt : List (Option Bool)} {x : WD → ℕ} :
    allOK n N pt x = true ↔ ∀ v, v.Valid n → chk n N pt x v = true := by
  unfold allOK
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro H v hv
    have := H _ (vertIdx_lt hv)
    rwa [vertOf_vertIdx hv] at this
  · intro H j hj
    exact H _ (vertOf_valid hj)

/-- All checks of the vertices of cluster `a` pass. -/
def clusOK (n N : ℕ) (pt : List (Option Bool)) (g a : ℕ) (x : WD → ℕ) : Bool :=
  (List.range (numVerts n)).all fun j =>
    !(decide (clus n g (vertOf n j) = a)) || chk n N pt x (vertOf n j)

theorem clusOK_iff {n N : ℕ} {pt : List (Option Bool)} {g a : ℕ} {x : WD → ℕ} :
    clusOK n N pt g a x = true ↔ ∀ v, v.Valid n → clus n g v = a → chk n N pt x v = true := by
  unfold clusOK
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · intro H v hv hc
    have := H _ (vertIdx_lt hv)
    rw [vertOf_vertIdx hv] at this
    exact this.resolve_left (not_not.2 hc)
  · intro H j hj
    by_cases hc : clus n g (vertOf n j) = a
    · exact Or.inr (H _ (vertOf_valid hj) hc)
    · exact Or.inl hc

/-- The checks of every cluster pass iff all checks pass. -/
theorem forall_clusOK_iff {n N : ℕ} {pt : List (Option Bool)} {g : ℕ} (hg : 1 ≤ g) (x : WD → ℕ) :
    (∀ a : Fin g, clusOK n N pt g a.val x = true) ↔ allOK n N pt x = true := by
  rw [allOK_iff]
  constructor
  · intro H v hv
    exact clusOK_iff.1 (H ⟨clus n g v, clus_lt hv hg⟩) v hv rfl
  · intro H a
    exact clusOK_iff.2 fun v hv _ => H v hv

/-- **The table of node `a`**: `1` if all checks of the vertices of cluster `a` pass, else `0`. -/
def mulT (n N : ℕ) (pt : List (Option Bool)) (g : ℕ) (a : Fin g) (ℓ : Fin (numWires n) → Lab n) : ℤ :=
  if clusOK n N pt g a.val (val n ℓ) = true then 1 else 0

/-- **The table of node `a` reads only the items incident to `a`.** -/
theorem mulT_local {n N : ℕ} {pt : List (Option Bool)} {g : ℕ} (a : Fin g)
    (ℓ ℓ' : Fin (numWires n) → Lab n)
    (h : ∀ k : Fin (numWires n), (wLo n g (wireOf n k.val) = a.val ∨ wHi n g (wireOf n k.val) = a.val) →
      ℓ k = ℓ' k) :
    mulT n N pt g a ℓ = mulT n N pt g a ℓ' := by
  have key : clusOK n N pt g a.val (val n ℓ) = clusOK n N pt g a.val (val n ℓ') := by
    rw [Bool.eq_iff_iff, clusOK_iff, clusOK_iff]
    refine forall_congr' fun v => forall_congr' fun hv => forall_congr' fun hc => ?_
    rw [chk_agree hv fun d hd hvd => ?_]
    rw [val_of_valid ℓ hd, val_of_valid ℓ' hd]
    refine congrArg Fin.val (h _ ?_)
    simp only [wireOf_wireIdx hd]
    have hm := clus_ends_mem n g d
    rcases hvd with e | e <;> rw [e, hc] at hm
    · exact hm.1.imp Eq.symm Eq.symm
    · exact hm.2.imp Eq.symm Eq.symm
  unfold mulT; rw [key]

/-! ## The label system -/

/-- **The multiplication network** (for `g ≥ 2` nodes): items are the wires `Fin (numWires n)`,
item `k` on the pair `wLo < wHi` of the wire `wireOf n k`; labels `Lab n`; no copy bits; node `a`
has the table `mulT a` (all checks of its cluster). Context: `n`, `N`, the pattern `pt`. -/
def mulSys (n N : ℕ) (pt : List (Option Bool)) (g : ℕ) (hg : 2 ≤ g) :
    LabelSystem g (Fin (numWires n)) Empty (Lab n) where
  kord := List.finRange _
  kord_nodup := List.nodup_finRange _
  mem_kord := List.mem_finRange
  rord := []
  rord_nodup := List.nodup_nil
  mem_rord j := j.elim
  lo k := ⟨wLo n g (wireOf n k.val), wLo_lt (wireOf_valid k.2) hg⟩
  hi k := ⟨wHi n g (wireOf n k.val), wHi_lt (wireOf_valid k.2) hg⟩
  lo_lt k := Fin.mk_lt_mk.2 (wLo_lt_wHi (wireOf_valid k.2) hg)
  holder j := j.elim
  source j := j.elim
  holder_ne j := j.elim
  dflt := 0
  par j _ := j.elim
  T a ℓ _ := mulT n N pt g a ℓ
  par_local j := j.elim
  T_local a ℓ ℓ' _ _ hℓ _ := mulT_local a ℓ ℓ' fun k hk =>
    hℓ k (hk.imp (fun e => Fin.ext e) (fun e => Fin.ext e))

theorem mulSys_T {n N : ℕ} {pt : List (Option Bool)} {g : ℕ} (hg : 2 ≤ g) (a : Fin g)
    (ℓ : Fin (numWires n) → Lab n) (y : Empty → Bool) :
    (mulSys n N pt g hg).T a ℓ y = mulT n N pt g a ℓ := rfl

theorem mulSys_inc {n N : ℕ} {pt : List (Option Bool)} {g : ℕ} (hg : 2 ≤ g) (a : Fin g)
    (k : Fin (numWires n)) :
    (mulSys n N pt g hg).Inc a k ↔ wLo n g (wireOf n k.val) = a.val ∨ wHi n g (wireOf n k.val) = a.val := by
  simp only [LabelSystem.Inc, mulSys, Fin.ext_iff]

/-- **The value of the multiplication network**: the number of labellings passing every check. -/
theorem mulSys_value' {n N : ℕ} {pt : List (Option Bool)} {g : ℕ} (hg : 2 ≤ g) :
    ((mulSys n N pt g hg).net (labCode n)).value =
      (#(univ.filter fun ℓ : Fin (numWires n) → Lab n => allOK n N pt (val n ℓ) = true) : ℤ) := by
  rw [LabelSystem.value_net, Finset.natCast_card_filter]
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [mulSys_T, mulT]
  rw [Finset.prod_boole]
  have := forall_clusOK_iff (n := n) (N := N) (pt := pt) (by omega : 1 ≤ g) (val n ℓ)
  simp only [mem_univ, true_implies] at *
  by_cases h : allOK n N pt (val n ℓ) = true
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h]

end EthFollowup.Factoring
