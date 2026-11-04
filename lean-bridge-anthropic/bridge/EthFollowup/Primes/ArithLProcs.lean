/-
# ArithL, module 4a: procedures, context, layout and table of the leveled network

Template: `ModP/ArithProcs.lean` (verbatim up to the description type; `aLabCode_complete`,
`filter_val_eqG`, `labelProcsW*` reused). Codes of `LDesc`: the tuple `(D, (lev, levC))`.
* `incA`, `pairA`, `layA`, **`layA_describes`**; context `ACtx`, `aCtxOf`;
* `tabA`, `tabAF`, `arithTp`, `tabA_eq`, **`arithSys_tspec`**; `arithNp`, **`arithNet_isNet`**.

Standard axioms only.
-/
import EthFollowup.Primes.ArithLNetDefs
import EthFollowup.ModP.ArithProcs

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Groundwork Groundwork.Prog QueryMachines Eight.SecNetworks Finset EthFollowup.ExactHC EthFollowup.Factoring
  EthFollowup.ModP
open EthFollowup.Factoring.MP (getD_map_range' idxOf_map_val map_val_finRange')

/-! ## Codes of leveled descriptions -/

/-- The code tuple of a leveled description. -/
def LDesc.toT (L : LDesc) : Desc × (List ℕ × List ℕ) := (L.D, (L.lev, L.levC))

instance : Enc LDesc := ⟨fun x => Enc.toV x.toT⟩
instance : HasSize LDesc := ⟨fun x => size x.toT⟩
instance : Carried LDesc := ⟨fun x => Carried.le x.toT⟩

/-! ## Incidence lists and pairs -/

section Wires
variable (n : ℕ) (L : LDesc) (g : ℕ)

/-- The indices of the wires incident to node `a`, increasing. -/
def incA (a : ℕ) : List ℕ :=
  (List.range (numAW n L)).filter fun k => decide (aLo n L g (awOf n L k) = a ∨ aHi n L g (awOf n L k) = a)

/-- The places, among the wires incident to `a`, of the wires on the pair `{a, c}`. -/
def pairA (a c : ℕ) : List ℕ :=
  ((List.range (numAW n L)).filter fun k => decide ((aLo n L g (awOf n L k) = a ∧ aHi n L g (awOf n L k) = c) ∨
      (aLo n L g (awOf n L k) = c ∧ aHi n L g (awOf n L k) = a))).map
    fun k => (incA n L g a).idxOf k

end Wires

section WiresEq
variable {n : ℕ} {L : LDesc} {g : ℕ} (hg : 2 ≤ g)

theorem incA_eq (a : Fin g) : incA n L g a.val = ((arithSys n L g hg).incList a).map Fin.val := by
  unfold incA LabelSystem.incList
  refine (filter_val_eqG _ _ fun k => ?_).symm
  rw [arithSys_inc]

theorem pairA_eq (a c : Fin g) :
    (pairA n L g a.val c.val, ([] : List (Bool × ℕ))) = (arithSys n L g hg).pairData a c := by
  unfold pairA LabelSystem.pairData
  refine Prod.ext ?_ rfl
  simp only
  rw [incA_eq hg a]
  unfold LabelSystem.pairItems
  have e := filter_val_eqG (G := numAW n L) (fun k => (arithSys n L g hg).OnPair a c k)
    (fun k => (aLo n L g (awOf n L k) = a.val ∧ aHi n L g (awOf n L k) = c.val) ∨
      (aLo n L g (awOf n L k) = c.val ∧ aHi n L g (awOf n L k) = a.val)) fun k => by
    simp only [LabelSystem.OnPair, arithSys, Fin.ext_iff]
  rw [← e, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, idxOf_map_val]

end WiresEq

/-! ## The layout and the context -/

/-- **The layout of the arithmetic network**: `P` and `B = 1` in unary, the code width `Wa`, no code
list (the code is complete), per node the incident wires in unary, per ordered pair the places of the
shared wires. -/
def layA (n : ℕ) (L : LDesc) (g P : ℕ) : Lay :=
  (((List.replicate P (), [()]), (List.replicate (Wa n) (), [])),
    ((List.range g).map fun a => ((incA n L g a).map fun _ => (), []),
      (List.range g).map fun a => (List.range g).map fun c => (pairA n L g a c, [])))

/-- The full list of code words (only used in proofs). -/
noncomputable def codesA (n : ℕ) : List (List Bool) :=
  (Finset.univ : Finset (ALab n)).toList.map (aLabCode n).enc

/-- **The layout describes the network** (with the full code list substituted). -/
theorem layA_describes {n : ℕ} {L : LDesc} {g : ℕ} (hg : 2 ≤ g) (P : ℕ) :
    (arithSys n L g hg).Describes (aLabCode n) P 1 ((layA n L g P).withCodes (codesA n)) where
  P_eq := by simp [Lay.P, layA, Lay.withCodes]
  B_eq := rfl
  w_eq := by simp [Lay.w, layA, Lay.withCodes, clog_Wa]
  codes_iff u := by simp [Lay.codes, Lay.withCodes, codesA]
  na_eq a := by
    simp only [Lay.na, Lay.node, layA, Lay.withCodes]
    rw [getD_map_range' _ a.2, List.length_map, incA_eq hg a, List.length_map]
  nh_eq a := by
    simp only [Lay.nh, Lay.node, layA, Lay.withCodes]
    rw [getD_map_range' _ a.2]
    rfl
  pair_eq a c _ := by
    simp only [Lay.pair, layA, Lay.withCodes]
    rw [getD_map_range' _ a.2, getD_map_range' _ c.2]
    exact pairA_eq hg a c

/-- **The context**: the layout, (`n` in unary, (the description, its `nV` in unary)), ((`g`, the vertex
indices `[0, numAV)`), per node the incident wires). The ranges are stored so that every loop of the
table runs over a list held by the context (polynomial time on every context, ArithPoly). -/
abbrev ACtx : Type := Lay × ((List Unit × (LDesc × List Unit)) × ((ℕ × List ℕ) × List (List ℕ)))

/-- The context of `n`, `D`, `g` nodes and the bound `P`. -/
def aCtxOf (n : ℕ) (L : LDesc) (g P : ℕ) : ACtx :=
  (layA n L g P, ((List.replicate n (), (L, List.replicate L.D.nV ())),
    ((g, List.range (numAV n L)), (List.range g).map (incA n L g))))

namespace ACtx
variable (c : ACtx)
/-- `n`. -/
def n : ℕ := c.2.1.1.length
/-- The description, its number of variables read from the unary copy, its levels clamped by the
number of vertices (no effect on the contexts `aCtxOf`, where every level is `< nL ≤ numAV`; on every
context the number of levels is then at most `rV.length + 1`, so the cell layout stays polynomial). -/
def L : LDesc :=
  { D := { c.2.1.2.1.D with nV := c.2.1.2.2.length },
    lev := c.2.1.2.1.lev.map (min · c.2.2.1.2.length),
    levC := c.2.1.2.1.levC.map (min · c.2.2.1.2.length) }
/-- The number of nodes. -/
def g : ℕ := c.2.2.1.1
/-- The vertex indices. -/
def rV : List ℕ := c.2.2.1.2
/-- The incidence lists. -/
def inc : List (List ℕ) := c.2.2.2
end ACtx

section CtxOf
variable (n : ℕ) (L : LDesc) (g P : ℕ)
@[simp] theorem aCtxOf_n : (aCtxOf n L g P).n = n := List.length_replicate
/-- Every level is below the number of vertices (each level has at least one cell). -/
theorem nL_le_numAV : L.nL ≤ numAV n L := by
  have e : numAV n L = (List.map List.prod (((List.range L.nL).map fun o => [kl n o]) ++
      LB.lay [L.D.nP, L.D.nP, L.D.nP, L.D.nP, L.D.nP, L.D.nC] fun κ => vBox n L (κ + 1))).sum := rfl
  rw [e, List.map_append, List.sum_append, List.map_map]
  have h1 : (List.range L.nL).length ≤ ((List.range L.nL).map (List.prod ∘ fun o => [kl n o])).sum := by
    rw [← List.length_map (f := List.prod ∘ fun o => [kl n o])]
    refine List.length_le_sum_of_one_le _ fun x hx => ?_
    obtain ⟨o, -, rfl⟩ := List.mem_map.1 hx
    simpa using Nat.one_le_iff_ne_zero.2 (kl_pos n o).ne'
  rw [List.length_range] at h1
  omega

theorem map_min_numAV {l : List ℕ} (hl : ∀ x ∈ l, x < numAV n L) : l.map (min · (numAV n L)) = l := by
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun x hx => min_eq_left (hl x hx).le

@[simp] theorem aCtxOf_L : (aCtxOf n L g P).L = L := by
  have h1 : ∀ x ∈ L.lev, x < numAV n L := fun x hx =>
    lt_of_lt_of_le (Nat.lt_succ_of_le ((LDesc.le_foldr_max hx).trans (le_max_left _ _))) (nL_le_numAV n L)
  have h2 : ∀ x ∈ L.levC, x < numAV n L := fun x hx =>
    lt_of_lt_of_le (Nat.lt_succ_of_le ((LDesc.le_foldr_max hx).trans (le_max_right _ _))) (nL_le_numAV n L)
  have e1 := map_min_numAV n L h1
  have e2 := map_min_numAV n L h2
  obtain ⟨⟨_, _, _, _, _⟩, _, _⟩ := L
  simp only [ACtx.L, aCtxOf, List.length_replicate, List.length_range] at e1 e2 ⊢
  rw [e1, e2]
@[simp] theorem aCtxOf_g : (aCtxOf n L g P).g = g := rfl
@[simp] theorem aCtxOf_rV : (aCtxOf n L g P).rV = List.range (numAV n L) := rfl
@[simp] theorem aCtxOf_inc : (aCtxOf n L g P).inc = (List.range g).map (incA n L g) := rfl
@[simp] theorem aCtxOf_fst : (aCtxOf n L g P).1 = layA n L g P := rfl
end CtxOf

/-! ## The table procedure -/

/-- All checks of the vertices of cluster `a`, the wire values read from the setting `z`. -/
def tabA (c : ACtx) (a : ℕ) (z : List Bool) : Bool :=
  c.rV.all fun j => !(decide (aClus c.n c.L c.g (avOf c.n c.L j) = a)) ||
    aChk c.n c.L (fun d => xz (Wa c.n) (c.inc.getD a []) z (awIdx c.n c.L d)) (avOf c.n c.L j)

/-- The table entry. -/
def tabAF (q : ACtx × WQ) : ℤ := if tabA q.1 q.2.1 q.2.2 = true then 1 else 0

/-- **The table procedure**: one step. -/
def arithTp : Stepped (ACtx × WQ) ℤ := Stepped.ofFun tabAF

section TabEq
variable {n : ℕ} {L : LDesc} {g : ℕ} (hg : 2 ≤ g)

/-- The value of an incident wire, read from a setting. -/
theorem xz_encA (a : Fin g) (x : (Fin (numAW n L) → ALab n) × (Empty → Bool)) (k : Fin (numAW n L))
    (hk : (arithSys n L g hg).Inc a k) :
    xz (Wa n) (((arithSys n L g hg).incList a).map Fin.val) ((arithSys n L g hg).enc (aLabCode n) a x) k.val =
      (x.1 k).val := by
  have hmem : k ∈ (arithSys n L g hg).incList a := (arithSys n L g hg).mem_incList.2 hk
  unfold xz
  rw [idxOf_map_val, blk_congr_w (clog_Wa n).symm]
  unfold LabelSystem.enc
  rw [blk_encL (aLabCode n) x.1 _ _ _ (List.idxOf_lt_length_of_mem hmem), List.getElem_idxOf,
    aLabCode, finCode_enc']
  refine ofWord_toWord ?_
  rw [clog_Wa]
  exact lt_of_lt_of_le (x.1 k).isLt (two_pow_Wa_sub_add n).le

/-- **The table procedure computes the table**: on a setting of `a`, `tabA` is `aClusOK`. -/
theorem tabA_eq (P : ℕ) (a : Fin g) (x : (Fin (numAW n L) → ALab n) × (Empty → Bool)) :
    tabA (aCtxOf n L g P) a.val ((arithSys n L g hg).enc (aLabCode n) a x) =
      aClusOK n L g a.val (aVal n L x.1) := by
  have hinc : ((List.range g).map (incA n L g)).getD a.val [] =
      ((arithSys n L g hg).incList a).map Fin.val := by
    rw [getD_map_range' _ a.2, incA_eq hg a]
  unfold tabA aClusOK
  simp only [aCtxOf_n, aCtxOf_L, aCtxOf_g, aCtxOf_rV, aCtxOf_inc, hinc]
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  refine forall_congr' fun j => imp_congr_right fun hj => ?_
  by_cases hc : aClus n L g (avOf n L j) = a.val
  · simp only [hc, not_true_eq_false, false_or]
    rw [aChk_agree (avOf_valid hj) fun d hd hw => ?_]
    show xz (Wa n) _ _ (awIdx n L d) = aVal n L x.1 d
    rw [aVal_of_valid _ hd]
    refine xz_encA hg a x ⟨awIdx n L d, awIdx_lt hd⟩ ?_
    rw [arithSys_inc]
    simp only [awOf_awIdx hd]
    have hm := aClus_ends_mem n L g d
    rcases hw with e | e <;> rw [e, hc] at hm
    · exact hm.1.imp Eq.symm Eq.symm
    · exact hm.2.imp Eq.symm Eq.symm
  · simp only [hc, not_false_eq_true, true_or]

theorem tabAF_eq (P : ℕ) (a : Fin g) (x : (Fin (numAW n L) → ALab n) × (Empty → Bool)) :
    tabAF (aCtxOf n L g P, (a.val, (arithSys n L g hg).enc (aLabCode n) a x)) =
      (arithSys n L g hg).T a x.1 x.2 := by
  unfold tabAF
  rw [tabA_eq hg P a x]
  rfl

/-- The state bound of the table procedure. -/
def SA (c : ACtx) (g P : ℕ) : ℕ := size c + g + 2 * P + 6

/-- **Definition 2(iii) for the tables**: one step, states of size `≤ SA`. -/
theorem arithSys_tspec (P : ℕ) (hP : ∀ a, ((arithSys n L g hg).net (aLabCode n)).len a ≤ P) :
    (arithSys n L g hg).TSpec (aLabCode n) arithTp (aCtxOf n L g P) 1 (SA (aCtxOf n L g P) g P) := by
  intro a x _
  have h := Stepped.ofFun_runs tabAF (aCtxOf n L g P, (a.val, (arithSys n L g hg).enc (aLabCode n) a x))
  rw [tabAF_eq hg P a x] at h
  refine h.mono le_rfl ?_
  have h1 := LabelSystem.size_fin' a
  have h2 := hP a
  have h3 : size ((arithSys n L g hg).T a x.1 x.2) ≤ 2 := by
    rw [arithSys_T]
    unfold arithT; exact LabelSystem.size_boole _
  have h4 := (arithSys n L g hg).length_enc (aLabCode n) a x
  have h5 := LabelSystem.size_word ((arithSys n L g hg).enc (aLabCode n) a x)
  have hs : size (aCtxOf n L g P, (a.val, (arithSys n L g hg).enc (aLabCode n) a x)) =
      size (aCtxOf n L g P) + (size a.val + size ((arithSys n L g hg).enc (aLabCode n) a x)) := rfl
  rw [hs]
  unfold SA
  omega

end TabEq

/-! ## The procedures -/

/-- The layout of a context. -/
def layAF (c : ACtx) : Lay := c.1
/-- No copy bits. -/
def parAF (_ : ACtx × (ℕ × List Bool)) : Bool := false

/-- **The procedures of the arithmetic networks.** -/
def arithNp : Procs ACtx := labelProcsW layAF parAF arithTp

/-- The state bound of the network. -/
def SAN (n : ℕ) (L : LDesc) (g P : ℕ) : ℕ :=
  SA (aCtxOf n L g P) g P + size (aCtxOf n L g P) + 2 * g + 4 * P + 8

/-- **Definition 2 for the arithmetic network** (given its bounds `Is P 1`). -/
theorem arithNet_isNet {n : ℕ} {L : LDesc} {g P : ℕ} (hg : 2 ≤ g)
    (hN : ((arithSys n L g hg).net (aLabCode n)).Is P 1) :
    IsNetwork arithNp (aCtxOf n L g P) ((arithSys n L g hg).net (aLabCode n)) P 1 1 (SAN n L g P) := by
  have h := LabelSystem.labelProcsW_isNet (lay := layAF) (par := parAF) (arithSys n L g hg) (aLabCode n)
    (aLabCode_complete n) arithTp (c := aCtxOf n L g P) (cs := codesA n) hN (layA_describes hg P)
    (fun j => j.elim) (arithSys_tspec hg P fun a => hN.len_le a) le_rfl
  unfold SAN
  exact h

end EthFollowup.Primes
