/-
# ArithNet, module L3 (part 1): procedures, context, layout and table of the arithmetic network

`scratchpad/plans/modp-plan.md`, ADDENDUM §B; interface `modp-interface.md` (L3). Template:
`Factoring/MulProcs.lean` (whose generic `labelProcsW`, `labelProcsW_isNet`, `labelProcsW_keeps` for a
complete code are reused by import).

* `aLabCode_complete`: every `Wa`-bit word is a code word;
* `incA`, `pairA` (the incident wires of a node, the places of the wires on a pair) with `incA_eq`,
  `pairA_eq`; the layout `layA` and **`layA_describes`**;
* the context `ACtx` (layout, `n` in unary, the description with `nV` in unary, `g`, the vertex range, the
  incidence lists) and `aCtxOf`;
* the table `tabA` (all checks of cluster `a`, wire values read from a setting via `MP.xz`), `tabAF`,
  `arithTp := Stepped.ofFun tabAF`, `tabA_eq` (= `aClusOK`), `tabAF_eq` (= the table `arithT`),
  **`arithSys_tspec`**;
* the procedures `arithNp := labelProcsW layAF parAF arithTp` and **`arithNet_isNet`** (Definition 2,
  given `Is P 1` of the network).

The PolyT proofs (`arithTp` polynomial-time, `arithNp.Keeps`) are module ArithPoly.

Standard axioms only.
-/
import EthFollowup.ModP.ArithNetDefs
import EthFollowup.ModP.ArithEnc
import EthFollowup.Factoring.MulProcs

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork Groundwork.Prog QueryMachines Eight.SecNetworks Finset EthFollowup.ExactHC EthFollowup.Factoring
open EthFollowup.Factoring.MP (getD_map_range' idxOf_map_val map_val_finRange')

theorem finCode_enc' (q : ℕ) (i : Fin (q + 1)) : (finCode q).enc i = toWord (Nat.clog 2 (q + 1)) i.val := rfl

/-- **Every `Wa`-bit word is a code word of `aLabCode n`.** -/
theorem aLabCode_complete (n : ℕ) :
    ∀ u : List Bool, u.length = Nat.clog 2 (2 ^ Wa n - 1 + 1) → ∃ l, (aLabCode n).enc l = u := by
  intro u hu
  have hlt : ofWord u < 2 ^ Wa n - 1 + 1 := by
    rw [two_pow_Wa_sub_add]
    have := ofWord_lt u
    rw [hu, clog_Wa] at this
    exact this
  refine ⟨⟨ofWord u, hlt⟩, ?_⟩
  rw [aLabCode, finCode_enc']
  show toWord _ (ofWord u) = u
  rw [← hu, toWord_ofWord]

/-! ## Incidence lists and pairs -/

section Wires
variable (n : ℕ) (D : Desc) (g : ℕ)

/-- The indices of the wires incident to node `a`, increasing. -/
def incA (a : ℕ) : List ℕ :=
  (List.range (numAW n D)).filter fun k => decide (aLo n D g (awOf n D k) = a ∨ aHi n D g (awOf n D k) = a)

/-- The places, among the wires incident to `a`, of the wires on the pair `{a, c}`. -/
def pairA (a c : ℕ) : List ℕ :=
  ((List.range (numAW n D)).filter fun k => decide ((aLo n D g (awOf n D k) = a ∧ aHi n D g (awOf n D k) = c) ∨
      (aLo n D g (awOf n D k) = c ∧ aHi n D g (awOf n D k) = a))).map
    fun k => (incA n D g a).idxOf k

end Wires

theorem filter_val_eqG {G : ℕ} (q : Fin G → Prop) [DecidablePred q] (q' : ℕ → Prop) [DecidablePred q']
    (h : ∀ k : Fin G, q k ↔ q' k.val) :
    ((List.finRange G).filter fun k => decide (q k)).map Fin.val = (List.range G).filter fun k => decide (q' k) := by
  rw [← map_val_finRange', List.filter_map]
  congr 1
  refine List.filter_congr fun k _ => ?_
  simp only [Function.comp, h]

section WiresEq
variable {n : ℕ} {D : Desc} {g : ℕ} (hg : 2 ≤ g)

theorem incA_eq (a : Fin g) : incA n D g a.val = ((arithSys n D g hg).incList a).map Fin.val := by
  unfold incA LabelSystem.incList
  refine (filter_val_eqG _ _ fun k => ?_).symm
  rw [arithSys_inc]

theorem pairA_eq (a c : Fin g) :
    (pairA n D g a.val c.val, ([] : List (Bool × ℕ))) = (arithSys n D g hg).pairData a c := by
  unfold pairA LabelSystem.pairData
  refine Prod.ext ?_ rfl
  simp only
  rw [incA_eq hg a]
  unfold LabelSystem.pairItems
  have e := filter_val_eqG (G := numAW n D) (fun k => (arithSys n D g hg).OnPair a c k)
    (fun k => (aLo n D g (awOf n D k) = a.val ∧ aHi n D g (awOf n D k) = c.val) ∨
      (aLo n D g (awOf n D k) = c.val ∧ aHi n D g (awOf n D k) = a.val)) fun k => by
    simp only [LabelSystem.OnPair, arithSys, Fin.ext_iff]
  rw [← e, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, idxOf_map_val]

end WiresEq

/-! ## The layout and the context -/

/-- **The layout of the arithmetic network**: `P` and `B = 1` in unary, the code width `Wa`, no code
list (the code is complete), per node the incident wires in unary, per ordered pair the places of the
shared wires. -/
def layA (n : ℕ) (D : Desc) (g P : ℕ) : Lay :=
  (((List.replicate P (), [()]), (List.replicate (Wa n) (), [])),
    ((List.range g).map fun a => ((incA n D g a).map fun _ => (), []),
      (List.range g).map fun a => (List.range g).map fun c => (pairA n D g a c, [])))

/-- The full list of code words (only used in proofs). -/
noncomputable def codesA (n : ℕ) : List (List Bool) :=
  (Finset.univ : Finset (ALab n)).toList.map (aLabCode n).enc

/-- **The layout describes the network** (with the full code list substituted). -/
theorem layA_describes {n : ℕ} {D : Desc} {g : ℕ} (hg : 2 ≤ g) (P : ℕ) :
    (arithSys n D g hg).Describes (aLabCode n) P 1 ((layA n D g P).withCodes (codesA n)) where
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
abbrev ACtx : Type := Lay × ((List Unit × (Desc × List Unit)) × ((ℕ × List ℕ) × List (List ℕ)))

/-- The context of `n`, `D`, `g` nodes and the bound `P`. -/
def aCtxOf (n : ℕ) (D : Desc) (g P : ℕ) : ACtx :=
  (layA n D g P, ((List.replicate n (), (D, List.replicate D.nV ())),
    ((g, List.range (numAV n D)), (List.range g).map (incA n D g))))

namespace ACtx
variable (c : ACtx)
/-- `n`. -/
def n : ℕ := c.2.1.1.length
/-- The description, its number of variables read from the unary copy. -/
def D : Desc := { c.2.1.2.1 with nV := c.2.1.2.2.length }
/-- The number of nodes. -/
def g : ℕ := c.2.2.1.1
/-- The vertex indices. -/
def rV : List ℕ := c.2.2.1.2
/-- The incidence lists. -/
def inc : List (List ℕ) := c.2.2.2
end ACtx

section CtxOf
variable (n : ℕ) (D : Desc) (g P : ℕ)
@[simp] theorem aCtxOf_n : (aCtxOf n D g P).n = n := List.length_replicate
@[simp] theorem aCtxOf_D : (aCtxOf n D g P).D = D := by
  cases D; simp [ACtx.D, aCtxOf]
@[simp] theorem aCtxOf_g : (aCtxOf n D g P).g = g := rfl
@[simp] theorem aCtxOf_rV : (aCtxOf n D g P).rV = List.range (numAV n D) := rfl
@[simp] theorem aCtxOf_inc : (aCtxOf n D g P).inc = (List.range g).map (incA n D g) := rfl
@[simp] theorem aCtxOf_fst : (aCtxOf n D g P).1 = layA n D g P := rfl
end CtxOf

/-! ## The table procedure -/

/-- All checks of the vertices of cluster `a`, the wire values read from the setting `z`. -/
def tabA (c : ACtx) (a : ℕ) (z : List Bool) : Bool :=
  c.rV.all fun j => !(decide (aClus c.n c.D c.g (avOf c.n c.D j) = a)) ||
    aChk c.n c.D (fun d => xz (Wa c.n) (c.inc.getD a []) z (awIdx c.n c.D d)) (avOf c.n c.D j)

/-- The table entry. -/
def tabAF (q : ACtx × WQ) : ℤ := if tabA q.1 q.2.1 q.2.2 = true then 1 else 0

/-- **The table procedure**: one step. -/
def arithTp : Stepped (ACtx × WQ) ℤ := Stepped.ofFun tabAF

section TabEq
variable {n : ℕ} {D : Desc} {g : ℕ} (hg : 2 ≤ g)

/-- The value of an incident wire, read from a setting. -/
theorem xz_encA (a : Fin g) (x : (Fin (numAW n D) → ALab n) × (Empty → Bool)) (k : Fin (numAW n D))
    (hk : (arithSys n D g hg).Inc a k) :
    xz (Wa n) (((arithSys n D g hg).incList a).map Fin.val) ((arithSys n D g hg).enc (aLabCode n) a x) k.val =
      (x.1 k).val := by
  have hmem : k ∈ (arithSys n D g hg).incList a := (arithSys n D g hg).mem_incList.2 hk
  unfold xz
  rw [idxOf_map_val, blk_congr_w (clog_Wa n).symm]
  unfold LabelSystem.enc
  rw [blk_encL (aLabCode n) x.1 _ _ _ (List.idxOf_lt_length_of_mem hmem), List.getElem_idxOf,
    aLabCode, finCode_enc']
  refine ofWord_toWord ?_
  rw [clog_Wa]
  exact lt_of_lt_of_le (x.1 k).isLt (two_pow_Wa_sub_add n).le

/-- **The table procedure computes the table**: on a setting of `a`, `tabA` is `aClusOK`. -/
theorem tabA_eq (P : ℕ) (a : Fin g) (x : (Fin (numAW n D) → ALab n) × (Empty → Bool)) :
    tabA (aCtxOf n D g P) a.val ((arithSys n D g hg).enc (aLabCode n) a x) =
      aClusOK n D g a.val (aVal n D x.1) := by
  have hinc : ((List.range g).map (incA n D g)).getD a.val [] =
      ((arithSys n D g hg).incList a).map Fin.val := by
    rw [getD_map_range' _ a.2, incA_eq hg a]
  unfold tabA aClusOK
  simp only [aCtxOf_n, aCtxOf_D, aCtxOf_g, aCtxOf_rV, aCtxOf_inc, hinc]
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  refine forall_congr' fun j => imp_congr_right fun hj => ?_
  by_cases hc : aClus n D g (avOf n D j) = a.val
  · simp only [hc, not_true_eq_false, false_or]
    rw [aChk_agree (avOf_valid hj) fun d hd hw => ?_]
    show xz (Wa n) _ _ (awIdx n D d) = aVal n D x.1 d
    rw [aVal_of_valid _ hd]
    refine xz_encA hg a x ⟨awIdx n D d, awIdx_lt hd⟩ ?_
    rw [arithSys_inc]
    simp only [awOf_awIdx hd]
    have hm := aClus_ends_mem n D g d
    rcases hw with e | e <;> rw [e, hc] at hm
    · exact hm.1.imp Eq.symm Eq.symm
    · exact hm.2.imp Eq.symm Eq.symm
  · simp only [hc, not_false_eq_true, true_or]

theorem tabAF_eq (P : ℕ) (a : Fin g) (x : (Fin (numAW n D) → ALab n) × (Empty → Bool)) :
    tabAF (aCtxOf n D g P, (a.val, (arithSys n D g hg).enc (aLabCode n) a x)) =
      (arithSys n D g hg).T a x.1 x.2 := by
  unfold tabAF
  rw [tabA_eq hg P a x]
  rfl

/-- The state bound of the table procedure. -/
def SA (c : ACtx) (g P : ℕ) : ℕ := size c + g + 2 * P + 6

/-- **Definition 2(iii) for the tables**: one step, states of size `≤ SA`. -/
theorem arithSys_tspec (P : ℕ) (hP : ∀ a, ((arithSys n D g hg).net (aLabCode n)).len a ≤ P) :
    (arithSys n D g hg).TSpec (aLabCode n) arithTp (aCtxOf n D g P) 1 (SA (aCtxOf n D g P) g P) := by
  intro a x _
  have h := Stepped.ofFun_runs tabAF (aCtxOf n D g P, (a.val, (arithSys n D g hg).enc (aLabCode n) a x))
  rw [tabAF_eq hg P a x] at h
  refine h.mono le_rfl ?_
  have h1 := LabelSystem.size_fin' a
  have h2 := hP a
  have h3 : size ((arithSys n D g hg).T a x.1 x.2) ≤ 2 := by
    rw [arithSys_T]
    unfold arithT; exact LabelSystem.size_boole _
  have h4 := (arithSys n D g hg).length_enc (aLabCode n) a x
  have h5 := LabelSystem.size_word ((arithSys n D g hg).enc (aLabCode n) a x)
  have hs : size (aCtxOf n D g P, (a.val, (arithSys n D g hg).enc (aLabCode n) a x)) =
      size (aCtxOf n D g P) + (size a.val + size ((arithSys n D g hg).enc (aLabCode n) a x)) := rfl
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
def SAN (n : ℕ) (D : Desc) (g P : ℕ) : ℕ :=
  SA (aCtxOf n D g P) g P + size (aCtxOf n D g P) + 2 * g + 4 * P + 8

/-- **Definition 2 for the arithmetic network** (given its bounds `Is P 1`). -/
theorem arithNet_isNet {n : ℕ} {D : Desc} {g P : ℕ} (hg : 2 ≤ g)
    (hN : ((arithSys n D g hg).net (aLabCode n)).Is P 1) :
    IsNetwork arithNp (aCtxOf n D g P) ((arithSys n D g hg).net (aLabCode n)) P 1 1 (SAN n D g P) := by
  have h := LabelSystem.labelProcsW_isNet (lay := layAF) (par := parAF) (arithSys n D g hg) (aLabCode n)
    (aLabCode_complete n) arithTp (c := aCtxOf n D g P) (cs := codesA n) hN (layA_describes hg P)
    (fun j => j.elim) (arithSys_tspec hg P fun a => hN.len_le a) le_rfl
  unfold SAN
  exact h

end EthFollowup.ModP
