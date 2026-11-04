/-
# ArithL, module 4b (part 2): the leveled table procedure and the context in polynomial time

Template: `ModP/ArithPoly.lean`. With the checks of `ArithLPolyChk`:
* the table on codes `tabLZ`, `tabA_eqLZ`, **`tabALF_polyT : PolyT tabAF`** (every context: the
  number of variables and `n` are stored in unary, the levels are clamped by `rV.length`, so
  `nL ≤ rV.length + 1`), `arithLTp_poly`, **`arithLNp_keeps`**;
* the reader: the ends of the wires on codes (`endsLZ`, `ends_eqZ`), `incLZ`, `pairLZ`, `layLZ`,
  `numAV_unary'`, `numAW_unary'` and **`aCtxOfL_polyT`** (`n`, `g`, `P`, the number of variables
  and the number of levels in unary, the description in polynomial time).

Standard axioms only.
-/
import EthFollowup.Primes.ArithLPolyChk

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Groundwork Groundwork.Prog EthFollowup.ExactHC EthFollowup.Factoring EthFollowup.ModP
open EthFollowup.Factoring.MP EthFollowup.Factoring.MPoly

/-! ## The vertex with a given index, on codes -/

def avK (n : ℕ) (L : LDesc) (j : ℕ) : ℕ := Blocks.fam (vObj L) (Blocks.fOf (vLay n L) j)
def avO (n : ℕ) (L : LDesc) (j : ℕ) : ℕ := Blocks.loc (vObj L) (Blocks.fOf (vLay n L) j)
def avC (n : ℕ) (L : LDesc) (j : ℕ) : List ℕ := Blocks.cOf (vLay n L) j

theorem avOf_eqK (n : ℕ) (L : LDesc) (j : ℕ) : avOf n L j = AVL.mk (avK n L j) (avO n L j) (avC n L j) := rfl

section VPoly
variable {α : Type} [Enc α] {n : α → ℕ} {L : α → LDesc} {j : α → ℕ} (hn : Unary n) (hL : PolyT L)
  (hK : Unary fun x => (L x).nL) (hj : PolyT j)
include hn hL hK hj

theorem avK_polyT : PolyT fun x => avK (n x) (L x) (j x) :=
  fam_polyT (vObj_polyT hL) (fOf_polyT (vLay_polyT hn hL hK) hj)
theorem avO_polyT : PolyT fun x => avO (n x) (L x) (j x) :=
  loc_polyT (vObj_polyT hL) (fOf_polyT (vLay_polyT hn hL hK) hj)
theorem avC_polyT : PolyT fun x => avC (n x) (L x) (j x) := cOf_polyT (vLay_polyT hn hL hK) hj

end VPoly

/-! ## The table on codes -/

/-- The table on codes. -/
def tabLZ (c : ACtx) (a : ℕ) (z : List Bool) : Bool :=
  c.rV.all fun j =>
    !(decide (clusLZ c.n c.L c.g (min (avK c.n c.L j) 6) (avO c.n c.L j) (coVL (avK c.n c.L j) (avC c.n c.L j)) = a)) ||
    chkLZ c.n c.L (Wa c.n, c.inc.getD a [], z, wLay c.n c.L) (avK c.n c.L j) (avO c.n c.L j) (avC c.n c.L j)

theorem tabA_eqLZ (c : ACtx) (a : ℕ) (z : List Bool) : EthFollowup.Primes.tabA c a z = tabLZ c a z := by
  have e : ∀ j, aChk c.n c.L (fun d => xz (Wa c.n) (c.inc.getD a []) z (awIdx c.n c.L d)) (avOf c.n c.L j) =
      chkLZ c.n c.L (Wa c.n, c.inc.getD a [], z, wLay c.n c.L) (avK c.n c.L j) (avO c.n c.L j) (avC c.n c.L j) :=
    fun j => aChk_eqZ c.n c.L (Wa c.n) (c.inc.getD a []) z _ _ _
  unfold EthFollowup.Primes.tabA tabLZ
  simp only [e]
  simp only [aClus_eqZ, avOf_eqK, avmkL_kind, avmkL_obj, avmkL_co]

/-! ### The context in polynomial time -/

theorem foldr_max_map_min_le (K : ℕ) : ∀ l : List ℕ, (l.map (min · K)).foldr max 0 ≤ K
  | [] => Nat.zero_le _
  | a :: l => by
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (min_le_right _ _) (foldr_max_map_min_le K l)

/-- On every context, the number of levels is at most `rV.length + 1`. -/
theorem ACtx.nL_le (c : ACtx) : c.L.nL ≤ c.rV.length + 1 := by
  have h1 := foldr_max_map_min_le c.2.2.1.2.length c.2.1.2.1.lev
  have h2 := foldr_max_map_min_le c.2.2.1.2.length c.2.1.2.1.levC
  show (_ ⊔ _) + 1 ≤ _
  exact Nat.succ_le_succ (max_le h1 h2)

theorem coVL_polyT {α : Type} [Enc α] {κ : α → ℕ} {xs : α → List ℕ} (hκ : PolyT κ) (hxs : PolyT xs) :
    PolyT fun x => coVL (κ x) (xs x) := by
  have g0 := PolyT.getD hxs (PolyT.const 0) (PolyT.const 0)
  have g1 := PolyT.getD hxs (PolyT.const 1) (PolyT.const 0)
  unfold coVL
  exact PolyT.ite' (PolyT.decide_eq hκ (PolyT.const 0)) (l1_polyT' g0)
    (PolyT.ite' (PolyT.decide_le hκ (PolyT.const 3)) (l2_polyT' g0 g1) (l1_polyT' g0))

section TPoly
variable {α : Type} [Enc α] {c : α → ACtx} (hc : PolyT c)
include hc

theorem ACtx.n_unaryL : Unary fun x => (c x).n := Unary.of_length (PolyT.fst (PolyT.fst (PolyT.snd hc)))
theorem ACtx.rV_polyTL : PolyT fun x => (c x).rV := PolyT.snd (PolyT.fst (PolyT.snd (PolyT.snd hc)))
theorem ACtx.g_polyTL : PolyT fun x => (c x).g := PolyT.fst (PolyT.fst (PolyT.snd (PolyT.snd hc)))
theorem ACtx.inc_polyTL : PolyT fun x => (c x).inc := PolyT.snd (PolyT.snd (PolyT.snd hc))
theorem ACtx.V_unaryL : Unary fun x => (c x).L.D.nV :=
  Unary.of_length (PolyT.snd (PolyT.snd (PolyT.fst (PolyT.snd hc))))

theorem ACtx.L_polyTL : PolyT fun x => (c x).L := by
  have h0 : PolyT fun x => (c x).2.1.2.1 := PolyT.fst (PolyT.snd (PolyT.fst (PolyT.snd hc)))
  have hD := LDesc.D_polyT h0
  have hK : PolyT fun x => (c x).2.2.1.2.length := PolyT.length (ACtx.rV_polyTL hc)
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hm : PolyT fun q : α × ℕ => min q.2 (c q.1).2.2.1.2.length := PolyT.min' (PolyT.snd PolyT.id') (hK.comp f1)
  exact (LDesc.mk_polyT (Desc.mk_polyT (PolyT.length (PolyT.snd (PolyT.snd (PolyT.fst (PolyT.snd hc)))))
    (Desc.pat_polyT hD) (Desc.prods_polyT hD) (Desc.chains_polyT hD) (Desc.cmps_polyT hD))
    (PolyT.map (f := fun x v => min v (c x).2.2.1.2.length) hm (LDesc.lev_polyT h0))
    (PolyT.map (f := fun x v => min v (c x).2.2.1.2.length) hm (LDesc.levC_polyT h0))).congr fun x => rfl

theorem ACtx.nL_unaryL : Unary fun x => (c x).L.nL :=
  Unary.of_le ((Unary.of_length (ACtx.rV_polyTL hc)).add (Unary.const 1)) (LDesc.nL_polyT (ACtx.L_polyTL hc))
    fun x => ACtx.nL_le (c x)

theorem tabLZ_polyT {a : α → ℕ} {z : α → List Bool} (ha : PolyT a) (hz : PolyT z) :
    PolyT fun x => tabLZ (c x) (a x) (z x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hcq := hc.comp f1
  have hn := ACtx.n_unaryL hcq
  have hL := ACtx.L_polyTL hcq
  have hK := ACtx.nL_unaryL hcq
  have hV := ACtx.V_unaryL hcq
  have hk := avK_polyT hn hL hK s1
  have ho := avO_polyT hn hL hK s1
  have hco := avC_polyT hn hL hK s1
  have hcl := clusLZ_polyT hn hL hK (ACtx.g_polyTL hcq) (PolyT.min' hk (PolyT.const 6)) ho (coVL_polyT hk hco)
  have hr : PolyT fun q : α × ℕ => (Wa (c q.1).n, (c q.1).inc.getD (a q.1) [], z q.1, wLay (c q.1).n (c q.1).L) :=
    PolyT.prodMk (Wa_unary hn).poly (PolyT.prodMk (PolyT.getD (ACtx.inc_polyTL hcq) (ha.comp f1) (PolyT.const []))
      (PolyT.prodMk (hz.comp f1) (wLay_polyT hn hL hV)))
  have hck := chkLZ_polyT (⟨hn, hL, hV, hr⟩ : LH _ _ _) hk ho hco
  have h := PolyT.all (f := fun x j =>
      !(decide (clusLZ (c x).n (c x).L (c x).g (min (avK (c x).n (c x).L j) 6) (avO (c x).n (c x).L j)
        (coVL (avK (c x).n (c x).L j) (avC (c x).n (c x).L j)) = a x)) ||
      chkLZ (c x).n (c x).L (Wa (c x).n, (c x).inc.getD (a x) [], z x, wLay (c x).n (c x).L)
        (avK (c x).n (c x).L j) (avO (c x).n (c x).L j) (avC (c x).n (c x).L j))
    (PolyT.or' (PolyT.not' (PolyT.decide_eq hcl (ha.comp f1))) hck) (ACtx.rV_polyTL hc)
  exact h.congr fun x => rfl

end TPoly

/-- **The table entry of the leveled network is polynomial-time** (on every context). -/
theorem tabALF_polyT : PolyT EthFollowup.Primes.tabAF := by
  have hc : PolyT fun q : ACtx × WQ => q.1 := PolyT.fst PolyT.id'
  have ht := tabLZ_polyT hc (PolyT.fst (PolyT.snd PolyT.id')) (PolyT.snd (PolyT.snd PolyT.id'))
  have h : PolyT fun q : ACtx × WQ => if tabLZ q.1 q.2.1 q.2.2 = true then (1 : ℤ) else 0 :=
    PolyT.ite' (PolyT.decide_eq ht (PolyT.const true)) (PolyT.const 1) (PolyT.const 0)
  exact h.congr fun q => by rw [EthFollowup.Primes.tabAF, tabA_eqLZ]

/-- **The table procedure has polynomial-time steps.** -/
theorem arithLTp_poly : Nonempty (IsPolyT EthFollowup.Primes.arithTp) := ⟨IsPolyT.ofFun tabALF_polyT⟩

theorem layALF_polyT : PolyT EthFollowup.Primes.layAF := PolyT.fst PolyT.id'

/-- **The procedures of the leveled network keep the resources.** -/
theorem arithLNp_keeps : EthFollowup.Primes.arithNp.Keeps :=
  labelProcsW_keeps layALF_polyT (PolyT.const false) arithLTp_poly

/-! ## The reader -/

/-- The code `(kind, object, coordinates)` of a vertex. -/
def vcode (v : AVL) : ℕ × ℕ × List ℕ := (v.kind, v.obj, v.co)

/-- The codes of the two ends of the wire `AWL.mk κ o xs` (as `aEnds`). -/
def endsLZ (n : ℕ) (L : LDesc) (κ o : ℕ) (xs : List ℕ) : (ℕ × ℕ × List ℕ) × (ℕ × ℕ × List ℕ) :=
  if κ = 0 then ((0, L.lv o, [xs.getD 0 0]), (0, L.lv o, [xs.getD 0 0]))
  else if κ = 1 then ((0, cellRk n L o (xs.getD 0 0) (xs.getD 1 0), [xs.getD 1 0]),
    (1, o, [xs.getD 0 0, xs.getD 1 0 / kl1 n (L.lp o)]))
  else if κ = 2 then ((1, o, [xs.getD 0 0, xs.getD 2 0]), (2, o, [xs.getD 0 0, xs.getD 1 0]))
  else if κ = 3 then ((2, o, [xs.getD 0 0, xs.getD 1 0]), (3, o, [xs.getD 1 0, xs.getD 2 0]))
  else if κ = 4 then ((3, o, [xs.getD 0 0, xs.getD 1 0]), (4, o, [xs.getD 0 0]))
  else if κ = 5 then ((4, o, [xs.getD 0 0]), (5, o, [xs.getD 1 0]))
  else if κ = 6 then
    (if chainOfZ L.D o < L.D.chains.length then
      ((5, o, [xs.getD 1 0]), (6, chainOfZ L.D o, [xs.getD 0 0 + kl1 n (L.lp o) * xs.getD 1 0]))
    else ((5, o, [xs.getD 1 0]), (5, o, [xs.getD 1 0])))
  else if κ = 7 then ((6, o, [xs.getD 0 0]), (6, o, [xs.getD 0 0 + 1]))
  else ((0, L.lq o, [xs.getD 0 0 + 1]), (0, L.lq o, [xs.getD 0 0]))

theorem ends_eqZ (n : ℕ) (L : LDesc) (κ o : ℕ) (xs : List ℕ) :
    (vcode (aEnds n L (AWL.mk κ o xs)).1, vcode (aEnds n L (AWL.mk κ o xs)).2) = endsLZ n L κ o xs := by
  rcases κ with _ | _ | _ | _ | _ | _ | _ | _ | κ
  · rfl
  · simp only [AWL.mk, aEnds, cellR_eqk]; rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [AWL.mk, aEnds, endsLZ, chainOfZ_eq, Desc.nC]
    split_ifs <;> first | rfl | contradiction
  · rfl
  · simp only [AWL.mk, aEnds, endsLZ, show κ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 0 by omega,
      show κ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 1 by omega, show κ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 2 by omega,
      show κ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 3 by omega, show κ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 4 by omega,
      show κ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 5 by omega, show κ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 6 by omega,
      show κ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 7 by omega, if_false]
    rfl

/-- The node pair of a wire with end codes `e`. -/
def lhE (n : ℕ) (L : LDesc) (g : ℕ) (e : (ℕ × ℕ × List ℕ) × (ℕ × ℕ × List ℕ)) : ℕ × ℕ :=
  lohi g (clusLZ n L g e.1.1 e.1.2.1 e.1.2.2) (clusLZ n L g e.2.1 e.2.2.1 e.2.2.2)

def awK (n : ℕ) (L : LDesc) (k : ℕ) : ℕ := Blocks.fam (wObj L) (Blocks.fOf (wLay n L) k)
def awO (n : ℕ) (L : LDesc) (k : ℕ) : ℕ := Blocks.loc (wObj L) (Blocks.fOf (wLay n L) k)
def awC (n : ℕ) (L : LDesc) (k : ℕ) : List ℕ := Blocks.cOf (wLay n L) k

/-- The node pair of the wire with index `k` (as `(aLo, aHi)` of `awOf n L k`). -/
def lhLZ (n : ℕ) (L : LDesc) (g k : ℕ) : ℕ × ℕ := lhE n L g (endsLZ n L (awK n L k) (awO n L k) (awC n L k))

theorem lhLZ_eq (n : ℕ) (L : LDesc) (g k : ℕ) :
    lhLZ n L g k = (aLo n L g (awOf n L k), aHi n L g (awOf n L k)) := by
  have e := ends_eqZ n L (awK n L k) (awO n L k) (awC n L k)
  unfold lhLZ lhE aLo aHi
  rw [← e, aClus_eqZ, aClus_eqZ]
  rfl

/-- `incA` with `lhLZ`. -/
def incLZ (n : ℕ) (L : LDesc) (rW : List ℕ) (g a : ℕ) : List ℕ :=
  rW.filter fun k => decide ((lhLZ n L g k).1 = a ∨ (lhLZ n L g k).2 = a)

theorem incA_eqLZ (n : ℕ) (L : LDesc) (g a : ℕ) :
    EthFollowup.Primes.incA n L g a = incLZ n L (List.range (numAW n L)) g a := by
  unfold EthFollowup.Primes.incA incLZ
  simp only [lhLZ_eq]

/-- `pairA` with `lhLZ`. -/
def pairLZ (n : ℕ) (L : LDesc) (rW : List ℕ) (g a c : ℕ) : List ℕ :=
  (rW.filter fun k => decide (((lhLZ n L g k).1 = a ∧ (lhLZ n L g k).2 = c) ∨
      ((lhLZ n L g k).1 = c ∧ (lhLZ n L g k).2 = a))).map fun k => (incLZ n L rW g a).idxOf k

theorem pairA_eqLZ (n : ℕ) (L : LDesc) (g a c : ℕ) :
    EthFollowup.Primes.pairA n L g a c = pairLZ n L (List.range (numAW n L)) g a c := by
  unfold EthFollowup.Primes.pairA pairLZ
  simp only [lhLZ_eq, ← incA_eqLZ]

/-- `layA` with `incLZ`, `pairLZ`. -/
def layLZ (n : ℕ) (L : LDesc) (rW : List ℕ) (g P W : ℕ) : Lay :=
  (((List.replicate P (), [()]), (List.replicate W (), [])),
    ((List.range g).map fun a => ((incLZ n L rW g a).map fun _ => (), []),
      (List.range g).map fun a => (List.range g).map fun c => (pairLZ n L rW g a c, [])))

theorem layA_eqLZ (n : ℕ) (L : LDesc) (g P : ℕ) :
    EthFollowup.Primes.layA n L g P = layLZ n L (List.range (numAW n L)) g P (Wa n) := by
  unfold EthFollowup.Primes.layA layLZ
  simp only [incA_eqLZ, pairA_eqLZ]

section RPoly
variable {α : Type} [Enc α] {n : α → ℕ} {L : α → LDesc} (hn : Unary n) (hL : PolyT L)
  (hV : Unary fun x => (L x).D.nV) (hK : Unary fun x => (L x).nL)

include hn hL hV in
theorem endsLZ_polyT {κ o : α → ℕ} {xs : α → List ℕ} (hκ : PolyT κ) (ho : PolyT o) (hxs : PolyT xs) :
    PolyT fun x => endsLZ (n x) (L x) (κ x) (o x) (xs x) := by
  have g : ∀ k : ℕ, PolyT fun x => (xs x).getD k 0 := fun k => PolyT.getD hxs (PolyT.const k) (PolyT.const 0)
  have e : ∀ k : ℕ, PolyT fun x => decide (κ x = k) := fun k => PolyT.decide_eq hκ (PolyT.const k)
  have v : ∀ {a : α → ℕ} {l : α → List ℕ}, PolyT a → PolyT l → PolyT fun x => (a x, o x, l x) :=
    fun ha hl => PolyT.prodMk ha (PolyT.prodMk ho hl)
  have hD := LDesc.D_polyT hL
  have hch : PolyT fun x => chainOfZ (L x).D (o x) := chainOfZ_polyT hD ho
  have hkl1 := (kl1_unary hn (LDesc.lp_polyT hL ho)).poly
  have h6 : PolyT fun x => if chainOfZ (L x).D (o x) < (L x).D.chains.length then
      ((5, o x, [(xs x).getD 1 0]), (6, chainOfZ (L x).D (o x), [(xs x).getD 0 0 + kl1 (n x) ((L x).lp (o x)) * (xs x).getD 1 0]))
      else ((5, o x, [(xs x).getD 1 0]), (5, o x, [(xs x).getD 1 0])) :=
    PolyT.ite' (PolyT.decide_lt hch (PolyT.length (Desc.chains_polyT hD)))
      (PolyT.prodMk (v (PolyT.const 5) (l1_polyT' (g 1)))
        (PolyT.prodMk (PolyT.const 6) (PolyT.prodMk hch (l1_polyT' (PolyT.add (g 0) (PolyT.mul hkl1 (g 1)))))))
      (PolyT.prodMk (v (PolyT.const 5) (l1_polyT' (g 1))) (v (PolyT.const 5) (l1_polyT' (g 1))))
  have hlv := LDesc.lv_polyT hL ho
  have hlq := LDesc.lq_polyT hL ho
  have hcR := cellRk_polyT (⟨hn, hL, hV, PolyT.const ((0 : ℕ), ([] : List ℕ), ([] : List Bool), ([] : List (List ℕ)))⟩ :
      LH n L fun _ => ((0 : ℕ), ([] : List ℕ), ([] : List Bool), ([] : List (List ℕ)))) ho (g 0) (g 1)
  refine PolyT.congr ?_ fun x => (rfl : _ = endsLZ (n x) (L x) (κ x) (o x) (xs x))
  exact PolyT.ite' (e 0) (PolyT.prodMk (PolyT.prodMk (PolyT.const 0) (PolyT.prodMk hlv (l1_polyT' (g 0))))
      (PolyT.prodMk (PolyT.const 0) (PolyT.prodMk hlv (l1_polyT' (g 0)))))
    (PolyT.ite' (e 1) (PolyT.prodMk (PolyT.prodMk (PolyT.const 0) (PolyT.prodMk hcR (l1_polyT' (g 1))))
      (v (PolyT.const 1) (l2_polyT' (g 0) (PolyT.div (g 1) hkl1))))
    (PolyT.ite' (e 2) (PolyT.prodMk (v (PolyT.const 1) (l2_polyT' (g 0) (g 2))) (v (PolyT.const 2) (l2_polyT' (g 0) (g 1))))
    (PolyT.ite' (e 3) (PolyT.prodMk (v (PolyT.const 2) (l2_polyT' (g 0) (g 1))) (v (PolyT.const 3) (l2_polyT' (g 1) (g 2))))
    (PolyT.ite' (e 4) (PolyT.prodMk (v (PolyT.const 3) (l2_polyT' (g 0) (g 1))) (v (PolyT.const 4) (l1_polyT' (g 0))))
    (PolyT.ite' (e 5) (PolyT.prodMk (v (PolyT.const 4) (l1_polyT' (g 0))) (v (PolyT.const 5) (l1_polyT' (g 1))))
    (PolyT.ite' (e 6) h6
    (PolyT.ite' (e 7) (PolyT.prodMk (v (PolyT.const 6) (l1_polyT' (g 0)))
        (v (PolyT.const 6) (l1_polyT' (PolyT.add (g 0) (PolyT.const 1)))))
      (PolyT.prodMk (PolyT.prodMk (PolyT.const 0) (PolyT.prodMk hlq (l1_polyT' (PolyT.add (g 0) (PolyT.const 1)))))
        (PolyT.prodMk (PolyT.const 0) (PolyT.prodMk hlq (l1_polyT' (g 0))))))))))))

include hn hL hV hK in
theorem lhLZ_polyT {g k : α → ℕ} (hg : PolyT g) (hk : PolyT k) : PolyT fun x => lhLZ (n x) (L x) (g x) (k x) := by
  have hw := wLay_polyT hn hL hV
  have hκ : PolyT fun x => awK (n x) (L x) (k x) := fam_polyT (wObj_polyT hL) (fOf_polyT hw hk)
  have ho : PolyT fun x => awO (n x) (L x) (k x) := loc_polyT (wObj_polyT hL) (fOf_polyT hw hk)
  have hc : PolyT fun x => awC (n x) (L x) (k x) := cOf_polyT hw hk
  have he := endsLZ_polyT hn hL hV hκ ho hc
  unfold lhLZ lhE
  exact lohi_polyT hg
    (clusLZ_polyT hn hL hK hg (PolyT.fst (PolyT.fst he)) (PolyT.fst (PolyT.snd (PolyT.fst he)))
      (PolyT.snd (PolyT.snd (PolyT.fst he))))
    (clusLZ_polyT hn hL hK hg (PolyT.fst (PolyT.snd he)) (PolyT.fst (PolyT.snd (PolyT.snd he)))
      (PolyT.snd (PolyT.snd (PolyT.snd he))))

include hn hL hV hK in
theorem incLZ_polyT {rW : α → List ℕ} {g a : α → ℕ} (hrW : PolyT rW) (hg : PolyT g) (ha : PolyT a) :
    PolyT fun x => incLZ (n x) (L x) (rW x) (g x) (a x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hl := lhLZ_polyT (hn.comp f1) (hL.comp f1) (hV.comp f1) (hK.comp f1) (hg.comp f1) (PolyT.snd PolyT.id')
  have haq := ha.comp f1
  exact PolyT.filter (f := fun x k => decide ((lhLZ (n x) (L x) (g x) k).1 = a x ∨ (lhLZ (n x) (L x) (g x) k).2 = a x))
    (PolyT.decide_or (PolyT.decide_eq (PolyT.fst hl) haq) (PolyT.decide_eq (PolyT.snd hl) haq)) hrW

include hn hL hV hK in
theorem pairLZ_polyT {rW : α → List ℕ} {g a c : α → ℕ} (hrW : PolyT rW) (hg : PolyT g) (ha : PolyT a)
    (hc : PolyT c) : PolyT fun x => pairLZ (n x) (L x) (rW x) (g x) (a x) (c x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hl := lhLZ_polyT (hn.comp f1) (hL.comp f1) (hV.comp f1) (hK.comp f1) (hg.comp f1) (PolyT.snd PolyT.id')
  have haq := ha.comp f1
  have hcq := hc.comp f1
  have hfil : PolyT fun x => (rW x).filter fun k => decide (((lhLZ (n x) (L x) (g x) k).1 = a x ∧
      (lhLZ (n x) (L x) (g x) k).2 = c x) ∨ ((lhLZ (n x) (L x) (g x) k).1 = c x ∧ (lhLZ (n x) (L x) (g x) k).2 = a x)) :=
    PolyT.filter (f := fun x k => decide (((lhLZ (n x) (L x) (g x) k).1 = a x ∧ (lhLZ (n x) (L x) (g x) k).2 = c x) ∨
        ((lhLZ (n x) (L x) (g x) k).1 = c x ∧ (lhLZ (n x) (L x) (g x) k).2 = a x)))
      (PolyT.decide_or (PolyT.decide_and (PolyT.decide_eq (PolyT.fst hl) haq) (PolyT.decide_eq (PolyT.snd hl) hcq))
        (PolyT.decide_and (PolyT.decide_eq (PolyT.fst hl) hcq) (PolyT.decide_eq (PolyT.snd hl) haq))) hrW
  have hinc : PolyT fun q : α × ℕ => incLZ (n q.1) (L q.1) (rW q.1) (g q.1) (a q.1) :=
    incLZ_polyT (hn.comp f1) (hL.comp f1) (hV.comp f1) (hK.comp f1) (hrW.comp f1) (hg.comp f1) haq
  exact PolyT.map (f := fun x k => (incLZ (n x) (L x) (rW x) (g x) (a x)).idxOf k)
    (PolyT.idxOf (PolyT.snd PolyT.id') hinc) hfil

include hn hL hV hK in
theorem layLZ_polyT {rW : α → List ℕ} {g P W : α → ℕ} (hrW : PolyT rW) (hg : Unary g) (hP : Unary P)
    (hW : Unary W) : PolyT fun x => layLZ (n x) (L x) (rW x) (g x) (P x) (W x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have f2 : PolyT fun q : (α × ℕ) × ℕ => q.1.1 := PolyT.fst (PolyT.fst PolyT.id')
  have hr : PolyT fun x => List.range (g x) := PolyT.range hg
  have hP' : PolyT fun x => List.replicate (P x) () := hP
  have hW' : PolyT fun x => List.replicate (W x) () := hW
  have hinc : PolyT fun q : α × ℕ => ((incLZ (n q.1) (L q.1) (rW q.1) (g q.1) q.2).map fun _ => (), ([] : List Unit)) :=
    PolyT.prodMk (PolyT.map (f := fun _ _ => ()) (PolyT.const ())
      (incLZ_polyT (hn.comp f1) (hL.comp f1) (hV.comp f1) (hK.comp f1) (hrW.comp f1) (hg.poly.comp f1)
        (PolyT.snd PolyT.id'))) (PolyT.const [])
  have hpair : PolyT fun q : (α × ℕ) × ℕ => (pairLZ (n q.1.1) (L q.1.1) (rW q.1.1) (g q.1.1) q.1.2 q.2,
      ([] : List (Bool × ℕ))) :=
    PolyT.prodMk (pairLZ_polyT (hn.comp f2) (hL.comp f2) (hV.comp f2) (hK.comp f2) (hrW.comp f2) (hg.poly.comp f2)
      (PolyT.snd (PolyT.fst PolyT.id')) (PolyT.snd PolyT.id')) (PolyT.const [])
  have hrow : PolyT fun q : α × ℕ => (List.range (g q.1)).map fun c =>
      (pairLZ (n q.1) (L q.1) (rW q.1) (g q.1) q.2 c, ([] : List (Bool × ℕ))) :=
    PolyT.map (f := fun (q : α × ℕ) c => (pairLZ (n q.1) (L q.1) (rW q.1) (g q.1) q.2 c, ([] : List (Bool × ℕ))))
      hpair (PolyT.comp (f := fun x => List.range (g x)) hr f1)
  refine PolyT.congr ?_ fun x => (rfl : _ = layLZ (n x) (L x) (rW x) (g x) (P x) (W x))
  exact PolyT.prodMk (PolyT.prodMk (PolyT.prodMk hP' (PolyT.const _)) (PolyT.prodMk hW' (PolyT.const _)))
    (PolyT.prodMk (PolyT.map (f := fun x a => ((incLZ (n x) (L x) (rW x) (g x) a).map fun _ => (), ([] : List Unit)))
      hinc hr)
      (PolyT.map (f := fun x a => (List.range (g x)).map fun c => (pairLZ (n x) (L x) (rW x) (g x) a c,
        ([] : List (Bool × ℕ)))) hrow hr))

end RPoly

/-! ### Sizes of the layouts in unary -/

theorem total_append (a b : List (List ℕ)) : Blocks.total (a ++ b) = Blocks.total a + Blocks.total b := by
  simp [Blocks.total, Blocks.sizes]

theorem total_rmap_le {N B : ℕ} {f : ℕ → List ℕ} (h : ∀ o, (f o).prod ≤ B) :
    Blocks.total ((List.range N).map f) ≤ N * B := by
  unfold Blocks.total Blocks.sizes
  rw [List.map_map]
  have := List.sum_le_card_nsmul ((List.range N).map (List.prod ∘ f)) B (by
    intro x hx
    obtain ⟨o, -, rfl⟩ := List.mem_map.1 hx
    exact h o)
  simpa using this

/-- The common bound `2 L1²` of the box sizes. -/
def bxB (n : ℕ) : ℕ := 2 * L1 n * L1 n

section Bx
variable (n k : ℕ)
theorem one_le_L1' : 1 ≤ L1 n := Nat.one_le_two_pow
theorem kl1_le_L1 : kl1 n k ≤ L1 n := (kl1_le n k).trans (ℓ1_le_L1 n)
theorem kl_le_B : kl n k ≤ bxB n := by
  have := kl1_le_L1 n k; unfold kl bxB; nlinarith
theorem two_kl_le_B : 2 * kl n k ≤ bxB n := by
  have := kl1_le_L1 n k; unfold kl bxB; nlinarith
theorem two_kl1_le_B : 2 * kl1 n k ≤ bxB n := by
  have := kl1_le_L1 n k; have := one_le_L1' n; unfold bxB; nlinarith
theorem two_kL1_le_B : 2 * kL1 n k ≤ bxB n := by
  have := kL1_le n k; have := one_le_L1' n; unfold bxB; nlinarith
theorem kL1_le_B : kL1 n k ≤ bxB n := by have := two_kL1_le_B n k; omega
theorem kL1sq_le_B : kL1 n k * kL1 n k ≤ bxB n := by
  have := kL1_le n k; unfold bxB; nlinarith
theorem two_kL1sq_le_B : 2 * (kL1 n k * kL1 n k) ≤ bxB n := by
  have := kL1_le n k; unfold bxB; nlinarith
theorem two_kL1kl1_le_B : 2 * (kL1 n k * kl1 n k) ≤ bxB n := by
  have := kL1_le n k; have := kl1_le_L1 n k; unfold bxB; nlinarith
theorem kKc_le_B : kKc n k ≤ bxB n := by
  have := kL1_le n k; have := kl1_le_L1 n k; have := one_le_L1' n; unfold kKc bxB; nlinarith
end Bx

theorem numAV_le_box (n : ℕ) (L : LDesc) : numAV n L ≤ (L.nL + 5 * L.D.nP + L.D.nC) * bxB n := by
  unfold numAV
  rw [vLay_eq]
  simp only [total_append]
  have h1 := total_rmap_le (N := L.nL) (B := bxB n) (f := fun o => [kl n o]) fun o => by simpa using kl_le_B n o
  have h2 := total_rmap_le (N := L.D.nP) (B := bxB n) (f := fun o => [2, kl1 n (L.lp o)]) fun o => by
    simpa using two_kl1_le_B n (L.lp o)
  have h3 := total_rmap_le (N := L.D.nP) (B := bxB n) (f := fun o => [2, kL1 n (L.lp o)]) fun o => by
    simpa using two_kL1_le_B n (L.lp o)
  have h4 := total_rmap_le (N := L.D.nP) (B := bxB n) (f := fun o => [kL1 n (L.lp o), kL1 n (L.lp o)]) fun o => by
    simpa using kL1sq_le_B n (L.lp o)
  have h5 := total_rmap_le (N := L.D.nP) (B := bxB n) (f := fun o => [kL1 n (L.lp o)]) fun o => by
    simpa using kL1_le_B n (L.lp o)
  have h7 := total_rmap_le (N := L.D.nC) (B := bxB n) (f := fun o => [kKc n (L.lc o)]) fun o => by
    simpa using kKc_le_B n (L.lc o)
  have h0 : Blocks.total ([] : List (List ℕ)) = 0 := rfl
  rw [h0]
  nlinarith

theorem numAW_le_box (n : ℕ) (L : LDesc) : numAW n L ≤ (L.D.nV + 6 * L.D.nP + L.D.nC + L.D.nQ) * bxB n := by
  unfold numAW
  rw [wLay_eq]
  simp only [total_append]
  have h1 := total_rmap_le (N := L.D.nV) (B := bxB n) (f := fun o => [kl n (L.lv o)]) fun o => by
    simpa using kl_le_B n (L.lv o)
  have h2 := total_rmap_le (N := L.D.nP) (B := bxB n) (f := fun o => [2, kl n (L.lp o)]) fun o => by
    simpa using two_kl_le_B n (L.lp o)
  have h3 := total_rmap_le (N := L.D.nP) (B := bxB n) (f := fun o => [2, kL1 n (L.lp o), kl1 n (L.lp o)]) fun o => by
    simpa [mul_assoc] using two_kL1kl1_le_B n (L.lp o)
  have h4 := total_rmap_le (N := L.D.nP) (B := bxB n) (f := fun o => [2, kL1 n (L.lp o), kL1 n (L.lp o)]) fun o => by
    simpa [mul_assoc] using two_kL1sq_le_B n (L.lp o)
  have h5 := total_rmap_le (N := L.D.nP) (B := bxB n) (f := fun o => [kL1 n (L.lp o), kL1 n (L.lp o)]) fun o => by
    simpa using kL1sq_le_B n (L.lp o)
  have h8 := total_rmap_le (N := L.D.nC) (B := bxB n) (f := fun o => [kKc n (L.lc o) - 1]) fun o => by
    have := kKc_le_B n (L.lc o); simp; omega
  have h9 := total_rmap_le (N := L.D.nQ) (B := bxB n) (f := fun o => [kl n (L.lq o) - 1]) fun o => by
    have := kl_le_B n (L.lq o); simp; omega
  have h0 : Blocks.total ([] : List (List ℕ)) = 0 := rfl
  rw [h0]
  nlinarith

section Unary
variable {α : Type} [Enc α] {n : α → ℕ} {L : α → LDesc} (hn : Unary n) (hL : PolyT L)
  (hV : Unary fun x => (L x).D.nV) (hK : Unary fun x => (L x).nL)

theorem bxB_unary (hn : Unary n) : Unary fun x => bxB (n x) :=
  Unary.mul (Unary.mul (Unary.const 2) (L1_unary hn)) (L1_unary hn)

include hn hL hK in
theorem numAV_unary' : Unary fun x => numAV (n x) (L x) :=
  Unary.of_le (Unary.mul ((hK.add (Unary.mul (Unary.const 5) (nP_unary hL))).add (nC_unary hL)) (bxB_unary hn))
    (total_polyT (vLay_polyT hn hL hK)) fun _ => numAV_le_box _ _

include hn hL hV in
theorem numAW_unary' : Unary fun x => numAW (n x) (L x) :=
  Unary.of_le (Unary.mul (((hV.add (Unary.mul (Unary.const 6) (nP_unary hL))).add (nC_unary hL)).add (nQ_unary hL))
    (bxB_unary hn)) (total_polyT (wLay_polyT hn hL hV)) fun _ => numAW_le_box _ _

/-- **The context of the leveled network is computed in polynomial time** (`n`, `g`, `P`, the number
of variables and the number of levels in unary, the description in polynomial time). -/
theorem aCtxOfL_polyT {g P : α → ℕ} (hn : Unary n) (hL : PolyT L) (hV : Unary fun x => (L x).D.nV)
    (hK : Unary fun x => (L x).nL) (hg : Unary g) (hP : Unary P) :
    PolyT fun x => EthFollowup.Primes.aCtxOf (n x) (L x) (g x) (P x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hrW : PolyT fun x => List.range (numAW (n x) (L x)) := PolyT.range (numAW_unary' hn hL hV)
  have hrV : PolyT fun x => List.range (numAV (n x) (L x)) := PolyT.range (numAV_unary' hn hL hK)
  have hlay := layLZ_polyT hn hL hV hK hrW hg hP (Wa_unary hn)
  have hn' : PolyT fun x => List.replicate (n x) () := hn
  have hV' : PolyT fun x => List.replicate (L x).D.nV () := hV
  have hinc : PolyT fun x => (List.range (g x)).map fun a => incLZ (n x) (L x) (List.range (numAW (n x) (L x))) (g x) a :=
    PolyT.map (f := fun x a => incLZ (n x) (L x) (List.range (numAW (n x) (L x))) (g x) a)
      (incLZ_polyT (hn.comp f1) (hL.comp f1) (hV.comp f1) (hK.comp f1)
        (PolyT.comp (f := fun x => List.range (numAW (n x) (L x))) hrW f1) (hg.poly.comp f1)
        (PolyT.snd PolyT.id')) (PolyT.range hg)
  have h : PolyT fun x => (layLZ (n x) (L x) (List.range (numAW (n x) (L x))) (g x) (P x) (Wa (n x)),
      ((List.replicate (n x) (), (L x, List.replicate (L x).D.nV ())),
        ((g x, List.range (numAV (n x) (L x))), (List.range (g x)).map fun a =>
          incLZ (n x) (L x) (List.range (numAW (n x) (L x))) (g x) a))) :=
    PolyT.prodMk hlay (PolyT.prodMk (PolyT.prodMk hn' (PolyT.prodMk hL hV'))
      (PolyT.prodMk (PolyT.prodMk hg.poly hrV) hinc))
  exact h.congr fun x => by
    have e : EthFollowup.Primes.incA (n x) (L x) (g x) =
        fun a => incLZ (n x) (L x) (List.range (numAW (n x) (L x))) (g x) a :=
      funext fun a => incA_eqLZ _ _ _ _
    unfold EthFollowup.Primes.aCtxOf
    rw [layA_eqLZ, e]

end Unary

end EthFollowup.Primes
