/-
# ArithNet, module L3 (part 2): the table procedure and the context in polynomial time

`PolyT` of everything the procedures and the reader of ArithNet evaluate (template:
`Factoring/MulCtxPoly.lean`):
* generic: `List.prod`, the `Blocks` index functions (`off`, `fam`, `loc`, `enc`, `dec`, `idx`, `fOf`,
  `cOf`) via list forms (`off_eq`, `fam_eq`, `loc_eq`, `enc_eq`, `dec_eq`);
* the checks on codes `(family, coordinates)` with the parameters `Prm` of `Factoring` (`chkZ`), the
  table `tabF'` and **`tabAF_polyT`**, **`arithTp_poly`**, **`arithNp_keeps`**;
* the reader: **`aCtxOf_polyT`** (`n`, `g`, `P` in unary; the description in polynomial time with
  `nV` in unary).

Standard axioms only.
-/
import EthFollowup.ModP.ArithProcs
import EthFollowup.ModP.ArithReaderPoly
import EthFollowup.Factoring.MulPackage

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Groundwork Groundwork.Prog EthFollowup.ExactHC EthFollowup.Factoring

/-! ## Generic: products and the index blocks -/

section Generic
variable {α β : Type} [Enc α] [Enc β]

theorem prod_eq_foldr (l : List ℕ) : l.prod = l.foldr (· * ·) 1 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.prod_cons, ih]

theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rcases Nat.eq_zero_or_pos (a * b) with h | h
  · rw [h, Nat.size_zero]; omega
  · rw [Nat.size_le, pow_add]
    exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

@[fun_prop] theorem prod_polyT {l : α → List ℕ} (hl : PolyT l) : PolyT fun x => (l x).prod := by
  obtain ⟨-, t, ht, -, -, hlen⟩ := hl.elim
  have h : PolyT fun x => (l x).foldr (fun e c => e * c) 1 := by
    refine PolyT.foldr_add (g := fun _ e c => e * c) hl (PolyT.const 1) (by fun_prop) ⟨t, ht, ?_⟩
    intro x c e he
    have h1 := len_le_of_mem he
    have h2 := hlen x
    have h3 := size_mul_le e c
    rw [len_nat] at h1
    rw [len_nat, len_nat]
    omega
  exact h.congr fun x => (prod_eq_foldr _).symm

theorem off_eq : ∀ (sz : List ℕ) (f : ℕ), Blocks.off sz f = (sz.take f).sum
  | _, 0 => by simp
  | [], _ + 1 => rfl
  | s :: sz, f + 1 => by rw [Blocks.off_cons_succ, off_eq sz f]; simp

theorem fam_eq : ∀ (sz : List ℕ) (j : ℕ),
    Blocks.fam sz j = (List.range sz.length).countP fun k => decide ((sz.take (k + 1)).sum ≤ j)
  | [], _ => rfl
  | s :: sz, j => by
    rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map]
    simp only [Blocks.fam]
    by_cases h : j < s
    · rw [if_pos h]
      have : List.countP ((fun k => decide (((s :: sz).take (k + 1)).sum ≤ j)) ∘ Nat.succ)
          (List.range sz.length) = 0 :=
        List.countP_eq_zero.2 fun k _ => by
          rw [Function.comp_apply, decide_eq_true_iff]
          simp only [Nat.succ_eq_add_one, List.take_succ_cons, List.sum_cons]; omega
      rw [this]; simp; omega
    · rw [if_neg h, fam_eq sz (j - s)]
      have : List.countP ((fun k => decide (((s :: sz).take (k + 1)).sum ≤ j)) ∘ Nat.succ)
          (List.range sz.length) =
          (List.range sz.length).countP fun k => decide ((sz.take (k + 1)).sum ≤ j - s) :=
        List.countP_congr fun k _ => by
          rw [Function.comp_apply, decide_eq_true_iff, decide_eq_true_iff]
          simp only [Nat.succ_eq_add_one, List.take_succ_cons, List.sum_cons]; omega
      rw [this]; simp; omega

theorem loc_eq (sz : List ℕ) (j : ℕ) : Blocks.loc sz j = j - (sz.take (Blocks.fam sz j)).sum := by
  have := Blocks.off_fam_add_loc sz j
  rw [off_eq] at this
  omega

theorem enc_eq : ∀ (ds xs : List ℕ), Blocks.enc ds xs =
    ((List.range (min ds.length xs.length)).map fun i => xs.getD i 0 * (ds.take i).prod).sum
  | [], xs => by simp
  | _ :: _, [] => by simp [Blocks.enc]
  | d :: ds, x :: xs => by
    rw [Blocks.enc_cons, enc_eq ds xs, List.length_cons, List.length_cons, Nat.succ_min_succ,
      List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [List.getD_cons_zero, List.take_zero, List.prod_nil, mul_one, Function.comp_def,
      List.getD_cons_succ, List.take_succ_cons, List.prod_cons]
    congr 1
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun i _ => by ring

theorem dec_eq : ∀ (ds : List ℕ) (j : ℕ), Blocks.dec ds j =
    (List.range ds.length).map fun i => j / (ds.take i).prod % ds.getD i 0
  | [], _ => rfl
  | d :: ds, j => by
    rw [Blocks.dec_cons, dec_eq ds (j / d), List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.take_zero, List.prod_nil, Nat.div_one, List.getD_cons_zero, Function.comp_def,
      List.take_succ_cons, List.prod_cons, List.getD_cons_succ, Nat.div_div_eq_div_mul]

@[fun_prop] theorem off_polyT {sz : α → List ℕ} {f : α → ℕ} (hs : PolyT sz) (hf : PolyT f) :
    PolyT fun x => Blocks.off (sz x) (f x) :=
  (PolyT.sum (PolyT.take hf hs)).congr fun x => (off_eq _ _).symm

@[fun_prop] theorem fam_polyT {sz : α → List ℕ} {j : α → ℕ} (hs : PolyT sz) (hj : PolyT j) :
    PolyT fun x => Blocks.fam (sz x) (j x) := by
  have hf : PolyT fun p : α × ℕ => p.1 := PolyT.fst PolyT.id'
  have hk : PolyT fun p : α × ℕ => p.2 := PolyT.snd PolyT.id'
  have hb : PolyT fun p : α × ℕ => decide (((sz p.1).take (p.2 + 1)).sum ≤ j p.1) :=
    PolyT.decide_le (PolyT.sum (PolyT.take (PolyT.add hk (PolyT.const 1)) (PolyT.comp hs hf)))
      (PolyT.comp hj hf)
  exact (PolyT.countP (f := fun x k => decide (((sz x).take (k + 1)).sum ≤ j x)) hb
    (PolyT.range (Unary.of_length hs))).congr fun x => (fam_eq _ _).symm

@[fun_prop] theorem loc_polyT {sz : α → List ℕ} {j : α → ℕ} (hs : PolyT sz) (hj : PolyT j) :
    PolyT fun x => Blocks.loc (sz x) (j x) :=
  (PolyT.sub hj (PolyT.sum (PolyT.take (fam_polyT hs hj) hs))).congr fun x => (loc_eq _ _).symm

@[fun_prop] theorem enc_polyT {ds xs : α → List ℕ} (hd : PolyT ds) (hx : PolyT xs) :
    PolyT fun x => Blocks.enc (ds x) (xs x) := by
  have hf : PolyT fun p : α × ℕ => p.1 := PolyT.fst PolyT.id'
  have hk : PolyT fun p : α × ℕ => p.2 := PolyT.snd PolyT.id'
  have hb : PolyT fun p : α × ℕ => (xs p.1).getD p.2 0 * ((ds p.1).take p.2).prod :=
    PolyT.mul (PolyT.getD (PolyT.comp hx hf) hk (PolyT.const 0)) (prod_polyT (PolyT.take hk (PolyT.comp hd hf)))
  have hu : Unary fun x => min (ds x).length (xs x).length :=
    Unary.of_le (Unary.of_length hd) (PolyT.min' (PolyT.length hd) (PolyT.length hx)) fun _ => min_le_left _ _
  exact (PolyT.sum (PolyT.map (f := fun x i => (xs x).getD i 0 * ((ds x).take i).prod) hb
    (PolyT.range hu))).congr fun x => (enc_eq _ _).symm

@[fun_prop] theorem dec_polyT {ds : α → List ℕ} {j : α → ℕ} (hd : PolyT ds) (hj : PolyT j) :
    PolyT fun x => Blocks.dec (ds x) (j x) := by
  have hf : PolyT fun p : α × ℕ => p.1 := PolyT.fst PolyT.id'
  have hk : PolyT fun p : α × ℕ => p.2 := PolyT.snd PolyT.id'
  have hb : PolyT fun p : α × ℕ => j p.1 / ((ds p.1).take p.2).prod % (ds p.1).getD p.2 0 :=
    PolyT.mod (PolyT.div (PolyT.comp hj hf) (prod_polyT (PolyT.take hk (PolyT.comp hd hf))))
      (PolyT.getD (PolyT.comp hd hf) hk (PolyT.const 0))
  exact (PolyT.map (f := fun x i => j x / ((ds x).take i).prod % (ds x).getD i 0) hb
    (PolyT.range (Unary.of_length hd))).congr fun x => (dec_eq _ _).symm

@[fun_prop] theorem sizes_polyT {d : α → List (List ℕ)} (hd : PolyT d) : PolyT fun x => Blocks.sizes (d x) := by
  unfold Blocks.sizes
  exact PolyT.map (f := fun _ l => l.prod) (prod_polyT (PolyT.snd PolyT.id')) hd

@[fun_prop] theorem total_polyT {d : α → List (List ℕ)} (hd : PolyT d) : PolyT fun x => Blocks.total (d x) := by
  unfold Blocks.total; exact PolyT.sum (sizes_polyT hd)

@[fun_prop] theorem idx_polyT {d : α → List (List ℕ)} {f : α → ℕ} {xs : α → List ℕ} (hd : PolyT d)
    (hf : PolyT f) (hx : PolyT xs) : PolyT fun x => Blocks.idx (d x) (f x) (xs x) := by
  unfold Blocks.idx
  exact PolyT.add (off_polyT (sizes_polyT hd) hf) (enc_polyT (PolyT.getD hd hf (PolyT.const [])) hx)

@[fun_prop] theorem fOf_polyT {d : α → List (List ℕ)} {j : α → ℕ} (hd : PolyT d) (hj : PolyT j) :
    PolyT fun x => Blocks.fOf (d x) (j x) := by
  unfold Blocks.fOf; exact fam_polyT (sizes_polyT hd) hj

@[fun_prop] theorem cOf_polyT {d : α → List (List ℕ)} {j : α → ℕ} (hd : PolyT d) (hj : PolyT j) :
    PolyT fun x => Blocks.cOf (d x) (j x) := by
  unfold Blocks.cOf
  exact dec_polyT (PolyT.getD hd (fOf_polyT hd hj) (PolyT.const [])) (loc_polyT (sizes_polyT hd) hj)

end Generic

/-! ## The checks on codes, with the parameters `Prm` -/

open EthFollowup.Factoring.MP EthFollowup.Factoring.MPoly

/-- A wire reader: width, incidence list, setting, wire layout. -/
abbrev Rd : Type := ℕ × (List ℕ × (List Bool × List (List ℕ)))

/-- The value of the wire `(f, co)`, read from the setting. -/
def rdw (r : Rd) (f : ℕ) (co : List ℕ) : ℕ := xz r.1 r.2.1 r.2.2.1 (Blocks.idx r.2.2.2 f co)

/-- `List.range l.length` (an atom: its length is unary). -/
def rgL {β : Type} (l : List β) : List ℕ := List.range l.length

/-- The relation test on codes (`CmpRel.toE`). -/
def testZ (k s : ℕ) : Bool :=
  if k = 0 then s == 0 else if k = 1 then s != 2 else if k = 2 then s == 1 else if k = 3 then s != 0 else s == 2

theorem test_eq (r : CmpRel) (s : ℕ) : r.test s = testZ r.toE s := by cases r <;> rfl

/-- `opLimb` on the code of the operand. -/
def opLimbZ (D : Desc) (r : Rd) (o : Operand) (i : ℕ) : ℕ :=
  o.toE.elim (fun v => if v < D.nV then rdw r 0 [v, i] else 0) (fun l => l.getD i 0)

/-- The comparison step of comparison `q` at cell `i`. -/
def cmpOKZ (p : Prm) (D : Desc) (r : Rd) (q i : ℕ) : Bool :=
  if i = 0 then testZ (D.cmps.getD q default).rel.toE
      (cmpStep (if i + 1 = p.l then 1 else rdw r 9 [q, i]) (opLimbZ D r (.var (D.cmps.getD q default).v) i)
        (opLimbZ D r (D.cmps.getD q default).rhs i))
  else rdw r 9 [q, i - 1] == cmpStep (if i + 1 = p.l then 1 else rdw r 9 [q, i])
      (opLimbZ D r (.var (D.cmps.getD q default).v) i) (opLimbZ D r (D.cmps.getD q default).rhs i)

def cellZ (p : Prm) (D : Desc) (rv : List ℕ) (r : Rd) (i : ℕ) : Bool :=
  (rv.all fun v => decide (rdw r 0 [v, i] < p.pb) && patE p (D.pat.getD v []) i (rdw r 0 [v, i])) &&
  ((rgL D.chains).all fun c => rv.all fun v => rdw r 1 [c, v, i] == rdw r 0 [v, i]) &&
  ((rgL D.prods).all fun pp => (List.range 2).all fun σ => rdw r 2 [pp, σ, i] == opLimbZ D r (opnd D pp σ) i) &&
  ((rgL D.cmps).all fun q => cmpOKZ p D r q i)

def rowZ (p : Prm) (r : Rd) (pp σ i2 : ℕ) : Bool := p.rL1.all fun s =>
  rdw r 3 [pp, σ, s, i2] == rowE p (fun i1 i2 => rdw r 2 [pp, σ, i1 + p.l1 * i2]) s i2
def colZ (p : Prm) (r : Rd) (pp σ s : ℕ) : Bool := p.rL2.all fun t =>
  rdw r 4 [pp, σ, s, t] == colE p (fun s i2 => rdw r 3 [pp, σ, s, i2]) s t
def mulZ (p : Prm) (r : Rd) (pp s t : ℕ) : Bool :=
  rdw r 5 [pp, s, t] == md (rdw r 4 [pp, 0, s, t] * rdw r 4 [pp, 1, s, t]) p.M
def icolZ (p : Prm) (r : Rd) (pp s : ℕ) : Bool := p.rL2.all fun u =>
  rdw r 6 [pp, s, u] == invColE p (fun s t => rdw r 5 [pp, s, t]) s u
def irowZ (p : Prm) (r : Rd) (pp u : ℕ) : Bool := p.rL1.all fun a =>
  rdw r 7 [pp, a, u] == invRowE p (fun s u => rdw r 6 [pp, s, u]) a u

/-- `t.src = .prod pp`, on codes. -/
def isProdZ (sr : Src) (pp : ℕ) : Bool := sr.toE.elim (fun q => decide (q = pp)) (fun _ => false)
/-- `HasProd`, on codes. -/
def hasProdZ (ch : ChainD) (pp : ℕ) : Bool := (ch.lhs ++ ch.rhs).any fun t => isProdZ t.src pp
/-- `chainOf`, on codes. -/
def chainOfZ (D : Desc) (pp : ℕ) : ℕ := (D.chains.map fun ch => hasProdZ ch pp).idxOf true

def tDigZ (p : Prm) (D : Desc) (r : Rd) (c : ℕ) (t : Term) (k : ℕ) : ℕ :=
  t.src.toE.elim
    (fun pp => if pp < D.prods.length ∧ chainOfZ D pp = c then convE p (fun a u => rdw r 7 [pp, a, u]) k else 0)
    (fun e => e.elim (fun v => if v < D.nV ∧ k < p.l then rdw r 1 [c, v, k] else 0) (fun l => l.getD k 0))

def sDigZ (p : Prm) (D : Desc) (r : Rd) (c : ℕ) (ts : List Term) (k : ℕ) : ℕ :=
  (ts.map fun t => t.coeff * tDigZ p D r c t k).sum

/-- The carry offset `2^(J+6) = 2^(W+4)`. -/
def offZ (p : Prm) : ℕ := 2 ^ (p.W + 4)

def carryZ (p : Prm) (D : Desc) (r : Rd) (c k : ℕ) : Bool :=
  decide ((if k + 1 < p.Kc then rdw r 8 [c, k] else offZ p) * p.pb + sDigZ p D r c (D.chains.getD c default).rhs k +
      offZ p = sDigZ p D r c (D.chains.getD c default).lhs k + (if k = 0 then offZ p else rdw r 8 [c, k - 1]) +
      offZ p * p.pb)

/-- **The check of the vertex with code `(f, co)`** (dispatch as `AV.mk`). -/
def chkZ (p : Prm) (D : Desc) (rv : List ℕ) (r : Rd) (f : ℕ) (co : List ℕ) : Bool :=
  if f = 0 then cellZ p D rv r (co.getD 0 0)
  else if f = 1 then rowZ p r (co.getD 0 0) (co.getD 1 0) (co.getD 2 0)
  else if f = 2 then colZ p r (co.getD 0 0) (co.getD 1 0) (co.getD 2 0)
  else if f = 3 then mulZ p r (co.getD 0 0) (co.getD 1 0) (co.getD 2 0)
  else if f = 4 then icolZ p r (co.getD 0 0) (co.getD 1 0)
  else if f = 5 then irowZ p r (co.getD 0 0) (co.getD 1 0)
  else carryZ p D r (co.getD 0 0) (co.getD 1 0)

/-- The coordinates of `AV.mk f co`. -/
def coV (f : ℕ) (co : List ℕ) : List ℕ :=
  if f = 0 then [co.getD 0 0] else if f ≤ 3 then [co.getD 0 0, co.getD 1 0, co.getD 2 0]
  else [co.getD 0 0, co.getD 1 0]

/-- The cluster of the vertex with family `f` and coordinates `co` (as `aClus`). -/
def clusC (vD : List (List ℕ)) (g f : ℕ) (co : List ℕ) : ℕ :=
  VB.vbN ((Blocks.sizes vD).getD f 0) g (Blocks.enc (vD.getD f []) co)

/-- The vertex layout from the parameters. -/
def vDimsZ (p : Prm) (D : Desc) : List (List ℕ) :=
  [[p.l], [D.prods.length, 2, p.l2], [D.prods.length, 2, p.L1], [D.prods.length, p.L1, p.L2],
    [D.prods.length, p.L1], [D.prods.length, p.L2], [D.chains.length, p.Kc]]

/-- The wire layout from the parameters (`nV` given). -/
def wDimsZ (p : Prm) (D : Desc) (nV : ℕ) : List (List ℕ) :=
  [[nV, p.l], [D.chains.length, nV, p.l], [D.prods.length, 2, p.l], [D.prods.length, 2, p.L1, p.l2],
    [D.prods.length, 2, p.L1, p.L2], [D.prods.length, p.L1, p.L2], [D.prods.length, p.L1, p.L2],
    [D.prods.length, p.L1, p.L2], [D.chains.length, p.Kc - 1], [D.cmps.length, p.l - 1]]

theorem vDimsZ_eq (n : ℕ) (D : Desc) : vDimsZ (prmOf n) D = vDims n D := rfl
theorem wDimsZ_eq (n : ℕ) (D : Desc) : wDimsZ (prmOf n) D D.nV = wDims n D := rfl

/-! ### The equations -/

section Eqs
variable (n : ℕ) (D : Desc) (W : ℕ) (inc : List ℕ) (z : List Bool)

/-- The wire values of the table. -/
abbrev xT (d : AW) : ℕ := xz W inc z (awIdx n D d)

theorem xT_eq (d : AW) : xT n D W inc z d = rdw (W, inc, z, wDims n D) d.fam d.co := rfl

theorem opLimbZ_eq (o : Operand) (i : ℕ) :
    opLimb D (xT n D W inc z) o i = opLimbZ D (W, inc, z, wDims n D) o i := by
  cases o <;> rfl

theorem cmpOKZ_eq (q i : ℕ) : cmpOK n D (xT n D W inc z) q i = cmpOKZ (prmOf n) D (W, inc, z, wDims n D) q i := by
  unfold cmpOK cmpCell cmpOKZ
  simp only [test_eq, opLimbZ_eq, prmOf_l, Desc.cq]
  rfl

theorem cellZ_eq (i : ℕ) :
    cellOK n D (xT n D W inc z) i = cellZ (prmOf n) D (List.range D.nV) (W, inc, z, wDims n D) i := by
  unfold cellOK cellZ rgL
  simp only [cmpOKZ_eq, opLimbZ_eq, patE_eq, prmOf_pb]
  rfl

theorem decide_hasProd (ch : ChainD) (pp : ℕ) : decide (ch.HasProd pp) = hasProdZ ch pp := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold ChainD.HasProd hasProdZ
  rw [List.any_eq_true]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  unfold isProdZ
  cases h : t.src <;> simp [Src.toE]

theorem findIdx_eq_idxOf {β : Type} (P : β → Bool) : ∀ l : List β, l.findIdx P = (l.map P).idxOf true
  | [] => rfl
  | a :: l => by
    rw [List.findIdx_cons, List.map_cons, List.idxOf_cons, findIdx_eq_idxOf P l]
    cases P a <;> rfl

theorem chainOfZ_eq (pp : ℕ) : D.chainOf pp = chainOfZ D pp := by
  unfold Desc.chainOf chainOfZ
  rw [findIdx_eq_idxOf]
  simp only [decide_hasProd]

theorem tDigZ_eq (c : ℕ) (t : Term) (k : ℕ) :
    tDig n D (xT n D W inc z) c t k = tDigZ (prmOf n) D (W, inc, z, wDims n D) c t k := by
  unfold tDig tDigZ
  rcases h : t.src with pp | v | l
  · simp only [Src.toE, Sum.elim_inl, chainOfZ_eq, convE_eq, prmOf_l]
    rfl
  · simp only [Src.toE, Sum.elim_inr, Sum.elim_inl, prmOf_l]
    rfl
  · rfl

theorem sDigZ_eq (c : ℕ) (ts : List Term) (k : ℕ) :
    sDig n D (xT n D W inc z) c ts k = sDigZ (prmOf n) D (W, inc, z, wDims n D) c ts k := by
  unfold sDig sDigZ; simp only [tDigZ_eq]

theorem offZ_eq : offZ (prmOf n) = aOFF n := by
  unfold offZ aOFF; rw [prmOf_W]; unfold W; congr 1

theorem chkZ_eq (f : ℕ) (co : List ℕ) :
    aChk n D (xT n D W inc z) (AV.mk f co) = chkZ (prmOf n) D (List.range D.nV) (W, inc, z, wDims n D) f co := by
  rcases f with _ | _ | _ | _ | _ | _ | f
  · exact cellZ_eq n D W inc z _
  · simp only [AV.mk, aChk, chkZ, rowZ, rowE_eq]; rfl
  · simp only [AV.mk, aChk, chkZ, colZ, colE_eq]; rfl
  · simp only [AV.mk, aChk, chkZ, mulZ, md]; rfl
  · simp only [AV.mk, aChk, chkZ, icolZ, invColE_eq]; rfl
  · simp only [AV.mk, aChk, chkZ, irowZ, invRowE_eq]; rfl
  · have h0 : f + 1 + 1 + 1 + 1 + 1 + 1 ≠ 0 := by omega
    have h1 : f + 1 + 1 + 1 + 1 + 1 + 1 ≠ 1 := by omega
    have h2 : f + 1 + 1 + 1 + 1 + 1 + 1 ≠ 2 := by omega
    have h3 : f + 1 + 1 + 1 + 1 + 1 + 1 ≠ 3 := by omega
    have h4 : f + 1 + 1 + 1 + 1 + 1 + 1 ≠ 4 := by omega
    have h5 : f + 1 + 1 + 1 + 1 + 1 + 1 ≠ 5 := by omega
    simp only [AV.mk, aChk, chkZ, h0, h1, h2, h3, h4, h5, if_false, carryZ, carryChk, sDigZ_eq, offZ_eq,
      prmOf_Kc, prmOf_pb, Desc.ch, xT_eq, AW.fam, AW.co]

theorem avmk_fam (f : ℕ) (co : List ℕ) : (AV.mk f co).fam = min f 6 := by
  rcases f with _ | _ | _ | _ | _ | _ | f <;> simp [AV.mk, AV.fam]

theorem avmk_co (f : ℕ) (co : List ℕ) : (AV.mk f co).co = coV f co := by
  rcases f with _ | _ | _ | _ | _ | _ | f <;> simp [AV.mk, AV.co, coV]

theorem aClus_eq (g : ℕ) (v : AV) : aClus n D g v = clusC (vDims n D) g v.fam v.co := rfl

end Eqs

/-! ### Polynomial time of the checks -/

section ZPoly
variable {α : Type} [Enc α]

@[fun_prop] theorem rdw_polyT {r : α → Rd} {f : α → ℕ} {co : α → List ℕ} (hr : PolyT r) (hf : PolyT f)
    (hco : PolyT co) : PolyT fun x => rdw (r x) (f x) (co x) := by
  unfold rdw; fun_prop

@[fun_prop] theorem rgL_polyT {β : Type} [Enc β] {l : α → List β} (hl : PolyT l) : PolyT fun x => rgL (l x) :=
  PolyT.range (Unary.of_length hl)

@[fun_prop] theorem testZ_polyT {k s : α → ℕ} (hk : PolyT k) (hs : PolyT s) : PolyT fun x => testZ (k x) (s x) := by
  unfold testZ; fun_prop

@[fun_prop] theorem CmpRel.toE_polyT {r : α → CmpRel} (hr : PolyT r) : PolyT fun x => (r x).toE :=
  polyT_toE_of CmpRel.toE (fun _ => rfl) hr
@[fun_prop] theorem Operand.toE_polyT {o : α → Operand} (ho : PolyT o) : PolyT fun x => (o x).toE :=
  polyT_toE_of Operand.toE (fun _ => rfl) ho
@[fun_prop] theorem Src.toE_polyT {o : α → Src} (ho : PolyT o) : PolyT fun x => (o x).toE :=
  polyT_toE_of Src.toE (fun _ => rfl) ho

@[fun_prop] theorem cmpN_polyT {u v : α → ℕ} (hu : PolyT u) (hv : PolyT v) : PolyT fun x => cmpN (u x) (v x) := by
  unfold cmpN; fun_prop
@[fun_prop] theorem cmpStep_polyT {s y q : α → ℕ} (hs : PolyT s) (hy : PolyT y) (hq : PolyT q) :
    PolyT fun x => cmpStep (s x) (y x) (q x) := by
  unfold cmpStep; fun_prop

@[fun_prop] theorem getD_prods_polyT {D : α → Desc} {k : α → ℕ} (hD : PolyT D) (hk : PolyT k) :
    PolyT fun x => (D x).prods.getD (k x) default := PolyT.getD (Desc.prods_polyT hD) hk (PolyT.const _)
@[fun_prop] theorem getD_chains_polyT {D : α → Desc} {k : α → ℕ} (hD : PolyT D) (hk : PolyT k) :
    PolyT fun x => (D x).chains.getD (k x) default := PolyT.getD (Desc.chains_polyT hD) hk (PolyT.const _)
@[fun_prop] theorem getD_cmps_polyT {D : α → Desc} {k : α → ℕ} (hD : PolyT D) (hk : PolyT k) :
    PolyT fun x => (D x).cmps.getD (k x) default := PolyT.getD (Desc.cmps_polyT hD) hk (PolyT.const _)

variable {p : α → Prm} {D : α → Desc} {r : α → Rd} (hp : PolyT p) (hD : PolyT D) (hr : PolyT r)
include hp hD hr

@[fun_prop] theorem opLimbZ_polyT {o : α → Operand} {i : α → ℕ} (ho : PolyT o) (hi : PolyT i) :
    PolyT fun x => opLimbZ (D x) (r x) (o x) (i x) := by
  have hf : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hg : PolyT fun q : α × List ℕ => q.1 := PolyT.fst PolyT.id'
  have hDq : PolyT fun q : α × ℕ => D q.1 := PolyT.comp hD hf
  have hrq : PolyT fun q : α × ℕ => r q.1 := PolyT.comp hr hf
  have hiq : PolyT fun q : α × ℕ => i q.1 := PolyT.comp hi hf
  have h1 : PolyT fun q : α × ℕ => if q.2 < (D q.1).nV then rdw (r q.1) 0 [q.2, i q.1] else 0 :=
    PolyT.ite' (PolyT.decide_lt (PolyT.snd PolyT.id') (Desc.nV_polyT hDq))
      (rdw_polyT hrq (PolyT.const 0) (PolyT.cons' (PolyT.snd PolyT.id') (PolyT.cons' hiq (PolyT.const []))))
      (PolyT.const 0)
  have h2 : PolyT fun q : α × List ℕ => q.2.getD (i q.1) 0 :=
    PolyT.getD (PolyT.snd PolyT.id') (PolyT.comp hi hg) (PolyT.const 0)
  exact PolyT.sumElim (s := fun x => (o x).toE) (f := fun x v => if v < (D x).nV then rdw (r x) 0 [v, i x] else 0)
    (g := fun x l => l.getD (i x) 0) (Operand.toE_polyT ho) h1 h2

omit hp hr in
@[fun_prop] theorem opnd_polyT {pp σ : α → ℕ} (hpp : PolyT pp) (hσ : PolyT σ) :
    PolyT fun x => opnd (D x) (pp x) (σ x) := by
  have h := getD_prods_polyT hD hpp
  unfold opnd
  exact PolyT.ite' (PolyT.decide_eq hσ (PolyT.const 0)) (Operand.var_polyT (ProdD.u_polyT h)) (ProdD.w_polyT h)

@[fun_prop] theorem cmpOKZ_polyT {q i : α → ℕ} (hq : PolyT q) (hi : PolyT i) :
    PolyT fun x => cmpOKZ (p x) (D x) (r x) (q x) (i x) := by
  have hcq := getD_cmps_polyT hD hq
  have hA : PolyT fun x => if i x + 1 = (p x).l then 1 else rdw (r x) 9 [q x, i x] :=
    PolyT.ite' (PolyT.decide_eq (PolyT.add hi (PolyT.const 1)) (l_polyT hp)) (PolyT.const 1)
      (rdw_polyT hr (PolyT.const 9) (PolyT.cons' hq (PolyT.cons' hi (PolyT.const []))))
  have hyl := opLimbZ_polyT hp hD hr (Operand.var_polyT (CmpD.v_polyT hcq)) hi
  have hpl := opLimbZ_polyT hp hD hr (CmpD.rhs_polyT hcq) hi
  have hst := cmpStep_polyT hA hyl hpl
  unfold cmpOKZ
  exact PolyT.ite' (PolyT.decide_eq hi (PolyT.const 0)) (testZ_polyT (CmpRel.toE_polyT (CmpD.rel_polyT hcq)) hst)
    (PolyT.beq' (rdw_polyT hr (PolyT.const 9) (PolyT.cons' hq (PolyT.cons' (PolyT.sub hi (PolyT.const 1))
      (PolyT.const [])))) hst)

set_option maxHeartbeats 1000000 in
@[fun_prop] theorem cellZ_polyT {rv : α → List ℕ} {i : α → ℕ} (hrv : PolyT rv) (hi : PolyT i) :
    PolyT fun x => cellZ (p x) (D x) (rv x) (r x) (i x) := by
  -- contexts x, (x, v), ((x, c), v)
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have f2 : PolyT fun q : (α × ℕ) × ℕ => q.1.1 := PolyT.fst (PolyT.fst PolyT.id')
  have m2 : PolyT fun q : (α × ℕ) × ℕ => q.1.2 := PolyT.snd (PolyT.fst PolyT.id')
  have s2 : PolyT fun q : (α × ℕ) × ℕ => q.2 := PolyT.snd PolyT.id'
  have hA : PolyT fun x => (rv x).all fun v =>
      decide (rdw (r x) 0 [v, i x] < (p x).pb) && patE (p x) ((D x).pat.getD v []) (i x) (rdw (r x) 0 [v, i x]) := by
    have hR0 : PolyT fun q : α × ℕ => rdw (r q.1) 0 [q.2, i q.1] :=
      rdw_polyT (PolyT.comp hr f1) (PolyT.const 0) (PolyT.cons' s1 (PolyT.cons' (PolyT.comp hi f1) (PolyT.const [])))
    exact PolyT.all (f := fun x v => decide (rdw (r x) 0 [v, i x] < (p x).pb) &&
        patE (p x) ((D x).pat.getD v []) (i x) (rdw (r x) 0 [v, i x]))
      (PolyT.and' (PolyT.decide_lt hR0 (pb_polyT (PolyT.comp hp f1)))
        (patE_polyT (PolyT.comp hp f1) (PolyT.getD (Desc.pat_polyT (PolyT.comp hD f1)) s1 (PolyT.const []))
          (PolyT.comp hi f1) hR0)) hrv
  have hB : PolyT fun x => (rgL (D x).chains).all fun c => (rv x).all fun v =>
      rdw (r x) 1 [c, v, i x] == rdw (r x) 0 [v, i x] := by
    have hin : PolyT fun q : (α × ℕ) × ℕ => rdw (r q.1.1) 1 [q.1.2, q.2, i q.1.1] == rdw (r q.1.1) 0 [q.2, i q.1.1] :=
      PolyT.beq' (rdw_polyT (PolyT.comp hr f2) (PolyT.const 1)
          (PolyT.cons' m2 (PolyT.cons' s2 (PolyT.cons' (PolyT.comp hi f2) (PolyT.const [])))))
        (rdw_polyT (PolyT.comp hr f2) (PolyT.const 0) (PolyT.cons' s2 (PolyT.cons' (PolyT.comp hi f2) (PolyT.const []))))
    have hout : PolyT fun q : α × ℕ => (rv q.1).all fun v => rdw (r q.1) 1 [q.2, v, i q.1] == rdw (r q.1) 0 [v, i q.1] :=
      PolyT.all (f := fun (q : α × ℕ) v => rdw (r q.1) 1 [q.2, v, i q.1] == rdw (r q.1) 0 [v, i q.1]) hin
        (PolyT.comp hrv f1)
    exact PolyT.all (f := fun x c => (rv x).all fun v => rdw (r x) 1 [c, v, i x] == rdw (r x) 0 [v, i x]) hout
      (rgL_polyT (Desc.chains_polyT hD))
  have hC : PolyT fun x => (rgL (D x).prods).all fun pp => (List.range 2).all fun σ =>
      rdw (r x) 2 [pp, σ, i x] == opLimbZ (D x) (r x) (opnd (D x) pp σ) (i x) := by
    have hin : PolyT fun q : (α × ℕ) × ℕ => rdw (r q.1.1) 2 [q.1.2, q.2, i q.1.1] ==
        opLimbZ (D q.1.1) (r q.1.1) (opnd (D q.1.1) q.1.2 q.2) (i q.1.1) :=
      PolyT.beq' (rdw_polyT (PolyT.comp hr f2) (PolyT.const 2)
          (PolyT.cons' m2 (PolyT.cons' s2 (PolyT.cons' (PolyT.comp hi f2) (PolyT.const [])))))
        (opLimbZ_polyT (PolyT.comp hp f2) (PolyT.comp hD f2) (PolyT.comp hr f2)
          (opnd_polyT (PolyT.comp hD f2) m2 s2) (PolyT.comp hi f2))
    have hout : PolyT fun q : α × ℕ => (List.range 2).all fun σ =>
        rdw (r q.1) 2 [q.2, σ, i q.1] == opLimbZ (D q.1) (r q.1) (opnd (D q.1) q.2 σ) (i q.1) :=
      PolyT.all (f := fun (q : α × ℕ) σ => rdw (r q.1) 2 [q.2, σ, i q.1] ==
        opLimbZ (D q.1) (r q.1) (opnd (D q.1) q.2 σ) (i q.1)) hin (PolyT.const _)
    exact PolyT.all (f := fun x pp => (List.range 2).all fun σ =>
      rdw (r x) 2 [pp, σ, i x] == opLimbZ (D x) (r x) (opnd (D x) pp σ) (i x)) hout (rgL_polyT (Desc.prods_polyT hD))
  have hE : PolyT fun x => (rgL (D x).cmps).all fun q => cmpOKZ (p x) (D x) (r x) q (i x) :=
    PolyT.all (f := fun x q => cmpOKZ (p x) (D x) (r x) q (i x))
      (cmpOKZ_polyT (PolyT.comp hp f1) (PolyT.comp hD f1) (PolyT.comp hr f1) s1 (PolyT.comp hi f1))
      (rgL_polyT (Desc.cmps_polyT hD))
  unfold cellZ
  exact PolyT.and' (PolyT.and' (PolyT.and' hA hB) hC) hE

omit hD in
@[fun_prop] theorem rowZ_polyT {a b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) :
    PolyT fun x => rowZ (p x) (r x) (a x) (b x) (c x) := by
  unfold rowZ rowE; fun_prop
omit hD in
@[fun_prop] theorem colZ_polyT {a b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) :
    PolyT fun x => colZ (p x) (r x) (a x) (b x) (c x) := by
  unfold colZ colE; fun_prop
omit hD in
@[fun_prop] theorem mulZ_polyT {a b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) :
    PolyT fun x => mulZ (p x) (r x) (a x) (b x) (c x) := by
  unfold mulZ; fun_prop
omit hD in
@[fun_prop] theorem icolZ_polyT {a b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => icolZ (p x) (r x) (a x) (b x) := by
  unfold icolZ invColE; fun_prop
omit hD in
@[fun_prop] theorem irowZ_polyT {a b : α → ℕ} (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => irowZ (p x) (r x) (a x) (b x) := by
  unfold irowZ invRowE; fun_prop

omit hp hD hr in
@[fun_prop] theorem isProdZ_polyT {sr : α → Src} {pp : α → ℕ} (hs : PolyT sr) (hpp : PolyT pp) :
    PolyT fun x => isProdZ (sr x) (pp x) := by
  have hf : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have h1 : PolyT fun q : α × ℕ => decide (q.2 = pp q.1) :=
    PolyT.decide_eq (PolyT.snd PolyT.id') (PolyT.comp hpp hf)
  unfold isProdZ
  exact PolyT.sumElim (s := fun x => (sr x).toE) (f := fun x q => decide (q = pp x)) (g := fun _ _ => false)
    (Src.toE_polyT hs) h1
    (PolyT.const false)

omit hp hD hr in
@[fun_prop] theorem hasProdZ_polyT {ch : α → ChainD} {pp : α → ℕ} (hc : PolyT ch) (hpp : PolyT pp) :
    PolyT fun x => hasProdZ (ch x) (pp x) := by
  unfold hasProdZ; fun_prop

omit hp hr in
@[fun_prop] theorem chainOfZ_polyT {pp : α → ℕ} (hpp : PolyT pp) : PolyT fun x => chainOfZ (D x) (pp x) := by
  unfold chainOfZ; fun_prop

omit hD in
@[fun_prop] theorem convRd_polyT {pp k : α → ℕ} (hpp : PolyT pp) (hk : PolyT k) :
    PolyT fun x => convE (p x) (fun a u => rdw (r x) 7 [pp x, a, u]) (k x) := by
  unfold convE; fun_prop

@[fun_prop] theorem tDigZ_polyT {c k : α → ℕ} {t : α → Term} (hc : PolyT c) (ht : PolyT t) (hk : PolyT k) :
    PolyT fun x => tDigZ (p x) (D x) (r x) (c x) (t x) (k x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hDq := PolyT.comp hD f1
  have h1 : PolyT fun q : α × ℕ => if q.2 < (D q.1).prods.length ∧ chainOfZ (D q.1) q.2 = c q.1 then
      convE (p q.1) (fun a u => rdw (r q.1) 7 [q.2, a, u]) (k q.1) else 0 :=
    PolyT.ite' (PolyT.decide_and (PolyT.decide_lt s1 (PolyT.length (Desc.prods_polyT hDq)))
        (PolyT.decide_eq (chainOfZ_polyT hDq s1) (PolyT.comp hc f1)))
      (convRd_polyT (PolyT.comp hp f1) (PolyT.comp hr f1) s1 (PolyT.comp hk f1)) (PolyT.const 0)
  have f3 : PolyT fun q : (α × (ℕ ⊕ List ℕ)) × ℕ => q.1.1 := PolyT.fst (PolyT.fst PolyT.id')
  have s3 : PolyT fun q : (α × (ℕ ⊕ List ℕ)) × ℕ => q.2 := PolyT.snd PolyT.id'
  have f4 : PolyT fun q : (α × (ℕ ⊕ List ℕ)) × List ℕ => q.1.1 := PolyT.fst (PolyT.fst PolyT.id')
  have h2 : PolyT fun q : (α × (ℕ ⊕ List ℕ)) × ℕ => if q.2 < (D q.1.1).nV ∧ k q.1.1 < (p q.1.1).l then
      rdw (r q.1.1) 1 [c q.1.1, q.2, k q.1.1] else 0 :=
    PolyT.ite' (PolyT.decide_and (PolyT.decide_lt s3 (Desc.nV_polyT (PolyT.comp hD f3)))
        (PolyT.decide_lt (PolyT.comp hk f3) (l_polyT (PolyT.comp hp f3))))
      (rdw_polyT (PolyT.comp hr f3) (PolyT.const 1) (PolyT.cons' (PolyT.comp hc f3)
        (PolyT.cons' s3 (PolyT.cons' (PolyT.comp hk f3) (PolyT.const []))))) (PolyT.const 0)
  have h3 : PolyT fun q : (α × (ℕ ⊕ List ℕ)) × List ℕ => q.2.getD (k q.1.1) 0 :=
    PolyT.getD (PolyT.snd PolyT.id') (PolyT.comp hk f4) (PolyT.const 0)
  have h23 : PolyT fun q : α × (ℕ ⊕ List ℕ) => q.2.elim
      (fun v => if v < (D q.1).nV ∧ k q.1 < (p q.1).l then rdw (r q.1) 1 [c q.1, v, k q.1] else 0)
      (fun l => l.getD (k q.1) 0) :=
    PolyT.sumElim (s := fun q : α × (ℕ ⊕ List ℕ) => q.2) (f := fun (q : α × (ℕ ⊕ List ℕ)) v =>
      if v < (D q.1).nV ∧ k q.1 < (p q.1).l then rdw (r q.1) 1 [c q.1, v, k q.1] else 0)
      (g := fun q l => l.getD (k q.1) 0) (PolyT.snd PolyT.id') h2 h3
  have h := PolyT.sumElim (s := fun x => (t x).src.toE)
    (f := fun x pp => if pp < (D x).prods.length ∧ chainOfZ (D x) pp = c x then
      convE (p x) (fun a u => rdw (r x) 7 [pp, a, u]) (k x) else 0)
    (g := fun x e => e.elim
      (fun v => if v < (D x).nV ∧ k x < (p x).l then rdw (r x) 1 [c x, v, k x] else 0) (fun l => l.getD (k x) 0))
    (Src.toE_polyT (Term.src_polyT ht)) h1 h23
  exact h.congr fun x => rfl

@[fun_prop] theorem sDigZ_polyT {c k : α → ℕ} {ts : α → List Term} (hc : PolyT c) (hts : PolyT ts) (hk : PolyT k) :
    PolyT fun x => sDigZ (p x) (D x) (r x) (c x) (ts x) (k x) := by
  have f1 : PolyT fun q : α × Term => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × Term => q.2 := PolyT.snd PolyT.id'
  refine PolyT.congr ?_ fun x => (rfl : _ = sDigZ (p x) (D x) (r x) (c x) (ts x) (k x))
  exact PolyT.sum (PolyT.map (f := fun x t => t.coeff * tDigZ (p x) (D x) (r x) (c x) t (k x))
    (PolyT.mul (Term.coeff_polyT s1) (tDigZ_polyT (PolyT.comp hp f1) (PolyT.comp hD f1) (PolyT.comp hr f1)
      (PolyT.comp hc f1) s1 (PolyT.comp hk f1))) hts)

omit hD hr in
@[fun_prop] theorem offZ_polyT : PolyT fun x => offZ (p x) := by
  unfold offZ Prm.W
  exact PolyT.two_pow (Unary.add (Unary.of_length (uW_polyT hp)) (Unary.const 4))

@[fun_prop] theorem carryZ_polyT {c k : α → ℕ} (hc : PolyT c) (hk : PolyT k) :
    PolyT fun x => carryZ (p x) (D x) (r x) (c x) (k x) := by
  have hch := getD_chains_polyT hD hc
  have hO := offZ_polyT hp
  have hpb := pb_polyT hp
  have hout : PolyT fun x => if k x + 1 < (p x).Kc then rdw (r x) 8 [c x, k x] else offZ (p x) :=
    PolyT.ite' (PolyT.decide_lt (PolyT.add hk (PolyT.const 1)) (Kc_polyT hp))
      (rdw_polyT hr (PolyT.const 8) (PolyT.cons' hc (PolyT.cons' hk (PolyT.const [])))) hO
  have hin : PolyT fun x => if k x = 0 then offZ (p x) else rdw (r x) 8 [c x, k x - 1] :=
    PolyT.ite' (PolyT.decide_eq hk (PolyT.const 0)) hO
      (rdw_polyT hr (PolyT.const 8) (PolyT.cons' hc (PolyT.cons' (PolyT.sub hk (PolyT.const 1)) (PolyT.const []))))
  have hr' := sDigZ_polyT hp hD hr hc (ChainD.rhs_polyT hch) hk
  have hl' := sDigZ_polyT hp hD hr hc (ChainD.lhs_polyT hch) hk
  refine PolyT.congr ?_ fun x => (rfl : _ = carryZ (p x) (D x) (r x) (c x) (k x))
  exact PolyT.decide_eq (PolyT.add (PolyT.add (PolyT.mul hout hpb) hr') hO)
    (PolyT.add (PolyT.add hl' hin) (PolyT.mul hO hpb))

@[fun_prop] theorem chkZ_polyT {rv : α → List ℕ} {f : α → ℕ} {co : α → List ℕ} (hrv : PolyT rv) (hf : PolyT f)
    (hco : PolyT co) : PolyT fun x => chkZ (p x) (D x) (rv x) (r x) (f x) (co x) := by
  have g0 : PolyT fun x => (co x).getD 0 0 := PolyT.getD hco (PolyT.const 0) (PolyT.const 0)
  have g1 : PolyT fun x => (co x).getD 1 0 := PolyT.getD hco (PolyT.const 1) (PolyT.const 0)
  have g2 : PolyT fun x => (co x).getD 2 0 := PolyT.getD hco (PolyT.const 2) (PolyT.const 0)
  have e : ∀ k : ℕ, PolyT fun x => decide (f x = k) := fun k => PolyT.decide_eq hf (PolyT.const k)
  refine PolyT.congr ?_ fun x => (rfl : _ = chkZ (p x) (D x) (rv x) (r x) (f x) (co x))
  exact PolyT.ite' (e 0) (cellZ_polyT hp hD hr hrv g0)
    (PolyT.ite' (e 1) (rowZ_polyT hp hr g0 g1 g2)
    (PolyT.ite' (e 2) (colZ_polyT hp hr g0 g1 g2)
    (PolyT.ite' (e 3) (mulZ_polyT hp hr g0 g1 g2)
    (PolyT.ite' (e 4) (icolZ_polyT hp hr g0 g1)
    (PolyT.ite' (e 5) (irowZ_polyT hp hr g0 g1) (carryZ_polyT hp hD hr g0 g1))))))

end ZPoly

section ZPoly2
variable {α : Type} [Enc α]

@[fun_prop] theorem coV_polyT {f : α → ℕ} {co : α → List ℕ} (hf : PolyT f) (hco : PolyT co) :
    PolyT fun x => coV (f x) (co x) := by
  unfold coV; fun_prop

@[fun_prop] theorem clusC_polyT {vD : α → List (List ℕ)} {g f : α → ℕ} {co : α → List ℕ} (hv : PolyT vD)
    (hg : PolyT g) (hf : PolyT f) (hco : PolyT co) : PolyT fun x => clusC (vD x) (g x) (f x) (co x) := by
  unfold clusC; fun_prop

@[fun_prop] theorem vDimsZ_polyT {p : α → Prm} {D : α → Desc} (hp : PolyT p) (hD : PolyT D) :
    PolyT fun x => vDimsZ (p x) (D x) := by
  unfold vDimsZ; fun_prop

@[fun_prop] theorem wDimsZ_polyT {p : α → Prm} {D : α → Desc} {v : α → ℕ} (hp : PolyT p) (hD : PolyT D)
    (hv : PolyT v) : PolyT fun x => wDimsZ (p x) (D x) (v x) := by
  unfold wDimsZ; fun_prop

end ZPoly2

/-! ## The table procedure in polynomial time -/

/-- The table on codes, with the parameters `p`. -/
def tabZ (p : Prm) (c : ACtx) (a : ℕ) (z : List Bool) : Bool :=
  c.rV.all fun j =>
    !(decide (clusC (vDimsZ p c.D) c.g (min (Blocks.fOf (vDimsZ p c.D) j) 6)
      (coV (Blocks.fOf (vDimsZ p c.D) j) (Blocks.cOf (vDimsZ p c.D) j)) = a)) ||
    chkZ p c.D (rgL c.2.1.2.2) (p.W + 6, c.inc.getD a [], z, wDimsZ p c.D c.D.nV)
      (Blocks.fOf (vDimsZ p c.D) j) (Blocks.cOf (vDimsZ p c.D) j)

theorem Wa_eq (n : ℕ) : Wa n = (prmOf n).W + 6 := by rw [prmOf_W]; unfold Wa W; omega

theorem tabA_eqZ (c : ACtx) (a : ℕ) (z : List Bool) : tabA c a z = tabZ (prmOf c.n) c a z := by
  unfold tabA tabZ avOf
  simp only [aClus_eq, avmk_fam, avmk_co, chkZ_eq, ← vDimsZ_eq, Wa_eq]
  rfl

section TPoly
variable {α : Type} [Enc α]

@[fun_prop] theorem ACtx.n_polyT {c : α → ACtx} (hc : PolyT c) : PolyT fun x => (c x).n :=
  PolyT.length (PolyT.fst (PolyT.fst (PolyT.snd hc)))
theorem ACtx.n_unary {c : α → ACtx} (hc : PolyT c) : Unary fun x => (c x).n :=
  Unary.of_length (PolyT.fst (PolyT.fst (PolyT.snd hc)))
@[fun_prop] theorem ACtx.D_polyT {c : α → ACtx} (hc : PolyT c) : PolyT fun x => (c x).D := by
  have h0 : PolyT fun x => (c x).2.1.2.1 := PolyT.fst (PolyT.snd (PolyT.fst (PolyT.snd hc)))
  have h1 : PolyT fun x => (c x).2.1.2.2 := PolyT.snd (PolyT.snd (PolyT.fst (PolyT.snd hc)))
  exact (Desc.mk_polyT (PolyT.length h1) (Desc.pat_polyT h0) (Desc.prods_polyT h0) (Desc.chains_polyT h0)
    (Desc.cmps_polyT h0)).congr fun x => rfl
@[fun_prop] theorem ACtx.g_polyT {c : α → ACtx} (hc : PolyT c) : PolyT fun x => (c x).g :=
  PolyT.fst (PolyT.fst (PolyT.snd (PolyT.snd hc)))
@[fun_prop] theorem ACtx.rV_polyT {c : α → ACtx} (hc : PolyT c) : PolyT fun x => (c x).rV :=
  PolyT.snd (PolyT.fst (PolyT.snd (PolyT.snd hc)))
@[fun_prop] theorem ACtx.inc_polyT {c : α → ACtx} (hc : PolyT c) : PolyT fun x => (c x).inc :=
  PolyT.snd (PolyT.snd (PolyT.snd hc))

theorem tabZ_polyT {p : α → Prm} {c : α → ACtx} {a : α → ℕ} {z : α → List Bool} (hp : PolyT p) (hc : PolyT c)
    (ha : PolyT a) (hz : PolyT z) : PolyT fun x => tabZ (p x) (c x) (a x) (z x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hpq := PolyT.comp hp f1
  have hcq := PolyT.comp hc f1
  have hDq := ACtx.D_polyT hcq
  have hvD : PolyT fun q : α × ℕ => vDimsZ (p q.1) (c q.1).D := vDimsZ_polyT hpq hDq
  have hf : PolyT fun q : α × ℕ => Blocks.fOf (vDimsZ (p q.1) (c q.1).D) q.2 := fOf_polyT hvD s1
  have hco : PolyT fun q : α × ℕ => Blocks.cOf (vDimsZ (p q.1) (c q.1).D) q.2 := cOf_polyT hvD s1
  have hcl : PolyT fun q : α × ℕ => clusC (vDimsZ (p q.1) (c q.1).D) (c q.1).g
      (min (Blocks.fOf (vDimsZ (p q.1) (c q.1).D) q.2) 6)
      (coV (Blocks.fOf (vDimsZ (p q.1) (c q.1).D) q.2) (Blocks.cOf (vDimsZ (p q.1) (c q.1).D) q.2)) :=
    clusC_polyT hvD (ACtx.g_polyT hcq) (PolyT.min' hf (PolyT.const 6)) (coV_polyT hf hco)
  have hrd : PolyT fun q : α × ℕ => ((p q.1).W + 6, (c q.1).inc.getD (a q.1) [], z q.1,
      wDimsZ (p q.1) (c q.1).D (c q.1).D.nV) :=
    PolyT.prodMk (PolyT.add (W_polyT hpq) (PolyT.const 6)) (PolyT.prodMk
      (PolyT.getD (ACtx.inc_polyT hcq) (PolyT.comp ha f1) (PolyT.const []))
      (PolyT.prodMk (PolyT.comp hz f1) (wDimsZ_polyT hpq hDq (Desc.nV_polyT hDq))))
  have hrv : PolyT fun q : α × ℕ => rgL (c q.1).2.1.2.2 :=
    rgL_polyT (PolyT.snd (PolyT.snd (PolyT.fst (PolyT.snd hcq))))
  have hck := chkZ_polyT hpq hDq hrd hrv hf hco
  have hbody : PolyT fun q : α × ℕ =>
      (!(decide (clusC (vDimsZ (p q.1) (c q.1).D) (c q.1).g (min (Blocks.fOf (vDimsZ (p q.1) (c q.1).D) q.2) 6)
        (coV (Blocks.fOf (vDimsZ (p q.1) (c q.1).D) q.2) (Blocks.cOf (vDimsZ (p q.1) (c q.1).D) q.2)) = a q.1)) ||
      chkZ (p q.1) (c q.1).D (rgL (c q.1).2.1.2.2) ((p q.1).W + 6, (c q.1).inc.getD (a q.1) [], z q.1,
        wDimsZ (p q.1) (c q.1).D (c q.1).D.nV) (Blocks.fOf (vDimsZ (p q.1) (c q.1).D) q.2)
        (Blocks.cOf (vDimsZ (p q.1) (c q.1).D) q.2)) :=
    PolyT.or' (PolyT.not' (PolyT.decide_eq hcl (PolyT.comp ha f1))) hck
  have h := PolyT.all (f := fun x j =>
      !(decide (clusC (vDimsZ (p x) (c x).D) (c x).g (min (Blocks.fOf (vDimsZ (p x) (c x).D) j) 6)
        (coV (Blocks.fOf (vDimsZ (p x) (c x).D) j) (Blocks.cOf (vDimsZ (p x) (c x).D) j)) = a x)) ||
      chkZ (p x) (c x).D (rgL (c x).2.1.2.2) ((p x).W + 6, (c x).inc.getD (a x) [], z x,
        wDimsZ (p x) (c x).D (c x).D.nV) (Blocks.fOf (vDimsZ (p x) (c x).D) j)
        (Blocks.cOf (vDimsZ (p x) (c x).D) j)) hbody (ACtx.rV_polyT hc)
  exact h.congr fun x => rfl

/-- **The table entry is polynomial-time.** -/
theorem tabAF_polyT : PolyT tabAF := by
  have hc : PolyT fun q : ACtx × WQ => q.1 := PolyT.fst PolyT.id'
  have hp : PolyT fun q : ACtx × WQ => prmOf q.1.n := prmOf_polyT (ACtx.n_unary hc)
  have ht := tabZ_polyT hp hc (PolyT.fst (PolyT.snd PolyT.id')) (PolyT.snd (PolyT.snd PolyT.id'))
  have h : PolyT fun q : ACtx × WQ => if tabZ (prmOf q.1.n) q.1 q.2.1 q.2.2 = true then (1 : ℤ) else 0 :=
    PolyT.ite' (PolyT.decide_eq ht (PolyT.const true)) (PolyT.const 1) (PolyT.const 0)
  exact h.congr fun q => by rw [tabAF, tabA_eqZ]

end TPoly

/-- **The table procedure has polynomial-time steps.** -/
theorem arithTp_poly : Nonempty (IsPolyT arithTp) := ⟨IsPolyT.ofFun tabAF_polyT⟩

theorem layAF_polyT : PolyT layAF := PolyT.fst PolyT.id'
theorem parAF_polyT : PolyT parAF := PolyT.const false

/-- **The procedures of the arithmetic network keep the resources** (unary numbers, PolyT steps). -/
theorem arithNp_keeps : arithNp.Keeps := labelProcsW_keeps layAF_polyT parAF_polyT arithTp_poly

theorem arithNp_P : Unary arithNp.P := labelProcsW_P layAF_polyT
theorem arithNp_B : Unary arithNp.B := labelProcsW_B layAF_polyT

/-! ## The reader: the context in polynomial time -/

/-- The codes of the two ends of the wire `AW.mk f co` (as `aEnds`). -/
def endsZ (p : Prm) (D : Desc) (f : ℕ) (co : List ℕ) : (ℕ × List ℕ) × (ℕ × List ℕ) :=
  if f = 0 then ((0, [co.getD 1 0]), (0, [co.getD 1 0]))
  else if f = 1 then ((0, [co.getD 2 0]), (6, [co.getD 0 0, co.getD 2 0]))
  else if f = 2 then ((0, [co.getD 2 0]), (1, [co.getD 0 0, co.getD 1 0, co.getD 2 0 / p.l1]))
  else if f = 3 then ((1, [co.getD 0 0, co.getD 1 0, co.getD 3 0]), (2, [co.getD 0 0, co.getD 1 0, co.getD 2 0]))
  else if f = 4 then ((2, [co.getD 0 0, co.getD 1 0, co.getD 2 0]), (3, [co.getD 0 0, co.getD 2 0, co.getD 3 0]))
  else if f = 5 then ((3, [co.getD 0 0, co.getD 1 0, co.getD 2 0]), (4, [co.getD 0 0, co.getD 1 0]))
  else if f = 6 then ((4, [co.getD 0 0, co.getD 1 0]), (5, [co.getD 0 0, co.getD 2 0]))
  else if f = 7 then ((5, [co.getD 0 0, co.getD 2 0]),
    if chainOfZ D (co.getD 0 0) < D.chains.length then (6, [chainOfZ D (co.getD 0 0), co.getD 1 0 + p.l1 * co.getD 2 0])
    else (5, [co.getD 0 0, co.getD 2 0]))
  else if f = 8 then ((6, [co.getD 0 0, co.getD 1 0]), (6, [co.getD 0 0, co.getD 1 0 + 1]))
  else ((0, [co.getD 1 0 + 1]), (0, [co.getD 1 0]))

theorem endsZ_eq (n : ℕ) (D : Desc) (f : ℕ) (co : List ℕ) :
    (((aEnds n D (AW.mk f co)).1.fam, (aEnds n D (AW.mk f co)).1.co),
      ((aEnds n D (AW.mk f co)).2.fam, (aEnds n D (AW.mk f co)).2.co)) = endsZ (prmOf n) D f co := by
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | _ | f
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [AW.mk, aEnds, chainOfZ_eq, Desc.nC]
    split_ifs with h <;> simp [endsZ, AV.fam, AV.co, prmOf_l1] <;>
      simp only [List.getD_eq_getElem?_getD] at h <;> omega
  · rfl
  · have : ¬ (f + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 0) := by omega
    simp only [AW.mk, aEnds, endsZ, show f + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 0 by omega,
      show f + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 1 by omega, show f + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 2 by omega,
      show f + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 3 by omega, show f + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 4 by omega,
      show f + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 5 by omega, show f + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 6 by omega,
      show f + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 7 by omega, show f + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 ≠ 8 by omega,
      if_false]
    rfl

/-- The node pair of the wire with index `k` (as `(aLo, aHi)` of `awOf n D k`). -/
def lhZ (p : Prm) (D : Desc) (g k : ℕ) : ℕ × ℕ :=
  lohi g (clusC (vDimsZ p D) g (endsZ p D (Blocks.fOf (wDimsZ p D D.nV) k) (Blocks.cOf (wDimsZ p D D.nV) k)).1.1
      (endsZ p D (Blocks.fOf (wDimsZ p D D.nV) k) (Blocks.cOf (wDimsZ p D D.nV) k)).1.2)
    (clusC (vDimsZ p D) g (endsZ p D (Blocks.fOf (wDimsZ p D D.nV) k) (Blocks.cOf (wDimsZ p D D.nV) k)).2.1
      (endsZ p D (Blocks.fOf (wDimsZ p D D.nV) k) (Blocks.cOf (wDimsZ p D D.nV) k)).2.2)

theorem lhZ_eq (n : ℕ) (D : Desc) (g k : ℕ) :
    lhZ (prmOf n) D g k = (aLo n D g (awOf n D k), aHi n D g (awOf n D k)) := by
  have e := endsZ_eq n D (Blocks.fOf (wDims n D) k) (Blocks.cOf (wDims n D) k)
  unfold lhZ aLo aHi awOf
  rw [wDimsZ_eq, vDimsZ_eq, ← e, aClus_eq, aClus_eq]

/-- `incA` with `lhZ`. -/
def incZ (p : Prm) (D : Desc) (rW : List ℕ) (g a : ℕ) : List ℕ :=
  rW.filter fun k => decide ((lhZ p D g k).1 = a ∨ (lhZ p D g k).2 = a)

theorem incA_eqZ (n : ℕ) (D : Desc) (g a : ℕ) :
    incA n D g a = incZ (prmOf n) D (List.range (numAW n D)) g a := by
  unfold incA incZ
  simp only [lhZ_eq]

/-- `pairA` with `lhZ`. -/
def pairZ (p : Prm) (D : Desc) (rW : List ℕ) (g a c : ℕ) : List ℕ :=
  (rW.filter fun k => decide (((lhZ p D g k).1 = a ∧ (lhZ p D g k).2 = c) ∨
      ((lhZ p D g k).1 = c ∧ (lhZ p D g k).2 = a))).map fun k => (incZ p D rW g a).idxOf k

theorem pairA_eqZ (n : ℕ) (D : Desc) (g a c : ℕ) :
    pairA n D g a c = pairZ (prmOf n) D (List.range (numAW n D)) g a c := by
  unfold pairA pairZ
  simp only [lhZ_eq, ← incA_eqZ]

section RPoly
variable {α : Type} [Enc α]

@[fun_prop] theorem endsZ_polyT {p : α → Prm} {D : α → Desc} {f : α → ℕ} {co : α → List ℕ} (hp : PolyT p)
    (hD : PolyT D) (hf : PolyT f) (hco : PolyT co) : PolyT fun x => endsZ (p x) (D x) (f x) (co x) := by
  have g : ∀ k : ℕ, PolyT fun x => (co x).getD k 0 := fun k => PolyT.getD hco (PolyT.const k) (PolyT.const 0)
  have e : ∀ k : ℕ, PolyT fun x => decide (f x = k) := fun k => PolyT.decide_eq hf (PolyT.const k)
  have l1 : ∀ {a : α → ℕ}, PolyT a → PolyT fun x => [a x] := fun ha => PolyT.cons' ha (PolyT.const [])
  have l2 : ∀ {a b : α → ℕ}, PolyT a → PolyT b → PolyT fun x => [a x, b x] := fun ha hb =>
    PolyT.cons' ha (PolyT.cons' hb (PolyT.const []))
  have l3 : ∀ {a b c : α → ℕ}, PolyT a → PolyT b → PolyT c → PolyT fun x => [a x, b x, c x] := fun ha hb hc =>
    PolyT.cons' ha (PolyT.cons' hb (PolyT.cons' hc (PolyT.const [])))
  have v : ∀ (k : ℕ) {l : α → List ℕ}, PolyT l → PolyT fun x => (k, l x) := fun k {_} hl => PolyT.prodMk (PolyT.const k) hl
  have hch : PolyT fun x => chainOfZ (D x) ((co x).getD 0 0) := chainOfZ_polyT hD (g 0)
  have h7 : PolyT fun x => if chainOfZ (D x) ((co x).getD 0 0) < (D x).chains.length then
      (6, [chainOfZ (D x) ((co x).getD 0 0), (co x).getD 1 0 + (p x).l1 * (co x).getD 2 0])
      else (5, [(co x).getD 0 0, (co x).getD 2 0]) :=
    PolyT.ite' (PolyT.decide_lt hch (PolyT.length (Desc.chains_polyT hD)))
      (v 6 (l2 hch (PolyT.add (g 1) (PolyT.mul (l1_polyT hp) (g 2))))) (v 5 (l2 (g 0) (g 2)))
  refine PolyT.congr ?_ fun x => (rfl : _ = endsZ (p x) (D x) (f x) (co x))
  exact PolyT.ite' (e 0) (PolyT.prodMk (v 0 (l1 (g 1))) (v 0 (l1 (g 1))))
    (PolyT.ite' (e 1) (PolyT.prodMk (v 0 (l1 (g 2))) (v 6 (l2 (g 0) (g 2))))
    (PolyT.ite' (e 2) (PolyT.prodMk (v 0 (l1 (g 2))) (v 1 (l3 (g 0) (g 1) (PolyT.div (g 2) (l1_polyT hp)))))
    (PolyT.ite' (e 3) (PolyT.prodMk (v 1 (l3 (g 0) (g 1) (g 3))) (v 2 (l3 (g 0) (g 1) (g 2))))
    (PolyT.ite' (e 4) (PolyT.prodMk (v 2 (l3 (g 0) (g 1) (g 2))) (v 3 (l3 (g 0) (g 2) (g 3))))
    (PolyT.ite' (e 5) (PolyT.prodMk (v 3 (l3 (g 0) (g 1) (g 2))) (v 4 (l2 (g 0) (g 1))))
    (PolyT.ite' (e 6) (PolyT.prodMk (v 4 (l2 (g 0) (g 1))) (v 5 (l2 (g 0) (g 2))))
    (PolyT.ite' (e 7) (PolyT.prodMk (v 5 (l2 (g 0) (g 2))) h7)
    (PolyT.ite' (e 8) (PolyT.prodMk (v 6 (l2 (g 0) (g 1))) (v 6 (l2 (g 0) (PolyT.add (g 1) (PolyT.const 1)))))
      (PolyT.prodMk (v 0 (l1 (PolyT.add (g 1) (PolyT.const 1)))) (v 0 (l1 (g 1))))))))))))

@[fun_prop] theorem lhZ_polyT {p : α → Prm} {D : α → Desc} {g k : α → ℕ} (hp : PolyT p) (hD : PolyT D)
    (hg : PolyT g) (hk : PolyT k) : PolyT fun x => lhZ (p x) (D x) (g x) (k x) := by
  have hwD := wDimsZ_polyT hp hD (Desc.nV_polyT hD)
  have he := endsZ_polyT hp hD (fOf_polyT hwD hk) (cOf_polyT hwD hk)
  have hvD := vDimsZ_polyT hp hD
  refine PolyT.congr ?_ fun x => (rfl : _ = lhZ (p x) (D x) (g x) (k x))
  exact lohi_polyT hg (clusC_polyT hvD hg (PolyT.fst (PolyT.fst he)) (PolyT.snd (PolyT.fst he)))
    (clusC_polyT hvD hg (PolyT.fst (PolyT.snd he)) (PolyT.snd (PolyT.snd he)))

@[fun_prop] theorem incZ_polyT {p : α → Prm} {D : α → Desc} {rW : α → List ℕ} {g a : α → ℕ} (hp : PolyT p)
    (hD : PolyT D) (hrW : PolyT rW) (hg : PolyT g) (ha : PolyT a) :
    PolyT fun x => incZ (p x) (D x) (rW x) (g x) (a x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hl := lhZ_polyT (PolyT.comp hp f1) (PolyT.comp hD f1) (PolyT.comp hg f1) (PolyT.snd PolyT.id')
  have haq := PolyT.comp ha f1
  refine PolyT.congr ?_ fun x => (rfl : _ = incZ (p x) (D x) (rW x) (g x) (a x))
  exact PolyT.filter (f := fun x k => decide ((lhZ (p x) (D x) (g x) k).1 = a x ∨ (lhZ (p x) (D x) (g x) k).2 = a x))
    (PolyT.decide_or (PolyT.decide_eq (PolyT.fst hl) haq) (PolyT.decide_eq (PolyT.snd hl) haq)) hrW

@[fun_prop] theorem pairZ_polyT {p : α → Prm} {D : α → Desc} {rW : α → List ℕ} {g a c : α → ℕ} (hp : PolyT p)
    (hD : PolyT D) (hrW : PolyT rW) (hg : PolyT g) (ha : PolyT a) (hc : PolyT c) :
    PolyT fun x => pairZ (p x) (D x) (rW x) (g x) (a x) (c x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hl := lhZ_polyT (PolyT.comp hp f1) (PolyT.comp hD f1) (PolyT.comp hg f1) (PolyT.snd PolyT.id')
  have haq := PolyT.comp ha f1
  have hcq := PolyT.comp hc f1
  have hfil : PolyT fun x => (rW x).filter fun k => decide (((lhZ (p x) (D x) (g x) k).1 = a x ∧
      (lhZ (p x) (D x) (g x) k).2 = c x) ∨ ((lhZ (p x) (D x) (g x) k).1 = c x ∧ (lhZ (p x) (D x) (g x) k).2 = a x)) :=
    PolyT.filter (f := fun x k => decide (((lhZ (p x) (D x) (g x) k).1 = a x ∧ (lhZ (p x) (D x) (g x) k).2 = c x) ∨
        ((lhZ (p x) (D x) (g x) k).1 = c x ∧ (lhZ (p x) (D x) (g x) k).2 = a x)))
      (PolyT.decide_or (PolyT.decide_and (PolyT.decide_eq (PolyT.fst hl) haq) (PolyT.decide_eq (PolyT.snd hl) hcq))
        (PolyT.decide_and (PolyT.decide_eq (PolyT.fst hl) hcq) (PolyT.decide_eq (PolyT.snd hl) haq))) hrW
  have hinc : PolyT fun q : α × ℕ => incZ (p q.1) (D q.1) (rW q.1) (g q.1) (a q.1) :=
    incZ_polyT (PolyT.comp hp f1) (PolyT.comp hD f1) (PolyT.comp hrW f1) (PolyT.comp hg f1) haq
  refine PolyT.congr ?_ fun x => (rfl : _ = pairZ (p x) (D x) (rW x) (g x) (a x) (c x))
  exact PolyT.map (f := fun x k => (incZ (p x) (D x) (rW x) (g x) (a x)).idxOf k)
    (PolyT.idxOf (PolyT.snd PolyT.id') hinc) hfil

end RPoly

/-! ### Sizes of the layouts in unary -/

theorem numAV_eq (n : ℕ) (D : Desc) : numAV n D = ℓ n + D.prods.length * (2 * ℓ1 n) +
    D.prods.length * (2 * L1 n) + D.prods.length * (L1 n * L1 n) + D.prods.length * L1 n +
    D.prods.length * L1 n + D.chains.length * Kc n := by
  simp [numAV, Blocks.total, Blocks.sizes, vDims, ℓ2_eq_ℓ1, L2_eq_L1]
  ring

theorem numAW_eq (n : ℕ) (D : Desc) : numAW n D = D.nV * ℓ n + D.chains.length * (D.nV * ℓ n) +
    D.prods.length * (2 * ℓ n) + D.prods.length * (2 * (L1 n * ℓ1 n)) + D.prods.length * (2 * (L1 n * L1 n)) +
    D.prods.length * (L1 n * L1 n) + D.prods.length * (L1 n * L1 n) + D.prods.length * (L1 n * L1 n) +
    D.chains.length * (Kc n - 1) + D.cmps.length * (ℓ n - 1) := by
  simp [numAW, Blocks.total, Blocks.sizes, wDims, ℓ2_eq_ℓ1, L2_eq_L1]
  ring

section Unary
variable {α : Type} [Enc α] {n : α → ℕ} {D : α → Desc} (hn : Unary n) (hD : PolyT D)
include hn hD

theorem Kc_unary : Unary fun x => Kc (n x) := by
  unfold Kc; rw [show (fun x => L1 (n x) + ℓ1 (n x) * L2 (n x)) = fun x => L1 (n x) + ℓ1 (n x) * L1 (n x) from
    funext fun x => by rw [L2_eq_L1]]
  exact Unary.add (L1_unary hn) (Unary.mul (ℓ1_unary hn) (L1_unary hn))

theorem numAV_unary : Unary fun x => numAV (n x) (D x) := by
  have hP := Unary.of_length (Desc.prods_polyT hD)
  have hC := Unary.of_length (Desc.chains_polyT hD)
  have hl := ℓ_unary hn
  have hl1 := ℓ1_unary hn
  have hL := L1_unary hn
  have hK := Kc_unary hn hD
  have h2 := Unary.const (α := α) 2
  have h := ((((((hl.add (hP.mul (h2.mul hl1))).add (hP.mul (h2.mul hL))).add (hP.mul (hL.mul hL))).add
    (hP.mul hL)).add (hP.mul hL)).add (hC.mul hK))
  exact PolyT.congr h fun x => by dsimp only; rw [numAV_eq]

theorem numAW_unary (hV : Unary fun x => (D x).nV) : Unary fun x => numAW (n x) (D x) := by
  have hP := Unary.of_length (Desc.prods_polyT hD)
  have hC := Unary.of_length (Desc.chains_polyT hD)
  have hQ := Unary.of_length (Desc.cmps_polyT hD)
  have hl := ℓ_unary hn
  have hl1 := ℓ1_unary hn
  have hL := L1_unary hn
  have hK := Kc_unary hn hD
  have hK1 : Unary fun x => Kc (n x) - 1 := Unary.of_le hK (PolyT.sub hK.poly (PolyT.const 1)) fun _ => Nat.sub_le _ _
  have hl' : Unary fun x => ℓ (n x) - 1 := Unary.of_le hl (PolyT.sub hl.poly (PolyT.const 1)) fun _ => Nat.sub_le _ _
  have h2 := Unary.const (α := α) 2
  have h := (((((((((hV.mul hl).add (hC.mul (hV.mul hl))).add (hP.mul (h2.mul hl))).add
    (hP.mul (h2.mul (hL.mul hl1)))).add (hP.mul (h2.mul (hL.mul hL)))).add (hP.mul (hL.mul hL))).add
    (hP.mul (hL.mul hL))).add (hP.mul (hL.mul hL))).add (hC.mul hK1)).add (hQ.mul hl')
  exact PolyT.congr h fun x => by dsimp only; rw [numAW_eq]

end Unary

/-! ### The layout and the context -/

/-- `layA` with `incZ`, `pairZ`. -/
def layZ (p : Prm) (D : Desc) (rW : List ℕ) (g P W : ℕ) : Lay :=
  (((List.replicate P (), [()]), (List.replicate W (), [])),
    ((List.range g).map fun a => ((incZ p D rW g a).map fun _ => (), []),
      (List.range g).map fun a => (List.range g).map fun c => (pairZ p D rW g a c, [])))

theorem layA_eqZ (n : ℕ) (D : Desc) (g P : ℕ) :
    layA n D g P = layZ (prmOf n) D (List.range (numAW n D)) g P (Wa n) := by
  unfold layA layZ
  simp only [incA_eqZ, pairA_eqZ]

section CPoly
variable {α : Type} [Enc α]

theorem layZ_polyT {p : α → Prm} {D : α → Desc} {rW : α → List ℕ} {g P W : α → ℕ} (hp : PolyT p) (hD : PolyT D)
    (hrW : PolyT rW) (hg : Unary g) (hP : Unary P) (hW : Unary W) :
    PolyT fun x => layZ (p x) (D x) (rW x) (g x) (P x) (W x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have f2 : PolyT fun q : (α × ℕ) × ℕ => q.1.1 := PolyT.fst (PolyT.fst PolyT.id')
  have hr : PolyT fun x => List.range (g x) := PolyT.range hg
  have hP' : PolyT fun x => List.replicate (P x) () := hP
  have hW' : PolyT fun x => List.replicate (W x) () := hW
  have hinc : PolyT fun q : α × ℕ => ((incZ (p q.1) (D q.1) (rW q.1) (g q.1) q.2).map fun _ => (), ([] : List Unit)) :=
    PolyT.prodMk (PolyT.map (f := fun _ _ => ()) (PolyT.const ())
      (incZ_polyT (PolyT.comp hp f1) (PolyT.comp hD f1) (PolyT.comp hrW f1) (PolyT.comp hg.poly f1)
        (PolyT.snd PolyT.id'))) (PolyT.const [])
  have hpair : PolyT fun q : (α × ℕ) × ℕ => (pairZ (p q.1.1) (D q.1.1) (rW q.1.1) (g q.1.1) q.1.2 q.2,
      ([] : List (Bool × ℕ))) :=
    PolyT.prodMk (pairZ_polyT (PolyT.comp hp f2) (PolyT.comp hD f2) (PolyT.comp hrW f2) (PolyT.comp hg.poly f2)
      (PolyT.snd (PolyT.fst PolyT.id')) (PolyT.snd PolyT.id')) (PolyT.const [])
  have hrow : PolyT fun q : α × ℕ => (List.range (g q.1)).map fun c =>
      (pairZ (p q.1) (D q.1) (rW q.1) (g q.1) q.2 c, ([] : List (Bool × ℕ))) :=
    PolyT.map (f := fun (q : α × ℕ) c => (pairZ (p q.1) (D q.1) (rW q.1) (g q.1) q.2 c, ([] : List (Bool × ℕ))))
      hpair (PolyT.comp (f := fun x => List.range (g x)) hr f1)
  refine PolyT.congr ?_ fun x => (rfl : _ = layZ (p x) (D x) (rW x) (g x) (P x) (W x))
  exact PolyT.prodMk (PolyT.prodMk (PolyT.prodMk hP' (PolyT.const _)) (PolyT.prodMk hW' (PolyT.const _)))
    (PolyT.prodMk (PolyT.map (f := fun x a => ((incZ (p x) (D x) (rW x) (g x) a).map fun _ => (), ([] : List Unit)))
      hinc hr)
      (PolyT.map (f := fun x a => (List.range (g x)).map fun c => (pairZ (p x) (D x) (rW x) (g x) a c,
        ([] : List (Bool × ℕ)))) hrow hr))

theorem Wa_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => Wa (n x) := by
  have h : Unary fun x => J (n x) + 8 := (J_unary hn).add (Unary.const 8)
  exact h

/-- **The context is computed in polynomial time** (`n`, `g`, `P` and the number of variables in
unary, the description in polynomial time). -/
theorem aCtxOf_polyT {n g P : α → ℕ} {D : α → Desc} (hn : Unary n) (hD : PolyT D)
    (hV : Unary fun x => (D x).nV) (hg : Unary g) (hP : Unary P) :
    PolyT fun x => aCtxOf (n x) (D x) (g x) (P x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hp : PolyT fun x => prmOf (n x) := prmOf_polyT hn
  have hrW : PolyT fun x => List.range (numAW (n x) (D x)) := PolyT.range (numAW_unary hn hD hV)
  have hrV : PolyT fun x => List.range (numAV (n x) (D x)) := PolyT.range (numAV_unary hn hD)
  have hlay := layZ_polyT hp hD hrW hg hP (Wa_unary hn)
  have hn' : PolyT fun x => List.replicate (n x) () := hn
  have hV' : PolyT fun x => List.replicate (D x).nV () := hV
  have hinc : PolyT fun x => (List.range (g x)).map fun a =>
      incZ (prmOf (n x)) (D x) (List.range (numAW (n x) (D x))) (g x) a :=
    PolyT.map (f := fun x a => incZ (prmOf (n x)) (D x) (List.range (numAW (n x) (D x))) (g x) a)
      (incZ_polyT (PolyT.comp (f := fun x => prmOf (n x)) hp f1) (PolyT.comp hD f1)
        (PolyT.comp (f := fun x => List.range (numAW (n x) (D x))) hrW f1) (PolyT.comp hg.poly f1)
        (PolyT.snd PolyT.id')) (PolyT.range hg)
  have h : PolyT fun x => (layZ (prmOf (n x)) (D x) (List.range (numAW (n x) (D x))) (g x) (P x) (Wa (n x)),
      ((List.replicate (n x) (), (D x, List.replicate (D x).nV ())),
        ((g x, List.range (numAV (n x) (D x))), (List.range (g x)).map fun a =>
          incZ (prmOf (n x)) (D x) (List.range (numAW (n x) (D x))) (g x) a))) :=
    PolyT.prodMk hlay (PolyT.prodMk (PolyT.prodMk hn' (PolyT.prodMk hD hV'))
      (PolyT.prodMk (PolyT.prodMk hg.poly hrV) hinc))
  exact h.congr fun x => by
    have e : incA (n x) (D x) (g x) = fun a => incZ (prmOf (n x)) (D x) (List.range (numAW (n x) (D x))) (g x) a :=
      funext fun a => incA_eqZ _ _ _ _
    unfold aCtxOf
    rw [layA_eqZ, e]

end CPoly


end EthFollowup.ModP
