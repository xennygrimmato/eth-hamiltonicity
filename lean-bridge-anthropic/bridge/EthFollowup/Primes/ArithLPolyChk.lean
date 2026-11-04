/-
# ArithL, module 4b (part 1): the pieces of the leveled table in polynomial time

Template: `ModP/ArithPoly.lean` (its generic `Blocks` lemmas, `rdw`, `testZ`, `chainOfZ` are reused by
import). PolyT of
* the codes of leveled descriptions (`LDesc.mk_polyT`, `LDesc.D_polyT`, `lev`, `levC`) and the
  levels `lv`, `lc`, `lp`, `lq`, `nL`;
* the shapes at a level (`kl1_unary`, `kL1_unary`, `kl_unary`, `kKc_unary`) and the parameter tuple
  **`kP_polyT`** (as `MulPackage.prmOf_polyT`);
* the boxes and layouts `wBox`, `vBox`, `wLay`, `vLay` (`vLay` with the number of levels in unary);
* the checks on codes (`opLimbRZ`, `opLimbCZ`, `cmpOKLZ`, `cellLZ`, …, `chkLZ`) with **`aChk_eqZ`**
  (the check of `AVL.mk κ o co` is `chkLZ κ o co`) and **`chkLZ_polyT`**.

Standard axioms only.
-/
import EthFollowup.Primes.ArithLProcs
import EthFollowup.ModP.ArithPoly

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Groundwork Groundwork.Prog EthFollowup.ExactHC EthFollowup.Factoring EthFollowup.ModP
open EthFollowup.Factoring.MP EthFollowup.Factoring.MPoly

/-! ## Codes of leveled descriptions and the levels -/

section Acc
variable {α : Type} [Enc α]

theorem LDesc.polyT_toT {f : α → LDesc} (hf : PolyT f) : PolyT fun x => (f x).toT :=
  PolyT.of_wd hf id (fun _ => rfl) fun _ => rfl

@[fun_prop] theorem LDesc.mk_polyT {D : α → Desc} {lev levC : α → List ℕ} (hD : PolyT D) (h1 : PolyT lev)
    (h2 : PolyT levC) : PolyT fun x => LDesc.mk (D x) (lev x) (levC x) :=
  polyT_into LDesc.toT (fun _ => rfl) (PolyT.prodMk hD (PolyT.prodMk h1 h2))

variable {L : α → LDesc} (hL : PolyT L)
include hL

@[fun_prop] theorem LDesc.D_polyT : PolyT fun x => (L x).D :=
  (PolyT.fst (LDesc.polyT_toT hL)).congr fun _ => rfl
@[fun_prop] theorem LDesc.lev_polyT : PolyT fun x => (L x).lev :=
  (PolyT.fst (PolyT.snd (LDesc.polyT_toT hL))).congr fun _ => rfl
@[fun_prop] theorem LDesc.levC_polyT : PolyT fun x => (L x).levC :=
  (PolyT.snd (PolyT.snd (LDesc.polyT_toT hL))).congr fun _ => rfl

@[fun_prop] theorem LDesc.lv_polyT {v : α → ℕ} (hv : PolyT v) : PolyT fun x => (L x).lv (v x) :=
  PolyT.getD (LDesc.lev_polyT hL) hv (PolyT.const 0)
@[fun_prop] theorem LDesc.lc_polyT {c : α → ℕ} (hc : PolyT c) : PolyT fun x => (L x).lc (c x) :=
  PolyT.getD (LDesc.levC_polyT hL) hc (PolyT.const 0)
@[fun_prop] theorem LDesc.lp_polyT {p : α → ℕ} (hp : PolyT p) : PolyT fun x => (L x).lp (p x) :=
  (LDesc.lc_polyT hL (chainOfZ_polyT (LDesc.D_polyT hL) hp)).congr fun x => by
    unfold LDesc.lp; rw [chainOfZ_eq]
@[fun_prop] theorem LDesc.lq_polyT {q : α → ℕ} (hq : PolyT q) : PolyT fun x => (L x).lq (q x) :=
  LDesc.lv_polyT hL (CmpD.v_polyT (getD_cmps_polyT (LDesc.D_polyT hL) hq))
@[fun_prop] theorem LDesc.nL_polyT : PolyT fun x => (L x).nL :=
  (PolyT.add (PolyT.max' (NetE.foldr_max_polyT (LDesc.lev_polyT hL)) (NetE.foldr_max_polyT (LDesc.levC_polyT hL)))
    (PolyT.const 1)).congr fun _ => rfl

end Acc

/-! ## The shapes and the parameters of a level -/

section Par
variable {α : Type} [Enc α] {n k : α → ℕ} (hn : Unary n) (hk : PolyT k)
include hn hk

theorem sh_polyT : PolyT fun x => sh (n x) (k x) :=
  PolyT.min' (PolyT.div hk (PolyT.const 2)) (PolyT.sub (m_unary hn).poly (PolyT.const 1))

theorem kl1_unary : Unary fun x => kl1 (n x) (k x) :=
  Unary.of_le (ℓ1_unary hn) (PolyT.two_pow (Unary.of_le (m_unary hn)
    (PolyT.sub (PolyT.sub (m_unary hn).poly (sh_polyT hn hk)) (PolyT.const 1)) fun _ => by omega))
    fun x => kl1_le _ _

theorem kL1_unary : Unary fun x => kL1 (n x) (k x) :=
  Unary.of_le (L1_unary hn) (PolyT.two_pow (Unary.of_le (m_unary hn)
    (PolyT.sub (m_unary hn).poly (sh_polyT hn hk)) fun _ => by omega)) fun x => kL1_le _ _

theorem kl_unary : Unary fun x => kl (n x) (k x) := Unary.mul (kl1_unary hn hk) (kl1_unary hn hk)

theorem kKc_unary : Unary fun x => kKc (n x) (k x) :=
  Unary.add (kL1_unary hn hk) (Unary.mul (kl1_unary hn hk) (kL1_unary hn hk))

theorem kiL_polyT : PolyT fun x => kiL (n x) (k x) :=
  PolyT.two_pow (Unary.of_le (Unary.mul (Unary.const 2) (J_unary hn))
    (PolyT.sub (PolyT.mul (PolyT.const 2) (J_unary hn).poly) (PolyT.sub (m_unary hn).poly (sh_polyT hn hk)))
    fun _ => Nat.sub_le _ _)

omit hn hk in
theorem wTabK_eq (n k : ℕ) : wTabK n k = (List.range (kL1 n k)).map fun e => 2 ^ (2 * J n / kL1 n k * (e % kL1 n k)) :=
  List.map_congr_left fun e he => by rw [Nat.mod_eq_of_lt (List.mem_range.1 he)]

theorem wTabK_polyT : PolyT fun x => wTabK (n x) (k x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hJ := (J_unary hn).comp f1
  have hL := (kL1_unary hn hk).comp f1
  have hE : Unary fun q : α × ℕ => 2 * J (n q.1) / kL1 (n q.1) (k q.1) * (q.2 % kL1 (n q.1) (k q.1)) :=
    Unary.of_le (Unary.mul (Unary.const 2) hJ)
      (PolyT.mul (PolyT.div (PolyT.mul (PolyT.const 2) hJ.poly) hL.poly) (PolyT.mod (PolyT.snd PolyT.id') hL.poly))
      fun q => by
        have h2 := two_le_kL1 (n q.1) (k q.1)
        have h3 := Nat.mod_lt q.2 (show 0 < kL1 (n q.1) (k q.1) by omega)
        calc 2 * J (n q.1) / kL1 (n q.1) (k q.1) * (q.2 % kL1 (n q.1) (k q.1))
            ≤ 2 * J (n q.1) / kL1 (n q.1) (k q.1) * kL1 (n q.1) (k q.1) := Nat.mul_le_mul_left _ h3.le
          _ ≤ 2 * J (n q.1) := Nat.div_mul_le_self _ _
  exact (PolyT.map (f := fun x e => 2 ^ (2 * J (n x) / kL1 (n x) (k x) * (e % kL1 (n x) (k x))))
    (PolyT.two_pow hE) (PolyT.range (kL1_unary hn hk))).congr fun x => (wTabK_eq _ _).symm

/-- **The parameters of a level, in polynomial time** (`n` in unary, the level in binary). -/
theorem kP_polyT : PolyT fun x => kP (n x) (k x) := by
  have hl1 := kl1_unary hn hk
  have hL1 := kL1_unary hn hk
  have hb := b_unary hn
  have hJ := J_unary hn
  have hW : PolyT fun x => List.replicate (Wa (n x)) () := Wa_unary hn
  have hM : PolyT fun x => M (n x) := PolyT.add (PolyT.two_pow hJ) (PolyT.const 1)
  have hpb : PolyT fun x => 2 ^ b (n x) := PolyT.two_pow hb
  have r1 : PolyT fun x => List.range (kl1 (n x) (k x)) := PolyT.range hl1
  have r2 : PolyT fun x => List.range (kL1 (n x) (k x)) := PolyT.range hL1
  have r3 : PolyT fun x => List.range (b (n x)) := PolyT.range hb
  unfold kP
  exact PolyT.prodMk (PolyT.prodMk (PolyT.prodMk hl1.poly hl1.poly) (PolyT.prodMk hL1.poly hL1.poly))
    (PolyT.prodMk (PolyT.prodMk (PolyT.prodMk hb.poly hpb) (PolyT.prodMk hM (kiL_polyT hn hk)))
      (PolyT.prodMk (PolyT.prodMk hW (wTabK_polyT hn hk))
        (PolyT.prodMk (PolyT.prodMk (PolyT.prodMk r1 r1) (PolyT.prodMk r2 r2))
          (PolyT.prodMk r3 (PolyT.prodMk (PolyT.const []) (PolyT.const []))))))

end Par

/-! ## Boxes and layouts -/

section Lay
variable (n : ℕ) (L : LDesc)

theorem wLay_eq : wLay n L =
    ((List.range L.D.nV).map fun o => [kl n (L.lv o)]) ++ (((List.range L.D.nP).map fun o => [2, kl n (L.lp o)]) ++
    (((List.range L.D.nP).map fun o => [2, kL1 n (L.lp o), kl1 n (L.lp o)]) ++
    (((List.range L.D.nP).map fun o => [2, kL1 n (L.lp o), kL1 n (L.lp o)]) ++
    (((List.range L.D.nP).map fun o => [kL1 n (L.lp o), kL1 n (L.lp o)]) ++
    (((List.range L.D.nP).map fun o => [kL1 n (L.lp o), kL1 n (L.lp o)]) ++
    (((List.range L.D.nP).map fun o => [kL1 n (L.lp o), kL1 n (L.lp o)]) ++
    (((List.range L.D.nC).map fun o => [kKc n (L.lc o) - 1]) ++
    (((List.range L.D.nQ).map fun o => [kl n (L.lq o) - 1]) ++ [])))))))) := rfl

theorem vLay_eq : vLay n L =
    ((List.range L.nL).map fun o => [kl n o]) ++ (((List.range L.D.nP).map fun o => [2, kl1 n (L.lp o)]) ++
    (((List.range L.D.nP).map fun o => [2, kL1 n (L.lp o)]) ++
    (((List.range L.D.nP).map fun o => [kL1 n (L.lp o), kL1 n (L.lp o)]) ++
    (((List.range L.D.nP).map fun o => [kL1 n (L.lp o)]) ++
    (((List.range L.D.nP).map fun o => [kL1 n (L.lp o)]) ++
    (((List.range L.D.nC).map fun o => [kKc n (L.lc o)]) ++ [])))))) := rfl

/-- `vBox` as a case distinction. -/
def vBoxZ (κ o : ℕ) : List ℕ :=
  if κ = 0 then [kl n o] else if κ = 1 then [2, kl1 n (L.lp o)] else if κ = 2 then [2, kL1 n (L.lp o)]
  else if κ = 3 then [kL1 n (L.lp o), kL1 n (L.lp o)] else if κ ≤ 5 then [kL1 n (L.lp o)] else [kKc n (L.lc o)]

theorem vBox_eqZ (κ o : ℕ) : vBox n L κ o = vBoxZ n L κ o := by
  rcases κ with _ | _ | _ | _ | _ | _ | κ <;> simp [vBox, vBoxZ]

/-- The cluster of the vertex of kind `κ`, object `o`, coordinates `co` (as `aClus`). -/
def clusLZ (g κ o : ℕ) (co : List ℕ) : ℕ :=
  VB.vbN ((Blocks.sizes (vLay n L)).getD (LB.fidx (vObj L) κ o) 0) g (Blocks.enc (vBoxZ n L κ o) co)

theorem aClus_eqZ (g : ℕ) (v : AVL) : aClus n L g v = clusLZ n L g v.kind v.obj v.co := by
  unfold aClus stSz AVL.stage AVL.idx clusLZ; rw [vBox_eqZ]

/-- The coordinates of `AVL.mk κ o xs`. -/
def coVL (κ : ℕ) (xs : List ℕ) : List ℕ :=
  if κ = 0 then [xs.getD 0 0] else if κ ≤ 3 then [xs.getD 0 0, xs.getD 1 0] else [xs.getD 0 0]

theorem avmkL_kind (κ o : ℕ) (xs : List ℕ) : (AVL.mk κ o xs).kind = min κ 6 := by
  rcases κ with _ | _ | _ | _ | _ | _ | κ <;> simp [AVL.mk, AVL.kind]
theorem avmkL_obj (κ o : ℕ) (xs : List ℕ) : (AVL.mk κ o xs).obj = o := by
  rcases κ with _ | _ | _ | _ | _ | _ | κ <;> rfl
theorem avmkL_co (κ o : ℕ) (xs : List ℕ) : (AVL.mk κ o xs).co = coVL κ xs := by
  rcases κ with _ | _ | _ | _ | _ | _ | κ <;> simp [AVL.mk, AVL.co, coVL]

end Lay

/-! ## The checks on codes -/

/-- The value of wire `(κ, o, co)` read from the setting (reader `r = (W, inc, z, wLay)`). -/
def rdx (L : LDesc) (r : Rd) (κ o : ℕ) (co : List ℕ) : ℕ := rdw r (LB.fidx (wObj L) κ o) co

section Chk
variable (n : ℕ) (L : LDesc) (r : Rd)

/-- The level of the cell checking the copy `R p σ i` (`cellR = .cell (cellRk …) i`). -/
def cellRk (p σ i : ℕ) : ℕ :=
  (opnd L.D p σ).toE.elim (fun w => if w < L.D.nV ∧ i < kl n (L.lv w) then L.lv w else L.lp p) (fun _ => L.lp p)

/-- `opLimbR` on codes. -/
def opLimbRZ (p σ i : ℕ) : ℕ :=
  (opnd L.D p σ).toE.elim (fun w => if w < L.D.nV ∧ i < kl n (L.lv w) then rdx L r 0 w [i] else 0)
    (fun l => l.getD i 0)

/-- `opLimbC` on codes. -/
def opLimbCZ (k : ℕ) (o : Operand) (i : ℕ) : ℕ :=
  o.toE.elim (fun w => if w < L.D.nV ∧ L.lv w = k then rdx L r 0 w [i] else 0) (fun l => l.getD i 0)

/-- `cmpOK` on codes. -/
def cmpOKLZ (q i : ℕ) : Bool :=
  if i = 0 then testZ (L.D.cq q).rel.toE (cmpStep (if i + 1 = kl n (L.lq q) then 1 else rdx L r 8 q [i])
      (opLimbCZ L r (L.lq q) (.var (L.D.cq q).v) i) (opLimbCZ L r (L.lq q) (L.D.cq q).rhs i))
  else rdx L r 8 q [i - 1] == cmpStep (if i + 1 = kl n (L.lq q) then 1 else rdx L r 8 q [i])
      (opLimbCZ L r (L.lq q) (.var (L.D.cq q).v) i) (opLimbCZ L r (L.lq q) (L.D.cq q).rhs i)

/-- `cellOK` on codes. -/
def cellLZ (k i : ℕ) : Bool :=
  ((List.range L.D.nV).all fun v => !(decide (L.lv v = k)) ||
    (decide (rdx L r 0 v [i] < 2 ^ b n) && patOK n (L.D.pat.getD v []) i (rdx L r 0 v [i]))) &&
  ((List.range L.D.nP).all fun p => (List.range 2).all fun σ =>
    !(decide (i < kl n (L.lp p) ∧ cellRk n L p σ i = k)) || rdx L r 1 p [σ, i] == opLimbRZ n L r p σ i) &&
  ((List.range L.D.nQ).all fun q => !(decide (L.lq q = k)) || cmpOKLZ n L r q i)

end Chk

section ChkG
variable (P : Prm) (L : LDesc) (r : Rd)

def rowG (p σ i2 : ℕ) : Bool := P.rL1.all fun s =>
  rdx L r 2 p [σ, s, i2] == rowE P (fun i1 i2 => rdx L r 1 p [σ, i1 + P.l1 * i2]) s i2
def colG (p σ s : ℕ) : Bool := P.rL2.all fun t =>
  rdx L r 3 p [σ, s, t] == colE P (fun s i2 => rdx L r 2 p [σ, s, i2]) s t
def mulG (p s t : ℕ) : Bool := rdx L r 4 p [s, t] == rdx L r 3 p [0, s, t] * rdx L r 3 p [1, s, t] % P.M
def icolG (p s : ℕ) : Bool := P.rL2.all fun u =>
  rdx L r 5 p [s, u] == invColE P (fun s t => rdx L r 4 p [s, t]) s u
def irowG (p u : ℕ) : Bool := P.rL1.all fun a =>
  rdx L r 6 p [a, u] == invRowE P (fun s u => rdx L r 5 p [s, u]) a u

def tDigG (c : ℕ) (t : Term) (k : ℕ) : ℕ :=
  t.src.toE.elim
    (fun pp => if pp < L.D.nP ∧ chainOfZ L.D pp = c then convE P (fun a u => rdx L r 6 pp [a, u]) k else 0)
    (fun e => e.elim (fun _ => 0) (fun l => l.getD k 0))

def sDigG (c : ℕ) (ts : List Term) (k : ℕ) : ℕ := (ts.map fun t => t.coeff * tDigG P L r c t k).sum

def carryG (K OFF c k : ℕ) : Bool :=
  decide ((if k + 1 < K then rdx L r 7 c [k] else OFF) * P.pb + sDigG P L r c (L.D.ch c).rhs k + OFF =
    sDigG P L r c (L.D.ch c).lhs k + (if k = 0 then OFF else rdx L r 7 c [k - 1]) + OFF * P.pb)

end ChkG

/-- **The check of the vertex of kind `κ`, object `o`, coordinates `co`** (dispatch as `AVL.mk`). -/
def chkLZ (n : ℕ) (L : LDesc) (r : Rd) (κ o : ℕ) (co : List ℕ) : Bool :=
  if κ = 0 then cellLZ n L r o (co.getD 0 0)
  else if κ = 1 then rowG (kP n (L.lp o)) L r o (co.getD 0 0) (co.getD 1 0)
  else if κ = 2 then colG (kP n (L.lp o)) L r o (co.getD 0 0) (co.getD 1 0)
  else if κ = 3 then mulG (kP n (L.lp o)) L r o (co.getD 0 0) (co.getD 1 0)
  else if κ = 4 then icolG (kP n (L.lp o)) L r o (co.getD 0 0)
  else if κ = 5 then irowG (kP n (L.lp o)) L r o (co.getD 0 0)
  else carryG (kP n (L.lc o)) L r (kKc n (L.lc o)) (aOFF n) o (co.getD 0 0)

/-! ### The equations -/

section Eqs
variable (n : ℕ) (L : LDesc) (W : ℕ) (inc : List ℕ) (z : List Bool)

/-- The wire values of the table. -/
abbrev xL (d : AWL) : ℕ := xz W inc z (awIdx n L d)

theorem xL_eq (d : AWL) : xL n L W inc z d = rdx L (W, inc, z, wLay n L) d.kind d.obj d.co := rfl

theorem cellR_eqk (p σ i : ℕ) : cellR n L p σ i = .cell (cellRk n L p σ i) i := by
  unfold cellR cellRk
  cases opnd L.D p σ with
  | var w => simp only [Operand.toE, Sum.elim_inl]; split_ifs <;> rfl
  | const l => rfl

theorem opLimbR_eqZ (p σ i : ℕ) :
    opLimbR n L (xL n L W inc z) p σ i = opLimbRZ n L (W, inc, z, wLay n L) p σ i := by
  unfold opLimbR opLimbRZ
  cases opnd L.D p σ <;> rfl

theorem opLimbC_eqZ (k : ℕ) (o : Operand) (i : ℕ) :
    opLimbC L (xL n L W inc z) k o i = opLimbCZ L (W, inc, z, wLay n L) k o i := by
  cases o <;> rfl

theorem cmpOK_eqZ (q i : ℕ) : cmpOK n L (xL n L W inc z) q i = cmpOKLZ n L (W, inc, z, wLay n L) q i := by
  unfold cmpOK cmpCell cmpOKLZ
  simp only [test_eq, opLimbC_eqZ]
  rfl

theorem cellOK_eqZ (k i : ℕ) : cellOK n L (xL n L W inc z) k i = cellLZ n L (W, inc, z, wLay n L) k i := by
  unfold cellOK cellLZ
  simp only [cmpOK_eqZ, opLimbR_eqZ, cellR_eqk, AVL.cell.injEq, and_true]
  rfl

theorem tDig_eqZ (c : ℕ) (t : Term) (k : ℕ) :
    tDig n L (xL n L W inc z) c t k = tDigG (kP n (L.lc c)) L (W, inc, z, wLay n L) c t k := by
  unfold tDig tDigG
  rcases h : t.src with pp | v | l
  · simp only [Src.toE, Sum.elim_inl, chainOfZ_eq]; rfl
  · rfl
  · rfl

theorem sDig_eqZ (c : ℕ) (ts : List Term) (k : ℕ) :
    sDig n L (xL n L W inc z) c ts k = sDigG (kP n (L.lc c)) L (W, inc, z, wLay n L) c ts k := by
  unfold sDig sDigG; simp only [tDig_eqZ]

/-- **The checks on codes**: the check of `AVL.mk κ o co` is `chkLZ κ o co`. -/
theorem aChk_eqZ (κ o : ℕ) (co : List ℕ) :
    aChk n L (xL n L W inc z) (AVL.mk κ o co) = chkLZ n L (W, inc, z, wLay n L) κ o co := by
  rcases κ with _ | _ | _ | _ | _ | _ | κ
  · exact cellOK_eqZ n L W inc z _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have h0 : κ + 1 + 1 + 1 + 1 + 1 + 1 ≠ 0 := by omega
    have h1 : κ + 1 + 1 + 1 + 1 + 1 + 1 ≠ 1 := by omega
    have h2 : κ + 1 + 1 + 1 + 1 + 1 + 1 ≠ 2 := by omega
    have h3 : κ + 1 + 1 + 1 + 1 + 1 + 1 ≠ 3 := by omega
    have h4 : κ + 1 + 1 + 1 + 1 + 1 + 1 ≠ 4 := by omega
    have h5 : κ + 1 + 1 + 1 + 1 + 1 + 1 ≠ 5 := by omega
    simp only [AVL.mk, aChk, chkLZ, h0, h1, h2, h3, h4, h5, if_false, carryG, carryChk, sDig_eqZ, kP_pb, Desc.ch]
    rfl

end Eqs

/-! ## Polynomial time of the layouts and the checks -/

/-- The hypotheses of the PolyT lemmas: `n` and the number of variables in unary, the description
and the wire reader in polynomial time. -/
structure LH {α : Type} [Enc α] (n : α → ℕ) (L : α → LDesc) (r : α → Rd) : Prop where
  un : Unary n
  pL : PolyT L
  uV : Unary fun x => (L x).D.nV
  pr : PolyT r

theorem LH.comp {α β : Type} [Enc α] [Enc β] {n : α → ℕ} {L : α → LDesc} {r : α → Rd} (h : LH n L r)
    {f : β → α} (hf : PolyT f) : LH (fun y => n (f y)) (fun y => L (f y)) (fun y => r (f y)) :=
  ⟨h.un.comp hf, h.pL.comp hf, h.uV.comp hf, h.pr.comp hf⟩

section LPoly
variable {α : Type} [Enc α]

theorem nP_unary {L : α → LDesc} (hL : PolyT L) : Unary fun x => (L x).D.nP :=
  Unary.of_length (Desc.prods_polyT (LDesc.D_polyT hL))
theorem nC_unary {L : α → LDesc} (hL : PolyT L) : Unary fun x => (L x).D.nC :=
  Unary.of_length (Desc.chains_polyT (LDesc.D_polyT hL))
theorem nQ_unary {L : α → LDesc} (hL : PolyT L) : Unary fun x => (L x).D.nQ :=
  Unary.of_length (Desc.cmps_polyT (LDesc.D_polyT hL))

@[fun_prop] theorem wObj_polyT {L : α → LDesc} (hL : PolyT L) : PolyT fun x => wObj (L x) := by
  have hD := LDesc.D_polyT hL
  have hP := (nP_unary hL).poly
  unfold wObj
  exact PolyT.cons' (Desc.nV_polyT hD) (PolyT.cons' hP (PolyT.cons' hP (PolyT.cons' hP (PolyT.cons' hP
    (PolyT.cons' hP (PolyT.cons' hP (PolyT.cons' (nC_unary hL).poly (PolyT.cons' (nQ_unary hL).poly
      (PolyT.const [])))))))))

@[fun_prop] theorem vObj_polyT {L : α → LDesc} (hL : PolyT L) : PolyT fun x => vObj (L x) := by
  have hP := (nP_unary hL).poly
  unfold vObj
  exact PolyT.cons' (LDesc.nL_polyT hL) (PolyT.cons' hP (PolyT.cons' hP (PolyT.cons' hP (PolyT.cons' hP
    (PolyT.cons' hP (PolyT.cons' (nC_unary hL).poly (PolyT.const [])))))))

/-- A list `(range N).map f` with `N` in unary and `f` PolyT on `(x, o)`. -/
theorem rmap_polyT {N : α → ℕ} {f : α → ℕ → List ℕ} (hN : Unary N) (hf : PolyT fun q : α × ℕ => f q.1 q.2) :
    PolyT fun x => (List.range (N x)).map (f x) := PolyT.map hf (PolyT.range hN)

theorem l1_polyT' {a : α → ℕ} (ha : PolyT a) : PolyT fun x => [a x] := PolyT.cons' ha (PolyT.const [])
theorem l2_polyT' {a b : α → ℕ} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => [a x, b x] :=
  PolyT.cons' ha (l1_polyT' hb)
theorem l3_polyT' {a b c : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) : PolyT fun x => [a x, b x, c x] :=
  PolyT.cons' ha (l2_polyT' hb hc)

variable {n : α → ℕ} {L : α → LDesc} (hn : Unary n) (hL : PolyT L)
include hn hL

theorem wLay_polyT (hV : Unary fun x => (L x).D.nV) : PolyT fun x => wLay (n x) (L x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hn1 := hn.comp f1
  have hL1 := hL.comp f1
  have hlp := LDesc.lp_polyT hL1 s1
  have kl1p := (kl1_unary hn1 hlp).poly
  have kL1p := (kL1_unary hn1 hlp).poly
  have klp := (kl_unary hn1 hlp).poly
  have hP := nP_unary hL
  refine PolyT.congr ?_ fun x => (wLay_eq (n x) (L x)).symm
  refine PolyT.append (rmap_polyT hV (l1_polyT' (kl_unary hn1 (LDesc.lv_polyT hL1 s1)).poly)) ?_
  refine PolyT.append (rmap_polyT hP (l2_polyT' (PolyT.const 2) klp)) ?_
  refine PolyT.append (rmap_polyT hP (l3_polyT' (PolyT.const 2) kL1p kl1p)) ?_
  refine PolyT.append (rmap_polyT hP (l3_polyT' (PolyT.const 2) kL1p kL1p)) ?_
  refine PolyT.append (rmap_polyT hP (l2_polyT' kL1p kL1p)) ?_
  refine PolyT.append (rmap_polyT hP (l2_polyT' kL1p kL1p)) ?_
  refine PolyT.append (rmap_polyT hP (l2_polyT' kL1p kL1p)) ?_
  refine PolyT.append (rmap_polyT (nC_unary hL) (l1_polyT' (PolyT.sub
    (kKc_unary hn1 (LDesc.lc_polyT hL1 s1)).poly (PolyT.const 1)))) ?_
  refine PolyT.append (rmap_polyT (nQ_unary hL) (l1_polyT' (PolyT.sub
    (kl_unary hn1 (LDesc.lq_polyT hL1 s1)).poly (PolyT.const 1)))) (PolyT.const [])

theorem vLay_polyT (hK : Unary fun x => (L x).nL) : PolyT fun x => vLay (n x) (L x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hn1 := hn.comp f1
  have hL1 := hL.comp f1
  have hlp := LDesc.lp_polyT hL1 s1
  have kl1p := (kl1_unary hn1 hlp).poly
  have kL1p := (kL1_unary hn1 hlp).poly
  have hP := nP_unary hL
  refine PolyT.congr ?_ fun x => (vLay_eq (n x) (L x)).symm
  refine PolyT.append (rmap_polyT hK (l1_polyT' (kl_unary hn1 s1).poly)) ?_
  refine PolyT.append (rmap_polyT hP (l2_polyT' (PolyT.const 2) kl1p)) ?_
  refine PolyT.append (rmap_polyT hP (l2_polyT' (PolyT.const 2) kL1p)) ?_
  refine PolyT.append (rmap_polyT hP (l2_polyT' kL1p kL1p)) ?_
  refine PolyT.append (rmap_polyT hP (l1_polyT' kL1p)) ?_
  refine PolyT.append (rmap_polyT hP (l1_polyT' kL1p)) ?_
  exact PolyT.append (rmap_polyT (nC_unary hL) (l1_polyT' (kKc_unary hn1 (LDesc.lc_polyT hL1 s1)).poly))
    (PolyT.const [])

theorem vBoxZ_polyT {κ o : α → ℕ} (hκ : PolyT κ) (ho : PolyT o) : PolyT fun x => vBoxZ (n x) (L x) (κ x) (o x) := by
  have hlp := LDesc.lp_polyT hL ho
  have kl1p := (kl1_unary hn hlp).poly
  have kL1p := (kL1_unary hn hlp).poly
  have e : ∀ k : ℕ, PolyT fun x => decide (κ x = k) := fun k => PolyT.decide_eq hκ (PolyT.const k)
  unfold vBoxZ
  exact PolyT.ite' (e 0) (l1_polyT' (kl_unary hn ho).poly)
    (PolyT.ite' (e 1) (l2_polyT' (PolyT.const 2) kl1p)
    (PolyT.ite' (e 2) (l2_polyT' (PolyT.const 2) kL1p)
    (PolyT.ite' (e 3) (l2_polyT' kL1p kL1p)
    (PolyT.ite' (PolyT.decide_le hκ (PolyT.const 5)) (l1_polyT' kL1p)
      (l1_polyT' (kKc_unary hn (LDesc.lc_polyT hL ho)).poly)))))

theorem clusLZ_polyT (hK : Unary fun x => (L x).nL) {g κ o : α → ℕ} {co : α → List ℕ} (hg : PolyT g)
    (hκ : PolyT κ) (ho : PolyT o) (hco : PolyT co) : PolyT fun x => clusLZ (n x) (L x) (g x) (κ x) (o x) (co x) := by
  unfold clusLZ LB.fidx
  exact vbN_polyT (PolyT.getD (sizes_polyT (vLay_polyT hn hL hK)) (PolyT.add (off_polyT (vObj_polyT hL) hκ) ho)
    (PolyT.const 0)) hg (enc_polyT (vBoxZ_polyT hn hL hκ ho) hco)

end LPoly

section CPoly
variable {α : Type} [Enc α]

@[fun_prop] theorem rdx_polyT {L : α → LDesc} {r : α → Rd} {κ o : α → ℕ} {co : α → List ℕ} (hL : PolyT L)
    (hr : PolyT r) (hκ : PolyT κ) (ho : PolyT o) (hco : PolyT co) :
    PolyT fun x => rdx (L x) (r x) (κ x) (o x) (co x) := by
  unfold rdx LB.fidx
  exact rdw_polyT hr (PolyT.add (off_polyT (wObj_polyT hL) hκ) ho) hco

section G
variable {P : α → Prm} {L : α → LDesc} {r : α → Rd} (hP : PolyT P) (hL : PolyT L) (hr : PolyT r)
include hP hL hr

theorem rowG_polyT {p σ i2 : α → ℕ} (hp : PolyT p) (hσ : PolyT σ) (hi : PolyT i2) :
    PolyT fun x => rowG (P x) (L x) (r x) (p x) (σ x) (i2 x) := by
  unfold rowG rowE; fun_prop
theorem colG_polyT {p σ s : α → ℕ} (hp : PolyT p) (hσ : PolyT σ) (hs : PolyT s) :
    PolyT fun x => colG (P x) (L x) (r x) (p x) (σ x) (s x) := by
  unfold colG colE; fun_prop
theorem mulG_polyT {p s t : α → ℕ} (hp : PolyT p) (hs : PolyT s) (ht : PolyT t) :
    PolyT fun x => mulG (P x) (L x) (r x) (p x) (s x) (t x) := by
  unfold mulG; fun_prop
theorem icolG_polyT {p s : α → ℕ} (hp : PolyT p) (hs : PolyT s) :
    PolyT fun x => icolG (P x) (L x) (r x) (p x) (s x) := by
  unfold icolG invColE; fun_prop
theorem irowG_polyT {p u : α → ℕ} (hp : PolyT p) (hu : PolyT u) :
    PolyT fun x => irowG (P x) (L x) (r x) (p x) (u x) := by
  unfold irowG invRowE; fun_prop

theorem convG_polyT {pp k : α → ℕ} (hpp : PolyT pp) (hk : PolyT k) :
    PolyT fun x => convE (P x) (fun a u => rdx (L x) (r x) 6 (pp x) [a, u]) (k x) := by
  unfold convE; fun_prop

theorem tDigG_polyT {c k : α → ℕ} {t : α → Term} (hc : PolyT c) (ht : PolyT t) (hk : PolyT k) :
    PolyT fun x => tDigG (P x) (L x) (r x) (c x) (t x) (k x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hD1 := LDesc.D_polyT (hL.comp f1)
  have h1 : PolyT fun q : α × ℕ => if q.2 < (L q.1).D.nP ∧ chainOfZ (L q.1).D q.2 = c q.1 then
      convE (P q.1) (fun a u => rdx (L q.1) (r q.1) 6 q.2 [a, u]) (k q.1) else 0 := by
    have e1 := PolyT.decide_lt s1 (PolyT.length (Desc.prods_polyT hD1))
    have e2 := PolyT.decide_eq (chainOfZ_polyT hD1 s1) (hc.comp f1)
    have e3 := convG_polyT (hP.comp f1) (hL.comp f1) (hr.comp f1) s1 (hk.comp f1)
    have e4 := PolyT.decide_and e1 e2
    exact PolyT.ite' e4 e3 (PolyT.const 0)
  have f3 : PolyT fun q : (α × (ℕ ⊕ List ℕ)) × List ℕ => q.1.1 := PolyT.fst (PolyT.fst PolyT.id')
  have h3 : PolyT fun q : (α × (ℕ ⊕ List ℕ)) × List ℕ => q.2.getD (k q.1.1) 0 :=
    PolyT.getD (PolyT.snd PolyT.id') (hk.comp f3) (PolyT.const 0)
  have h23 : PolyT fun q : α × (ℕ ⊕ List ℕ) => q.2.elim (fun _ => 0) (fun l => l.getD (k q.1) 0) :=
    PolyT.sumElim (s := fun q : α × (ℕ ⊕ List ℕ) => q.2) (f := fun _ _ => 0)
      (g := fun q l => l.getD (k q.1) 0) (PolyT.snd PolyT.id') (PolyT.const 0) h3
  have hs := Src.toE_polyT (Term.src_polyT ht)
  have h := PolyT.sumElim (s := fun x => (t x).src.toE)
    (f := fun x pp => if pp < (L x).D.nP ∧ chainOfZ (L x).D pp = c x then
      convE (P x) (fun a u => rdx (L x) (r x) 6 pp [a, u]) (k x) else 0)
    (g := fun x e => e.elim (fun _ => 0) (fun l => l.getD (k x) 0)) hs h1 h23
  exact h.congr fun x => rfl
theorem sDigG_polyT {c k : α → ℕ} {ts : α → List Term} (hc : PolyT c) (hts : PolyT ts) (hk : PolyT k) :
    PolyT fun x => sDigG (P x) (L x) (r x) (c x) (ts x) (k x) := by
  have f1 : PolyT fun q : α × Term => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × Term => q.2 := PolyT.snd PolyT.id'
  exact PolyT.sum (PolyT.map (f := fun x t => t.coeff * tDigG (P x) (L x) (r x) (c x) t (k x))
    (PolyT.mul (Term.coeff_polyT s1) (tDigG_polyT (hP.comp f1) (hL.comp f1) (hr.comp f1)
      (hc.comp f1) s1 (hk.comp f1))) hts)

theorem carryG_polyT {K OFF c k : α → ℕ} (hK : PolyT K) (hO : PolyT OFF) (hc : PolyT c) (hk : PolyT k) :
    PolyT fun x => carryG (P x) (L x) (r x) (K x) (OFF x) (c x) (k x) := by
  have hch := getD_chains_polyT (LDesc.D_polyT hL) hc
  have hpb := pb_polyT hP
  have hout : PolyT fun x => if k x + 1 < K x then rdx (L x) (r x) 7 (c x) [k x] else OFF x :=
    PolyT.ite' (PolyT.decide_lt (PolyT.add hk (PolyT.const 1)) hK)
      (rdx_polyT hL hr (PolyT.const 7) hc (l1_polyT' hk)) hO
  have hin : PolyT fun x => if k x = 0 then OFF x else rdx (L x) (r x) 7 (c x) [k x - 1] :=
    PolyT.ite' (PolyT.decide_eq hk (PolyT.const 0)) hO
      (rdx_polyT hL hr (PolyT.const 7) hc (l1_polyT' (PolyT.sub hk (PolyT.const 1))))
  have hr' := sDigG_polyT hP hL hr hc (ChainD.rhs_polyT hch) hk
  have hl' := sDigG_polyT hP hL hr hc (ChainD.lhs_polyT hch) hk
  exact PolyT.decide_eq (PolyT.add (PolyT.add (PolyT.mul hout hpb) hr') hO)
    (PolyT.add (PolyT.add hl' hin) (PolyT.mul hO hpb))

end G

section Z
variable {n : α → ℕ} {L : α → LDesc} {r : α → Rd} (h : LH n L r)
include h

theorem cellRk_polyT {p σ i : α → ℕ} (hp : PolyT p) (hσ : PolyT σ) (hi : PolyT i) :
    PolyT fun x => cellRk (n x) (L x) (p x) (σ x) (i x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have h1 := h.comp f1
  have hlv := LDesc.lv_polyT h1.pL s1
  have hlp := LDesc.lp_polyT h1.pL (hp.comp f1)
  exact PolyT.sumElim (s := fun x => (opnd (L x).D (p x) (σ x)).toE)
    (f := fun x w => if w < (L x).D.nV ∧ i x < kl (n x) ((L x).lv w) then (L x).lv w else (L x).lp (p x))
    (g := fun x _ => (L x).lp (p x))
    (Operand.toE_polyT (opnd_polyT (LDesc.D_polyT h.pL) hp hσ))
    (PolyT.ite' (PolyT.decide_and (PolyT.decide_lt s1 (Desc.nV_polyT (LDesc.D_polyT h1.pL)))
      (PolyT.decide_lt (hi.comp f1) (kl_unary h1.un hlv).poly)) hlv hlp)
    (LDesc.lp_polyT (h.pL.comp (PolyT.fst PolyT.id')) (hp.comp (PolyT.fst PolyT.id')))

theorem opLimbRZ_polyT {p σ i : α → ℕ} (hp : PolyT p) (hσ : PolyT σ) (hi : PolyT i) :
    PolyT fun x => opLimbRZ (n x) (L x) (r x) (p x) (σ x) (i x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have h1 := h.comp f1
  have hlv := LDesc.lv_polyT h1.pL s1
  have f2 : PolyT fun q : α × List ℕ => q.1 := PolyT.fst PolyT.id'
  exact PolyT.sumElim (s := fun x => (opnd (L x).D (p x) (σ x)).toE)
    (f := fun x w => if w < (L x).D.nV ∧ i x < kl (n x) ((L x).lv w) then rdx (L x) (r x) 0 w [i x] else 0)
    (g := fun x l => l.getD (i x) 0)
    (Operand.toE_polyT (opnd_polyT (LDesc.D_polyT h.pL) hp hσ))
    (PolyT.ite' (PolyT.decide_and (PolyT.decide_lt s1 (Desc.nV_polyT (LDesc.D_polyT h1.pL)))
      (PolyT.decide_lt (hi.comp f1) (kl_unary h1.un hlv).poly))
      (rdx_polyT h1.pL h1.pr (PolyT.const 0) s1 (l1_polyT' (hi.comp f1))) (PolyT.const 0))
    (PolyT.getD (PolyT.snd PolyT.id') (hi.comp f2) (PolyT.const 0))

omit h in
theorem opLimbCZ_polyT (hL : PolyT L) (hr : PolyT r) {k i : α → ℕ} {o : α → Operand} (hk : PolyT k)
    (ho : PolyT o) (hi : PolyT i) : PolyT fun x => opLimbCZ (L x) (r x) (k x) (o x) (i x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hL1 := hL.comp f1
  have f2 : PolyT fun q : α × List ℕ => q.1 := PolyT.fst PolyT.id'
  exact PolyT.sumElim (s := fun x => (o x).toE)
    (f := fun x w => if w < (L x).D.nV ∧ (L x).lv w = k x then rdx (L x) (r x) 0 w [i x] else 0)
    (g := fun x l => l.getD (i x) 0) (Operand.toE_polyT ho)
    (PolyT.ite' (PolyT.decide_and (PolyT.decide_lt s1 (Desc.nV_polyT (LDesc.D_polyT hL1)))
      (PolyT.decide_eq (LDesc.lv_polyT hL1 s1) (hk.comp f1)))
      (rdx_polyT hL1 (hr.comp f1) (PolyT.const 0) s1 (l1_polyT' (hi.comp f1))) (PolyT.const 0))
    (PolyT.getD (PolyT.snd PolyT.id') (hi.comp f2) (PolyT.const 0))

theorem cmpOKLZ_polyT {q i : α → ℕ} (hq : PolyT q) (hi : PolyT i) :
    PolyT fun x => cmpOKLZ (n x) (L x) (r x) (q x) (i x) := by
  have hcq := getD_cmps_polyT (LDesc.D_polyT h.pL) hq
  have hlq := LDesc.lq_polyT h.pL hq
  have hA : PolyT fun x => if i x + 1 = kl (n x) ((L x).lq (q x)) then 1 else rdx (L x) (r x) 8 (q x) [i x] :=
    PolyT.ite' (PolyT.decide_eq (PolyT.add hi (PolyT.const 1)) (kl_unary h.un hlq).poly) (PolyT.const 1)
      (rdx_polyT h.pL h.pr (PolyT.const 8) hq (l1_polyT' hi))
  have hyl := opLimbCZ_polyT h.pL h.pr hlq (Operand.var_polyT (CmpD.v_polyT hcq)) hi
  have hpl := opLimbCZ_polyT h.pL h.pr hlq (CmpD.rhs_polyT hcq) hi
  have hst := cmpStep_polyT hA hyl hpl
  unfold cmpOKLZ
  exact PolyT.ite' (PolyT.decide_eq hi (PolyT.const 0)) (testZ_polyT (CmpRel.toE_polyT (CmpD.rel_polyT hcq)) hst)
    (PolyT.beq' (rdx_polyT h.pL h.pr (PolyT.const 8) hq (l1_polyT' (PolyT.sub hi (PolyT.const 1)))) hst)

set_option maxHeartbeats 1000000 in
theorem cellLZ_polyT {k i : α → ℕ} (hk : PolyT k) (hi : PolyT i) :
    PolyT fun x => cellLZ (n x) (L x) (r x) (k x) (i x) := by
  have f1 : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have s1 : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have f2 : PolyT fun q : (α × ℕ) × ℕ => q.1.1 := PolyT.fst (PolyT.fst PolyT.id')
  have m2 : PolyT fun q : (α × ℕ) × ℕ => q.1.2 := PolyT.snd (PolyT.fst PolyT.id')
  have s2 : PolyT fun q : (α × ℕ) × ℕ => q.2 := PolyT.snd PolyT.id'
  have h1 := h.comp f1
  have h2 := h.comp f2
  have hA : PolyT fun x => (List.range (L x).D.nV).all fun v => !(decide ((L x).lv v = k x)) ||
      (decide (rdx (L x) (r x) 0 v [i x] < 2 ^ b (n x)) &&
        patOK (n x) ((L x).D.pat.getD v []) (i x) (rdx (L x) (r x) 0 v [i x])) := by
    have hR0 : PolyT fun q : α × ℕ => rdx (L q.1) (r q.1) 0 q.2 [i q.1] :=
      rdx_polyT h1.pL h1.pr (PolyT.const 0) s1 (l1_polyT' (hi.comp f1))
    have hpat : PolyT fun q : α × ℕ => patOK (n q.1) ((L q.1).D.pat.getD q.2 []) (i q.1)
        (rdx (L q.1) (r q.1) 0 q.2 [i q.1]) :=
      (patE_polyT (prmOf_polyT h1.un) (PolyT.getD (Desc.pat_polyT (LDesc.D_polyT h1.pL)) s1 (PolyT.const []))
        (hi.comp f1) hR0).congr fun _ => rfl
    exact PolyT.all (f := fun x v => !(decide ((L x).lv v = k x)) ||
        (decide (rdx (L x) (r x) 0 v [i x] < 2 ^ b (n x)) &&
          patOK (n x) ((L x).D.pat.getD v []) (i x) (rdx (L x) (r x) 0 v [i x])))
      (PolyT.or' (PolyT.not' (PolyT.decide_eq (LDesc.lv_polyT h1.pL s1) (hk.comp f1)))
        (PolyT.and' (PolyT.decide_lt hR0 (PolyT.two_pow (b_unary h1.un))) hpat)) (PolyT.range h.uV)
  have hB : PolyT fun x => (List.range (L x).D.nP).all fun p => (List.range 2).all fun σ =>
      !(decide (i x < kl (n x) ((L x).lp p) ∧ cellRk (n x) (L x) p σ (i x) = k x)) ||
        rdx (L x) (r x) 1 p [σ, i x] == opLimbRZ (n x) (L x) (r x) p σ (i x) := by
    have hin : PolyT fun q : (α × ℕ) × ℕ =>
        !(decide (i q.1.1 < kl (n q.1.1) ((L q.1.1).lp q.1.2) ∧ cellRk (n q.1.1) (L q.1.1) q.1.2 q.2 (i q.1.1) = k q.1.1)) ||
          rdx (L q.1.1) (r q.1.1) 1 q.1.2 [q.2, i q.1.1] == opLimbRZ (n q.1.1) (L q.1.1) (r q.1.1) q.1.2 q.2 (i q.1.1) :=
      PolyT.or' (PolyT.not' (PolyT.decide_and
          (PolyT.decide_lt (hi.comp f2) (kl_unary h2.un (LDesc.lp_polyT h2.pL m2)).poly)
          (PolyT.decide_eq (cellRk_polyT h2 m2 s2 (hi.comp f2)) (hk.comp f2))))
        (PolyT.beq' (rdx_polyT h2.pL h2.pr (PolyT.const 1) m2 (l2_polyT' s2 (hi.comp f2)))
          (opLimbRZ_polyT h2 m2 s2 (hi.comp f2)))
    have hout : PolyT fun q : α × ℕ => (List.range 2).all fun σ =>
        !(decide (i q.1 < kl (n q.1) ((L q.1).lp q.2) ∧ cellRk (n q.1) (L q.1) q.2 σ (i q.1) = k q.1)) ||
          rdx (L q.1) (r q.1) 1 q.2 [σ, i q.1] == opLimbRZ (n q.1) (L q.1) (r q.1) q.2 σ (i q.1) :=
      PolyT.all (f := fun (q : α × ℕ) σ =>
        !(decide (i q.1 < kl (n q.1) ((L q.1).lp q.2) ∧ cellRk (n q.1) (L q.1) q.2 σ (i q.1) = k q.1)) ||
          rdx (L q.1) (r q.1) 1 q.2 [σ, i q.1] == opLimbRZ (n q.1) (L q.1) (r q.1) q.2 σ (i q.1)) hin (PolyT.const _)
    exact PolyT.all (f := fun x p => (List.range 2).all fun σ =>
      !(decide (i x < kl (n x) ((L x).lp p) ∧ cellRk (n x) (L x) p σ (i x) = k x)) ||
        rdx (L x) (r x) 1 p [σ, i x] == opLimbRZ (n x) (L x) (r x) p σ (i x)) hout (PolyT.range (nP_unary h.pL))
  have hC : PolyT fun x => (List.range (L x).D.nQ).all fun q => !(decide ((L x).lq q = k x)) ||
      cmpOKLZ (n x) (L x) (r x) q (i x) :=
    PolyT.all (f := fun x q => !(decide ((L x).lq q = k x)) || cmpOKLZ (n x) (L x) (r x) q (i x))
      (PolyT.or' (PolyT.not' (PolyT.decide_eq (LDesc.lq_polyT h1.pL s1) (hk.comp f1)))
        (cmpOKLZ_polyT h1 s1 (hi.comp f1))) (PolyT.range (nQ_unary h.pL))
  unfold cellLZ
  exact PolyT.and' (PolyT.and' hA hB) hC

/-- **The checks on codes are polynomial-time.** -/
theorem chkLZ_polyT {κ o : α → ℕ} {co : α → List ℕ} (hκ : PolyT κ) (ho : PolyT o) (hco : PolyT co) :
    PolyT fun x => chkLZ (n x) (L x) (r x) (κ x) (o x) (co x) := by
  have g0 : PolyT fun x => (co x).getD 0 0 := PolyT.getD hco (PolyT.const 0) (PolyT.const 0)
  have g1 : PolyT fun x => (co x).getD 1 0 := PolyT.getD hco (PolyT.const 1) (PolyT.const 0)
  have e : ∀ k : ℕ, PolyT fun x => decide (κ x = k) := fun k => PolyT.decide_eq hκ (PolyT.const k)
  have hP := kP_polyT h.un (LDesc.lp_polyT h.pL ho)
  have hlc := LDesc.lc_polyT h.pL ho
  have hO : PolyT fun x => aOFF (n x) := PolyT.two_pow ((J_unary h.un).add (Unary.const 6))
  unfold chkLZ
  exact PolyT.ite' (e 0) (cellLZ_polyT h ho g0)
    (PolyT.ite' (e 1) (rowG_polyT hP h.pL h.pr ho g0 g1)
    (PolyT.ite' (e 2) (colG_polyT hP h.pL h.pr ho g0 g1)
    (PolyT.ite' (e 3) (mulG_polyT hP h.pL h.pr ho g0 g1)
    (PolyT.ite' (e 4) (icolG_polyT hP h.pL h.pr ho g0)
    (PolyT.ite' (e 5) (irowG_polyT hP h.pL h.pr ho g0)
      (carryG_polyT (kP_polyT h.un hlc) h.pL h.pr (kKc_unary h.un hlc).poly hO ho g0))))))

end Z

end CPoly

end EthFollowup.Primes
