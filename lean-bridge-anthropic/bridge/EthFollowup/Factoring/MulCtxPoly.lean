/-
# Factoring, module F3 (part 2): the context and the table procedure in polynomial time

`PolyT` of every function of `MulProcs.lean` that the procedures or the reader evaluate: the
parameter accessors, the clusters and wire ends (`clusJ`, `endE`, `wLoE`, `wHiE`), the incidence
and pair lists (`incE`, `pairE`), the layout `layM`, the context `mctxOf`, the checks with the wire
values read from a setting (`chkZ`), the table `tabF`; `mulTp_poly : Nonempty (IsPolyT mulTp)`.

Standard axioms only.
-/
import EthFollowup.Factoring.MulProcs
import ToTuring.Poly.Range
import ToTuring.Poly.Basic
import ToTuring.Lib.List3
import ToTuring.Lib.Nat2
import ToTuring.Lib.List2
import ToTuring.Lib.Nat1b
import ToTuring.Lib.List1b

set_option linter.unusedSectionVars false

namespace EthFollowup.Factoring

open Groundwork Groundwork.Prog EthFollowup.ExactHC MP

namespace MPoly

variable {α : Type} [Enc α]

/-! ### The parameter accessors -/

section Acc
variable {d : α → Prm} (hd : PolyT d)
include hd

@[fun_prop] theorem l1_polyT : PolyT fun x => (d x).l1 := by unfold Prm.l1; fun_prop
@[fun_prop] theorem l2_polyT : PolyT fun x => (d x).l2 := by unfold Prm.l2; fun_prop
@[fun_prop] theorem L1_polyT : PolyT fun x => (d x).L1 := by unfold Prm.L1; fun_prop
@[fun_prop] theorem L2_polyT : PolyT fun x => (d x).L2 := by unfold Prm.L2; fun_prop
@[fun_prop] theorem b_polyT : PolyT fun x => (d x).b := by unfold Prm.b; fun_prop
@[fun_prop] theorem pb_polyT : PolyT fun x => (d x).pb := by unfold Prm.pb; fun_prop
@[fun_prop] theorem M_polyT : PolyT fun x => (d x).M := by unfold Prm.M; fun_prop
@[fun_prop] theorem iL_polyT : PolyT fun x => (d x).iL := by unfold Prm.iL; fun_prop
@[fun_prop] theorem uW_polyT : PolyT fun x => (d x).uW := by unfold Prm.uW; fun_prop
@[fun_prop] theorem W_polyT : PolyT fun x => (d x).W := by unfold Prm.W Prm.uW; fun_prop
@[fun_prop] theorem wT_polyT : PolyT fun x => (d x).wT := by unfold Prm.wT; fun_prop
@[fun_prop] theorem rl1_polyT : PolyT fun x => (d x).rl1 := by unfold Prm.rl1; fun_prop
@[fun_prop] theorem rl2_polyT : PolyT fun x => (d x).rl2 := by unfold Prm.rl2; fun_prop
@[fun_prop] theorem rL1_polyT : PolyT fun x => (d x).rL1 := by unfold Prm.rL1; fun_prop
@[fun_prop] theorem rL2_polyT : PolyT fun x => (d x).rL2 := by unfold Prm.rL2; fun_prop
@[fun_prop] theorem rb_polyT : PolyT fun x => (d x).rb := by unfold Prm.rb; fun_prop
@[fun_prop] theorem rW_polyT : PolyT fun x => (d x).rW := by unfold Prm.rW; fun_prop
@[fun_prop] theorem rV_polyT : PolyT fun x => (d x).rV := by unfold Prm.rV; fun_prop
@[fun_prop] theorem l_polyT : PolyT fun x => (d x).l := by unfold Prm.l; fun_prop
@[fun_prop] theorem nA_polyT : PolyT fun x => (d x).nA := by unfold Prm.nA; fun_prop
@[fun_prop] theorem nF_polyT : PolyT fun x => (d x).nF := by unfold Prm.nF; fun_prop
@[fun_prop] theorem Kc_polyT : PolyT fun x => (d x).Kc := by unfold Prm.Kc; fun_prop

end Acc

/-! ### Small functions -/

theorem obit_eq (o : Option Bool) (x : Bool) : obit o x = (o.isNone || (x == o.getD false)) := by
  cases o <;> rfl

@[fun_prop] theorem obit_polyT {o : α → Option Bool} {x : α → Bool} (ho : PolyT o) (hx : PolyT x) :
    PolyT fun y => obit (o y) (x y) := by
  have h : PolyT fun y => ((o y).isNone || (x y == (o y).getD false)) := by fun_prop
  exact h.congr fun y => (obit_eq _ _).symm

@[fun_prop] theorem lohi_polyT {g a c : α → ℕ} (hg : PolyT g) (ha : PolyT a) (hc : PolyT c) :
    PolyT fun x => lohi (g x) (a x) (c x) := by unfold lohi; fun_prop

@[fun_prop] theorem dv_polyT {a c : α → ℕ} (ha : PolyT a) (hc : PolyT c) : PolyT fun x => dv (a x) (c x) :=
  PolyT.div ha hc
@[fun_prop] theorem md_polyT {a c : α → ℕ} (ha : PolyT a) (hc : PolyT c) : PolyT fun x => md (a x) (c x) :=
  PolyT.mod ha hc
@[fun_prop] theorem dvp_polyT {a e : α → ℕ} (ha : PolyT a) (he : PolyT e) : PolyT fun x => dvp (a x) (e x) :=
  PolyT.div_pow ha (PolyT.const 2) he

@[fun_prop] theorem vbN_polyT {n g v : α → ℕ} (hn : PolyT n) (hg : PolyT g) (hv : PolyT v) :
    PolyT fun x => VB.vbN (n x) (g x) (v x) := by
  unfold VB.vbN; exact PolyT.div (PolyT.mul hv hg) hn

@[fun_prop] theorem xz_polyT {Wd : α → ℕ} {inc : α → List ℕ} {z : α → List Bool} {k : α → ℕ}
    (hW : PolyT Wd) (hi : PolyT inc) (hz : PolyT z) (hk : PolyT k) :
    PolyT fun x => xz (Wd x) (inc x) (z x) (k x) := by unfold xz; fun_prop

@[fun_prop] theorem wq_polyT {p : α → Prm} {e : α → ℕ} (hp : PolyT p) (he : PolyT e) :
    PolyT fun x => wq (p x) (e x) := by unfold wq; fun_prop

@[fun_prop] theorem patE_polyT {p : α → Prm} {pt : α → List (Option Bool)} {i y : α → ℕ} (hp : PolyT p)
    (hpt : PolyT pt) (hi : PolyT i) (hy : PolyT y) : PolyT fun x => patE (p x) (pt x) (i x) (y x) := by
  unfold patE; fun_prop

@[fun_prop] theorem carryE_polyT {p : α → Prm} {Nl c rin rout : α → ℕ} (hp : PolyT p) (h1 : PolyT Nl)
    (h2 : PolyT c) (h3 : PolyT rin) (h4 : PolyT rout) :
    PolyT fun x => carryE (p x) (Nl x) (c x) (rin x) (rout x) := by
  unfold carryE; fun_prop

@[fun_prop] theorem NkE_polyT {p : α → Prm} {N k : α → ℕ} (hp : PolyT p) (hN : PolyT N) (hk : PolyT k) :
    PolyT fun x => NkE (p x) (N x) (k x) := by
  unfold NkE; fun_prop

/-! ### Offsets and indices as atoms (they keep the `fun_prop` goals small) -/

section Atoms
variable (p : Prm)
/-- `2ℓ`. -/
def o2 : ℕ := 2 * p.l
def wAq : ℕ := 2 * p.l + p.nA
def wPf : ℕ := 2 * p.l + 2 * p.nA
def wQf : ℕ := 2 * p.l + 2 * p.nA + p.nF
def wCf : ℕ := 2 * p.l + 2 * p.nA + 2 * p.nF
def wDc : ℕ := 2 * p.l + 2 * p.nA + 3 * p.nF
def wCc : ℕ := 2 * p.l + 2 * p.nA + 4 * p.nF
def wrr : ℕ := 2 * p.l + 2 * p.nA + 5 * p.nF
def v3 : ℕ := 2 * p.l + p.l2
def v4 : ℕ := 2 * p.l + 2 * p.l2
def v5 : ℕ := 2 * p.l + 2 * p.l2 + p.L1
def v6 : ℕ := 2 * p.l + 2 * p.l2 + 2 * p.L1
def v7 : ℕ := 2 * p.l + 2 * p.l2 + 2 * p.L1 + p.nF
def v8 : ℕ := 2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF
def v9 : ℕ := 2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF + p.L2
end Atoms

/-- `s + L·t`. -/
def ix0 (L s t : ℕ) : ℕ := s + L * t
/-- `o + (s + L·t)`. -/
def ix (o L s t : ℕ) : ℕ := o + (s + L * t)
/-- `j mod L + L·(j div L)`. -/
def rc (L j : ℕ) : ℕ := md j L + L * dv j L

section AtomPoly
variable {p : α → Prm} (hp : PolyT p)
include hp
@[fun_prop] theorem o2_polyT : PolyT fun x => o2 (p x) := by unfold o2; fun_prop
@[fun_prop] theorem wAq_polyT : PolyT fun x => wAq (p x) := by unfold wAq; fun_prop
@[fun_prop] theorem wPf_polyT : PolyT fun x => wPf (p x) := by unfold wPf; fun_prop
@[fun_prop] theorem wQf_polyT : PolyT fun x => wQf (p x) := by unfold wQf; fun_prop
@[fun_prop] theorem wCf_polyT : PolyT fun x => wCf (p x) := by unfold wCf; fun_prop
@[fun_prop] theorem wDc_polyT : PolyT fun x => wDc (p x) := by unfold wDc; fun_prop
@[fun_prop] theorem wCc_polyT : PolyT fun x => wCc (p x) := by unfold wCc; fun_prop
@[fun_prop] theorem wrr_polyT : PolyT fun x => wrr (p x) := by unfold wrr; fun_prop
@[fun_prop] theorem v3_polyT : PolyT fun x => v3 (p x) := by unfold v3; fun_prop
@[fun_prop] theorem v4_polyT : PolyT fun x => v4 (p x) := by unfold v4; fun_prop
@[fun_prop] theorem v5_polyT : PolyT fun x => v5 (p x) := by unfold v5; fun_prop
@[fun_prop] theorem v6_polyT : PolyT fun x => v6 (p x) := by unfold v6; fun_prop
@[fun_prop] theorem v7_polyT : PolyT fun x => v7 (p x) := by unfold v7; fun_prop
@[fun_prop] theorem v8_polyT : PolyT fun x => v8 (p x) := by unfold v8; fun_prop
@[fun_prop] theorem v9_polyT : PolyT fun x => v9 (p x) := by unfold v9; fun_prop
end AtomPoly

@[fun_prop] theorem ix0_polyT {L s t : α → ℕ} (h1 : PolyT L) (h2 : PolyT s) (h3 : PolyT t) :
    PolyT fun x => ix0 (L x) (s x) (t x) := by unfold ix0; fun_prop
@[fun_prop] theorem ix_polyT {o L s t : α → ℕ} (h0 : PolyT o) (h1 : PolyT L) (h2 : PolyT s) (h3 : PolyT t) :
    PolyT fun x => ix (o x) (L x) (s x) (t x) := by unfold ix; fun_prop
@[fun_prop] theorem rc_polyT {L j : α → ℕ} (h1 : PolyT L) (h2 : PolyT j) :
    PolyT fun x => rc (L x) (j x) := by unfold rc; fun_prop

/-! ### The checks with the wire values read from a setting -/

section Z
variable (p : Prm) (N : ℕ) (pt : List (Option Bool)) (Wd : ℕ) (inc : List ℕ) (z : List Bool)

def cellPZ (i1 i2 : ℕ) : Bool :=
  decide (xz Wd inc z (ix0 p.l1 i1 i2) < p.pb) && patE p pt (ix0 p.l1 i1 i2) (xz Wd inc z (ix0 p.l1 i1 i2))
def cellQZ (i1 i2 : ℕ) : Bool := decide (xz Wd inc z (ix p.l p.l1 i1 i2) < p.pb)
def rowPZ (i2 : ℕ) : Bool := p.rL1.all fun s =>
  xz Wd inc z (ix (o2 p) p.L1 s i2) ==
    md (p.rl1.map fun i1 => xz Wd inc z (ix0 p.l1 i1 i2) * wq p (i1 * s)).sum p.M
def rowQZ (i2 : ℕ) : Bool := p.rL1.all fun s =>
  xz Wd inc z (ix (wAq p) p.L1 s i2) ==
    md (p.rl1.map fun i1 => xz Wd inc z (ix p.l p.l1 i1 i2) * wq p (i1 * s)).sum p.M
def colPZ (s : ℕ) : Bool := p.rL2.all fun t =>
  xz Wd inc z (ix (wPf p) p.L1 s t) ==
    md (p.rl2.map fun i2 => xz Wd inc z (ix (o2 p) p.L1 s i2) * wq p (i2 * t)).sum p.M
def colQZ (s : ℕ) : Bool := p.rL2.all fun t =>
  xz Wd inc z (ix (wQf p) p.L1 s t) ==
    md (p.rl2.map fun i2 => xz Wd inc z (ix (wAq p) p.L1 s i2) * wq p (i2 * t)).sum p.M
def mulZ (s t : ℕ) : Bool :=
  xz Wd inc z (ix (wCf p) p.L1 s t) ==
    md (xz Wd inc z (ix (wPf p) p.L1 s t) * xz Wd inc z (ix (wQf p) p.L1 s t)) p.M
def icolZ (s : ℕ) : Bool := p.rL2.all fun u =>
  xz Wd inc z (ix (wDc p) p.L1 s u) ==
    md (p.iL * (p.rL2.map fun t => xz Wd inc z (ix (wCf p) p.L1 s t) * wq p ((p.L2 - u) * t)).sum) p.M
def irowZ (u : ℕ) : Bool := p.rL1.all fun a =>
  xz Wd inc z (ix (wCc p) p.L1 a u) ==
    md (p.iL * (p.rL1.map fun s => xz Wd inc z (ix (wDc p) p.L1 s u) * wq p ((p.L1 - a) * s)).sum) p.M
def convZ (k : ℕ) : ℕ :=
  (p.rL1.map fun a => (p.rL2.map fun u =>
    if ix0 p.l1 a u = k then xz Wd inc z (ix (wCc p) p.L1 a u) else 0).sum).sum
def carryZ (k : ℕ) : Bool :=
  carryE p (NkE p N k) (convZ p Wd inc z k)
    (if k = 0 then 0 else xz Wd inc z (wrr p + (k - 1)))
    (if k + 1 < p.Kc then xz Wd inc z (wrr p + k) else 0)

/-- `chkE` with the wire values read from `z`, as an if-chain of first-order branches. -/
def chkZ (j : ℕ) : Bool :=
  if j < p.l then cellPZ p pt Wd inc z (md j p.l1) (dv j p.l1)
  else if j < o2 p then cellQZ p Wd inc z (md (j - p.l) p.l1) (dv (j - p.l) p.l1)
  else if j < v3 p then rowPZ p Wd inc z (j - o2 p)
  else if j < v4 p then rowQZ p Wd inc z (j - v3 p)
  else if j < v5 p then colPZ p Wd inc z (j - v4 p)
  else if j < v6 p then colQZ p Wd inc z (j - v5 p)
  else if j < v7 p then mulZ p Wd inc z (md (j - v6 p) p.L1) (dv (j - v6 p) p.L1)
  else if j < v8 p then icolZ p Wd inc z (j - v7 p)
  else if j < v9 p then irowZ p Wd inc z (j - v8 p)
  else carryZ p N Wd inc z (j - v9 p)

theorem chkZ_eq (j : ℕ) : chkZ p N pt Wd inc z j = chkE p N pt (xz Wd inc z) j := rfl

end Z

section ZPoly
variable {p : α → Prm} {N : α → ℕ} {pt : α → List (Option Bool)} {Wd : α → ℕ} {inc : α → List ℕ}
  {z : α → List Bool} (hp : PolyT p) (hW : PolyT Wd) (hi : PolyT inc) (hz : PolyT z)
include hp hW hi hz

@[fun_prop] theorem cellPZ_polyT {i1 i2 : α → ℕ} (hpt : PolyT pt) (h1 : PolyT i1) (h2 : PolyT i2) :
    PolyT fun x => cellPZ (p x) (pt x) (Wd x) (inc x) (z x) (i1 x) (i2 x) := by
  unfold cellPZ; fun_prop
@[fun_prop] theorem cellQZ_polyT {i1 i2 : α → ℕ} (h1 : PolyT i1) (h2 : PolyT i2) :
    PolyT fun x => cellQZ (p x) (Wd x) (inc x) (z x) (i1 x) (i2 x) := by
  unfold cellQZ; fun_prop
@[fun_prop] theorem rowPZ_polyT {i2 : α → ℕ} (h2 : PolyT i2) :
    PolyT fun x => rowPZ (p x) (Wd x) (inc x) (z x) (i2 x) := by
  unfold rowPZ; fun_prop
@[fun_prop] theorem rowQZ_polyT {i2 : α → ℕ} (h2 : PolyT i2) :
    PolyT fun x => rowQZ (p x) (Wd x) (inc x) (z x) (i2 x) := by
  unfold rowQZ; fun_prop
@[fun_prop] theorem colPZ_polyT {s : α → ℕ} (hs : PolyT s) :
    PolyT fun x => colPZ (p x) (Wd x) (inc x) (z x) (s x) := by
  unfold colPZ; fun_prop
@[fun_prop] theorem colQZ_polyT {s : α → ℕ} (hs : PolyT s) :
    PolyT fun x => colQZ (p x) (Wd x) (inc x) (z x) (s x) := by
  unfold colQZ; fun_prop
@[fun_prop] theorem mulZ_polyT {s t : α → ℕ} (hs : PolyT s) (ht : PolyT t) :
    PolyT fun x => mulZ (p x) (Wd x) (inc x) (z x) (s x) (t x) := by
  unfold mulZ; fun_prop
@[fun_prop] theorem icolZ_polyT {s : α → ℕ} (hs : PolyT s) :
    PolyT fun x => icolZ (p x) (Wd x) (inc x) (z x) (s x) := by
  unfold icolZ; fun_prop
@[fun_prop] theorem irowZ_polyT {u : α → ℕ} (hu : PolyT u) :
    PolyT fun x => irowZ (p x) (Wd x) (inc x) (z x) (u x) := by
  unfold irowZ; fun_prop
@[fun_prop] theorem convZ_polyT {k : α → ℕ} (hk : PolyT k) :
    PolyT fun x => convZ (p x) (Wd x) (inc x) (z x) (k x) := by
  unfold convZ; fun_prop
@[fun_prop] theorem carryZ_polyT {k : α → ℕ} (hN : PolyT N) (hk : PolyT k) :
    PolyT fun x => carryZ (p x) (N x) (Wd x) (inc x) (z x) (k x) := by
  unfold carryZ; fun_prop

set_option maxHeartbeats 1000000 in
@[fun_prop] theorem chkZ_polyT {j : α → ℕ} (hN : PolyT N) (hpt : PolyT pt) (hj : PolyT j) :
    PolyT fun x => chkZ (p x) (N x) (pt x) (Wd x) (inc x) (z x) (j x) := by
  unfold chkZ; fun_prop

end ZPoly

/-! ### Clusters, ends, incidence and pair lists -/

section W
variable (p : Prm) (g : ℕ)

/-- `clusJ` with atoms. -/
def clusZ (j : ℕ) : ℕ :=
  if j < p.l then VB.vbN p.l g (rc p.l1 j)
  else if j < o2 p then VB.vbN p.l g (rc p.l1 (j - p.l))
  else if j < v3 p then VB.vbN p.l2 g (j - o2 p)
  else if j < v4 p then VB.vbN p.l2 g (j - v3 p)
  else if j < v5 p then VB.vbN p.L1 g (j - v4 p)
  else if j < v6 p then VB.vbN p.L1 g (j - v5 p)
  else if j < v7 p then VB.vbN p.nF g (rc p.L1 (j - v6 p))
  else if j < v8 p then VB.vbN p.L1 g (j - v7 p)
  else if j < v9 p then VB.vbN p.L2 g (j - v8 p)
  else VB.vbN p.Kc g (j - v9 p)

theorem clusZ_eq (j : ℕ) : clusZ p g j = clusJ p g j := rfl

/-- `endE` with atoms. -/
def endZ (k : ℕ) : ℕ × ℕ :=
  if k < p.l then (rc p.l1 k, o2 p + dv k p.l1)
  else if k < o2 p then (p.l + rc p.l1 (k - p.l), v3 p + dv (k - p.l) p.l1)
  else if k < wAq p then (o2 p + dv (k - o2 p) p.L1, v4 p + md (k - o2 p) p.L1)
  else if k < wPf p then (v3 p + dv (k - wAq p) p.L1, v5 p + md (k - wAq p) p.L1)
  else if k < wQf p then (v4 p + md (k - wPf p) p.L1, v6 p + rc p.L1 (k - wPf p))
  else if k < wCf p then (v5 p + md (k - wQf p) p.L1, v6 p + rc p.L1 (k - wQf p))
  else if k < wDc p then (v6 p + rc p.L1 (k - wCf p), v7 p + md (k - wCf p) p.L1)
  else if k < wCc p then (v7 p + md (k - wDc p) p.L1, v8 p + dv (k - wDc p) p.L1)
  else if k < wrr p then
    (v8 p + dv (k - wCc p) p.L1, v9 p + (md (k - wCc p) p.L1 + p.l1 * dv (k - wCc p) p.L1))
  else (v9 p + (k - wrr p), v9 p + (k - wrr p + 1))

theorem endZ_eq (k : ℕ) : endZ p k = endE p k := rfl

end W

/-- `endE` in polynomial time (an explicit composition: `fun_prop` is slow on this chain). -/
@[fun_prop] theorem endE_polyT {p : α → Prm} {k : α → ℕ} (hp : PolyT p) (hk : PolyT k) :
    PolyT fun x => endE (p x) (k x) := by
  have hl := l_polyT hp
  have hl1 := l1_polyT hp
  have hL1 := L1_polyT hp
  have ho2 := o2_polyT hp
  have hAq := wAq_polyT hp
  have hPf := wPf_polyT hp
  have hQf := wQf_polyT hp
  have hCf := wCf_polyT hp
  have hDc := wDc_polyT hp
  have hCc := wCc_polyT hp
  have hrr := wrr_polyT hp
  have h3 := v3_polyT hp
  have h4 := v4_polyT hp
  have h5 := v5_polyT hp
  have h6 := v6_polyT hp
  have h7 := v7_polyT hp
  have h8 := v8_polyT hp
  have h9 := v9_polyT hp
  have s1 := PolyT.sub hk hl
  have s2 := PolyT.sub hk ho2
  have s3 := PolyT.sub hk hAq
  have s4 := PolyT.sub hk hPf
  have s5 := PolyT.sub hk hQf
  have s6 := PolyT.sub hk hCf
  have s7 := PolyT.sub hk hDc
  have s8 := PolyT.sub hk hCc
  have s9 := PolyT.sub hk hrr
  have h : PolyT fun x => endZ (p x) (k x) := by
    unfold endZ
    exact PolyT.ite' (PolyT.decide_lt hk hl)
      (PolyT.prodMk (rc_polyT hl1 hk) (PolyT.add ho2 (dv_polyT hk hl1)))
      (PolyT.ite' (PolyT.decide_lt hk ho2)
      (PolyT.prodMk (PolyT.add hl (rc_polyT hl1 s1)) (PolyT.add h3 (dv_polyT s1 hl1)))
      (PolyT.ite' (PolyT.decide_lt hk hAq)
      (PolyT.prodMk (PolyT.add ho2 (dv_polyT s2 hL1)) (PolyT.add h4 (md_polyT s2 hL1)))
      (PolyT.ite' (PolyT.decide_lt hk hPf)
      (PolyT.prodMk (PolyT.add h3 (dv_polyT s3 hL1)) (PolyT.add h5 (md_polyT s3 hL1)))
      (PolyT.ite' (PolyT.decide_lt hk hQf)
      (PolyT.prodMk (PolyT.add h4 (md_polyT s4 hL1)) (PolyT.add h6 (rc_polyT hL1 s4)))
      (PolyT.ite' (PolyT.decide_lt hk hCf)
      (PolyT.prodMk (PolyT.add h5 (md_polyT s5 hL1)) (PolyT.add h6 (rc_polyT hL1 s5)))
      (PolyT.ite' (PolyT.decide_lt hk hDc)
      (PolyT.prodMk (PolyT.add h6 (rc_polyT hL1 s6)) (PolyT.add h7 (md_polyT s6 hL1)))
      (PolyT.ite' (PolyT.decide_lt hk hCc)
      (PolyT.prodMk (PolyT.add h7 (md_polyT s7 hL1)) (PolyT.add h8 (dv_polyT s7 hL1)))
      (PolyT.ite' (PolyT.decide_lt hk hrr)
      (PolyT.prodMk (PolyT.add h8 (dv_polyT s8 hL1))
        (PolyT.add h9 (PolyT.add (md_polyT s8 hL1) (PolyT.mul hl1 (dv_polyT s8 hL1)))))
      (PolyT.prodMk (PolyT.add h9 s9) (PolyT.add h9 (PolyT.add s9 (PolyT.const 1))))))))))))
  exact h.congr fun x => endZ_eq _ _

section WPoly
variable {p : α → Prm} {g : α → ℕ} (hp : PolyT p) (hg : PolyT g)
include hp hg

set_option maxHeartbeats 1000000 in
@[fun_prop] theorem clusJ_polyT {j : α → ℕ} (hj : PolyT j) : PolyT fun x => clusJ (p x) (g x) (j x) := by
  have h : PolyT fun x => clusZ (p x) (g x) (j x) := by unfold clusZ; fun_prop
  exact h.congr fun x => clusZ_eq _ _ _


@[fun_prop] theorem wLoE_polyT {k : α → ℕ} (hk : PolyT k) : PolyT fun x => wLoE (p x) (g x) (k x) := by
  unfold wLoE; fun_prop

@[fun_prop] theorem wHiE_polyT {k : α → ℕ} (hk : PolyT k) : PolyT fun x => wHiE (p x) (g x) (k x) := by
  unfold wHiE; fun_prop

@[fun_prop] theorem incE_polyT {a : α → ℕ} (ha : PolyT a) : PolyT fun x => incE (p x) (g x) (a x) := by
  have hf : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hs : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hpq : PolyT fun q : α × ℕ => p q.1 := PolyT.comp hp hf
  have hgq : PolyT fun q : α × ℕ => g q.1 := PolyT.comp hg hf
  have haq : PolyT fun q : α × ℕ => a q.1 := PolyT.comp ha hf
  unfold incE
  exact PolyT.filter (f := fun x k => decide (wLoE (p x) (g x) k = a x ∨ wHiE (p x) (g x) k = a x))
    (PolyT.decide_or (PolyT.decide_eq (wLoE_polyT hpq hgq hs) haq) (PolyT.decide_eq (wHiE_polyT hpq hgq hs) haq))
    (rW_polyT hp)

@[fun_prop] theorem pairE_polyT {a c : α → ℕ} (ha : PolyT a) (hc : PolyT c) :
    PolyT fun x => pairE (p x) (g x) (a x) (c x) := by
  have hf : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
  have hs : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hpq : PolyT fun q : α × ℕ => p q.1 := PolyT.comp hp hf
  have hgq : PolyT fun q : α × ℕ => g q.1 := PolyT.comp hg hf
  have haq : PolyT fun q : α × ℕ => a q.1 := PolyT.comp ha hf
  have hcq : PolyT fun q : α × ℕ => c q.1 := PolyT.comp hc hf
  have hlo := wLoE_polyT hpq hgq hs
  have hhi := wHiE_polyT hpq hgq hs
  have hfil : PolyT fun x => (p x).rW.filter fun k =>
      decide ((wLoE (p x) (g x) k = a x ∧ wHiE (p x) (g x) k = c x) ∨
        (wLoE (p x) (g x) k = c x ∧ wHiE (p x) (g x) k = a x)) :=
    PolyT.filter (f := fun x k => decide ((wLoE (p x) (g x) k = a x ∧ wHiE (p x) (g x) k = c x) ∨
        (wLoE (p x) (g x) k = c x ∧ wHiE (p x) (g x) k = a x)))
      (PolyT.decide_or (PolyT.decide_and (PolyT.decide_eq hlo haq) (PolyT.decide_eq hhi hcq))
        (PolyT.decide_and (PolyT.decide_eq hlo hcq) (PolyT.decide_eq hhi haq))) (rW_polyT hp)
  have hinc : PolyT fun q : α × ℕ => incE (p q.1) (g q.1) (a q.1) := incE_polyT hpq hgq haq
  unfold pairE
  exact PolyT.map (f := fun x k => (incE (p x) (g x) (a x)).idxOf k) (PolyT.idxOf hs hinc) hfil

end WPoly

/-! ### The layout and the context -/

theorem layM_polyT {p : α → Prm} {g P : α → ℕ} (hp : PolyT p) (hg : Unary g) (hP : Unary P) :
    PolyT fun x => layM (p x) (g x) (P x) := by
  have hr : PolyT fun x => List.range (g x) := PolyT.range hg
  have hP' : PolyT fun x => List.replicate (P x) () := hP
  have hg' : PolyT g := hg.poly
  unfold layM; fun_prop

theorem mctxOf_polyT {p : α → Prm} {g N P : α → ℕ} {pt : α → List (Option Bool)} (hp : PolyT p)
    (hg : Unary g) (hN : PolyT N) (hpt : PolyT pt) (hP : Unary P) :
    PolyT fun x => mctxOf (p x) (g x) (N x) (pt x) (P x) := by
  have hl := layM_polyT hp hg hP
  have hr : PolyT fun x => List.range (g x) := PolyT.range hg
  have hg' : PolyT g := hg.poly
  unfold mctxOf; fun_prop

/-! ### The table procedure -/

theorem tabB_eqZ (c : MCtx) (a : ℕ) (z : List Bool) : tabB c a z =
    c.2.1.rV.all fun j => !(decide (clusJ c.2.1 c.2.2.1.1 j = a)) ||
      chkZ c.2.1 c.2.2.1.2 c.2.2.2.1 c.2.1.W (c.2.2.2.2.getD a []) z j := by
  unfold tabB
  simp only [chkZ_eq]

theorem tabF_polyT : PolyT tabF := by
  have h : PolyT fun q : MCtx × WQ =>
      if (q.1.2.1.rV.all fun j => !(decide (clusJ q.1.2.1 q.1.2.2.1.1 j = q.2.1)) ||
        chkZ q.1.2.1 q.1.2.2.1.2 q.1.2.2.2.1 q.1.2.1.W (q.1.2.2.2.2.getD q.2.1 []) q.2.2 j) = true
      then (1 : ℤ) else 0 := by
    fun_prop
  exact h.congr fun q => by rw [tabF, tabB_eqZ]

/-- **The table procedure has polynomial-time steps.** -/
theorem mulTp_poly : Nonempty (IsPolyT mulTp) := ⟨IsPolyT.ofFun tabF_polyT⟩

end MPoly

end EthFollowup.Factoring
