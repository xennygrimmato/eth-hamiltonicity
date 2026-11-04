/-
# Factoring, module F3 (part 1): procedures, context, layout and table of the multiplication network

`scratchpad/plans/factoring-plan.md` §2–§4 (row F3); interface `facM-interface.md` (F3/F4).

**Deviation from the plan (the code list).** `labelProcs` (C1b) decides membership with the list
of all code words held by the layout. The labels of the multiplication network are `W`-bit words
(`W ≈ 2^{ν/2+7}`), so that list has `2^W` entries and no polynomial-size context can hold it.
Every `W`-bit word is a code word of `labCode n` (`labCode_complete`), so membership in `S a` is
just the length test (`memW`). `labelProcsW lay par Tp` is `labelProcs` with this membership
procedure; `labelProcsW_give` is `labelProcs_give` for a *complete* code, with the layout's code
list ignored (the hypothesis `Describes` is stated for the layout with any code list `cs`,
`Lay.withCodes`).

* `labelProcsW`, `labelProcsW_give`, `labelProcsW_keeps`, `labelProcsW_isNet`;
* `Prm` (the parameters of `n` as one tuple of numbers and ranges), `prmOf n`;
* the numeric vertex/wire descriptions `vszE`, `vidxE`, `clusJ`, `endE`, `wLoE`, `wHiE`, `incE`,
  `pairE` with `clusJ_eq`, `wLoE_eq`, `wHiE_eq`, `incE_eq`, `pairE_eq`;
* the context `MCtx`, `mctx`, the layout `layM`, `layM_describes`;
* the checks with the wire values read from a setting: `chkE` (`chkE_eq`), `xz`, the table
  `tabF`, `Tp := Stepped.ofFun tabF`, `tabF_eq`, `mulSys_tspec`.

Standard axioms only.
-/
import EthFollowup.Factoring.MulNet
import EthFollowup.ExactHC.LabelProcs

set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Groundwork Groundwork.Prog QueryMachines Eight.SecNetworks Finset

/-! ## Label procedures for a complete code -/

/-- A layout with its list of code words replaced. -/
def Lay.withCodes (d : Lay) (cs : List (List Bool)) : Lay := ((d.1.1, (d.1.2.1, cs)), d.2)

section ProcsW

variable {Ctx : Type} (lay : Ctx → Lay) (par : Ctx × (ℕ × List Bool) → Bool)

/-- Membership for a complete code: the right length. -/
def memW (x : Ctx × WQ) : Bool := decide (x.2.2.length = (lay x.1).len x.2.1)

variable [HasSize Ctx]

/-- **The procedures of a label-sharing network with a complete code**: `labelProcs` with the
membership procedure `memW`. -/
def labelProcsW (Tp : Stepped (Ctx × WQ) ℤ) : Procs Ctx :=
  { labelProcs lay par Tp with mem := Stepped.ofFun (memW lay) }

end ProcsW

namespace LabelSystem

variable {g : ℕ} {K R L : Type} [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
  [Fintype L] [DecidableEq L] (X : LabelSystem g K R L) {w : ℕ} (C : LabelCode L w)
  {Ctx : Type} {lay : Ctx → Lay} {par : Ctx × (ℕ × List Bool) → Bool}

theorem length_blk {z : List Bool} {i : ℕ} (h : (i + 1) * w ≤ z.length) : (blk w z i).length = w := by
  unfold blk
  rw [List.length_take, List.length_drop]
  rw [Nat.succ_mul] at h
  omega

/-- With a complete code, every string of length `len a` is a setting of `a`. -/
theorem mem_S_of_length (hC : ∀ u : List Bool, u.length = w → ∃ l, C.enc l = u) (a : Fin g)
    {z : List Bool} (hz : z.length = (X.net C).len a) : z ∈ (X.net C).S a := by
  refine (X.mem_S_iff C a z).2 ⟨hz, fun i hi => hC _ (length_blk ?_)⟩
  rw [hz]
  simp only [net]
  have : (i + 1) * w ≤ (X.incList a).length * w := Nat.mul_le_mul_right _ hi
  omega

variable [HasSize Ctx]

/-- **Definition 2(iii) for the procedures with a complete code** (as `labelProcs_give`). -/
theorem labelProcsW_give (hC : ∀ u : List Bool, u.length = w → ∃ l, C.enc l = u)
    (Tp : Stepped (Ctx × WQ) ℤ) {c : Ctx} {P B τ S : ℕ} {cs : List (List Bool)}
    (hN : (X.net C).Is P B) (hD : X.Describes C P B ((lay c).withCodes cs)) (hp : X.ParSpec C par c)
    (hT : X.TSpec C Tp c τ S) (hτ : 1 ≤ τ) :
    (labelProcsW lay par Tp).Give c (X.net C) P B τ (S + size c + 2 * g + 4 * P + 8) := by
  have hpr : ∀ (a b : Fin g), a ≠ b → ∀ x ∈ X.locSet a,
      projF lay par c a.val b.val (X.enc C a x) = X.proj C a b x := fun a b hab x hx =>
    X.projF_eq (lay := fun c' => (lay c').withCodes cs) C hD hp hab hx
  exact {
  P_eq := hD.P_eq
  B_eq := hD.B_eq
  len_eq := fun a => by
    show (lay c).len a.val = _
    rw [show (lay c).len a.val = ((lay c).withCodes cs).len a.val from rfl]
    simp [Lay.len, hD.na_eq a, hD.nh_eq a, hD.w_eq, net]
  cap_eq := fun a b hab => by
    show (lay c).cap a.val b.val = _
    rw [show (lay c).cap a.val b.val = ((lay c).withCodes cs).cap a.val b.val from rfl]
    simp [Lay.cap, hD.pair_eq a b hab, hD.w_eq, net, pairData]
  mem_runs := fun a z hz => by
    have h := Stepped.ofFun_runs (memW lay) (c, (a.val, z))
    have hl : (lay c).len a.val = (X.net C).len a := by
      rw [show (lay c).len a.val = ((lay c).withCodes cs).len a.val from rfl]
      simp [Lay.len, hD.na_eq a, hD.nh_eq a, hD.w_eq, net]
    have e : memW lay (c, (a.val, z)) = decide (z ∈ (X.net C).S a) := by
      simp only [memW, hl, hz, decide_true, X.mem_S_of_length C hC a hz]
    rw [e] at h
    refine h.mono hτ ?_
    have h1 := LabelSystem.size_fin' a
    have h2 := hN.len_le a
    have h3 : size (decide (z ∈ (X.net C).S a)) = 1 := rfl
    simp only [size_prod, size_word, hz, h3] at *
    omega
  W_runs := fun a z hz => by
    obtain ⟨x, hx, rfl⟩ := (X.mem_S C).1 hz
    have h := hT a x hx
    have e : (X.net C).W a (X.enc C a x) = X.T a x.1 x.2 := by
      simp only [net, X.dec_enc C hx]
    rw [e]
    exact h.mono le_rfl (by omega)
  Ψ_runs := fun a b hab z hz z' hz' => by
    obtain ⟨x, hx, rfl⟩ := (X.mem_S C).1 hz
    obtain ⟨x', hx', rfl⟩ := (X.mem_S C).1 hz'
    have h := Stepped.ofFun_runs (psiF lay par) (c, ((a.val, b.val), (X.enc C a x, X.enc C b x')))
    have e : psiF lay par (c, ((a.val, b.val), (X.enc C a x, X.enc C b x'))) =
        (X.net C).Ψ a b (X.enc C a x) (X.enc C b x') := by
      simp only [psiF, net, X.dec_enc C hx, X.dec_enc C hx', hpr a b hab x hx,
        hpr b a (Ne.symm hab) x' hx']
    rw [e] at h
    refine h.mono hτ ?_
    have h1 := LabelSystem.size_fin' a
    have h1' := size_fin' b
    have h2 := hN.len_le a
    have h2' := hN.len_le b
    have h3 : size ((X.net C).Ψ a b (X.enc C a x) (X.enc C b x')) ≤ 2 := size_boole _
    have h4 := X.length_enc C a x
    have h4' := X.length_enc C b x'
    simp only [size_prod, size_word] at *
    omega
  f_runs := fun a b hab z hz θ hθ => by
    obtain ⟨x, hx, rfl⟩ := (X.mem_S C).1 hz
    have h := Stepped.ofFun_runs (fF lay par) (c, ((a.val, b.val), (X.enc C a x, θ)))
    have e : fF lay par (c, ((a.val, b.val), (X.enc C a x, θ))) = (X.net C).f a b (X.enc C a x) θ := by
      simp only [fF, net, X.dec_enc C hx, hpr a b hab x hx]
    rw [e] at h
    refine h.mono hτ ?_
    have h1 := LabelSystem.size_fin' a
    have h1' := size_fin' b
    have h2 := hN.len_le a
    have h3 : size ((X.net C).f a b (X.enc C a x) θ) ≤ 2 := size_boole _
    have h4 := X.length_enc C a x
    have h5 : θ.length = (X.net C).c a b := mem_words.1 hθ
    have h6 := X.c_le C hN hab
    simp only [size_prod, size_word] at *
    omega }

/-- **The network with a complete code is a network given by `labelProcsW`** (Definition 2). -/
theorem labelProcsW_isNet (hC : ∀ u : List Bool, u.length = w → ∃ l, C.enc l = u)
    (Tp : Stepped (Ctx × WQ) ℤ) {c : Ctx} {P B τ S : ℕ} {cs : List (List Bool)}
    (hN : (X.net C).Is P B) (hD : X.Describes C P B ((lay c).withCodes cs)) (hp : X.ParSpec C par c)
    (hT : X.TSpec C Tp c τ S) (hτ : 1 ≤ τ) :
    IsNetwork (labelProcsW lay par Tp) c (X.net C) P B τ (S + size c + 2 * g + 4 * P + 8) :=
  ⟨hN, hτ, X.labelProcsW_give C hC Tp hN hD hp hT hτ⟩

end LabelSystem

section KeepsW

variable {Ctx : Type} [Enc Ctx] [HasSize Ctx] [Carried Ctx] {lay : Ctx → Lay}
  {par : Ctx × (ℕ × List Bool) → Bool}

theorem memW_polyT (hlay : PolyT lay) : PolyT (memW lay) := by
  unfold memW
  fun_prop

/-- The procedures with a complete code: unary numbers, polynomial-time steps. -/
theorem labelProcsW_keeps (hlay : PolyT lay) (hpar : PolyT par) {Tp : Stepped (Ctx × WQ) ℤ}
    (hT : Nonempty (IsPolyT Tp)) : (labelProcsW lay par Tp).Keeps where
  len := Lay.len_unary (d := fun p : Ctx × ℕ => lay p.1) (by fun_prop) (by fun_prop)
  cap := Lay.cap_unary (d := fun p : Ctx × ℕ × ℕ => lay p.1) (by fun_prop) (by fun_prop) (by fun_prop)
  mem := ⟨IsPolyT.ofFun (memW_polyT hlay)⟩
  W := hT
  Ψ := ⟨IsPolyT.ofFun (psiF_polyT hlay hpar)⟩
  f := ⟨IsPolyT.ofFun (fF_polyT hlay hpar)⟩

theorem labelProcsW_P (hlay : PolyT lay) {Tp : Stepped (Ctx × WQ) ℤ} : Unary (labelProcsW lay par Tp).P :=
  Lay.P_unary hlay

theorem labelProcsW_B (hlay : PolyT lay) {Tp : Stepped (Ctx × WQ) ℤ} : Unary (labelProcsW lay par Tp).B :=
  Lay.B_unary hlay

end KeepsW

end EthFollowup.ExactHC

namespace EthFollowup.Factoring

open Groundwork Groundwork.Prog QueryMachines Eight.SecNetworks Finset EthFollowup.ExactHC

/-- **Every `W`-bit word is a code word of `labCode n`.** -/
theorem labCode_complete (n : ℕ) :
    ∀ u : List Bool, u.length = Nat.clog 2 (2 ^ W n - 1 + 1) → ∃ l, (labCode n).enc l = u := by
  intro u hu
  have hlt : ofWord u < 2 ^ W n - 1 + 1 := by
    rw [two_pow_W_sub_add]
    have := ofWord_lt u
    rw [hu, clog_W] at this
    exact this
  refine ⟨⟨ofWord u, hlt⟩, ?_⟩
  show toWord (Nat.clog 2 (2 ^ W n - 1 + 1)) (ofWord u) = u
  rw [← hu, toWord_ofWord]

/-! ## The parameters as data -/

/-- The parameters of `n` as numbers and ranges:
`((ℓ1, ℓ2), (L1, L2)), ((b, 2^b), (M, iL)), (W in unary, ω-table), ((⟦ℓ1⟧, ⟦ℓ2⟧), (⟦L1⟧, ⟦L2⟧)),
(⟦b⟧, (⟦numWires⟧, ⟦numVerts⟧))`, where `⟦k⟧ = List.range k`. -/
abbrev Prm : Type :=
  ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ)) × (List Unit × List ℕ) ×
    ((List ℕ × List ℕ) × (List ℕ × List ℕ)) × (List ℕ × (List ℕ × List ℕ))

namespace Prm

variable (p : Prm)

def l1 : ℕ := p.1.1.1
def l2 : ℕ := p.1.1.2
def L1 : ℕ := p.1.2.1
def L2 : ℕ := p.1.2.2
def b : ℕ := p.2.1.1.1
def pb : ℕ := p.2.1.1.2
def M : ℕ := p.2.1.2.1
def iL : ℕ := p.2.1.2.2
def uW : List Unit := p.2.2.1.1
/-- The wire width `W`. -/
def W : ℕ := p.uW.length
def wT : List ℕ := p.2.2.1.2
def rl1 : List ℕ := p.2.2.2.1.1.1
def rl2 : List ℕ := p.2.2.2.1.1.2
def rL1 : List ℕ := p.2.2.2.1.2.1
def rL2 : List ℕ := p.2.2.2.1.2.2
def rb : List ℕ := p.2.2.2.2.1
def rW : List ℕ := p.2.2.2.2.2.1
def rV : List ℕ := p.2.2.2.2.2.2
/-- `ℓ = ℓ1·ℓ2`. -/
def l : ℕ := p.l1 * p.l2
/-- `nA = L1·ℓ2`. -/
def nA : ℕ := p.L1 * p.l2
/-- `nF = L1·L2`. -/
def nF : ℕ := p.L1 * p.L2
/-- `Kc = L1 + ℓ1·L2`. -/
def Kc : ℕ := p.L1 + p.l1 * p.L2

end Prm

/-- The table of the powers `ω^e = 2^{wE n e}`, `e < L1`. -/
def wTab (n : ℕ) : List ℕ := (List.range (L1 n)).map (wP n)

/-- **The parameters of `n`.** -/
def prmOf (n : ℕ) : Prm :=
  (((ℓ1 n, ℓ2 n), (L1 n, L2 n)), ((b n, 2 ^ b n), (M n, iL n)), (List.replicate (W n) (), wTab n),
    ((List.range (ℓ1 n), List.range (ℓ2 n)), (List.range (L1 n), List.range (L2 n))),
    (List.range (b n), (List.range (numWires n), List.range (numVerts n))))

section PrmOf
variable (n : ℕ)
@[simp] theorem prmOf_l1 : (prmOf n).l1 = ℓ1 n := rfl
@[simp] theorem prmOf_l2 : (prmOf n).l2 = ℓ2 n := rfl
@[simp] theorem prmOf_L1 : (prmOf n).L1 = L1 n := rfl
@[simp] theorem prmOf_L2 : (prmOf n).L2 = L2 n := rfl
@[simp] theorem prmOf_b : (prmOf n).b = b n := rfl
@[simp] theorem prmOf_pb : (prmOf n).pb = 2 ^ b n := rfl
@[simp] theorem prmOf_M : (prmOf n).M = M n := rfl
@[simp] theorem prmOf_iL : (prmOf n).iL = iL n := rfl
@[simp] theorem prmOf_uW : (prmOf n).uW = List.replicate (W n) () := rfl
@[simp] theorem prmOf_W : (prmOf n).W = W n := List.length_replicate
@[simp] theorem prmOf_wT : (prmOf n).wT = wTab n := rfl
@[simp] theorem prmOf_rl1 : (prmOf n).rl1 = List.range (ℓ1 n) := rfl
@[simp] theorem prmOf_rl2 : (prmOf n).rl2 = List.range (ℓ2 n) := rfl
@[simp] theorem prmOf_rL1 : (prmOf n).rL1 = List.range (L1 n) := rfl
@[simp] theorem prmOf_rL2 : (prmOf n).rL2 = List.range (L2 n) := rfl
@[simp] theorem prmOf_rb : (prmOf n).rb = List.range (b n) := rfl
@[simp] theorem prmOf_rW : (prmOf n).rW = List.range (numWires n) := rfl
@[simp] theorem prmOf_rV : (prmOf n).rV = List.range (numVerts n) := rfl
@[simp] theorem prmOf_l : (prmOf n).l = ℓ n := rfl
@[simp] theorem prmOf_nA : (prmOf n).nA = nA n := rfl
@[simp] theorem prmOf_nF : (prmOf n).nF = nF n := rfl
@[simp] theorem prmOf_Kc : (prmOf n).Kc = Kc n := rfl
end PrmOf

namespace MP

/-! ## The pipeline functions on the parameter data -/

theorem sum_range_list (k : ℕ) (f : ℕ → ℕ) : ∑ i ∈ range k, f i = ((List.range k).map f).sum := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]; simp

theorem getD_map_range' {β : Type} (f : ℕ → β) {k i : ℕ} (hi : i < k) (d : β) :
    ((List.range k).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- Division, remainder and division by a power of two, as atoms for `fun_prop`. -/
def dv (a b : ℕ) : ℕ := a / b
/-- Remainder (atom). -/
def md (a b : ℕ) : ℕ := a % b
/-- `a / 2^e` (atom). -/
def dvp (a e : ℕ) : ℕ := a / 2 ^ e

/-- `ω^e`, read from the table (the exponent reduced mod `L1`). -/
def wq (p : Prm) (e : ℕ) : ℕ := p.wT.getD (md e p.L1) 0

theorem wq_eq (n e : ℕ) : wq (prmOf n) e = wP n e := by
  unfold wq md
  rw [prmOf_wT, prmOf_L1, wTab, getD_map_range' _ (Nat.mod_lt _ (by have := two_le_L1 n; omega))]
  simp only [wP, wE, Nat.mod_mod]

def rowE (p : Prm) (x : ℕ → ℕ → ℕ) (s i2 : ℕ) : ℕ :=
  md (p.rl1.map fun i1 => x i1 i2 * wq p (i1 * s)).sum p.M
def colE (p : Prm) (A : ℕ → ℕ → ℕ) (s t : ℕ) : ℕ :=
  md (p.rl2.map fun i2 => A s i2 * wq p (i2 * t)).sum p.M
def invColE (p : Prm) (C : ℕ → ℕ → ℕ) (s u : ℕ) : ℕ :=
  md (p.iL * (p.rL2.map fun t => C s t * wq p ((p.L2 - u) * t)).sum) p.M
def invRowE (p : Prm) (E : ℕ → ℕ → ℕ) (a u : ℕ) : ℕ :=
  md (p.iL * (p.rL1.map fun s => E s u * wq p ((p.L1 - a) * s)).sum) p.M
def convE (p : Prm) (C : ℕ → ℕ → ℕ) (k : ℕ) : ℕ :=
  (p.rL1.map fun a => (p.rL2.map fun u => if a + p.l1 * u = k then C a u else 0).sum).sum
def patE (p : Prm) (pt : List (Option Bool)) (i x : ℕ) : Bool :=
  p.rb.all fun j => obit (pt.getD (p.b * i + j) none) (x.testBit j)
def carryE (p : Prm) (Nl c rin rout : ℕ) : Bool :=
  decide (Nl ≤ c + rin) && decide (md (c + rin - Nl) p.pb = 0) && rout == dv (c + rin - Nl) p.pb
def NkE (p : Prm) (N k : ℕ) : ℕ := md (dvp N (p.b * k)) p.pb

section Eqs
variable (n : ℕ)

theorem rowE_eq (x : ℕ → ℕ → ℕ) (s i2 : ℕ) : rowE (prmOf n) x s i2 = rowDFT n x s i2 := by
  simp only [rowE, rowDFT, md, prmOf_rl1, prmOf_M, wq_eq, sum_range_list]
theorem colE_eq (A : ℕ → ℕ → ℕ) (s t : ℕ) : colE (prmOf n) A s t = colDFT n A s t := by
  simp only [colE, colDFT, md, prmOf_rl2, prmOf_M, wq_eq, sum_range_list]
theorem invColE_eq (C : ℕ → ℕ → ℕ) (s u : ℕ) : invColE (prmOf n) C s u = invCol n C s u := by
  simp only [invColE, invCol, md, prmOf_rL2, prmOf_M, prmOf_iL, prmOf_L2, wq_eq, sum_range_list]
theorem invRowE_eq (E : ℕ → ℕ → ℕ) (a u : ℕ) : invRowE (prmOf n) E a u = invRow n E a u := by
  simp only [invRowE, invRow, md, prmOf_rL1, prmOf_M, prmOf_iL, prmOf_L1, wq_eq, sum_range_list]
theorem convE_eq (C : ℕ → ℕ → ℕ) (k : ℕ) : convE (prmOf n) C k = convCoeff n C k := by
  unfold convE convCoeff
  rw [prmOf_rL1, prmOf_rL2, prmOf_l1]
  simp only [sum_range_list]
theorem patE_eq (pt : List (Option Bool)) (i x : ℕ) : patE (prmOf n) pt i x = patOK n pt i x := rfl
theorem carryE_eq (Nl c rin rout : ℕ) : carryE (prmOf n) Nl c rin rout = carryOK n Nl c rin rout := rfl
theorem NkE_eq (N k : ℕ) : NkE (prmOf n) N k = Nk n N k := rfl

end Eqs

/-! ## The checks with the wire values given by index -/

section Checks
variable (p : Prm) (N : ℕ) (pt : List (Option Bool)) (xr : ℕ → ℕ)

def cellPE (i1 i2 : ℕ) : Bool :=
  decide (xr (i1 + p.l1 * i2) < p.pb) && patE p pt (i1 + p.l1 * i2) (xr (i1 + p.l1 * i2))
def cellQE (i1 i2 : ℕ) : Bool := decide (xr (p.l + (i1 + p.l1 * i2)) < p.pb)
def rowPE (i2 : ℕ) : Bool := p.rL1.all fun s =>
  xr (2 * p.l + (s + p.L1 * i2)) == rowE p (fun i1 i2 => xr (i1 + p.l1 * i2)) s i2
def rowQE (i2 : ℕ) : Bool := p.rL1.all fun s =>
  xr (2 * p.l + p.nA + (s + p.L1 * i2)) == rowE p (fun i1 i2 => xr (p.l + (i1 + p.l1 * i2))) s i2
def colPE (s : ℕ) : Bool := p.rL2.all fun t =>
  xr (2 * p.l + 2 * p.nA + (s + p.L1 * t)) == colE p (fun s i2 => xr (2 * p.l + (s + p.L1 * i2))) s t
def colQE (s : ℕ) : Bool := p.rL2.all fun t =>
  xr (2 * p.l + 2 * p.nA + p.nF + (s + p.L1 * t)) ==
    colE p (fun s i2 => xr (2 * p.l + p.nA + (s + p.L1 * i2))) s t
def mulE (s t : ℕ) : Bool :=
  xr (2 * p.l + 2 * p.nA + 2 * p.nF + (s + p.L1 * t)) ==
    md (xr (2 * p.l + 2 * p.nA + (s + p.L1 * t)) * xr (2 * p.l + 2 * p.nA + p.nF + (s + p.L1 * t))) p.M
def icolE (s : ℕ) : Bool := p.rL2.all fun u =>
  xr (2 * p.l + 2 * p.nA + 3 * p.nF + (s + p.L1 * u)) ==
    invColE p (fun s t => xr (2 * p.l + 2 * p.nA + 2 * p.nF + (s + p.L1 * t))) s u
def irowE (u : ℕ) : Bool := p.rL1.all fun a =>
  xr (2 * p.l + 2 * p.nA + 4 * p.nF + (a + p.L1 * u)) ==
    invRowE p (fun s u => xr (2 * p.l + 2 * p.nA + 3 * p.nF + (s + p.L1 * u))) a u
def carryVE (k : ℕ) : Bool :=
  carryE p (NkE p N k) (convE p (fun a u => xr (2 * p.l + 2 * p.nA + 4 * p.nF + (a + p.L1 * u))) k)
    (if k = 0 then 0 else xr (2 * p.l + 2 * p.nA + 5 * p.nF + (k - 1)))
    (if k + 1 < p.Kc then xr (2 * p.l + 2 * p.nA + 5 * p.nF + k) else 0)

/-- **The check of the vertex with index `j`**, the value of wire `k` being `xr k`. -/
def chkE (j : ℕ) : Bool :=
  if j < p.l then cellPE p pt xr (md j p.l1) (dv j p.l1)
  else if j < 2 * p.l then cellQE p xr (md (j - p.l) p.l1) (dv (j - p.l) p.l1)
  else if j < 2 * p.l + p.l2 then rowPE p xr (j - 2 * p.l)
  else if j < 2 * p.l + 2 * p.l2 then rowQE p xr (j - (2 * p.l + p.l2))
  else if j < 2 * p.l + 2 * p.l2 + p.L1 then colPE p xr (j - (2 * p.l + 2 * p.l2))
  else if j < 2 * p.l + 2 * p.l2 + 2 * p.L1 then colQE p xr (j - (2 * p.l + 2 * p.l2 + p.L1))
  else if j < 2 * p.l + 2 * p.l2 + 2 * p.L1 + p.nF then
    mulE p xr (md (j - (2 * p.l + 2 * p.l2 + 2 * p.L1)) p.L1) (dv (j - (2 * p.l + 2 * p.l2 + 2 * p.L1)) p.L1)
  else if j < 2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF then icolE p xr (j - (2 * p.l + 2 * p.l2 + 2 * p.L1 + p.nF))
  else if j < 2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF + p.L2 then
    irowE p xr (j - (2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF))
  else carryVE p N xr (j - (2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF + p.L2))

end Checks

section ChecksEq
variable (n N : ℕ) (pt : List (Option Bool)) (xr : ℕ → ℕ)

/-- The wire values `xr (wireIdx n d)`. -/
abbrev xw (d : WD) : ℕ := xr (wireIdx n d)

theorem cellPE_eq (i1 i2 : ℕ) : cellPE (prmOf n) pt xr i1 i2 = chk n N pt (xw n xr) (.cellP i1 i2) := rfl
theorem cellQE_eq (i1 i2 : ℕ) : cellQE (prmOf n) xr i1 i2 = chk n N pt (xw n xr) (.cellQ i1 i2) := rfl
theorem rowPE_eq (i2 : ℕ) : rowPE (prmOf n) xr i2 = chk n N pt (xw n xr) (.rowP i2) := by
  simp only [rowPE, rowE_eq]; rfl
theorem rowQE_eq (i2 : ℕ) : rowQE (prmOf n) xr i2 = chk n N pt (xw n xr) (.rowQ i2) := by
  simp only [rowQE, rowE_eq]; rfl
theorem colPE_eq (s : ℕ) : colPE (prmOf n) xr s = chk n N pt (xw n xr) (.colP s) := by
  simp only [colPE, colE_eq]; rfl
theorem colQE_eq (s : ℕ) : colQE (prmOf n) xr s = chk n N pt (xw n xr) (.colQ s) := by
  simp only [colQE, colE_eq]; rfl
theorem mulE_eq (s t : ℕ) : mulE (prmOf n) xr s t = chk n N pt (xw n xr) (.mul s t) := rfl
theorem icolE_eq (s : ℕ) : icolE (prmOf n) xr s = chk n N pt (xw n xr) (.icol s) := by
  simp only [icolE, invColE_eq]; rfl
theorem irowE_eq (u : ℕ) : irowE (prmOf n) xr u = chk n N pt (xw n xr) (.irow u) := by
  simp only [irowE, invRowE_eq]; rfl
theorem carryVE_eq (k : ℕ) : carryVE (prmOf n) N xr k = chk n N pt (xw n xr) (.carry k) := by
  simp only [carryVE, convE_eq]; rfl

/-- **The numeric check is the check of `vertOf n j`.** -/
theorem chkE_eq (j : ℕ) : chkE (prmOf n) N pt xr j = chk n N pt (xw n xr) (vertOf n j) := by
  unfold chkE vertOf
  rw [prmOf_l, prmOf_l1, prmOf_l2, prmOf_L1, prmOf_L2, prmOf_nF]
  split_ifs
  · exact cellPE_eq n N pt xr _ _
  · exact cellQE_eq n N pt xr _ _
  · exact rowPE_eq n N pt xr _
  · exact rowQE_eq n N pt xr _
  · exact colPE_eq n N pt xr _
  · exact colQE_eq n N pt xr _
  · exact mulE_eq n N pt xr _ _
  · exact icolE_eq n N pt xr _
  · exact irowE_eq n N pt xr _
  · exact carryVE_eq n N pt xr _

end ChecksEq

/-! ## Clusters, ends, pairs on the parameter data -/

section Wires
variable (p : Prm) (g : ℕ)

/-- **The cluster of the vertex with index `j`** (as `clus n g (vertOf n j)`). -/
def clusJ (j : ℕ) : ℕ :=
  if j < p.l then VB.vbN p.l g (md j p.l1 + p.l1 * (dv j p.l1))
  else if j < 2 * p.l then VB.vbN p.l g (md (j - p.l) p.l1 + p.l1 * (dv (j - p.l) p.l1))
  else if j < 2 * p.l + p.l2 then VB.vbN p.l2 g (j - 2 * p.l)
  else if j < 2 * p.l + 2 * p.l2 then VB.vbN p.l2 g (j - (2 * p.l + p.l2))
  else if j < 2 * p.l + 2 * p.l2 + p.L1 then VB.vbN p.L1 g (j - (2 * p.l + 2 * p.l2))
  else if j < 2 * p.l + 2 * p.l2 + 2 * p.L1 then VB.vbN p.L1 g (j - (2 * p.l + 2 * p.l2 + p.L1))
  else if j < 2 * p.l + 2 * p.l2 + 2 * p.L1 + p.nF then
    VB.vbN p.nF g (md (j - (2 * p.l + 2 * p.l2 + 2 * p.L1)) p.L1 +
      p.L1 * (dv (j - (2 * p.l + 2 * p.l2 + 2 * p.L1)) p.L1))
  else if j < 2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF then
    VB.vbN p.L1 g (j - (2 * p.l + 2 * p.l2 + 2 * p.L1 + p.nF))
  else if j < 2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF + p.L2 then
    VB.vbN p.L2 g (j - (2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF))
  else VB.vbN p.Kc g (j - (2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF + p.L2))

/-- The base index of the carry vertices. -/
def cOff : ℕ := 2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF + p.L2

/-- **The indices of the two end vertices of the wire with index `k`** (as
`vertIdx n (ends n (wireOf n k))`). -/
def endE (k : ℕ) : ℕ × ℕ :=
  if k < p.l then (md k p.l1 + p.l1 * (dv k p.l1), 2 * p.l + dv k p.l1)
  else if k < 2 * p.l then
    (p.l + (md (k - p.l) p.l1 + p.l1 * (dv (k - p.l) p.l1)), 2 * p.l + p.l2 + dv (k - p.l) p.l1)
  else if k < 2 * p.l + p.nA then
    (2 * p.l + dv (k - 2 * p.l) p.L1, 2 * p.l + 2 * p.l2 + md (k - 2 * p.l) p.L1)
  else if k < 2 * p.l + 2 * p.nA then
    (2 * p.l + p.l2 + dv (k - (2 * p.l + p.nA)) p.L1, 2 * p.l + 2 * p.l2 + p.L1 + md (k - (2 * p.l + p.nA)) p.L1)
  else if k < 2 * p.l + 2 * p.nA + p.nF then
    (2 * p.l + 2 * p.l2 + md (k - (2 * p.l + 2 * p.nA)) p.L1,
      2 * p.l + 2 * p.l2 + 2 * p.L1 + (md (k - (2 * p.l + 2 * p.nA)) p.L1 + p.L1 * (dv (k - (2 * p.l + 2 * p.nA)) p.L1)))
  else if k < 2 * p.l + 2 * p.nA + 2 * p.nF then
    (2 * p.l + 2 * p.l2 + p.L1 + md (k - (2 * p.l + 2 * p.nA + p.nF)) p.L1,
      2 * p.l + 2 * p.l2 + 2 * p.L1 + (md (k - (2 * p.l + 2 * p.nA + p.nF)) p.L1 +
        p.L1 * (dv (k - (2 * p.l + 2 * p.nA + p.nF)) p.L1)))
  else if k < 2 * p.l + 2 * p.nA + 3 * p.nF then
    (2 * p.l + 2 * p.l2 + 2 * p.L1 + (md (k - (2 * p.l + 2 * p.nA + 2 * p.nF)) p.L1 +
        p.L1 * (dv (k - (2 * p.l + 2 * p.nA + 2 * p.nF)) p.L1)),
      2 * p.l + 2 * p.l2 + 2 * p.L1 + p.nF + md (k - (2 * p.l + 2 * p.nA + 2 * p.nF)) p.L1)
  else if k < 2 * p.l + 2 * p.nA + 4 * p.nF then
    (2 * p.l + 2 * p.l2 + 2 * p.L1 + p.nF + md (k - (2 * p.l + 2 * p.nA + 3 * p.nF)) p.L1,
      2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF + dv (k - (2 * p.l + 2 * p.nA + 3 * p.nF)) p.L1)
  else if k < 2 * p.l + 2 * p.nA + 5 * p.nF then
    (2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF + dv (k - (2 * p.l + 2 * p.nA + 4 * p.nF)) p.L1,
      2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF + p.L2 + (md (k - (2 * p.l + 2 * p.nA + 4 * p.nF)) p.L1 +
        p.l1 * (dv (k - (2 * p.l + 2 * p.nA + 4 * p.nF)) p.L1)))
  else (2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF + p.L2 + (k - (2 * p.l + 2 * p.nA + 5 * p.nF)),
    2 * p.l + 2 * p.l2 + 3 * p.L1 + p.nF + p.L2 + (k - (2 * p.l + 2 * p.nA + 5 * p.nF) + 1))

/-- The lower node of the wire with index `k`. -/
def wLoE (k : ℕ) : ℕ := (lohi g (clusJ p g (endE p k).1) (clusJ p g (endE p k).2)).1
/-- The upper node of the wire with index `k`. -/
def wHiE (k : ℕ) : ℕ := (lohi g (clusJ p g (endE p k).1) (clusJ p g (endE p k).2)).2

/-- The indices of the wires incident to node `a`, increasing. -/
def incE (a : ℕ) : List ℕ := p.rW.filter fun k => decide (wLoE p g k = a ∨ wHiE p g k = a)

/-- The places, among the wires incident to `a`, of the wires on the pair `{a, c}`. -/
def pairE (a c : ℕ) : List ℕ :=
  (p.rW.filter fun k => decide ((wLoE p g k = a ∧ wHiE p g k = c) ∨ (wLoE p g k = c ∧ wHiE p g k = a))).map
    fun k => (incE p g a).idxOf k

end Wires

section WiresEq
variable (n g : ℕ)

theorem clusJ_eq (j : ℕ) : clusJ (prmOf n) g j = clus n g (vertOf n j) := by
  unfold clusJ vertOf
  rw [prmOf_l, prmOf_l1, prmOf_l2, prmOf_L1, prmOf_L2, prmOf_nF, prmOf_Kc]
  split_ifs <;> rfl

theorem endE_eq (k : ℕ) :
    endE (prmOf n) k = (vertIdx n (ends n (wireOf n k)).1, vertIdx n (ends n (wireOf n k)).2) := by
  unfold endE wireOf
  rw [prmOf_l, prmOf_l1, prmOf_l2, prmOf_L1, prmOf_L2, prmOf_nF, prmOf_nA]
  split_ifs <;> rfl

theorem wLoE_eq {k : ℕ} (hk : k < numWires n) : wLoE (prmOf n) g k = wLo n g (wireOf n k) := by
  have h := ends_valid (wireOf_valid hk)
  unfold wLoE wLo
  rw [endE_eq, clusJ_eq, clusJ_eq, vertOf_vertIdx h.1, vertOf_vertIdx h.2]

theorem wHiE_eq {k : ℕ} (hk : k < numWires n) : wHiE (prmOf n) g k = wHi n g (wireOf n k) := by
  have h := ends_valid (wireOf_valid hk)
  unfold wHiE wHi
  rw [endE_eq, clusJ_eq, clusJ_eq, vertOf_vertIdx h.1, vertOf_vertIdx h.2]

theorem map_val_finRange' (G : ℕ) : (List.finRange G).map Fin.val = List.range G :=
  List.ext_getElem (by simp) fun i h1 h2 => by simp

theorem idxOf_map_val {G : ℕ} (k : Fin G) :
    ∀ l : List (Fin G), (l.map Fin.val).idxOf k.val = l.idxOf k
  | [] => rfl
  | y :: l => by
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, idxOf_map_val k l]
    by_cases h : y = k
    · subst h; simp
    · have : y.val ≠ k.val := fun e => h (Fin.ext e)
      rw [beq_false_of_ne h, beq_false_of_ne this]

variable {n g} {N : ℕ} {pt : List (Option Bool)} (hg : 2 ≤ g)

theorem filter_val_eq (q : Fin (numWires n) → Prop) [DecidablePred q] (q' : ℕ → Prop) [DecidablePred q']
    (h : ∀ k : Fin (numWires n), q k ↔ q' k.val) :
    ((List.finRange (numWires n)).filter fun k => decide (q k)).map Fin.val =
      (List.range (numWires n)).filter fun k => decide (q' k) := by
  rw [← map_val_finRange', List.filter_map]
  congr 1
  refine List.filter_congr fun k _ => ?_
  simp only [Function.comp, h]

theorem incE_eq (a : Fin g) :
    incE (prmOf n) g a.val = ((mulSys n N pt g hg).incList a).map Fin.val := by
  unfold incE LabelSystem.incList
  rw [prmOf_rW]
  refine (filter_val_eq _ _ fun k => ?_).symm
  rw [mulSys_inc, wLoE_eq n g k.2, wHiE_eq n g k.2]

theorem pairE_eq (a c : Fin g) :
    (pairE (prmOf n) g a.val c.val, ([] : List (Bool × ℕ))) = (mulSys n N pt g hg).pairData a c := by
  unfold pairE LabelSystem.pairData
  refine Prod.ext ?_ rfl
  simp only
  rw [incE_eq hg a, prmOf_rW]
  unfold LabelSystem.pairItems
  have e := filter_val_eq (n := n) (fun k => (mulSys n N pt g hg).OnPair a c k)
    (fun k => (wLoE (prmOf n) g k = a.val ∧ wHiE (prmOf n) g k = c.val) ∨
      (wLoE (prmOf n) g k = c.val ∧ wHiE (prmOf n) g k = a.val)) fun k => by
    simp only [LabelSystem.OnPair, mulSys, Fin.ext_iff, wLoE_eq n g k.2, wHiE_eq n g k.2]
  rw [← e, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, idxOf_map_val]
  rfl

end WiresEq

end MP

open MP

/-! ## The layout and the context -/

/-- **The layout of the multiplication network**: `P` and `B = 1` in unary, the code width `W`, no
code list (the code is complete), per node the incident wires in unary, per ordered pair the places
of the shared wires. -/
def layM (p : Prm) (g P : ℕ) : Lay :=
  (((List.replicate P (), [()]), (p.uW, [])),
    ((List.range g).map fun a => ((incE p g a).map fun _ => (), []),
      (List.range g).map fun a => (List.range g).map fun c => (pairE p g a c, [])))

/-- The full list of code words (only used in proofs). -/
noncomputable def codesM (n : ℕ) : List (List Bool) :=
  (Finset.univ : Finset (Lab n)).toList.map (labCode n).enc

/-- **The layout describes the network** (with the full code list substituted). -/
theorem layM_describes {n N : ℕ} {pt : List (Option Bool)} {g : ℕ} (hg : 2 ≤ g) (P : ℕ) :
    (mulSys n N pt g hg).Describes (labCode n) P 1 ((layM (prmOf n) g P).withCodes (codesM n)) where
  P_eq := by simp [Lay.P, layM, Lay.withCodes]
  B_eq := rfl
  w_eq := by simp [Lay.w, layM, Lay.withCodes, clog_W, Prm.uW, prmOf]
  codes_iff u := by simp [Lay.codes, Lay.withCodes, codesM]
  na_eq a := by
    simp only [Lay.na, Lay.node, layM, Lay.withCodes]
    rw [getD_map_range' _ a.2, List.length_map, incE_eq (N := N) (pt := pt) hg a, List.length_map]
  nh_eq a := by
    simp only [Lay.nh, Lay.node, layM, Lay.withCodes]
    rw [getD_map_range' _ a.2]
    rfl
  pair_eq a c _ := by
    simp only [Lay.pair, layM, Lay.withCodes]
    rw [getD_map_range' _ a.2, getD_map_range' _ c.2]
    exact pairE_eq hg a c

/-- **The context**: the layout, the parameters, `(g, N)`, the pattern, per node the incident wires. -/
abbrev MCtx : Type := Lay × (Prm × ((ℕ × ℕ) × (List (Option Bool) × List (List ℕ))))

/-- The context of the parameters `p`, `g` nodes, `N`, the pattern `pt`, the bound `P`. -/
def mctxOf (p : Prm) (g N : ℕ) (pt : List (Option Bool)) (P : ℕ) : MCtx :=
  (layM p g P, (p, ((g, N), (pt, (List.range g).map (incE p g)))))

/-! ## The table procedure -/

/-- The value of wire `k` read from a setting `z` (wires `inc`, width `Wd`). -/
def xz (Wd : ℕ) (inc : List ℕ) (z : List Bool) (k : ℕ) : ℕ := ofWord (blk Wd z (inc.idxOf k))

/-- All checks of the vertices of cluster `a`, the wire values read from `z`. -/
def tabB (c : MCtx) (a : ℕ) (z : List Bool) : Bool :=
  c.2.1.rV.all fun j => !(decide (clusJ c.2.1 c.2.2.1.1 j = a)) ||
    chkE c.2.1 c.2.2.1.2 c.2.2.2.1 (xz c.2.1.W (c.2.2.2.2.getD a []) z) j

/-- The table entry. -/
def tabF (q : MCtx × WQ) : ℤ := if tabB q.1 q.2.1 q.2.2 = true then 1 else 0

/-- **The table procedure**: one step. -/
def mulTp : Stepped (MCtx × WQ) ℤ := Stepped.ofFun tabF

theorem blk_congr_w {w w' : ℕ} (h : w = w') (z : List Bool) (i : ℕ) : blk w z i = blk w' z i := by
  rw [h]

section TabEq
variable {n N : ℕ} {pt : List (Option Bool)} {g : ℕ} (hg : 2 ≤ g)

/-- The value of an incident wire, read from a setting. -/
theorem xz_enc (a : Fin g) (x : (Fin (numWires n) → Lab n) × (Empty → Bool)) (k : Fin (numWires n))
    (hk : (mulSys n N pt g hg).Inc a k) :
    xz (W n) (((mulSys n N pt g hg).incList a).map Fin.val) ((mulSys n N pt g hg).enc (labCode n) a x) k.val =
      (x.1 k).val := by
  have hmem : k ∈ (mulSys n N pt g hg).incList a := (mulSys n N pt g hg).mem_incList.2 hk
  unfold xz
  rw [idxOf_map_val, blk_congr_w (clog_W n).symm]
  unfold LabelSystem.enc
  rw [blk_encL (labCode n) x.1 _ _ _ (List.idxOf_lt_length_of_mem hmem), List.getElem_idxOf]
  show ofWord (toWord _ (x.1 k).val) = _
  refine ofWord_toWord ?_
  rw [clog_W]
  exact lt_of_lt_of_le (x.1 k).isLt (two_pow_W_sub_add n).le

/-- **The table procedure computes the table**: on a setting of `a`, `tabB` is `clusOK`. -/
theorem tabB_eq (P : ℕ) (a : Fin g) (x : (Fin (numWires n) → Lab n) × (Empty → Bool)) :
    tabB (mctxOf (prmOf n) g N pt P) a.val ((mulSys n N pt g hg).enc (labCode n) a x) =
      clusOK n N pt g a.val (val n x.1) := by
  have hinc : ((List.range g).map (incE (prmOf n) g)).getD a.val [] =
      ((mulSys n N pt g hg).incList a).map Fin.val := by
    rw [getD_map_range' _ a.2, incE_eq hg a]
  unfold tabB clusOK
  simp only [mctxOf, hinc, prmOf_rV, prmOf_W]
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  refine forall_congr' fun j => imp_congr_right fun hj => ?_
  simp only [clusJ_eq, chkE_eq, decide_eq_false_iff_not]
  by_cases hc : clus n g (vertOf n j) = a.val
  · simp only [hc, not_true_eq_false, false_or]
    rw [chk_agree (vertOf_valid hj) fun d hd hw => ?_]
    show xz (W n) _ _ (wireIdx n d) = val n x.1 d
    rw [val_of_valid _ hd]
    refine xz_enc hg a x ⟨wireIdx n d, wireIdx_lt hd⟩ ?_
    rw [mulSys_inc]
    simp only [wireOf_wireIdx hd]
    have hm := clus_ends_mem n g d
    rcases hw with e | e <;> rw [e, hc] at hm
    · exact hm.1.imp Eq.symm Eq.symm
    · exact hm.2.imp Eq.symm Eq.symm
  · simp only [hc, not_false_eq_true, true_or]

theorem tabF_eq (P : ℕ) (a : Fin g) (x : (Fin (numWires n) → Lab n) × (Empty → Bool)) :
    tabF (mctxOf (prmOf n) g N pt P, (a.val, (mulSys n N pt g hg).enc (labCode n) a x)) =
      (mulSys n N pt g hg).T a x.1 x.2 := by
  unfold tabF
  rw [tabB_eq hg P a x]
  rfl

/-- The state bound of the table procedure. -/
def SM (c : MCtx) (g P : ℕ) : ℕ := size c + g + 2 * P + 6

/-- **Definition 2(iii) for the tables**: one step, states of size `≤ SM`. -/
theorem mulSys_tspec (P : ℕ) (hP : ∀ a, ((mulSys n N pt g hg).net (labCode n)).len a ≤ P) :
    (mulSys n N pt g hg).TSpec (labCode n) mulTp (mctxOf (prmOf n) g N pt P) 1
      (SM (mctxOf (prmOf n) g N pt P) g P) := by
  intro a x _
  have h := Stepped.ofFun_runs tabF (mctxOf (prmOf n) g N pt P, (a.val, (mulSys n N pt g hg).enc (labCode n) a x))
  rw [tabF_eq hg P a x] at h
  refine h.mono le_rfl ?_
  have h1 := LabelSystem.size_fin' a
  have h2 := hP a
  have h3 : size ((mulSys n N pt g hg).T a x.1 x.2) ≤ 2 := by
    show size (mulT n N pt g a x.1) ≤ 2
    unfold mulT; exact LabelSystem.size_boole _
  have h4 := (mulSys n N pt g hg).length_enc (labCode n) a x
  have h5 := LabelSystem.size_word ((mulSys n N pt g hg).enc (labCode n) a x)
  have hs : size (mctxOf (prmOf n) g N pt P, (a.val, (mulSys n N pt g hg).enc (labCode n) a x)) =
      size (mctxOf (prmOf n) g N pt P) + (size a.val + size ((mulSys n N pt g hg).enc (labCode n) a x)) := rfl
  rw [hs]
  unfold SM
  omega

end TabEq

end EthFollowup.Factoring
