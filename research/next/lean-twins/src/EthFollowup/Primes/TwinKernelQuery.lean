/- Query encoding, polynomial-time reader and the counted-network package of
the doubled (twin) descriptor. -/
import EthFollowup.Primes.TwinKernelCount
import EthFollowup.Primes.CountKernelQuery

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace EthFollowup.Primes.TwinKernel
open Groundwork EthFollowup.ModP EthFollowup.Factoring EthFollowup.ExactHC Finset
open EthFollowup.Primes.CountKernel

/-! ## Query words -/

/-- 48 equal-width entries: the 24 entries of each copy. -/
def twinQueryData (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch) : List ℕ :=
  queryData P₁ br₁ ++ queryData P₂ br₂

def twinQuery (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch) : List Bool :=
  encodeList (twinQueryData P₁ br₁ P₂ br₂)

@[simp] theorem twinQueryData_length (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters)
    (br₂ : Branch) : (twinQueryData P₁ br₁ P₂ br₂).length = 48 := by
  simp [twinQueryData]

/-- Copy at block offset `o`; its bound is the input value plus `e`. -/
def readParams (e o : ℕ) (w π : List Bool) : Parameters where
  bound := Groundwork.ofWord w + e
  baseM := rdBlk 48 (o + 0) π
  baseN := rdBlk 48 (o + 1) π
  scale := rdBlk 48 (o + 2) π
  U k := rdBlk 48 (o + (3 + 3 * k.val)) π
  V k := rdBlk 48 (o + (4 + 3 * k.val)) π
  Q k := rdBlk 48 (o + (5 + 3 * k.val)) π

def readBr (o : ℕ) (π : List Bool) : Branch where
  unitD := decide (rdBlk 48 (o + 15) π = 1)
  neg k := decide (rdBlk 48 (o + (16 + k.val)) π = 1)
  imag k := decide (rdBlk 48 (o + (20 + k.val)) π = 1)

theorem rdBlk_twin_first (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch)
    (j : ℕ) (hj : j < 24) :
    rdBlk 48 (0 + j) (twinQuery P₁ br₁ P₂ br₂) = (queryData P₁ br₁).getD j 0 := by
  have h := rdBlk_encodeList (l := twinQueryData P₁ br₁ P₂ br₂) (j := j) (by simp; omega)
  rw [twinQueryData_length] at h
  rw [Nat.zero_add, twinQuery, h, twinQueryData, List.getD_append _ _ _ _ (by simp; omega)]

theorem rdBlk_twin_second (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch)
    (j : ℕ) (hj : j < 24) :
    rdBlk 48 (24 + j) (twinQuery P₁ br₁ P₂ br₂) = (queryData P₂ br₂).getD j 0 := by
  have h := rdBlk_encodeList (l := twinQueryData P₁ br₁ P₂ br₂) (j := 24 + j) (by simp; omega)
  rw [twinQueryData_length] at h
  rw [twinQuery, h, twinQueryData, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem readParams_of {P : Parameters} {e o : ℕ} {w π : List Bool} {br : Branch}
    (hN : Groundwork.ofWord w + e = P.bound)
    (h : ∀ j < 24, rdBlk 48 (o + j) π = (queryData P br).getD j 0) :
    readParams e o w π = P := by
  cases P
  unfold readParams
  congr 1
  · rw [h 0 (by decide)]; rfl
  · rw [h 1 (by decide)]; rfl
  · rw [h 2 (by decide)]; rfl
  all_goals funext k; fin_cases k <;> rw [h _ (by decide)] <;> rfl

theorem readBr_of {P : Parameters} {o : ℕ} {π : List Bool} {br : Branch}
    (h : ∀ j < 24, rdBlk 48 (o + j) π = (queryData P br).getD j 0) :
    readBr o π = br := by
  cases br with
  | mk unitD neg imag =>
    unfold readBr
    congr 1
    · rw [h 15 (by decide)]
      simp only [queryData, List.getD_cons_succ, List.getD_cons_zero]
      cases unitD <;> rfl
    · funext k
      fin_cases k <;> rw [h _ (by decide)] <;>
        simp only [queryData, List.getD_cons_succ, List.getD_cons_zero]
      all_goals split <;> simp_all
    · funext k
      fin_cases k <;> rw [h _ (by decide)] <;>
        simp only [queryData, List.getD_cons_succ, List.getD_cons_zero]
      all_goals split <;> simp_all

def twinReader (y : List Bool × List Bool) : LDesc :=
  twinActual (readParams 0 0 y.1 y.2) (readBr 0 y.2) (readParams 2 24 y.1 y.2) (readBr 24 y.2)
    y.1.length

/-- Exact doubled count, at any sufficient input length. -/
theorem twin_reader_query_count {P₁ P₂ : Parameters} {br₁ br₂ : Branch} {B : ℕ} (w : List Bool)
    (hN : Groundwork.ofWord w = P₁.bound) (hN₂ : P₂.bound = P₁.bound + 2)
    (hb₁ : BitBounds P₁ B) (hb₂ : BitBounds P₂ B) (hn : 5*B+2 ≤ w.length) :
    (twinReader (w, twinQuery P₁ br₁ P₂ br₂)).count w.length = twinValue P₁ br₁ P₂ br₂ := by
  unfold twinReader
  dsimp only
  rw [readParams_of (by rw [hN, Nat.add_zero]) (rdBlk_twin_first P₁ br₁ P₂ br₂),
    readBr_of (rdBlk_twin_first P₁ br₁ P₂ br₂),
    readParams_of (by rw [hN, hN₂]) (rdBlk_twin_second P₁ br₁ P₂ br₂),
    readBr_of (rdBlk_twin_second P₁ br₁ P₂ br₂)]
  exact twin_count_at hb₁ hb₂ hn

/-! ## Polynomial time -/

section Poly
variable {α : Type} [Enc α]

theorem shiftOp_eq_elim (s : ℕ) (o : Operand) :
    shiftOp s o = o.toE.elim (fun v => .var (v + s)) (fun l => .const l) := by
  cases o <;> rfl

theorem shiftOp_polyT (s : ℕ) {o : α → Operand} (ho : PolyT o) :
    PolyT fun x => shiftOp s (o x) := by
  have h := PolyT.sumElim (f := fun (_ : α) (v : ℕ) => Operand.var (v + s))
    (g := fun (_ : α) (l : List ℕ) => Operand.const l) (Operand.toE_polyT ho)
    (Operand.var_polyT (PolyT.add (PolyT.snd PolyT.id') (PolyT.const s)))
    (Operand.const_polyT (PolyT.snd PolyT.id'))
  exact h.congr (fun x => (shiftOp_eq_elim s (o x)).symm)

theorem shiftProd_polyT (s : ℕ) {p : α → ProdD} (hp : PolyT p) :
    PolyT fun x => shiftProd s (p x) :=
  ProdD.mk_polyT (PolyT.add (ProdD.u_polyT hp) (PolyT.const s)) (shiftOp_polyT s (ProdD.w_polyT hp))

theorem shiftCmp_polyT (s : ℕ) {q : α → CmpD} (hq : PolyT q) :
    PolyT fun x => shiftCmp s (q x) :=
  CmpD.mk_polyT (PolyT.add (CmpD.v_polyT hq) (PolyT.const s)) (shiftOp_polyT s (CmpD.rhs_polyT hq))
    (CmpD.rel_polyT hq)

theorem compiledChain_polyT' {m : ℕ} {es : α → Fin m → Equation} (c : Fin m)
    (hl : PolyT fun x => (es x c).left) (hr : PolyT fun x => (es x c).right) :
    PolyT fun x => compiledChain (es x) c := by
  unfold compiledChain
  fun_prop

theorem comparisons_polyT {P : α → Parameters} {br : α → Branch} {b l : α → ℕ}
    (hb : Unary b) (hl : Unary l)
    (hbound : PolyT fun x => (P x).bound)
    (hM : PolyT fun x => (P x).baseM) (hN : PolyT fun x => (P x).baseN)
    (hS : PolyT fun x => (P x).scale)
    (hU : ∀k,PolyT fun x => (P x).U k) (hV : ∀k,PolyT fun x => (P x).V k)
    (hQ : ∀k,PolyT fun x => (P x).Q k)
    (hu : PolyT fun x => (br x).unitD)
    (hn : ∀k,PolyT fun x => (br x).neg k) :
    PolyT fun x => comparisons (P x) (br x) (b x) (l x) := by
  have hhead := headComparisons_polyT hb hl hu hbound hM hN
  have hbody : PolyT fun x => List.ofFn fun k : Fin 4 =>
      kernelComparisons ((br x).neg k) (offset k) ++ inputComparisons (P x) (b x) (l x) k :=
    ofFn_polyT _ (fun k => PolyT.append (kernelComparisons_polyT (hn k) _)
      (inputComparisons_polyT hb hl hM hN hS hU hV hQ k))
  unfold comparisons
  fun_prop

theorem twinEquations_left (br₁ br₂ : Branch) (b l : ℕ) (c : Fin 67) :
    (twinEquations br₁ br₂ b l c).left = [] := by
  unfold twinEquations
  split_ifs
  · exact equations_left_nil _ _
  · exact equations_left_nil _ _
  · rfl

theorem twinEquations_prod_polyT {br₁ br₂ : α → Branch} {b l : α → ℕ}
    (hn₁ : ∀k,PolyT fun x => (br₁ x).neg k) (hi₁ : ∀k,PolyT fun x => (br₁ x).imag k)
    (hn₂ : ∀k,PolyT fun x => (br₂ x).neg k) (hi₂ : ∀k,PolyT fun x => (br₂ x).imag k)
    (c : Fin 67) (i : Fin 4) :
    PolyT fun x => (twinEquations (br₁ x) (br₂ x) (b x) (l x) c).prod i := by
  by_cases h1 : c.val < 33
  · simp only [twinEquations, h1, ↓reduceDIte]
    exact equations_prod_polyT hn₁ hi₁ _ _
  · by_cases h2 : c.val < 66
    · simp only [twinEquations, h1, h2, ↓reduceDIte, shiftEq_prod]
      exact shiftProd_polyT 72 (equations_prod_polyT hn₂ hi₂ _ _)
    · simp only [twinEquations, h1, h2, ↓reduceDIte]
      fin_cases i <;> exact PolyT.const _

theorem twinEquations_right_polyT {br₁ br₂ : α → Branch} {b l : α → ℕ}
    (hb : Unary b) (hl : Unary l)
    (hu₁ : PolyT fun x => (br₁ x).unitD) (hu₂ : PolyT fun x => (br₂ x).unitD) (c : Fin 67) :
    PolyT fun x => (twinEquations (br₁ x) (br₂ x) (b x) (l x) c).right := by
  by_cases h1 : c.val < 33
  · simp only [twinEquations, h1, ↓reduceDIte]
    exact equations_right_polyT hu₁ _
  · by_cases h2 : c.val < 66
    · simp only [twinEquations, h1, h2, ↓reduceDIte, shiftEq]
      exact equations_right_polyT hu₂ _
    · simp only [twinEquations, h1, h2, ↓reduceDIte, linkEq]
      exact toLimbs_polyT hb hl (PolyT.const 2)

theorem twinDescriptor_polyT {P₁ P₂ : α → Parameters} {br₁ br₂ : α → Branch} {b l : α → ℕ}
    (hb : Unary b) (hl : Unary l)
    (hbound₁ : PolyT fun x => (P₁ x).bound)
    (hM₁ : PolyT fun x => (P₁ x).baseM) (hN₁ : PolyT fun x => (P₁ x).baseN)
    (hS₁ : PolyT fun x => (P₁ x).scale)
    (hU₁ : ∀k,PolyT fun x => (P₁ x).U k) (hV₁ : ∀k,PolyT fun x => (P₁ x).V k)
    (hQ₁ : ∀k,PolyT fun x => (P₁ x).Q k)
    (hu₁ : PolyT fun x => (br₁ x).unitD)
    (hn₁ : ∀k,PolyT fun x => (br₁ x).neg k) (hi₁ : ∀k,PolyT fun x => (br₁ x).imag k)
    (hbound₂ : PolyT fun x => (P₂ x).bound)
    (hM₂ : PolyT fun x => (P₂ x).baseM) (hN₂ : PolyT fun x => (P₂ x).baseN)
    (hS₂ : PolyT fun x => (P₂ x).scale)
    (hU₂ : ∀k,PolyT fun x => (P₂ x).U k) (hV₂ : ∀k,PolyT fun x => (P₂ x).V k)
    (hQ₂ : ∀k,PolyT fun x => (P₂ x).Q k)
    (hu₂ : PolyT fun x => (br₂ x).unitD)
    (hn₂ : ∀k,PolyT fun x => (br₂ x).neg k) (hi₂ : ∀k,PolyT fun x => (br₂ x).imag k) :
    PolyT fun x => twinDescriptor (P₁ x) (br₁ x) (P₂ x) (br₂ x) (b x) (l x) := by
  have hp : PolyT fun x => compiledProducts (twinEquations (br₁ x) (br₂ x) (b x) (l x)) :=
    ofFn_polyT _ (fun p => twinEquations_prod_polyT hn₁ hi₁ hn₂ hi₂ _ _)
  have hc : PolyT fun x => List.ofFn (compiledChain (twinEquations (br₁ x) (br₂ x) (b x) (l x))) :=
    ofFn_polyT _ (fun c => compiledChain_polyT' c
      (by simp only [twinEquations_left]; exact PolyT.const _)
      (twinEquations_right_polyT hb hl hu₁ hu₂ c))
  have hc₁ := comparisons_polyT hb hl hbound₁ hM₁ hN₁ hS₁ hU₁ hV₁ hQ₁ hu₁ hn₁
  have hc₂ := comparisons_polyT hb hl hbound₂ hM₂ hN₂ hS₂ hU₂ hV₂ hQ₂ hu₂ hn₂
  have hc₂' : PolyT fun x => (comparisons (P₂ x) (br₂ x) (b x) (l x)).map (shiftCmp 72) :=
    PolyT.map (f := fun _ q => shiftCmp 72 q) (shiftCmp_polyT 72 (PolyT.snd PolyT.id')) hc₂
  have hcmps : PolyT fun x => twinComparisons (P₁ x) (br₁ x) (P₂ x) (br₂ x) (b x) (l x) := by
    unfold twinComparisons
    exact PolyT.append hc₁ hc₂'
  unfold twinDescriptor compile
  fun_prop

theorem twinReader_polyT : PolyT twinReader := by
  have hblk (i : ℕ) : PolyT fun y : List Bool × List Bool => rdBlk 48 i y.2 :=
    (rdBlk_polyT 48 i).comp (PolyT.snd PolyT.id')
  unfold twinReader twinActual
  apply twinDescriptor_polyT (b_unary len_fst_unary) (kl_unary len_fst_unary (PolyT.const 0))
  · exact PolyT.add gofWord_fst_polyT (PolyT.const 0)
  · exact hblk _
  · exact hblk _
  · exact hblk _
  · intro k; exact hblk _
  · intro k; exact hblk _
  · intro k; exact hblk _
  · exact PolyT.decide_eq (hblk _) (PolyT.const 1)
  · intro k; exact PolyT.decide_eq (hblk _) (PolyT.const 1)
  · intro k; exact PolyT.decide_eq (hblk _) (PolyT.const 1)
  · exact PolyT.add gofWord_fst_polyT (PolyT.const 2)
  · exact hblk _
  · exact hblk _
  · exact hblk _
  · intro k; exact hblk _
  · intro k; exact hblk _
  · intro k; exact hblk _
  · exact PolyT.decide_eq (hblk _) (PolyT.const 1)
  · intro k; exact PolyT.decide_eq (hblk _) (PolyT.const 1)
  · intro k; exact PolyT.decide_eq (hblk _) (PolyT.const 1)

theorem twinQuery_polyT {P₁ P₂ : α → Parameters} {br₁ br₂ : α → Branch}
    (hM₁ : PolyT fun x => (P₁ x).baseM) (hN₁ : PolyT fun x => (P₁ x).baseN)
    (hS₁ : PolyT fun x => (P₁ x).scale)
    (hU₁ : ∀k,PolyT fun x => (P₁ x).U k) (hV₁ : ∀k,PolyT fun x => (P₁ x).V k)
    (hQ₁ : ∀k,PolyT fun x => (P₁ x).Q k)
    (hu₁ : PolyT fun x => (br₁ x).unitD)
    (hn₁ : ∀k,PolyT fun x => (br₁ x).neg k) (hi₁ : ∀k,PolyT fun x => (br₁ x).imag k)
    (hM₂ : PolyT fun x => (P₂ x).baseM) (hN₂ : PolyT fun x => (P₂ x).baseN)
    (hS₂ : PolyT fun x => (P₂ x).scale)
    (hU₂ : ∀k,PolyT fun x => (P₂ x).U k) (hV₂ : ∀k,PolyT fun x => (P₂ x).V k)
    (hQ₂ : ∀k,PolyT fun x => (P₂ x).Q k)
    (hu₂ : PolyT fun x => (br₂ x).unitD)
    (hn₂ : ∀k,PolyT fun x => (br₂ x).neg k) (hi₂ : ∀k,PolyT fun x => (br₂ x).imag k) :
    PolyT fun x => twinQuery (P₁ x) (br₁ x) (P₂ x) (br₂ x) :=
  encodeList_polyT (PolyT.append (queryData_polyT hM₁ hN₁ hS₁ hU₁ hV₁ hQ₁ hu₁ hn₁ hi₁)
    (queryData_polyT hM₂ hN₂ hS₂ hU₂ hV₂ hQ₂ hu₂ hn₂ hi₂))
end Poly

/-! ## The package -/

def arithTwinKernel : ArithLSpec where
  nf w := w.length
  nf_le _ := le_rfl
  nf_unary := len_unary
  R w := w.length
  R_le _ := le_rfl
  R_poly := len_unary.poly
  desc := twinReader
  desc_poly := twinReader_polyT
  cS := 268
  one_le_cS := by norm_num
  spread y := twinActual_spread _ _ _ _ _
  lev_le y := by simp [twinReader, twinActual, twinDescriptor, compile, LDesc.nL]
  wf w π _ := twinActual_WF _ _ _ _ _

/-- One counted-network package whose every valid twin query has the exact doubled count. -/
theorem twin_package_exact_exists :
    ∃ pk : CntPackage (2^22*268),
      (∀ w, pk.R w = w.length) ∧ (∀ w, pk.Ok w) ∧
      ∀ (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch) (B : ℕ)
        (w : List Bool),
        Groundwork.ofWord w = P₁.bound → P₂.bound = P₁.bound + 2 →
        BitBounds P₁ B → BitBounds P₂ B → 5*B+2 ≤ w.length →
        pk.Q w (twinQuery P₁ br₁ P₂ br₂) = twinValue P₁ br₁ P₂ br₂ := by
  obtain ⟨pk, hQ, hR, hOk, _⟩ := arithTwinKernel.pkg_exists
  refine ⟨pk, hR, hOk, ?_⟩
  intro P₁ br₁ P₂ br₂ B w hN hN₂ hb₁ hb₂ hn
  rw [hQ]
  exact twin_reader_query_count w hN hN₂ hb₁ hb₂ hn

end EthFollowup.Primes.TwinKernel
