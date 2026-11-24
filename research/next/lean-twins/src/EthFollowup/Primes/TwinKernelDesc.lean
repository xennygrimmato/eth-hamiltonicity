/- The doubled (eight-kernel) descriptor: two copies of Ni's four-kernel
prime-indicator descriptor, on disjoint variables, linked by `n₂ = n + 2`. -/
import EthFollowup.Primes.CountKernelWF

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace EthFollowup.Primes.TwinKernel
open Finset EthFollowup.ModP EthFollowup.Factoring EthFollowup.ExactHC
open EthFollowup.Primes.CountKernel

/-! ## Shifting variable indices -/

def shiftOp (s : ℕ) : Operand → Operand
  | .var v => .var (v + s)
  | .const l => .const l

@[simp] theorem shiftOp_var (s v : ℕ) : shiftOp s (.var v) = .var (v + s) := rfl
@[simp] theorem shiftOp_const (s : ℕ) (l : List ℕ) : shiftOp s (.const l) = .const l := rfl

def shiftProd (s : ℕ) (p : ProdD) : ProdD := ⟨p.u + s, shiftOp s p.w⟩

def shiftEq (s : ℕ) (e : Equation) : Equation :=
  ⟨shiftProd s e.p0, shiftProd s e.p1, shiftProd s e.p2, shiftProd s e.p3, e.left, e.right⟩

def shiftCmp (s : ℕ) (q : CmpD) : CmpD := ⟨q.v + s, shiftOp s q.rhs, q.rel⟩

theorem shiftOp_eval (s b : ℕ) (x : ℕ → ℕ) (o : Operand) :
    (shiftOp s o).eval b x = o.eval b (fun i => x (i + s)) := by
  cases o <;> rfl

theorem shiftProd_eval (s b : ℕ) (x : ℕ → ℕ) (p : ProdD) :
    (shiftProd s p).eval b x = p.eval b (fun i => x (i + s)) := by
  simp only [shiftProd, ProdD.eval, shiftOp_eval]

theorem shiftEq_prod (s : ℕ) (e : Equation) (i : Fin 4) :
    (shiftEq s e).prod i = shiftProd s (e.prod i) := by
  fin_cases i <;> rfl

theorem shiftEq_holds (s b : ℕ) (x : ℕ → ℕ) (e : Equation) :
    (shiftEq s e).Holds b x ↔ e.Holds b (fun i => x (i + s)) := by
  simp only [Equation.Holds, shiftEq, shiftProd_eval]

theorem shiftCmp_holds (s b : ℕ) (x : ℕ → ℕ) (q : CmpD) :
    (shiftCmp s q).rel.Holds (x (shiftCmp s q).v) ((shiftCmp s q).rhs.eval b x) ↔
      q.rel.Holds ((fun i => x (i + s)) q.v) (q.rhs.eval b (fun i => x (i + s))) := by
  simp only [shiftCmp, shiftOp_eval]

/-! ## Dependence on the first `n` variables only -/

theorem op_eval_congr {b l n : ℕ} {x y : ℕ → ℕ} {o : Operand} (ho : o.OK b l n)
    (h : ∀ i < n, x i = y i) : o.eval b x = o.eval b y := by
  cases o with
  | var v => exact h v ho
  | const _ => rfl

theorem prod_eval_congr {b l n : ℕ} {x y : ℕ → ℕ} {p : ProdD} (hp : p.u < n ∧ p.w.OK b l n)
    (h : ∀ i < n, x i = y i) : p.eval b x = p.eval b y := by
  simp only [ProdD.eval, h p.u hp.1, op_eval_congr hp.2 h]

theorem eq_holds_congr {b l n : ℕ} {x y : ℕ → ℕ} {e : Equation}
    (hp : ∀ i, (e.prod i).u < n ∧ (e.prod i).w.OK b l n)
    (h : ∀ i < n, x i = y i) : e.Holds b x ↔ e.Holds b y := by
  have h0 := prod_eval_congr (hp 0) h
  have h1 := prod_eval_congr (hp 1) h
  have h2 := prod_eval_congr (hp 2) h
  have h3 := prod_eval_congr (hp 3) h
  simp only [Equation.prod, show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl] at h0 h1 h2 h3
  simp only [Equation.Holds, h0, h1, h2, h3]

theorem cmp_holds_congr {b l n : ℕ} {x y : ℕ → ℕ} {q : CmpD} (hq : q.v < n ∧ q.rhs.OK b l n)
    (h : ∀ i < n, x i = y i) :
    q.rel.Holds (x q.v) (q.rhs.eval b x) ↔ q.rel.Holds (y q.v) (q.rhs.eval b y) := by
  rw [h q.v hq.1, op_eval_congr hq.2 h]

theorem equations_prod_ok {b l : ℕ} (hb : 1 ≤ b) (hl : 1 ≤ l) (br : Branch) :
    ∀ c i, ((equations br c).prod i).u < 72 ∧ ((equations br c).prod i).w.OK b l 72 := by
  intro c i
  unfold equations
  split_ifs with hc
  · exact head_products_ok hb hl br.unitD _ i
  · exact kernel_products_ok hb hl (offset_bound _) _ _ _ i

/-- Ni's relations depend only on the first 72 variables. -/
theorem relations_congr {P : Parameters} {br : Branch} {b l : ℕ} (hf : Fits P b l)
    (hb : 1 ≤ b) (hl : 1 ≤ l) {x y : ℕ → ℕ} (h : ∀ i < 72, x i = y i) :
    Relations P br x ↔ Relations P br y := by
  rw [← descriptor_sat hf, ← descriptor_sat hf, descriptor, compile_sat, compile_sat]
  apply and_congr
  · apply forall₂_congr
    intro q hq
    exact cmp_holds_congr (comparisons_ok hb hl P br q hq) h
  · apply forall_congr'
    intro c
    exact eq_holds_congr (equations_prod_ok hb hl br c) h

/-! ## The doubled descriptor -/

/-- The link `x₇₂ = x₀ + 2` between the two copies' values of `n`. -/
def linkEq (b l : ℕ) : Equation :=
  ⟨linearProd 72, zeroProd, linearProd 0, zeroProd, [], toLimbs b l 2⟩

def twinEquations (br₁ br₂ : Branch) (b l : ℕ) (c : Fin 67) : Equation :=
  if h : c.val < 33 then equations br₁ ⟨c.val, h⟩
  else if h' : c.val < 66 then shiftEq 72 (equations br₂ ⟨c.val - 33, by omega⟩)
  else linkEq b l

def twinComparisons (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch)
    (b l : ℕ) : List CmpD :=
  comparisons P₁ br₁ b l ++ (comparisons P₂ br₂ b l).map (shiftCmp 72)

def twinDescriptor (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch)
    (b l : ℕ) : LDesc :=
  compile 144 (twinEquations br₁ br₂ b l) (twinComparisons P₁ br₁ P₂ br₂ b l)

theorem linkEq_holds {b l : ℕ} (h2 : 2 < 2 ^ (b * l)) (x : ℕ → ℕ) :
    (linkEq b l).Holds b x ↔ x 72 = x 0 + 2 := by
  simp [linkEq, Equation.Holds, linearProd, zeroProd, ProdD.eval, Operand.eval,
    limbsVal_toLimbs h2, show limbsVal b [1] = 1 by simp [limbsVal],
    show limbsVal b [] = 0 by simp [limbsVal]]

theorem twinEquations_holds (br₁ br₂ : Branch) {b l : ℕ} (h2 : 2 < 2 ^ (b * l)) (x : ℕ → ℕ) :
    (∀ c, (twinEquations br₁ br₂ b l c).Holds b x) ↔
      (∀ c, (equations br₁ c).Holds b x) ∧
      (∀ c, (equations br₂ c).Holds b (fun i => x (i + 72))) ∧ x 72 = x 0 + 2 := by
  constructor
  · intro h
    refine ⟨fun c => ?_, fun c => ?_, ?_⟩
    · have := h ⟨c.val, by omega⟩
      simpa [twinEquations, c.isLt] using this
    · have := h ⟨c.val + 33, by omega⟩
      have hc1 : ¬ c.val + 33 < 33 := by omega
      have hc2 : c.val + 33 < 66 := by omega
      simp only [twinEquations, hc1, hc2, ↓reduceDIte, Nat.add_sub_cancel] at this
      exact (shiftEq_holds 72 b x _).1 this
    · have := h ⟨66, by omega⟩
      simp only [twinEquations, show ¬ (66 : ℕ) < 33 by omega, show ¬ (66 : ℕ) < 66 by omega,
        ↓reduceDIte] at this
      exact (linkEq_holds h2 x).1 this
  · rintro ⟨h1, h2', h3⟩ c
    unfold twinEquations
    split_ifs with ha hb'
    · exact h1 _
    · exact (shiftEq_holds 72 b x _).2 (h2' _)
    · exact (linkEq_holds h2 x).2 h3

theorem twinComparisons_holds (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch)
    (b l : ℕ) (x : ℕ → ℕ) :
    (∀ q ∈ twinComparisons P₁ br₁ P₂ br₂ b l, q.rel.Holds (x q.v) (q.rhs.eval b x)) ↔
      (∀ q ∈ comparisons P₁ br₁ b l, q.rel.Holds (x q.v) (q.rhs.eval b x)) ∧
      (∀ q ∈ comparisons P₂ br₂ b l, q.rel.Holds ((fun i => x (i + 72)) q.v)
        (q.rhs.eval b (fun i => x (i + 72)))) := by
  unfold twinComparisons
  rw [List.forall_mem_append, List.forall_mem_map]
  apply and_congr Iff.rfl
  apply forall₂_congr
  intro q _
  exact shiftCmp_holds 72 b x q

/-- Satisfaction of the doubled descriptor: both copies and the link. -/
theorem twin_sat {P₁ P₂ : Parameters} {br₁ br₂ : Branch} {b l : ℕ}
    (hf₁ : Fits P₁ b l) (hf₂ : Fits P₂ b l) (x : ℕ → ℕ) :
    (twinDescriptor P₁ br₁ P₂ br₂ b l).D.Sat b x ↔
      Relations P₁ br₁ x ∧ Relations P₂ br₂ (fun i => x (i + 72)) ∧ x 72 = x 0 + 2 := by
  rw [twinDescriptor, compile_sat, twinComparisons_holds, twinEquations_holds _ _ hf₁.two,
    ← descriptor_sat hf₁ br₁, ← descriptor_sat hf₂ br₂, descriptor, descriptor,
    compile_sat, compile_sat]
  tauto

/-! ## Well-formedness and spread -/

theorem op_OK_mono {b l n m : ℕ} {o : Operand} (h : o.OK b l n) (hnm : n ≤ m) : o.OK b l m := by
  cases o with
  | var v => exact lt_of_lt_of_le h hnm
  | const _ => exact h

theorem shiftOp_OK {b l : ℕ} {o : Operand} (h : o.OK b l 72) : (shiftOp 72 o).OK b l 144 := by
  cases o with
  | var v =>
    change v < 72 at h
    change v + 72 < 144
    omega
  | const _ => exact h

theorem twin_products_ok {b l : ℕ} (hb : 1 ≤ b) (hl : 1 ≤ l) (br₁ br₂ : Branch) :
    ∀ c i, ((twinEquations br₁ br₂ b l c).prod i).u < 144 ∧
      ((twinEquations br₁ br₂ b l c).prod i).w.OK b l 144 := by
  have h1 : 1 < 2 ^ b := Nat.one_lt_two_pow (by omega)
  intro c i
  unfold twinEquations
  split_ifs with ha hb'
  · obtain ⟨hu, hw⟩ := equations_prod_ok hb hl br₁ ⟨c.val, ha⟩ i
    exact ⟨by omega, op_OK_mono hw (by norm_num)⟩
  · obtain ⟨hu, hw⟩ := equations_prod_ok hb hl br₂ ⟨c.val - 33, by omega⟩ i
    rw [shiftEq_prod]
    exact ⟨by simp only [shiftProd]; omega, shiftOp_OK hw⟩
  · fin_cases i <;>
      norm_num [linkEq, Equation.prod, linearProd, zeroProd, Operand.OK, hl, h1]

theorem equations_left_nil (br : Branch) (c : Fin 33) : (equations br c).left = [] := by
  unfold equations
  split_ifs with h
  · generalize (⟨c.val, h⟩ : Fin 5) = j
    fin_cases j <;> rfl
  · generalize (⟨(c.val - 5) % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7) = j
    fin_cases j <;> simp [kernelEquations]; split <;> rfl

theorem equations_right_ok {b l : ℕ} (hb : 1 ≤ b) (hl : 1 ≤ l) (br : Branch) (c : Fin 33) :
    (equations br c).right.length ≤ l ∧ ∀ a ∈ (equations br c).right, a < 2 ^ b := by
  unfold equations
  split_ifs with hc
  · exact (head_constants_ok hb hl br.unitD _).2
  · exact (kernel_constants_ok _ _ _).2

theorem twin_left_ok {b l : ℕ} (br₁ br₂ : Branch) (c : Fin 67) :
    (twinEquations br₁ br₂ b l c).left.length ≤ l ∧
      ∀ a ∈ (twinEquations br₁ br₂ b l c).left, a < 2 ^ b := by
  unfold twinEquations
  split_ifs with ha hb'
  · simp [equations_left_nil]
  · simp [shiftEq, equations_left_nil]
  · simp [linkEq]

theorem twin_right_ok {b l : ℕ} (hb : 1 ≤ b) (hl : 1 ≤ l) (br₁ br₂ : Branch) (c : Fin 67) :
    (twinEquations br₁ br₂ b l c).right.length ≤ l ∧
      ∀ a ∈ (twinEquations br₁ br₂ b l c).right, a < 2 ^ b := by
  unfold twinEquations
  split_ifs with ha hb'
  · exact equations_right_ok hb hl br₁ _
  · exact equations_right_ok hb hl br₂ _
  · exact toLimbs_OK b l 2

theorem twin_comparisons_ok {b l : ℕ} (hb : 1 ≤ b) (hl : 1 ≤ l)
    (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch) :
    ∀ q ∈ twinComparisons P₁ br₁ P₂ br₂ b l, q.v < 144 ∧ q.rhs.OK b l 144 := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨hv, ho⟩ := comparisons_ok hb hl P₁ br₁ q h
    exact ⟨by omega, op_OK_mono ho (by norm_num)⟩
  · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp h
    obtain ⟨hv, ho⟩ := comparisons_ok hb hl P₂ br₂ q' hq'
    exact ⟨by simp only [shiftCmp]; omega, shiftOp_OK ho⟩

theorem twinDescriptor_WFB {b l : ℕ} (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters)
    (br₂ : Branch) (lk : ℕ → ℕ) (hb : 1 ≤ b) (hl : 1 ≤ l) (hl0 : lk 0 = l) :
    (twinDescriptor P₁ br₁ P₂ br₂ b l).WFB b lk :=
  compile_WFB (twinEquations br₁ br₂ b l) (twinComparisons P₁ br₁ P₂ br₂ b l) lk hl0
    (twin_products_ok hb hl br₁ br₂) (twin_left_ok br₁ br₂) (twin_right_ok hb hl br₁ br₂)
    (twin_comparisons_ok hb hl P₁ br₁ P₂ br₂)

theorem twinComparisons_length_le (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters)
    (br₂ : Branch) (b l : ℕ) : (twinComparisons P₁ br₁ P₂ br₂ b l).length ≤ 116 := by
  have h1 := comparisons_length_le P₁ br₁ b l
  have h2 := comparisons_length_le P₂ br₂ b l
  simp only [twinComparisons, List.length_append, List.length_map]
  omega

theorem twinDescriptor_spread (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters)
    (br₂ : Branch) (b l : ℕ) : (twinDescriptor P₁ br₁ P₂ br₂ b l).Spread 268 where
  var := by
    intro v hv
    change v < 144 at hv
    change v / 268 ≤ 0
    omega
  prod := by
    intro p hp
    have hp' : p < 268 := by
      simpa only [twinDescriptor, compile, compiledProducts, List.length_ofFn] using hp
    change p / 268 ≤ 0
    omega
  chain := by
    intro c hc
    have hc' : c < 67 := by simpa only [twinDescriptor, compile, List.length_ofFn] using hc
    change c / 268 ≤ 0
    omega
  cmp := by
    intro q hq
    have hlen := twinComparisons_length_le P₁ br₁ P₂ br₂ b l
    change q < (twinComparisons P₁ br₁ P₂ br₂ b l).length at hq
    change q / 268 ≤ 0
    omega

def twinActual (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch)
    (n : ℕ) : LDesc :=
  twinDescriptor P₁ br₁ P₂ br₂ (b n) (kl n 0)

theorem twinActual_WF (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch)
    (n : ℕ) : (twinActual P₁ br₁ P₂ br₂ n).WF n :=
  twinDescriptor_WFB P₁ br₁ P₂ br₂ (kl n) (one_le_b n) (kl_pos n 0) rfl

theorem twinActual_spread (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters) (br₂ : Branch)
    (n : ℕ) : (twinActual P₁ br₁ P₂ br₂ n).Spread 268 :=
  twinDescriptor_spread P₁ br₁ P₂ br₂ (b n) (kl n 0)

/-- Linear communication of the doubled network (constant `2^19 · 268`). -/
theorem twinNetwork_communication (P₁ : Parameters) (br₁ : Branch) (P₂ : Parameters)
    (br₂ : Branch) {n g : ℕ} (hg : 2 ≤ g) :
    ((arithSys n (twinActual P₁ br₁ P₂ br₂ n) g hg).net (aLabCode n)).U ≤ 2^19*268*(n+2) := by
  apply arithSys_U_le hg (twinActual_WF P₁ br₁ P₂ br₂ n) (twinActual_spread P₁ br₁ P₂ br₂ n)
    (by norm_num)
  simp [twinActual, twinDescriptor, compile, LDesc.nL]

end EthFollowup.Primes.TwinKernel
