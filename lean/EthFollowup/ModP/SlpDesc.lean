/-
# Straight-line-program descriptions (repnum-plan.md §2, R1)

A uniform gadget for descriptions whose auxiliary variables are determined by the free ones.
A *step* `s = (a?, u, w, c) : Step` computes `z := (x_a or 0) + x_u · w + const c` and is encoded as
ONE product `x_u · w` and ONE 3-term chain `1·lin a + 1·prod t + 1·const c = 1·lin z`.
The description `slpDesc k P fin` has the `k` free variables `x_0, …, x_{k-1}`, the auxiliary
variable `k + t` defined by step `t` of the program `P`, no patterns, and the final comparisons `fin`.

* `slpDesc_sat_iff`: satisfying assignments = assignments obeying every step, plus `fin`;
* `slpRun`: the canonical run on a free assignment; `slpRun_unique`, `slpRun_step`;
* `slpDesc_count`: the count is the number of free tuples in the box whose run satisfies `fin`
  (if the aux values of such runs fit in the box);
* `slpDesc_WF`: well-formedness.

Pure Mathlib; compiles in both toolchains. Standard axioms only.
-/
import EthFollowup.ModP.ArithDesc
import EthFollowup.ModP.ArithInstances

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset

/-! ## Definitions (FROZEN, repnum-plan.md §2) -/

/-- A step `z := (a? ) + x_u * w + const c`; `a = none` means `0`. A product type (not a structure) so that the
bridge gets `Enc`/`PolyT` for free (`Enc (Option ℕ)`, `Enc Operand` (ArithEnc), products, lists). -/
abbrev Step : Type := Option ℕ × ℕ × Operand × List ℕ

/-- The value computed by a step. -/
def Step.val (b : ℕ) (x : ℕ → ℕ) (s : Step) : ℕ :=
  s.1.elim 0 x + x s.2.1 * s.2.2.1.eval b x + limbsVal b s.2.2.2

/-- Every variable the step reads is `< m`. -/
def Step.Scoped (m : ℕ) (s : Step) : Prop :=
  (∀ a ∈ s.1, a < m) ∧ s.2.1 < m ∧ ∀ v, s.2.2.1 = .var v → v < m

/-- The products of a program: product `t` is `x_u · w` of step `t`. -/
def slpProds (P : List Step) : List ProdD := P.map fun s => ⟨s.2.1, s.2.2.1⟩

/-- The chain of step `t`: `1·lin a + 1·prod t + 1·const c = 1·lin (k + t)`. -/
def slpChain (k : ℕ) (P : List Step) (t : ℕ) : ChainD :=
  ⟨(((P.getD t default).1.map fun a => [(⟨1, .lin a⟩ : Term)]).getD []) ++
      [⟨1, .prod t⟩, ⟨1, .const (P.getD t default).2.2.2⟩], [⟨1, .lin (k + t)⟩]⟩

/-- `k` free variables `x_0..x_{k-1}`, aux variable `k + t` defined by step `t`, final comparisons `fin`. -/
def slpDesc (k : ℕ) (P : List Step) (fin : List CmpD) : Desc :=
  { nV := k + P.length, pat := [], prods := slpProds P, chains := (List.range P.length).map (slpChain k P),
    cmps := fin }

/-- The final comparisons hold. -/
def FinHolds (b : ℕ) (fin : List CmpD) (x : ℕ → ℕ) : Prop := ∀ q ∈ fin, q.rel.Holds (x q.v) (q.rhs.eval b x)

instance instDecFinHolds (b : ℕ) (fin : List CmpD) (x : ℕ → ℕ) : Decidable (FinHolds b fin x) := by
  unfold FinHolds; infer_instance

/-- The canonical run: `t` steps applied to the free assignment `u`. -/
def slpRun (b k : ℕ) (P : List Step) (u : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => u
  | t + 1 => Function.update (slpRun b k P u t) (k + t) ((P.getD t default).val b (slpRun b k P u t))

/-- Every step reads only free variables and earlier aux variables. -/
def Scoped (k : ℕ) (P : List Step) : Prop := ∀ t < P.length, (P.getD t default).Scoped (k + t)

/-! ## Shape -/

@[simp] theorem slpDesc_nV (k : ℕ) (P : List Step) (fin : List CmpD) : (slpDesc k P fin).nV = k + P.length := rfl

@[simp] theorem slpDesc_pat (k : ℕ) (P : List Step) (fin : List CmpD) : (slpDesc k P fin).pat = [] := rfl

@[simp] theorem slpDesc_prods (k : ℕ) (P : List Step) (fin : List CmpD) :
    (slpDesc k P fin).prods = slpProds P := rfl

@[simp] theorem slpDesc_cmps (k : ℕ) (P : List Step) (fin : List CmpD) : (slpDesc k P fin).cmps = fin := rfl

theorem slpDesc_chains (k : ℕ) (P : List Step) (fin : List CmpD) :
    (slpDesc k P fin).chains = (List.range P.length).map (slpChain k P) := rfl

theorem slpDesc_nP (k : ℕ) (P : List Step) (fin : List CmpD) :
    (slpDesc k P fin).prods.length = P.length := by simp [slpDesc, slpProds]

theorem slpDesc_nC (k : ℕ) (P : List Step) (fin : List CmpD) :
    (slpDesc k P fin).chains.length = P.length := by simp [slpDesc]

theorem slpDesc_nQ (k : ℕ) (P : List Step) (fin : List CmpD) :
    (slpDesc k P fin).cmps.length = fin.length := rfl

/-- The description constant `64 (nV + nP + nQ + 1)(nC + 1)` of ArithNet (`cA`, bridge) for an SLP description. -/
theorem slpDesc_cA_eq (k : ℕ) (P : List Step) (fin : List CmpD) :
    64 * (((slpDesc k P fin).nV + (slpDesc k P fin).prods.length + (slpDesc k P fin).cmps.length + 1) *
      ((slpDesc k P fin).chains.length + 1)) =
      64 * ((k + P.length + P.length + fin.length + 1) * (P.length + 1)) := by
  rw [slpDesc_nV, slpDesc_nP, slpDesc_nQ, slpDesc_nC]

/-! ## Products and chains evaluated -/

theorem getD_slpProds {P : List Step} {t : ℕ} (ht : t < P.length) :
    (slpProds P).getD t default = ⟨(P.getD t default).2.1, (P.getD t default).2.2.1⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa [slpProds] using ht), List.getD_eq_getElem _ _ ht]
  simp [slpProds]

theorem sideVal_slpChain_lhs (b k : ℕ) {P : List Step} (x : ℕ → ℕ) {t : ℕ} (ht : t < P.length) :
    sideVal b (slpProds P) x (slpChain k P t).lhs = (P.getD t default).val b x := by
  have hp := getD_slpProds ht
  unfold slpChain
  generalize P.getD t default = s at hp ⊢
  simp only [List.getD_eq_getElem?_getD] at hp
  obtain ⟨_ | a, u, w, l⟩ := s
  · simp [sideVal, Src.eval, ProdD.eval, Step.val, hp]
  · simp [sideVal, Src.eval, ProdD.eval, Step.val, hp]; ring

theorem sideVal_slpChain_rhs (b k : ℕ) (P : List Step) (x : ℕ → ℕ) (t : ℕ) :
    sideVal b (slpProds P) x (slpChain k P t).rhs = x (k + t) := by
  simp [slpChain, sideVal, Src.eval]

theorem Step.val_congr {b m : ℕ} {s : Step} (hs : s.Scoped m) {x y : ℕ → ℕ} (h : ∀ v < m, x v = y v) :
    s.val b x = s.val b y := by
  obtain ⟨a, u, w, l⟩ := s
  obtain ⟨ha, hu, hw⟩ := hs
  simp only [Step.val]
  have h1 : a.elim 0 x = a.elim 0 y := by
    cases a with
    | none => rfl
    | some a => exact h a (ha a rfl)
  have h2 : w.eval b x = w.eval b y := by
    cases w with
    | var v => exact h v (hw v rfl)
    | const l => rfl
  rw [h1, h2, h u hu]

/-! ## The satisfying assignments -/

/-- **The satisfying assignments of an SLP description**: every aux variable is its step's value, and `fin` holds. -/
theorem slpDesc_sat_iff (b k : ℕ) (P : List Step) (fin : List CmpD) (x : ℕ → ℕ) :
    (slpDesc k P fin).Sat b x ↔ (∀ t < P.length, x (k + t) = (P.getD t default).val b x) ∧ FinHolds b fin x := by
  unfold Desc.Sat
  simp only [slpDesc_pat, List.getD_nil, patMatch_nil, implies_true, true_and, slpDesc_cmps, slpDesc_prods,
    slpDesc_chains, List.forall_mem_map, List.mem_range]
  rw [and_comm]
  apply and_congr_left'
  apply forall₂_congr
  intro t ht
  rw [sideVal_slpChain_lhs b k x ht, sideVal_slpChain_rhs]
  exact eq_comm

/-! ## The canonical run -/

theorem slpRun_zero (b k : ℕ) (P : List Step) (u : ℕ → ℕ) : slpRun b k P u 0 = u := rfl

theorem slpRun_succ (b k : ℕ) (P : List Step) (u : ℕ → ℕ) (t : ℕ) :
    slpRun b k P u (t + 1) =
      Function.update (slpRun b k P u t) (k + t) ((P.getD t default).val b (slpRun b k P u t)) := rfl

/-- Free variables are never changed. -/
theorem slpRun_of_lt {b k : ℕ} {P : List Step} {u : ℕ → ℕ} {v : ℕ} (hv : v < k) (t : ℕ) :
    slpRun b k P u t v = u v := by
  induction t with
  | zero => rfl
  | succ t ih => rw [slpRun_succ, Function.update_of_ne (by omega), ih]

/-- Variables beyond the run are never changed. -/
theorem slpRun_of_ge {b k : ℕ} {P : List Step} {u : ℕ → ℕ} {v t : ℕ} (hv : k + t ≤ v) :
    slpRun b k P u t v = u v := by
  induction t with
  | zero => rfl
  | succ t ih => rw [slpRun_succ, Function.update_of_ne (by omega), ih (by omega)]

theorem slpRun_stable {b k : ℕ} {P : List Step} {u : ℕ → ℕ} {v t : ℕ} (hv : v < k + t) :
    slpRun b k P u (t + 1) v = slpRun b k P u t v := by
  rw [slpRun_succ, Function.update_of_ne (by omega)]

/-- Once set, a variable keeps its value. -/
theorem slpRun_mono {b k : ℕ} {P : List Step} {u : ℕ → ℕ} {v t : ℕ} (hv : v < k + t) {t' : ℕ} (htt : t ≤ t') :
    slpRun b k P u t' v = slpRun b k P u t v := by
  induction t', htt using Nat.le_induction with
  | base => rfl
  | succ t' htt ih => rw [slpRun_stable (by omega), ih]

theorem slpRun_self (b k : ℕ) (P : List Step) (u : ℕ → ℕ) (t : ℕ) :
    slpRun b k P u (t + 1) (k + t) = (P.getD t default).val b (slpRun b k P u t) := by
  rw [slpRun_succ, Function.update_self]

/-- The full run obeys every step. -/
theorem slpRun_step {b k : ℕ} {P : List Step} {u : ℕ → ℕ} (hP : Scoped k P) {t : ℕ} (ht : t < P.length) :
    slpRun b k P u P.length (k + t) = (P.getD t default).val b (slpRun b k P u P.length) := by
  rw [slpRun_mono (t := t + 1) (by omega) (by omega), slpRun_self]
  exact Step.val_congr (hP t ht) fun v hv => (slpRun_mono hv (by omega)).symm

/-- **Uniqueness**: an assignment obeying every step and agreeing with `u` on the free variables is the run. -/
theorem slpRun_unique {b k : ℕ} {P : List Step} {u y : ℕ → ℕ} (hP : Scoped k P)
    (hy : ∀ t < P.length, y (k + t) = (P.getD t default).val b y) (hu : ∀ v < k, y v = u v) :
    ∀ v < k + P.length, y v = slpRun b k P u P.length v := by
  have key : ∀ t ≤ P.length, ∀ v < k + t, y v = slpRun b k P u t v := by
    intro t
    induction t with
    | zero => intro _ v hv; exact hu v (by omega)
    | succ t ih =>
      intro ht v hv
      rcases Nat.lt_or_ge v (k + t) with hlt | hge
      · rw [slpRun_stable hlt]; exact ih (by omega) v hlt
      · obtain rfl : v = k + t := by omega
        rw [slpRun_self, hy t (by omega)]
        exact Step.val_congr (hP t (by omega)) (ih (by omega))
  exact key _ le_rfl

/-! ## The count -/

/-- A copy of HornerDesc's `extV_of_lt` (renamed so that both files can be imported together). -/
theorem extV_eq_of_lt {N : ℕ} (x : Fin N → ℕ) {v : ℕ} (hv : v < N) : extV N x v = x ⟨v, hv⟩ := by
  simp [extV, hv]

theorem extV_eq_of_ge {N : ℕ} (x : Fin N → ℕ) {v : ℕ} (hv : N ≤ v) : extV N x v = 0 := by
  simp [extV, show ¬ v < N by omega]

/-- An assignment of `slpDesc` obeying every step is the run on its free part. -/
theorem extV_eq_slpRun {b k : ℕ} {P : List Step} (hP : Scoped k P) (x : Fin (k + P.length) → ℕ)
    (hx : ∀ t < P.length, extV _ x (k + t) = (P.getD t default).val b (extV _ x)) :
    extV (k + P.length) x = slpRun b k P (extV k fun i : Fin k => x ⟨i, by omega⟩) P.length := by
  funext v
  rcases Nat.lt_or_ge v (k + P.length) with hv | hv
  · refine slpRun_unique hP hx (fun v hv' => ?_) v hv
    rw [extV_eq_of_lt _ hv', extV_eq_of_lt _ (by omega)]
  · rw [extV_eq_of_ge _ hv, slpRun_of_ge hv, extV_eq_of_ge _ (by omega)]

/-- **The count of an SLP description**: the number of free tuples in the box whose run satisfies `fin`,
provided the aux values of every such run lie in the box. -/
theorem slpDesc_count {b k Bx : ℕ} {P : List Step} {fin : List CmpD} (hP : Scoped k P)
    (hbox : ∀ u : Fin k → ℕ, (∀ i, u i < Bx) → FinHolds b fin (slpRun b k P (extV k u) P.length) →
      ∀ t < P.length, slpRun b k P (extV k u) P.length (k + t) < Bx) :
    (slpDesc k P fin).countB b Bx =
      ((Fintype.piFinset fun _ : Fin k => range Bx).filter fun u =>
        FinHolds b fin (slpRun b k P (extV k u) P.length)).card := by
  unfold Desc.countB
  rw [slpDesc_nV]
  have hsat : ∀ x : Fin (k + P.length) → ℕ, (slpDesc k P fin).Sat b (extV (k + P.length) x) →
      extV (k + P.length) x = slpRun b k P (extV k fun i : Fin k => x ⟨i, by omega⟩) P.length := by
    intro x hx
    exact extV_eq_slpRun hP x ((slpDesc_sat_iff b k P fin _).1 hx).1
  have hrun : ∀ u : Fin k → ℕ, extV (k + P.length)
      (fun v : Fin (k + P.length) => slpRun b k P (extV k u) P.length v) = slpRun b k P (extV k u) P.length := by
    intro u
    funext v
    rcases Nat.lt_or_ge v (k + P.length) with hv | hv
    · rw [extV_eq_of_lt _ hv]
    · rw [extV_eq_of_ge _ hv, slpRun_of_ge hv, extV_eq_of_ge _ (by omega)]
  refine card_bij' (fun x _ => fun i : Fin k => x ⟨i, by omega⟩)
    (fun u _ => fun v : Fin (k + P.length) => slpRun b k P (extV k u) P.length v) ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨hb, hs⟩ := hx
    rw [mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => hb _, ?_⟩
    rw [← hsat x hs]
    exact ((slpDesc_sat_iff b k P fin _).1 hs).2
  · intro u hu
    rw [mem_filter, Fintype.mem_piFinset] at hu
    obtain ⟨hb, hf⟩ := hu
    rw [mem_filter, Fintype.mem_piFinset, hrun, slpDesc_sat_iff]
    refine ⟨fun v => ?_, fun t ht => slpRun_step hP ht, hf⟩
    rw [mem_range]
    rcases Nat.lt_or_ge (v : ℕ) k with hv | hv
    · rw [slpRun_of_lt hv, extV_eq_of_lt _ hv]; exact mem_range.1 (hb _)
    · have := hbox u (fun i => mem_range.1 (hb i)) hf (v - k) (by omega)
      rwa [show k + (v - k) = v by omega] at this
  · intro x hx
    rw [mem_filter] at hx
    have h := hsat x hx.2
    funext v
    rw [← h, extV_eq_of_lt _ v.isLt]
  · intro u _
    funext i
    simp only
    rw [slpRun_of_lt i.isLt, extV_eq_of_lt _ i.isLt]

/-! ## Well-formedness -/

theorem slpChain_hasProd (k : ℕ) (P : List Step) (c p : ℕ) : (slpChain k P c).HasProd p ↔ p = c := by
  unfold ChainD.HasProd slpChain
  generalize P.getD c default = s
  obtain ⟨_ | a, u, w, l⟩ := s <;> simp [eq_comm]

/-- **Well-formedness** of an SLP description (every index in range, constants of `≤ ℓ` limbs `< 2^b`). -/
theorem slpDesc_WF {b ℓ nB k : ℕ} {P : List Step} {fin : List CmpD}
    (hP : ∀ s ∈ P, s.2.1 < k + P.length ∧ s.2.2.1.OK b ℓ (k + P.length) ∧ (∀ a ∈ s.1, a < k + P.length) ∧
      s.2.2.2.length ≤ ℓ ∧ ∀ y ∈ s.2.2.2, y < 2 ^ b)
    (hfin : ∀ q ∈ fin, q.v < k + P.length ∧ q.rhs.OK b ℓ (k + P.length)) :
    (slpDesc k P fin).WFB b ℓ nB where
  pat_len := by simp
  prod_ok := by
    intro pd hpd
    simp only [slpDesc_prods, slpProds, List.mem_map] at hpd
    obtain ⟨s, hs, rfl⟩ := hpd
    exact ⟨(hP s hs).1, (hP s hs).2.1⟩
  term_ok := by
    intro ch hch t ht
    simp only [slpDesc_chains, List.mem_map, List.mem_range] at hch
    obtain ⟨i, hi, rfl⟩ := hch
    have hmem : P.getD i default ∈ P := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    obtain ⟨-, -, ha, hl, hy⟩ := hP _ hmem
    rw [slpDesc_nV, slpDesc_nP]
    unfold slpChain at ht
    generalize P.getD i default = s at ha hl hy ht
    obtain ⟨_ | a, u, w, l⟩ := s
    · simp at ht
      rcases ht with rfl | rfl | rfl
      · simpa [Src.OK] using hi
      · exact ⟨hl, hy⟩
      · simp [Src.OK]; omega
    · simp at ht
      rcases ht with rfl | rfl | rfl | rfl
      · simpa [Src.OK] using ha a rfl
      · simpa [Src.OK] using hi
      · exact ⟨hl, hy⟩
      · simp [Src.OK]; omega
  coeff_le := by
    intro ch hch
    simp only [slpDesc_chains, List.mem_map, List.mem_range] at hch
    obtain ⟨i, hi, rfl⟩ := hch
    unfold slpChain
    generalize P.getD i default = s
    obtain ⟨_ | a, u, w, l⟩ := s <;> simp
  prod_once := by
    intro c hc c' hc' p h h'
    simp only [slpDesc_chains, List.length_map, List.length_range] at hc hc' h h'
    rw [List.getD_eq_getElem _ _ (by simpa using hc)] at h
    rw [List.getD_eq_getElem _ _ (by simpa using hc')] at h'
    simp only [List.getElem_map, List.getElem_range, slpChain_hasProd] at h h'
    omega
  cmp_ok := by
    intro q hq
    exact hfin q hq

end EthFollowup.ModP
