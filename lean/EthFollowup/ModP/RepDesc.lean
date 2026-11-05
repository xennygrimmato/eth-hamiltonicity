/-
# The representation-number description (repnum-plan.md §3, R2)

For `A : Matrix (Fin k) (Fin k) ℤ` (`k ≥ 1`), a shift `B` and a target `n`, the SLP description
`repDesc b ℓ k (monoL A) (monoR A) B n` (SlpDesc) has the `k` free variables `u_0, …, u_{k-1}`
and counts the `u ∈ [0, Bx)^k` with `Σ_ij A_ij (u_i − B)(u_j − B) = n`.

Layout (deviation from the plan's `sideProg`: a uniform interleaved accumulator, see below). The
auxiliary variable `k` holds `B`; a *monomial* `(p, q, c) : Mono` is `c · x_p · x_q` (indices `≤ k`,
`x_k = B`). One side `sumProg base C ms` of `T = |ms|` monomials is the program
`acc_0 := C; y_m := c_m · x_{p_m}; acc_{m+1} := acc_m + x_{q_m} · y_m` with `acc_m` at variable
`base + 2m` and `y_m` at `base + 2m + 1`, so `acc_T = C + Σ_m c_m x_{p_m} x_{q_m}`. Every entry
`A_ij (u_i − B)(u_j − B)` is split into four monomials with sign-split coefficients
`A⁺ = A.toNat`, `A⁻ = (−A).toNat`:
`A⁺ u_i u_j + A⁻ B u_i + A⁻ B u_j + A⁺ B²  =  [A⁻ u_i u_j + A⁺ B u_i + A⁺ B u_j + A⁻ B²] + A_ij (u_i − B)(u_j − B)`,
the left monomials form `monoL A`, the right ones `monoR A`; the description compares
`acc(monoL A, C = 0)` with `acc(monoR A, C = n)`.

* `sumProg`, `repProg`, `repFin`, `repDesc`, `monos`, `monoL`, `monoR`, `cM`, `repK`, `repCD`;
* `repProg_scoped`, `sumProg_run`, `repProg_blocks`, `monos_shift` (the shift identity);
* **`repDesc_count`**: `countB b Bx = #(sols A c n)` under `Coercive A c`, `c n < B`, `n + K B² < Bx, 2^{bℓ}`;
* **`repDesc_WF`** (unconditional), `repDesc_cA_eq` (the shape constant `repCD k`).

Pure Mathlib; compiles in both toolchains. Standard axioms only.
-/
import EthFollowup.ModP.SlpDesc
import EthFollowup.ModP.RepQF

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset Matrix

/-! ## Generic list and sum facts -/

theorem forall_mem_of_getD {α : Type*} {l : List α} {d : α} {Φ : α → Prop}
    (h : ∀ t < l.length, Φ (l.getD t d)) : ∀ s ∈ l, Φ s := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hs
  have := h t ht
  rwa [List.getD_eq_getElem _ _ ht] at this

theorem getD_mem_or {α : Type*} (l : List α) (d : α) (i : ℕ) : l.getD i d ∈ l ∨ l.getD i d = d := by
  rcases Nat.lt_or_ge i l.length with h | h
  · left; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · right; exact List.getD_eq_default _ _ h

theorem sum_range_getD {α : Type*} (f : α → ℕ) (d : α) (l : List α) :
    ∑ i ∈ range l.length, f (l.getD i d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, sum_range_succ', List.map_cons, List.sum_cons, ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem listSum_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, ih, sum_range_succ]

theorem sum_range_divmod {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) (k : ℕ) :
    ∑ m ∈ range (k * k), F (m / k) (m % k) = ∑ i ∈ range k, ∑ j ∈ range k, F i j := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  suffices h : ∀ a, ∑ m ∈ range (a * k), F (m / k) (m % k) = ∑ i ∈ range a, ∑ j ∈ range k, F i j from h k
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    have e1 : (a * k + j) / k = a := by
      rw [mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt hj', add_zero]
    have e2 : (a * k + j) % k = j := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj']
    rw [e1, e2]

/-! ## Definitions -/

/-- A monomial `(p, q, c)`: the value `c · x_p · x_q`. -/
abbrev Mono : Type := ℕ × ℕ × ℕ

/-- The value of a monomial. -/
def Mono.val (x : ℕ → ℕ) (m : Mono) : ℕ := m.2.2 * x m.1 * x m.2.1

/-- The constant step `z := C` (it reads `x_0 · 0`). -/
def initStep (b ℓ C : ℕ) : Step := (none, 0, .const [], toLimbs b ℓ C)

/-- Step `p + 1` of an accumulator: for `p = 2m`, `y_m := x_{p_m} · c_m`; for `p = 2m + 1`,
`acc_{m+1} := acc_m + x_{q_m} · y_m` (`acc_m` at `base + p − 1`, `y_m` at `base + p`). -/
def sumStep (b ℓ base : ℕ) (ms : List Mono) (p : ℕ) : Step :=
  if p % 2 = 0 then (none, (ms.getD (p / 2) default).1, .const (toLimbs b ℓ (ms.getD (p / 2) default).2.2), [])
  else (some (base + (p - 1)), (ms.getD (p / 2) default).2.1, .var (base + p), [])

/-- **The accumulator** `C + Σ_m c_m x_{p_m} x_{q_m}`: `2|ms| + 1` steps, the result at offset `2|ms|`. -/
def sumProg (b ℓ base C : ℕ) (ms : List Mono) : List Step :=
  initStep b ℓ C :: (List.range (2 * ms.length)).map (sumStep b ℓ base ms)

/-- `x_k := B`, then the left accumulator (`C = 0`, base `k + 1`), then the right one (`C = n`). -/
def repProg (b ℓ k : ℕ) (mL mR : List Mono) (B n : ℕ) : List Step :=
  initStep b ℓ B :: (sumProg b ℓ (k + 1) 0 mL ++ sumProg b ℓ (k + 2 + 2 * mL.length) n mR)

/-- The final comparison: the two accumulators are equal. -/
def repFin (k : ℕ) (mL mR : List Mono) : List CmpD :=
  [⟨k + 1 + 2 * mL.length, .var (k + 2 + 2 * mL.length + 2 * mR.length), .eq⟩]

/-- **The representation-number description.** -/
def repDesc (b ℓ k : ℕ) (mL mR : List Mono) (B n : ℕ) : Desc :=
  slpDesc k (repProg b ℓ k mL mR B n) (repFin k mL mR)

/-- The entry `A i j` (`0` out of range). -/
def ent {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (i j : ℕ) : ℤ :=
  if h : i < k ∧ j < k then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- The four monomial families of all entries `m = i k + j`: `f u_i u_j`, `g B u_i`, `g B u_j`, `f B B`. -/
def monos (k : ℕ) (f g : ℕ → ℕ) : List Mono :=
  (List.range (k * k)).map (fun m => (m / k, m % k, f m)) ++ (List.range (k * k)).map (fun m => (k, m / k, g m)) ++
    (List.range (k * k)).map (fun m => (k, m % k, g m)) ++ (List.range (k * k)).map (fun m => (k, k, f m))

/-- `A⁺` at the entry `m = i k + j`. -/
def posC {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (m : ℕ) : ℕ := (ent A (m / k) (m % k)).toNat

/-- `A⁻` at the entry `m = i k + j`. -/
def negC {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (m : ℕ) : ℕ := (-ent A (m / k) (m % k)).toNat

/-- The left monomials. -/
def monoL {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) : List Mono := monos k (posC A) (negC A)

/-- The right monomials. -/
def monoR {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) : List Mono := monos k (negC A) (posC A)

/-- `Σ_ij |A_ij|`. -/
def cM {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) : ℕ := ∑ i, ∑ j, (A i j).natAbs

/-- The value bound: every value of the run is `≤ n + repK k cm · B²` (`|A_ij| ≤ cm`, `u < 2B`). -/
def repK (k cm : ℕ) : ℕ := 16 * (k * k + 1) * (cm + 1)

/-- The shape constant `64 (nV + nP + nQ + 1)(nC + 1)` of `repDesc` (`|repProg| = 16 k² + 3`). -/
def repCD (k : ℕ) : ℕ := 64 * ((k + 2 * (16 * (k * k) + 3) + 2) * (16 * (k * k) + 4))

/-! ## Positions -/

theorem length_sumProg (b ℓ base C : ℕ) (ms : List Mono) :
    (sumProg b ℓ base C ms).length = 2 * ms.length + 1 := by
  simp [sumProg]

theorem getD_sumProg_zero (b ℓ base C : ℕ) (ms : List Mono) :
    (sumProg b ℓ base C ms).getD 0 default = initStep b ℓ C := rfl

theorem getD_sumProg_succ {b ℓ base C : ℕ} {ms : List Mono} {p : ℕ} (hp : p < 2 * ms.length) :
    (sumProg b ℓ base C ms).getD (p + 1) default = sumStep b ℓ base ms p := by
  rw [sumProg, List.getD_cons_succ, List.getD_eq_getElem _ _ (by simpa using hp)]
  simp

theorem sumProg_cases {b ℓ base C : ℕ} {ms : List Mono} (Φ : ℕ → Step → Prop)
    (h0 : Φ 0 (initStep b ℓ C)) (h1 : ∀ p < 2 * ms.length, Φ (p + 1) (sumStep b ℓ base ms p)) :
    ∀ o < 2 * ms.length + 1, Φ o ((sumProg b ℓ base C ms).getD o default) := by
  intro o ho
  cases o with
  | zero => exact h0
  | succ p => rw [getD_sumProg_succ (by omega)]; exact h1 p (by omega)

theorem length_repProg (b ℓ k : ℕ) (mL mR : List Mono) (B n : ℕ) :
    (repProg b ℓ k mL mR B n).length = 2 * mL.length + 2 * mR.length + 3 := by
  simp only [repProg, List.length_cons, List.length_append, length_sumProg]; omega

theorem getD_repProg_zero (b ℓ k : ℕ) (mL mR : List Mono) (B n : ℕ) :
    (repProg b ℓ k mL mR B n).getD 0 default = initStep b ℓ B := rfl

theorem getD_repProg_L {b ℓ k B n : ℕ} {mL mR : List Mono} {o : ℕ} (ho : o < 2 * mL.length + 1) :
    (repProg b ℓ k mL mR B n).getD (1 + o) default = (sumProg b ℓ (k + 1) 0 mL).getD o default := by
  rw [add_comm, repProg, List.getD_cons_succ, List.getD_append _ _ _ _ (by rw [length_sumProg]; exact ho)]

theorem getD_repProg_R {b ℓ k B n : ℕ} {mL mR : List Mono} {o : ℕ} :
    (repProg b ℓ k mL mR B n).getD (2 + 2 * mL.length + o) default =
      (sumProg b ℓ (k + 2 + 2 * mL.length) n mR).getD o default := by
  rw [show 2 + 2 * mL.length + o = (2 * mL.length + 1 + o) + 1 by omega, repProg, List.getD_cons_succ,
    List.getD_append_right _ _ _ _ (by rw [length_sumProg]; omega), length_sumProg]
  congr 1; omega

theorem repProg_cases {b ℓ k B n : ℕ} {mL mR : List Mono} (Φ : ℕ → Step → Prop)
    (h0 : Φ 0 (initStep b ℓ B))
    (hL : ∀ o < 2 * mL.length + 1, Φ (1 + o) ((sumProg b ℓ (k + 1) 0 mL).getD o default))
    (hR : ∀ o < 2 * mR.length + 1,
      Φ (2 + 2 * mL.length + o) ((sumProg b ℓ (k + 2 + 2 * mL.length) n mR).getD o default)) :
    ∀ t < (repProg b ℓ k mL mR B n).length, Φ t ((repProg b ℓ k mL mR B n).getD t default) := by
  intro t ht
  rw [length_repProg] at ht
  rcases Nat.lt_or_ge t 1 with h | h
  · obtain rfl : t = 0 := by omega
    exact h0
  rcases Nat.lt_or_ge t (2 * mL.length + 2) with h' | h'
  · obtain ⟨o, rfl⟩ : ∃ o, t = 1 + o := ⟨t - 1, by omega⟩
    rw [getD_repProg_L (by omega)]
    exact hL o (by omega)
  · obtain ⟨o, rfl⟩ : ∃ o, t = 2 + 2 * mL.length + o := ⟨t - (2 + 2 * mL.length), by omega⟩
    rw [getD_repProg_R]
    exact hR o (by omega)

/-! ## Scope -/

/-- All monomial indices (also of the default) are `< N`. -/
def MonoIdx (N : ℕ) (ms : List Mono) : Prop := ∀ i, (ms.getD i default).1 < N ∧ (ms.getD i default).2.1 < N

theorem MonoIdx.mono {N N' : ℕ} {ms : List Mono} (h : MonoIdx N ms) (hN : N ≤ N') : MonoIdx N' ms :=
  fun i => ⟨(h i).1.trans_le hN, (h i).2.trans_le hN⟩

theorem initStep_scoped (b ℓ C : ℕ) {m : ℕ} (hm : 0 < m) : (initStep b ℓ C).Scoped m := by
  refine ⟨by simp [initStep], hm, ?_⟩
  intro v hv
  simp [initStep] at hv

theorem sumStep_scoped (b ℓ base : ℕ) {ms : List Mono} (hms : MonoIdx base ms) (p : ℕ) :
    (sumStep b ℓ base ms p).Scoped (base + (p + 1)) := by
  unfold sumStep
  have h := hms (p / 2)
  split_ifs
  · refine ⟨by simp, by dsimp only; omega, fun v hv => by simp at hv⟩
  · refine ⟨fun a ha => ?_, by dsimp only; omega, fun v hv => ?_⟩
    · simp only [Option.mem_def, Option.some.injEq] at ha; omega
    · simp only [Operand.var.injEq] at hv; omega

theorem sumProg_scoped {b ℓ base C : ℕ} {ms : List Mono} (hb : 0 < base) (hms : MonoIdx base ms) :
    ∀ o < 2 * ms.length + 1, ((sumProg b ℓ base C ms).getD o default).Scoped (base + o) :=
  sumProg_cases (fun o s => s.Scoped (base + o)) (initStep_scoped b ℓ C (by omega))
    fun p _ => sumStep_scoped b ℓ base hms p

theorem repProg_scoped {b ℓ k B n : ℕ} {mL mR : List Mono} (hk : 0 < k) (hL : MonoIdx (k + 1) mL)
    (hR : MonoIdx (k + 1) mR) : Scoped k (repProg b ℓ k mL mR B n) := fun t ht =>
  repProg_cases (fun t s => s.Scoped (k + t)) (initStep_scoped b ℓ B (by omega))
    (fun o ho => by
      rw [show k + (1 + o) = k + 1 + o by omega]
      exact sumProg_scoped (by omega) hL o ho)
    (fun o ho => by
      rw [show k + (2 + 2 * mL.length + o) = k + 2 + 2 * mL.length + o by omega]
      exact sumProg_scoped (by omega) (hR.mono (by omega)) o ho) t ht

theorem mem_monos {k : ℕ} {f g : ℕ → ℕ} {m : Mono} (hm : m ∈ monos k f g) :
    m.1 ≤ k ∧ m.2.1 ≤ k ∧ ∃ a < k * k, m.2.2 = f a ∨ m.2.2 = g a := by
  have hd : ∀ a < k * k, a / k ≤ k ∧ a % k ≤ k := fun a ha => by
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at ha)
    exact ⟨(Nat.div_lt_of_lt_mul ha).le, (Nat.mod_lt _ hk).le⟩
  simp only [monos, List.mem_append, List.mem_map, List.mem_range] at hm
  rcases hm with ((⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
  · exact ⟨(hd a ha).1, (hd a ha).2, a, ha, Or.inl rfl⟩
  · exact ⟨le_rfl, (hd a ha).1, a, ha, Or.inr rfl⟩
  · exact ⟨le_rfl, (hd a ha).2, a, ha, Or.inr rfl⟩
  · exact ⟨le_rfl, le_rfl, a, ha, Or.inl rfl⟩

theorem monos_idx (k : ℕ) (f g : ℕ → ℕ) : MonoIdx (k + 1) (monos k f g) := by
  intro i
  rcases getD_mem_or (monos k f g) default i with h | h
  · have := mem_monos h; omega
  · rw [h]; exact ⟨Nat.succ_pos _, Nat.succ_pos _⟩

theorem length_monos (k : ℕ) (f g : ℕ → ℕ) : (monos k f g).length = 4 * (k * k) := by
  simp only [monos, List.length_append, List.length_map, List.length_range]; ring

/-! ## The run -/

theorem initStep_val (b ℓ C : ℕ) (x : ℕ → ℕ) (hC : C < 2 ^ (b * ℓ)) : (initStep b ℓ C).val b x = C := by
  simp [initStep, Step.val, Operand.eval, limbsVal_toLimbs hC]

theorem sumStep_val_even {b ℓ base p : ℕ} {ms : List Mono} (x : ℕ → ℕ) (hp : p % 2 = 0)
    (hc : (ms.getD (p / 2) default).2.2 < 2 ^ (b * ℓ)) :
    (sumStep b ℓ base ms p).val b x = (ms.getD (p / 2) default).2.2 * x (ms.getD (p / 2) default).1 := by
  simp only [sumStep, hp, ↓reduceIte, Step.val, Option.elim_none, Operand.eval, limbsVal_toLimbs hc, limbsVal_nil,
    zero_add, add_zero]
  try ring

theorem sumStep_val_odd {b ℓ base p : ℕ} {ms : List Mono} (x : ℕ → ℕ) (hp : p % 2 = 1) :
    (sumStep b ℓ base ms p).val b x =
      x (base + (p - 1)) + x (ms.getD (p / 2) default).2.1 * x (base + p) := by
  simp only [sumStep, hp, one_ne_zero, ↓reduceIte, Step.val, Option.elim_some, Operand.eval, limbsVal_nil, add_zero]

/-- **The accumulator's values**: `y_m = c_m x_{p_m}` and `acc_m = C + Σ_{i<m} c_i x_{p_i} x_{q_i}`, for any
assignment obeying the block's steps. -/
theorem sumProg_run {b ℓ base C : ℕ} {ms : List Mono} {R : ℕ → ℕ} (hC : C < 2 ^ (b * ℓ))
    (hms : ∀ i < ms.length, (ms.getD i default).2.2 < 2 ^ (b * ℓ))
    (hR : ∀ o < 2 * ms.length + 1, R (base + o) = ((sumProg b ℓ base C ms).getD o default).val b R) :
    (∀ m < ms.length, R (base + (2 * m + 1)) = (ms.getD m default).2.2 * R (ms.getD m default).1) ∧
    ∀ m ≤ ms.length, R (base + 2 * m) = C + ∑ i ∈ range m, Mono.val R (ms.getD i default) := by
  have hy : ∀ m < ms.length, R (base + (2 * m + 1)) = (ms.getD m default).2.2 * R (ms.getD m default).1 := by
    intro m hm
    have e : (2 * m) / 2 = m := by omega
    rw [hR _ (by omega), getD_sumProg_succ (by omega),
      sumStep_val_even R (by omega) (by rw [e]; exact hms m hm), e]
  refine ⟨hy, fun m hm => ?_⟩
  induction m with
  | zero =>
    have h := hR 0 (by omega)
    rw [add_zero, getD_sumProg_zero, initStep_val _ _ _ _ hC] at h
    simp [h]
  | succ m ih =>
    have e : (2 * m + 1) / 2 = m := by omega
    rw [show base + 2 * (m + 1) = base + (2 * m + 1 + 1) by ring, hR _ (by omega), getD_sumProg_succ (by omega),
      sumStep_val_odd R (by omega), e, show 2 * m + 1 - 1 = 2 * m by omega, ih (by omega), hy m (by omega),
      sum_range_succ]
    simp only [Mono.val]; ring

/-- Every value of an accumulator block is `≤ C + |ms| · V`. -/
theorem sumProg_bound {base C V : ℕ} {ms : List Mono} {R : ℕ → ℕ}
    (hy : ∀ m < ms.length, R (base + (2 * m + 1)) = (ms.getD m default).2.2 * R (ms.getD m default).1)
    (hacc : ∀ m ≤ ms.length, R (base + 2 * m) = C + ∑ i ∈ range m, Mono.val R (ms.getD i default))
    (hV1 : ∀ m < ms.length, (ms.getD m default).2.2 * R (ms.getD m default).1 ≤ V)
    (hV2 : ∀ m < ms.length, Mono.val R (ms.getD m default) ≤ V) :
    ∀ o < 2 * ms.length + 1, R (base + o) ≤ C + ms.length * V := by
  intro o ho
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' o
  · rw [hacc m (by omega)]
    have h1 : ∑ i ∈ range m, Mono.val R (ms.getD i default) ≤ m * V := by
      calc _ ≤ ∑ _i ∈ range m, V := sum_le_sum fun i hi => hV2 i (by have := mem_range.1 hi; omega)
        _ = m * V := by simp
    have h2 : m * V ≤ ms.length * V := Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [hy m (by omega)]
    have h1 := hV1 m (by omega)
    have h2 : V ≤ ms.length * V := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- **The blocks of the run**: `x_k = B`, and each accumulator block obeys its steps. -/
theorem repProg_blocks {b ℓ k B n : ℕ} {mL mR : List Mono} (hk : 0 < k) (hL : MonoIdx (k + 1) mL)
    (hR : MonoIdx (k + 1) mR) (hB : B < 2 ^ (b * ℓ)) (u : ℕ → ℕ) :
    slpRun b k (repProg b ℓ k mL mR B n) u (repProg b ℓ k mL mR B n).length k = B ∧
    (∀ o < 2 * mL.length + 1,
      slpRun b k (repProg b ℓ k mL mR B n) u (repProg b ℓ k mL mR B n).length (k + 1 + o) =
        ((sumProg b ℓ (k + 1) 0 mL).getD o default).val b
          (slpRun b k (repProg b ℓ k mL mR B n) u (repProg b ℓ k mL mR B n).length)) ∧
    (∀ o < 2 * mR.length + 1,
      slpRun b k (repProg b ℓ k mL mR B n) u (repProg b ℓ k mL mR B n).length (k + 2 + 2 * mL.length + o) =
        ((sumProg b ℓ (k + 2 + 2 * mL.length) n mR).getD o default).val b
          (slpRun b k (repProg b ℓ k mL mR B n) u (repProg b ℓ k mL mR B n).length)) := by
  have hP := repProg_scoped (b := b) (ℓ := ℓ) (B := B) (n := n) hk hL hR
  have hlen := length_repProg b ℓ k mL mR B n
  refine ⟨?_, fun o ho => ?_, fun o ho => ?_⟩
  · have h := slpRun_step (b := b) (u := u) hP (t := 0) (by omega)
    rw [add_zero, getD_repProg_zero, initStep_val _ _ _ _ hB] at h
    exact h
  · have h := slpRun_step (b := b) (u := u) hP (t := 1 + o) (by omega)
    rw [show k + (1 + o) = k + 1 + o by omega, getD_repProg_L ho] at h
    exact h
  · have h := slpRun_step (b := b) (u := u) hP (t := 2 + 2 * mL.length + o) (by omega)
    rw [show k + (2 + 2 * mL.length + o) = k + 2 + 2 * mL.length + o by omega, getD_repProg_R] at h
    exact h

/-! ## The shift identity -/

theorem sum_monos (k : ℕ) (f g : ℕ → ℕ) (x : ℕ → ℕ) :
    ((monos k f g).map (Mono.val x)).sum = ∑ m ∈ range (k * k),
      (f m * x (m / k) * x (m % k) + g m * x k * x (m / k) + g m * x k * x (m % k) + f m * x k * x k) := by
  simp only [monos, List.map_append, List.sum_append, List.map_map]
  rw [listSum_range, listSum_range, listSum_range, listSum_range]
  simp only [Function.comp_apply, Mono.val, sum_add_distrib]

/-- **The shift identity**: for `x` with `x_i = u_i` (`i < k`) and `x_k = B`, the left accumulator equals
`n` plus the right one iff `Q(u − B) = n`. -/
theorem monos_shift {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (x : ℕ → ℕ) (u : Fin k → ℕ) (B n : ℕ)
    (hx : ∀ i : Fin k, x i = u i) (hB : x k = B) :
    ((monoL A).map (Mono.val x)).sum = n + ((monoR A).map (Mono.val x)).sum ↔
      (fun i => (u i : ℤ) - B) ⬝ᵥ A *ᵥ (fun i => (u i : ℤ) - B) = n := by
  have key : (((monoL A).map (Mono.val x)).sum : ℤ) - ((monoR A).map (Mono.val x)).sum =
      (fun i => (u i : ℤ) - B) ⬝ᵥ A *ᵥ (fun i => (u i : ℤ) - B) := by
    calc (((monoL A).map (Mono.val x)).sum : ℤ) - ((monoR A).map (Mono.val x)).sum
        = ∑ m ∈ range (k * k), ent A (m / k) (m % k) * ((x (m / k) : ℤ) - B) * ((x (m % k) : ℤ) - B) := by
          rw [monoL, monoR, sum_monos, sum_monos, hB]
          push_cast
          rw [← sum_sub_distrib]
          refine sum_congr rfl fun m _ => ?_
          have h := Int.toNat_sub_toNat_neg (ent A (m / k) (m % k))
          simp only [posC, negC]
          linear_combination ((x (m / k) : ℤ) - B) * ((x (m % k) : ℤ) - B) * h
      _ = ∑ i ∈ range k, ∑ j ∈ range k, ent A i j * ((x i : ℤ) - B) * ((x j : ℤ) - B) :=
          sum_range_divmod (fun i j => ent A i j * ((x i : ℤ) - B) * ((x j : ℤ) - B)) k
      _ = ∑ i : Fin k, ∑ j : Fin k, ent A i j * ((x i : ℤ) - B) * ((x j : ℤ) - B) := by
          refine (Fin.sum_univ_eq_sum_range
            (fun i => ∑ j ∈ range k, ent A i j * ((x i : ℤ) - B) * ((x j : ℤ) - B)) k).symm.trans ?_
          refine sum_congr rfl fun i _ => ?_
          exact (Fin.sum_univ_eq_sum_range (fun j => ent A i j * ((x i : ℤ) - B) * ((x j : ℤ) - B)) k).symm
      _ = ∑ i : Fin k, ∑ j : Fin k, A i j * ((u i : ℤ) - B) * ((u j : ℤ) - B) := by
          refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
          simp [ent, hx]
      _ = (fun i => (u i : ℤ) - B) ⬝ᵥ A *ᵥ (fun i => (u i : ℤ) - B) := by
          simp only [dotProduct, mulVec, Finset.mul_sum]
          refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
          ring
  rw [← key]
  constructor
  · intro h; rw [h]; push_cast; ring
  · intro h
    have : (((monoL A).map (Mono.val x)).sum : ℤ) = n + ((monoR A).map (Mono.val x)).sum := by linarith
    exact_mod_cast this

/-! ## Coefficient bounds -/

theorem natAbs_ent_le {k cm : ℕ} {A : Matrix (Fin k) (Fin k) ℤ} (hcm : ∀ i j, (A i j).natAbs ≤ cm) (i j : ℕ) :
    (ent A i j).natAbs ≤ cm := by
  unfold ent; split_ifs
  · exact hcm _ _
  · simp

theorem posC_le {k cm : ℕ} {A : Matrix (Fin k) (Fin k) ℤ} (hcm : ∀ i j, (A i j).natAbs ≤ cm) (m : ℕ) :
    posC A m ≤ cm := by
  have := natAbs_ent_le hcm (m / k) (m % k)
  unfold posC; omega

theorem negC_le {k cm : ℕ} {A : Matrix (Fin k) (Fin k) ℤ} (hcm : ∀ i j, (A i j).natAbs ≤ cm) (m : ℕ) :
    negC A m ≤ cm := by
  have := natAbs_ent_le hcm (m / k) (m % k)
  unfold negC; omega

theorem monos_coef_le {k cm : ℕ} {f g : ℕ → ℕ} (hf : ∀ m, f m ≤ cm) (hg : ∀ m, g m ≤ cm) (i : ℕ) :
    ((monos k f g).getD i default).2.2 ≤ cm := by
  rcases getD_mem_or (monos k f g) default i with h | h
  · obtain ⟨-, -, a, -, e | e⟩ := mem_monos h <;> rw [e]
    exacts [hf a, hg a]
  · rw [h]; exact Nat.zero_le _

theorem natAbs_le_cM {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (i j : Fin k) : (A i j).natAbs ≤ cM A := by
  unfold cM
  calc (A i j).natAbs ≤ ∑ j', (A i j').natAbs :=
        Finset.single_le_sum (f := fun j' => (A i j').natAbs) (fun _ _ => Nat.zero_le _) (mem_univ j)
    _ ≤ ∑ i', ∑ j', (A i' j').natAbs :=
        Finset.single_le_sum (f := fun i' => ∑ j', (A i' j').natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)

/-! ## The count -/

theorem length_monoL {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) : (monoL A).length = 4 * (k * k) :=
  length_monos _ _ _

theorem length_monoR {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) : (monoR A).length = 4 * (k * k) :=
  length_monos _ _ _

theorem monoL_idx {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) : MonoIdx (k + 1) (monoL A) := monos_idx _ _ _

theorem monoR_idx {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) : MonoIdx (k + 1) (monoR A) := monos_idx _ _ _

/-- The final comparison holds iff `Q(u − B) = n`. -/
theorem repDesc_finHolds_iff {k b ℓ cm B n : ℕ} {A : Matrix (Fin k) (Fin k) ℤ} (hk : 0 < k)
    (hcm : ∀ i j, (A i j).natAbs ≤ cm) (hB1 : 1 ≤ B) (hlimb : n + repK k cm * B ^ 2 < 2 ^ (b * ℓ))
    (u : Fin k → ℕ) :
    FinHolds b (repFin k (monoL A) (monoR A))
        (slpRun b k (repProg b ℓ k (monoL A) (monoR A) B n) (extV k u)
          (repProg b ℓ k (monoL A) (monoR A) B n).length) ↔
      (fun i => (u i : ℤ) - B) ⬝ᵥ A *ᵥ (fun i => (u i : ℤ) - B) = n := by
  have hK : 0 < repK k cm := by unfold repK; positivity
  have hBB : B ≤ repK k cm * B ^ 2 := by
    calc B ≤ B ^ 2 := by nlinarith
      _ ≤ repK k cm * B ^ 2 := Nat.le_mul_of_pos_left _ hK
  have hcmK : cm ≤ repK k cm * B ^ 2 := by
    have : cm ≤ repK k cm := by unfold repK; nlinarith
    exact this.trans (Nat.le_mul_of_pos_right _ (by positivity))
  have hBl : B < 2 ^ (b * ℓ) := by omega
  have hcL : ∀ i < (monoL A).length, ((monoL A).getD i default).2.2 < 2 ^ (b * ℓ) := fun i _ =>
    lt_of_le_of_lt (monos_coef_le (posC_le hcm) (negC_le hcm) i) (by omega)
  have hcR : ∀ i < (monoR A).length, ((monoR A).getD i default).2.2 < 2 ^ (b * ℓ) := fun i _ =>
    lt_of_le_of_lt (monos_coef_le (negC_le hcm) (posC_le hcm) i) (by omega)
  obtain ⟨hRk, hLb, hRb⟩ := repProg_blocks (n := n) hk (monoL_idx A) (monoR_idx A) hBl (extV k u)
  obtain ⟨-, hLacc⟩ := sumProg_run (Nat.two_pow_pos _) hcL hLb
  obtain ⟨-, hRacc⟩ := sumProg_run (by omega) hcR hRb
  simp only [FinHolds, repFin, List.mem_singleton, forall_eq, CmpRel.Holds, Operand.eval]
  rw [hLacc _ le_rfl, hRacc _ le_rfl, sum_range_getD, sum_range_getD, zero_add]
  refine monos_shift A _ u B n (fun i => ?_) hRk
  rw [slpRun_of_lt i.isLt, extV_eq_of_lt _ i.isLt]

/-- **The count of the representation-number description**: for `Coercive A c`, `|A_ij| ≤ cm`,
`c n < B` and `n + repK k cm · B² < Bx, 2^{bℓ}`, it is the number of solutions `#(sols A c n)`. -/
theorem repDesc_count {k b ℓ c cm n B Bx : ℕ} {A : Matrix (Fin k) (Fin k) ℤ} (hk : 0 < k)
    (hc : Coercive A c) (hcm : ∀ i j, (A i j).natAbs ≤ cm) (hB : c * n < B)
    (hBx : n + repK k cm * B ^ 2 < Bx) (hlimb : n + repK k cm * B ^ 2 < 2 ^ (b * ℓ)) :
    (repDesc b ℓ k (monoL A) (monoR A) B n).countB b Bx = (sols A c n).card := by
  have hB1 : 1 ≤ B := by omega
  have hK : 16 ≤ repK k cm := by unfold repK; nlinarith
  have h2B : 2 * B ≤ repK k cm * B ^ 2 := by nlinarith
  have hBx' : B + c * n < Bx := by omega
  have hP := repProg_scoped (b := b) (ℓ := ℓ) (B := B) (n := n) hk (monoL_idx A) (monoR_idx A)
  unfold repDesc
  rw [slpDesc_count hP, ← card_shift hc hB hBx']
  · congr 1
    apply filter_congr
    intro u _
    exact repDesc_finHolds_iff hk hcm hB1 hlimb u
  · -- every aux value of a solution lies in the box
    intro u _ hf t ht
    have hq := (repDesc_finHolds_iff hk hcm hB1 hlimb u).1 hf
    have hu : ∀ i, u i < 2 * B := fun i => (shift_bounds hc hB u hq i).2
    have hBl : B < 2 ^ (b * ℓ) := by
      have : B ≤ repK k cm * B ^ 2 := by nlinarith
      omega
    have hcmK : cm ≤ repK k cm * B ^ 2 := by
      have : cm ≤ repK k cm := by unfold repK; nlinarith
      exact this.trans (Nat.le_mul_of_pos_right _ (by positivity))
    have hcL : ∀ i < (monoL A).length, ((monoL A).getD i default).2.2 < 2 ^ (b * ℓ) := fun i _ =>
      lt_of_le_of_lt (monos_coef_le (posC_le hcm) (negC_le hcm) i) (by omega)
    have hcR : ∀ i < (monoR A).length, ((monoR A).getD i default).2.2 < 2 ^ (b * ℓ) := fun i _ =>
      lt_of_le_of_lt (monos_coef_le (negC_le hcm) (posC_le hcm) i) (by omega)
    obtain ⟨hRk, hLb, hRb⟩ := repProg_blocks (n := n) hk (monoL_idx A) (monoR_idx A) hBl (extV k u)
    obtain ⟨hLy, hLacc⟩ := sumProg_run (Nat.two_pow_pos _) hcL hLb
    obtain ⟨hRy, hRacc⟩ := sumProg_run (by omega) hcR hRb
    set R := slpRun b k (repProg b ℓ k (monoL A) (monoR A) B n) (extV k u)
      (repProg b ℓ k (monoL A) (monoR A) B n).length with hRdef
    -- the free values and `x_k` are `≤ 2B`
    have hx : ∀ p ≤ k, R p ≤ 2 * B := by
      intro p hp
      rcases Nat.lt_or_ge p k with h | h
      · rw [hRdef, slpRun_of_lt h, extV_eq_of_lt _ h]; exact (hu _).le
      · obtain rfl : p = k := by omega
        rw [hRk]; omega
    have hV : ∀ (ms : List Mono), MonoIdx (k + 1) ms → (∀ i, (ms.getD i default).2.2 ≤ cm) →
        (∀ m < ms.length, (ms.getD m default).2.2 * R (ms.getD m default).1 ≤ 4 * cm * B ^ 2) ∧
        (∀ m < ms.length, Mono.val R (ms.getD m default) ≤ 4 * cm * B ^ 2) := by
      intro ms hidx hco
      refine ⟨fun m _ => ?_, fun m _ => ?_⟩
      · have h1 := hx _ (Nat.lt_succ_iff.1 (hidx m).1)
        have h2 := hco m
        calc _ ≤ cm * (2 * B) := Nat.mul_le_mul h2 h1
          _ ≤ cm * (4 * B ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
          _ = 4 * cm * B ^ 2 := by ring
      · have h1 := hx _ (Nat.lt_succ_iff.1 (hidx m).1)
        have h1' := hx _ (Nat.lt_succ_iff.1 (hidx m).2)
        have h2 := hco m
        unfold Mono.val
        calc _ ≤ cm * (2 * B) * (2 * B) := Nat.mul_le_mul (Nat.mul_le_mul h2 h1) h1'
          _ = 4 * cm * B ^ 2 := by ring
    obtain ⟨hL1, hL2⟩ := hV _ (monoL_idx A) (monos_coef_le (posC_le hcm) (negC_le hcm))
    obtain ⟨hR1, hR2⟩ := hV _ (monoR_idx A) (monos_coef_le (negC_le hcm) (posC_le hcm))
    have hbL := sumProg_bound hLy hLacc hL1 hL2
    have hbR := sumProg_bound hRy hRacc hR1 hR2
    have hT : 4 * (k * k) * (4 * cm * B ^ 2) ≤ repK k cm * B ^ 2 := by
      have : 16 * (k * k) * cm ≤ repK k cm := by
        unfold repK
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.le_succ _)) (Nat.le_succ _)
      calc 4 * (k * k) * (4 * cm * B ^ 2) = 16 * (k * k) * cm * B ^ 2 := by ring
        _ ≤ repK k cm * B ^ 2 := Nat.mul_le_mul_right _ this
    rw [length_monoL] at hbL
    rw [length_monoR] at hbR
    rw [length_repProg, length_monoL, length_monoR] at ht
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      rw [add_zero, hRk]; omega
    rcases Nat.lt_or_ge t (2 * (4 * (k * k)) + 2) with h' | h'
    · have := hbL (t - 1) (by omega)
      rw [show k + 1 + (t - 1) = k + t by omega] at this
      omega
    · have := hbR (t - (2 + 2 * (monoL A).length)) (by rw [length_monoL]; omega)
      rw [length_monoL, show k + 2 + 2 * (4 * (k * k)) + (t - (2 + 2 * (4 * (k * k)))) = k + t by omega] at this
      omega

/-! ## Well-formedness and shape -/

/-- The well-formedness conditions of `slpDesc_WF` for one step, with `N` variables. -/
def StepOK (b ℓ N : ℕ) (s : Step) : Prop :=
  s.2.1 < N ∧ s.2.2.1.OK b ℓ N ∧ (∀ a ∈ s.1, a < N) ∧ s.2.2.2.length ≤ ℓ ∧ ∀ y ∈ s.2.2.2, y < 2 ^ b

theorem initStep_ok (b ℓ C : ℕ) {N : ℕ} (hN : 0 < N) : StepOK b ℓ N (initStep b ℓ C) :=
  ⟨hN, ⟨by simp, by simp⟩, by simp [initStep], toLimbs_OK b ℓ C⟩

theorem sumProg_ok {b ℓ base C N : ℕ} {ms : List Mono} (hN : base + 2 * ms.length ≤ N) (h0 : 0 < N)
    (hms : MonoIdx N ms) : ∀ o < 2 * ms.length + 1, StepOK b ℓ N ((sumProg b ℓ base C ms).getD o default) :=
  sumProg_cases (fun _ s => StepOK b ℓ N s) (initStep_ok b ℓ C h0) fun p hp => by
    unfold sumStep
    have h := hms (p / 2)
    split_ifs
    · exact ⟨h.1, toLimbs_OK _ _ _, by simp, by simp, by simp⟩
    · refine ⟨h.2, show base + p < N by omega, fun a ha => ?_, by simp, by simp⟩
      simp only [Option.mem_def, Option.some.injEq] at ha; omega

/-- **Well-formedness** (no size hypotheses). -/
theorem repDesc_WF {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (hk : 0 < k) (b ℓ nB B n : ℕ) :
    (repDesc b ℓ k (monoL A) (monoR A) B n).WFB b ℓ nB := by
  have hlen := length_repProg b ℓ k (monoL A) (monoR A) B n
  have hL := length_monoL A
  have hR := length_monoR A
  unfold repDesc
  refine slpDesc_WF (fun s hs => ?_) (fun q hq => ?_)
  · refine forall_mem_of_getD (d := default) (Φ := StepOK b ℓ (k + (repProg b ℓ k (monoL A) (monoR A) B n).length)) ?_ s hs
    refine repProg_cases (fun _ s => StepOK b ℓ (k + (repProg b ℓ k (monoL A) (monoR A) B n).length) s)
      (initStep_ok _ _ _ (by omega)) (fun o ho => ?_) (fun o ho => ?_)
    · exact sumProg_ok (by omega) (by omega) ((monoL_idx A).mono (by omega)) o ho
    · exact sumProg_ok (by omega) (by omega) ((monoR_idx A).mono (by omega)) o ho
  · simp only [repFin, List.mem_singleton] at hq
    subst hq
    constructor
    · show k + 1 + 2 * (monoL A).length < _; omega
    · show k + 2 + 2 * (monoL A).length + 2 * (monoR A).length < _; omega

/-- **The shape constant**: `64 (nV + nP + nQ + 1)(nC + 1) = repCD k`. -/
theorem repDesc_cA_eq {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (b ℓ B n : ℕ) :
    64 * (((repDesc b ℓ k (monoL A) (monoR A) B n).nV + (repDesc b ℓ k (monoL A) (monoR A) B n).prods.length +
      (repDesc b ℓ k (monoL A) (monoR A) B n).cmps.length + 1) *
      ((repDesc b ℓ k (monoL A) (monoR A) B n).chains.length + 1)) = repCD k := by
  unfold repDesc
  rw [slpDesc_cA_eq, length_repProg, length_monoL, length_monoR]
  simp only [repFin, List.length_singleton, repCD]
  ring

end EthFollowup.ModP
