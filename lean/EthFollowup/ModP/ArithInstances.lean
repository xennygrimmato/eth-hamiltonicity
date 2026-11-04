/-
# ArithNet instances (E1): the concrete descriptions of the headline problems and their counts

Pure Mathlib (imports `ArithDesc` and E2's pure count files); compiles in both toolchains.

For each instance: a description built from the input number(s) and the limb parameters `b, ℓ`
(constants enter as `toLimbs b ℓ N`, `ℓ` limbs of `b` bits: PolyT-friendly `List.range`/`map`/`/`/`%`),
its well-formedness `WFB b ℓ nB`, and `countB b B D = <E2's pure count>` (box `[0, B)`; the network uses
`b = b n`, `ℓ = ℓ n`, `B = 2^(nB n)`, `nB = nB n`, so `Desc.count n D = D.countB (b n) (2 ^ nB n)`).

* (E) class forms: `hDesc1 b ℓ N`, `hDesc2 b ℓ N` (variables `a, b, c`; products `b·b`, `a·c`;
  chain `1·(b·b) + 1·N = 4·(a·c)`; query 1: `b ≤ a`, `a ≤ c`; query 2: `b > 0`, `b < a`, `a < c`).
  `hDesc1_count : countB = hQ1 B N`, `hDesc2_count`, **`hDesc_count : countB₁ + countB₂ = hForm (−N)`**.
* (A) square roots: `sqDescA b ℓ n m a π` (variables `y, k, x`; `y·y = x + k·m`, `y < m`, `x < m`, `x = a`,
  prefix pattern on `y`): `sqDescA_count : countB b (2^n') … = S3A n' n m a π`.
* (B) least QNR: `sqDescB b ℓ n p π` (prefix pattern on `x`, no `x = a`): `sqDescB_count : … = S3B n' n p π`.
* (F) `divDesc` (`a·b + s = x`, `a, b > 0`) `= divQ`; `circDesc` (`a·a + b·b + s = x`, `a > 0`) `= circQ`;
  `sigDesc` (`a·b + s = x`, `b > 0`, `c > 0`, `c ≤ a`; four variables) `= sigQ`.
* Generic: `toLimbs`, `limbsVal_toLimbs`, `tri`/`card_pi3`, `quad`/`card_pi4`, `countB_tri`, `countB_quad`,
  `prePat n π` (pattern of the prefix `π` on the bits `≥ n − |π|`) with `patMatch_prePat`.

Standard axioms only.
-/
import EthFollowup.ModP.ArithDesc
import EthFollowup.ModP.ClassForms
import EthFollowup.ModP.Lattice
import EthFollowup.ModP.QRCount
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

set_option linter.unusedSectionVars false

namespace EthFollowup.ModP

open Finset

/-! ## Constants -/

/-- The `ℓ` limbs (`b` bits each, little-endian) of `N`. -/
def toLimbs (b ℓ N : ℕ) : List ℕ := (List.range ℓ).map fun i => N / 2 ^ (b * i) % 2 ^ b

theorem length_toLimbs (b ℓ N : ℕ) : (toLimbs b ℓ N).length = ℓ := by simp [toLimbs]

theorem toLimbs_lt (b ℓ N : ℕ) : ∀ y ∈ toLimbs b ℓ N, y < 2 ^ b := by
  intro y hy
  simp only [toLimbs, List.mem_map, List.mem_range] at hy
  obtain ⟨i, -, rfl⟩ := hy
  exact Nat.mod_lt _ (by positivity)

theorem limbsVal_toLimbs {b ℓ N : ℕ} (hN : N < 2 ^ (b * ℓ)) : limbsVal b (toLimbs b ℓ N) = N := by
  unfold limbsVal
  rw [length_toLimbs]
  have : ∀ i ∈ range ℓ, (toLimbs b ℓ N).getD i 0 * 2 ^ (b * i) = N / 2 ^ (b * i) % 2 ^ b * 2 ^ (b * i) :=
    fun i hi => by
      rw [List.getD_eq_getElem _ _ (by rw [length_toLimbs]; exact mem_range.1 hi)]
      simp [toLimbs]
  rw [sum_congr rfl this]
  exact sum_limb b ℓ N hN

theorem toLimbs_OK (b ℓ N : ℕ) : (toLimbs b ℓ N).length ≤ ℓ ∧ ∀ y ∈ toLimbs b ℓ N, y < 2 ^ b :=
  ⟨(length_toLimbs b ℓ N).le, toLimbs_lt b ℓ N⟩

@[simp] theorem limbsVal_nil (b : ℕ) : limbsVal b [] = 0 := by simp [limbsVal]

/-! ## Tuples -/

/-- A triple as a variable assignment. -/
def tri (t : ℕ × ℕ × ℕ) : ℕ → ℕ := fun v => if v = 0 then t.1 else if v = 1 then t.2.1 else if v = 2 then t.2.2 else 0

/-- A quadruple as a variable assignment. -/
def quad (t : ℕ × ℕ × ℕ × ℕ) : ℕ → ℕ := fun v =>
  if v = 0 then t.1 else if v = 1 then t.2.1 else if v = 2 then t.2.2.1 else if v = 3 then t.2.2.2 else 0

@[simp] theorem tri_0 (t : ℕ × ℕ × ℕ) : tri t 0 = t.1 := rfl
@[simp] theorem tri_1 (t : ℕ × ℕ × ℕ) : tri t 1 = t.2.1 := rfl
@[simp] theorem tri_2 (t : ℕ × ℕ × ℕ) : tri t 2 = t.2.2 := rfl
@[simp] theorem quad_0 (t : ℕ × ℕ × ℕ × ℕ) : quad t 0 = t.1 := rfl
@[simp] theorem quad_1 (t : ℕ × ℕ × ℕ × ℕ) : quad t 1 = t.2.1 := rfl
@[simp] theorem quad_2 (t : ℕ × ℕ × ℕ × ℕ) : quad t 2 = t.2.2.1 := rfl
@[simp] theorem quad_3 (t : ℕ × ℕ × ℕ × ℕ) : quad t 3 = t.2.2.2 := rfl

theorem extV_three (x : Fin 3 → ℕ) : extV 3 x = tri (x 0, x 1, x 2) := by
  funext v
  unfold extV tri
  rcases v with _ | _ | _ | v <;> simp

theorem extV_four (x : Fin 4 → ℕ) : extV 4 x = quad (x 0, x 1, x 2, x 3) := by
  funext v
  unfold extV quad
  rcases v with _ | _ | _ | _ | v <;> simp

theorem card_pi3 (B : ℕ) (P : (ℕ → ℕ) → Prop) [DecidablePred P] :
    ((Fintype.piFinset fun _ : Fin 3 => range B).filter fun x => P (extV 3 x)).card =
      ((range B ×ˢ range B ×ˢ range B).filter fun t => P (tri t)).card := by
  refine card_bij' (fun x _ => (x 0, x 1, x 2)) (fun t _ => ![t.1, t.2.1, t.2.2]) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, Fintype.mem_piFinset] at hx
    simp only [mem_filter, mem_product]
    exact ⟨⟨hx.1 0, hx.1 1, hx.1 2⟩, by rw [← extV_three]; exact hx.2⟩
  · intro t ht
    simp only [mem_filter, mem_product] at ht
    simp only [mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [ht.1.1, ht.1.2.1, ht.1.2.2]
    · rw [extV_three]; simpa using ht.2
  · intro x _; funext i; fin_cases i <;> rfl
  · intro t _; rfl

theorem card_pi4 (B : ℕ) (P : (ℕ → ℕ) → Prop) [DecidablePred P] :
    ((Fintype.piFinset fun _ : Fin 4 => range B).filter fun x => P (extV 4 x)).card =
      ((range B ×ˢ range B ×ˢ range B ×ˢ range B).filter fun t => P (quad t)).card := by
  refine card_bij' (fun x _ => (x 0, x 1, x 2, x 3)) (fun t _ => ![t.1, t.2.1, t.2.2.1, t.2.2.2]) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, Fintype.mem_piFinset] at hx
    simp only [mem_filter, mem_product]
    exact ⟨⟨hx.1 0, hx.1 1, hx.1 2, hx.1 3⟩, by rw [← extV_four]; exact hx.2⟩
  · intro t ht
    simp only [mem_filter, mem_product] at ht
    simp only [mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [ht.1.1, ht.1.2.1, ht.1.2.2.1, ht.1.2.2.2]
    · rw [extV_four]; simpa using ht.2
  · intro x _; funext i; fin_cases i <;> rfl
  · intro t _; rfl

/-- A description with three variables counts triples. -/
theorem countB_tri {b B : ℕ} {D : Desc} (h : D.nV = 3) :
    D.countB b B = ((range B ×ˢ range B ×ˢ range B).filter fun t => D.Sat b (tri t)).card := by
  unfold Desc.countB
  generalize D.nV = k at h ⊢
  subst h
  exact card_pi3 B (D.Sat b)

/-- A description with four variables counts quadruples. -/
theorem countB_quad {b B : ℕ} {D : Desc} (h : D.nV = 4) :
    D.countB b B = ((range B ×ˢ range B ×ˢ range B ×ˢ range B).filter fun t => D.Sat b (quad t)).card := by
  unfold Desc.countB
  generalize D.nV = k at h ⊢
  subst h
  exact card_pi4 B (D.Sat b)

/-! ## (E) class forms -/

/-- The common part: variables `a = 0, b = 1, c = 2`; products `b·b`, `a·c`;
chain `1·(b·b) + 1·N = 4·(a·c)`. -/
def hProds : List ProdD := [⟨1, .var 1⟩, ⟨0, .var 2⟩]
def hChains (b ℓ N : ℕ) : List ChainD := [⟨[⟨1, .prod 0⟩, ⟨1, .const (toLimbs b ℓ N)⟩], [⟨4, .prod 1⟩]⟩]

/-- (E) query 1: `b ≤ a`, `a ≤ c`. -/
def hDesc1 (b ℓ N : ℕ) : Desc :=
  { nV := 3, pat := [], prods := hProds, chains := hChains b ℓ N,
    cmps := [⟨1, .var 0, .le⟩, ⟨0, .var 2, .le⟩] }

/-- (E) query 2: `b > 0`, `b < a`, `a < c`. -/
def hDesc2 (b ℓ N : ℕ) : Desc :=
  { nV := 3, pat := [], prods := hProds, chains := hChains b ℓ N,
    cmps := [⟨1, .const [], .gt⟩, ⟨1, .var 0, .lt⟩, ⟨0, .var 2, .lt⟩] }

theorem hDesc1_count {b ℓ N B : ℕ} (hN : N < 2 ^ (b * ℓ)) : (hDesc1 b ℓ N).countB b B = hQ1 B N := by
  rw [countB_tri rfl, hQ1]
  congr 1
  refine filter_congr fun t _ => ?_
  simp [Desc.Sat, hDesc1, hProds, hChains, sideVal, Src.eval, ProdD.eval, Operand.eval, CmpRel.Holds,
    limbsVal_toLimbs hN, patMatch]
  tauto

theorem hDesc2_count {b ℓ N B : ℕ} (hN : N < 2 ^ (b * ℓ)) : (hDesc2 b ℓ N).countB b B = hQ2 B N := by
  rw [countB_tri rfl, hQ2]
  congr 1
  refine filter_congr fun t _ => ?_
  simp [Desc.Sat, hDesc2, hProds, hChains, sideVal, Src.eval, ProdD.eval, Operand.eval, CmpRel.Holds,
    limbsVal_toLimbs hN, patMatch]
  tauto

/-- **(E)**: the two query counts give the number of reduced forms of discriminant `−N`. -/
theorem hDesc_count {b ℓ N B : ℕ} (hN0 : 0 < N) (hNB : N < B) (hN : N < 2 ^ (b * ℓ)) :
    (hDesc1 b ℓ N).countB b B + (hDesc2 b ℓ N).countB b B = hForm (-(N : ℤ)) := by
  rw [hDesc1_count hN, hDesc2_count hN, hForm_split N hN0 hNB]

theorem hDesc1_WF (b ℓ nB N : ℕ) : (hDesc1 b ℓ N).WFB b ℓ nB where
  pat_len := by simp [hDesc1]
  prod_ok := by simp [hDesc1, hProds, Operand.OK]
  term_ok := by
    simp only [hDesc1, hChains, List.mem_singleton, forall_eq, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, Src.OK, hProds]
    exact ⟨by decide, toLimbs_OK b ℓ N, by decide⟩
  coeff_le := by simp [hDesc1, hChains]
  prod_once := by simp [hDesc1, hChains]
  cmp_ok := by simp [hDesc1, Operand.OK]

theorem hDesc2_WF (b ℓ nB N : ℕ) : (hDesc2 b ℓ N).WFB b ℓ nB where
  pat_len := by simp [hDesc2]
  prod_ok := by simp [hDesc2, hProds, Operand.OK]
  term_ok := by
    simp only [hDesc2, hChains, List.mem_singleton, forall_eq, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, Src.OK, hProds]
    exact ⟨by decide, toLimbs_OK b ℓ N, by decide⟩
  coeff_le := by simp [hDesc2, hChains]
  prod_once := by simp [hDesc2, hChains]
  cmp_ok := by simp [hDesc2, Operand.OK]

/-! ## (F) divisor sums and the circle count -/

/-- `a·b + s = x`, `a > 0`, `b > 0` (variables `a = 0, b = 1, s = 2`). -/
def divDesc (b ℓ x : ℕ) : Desc :=
  { nV := 3, pat := [], prods := [⟨0, .var 1⟩],
    chains := [⟨[⟨1, .prod 0⟩, ⟨1, .lin 2⟩], [⟨1, .const (toLimbs b ℓ x)⟩]⟩],
    cmps := [⟨0, .const [], .gt⟩, ⟨1, .const [], .gt⟩] }

/-- `a·a + b·b + s = x`, `a > 0`. -/
def circDesc (b ℓ x : ℕ) : Desc :=
  { nV := 3, pat := [], prods := [⟨0, .var 0⟩, ⟨1, .var 1⟩],
    chains := [⟨[⟨1, .prod 0⟩, ⟨1, .prod 1⟩, ⟨1, .lin 2⟩], [⟨1, .const (toLimbs b ℓ x)⟩]⟩],
    cmps := [⟨0, .const [], .gt⟩] }

/-- `a·b + s = x`, `b > 0`, `c > 0`, `c ≤ a` (variables `a = 0, b = 1, c = 2, s = 3`). -/
def sigDesc (b ℓ x : ℕ) : Desc :=
  { nV := 4, pat := [], prods := [⟨0, .var 1⟩],
    chains := [⟨[⟨1, .prod 0⟩, ⟨1, .lin 3⟩], [⟨1, .const (toLimbs b ℓ x)⟩]⟩],
    cmps := [⟨1, .const [], .gt⟩, ⟨2, .const [], .gt⟩, ⟨2, .var 0, .le⟩] }

theorem divDesc_count {b ℓ x B : ℕ} (hx : x < 2 ^ (b * ℓ)) : (divDesc b ℓ x).countB b B = divQ B x := by
  rw [countB_tri rfl, divQ]
  congr 1
  refine filter_congr fun t _ => ?_
  simp [Desc.Sat, divDesc, sideVal, Src.eval, ProdD.eval, Operand.eval, CmpRel.Holds,
    limbsVal_toLimbs hx, patMatch]
  tauto

theorem circDesc_count {b ℓ x B : ℕ} (hx : x < 2 ^ (b * ℓ)) : (circDesc b ℓ x).countB b B = circQ B x := by
  rw [countB_tri rfl, circQ]
  congr 1
  refine filter_congr fun t _ => ?_
  simp [Desc.Sat, circDesc, sideVal, Src.eval, ProdD.eval, Operand.eval, CmpRel.Holds,
    limbsVal_toLimbs hx, patMatch, add_assoc]
  tauto

theorem sigDesc_count {b ℓ x B : ℕ} (hx : x < 2 ^ (b * ℓ)) : (sigDesc b ℓ x).countB b B = sigQ B x := by
  rw [countB_quad rfl, sigQ]
  congr 1
  refine filter_congr fun t _ => ?_
  simp [Desc.Sat, sigDesc, sideVal, Src.eval, ProdD.eval, Operand.eval, CmpRel.Holds,
    limbsVal_toLimbs hx, patMatch]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h4, h1, h2, h3⟩
  · rintro ⟨h4, h1, h2, h3⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩

/-- **(F)**: the divisor sum `Σ_{m ≤ x} τ(m)` (any box `B > x`). -/
theorem divDesc_count_eq {b ℓ x B : ℕ} (hxB : x < B) (hx : x < 2 ^ (b * ℓ)) :
    (divDesc b ℓ x).countB b B = divSum x := by rw [divDesc_count hx, divQ_eq hxB]

/-- **(F)**: the Gauss circle count `#{(u, v) ∈ ℤ² : u² + v² ≤ x} = 4·count + 1`. -/
theorem circDesc_count_eq {b ℓ x B : ℕ} (hxB : x < B) (hx : x < 2 ^ (b * ℓ)) :
    4 * (circDesc b ℓ x).countB b B + 1 = circ x := by rw [circDesc_count hx, circ_eq hxB]

/-- **(F)**: `Σ_{m ≤ x} σ(m)`. -/
theorem sigDesc_count_eq {b ℓ x B : ℕ} (hxB : x < B) (hx : x < 2 ^ (b * ℓ)) :
    (sigDesc b ℓ x).countB b B = sigSum x := by rw [sigDesc_count hx, sigQ_eq hxB]

theorem divDesc_WF (b ℓ nB x : ℕ) : (divDesc b ℓ x).WFB b ℓ nB where
  pat_len := by simp [divDesc]
  prod_ok := by simp [divDesc, Operand.OK]
  term_ok := by
    simp only [divDesc, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Src.OK]
    exact ⟨by decide, by decide, toLimbs_OK b ℓ x⟩
  coeff_le := by simp [divDesc]
  prod_once := by simp [divDesc]
  cmp_ok := by simp [divDesc, Operand.OK]

theorem circDesc_WF (b ℓ nB x : ℕ) : (circDesc b ℓ x).WFB b ℓ nB where
  pat_len := by simp [circDesc]
  prod_ok := by simp [circDesc, Operand.OK]
  term_ok := by
    simp only [circDesc, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Src.OK]
    exact ⟨by decide, by decide, by decide, toLimbs_OK b ℓ x⟩
  coeff_le := by simp [circDesc]
  prod_once := by simp [circDesc]
  cmp_ok := by simp [circDesc, Operand.OK]

theorem sigDesc_WF (b ℓ nB x : ℕ) : (sigDesc b ℓ x).WFB b ℓ nB where
  pat_len := by simp [sigDesc]
  prod_ok := by simp [sigDesc, Operand.OK]
  term_ok := by
    simp only [sigDesc, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Src.OK]
    exact ⟨by decide, by decide, toLimbs_OK b ℓ x⟩
  coeff_le := by simp [sigDesc]
  prod_once := by simp [sigDesc]
  cmp_ok := by simp [sigDesc, Operand.OK]

/-! ## Prefix patterns -/

/-- The pattern of the prefix `π` (big-endian, `Search.ofWord`) on the bits `≥ n − |π|` of an `n`-bit number. -/
def prePat (n : ℕ) (π : List Bool) : List (Option Bool) :=
  (List.range n).map fun j =>
    if n - π.length ≤ j then some ((Factoring.Search.ofWord π).testBit (j - (n - π.length))) else none

theorem length_prePat (n : ℕ) (π : List Bool) : (prePat n π).length = n := by simp [prePat]

theorem patMatch_prePat_iff (n : ℕ) (π : List Bool) (y : ℕ) :
    patMatch (prePat n π) y ↔ ∀ j, n - π.length ≤ j → j < n →
      y.testBit j = (Factoring.Search.ofWord π).testBit (j - (n - π.length)) := by
  unfold patMatch
  rw [length_prePat]
  constructor
  · intro h j hsj hjn
    have := h j hjn
    rw [List.getD_eq_getElem _ _ (by rw [length_prePat]; exact hjn)] at this
    simp only [prePat, List.getElem_map, List.getElem_range, if_pos hsj, optBit, beq_iff_eq] at this
    exact this
  · intro h j hjn
    rw [List.getD_eq_getElem _ _ (by rw [length_prePat]; exact hjn)]
    simp only [prePat, List.getElem_map, List.getElem_range]
    split_ifs with hsj
    · simp [optBit, h j hsj hjn]
    · rfl

/-- The prefix pattern is the prefix test `y / 2^(n−|π|) = ofWord π` on `n`-bit numbers. -/
theorem patMatch_prePat {n : ℕ} {π : List Bool} (hπ : π.length ≤ n) {y : ℕ} (hy : y < 2 ^ n) :
    patMatch (prePat n π) y ↔ y / 2 ^ (n - π.length) = Factoring.Search.ofWord π := by
  have hc : Factoring.Search.ofWord π < 2 ^ π.length := Factoring.Search.ofWord_lt π
  rw [patMatch_prePat_iff]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow]
    by_cases hi : i + (n - π.length) < n
    · rw [h _ (by omega) hi, Nat.add_sub_cancel]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · intro h j hsj _
    rw [← h, Nat.testBit_div_two_pow, Nat.sub_add_cancel hsj]

theorem forall_lt_three (P : ℕ → Prop) : (∀ v < 3, P v) ↔ P 0 ∧ P 1 ∧ P 2 :=
  ⟨fun h => ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega)⟩, fun ⟨h0, h1, h2⟩ v hv => by
    interval_cases v <;> assumption⟩

@[simp] theorem patMatch_nil (y : ℕ) : patMatch [] y := fun j hj => absurd hj (by simp)

/-! ## (A) square roots modulo `m`, (B) the least quadratic non-residue -/

/-- (A): variables `y = 0, k = 1, x = 2`; `y·y = x + k·m`, `y < m`, `x < m`, `x = a`, prefix `π` on `y`. -/
def sqDescA (b ℓ n m a : ℕ) (π : List Bool) : Desc :=
  { nV := 3, pat := [prePat n π], prods := [⟨0, .var 0⟩, ⟨1, .const (toLimbs b ℓ m)⟩],
    chains := [⟨[⟨1, .prod 0⟩], [⟨1, .lin 2⟩, ⟨1, .prod 1⟩]⟩],
    cmps := [⟨0, .const (toLimbs b ℓ m), .lt⟩, ⟨2, .const (toLimbs b ℓ m), .lt⟩,
      ⟨2, .const (toLimbs b ℓ a), .eq⟩] }

/-- (B): the same chain and ranges with modulus `p`, prefix `π` on `x`, no condition `x = a`. -/
def sqDescB (b ℓ n p : ℕ) (π : List Bool) : Desc :=
  { nV := 3, pat := [[], [], prePat n π], prods := [⟨0, .var 0⟩, ⟨1, .const (toLimbs b ℓ p)⟩],
    chains := [⟨[⟨1, .prod 0⟩], [⟨1, .lin 2⟩, ⟨1, .prod 1⟩]⟩],
    cmps := [⟨0, .const (toLimbs b ℓ p), .lt⟩, ⟨2, .const (toLimbs b ℓ p), .lt⟩] }

theorem sqDescA_sat {b ℓ n m a : ℕ} {π : List Bool} (hm : m < 2 ^ (b * ℓ)) (ha : a < 2 ^ (b * ℓ))
    (t : ℕ × ℕ × ℕ) : (sqDescA b ℓ n m a π).Sat b (tri t) ↔
      patMatch (prePat n π) t.1 ∧ (t.1 < m ∧ t.2.2 < m ∧ t.2.2 = a) ∧ t.1 * t.1 = t.2.2 + t.2.1 * m := by
  simp only [Desc.Sat, sqDescA, forall_lt_three, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
    patMatch_nil, and_true, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    CmpRel.Holds, Operand.eval, limbsVal_toLimbs hm, limbsVal_toLimbs ha, tri_0, tri_1, tri_2, sideVal,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Src.eval, ProdD.eval, List.getD_cons_zero,
    List.getD_cons_succ, one_mul, add_zero, IsEmpty.forall_iff, implies_true]

theorem sqDescB_sat {b ℓ n p : ℕ} {π : List Bool} (hp : p < 2 ^ (b * ℓ)) (t : ℕ × ℕ × ℕ) :
    (sqDescB b ℓ n p π).Sat b (tri t) ↔
      patMatch (prePat n π) t.2.2 ∧ (t.1 < p ∧ t.2.2 < p) ∧ t.1 * t.1 = t.2.2 + t.2.1 * p := by
  simp only [Desc.Sat, sqDescB, forall_lt_three, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
    patMatch_nil, true_and, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    CmpRel.Holds, Operand.eval, limbsVal_toLimbs hp, tri_0, tri_1, tri_2, sideVal,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Src.eval, ProdD.eval,
    one_mul, add_zero, IsEmpty.forall_iff, implies_true, and_true]

/-- **(A)**: the count of the (A) description is `S3A` (box `2^n'`; `m ≤ 2^n`, `|π| ≤ n`). -/
theorem sqDescA_count {b ℓ n n' m a : ℕ} {π : List Bool} (hm : m < 2 ^ (b * ℓ)) (ha : a < 2 ^ (b * ℓ))
    (hmn : m ≤ 2 ^ n) (hπ : π.length ≤ n) :
    (sqDescA b ℓ n m a π).countB b (2 ^ n') = S3A n' n m a π := by
  rw [countB_tri rfl, S3A]
  congr 1
  refine filter_congr fun t _ => ?_
  rw [sqDescA_sat hm ha]
  constructor
  · rintro ⟨hp, ⟨h1, h2, h3⟩, h4⟩
    exact ⟨h4, h1, h2, (patMatch_prePat hπ (by omega)).1 hp, h3⟩
  · rintro ⟨h4, h1, h2, hp, h3⟩
    exact ⟨(patMatch_prePat hπ (by omega)).2 hp, ⟨h1, h2, h3⟩, h4⟩

/-- **(B)**: the count of the (B) description is `S3B` (box `2^n'`; `p ≤ 2^n`, `|π| ≤ n`). -/
theorem sqDescB_count {b ℓ n n' p : ℕ} {π : List Bool} (hp : p < 2 ^ (b * ℓ))
    (hpn : p ≤ 2 ^ n) (hπ : π.length ≤ n) :
    (sqDescB b ℓ n p π).countB b (2 ^ n') = S3B n' n p π := by
  rw [countB_tri rfl, S3B]
  congr 1
  refine filter_congr fun t _ => ?_
  rw [sqDescB_sat hp]
  constructor
  · rintro ⟨hx, ⟨h1, h2⟩, h4⟩
    exact ⟨h4, h1, h2, (patMatch_prePat hπ (by omega)).1 hx⟩
  · rintro ⟨h4, h1, h2, hx⟩
    exact ⟨(patMatch_prePat hπ (by omega)).2 hx, ⟨h1, h2⟩, h4⟩

theorem sqDescA_WF {b ℓ n nB m a : ℕ} {π : List Bool} (hn : n ≤ nB) : (sqDescA b ℓ n m a π).WFB b ℓ nB where
  pat_len := by simp [sqDescA, length_prePat, hn]
  prod_ok := by simp [sqDescA, Operand.OK, length_toLimbs]; exact toLimbs_lt b ℓ m
  term_ok := by
    simp only [sqDescA, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Src.OK]
    exact ⟨by simp, by simp, by simp⟩
  coeff_le := by simp [sqDescA]
  prod_once := by simp [sqDescA]
  cmp_ok := by simp [sqDescA, Operand.OK, length_toLimbs]; exact ⟨toLimbs_lt b ℓ m, toLimbs_lt b ℓ a⟩

theorem sqDescB_WF {b ℓ n nB p : ℕ} {π : List Bool} (hn : n ≤ nB) : (sqDescB b ℓ n p π).WFB b ℓ nB where
  pat_len := by simp [sqDescB, length_prePat, hn]
  prod_ok := by simp [sqDescB, Operand.OK, length_toLimbs]; exact toLimbs_lt b ℓ p
  term_ok := by
    simp only [sqDescB, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Src.OK]
    exact ⟨by simp, by simp, by simp⟩
  coeff_le := by simp [sqDescB]
  prod_once := by simp [sqDescB]
  cmp_ok := by simp [sqDescB, Operand.OK, length_toLimbs]; exact toLimbs_lt b ℓ p

end EthFollowup.ModP
