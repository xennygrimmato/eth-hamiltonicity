/-
# The node tables as a step machine (module C1c)

A polynomial-space, `2^{O(μ_a)}`-time step machine (Anthropic's `Stepped` model) for the node table
`σ_a(ℓ) · χ_a(ℓ, y) · I_a(ℓ)` of the blob network (`Blobs.lean`), and the parity bits `P_{cd}`.

## Layer 1: the streamed value (`tableStream`)
The machine reads `d : TD = ((r, a), (V_a, V_a \ {r} sorted), (E_int(a), crossing data at a), copy bits)`
(`TDesc` says what it must hold). `I_a(ℓ)` is streamed: the term number `i < tdN d = 2^p · 8^{p+q}`
(`p = |E_int(a)|`, `q = |δ(a)|`) is a mask `m = i mod 2^p` (a subset `x ⊆ E_int(a)`) and a choice
`j = i / 2^p` of one signed monomial (`Alt`) from each factor `1 + q_e` (`e ∈ x`) and each piece of
`Γ_a(ℓ)` (base-8 digits). The monomial is multiplied out letter by letter (`stepL`), keeping only a
sign and the list of generators met (merge signs from inversion counts), and its coefficient at
`e_{Γ_{V_a}}` is read off (`finalC`). No Grassmann element is ever stored.
* `stepL_sem`, `foldL_sem`, `valC_eq`: the streaming evaluator is correct;
* `sum_choices`: `Σ_{j < 8^N} Π (chosen alternatives) = Π (factors)` (coefficient of a product of sums
  of signed monomials = sum over monomial choices);
* `sum_masks`: masks enumerate the subsets; `prod_intR`: the selected factors multiply to `F_a(x)`;
* `sigma_eqC`, `chi_eqC`, `degL_eqC`, `deg_eqC`: `σ_a`, `χ_a`, the degree test from the data;
* **`tableStream_eq`**: `tableStream d = σ_a(ℓ) χ_a(ℓ, y) I_a(ℓ)` under `TDesc`.

## Layer 2: the machine
* `tableMachine = Stepped.sumRange tdN (Stepped.ofFun termR)` (one term per step);
* `tableMachine_poly : Nonempty (IsPolyT tableMachine)`;
* `tableMachine_runs'`: `Runs d (2 · tdN d) (2 · size d + 3 · size (tdN d) + 3) (tableStream d)`;
* **`tableMachine_runs`**: under `TDesc`, `Runs d (2 · 2^{4|E_int(a)| + 3|δ(a)|})
  (2 · size d + 12|E_int(a)| + 9|δ(a)| + 9) (σ_a χ_a I_a)`;
* `sum_degree_blob`: `Σ_{v ∈ V_a} deg v = 2|E_int(a)| + |δ(a)|`, so `steps_le_mu`:
  `2^{4|E_int(a)| + 3|δ(a)|} ≤ 8^{μ_a}`;
* `tableProc rd = Stepped.mapIn rd tableMachine` (the T-procedure for any polynomial-time reader `rd`),
  `tableProc_poly`, `tableProc_runs`;
* `parBit` (`P_{cd}` from the crossing data at `c`), `parBit_polyT`, `P_eq_parBit`.
-/
import EthFollowup.ExactHC.Blobs
import ToTuring.Poly.Range
import ToTuring.Poly.Basic
import ToTuring.Lib.List3
import ToTuring.Lib.Nat2
import ToTuring.Lib.List2
import ToTuring.Lib.Nat1b
import ToTuring.Lib.List1b

-- This file was developed with Lean's default auto-bound implicits; Anthropic's workspace
-- disables them globally, so they are re-enabled here (binders such as {n g m : ℕ} are implicit).
set_option autoImplicit true

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace EthFollowup.ExactHC

open Finset

/-! ### The streaming evaluator (computational side) -/

/-- A letter `(b, v)`: `ψ_v` if `b`, `ψ̄_v` otherwise. -/
abbrev Letter := Bool × ℕ

/-- The generator index `2v + b` of a letter. -/
def genIdx (x : Letter) : ℕ := 2 * x.2 + x.1.toNat

/-- `(-1)^k`. -/
def sgnN (k : ℕ) : ℤ := if k % 2 = 0 then 1 else -1

/-- One letter: multiply the signed monomial `ε e_T` (or `0 = none`) on the right by the letter;
`rr` is the root (whose letters are `0`). -/
def stepL (rr : ℕ) (s : Option (ℤ × List ℕ)) (x : Letter) : Option (ℤ × List ℕ) :=
  s.elim none fun q =>
    if x.2 = rr ∨ genIdx x ∈ q.2 then none
    else some (if q.2.countP (fun t => decide (genIdx x < t)) % 2 = 0 then q.1 else -q.1,
      genIdx x :: q.2)

/-- The coefficient of `e_A` (`A` given as a list) of a streamed monomial. -/
def finalC (Al : List ℕ) (s : Option (ℤ × List ℕ)) : ℤ :=
  s.elim 0 fun q =>
    if (q.2.all fun γ => decide (γ ∈ Al)) && (Al.all fun γ => decide (γ ∈ q.2)) then q.1 else 0

/-! ### Semantics -/

noncomputable section

variable {n : ℕ}

/-- The value of a letter. -/
def lit (r : Fin n) (x : Letter) : Grass (Fin (2 * n)) :=
  if h : x.2 < n then (if x.1 then psi r ⟨x.2, h⟩ else psibar r ⟨x.2, h⟩) else 0

variable (n) in
/-- The finset of generators listed in `T`. -/
def finOf (T : List ℕ) : Finset (Fin (2 * n)) := univ.filter fun γ => γ.val ∈ T

variable (n) in
/-- The value of a streamed state. -/
def sem (s : Option (ℤ × List ℕ)) : Grass (Fin (2 * n)) := s.elim 0 fun q => q.1 • Grass.e (finOf n q.2)

variable (n) in
/-- The invariant of a streamed state: distinct generators of `Fin (2n)`. -/
def SInv (s : Option (ℤ × List ℕ)) : Prop := ∀ q ∈ s, q.2.Nodup ∧ ∀ γ ∈ q.2, γ < 2 * n

theorem sInv_none : SInv n none := fun _ h => absurd h (by simp)

theorem sInv_some_nil (ε : ℤ) : SInv n (some (ε, [])) := by
  intro q hq
  simp only [Option.mem_def, Option.some.injEq] at hq
  subst hq
  simp

@[simp] theorem mem_finOf {T : List ℕ} {γ : Fin (2 * n)} : γ ∈ finOf n T ↔ γ.val ∈ T := by
  simp [finOf]

theorem finOf_cons {γ : ℕ} (h : γ < 2 * n) (T : List ℕ) :
    finOf n (γ :: T) = insert ⟨γ, h⟩ (finOf n T) := by
  ext δ
  simp only [finOf, mem_filter, mem_univ, true_and, List.mem_cons, mem_insert, Fin.ext_iff]

theorem card_filter_finOf (p : ℕ → Prop) [DecidablePred p] :
    ∀ T : List ℕ, T.Nodup → (∀ γ ∈ T, γ < 2 * n) →
      ((finOf n T).filter fun t => p t.val).card = T.countP fun t => decide (p t)
  | [], _, _ => by simp [finOf]
  | γ :: T, hn, hb => by
    have hγ : γ < 2 * n := hb γ List.mem_cons_self
    have ih := card_filter_finOf p T (List.nodup_cons.1 hn).2 fun t ht => hb t (List.mem_cons_of_mem _ ht)
    have e : finOf n (γ :: T) = insert ⟨γ, hγ⟩ (finOf n T) := finOf_cons hγ T
    have hni : (⟨γ, hγ⟩ : Fin (2 * n)) ∉ finOf n T := by
      simp only [finOf, mem_filter, mem_univ, true_and]; exact (List.nodup_cons.1 hn).1
    rw [e, filter_insert, List.countP_cons]
    by_cases hp : p γ
    · rw [if_pos hp, card_insert_of_notMem (fun h => hni (mem_filter.1 h).1), ih]
      simp [hp]
    · rw [if_neg hp, ih]
      simp [hp]

theorem lit_root (r : Fin n) (b : Bool) : lit r (b, r.val) = 0 := by
  simp [lit, psi, psibar]

theorem lit_eq_gen (r : Fin n) (x : Letter) (hx : x.2 < n) (hr : x.2 ≠ r.val) (h : genIdx x < 2 * n) :
    lit r x = Grass.gen (⟨genIdx x, h⟩ : Fin (2 * n)) := by
  have hne : (⟨x.2, hx⟩ : Fin n) ≠ r := fun h => hr (by rw [← h])
  unfold lit
  rw [dif_pos hx]
  rcases x with ⟨b, v⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, psibar, if_neg hne, gbarIdx, genIdx, Bool.toNat_false,
      add_zero]
  · simp only [↓reduceIte, psi, if_neg hne, gIdx, genIdx, Bool.toNat_true]

/-- **One letter step is correct.** -/
theorem stepL_sem (r : Fin n) {s : Option (ℤ × List ℕ)} (hs : SInv n s) (x : Letter) (hx : x.2 < n) :
    sem n (stepL r.val s x) = sem n s * lit r x ∧ SInv n (stepL r.val s x) := by
  rcases s with _ | ⟨ε, T⟩
  · exact ⟨by simp [stepL, sem], sInv_none⟩
  obtain ⟨hn, hb⟩ := hs (ε, T) rfl
  by_cases hr : x.2 = r.val
  · have : lit r x = 0 := by rcases x with ⟨b, v⟩; simp only at hr; subst hr; exact lit_root r b
    refine ⟨?_, ?_⟩
    · simp [stepL, sem, hr, this]
    · simp only [stepL, Option.elim, hr, true_or, ↓reduceIte]; exact sInv_none
  have hγ : genIdx x < 2 * n := by unfold genIdx; cases x.1 <;> simp <;> omega
  set γf : Fin (2 * n) := ⟨genIdx x, hγ⟩ with hγf
  rw [lit_eq_gen r x hx hr hγ]
  by_cases hm : genIdx x ∈ T
  · have hmf : γf ∈ finOf n T := by simp [finOf, γf, hm]
    refine ⟨?_, ?_⟩
    · simp only [stepL, Option.elim, hr, hm, or_true, ↓reduceIte, sem]
      rw [smul_mul_assoc, Grass.gen, Grass.e_mul_e, if_neg (by
        rw [Finset.disjoint_singleton_right]; exact not_not.2 hmf), smul_zero]
    · simp only [stepL, Option.elim, hr, hm, or_true, ↓reduceIte]; exact sInv_none
  have hmf : γf ∉ finOf n T := by simp [finOf, γf, hm]
  have hinv : invCount (finOf n T) {γf} = T.countP fun t => decide (genIdx x < t) := by
    unfold invCount
    rw [← card_filter_finOf (fun t => genIdx x < t) T hn hb]
    have e : ((finOf n T ×ˢ {γf}).filter fun p => p.2 < p.1) =
        ((finOf n T).filter fun t => genIdx x < t.val) ×ˢ {γf} := by
      ext ⟨p1, p2⟩
      simp only [mem_filter, mem_product, mem_singleton]
      constructor
      · rintro ⟨⟨h1, rfl⟩, h3⟩; exact ⟨⟨h1, h3⟩, rfl⟩
      · rintro ⟨⟨h1, h3⟩, rfl⟩; exact ⟨⟨h1, rfl⟩, h3⟩
    rw [e, card_product, card_singleton, mul_one]
  have hd : Disjoint (finOf n T) {γf} := Finset.disjoint_singleton_right.2 hmf
  refine ⟨?_, ?_⟩
  · simp only [stepL, Option.elim, hr, hm, or_self, ↓reduceIte, sem]
    rw [smul_mul_assoc, Grass.gen, Grass.e_mul_e, if_pos hd, smul_smul, mergeSign, hinv,
      finOf_cons hγ T, Finset.union_singleton]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one (T.countP fun t => decide (genIdx x < t)) with h | h
    · rw [if_pos h, (Nat.even_iff.2 h).neg_one_pow, mul_one]
    · rw [if_neg (by omega), (Nat.odd_iff.2 h).neg_one_pow, mul_neg_one]
  · simp only [stepL, Option.elim, hr, hm, or_self, ↓reduceIte]
    intro q hq
    simp only [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact ⟨List.nodup_cons.2 ⟨hm, hn⟩, fun t ht => by
      rcases List.mem_cons.1 ht with rfl | ht
      · exact hγ
      · exact hb t ht⟩

/-- **A word of letters is streamed correctly.** -/
theorem foldL_sem (r : Fin n) :
    ∀ (w : List Letter), (∀ x ∈ w, x.2 < n) → ∀ s : Option (ℤ × List ℕ), SInv n s →
      sem n (w.foldl (stepL r.val) s) = sem n s * (w.map (lit r)).prod ∧ SInv n (w.foldl (stepL r.val) s)
  | [], _, s, hs => ⟨by simp, hs⟩
  | x :: w, hw, s, hs => by
    obtain ⟨h1, h2⟩ := stepL_sem r hs x (hw x List.mem_cons_self)
    obtain ⟨h3, h4⟩ := foldL_sem r w (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _ h2
    refine ⟨?_, h4⟩
    rw [List.foldl_cons, h3, h1, List.map_cons, List.prod_cons, mul_assoc]

theorem finalC_eq {Al : List ℕ} (hA : ∀ γ ∈ Al, γ < 2 * n) {s : Option (ℤ × List ℕ)} (hs : SInv n s) :
    finalC Al s = (sem n s).coeff (finOf n Al) := by
  rcases s with _ | ⟨ε, T⟩
  · simp [finalC, sem]
  obtain ⟨-, hb⟩ := hs (ε, T) rfl
  simp only [finalC, sem, Option.elim, Grass.coeff_zsmul, Grass.coeff_e]
  have key : (finOf n T = finOf n Al) ↔ ((T.all fun γ => decide (γ ∈ Al)) && (Al.all fun γ => decide (γ ∈ T))) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨fun γ hγ => ?_, fun γ hγ => ?_⟩
      · have : (⟨γ, hb γ hγ⟩ : Fin (2 * n)) ∈ finOf n T := by simp [finOf, hγ]
        rw [h] at this; simpa [finOf] using this
      · have : (⟨γ, hA γ hγ⟩ : Fin (2 * n)) ∈ finOf n Al := by simp [finOf, hγ]
        rw [← h] at this; simpa [finOf] using this
    · rintro ⟨h1, h2⟩
      ext δ
      simp only [finOf, mem_filter, mem_univ, true_and]
      exact ⟨h1 _, h2 _⟩
  by_cases h : finOf n T = finOf n Al
  · rw [if_pos (key.1 h), if_pos h, mul_one]
  · rw [if_neg (fun h' => h (key.2 h')), if_neg h, mul_zero]

/-! ### Alternatives and choices -/

/-- An alternative: a sign bit (negated if `true`) and a word of letters. A factor is a list of
alternatives, standing for their sum. -/
abbrev Alt := Bool × List Letter

/-- `±1` from a sign bit. -/
def sgnB (b : Bool) : ℤ := if b then -1 else 1

/-- The value of an alternative. -/
def altVal (r : Fin n) (a : Alt) : Grass (Fin (2 * n)) := sgnB a.1 • (a.2.map (lit r)).prod

/-- The value of a factor: the sum of its alternatives. -/
def fval (r : Fin n) (f : List Alt) : Grass (Fin (2 * n)) := (f.map (altVal r)).sum

end

/-- Alternative number `d` of a factor; the zero alternative `ψ̄_r` beyond the end. -/
def pick (rr : ℕ) (f : List Alt) (d : ℕ) : Alt := f.getD d (false, [(false, rr)])

/-- Digit-wise map: the element number `k` of `l` is mapped with the digit number `k` of `m` in base
`b`. -/
def digR (b : ℕ) {α β : Type} (H : α → ℕ → β) : List α → ℕ → List β
  | [], _ => []
  | e :: l, m => H e (m % b) :: digR b H l (m / b)

/-- The streamed value of a choice of one alternative per factor. -/
def valC (rr : ℕ) (Al : List ℕ) (cs : List Alt) : ℤ :=
  finalC Al ((cs.flatMap fun c => c.2).foldl (stepL rr) (some (sgnN (cs.countP fun c => c.1), [])))

theorem sgnN_add (a b : ℕ) : sgnN (a + b) = sgnN a * sgnN b := by
  unfold sgnN
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    simp [Nat.add_mod, ha, hb]

theorem sgnN_countP (cs : List Alt) : sgnN (cs.countP fun c => c.1) = (cs.map fun c => sgnB c.1).prod := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.countP_cons, sgnN_add, ih, List.map_cons, List.prod_cons, mul_comm]
    congr 1
    cases c.1 <;> rfl

noncomputable section

variable {n : ℕ}

theorem prod_altVal (r : Fin n) (cs : List Alt) :
    (cs.map (altVal r)).prod = (cs.map fun c => sgnB c.1).prod • ((cs.flatMap fun c => c.2).map (lit r)).prod := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, List.prod_cons, ih, List.flatMap_cons, List.map_append, List.prod_append, altVal,
      List.map_cons, List.prod_cons, smul_mul_smul_comm]

/-- **A choice is streamed correctly.** -/
theorem valC_eq (r : Fin n) {Al : List ℕ} (hA : ∀ γ ∈ Al, γ < 2 * n) (cs : List Alt)
    (hc : ∀ c ∈ cs, ∀ x ∈ c.2, x.2 < n) :
    valC r.val Al cs = ((cs.map (altVal r)).prod).coeff (finOf n Al) := by
  have hw : ∀ x ∈ cs.flatMap (fun c => c.2), x.2 < n := by
    intro x hx
    obtain ⟨c, hc', hx'⟩ := List.mem_flatMap.1 hx
    exact hc c hc' x hx'
  obtain ⟨h1, h2⟩ := foldL_sem r _ hw _ (sInv_some_nil (n := n) (sgnN (cs.countP fun c => c.1)))
  unfold valC
  rw [finalC_eq hA h2, h1, prod_altVal, sgnN_countP]
  simp only [sem, Option.elim]
  rw [show finOf n [] = ∅ by simp [finOf], Grass.e_empty, smul_mul_assoc, one_mul]

theorem altVal_zero (r : Fin n) : altVal r (false, [(false, r.val)]) = 0 := by
  simp [altVal, lit_root]

theorem sum_pick (r : Fin n) : ∀ (f : List Alt) (K : ℕ), f.length ≤ K →
    ∑ d ∈ range K, altVal r (pick r.val f d) = fval r f
  | [], K, _ => by simp [pick, fval, altVal_zero]
  | c :: f, K, hK => by
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by simp at hK; omega⟩
    rw [sum_range_succ', fval, List.map_cons, List.sum_cons, add_comm]
    congr 1
    exact sum_pick r f K (by simp at hK; omega)

theorem sum_range_mul_divmod {M : Type*} [AddCommMonoid M] (a : ℕ) (F : ℕ → ℕ → M) :
    ∀ N : ℕ, ∑ i ∈ range (a * N), F (i % a) (i / a) = ∑ j ∈ range N, ∑ d ∈ range a, F d j
  | 0 => by simp
  | N + 1 => by
    rw [Nat.mul_succ, sum_range_add, sum_range_mul_divmod a F N, sum_range_succ]
    congr 1
    refine sum_congr rfl fun d hd => ?_
    have hd : d < a := mem_range.1 hd
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd,
      Nat.add_mul_div_left _ _ (by omega : 0 < a), Nat.div_eq_of_lt hd, zero_add]

/-- **The sum over all choices is the product of the factors.** -/
theorem sum_choices (r : Fin n) : ∀ fs : List (List Alt), (∀ f ∈ fs, f.length ≤ 8) →
    ∑ j ∈ range (8 ^ fs.length), ((digR 8 (pick r.val) fs j).map (altVal r)).prod = (fs.map (fval r)).prod
  | [], _ => by simp [digR]
  | f :: fs, hf => by
    simp only [digR, List.map_cons, List.prod_cons]
    rw [List.length_cons, pow_succ', sum_range_mul_divmod 8 (fun d j =>
      altVal r (pick r.val f d) * ((digR 8 (pick r.val) fs j).map (altVal r)).prod) (8 ^ fs.length)]
    · simp only [← sum_mul, sum_pick r f 8 (hf f List.mem_cons_self), ← mul_sum,
        sum_choices r fs fun f' hf' => hf f' (List.mem_cons_of_mem _ hf')]

end

/-! ### Subsets of the internal edges as masks -/

/-- The elements of `l` selected by the binary digits of `m`. -/
def selR {α : Type} (l : List α) (m : ℕ) : List α :=
  (digR 2 (fun e d => if d = 1 then [e] else []) l m).flatten

theorem selR_cons {α : Type} (e : α) (l : List α) (m : ℕ) :
    selR (e :: l) m = (if m % 2 = 1 then [e] else []) ++ selR l (m / 2) := rfl

theorem selR_map {α β : Type} (φ : α → β) : ∀ (l : List α) (m : ℕ), selR (l.map φ) m = (selR l m).map φ
  | [], _ => rfl
  | e :: l, m => by
    rw [List.map_cons, selR_cons, selR_cons, selR_map φ l, List.map_append]
    split_ifs <;> rfl

theorem selR_sublist {α : Type} : ∀ (l : List α) (m : ℕ), (selR l m).Sublist l
  | [], _ => List.Sublist.slnil
  | e :: l, m => by
    rw [selR_cons]
    split_ifs
    · exact (selR_sublist l _).cons_cons e
    · exact (selR_sublist l _).cons e

theorem digR_map (b : ℕ) {α β γ : Type} (H : β → ℕ → γ) (φ : α → β) :
    ∀ (l : List α) (m : ℕ), digR b H (l.map φ) m = digR b (fun e d => H (φ e) d) l m
  | [], _ => rfl
  | e :: l, m => by simp only [List.map_cons, digR, digR_map b H φ l]

theorem mem_digR (b : ℕ) {α β : Type} (H : α → ℕ → β) :
    ∀ (l : List α) (m : ℕ) (c : β), c ∈ digR b H l m → ∃ e ∈ l, ∃ d, c = H e d
  | [], _, _, h => absurd h (by simp [digR])
  | e :: l, m, c, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨e, List.mem_cons_self, _, rfl⟩
    · obtain ⟨e', he', d, rfl⟩ := mem_digR b H l _ c h
      exact ⟨e', List.mem_cons_of_mem _ he', d, rfl⟩

theorem length_digR (b : ℕ) {α β : Type} (H : α → ℕ → β) :
    ∀ (l : List α) (m : ℕ), (digR b H l m).length = l.length
  | [], _ => rfl
  | e :: l, m => by simp only [digR, List.length_cons, length_digR b H l]

/-- **Masks enumerate the subsets.** -/
theorem sum_masks {β : Type} {M : Type*} [DecidableEq β] [AddCommMonoid M] :
    ∀ (l : List β), l.Nodup → ∀ H : Finset β → M,
      ∑ m ∈ range (2 ^ l.length), H (selR l m).toFinset = ∑ x ∈ l.toFinset.powerset, H x
  | [], _, H => by simp [selR, digR]
  | e :: l, hn, H => by
    have he : e ∉ l.toFinset := by rw [List.mem_toFinset]; exact (List.nodup_cons.1 hn).1
    simp only [selR_cons]
    rw [List.length_cons, pow_succ', sum_range_mul_divmod 2 (fun d j =>
      H ((if d = 1 then [e] else []) ++ selR l j).toFinset) (2 ^ l.length), List.toFinset_cons,
      sum_powerset_insert he, ← sum_masks l (List.nodup_cons.1 hn).2 H,
      ← sum_masks l (List.nodup_cons.1 hn).2 (fun x => H (insert e x)), ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_range_succ, sum_range_one]
    simp only [zero_ne_one, ↓reduceIte, List.nil_append, List.toFinset_append, List.toFinset_cons,
      List.toFinset_nil, insert_empty, Finset.singleton_union]

theorem card_filter_toFinset {β : Type*} [DecidableEq β] (p : β → Prop) [DecidablePred p] {l : List β}
    (hl : l.Nodup) : (l.toFinset.filter p).card = l.countP fun x => decide (p x) := by
  have e : l.toFinset.filter p = (l.filter fun x => decide (p x)).toFinset := by ext; simp
  rw [e, List.toFinset_card_of_nodup (hl.filter _), List.countP_eq_length_filter]

/-! ### The factors -/

/-- `1 + q_{ij}` as alternatives: `1 + ψ̄_iψ_i − ψ̄_iψ_j − ψ̄_jψ_i + ψ̄_jψ_j`. -/
def qAlts (e : ℕ × ℕ) : List Alt :=
  [(false, []), (false, [(false, e.1), (true, e.1)]), (true, [(false, e.1), (true, e.2)]),
    (true, [(false, e.2), (true, e.1)]), (false, [(false, e.2), (true, e.2)])]

/-- The factor `1`. -/
def oneAlts : List Alt := [(false, [])]

/-- The internal-edge factors for the mask `m`: `1 + q_e` for the selected edges, `1` for the others. -/
def intR (es : List (ℕ × ℕ)) (m : ℕ) : List (List Alt) :=
  digR 2 (fun e d => if d = 1 then qAlts e else oneAlts) es m

/-- `α_ℓ` (code `c` of the label) for the low end `s`. -/
def aAlts (s c : ℕ) : List Alt :=
  if c = 2 then [(false, [(false, s), (true, s)])] else if c = 3 then [(false, [(false, s)])]
  else if c = 4 then [(false, [(true, s)])] else [(false, [])]

/-- `β_ℓ` (code `c` of the label) for the high end `t`. -/
def bAlts (t c : ℕ) : List Alt :=
  if c = 1 then [(false, []), (false, [(false, t), (true, t)])] else if c = 3 then [(true, [(true, t)])]
  else if c = 4 then [(false, [(false, t)])] else [(false, [])]

/-- The data of a crossing edge `k` at the node `a`: `((k, [β s_k = a]), (s_k, t_k), (a_k, b_k), code ℓ_k)`. -/
abbrev CE := (ℕ × Bool) × (ℕ × ℕ) × (ℕ × ℕ) × ℕ

/-- The piece of a crossing edge at the node, as alternatives. -/
def pieceAlts (u : CE) : List Alt := if u.1.2 then aAlts u.2.1.1 u.2.2.2 else bAlts u.2.1.2 u.2.2.2

/-- The code `0, …, 4` of a label. -/
def Label.code : Label → ℕ
  | .N => 0
  | .l0 => 1
  | .l1 => 2
  | .l2 => 3
  | .l3 => 4

/-- The parity of a label code. -/
def parC (c : ℕ) : ℕ := if 3 ≤ c then 1 else 0

theorem parC_code (ℓ : Label) : parC ℓ.code = ℓ.par := by cases ℓ <;> rfl

theorem code_eq_zero (ℓ : Label) : ℓ.code = 0 ↔ ℓ = .N := by cases ℓ <;> simp [Label.code]

noncomputable section

variable {n : ℕ}

theorem lit_val (r : Fin n) (b : Bool) (v : Fin n) : lit r (b, v.val) = if b then psi r v else psibar r v := by
  simp [lit, v.2]

theorem fval_qAlts (r i j : Fin n) : fval r (qAlts (i.val, j.val)) = 1 + qPair r i j := by
  simp only [fval, qAlts, altVal, sgnB, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    List.sum_cons, List.sum_nil, lit_val, Bool.false_eq_true, ↓reduceIte, qPair, one_smul, neg_smul,
    mul_one, add_zero]
  noncomm_ring

theorem fval_oneAlts (r : Fin n) : fval r oneAlts = 1 := by simp [fval, oneAlts, altVal, sgnB]

theorem fval_aAlts (r s : Fin n) (ℓ : Label) : fval r (aAlts s.val ℓ.code) = pieceA r s ℓ := by
  cases ℓ <;> simp [fval, aAlts, Label.code, altVal, sgnB, lit_val, pieceA]

theorem fval_bAlts (r t : Fin n) (ℓ : Label) : fval r (bAlts t.val ℓ.code) = pieceB r t ℓ := by
  cases ℓ <;> simp [fval, bAlts, Label.code, altVal, sgnB, lit_val, pieceB]

/-- The edge `s(p.1, p.2)` of a pair. -/
def symP (p : Fin n × Fin n) : Sym2 (Fin n) := s(p.1, p.2)

/-- The pair of values. -/
def valP (p : Fin n × Fin n) : ℕ × ℕ := (p.1.val, p.2.val)

/-- **The internal factors multiply to `F_a(x)`** for the subset `x` selected by the mask. -/
theorem prod_intR (r : Fin n) : ∀ (esF : List (Fin n × Fin n)), (esF.map symP).Nodup → ∀ m : ℕ,
    ((intR (esF.map valP) m).map (fval r)).prod = edgeProd r (selR (esF.map symP) m).toFinset
  | [], _, m => by simp [intR, digR, selR, edgeProd]
  | p :: esF, hn, m => by
    have hn' := List.nodup_cons.1 (by simpa using hn : (symP p :: esF.map symP).Nodup)
    have ih := prod_intR r esF hn'.2 (m / 2)
    rw [edgeProd_eq] at ih ⊢
    simp only [intR, List.map_cons, digR] at ih ⊢
    rw [List.prod_cons, ih, selR_cons]
    split_ifs with h
    · have hni : symP p ∉ (selR (esF.map symP) (m / 2)).toFinset := fun h' =>
        hn'.1 ((selR_sublist _ _).subset (List.mem_toFinset.1 h'))
      rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty, singleton_union,
        prod_insert hni, Subring.coe_mul]
      congr 1
      simp only [valP, fval_qAlts, oneQ, symP, qEdge_mk]
    · rw [List.nil_append, fval_oneAlts, one_mul]

/-- The letters of `Ω_S` for `S` listed by `vr`. -/
def omL (vr : List ℕ) : List Letter := vr.flatMap fun v => [(false, v), (true, v)]

/-- The generators `Γ_S` for `S` listed by `vr`. -/
def genL (vr : List ℕ) : List ℕ := vr.flatMap fun v => [2 * v, 2 * v + 1]

theorem prod_omL (r : Fin n) : ∀ L : List (Fin n), ((omL (L.map Fin.val)).map (lit r)).prod = OmegaOf r L
  | [] => rfl
  | v :: L => by
    have ih := prod_omL r L
    simp only [omL, OmegaOf, List.map_cons, List.flatMap_cons, List.map_append, List.prod_append,
      List.prod_cons] at ih ⊢
    rw [ih]
    simp [lit_val, omega, mul_assoc]

theorem finOf_genL (r : Fin n) (S : Finset (Fin n)) :
    finOf n (genL ((((S.erase r).sort (· ≤ ·))).map Fin.val)) = genSet r S := by
  ext γ
  simp only [mem_finOf, genL, List.mem_flatMap, List.mem_map, mem_sort,
    mem_erase, List.mem_cons, List.not_mem_nil, or_false, mem_genSet]
  constructor
  · rintro ⟨_, ⟨v, ⟨hv1, hv2⟩, rfl⟩, h⟩
    refine ⟨v, hv2, hv1, ?_⟩
    rcases h with h | h
    · left; exact Fin.ext (by simp [gbarIdx, h])
    · right; exact Fin.ext (by simp [gIdx, h])
  · rintro ⟨v, hv2, hv1, h⟩
    refine ⟨v.val, ⟨v, ⟨hv1, hv2⟩, rfl⟩, ?_⟩
    rcases h with rfl | rfl
    · left; rfl
    · right; rfl

theorem genL_lt (L : List (Fin n)) : ∀ γ ∈ genL (L.map Fin.val), γ < 2 * n := by
  intro γ hγ
  simp only [genL, List.mem_flatMap, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at hγ
  obtain ⟨_, ⟨v, -, rfl⟩, h⟩ := hγ
  have := v.2
  omega

end

/-! ### The signs `σ_a`, `χ_a` and the degree test, computed from the data -/

/-- The common blob of two chords (`Chords.shared`). -/
def sharedC (u w : CE) : ℕ :=
  if u.2.2.1.1 = w.2.2.1.1 ∨ u.2.2.1.1 = w.2.2.1.2 then u.2.2.1.1 else u.2.2.1.2

/-- The chords meet (`Chords.Meet`). -/
def meetC (u w : CE) : Bool :=
  decide (u.2.2.1.1 = w.2.2.1.1 ∨ u.2.2.1.1 = w.2.2.1.2 ∨ u.2.2.1.2 = w.2.2.1.1 ∨ u.2.2.1.2 = w.2.2.1.2)

/-- `c_{kl}` (`Chords.cross_eq`). -/
def crossC (u w : CE) : ℕ :=
  ((if w.2.2.1.1 < u.2.2.1.1 then 1 else 0) + (if w.2.2.1.2 < u.2.2.1.1 then 1 else 0)) +
    ((if w.2.2.1.1 < u.2.2.1.2 then 1 else 0) + (if w.2.2.1.2 < u.2.2.1.2 then 1 else 0))

/-- A term of the exponent of `σ_a`. -/
def sigTerm (a : ℕ) (u w : CE) : ℕ :=
  if u.1.1 < w.1.1 ∧ meetC u w = true ∧ sharedC u w = a then parC u.2.2.2 * parC w.2.2.2 * crossC u w else 0

/-- `σ_a` from the crossing data at `a`. -/
def sigmaC (a : ℕ) (cl : List CE) : ℤ := sgnN (cl.flatMap fun u => cl.map fun w => sigTerm a u w).sum

/-- A term of the exponent of `χ_a`: copy bit `y_{cd}` times `Σ_{c<b<d} P_{ab}`. -/
def chiTerm (a : ℕ) (cl : List CE) (q : (ℕ × ℕ) × Bool) : ℕ :=
  if q.2 then (cl.map fun u =>
    if u.2.2.1.1 = a ∧ q.1.1 < u.2.2.1.2 ∧ u.2.2.1.2 < q.1.2 then parC u.2.2.2 else 0).sum else 0

/-- `χ_a(y)` from the crossing data at `a` and the copy bits. -/
def chiC (a : ℕ) (cl : List CE) (yl : List ((ℕ × ℕ) × Bool)) : ℤ := sgnN (yl.map (chiTerm a cl)).sum

/-- `deg_ℓ(v)`. -/
def degC (cl : List CE) (v : ℕ) : ℕ :=
  cl.countP fun u => decide (u.2.2.2 ≠ 0 ∧ (u.2.1.1 = v ∨ u.2.1.2 = v))

/-- The degree test `Π_{v ∈ V_a} [deg_x(v) + deg_ℓ(v) = 2]` for the edges `xl`. -/
def DC (va : List ℕ) (cl : List CE) (xl : List (ℕ × ℕ)) : ℤ :=
  if va.all (fun v => decide (xl.countP (fun e => decide (e.1 = v ∨ e.2 = v)) + degC cl v = 2)) then 1 else 0

/-! ### The streamed node table -/

/-- The data read by the table procedure:
`((r, a), (V_a, V_a \ {r} sorted), (E_int(a), crossing edges at a sorted), copy bits on Q_a)`. -/
abbrev TD : Type :=
  (ℕ × ℕ) × (List ℕ × List ℕ) × (List (ℕ × ℕ) × List CE) × List ((ℕ × ℕ) × Bool)

/-- The number of terms: `2^{|E_int|} · 8^{|E_int| + |δ(a)|}`. -/
def tdN (d : TD) : ℕ := 2 ^ d.2.2.1.1.length * 8 ^ (d.2.2.1.1.length + d.2.2.1.2.length)

/-- The term for the mask `m` (a subset of `E_int`) and the choice `j` (one alternative per factor). -/
def termMJ (d : TD) (m j : ℕ) : ℤ :=
  sigmaC d.1.2 d.2.2.1.2 * chiC d.1.2 d.2.2.1.2 d.2.2.2 * DC d.2.1.1 d.2.2.1.2 (selR d.2.2.1.1 m) *
    valC d.1.1 (genL d.2.1.2) (digR 8 (pick d.1.1) (intR d.2.2.1.1 m ++ d.2.2.1.2.map pieceAlts) j) *
    finalC (genL d.2.1.2) ((omL d.2.1.2).foldl (stepL d.1.1) (some (1, [])))

/-- **The term number `i`** of the streamed node table. -/
def termR (d : TD) (i : ℕ) : ℤ :=
  termMJ d (i % 2 ^ d.2.2.1.1.length) (i / 2 ^ d.2.2.1.1.length)

/-- **`tableStream`**: the streamed value `Σ_{i < N} term i`. -/
def tableStream (d : TD) : ℤ := ∑ i ∈ range (tdN d), termR d i

noncomputable section

variable {n g m : ℕ}

/-- The data of the crossing edge `k` at the node `a`. -/
def ceOf {G : SimpleGraph (Fin n)} {β : Fin n → Fin g} (X : Crossing G β m) (ℓ : Fin m → Label) (a : Fin g)
    (k : Fin m) : CE :=
  ((k.val, decide (β (X.s k) = a)), ((X.s k).val, (X.t k).val), ((β (X.s k)).val, (β (X.t k)).val), (ℓ k).code)

/-- **What the data must hold** for the node `a`, the labels `ℓ` and the copy bits `y`. -/
structure TDesc (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {β : Fin n → Fin g} (X : Crossing G β m)
    (r : Fin n) (a : Fin g) (ℓ : Fin m → Label) (y : Fin g × Fin g → ZMod 2) (d : TD) : Prop where
  r_eq : d.1.1 = r.val
  a_eq : d.1.2 = a.val
  va : ∃ L : List (Fin n), (∀ v, v ∈ L ↔ β v = a) ∧ d.2.1.1 = L.map Fin.val
  vr_eq : d.2.1.2 = (((blob β a).erase r).sort (· ≤ ·)).map Fin.val
  es : ∃ esF : List (Fin n × Fin n), (esF.map symP).Nodup ∧ (∀ e, e ∈ esF.map symP ↔ e ∈ Crossing.Eint G β a) ∧
    d.2.2.1.1 = esF.map valP
  cl_eq : d.2.2.1.2 = ((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a)
  yl : ∃ ql : List (Fin g × Fin g), ql.Nodup ∧ (∀ p, p ∈ ql ↔ p ∈ Chords.Q a) ∧
    d.2.2.2 = ql.map fun p => ((p.1.val, p.2.val), decide (y p = 1))

theorem sum_sort {M : Type*} [AddCommMonoid M] {α : Type*} [LinearOrder α] (s : Finset α) (f : α → M) :
    ∑ k ∈ s, f k = ((s.sort (· ≤ ·)).map f).sum := by
  rw [← List.sum_toFinset f (s.sort_nodup (· ≤ ·)), sort_toFinset]

theorem sgn_cast (N : ℕ) : sgn (N : ZMod 2) = sgnN N := by
  rw [sgn_natCast]
  unfold sgnN
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · rw [if_pos h, (Nat.even_iff.2 h).neg_one_pow]
  · rw [if_neg (by omega), (Nat.odd_iff.2 h).neg_one_pow]

theorem sum_flatMap' {α : Type*} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun u => (f u).sum).sum := by
  induction l with
  | nil => rfl
  | cons u l ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]

section Bridge

variable {G : SimpleGraph (Fin n)} {β : Fin n → Fin g} (X : Crossing G β m)

theorem fval_piece (r : Fin n) (ℓ : Fin m → Label) (a : Fin g) (k : Fin m) :
    fval r (pieceAlts (ceOf X ℓ a k)) = X.piece r ℓ k a := by
  unfold pieceAlts ceOf Crossing.piece
  by_cases h : β (X.s k) = a
  · simp only [h, decide_true, ↓reduceIte, fval_aAlts]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, fval_bAlts]

theorem prod_pieces (r : Fin n) (ℓ : Fin m → Label) (a : Fin g) :
    (((((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a)).map pieceAlts).map (fval r)).prod =
      X.Gam r ℓ a := by
  simp only [List.map_map, Crossing.Gam]
  congr 1
  exact List.map_congr_left fun k _ => fval_piece X r ℓ a k

theorem labelPar_eq (ℓ : Fin m → Label) (k : Fin m) : labelPar ℓ k = ((parC (ℓ k).code : ℕ) : ZMod 2) := by
  rw [parC_code]; rfl

theorem shared_val (ℓ : Fin m → Label) (a : Fin g) (k l : Fin m) :
    (X.chords.shared k l).val = sharedC (ceOf X ℓ a k) (ceOf X ℓ a l) := by
  simp only [Chords.shared, sharedC, ceOf, Crossing.chords_a, Crossing.chords_b, ← Fin.ext_iff]
  by_cases h : β (X.s k) = β (X.s l) ∨ β (X.s k) = β (X.t l) <;> simp [h]

theorem meet_iff (ℓ : Fin m → Label) (a : Fin g) (k l : Fin m) :
    X.chords.Meet k l ↔ meetC (ceOf X ℓ a k) (ceOf X ℓ a l) = true := by
  simp only [Chords.Meet, meetC, ceOf, Crossing.chords_a, Crossing.chords_b, ← Fin.ext_iff, decide_eq_true_eq]

theorem cross_eqC (ℓ : Fin m → Label) (a : Fin g) (k l : Fin m) :
    X.chords.cross k l = crossC (ceOf X ℓ a k) (ceOf X ℓ a l) := by
  rw [Chords.cross_eq]
  simp only [crossC, ceOf, Crossing.chords_a, Crossing.chords_b, Fin.lt_def]
  rfl

/-- **`σ_a` from the data.** -/
theorem sigma_eqC (ℓ : Fin m → Label) (a : Fin g) :
    X.chords.sigma (labelPar ℓ) a = sigmaC a.val (((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a)) := by
  unfold Chords.sigma sigmaC
  set C := X.chords
  have hrestr : (∑ k, ∑ l, if k < l ∧ C.Meet k l ∧ C.shared k l = a then
      labelPar ℓ k * labelPar ℓ l * (C.cross k l : ZMod 2) else 0) =
      ∑ k ∈ C.delta a, ∑ l ∈ C.delta a, if k < l ∧ C.Meet k l ∧ C.shared k l = a then
      labelPar ℓ k * labelPar ℓ l * (C.cross k l : ZMod 2) else 0 := by
    symm
    refine sum_subset (subset_univ _) (fun k _ hk => sum_eq_zero fun l _ => ?_) |>.trans ?_
    · rw [if_neg]
      rintro ⟨-, -, h⟩
      exact hk (h ▸ C.mem_delta_shared_left k l)
    · refine sum_congr rfl fun k _ => sum_subset (subset_univ _) fun l _ hl => ?_
      rw [if_neg]
      rintro ⟨-, hm, h⟩
      exact hl (h ▸ C.mem_delta_shared_right hm)
  rw [hrestr]
  have hterm : ∀ k l, (if k < l ∧ C.Meet k l ∧ C.shared k l = a then
      labelPar ℓ k * labelPar ℓ l * (C.cross k l : ZMod 2) else 0) =
      ((sigTerm a.val (ceOf X ℓ a k) (ceOf X ℓ a l) : ℕ) : ZMod 2) := by
    intro k l
    have hc : (k < l ∧ C.Meet k l ∧ C.shared k l = a) ↔
        ((ceOf X ℓ a k).1.1 < (ceOf X ℓ a l).1.1 ∧ meetC (ceOf X ℓ a k) (ceOf X ℓ a l) = true ∧
          sharedC (ceOf X ℓ a k) (ceOf X ℓ a l) = a.val) := by
      rw [← meet_iff X ℓ a k l, ← shared_val X ℓ a k l, Fin.lt_def, Fin.ext_iff]
      rfl
    unfold sigTerm
    by_cases h : k < l ∧ C.Meet k l ∧ C.shared k l = a
    · rw [if_pos h, if_pos (hc.1 h), labelPar_eq, labelPar_eq, cross_eqC X ℓ a k l]
      push_cast; rfl
    · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]; simp
  simp only [hterm]
  rw [show (∑ k ∈ C.delta a, ∑ l ∈ C.delta a, ((sigTerm a.val (ceOf X ℓ a k) (ceOf X ℓ a l) : ℕ) : ZMod 2)) =
      ((∑ k ∈ C.delta a, ∑ l ∈ C.delta a, sigTerm a.val (ceOf X ℓ a k) (ceOf X ℓ a l) : ℕ) : ZMod 2) by
    push_cast; rfl]
  rw [sgn_cast, sum_flatMap', sum_sort, List.map_map]
  congr 2
  refine List.map_congr_left fun k _ => ?_
  rw [sum_sort, Function.comp_apply, List.map_map]
  rfl

theorem sum_P_eq (ℓ : Fin m → Label) (a : Fin g) (c d : Fin g) :
    (∑ b ∈ univ.filter (fun b => c < b ∧ b < d), X.chords.P (labelPar ℓ) a b) =
      ((((((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a)).map fun u =>
        if u.2.2.1.1 = a.val ∧ c.val < u.2.2.1.2 ∧ u.2.2.1.2 < d.val then parC u.2.2.2 else 0).sum : ℕ) : ZMod 2) := by
  set F := univ.filter (fun b : Fin g => c < b ∧ b < d)
  have h1 : (∑ b ∈ F, X.chords.P (labelPar ℓ) a b) =
      ∑ k, if X.chords.a k = a ∧ X.chords.b k ∈ F then labelPar ℓ k else 0 := by
    unfold Chords.P Chords.E
    simp only [sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    by_cases ha : X.chords.a k = a
    · simp only [ha, true_and]
      rw [sum_ite_eq]
    · simp only [Crossing.chords_a] at ha; simp [ha]
  have h2 : (∑ k, if X.chords.a k = a ∧ X.chords.b k ∈ F then labelPar ℓ k else 0) =
      ∑ k ∈ X.chords.delta a, if X.chords.a k = a ∧ X.chords.b k ∈ F then labelPar ℓ k else 0 := by
    symm
    refine sum_subset (subset_univ _) fun k _ hk => ?_
    rw [if_neg]
    rintro ⟨h, -⟩
    simp only [Crossing.chords_a] at h
    exact hk (X.mem_delta.2 (Or.inl h))
  rw [h1, h2, sum_sort, List.map_map, Nat.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply]
  by_cases h : β (X.s k) = a ∧ c < β (X.t k) ∧ β (X.t k) < d
  · have h' : (ceOf X ℓ a k).2.2.1.1 = a.val ∧ c.val < (ceOf X ℓ a k).2.2.1.2 ∧
        (ceOf X ℓ a k).2.2.1.2 < d.val := ⟨congrArg Fin.val h.1, h.2.1, h.2.2⟩
    have hL : X.chords.a k = a ∧ X.chords.b k ∈ F := ⟨h.1, by simp [F, h.2.1, h.2.2]⟩
    rw [if_pos h', if_pos hL, labelPar_eq]
    rfl
  · have h' : ¬((ceOf X ℓ a k).2.2.1.1 = a.val ∧ c.val < (ceOf X ℓ a k).2.2.1.2 ∧
        (ceOf X ℓ a k).2.2.1.2 < d.val) := fun h' => h ⟨Fin.ext h'.1, h'.2.1, h'.2.2⟩
    have hL : ¬(X.chords.a k = a ∧ X.chords.b k ∈ F) := fun hL => h ⟨hL.1, by simpa [F] using hL.2⟩
    rw [if_neg h', if_neg hL, Nat.cast_zero]

/-- **`χ_a` from the data.** -/
theorem chi_eqC (ℓ : Fin m → Label) (a : Fin g) (y : Fin g × Fin g → ZMod 2) (ql : List (Fin g × Fin g))
    (hn : ql.Nodup) (hq : ∀ p, p ∈ ql ↔ p ∈ Chords.Q a) :
    X.chords.chi (labelPar ℓ) a y = chiC a.val (((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a))
      (ql.map fun p => ((p.1.val, p.2.val), decide (y p = 1))) := by
  unfold Chords.chi chiC
  have hQ : Chords.Q a = ql.toFinset := by ext p; simp [hq]
  rw [hQ, List.sum_toFinset _ hn, ← sgn_cast, List.map_map, Nat.cast_list_sum, List.map_map]
  congr 2
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, sum_P_eq, chiTerm]
  have : y p = 0 ∨ y p = 1 := (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) (y p)
  rcases this with h | h <;> simp [h]

theorem degL_eqC (ℓ : Fin m → Label) (a : Fin g) (v : Fin n) :
    X.degL ℓ a v = degC (((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a)) v.val := by
  unfold Crossing.degL degC
  rw [← sort_toFinset (X.chords.delta a) (· ≤ ·), card_filter_toFinset _ ((X.chords.delta a).sort_nodup _),
    sort_toFinset, List.countP_map]
  congr 1
  funext k
  simp only [Function.comp_apply, ceOf, ne_eq, code_eq_zero, Fin.ext_iff]

theorem deg_eqC (esF : List (Fin n × Fin n)) (hn : (esF.map symP).Nodup) (mm : ℕ) (v : Fin n) :
    Crossing.deg (selR (esF.map symP) mm).toFinset v =
      (selR (esF.map valP) mm).countP (fun e => decide (e.1 = v.val ∨ e.2 = v.val)) := by
  unfold Crossing.deg
  rw [card_filter_toFinset _ ((selR_sublist _ _).nodup hn), selR_map, selR_map, List.countP_map,
    List.countP_map]
  congr 1
  funext p
  simp only [Function.comp_apply, symP, valP, Sym2.mem_iff, ← Fin.ext_iff, eq_comm]

end Bridge

/-! ### Letters are in range -/

/-- All letters of the factor are vertices `< n`. -/
def AltOK (n : ℕ) (f : List Alt) : Prop := ∀ c ∈ f, ∀ x ∈ c.2, x.2 < n

theorem altOK_qAlts {i j : ℕ} (hi : i < n) (hj : j < n) : AltOK n (qAlts (i, j)) := by
  intro c hc x hx
  simp only [qAlts, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl <;> assumption

theorem altOK_oneAlts : AltOK n oneAlts := by
  intro c hc x hx
  simp only [oneAlts, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc; simp at hx

theorem altOK_aAlts {s : ℕ} (hs : s < n) (c : ℕ) : AltOK n (aAlts s c) := by
  intro u hu x hx
  unfold aAlts at hu
  split_ifs at hu <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu <;> subst hu <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    (try rcases hx with rfl | rfl) <;> assumption

theorem altOK_bAlts {t : ℕ} (ht : t < n) (c : ℕ) : AltOK n (bAlts t c) := by
  intro u hu x hx
  unfold bAlts at hu
  split_ifs at hu <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu <;>
    (try rcases hu with rfl | rfl) <;> 
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    (try rcases hx with rfl | rfl) <;> assumption

theorem altOK_pick {f : List Alt} (hf : AltOK n f) {rr : ℕ} (hr : rr < n) (d : ℕ) :
    ∀ x ∈ (pick rr f d).2, x.2 < n := by
  unfold pick
  rw [List.getD_eq_getElem?_getD]
  rcases h : f[d]? with _ | c
  · intro x hx; simp only [Option.getD_none, List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; exact hr
  · exact hf c (List.mem_of_getElem? h)

section Main

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {β : Fin n → Fin g} (X : Crossing G β m)

theorem altOK_pieceAlts (ℓ : Fin m → Label) (a : Fin g) (k : Fin m) : AltOK n (pieceAlts (ceOf X ℓ a k)) := by
  unfold pieceAlts ceOf
  split_ifs
  · exact altOK_aAlts (X.s k).2 _
  · exact altOK_bAlts (X.t k).2 _

/-- **`tableStream` computes the node table** `σ_a(ℓ) · χ_a(ℓ, y) · I_a(ℓ)`. -/
theorem tableStream_eq (r : Fin n) (a : Fin g) (ℓ : Fin m → Label) (y : Fin g × Fin g → ZMod 2) (d : TD)
    (hD : TDesc G X r a ℓ y d) :
    tableStream d = X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a y * X.I r ℓ a := by
  obtain ⟨⟨rr, aa⟩, ⟨va, vr⟩, ⟨es, cl⟩, yl⟩ := d
  obtain ⟨hr, ha, ⟨L, hL, hva⟩, hvr, ⟨esF, hn, hE, hes⟩, hcl, ⟨ql, hqn, hq, hyl⟩⟩ := hD
  simp only at hr ha hva hvr hes hcl hyl
  subst hr ha hva hvr hes hcl hyl
  set S := blob β a
  set cl0 := ((X.chords.delta a).sort (· ≤ ·)).map (ceOf X ℓ a)
  set A := genSet r S
  set Ω := OmegaSet r S
  have hAl : ∀ γ ∈ genL ((((S.erase r).sort (· ≤ ·))).map Fin.val), γ < 2 * n := genL_lt _
  have hfA : finOf n (genL ((((S.erase r).sort (· ≤ ·))).map Fin.val)) = A := finOf_genL r S
  -- the coefficient of `Ω` is streamed
  have hOm : finalC (genL ((((S.erase r).sort (· ≤ ·))).map Fin.val))
      ((omL ((((S.erase r).sort (· ≤ ·))).map Fin.val)).foldl (stepL r.val) (some (1, []))) = Ω.coeff A := by
    have hw : ∀ x ∈ omL ((((S.erase r).sort (· ≤ ·))).map Fin.val), x.2 < n := by
      intro x hx
      simp only [omL, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨_, ⟨v, -, rfl⟩, h⟩ := hx
      rcases h with rfl | rfl <;> exact v.2
    obtain ⟨h1, h2⟩ := foldL_sem r _ hw _ (sInv_some_nil (n := n) 1)
    rw [finalC_eq hAl h2, h1, prod_omL, hfA]
    simp only [sem, Option.elim, one_smul]
    rw [show finOf n [] = ∅ by ext; simp, Grass.e_empty, one_mul]
    rfl
  -- the choices for a fixed mask
  have hlen : ∀ mm, (intR (esF.map valP) mm ++ cl0.map pieceAlts).length = esF.length + cl0.length := by
    intro mm; simp [intR, length_digR]
  have hfs : ∀ mm, ∀ f ∈ intR (esF.map valP) mm ++ cl0.map pieceAlts, AltOK n f ∧ f.length ≤ 8 := by
    intro mm f hf
    rcases List.mem_append.1 hf with hf | hf
    · obtain ⟨e, he, dd, rfl⟩ := mem_digR 2 _ _ _ f hf
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 he
      split_ifs
      · exact ⟨altOK_qAlts p.1.2 p.2.2, by simp [qAlts]⟩
      · exact ⟨altOK_oneAlts, by simp [oneAlts]⟩
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hf
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hu
      refine ⟨altOK_pieceAlts G X ℓ a k, ?_⟩
      unfold pieceAlts aAlts bAlts
      split_ifs <;> simp
  have hchoice : ∀ mm, ∑ j ∈ range (8 ^ (esF.length + cl0.length)),
      valC r.val (genL ((((S.erase r).sort (· ≤ ·))).map Fin.val))
        (digR 8 (pick r.val) (intR (esF.map valP) mm ++ cl0.map pieceAlts) j) =
      (edgeProd r (selR (esF.map symP) mm).toFinset * X.Gam r ℓ a).coeff A := by
    intro mm
    have hv : ∀ j, valC r.val (genL ((((S.erase r).sort (· ≤ ·))).map Fin.val))
        (digR 8 (pick r.val) (intR (esF.map valP) mm ++ cl0.map pieceAlts) j) =
        (((digR 8 (pick r.val) (intR (esF.map valP) mm ++ cl0.map pieceAlts) j).map (altVal r)).prod).coeff A := by
      intro j
      rw [valC_eq r hAl _ ?_, hfA]
      intro c hc
      obtain ⟨f, hf, dd, rfl⟩ := mem_digR 8 _ _ _ c hc
      exact altOK_pick (hfs mm f hf).1 r.2 dd
    simp only [hv, ← Grass.coeff_sum]
    rw [← hlen mm, sum_choices r _ fun f hf => (hfs mm f hf).2, List.map_append, List.prod_append,
      prod_intR r esF hn mm, prod_pieces]
  -- the degree test
  have hdeg : ∀ mm, DC (L.map Fin.val) cl0 (selR (esF.map valP) mm) =
      X.degInd ℓ a (selR (esF.map symP) mm).toFinset := by
    intro mm
    unfold DC Crossing.degInd
    congr 1
    simp only [List.all_eq_true, List.mem_map, decide_eq_true_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, mem_blob]
    refine propext ⟨fun h v hv => ?_, fun h v hv => ?_⟩
    · rw [deg_eqC esF hn, degL_eqC]; exact h v ((hL v).2 hv)
    · rw [← deg_eqC esF hn, ← degL_eqC]; exact h v ((hL v).1 hv)
  -- assemble
  have hEint : (esF.map symP).toFinset = Crossing.Eint G β a := by ext e; simp only [List.mem_toFinset, hE]
  unfold tableStream tdN termR termMJ
  simp only [List.length_map]
  rw [sum_range_mul_divmod (2 ^ esF.length) (fun mm j => sigmaC a.val cl0 * chiC a.val cl0
      (ql.map fun p => ((p.1.val, p.2.val), decide (y p = 1))) * DC (L.map Fin.val) cl0 (selR (esF.map valP) mm) *
      valC r.val (genL ((((S.erase r).sort (· ≤ ·))).map Fin.val))
        (digR 8 (pick r.val) (intR (esF.map valP) mm ++ cl0.map pieceAlts) j) *
      finalC (genL ((((S.erase r).sort (· ≤ ·))).map Fin.val))
        ((omL ((((S.erase r).sort (· ≤ ·))).map Fin.val)).foldl (stepL r.val) (some (1, []))))
      (8 ^ (esF.length + cl0.length)), sum_comm]
  have hs : sigmaC a.val cl0 = X.chords.sigma (labelPar ℓ) a := (sigma_eqC X ℓ a).symm
  have hc : chiC a.val cl0 (ql.map fun p => ((p.1.val, p.2.val), decide (y p = 1))) =
      X.chords.chi (labelPar ℓ) a y := (chi_eqC X ℓ a y ql hqn hq).symm
  simp only [hs, hc, hOm, hdeg]
  simp only [← sum_mul, ← mul_sum, hchoice]
  rw [sum_mul]
  rw [show esF.length = (esF.map symP).length by simp,
    sum_masks (esF.map symP) hn (fun x => X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a y *
      X.degInd ℓ a x * (edgeProd r x * X.Gam r ℓ a).coeff A * Ω.coeff A),
    hEint, Crossing.I, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  simp only [Grass.topCoeff]
  ring

end Main

end

/-! ## Layer 2: the step machine -/

/-- `digR` written with `zip` and `range` (the form computed). -/
def digC (b : ℕ) {α β : Type} (H : α → ℕ → β) (l : List α) (m : ℕ) : List β :=
  (l.zip (List.range l.length)).map fun p => H p.1 (m / b ^ p.2 % b)

theorem digC_eq (b : ℕ) {α β : Type} (H : α → ℕ → β) :
    ∀ (l : List α) (m : ℕ), digC b H l m = digR b H l m
  | [], _ => rfl
  | e :: l, m => by
    rw [digR, ← digC_eq b H l (m / b)]
    simp only [digC, List.length_cons, List.range_succ_eq_map, List.zip_cons_cons, List.map_cons,
      pow_zero, Nat.div_one, List.zip_map_right, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, Prod.map, id, pow_succ', Nat.div_div_eq_div_mul]

section Poly

open Groundwork

variable {γ : Type} [Enc γ]

theorem digC_polyT {α β : Type} [Enc α] [Enc β] (b : ℕ) {H : γ → α → ℕ → β}
    (hH : PolyT fun q : γ × α × ℕ => H q.1 q.2.1 q.2.2) {l : γ → List α} {m : γ → ℕ} (hl : PolyT l)
    (hm : PolyT m) : PolyT fun x => digC b (H x) (l x) (m x) := by
  unfold digC
  have hr : PolyT fun x => List.range (l x).length := PolyT.range (Unary.of_length hl)
  exact PolyT.map (f := fun x (p : α × ℕ) => H x p.1 (m x / b ^ p.2 % b))
    (PolyT.comp (g := fun q : γ × (α × ℕ) => (q.1, q.2.1, m q.1 / b ^ q.2.2 % b)) hH (by fun_prop))
    (by fun_prop)

theorem digR_polyT {α β : Type} [Enc α] [Enc β] (b : ℕ) {H : γ → α → ℕ → β}
    (hH : PolyT fun q : γ × α × ℕ => H q.1 q.2.1 q.2.2) {l : γ → List α} {m : γ → ℕ} (hl : PolyT l)
    (hm : PolyT m) : PolyT fun x => digR b (H x) (l x) (m x) :=
  (digC_polyT b hH hl hm).congr fun x => digC_eq b (H x) (l x) (m x)

theorem stepL_polyT : PolyT (fun p : ℕ × Option (ℤ × List ℕ) × Letter => stepL p.1 p.2.1 p.2.2) := by
  unfold stepL genIdx
  refine PolyT.optionElim (o := fun p : ℕ × Option (ℤ × List ℕ) × Letter => p.2.1) (d := fun _ => none)
    (f := fun p q => if p.2.2.2 = p.1 ∨ 2 * p.2.2.2 + p.2.2.1.toNat ∈ q.2 then none
      else some (if q.2.countP (fun t => decide (2 * p.2.2.2 + p.2.2.1.toNat < t)) % 2 = 0 then q.1 else -q.1,
        (2 * p.2.2.2 + p.2.2.1.toNat) :: q.2)) (by fun_prop) (by fun_prop) ?_
  fun_prop

theorem len_stepL (rr : ℕ) (c : Option (ℤ × List ℕ)) (e : Letter) : len (stepL rr c e) ≤ len c + len e + 2 := by
  rcases c with _ | ⟨ε, T⟩
  · simp only [stepL, Option.elim]; omega
  simp only [stepL, Option.elim]
  split_ifs with h1 h2
  · rw [len_none]; omega
  · rw [len_some, len_some, len_pair, len_pair, len_cons, len_pair]
    have hv : genIdx e < 2 ^ (Nat.size e.2 + 1) := by
      have := Nat.lt_size_self e.2
      unfold genIdx; rw [pow_succ]; cases e.1 <;> simp <;> omega
    have hs := Nat.size_le.2 hv
    have : len (genIdx e) ≤ len e.2 + 3 := by rw [len_nat, len_nat]; omega
    have hb : len e.1 = 1 := rfl
    omega
  · rw [len_some, len_some, len_pair, len_pair, len_cons, len_int, len_int, Int.natAbs_neg]
    have hv : genIdx e < 2 ^ (Nat.size e.2 + 1) := by
      have := Nat.lt_size_self e.2
      unfold genIdx; rw [pow_succ]; cases e.1 <;> simp <;> omega
    have hs := Nat.size_le.2 hv
    have : len (genIdx e) ≤ len e.2 + 3 := by rw [len_nat, len_nat]; omega
    have hb : len e.1 = 1 := rfl
    rw [len_pair]
    omega

theorem foldL_polyT : PolyT (fun p : (ℕ × Option (ℤ × List ℕ)) × List Letter => p.2.foldl (stepL p.1.1) p.1.2) :=
  PolyT.foldl_add (l := fun p : (ℕ × Option (ℤ × List ℕ)) × List Letter => p.2) (a := fun p => p.1.2)
    (g := fun p c e => stepL p.1.1 c e) (by fun_prop) (by fun_prop)
    (PolyT.comp (g := fun q : ((ℕ × Option (ℤ × List ℕ)) × List Letter) × Option (ℤ × List ℕ) × Letter =>
      (q.1.1.1, q.2.1, q.2.2)) stepL_polyT (by fun_prop))
    ⟨fun n => n + 2, PB.id'.add (PB.const 2), fun x c e he => by
      have h1 := len_stepL x.1.1 c e
      have h2 := len_le_of_mem he
      have h3 : len x = len x.1 + len x.2 + 2 := len_pair _ _
      dsimp only
      omega⟩

@[fun_prop] theorem foldL_polyT' {rr : γ → ℕ} {s : γ → Option (ℤ × List ℕ)} {w : γ → List Letter}
    (hr : PolyT rr) (hs : PolyT s) (hw : PolyT w) : PolyT fun x => (w x).foldl (stepL (rr x)) (s x) :=
  PolyT.comp (g := fun x => ((rr x, s x), w x)) foldL_polyT (by fun_prop)

@[fun_prop] theorem finalC_polyT {Al : γ → List ℕ} {s : γ → Option (ℤ × List ℕ)} (hA : PolyT Al)
    (hs : PolyT s) : PolyT fun x => finalC (Al x) (s x) := by
  unfold finalC
  refine PolyT.optionElim (o := s) (d := fun _ => 0)
    (f := fun x q => if (q.2.all fun γ => decide (γ ∈ Al x)) && (Al x).all (fun γ => decide (γ ∈ q.2)) then q.1
      else 0) hs (by fun_prop) ?_
  fun_prop

@[fun_prop] theorem sgnN_polyT {k : γ → ℕ} (hk : PolyT k) : PolyT fun x => sgnN (k x) := by
  unfold sgnN; fun_prop

@[fun_prop] theorem valC_polyT {rr : γ → ℕ} {Al : γ → List ℕ} {cs : γ → List Alt} (hr : PolyT rr)
    (hA : PolyT Al) (hc : PolyT cs) : PolyT fun x => valC (rr x) (Al x) (cs x) := by
  unfold valC; fun_prop

@[fun_prop] theorem pick_polyT {rr : γ → ℕ} {f : γ → List Alt} {dd : γ → ℕ} (hr : PolyT rr) (hf : PolyT f)
    (hd : PolyT dd) : PolyT fun x => pick (rr x) (f x) (dd x) := by
  unfold pick; fun_prop

@[fun_prop] theorem chosen_polyT {rr : γ → ℕ} {fs : γ → List (List Alt)} {j : γ → ℕ} (hr : PolyT rr)
    (hf : PolyT fs) (hj : PolyT j) : PolyT fun x => digR 8 (pick (rr x)) (fs x) (j x) :=
  digR_polyT 8 (H := fun x f d => pick (rr x) f d) (by fun_prop) hf hj

@[fun_prop] theorem qAlts_polyT {e : γ → ℕ × ℕ} (he : PolyT e) : PolyT fun x => qAlts (e x) := by
  unfold qAlts; fun_prop

theorem oneAlts_polyT : PolyT fun _ : γ => oneAlts := PolyT.const _

@[fun_prop] theorem intR_polyT {es : γ → List (ℕ × ℕ)} {mm : γ → ℕ} (he : PolyT es) (hm : PolyT mm) :
    PolyT fun x => intR (es x) (mm x) := by
  unfold intR
  exact digR_polyT 2 (H := fun _ e d => if d = 1 then qAlts e else oneAlts) (by unfold oneAlts; fun_prop) he hm

@[fun_prop] theorem selR_polyT {es : γ → List (ℕ × ℕ)} {mm : γ → ℕ} (he : PolyT es) (hm : PolyT mm) :
    PolyT fun x => selR (es x) (mm x) := by
  unfold selR
  exact PolyT.flatten (digR_polyT 2 (H := fun _ e d => if d = 1 then [e] else []) (by fun_prop) he hm)

@[fun_prop] theorem pieceAlts_polyT {u : γ → CE} (hu : PolyT u) : PolyT fun x => pieceAlts (u x) := by
  unfold pieceAlts aAlts bAlts; fun_prop

@[fun_prop] theorem genL_polyT {vr : γ → List ℕ} (hv : PolyT vr) : PolyT fun x => genL (vr x) := by
  unfold genL; fun_prop

@[fun_prop] theorem omL_polyT {vr : γ → List ℕ} (hv : PolyT vr) : PolyT fun x => omL (vr x) := by
  unfold omL; fun_prop

@[fun_prop] theorem parC_polyT {c : γ → ℕ} (hc : PolyT c) : PolyT fun x => parC (c x) := by
  unfold parC; fun_prop

@[fun_prop] theorem sharedC_polyT {u w : γ → CE} (hu : PolyT u) (hw : PolyT w) :
    PolyT fun x => sharedC (u x) (w x) := by
  unfold sharedC; fun_prop

@[fun_prop] theorem meetC_polyT {u w : γ → CE} (hu : PolyT u) (hw : PolyT w) :
    PolyT fun x => meetC (u x) (w x) := by
  unfold meetC; fun_prop

theorem ind_lt_polyT {f g : γ → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT fun x => if f x < g x then (1 : ℕ) else 0 := by fun_prop

@[fun_prop] theorem crossC_polyT {u w : γ → CE} (hu : PolyT u) (hw : PolyT w) :
    PolyT fun x => crossC (u x) (w x) := by
  have hua : PolyT fun x => (u x).2.2.1.1 := by fun_prop
  have hub : PolyT fun x => (u x).2.2.1.2 := by fun_prop
  have hwa : PolyT fun x => (w x).2.2.1.1 := by fun_prop
  have hwb : PolyT fun x => (w x).2.2.1.2 := by fun_prop
  unfold crossC
  exact PolyT.add (PolyT.add (ind_lt_polyT hwa hua) (ind_lt_polyT hwb hua))
    (PolyT.add (ind_lt_polyT hwa hub) (ind_lt_polyT hwb hub))

@[fun_prop] theorem sigTerm_polyT {a : γ → ℕ} {u w : γ → CE} (ha : PolyT a) (hu : PolyT u) (hw : PolyT w) :
    PolyT fun x => sigTerm (a x) (u x) (w x) := by
  unfold sigTerm
  have h1 : PolyT fun x => decide ((u x).1.1 < (w x).1.1) := by fun_prop
  have h2 : PolyT fun x => decide (meetC (u x) (w x) = true) := by fun_prop
  have h3 : PolyT fun x => decide (sharedC (u x) (w x) = a x) := by fun_prop
  have hc := PolyT.decide_and h1 (PolyT.decide_and h2 h3)
  have hp1 : PolyT fun x => parC (u x).2.2.2 := parC_polyT (by fun_prop)
  have hp2 : PolyT fun x => parC (w x).2.2.2 := parC_polyT (by fun_prop)
  have hv : PolyT fun x => parC (u x).2.2.2 * parC (w x).2.2.2 * crossC (u x) (w x) :=
    PolyT.mul (PolyT.mul hp1 hp2) (crossC_polyT hu hw)
  exact PolyT.ite' hc hv (PolyT.const 0)

@[fun_prop] theorem sigmaC_polyT {a : γ → ℕ} {cl : γ → List CE} (ha : PolyT a) (hc : PolyT cl) :
    PolyT fun x => sigmaC (a x) (cl x) := by
  unfold sigmaC; fun_prop

@[fun_prop] theorem chiTerm_polyT {a : γ → ℕ} {cl : γ → List CE} {q : γ → (ℕ × ℕ) × Bool} (ha : PolyT a)
    (hc : PolyT cl) (hq : PolyT q) : PolyT fun x => chiTerm (a x) (cl x) (q x) := by
  unfold chiTerm; fun_prop

@[fun_prop] theorem chiC_polyT {a : γ → ℕ} {cl : γ → List CE} {yl : γ → List ((ℕ × ℕ) × Bool)} (ha : PolyT a)
    (hc : PolyT cl) (hy : PolyT yl) : PolyT fun x => chiC (a x) (cl x) (yl x) := by
  unfold chiC; fun_prop

@[fun_prop] theorem degC_polyT {cl : γ → List CE} {v : γ → ℕ} (hc : PolyT cl) (hv : PolyT v) :
    PolyT fun x => degC (cl x) (v x) := by
  unfold degC; fun_prop

@[fun_prop] theorem DC_polyT {va : γ → List ℕ} {cl : γ → List CE} {xl : γ → List (ℕ × ℕ)} (hv : PolyT va)
    (hc : PolyT cl) (hx : PolyT xl) : PolyT fun x => DC (va x) (cl x) (xl x) := by
  unfold DC; fun_prop

theorem termR_polyT : PolyT fun p : TD × ℕ => termR p.1 p.2 := by
  have h2 : PolyT fun p : TD × ℕ => 2 ^ p.1.2.2.1.1.length := PolyT.two_pow (Unary.of_length (by fun_prop))
  unfold termR termMJ
  fun_prop

theorem tdN_polyT : PolyT tdN := by
  unfold tdN
  have h1 : PolyT fun d : TD => 2 ^ d.2.2.1.1.length := PolyT.two_pow (Unary.of_length (by fun_prop))
  have h2 : PolyT fun d : TD => 8 ^ (d.2.2.1.1.length + d.2.2.1.2.length) :=
    PolyT.pow_unary (PolyT.const 8) ((Unary.of_length (by fun_prop)).add (Unary.of_length (by fun_prop)))
  fun_prop

end Poly

/-! ### Bounds on the terms -/

/-- The sign of a streamed state is `0` or `±1`. -/
def SOK (s : Option (ℤ × List ℕ)) : Prop := ∀ q ∈ s, q.1.natAbs ≤ 1

theorem stepL_SOK (rr : ℕ) {s : Option (ℤ × List ℕ)} (hs : SOK s) (x : Letter) : SOK (stepL rr s x) := by
  rcases s with _ | ⟨ε, T⟩
  · intro q hq; simp [stepL] at hq
  have h := hs (ε, T) rfl
  intro q hq
  simp only [stepL, Option.elim] at hq
  split_ifs at hq with h1 h2
  · simp at hq
  · simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; exact h
  · simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; simpa using h

theorem foldL_SOK (rr : ℕ) : ∀ (w : List Letter) {s : Option (ℤ × List ℕ)}, SOK s → SOK (w.foldl (stepL rr) s)
  | [], _, hs => hs
  | x :: w, _, hs => foldL_SOK rr w (stepL_SOK rr hs x)

theorem finalC_le (Al : List ℕ) {s : Option (ℤ × List ℕ)} (hs : SOK s) : (finalC Al s).natAbs ≤ 1 := by
  rcases s with _ | ⟨ε, T⟩
  · simp [finalC]
  simp only [finalC, Option.elim]
  split_ifs
  · exact hs (ε, T) rfl
  · simp

theorem sgnN_natAbs (k : ℕ) : (sgnN k).natAbs = 1 := by unfold sgnN; split_ifs <;> rfl

theorem sOK_some (k : ℕ) : SOK (some (sgnN k, [])) := by
  intro q hq; simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; simp [sgnN_natAbs]

theorem valC_le (rr : ℕ) (Al : List ℕ) (cs : List Alt) : (valC rr Al cs).natAbs ≤ 1 :=
  finalC_le Al (foldL_SOK rr _ (sOK_some _))

theorem termR_le (d : TD) (i : ℕ) : (termR d i).natAbs ≤ 1 := by
  unfold termR termMJ
  have h1 := sgnN_natAbs (List.flatMap (fun u => List.map (fun w => sigTerm d.1.2 u w) d.2.2.1.2) d.2.2.1.2).sum
  have h2 := sgnN_natAbs (List.map (chiTerm d.1.2 d.2.2.1.2) d.2.2.2).sum
  have h3 : (DC d.2.1.1 d.2.2.1.2 (selR d.2.2.1.1 (i % 2 ^ d.2.2.1.1.length))).natAbs ≤ 1 := by
    unfold DC; split_ifs <;> simp
  have h4 := valC_le d.1.1 (genL d.2.1.2)
    (digR 8 (pick d.1.1) (intR d.2.2.1.1 (i % 2 ^ d.2.2.1.1.length) ++ d.2.2.1.2.map pieceAlts)
      (i / 2 ^ d.2.2.1.1.length))
  have h5 := finalC_le (genL d.2.1.2) (foldL_SOK d.1.1 (omL d.2.1.2) (s := some (1, [])) (sOK_some 0))
  unfold sigmaC chiC
  simp only [Int.natAbs_mul]
  have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1.le h2.le) h3) h4) h5
  simpa using this

/-! ### The machine -/

section Machine

open Groundwork

/-- **The node-table machine**: one term `termR d i` per step, `i < tdN d`; its states hold the data,
the counter and the running sum, nothing else. -/
def tableMachine : Stepped TD ℤ := Stepped.sumRange tdN (Stepped.ofFun fun p : TD × ℕ => termR p.1 p.2)

/-- The machine has polynomial-time steps. -/
theorem tableMachine_poly : Nonempty (IsPolyT tableMachine) := by
  have : IsPolyT (Stepped.ofFun fun p : TD × ℕ => termR p.1 p.2) := IsPolyT.ofFun termR_polyT
  exact ⟨IsPolyT.sumRange tdN_polyT⟩

/-- **Steps and states of the machine** (for any data): `2 · tdN d` steps, states of size
`2 · size d + 3 · size (tdN d) + 3`, result `tableStream d`. -/
theorem tableMachine_runs' (d : TD) :
    tableMachine.Runs d (2 * tdN d) (2 * size d + 3 * size (tdN d) + 3) (tableStream d) := by
  have hM : ∀ y < tdN d, (Stepped.ofFun fun p : TD × ℕ => termR p.1 p.2).Runs (d, y) 1
      (size d + size (tdN d) + 2) (termR d y) := by
    intro y hy
    refine (Stepped.ofFun_runs (fun p : TD × ℕ => termR p.1 p.2) (d, y)).mono le_rfl ?_
    have h1 : Nat.size y ≤ Nat.size (tdN d) := Nat.size_le_size hy.le
    have h2 : Nat.size (termR d y).natAbs ≤ 1 := Nat.size_le.2 (by have := termR_le d y; omega)
    simp only [size_prod, size_nat, size_int]
    omega
  have h := Stepped.sumRange_runs (N := tdN) (a := d) (fun _ => 1) (fun y => termR d y) 1 _ hM
    (fun y _ => termR_le d y)
  refine h.mono ?_ ?_
  · simp [sum_const, card_range]; omega
  · rw [mul_one]; omega

end Machine

section Spec

open Groundwork

variable {n g m : ℕ}
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {β : Fin n → Fin g} (X : Crossing G β m)

theorem tdN_eq {r : Fin n} {a : Fin g} {ℓ : Fin m → Label} {y : Fin g × Fin g → ZMod 2} {d : TD}
    (hD : TDesc G X r a ℓ y d) :
    tdN d = 2 ^ (4 * (Crossing.Eint G β a).card + 3 * (X.chords.delta a).card) := by
  obtain ⟨esF, hn, hE, hes⟩ := hD.es
  have hp : d.2.2.1.1.length = (Crossing.Eint G β a).card := by
    have : (esF.map symP).toFinset = Crossing.Eint G β a := by ext e; simp only [List.mem_toFinset, hE]
    rw [hes, ← this, List.toFinset_card_of_nodup hn]; simp
  have hq : d.2.2.1.2.length = (X.chords.delta a).card := by rw [hD.cl_eq]; simp
  unfold tdN
  rw [hp, hq, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add]
  congr 1
  ring

/-- **The node-table machine computes `σ_a(ℓ) χ_a(ℓ, y) I_a(ℓ)`** within `2 · 2^{4|E_int(a)| + 3|δ(a)|}`
steps on states of size `2 · size d + 12 |E_int(a)| + 9 |δ(a)| + 9`. Note `2|E_int(a)| + |δ(a)| = μ_a`, so
the number of steps is at most `2 · 8^{μ_a}`. -/
theorem tableMachine_runs (r : Fin n) (a : Fin g) (ℓ : Fin m → Label) (y : Fin g × Fin g → ZMod 2) (d : TD)
    (hD : TDesc G X r a ℓ y d) :
    tableMachine.Runs d (2 * 2 ^ (4 * (Crossing.Eint G β a).card + 3 * (X.chords.delta a).card))
      (2 * size d + 12 * (Crossing.Eint G β a).card + 9 * (X.chords.delta a).card + 9)
      (X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a y * X.I r ℓ a) := by
  have h := tableMachine_runs' d
  rw [tableStream_eq G X r a ℓ y d hD, tdN_eq G X hD] at h
  refine h.mono le_rfl (le_of_eq ?_)
  rw [size_nat, Nat.size_pow]
  ring

/-- The T-procedure: read the data with `rd`, then run the node-table machine. -/
def tableProc {Q : Type} (rd : Q → TD) : Stepped Q ℤ := Stepped.mapIn rd tableMachine

theorem tableProc_poly {Q : Type} [Enc Q] {rd : Q → TD} (hrd : PolyT rd) : Nonempty (IsPolyT (tableProc rd)) := by
  obtain ⟨i⟩ := tableMachine_poly
  exact ⟨IsPolyT.mapIn hrd⟩

theorem tableProc_runs {Q : Type} (rd : Q → TD) (q : Q) (r : Fin n) (a : Fin g) (ℓ : Fin m → Label)
    (y : Fin g × Fin g → ZMod 2) (hD : TDesc G X r a ℓ y (rd q)) :
    (tableProc rd).Runs q (2 * 2 ^ (4 * (Crossing.Eint G β a).card + 3 * (X.chords.delta a).card))
      (2 * size (rd q) + 12 * (Crossing.Eint G β a).card + 9 * (X.chords.delta a).card + 9)
      (X.chords.sigma (labelPar ℓ) a * X.chords.chi (labelPar ℓ) a y * X.I r ℓ a) :=
  Stepped.mapIn_runs (tableMachine_runs G X r a ℓ y (rd q) hD)

end Spec

/-! ### The parity bits `P_{cd}` -/

/-- `P_{cd}` from the crossing data at `c`. -/
def parBit (c d : ℕ) (cl : List CE) : Bool :=
  decide ((cl.map fun u => if u.2.2.1.1 = c ∧ u.2.2.1.2 = d then parC u.2.2.2 else 0).sum % 2 = 1)

theorem parBit_polyT : Groundwork.PolyT fun p : (ℕ × ℕ) × List CE => parBit p.1.1 p.1.2 p.2 := by
  unfold parBit; fun_prop

theorem P_eq_parBit {G : SimpleGraph (Fin n)} {β : Fin n → Fin g} (X : Crossing G β m) (ℓ : Fin m → Label)
    (c d : Fin g) :
    X.chords.P (labelPar ℓ) c d =
      if parBit c.val d.val (((X.chords.delta c).sort (· ≤ ·)).map (ceOf X ℓ c)) then 1 else 0 := by
  have h1 : X.chords.P (labelPar ℓ) c d = ∑ k ∈ X.chords.delta c,
      if X.chords.a k = c ∧ X.chords.b k = d then labelPar ℓ k else 0 := by
    unfold Chords.P Chords.E
    rw [sum_filter]
    symm
    refine sum_subset (subset_univ _) fun k _ hk => ?_
    rw [if_neg]
    rintro ⟨h, -⟩
    simp only [Crossing.chords_a] at h
    exact hk (X.mem_delta.2 (Or.inl h))
  rw [h1, sum_sort]
  have h2 : ((X.chords.delta c).sort (· ≤ ·)).map
      ((fun k => if X.chords.a k = c ∧ X.chords.b k = d then labelPar ℓ k else 0)) =
      ((X.chords.delta c).sort (· ≤ ·)).map (fun k => (((fun u : CE => if u.2.2.1.1 = c.val ∧ u.2.2.1.2 = d.val then
        parC u.2.2.2 else 0) (ceOf X ℓ c k) : ℕ) : ZMod 2)) := by
    refine List.map_congr_left fun k _ => ?_
    by_cases h : β (X.s k) = c ∧ β (X.t k) = d
    · have h' : (ceOf X ℓ c k).2.2.1.1 = c.val ∧ (ceOf X ℓ c k).2.2.1.2 = d.val :=
        ⟨congrArg Fin.val h.1, congrArg Fin.val h.2⟩
      simp only
      rw [if_pos h', if_pos (show X.chords.a k = c ∧ X.chords.b k = d from h), labelPar_eq]
      rfl
    · have h' : ¬((ceOf X ℓ c k).2.2.1.1 = c.val ∧ (ceOf X ℓ c k).2.2.1.2 = d.val) :=
        fun h' => h ⟨Fin.ext h'.1, Fin.ext h'.2⟩
      simp only
      rw [if_neg h', if_neg (show ¬(X.chords.a k = c ∧ X.chords.b k = d) from h), Nat.cast_zero]
  set F : CE → ℕ := fun u => if u.2.2.1.1 = c.val ∧ u.2.2.1.2 = d.val then parC u.2.2.2 else 0
  have h3 : (((X.chords.delta c).sort (· ≤ ·)).map fun k => ((F (ceOf X ℓ c k) : ℕ) : ZMod 2)).sum =
      (((((X.chords.delta c).sort (· ≤ ·)).map (ceOf X ℓ c)).map F).sum : ℕ) := by
    rw [Nat.cast_list_sum, List.map_map, List.map_map]; rfl
  rw [h2, h3, ← ZMod.natCast_mod]
  unfold parBit
  rcases Nat.mod_two_eq_zero_or_one ((((X.chords.delta c).sort (· ≤ ·)).map (ceOf X ℓ c)).map F).sum with h | h
  · rw [h]; simp
  · rw [h]; simp

/-! ### The degree sum `μ_a = 2|E_int(a)| + |δ(a)|` -/

section Mu

variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {β : Fin n → Fin g}

theorem card_blob_mem (a : Fin g) {u w : Fin n} (h : u ≠ w) :
    ((blob β a).filter fun v => v ∈ s(u, w)).card = (if β u = a then 1 else 0) + (if β w = a then 1 else 0) := by
  have e : ((blob β a).filter fun v => v ∈ s(u, w)) =
      ((blob β a).filter fun v => v = u) ∪ ((blob β a).filter fun v => v = w) := by
    ext v; simp only [mem_filter, mem_union, Sym2.mem_iff]; tauto
  rw [e, card_union_of_disjoint (disjoint_filter.2 fun v _ h1 h2 => h (h1.symm.trans h2)), filter_eq',
    filter_eq']
  simp only [mem_blob]
  split_ifs <;> simp

/-- **`Σ_{v ∈ V_a} deg v = 2 |E_int(a)| + |δ(a)|`**: the exponent `4|E_int(a)| + 3|δ(a)|` of the step
bound is at most `3 μ_a`. -/
theorem sum_degree_blob (X : Crossing G β m) (a : Fin g) :
    ∑ v ∈ blob β a, G.degree v = 2 * (Crossing.Eint G β a).card + (X.chords.delta a).card := by
  have h1 : ∀ v, G.degree v = (G.edgeFinset.filter fun e => v ∈ e).card := fun v => by
    rw [← G.card_incidenceFinset_eq_degree, G.incidenceFinset_eq_filter]
  simp only [h1, card_filter]
  rw [sum_comm]
  simp only [← card_filter]
  have key : ∀ e ∈ G.edgeFinset, ((blob β a).filter fun v => v ∈ e).card =
      2 * (if e ∈ Crossing.Eint G β a then 1 else 0) + (if e ∈ (X.chords.delta a).image X.edge then 1 else 0) := by
    intro e he
    rcases X.edge_cases he with ⟨a', ha'⟩ | ⟨k, rfl⟩
    · have hni : e ∉ (X.chords.delta a).image X.edge := by
        intro h
        obtain ⟨k, -, rfl⟩ := mem_image.1 h
        exact X.edge_not_mem_Eint k a' ha'
      rw [if_neg hni, add_zero]
      induction e using Sym2.ind with
      | _ u w =>
        have hu := (Crossing.mem_Eint.1 ha').2 u (Sym2.mem_mk_left u w)
        have hw := (Crossing.mem_Eint.1 ha').2 w (Sym2.mem_mk_right u w)
        have huw : u ≠ w := G.ne_of_adj (by simpa using he)
        rw [card_blob_mem a huw]
        by_cases haa : a' = a
        · subst haa; rw [if_pos ha', if_pos hu, if_pos hw]
        · have : s(u, w) ∉ Crossing.Eint G β a := fun h =>
            haa (hu.symm.trans ((Crossing.mem_Eint.1 h).2 u (Sym2.mem_mk_left u w)))
          rw [if_neg this, if_neg (fun h => haa (hu.symm.trans h)), if_neg (fun h => haa (hw.symm.trans h))]
    · rw [if_neg (X.edge_not_mem_Eint k a), mul_zero, zero_add]
      have hlt := X.lt k
      have hne : X.s k ≠ X.t k := fun h => (lt_irrefl (β (X.s k))) (by rwa [← h] at hlt)
      rw [Crossing.edge, card_blob_mem a hne, ← Crossing.edge]
      have him : X.edge k ∈ (X.chords.delta a).image X.edge ↔ k ∈ X.chords.delta a := by
        rw [mem_image]
        exact ⟨fun ⟨k', hk', e⟩ => X.edge_injective e ▸ hk', fun h => ⟨k, h, rfl⟩⟩
      by_cases hk : k ∈ X.chords.delta a
      · rw [if_pos (him.2 hk)]
        rcases X.mem_delta.1 hk with h | h
        · rw [if_pos h, if_neg (fun h' => by rw [h, h'] at hlt; exact lt_irrefl a hlt)]
        · rw [if_neg (fun h' => by rw [h, h'] at hlt; exact lt_irrefl a hlt), if_pos h]
      · rw [if_neg (fun h => hk (him.1 h))]
        rw [if_neg (fun h => hk (X.mem_delta.2 (Or.inl h))), if_neg (fun h => hk (X.mem_delta.2 (Or.inr h)))]
  rw [sum_congr rfl key, sum_add_distrib, ← mul_sum, ← card_filter, ← card_filter]
  have e1 : G.edgeFinset.filter (fun e => e ∈ Crossing.Eint G β a) = Crossing.Eint G β a := by
    ext e; simp only [mem_filter, and_iff_right_iff_imp]; exact fun h => Crossing.Eint_subset a h
  have e2 : G.edgeFinset.filter (fun e => e ∈ (X.chords.delta a).image X.edge) = (X.chords.delta a).image X.edge := by
    ext e; simp only [mem_filter, and_iff_right_iff_imp]
    intro h; obtain ⟨k, -, rfl⟩ := mem_image.1 h; exact X.edge_mem_edgeFinset k
  rw [e1, e2, card_image_of_injective _ X.edge_injective]

/-- The step bound in terms of `μ_a = Σ_{v ∈ V_a} deg v`: `2^{4|E_int(a)| + 3|δ(a)|} ≤ 8^{μ_a}`. -/
theorem steps_le_mu (X : Crossing G β m) (a : Fin g) :
    2 ^ (4 * (Crossing.Eint G β a).card + 3 * (X.chords.delta a).card) ≤ 8 ^ (∑ v ∈ blob β a, G.degree v) := by
  rw [sum_degree_blob X a, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end Mu

end EthFollowup.ExactHC

