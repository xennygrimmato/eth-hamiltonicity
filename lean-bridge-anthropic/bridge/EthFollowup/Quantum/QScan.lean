/-
# Theorem Q1, bridge part 6: the scan in polynomial time

The scan of `Circuit.lean` reads the number of blocks from the state; to fold it with a length bound
that is additive in the step (`PolyT.foldl_add`), every gate code is annotated with the number of
two-qubit gates before it (`annotK`), and the step `scanStepA` takes the block number from the
annotation. `scanA_eq`: on valid codes this is the scan. `scanA_polyT`.
-/
import EthFollowup.Quantum.QPoly

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Groundwork Groundwork.Prog

/-- The scan step with the block number given. -/
def scanStepA (st : SS) (e : GC × ℕ) : SS :=
  if e.1.1 < 7 then (st.1, (st.2.1.set e.1.2.1 (st.2.1.getD e.1.2.1 [] ++ [e.1.1]), st.2.2))
  else if e.1.2.1 = e.1.2.2 then st
  else (st.1 ++ [mkBlk st e.1.1 e.1.2.1 e.1.2.2], ((st.2.1.set e.1.2.1 []).set e.1.2.2 [],
    (st.2.2.set e.1.2.1 (some (e.2, false))).set e.1.2.2 (some (e.2, true))))

/-- The codes, each with `k` plus the number of two-qubit gates before it. -/
def annotK (k : ℕ) (cs : List GC) : List (GC × ℕ) :=
  (List.range cs.length).map fun j => (cs.getD j (0, 0, 0), k + ((cs.take j).filter fun c => decide (7 ≤ c.1)).length)

/-- The annotated scan. -/
def scanA (n : ℕ) (cs : List GC) : SS := (annotK 0 cs).foldl scanStepA (scanInit n)

theorem annotK_cons (k : ℕ) (c : GC) (cs : List GC) :
    annotK k (c :: cs) = (c, k) :: annotK (k + if 7 ≤ c.1 then 1 else 0) cs := by
  unfold annotK
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, List.getD_cons_succ, List.take_succ_cons]
  rw [List.filter_cons]
  by_cases h : 7 ≤ c.1
  · simp only [h, decide_true, ↓reduceIte, List.length_cons]; congr 1; omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; congr 1

theorem scanStepA_eq {n : ℕ} (st : SS) (c : GC) (hv : ValidC n c) :
    scanStepA st (c, st.1.length) = scanStep st c := by
  unfold scanStepA scanStep
  by_cases hu : c.1 < 7
  · simp [hu]
  · have hq : c.2.1 ≠ c.2.2 := hv.2.2 (by omega)
    simp only [hu, ↓reduceIte, hq]
    rfl

theorem scanStep_length (st : SS) (c : GC) :
    (scanStep st c).1.length = st.1.length + if 7 ≤ c.1 then 1 else 0 := by
  unfold scanStep
  by_cases hu : c.1 < 7
  · simp [hu, show ¬ 7 ≤ c.1 by omega]
  · simp [hu, show 7 ≤ c.1 by omega]

theorem foldl_scanA {n : ℕ} : ∀ (cs : List GC), (∀ c ∈ cs, ValidC n c) → ∀ (st : SS),
    (annotK st.1.length cs).foldl scanStepA st = cs.foldl scanStep st
  | [], _, _ => rfl
  | c :: cs, hv, st => by
    rw [annotK_cons, List.foldl_cons, List.foldl_cons, scanStepA_eq st c (hv c List.mem_cons_self),
      ← scanStep_length]
    exact foldl_scanA cs (fun c' h => hv c' (List.mem_cons_of_mem _ h)) _

/-- **The annotated scan is the scan** on valid codes. -/
theorem scanA_eq {n : ℕ} (cs : List GC) (hv : ∀ c ∈ cs, ValidC n c) : scanA n cs = scan n cs :=
  foldl_scanA cs hv (scanInit n)

/-! ### Lengths -/

theorem len_set_getD {α : Type} [Enc α] : ∀ (l : List α) (i : ℕ) (a d : α),
    len (l.set i a) + len (l.getD i d) ≤ len l + len a + len d
  | [], _, _, _ => by simp
  | b :: l, 0, a, d => by simp [len_cons]; omega
  | b :: l, i + 1, a, d => by
    have := len_set_getD l i a d
    simp only [List.set_cons_succ, List.getD_cons_succ, len_cons] at this ⊢
    omega

theorem len_component (u q₁ q₂ k : ℕ) : len u + len q₁ + len q₂ + len k ≤ len ((u, q₁, q₂), k) := by
  simp only [len_pair]; omega

theorem len_scanStepA (st : SS) (e : GC × ℕ) : len (scanStepA st e) ≤ len st + 3 * len e + 40 := by
  obtain ⟨⟨u, q₁, q₂⟩, k⟩ := e
  have he := len_component u q₁ q₂ k
  have hst : len st = len st.1 + (len st.2.1 + len st.2.2 + 2) + 2 := by
    show len (st.1, (st.2.1, st.2.2)) = _; rw [len_pair, len_pair]
  unfold scanStepA
  simp only
  by_cases hu : u < 7
  · rw [if_pos hu]
    have h1 := len_set_getD st.2.1 q₁ (st.2.1.getD q₁ [] ++ [u]) []
    have h2 := len_append (st.2.1.getD q₁ []) [u]
    have h3 : len [u] = len u + 4 := by rw [len_cons, len_nil]
    have h4 : len ([] : List ℕ) = 2 := len_nil
    simp only [len_pair] at h1 ⊢
    omega
  · rw [if_neg hu]
    by_cases hq : q₁ = q₂
    · rw [if_pos hq]; omega
    · rw [if_neg hq]
      have hb := len_append st.1 [mkBlk st u q₁ q₂]
      have hb1 : len [mkBlk st u q₁ q₂] = len (mkBlk st u q₁ q₂) + 4 := by rw [len_cons, len_nil]
      have hblk : len (mkBlk st u q₁ q₂) = len u + (len q₁ + len q₂ + 2) +
          ((len (st.2.2.getD q₁ none) + len (st.2.2.getD q₂ none) + 2) +
            (len (st.2.1.getD q₁ []) + len (st.2.1.getD q₂ []) + 2) + 2) + 4 := by
        simp only [mkBlk, len_pair]; omega
      have p1 := len_set_getD st.2.1 q₁ [] []
      have p2 := len_set_getD (st.2.1.set q₁ []) q₂ [] []
      have p3 : (st.2.1.set q₁ []).getD q₂ [] = st.2.1.getD q₂ [] := getD_set_ne _ _ _ hq
      have c1 := len_set_getD st.2.2 q₁ (some (k, false)) none
      have c2 := len_set_getD (st.2.2.set q₁ (some (k, false))) q₂ (some (k, true)) none
      have c3 : (st.2.2.set q₁ (some (k, false))).getD q₂ none = st.2.2.getD q₂ none := getD_set_ne _ _ _ hq
      have n1 : len (some (k, false)) = len k + 7 := by rw [len_some, len_pair, len_bool]
      have n2 : len (some (k, true)) = len k + 7 := by rw [len_some, len_pair, len_bool]
      have h0 : len (none : Src) = 2 := len_none
      have h4 : len ([] : List ℕ) = 2 := len_nil
      rw [p3] at p2; rw [c3] at c2
      simp only [len_pair] at ⊢
      omega

/-- The scan as a function of `(n in unary, annotated codes)`. -/
def scanF (p : List Unit × List (GC × ℕ)) : SS := p.2.foldl scanStepA (scanInit p.1.length)

namespace QP

theorem scanInit_polyT : PolyT fun p : List Unit × List (GC × ℕ) => scanInit p.1.length := by
  unfold scanInit
  have h1 := replicate_polyT (γ := List Unit × List (GC × ℕ)) (k := fun p => p.1.length)
    (Unary.of_length (by fun_prop)) ([] : List ℕ)
  have h2 := replicate_polyT (γ := List Unit × List (GC × ℕ)) (k := fun p => p.1.length)
    (Unary.of_length (by fun_prop)) (none : Src)
  fun_prop

theorem mkBlk_polyT {γ : Type} [Enc γ] {st : γ → SS} {u q₁ q₂ : γ → ℕ} (hs : PolyT st) (hu : PolyT u)
    (h1 : PolyT q₁) (h2 : PolyT q₂) : PolyT fun x => mkBlk (st x) (u x) (q₁ x) (q₂ x) := by
  unfold mkBlk; fun_prop

theorem scanStepA_polyT : PolyT fun p : SS × (GC × ℕ) => scanStepA p.1 p.2 := by
  unfold scanStepA
  have hs1 : PolyT fun p : SS × (GC × ℕ) =>
      p.1.2.1.set p.2.1.2.1 (p.1.2.1.getD p.2.1.2.1 [] ++ [p.2.1.1]) :=
    set_polyT [] (by fun_prop) (by fun_prop) (by fun_prop)
  have hp1 : PolyT fun p : SS × (GC × ℕ) => p.1.2.1.set p.2.1.2.1 [] := set_polyT [] (by fun_prop) (by fun_prop) (by fun_prop)
  have hp2 : PolyT fun p : SS × (GC × ℕ) => (p.1.2.1.set p.2.1.2.1 []).set p.2.1.2.2 [] :=
    set_polyT [] hp1 (by fun_prop) (by fun_prop)
  have hc1 : PolyT fun p : SS × (GC × ℕ) => p.1.2.2.set p.2.1.2.1 (some (p.2.2, false)) :=
    set_polyT none (by fun_prop) (by fun_prop) (by fun_prop)
  have hc2 : PolyT fun p : SS × (GC × ℕ) =>
      (p.1.2.2.set p.2.1.2.1 (some (p.2.2, false))).set p.2.1.2.2 (some (p.2.2, true)) :=
    set_polyT none hc1 (by fun_prop) (by fun_prop)
  have hb : PolyT fun p : SS × (GC × ℕ) => mkBlk p.1 p.2.1.1 p.2.1.2.1 p.2.1.2.2 :=
    mkBlk_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  fun_prop

theorem scanF_polyT : PolyT scanF := by
  unfold scanF
  refine PolyT.foldl_add (l := fun p : List Unit × List (GC × ℕ) => p.2) (a := fun p => scanInit p.1.length)
    (g := fun _ st e => scanStepA st e) (by fun_prop) scanInit_polyT
    (PolyT.comp (g := fun q : (List Unit × List (GC × ℕ)) × SS × (GC × ℕ) => (q.2.1, q.2.2)) scanStepA_polyT
      (by fun_prop)) ⟨fun m => 3 * m + 40, (PB.const 3).mul PB.id' |>.add (PB.const 40), fun x c e he => ?_⟩
  have h1 := len_scanStepA c e
  have h2 : len e ≤ len x := (len_le_of_mem he).trans (by rw [len_pair]; omega)
  simp only
  omega

theorem annotK_polyT {γ : Type} [Enc γ] {cs : γ → List GC} (hc : PolyT cs) :
    PolyT fun x => annotK 0 (cs x) := by
  unfold annotK
  have hr : PolyT fun x => List.range (cs x).length := PolyT.range (Unary.of_length hc)
  fun_prop

/-- **The scan in polynomial time.** -/
theorem scanA_polyT {γ : Type} [Enc γ] {n : γ → ℕ} {cs : γ → List GC} (hn : Unary n) (hc : PolyT cs) :
    PolyT fun x => scanA (n x) (cs x) := by
  have h := PolyT.comp (g := fun x => (List.replicate (n x) (), annotK 0 (cs x))) scanF_polyT
    (PolyT.prodMk hn (annotK_polyT hc))
  exact h.congr fun x => by simp [scanF, scanA]

end QP

end EthFollowup.Quantum
