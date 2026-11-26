import MC222.TT

/-!
# XOR-combinations with 16-bit coefficient vectors, on both sides of `tt`
-/

namespace MC222

/-- `∑_{j < 16} c_j v_j` in `Fn`. -/
def combF (c : BitVec 16) (v : Nat → Fn) : Fn :=
  ∑ j ∈ Finset.range 16, if c.getLsbD j then v j else 0

theorem extract_one (c : BitVec 16) (j : Nat) :
    BitVec.extractLsb' j 1 c = if c.getLsbD j then 1#1 else 0#1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : i = 0 := by omega
  subst this
  cases h : c.getLsbD j <;> simp [h]

theorem sel_eq (c : BitVec 16) (j : Nat) (t : TT) : sel c j t = if c.getLsbD j then t else 0 := by
  unfold sel; rw [extract_one]
  cases c.getLsbD j
  · simp only [Bool.false_eq_true, ite_false]; rw [show BitVec.signExtend 256 0#1 = 0#256 by decide]; simp
  · simp only [ite_true]; rw [show BitVec.signExtend 256 1#1 = BitVec.allOnes 256 by decide]
    exact BitVec.and_allOnes

theorem tt_ite (q : Bool) (f : Fn) : tt (if q then f else 0) = if q then tt f else 0 := by
  cases q <;> simp [tt_zero]

theorem tt_combF (c : BitVec 16) (v : Nat → Fn) : tt (combF c v) = comb c (fun j => tt (v j)) := by
  simp only [combF, comb, Finset.sum_range_succ, Finset.sum_range_zero, tt_add, zero_add, tt_ite,
    sel_eq]

theorem fn_add_self (f : Fn) : f + f = 0 := by
  funext p; simp only [Pi.add_apply, Pi.zero_apply]; generalize f p = u; revert u; decide

theorem combF_xor (l r : BitVec 16) (v : Nat → Fn) : combF (l ^^^ r) v = combF l v + combF r v := by
  simp only [combF, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [BitVec.getLsbD_xor]
  cases l.getLsbD j <;> cases r.getLsbD j <;> simp [fn_add_self]

theorem combF_zero (v : Nat → Fn) : combF 0 v = 0 := by simp [combF]

theorem combF_mem (M : Submodule (ZMod 2) Fn) (c : BitVec 16) (v : Nat → Fn)
    (hv : ∀ j < 16, v j ∈ M) : combF c v ∈ M := by
  refine Submodule.sum_mem _ fun j hj => ?_
  split
  · exact hv j (Finset.mem_range.mp hj)
  · exact M.zero_mem

theorem zmod_smul_eq (e : ZMod 2) (f : Fn) : e • f = if decide (e = 1) then f else 0 := by
  rcases zmod2_cases e with h | h <;> simp [h]

/-- Membership in the span of 16 generators gives a coefficient vector. -/
theorem exists_combF {v : Nat → Fn} {f : Fn}
    (h : f ∈ Submodule.span (ZMod 2) (Set.range (fun j : Fin 16 => v j))) :
    ∃ c : BitVec 16, f = combF c v := by
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp h
  refine ⟨ofPred 16 (fun j => if hj : j < 16 then decide (e ⟨j, hj⟩ = 1) else false), ?_⟩
  rw [← he, combF, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [getLsbD_ofPred, zmod_smul_eq]
  simp [j.isLt]

/-- Clearing coefficients at positions whose generator is zero does not change the sum. -/
theorem combF_cut (n : Nat) (c : BitVec 16) (v : Nat → Fn) (hv : ∀ j, n ≤ j → v j = 0) :
    combF (ofPred 16 (fun j => decide (j < n) && c.getLsbD j)) v = combF c v := by
  simp only [combF]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [getLsbD_ofPred]
  have hj' : j < 16 := Finset.mem_range.mp hj
  by_cases hn : j < n
  · simp [hn, hj']
  · simp [hn, hv j (by omega)]

end MC222
