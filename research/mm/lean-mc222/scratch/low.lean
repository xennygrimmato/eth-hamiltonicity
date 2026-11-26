import MC222.Comb
namespace MC222
theorem low_of {n : Nat} (hn : 8 ≤ n ∧ n ≤ 13) {c : BitVec 16}
    (h : ∀ i, n ≤ i → c.getLsbD i = false) : Low n c := by
  unfold Low; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases hin : n ≤ i
  · simp [h i hin]
  · have : ((1#16 <<< n) - 1).getLsbD i = true := by
      obtain rfl | rfl | rfl | rfl | rfl | rfl : n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 := by omega
      all_goals (interval_cases i <;> first | omega | decide)
    simp only [this, Bool.not_true, Bool.and_false]
    exact (by simp : BitVec.getLsbD (0 : BitVec 16) i = false).symm

theorem ech_exists (l r : BitVec 16) (h1 : l ≠ 0) (h2 : r ≠ 0) (h3 : l ≠ r) :
    Ech l r ∨ Ech r l ∨ Ech l (l ^^^ r) ∨ Ech (l ^^^ r) l ∨ Ech r (l ^^^ r) ∨ Ech (l ^^^ r) r := by
  unfold Ech; bv_decide
end MC222
