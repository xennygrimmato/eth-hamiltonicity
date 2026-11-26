import MC222.Cube
namespace MC222
set_option maxHeartbeats 0
theorem AT_indep (G : Nat → TT) (h : Nat) (w : BitVec 16) (hw : comb w (witGens G 0 h 0) = 0) :
    w &&& 8191#16 = 0 := by
  simp only [comb, witGens, X, C, sel, Nat.not_lt_zero, ↓reduceIte] at hw
  bv_decide

theorem first_helper (G : Nat → TT) (h : Nat) (α β w : BitVec 16) (h1 : α &&& 255#16 ≠ 0)
    (h2 : β &&& 255#16 ≠ 0) (h3 : α &&& 255#16 ≠ β &&& 255#16) :
    comb α (gateGens G 0) &&& comb β (gateGens G 0) ≠ comb w (witGens G 0 h 0) := by
  simp only [comb, witGens, gateGens, X, C, sel, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero]
  bv_decide (config := { timeout := 3600 })
end MC222
