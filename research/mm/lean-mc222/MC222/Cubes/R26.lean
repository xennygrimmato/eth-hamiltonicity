import MC222.Cube

namespace MC222

set_option maxHeartbeats 0

/-- Cube: first gate ℓ_6 ℓ_96 (orbit 26), helper gates {0, 1}. -/
theorem cube_26_1 : Cube 6#16 96#16 0 1 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

/-- Cube: first gate ℓ_6 ℓ_96 (orbit 26), helper gates {0, 2}. -/
theorem cube_26_2 : Cube 6#16 96#16 0 2 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

/-- Cube: first gate ℓ_6 ℓ_96 (orbit 26), helper gates {0, 3}. -/
theorem cube_26_3 : Cube 6#16 96#16 0 3 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

/-- Cube: first gate ℓ_6 ℓ_96 (orbit 26), helper gates {0, 4}. -/
theorem cube_26_4 : Cube 6#16 96#16 0 4 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

/-- Cube: first gate ℓ_6 ℓ_96 (orbit 26), helper gates {0, 5}. -/
theorem cube_26_5 : Cube 6#16 96#16 0 5 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

end MC222
