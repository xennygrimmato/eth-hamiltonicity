import MC222.Cube

namespace MC222

set_option maxHeartbeats 0

/-- Cube: first gate ℓ_18 ℓ_73 (orbit 54), helper gates {0, 1}. -/
theorem cube_54_1 : Cube 18#16 73#16 0 1 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

/-- Cube: first gate ℓ_18 ℓ_73 (orbit 54), helper gates {0, 2}. -/
theorem cube_54_2 : Cube 18#16 73#16 0 2 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

/-- Cube: first gate ℓ_18 ℓ_73 (orbit 54), helper gates {0, 3}. -/
theorem cube_54_3 : Cube 18#16 73#16 0 3 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

/-- Cube: first gate ℓ_18 ℓ_73 (orbit 54), helper gates {0, 4}. -/
theorem cube_54_4 : Cube 18#16 73#16 0 4 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

/-- Cube: first gate ℓ_18 ℓ_73 (orbit 54), helper gates {0, 5}. -/
theorem cube_54_5 : Cube 18#16 73#16 0 5 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

end MC222
