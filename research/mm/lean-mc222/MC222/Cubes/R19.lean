import MC222.Cube

namespace MC222

set_option maxHeartbeats 0

/-- Cube: first gate ℓ_1 ℓ_104 (orbit 19), helper gates {0, 1}. -/
theorem cube_19_1 : Cube 1#16 104#16 0 1 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

/-- Cube: first gate ℓ_1 ℓ_104 (orbit 19), helper gates {0, 2}. -/
theorem cube_19_2 : Cube 1#16 104#16 0 2 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

/-- Cube: first gate ℓ_1 ℓ_104 (orbit 19), helper gates {0, 3}. -/
theorem cube_19_3 : Cube 1#16 104#16 0 3 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

/-- Cube: first gate ℓ_1 ℓ_104 (orbit 19), helper gates {0, 4}. -/
theorem cube_19_4 : Cube 1#16 104#16 0 4 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

/-- Cube: first gate ℓ_1 ℓ_104 (orbit 19), helper gates {0, 5}. -/
theorem cube_19_5 : Cube 1#16 104#16 0 5 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,
    sel] at h
  bv_decide (config := { timeout := 7200 })

end MC222
