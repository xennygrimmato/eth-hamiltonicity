import MC222.Cube
open MC222
set_option maxHeartbeats 0
set_option trace.profiler true
theorem cube_9_01 : Cube 1#16 28#16 0 1 := by
  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h
  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low, sel] at h
  bv_decide (config := { timeout := 3600 })
