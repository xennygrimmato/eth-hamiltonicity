import MC222.Cube
open MC222
set_option maxHeartbeats 0
-- sanity: three of the four targets with 6 gates, first gate Strassen's m1; should be SAT
example (G0 G1 G2 G3 G4 G5 : TT) (l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 : BitVec 16) :
  let G := gv G0 G1 G2 G3 G4 G5
  ¬ (G0 = comb 9#16 (gateGens G 0) &&& comb 144#16 (gateGens G 0) ∧
  GateOK G 1 l1 r1 ∧ GateOK G 2 l2 r2 ∧ GateOK G 3 l3 r3 ∧ GateOK G 4 l4 r4 ∧ GateOK G 5 l5 r5 ∧
  comb o0 (outGens G) = C 0 ∧ comb o1 (outGens G) = C 1 ∧ comb o2 (outGens G) = C 2) := by
  intro G h
  simp only [G, CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low, sel] at h
  bv_decide (config := { timeout := 600 })
