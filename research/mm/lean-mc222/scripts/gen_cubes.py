#!/usr/bin/env python3
"""Writes MC222/Cubes/R<r>.lean: for orbit representative r (from plane_orbits.txt, the
72 first-gate planes, one line "a b orbit_size" each) the five cube theorems
Cube a b 0 h for h = 1..5, each proved by bv_decide.  Also writes MC222/Cubes/Reps.lean
(the list of representatives) is NOT done here: the list lives in MC222/Orbits.lean."""
import os, sys
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.dirname(here)
reps = [tuple(map(int, l.split()[:2])) for l in open(os.path.join(here, "plane_orbits.txt"))]
assert len(reps) == 72
os.makedirs(os.path.join(root, "MC222", "Cubes"), exist_ok=True)
for r, (a, b) in enumerate(reps):
    out = ["import MC222.Cube", "", "namespace MC222", "",
           "set_option maxHeartbeats 0", ""]
    for h in range(1, 6):
        out += [f"/-- Cube: first gate ℓ_{a} ℓ_{b} (orbit {r}), helper gates {{0, {h}}}. -/",
                f"theorem cube_{r}_{h} : Cube {a}#16 {b}#16 0 {h} := by",
                "  intro G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 h",
                "  simp only [CubeOK, GateOK, WitOK, comb, gateGens, outGens, witGens, gv, X, C, Ech, Low,",
                "    sel] at h",
                "  bv_decide (config := { timeout := 7200 })", ""]
    out += ["end MC222", ""]
    open(os.path.join(root, "MC222", "Cubes", f"R{r:02d}.lean"), "w").write("\n".join(out))
print("wrote", len(reps), "files")
