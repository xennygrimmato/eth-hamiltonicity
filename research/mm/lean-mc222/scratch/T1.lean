import Std.Tactic.BVDecide
set_option trace.Meta.Tactic.bv true
example (c : BitVec 3) (x y z : BitVec 256) :
  ((if c.getLsbD 0 then x else 0) ^^^ (if c.getLsbD 1 then y else 0)) &&& z =
  ((if c.getLsbD 0 then x &&& z else 0) ^^^ (if c.getLsbD 1 then y &&& z else 0)) := by
  bv_decide (config := { timeout := 120 })
