import Std.Tactic.BVDecide

/-!
# The cube propositions, at the level of 256-bit truth tables

A Boolean function `F₂⁸ → F₂` is represented by its truth table `TT = BitVec 256`: bit `p`
is the value at the point whose coordinate `k` is bit `k` of `p` (coordinates in the order
a11 a12 a21 a22 b11 b12 b21 b22).  XOR of functions is `^^^`, product is `&&&`.

`CubeOK α β h₁ h₂ …` says that the variables describe a 6-gate circuit in normal form whose
first gate is `ℓ_α ℓ_β`, which computes the four targets, and in which every gate outside
`{h₁, h₂}` lies in `A + T + span{g_h : h ∈ {h₁,h₂}, h < i}`.  The cube theorems (in
`MC222/Cubes/*.lean`) say that no assignment satisfies `CubeOK`; they are proved by
`bv_decide`.  This file only contains definitions; it does not import Mathlib.
-/

namespace MC222

/-- 256-bit truth tables. -/
abbrev TT := BitVec 256

/-- Truth table of the input `x_k` (`k = 0..7`): bit `p` is bit `k` of `p`. -/
def X : Nat → TT
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa#256
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc#256
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0#256
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00#256
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000#256
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000#256
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000#256
  | 7 => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000#256
  | _ => 0#256

/-- Truth tables of the targets `c₁₁, c₁₂, c₂₁, c₂₂` (index `2i+j`, 0-based). -/
def C : Nat → TT
  | 0 => 0x6666cccc6666ccccaaaa0000aaaa00006666cccc6666ccccaaaa0000aaaa0000#256
  | 1 => 0x66666666cccccccc66666666ccccccccaaaaaaaa00000000aaaaaaaa00000000#256
  | 2 => 0x0ff0ff000ff0ff00f0f00000f0f000000ff0ff000ff0ff00f0f00000f0f00000#256
  | 3 => 0x0ff00ff0ff00ff000ff00ff0ff00ff00f0f0f0f000000000f0f0f0f000000000#256
  | _ => 0#256

/-- `v` if bit `j` of `c` is set, else `0`. -/
def sel (c : BitVec 16) (j : Nat) (v : TT) : TT :=
  v &&& BitVec.signExtend 256 (c.extractLsb' j 1)

/-- The XOR-combination `∑_{j < 16} c_j v_j`. -/
def comb (c : BitVec 16) (v : Nat → TT) : TT :=
  sel c 0 (v 0) ^^^ sel c 1 (v 1) ^^^ sel c 2 (v 2) ^^^ sel c 3 (v 3) ^^^
  sel c 4 (v 4) ^^^ sel c 5 (v 5) ^^^ sel c 6 (v 6) ^^^ sel c 7 (v 7) ^^^
  sel c 8 (v 8) ^^^ sel c 9 (v 9) ^^^ sel c 10 (v 10) ^^^ sel c 11 (v 11) ^^^
  sel c 12 (v 12) ^^^ sel c 13 (v 13) ^^^ sel c 14 (v 14) ^^^ sel c 15 (v 15)

/-- The six gate truth tables as a function of the index. -/
def gv (G0 G1 G2 G3 G4 G5 : TT) : Nat → TT
  | 0 => G0 | 1 => G1 | 2 => G2 | 3 => G3 | 4 => G4 | 5 => G5 | _ => 0

/-- Generators available to the factors of gate `i` (constant term dropped):
position `j < 8` is `x_j`, position `8 + j` (`j < i`) is gate `j`. -/
def gateGens (G : Nat → TT) (i j : Nat) : TT :=
  if j < 8 then X j else if j < 8 + i then G (j - 8) else 0

/-- Generators of `S₆`: position 0 is the constant `1`, `1..8` the inputs, `9..14` the gates. -/
def outGens (G : Nat → TT) (j : Nat) : TT :=
  if j = 0 then -1 else if j < 9 then X (j - 1) else if j < 15 then G (j - 9) else 0

/-- Generators of `W_i = A + T + span{g_h : h ∈ {h₁,h₂}, h < i}`. -/
def witGens (G : Nat → TT) (h₁ h₂ i j : Nat) : TT :=
  if j = 0 then -1 else if j < 9 then X (j - 1) else if j < 13 then C (j - 9)
  else if j = 13 then (if h₁ < i then G h₁ else 0)
  else if j = 14 then (if h₂ < i then G h₂ else 0) else 0

/-- `(l, r)` is a reduced echelon pair: both nonzero, the lowest set bit of `l` is below the
lowest set bit of `r`, and each vanishes at the other's lowest set bit. -/
def Ech (l r : BitVec 16) : Prop :=
  l ≠ 0 ∧ r ≠ 0 ∧ r &&& (l &&& -l) = 0 ∧ l &&& (r &&& -r) = 0 ∧ (l &&& -l) < (r &&& -r)

/-- Coefficient vector `c` uses only positions `< n`. -/
def Low (n : Nat) (c : BitVec 16) : Prop := c &&& ~~~((1#16 <<< n) - 1) = 0

/-- Conditions on gate `i ≥ 1`. -/
def GateOK (G : Nat → TT) (i : Nat) (l r : BitVec 16) : Prop :=
  G i = comb l (gateGens G i) &&& comb r (gateGens G i) ∧ Ech l r ∧ Low (8 + i) l ∧ Low (8 + i) r

/-- Helper condition for gate `i`. -/
def WitOK (G : Nat → TT) (h₁ h₂ i : Nat) (w : BitVec 16) : Prop :=
  i = h₁ ∨ i = h₂ ∨ G i = comb w (witGens G h₁ h₂ i)

/-- All conditions of the cube `(α, β, {h₁, h₂})`. -/
def CubeOK (α β : BitVec 16) (h₁ h₂ : Nat) (G0 G1 G2 G3 G4 G5 : TT)
    (l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 : BitVec 16) : Prop :=
  let G := gv G0 G1 G2 G3 G4 G5
  G0 = comb α (gateGens G 0) &&& comb β (gateGens G 0) ∧
  GateOK G 1 l1 r1 ∧ GateOK G 2 l2 r2 ∧ GateOK G 3 l3 r3 ∧ GateOK G 4 l4 r4 ∧ GateOK G 5 l5 r5 ∧
  comb o0 (outGens G) = C 0 ∧ comb o1 (outGens G) = C 1 ∧
  comb o2 (outGens G) = C 2 ∧ comb o3 (outGens G) = C 3 ∧
  WitOK G h₁ h₂ 0 w0 ∧ WitOK G h₁ h₂ 1 w1 ∧ WitOK G h₁ h₂ 2 w2 ∧
  WitOK G h₁ h₂ 3 w3 ∧ WitOK G h₁ h₂ 4 w4 ∧ WitOK G h₁ h₂ 5 w5

/-- The cube proposition: no assignment satisfies `CubeOK`. -/
def Cube (α β : BitVec 16) (h₁ h₂ : Nat) : Prop :=
  ∀ (G0 G1 G2 G3 G4 G5 : TT)
    (l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5 : BitVec 16),
    ¬ CubeOK α β h₁ h₂ G0 G1 G2 G3 G4 G5 l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5

end MC222
