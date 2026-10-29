/-
# Theorem Q1, bridge part 9: the procedures, one circuit network, the machine

* `qNp`: the procedures of the circuit network (`labelProcs` with the layout of the context, no copy
  bits, the table procedure `qTp`), `qNp_keeps`;
* `qGiven`: for every circuit, `Given.IsGivenNetwork` for the context `prepQ g (circCode C x y)`;
* `qValue`: the value of the network is `P(2^b)` modulo `M_b` (`P = ampPoly C x y`); `value_nonneg`,
  `value_lt`;
* the machine `qM g NM`: read the word, build the context, run Lemma 1 (`networkOnSteps`), decode the
  value (`finQ`); `qM_poly`.
-/
import EthFollowup.Quantum.QRead
import Given.Networks
import Given.End
import Printed.End
import StepMachines.Prog.Range
import ToTuring.Poly.Comb

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset

def layF (c : QCtx) : Lay := c.1
def parF (_ : QCtx × (ℕ × List Bool)) : Bool := false

/-- **The procedures of the circuit network.** -/
def qNp : Procs QCtx := labelProcs layF parF qTp

theorem layF_polyT : PolyT layF := PolyT.fst PolyT.id'
theorem parF_polyT : PolyT parF := PolyT.const false

theorem qNp_keeps : qNp.Keeps := labelProcs_keeps layF_polyT parF_polyT qTp_poly
theorem qNp_P : Unary qNp.P := Lay.P_unary layF_polyT
theorem qNp_B : Unary qNp.B := Lay.B_unary layF_polyT

section Circ

variable (g : ℕ) [NeZero g] {n : ℕ} (C : List (Gate n)) (x y : Basis n)

/-- The scan state of a circuit. -/
abbrev stC : SS := scan n (codes C)
/-- The precision. -/
abbrev bC : ℕ := bK n C.length
/-- The modulus. -/
abbrev MC : ℕ := Mb (bC C)

/-- The label system of a circuit. -/
abbrev XC : LabelSystem g (Fin (cpart (stC C) g).cl.length) Empty Bool :=
  qSys (stC C) g n (MC C) (2 ^ bC C % MC C) (2 ^ (2 * bC C) % MC C) (2 ^ (3 * bC C) % MC C) (List.ofFn x) (List.ofFn y)

/-- The context of a circuit. -/
abbrev cC : QCtx :=
  qCtx (stC C) g n (MC C) (2 ^ bC C % MC C) (2 ^ (2 * bC C) % MC C) (2 ^ (3 * bC C) % MC C) (List.ofFn x) (List.ofFn y)
    (PQ (stC C) g) (BQ (stC C) (bC C))

theorem MC_pos : 0 < MC C := by unfold MC Mb; positivity

instance : NeZero (MC C) := ⟨(MC_pos C).ne'⟩

theorem prep_cC : prepQ g (circCode C x y) = cC g C x y := prepQ_code g C x y

theorem good2C : Good2 (stC C).1.length (stC C) := good2_scan n (codes C) (validC_codes C)

theorem isC : ((XC g C x y).net boolCode).Is (PQ (stC C) g) (BQ (stC C) (bC C)) :=
  qSys_is (stC C) g n _ _ _ _ _ _ (good2C C) rfl

/-- **One circuit network, given by the procedures** (Definition 2(iii)). -/
theorem qGiven : Given.IsGivenNetwork (Given.ofProcs qNp) Given.noTable (cC g C x y) ((XC g C x y).net boolCode)
    (PQ (stC C) g) (BQ (stC C) (bC C)) (τQ (stC C) g)
    (SQ (stC C) g (cC g C x y) (PQ (stC C) g) + size (cC g C x y) + 2 * g + 4 * PQ (stC C) g + 8) :=
  labelProcs_given (XC g C x y) boolCode layF_polyT parF_polyT qTp_poly (isC g C x y)
    (layQ_describes (stC C) g n _ _ _ _ _ _ _ _) (fun j => j.elim)
    (qSys_tspec (stC C) g n _ _ _ _ _ _ (MC_pos C) _ _ fun a => (isC g C x y).len_le a)
    (by unfold τQ; have := Nat.one_le_two_pow (n := 2 * ((stC C).1.length / g + 1)); omega)

/-- **The value of the circuit network** is `P(2^b)` modulo `M_b`. -/
theorem qValue : ((((XC g C x y).net boolCode).value : ℤ) : ZMod (MC C)) =
    evR ((2 : ZMod (MC C)) ^ bC C) (ampPoly C x y) := by
  rw [qSys_value (g := g) (n := n) (M := MC C) (cs := codes C) (hv := validC_codes C) (hz := zp_of (bC C))
    (x := x) (y := y)]
  have := cmat_map (n := n) numI (evR ((2 : ZMod (MC C)) ^ bC C)) (codes C)
  simp only [IM] at this ⊢
  rw [this]; rfl

theorem value_eq : ((XC g C x y).net boolCode).value =
    ((∑ ℓ : Fin (cpart (stC C) g).cl.length → Bool, ∏ a : Fin g,
      streamN (MC C) (ilN (stC C) g a.val).length
        (descN (stC C) g n (MC C) (2 ^ bC C % MC C) (2 ^ (2 * bC C) % MC C) (2 ^ (3 * bC C) % MC C)
          (List.ofFn x) (List.ofFn y) a.val) (zOf (stC C) g a.val ℓ) : ℕ) : ℤ) := by
  rw [LabelSystem.value_net]; push_cast; rfl

theorem value_nonneg : 0 ≤ ((XC g C x y).net boolCode).value := by rw [value_eq]; positivity

theorem stream_lt_B (a : Fin g) (ℓ : Fin (cpart (stC C) g).cl.length → Bool) :
    streamN (MC C) (ilN (stC C) g a.val).length
      (descN (stC C) g n (MC C) (2 ^ bC C % MC C) (2 ^ (2 * bC C) % MC C) (2 ^ (3 * bC C) % MC C)
        (List.ofFn x) (List.ofFn y) a.val) (zOf (stC C) g a.val ℓ) < 2 ^ BQ (stC C) (bC C) := by
  have h1 := streamN_lt (MC_pos C) (descN (stC C) g n (MC C) (2 ^ bC C % MC C) (2 ^ (2 * bC C) % MC C)
    (2 ^ (3 * bC C) % MC C) (List.ofFn x) (List.ofFn y) a.val) (zOf (stC C) g a.val ℓ)
    (N := (ilN (stC C) g a.val).length)
  have h2 := length_ilN_le' (stC C) g a.val
  have h3 : MC C ≤ 2 ^ (4 * bC C + 1) := by
    unfold MC Mb; rw [pow_succ]; have : 1 ≤ 2 ^ (4 * bC C) := Nat.one_le_two_pow; omega
  have h4 := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num : 0 < 2) h2) h3
  have h5 : 2 ^ (2 * (stC C).1.length) * 2 ^ (4 * bC C + 1) < 2 ^ BQ (stC C) (bC C) := by
    rw [← pow_add]; exact Nat.pow_lt_pow_right (by norm_num) (by unfold BQ; omega)
  omega

theorem value_le : ((XC g C x y).net boolCode).value.natAbs ≤
    2 ^ ((cpart (stC C) g).cl.length + g * BQ (stC C) (bC C)) := by
  rw [value_eq, Int.natAbs_natCast]
  calc _ ≤ ∑ _ℓ : Fin (cpart (stC C) g).cl.length → Bool, (2 ^ BQ (stC C) (bC C)) ^ g := by
        refine Finset.sum_le_sum fun ℓ _ => ?_
        calc _ ≤ ∏ _a : Fin g, 2 ^ BQ (stC C) (bC C) :=
              Finset.prod_le_prod' fun a _ => (stream_lt_B g C x y a ℓ).le
          _ = _ := by simp
    _ = 2 ^ (cpart (stC C) g).cl.length * (2 ^ BQ (stC C) (bC C)) ^ g := by simp
    _ = _ := by rw [← pow_mul, ← pow_add, mul_comm (BQ _ _) g]

end Circ

/-! ### The machine -/

/-- The precision read from the word. -/
def bW (w : List Bool) : ℕ := bK (readQ w).1.length (readQ w).2.2.2.length

/-- The output: the decoded residue and the number of `H`, `CH` gates. -/
def finQ (p : List Bool × ℤ) : List Bool :=
  outWord (fun j => decodeK (bW p.1) (p.2.toNat % Mb (bW p.1)) j.val)
    (((readQ p.1).2.2.2.map fun c => kapC c.1).sum)

/-- Lemma 1 on the circuit network of the word. -/
def mainQ (g : ℕ) (NM : Printed.NetMachine) : Stepped (List Bool) ℤ :=
  Stepped.mapIn (prepQ g) (Printed.networkOnSteps g NM qNp)

/-- **The machine of Theorem Q1** (fixed number `g` of nodes). -/
def qM (g : ℕ) (NM : Printed.NetMachine) : Stepped (List Bool) (List Bool) :=
  Stepped.bind (mainQ g NM) (Stepped.ofFun finQ)

end EthFollowup.Quantum
