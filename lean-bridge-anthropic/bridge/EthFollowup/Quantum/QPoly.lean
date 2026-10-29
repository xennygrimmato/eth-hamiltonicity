/-
# Theorem Q1, bridge part 5: polynomial-time steps (generic helpers, the table procedure)

* `prod_polyT` (products of lists of naturals), `set_polyT` (`List.set`), `replicate_polyT`;
* `termZ_polyT`, `rdT_polyT`, `qTp_poly : Nonempty (IsPolyT qTp)`.
-/
import EthFollowup.Quantum.QProc
import ToTuring.Poly.Range
import ToTuring.Poly.Basic
import ToTuring.Lib.List3
import ToTuring.Lib.Nat2
import ToTuring.Lib.List2
import ToTuring.Lib.Nat1b
import ToTuring.Lib.List1b

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Groundwork Groundwork.Prog

namespace QP

variable {γ : Type} [Enc γ]

theorem size_mul_le (c e : ℕ) : Nat.size (c * e) ≤ Nat.size c + Nat.size e := by
  refine Nat.size_le.2 ?_
  rw [pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self c) (Nat.lt_size_self e)

theorem len_mul_le' (c e : ℕ) : len (c * e) ≤ len c + len e := by
  rw [len_nat, len_nat, len_nat]; have := size_mul_le c e; omega

theorem prod_polyT0 : PolyT fun l : List ℕ => l.prod := by
  have h : PolyT fun l : List ℕ => l.foldl (fun c e => c * e) 1 :=
    PolyT.foldl_add (l := fun l : List ℕ => l) (a := fun _ => 1) (g := fun _ c e => c * e)
      (by fun_prop) (by fun_prop) (by fun_prop)
      ⟨fun n => n, PB.id', fun x c e he => (len_mul_le' c e).trans (Nat.add_le_add_left (len_le_of_mem he) _)⟩
  exact h.congr fun l => by rw [List.prod_eq_foldl]

@[fun_prop] theorem prod_polyT {l : γ → List ℕ} (hl : PolyT l) : PolyT fun x => (l x).prod :=
  PolyT.comp prod_polyT0 hl

theorem set_eq_map {α : Type} (l : List α) (i : ℕ) (a d : α) :
    l.set i a = (List.range l.length).map fun j => if j = i then a else l.getD j d := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_set, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp [List.getElem?_eq_getElem (by simpa using h1)]

theorem set_polyT {α : Type} [Enc α] {l : γ → List α} {i : γ → ℕ} {a : γ → α} (d : α) (hl : PolyT l)
    (hi : PolyT i) (ha : PolyT a) : PolyT fun x => (l x).set (i x) (a x) := by
  have hr : PolyT fun x => List.range (l x).length := PolyT.range (Unary.of_length hl)
  have h : PolyT fun x => (List.range (l x).length).map fun j => if j = i x then a x else (l x).getD j d := by
    fun_prop
  exact h.congr fun x => (set_eq_map (l x) (i x) (a x) d).symm

theorem replicate_polyT {α : Type} [Enc α] {k : γ → ℕ} (hk : Unary k) (a : α) :
    PolyT fun x => List.replicate (k x) a := by
  have hr : PolyT fun x => List.range (k x) := PolyT.range hk
  have h : PolyT fun x => (List.range (k x)).map fun _ => a := by fun_prop
  exact h.congr fun x => by simp

end QP

/-! ### The terms -/

/-- The bit of a leg for the internal bits of `i`. -/
def legBitI (z : List Bool) (i : ℕ) (r : ℕ × ℕ) : Bool :=
  if r.1 = 0 then z.getD r.2 false else if r.1 = 1 then i.testBit r.2 else decide (r.2 = 1)

theorem legBitI_eq (z : List Bool) (i : ℕ) (r : ℕ × ℕ) : legBitI z i r = legBitB z i.testBit r := rfl

def fidxI (z : List Bool) (i : ℕ) (legs : List (ℕ × ℕ)) : ℕ :=
  legs.foldl (fun acc r => 2 * acc + (legBitI z i r).toNat) 0

theorem fidxI_eq (z : List Bool) (i : ℕ) (legs : List (ℕ × ℕ)) : fidxI z i legs = fidxB z i.testBit legs := rfl

namespace QP

variable {γ : Type} [Enc γ]

@[fun_prop] theorem legBitI_polyT {z : γ → List Bool} {i : γ → ℕ} {r : γ → ℕ × ℕ} (hz : PolyT z) (hi : PolyT i)
    (hr : PolyT r) : PolyT fun x => legBitI (z x) (i x) (r x) := by
  unfold legBitI; fun_prop

theorem len_dbl (a : ℕ) (b : Bool) : len (2 * a + b.toNat) ≤ len a + 3 := by
  rw [len_nat, len_nat]
  have : Nat.size (2 * a + b.toNat) ≤ Nat.size a + 1 := by
    refine Nat.size_le.2 ?_
    have := Nat.lt_size_self a
    rw [pow_succ]; cases b <;> simp <;> omega
  omega

theorem fidxI_polyT : PolyT fun p : (List Bool × ℕ) × List (ℕ × ℕ) => fidxI p.1.1 p.1.2 p.2 := by
  unfold fidxI
  exact PolyT.foldl_add (l := fun p : (List Bool × ℕ) × List (ℕ × ℕ) => p.2) (a := fun _ => 0)
    (g := fun p acc r => 2 * acc + (legBitI p.1.1 p.1.2 r).toNat) (by fun_prop) (by fun_prop) (by fun_prop)
    ⟨fun _ => 3, PB.const 3, fun x c e _ => len_dbl c _⟩

@[fun_prop] theorem fidxI_polyT' {z : γ → List Bool} {i : γ → ℕ} {l : γ → List (ℕ × ℕ)} (hz : PolyT z)
    (hi : PolyT i) (hl : PolyT l) : PolyT fun x => fidxI (z x) (i x) (l x) :=
  PolyT.comp (g := fun x => ((z x, i x), l x)) fidxI_polyT (by fun_prop)

theorem termZ_eq (p : TDat × ℕ) : termZ p =
    (((p.1.1.2.map fun f => f.1.getD (fidxI p.1.2.2 p.2 f.2) 0).prod % p.1.1.1 : ℕ) : ℤ) := rfl

theorem termZ_polyT : PolyT termZ := by
  have h : PolyT fun p : TDat × ℕ =>
      (((p.1.1.2.map fun f => f.1.getD (fidxI p.1.2.2 p.2 f.2) 0).prod % p.1.1.1 : ℕ) : ℤ) := by
    fun_prop
  exact h.congr fun p => (termZ_eq p).symm

theorem rdT_polyT : PolyT rdT := by unfold rdT; fun_prop

end QP

theorem tableQ_poly : Nonempty (IsPolyT tableQ) := by
  have : IsPolyT (Stepped.ofFun termZ) := IsPolyT.ofFun QP.termZ_polyT
  exact ⟨IsPolyT.sumRange (PolyT.two_pow (Unary.of_length (by fun_prop)))⟩

theorem qTp_poly : Nonempty (IsPolyT qTp) := by
  obtain ⟨i⟩ := tableQ_poly
  exact ⟨IsPolyT.mapIn QP.rdT_polyT⟩

end EthFollowup.Quantum
