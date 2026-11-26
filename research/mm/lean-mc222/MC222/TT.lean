import MC222.Statement
import MC222.Cube

/-!
# Truth tables: from `Fn` to `BitVec 256`

`tt f` is the truth table of `f`: bit `p` is `f (pt p) = 1`, where `pt p` is the point whose
coordinate `k` is bit `k` of `p`.  `tt` turns `+` into `^^^` and `*` into `&&&`, is injective,
and sends the inputs and targets to the literals `X k`, `C t` of `MC222.Cube`.
-/

namespace MC222

/-- The bit vector whose bit `i` is `f i`. -/
def ofPred : (n : Nat) → (Nat → Bool) → BitVec n
  | 0, _ => 0#0
  | n + 1, f => BitVec.cons (f n) (ofPred n f)

theorem getLsbD_ofPred (n : Nat) (f : Nat → Bool) (i : Nat) :
    (ofPred n f).getLsbD i = (decide (i < n) && f i) := by
  induction n generalizing i with
  | zero => simp [ofPred]
  | succ n ih =>
    simp only [ofPred, BitVec.getLsbD_cons, ih]
    by_cases h : i = n
    · subst h; simp
    · simp only [h, ite_false]
      by_cases h' : i < n
      · simp [h', show i < n + 1 by omega]
      · simp [h', show ¬ i < n + 1 by omega]

/-- The point with index `p`: coordinate `k` is bit `k` of `p`. -/
def pt (p : Nat) : Pt := fun k => if p.testBit k then 1 else 0

/-- The truth table of a function. -/
def tt (f : Fn) : TT := ofPred 256 (fun p => decide (f (pt p) = 1))

theorem getLsbD_tt (f : Fn) (p : Nat) :
    (tt f).getLsbD p = (decide (p < 256) && decide (f (pt p) = 1)) := getLsbD_ofPred _ _ _

/-- Every point has an index. -/
theorem pt_surj (q : Pt) : ∃ p < 256, pt p = q := by
  let q' : Fin 8 → Fin 2 := q
  let e := finFunctionFinEquiv (m := 2) (n := 8)
  refine ⟨(e q' : ℕ), by have := (e q').isLt; simp, ?_⟩
  funext k
  have h1 : (e.symm (e q') k : ℕ) = (e q' : ℕ) / 2 ^ k.val % 2 :=
    finFunctionFinEquiv_symm_apply_val _ _
  have h2 : e.symm (e q') = q' := e.symm_apply_apply q'
  rw [h2] at h1
  have hk : (q' k).val < 2 := (q' k).isLt
  simp only [pt, Nat.testBit_eq_decide_div_mod_eq]
  rcases (show (q' k).val = 0 ∨ (q' k).val = 1 by omega) with h0 | h0
  · have hq : q k = 0 := Fin.ext h0
    rw [hq]; rw [h0] at h1
    have : ¬ ((e q' : ℕ) / 2 ^ k.val % 2 = 1) := by omega
    simp [this]
  · have hq : q k = 1 := Fin.ext h0
    rw [hq]; rw [h0] at h1
    have : ((e q' : ℕ) / 2 ^ k.val % 2 = 1) := by omega
    simp [this]

theorem zmod2_cases (u : ZMod 2) : u = 0 ∨ u = 1 := by revert u; decide

theorem tt_injective {f g : Fn} (h : tt f = tt g) : f = g := by
  funext q
  obtain ⟨p, hp, rfl⟩ := pt_surj q
  have := congrArg (fun v => v.getLsbD p) h
  simp only [getLsbD_tt, hp, decide_true, Bool.true_and, decide_eq_decide] at this
  rcases zmod2_cases (f (pt p)) with h1 | h1 <;> rcases zmod2_cases (g (pt p)) with h2 | h2 <;>
    simp_all

theorem tt_add (f g : Fn) : tt (f + g) = tt f ^^^ tt g := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, getLsbD_tt, Pi.add_apply]
  rcases zmod2_cases (f (pt i)) with h1 | h1 <;> rcases zmod2_cases (g (pt i)) with h2 | h2 <;>
    simp [h1, h2]

theorem tt_mul (f g : Fn) : tt (f * g) = tt f &&& tt g := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, getLsbD_tt, Pi.mul_apply]
  rcases zmod2_cases (f (pt i)) with h1 | h1 <;> rcases zmod2_cases (g (pt i)) with h2 | h2 <;>
    simp [h1, h2]

theorem tt_zero : tt 0 = 0#256 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [getLsbD_tt]

theorem tt_one : tt 1 = -1#256 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_tt, Pi.one_apply, decide_true, Bool.and_true]
  rw [show (-1#256) = BitVec.allOnes 256 by decide, BitVec.getLsbD_allOnes]

set_option maxRecDepth 100000 in
theorem X_bits : ∀ k < 8, ∀ p < 256, (X k).getLsbD p = p.testBit k := by decide

theorem tt_x (k : Fin 8) : tt (x k) = X k.val := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_tt, X_bits k.val k.isLt i hi]
  simp only [x, pt, hi, decide_true, Bool.true_and]
  by_cases h : i.testBit k.val <;> simp [h]

set_option maxRecDepth 100000 in
theorem C_bits : ∀ i < 2, ∀ j < 2, ∀ p < 256, (C (2 * i + j)).getLsbD p =
    ((p.testBit (2 * i) && p.testBit (4 + j)) ^^ (p.testBit (2 * i + 1) && p.testBit (6 + j))) := by
  decide

/-- The Boolean value of an element of `ZMod 2`. -/
def toB (u : ZMod 2) : Bool := decide (u = 1)

theorem toB_add (u v : ZMod 2) : toB (u + v) = (toB u ^^ toB v) := by revert u v; decide
theorem toB_mul (u v : ZMod 2) : toB (u * v) = (toB u && toB v) := by revert u v; decide
theorem toB_ite (q : Bool) : toB (if q then 1 else 0) = q := by cases q <;> decide

theorem tt_c (i j : Fin 2) : tt (c i j) = C (2 * i.val + j.val) := by
  apply BitVec.eq_of_getLsbD_eq; intro p hp
  rw [getLsbD_tt, C_bits i.val i.isLt j.val j.isLt p hp]
  have : decide (c i j (pt p) = 1) = toB (c i j (pt p)) := rfl
  rw [this]
  simp only [c, a, b, x, pt, Pi.add_apply, Pi.mul_apply, toB_add, toB_mul, toB_ite, hp,
    decide_true, Bool.true_and, Fin.val_zero, Fin.val_one, Nat.add_zero]

end MC222
