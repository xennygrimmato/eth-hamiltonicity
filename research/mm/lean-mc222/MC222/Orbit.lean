import MC222.Normal
import MC222.OrbitData

/-!
# Symmetry: moving the first gate onto one of the 72 representatives (Lemma 4.3, Prop. 4.4)

A list `s` of 8 row masks defines the linear map `sig s : F₂⁸ → F₂⁸`, `(sig s p)_k = ℓ_{row k}(p)`.
Composition with it, `compL s`, is linear and multiplicative and maps inputs to linear forms,
so it maps circuits to circuits.  Two finite facts are checked by `native_decide`:
* `checkT_all`: for each of the 432 maps, every target is a combination of the composed
  targets (so a composed circuit still computes the targets);
* `covers_all`: every echelon pair `(a, b)` of 8-bit masks is mapped by some `s` to a pair
  spanning the same plane as one of the 72 representatives.
-/

namespace MC222

open Submodule

/-- The linear form with coefficient mask `a` (bits `0..7`). -/
def lin (a : BitVec 16) : Fn := combF a xN

/-- Row `k` of the map `s`. -/
def row (s : List Nat) (k : Nat) : BitVec 16 := BitVec.ofNat 16 (s.getD k 0)

/-- The linear map of `F₂⁸` with rows `row s k`. -/
def sig (s : List Nat) (p : Pt) : Pt := fun k => lin (row s k.val) p

/-- Composition with `sig s`, as a linear map. -/
def compL (s : List Nat) : Fn →ₗ[ZMod 2] Fn := LinearMap.funLeft (ZMod 2) (ZMod 2) (sig s)

theorem compL_apply (s : List Nat) (f : Fn) (p : Pt) : compL s f p = f (sig s p) := rfl
theorem compL_mul (s : List Nat) (f h : Fn) : compL s (f * h) = compL s f * compL s h := rfl
theorem compL_one (s : List Nat) : compL s 1 = 1 := rfl

theorem compL_xN (s : List Nat) (j : Nat) :
    compL s (xN j) = if j < 8 then lin (row s j) else 0 := by
  funext p
  by_cases h : j < 8
  · simp [compL_apply, xN, h, sig]
  · simp [compL_apply, xN, h]

theorem compL_combF (s : List Nat) (a : BitVec 16) (v : Nat → Fn) :
    compL s (combF a v) = combF a (fun j => compL s (v j)) := by
  simp only [combF, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split <;> simp

/-- `if a_j then v else 0` on masks. -/
def selB (a : BitVec 16) (j : Nat) (v : BitVec 16) : BitVec 16 := if a.getLsbD j then v else 0

/-- The image of the mask `a` under `s`: `ℓ_a ∘ sig s = ℓ_{act s a}`. -/
def act (s : List Nat) (a : BitVec 16) : BitVec 16 :=
  selB a 0 (row s 0) ^^^ selB a 1 (row s 1) ^^^ selB a 2 (row s 2) ^^^ selB a 3 (row s 3) ^^^
  selB a 4 (row s 4) ^^^ selB a 5 (row s 5) ^^^ selB a 6 (row s 6) ^^^ selB a 7 (row s 7)

theorem lin_xor (u w : BitVec 16) : lin (u ^^^ w) = lin u + lin w := combF_xor u w xN

theorem lin_selB (a : BitVec 16) (j : Nat) (v : BitVec 16) :
    lin (selB a j v) = if a.getLsbD j then lin v else 0 := by
  unfold selB; split
  · rfl
  · exact combF_zero xN

theorem compL_lin (s : List Nat) (a : BitVec 16) : compL s (lin a) = lin (act s a) := by
  rw [lin, compL_combF]
  simp only [act, lin_xor, lin_selB, combF, Finset.sum_range_succ, Finset.sum_range_zero,
    compL_xN, zero_add]
  simp

theorem xN_mem_S {k : ℕ} (g : Fin k → Fn) (j i : Nat) : xN i ∈ S g j := by
  unfold xN; split
  · exact x_mem_S _ _ _
  · exact zero_mem _

theorem lin_mem_S {k : ℕ} (g : Fin k → Fn) (j : Nat) (a : BitVec 16) : lin a ∈ S g j :=
  combF_mem _ a xN fun i _ => xN_mem_S g j i

theorem x_eq_xN (k : Fin 8) : x k = xN k.val := by simp [xN, k.isLt]

theorem compL_x (s : List Nat) (k : Fin 8) : compL s (x k) = lin (row s k.val) := by
  rw [x_eq_xN, compL_xN, if_pos k.isLt]

/-- Composition maps the spaces of `g` into those of the composed circuit. -/
theorem compL_mem_S {k : ℕ} (s : List Nat) (g : Fin k → Fn) (j : ℕ) {f : Fn} (hf : f ∈ S g j) :
    compL s f ∈ S (fun i => compL s (g i)) j := by
  have : S g j ≤ (S (fun i => compL s (g i)) j).comap (compL s) :=
    S_le g j _ (by simp [compL_one, one_mem_S]) (fun i => by simp [compL_x, lin_mem_S])
      (fun i hi => by simpa using g_mem_S (fun i => compL s (g i)) i hi)
  exact this hf

theorem compL_isCircuit {k : ℕ} (s : List Nat) (g : Fin k → Fn) (hg : IsCircuit g) :
    IsCircuit (fun i => compL s (g i)) := by
  intro i
  obtain ⟨u, hu, v, hv, he⟩ := hg i
  exact ⟨compL s u, compL_mem_S s g i hu, compL s v, compL_mem_S s g i hv, by
    simp only [he, compL_mul]⟩

/-! ## The targets under composition (checked on truth tables) -/

/-- Truth tables of the inputs, indexed by `ℕ`. -/
def XG (j : Nat) : TT := if j < 8 then X j else 0

theorem tt_xN (j : Nat) : tt (xN j) = XG j := by
  unfold xN XG
  split
  · next h => exact tt_x ⟨j, h⟩
  · exact tt_zero

theorem tt_lin (a : BitVec 16) : tt (lin a) = comb a XG := by
  rw [lin, tt_combF]; simp only [tt_xN]

/-- Truth table of `c i j ∘ sig s`. -/
def cSig (s : List Nat) (i j : Nat) : TT :=
  comb (row s (2 * i)) XG &&& comb (row s (4 + j)) XG ^^^
    comb (row s (2 * i + 1)) XG &&& comb (row s (6 + j)) XG

theorem compL_c (s : List Nat) (i j : Fin 2) :
    compL s (c i j) = lin (row s (2 * i.val)) * lin (row s (4 + j.val)) +
      lin (row s (2 * i.val + 1)) * lin (row s (6 + j.val)) := by
  simp only [c, a, b, map_add, compL_mul, compL_x, Fin.val_zero, Fin.val_one]
  congr 3 <;> ring_nf

theorem tt_compL_c (s : List Nat) (i j : Fin 2) : tt (compL s (c i j)) = cSig s i.val j.val := by
  rw [compL_c, tt_add, tt_mul, tt_mul, tt_lin, tt_lin, tt_lin, tt_lin]; rfl

/-- Bit vector of the combination with mask `d` of the composed targets. -/
def combT (s : List Nat) (d : Nat) : TT :=
  (bif d.testBit 0 then cSig s 0 0 else 0) ^^^ (bif d.testBit 1 then cSig s 0 1 else 0) ^^^
  (bif d.testBit 2 then cSig s 1 0 else 0) ^^^ (bif d.testBit 3 then cSig s 1 1 else 0)

/-- Every target is a combination of the composed targets. -/
def checkT (s : List Nat) : Bool :=
  [(0, 0), (0, 1), (1, 0), (1, 1)].all fun ij =>
    (List.range 16).any fun d => C (2 * ij.1 + ij.2) == combT s d

theorem checkT_all : sigmas.all checkT = true := by native_decide

theorem tt_cond (q : Bool) (f : Fn) : tt (if q then f else 0) = (bif q then tt f else 0) := by
  cases q <;> simp [tt_zero]

theorem compL_computes (s : List Nat) (hs : s ∈ sigmas) (g : Fin 6 → Fn) (hc : Computes g) :
    Computes (fun i => compL s (g i)) := by
  have hck : checkT s = true := List.all_eq_true.mp checkT_all s hs
  have hm : ∀ i j : Fin 2, compL s (c i j) ∈ S (fun i => compL s (g i)) 6 :=
    fun i j => compL_mem_S s g 6 (hc i j)
  intro i j
  have hij : (i.val, j.val) ∈ [(0, 0), (0, 1), (1, 0), (1, 1)] := by
    fin_cases i <;> fin_cases j <;> simp
  obtain ⟨d, -, hd⟩ := List.any_eq_true.mp (List.all_eq_true.mp hck _ hij)
  have hd' : C (2 * i.val + j.val) = combT s d := by simpa using hd
  have : c i j = (if d.testBit 0 then compL s (c 0 0) else 0) +
      (if d.testBit 1 then compL s (c 0 1) else 0) +
      (if d.testBit 2 then compL s (c 1 0) else 0) + (if d.testBit 3 then compL s (c 1 1) else 0) := by
    apply tt_injective
    rw [tt_c, hd', tt_add, tt_add, tt_add, tt_cond, tt_cond, tt_cond, tt_cond, tt_compL_c,
      tt_compL_c, tt_compL_c, tt_compL_c]
    rfl
  rw [this]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;> (split <;> [exact hm _ _; exact zero_mem _])

/-! ## Coverage of all planes -/

/-- `(α, β)` is one of the six ordered bases of `span{a, b}` built from `a, b, a ^^^ b`. -/
def six (a b α β : BitVec 16) : Bool :=
  (α == a && β == b) || (α == b && β == a) || (α == a && β == (a ^^^ b)) ||
  (α == (a ^^^ b) && β == a) || (α == b && β == (a ^^^ b)) || (α == (a ^^^ b) && β == b)

/-- Some map of the list sends the pair `(a, b)` onto a basis of a representative plane. -/
def coveredBy (a b : BitVec 16) : Bool :=
  sigmas.any fun s =>
    let a' := act s a
    let b' := act s b
    reps.any fun r => six a' b' (BitVec.ofNat 16 r.1) (BitVec.ofNat 16 r.2)

/-- Every echelon pair of 8-bit masks is covered. -/
def coversAll : Bool :=
  (List.range 256).all fun a => (List.range 256).all fun b =>
    !(decide (Ech (BitVec.ofNat 16 a) (BitVec.ofNat 16 b))) ||
      coveredBy (BitVec.ofNat 16 a) (BitVec.ofNat 16 b)

theorem covers_all : coversAll = true := by native_decide

end MC222
