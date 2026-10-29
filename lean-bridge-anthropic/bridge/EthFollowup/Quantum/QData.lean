/-
# Theorem Q1, bridge part 2: the node tables as streams over factor descriptors

The partition of `Paths.lean` (`cpart`) in word-level form (`clN`, `ilN`, the item endpoints
`loN`, `hiN`, the items at a node `incN`), the description of the factors of a node (`descN`: for
each block and each tail its residues and, per leg, where its bit is: `(0, p)` bit `p` of the
setting, `(1, p)` internal bit `p`, `(2, c)` the constant `c`), and the stream that the table
procedure computes (`streamN`: the sum over the internal bits of the product of the factors, modulo
`M`). **`streamN_eq`**: the stream is the node sum of `Paths.lean` in `ZMod M`.
-/
import EthFollowup.Quantum.QMat

set_option linter.unusedSectionVars false

namespace EthFollowup.Quantum

open Finset

/-! ### Word-level partition -/

section Lists

variable (st : SS) (g : ℕ)

def rgN (v : ℕ × Bool) : ℕ := (reader st v).elim (v.1 % g) (fun t => t % g)
def crossN (v : ℕ × Bool) : Bool := decide (v.1 % g ≠ rgN st g v)
def allN (G : ℕ) : List (ℕ × Bool) := (List.range G).flatMap fun t => [(t, false), (t, true)]
def clN : List (ℕ × Bool) := (allN st.1.length).filter (crossN st g)
def ilN (a : ℕ) : List (ℕ × Bool) := (allN st.1.length).filter fun v => !crossN st g v && decide (v.1 % g = a)
def itemV (k : ℕ) : ℕ × Bool := (clN st g).getD k (0, false)
def loN (k : ℕ) : ℕ := min ((itemV st g k).1 % g) (rgN st g (itemV st g k))
def hiN (k : ℕ) : ℕ := max ((itemV st g k).1 % g) (rgN st g (itemV st g k))
def incN (a : ℕ) : List ℕ := (List.range (clN st g).length).filter fun k => decide (loN st g k = a ∨ hiN st g k = a)
def refN (a : ℕ) (v : ℕ × Bool) : ℕ × ℕ :=
  if v ∈ clN st g then (0, (incN st g a).idxOf ((clN st g).idxOf v)) else (1, (ilN st g a).idxOf v)
def srcRefN (a : ℕ) (xs : List Bool) (q : ℕ) (s : Src) : ℕ × ℕ := s.elim (2, (xs.getD q false).toNat) (refN st g a)
def tailGrpN (q : ℕ) : ℕ := (st.2.2.getD q none).elim 0 (fun v => v.1 % g)

/-- A factor: its residues and its legs. -/
abbrev FDesc := List ℕ × List (ℕ × ℕ)

def blockDesc (M z₁ z₂ z₃ : ℕ) (xs : List Bool) (a t : ℕ) : FDesc :=
  (blkEntN M z₁ z₂ z₃ (blkAt st t), [refN st g a (t, false), refN st g a (t, true),
    srcRefN st g a xs (blkAt st t).2.1.1 (blkAt st t).2.2.1.1, srcRefN st g a xs (blkAt st t).2.1.2 (blkAt st t).2.2.1.2])

def tailDesc (M z₁ z₂ z₃ : ℕ) (xs ys : List Bool) (a q : ℕ) : FDesc :=
  (prodLN M z₁ z₂ z₃ (st.2.1.getD q []), [(2, (ys.getD q false).toNat), srcRefN st g a xs q (st.2.2.getD q none)])

/-- **The factors of node `a`**: its blocks, then its tails. -/
def descN (n M z₁ z₂ z₃ : ℕ) (xs ys : List Bool) (a : ℕ) : List FDesc :=
  ((List.range st.1.length).filter (fun t => decide (t % g = a))).map (blockDesc st g M z₁ z₂ z₃ xs a) ++
    ((List.range n).filter (fun q => decide (tailGrpN st g q = a))).map (tailDesc st g M z₁ z₂ z₃ xs ys a)

end Lists

/-! ### The stream -/

def legBitB (z : List Bool) (β : ℕ → Bool) (r : ℕ × ℕ) : Bool :=
  if r.1 = 0 then z.getD r.2 false else if r.1 = 1 then β r.2 else decide (r.2 = 1)
def fidxB (z : List Bool) (β : ℕ → Bool) (legs : List (ℕ × ℕ)) : ℕ :=
  legs.foldl (fun acc r => 2 * acc + (legBitB z β r).toNat) 0
def fvalB (z : List Bool) (β : ℕ → Bool) (f : FDesc) : ℕ := f.1.getD (fidxB z β f.2) 0
/-- One term: the product of the factors at the internal bits of `i`, modulo `M`. -/
def termN (M : ℕ) (fs : List FDesc) (z : List Bool) (i : ℕ) : ℕ := (fs.map (fvalB z i.testBit)).prod % M
/-- **The stream**: the sum of the terms over the `2^N` values of the internal bits. -/
def streamN (M N : ℕ) (fs : List FDesc) (z : List Bool) : ℕ := ∑ i ∈ range (2 ^ N), termN M fs z i

/-! ### Sums over the bits of a number -/

def extB {N : ℕ} (w : Fin N → Bool) (p : ℕ) : Bool := if h : p < N then w ⟨p, h⟩ else false

def cons0 (b : Bool) (β : ℕ → Bool) (p : ℕ) : Bool := if p = 0 then b else β (p - 1)

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (K : ℕ) :
    ∑ i ∈ range (2 * K), f i = ∑ j ∈ range K, (f (2 * j) + f (2 * j + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ,
      add_assoc]

theorem testBit_two_mul_add (j : ℕ) (b : Bool) : (fun p => (2 * j + b.toNat).testBit p) = cons0 b j.testBit := by
  funext p
  rcases p with _ | p
  · simp only [Nat.testBit_zero, cons0, ↓reduceIte]; cases b <;> simp <;> omega
  · simp only [Nat.testBit_succ, cons0, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    congr 1; cases b <;> simp <;> omega

theorem extB_cons {N : ℕ} (b : Bool) (w : Fin N → Bool) :
    extB (Fin.cons (α := fun _ => Bool) b w) = cons0 b (extB w) := by
  funext p
  rcases p with _ | p
  · simp [extB, cons0]
  · simp only [extB, cons0, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    by_cases h : p < N
    · rw [dif_pos (by omega), dif_pos h]
      exact Fin.cons_succ (α := fun _ => Bool) b w ⟨p, h⟩
    · rw [dif_neg (by omega), dif_neg h]

theorem sum_cons {N : ℕ} {M : Type*} [AddCommMonoid M] (G : (Fin (N + 1) → Bool) → M) :
    ∑ w, G w = ∑ b : Bool, ∑ w' : Fin N → Bool, G (Fin.cons (α := fun _ => Bool) b w') := by
  rw [← Fintype.sum_prod_type' (f := fun b w' => G (Fin.cons (α := fun _ => Bool) b w'))]
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Bool) _ _ fun p => rfl).symm

/-- **The numbers below `2^N` are the assignments of `N` bits.** -/
theorem sum_testBit {M : Type*} [AddCommMonoid M] : ∀ (N : ℕ) (F : (ℕ → Bool) → M),
    ∑ i ∈ range (2 ^ N), F i.testBit = ∑ w : Fin N → Bool, F (extB w)
  | 0, F => by
    have : ∀ w : Fin 0 → Bool, (0 : ℕ).testBit = extB w := by
      intro w; funext p; simp [extB]
    simp only [pow_zero, range_one, sum_singleton, Finset.univ_unique, sum_singleton]
    rw [this]
  | N + 1, F => by
    rw [pow_succ, mul_comm, sum_range_two_mul, sum_cons]
    have h0 := testBit_two_mul_add
    have e : ∀ j, F (2 * j).testBit + F (2 * j + 1).testBit = ∑ b : Bool, F (cons0 b j.testBit) := by
      intro j
      rw [Fintype.sum_bool, ← h0 j true, ← h0 j false]
      simp [add_comm]
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [sum_testBit N (fun β => F (cons0 b β))]
    simp only [extB_cons]

/-! ### Products over lists and finsets -/

theorem prod_filter_range {M : Type*} [CommMonoid M] (G : ℕ) (p : ℕ → Prop) [DecidablePred p] (h : ℕ → M) :
    (((List.range G).filter fun t => decide (p t)).map h).prod = ∏ t ∈ (range G).filter p, h t := by
  rw [← List.prod_toFinset h ((List.nodup_range).filter _)]
  congr 1; ext t; simp

theorem fin_prod_filter {M : Type*} [CommMonoid M] (G : ℕ) (p : ℕ → Prop) [DecidablePred p] (h : ℕ → M) :
    ∏ t ∈ Finset.univ.filter (fun t : Fin G => p t.val), h t.val = ∏ t ∈ (range G).filter p, h t := by
  rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_eq_prod_range (fun t => if p t then h t else 1)]

/-! ### The word-level partition is `cpart` -/

/-- A leg as a pair of numbers. -/
def vval {G : ℕ} (v : Fin G × Bool) : ℕ × Bool := (v.1.val, v.2)

theorem vval_inj {G : ℕ} : Function.Injective (vval (G := G)) := by
  rintro ⟨t, i⟩ ⟨t', i'⟩ h
  simp only [vval, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) h.2

theorem map_val_finRange (G : ℕ) : (List.finRange G).map Fin.val = List.range G :=
  List.ext_getElem (by simp) fun i h1 h2 => by simp

theorem allV_map (G : ℕ) : (allV G).map vval = allN G := by
  have e : allV G = (List.finRange G).flatMap fun t => [(t, false), (t, true)] := by
    simp [allV, SProd.sprod, List.product]
  rw [e, List.map_flatMap, allN, ← map_val_finRange, List.flatMap_map]
  rfl

theorem idxOf_map_inj {α β : Type*} [DecidableEq α] [BEq β] [LawfulBEq β] {f : α → β}
    (hf : Function.Injective f) (a : α) : ∀ l : List α,
      (l.map f).idxOf (f a) = @List.idxOf _ instBEqOfDecidableEq a l
  | [] => rfl
  | b :: l => by
    simp only [List.map_cons, List.idxOf_cons]
    by_cases h : b = a
    · subst h; simp
    · have : ¬ f b = f a := fun e => h (hf e)
      have h1 : (f b == f a) = false := beq_eq_false_iff_ne.2 this
      have h2 : (@BEq.beq _ instBEqOfDecidableEq b a) = false := by simp [h]
      rw [h1, h2, idxOf_map_inj hf a l]

variable (st : SS) (g : ℕ) [NeZero g]

theorem rg_val (v : ℕ × Bool) : (rg st g v).val = rgN st g v := by
  unfold rg rgN; cases reader st v <;> rfl

theorem crossB_eq (v : Fin st.1.length × Bool) : crossB st g v = crossN st g (vval v) := by
  unfold crossB crossN
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ne_eq, ne_eq, Fin.ext_iff, rg_val]
  rfl

theorem cl_map : (cpart st g).cl.map vval = clN st g := by
  simp only [cpart, clN, ← allV_map, List.filter_map]
  congr 1
  exact List.filter_congr fun v _ => by simp [crossB_eq]

theorem il_map (a : Fin g) : ((cpart st g).il a).map vval = ilN st g a.val := by
  simp only [cpart, ilN, ← allV_map, List.filter_map]
  congr 1
  refine List.filter_congr fun v _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [crossB_eq, vval, grp, Fin.ext_iff, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_iff,
    Function.comp_apply]
  exact and_congr Iff.rfl decide_eq_true_iff.symm

theorem length_cl : (cpart st g).cl.length = (clN st g).length := by rw [← cl_map, List.length_map]

theorem length_il (a : Fin g) : ((cpart st g).il a).length = (ilN st g a.val).length := by
  rw [← il_map, List.length_map]

theorem mem_clN (v : Fin st.1.length × Bool) : vval v ∈ clN st g ↔ v ∈ (cpart st g).cl := by
  rw [← cl_map, List.mem_map]
  exact ⟨fun ⟨w, hw, e⟩ => vval_inj e ▸ hw, fun h => ⟨v, h, rfl⟩⟩

theorem mem_ilN (a : Fin g) (v : Fin st.1.length × Bool) : vval v ∈ ilN st g a.val ↔ v ∈ (cpart st g).il a := by
  rw [← il_map, List.mem_map]
  exact ⟨fun ⟨w, hw, e⟩ => vval_inj e ▸ hw, fun h => ⟨v, h, rfl⟩⟩

theorem mem_allN {G : ℕ} {v : ℕ × Bool} : v ∈ allN G ↔ v.1 < G := by
  rcases v with ⟨t, i⟩
  simp only [allN, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false,
    Prod.mk.injEq]
  constructor
  · rintro ⟨t', h, h'⟩; rcases h' with h' | h' <;> (rw [h'.1]; exact h)
  · intro h; exact ⟨t, h, by cases i <;> simp⟩

/-- The setting of node `a` for the crossing bits `ℓ`. -/
def zOf (a : ℕ) (ℓ : Fin (cpart st g).cl.length → Bool) : List Bool :=
  (incN st g a).map fun k => if h : k < (cpart st g).cl.length then ℓ ⟨k, h⟩ else false

theorem getD_map_idxOf {α β : Type*} [DecidableEq α] (f : α → β) {l : List α} {a : α} (h : a ∈ l) (d : β) :
    (l.map f).getD (l.idxOf a) d = f a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h), List.getElem_idxOf]
  rfl

/-- **The bit of a leg attached to node `a`** is the bit of the glued assignment. -/
theorem legBit_ref (a : Fin g) (ℓ : Fin (cpart st g).cl.length → Bool)
    (w : Fin ((cpart st g).il a).length → Bool) {t : ℕ} (ht : t < st.1.length) (i : Bool)
    (hat : t % g = a.val ∨ rgN st g (t, i) = a.val) :
    legBitB (zOf st g a.val ℓ) (extB w) (refN st g a.val (t, i)) = (cpart st g).glue a ℓ w (⟨t, ht⟩, i) := by
  set v' : Fin st.1.length × Bool := (⟨t, ht⟩, i)
  have hv : vval v' = (t, i) := rfl
  unfold refN
  by_cases hc : (t, i) ∈ clN st g
  · have hc' : v' ∈ (cpart st g).cl := (mem_clN st g v').1 hc
    rw [if_pos hc]
    simp only [legBitB, ↓reduceIte]
    set k := (clN st g).idxOf (t, i)
    have hk : k < (clN st g).length := List.idxOf_lt_length_of_mem hc
    have hitem : itemV st g k = (t, i) := by
      simp only [itemV, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, k, List.getElem_idxOf]; rfl
    have hinc : k ∈ incN st g a.val := by
      simp only [incN, List.mem_filter, List.mem_range, hk, true_and, decide_eq_true_eq, loN, hiN, hitem]
      omega
    unfold zOf
    rw [getD_map_idxOf _ hinc]
    have hk' : k = @List.idxOf _ instBEqOfDecidableEq v' (cpart st g).cl := by
      rw [← idxOf_map_inj vval_inj v' (cpart st g).cl, cl_map]; rfl
    simp only [VPart.glue, dif_pos hc']
    rw [dif_pos (by rw [length_cl]; exact hk)]
    congr 1; exact Fin.ext hk'

  · rw [if_neg hc]
    have hil : (t, i) ∈ ilN st g a.val := by
      have hcr : crossN st g (t, i) = false := by
        simp only [clN, List.mem_filter, mem_allN, ht, true_and] at hc; simpa using hc
      simp only [crossN, decide_eq_false_iff_not, not_not] at hcr
      simp only [ilN, List.mem_filter, mem_allN, ht, true_and, Bool.and_eq_true, Bool.not_eq_true',
        crossN, decide_eq_true_eq, decide_eq_false_iff_not, not_not]
      exact ⟨hcr, by omega⟩
    have hil' : v' ∈ (cpart st g).il a := (mem_ilN st g a v').1 hil
    have hc' : v' ∉ (cpart st g).cl := fun h => hc ((mem_clN st g v').2 h)
    simp only [legBitB, show (1 : ℕ) ≠ 0 by omega, ↓reduceIte, extB]
    have hp : (ilN st g a.val).idxOf (t, i) = @List.idxOf _ instBEqOfDecidableEq v' ((cpart st g).il a) := by
      rw [← idxOf_map_inj vval_inj v' ((cpart st g).il a), il_map]; rfl
    simp only [VPart.glue, dif_neg hc', dif_pos hil']
    rw [dif_pos (by first
      | (rw [length_il]; exact List.idxOf_lt_length_of_mem hil)
      | (rw [← hp, length_il]; exact List.idxOf_lt_length_of_mem hil))]
    congr 1; exact Fin.ext hp

theorem getD_ofFn {n : ℕ} (x : Basis n) (q : ℕ) : (List.ofFn x).getD q false = vq x q := by
  unfold vq
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl

theorem legBit_const (z : List Bool) (β : ℕ → Bool) (b : Bool) : legBitB z β (2, b.toNat) = b := by
  cases b <;> simp [legBitB]

theorem sv_glue {n : ℕ} (x : Basis n) (a : Fin g) (ℓ : Fin (cpart st g).cl.length → Bool)
    (w : Fin ((cpart st g).il a).length → Bool) (q : ℕ) (s : Src)
    (hs : ∀ t i, s = some (t, i) → t < st.1.length ∧ (t % g = a.val ∨ rgN st g (t, i) = a.val)) :
    legBitB (zOf st g a.val ℓ) (extB w) (srcRefN st g a.val (List.ofFn x) q s) =
      sv x (oV ((cpart st g).glue a ℓ w)) q s := by
  rcases s with _ | ⟨t, i⟩
  · simp only [srcRefN, Option.elim, legBit_const, getD_ofFn, sv]
  · obtain ⟨ht, hat⟩ := hs t i rfl
    simp only [srcRefN, Option.elim]
    rw [legBit_ref st g a ℓ w ht i hat]
    simp only [sv, rd, dif_pos ht, oV]
    cases i <;> rfl

/-! ### The stream is the node sum -/

theorem fidx4 (z : List Bool) (β : ℕ → Bool) (r₁ r₂ r₃ r₄ : ℕ × ℕ) :
    fidxB z β [r₁, r₂, r₃, r₄] = 4 * (bit2 (legBitB z β r₁) (legBitB z β r₂)).val +
      (bit2 (legBitB z β r₃) (legBitB z β r₄)).val := by
  simp only [fidxB, List.foldl, bit2]; ring

theorem bit_val (b : Bool) : (bit b).val = b.toNat := by cases b <;> rfl

theorem fidx2 (z : List Bool) (β : ℕ → Bool) (r₁ r₂ : ℕ × ℕ) :
    fidxB z β [r₁, r₂] = 2 * (bit (legBitB z β r₁)).val + (bit (legBitB z β r₂)).val := by
  simp only [fidxB, List.foldl, bit_val]; ring

theorem rgN_of_src (hg2 : Good2 st.1.length st) {t : ℕ} (ht : t < st.1.length) {j : Bool} {v : ℕ × Bool}
    (e : srcOf (blkAt st t) j = some v) : rgN st g v = t % g := by
  unfold rgN; rw [reader_eq st hg2 rfl ht e]; rfl

theorem fval_block {n : ℕ} (hg2 : Good2 st.1.length st) {M b z₁ z₂ z₃ : ℕ} [NeZero M]
    (hz : ZP M b z₁ z₂ z₃) (x : Basis n) (a : Fin g) (ℓ : Fin (cpart st g).cl.length → Bool)
    (w : Fin ((cpart st g).il a).length → Bool) {t : ℕ} (ht : t < st.1.length) (hta : t % g = a.val) :
    (fvalB (zOf st g a.val ℓ) (extB w) (blockDesc st g M z₁ z₂ z₃ (List.ofFn x) a.val t) : ZMod M) =
      blockF (IM M b) x (oV ((cpart st g).glue a ℓ w)) t (blkAt st t) := by
  unfold fvalB blockDesc
  simp only
  rw [fidx4]
  show toM4 M (blkEntN M z₁ z₂ z₃ (blkAt st t)) _ _ = _
  rw [toM4_blkEntN hz]
  have hrd : rd (oV ((cpart st g).glue a ℓ w)) t =
      ((cpart st g).glue a ℓ w (⟨t, ht⟩, false), (cpart st g).glue a ℓ w (⟨t, ht⟩, true)) := by
    simp [rd, dif_pos ht, oV]
  have hsrc : ∀ j, ∀ t' i, srcOf (blkAt st t) j = some (t', i) →
      t' < st.1.length ∧ (t' % g = a.val ∨ rgN st g (t', i) = a.val) := by
    intro j t' i e
    obtain ⟨h1, -, -⟩ := hg2.src t j t' i (hg2.len ▸ ht) e
    exact ⟨h1.trans ht, Or.inr ((rgN_of_src st g hg2 ht e).trans hta)⟩
  unfold blockF
  rw [hrd, legBit_ref st g a ℓ w ht false (Or.inl hta), legBit_ref st g a ℓ w ht true (Or.inl hta),
    sv_glue st g x a ℓ w _ (blkAt st t).2.2.1.1 (hsrc false), sv_glue st g x a ℓ w _ (blkAt st t).2.2.1.2 (hsrc true)]

theorem tailGrp_val {n : ℕ} (q : ℕ) : (tailGrp st g q).val = tailGrpN st g q := by
  unfold tailGrp tailGrpN
  cases st.2.2.getD q none <;> rfl

theorem fval_tail {n : ℕ} (hg : Good n st.1.length st) {M b z₁ z₂ z₃ : ℕ} [NeZero M]
    (hz : ZP M b z₁ z₂ z₃) (x y : Basis n) (a : Fin g) (ℓ : Fin (cpart st g).cl.length → Bool)
    (w : Fin ((cpart st g).il a).length → Bool) {q : ℕ} (hq : q < n) (hqa : tailGrpN st g q = a.val) :
    (fvalB (zOf st g a.val ℓ) (extB w) (tailDesc st g M z₁ z₂ z₃ (List.ofFn x) (List.ofFn y) a.val q) : ZMod M) =
      tailF (IM M b) x (oV ((cpart st g).glue a ℓ w)) st y ⟨q, hq⟩ := by
  unfold fvalB tailDesc
  simp only
  rw [fidx2]
  show toM2 M (prodLN M z₁ z₂ z₃ (st.2.1.getD q [])) _ _ = _
  rw [toM2_prodLN hz]
  have hs : ∀ t i, st.2.2.getD q none = some (t, i) →
      t < st.1.length ∧ (t % g = a.val ∨ rgN st g (t, i) = a.val) := by
    intro t i e
    refine ⟨hg.csrc q t i e, Or.inl ?_⟩
    unfold tailGrpN at hqa; rw [e] at hqa; exact hqa
  unfold tailF
  rw [legBit_const, getD_ofFn, sv_glue st g x a ℓ w _ _ hs]
  simp [vq, hq]

/-- **The stream of node `a` is its node sum** (`Paths.lean`) in `ZMod M`. -/
theorem streamN_eq {n : ℕ} (hg : Good n st.1.length st) (hg2 : Good2 st.1.length st) {M b z₁ z₂ z₃ : ℕ}
    [NeZero M] (hz : ZP M b z₁ z₂ z₃) (x y : Basis n) (a : Fin g) (ℓ : Fin (cpart st g).cl.length → Bool) :
    (streamN M (ilN st g a.val).length (descN st g n M z₁ z₂ z₃ (List.ofFn x) (List.ofFn y) a.val)
      (zOf st g a.val ℓ) : ZMod M) =
      ∑ w : Fin ((cpart st g).il a).length → Bool, nodeF (IM M b) st g x y a ((cpart st g).glue a ℓ w) := by
  rw [← length_il]
  unfold streamN termN
  rw [Nat.cast_sum]
  simp only [ZMod.natCast_mod]
  refine (sum_testBit _ (fun β => (((descN st g n M z₁ z₂ z₃ (List.ofFn x) (List.ofFn y) a.val).map
    (fvalB (zOf st g a.val ℓ) β)).prod : ZMod M))).trans ?_
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Nat.cast_list_prod, List.map_map, descN, List.map_append, List.prod_append, List.map_map, List.map_map,
    prod_filter_range, prod_filter_range]
  unfold nodeF
  congr 1
  · rw [fin_prod_filter st.1.length (fun t => grp g t = a)
      (fun t => blockF (IM M b) x (oV ((cpart st g).glue a ℓ w)) t (blkAt st t))]
    have hf : (range st.1.length).filter (fun t => grp g t = a) = (range st.1.length).filter (fun t => t % g = a.val) :=
      Finset.filter_congr fun t _ => by simp [grp, Fin.ext_iff]
    rw [hf]
    refine Finset.prod_congr rfl fun t ht => ?_
    obtain ⟨ht1, ht2⟩ := Finset.mem_filter.1 ht
    rw [Function.comp_apply, Function.comp_apply]
    exact fval_block st g hg2 hz x a ℓ w (Finset.mem_range.1 ht1) ht2
  · have e1 : ∏ q ∈ Finset.univ.filter (fun q : Fin n => tailGrp st g q.val = a),
        tailF (IM M b) x (oV ((cpart st g).glue a ℓ w)) st y q =
        ∏ q ∈ Finset.univ.filter (fun q : Fin n => tailGrp st g q.val = a),
          (fun q : ℕ => if h : q < n then tailF (IM M b) x (oV ((cpart st g).glue a ℓ w)) st y ⟨q, h⟩ else 1) q.val :=
      Finset.prod_congr rfl fun q _ => by simp [dif_pos q.2]
    rw [e1]
    refine Eq.trans ?_ (fin_prod_filter n (fun q => tailGrp st g q = a) (fun q =>
      if h : q < n then tailF (IM M b) x (oV ((cpart st g).glue a ℓ w)) st y ⟨q, h⟩ else 1)).symm
    have hf : (range n).filter (fun q => tailGrp st g q = a) = (range n).filter (fun q => tailGrpN st g q = a.val) :=
      Finset.filter_congr fun q _ => by rw [Fin.ext_iff, tailGrp_val st g (n := n)]
    rw [hf]
    refine Finset.prod_congr rfl fun q hq => ?_
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
    have hqn := Finset.mem_range.1 hq1
    rw [Function.comp_apply, Function.comp_apply, fval_tail st g hg hz x y a ℓ w hqn hq2, dif_pos hqn]

end EthFollowup.Quantum
