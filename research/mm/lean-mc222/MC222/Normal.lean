import MC222.Comb
import MC222.Circuit

/-!
# Normal form of a gate (Lemma 4.1(b),(c) of the paper)

Every gate `g m = u * v` can be replaced by a product `combF l G * combF r G` of two
constant-free combinations of the generators `G = gateGensF g m` (inputs and earlier gates),
with `(l, r)` a reduced echelon pair, such that the old gate lies in `S g m + span{new gate}`.
-/

namespace MC222

open Submodule

theorem low_of {n : Nat} (hn : 8 ≤ n ∧ n ≤ 13) {c : BitVec 16}
    (h : ∀ i, n ≤ i → c.getLsbD i = false) : Low n c := by
  unfold Low; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases hin : n ≤ i
  · simp [h i hin]
  · have : ((1#16 <<< n) - 1).getLsbD i = true := by
      obtain rfl | rfl | rfl | rfl | rfl | rfl : n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 := by omega
      all_goals (interval_cases i <;> first | omega | decide)
    simp only [this, Bool.not_true, Bool.and_false]
    exact (by simp : BitVec.getLsbD (0 : BitVec 16) i = false).symm

theorem ech_exists (l r : BitVec 16) (h1 : l ≠ 0) (h2 : r ≠ 0) (h3 : l ≠ r) :
    Ech l r ∨ Ech r l ∨ Ech l (l ^^^ r) ∨ Ech (l ^^^ r) l ∨ Ech r (l ^^^ r) ∨ Ech (l ^^^ r) r := by
  unfold Ech; bv_decide
/-- Inputs indexed by `ℕ` (zero beyond 7). -/
def xN (j : Nat) : Fn := if h : j < 8 then x ⟨j, h⟩ else 0
/-- Gates indexed by `ℕ` (zero beyond 5). -/
def gN (g : Fin 6 → Fn) (j : Nat) : Fn := if h : j < 6 then g ⟨j, h⟩ else 0
/-- Generators for the factors of gate `i`: inputs at `0..7`, gate `j` at `8 + j` for `j < i`. -/
def gateGensF (g : Fin 6 → Fn) (i j : Nat) : Fn :=
  if j < 8 then xN j else if j < 8 + i then gN g (j - 8) else 0
/-- The coefficient vector `c` vanishes at positions `≥ n`. -/
def LowB (n : Nat) (c : BitVec 16) : Prop := ∀ i, n ≤ i → c.getLsbD i = false

theorem gateGensF_mem (g : Fin 6 → Fn) (i : Nat) (j : Nat) : gateGensF g i j ∈ S g i := by
  unfold gateGensF
  split_ifs with h1 h2
  · rw [xN, dif_pos h1]; exact x_mem_S _ _ _
  · by_cases h : j - 8 < 6
    · unfold gN; rw [dif_pos h]; exact g_mem_S g ⟨j - 8, h⟩ (by simp; omega)
    · unfold gN; rw [dif_neg h]; exact zero_mem _
  · exact zero_mem _

theorem gateGensF_congr (g g' : Fin 6 → Fn) (i : Nat) (h : ∀ j : Fin 6, j.val < i → g j = g' j) :
    gateGensF g i = gateGensF g' i := by
  funext j
  unfold gateGensF gN
  split_ifs with h1 h2 h3 <;> try rfl
  exact h _ (by simp; omega)

theorem S_le_gate (g : Fin 6 → Fn) (i : Nat) (hi : i ≤ 8) :
    S g i ≤ span (ZMod 2) (insert 1 (Set.range (fun j : Fin 16 => gateGensF g i j))) := by
  refine S_le g i _ (subset_span (Set.mem_insert _ _)) (fun k => ?_) (fun i' hi' => ?_)
  · refine subset_span (Set.mem_insert_of_mem _ ⟨⟨k.val, by omega⟩, ?_⟩)
    simp [gateGensF, xN, k.isLt]
  · refine subset_span (Set.mem_insert_of_mem _ ⟨⟨8 + i'.val, by omega⟩, ?_⟩)
    simp [gateGensF, gN, hi', i'.isLt]

theorem lowB_cut (n : Nat) (c : BitVec 16) :
    LowB n (ofPred 16 (fun j => decide (j < n) && c.getLsbD j)) := by
  intro i hi; rw [getLsbD_ofPred]; simp; omega

/-- An element of `S g i` is a constant plus a constant-free combination of the generators. -/
theorem decomp (g : Fin 6 → Fn) (i : Nat) (hi : i ≤ 6) {u : Fn} (hu : u ∈ S g i) :
    ∃ (e : ZMod 2) (l : BitVec 16), LowB (8 + i) l ∧ u = e • 1 + combF l (gateGensF g i) := by
  obtain ⟨e, z, hz, rfl⟩ := mem_span_insert.mp (S_le_gate g i (by omega) hu)
  obtain ⟨c, rfl⟩ := exists_combF hz
  refine ⟨e, _, lowB_cut (8 + i) c, ?_⟩
  rw [combF_cut]
  intro j hj; simp [gateGensF, show ¬ j < 8 by omega, show ¬ j < 8 + i by omega]

theorem fn_mul_self (f : Fn) : f * f = f := by
  funext p; simp only [Pi.mul_apply]; generalize f p = u; revert u; decide

theorem prod_decomp (e f : ZMod 2) (L R : Fn) :
    (e • 1 + L) * (f • 1 + R) = L * R + (e • R + f • L + (e * f) • (1 : Fn)) := by
  simp only [Algebra.smul_def, map_mul]; ring

theorem mem_sup_of {M : Submodule (ZMod 2) Fn} {y t : Fn} (ht : t ∈ M) :
    y + t ∈ M ⊔ span (ZMod 2) {y} :=
  mem_sup.mpr ⟨t, ht, y, mem_span_singleton_self y, add_comm _ _⟩

theorem lowB_xor {n : Nat} {l r : BitVec 16} (hl : LowB n l) (hr : LowB n r) : LowB n (l ^^^ r) := by
  intro i hi; rw [BitVec.getLsbD_xor, hl i hi, hr i hi]; rfl

theorem lowB_small {n : Nat} (hn : 8 ≤ n) (c : Nat) (hc : c < 256) : LowB n (BitVec.ofNat 16 c) := by
  intro i hi
  rw [BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  have : c / 2 ^ i = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hc (by
    calc 256 = 2 ^ 8 := rfl
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))
  simp [this]

/-- Normal form of one gate. -/
theorem normalize_gate (g : Fin 6 → Fn) (hg : IsCircuit g) (m : Fin 6) :
    ∃ l r : BitVec 16, Ech l r ∧ LowB (8 + m) l ∧ LowB (8 + m) r ∧
      g m ∈ S g m ⊔ span (ZMod 2) {combF l (gateGensF g m) * combF r (gateGensF g m)} := by
  obtain ⟨u, hu, v, hv, huv⟩ := hg m
  have hm6 : m.val ≤ 6 := by omega
  obtain ⟨e, l, hl, rfl⟩ := decomp g m hm6 hu
  obtain ⟨f, r, hr, rfl⟩ := decomp g m hm6 hv
  set G := gateGensF g m
  have hmemc : ∀ c, combF c G ∈ S g m := fun c => combF_mem _ c G fun j _ => gateGensF_mem g m j
  set L := combF l G
  set R := combF r G
  have hs : e • R + f • L + (e * f) • (1 : Fn) ∈ S g m :=
    add_mem (add_mem (smul_mem _ _ (hmemc r)) (smul_mem _ _ (hmemc l)))
      (smul_mem _ _ (one_mem_S _ _))
  rw [prod_decomp] at huv
  -- generic finishing step: a new product `L' * R' = L * R + s'` with `s' ∈ S g m`
  have finish : ∀ l' r' : BitVec 16, Ech l' r' → LowB (8 + m) l' → LowB (8 + m) r' →
      ∀ s' ∈ S g m, combF l' G * combF r' G = L * R + s' →
      ∃ l r : BitVec 16, Ech l r ∧ LowB (8 + m) l ∧ LowB (8 + m) r ∧
        g m ∈ S g m ⊔ span (ZMod 2) {combF l G * combF r G} := by
    intro l' r' he hl' hr' s' hs' heq
    refine ⟨l', r', he, hl', hr', ?_⟩
    have : g m = combF l' G * combF r' G + (s' + (e • R + f • L + (e * f) • (1 : Fn))) := by
      rw [huv, heq, show ∀ a b c : Fn, a + b + (b + c) = a + c from fun a b c => by
        rw [show a + b + (b + c) = a + (b + b) + c by abel, fn_add_self, add_zero]]
    rw [this]; exact mem_sup_of (add_mem hs' hs)
  by_cases hdeg : l ≠ 0 ∧ r ≠ 0 ∧ l ≠ r
  · obtain ⟨h1, h2, h3⟩ := hdeg
    have hxor : combF (l ^^^ r) G = L + R := combF_xor l r G
    rcases ech_exists l r h1 h2 h3 with h | h | h | h | h | h
    · exact finish l r h hl hr 0 (zero_mem _) (by simp [L, R])
    · exact finish r l h hr hl 0 (zero_mem _) (by rw [add_zero, mul_comm])
    · exact finish l (l ^^^ r) h hl (lowB_xor hl hr) L (hmemc l)
        (by rw [hxor, mul_add, fn_mul_self, add_comm])
    · exact finish (l ^^^ r) l h (lowB_xor hl hr) hl L (hmemc l)
        (by rw [hxor, add_mul, fn_mul_self, mul_comm R L, add_comm])
    · exact finish r (l ^^^ r) h hr (lowB_xor hl hr) R (hmemc r)
        (by rw [hxor, mul_add, fn_mul_self, mul_comm R L])
    · exact finish (l ^^^ r) r h (lowB_xor hl hr) hr R (hmemc r)
        (by rw [hxor, add_mul, fn_mul_self])
  · -- degenerate: `L * R ∈ S g m`; use the padding product `x 0 * x 1`
    have hLR : L * R ∈ S g m := by
      by_cases h1 : l = 0
      · have : L = 0 := by simp only [L, h1, combF_zero]
        rw [this, zero_mul]; exact zero_mem _
      by_cases h2 : r = 0
      · have : R = 0 := by simp only [R, h2, combF_zero]
        rw [this, mul_zero]; exact zero_mem _
      have h3 : l = r := by tauto
      simp only [L, R, h3, fn_mul_self]; exact hmemc r
    refine ⟨1#16, 2#16, by unfold Ech; decide, lowB_small (by omega) 1 (by norm_num),
      lowB_small (by omega) 2 (by norm_num), mem_sup_left ?_⟩
    rw [huv]; exact add_mem hLR hs

end MC222
