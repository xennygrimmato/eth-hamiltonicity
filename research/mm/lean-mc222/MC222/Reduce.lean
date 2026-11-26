import MC222.Orbit

/-!
# Reduction to a normalized circuit with a representative first gate
-/

namespace MC222

open Submodule

theorem gateGensF_zero (g : Fin 6 → Fn) : gateGensF g 0 = xN := by
  funext j; unfold gateGensF
  by_cases h : j < 8
  · simp [h]
  · simp [h, xN]

/-- The six ordered bases give products that differ by elements of any space containing
both factors. -/
theorem six_prod (v : Nat → Fn) (l r α β : BitVec 16) (h : six l r α β = true)
    (M : Submodule (ZMod 2) Fn) (hl : combF l v ∈ M) (hr : combF r v ∈ M) :
    ∃ s ∈ M, combF α v * combF β v = combF l v * combF r v + s := by
  have hxor : combF (l ^^^ r) v = combF l v + combF r v := combF_xor l r v
  simp only [six, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩ <;>
    rw [h1, h2]
  · exact ⟨0, zero_mem _, by rw [add_zero]⟩
  · exact ⟨0, zero_mem _, by rw [add_zero, mul_comm]⟩
  · exact ⟨_, hl, by rw [hxor, mul_add, fn_mul_self, add_comm]⟩
  · exact ⟨_, hl, by rw [hxor, add_mul, fn_mul_self, mul_comm (combF r v), add_comm]⟩
  · exact ⟨_, hr, by rw [hxor, mul_add, fn_mul_self, mul_comm (combF r v)]⟩
  · exact ⟨_, hr, by rw [hxor, add_mul, fn_mul_self]⟩

theorem mem_sup_of' {M : Submodule (ZMod 2) Fn} {y z t : Fn} (ht : t ∈ M) (h : y = z + t) :
    z ∈ M ⊔ span (ZMod 2) {y} := by
  have : z = y + t := by rw [h, add_assoc, fn_add_self, add_zero]
  rw [this]; exact mem_sup_of ht

theorem toNat_lt_of_lowB {l : BitVec 16} (hl : LowB 8 l) : l.toNat < 256 :=
  Nat.lt_pow_two_of_testBit l.toNat fun i hi => hl i hi

/-- Any circuit computing the targets can be replaced by one whose first gate is
`lin a * lin b` for a representative `(a, b)`. -/
theorem orbit_step (g : Fin 6 → Fn) (hg : IsCircuit g) (hc : Computes g) :
    ∃ g' : Fin 6 → Fn, IsCircuit g' ∧ Computes g' ∧
      ∃ r ∈ reps, g' 0 = lin (BitVec.ofNat 16 r.1) * lin (BitVec.ofNat 16 r.2) := by
  -- normalize the first gate
  obtain ⟨l, r, he, hl, hr, hm⟩ := normalize_gate g hg 0
  have hmem : ∀ c, combF c (gateGensF g 0) ∈ S g 0 :=
    fun c => combF_mem _ c _ fun j _ => gateGensF_mem g 0 j
  obtain ⟨hg1, hS1, -⟩ := update_circuit g hg 0 _ _ (hmem l) (hmem r) hm
  set g1 := Function.update g 0 (combF l (gateGensF g 0) * combF r (gateGensF g 0))
  have hc1 : Computes g1 := fun i j => hS1 6 (hc i j)
  have h10 : g1 0 = lin l * lin r := by
    simp only [g1, Function.update_self, gateGensF_zero]; rfl
  -- find the symmetry
  have hl8 := toNat_lt_of_lowB (by simpa using hl)
  have hr8 := toNat_lt_of_lowB (by simpa using hr)
  have hcov := covers_all
  simp only [coversAll, List.all_eq_true, List.mem_range] at hcov
  have hcv := hcov _ hl8 _ hr8
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hcv
  have hcl : coveredBy l r = true := hcv.resolve_left (not_not.mpr he)
  obtain ⟨s, hs, hsr⟩ := List.any_eq_true.mp hcl
  obtain ⟨rp, hrp, hsix⟩ := List.any_eq_true.mp hsr
  -- compose
  set g2 := fun i => compL s (g1 i)
  have hg2 : IsCircuit g2 := compL_isCircuit s g1 hg1
  have hc2 : Computes g2 := compL_computes s hs g1 hc1
  have h20 : g2 0 = lin (act s l) * lin (act s r) := by
    simp only [g2, h10, compL_mul, compL_lin]
  -- replace the first gate by the representative basis of the same plane
  obtain ⟨t, ht, hprod⟩ := six_prod xN _ _ _ _ hsix (S g2 0) (lin_mem_S g2 0 _) (lin_mem_S g2 0 _)
  have hm2 : g2 0 ∈ S g2 0 ⊔ span (ZMod 2) {lin (BitVec.ofNat 16 rp.1) * lin (BitVec.ofNat 16 rp.2)} :=
    mem_sup_of' ht (by rw [h20]; exact hprod)
  obtain ⟨hg3, hS3, -⟩ := update_circuit g2 hg2 0 _ _ (lin_mem_S g2 0 _) (lin_mem_S g2 0 _) hm2
  exact ⟨_, hg3, fun i j => hS3 6 (hc2 i j), rp, hrp, Function.update_self _ _ _⟩

/-- Gate `m` is in normal form. -/
def GateNF (g : Fin 6 → Fn) (m : Fin 6) : Prop :=
  ∃ l r : BitVec 16, Ech l r ∧ LowB (8 + m) l ∧ LowB (8 + m) r ∧
    g m = combF l (gateGensF g m) * combF r (gateGensF g m)

theorem GateNF_congr (g g' : Fin 6 → Fn) (m : Fin 6) (h : ∀ j : Fin 6, j.val ≤ m.val → g j = g' j)
    (hn : GateNF g m) : GateNF g' m := by
  obtain ⟨l, r, he, hl, hr, heq⟩ := hn
  refine ⟨l, r, he, hl, hr, ?_⟩
  rw [← gateGensF_congr g g' m (fun j hj => h j (le_of_lt hj)), ← h m le_rfl, heq]

/-- Normalize gates `1, …, n-1` one after another, keeping the first gate. -/
theorem normalize_upto (g : Fin 6 → Fn) (hg : IsCircuit g) (hc : Computes g) :
    ∀ n ≤ 6, ∃ g' : Fin 6 → Fn, IsCircuit g' ∧ Computes g' ∧ g' 0 = g 0 ∧
      ∀ m : Fin 6, 1 ≤ m.val → m.val < n → GateNF g' m := by
  intro n hn
  induction n with
  | zero => exact ⟨g, hg, hc, rfl, fun m _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨g', hg', hc', h0, hnf⟩ := ih (by omega)
    by_cases hn0 : n = 0
    · subst hn0
      exact ⟨g', hg', hc', h0, fun m h1 h2 => absurd h2 (by omega)⟩
    set m : Fin 6 := ⟨n, by omega⟩
    obtain ⟨l, r, he, hl, hr, hm⟩ := normalize_gate g' hg' m
    have hmem : ∀ c, combF c (gateGensF g' m) ∈ S g' m :=
      fun c => combF_mem _ c _ fun j _ => gateGensF_mem g' m j
    obtain ⟨hg'', hS'', hsame⟩ := update_circuit g' hg' m _ _ (hmem l) (hmem r) hm
    set g'' := Function.update g' m (combF l (gateGensF g' m) * combF r (gateGensF g' m))
    have hlow : ∀ j : Fin 6, j.val < n → g' j = g'' j := fun j hj =>
      (hsame j (fun h => by subst h; simp [m] at hj)).symm
    refine ⟨g'', hg'', fun i j => hS'' 6 (hc' i j), ?_, ?_⟩
    · rw [← h0]; exact (hlow 0 (by omega)).symm
    · intro k h1 h2
      by_cases hk : k.val < n
      · exact GateNF_congr g' g'' k (fun j hj => hlow j (by omega)) (hnf k h1 hk)
      · have hkm : k = m := Fin.ext (by simp [m]; omega)
        subst hkm
        refine ⟨l, r, he, hl, hr, ?_⟩
        rw [← gateGensF_congr g' g'' m hlow]
        exact Function.update_self _ _ _

end MC222
