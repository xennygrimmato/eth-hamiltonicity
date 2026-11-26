import MC222.Helpers

/-!
# From the cube propositions to the lower bound

`lower_of_cubes`: if all 360 cube propositions `Cube a b 0 h` (representative `(a, b)`,
`1 ≤ h ≤ 5`) hold, then no circuit with 6 gates computes the 2×2 matrix product.
-/

namespace MC222

open Submodule

set_option maxHeartbeats 0

theorem gate_ok (g : Fin 6 → Fn) (m : Fin 6) (hm : 1 ≤ m.val) (hm' : m.val ≤ 5) (hnf : GateNF g m) :
    ∃ l r, GateOK (GT g) m.val l r := by
  obtain ⟨l, r, he, hl, hr, heq⟩ := hnf
  refine ⟨l, r, ?_, he, low_of ⟨by omega, by omega⟩ hl, low_of ⟨by omega, by omega⟩ hr⟩
  have hg : gateGens (GT g) m.val = fun j => tt (gateGensF g m.val j) := by
    funext j; rw [tt_gateGensF]
  rw [GT_eq, gN_val, heq, tt_mul, tt_combF, tt_combF, hg]

theorem S6_le_out (g : Fin 6 → Fn) :
    S g 6 ≤ Submodule.span (ZMod 2) (Set.range (fun j : Fin 16 => outGensF g j)) :=
  S_le g 6 _ (subset_span ⟨⟨0, by omega⟩, by simp [outGensF]⟩)
    (fun k => subset_span ⟨⟨k.val + 1, by omega⟩, by
      simp [outGensF, show k.val + 1 < 9 by omega, xN, k.isLt]⟩)
    (fun i _ => subset_span ⟨⟨i.val + 9, by omega⟩, by
      simp [outGensF, show ¬ i.val + 9 < 9 by omega, gN_val]⟩)

theorem out_ok (g : Fin 6 → Fn) (hc : Computes g) (i j : Fin 2) :
    ∃ o, comb o (outGens (GT g)) = C (2 * i.val + j.val) := by
  obtain ⟨o, ho⟩ := exists_combF (S6_le_out g (hc i j))
  refine ⟨o, ?_⟩
  have := congrArg tt ho
  rw [tt_c, tt_combF] at this
  simp only [tt_outGensF] at this
  exact this.symm

theorem wit_ok (g : Fin 6 → Fn) (h : Nat)
    (hH : ∀ j : Fin 6, j.val ≠ 0 → j.val ≠ h → g j ∈ U g j) (i : Fin 6) :
    ∃ w, WitOK (GT g) 0 h i.val w := by
  by_cases hi : i.val = 0 ∨ i.val = h
  · exact ⟨0, by rcases hi with hi | hi <;> simp [WitOK, hi]⟩
  push Not at hi
  have hW := U_le_W g h i.val (fun j _ h0 hh => hH j h0 hh) (hH i hi.1 hi.2)
  obtain ⟨w, hw⟩ := exists_combF hW
  refine ⟨w, Or.inr (Or.inr ?_)⟩
  have := congrArg tt hw
  rw [tt_combF] at this
  simp only [tt_witGensF] at this
  rw [GT_eq, gN_val]; exact this

theorem reps_ok : ∀ r ∈ reps, BitVec.ofNat 16 r.1 &&& 255#16 ≠ 0 ∧ BitVec.ofNat 16 r.2 &&& 255#16 ≠ 0 ∧
    BitVec.ofNat 16 r.1 &&& 255#16 ≠ BitVec.ofNat 16 r.2 &&& 255#16 := by decide

/-- The lower bound, assuming the cube propositions. -/
theorem lower_of_cubes
    (hcubes : ∀ r ∈ reps, ∀ h, 1 ≤ h → h ≤ 5 → Cube (BitVec.ofNat 16 r.1) (BitVec.ofNat 16 r.2) 0 h) :
    ¬ HasCircuit 6 := by
  rintro ⟨g0, hg0, hc0⟩
  obtain ⟨g1, hg1, hc1, rp, hrp, h10⟩ := orbit_step g0 hg0 hc0
  obtain ⟨g, -, hc, h0, hnf⟩ := normalize_upto g1 hg1 hc1 6 le_rfl
  rw [h10] at h0
  obtain ⟨c1, c2, c3⟩ := reps_ok rp hrp
  obtain ⟨h, h1, h5, hH⟩ := helper_set g hc _ _ c1 c2 c3 h0
  have cube := hcubes rp hrp h h1 h5
  obtain ⟨l1, r1, k1⟩ := gate_ok g 1 (by decide) (by decide) (hnf 1 (by decide) (by decide))
  obtain ⟨l2, r2, k2⟩ := gate_ok g 2 (by decide) (by decide) (hnf 2 (by decide) (by decide))
  obtain ⟨l3, r3, k3⟩ := gate_ok g 3 (by decide) (by decide) (hnf 3 (by decide) (by decide))
  obtain ⟨l4, r4, k4⟩ := gate_ok g 4 (by decide) (by decide) (hnf 4 (by decide) (by decide))
  obtain ⟨l5, r5, k5⟩ := gate_ok g 5 (by decide) (by decide) (hnf 5 (by decide) (by decide))
  obtain ⟨o0, ho0⟩ := out_ok g hc 0 0
  obtain ⟨o1, ho1⟩ := out_ok g hc 0 1
  obtain ⟨o2, ho2⟩ := out_ok g hc 1 0
  obtain ⟨o3, ho3⟩ := out_ok g hc 1 1
  obtain ⟨w0, hw0⟩ := wit_ok g h hH 0
  obtain ⟨w1, hw1⟩ := wit_ok g h hH 1
  obtain ⟨w2, hw2⟩ := wit_ok g h hH 2
  obtain ⟨w3, hw3⟩ := wit_ok g h hH 3
  obtain ⟨w4, hw4⟩ := wit_ok g h hH 4
  obtain ⟨w5, hw5⟩ := wit_ok g h hH 5
  refine cube (tt (g 0)) (tt (g 1)) (tt (g 2)) (tt (g 3)) (tt (g 4)) (tt (g 5))
    l1 r1 l2 r2 l3 r3 l4 r4 l5 r5 o0 o1 o2 o3 w0 w1 w2 w3 w4 w5
    ⟨?_, k1, k2, k3, k4, k5, ho0, ho1, ho2, ho3, hw0, hw1, hw2, hw3, hw4, hw5⟩
  rw [h0, tt_mul, lin_eq_comb _ (GT g), lin_eq_comb _ (GT g)]
  rfl

end MC222
