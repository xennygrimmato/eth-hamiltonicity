import MC222.Circuit

/-! # Upper bound: Strassen's algorithm (Proposition 2.2 of the paper) -/

namespace MC222

/-- Strassen's seven products, in the order m1..m7. -/
def strassen : Fin 7 → Fn :=
  ![(x 0 + x 3) * (x 4 + x 7), (x 2 + x 3) * x 4, x 0 * (x 5 + x 7), x 3 * (x 4 + x 6),
    (x 0 + x 1) * x 7, (x 0 + x 2) * (x 4 + x 5), (x 1 + x 3) * (x 6 + x 7)]

theorem strassen_isCircuit : IsCircuit strassen := by
  intro i
  fin_cases i <;> simp only [strassen] <;> refine ⟨_, ?_, _, ?_, rfl⟩ <;>
    first
    | exact x_mem_S _ _ _
    | exact Submodule.add_mem _ (x_mem_S _ _ _) (x_mem_S _ _ _)

lemma sm (i : Fin 7) : strassen i ∈ S strassen 7 := g_mem_S _ i i.isLt

theorem strassen_computes : Computes strassen := by
  intro i j
  fin_cases i <;> fin_cases j
  · have : c 0 0 = strassen 0 + strassen 3 + strassen 4 + strassen 6 := by
      funext p; simp [c, a, b, x, strassen]; ring_nf; reduce_mod_char
    exact this ▸ add_mem (add_mem (add_mem (sm 0) (sm 3)) (sm 4)) (sm 6)
  · have : c 0 1 = strassen 2 + strassen 4 := by
      funext p; simp [c, a, b, x, strassen]; ring_nf; reduce_mod_char
    exact this ▸ add_mem (sm 2) (sm 4)
  · have : c 1 0 = strassen 1 + strassen 3 := by
      funext p; simp [c, a, b, x, strassen]; ring_nf; reduce_mod_char
    exact this ▸ add_mem (sm 1) (sm 3)
  · have : c 1 1 = strassen 0 + strassen 1 + strassen 2 + strassen 5 := by
      funext p; simp [c, a, b, x, strassen]; ring_nf; reduce_mod_char
    exact this ▸ add_mem (add_mem (add_mem (sm 0) (sm 1)) (sm 2)) (sm 5)

/-- Upper bound: Strassen's algorithm is a 7-gate circuit. -/
theorem hasCircuit_seven : HasCircuit 7 := ⟨strassen, strassen_isCircuit, strassen_computes⟩

end MC222
