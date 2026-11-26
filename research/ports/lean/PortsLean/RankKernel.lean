import Mathlib

/-!
# Rank kernel and the spectral inequality (`research/ports/middle/notes.md` §4)

(a) `card_ker_mul_two_pow_rank`: for `c : Matrix (Fin m) (Fin n) (ZMod 2)`,
    `#{x | c x = 0} · 2^{rank c} = 2^n`.
(b) `rankKernel_psd`: `Σ_{i,j} w_i w_j 2^{-rank(a_i - a_j)} ≥ 0`, and the `k`-th power version
    `rankKernel_pow_psd`; both through an explicit feature map (`rankKernel_eq_feature`).
(c) `spectral_ineq`: abstract form of Proposition S, and `propS_rank` / `propS_rank_pow`, the
    statement for rank placements.

Normalisation (as in the notes): `E_pairs w = n⁻² Σ_{u,v} w(u,v)` (ordered pairs, `u = v` included),
`E_edges w = n⁻¹ Σ_{u,v} A_{uv} w(u,v)` with `A` the normalised adjacency matrix.
-/

namespace PortsLean.RankKernel

open Finset Matrix

/-! ## (a) Kernel cardinality -/

theorem card_ker_mul_two_pow_rank {m n : ℕ} (c : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (univ.filter (fun x : Fin n → ZMod 2 => c.mulVec x = 0)).card * 2 ^ c.rank = 2 ^ n := by
  classical
  have hrn := LinearMap.finrank_range_add_finrank_ker c.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  have hcard : (univ.filter (fun x : Fin n → ZMod 2 => c.mulVec x = 0)).card
      = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker c.mulVecLin) := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker c.mulVecLin)
    rw [ZMod.card] at h1
    rw [← h1, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp [LinearMap.mem_ker]))
  rw [hcard, ← pow_add, Matrix.rank, add_comm, hrn]

end PortsLean.RankKernel
