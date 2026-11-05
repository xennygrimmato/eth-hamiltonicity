/-
# The ArithNet description constant of the Horner description (roots-plan.md, H3; bridge)

`cA_hornerDesc : cA (hornerDesc b ℓ n d m a lo π) = 64 * (5 * d + 2) * (d + 1)` (`d ≥ 1`), from the pure
shape lemma `hornerDesc_cA_eq`. Standard axioms only.
-/
import EthFollowup.ModP.ArithNetCount
import EthFollowup.ModP.HornerDesc

namespace EthFollowup.ModP

theorem cA_hornerDesc {b ℓ n d m : ℕ} {a : List ℕ} {lo : ℕ} {π : List Bool} (hd : 1 ≤ d) :
    cA (hornerDesc b ℓ n d m a lo π) = 64 * (5 * d + 2) * (d + 1) := by
  unfold cA
  rw [← hornerDesc_cA_eq (b := b) (ℓ := ℓ) (n := n) (m := m) (a := a) (lo := lo) (π := π) hd]

end EthFollowup.ModP
