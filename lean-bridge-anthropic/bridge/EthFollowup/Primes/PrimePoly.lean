/-
# Polynomial-time construction of the prime-parity description (Executor P, step P2)

PolyT of the pieces of `primeDescL` (`PrimeDesc.lean`): `prodKR_polyT`, `prodOf_polyT`,
`chainOfIdx_polyT`, `levOf_polyT`, `primeL_unary` (`L = (Nat.bits n).length` in unary),
`primeDescL_D_polyT` (the `Desc` part), `primeDescL_lev_polyT`, `primeDescL_levC_polyT`.

Standard axioms only.
-/
import EthFollowup.ModP.ArithReaderPoly
import EthFollowup.Primes.PrimeDesc

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes

open Groundwork EthFollowup.ModP

variable {α : Type} [Enc α]

theorem prodKR_polyT {k r : α → ℕ} (hk : PolyT k) (hr : PolyT r) :
    PolyT fun x => prodKR (k x) (r x) := by
  unfold prodKR
  fun_prop

theorem prodOf_polyT {p : α → ℕ} (hp : PolyT p) : PolyT fun x => prodOf (p x) := by
  unfold prodOf
  exact prodKR_polyT (by fun_prop) (by fun_prop)

theorem chainOfIdx_polyT {j : α → ℕ} (hj : PolyT j) : PolyT fun x => chainOfIdx (j x) := by
  unfold chainOfIdx
  fun_prop

theorem levOf_polyT {v : α → ℕ} (hv : PolyT v) : PolyT fun x => levOf (v x) := by
  unfold levOf
  fun_prop

theorem primeL_unary {n : α → ℕ} (hn : PolyT n) : Unary fun x => primeL (n x) := by
  unfold primeL
  exact Unary.of_length (PolyT.bits hn)

theorem primeDescL_D_polyT {b l0 L A B : α → ℕ} (hb : Unary b) (hl0 : Unary l0) (hL : Unary L)
    (hA : PolyT A) (hB : PolyT B) : PolyT fun x => (primeDescL (b x) (l0 x) (L x) (A x) (B x)).D := by
  have hsnd : PolyT fun q : α × ℕ => q.2 := PolyT.snd PolyT.id'
  have hP : PolyT fun x => (List.range (4 * L x + 2)).map prodOf :=
    PolyT.map (f := fun _ p => prodOf p) (prodOf_polyT hsnd)
      (PolyT.range (Unary.add (Unary.mul (Unary.const 4) hL) (Unary.const 2)))
  have hC : PolyT fun x => (List.range (2 * L x + 1)).map chainOfIdx :=
    PolyT.map (f := fun _ j => chainOfIdx j) (chainOfIdx_polyT hsnd)
      (PolyT.range (Unary.add (Unary.mul (Unary.const 2) hL) (Unary.const 1)))
  have hTA := toLimbs_polyT hb hl0 (PolyT.max' hA (PolyT.const 1))
  have hTB := toLimbs_polyT hb hl0 hB
  have hLp := hL.poly
  show PolyT fun x => Desc.mk (3 * L x + 3) [] ((List.range (4 * L x + 2)).map prodOf)
    ((List.range (2 * L x + 1)).map chainOfIdx)
    [⟨0, .const (toLimbs (b x) (l0 x) (max (A x) 1)), .ge⟩, ⟨0, .const (toLimbs (b x) (l0 x) (B x)), .le⟩,
      ⟨1, .var 2, .lt⟩]
  fun_prop

theorem primeDescL_lev_polyT {L : α → ℕ} (hL : Unary L) :
    PolyT fun x => (List.range (3 * L x + 3)).map levOf :=
  PolyT.map (f := fun _ v => levOf v) (levOf_polyT (PolyT.snd PolyT.id'))
    (PolyT.range (Unary.add (Unary.mul (Unary.const 3) hL) (Unary.const 3)))

theorem primeDescL_levC_polyT {L : α → ℕ} (hL : Unary L) :
    PolyT fun x => (List.range (2 * L x + 1)).map fun j => (j - 1) / 2 :=
  PolyT.map (f := fun _ j => (j - 1) / 2) (by fun_prop)
    (PolyT.range (Unary.add (Unary.mul (Unary.const 2) hL) (Unary.const 1)))

end EthFollowup.Primes
