# x5 notebook: crossing exponent ρ_× and the five-point set M5

24 Nov 2026. Tags: [R] proved here, [N] computed, [C] conjecture. Code in `code/`.

## Status (early checkpoint)

**Task 1, exact Prop. B.2: done and calibrated.** [N]
- `code/crossing.py` builds the paper's matrix M(X) (App. B.3) and computes Ψ = det M exactly, using integer Bareiss
  determinants at X = 0..Θ and exact Newton interpolation.
- It checks deg Ψ ≤ Θ by an extra evaluation, and Ψ(1) = ε·[matching] with ε = +1. It then computes the three flattening ranks
  of every Ψ_N (over ℚ: the maximum of the ranks mod two large primes).
- All assertions pass for (n,e) = (1,4),(1,6),(1,8),(1,10),(2,12) on both wires, and for the unequal case (1,12)×(1,4).
  Output: `b2_ranks.out`.
- **Calibration**: 1/√2 is reproduced from exact counts (`code/calib.py`, `calib.out`). Symbols of energy 2n are partitions
  of n, so P(E) = Σ_{n≤E/2} p(n). ρ_count(E) := max_N [ln P(N) + ln P(4E−N)]/(4 ln P(E)) is 0.801, 0.754, 0.742, 0.731, 0.725,
  0.720, 0.717 at E = 20, 100, 200, 500, 1000, 2000, 4000, and the excess decays like E^{−1/2}. So the limit is 1/√2 = 0.7071.

**Idea 1 back-of-envelope: the ideas file has the direction backwards.** [R]
1/√2 is rigid for every Fock-type identity, whatever the dispersion. The reason is flattening, not a group action.

## Hypothesis
- ρ_× = 1/√2 is forced inside the "energy-graded" framework (§2).
- A construction that beats it has to break "degree = total energy" (β < 2 below). A new spectrum cannot do it.
- For M5, compositions of crossing identities cannot refute anything that satisfies B.3 (§3), so a genuinely new identity
  is needed.
