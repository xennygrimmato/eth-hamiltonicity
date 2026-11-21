# Referee report: p4 Theorem 7.1 (Selberg Λ_R² certificate plus bisection)

**Verdict: CORRECT WITH FIXES.** All fixes are minor. The finding theorem holds conditionally on the engine counting theorem.

## Corrected statement
Fix ρ ∈ (0,1). Take A ≥ (1+ρ²)/(2ρ) + C₀/(ρ² log u), and integer weights L(e) = round(C·log(R/e)) with C ≥ log² R.
Then O(A²ρ⁻¹R² log² u) exact counts Q_k with k ≤ A/ρ, one factorisation, and a μ-sieve to R = u^ρ deterministically
give a prime in (u, 2u^A].
- Correctness never depends on analysis. F(J₀) is computed exactly, and if F(J₀) ≤ 0 one raises A.
- Each Q_k is one engine count at 2^{O(n/√log n)}, where n = A·log₂u. Computing (mt)^k by square-and-multiply has
  geometric sizes, so the cut is O(n) for every k ≤ n. The notebook's "one k-fold product" picture is too
  pessimistic; even the tree bound n·log k would only add a log(1/ρ) factor.
- Total time is u^{2ρ + O(1/(ρ√log log u))}. With ρ = (log log u)^{-1/4} this is u^{O((log log u)^{-1/4})}.
  So a prime with ≥ k digits is found in 10^{O(k/(log k)^{1/4})} = 10^{o(k)}. No RH is used.

## Checks
1. **Pointwise.** For R < p ≤ u, Λ_R(p^j) = L(1) exactly, because only e = 1 divides. Also w ≥ 0, since every term is a square times a positive ceiling.
   - If P⁺(n) ≤ u then w(n) ≥ L₁²·Σ a_p⌈log₂p⌉ ≥ L₁²·log₂n, so F(n) ≤ 0.
   - Prime powers p^j > R with p ≤ R, and composite d, only add nonnegative mass.
   - Brute force: 69,994 values of n at (u,ρ) = (30,.5), (100,.4), (60,.7), (200,.3). Of these, 53,164 have F > 0, with 0 violations.
   - The additivity check (code F(J) = Σ pointwise) matched exactly on 18 random intervals.
2. **Exactness.** The expansion Λ_R² = Σ_m b(m)[m|d], the dyadic ⌈log₂d⌉ blocks, the k ≥ 2 terms and the closed form for Σ⌊log₂n⌋ are all correct.
   - The bisection is fine. Flo is never updated, but only the sign of the left half is used.
3. **Positivity.** Graham (JNT 10, 1978) gives Σ_{n≤N}Λ_z(n)² = N log z + O(N), uniformly for z ≤ N. Partial summation then gives the threshold (1+ρ²)/(2ρ), which is right. The error terms, in bits per n, are:
   - O(1/ρ²) from Graham's error;
   - O(1/ρ) from the ceilings;
   - O(log log R) from the small primes;
   - O(u log u/(xρ)) from the floors.

   All of these are o(log u) when ρ²·log u → ∞. With fixed C, the rounding δ_e adds about log³R/C² against C²·log R, which forces C ≫ log R (fix above). An explicit version is feasible because Graham's proof is elementary, but it is not needed.
4. **Engine.** The cost is as stated in item 2 of the corrected statement. It survives ρ → 0. It is conditional on the engine theorem; this report did not re-verify it.
5. **Classical.** Σ_{d≤u, m|d}⌊x/d^k⌋ with x = u^A ≫ u³: the curvature X/t³ is ≫ 1, so convex-hull and lattice methods do not apply. No o(u) method is known [C]. Not a classical result.
6. **Trivial alternative.** None found.
   - Factoring n²+1 for n ≤ N (Merikoski, P⁺ ≥ N^{1.279}) costs u^{0.78}.
   - Parity of π cannot locate a prime (TCH, p1–p3).
   - Direct roughness counts are ∀-counts and need the iterated product.
7. **Prior art.** Polymath4 states the weak conjecture verbatim: "a prime of ≥ k digits in exp(o(k)) time". It is open; the record is about 10^{k/2}, even with a factoring oracle.
   - polymathprojects.org/2009/07/27/proposal-deterministic-way-to-find-primes/
   - arXiv 1009.3956
   - No counting-oracle or 2025–26 solution was found (weak negative).
8. **Runs (u,ρ,A).** All p are prime and > u, and the smooth part is < n in every run.

   | u | ρ | A | F/(xL₁²) | asymptotic prediction | p |
   |---|---|---|---|---|---|
   | 3000 | .45 | 1.6 | 4.06 | 3.05 | 365933 |
   | 3·10⁴ | .3 | 2.2 | 8.52 | 5.70 | 14987347 |
   | 5·10⁴ | .35 | 1.75 | 4.33 | 2.29 | 5765003 |
   | 2·10⁵ | .25 | 2.4 | 9.21 | 4.84 | 7807739117 |

## Issues by severity
- **Moderate.** The headline is entirely conditional on the engine counting theorem. The "10^{o(k)}" claim should be stated with that condition and with the explicit rate.
- **Minor.** C must grow (C ≥ log² R).
- **Minor.** The threshold needs the margin C₀/(ρ² log u) and u ≥ u₀(ρ, A).
- **Minor.** The query count is O(A²ρ⁻¹R² log² u).
- **Minor.** Describe Q_k as using square-and-multiply, cut O(n).
