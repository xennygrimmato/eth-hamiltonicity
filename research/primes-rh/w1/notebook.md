# w1 notebook: wild ideas for a deterministic prime in [x,2x] faster than sqrt(x)

Explorer w1 works apart from the parity-bisection framing. Subtask 9 (P4 wild ideas).
Engine model used here is the one in research/prime-finding.md §2. Cheap means: a count of tuples of O(n)-bit integers
that satisfy O(1) multiplications, comparisons, divisibility checks and congruences, with total cut O(n)
(k-fold products have cut n log k, so k ≤ 2^{o(√log n)}). Arbitrary poly-time predicates are allowed on node-size
integers (≤ n^{4/5} bits). Signed integer weights are allowed only on node-size variables. The cost is
2^{O(U/√log n)} = x^{o(1)} iff U = o(n√log n).
Scripts are in this folder. All numbers below come from real primes (sympy/numpy).

Summary table (details below)

| # | idea | verdict |
|---|------|---------|
| I1 | **certifying-weight bisection** (one-sided sieve weights instead of exact or mod-M counts) | best idea. Proved reduction; measured threshold u0≈5.5; still hits the iterated-product barrier, from a new side |
| I2 | prime factors in [x,2x] of integers in a short interval near Y=x^k (Gowers strategy 3) | dead: the Dirichlet-polynomial error is √Y ≥ √x, even under RH and Lindelöf |
| I3 | factor Φ_m(t), t^k+1 for tiny t (Tao strategy 7 / cyclotomic) | works heuristically (≈10–200 tries); no proof route; RH does not help |
| I4 | Pocklington/Proth/Lucas certificates searched by the engine | dead: an exponentiation chain has cut n² |
| I5 | Bezout: gcd(m,Q)=1 is an exact cheap weight | [R] small tool: exact z-roughness for z ≈ Kn only; feeds I1 |
| I6 | RH-derandomised "almost all short intervals" with residue scans | dead: deterministic sampling needs about x/M² windows |
| I7 | Gaussian/Eisenstein primes in small boxes or sectors | dead: square-root barrier in every shape, and it needs Hecke-GRH, not RH |
| I8 | Maurer/Pocklington recursion: primes 2kq+1 with q a known prime | dead: needs Linnik for modulus ≈ x^θ, so the AP length is ≥ √x |
| I9 | sparse prime-rich sets (a²+b⁴, x³+2y³) as engine sets | dead: same zero-residue problem; the sets are not small enough |
| I10 | PRG / hitting sets, pseudodeterministic constructions | known prior art (CLORS 2023, pseudodeterministic and i.o.); RH gives nothing here |

---------------------------------------------------------------------------------------------------------------------

## I1. Certifying-weight bisection  (scripts i1_minorant.py, i5_bezout_rough.py, i1b_threshold.py)

**Idea.** The parity route needs a set with an odd count, and mod-M needs a nonzero residue. A third route needs only
a *sign*. Call an integer weight w on [x,2x] *certifying* if
 (a) w(m) ≤ 0 for every composite m, and w(p) = 1 for primes p (or ≥ 1; enough: w(m) > 0 ⇒ m prime),
 (b) Σ_{m∈I} w(m) is cheap (x^{o(1)}) for every interval I,
 (c) Σ_{m∈[x,2x]} w(m) > 0.

**Lemma 1 [R].** With a certifying w, a prime in [x,2x] is found with n+O(1) engine calls.
Proof: Σ is additive. If Σ_I w > 0, one half J has Σ_J w > 0. Recurse down to a single m with w(m) > 0. By (a), m is prime. ∎
This is like a lower-bound sieve, but the sieve sum is computed exactly, so remainder terms never appear. Only the
sign of the main term matters, and only on the top interval. No averaging is needed after the top level, because
the recursion always keeps a positive half. The even-total obstruction does not arise.

**Building blocks (all [R], elementary).** Let s_z(m) = #{d | m : z ≤ d ≤ √m}. This is cheap: one divisor witness
plus comparisons. Let R_z(m) = [m has no prime factor < z].
 * w = R_z·(1 − s_z) is certifying whenever R_z is a cheap exact weight. For a composite z-rough m, the least prime
   factor lies in [z, √m], so s ≥ 1. For a prime, s = 0.
 * More generally, w = ρ⁻ − ρ⁺·s_z with ρ⁻ ≤ R_z ≤ ρ⁺ and ρ⁺ ≥ 0 is certifying. On non-rough composites both terms
   are ≤ 0. On rough composites w ≤ 1 − 1.
 * w = 1 − Σ_{d|m, 1<d≤√m} v(d) with v ≥ 1_P and v ≥ 0 is certifying, but its total is very negative
   (Σ v(d)/d ≥ log log x).
 * Brun with exact prime recognition: Bon_k(m) = Σ_{i<k} (−1)^i C(ω_{≤√m}(m), i) with k even is certifying. It equals
   1_P(m) **exactly** when ω(m) < k. Its total is π − Σ_comp C(ω'−1, k−1) ≥ π − |I|(log log x)^{k−1}/(k−1)!, so it is
   positive for k ≈ e² log n.

**Tests (real data).**
 * w = 1 − s_2 on [10^6, 2·10^6]: Σ = −5,678,361 against π = 70,435.
 * Cheap Bonferroni variants ((1−ω_z) − s, with or without a Bonferroni-2 ρ⁺) at z = 10…1000: all hugely negative.
 * Exact R_z·(1−s_z) (i1b_threshold.py, x = 10^12, window of 10^5, π = 3614), as a function of u = log x/log z:
   u = 3 gives Σ = 3614 = π exactly; u = 4 gives 2574; u = 5 gives 505; u = 6 gives −2709; u = 8 gives −10297.
   Using exact prime-divisor counts (ω' in place of s) shifts the threshold only slightly (u = 5 gives 942; u = 6 gives −1002).
   **Critical roughness u0 ≈ 5.5:** a cheap exact (or one-sided) x^{1/5.5}-roughness weight would finish the job.
 * Bezout roughness (I5) at x = 10^9: z = 100, where P(z) has 4n bits, gives Σ = 4515 > 0 (π = 9604 in the window). So
   **for x ≈ 10^9 the fully cheap weight R_z(1−s_z), with R_z by Bezout and witness 4n bits, is certifying with positive
   total.** This is a genuine x^{o(1)}-query prime finder in that range. Asymptotically it fails, because z = Kn
   gives u = n/log(Kn) → ∞.

**Where it dies (the barrier, from a new side).** Cheap roughness exists only to level z = O(Kn) (Bezout) or to
node size z = 2^{n^{4/5}} (exact primality inside a node; then u = n^{1/5} → ∞). Getting to u = O(1) needs exact
recognition of primes up to x^{1/5} inside the sieve, which means recursion. If children are ≤ parent^{1/u}, the
recursion depth is log(n^{1/5})/log u. Each level can carry n bits in the worst case (the children's product divides
the parent), so U = Θ(n log n/log u). Exact 0/1 inner levels need u ≤ 3 (so that s ∈ {0,1}), which gives U = Θ(n log n).
That is again the iterated-product barrier of prime-finding.md §4 (need U = o(n√log n)).
New information:
 (i) only one-sided correctness is needed;
 (ii) the top level needs only u ≤ 5.5;
 (iii) with exact prime recognition, the Brun weight equals 1_P outside {ω(m) ≥ k}, with k ≈ 8 log n. All the
       difficulty sits in numbers with ≥ 8 log n prime factors (density n^{-8}) and in the depth of the recursion.
**Relation to the board.** I1 is consistent with the robustness barriers (p1 Thm 2, p2, p3, w2 Prop G). The
weight is an *exact* engine count, not a residue or distribution query, so it is the kind of non-robust information
those barriers demand. w2 landed #9 (LP: polynomial weights in divisor-range counts need degree ≈ 0.65 log x) is the
no-sieve case of I1. The difference is the exact roughness factor R_z: with it, degree 1 in s suffices once u ≤ 5.5,
so the whole difficulty moves into R_z. That agrees with p3 #11 (fold ≥ Ω_max).
**Open sub-question:** is there a cheap *one-sided* majorant ψ ∈ {0,1} of 1_P on [x^{1/5.5}… x^{1/2}] whose Brun
sum stays positive? A {0,1}-valued majorant keeps Bonferroni sign-safe, while integer majorants do not. With such a
ψ, the depth problem disappears. I found none.

## I2. Prime factors in [x,2x] of integers near Y = x^k  (i2_shortint_factor.py)
Idea: the engine factors any O(n)-bit number, so scan [Y, Y+H] for an integer with a prime factor in [x,2x].
Empirically the density is about ln2/ln x and the max gap in 2·10^5-windows is 140–217 (x = 10^4…10^6), so it behaves
like the primes. Proof: the count is ∫ P(1+it)C(1+it)… with P = Σ_{p~x} p^{-s} and C = Σ_{c~Y/x} c^{-s}.
Mean values (or RH+Lindelöf pointwise) give an error of ≈ √Y ≥ √x. This is worse than plain primes; the Polymath
thread reached the same conclusion ("error terms cannot beat S^{1/2}").
Dyadic localisation of the factor is the killer. Verdict: dead.

## I3. Cyclotomic / polynomial values with tiny t  (i3_polyvalues.py)
Factor Φ_m(t) for t = 2, 3, … (O(n) bits, engine factoring) until a prime factor lands in [x,2x]. Real data: for
x = 10^6…10^12 the first success comes after about 10–200 values of t past the threshold t ≈ x^{1/φ(m)}. Examples:
Φ_13 at x = 10^10 succeeds at t = 7; Φ_7 at x = 10^12 succeeds at t = 193. That is polylog heuristically.
A proof would need the roots of Φ_m mod p, for p ∈ [x,2x], to hit a box [0,T] with T ≈ x^{1/d}·polylog. That is
equidistribution of roots at discrepancy x^{-1+1/d}. Only quadratic root equidistribution is known (Duke–Friedlander–
Iwaniec, Tóth), with tiny power savings, and RH for ζ says nothing. Cyclotomic values cannot force large factors:
the order m is O(n), so the factors are only ≥ m. Verdict: heuristic only, dead.

## I4. Pocklington / Proth / Lucas certificates as engine witnesses
A certificate needs a^{(N−1)/q} mod N, which is a chain of n squarings of n-bit numbers. That is a path network with
n-bit edges, so U = n², and any dynamic program carries n bits of state. Small-exponent variants (b^r ≡ 1 with r small)
force only p ≡ 1 mod r, with no size control. Cheap exponents are r ≤ 2^{o(√log n)}. Verdict: dead; the obstruction
is structural, not quantitative.

## I5. Exact coprimality via Bezout [R]
gcd(m, Q) = 1 ⇔ there is a unique u ∈ (0,Q) with u·m ≡ 1 (mod Q). That is one multiplication and a witness of log Q bits,
so [gcd(m,Q)=1] is an **exact** cheap weight for any fixed Q of O(n) bits. Consequences:
 * exact z-roughness for z ≈ K·n·ln 2 (Q = P(z)), any K = o(√log n);
 * a cheap g(m) = #{a ≤ √m : gcd(a,m) > 1} that is 0 on primes and ≥ 1 on composites (useless: the excess is ≈ √m).
At x = 10^9 this gives a certifying weight with positive total (I1). Asymptotically it is too weak.

## I6. RH almost-all short intervals plus mod-M scans  (i6_sampling.py)
Under RH, Selberg's mean square gives |π(I_y) − li(I_y)| < M/4 for all but a fraction 16h log²x/M² of y, with
h ≈ M log x. So a single window [y, y+h] with nonzero residue mod M exists for most y.
Deterministic derandomisation: each bad y comes with bad measure ≥ M/16, so the number of bad clusters is
≤ x log³x/M², and a disjoint scan needs about x/M² windows. That is x^{1−o(1)}.
Equivalently, a sparse sample must resolve all ≈ x/h zeros. Real primes (x = 10^9, 2·10^7 range): for M = 16, 0.1% of
windows are bad and the longest bad run is 1; for M = 32, no window is bad. True, but not provable. Verdict: dead.

## I7. Gaussian / Eisenstein primes in boxes and sectors  (i78_quick.py)
Real data: boxes of side 7–9 (49–81 lattice points) already contain a Gaussian prime at norms 10^8–10^12. Proof:
Hecke-GRH gives an error ≈ √x for any region at norm x, so the region needs ≥ √x lattice points. It needs GRH for
Hecke L-functions, which the claimed RH (ζ only) does not give. Verdict: dead (square-root barrier is shape-independent).

## I8. Maurer / Pocklington recursion via APs 2kq+1  (i78_quick.py)
Real data: for q ≈ x^θ (θ = 0.5, 0.7, 0.9) the least k is ≤ 55 even when the AP has only 16 terms. Proof: the least prime
in an AP mod q ≈ x^θ needs Linnik-type bounds. GRH gives q^{2+ε}, which forces k ≥ q, so the cost is ≥ √x. RH for ζ
does not give GRH for Dirichlet L-functions. Freedom in q does not help: the union of the candidate sets is again
subject to the √x error. Verdict: dead.

## I9. Sparse prime-rich sets as engine sets
{a²+b⁴} (Friedlander–Iwaniec) and {x³+2y³} (Heath-Brown) are cheap sets, so the engine gives π(A∩I) mod M. But these
sets contain x^{3/4} or x^{2/3} primes, so the residues can vanish. Exact counts need |A∩I| < M, and no theorem
covers such short pieces. Verdict: dead.

## I10. PRG / hitting sets
Impagliazzo–Wigderson-type hardness gives poly-size hitting sets for primes (Polymath4). Chen–Lu–Oliveira–Ren–Santhanam
(FOCS 2023) give a *pseudodeterministic* poly-time prime construction for infinitely many n. RH supplies no hardness,
and the engine supplies counting but no circuit lower bound. Verdict: nothing new.

## What I would do next
Attack the open sub-question of I1: a cheap {0,1}-valued (or one-sided-safe) recogniser of primes between x^{1/5.5}
and x^{1/2}, or a proof that every cheap certifying weight has a negative total for u → ∞ (a parity-problem analogue
for the engine class). The Brun weight's exactness outside {ω ≥ 8 log n} suggests a test: compute the depth/cut
trade-off U(u) = n log n/log u precisely and see whether children ≤ parent^{1/u} with *large* u can be made sign-safe
at inner levels.
