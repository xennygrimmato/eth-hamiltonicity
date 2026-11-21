# w2 notebook — "what certifies / forces a prime" angle

Engine model used (from research/prime-finding.md §2 and parity-note §2): exact counts of tuples of O(n)-bit
integers under O(1) multiplications/divisibilities/congruences/comparisons (n = log2 x), integer weights only
on node-sized integers (≤ x^{1/K^7} = x^{o(1)}); from it: π(S) mod M (M ≤ 2^{2^{o(√log n)}}) for cheap S,
least prime factor of any N ≤ x^{O(1)}, exact divisor-type sums. Cost 2^{O(U/√log n)} with U = cut;
k-fold products cost U ≈ n log k. Nodes must stay ≤ n/K^7 bits: the cost term 2^{2gP/K} (g = 3K^8 nodes,
P = max node load) forbids even one node of δn bits (parity-note, Imported Thm 2.2).

Scripts in this folder; all numbers below reproducible with `python3 <script>`.

---------------------------------------------------------------------------------------------------
## Idea 1 — Robustness barrier: parity/residue queries on ARBITRARY sets cannot beat the gap bound  [R]

Generalises parity-note Prop. (Adversary), which handles interval queries and a dense fake set S.

**Prop. G.** Let P ⊆ [x,2x] be any set (e.g. the true primes). Let an algorithm make q_p adaptive queries
"|S ∩ Q_j| mod 2" for arbitrary sets Q_j (intervals, progressions, polynomial families, bit-prefix sets,
weighted versions Σ_{u∈S} w_j(u) mod 2 — anything) and q_m membership queries, then output y. Then there is
S with |S Δ P| ≤ q_p + q_m + 1 that is consistent with the answer "even" to every parity query, "no" to every
membership query, and y ∉ S.
*Proof.* Unknown R ∈ GF(2)^U, S = P ⊕ R. Constraints: ⟨R,Q_j⟩ = ⟨P,Q_j⟩ (all parities of S even) and R_u = P_u
on the q_m+1 forced points (so S_u = 0). The system is consistent (R = P solves it, S = ∅), and a consistent
GF(2) system with r rows has a basic solution supported on ≤ r coordinates. ∎
**Mod M (prime power).** With answers "≡ 0 mod M": remove forced points from P, then repeatedly delete from
the multiset of query-vectors v_u ∈ (Z/M)^{q} (u ∈ P) a zero-sum subsequence; Olson's theorem
(Davenport constant D((Z/M)^q) = q(M−1)+1) leaves T with |T| ≤ q(M−1). S = P \ (T ∪ forced),
|S Δ P| ≤ q(M−1) + q_m + 1. (General M: D(G) ≤ exp(G)(1+log(|G|/exp(G))).)

**Meaning.** S differs from the real primes in ≤ q(M−1)+q_m+1 points, so it satisfies RH in the form
|π_S(y) − li(y)| ≤ √y log y/(8π) + q M, the BHP/RH gap bound up to merging ≤ qM gaps, Brun–Titchmarsh,
Bombieri–Vinogradov, pair-correlation statistics … with negligible change. Hence: **any proof that a
q-query residue strategy finds a prime must use a property of the primes that is destroyed by changing
qM points of [x,2x]**. Analytic consequences of RH are bounds with error ≍ √x log x; any form of them with
slack ≥ qM + q_m + 1 holds for S as well, so with qM ≤ c√x such inputs cannot certify the strategy. This is the "parity problem" for
prime finding, in a model that allows arbitrary query sets (not only intervals) and prime-like fakes.
Numerical sanity: `adversary_test.py` (20 random trials, mixed interval/AP/random queries, q ≤ 60, x ≤ 10^6:
|R| ≤ q+3, all queried parities of S even, max gap of S = max gap of P in every trial).
Verdict: clean theorem, negative. It says what a positive result must look like: an *exact* identity
(non-robust input), not an analytic estimate.

---------------------------------------------------------------------------------------------------
## Idea 2 — Prefix-parity hitting: find y with π((x,y]) odd, then bisect  [N],[C]

g(y) = π(y) mod 2 is a ±step function that flips at every prime; {y : g(y) ≠ g(x)} has density ≈ 1/2.
A deterministic hitting schedule for this set gives a prime in O(n) extra parity calls.
`parity_hitting.py` (2·10^5 random x ∈ [10^7,10^8], pi table to 2·10^8):
* schedule C, y_j = x + j⌊x/64⌋: P(first odd index ≥ k) = 0.499, 0.249, 0.123, 0.061, 0.031, 0.015, … — exactly
  geometric(1/2); max 17.
* schedule A, y_j = x + 2^j: exhaustive over 5·10^6 consecutive x near 10^7: max first-odd j = 24, and 2 values of
  x where all j ≤ 26 fail (expected under the random model: 5·10^6·2^{-21} ≈ 2).
* parities of consecutive dyadic blocks: P(odd) = 0.500±0.001, correlation |ρ| < 0.004 at block sizes 2^10..2^22.
Conjecture C2 ("parity pseudo-randomness"): for K = C log x, some y_j = x + j⌊x/K⌋ has π((x,y_j]) odd.
This gives x^{o(1)} deterministic prime finding. By Idea 1 it is unprovable from any robust input; it is a
parity-problem statement, *not* implied by RH and not easier than Cramér (which already gives polylog by
scanning). Verdict: heuristic positive, proof hopeless with current tools.

---------------------------------------------------------------------------------------------------
## Idea 3 — Factoring-oracle reduction: produce N ≤ x^C with a prime factor in [x,2x]  [N]

The engine factors any N ≤ x^{O(1)} in x^{o(1)}. So it suffices to produce, deterministically, a short list
N_1..N_K with one having a prime factor in [x,2x]. With N_i = Y+i: K(x,Y) = min_p (−Y mod p), p ∈ [x,2x] prime.
`factor_oracle.py`: Y = x², x²+x, x³, 2^{⌈3 log2 x⌉}, lcm(1..60): K between 3 and 93 for x ∈ [10^4,10^6]; worst
over 200 consecutive x: 73–183 ≈ 7–13 log x. So empirically K = O(log x) (heuristic: min of π(x) quasi-random
residues in [0,x)).
Provable side: K(x,Y) ≤ K ⇔ some prime p ∈ [x,2x] lies in ∪_m [Y/m, (Y+K)/m], a set of total measure ≈ K log 2.
Needs discrepancy of {Y/p} (p ∈ [x,2x]) below K/x, i.e. square-root cancellation in Σ_p e(hY/p) — at the
random-model limit, unattainable; RH explicit-formula error for this set is ≈ √Y ≥ √x. Special Y (x(x+t),
x²+c) just re-encode primes x+a in short intervals ((x+a)(x+t−a) = x(x+t)+a(t−a)). Verdict: dead
(provably ≥ √x), empirically polylog. Note: same √x wall as for short intervals, despite total "measure" K.

---------------------------------------------------------------------------------------------------
## Idea 4 — Exact prime-detecting functionals + bisection (the "monotone count" route)  [N]

Bisection needs only an exact *additive* functional f(I) = Σ_{n∈I} w(n) with w ≤ 0 on composites and
f([x,2x]) > 0: one half always keeps f > 0, a singleton with f > 0 is prime. (Monotone counts are the special
case w ≥ 0; then w must vanish on composites = an ∃-characterisation of primes with O(1) multiplications,
which needs Pratt/Pomerance certificates of Θ(n²) bits — out.) Engine-exact w: polynomials of degree D in
divisor-range counts c_i(n) = #{d | n : d ∈ J_i} (witness D divisors, cut O(Dn): allowed for D = O(1), and for
beating √x even D ≤ c√log n). Primes have c = 0, composites c ≠ 0.
`lp_weights.py`, `lp_degree.py`: LP maximising f([x,2x]) over all such w with w(0)=1, w ≤ 0 on every composite
feature vector (in-sample, so an UPPER bound for any weight of the family). 4 ranges with cuts x^{1/6},x^{1/4},x^{1/3}:
max f/π:
| x | D=2 | 3 | 4 | 5 | 6 | 7 | 8 | D* |
|---|---|---|---|---|---|---|---|---|
| 10^4 | −9.3 | −2.8 | −0.53 | +0.67 | | | | 5 |
| 10^5 | −21.7 | −7.4 | −3.2 | −1.1 | +0.09 | | | 6 |
| 10^6 | −34.7 | −12.6 | −6.7 | −2.9 | −1.2 | −0.20 | +0.68 | 8 |
(see lp_degree output for 3·10^6 and the 7-range family). The minimal degree D*(x) grows ≈ 1.5 per decade,
i.e. ~ 0.65 log x: no bounded-degree weight exists, matching the Vandermonde barrier of prime-finding.md §4
(isolating ω = 1 needs ≈ n/log n terms) — here observed for the much larger class of *non-sieve*, *divisor-range*
polynomial weights with w ≤ 0 allowed on composites (Bonferroni-type). Verdict: dead; quantitative evidence.

---------------------------------------------------------------------------------------------------
## Idea 5 — mod-M residues + Selberg variance under RH  [N] + heuristic analysis

Under RH (Selberg) Σ_{y∈[x,2x]} (π(y,y+h] − h/log y)² ≪ h x log² x. Take h ≈ (M/2) log x (mean count M/2):
π(y,y+h] ≡ 0 (mod M) forces deviation ≥ M/2, so #bad y ≪ x log³x / M: all but a fraction log³x/M of shifts give
a nonzero residue, and then bisection finds a prime. But the bad shifts may form one block of length x log³x/M
— no deterministic gain (and a random shift is anyway a trivial randomized algorithm). A local Selberg bound on
windows of length x^{1/2−δ} would be needed; RH gives nothing below √x (mean-value theorem for Σ_γ y^{iγ}
has no orthogonality on windows shorter than y/spacing ≈ y log y).
Numerics (`parity_hitting.py`, 2·10^5 random x ∈ [10^7,10^8], scan blocks of length h until count ≢ 0 mod M):
M=2,h=1: mean 15.8 blocks, max 172 (= prime gaps); M=6,h=20: max 9; M=30,h=200: always the first block;
M=210,h=2500: always the first block. Verdict: true primes behave perfectly; nothing provable beyond Idea 1.

---------------------------------------------------------------------------------------------------
## Idea 6 — Bootstrap recursion (prime p ≈ √x first, then Pocklington family kp+1)  [N]

Primality is already free (AKS / engine), so recursion only helps if it shrinks the *candidate set that provably
contains a prime*. With p ≈ √x: N = kp+1 ∈ [x,2x] needs k ∈ [√x, 2√x]; under GRH, π(2x;p,1) − π(x;p,1) =
li-main/(p−1) + O(√x log² x), so the guaranteed candidate set has ≈ x/p = √x elements — no gain; Linnik under
GRH (least prime ≡ 1 mod p ≪ (p log p)²) says the same. `bootstrap.py`: mean extra k over 300 consecutive
p ≈ √x is 17–36 ≈ log x, worst 115–206 (x = 10^8..10^16), so empirically polylog, provably √x. Recursion
T(x) = T(√x) + (search) cannot beat the search term. Verdict: dead.

---------------------------------------------------------------------------------------------------
## Idea 7 — Explicit sparse sets with proved primes  [K]+[N]

`sparse_sets.py`: sizes inside [x,2x]: Friedlander–Iwaniec a²+b⁴ ≈ x^{0.74} (→ x^{3/4}); Piatetski-Shapiro ⌊n^c⌋,
c < 243/205 (Rivat–Wu) ≈ x^{0.844}; n²+1 ≈ 0.41√x (conjectural only); BHP interval x^{0.525}; RH interval √x log x.
Gaussian sectors a²+b², b ≤ B have ≥ B√x members. Every set with a *proved* prime has ≥ x^{1/2} elements;
the GRH explicit formula for any such family has error ≳ √x independent of the set size ("square-root law").
With the engine the set size is irrelevant anyway (bisection is cheap) — the obstruction is parity (Idea 1),
and sparse sets do not change it. Verdict: dead for both scanning and engine routes.

---------------------------------------------------------------------------------------------------
## Idea 8 — Rough-by-construction exact counts (Linnik identity on z-rough factors)

log(ζ/ζ_z) = Σ_j (−1)^{j−1}(R−1)^j/j with R = Σ_{n z-rough} n^{−s}: for z = x^δ only j ≤ 1/δ factors occur, so
Σ_{p∈I, p≥z} 1 (+ prime-power corrections) = Σ_{j≤1/δ} (−1)^{j−1}/j · #{(r_1..r_j) z-rough, r_i>1, Πr_i ∈ I}:
O(1)-fold products — engine-cheap EXCEPT the predicate "r is z-rough" (∀ d<z: d∤r), which is Φ(J,z), the
Meissel–Lehmer quantity: needs μ over z-smooth squarefree d of size up to x (k-fold product) — same barrier.
Variants: S = {n : no factor < (2x)^{1/3}} has unique composite factorisations n = ab (a ≤ b, a prime
automatically), so π(S∩I) = |S∩I| − #{(a,b)} — again needs |S∩I| = Φ. Forcing roughness by congruences
(n ≡ 1 mod primorial) only reaches z ≈ log x. Verdict: dead; every "unique-witness" construction moves the
difficulty into an exact rough-number count.

---------------------------------------------------------------------------------------------------
## Idea 9 — Heath-Brown identity with μ inside big nodes

HB identity with k = 1/δ needs μ(m) for m ≤ x^δ, applied as node weights, and only 2k-fold products. If a node
of δn bits cost 2^{δn}, exact ψ(I) would follow in x^{O(δ)} — too good. The engine's cost term 2^{2gP/K}
(P = max node load, g = 3K^8) makes a δn-bit node cost 2^{6K^7 δ n}; with nodes ≤ n/K^7 one needs k ≥ K^7 =
n^{7/40}, i.e. cut n log k = Θ(n log n): 2^{Θ(n√log n)}. Outer loop over m ≤ x^δ instead: the coefficients
a_j(M) = (μ_{≤z})^{*j}(M) range over M ≤ x. Verdict: dead (precisely the iterated-product barrier).
