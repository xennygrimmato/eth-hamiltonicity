# p3 notebook: prime finding as a query problem (subtasks 3 and 5)

Scripts: `adversary.py` (builds and checks the adversary for any query matrix), `realparity.py` (block-parity statistics of real primes).

## 0. Verdict (written last)

* **[R] Theorem 1 (GF(2), any query sets).** You make k parity queries ⟨a_i, 1_S⟩ mod 2 with *arbitrary* a_i ⊂ [N,2N] (adaptive or not; intervals, APs, anything else). If the only things you know about S are "gaps ≤ G" and "prefix counts within E of li", then you need k ≥ min(G, E) − O(log N) queries. Under RH, G and E are both Θ(√N log N). The singleton-scan upper bound uses G queries, so the bound is tight up to constants. **o(√N) is impossible for intervals, for intervals × residue classes, and for every other family.**
* **[R] Theorem 2 (mod M).** For answers mod M the bound is k ≳ G / (4 M ln M log N). The condition on the adversary is 4·D·log N ≤ G with Davenport constant D ≤ M(1 + (k−1) ln M), which is linear in k. The intervals-only upper bound is G/M + log N. **The modulus threshold is M\* = N^{1/2 ± o(1)} under RH, for any query family.** Above it, O(log N) interval queries suffice. Below it, no family of queries helps by more than M·N^{o(1)}. This replaces the x^{0.525} threshold of prime-finding.md §4, which was stated for intervals and BHP, by a statement for every family under RH.
* **[R] Theorem 1′ (robust form, real primes).** For the true prime set P and any algorithm that outputs x after k GF(2) queries, exactly one of two things holds.
  1. The queries certify x algebraically: e_x lies in the GF(2)-span of the queried sets.
  2. There is a set S′ with |S′ Δ P| ≤ k + 2 that gives identical answers and has x ∉ S′. S′ can also be required to lie inside any allowed residue pattern (coprime to small primes).

  So a proved theorem can serve as the key lemma only if it is not (k+2)-robust. RH, Bombieri–Vinogradov, Maynard–Tao, Zhang, Brun–Titchmarsh, Selberg almost-all results and pair correlation are all robust at k = N^{1/2−c} (§3). **None of them can be the key lemma.**
* **[N] Real primes look nothing like the adversary.** Block parities for h ≥ 100 behave like fair coins: fraction odd 0.497–0.504, and the longest even run matches the coin-flip value log₂(#blocks). The deterministic doubling strategy (find the first j with π([y, y+2^j)) odd, then bisect) needs 4.7 queries on average, at most 18, over 5824 starts near 10^12. So the obstruction is about proof, not truth. Equidistribution of π(n) mod 2 is itself open (see §4).
* **Best idea.** [C] Under the "parity-randomness" Conjecture PR (§4), the engine gives deterministic prime finding in x^{o(1)}. Unconditionally, the query model is closed: the only way past √N is a non-robust exact computation with M ≥ N^{1/2−o(1)}. That is the iterated-product barrier of iterated-product.md, or LO-type analytic exact counts at cost √N.

## 1. Model

Unknown S ⊂ [N, 2N]. A query is a ∈ F₂^n (or Z_M^n) and returns ⟨a, 1_S⟩ mod 2 (or mod M). Known global information:

  𝒮(G, E) = { S : every window of length G meets S, and |S ∩ [N, y]| − (li y − li N)| ≤ E for all y }.

Under RH:
- G = (22/25)√N log N (Carneiro–Milinovich–Soundararajan 2019; Cramér gives O(√N log N)).
- E ≈ √N log N / (8π) (Schoenfeld 1976), doubled for windows.

The algorithm must output x ∈ S. Primality testing of a single x is the singleton query a = e_x, so it is included in the model. Everything the counting engine supports (Theorem B and B′ of prime-finding.md) is a query of this kind with M ≤ exp exp o(√log log x).

## 2. Lower bounds

**Lemma (pivots).** Let K ⊂ F₂^n be a subspace of codimension ≤ c. Put a basis of K in reduced echelon form, with pivot set Π, |Π| ≥ n − c. For every T ⊆ Π, the vector v_T = Σ_{j∈T} b_j satisfies v_T|_Π = 1_T. So on all but ≤ c coordinates, an element of K can follow any pattern prescribed in advance.

**Theorem 1.** Let the queries be H (k × n). The adversary answers 0 to everything; adaptivity does not matter because the transcript is fixed. Let K = ker H ∩ {v_x = 0}, which has codimension ≤ k + 1, and x is a non-pivot. Choose T to contain every ⌈log N⌉-th pivot, in increasing order (adjusted to follow li). Then S = supp v_T satisfies:
- S ⊥ every query, and x ∉ S;
- max gap ≤ log N + k + 1, because a zero run contains fewer than log N consecutive pivots plus at most k+1 non-pivots in total;
- prefix error ≤ k + 3.

So S ∈ 𝒮(G, E) whenever k ≤ min(G, E) − log N − 3, and the algorithm is wrong on S. ∎

Upper bound: scan G consecutive singletons, which takes G queries. So the query complexity is Θ(√N log N) under RH for every family A, with leading constants between about 1/(4π) and 22/25. `adversary.py` builds this kind of adversary (a block-greedy variant) for random sets, intervals and intervals × APs (q ≤ 50), and checks syndrome 0, v_x = 0, gaps and prefix error. The block-greedy version can fall short of the density target when k is close to the block length (seen at k=120 for intervals); the pivot version above does not have this problem.

**Theorem 1′ (robust).** Apply the lemma to the affine space {S : H1_S = H1_P, S_x = 0}. It is nonempty unless column x of H is outside the span of the other columns, which is equivalent to e_x ∈ rowspace(H), meaning the answers determine 1_P(x). Its direction space has codimension ≤ k + 1. Take the target pattern P \ {x} on the pivots. This gives |S′ Δ P| ≤ k + 2. Restricting the columns to an allowed set R (for example integers coprime to a primorial) keeps S′ ⊂ R. ∎

**Theorem 2 (mod M, adversary answers 0).** Columns h_i ∈ Z_M^k. The Davenport constant satisfies D = D(Z_M^k) ≤ M(1 + (k−1) ln M) (van Emde Boas–Kruyswijk / Meshulam; it equals k(M−1)+1 for M prime, by Olson).

Construction:
1. Cut [N, 2N] \ {x} into blocks of length ℓ = 2D⌈log N⌉.
2. In each block, greedily extract disjoint zero-sum subsets. Each has size ≤ D, and together they cover all but < D coordinates of the block.
3. Pick a sub-collection whose weight lies in [t, t + D], with t = (block target) − (running excess).

Result: prefix error ≤ 2D, max gap ≤ 2ℓ, and S ⊥ every query mod M. So the algorithm fails if 4D log N ≤ G and 2D ≤ E. With D ≈ kM ln M this gives k ≳ G / (4M ln M log N). Upper bound with intervals only: G/(M−1) exact block counts (a block of length < M has count < M, so its residue is its count), then log M bisection steps. ∎

**Threshold.** If M exceeds the largest count in a window of length G, one interval query is nonzero mod M, and bisection finds a prime in O(log N) queries. Theorem 2 says that for k = N^{o(1)} you need M ≥ G / N^{o(1)}. So M\* = N^{1/2 ± o(1)} for every family.

Answers to the questions in the brief: o(√N) is not possible for intervals, not for intervals × residue classes (any moduli, even q up to N), and not for arbitrary sets, with M = x^{o(1)}. An earlier structured adversary used translates of the support of lcm_{q≤Q}(z^q − 1) over F₂; it handled only q ≤ Q ≈ √G and is superseded by Theorem 1.

## 3. Could real primes look like the adversary? Which theorems are robust?

By Theorem 1′, S′ is P with ≤ k+2 edits, all inside an admissible residue pattern. A theorem T is (k+2)-robust if every such S′ still satisfies it. At k = N^{1/2−c}:

| Theorem | Why it is robust |
|---|---|
| RH counts | error √N log N ≫ k |
| Cramér / CMS gaps | edits can widen a gap by at most the run of non-pivots; the gap-controlled adversary of Thm 1 is used |
| Bombieri–Vinogradov | edits change Σ_{q≤Q} max_a by ≤ kQ = N^{1−c}/log^B ≪ N/log^A |
| Maynard–Tao / Zhang | "infinitely many n", or ≫ N/log^C such n in [N,2N]; k edits destroy at most k·|H| tuples |
| Brun–Titchmarsh | holds for S′ ⊂ R with spread edits; slack for small h |
| Selberg / Saffari–Vaughan almost-all short intervals | edits touch ≤ kh windows, a measure-zero proportion |
| Montgomery pair correlation (under RH) | concerns zeros, i.e. smoothed counts with error ≫ k |

The non-robust facts are exact ones: primality of specific integers (Wilson, AKS), Legendre / Meissel identities, the explicit formula with all zeros, and genus theory (h(−n) parity). Each of these is a query with large M, and its cost is the whole issue. A key lemma would have to be a precision-1 statement about the joint parities of π at N^{1/2−c} prescribed points. No such statement is known, and even the density of {n : π(n) even} being 1/2 is open (§4).

## 4. Real primes (realparity.py, N = 10^12, window 10^7; same picture at 10^9) [N]

| block h | frac odd | longest even run | coin-flip value |
|---|---|---|---|
| 8 | 0.243 | 43 | 20 (dominated by empty blocks) |
| 30 | 0.467 | 19 | 18.3 |
| 100 | 0.497 | 16 | 16.6 |
| 1000 | 0.503 | 13 | 13.3 |
| 10^4 | 0.504 | 9 | 10.0 |

Doubling strategy: P(first odd j = log₂log N + t) ≈ 2^{−t}, mean 4.7, max 18 over 5824 starts.

**Conjecture PR [C].** For every N, some j ≤ C (log log N)² has π([N, N + 2^j)) odd. A weaker version suffices: one of N^{o(1)} prescribed starting points y ∈ [N, 2N] works.

> **Erratum (r1, 21 Nov) [N].** PR as stated, with a single starting point and doubling, is FALSE.
> - Exhaustive search below 2^30 finds 124 values of N with π([N, N+2^j)) even for EVERY j ≤ log₂ N. Two examples: N = 1229830 and N = 1014257268; the lead re-checked both with sympy.
> - The Cramér model predicts about 121.5 such N, so these failures should never stop.
> - Replacement **PR\*** [C], with n = log₂ N: among n² disjoint blocks of length n³ starting at N, at least one has an odd prime count. This is Borel–Cantelli-safe and gives a prime in [N, N+n⁵) in N^{o(1)}. No failures for N < 2^28 were found with 2·log₂ N blocks of length 256.
> - The "prescribed starting points" weak form above is essentially PR\*.
> - See r1/notebook.md.

PR together with Theorem B gives deterministic prime finding in x^{o(1)} = 2^{O(n/√log n)}: O(log N) parity queries plus bisection. PR is the precise missing lemma, and it is at least as hard as parity-equidistribution of π. The proportion of n with π(n) even is only known to be bounded below, by a sieve, in Integers n79 (2013) and in "On the parity of the prime-counting function and related problems" (2015). Full equidistribution is conjectural.

## 5. Subtask 5: alternative targets, ranked (achievable × value)

1. **[R, done] Barrier theorem.** Theorems 1, 1′ and 2 make prime-finding.md §3(c) a theorem for every GF(2) or Z_M linear query family, with the sharp threshold M\* = N^{1/2±o(1)} under RH. It fits the parity note as "parity is information-theoretically useless for locating primes". Cheap to Lean-formalize: the pivot lemma is mathlib linear algebra.
2. **[C → R conditional] x^{o(1)} prime finding under Conjecture PR**, with numerics. A clean conditional statement. It is ambitious only if PR can be weakened to something averaged that is provable, but Theorem 1′ shows any such statement must be non-robust.
3. **TCH Conj. 1.1 (decision) in x^{o(1)} for |I| ≤ H₀**, already proved, together with the matching lower bound from the Thm 2 adversary restricted to I: deciding requires ≳ |I|/(M polylog) queries. So the engine route stops at |I| = H₀·x^{o(1)}. This is a complete picture.
4. **Lean-certified corollaries**: general proof of Theorem B / B′ and of the pivot lemma.
5. **Exact π(x) faster than Õ(√x)** (Hirsch–Kessler–Mendlovic, elementary Õ(√x)), or prime finding in √x / exp((log x)^c) under RH. Both are blocked: each engine query costs exp(Θ(log x/√log log x)), which exceeds any exp((log x)^c) saving, and Theorem 2 forces M ≥ √N. Do not pursue.
6. Deterministic primes in APs or smallest prime > N: the same model and the same bounds (restrict the coordinates to the AP), so no gain.

## 6. Next

- Sharpen Theorem 2 with a pivot-style argument over Z_M (for M prime, Olson-type zero-sum structure) to get k ≥ G/(M polylog).
- Test Conjecture PR at 10^15–10^18 windows.
- Ask the lead whether the barrier is worth a Lean formalization.

## 7. Cross-references (board, 23:14)
p1 (Thm 2, deletion-only fooling set, a subset of the real primes) and p2 (note 7, family-independent syndrome adversary) proved the same barrier independently. Mine adds three things: (a) the pivot lemma, which gives tight constants (k ≥ min(G, E) − O(log N)) and a fooling set that satisfies the density and gap constraints with arbitrary edits; (b) the threshold M* = N^{1/2±o(1)} for every family; (c) Conjecture PR with numerics. p2 corrects the engine's modulus range to M ≤ exp(o(√log log x)) rigorously. This does not change any bound here, since all M = x^{o(1)} behave the same.

## 8. Escape (A)/(C): exact NONLINEAR counts (lead request, 23:15)

Scripts: `nonlin_span.py`, `nonlin_K.py` (outputs nk10.out, nk11.out), `trade_modulus.py`.

**8.1 Why Theorem 1′ does not transfer directly, and what replaces it.** An exact count Q(I, φ) = Σ_{m∈I} W_φ(m) is still LINEAR, but in the *profile* vector w(m) = (W_φ(m))_φ of each m, not in 1_P. Here W_φ(m) = #{z : Πz_i = m, z ∈ box_φ, congruences on the z_i}, the K-fold counts of the lead's list. An adversary can no longer delete primes. It can, however, *trade profiles*. Call the trade lattice
 L_Φ = { Σ_i c_i 1_P(m_i) : Σ_i c_i w_Φ(m_i) = 0 }.
It equals d_Φ·Z, where d_Φ is the largest d with 1_P ≡ Σ_φ λ_φ W_φ (mod d) on [N,2N]. If 1_P is in the Q-span of the features, then d_Φ = ∞.

The "fake multiplicative world" relabels which integer each factor tuple multiplies to (σ∘mult), inside one segment between queried endpoints. Replacing a multiset of profiles in a segment by another multiset with the same Φ-sums leaves every answer unchanged. It shifts the segment's prime count by a multiple of d_Φ.

[C/sketch] **Theorem 4 (profile-trade barrier).** Assume each trade can be realized locally: profiles of the required shapes occur in every window of length ≪ G. That is true for coarse (dyadic) boxes, and under RH for shapes such as p, 2p, 3p. Then exact Φ-counts reveal π(segment) mod d_Φ and nothing finer about where the primes are. So Theorem 2 applies with M = d_Φ: a prime finder needs ≳ G/(d_Φ log d_Φ log N) queries.

Dichotomy:
- **(i) d_Φ < ∞.** This covers Theorem B (d = 2) and B′ (d = k). The √N barrier holds.
- **(ii) d_Φ = ∞.** Exact prime counts are available and bisection wins in O(log N) queries. But (ii) needs fold K ≥ K*, which grows with log N (8.2). That is the iterated-product cut Θ(n log n) (iterated-product.md), so each query costs 2^{Θ(n√log n)} ≫ x.

A fake world is a Beurling-type relabeling at the level of profiles. This is the precise sense in which nonlinear exact counts "pin down" a prime: only when they span 1_P.

**8.2 Numerics [N]** (rows m ∈ [N,2N), proper prime powers dropped; features are ordered K-fold factorization counts with dyadic boxes on the factors, z=1 allowed).

| N | plain features, exact over Q first at | max Ω of rows |
|---|---|---|
| 2^9 | K = 8 | 9 |
| 2^10 | K = 9 | 10 |

So K* = Ω_max − 1 and grows like log₂N. At 2^11 (nonlin_span), the relative L² residual is still 0.48 at K ≤ 5.

**Mod p:** for p ∈ {2,3,5,7}, 1_P is NOT in the span mod p for any K ≤ 8, so d_Φ = 1 for these small primes. The Q-exactness uses Linnik-type denominators 1/k. Plain products do not even give parity; Theorem B needs the squarefree chain C_L.

**8.3 Möbius-signed weights.** The engine can carry μ(z) only for z inside one node (z ≤ y = x^{o(1)}, factored inside the node).
- With μ on factors ≤ 8: exact at K = 5 for N = 2^9; for N = 2^10 exact first at K = 6 (nk10.out). The needed fold grows with N.
- Asymptotically the needed fold is about the number of prime factors > y, up to log x/log y = K_eng^7 → ∞. So the cut is still Θ(n log n). **The barrier survives.**
- μ on arbitrary O(log x)-bit factors (exact at K = 4 for both N = 2^9 and 2^10) is NOT an engine primitive. A unique witness for μ(d) needs d's certified factorization, which is the iterated product again. Assuming it would already give Σ_{m∈I} μ(m) exactly, i.e. Mertens on intervals, which is equivalent in difficulty to exact π.

**8.4 Polymath4 Problem 1 with a counting oracle.** "Count m ∈ [N,2N] with no divisor in [2, √2N]" = π([N,2N]) is a ∀-count. Its unique-witness forms all go through roughness:
- the Buchstab tree #{lpf = p} = Φ(I/p, p), depth Ω;
- the Legendre sum Σ_{d|P(y)} μ(d)⌊·⌋ with d smooth, needing factorizations of d;
- canonical Pratt certificates, of size Θ(n²) with n modular squarings, so cut ≥ n²: much worse.

A factoring oracle (lpf of one number) is a singleton query and cannot help select x (Theorem 1′ still applies to how x is chosen). Combining exact τ-type counts near √(2N) and N with parities: the profile-trade lattice for {τ-features, chain features} has d = 2 (Theorem B), and adding plain K-fold counts with K < K* does not raise d at p ≤ 7 (8.2). So that route does not isolate an odd window beyond what parity already gives.

**Verdict on escape (A)/(C):** no barrier break. The obstruction for nonlinear exact counts is the pair (d_Φ, fold): either finite detection modulus (√N barrier via Theorem 2) or fold ≥ K* ≍ log N (iterated-product barrier). The genuinely open item is the same as before: a parsimonious iterated-product network with cut o(n√log n), or a rigid scale-local identity (escape B).
