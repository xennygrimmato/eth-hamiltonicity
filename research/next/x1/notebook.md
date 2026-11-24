# x1 notebook: twin primes, Goldbach, k-tuples and Mertens in N^{o(1)} via Ni's analytic reduction

Tags: **[R]** proved here (with the dependencies named) · **[K]** known · **[N]** computed · **[C]** conjecture.
Files: `pipeline.py` (exact-arithmetic simulation of Ni's kernel pipeline), `run.py` (driver), `results.out`
(the runs quoted in §5). Engine: Ni's Proposition 4 = `NatBatchQuery.machine_TM_linear_input`
(Ni repo `formal/bridge/EthFollowup/ModP/BatchNatQueries.lean`), on top of Anthropic's #3-SAT counting route.

## 0. Summary

| statement | status |
|---|---|
| Thm A: π₂(N) exact in 2^{O(b/√log b)} | [R] modulo Prop 4 plus a network lemma (§3) of the same kind Ni proves for π; [N] N ≤ 2000 |
| Thm B: G(2n), Sophie Germain count, any fixed admissible k-tuple, semiprimes, π(N;q,a) | same as A; [N] for G and SG |
| Thm C: Mertens M(x) and Liouville L(x) exact in 2^{O(b/√log b)} | [R] mod Prop 4 + network lemma (one copy, no logs); [N] x ≤ 3000 |
| Thm D (general): sums of bounded products of Ramanujan phases and analytic functions over a bounded engine system | [R] same dependencies |
| Ni's literal coefficient table (M=35β+185, p=7β+32, t=7β+25) already meets the twin budget once β ≥ 22 | [R] (arithmetic, §2) |
| Prior art | none found for twins/Goldbach/tuples; Ni's Remark 7 *expects* Mertens but does not claim it (§8) |

## 1. Identities  [R, elementary]

Write P(n) = 1_prime(n). For n ≥ 2 (Ni §3.1)

  P(n) = −μ(n)Λ(n)/log n = − Σ_{dm=n} Σ_{0≤x<d,(x,d)=1} Σ_{0≤x′<n,(x′,n)=1} e(x/d) e(x′/n) log m · (1/log n).

(The m = 1 term vanishes since log 1 = 0; d = 1 contributes the single phase e(0) = 1. Both are Ni's
"boundary cases" and are treated exactly.)

**Twins.** π₂(N) = Σ_{2≤n≤N} P(n) P(n+2)
 = Σ over (n; d,m,x,x′; d₂,m₂,x₂,x₂′) with dm = n, d₂m₂ = n+2, (x,d) = (x′,n) = (x₂,d₂) = (x₂′,n+2) = 1 of
   e(x/d) e(x′/n) log m (1/log n) · e(x₂/d₂) e(x₂′/(n+2)) log m₂ (1/log(n+2)).

This is a sum of **8 analytic factors** over the solution set of a system that is two disjoint copies of Ni's
system **sharing only n** (the second copy reads n₂ with the linear constraint n₂ = n + 2). It is the p2 §5.1
pattern trick, except that the counts now multiply as real weights, not just parities.

**Other patterns** (same shape, two or k copies):
- Goldbach G(2n) = #{p ≤ n : 2n − p prime} = Σ_{2≤m≤n} P(m) P(2n−m) (constraint m + m₂ = 2n, m ≤ n).
- Sophie Germain #{p ≤ N : 2p+1 prime} = Σ_{n≤N} P(n) P(2n+1) (constraint n₂ = 2n + 1).
- Admissible k-tuple (h₁,…,h_k): Σ_{n≤N} Π_i P(n + h_i), with 4k factors.
- Semiprimes #{pq ≤ N} = Σ_{d m ≤ N, d ≤ m} P(d) P(m), with weight-free counting of n = dm ≤ N.
- Primes in progressions π(N; q, a) = Σ_{k} P(qk + a) (one copy, one more linear constraint, any q ≤ N).
- **Mertens** M(x) = Σ_{1≤n≤x} Σ_{0≤x′<n,(x′,n)=1} e(x′/n): one phase factor and no logarithm.
- Liouville L(x) = Σ_{n≤x} λ(n) with λ(n) = Σ_{d²k=n} μ(k): variables d, k, the product d·d·k, and one phase.

## 2. Error budget  [R, given Ni's Lemma 5]

**Per-factor error.** Take c = 3/2, r = 3/4 and nodes z_ℓ = c + r e(ℓ/M). Round each node to z̃_ℓ = (U+iV)/2^p
and each coefficient c_ℓ = h(z_ℓ)(z_ℓ−c)/M to p bits. Truncate both parts of 1/(z̃_ℓ − y) to t bits (Ni's
eq. (2)). For y ∈ [1,2), we have |z − y| ≥ 1/4 and Σ_ℓ |c_ℓ| ≤ (3/4)H, where H = sup|h| on |z − c| ≤ 7/8.
The factor error is then

  δ ≤ 49H(6/7)^M  [Lemma 5]  + 8.6H·2^{−p}  [node rounding]  + 3M·2^{−p}  [coefficient rounding]  + 1.1H·2^{−t}  [truncation].

H is at most max(e^{7π/4} ≈ 245, β ln 2 + 4.3, 1/(ln 2 + ln(5/8)) ≈ 4.5). The lower bound Re(j ln 2 + log z) ≥
ln 2 + ln(5/8) = 0.223 for j ≥ 1 is what makes 1/log analytic on the disc. Hence a target of δ ≤ 2^{−D} is met by

  M = ⌈(D + log₂(147H)) / log₂(7/6)⌉ ≈ 4.5D + O(log β),   p = D + O(log(β + M)),   t = D + O(log β).

This is `params_for` in `pipeline.py`.
[N] Measured worst factor errors (`run.py factors`): phase, log and 1/log come out at 2^{−(D+8)} to 2^{−(D+10)}
for D = 20 and D = 74 (X = 2002). So the formula is safe, with about 8 bits of slack (the Lemma 5 constant).

**Products.** Suppose |f_i| ≤ B_i and |f̃_i − f_i| ≤ δ ≤ 1. Then |Πf̃_i − Πf_i| ≤ kδ Π(B_i + 1). Here B = 1 for a
phase, B < β for log m (m < 2^β), and B < 1/ln 2 for 1/log n. So one prime-indicator copy carries
Π(B+1) ≤ 9.8(β+1).

**Number of summands.** Since Σ_{d|n} φ(d) = n, one copy at n has exactly n·φ(n) tuples (d, m, x, x′).

| problem | k | summands T | per-factor exponent D (error < 1/2) |
|---|---|---|---|
| M(x) | 1 | Σφ(n) ≤ x² | 2β + 2 |
| π(N) | 4 | Σ nφ(n) ≤ N³ | 3β + log₂(80(β+1)) + 1 |
| π₂(N) | 8 | Σ nφ(n)(n+2)φ(n+2) ≤ (N+2)⁵ | 5β′ + log₂(1540(β′+1)²) + 1, β′ = b(N+2) |
| G(2n) | 8 | ≤ (2n)⁵ | same, with β′ = b(2n) |
| SG(N) | 8 | ≤ (2N+1)⁵ | same, with β′ = b(2N+1) |
| j-copy pattern | 4j | ≤ X^{2j+1} | (2j+1)β′ + j·log₂(9.8(β′+1)) + log₂(16j) |

The total error is at most T·k·δ·Π(B+1) < 1/2, so ⌊Re S̃ + 1/2⌋ is exact.

Concrete values of (M, p, t) from this budget:

| b | Mertens | π | twins |
|---|---|---|---|
| 10 | (167, 36, 32) | (253, 56, 51) | (379, 84, 79) |
| 65 | (662, 147, 142) | (1008, 224, 219) | (1638, 365, 359) |
| 333 | (3072, 685, 678) | (4633, 1032, 1025) | (7686, 1712, 1704) |

Ni's table for π is (M, p, t) = (35β+185, 7β+32, 7β+25), with δ = 2^{−(6β+6)}. That **already meets the twin
budget** once (N+2)⁵·770(β+2)²·2^{−6β−6} < 1/2, which holds for β ≥ 22. So the same certified coefficient table
serves twins, Goldbach and Sophie Germain. Only small N need a slightly larger M. [R, arithmetic]

**Multiplicities (task 1c).** Each truncated kernel part is s·q with s = ±1 and 0 ≤ q = ⌊2^{t+p} q_y|X|/D⌋ <
2^{t+3} (|1/(z−y)| ≤ 4.1). Expanding the 8 linear combinations, the real/imaginary choice (2⁸) and the sign
branches (2⁸, decided by comparisons inside the system on X ≷ 0, which is a sign condition on U·q_y − 2^p·a)
gives

  2^{8(p+t)} S̃ = Σ_{ℓ₁..ℓ₈, parts, signs, dyadic scales j} (Π_i ±C_{ℓ_i}^{(part, j)}) · #{solutions of system Σ(ℓ, part, sign, j)},

where each system Σ adds free variables v_i < q_i, so that its count is Σ_tuples Π q_i. That makes
M⁸·2¹⁶·β⁴ = β^{O(1)} queries, each count < (N+2)⁵·2^{8t+24} = 2^{O(β)}, and Gaussian-integer coefficients
computed outside the engine. [N] `run.py nodes 8 3`: 6576 (node, part, sign) classes for π at N = 8, M = 3. The
integer combination of the class counts equals the literal tuple sum **bit for bit**.

## 3. Engine accounting  [R as a count, plus one lemma not written in Lean]

Ni's π/S system has 72 variables, 33 equations and 132 product slots. Every variable has O(β) bits and every
auxiliary variable is uniquely determined. The twin system is two copies plus n₂ = n + 2, with n shared: about
144 variables, 67 equations and 264 product slots. Each variable still has O(β) bits, but β grows to O(p + t) =
O(β) with constant about 6 instead of about 7. **Shared bits (the network parameter U) stay ≤ c₀′(b+2) with
c₀′ ≈ 2c₀.** Other requirements of `CntPackage`:
- Query length ≤ R(w) ≤ |w|. A query carries 8 nodes (U_ℓ, V_ℓ) of p bits each, the scales j, and the
  part/sign bits, which is about 16p = O(β) bits. As in Ni, w is padded linearly (his factor is 2049; ours is
  about 2×). Linear padding is allowed by `machine_TM_linear_input` (premise `hhi`).
- Q < 2^{qb(|w|+2)}: the count is 2^{O(β)}. ✓
- The number of queries β^{O(1)} and the outside arithmetic on β^{O(1)}-bit numbers are both polynomial. ✓

**What is not checked:** the Lean lemma that the conjoined system is a `CntPackage` with the stated U, P, B, τ, S
bounds, i.e. Ni's "counting bijection for the network and bit bounds" for the doubled system. Ni has not released
this for his own system either (his Remark 8 promises it). Our conjunction-of-copies construction for parity
(p2 §5.1) uses the same composition. I see no obstruction, but it is a real lemma.

## 4. Theorems

Let T_C(N) = C·2^{C·b/√log₂(b+2)}, as in Ni.

**Theorem A (twin primes).** [R, assuming Ni's Prop. 4 and the network lemma of §3 for the doubled system] There
is a deterministic machine and a constant C such that, on input N, it outputs π₂(N) = #{p ≤ N : p, p+2 prime}
within T_C(N) steps.
Proof: §1 identity, §2 budget (D = 5β′ + O(log β), or Ni's table for β ≥ 22), §2 expansion into β^{O(1)}
counting queries, §3 accounting, Prop. 4, then round. ∎
Corollaries: the n-th twin pair and the largest twin pair ≤ N (by bisection, which uses adaptive queries and Prop
4 allows them); deciding whether [a, b] contains a twin pair.

**Theorem B (patterns).** Same hypotheses and the same time bound, for:
- G(2n);
- #{p ≤ N : 2p+1 prime};
- #{n ≤ N : n + h₁, …, n + h_k all prime} for any fixed k and h;
- #{pq ≤ N};
- π(N; q, a) for every q ≤ N, which also gives the least prime ≡ a (mod q) in time q^{o(1)}·(that prime)^{o(1)},
  by bisection up to Linnik's bound;
- #{a ≤ A : a² + 1 prime}, using the constraint n = a·a + 1, in time A^{o(1)}.
For a k-copy pattern, the time is β^{O(k)}·2^{O(kb/√log(kb))}. This is N^{o(1)} for k = o(√log b).

**Theorem C (Mertens, Liouville).** [R, assuming Prop. 4 and a one-copy network lemma, which is simpler than
Ni's: there is no log, 1/log or division chain, so the variables are only n, x′, a Bézout pair (u, v), one kernel
quotient/remainder and one multiplicity] M(x) and L(x) are computable exactly in T_C(x). The best previous bound
for M(x) is O(x^{3/5}(log x)^{3/5+ε}) (Helfgott–Thompson 2021) [K].

**Theorem D (general form).** [R, same dependencies] Fix a template: a system Σ of the engine's kind (additions,
comparisons, copies and O(1) multiplications) with O(1) variables of O(b) bits, plus k = O(1) factors
φ_i(r_i). Each r_i = a_i/q_i is a ratio of system variables that lies in [1, 2) after an outside-enumerated dyadic
shift. Each φ_i is analytic on |z − 3/2| ≤ 7/8 with sup ≤ 2^{poly β}, and its node values are computable to
poly(β) bits in poly(β) time; e(·−1), j ln 2 + log, 1/(j ln 2 + log) and polynomials all qualify. Integer weights
are polynomial in system variables and are realised as multiplicities. Suppose the total mass Σ_{sol} Π|φ_i| is at
most N^{O(1)}. Then S = Σ_{sol(Σ)} weight·Π φ_i(r_i) can be computed to within N^{−A}, for any fixed A, in time
2^{O(b/√log b)}, and exactly when S is known to lie in ℤ (or in (1/Q)ℤ with Q ≤ N^{O(1)}).
**What this captures:** fixed-depth Dirichlet convolutions of μ (via Ramanujan sums), 1, log, 1/log and polynomial
weights, evaluated at O(1) affine or polynomial images of n. That includes μ, Λ, 1_prime, λ, φ, τ_k, ω, μ² and
their bounded products and shifted correlations, e.g. Σ μ(n)μ(n+h) exactly (Chowla sums). It also includes
ψ(x) and θ(x) to precision N^{−A}, since they are not integers.

**What does not follow.**
1. **An unbounded number of factors.** Examples: k-tuples or "prime constellation" counts with k ≫ √log b, the
   number of prime gaps ≥ g for g → ∞ (this needs Π_{i<g}(1 − P(n+i))), and the maximal prime gap below N. Here
   both the shared bits (kb) and the query count (M^{4k}) blow up.
2. **Non-polynomial functions of an inner sum.** Examples: the Goldbach exceptional set #{2n ≤ N : G(2n) = 0}, and
   #{n ≤ N : π(n) is even}. The method handles 1[inner sum = 0] only one n at a time (N^{1+o(1)} in total).
   Verifying Goldbach up to N therefore stays at N^{1+o(1)}, but a single 2n takes (2n)^{o(1)}.
3. **Quantities not of bounded convolution depth.** Examples: Ψ(x, y) for y = (log x)^{O(1)} (unbounded u; for
   fixed u = log x/log y, inclusion–exclusion over the ≤ u large prime divisors does fit, which is [C] pending
   checks), Artin primitive-root counts (these need modular exponentiation), and class numbers.
4. **Anything whose exactness is not an integer.** Only approximations are available.

## 5. Numerical validation  [N]

`pipeline.py` builds every approximate factor exactly as Ni's eq. (2): integer kernel quotients and p-bit
Gaussian-integer coefficients from mpmath. All sums are done in exact integer arithmetic, with no engine. The
tuple sum is factored by distributivity, which is an exact identity on the approximate values:
Σ_n −A(n)F_inv(n)Σ_{dm=n} A(d)F_log(m), with A(d) = Σ_{(x,d)=1} F_e(x/d). Twins use P̃(n)P̃(n+2) in the same way.

RESULTS_PLACEHOLDER

## 6. Mertens details
M(x) is the special case k = 1 of Theorem D: the only factor is the Ramanujan phase. The budget is D = 2β + 2,
so M ≈ 9β, and n = 1 is exact. Measured at x ≤ 3000: see §5. The error is ~2^{-16} at x ≤ 500 against a bound of
0.24 (only ~14 bits of slack). Here the budget is fairly tight, unlike π₂, because there are only φ(n) terms per
n and no cancelling products.

## 7. Risks
1. **Everything inherits Prop. 4.** It is formalised in Lean, but the 3-SAT engine underneath is an unrefereed
   2026 result. Ni's own results are unreproduced (NI-2611.md).
2. **Network lemma for the doubled system (§3)** is not written. Ni's own network proof is "in preparation". The
   conjunction is routine in our parity setting (p2 §5.1), but the analytic version has 2× variables and must
   respect the U ≤ c₀(n+2) template. c₀ is a package parameter, so a new package is needed, and the rate constant
   C changes.
3. Coefficient certification: the same CertifiedGenerator works (the functions are the same), at precision
   p = O(β).
4. **Novelty is a corollary of Ni.** Ni explicitly anticipates Mertens (Remark 7). Twins/Goldbach are the natural
   next step, and others may post it quickly.

## 8. Prior art (searched 24 Nov 2026)
- Ni repo github.com/6teamFurina/prime-algorithm. HEAD is 17 Nov ("Sync latest author revisions"); the tag is
  v0.1-verified. It contains only π, S and prime finding. Remark 7: "We expect it to apply to other summatory
  functions, such as the Mertens function, but only the three theorems above have been formalized." There is no
  mention of twins, Goldbach or tuples.
- Web search (arXiv, alphaXiv, general): no N^{o(1)} or sublinear exact algorithm for π₂, G(2n), k-tuples or M(x).
  arXiv 2610.13365 ("Short recurrences and straight-line programs for primes") gives a length-167 straight-line
  program for twin-prime counts. That bounds the number of operations, not the running time; its intermediate
  integers are huge. It is not a competitor. The best known for M(x) is x^{3/5} (Helfgott–Thompson) [K]. For π₂ and
  G(2n), no algorithm better than sieving (N^{1+o(1)}, or N^{1/2+o(1)} space-segmented) is known [K, to our
  knowledge]. Hexagon is not indexed by the search tools, so that check is weak.
