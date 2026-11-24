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

## 3. Engine accounting and the doubled-system network lemma

### 3.1 One copy, written out  [R, elementary]

Ni does not list his 72 variables, 33 equations or 132 slots; his slot count probably uses the network's own
granularity. So I give my own explicit system and count it. A reader can check every line, and it can be compared
with his.

**Query data** (computed outside, written in the query word): for each of the four factors f ∈ {e₁ = e(x/d),
e₂ = e(x′/n), L = log m, I = 1/log n} the query fixes:
- a node index ℓ_f and its rounded node integers U_f, V_f (p + 2 bits each);
- a part π_f ∈ {re, im} and a sign branch σ_f ∈ {+, −};
- the dyadic scales j_m and j_n (j_m = ⌊log₂ m⌋, j_n = ⌊log₂ n⌋).
The constants 2^p, 2^{t+p}, 2^{j_m}, 2^{j_n} and N are also in the query. The boundary sub-queries (d = 1 with
x = 0, where e₁ ≡ 1 is exact and the e₁ kernel is dropped) are separate queries with that block deleted. So is
m = 1, which is not queried at all.

**Variables of copy(n)**:
- Data (5): n, d, m, x, x′.
- Bézout witnesses (4): u₁, v₁ for (x, d) and u₂, v₂ for (x′, n).
- One kernel block per factor f, 10 variables each, so 40 in all: a_f, X_f, Y_f, XX_f, YY_f, D_f, P_f, q_f,
  r_f, w_f.
- Total: **49 variables.**

**Kernel block for f, at y_f = a_f / s_f.** The pairs (a_f, s_f) are:
- e₁: (d + x, d);
- e₂: (n + x′, n);
- L: (m, 2^{j_m});
- I: (n, 2^{j_n}).

| # | constraint | kind |
|---|---|---|
| K1 | a_f = (its linear form) | linear |
| K2 | X_f = U_f·s_f − 2^p·a_f (σ_f fixes the sign: σ_f X_f ≥ 0, with X_f stored as |X_f|) | product by a query constant (a shift for L and I) |
| K3 | Y_f = V_f·s_f (σ for Y is fixed by the sign of V_f, known outside) | product by a query constant |
| K4 | XX_f = X_f·X_f | product |
| K5 | YY_f = Y_f·Y_f | product |
| K6 | D_f = XX_f + YY_f | linear |
| K7 | P_f = s_f·|X_f| (π = re) or s_f·|Y_f| (π = im) | product (a shift for L and I) |
| K8 | 2^{t+p}·P_f = q_f·D_f + r_f | product q·D |
| C1 | r_f < D_f | comparison |
| C2 | w_f < q_f | comparison (the multiplicity) |

**Data constraints.**

| # | constraint | kind |
|---|---|---|
| E1 | d·m = n | product |
| E2 | x·u₁ = 1 + d·v₁ | 2 products |
| E3 | x′·u₂ = 1 + n·v₂ | 2 products |
| C3 | 1 ≤ x < d, u₁ < d, v₁ < x | comparisons |
| C4 | 1 ≤ x′ < n, u₂ < n, v₂ < x′ | comparisons |
| C5 | 2^{j_m} ≤ m < 2^{j_m+1}, 2^{j_n} ≤ n < 2^{j_n+1}, 2 ≤ n ≤ N, m ≥ 2 | comparisons |

**Count for one copy:**
- Equations: 3 (E1–E3) + 4 × 8 (K1–K8) = **35**.
- Variable × variable products: 5 (E1–E3) + 4 × 3 (K4, K5, K8) + 2 (K7 for e₁, e₂) = **19**.
- Variable × query-constant products: 4 (K2, K3 for e₁, e₂). L and I use only shifts.
- Comparisons: about 20.

Ni's numbers are 72 / 33 / 132. My 35 equations match his 33 up to bookkeeping (e.g. folding K1 and K6). His
larger variable and slot counts presumably come from binary splitting of the products in the network
representation.

**Bit sizes** (β = b(N), y ∈ [1, 2), |z̃ − y| ≥ 1/4):

| variable | bits |
|---|---|
| a | ≤ β + 1 |
| X | ≤ p + β + 3 |
| Y | ≤ p + β + 2 |
| XX, YY, D, r | ≤ 2p + 2β + 7 |
| P | ≤ p + 2β + 3 |
| q, w | ≤ t + 3, since q = ⌊2^t·|Re or Im 1/(z̃ − y)|⌋ ≤ 4.1·2^t |
| data and Bézout | ≤ β + 1 each |

The total is ≤ 4(9p + 13β + 2t + 40) + 9(β + 1) bits per copy. With p, t = D + O(log β), this is O(β).

**Unique determination** (so that #solutions = Σ_{data} Π_f q_f exactly):
1. Given n, d, x, x′, the witnesses (u₁, v₁) and (u₂, v₂) exist and are unique iff the gcds are 1. This is Ni's
   Bézout lemma; [N] it is checked for d ≤ 200 (`run.py bezout`).
2. a, X, Y, XX, YY, D and P are given by equations.
3. D > 0 because |z̃ − y| ≥ 1/4.
4. (q, r) is the unique quotient and remainder with 0 ≤ r < D.
5. The sign branch is fixed by the query and checked by a comparison, so each data tuple lies in exactly one
   σ-branch.
6. The only free variables are the w_f < q_f, which give the multiplicity Π q_f.
7. m and x are determined by (n, d) and the data, and j_m, j_n are fixed by the query, so no tuple is counted
   twice.

### 3.2 The doubled system for π₂  [R]

The variables are copy(n) on (n, d, m, x, x′, …) and copy(n₂) on fresh variables (n₂, d′, m′, y, y′, …), plus one
linear equation n₂ = n + 2. **The only variable that occurs in constraints of both copies is n**, through
n₂ = n + 2. Every other constraint mentions variables of one copy only.

Hence the solution set is the fibre product over n:

  #sol = Σ_{n} [Σ_{data of copy(n)} Π_{f∈copy 1} q_f] · [Σ_{data of copy(n+2)} Π_{f∈copy 2} q_f],

which is the term that Σ_n P̃(n)P̃(n+2) needs for the chosen (node, part, sign, scale) query.

**Count:**
- Variables: 49 + 49 = **98** (n₂ is copy 2's "n").
- Equations: 35 + 35 + 1 = **71**.
- Variable × variable products: **38**, plus 8 by-constant products.
- Bits: twice one copy, at the twin precision D ≈ 5β.

For Goldbach, replace the link by m₂ = 2n_input − m with m ≤ n. For Sophie Germain, use n₂ = 2n + 1. For a k-tuple
there are k copies linked by n_i = n + h_i, so 49k variables and 35k + k − 1 equations.

**Network lemma (what must be proved to apply Prop. 4).** For each query π, this system must be realised as a
`Net` inside one `CntPackage c₀′`:
- U ≤ c₀′(|w| + 2);
- P, B, τ and S bounds as in `CntPackage.lean`;
- value equal to the count above.
Because the system has a constant number of variables, each of O(|w|) bits after linear padding, the shared-bit
bound holds with c₀′ = O(1) (about 2× Ni's constant per copy, times the precision ratio 5/3 relative to his π).
**Status:** the arithmetic content (this section) is [R]. The Lean/`Net` realisation is not written by us or by Ni
(his Remark 8). It should be the same proof as Ni's network with the block duplicated. This is the main formal
gap, so **Theorem A is conditional on it.**

### 3.3 Remaining CntPackage requirements
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

"Rounding OK" means that ⌊Re S̃ + 1/2⌋ equals the true value for **every** prefix N′ ≤ N (or every 2n ≤ N).
Truth comes from a sieve. Raw output is in `results.out` and `results2.out`.

| run | parameters (M, p, t) | values checked | rounding failures | max \|S̃ − S\| | budget bound |
|---|---|---|---|---|---|
| fully literal (n,d,m,x,x′) loop, π, N = 40 (`tuple`) | Ni: 395, 74, 67 | 1 | 0 | ~1e−20 | 1/2 |
| literal loop == factored sum, bit for bit | N = 12 and N = 40 | ✓ | | | |
| node/part/sign expansion == literal sum (`nodes 8 3`) | M = 3, p = t = 12 | 6576 classes | ✓ bit for bit | | |
| π(N′), N′ ≤ 2000, Ni's table | 570, 109, 102 | 1999 | 0 | 2^−85.3 | 1/2 |
| π(N′), N′ ≤ 2000, our budget (D = 41) | 266, 59, 54 | 1999 | 0 | 2^−36.5 | 0.21 |
| π₂(N′), N′ ≤ 2000 (D = 74) | 401, 89, 84 | 1999 | 0 | 2^−68.4 | 0.19 |
| G(2n), 2n ≤ 2000 (D = 74) | 401, 89, 84 | 999 | 0 | 2^−67.6 | 0.19 |
| Sophie Germain, N′ ≤ 1000 (X = 2001) | 401, 89, 84 | 999 | 0 | 2^−69.7 | 0.19 |
| M(x), x ≤ 3000 (D = 2β + 2 = 26) | 185, 41, 36 | 3000 | 0 | 2^−16.3 | 0.13 |

Per-indicator accuracy: max_n |P̃(n) − 1_prime(n)| = 1.5e−28 (Ni's table) and 7.6e−14 (D = 41). For Mertens,
max_n |μ̃(n) − μ(n)| = 1.4e−8.

**Stress test (twins, N = 300; the budget asks for D = 64).** The table below lowers D:

| D | 48 | 32 | 24 | 16 | 12 | 10 | 8 | 6 |
|---|---|---|---|---|---|---|---|---|
| max error | 2^−48 | 2^−33 | 2^−26 | 2^−15 | 2^−12 | 2^−10 | 2^−7 | 2^−3.7 |
| failures | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

(The D = 4 run was cut off by the time limit.)

So the worst-case budget is very conservative for products: about 58 bits of slack at N = 300. The reasons:
- per-factor errors are ~2^{−(D+8)};
- the tuple count T ≈ N⁵ is an absolute-value bound;
- the errors do not align.
The observed error scales like 2^{−D}·poly(N), not N⁵·2^{−D}. This is not used anywhere; the theorem uses the
rigorous budget.

PATTERNS_PLACEHOLDER

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
