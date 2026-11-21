# p1 notebook — subtasks 1 (T1) and 6 (P1): from parity queries to a prime

Data: all primes ≤ 2.1·10^9 (numpy segmented sieve, `sieve.py`, 102,886,526 primes; array kept in scratch, not here).
Engine capability used: per p2 (board note 1), #{p ∈ I ∩ S} mod 2 is one engine count for every interval I and every
cheap set S (residue classes mod any q ≤ x, bit patterns, Jacobi classes); unions are GF(2)-sums. So "query" below
means: any cheap set S, answer π(S) mod 2 (or mod M, M ≤ 2^{2^{o(√log n)}}), cost x^{o(1)} each.

## 1. Bisection (T1 part 1) — [R]

**Lemma 1.** Let S be a cheap set and I = [a,b] with π(S ∩ I) odd. Then ⌈log₂(b−a+1)⌉ further parity queries find a
prime in S ∩ I.
Proof. Invariant: J = [lo,hi] with π(S∩J) odd. Split at mid; π(S∩[lo,mid]) + π(S∩(mid,hi]) = π(S∩J) is odd, so exactly
one half is odd; one query (the left half) decides which. Length halves each step; at length 1, J = {m} and
π(S∩{m}) = 1 means m ∈ S is prime. Each query is an interval ∩ S, still cheap. ∎
**Lemma 1′ (mod M).** If π(S∩I) ≢ 0 (mod M), at every split at least one half is ≢ 0 (two queries per step suffice: ask
the left half; the right half's residue is the difference). Once |J| < H₀ (where 2|J|/log|J| < M, Montgomery–Vaughan),
the residue is the exact count, so it is ≥ 1, and we still continue to length 1: n+O(1) queries. ∎
**Lemma 1″ (weights).** The same holds for any cheap weight w with Σ_{p∈I} w(p) ≢ 0 (mod M): restriction to subintervals
keeps the weight cheap; at length 1 the single term w(m)[m prime] ≢ 0 forces m prime.

So prime finding in x^{o(1)} ⇔ deterministically exhibiting ONE cheap (S, I) (or weight) with nonzero residue.
Quantification ([N], `exp1.py`): π([N,2N]) is odd for 49.6% of 20,000 random N ∈ [10^6,10^9]. Note that varying the
endpoints of [N,2N] by one changes the parity only when the endpoint is prime, so "try neighbouring windows" is a scan.

## 2. Query families on real windows (P1 experiments) — [N], `exp1.py`

| family | failure on real data |
|---|---|
| total parity π([N,N+h]) | even ≈ 50% for every h (2^4…2^20) |
| XOR of primes in [N,N+h] (n bit-class queries) | XOR=0 among nonempty windows ≈ 1/(2h): h=2^8: 1.8e-3, 2^10: 5e-4, 2^12: 3e-4, 2^14: 0/4000 |
| geometric prefixes [N,N+2^i], i=0,1,…: first odd i | 200,000 random N ≤ 2·10^9: mode i=4, tail halves per step, max i=21 |
| XOR of [N,N+2^i]: first i with XOR≠0 | 50,000 N: max i = 9 |

Heuristic [C]: each extra "independent" bit query halves the failure probability; XOR of a window of length h fails
w.p. ≈ 1/(2h) (bit 0 = total parity, and ~log₂h low bits behave like fair coins). So on real primes every reasonable
family succeeds after O(1)–O(log x) queries. Nothing here is a proof; §3 shows why no proof of this kind can exist
from distributional facts.

## 3. Deletion barrier (P1 core, T1 part 2) — [R]

**Theorem 2 (deletion adversary).** Let 𝒜 be any deterministic, adaptive algorithm that makes Q queries, each of the
form "Σ_{p∈X} v_i(p) mod M" for arbitrary weights v_i : [N,2N] → ℤ/M (arbitrary sets: v_i = indicator; no cheapness
assumed), and then outputs a number m. Let P = primes in [N,2N]. There is X ⊆ P with
  |P \ X| < D((ℤ/M)^{Q+1}) ≤ M(1 + (Q+1) ln M)   (= Q+2 when M = 2; = (Q+1)(M−1)+1 for M a prime power, Olson 1969)
such that 𝒜 run with X in place of the primes outputs m ∉ X.
Proof. Run 𝒜 answering 0 to every query; this fixes v_1..v_Q and the output m. Add v_{Q+1} = 1_{m}. Give each p ∈ P
the vector u_p = (v_i(p))_i ∈ G = (ℤ/M)^{Q+1}. Repeatedly remove from P a nonempty zero-sum subsequence (exists while
≥ D(G) elements remain; D = Davenport constant). The union X of removed blocks has Σ_{p∈X} u_p = 0, so 𝒜 on X sees
exactly the all-zero transcript, outputs m, and m ∉ X because the (Q+1)-st coordinate sums to 0 (|X∩{m}| ≡ 0, ≤ 1).
The remainder P\X has < D(G) elements; D(G) ≤ exp(G)(1 + ln(|G|/exp(G))) = M(1 + Q ln M) (van Emde Boas–Kruyswijk 1967); for p-groups
D = (Q+1)(M−1)+1 (Olson 1969). ∎

**Corollary 3 (what RH-type facts cannot prove) — [R], under RH only as stated.** Let K = M(1+(Q+1)ln M).
Any property of P that survives deleting K primes is also true of X. Under RH (Schoenfeld: |π(y)−li(y)| < √y log y/(8π),
y ≥ 2657), every interval [y, y+√y log²y] ⊂ [N,2N] contains ≥ (1−o(1))·√y log y primes; so if K < 0.9·√N log N, X still
(i) meets every interval of length √y log²y, (ii) satisfies |π_X(y)−li(y)| ≤ √y log y/(8π) + K, (iii) satisfies
Brun–Titchmarsh/BHP/PNT-in-APs with any error term ≥ K, and (iv) consists only of genuine primes. Hence a correctness
proof of a prime finder with Q ≤ c·√N log N/(M log M) queries cannot use only RH, short-interval, gap or AP-distribution
facts: it must use a **rigid** property of P (one destroyed by deleting x^{o(1)} specific primes). This matches the
block-scan upper bound √N log²N/(M log M) (prime-finding.md §3(d)) up to one log: in the residue-query model with
distribution-only proofs, √x is tight. Compared with p3/adversary.py (synthetic codeword adversary), this one is
deletion-only, so the fake prime set is a subset of the real primes and inherits every upper-bound / local-statistic
property automatically; it also covers mod M and arbitrary weights.

**Demonstration on real primes ([N], `exp2.py`).** Family = classes mod 2^j (j ≤ J) of every geometric prefix
[N,N+2^i] + XOR bit-classes of each prefix + 64 sliding windows. GF(2) elimination finds the deletion set:

| N | H | Q queries | rank | #P in window | deleted |Y| | all answers even after deletion |
|---|---|---|---|---|---|---|
| 10^9 | 2^12 | 779 | 97 | 194 | 68 | yes |
| 10^9+12345 | 2^14 | 1129 | 161 | 771 | 79 | yes |
| 1999999000 | 2^15 | 1712 | 208 | 1526 | 118 | yes |

So the "XOR + residue classes + sliding windows" family, which succeeds instantly on the real primes, is defeated by
removing ~8% of the primes of the window (≈ rank/2, far fewer than Q).

## 4. Looking for a rigid odd-parity theorem (variants; switched angle after two)

Goal: an explicit cheap S ⊂ [N,2N] with a THEOREM "π(S) odd" (Theorem 2 says nothing robust can do it).

R1. **Legendre/Wilson identity** — dead. ∏_p p^{v_p(n!)} = n! gives, mod 3 and taking indices mod 2,
Σ_{p≤n, p≡2(3)} v_p(n!) ≡ [n!/3^{v_3(n!)} ≡ 2 (mod 3)] (mod 2), and the right side is explicit from base-3 digits
(n!/3^v ≡ (−1)^v ∏ d_i! mod 3). This IS rigid (deleting one prime ≡ 2 mod 3 breaks it) and the set
A_n = {p ≡ 2 (3): v_p(n!) odd} is cheap, so for half of all n we get a provably odd cheap set and Lemma 1 finds a prime
in A_n. Why it dies: the odd mass is spread over all scales (√n,n] ∪ small p; the prime found may be tiny. To force the
odd part into [N,2N] we need the contribution of A_n ∩ [2,N) to be known — that is again an unproved parity (or a
√-cost sieve). Pairing n, n' with equal small parts needs ∏_{(n,n']} m to be a square in all primes < N: impossible.
R2. **Jacobi symbols** — dead. (a/Q) = (−1)^{#{p | Q odd mult.: (a/p)=−1}} is a rigid parity in poly time for any Q,
but useful only if Q's prime factors outside [N,2N] are controlled — i.e. we need Q with a guaranteed prime factor in
[N,2N] and no uncontrolled small factors. That is the "factoring oracle" version of the problem, which Polymath4
records as still stuck at √x even with a factoring oracle (polymathprojects.org, Polymath4 research threads; Tao–Croot–
Helfgott). Same disease as R1: multiplicative identities couple all scales, and isolating one scale is a sieve, where
the classical parity problem returns.

Verdict on (b): no deterministic guarantee found; Theorem 2 pins down why: needed is a rigid, scale-localised parity
theorem about primes, and the only rigid identities available (multiplicative: factorials, Jacobi, genus theory) are
not scale-localised.

## 5. Next steps I would take
* Look for rigid identities that ARE scale-localised: e.g. Σ_{p∈[N,2N]} f(p) for f a polynomial-time weight whose sum
  over ALL integers in [N,2N] of a "fixed-point-free involution" structure (Zagier style) has known parity and whose
  fixed points are exactly primes in [N,2N] — Zagier's involution on x²+4yz=m gives fixed points = divisor counts, i.e.
  back to τ; need an involution with fixed points = {primes in window} ∪ {explicitly known set}.
* Make Theorem 2 adaptive to "cheap-only" queries plus the engine's own identities (show they add no rigid information
  about location).

## 6. Prior art (from p4 board notes 3–4, checked against my claims)
* TCH arXiv 1009.3956 §1, §4 already note AP parities via P(t) mod (2,g) and the obstruction "all low-degree g divide
  P mod 2"; Tao (Polymath4 thread V, 2010) gives the heuristic that random-like sets can have all AP parities even.
  Theorem 2 above is a rigorous, query-family-independent version of that heuristic, with the extra point that the
  fooling set can be taken INSIDE the true primes (deletion of < Davenport-constant many), hence satisfies every
  upper-bound/local statistic and, under RH, every short-interval lower bound when K < 0.9√N log N.
  I have not found Theorem 2 stated in this form; novelty claimed only modestly (it is a short Davenport-constant argument).
* Kalai (2015, Polymath4 comment) asks for special sequences a_n with [a_n,2a_n] provably odd — exactly the "rigid
  theorem" Theorem 2 says is necessary. R1 (Legendre/n!) gives provably odd cheap sets, but not inside one dyadic range.
