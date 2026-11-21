# r1 notebook (second r1; 21–22 Nov 2026)

Tags: [R] proved here, [K] known (citation), [N] computed (script in this folder), [C] conjecture/heuristic.
Scripts: `pr_stats.py` (-> `pr_stats_31.out`), `pr_model.py` (-> `pr_model.out`), `prstar.py` (-> `prstar_29_L256.out`).
Leftovers of the first r1 (`explicit_window.py`, `zeros_rs.py`) were not needed: they belong to the analytic-hybrid
route that p4 already closed (cost x/M).

## 0. Summary

1. **Task 1: the RH proof's method gives nothing beyond the statement for prime finding.** Its object is a
   Chebyshev-type "divisibility <= size" certificate: one-sided, linear in Λ, slack x^{1/2+ε}, and of size
   exp(x^ε) times x. Details in §1.
2. **Task 2: Conjecture PR as stated is heuristically FALSE, and numerically the doubling strategy from a fixed start N
   really fails** [N]: for 124 values of N in [2^9, 2^30) NO j ≤ log2 N gives π([N, N+2^j)) odd; the Cramér model
   predicts 121.5. Failures per dyadic block grow like 0.35·log2 N, so they never stop [C]. The fix is a family with
   ≥ (1+ε)·log2 N independent block parities (Conjecture PR*, §2.4); K = 2·log2 N blocks never failed for N < 2^28 [N].
   No "for every N" form can be proved from GRH + pair correlation + HL-type asymptotics (deletion-robust) [R, by p1
   Thm 2 / p3 Thm 1']; the almost-all form is provable under uniform Hardy–Littlewood (Gallagher) but is
   algorithmically empty (§2.3).
3. **Task 3:** four angles, all dead, each for a stated reason (§3). The cleanest is the Möbius-factorial isolation:
   a rigid identity that isolates the window (n/D, n] exactly, at cost D + n/D ≥ 2√n. Same wall.

## 1. Task 1: what the RH proof's method produces

Sources (all secondary to the Lean archive; I did not open the archive):
- Rubinstein et al., "The Alpöge–Claude proof of the Riemann hypothesis explained for the Riemann zeta function",
  working draft 21 Nov 2026, https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/zeta-paper.pdf (Parts I–II;
  the main inequality (M) is quoted from Lean, not proved there).
- riemannhypothesisclaude.org summary of Alpöge's 4-page note; nasqret "atlas blueprint"; tamnd/riemann-lean
  (Main.lean lists five theorems, including `LFunction_eq_zero_re : DirichletLZerosOnLine`); Lean community blog
  post of 21 Nov 2026 certifying `RiemannHypothesis`.
- Correction to p4/literature.md §4: GRH for Dirichlet L-functions is among the five exported Lean theorems
  (per tamnd/riemann-lean and the blueprint's "all five theorems matched"). The Lean community statement I read
  certifies only the ζ statement explicitly. [K, secondary sources]

**The method** [K, Rubinstein draft §I.0–I.8]:
- Statistic: S(x) = Σ Λ(n)(x/n − 1)_+ , G(x) = S(x) − x log x + (1+γ)x = log 2π − Σ_ρ x^ρ/(ρ(ρ−1)) + O(x^-2).
- Analytic step: a ONE-SIDED bound G(x) ≤ x^{1/2+ε} on intervals [Y, Y^{3/2}] for arbitrarily large Y implies RH
  (Landau-type oscillation argument).
- Arithmetic step: Chebyshev's "divisibility ≤ size" with a better integer. The object is a chain of m ≈ √x theta
  lifts between definite unitary groups, i.e. an integer matrix T whose entries are derivatives of order
  a ≈ x·b, b = exp(x^ε), of theta series of CM lattices. At primes inert in the CM field, p^e | T with
  e ≥ Σ_{h odd} (a/p^h − w)_+ = w·(x/p^h − 1)_+ (x = a/w): the ramp kernel with no floor functions. Size is known
  through the linear term (Chowla–Selberg, mass formula). Slope inequality e·log p ≤ log‖T‖ + μ_max(M) − μ(L) gives
  the main inequality (M): (1/n)Σ_{u,t,j}(P − M) ≤ E with E/B ≤ x^{Cε}(x/m + xm/k + m + k/n²); m ≈ √x balances.
- Toy model: A_n = sl^{(n)}(0) (Hurwitz), v_p(A_n) ≈ n·p/(p²−1) at p ≡ 3 mod 4.

**Why it is not a lever** (the 10-line note):
1. The certificate is an INEQUALITY with slack x^{1/2+ε}, on the linear functional G of Λ. It is exactly the
   statement RH in the form "|G(x)| ≤ x^{1/2+ε}". Nothing is evaluated exactly. [K]
2. It is linear in the prime indicator (a sum over prime powers of a fixed kernel times characters χ_d, χ_q and
   residue-class cells). So it sits inside the linear-query model, where the barrier (p1/p2/p3) applies. [R given barrier]
3. It is deletion-robust: removing x^{o(1)} primes changes P by x^{o(1)}·b, far inside the error E. So by p1 Thm 2 it
   cannot certify any sub-√N family. [R]
4. It is not local. The ramp (x/p − 1)_+ sees all primes ≤ x. A second difference in x does localise
   (f(x+h) − 2f(x) + f(x−h) is a tent on |p − x| < h), but the bound on each G is ±x^{1/2+ε}, so the window sum is
   controlled only for h ≫ x^{1/2+ε}. This is Cramér's range again. [R]
5. It is not computable: the entries of T have ≥ a·log a ≈ x·exp(x^ε) bits, and the construction uses auxiliary
   primes q, d with log q ≈ Y^{ε/5}. Even the toy A_n has ~n log n bits and its exponents e_p are "all primes ≤ n",
   like n!. Computing A_n mod M quickly would be a factorial-type oracle (not known below √n). [K/C]
6. One-sidedness does not help: w1's certifying-weight idea needs a weight ≤ 0 on composites; here the sign
   information is about the SUM (upper bound), not about individual terms.
7. The proof never produces a positivity kernel, an operator with spectrum = zeros, or a Weil-positivity witness.
   It is Stepanov/Chebyshev-style (multiplicity via iterated lifts), not Hilbert–Pólya. [K, per the draft]
Verdict: method = statement for our purposes. Pivot.

## 2. Task 2: Conjecture PR

PR (p3 §4): for every N some j ≤ C(log log N)² has π([N, N+2^j)) odd. Write L(N) for the least such j ≥ 0.

### 2.1 Heuristic: PR is false infinitely often, and so is "j ≤ log2 N" [C]

Block j = [N+2^{j−1}, N+2^j) is disjoint from the earlier ones. In the Cramér model its parity is a coin with
P(even) = (1 + e^{−2λ_j})/2, λ_j = 2^{j−1}/ln N, independent over j. So
 P(L(N) > J) = Π_{j≤J} (1+e^{−2^j/ln N})/2 ≈ c·ln N·2^{−J}   (J ≥ log2 ln N).
- With J = C(log log N)²: P(fail) = exp(−c'(log log N)²), and Σ_N of that diverges. A positive, slowly decaying
  proportion of N violates PR for any fixed C.
- Even with J = ⌊log2 N⌋ (the largest j keeping the interval inside [N, 2N)): P(fail) ≈ c·ln N/N, expected number of
  failing N in [2^k, 2^{k+1}) ≈ c·k, total over k diverges. By (second) Borel–Cantelli, infinitely many N fail.
So a single start N plus doubling is the wrong family: it has only log2 N − log2 ln N fair coins, about ln N too few.

### 2.2 Numerics, exhaustive over all N < 2^30 [N] (`pr_stats.py 31`, 6 min)

For every N in [2^k, 2^{k+1}), k ≤ 29, least j ≤ k with π([N, N+2^j)) odd.
- Tail is geometric with ratio 1/2: e.g. k = 29 (5.4·10^8 values of N), #N with L ≥ 21,22,…,29 =
  4248, 2100, 1014, 568, 322, 178, 82, 40, 24; and 18 values of N have no odd j ≤ 29 at all.
- Mean of L grows like log2 ln N: 3.35 (k=16), 3.71 (k=20), 3.99 (k=24), 4.28 (k=29).
- **Full failures (no odd j ≤ k):** in every dyadic block from k = 18 to 29 (2 to 18 per block); 124 in total for
  9 ≤ k ≤ 29. Cramér-on-odd-numbers model (`pr_model.py`): 121.5 expected, per block 0.35·k. Examples:
  N = 1229830, 4914212, 261747954, 1014257268 (failures come in pairs N, N+1 with N even).
- Versus the conjectured bounds at N ≈ 2^29: (ln ln N)² = 9.0, (log2 log2 N)² = 23.6, log2 N = 29, log2 √N = 14.5.
  Measured P(L ≥ J) ≈ 2^{−(J−4.05)} (from L ≥ 21: 7.9·10^{−6}). So the fraction of N with L > 9 is about 2^{−6} and
  with L > 14 about 2^{−11} (both extrapolated along the geometric tail); L ≥ 25: 6·10^{−7} (322 values); no odd j
  at all: 3·10^{−8} (18 values). So PR "for every N" fails at every scale tested for any reading of C(log log N)² below log2 N,
  and "j ≤ ½ log2 N" fails for ~0.05% of N. As an almost-all statement it is fine.

### 2.3 What can be proved conditionally

**(a) Almost all N, under uniform Hardy–Littlewood.** [K + routine extension, not written out line by line]
Assume the HL k-tuple asymptotic Σ_{n≤X} Π_i 1_P(n+h_i) ~ 𝔖(h) X/log^k X uniformly for distinct h_i ≤ A log X, every
fixed k, A (Gallagher's hypothesis, Mathematika 23 (1976)). Gallagher: π(n+λ log X) − π(n) is Poisson(λ) for n ≤ X.
The same factorial-moment proof for consecutive intervals of lengths λ_i log X gives independent Poisson(λ_i)
(needs Σ𝔖 over a product of boxes ~ volume; this is the step I did not write out). Then, with θ = 2^J/ln X ∈ [1,2):
 density{N ∈ [X,2X] : L(N) > J + r} → F(θ, r) = Π_{i ≤ r} (1 + e^{−θ2^i})/2,  and c₁2^{−r} ≤ F ≤ c₂2^{−r}
 (numerically c₁ ≥ 0.24, c₂ ≤ 1.16 for θ ∈ [1,2)).
Consequences under this hypothesis:
 - L(N) ≤ log2 log N + ω(N) for a density-1 set of N, any ω → ∞;
 - for each fixed r a positive proportion (≥ c₁2^{−r}) of N has L(N) > log2 log N + r, so the tail is truly geometric
   and nothing better than "almost all" holds at scale log2 log N + O(1).
 This is algorithmically EMPTY: for those N the interval [N, N + 2^ω log N] is short enough to scan. Parity queries
 only matter for the exceptional N, and averaged hypotheses say nothing about them. RH alone gives no parity
 statement at all (even equidistribution of π(n) mod 2 is open).
 Refuting PR rigorously along these lines would need HL uniform in k up to (log N)^{C log log N}; far out of reach. [C]

**(b) Every N: impossible from robust hypotheses.** [R, corollary of p1 Thm 2 / p3 Thm 1′ / w2 Prop G]
Any PR-type statement "for every N, one of Q prescribed cheap sets in [N,2N] has an odd number of primes" is false
for S = P minus ≤ Q+2 suitable primes. GRH-type error terms (≥ √N), Montgomery pair correlation, the
Goldston–Montgomery variance asymptotic and HL asymptotics (any error term ≫ Q) hold for S as well as for P. So no
proof can use them as the only arithmetic input, whatever the family, as long as Q < √N/polylog. I therefore did
not attempt a GRH + pair-correlation proof: it cannot exist in that form. A proof needs an input that changes when
one prime is deleted.

### 2.4 Corrected conjecture PR* [C]

n = ⌈log2 N⌉, L = n³, K = n². **PR\*: for every N ≥ N₀ some i ≤ K has π([N+(i−1)L, N+iL)) odd.**
- Heuristic failure probability 2^{−n²}(1+o(1)) per N; summable, so in the Cramér model PR* holds for all large N.
  Any K ≥ (1+ε)n suffices heuristically; K ≤ n − log2 n − O(1) fails infinitely often.
- PR* + parity engine (Theorem B) ⇒ deterministic prime in [N, N+n⁵) in n² + O(log n) engine calls, N^{o(1)} time.
- A 2-D family (starts y = N + tL, t < K; lengths 2^j) has the same content: it fails iff K·(n − log2 L) disjoint
  blocks are all even [R, telescoping]. With L = 1 it degenerates to scanning: failure forces p + 2^j prime for all
  j, impossible, but K must exceed the gap.
- [N] `prstar.py 29 256`: L = 256, every N in [2^k, 2^{k+1}), 12 ≤ k ≤ 27: the worst N needs i = k − 2 ± 3 blocks
  (max 27 at k = 24); no N needs more than 2k. So the threshold K ≈ log2 N is visible, and K = 2 log2 N is safe in
  the tested range.
- PR* is exactly as unprovable as PR (2.3b). Its value: it is the statement that is not contradicted by the model.
- Using π mod M (p2: M up to exp(o(√log log N))) replaces coins by M-sided dice: K ≥ (1+ε) n/log2 M. Same status.

## 3. Task 3: angles outside the basin (each ≤ 15 min, all dead)

**3.1 Weighted parity with a zero-sum kernel.** Σ_{p∈I} w(p) mod 2 with w from a truncated zero sum (or from the RH
proof's ramp second difference) is still GF(2)-linear in 1_P. p2's syndrome adversary applies verbatim: "all even"
is consistent after ≤ Q deletions. Concentrating the signal changes the bias of each coin, not the worst case.
Dead by theorem [R].

**3.2 Möbius-factorial isolation of a window (rigid, exact).** For p ≡ 2 mod 3 and χ = (·/3): every integer k has
[χ(k′) = −1] ≡ Ω₋(k) mod 2 (k′ = 3-free part, Ω₋ = number of prime factors ≡ 2 mod 3 with multiplicity). Sum over
k ≤ n/d and over squarefree d ≤ D, using Σ_{d≤D} μ(d)⌊t/d⌋ = 1 for 1 ≤ t < D and μ ≡ μ² mod 2:
 R(n,D) := Σ_{d≤D sqfree} #{k ≤ n/d : k′ ≡ 2 (3)} ≡ #{p ∈ (n/D, n], p ≡ 2 (3)} + Cont(n,D)  (mod 2),
 Cont = Σ over prime powers p^i with p ≡ 2 (3) and (p ≤ n/D or i ≥ 2) of #{(d,k): d ≤ D sqfree, dk ≤ n/p^i}. [R]
The window (n/D, n] is isolated with weight exactly 1 (this fixes p1's "mass at all scales" for the top window), but:
 - every term is already an engine count, so the identity is 0 = 0 for the engine: it certifies nothing;
 - used without the engine, the contamination needs the primes ≤ n/D: cost D + n/D ≥ 2√n.
 A rigid identity between cheap counts cannot force an odd window; it only relates the window parity to another
 unknown parity. Same conclusion as p2 §5.2, now with exact isolation. Dead [R].

**3.3 π(I) mod 2^e with e ≈ n/2 (modulus above the threshold M\* = √N).** p2: mod k needs c ≡ −1 mod k² with small
sopfr(c). For k = 2^e take c = Π p_i^{a_i} over the first r primes: a short vector in the relation lattice
(determinant 2^{2e−1}) has Σa_i ≈ r·2^{2e/r}; with r ≈ e, sopfr(c) = O(e² log e) [C, lattice heuristic]. Cut
O(n·e² log e), so N^{o(1)} only for e = o((log n)^{1/4}); e = n/2 costs 2^{Ω(n³)}. Dead.

**3.4 Nonlinear pattern parities (p2's twin/k-tuple counts).** An odd twin count in I also bisects to a prime, so
these are extra coins. But the truth for P is one consistent answer set and deleting isolated primes does not
change pattern counts, so no rigidity is gained; heuristically they add O(1) independent coins per query. Not
proved to be covered by the barrier (quadratic syndromes), not a route either. [C]

## 4. What I would do next

- Replace PR by PR* everywhere (p3 notebook §4, any write-up): PR as stated is contradicted by the model and by
  124 explicit N < 2^30 in its strongest form (j ≤ log2 N).
- If the team wants a conditional theorem: "PR* ⇒ prime in [N, N+log^5 N) in N^{o(1)}" is honest and clean; the
  hypothesis is a Borel–Cantelli-safe parity statement.
- The only non-robust inputs seen so far are exact identities, and §3.2 shows the best one still costs D + n/D.
  I see no further angle worth a time-box from my side.
