# mr2 notebook: deterministic Miller-Rabin under GRH

GRH is taken as proven (lead's instruction); every use is marked "under GRH".
n = odd composite, w(n) = least strong-pseudoprime witness, log = ln. Tags [R]/[K]/[N]/[C].
Files: literature.md (prior art), leastwit.c + leastwit_1e10.out (numerics), kernel_opt.py / kernel_scan.py /
kernels.json / certify.py / certify.out (constants), check_cases.py (structural lemma), smooth_check.py.

## 0. Summary

| # | statement | tag |
|---|---|---|
| A | **Under GRH: w(n) <= (0.2919 + o(1)) log^2 n** for all odd composite n (explicit Gamma kernel); **0.2706** with a numerically optimised kernel. Previous: Bach 2 log^2 n; LLS => log^2 n explicit, (0.794+o(1)) log^2 n asymptotic. | [R] modulo [K] LLS Lemma 6.1; constants [N] |
| A' | Under GRH: w(n) <= (0.1984 + o(1)) log^2 n (0.191 with optimised kernel) unless n = pqr is a Carmichael number with v2(p-1)=v2(q-1)=v2(r-1) (exactly the Burthe/Balasubramanian-Nagaraj exceptional family). | same |
| S | **Unconditional**: if p^2 \| n, or n has a prime factor q > n^{2/3}, then w(n) <= (e^{-2}+o(1)) log^2 d with d = p^2 resp. q (e^{-2} = 0.1353). For q >= n^theta, theta > 2/3: w(n) < (log q)^{theta/(2 theta - 1)} = o(log^2 n). In particular least a with a^{p-1} != 1 mod p^2 is <= (4e^{-2}+o(1)) log^2 p = 0.541 log^2 p (Lenstra 1979: 4 log^2 p). | [R] (novelty of the constant not checked beyond a quick search) |
| E | w(n) < log^2 n for EVERY odd composite n (GRH): LLS Thm 1.1(2) for n >= 3000 + table below 3000. | [K]+[N], trivial corollary |
| N | Exhaustive n <= 10^10: w(n) in {2,3,5,7,11}; max w/log^2 n = 0.414 (n=9), and 0.0516 for n >= 1000 (n=2047); records = psi_1..psi_4. | [N] |
| 3 | o(log^2 n) bases: trivially yes (prime bases only: ~0.146 log^2 n / loglog n bases). (log n)^{2-delta} bases or O~(log^3 n): equivalent to beating the Ankeny/GRH barrier for the least prime outside a subgroup; open. | [K]/[C] |

## 1. Structural lemma  [R], brute-force checked for all n < 60000 [N] (check_cases.py)

Let a be a strong liar for n (so (a,n)=1).
- (F1) a^{n-1} = 1 mod n, hence for each prime p | n with p^e || n, ord(a mod p^e) divides gcd(n-1, p^{e-1}(p-1)) = g_p := gcd(n-1,p-1).
  So a mod p^e lies in the subgroup H_p of order g_p, index h_p = p^{e-1}(p-1)/g_p.
  If p || n and m = n/p then n-1 = m(p-1)+(m-1), so g_p = gcd(m-1,p-1) <= m-1.
- (F2) v2(ord_p(a)) is the same for all primes p | n. (If a^d = 1 all orders are odd; if a^{2^i d} = -1 mod n then v2(ord_p a) = i+1 for every p.)

Case tree (q = largest prime factor, m = n/q):
- (N) p^2 | n: liars satisfy a^{p-1} = 1 mod p^2; H = that subgroup of (Z/p^2)^*, |H| = p-1 < sqrt(p^2).
- (Q1) n squarefree, q > m^2 (q > n^{2/3}): liars mod q lie in H_q, |H_q| <= m-1 < sqrt(q).
- (Q2) squarefree, m < q <= m^2 (n^{1/2} < q <= n^{2/3}): H_q has index h_q >= (q-1)/(m-1) >= max(2, q^2/n); conductor q.
- (Q3a) squarefree, q < m (all primes < sqrt n), some p with (p-1) not dividing n-1: H_p of index >= 2, conductor p < sqrt n.
- (Q3b) Carmichael (Korselt), k >= 3 primes, all < sqrt n. Let e_p = v2(p-1).
  - not all e_p equal: take p with e_p > min; by (F2) every liar is a square mod p: index 2, conductor p < sqrt n.
  - all e_p equal: by (F2) the Legendre symbols (a/p), p | n, are all equal for a liar.
    k >= 4: use the two smallest primes: character (./p1p2), conductor p1p2 <= n^{2/k} <= sqrt n.
    k = 3: H = {a : (a/p1)=(a/p2)=(a/p3)}, index 4; the three non-trivial characters trivial on H are
    (./p1p2), (./p1p3), (./p2p3), with conductors whose logs add up to **2 log n** (not 3 log n).
In every case the least prime outside H (primes dividing n are witnesses anyway) is a witness.
NB: the liars themselves are not a group; only containment in H is used.

## 2. Method G (GRH, LLS kernels with conductor weights)

[K] LLS Lemma 6.1 (arXiv:1309.3595v3), read in the form its proof gives: for chi mod q non-principal induced by a
primitive character of conductor q~, and an admissible kernel K,
 Re sum_n Lambda(n) chi(n) n^{-1/2} K~(n/x) <= (1+o(1)) (log q~ / 2pi) int |K(it)| dt + O(1 + log q log x / sqrt x),
and for the principal character the sum is K(1/2) sqrt x + O(1 + log q log x / sqrt x).
(The statement of the lemma has log q; the last display of its proof has log q~. This is the only place where I rely
on the inside of their proof. In the k=3 Carmichael case all three conductors are >= sqrt n -> infinity.)

Normalisation: g(t) := K~(lambda e^t) >= 0,  P = int_{t<=0} g e^{t/2} dt, Q = int_{t>0} g e^{t/2} dt,
C = (1/2pi) int |ghat|.  (LLS: A = sqrt(lambda) P, B = sqrt(lambda)(P+Q).)

**Prop G** [R given the [K] lemma; same proof as LLS Prop 6.1]. Under GRH, let H be a subgroup of (Z/N)^* of index h,
H^ its dual (characters trivial on H), and suppose all primes l <= X, l not dividing N, lie in H. Then
 ((h-1) P - Q) sqrt X <= (1+o(1)) C * Sigma,   Sigma := sum_{chi in H^, chi != 1} log cond(chi).
Proof: sum over chi in H^ of the lemma at x = X/lambda; sum_chi chi = h 1_H >= 0 and K~ >= 0, so the left side is
>= h sum_{n<=X} Lambda(n) n^{-1/2} K~(n/x) + o(h log N) = h sqrt(x) sqrt(lambda) P + o(h log N). QED.
LLS use Sigma <= (h-1) log q. The new input is only that for Miller-Rabin Sigma is much smaller than (h-1) log n.

Define alpha_K(h) = (C (h-1)/((h-1)P-Q))^2 (LLS's alpha(h)), alpha_K(inf) = (C/P)^2 and R_4 = (3P-Q)/C.
Since Q >= 0, alpha_K(h) <= alpha_K(2) for all h >= 2 with the same kernel (uniform in h).

Constants [N] (certify.py -> certify.out; mpmath for the Gamma kernel, fine quadrature + tail bound for splines):

| kernel | alpha(2) | alpha(2)/4 | Carm3: 4/R_4^2 | alpha(inf) | alpha(inf)*4/9 |
|---|---|---|---|---|---|
| Gamma(s+1/2) (LLS 6.3), C = 0.4708878 | 0.79342 (lam 2.477) | 0.19836 | **0.29183** (lam 1.824) | 0.54445 | 0.24198 |
| triangle (LLS 6.2), half-width 2*10 | - | - | - | 0.30864 | 0.13717 |
| optimised linear splines (kernels.json) | 0.7634 | 0.1908 | **0.2706** | 0.3250 | 0.1444 |
| limit of Prop G (LLS 6.1 argument) | 1/4 | 1/16 | 1/9 | 1/4 | 1/9 |

Spline kernels are compactly supported piecewise-linear g >= 0, so K is entire, |K(s)| << 1/(1+|s|^2) in the strip,
K~ >= 0 (LLS's own triangle kernel is of this type). Their constants are [N] (double precision quadrature of |ghat| on
[0,4000] step 0.002 plus the rigorous tail sum|slope jumps|/T), not interval-arithmetic certified.

## 3. Method S (smooth numbers; unconditional)  [R]

**Lemma S.** Let H be a subgroup of (Z/d)^* with |H| < sqrt d and suppose every prime l <= X lies in H mod d.
Then X < (e^{-2}+o(1)) log^2 d (d -> infinity), and X < d always.
Proof. The X-smooth integers in [1,d) are distinct residues and lie in H, so Psi(d,X) <= |H| < sqrt d (if X >= d this
already fails since Psi(d,X) = d-1). Products of at most u = floor(log d/log X) primes <= X are <= d, so
Psi(d,X) >= binom(pi(X)+u,u) >= ((pi(X)+u) e/u)^u / (e sqrt u). With X = c L^2, L = log d: pi(X)/u >= X/L = cL, hence
log Psi >= (L/log X - 1)(1 + log c + log L) - O(log L) = (L/2)(1 + (1 + (1/2) log c)/(log L + (1/2) log c)) - O(log L),
which exceeds L/2 for large L as soon as 1 + (1/2) log c > 0, i.e. c > e^{-2}. QED
(smooth_check.py: margin log binom - L/2 is positive for c=0.25 from L ~ 100, for c=0.15 from L ~ 300.) [N]
Remarks. (i) [K] Konyagin-Pomerance Thm 2.1 (Psi(x, log^A x) > x^{1-1/A}) gives the explicit X < log^2 d, and
X < (log d)^{1/(1-beta)} when |H| <= d^beta, beta < 1/2. (ii) [C] With the Hildebrand-Tenenbaum saddle-point
formula the constant e^{-2} should improve to 1/(4e^2) = 0.0338 (heuristic computation: log Psi(x, c log^2 x) =
(L/2)(1 + (1+log(2 sqrt c))/log L + ...)); not written out.
Applications: (N) d = p^2; (Q1) d = q. For bounded d the witness is < d = O(1).

## 4. Theorem A  [R modulo the [K] lemma; constants [N]]

**Theorem A (under GRH).** For odd composite n -> infinity,
 w(n) <= (c0 + o(1)) log^2 n,  c0 = max( 4/R_4^2 , alpha(2)/4 , (4/9) alpha(inf) , e^{-2} ),
where the three analytic constants may be taken from (possibly different) admissible kernels. Hence
c0 = 0.2919 (Gamma kernel for the first two, triangle kernel for the third), and c0 = 0.2706 with the optimised
spline kernel. The maximum is attained only in the case "Carmichael n = pqr with equal v2(p-1)"; for all other n
 w(n) <= (max(alpha(2)/4, (4/9)alpha(inf), e^{-2}) + o(1)) log^2 n = (0.1984+o(1)) log^2 n   (Theorem A').

Proof (case tree of Section 1; fix eps > 0).
- (N), (Q1): Lemma S: w(n) <= max(O_eps(1), (e^{-2}+eps) log^2 n).
- (Q2): Prop G with N = q prime, H = H_q, all non-trivial characters of conductor q: X <= (1+o(1)) alpha_K(h_q) log^2 q.
  If q <= n^{1/2+eps}: use alpha_K(h) <= alpha_K(2): X <= (alpha(2)+o(1)) (1/2+eps)^2 log^2 n.
  If n^{1/2+eps} < q <= n^{2/3}: h_q >= q^2/n >= n^{2 eps} -> infinity, so for a fixed kernel
  alpha_K(h_q) -> alpha_K(inf): X <= (alpha(inf)+o(1)) (4/9) log^2 n.  (q > sqrt n -> infinity, so o(1) is legitimate.)
- (Q3a), Carmichael with unequal v2, Carmichael k >= 4 with equal v2: index 2, conductor f <= sqrt n:
  X <= (alpha(2)+eps) log^2 f + O_eps(1) <= (alpha(2)/4 + eps) log^2 n + O_eps(1).
- Carmichael k = 3, equal v2: Prop G with N = n, h = 4, Sigma = 2 log n: sqrt X <= (1+o(1)) (2/R_4) log n. QED

Why this is not in LLS/Bach: they bound "least prime outside H mod q" in terms of log q with q = modulus. For
Miller-Rabin the modulus n is not the relevant conductor: Korselt-type divisibility forces either a subgroup of small
conductor (<= sqrt n), or of huge index with conductor <= n^{2/3}, or a tiny liar group (then smooth numbers
finish, no GRH). LLS do not discuss Miller-Rabin at all (literature.md).

Limits of the method. With ideal kernels Prop G gives 1/9 (Carm3), 1/16, 1/9 -> c0 >= 1/9 + ; the S-part is
0.135 (0.034 heuristically). So this route cannot go below ~0.11-0.135; the realistic gain left is 0.27 -> ~0.2 by
better kernels for the h=4 problem (the spline optimum 3.845 for R_4 seems to be the true optimum of
sup (3P-Q)/C over g >= 0: three discretisations agree to 0.2%).

Not done (honest gaps):
1. No fully explicit version with c < 1 for all n beyond statement E (c = 1). An explicit c ~ 4/9 looks feasible
   (LLS Thm 1.1 with the conductors of Section 1 gives ((2/3) log n + O(loglog n))^2 in cases Q2/Q3; cases N/Q1
   need an explicit Lemma S with constant < 1, i.e. a numerical verification of the binomial inequality) - not written.
2. Spline constants are not interval-certified; the Gamma-kernel constants are (mpmath, 30 digits).
3. Lemma 6.1 with log q~ is taken from the proof text of LLS, not re-derived.

## 5. Task 3: fewer bases / O~(log^3)   (verdict: equivalent to a known hard problem; stopped)

- [R] trivial: liar-containing H is a group, so only PRIME bases are needed: under GRH pi(0.292 log^2 n) ~
  0.146 log^2 n / loglog n bases. That is o(log^2 n) bases, cost O~(log^4 n) still (O~ hides the loglog).
- (log n)^{2-delta} bases via characters = a bound o(log^2 q) for the least prime outside an index-2 subgroup of
  conductor q ~ sqrt n (family n = p(2p-1), where the liars are cut out by a quadratic/quartic character mod 2p-1).
  Under GRH the explicit-formula method is stuck at (1/4) log^2 q (LLS Sec 6.1); o(log^2 q) for the least quadratic
  non-residue under GRH alone is a classical open problem (needs information on zero spacings). [K]
- A single fixed test cannot work: for any fixed base set there are infinitely many Carmichael numbers that are
  strong pseudoprimes to all of them (AGP 1994), and for any fixed monic squarefree f infinitely many Frobenius
  pseudoprimes (Grantham 2001). [K] So parameters must depend on n, and derandomising the choice again needs
  "least element outside a proper subgroup" (now of (O_K/n)^*), i.e. the same log^2 barrier.
- What Lemma S adds [R]: the number of bases is (log n)^{A}, A = theta/(2 theta-1) < 2, unconditionally, when n has a
  prime factor n^theta, theta > 2/3, or the liar group has size <= n^{beta}, beta < 1/2. A test with provably small
  liar groups (|L| <= |G|^{1/2-delta}) for ALL composites would give (log n)^{2-delta'} trials without GRH; for
  Miller-Rabin and quadratic Frobenius the worst composites have |L| >= c|G|, so this needs a different test. [C]
- O~(log^3 n) total: no route found; multi-exponentiation does not share work between bases. Stopped.

## 6. Numerics  [N]  (leastwit.c, 4 threads, 12.7 CPU-min; leastwit_1e10.out)

All odd composite n <= 10^10 (sieve + Montgomery strong test; 3291 spsp(2) found, matches the known count).

| w(n) | # n <= 10^10 | first n | w/log^2 n |
|---|---|---|---|
| 2 | 4544944198 | 9 | 0.4143 |
| 3 | 3158 | 2047 = 23*89 | 0.0516 |
| 5 | 125 | 1373653 = 829*1657 | 0.0250 |
| 7 | 7 | 25326001 = 2251*11251 | 0.0241 |
| 11 | 1 | 3215031751 = 151*751*28351 | 0.0230 |

max over each decade of w/log^2 n: 0.414 (9), 0.273 (15), 0.092 (105), 0.0516 (2047), 0.0321 (15841), 0.0225
(104653), 0.0250, 0.0241, 0.0196 (161304001), 0.0230. Beyond 10^10 the known psi_5..psi_13 give 0.0135-0.0205
(literature.md). Comparison: Theorem A allows 0.27-0.29, Bach 2, LLS 1 / 0.794; reality ~0.02 and decreasing,
consistent with the Bach-Huelsbergen heuristic log n loglog n / log 2. The theorem is still ~13x from the data.
The first three record holders are of type (Q2)/(Q3a) with q = 4p-3, 2p-1, 5p-4 (bounded index h_q), i.e. the
alpha(2)/4-type cases; psi_4 is a 3-prime Carmichael number.

## 7. Idea log
1. Use LLS as a black box with modulus n -> c = 0.794 (asymptotic), 1 (explicit). Known corollary; baseline.
2. Conductor reduction via Fermat condition (F1) -> works, cases Q2/Q3a. KEPT.
3. Conductor-weighted Prop G for the Jacobi-character family of Carmichael numbers -> 0.353 -> 0.292 -> 0.271. KEPT.
4. Smooth-number counting when the liar group is < sqrt(d) -> unconditional e^{-2}. KEPT. (HT refinement: [C].)
5. Non-subgroup positivity (weights a chi12 + b chi13 + c chi23, sign-sensitive F+-): linear-fractional in the weights,
   optimum at the vertices already used. DEAD.
6. Averaging over all characters of the Fermat-liar group F with D = sum (1-1/h_p) log p: never better than the best
   single prime. DEAD (kept as a remark).
