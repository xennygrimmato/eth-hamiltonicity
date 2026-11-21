# p4 notebook: subtask 4 (what RH actually buys) and subtask 8 (literature)

Literature is in `literature.md`. Scripts are in this folder (`degG.py`, `zeros_res.py`). "Under RH" is now
unconditional if the Alpöge+Claude proof stands. Its Lean statement matches Mathlib's RH for ζ only; GRH is not
certified (literature.md §4).

## 0. Verdicts (short)

1. **RH alone gives exactly √x.**
   * Cramér/CMS: a prime in (x − 0.88√x log x, x].
   * Schoenfeld: |π − li| < √x log x/(8π).
   * Selberg: primes in almost all intervals of length ≫ log² x. This is a measure statement and is useless
     deterministically.
   * Montgomery's F(α), |α| ≤ 1, becomes unconditional. The pair-correlation *conjecture* does not, so the
     gap improvements to o(√x log x) stay conditional.
   * No RH consequence is known to localise a prime in an explicit interval shorter than ~√x log x. [K]
2. **A truncated explicit formula cannot beat √x for finding (§3).**
   * Certifying a prime in a window of length h needs the zero sum up to height T ≳ x/h, evaluated *with its
     cancellation*.
   * Bounding the sum term by term (all zeros on the line) only gives h ≳ √x log x, i.e. Cramér again. [R]
   * Evaluating it costs at least the number of terms, about (x/h) log x, in every known representation:
     zeros, contour integral via Odlyzko–Schönhage, or the dual prime sum. So the total is x/h + h ≥ 2√x.
     [K]+[C] (not a lower-bound theorem, but no sublinear method is known for any representation).
   * The experiment at x = 10^6 with 300 zeros (§3.3) shows the observed error of the smoothed sum is far below
     the rigorous √x log T bound. The cancellation is real but unusable without computing the sum.
3. **Hybrids of analytic accuracy and engine residues gain nothing (§4).**
   * Residues mod M decide a count exactly only once the analytic error is < M/2. LO accuracy E costs x/E,
     so the hybrid costs x/M = x^{1−o(1)}.
   * Selberg's almost-all statement plus exact engine tests of windows of length H₀ fails against an
     adversarial exceptional set.
   * The "stretch" version (average over a stretch of length L) needs L ≳ √x log x. This is Cramér's argument,
     and it is sharp for RH-only reasoning.
4. **The AP-parity family is worth exactly Θ(Q²) bits (§2).** [R]+[N]
   * The AP parities π(I;a,q) mod 2, q ≤ Q, vanish for all a, q iff V_I(t) := Σ_{p∈I} t^p ≡ 0 mod
     G_Q = lcm_{q≤Q}(t^q − 1) over F₂.
   * deg G_Q = Σ_{d≤Q odd} φ(d)·2^{⌊log₂(Q/d)⌋} ≈ 0.304 Q² ≈ (3/π²) Q², computed for Q = 10..10⁴.
   * So these parities pin down the prime indicator only on intervals of length ≤ 0.304 Q², using ~Q²/2
     queries. There is no compression versus scanning. TCH's "Goal 1" fails for APs by pure linear algebra.
5. **Best lead found: Polymath4 Problem 1 has both its hypotheses satisfied now (§5).**
   * The problem asks for a prime with ≥ k digits in o(√n) time, assuming RH, with a factoring oracle.
   * We now have RH (claimed) and deterministic N^{o(1)} factoring (RR26/TulFac26). The problem is still open.
   * For primes *in [N,2N]* via factoring, every equidistribution argument I tried stops at N^{1/2+ε}, even
     under the exponent-pair conjecture. This is a square-root-cancellation barrier.
   * The *weak* goal (any prime ≥ u) via Polymath Strategy C has a conditional u^{0.4} route: an integer
     with a factor near u lies within O(u^{0.4}) of n ~ u², assuming an exponential-sum estimate.
   * It still needs the factor to be *prime*. Open.

## 1. RH catalogue: what becomes available and what it does for locating primes

| statement (now unconditional) | source | can it locate primes below √x? |
|---|---|---|
| π(x) = li(x) + O(√x log x), explicit < √x log x/(8π) (x ≥ 2657) | von Koch, Schoenfeld 1976 | No. Gives π in a window of length √x log x for free. A residue mod M does not combine with it (§4). |
| ψ(x) = x + O(√x log² x), explicit /(8π) (x ≥ 73.2) | Schoenfeld | same |
| gap ≤ (22/25)√x log x (x ≥ 4) | CMS 2019 | This is exactly the √x scan. Not polylog. RH cannot give o(√x log x) without extra input (pair correlation, still conjectural). |
| explicit formula ψ(x) = x − Σ_ρ x^ρ/ρ − log 2π − ½log(1−x^{−2}), all |x^ρ| = √x | Riemann–von Mangoldt | Only if the zero sum up to T ≈ x/h is *evaluated*, at cost ≥ T (§3). |
| almost all [x, x+h], h/log² x → ∞, contain ~h/log x primes; exceptional measure ≪ X log² X/h | Selberg 1943 | Not deterministically (§4b). |
| Montgomery F(α) for |α| ≤ 1; ≥ 2/3 simple zeros | Montgomery 1973 | No algorithmic content known. The full pair-correlation conjecture is NOT implied by RH. |
| zero-density: N(σ,T) = 0 for σ > 1/2 | — | Makes every density-based short-interval result (Huxley, Guth–Maynard) moot. RH is stronger, but still only at √x. |
| Landau–Gonek Σ_{0<γ≤T} x^ρ = −TΛ(x)/2π + O(x log(xT) log log x) | Gonek 1993 | Detects prime powers via zeros, but only for T ≫ x log x. |
| LO/Platt/Büthe with explicit constants | literature.md §2 | x^{1/2+o(1)}. RH gives slightly better constants; the exponent is unchanged. |
| Lindelöf, so ζ(1/2+it) ≪ t^ε | (RH ⇒ LH) | Speeds up nothing in LO, whose cost is the number of samples, not the size of ζ. |
| bounds on M(x), Mertens: O(√x exp(log^{1/2+ε} x)) | (RH) | Analogue for μ; same √x scale. |
| GRH (NOT certified): Miller test, Bach's non-residue bound, least prime in AP ≪ q^{2+ε} | — | Least prime in AP mod q ≈ x^{1/2} gives a prime ~ x in an explicit AP. Scanning the AP costs x/q·… ≥ √x. Nothing better. |

## 2. How much information is in the AP parities? (feeds subtasks 2, 3, 6, 7) [R] + [N]

Setting: I = [a, a+H), v ∈ F₂^H the prime indicator, V(t) = Σ_{n∈I} v_n t^{n−a}. Then #{p ∈ I : p ≡ r mod q} mod 2,
for all r, is V mod (t^q − 1) over F₂ (Tao's remark, Thread V).

**Claim.** All AP parities with modulus ≤ Q vanish iff G_Q | V, where G_Q = lcm_{q≤Q}(t^q − 1). Over F₂,
t^q − 1 = (t^{q'} − 1)^{2^e} for q = 2^e q', q' odd. Hence G_Q = Π_{d≤Q odd} Φ_d^{2^{⌊log₂(Q/d)⌋}}. Since deg V < H:

* if H ≤ deg G_Q, the parities determine v completely;
* if H > deg G_Q, there is a (H − deg G_Q)-dimensional space of indicators with all parities even.

**Numbers** (`degG.py`): deg G_Q / Q² = 0.320, 0.3044, 0.30419, 0.30397 for Q = 10, 10², 10³, 10⁴, so ≈ 3/π².

**Consequences.**
* (i) AP parities resolve an interval of length H only when Q ≳ 1.8√H. That is Θ(H) queries, the same as testing
  each integer.
* (ii) An adversary argument against an odd AP must use more than linear algebra: v must also look like primes. Tao's
  heuristic says 2^{H−0.3Q²} candidate sets exist, and nothing proven about the primes excludes them.
* (iii) The same count applies to TCH's general P mod (2,g): the family {g : deg g ≤ D} has lcm of degree ≈ 2^{D+1}.
  So polynomial moduli of degree D are worth about 2^D bits, which is again linear in the number of queries.
* (iv) Shifts and dilations (P(t^j) mod g) are equivalent to APs with other moduli. They give nothing new.

The only way out of the linear-algebra bound is a *nonlinear* constraint on v that the primes are proven to satisfy.
RH gives exactly one kind: counts in windows ≥ √x log x are positive, plus mean-square statements. Those act only at
scale √x.

## 3. Can a truncated explicit-formula sum be evaluated fast and give π on short intervals?

### 3.1 Uncertainty principle [R]

Take g with ĝ supported in [−T, T]. The explicit formula
`Σ_n Λ(n) g(log n − log x)·(n/x)^{1/2} = (main) − Σ_γ ĝ(γ) x^{iγ} + (small)`
is an exact Fourier duality. The zero side with |γ| ≤ T carries prime information only at resolution Δlog n ≈ 1/T,
i.e. windows of length x/T. So π on a window of length h needs T ≳ x/h, i.e. about (x/h)(log x)/2π zeros.

### 3.2 Term-by-term bounds give only Cramér [R]

With a smooth bump φ of width h at y, π_φ(y) = Σ Λ(n) φ((n−y)/h) = h φ̂(0) − Σ_ρ (stuff). Under RH each zero
contributes ≤ √y·(h/y)·|φ̂(γh/y)|. Summing over N(y/h) ≈ (y/h) log y zeros gives an error ≲ √y log y. The main term is
h, so certification needs h ≳ √y log y. Every RH-only bound that ignores the phases of x^{iγ} is stuck here.

Similarly the Fejér-weighted truncation ψ_T(y) = y − 2Re Σ_{γ≤T} (1 − γ/T) y^ρ/ρ has rigorous error ≥
(√y/T)·N(T) ≈ √y log T/(2π) from the weights alone, plus the sharp-cutoff tail.

### 3.3 Experiment (`zeros_res.py`, 300 zeros, T = 541.8, x = 10^6, √x = 1000) [N]

| T | rms error ψ_T − ψ on [10^6, 10^6 + 2·10^4] | max error | x/T |
|---|---|---|---|
| 50 | 127.7 | 342.7 | 20000 |
| 200 | 76.7 | 207.1 | 5000 |
| 542 | 59.3 | 161.3 | 1846 |

The observed error is far below the rigorous √x log T/(2π) ≈ 1000. The phases do cancel, roughly √N(T) instead of
N(T). But certifying the cancellation requires computing the sum, at cost ≥ N(T) ≈ (x/h) log x.

### 3.4 Can the sum be evaluated in time sublinear in its length? [K]+[C]

Known representations of the same number:

* (a) The zero sum. It needs all zeros up to T; Odlyzko–Schönhage gives T^{1+o(1)}. A single evaluation is a
  non-uniform exponential sum Σ_γ c_γ e^{iγ log x}. No fast single-point method is known, because the zeros have no
  known algebraic structure.
* (b) LO's contour integral. Quadrature with step Δ aliases the prime sum with period 2π/Δ in log n, so Δ ≲ 1/log x.
  That means T log x samples of ζ'/ζ, amortised by Odlyzko–Schönhage to T^{1+o(1)}. Fast single-value ζ algorithms
  (Hiary t^{1/3}, t^{4/13}) are slower per sample than this amortisation.
* (c) The dual prime sum over a window of length x/T (sieve, or HKM elementary √x).

All three cost ≈ T or x/T. Choosing T is the LO balance, giving 2√x. Our engine could replace (c) only if it computed
*real-weighted* sums Σ_{p∈W} w(p) exactly. It computes integer-weighted counts mod M, and exact counts only on
|I| ≤ H₀. So no. Hence the answer to the brief's question is **no**: not by any known method, and any method would be
a sub-√x algorithm for smoothed π(x), which is the open problem itself.

## 4. Hybrids: RH information plus engine residues

**(a) Residue + analytic bound.**
* If π(J) ∈ [A − E, A + E] is known and π(J) mod M is known with 2E < M, then π(J) is known exactly.
* With RH for free, E ≈ √x log x, which forces M ≥ √x. The engine only reaches M = x^{o(1)}.
* With LO, E costs x/E, so the hybrid costs x/M = x^{1−o(1)}.
* Window-search variant (prime-finding.md §3(d)): engine queries cost C_E = 2^{Θ(n/√log n)}, while the residue gain is
  ≤ log M = 2^{o(√log n)} bits. Any gain must be a power of x, and residues never provide one.

**(b) Selberg almost-all + exact tests of windows of length H₀.**
* The fraction of bad windows is ≪ log² x/H₀ → 0, but the bad set is adversarial for a fixed deterministic list.
* With a stretch of K consecutive windows, the zeros with γ < x/L (L = K H₀) are coherent across the stretch.
  Their contribution √x log x·h/L must be < h, which forces L ≳ √x log x.
* So a deterministic guarantee needs ≳ √x log x/H₀ queries, each costing C_E ≫ H₀. That is worse than scanning.
* This is Cramér's argument and is sharp for RH-only inputs.

**(c) Parity of large sets via RH?** π([N,2N]) mod 2 is a fixed bit. RH gives π([N,2N]) only to ±√N log N, so it says
nothing about parity. A deterministic odd interval must come from arithmetic, not analysis.

## 5. Factoring-oracle route (Polymath4 Thread III, Problem 1) [K] + [C]

Problem 1 (13 Aug 2009): with a factoring oracle and assuming RH, find a prime with ≥ k digits in o(√n) time. In our
world both hypotheses hold. Deterministic factoring is N^{o(1)}: parity-note cites Rudich–Rousseau and TulFac26.
Reduction: a prime ≥ u can be found if we can explicitly list o(√u) integers m ≤ u^{O(1)}, one of which has
P^+(m) ≥ u.

* **Short intervals.** We need every [x, x + x^θ] to contain m with P^+(m) > x^{f}, with θ/f < 1/2. Known: θ = 1/2
  gives f = 0.7437 (Baker–Harman and later); θ = 1/2+ε gives f = 51/53 (R. Li, preprint). The ratio is ≥ 1/2 in all
  known cases. For small θ, the Chebyshev-type argument needs
  Σ_{p≤u} log p·(ψ(x/p) − ψ((x+y)/p)) = o(y log x).
  * At x = u² this is a divisor-problem sum. Bourgain–Watt give an exponent of 0.3137 for Σ_{n≤√x} ψ(x/n), so
    y ≥ x^{0.314} = u^{0.627}. To get o(√u) one needs exponent < 1/4 for x = u², i.e. *better than the exponent-pair
    conjecture*.
  * Polymath's O(u^{0.4}) for n ~ u² concerns a *factor* near u, not a prime, assumes a strong exp-sum estimate, and
    exploits divisor (bilinear) structure that primes lack.
* **For [N,2N] specifically.** Look in (N², N² + y] for m = kp with p ∈ [N, 2N]. The expected number of hits is
  y log 2/log N. Proving one exists needs the discrepancy of {N²/p}, p ∈ [N,2N]:
  * second-derivative test: N^{2/3};
  * exponent pairs: about N^{0.63};
  * even the exponent-pair conjecture (square-root cancellation) only gives y ≳ N^{1/2+ε}.
  Larger x = N^A makes it worse. **Square-root cancellation over ~N/log N primes is the barrier**: any
  "asymptotic count, then existence" argument over a family of N candidates has an error ≥ √N. Sub-√N needs either a
  thin family with a proven asymptotic (Heath-Brown-type; best N^{2/3}) or exact computation (our engine).
* Verdict: this is a promising direction only for the weak goal, and it needs a new exponential-sum input. I suggest
  logging it as an open subtask for p-wild (subtask 9), with no further p4 time now.

## 6. What I would do next

* Turn §2 into a clean lemma for p1/p2/p3. It is trivial for *any* family: m adaptive F₂-linear queries leave an
  affine space of dimension ≥ H − m of consistent indicators. Single points are intervals, so the span is never the
  issue; the issue is the number of queries. So the even-total obstruction holds for every linear strategy unless
  "prime-like" constraints cut the space down. The real question for p3 is whether any *proven* property of the
  primes (RH positivity at scale √x, Brun–Titchmarsh, BHP) is incompatible with all m = o(√x) parities vanishing.
  My guess is no, because those properties are all "large-scale" while parities are local.
* Check whether the engine can compute an *integer-weighted smooth approximation* Σ_p w(p) with w a step function of
  x^{o(1)} steps exactly, not mod M. If exact counts on long intervals were possible, the LO window could be closed.
  prime-finding.md §4 says this needs k-fold products, so I expect no.

## 7. Session 2 (new p4): counting + factoring, the Chebyshev–Selberg certificate

### 7.0 What the two unexplained scripts do
* `graham_check.py` checks Graham's identity (JNT 10, 1978):
  Σ_{n≤N} Λ_z(n)² = N log z + O(N), where Λ_z(n) = Σ_{d|n, d≤z} μ(d) log(z/d).
  At N = 2·10⁶ the measured O(N) term is −0.49N, −0.59N, −0.60N for z = 10, 100, 1000 [N].
  The constant is negative, which helps the certificate below.
* `cheb_bisect.py` is a brute-force simulation of a **Chebyshev certificate** for a prime > u.
  * It sets w(n) = L₁²·Σ_{p^k|n, p≤R} ⌈log₂p⌉ + Σ_{R<d≤u} Λ_R(d)²⌈log₂d⌉·#{k : d^k | n}.
  * Since Λ_R(p^j) = log R for p > R, we get w(n) ≥ L₁²·log₂(u-smooth part of n). Also w ≥ 0.
  * So F(n) = L₁²⌊log₂n⌋ − w(n) > 0 implies P⁺(n) > u.
  * F is additive, so the script bisects from [x, 2x) and then factors the n it lands on.
  * It sums w directly over d ≤ u, which costs u. That is no better than scanning.
  * The previous p4 did not record it. §7.2 puts it in query form.

### 7.1 Prior art (Q1) [K]
* **With a factoring oracle.**
  * Polymath4 Thread III, Problem 1: find a prime ≥ n in o(√n) time, assuming RH and a factoring oracle. Open.
  * Problem 2 asks for n^{1/2+o(1)} unconditionally, also with the oracle. LO answers it without any oracle.
  * Strategy B: an interval [n, n+a] with a = o(√u) cannot consist entirely of u-smooth numbers.
  * Strategy C: integers with a divisor near u. Distance bounds u/2; n/u; √u for n ~ u²; u^{0.4} conditionally.
  * Best known unconditional result via short-interval large prime factors: ≈ u^{0.53} (§5). All of these are ≥ √u.
  * The paper (TCH, Math. Comp. 2012) states no factoring-oracle theorem. Its §1 says the problem stays open even with
    the oracle and GRH.
* **With a π(x) oracle.** Exact π gives a prime in [N, 2N] in O(log N) queries by bisection. This is Thread IV's
  "finding reduces to counting". The N^{1/2+o(1)} figure is the cost of *implementing* the oracle (LO; HKM elementary),
  not a property of the oracle model.
* **With a parity oracle.** TCH Thm 1.2 computes π mod 2 on intervals of length ≤ N^{1/2+c} in N^{1/2−c}. They state they
  cannot locate an odd interval, so a parity oracle gives no finding theorem (literature.md §1). Our barrier theorems
  (p1/p2/p3/w2) make this rigorous for any linear-query use.

### 7.2 New primitive and theorem (Q2) [R] (simulated end to end [N])
**Primitive.** Q_k(J; m, a, b) = #{(t, q) : a ≤ mt ≤ b, (mt)^k q ∈ J}.
* This counts lattice points under a steep hyperbola. It is a unique-witness system with one k-fold product, k ≤ A/ρ = O(1).
* So it is one engine count, x^{o(1)}.
* Classically, for b ≤ x^{1/3} the boundary has second derivative > 1, so the convex-hull trick fails. No o(b/m) method
  is known [C].
* A factoring oracle cannot supply this count, because it handles one integer at a time. A counting oracle can.

**Theorem 7.1.** Fix ρ ∈ (0, 1) and A > (1+ρ²)/(2ρ). Using the engine's Q_k counts and factoring, plus a sieve of μ up to
R = u^ρ, one deterministically finds a prime p ∈ (u, 2u^A]. The cost is O(R²·log³u) counts, i.e. u^{2ρ+o(1)} time.
No RH is needed. Hence a prime > u can be found in u^ε for every ε > 0. Balancing ρ ≍ (log log u)^{−1/4} against the
engine's 2^{O(n/√log n)} gives u^{o(1)}.

*Proof.*
1. Λ_R(d)² = Σ_{e₁,e₂≤R} μμ L L·[lcm(e₁,e₂) | d]. So Σ_{n∈J} w(n) = Σ_m b(m)·Σ_blocks c·Q_k(J; m, block). There are
   ≤ R² values of m, O(log u) dyadic blocks for ⌈log₂d⌉, and k ≤ A/ρ.
2. Σ_J L₁²⌊log₂n⌋ has a closed form, so F(J) is exact for every J.
3. Positivity of the top interval: on J = [x, 2x),
   Σ_J w = x·Σ_d W(d)/d + O(u·L₁²·log u)
   with mean Σ_{R<d≤u} Λ_R(d)² log d/d = L₁²·log u·(1−ρ²)/(2ρ) + O(L₁²) (Graham plus partial summation), plus
   ρ log u from p ≤ R. So F(J)/x ≥ L₁²·log u·(A − (1+ρ²)/(2ρ) − o(1)) > 0.
4. Bisection keeps a positive half for log₂x steps and ends at n ∈ [x, 2x) with F(n) > 0, so P⁺(n) > u.
5. Factor n. Since n < 2x, its largest prime factor p satisfies u < p ≤ 2u^A. ∎

**Run (`chebq.py`, oracle simulated by floor sums, every query counted, n factored with sympy).**

| u | R | A | F/(xL₁²) | asymptotic prediction | queries | n | p > u |
|---|---|---|---|---|---|---|---|
| 10³ | 32 | 2.0 | 8.14 | 7.47 | 18,303 | 1,000,001 | 9901 ✓ |
| 10⁴ | 10 | 2.0 | 2.34 | −1.66 | 12,284 | 100,000,023 | 14537 ✓ |
| 10⁴ | 10 | 1.7 | −1.65 | −5.65 | 369 | — (top F < 0) | — |
| 10⁴ | 10 | 3.0 | 15.6 | 11.6 | 28,502 | 10¹²+3 | 1,152,763 ✓ |
| 10⁵ | 10 | 2.6 | 6.79 | 0.00 | 38,205 | 10¹³+36 | 2.5·10¹² ✓ |
| 10⁶ | 16 | 2.7 | 9.31 | 1.99 | 130,082 | 1.58·10¹⁶ | 3.05·10¹⁴ ✓ |

* The query count is R²·polylog. The simulated oracle costs ≤ u/m per query; that is the cost the engine removes.
* The measured margin beats the asymptotic prediction by 4–7 bits, because Graham's O(N) constant is negative (≈ −0.6).
* The pointwise certificate (u-smooth part < n) was re-checked by brute force at each output.

**Catches checked.**
* (a) It is the WEAK goal. The output p can sit anywhere in (u, 2u^A]; in the runs it ranged from just above u to ≈ x/4.
* (b) All the power comes from the engine computing Q_k. With only a factoring oracle, the same certificate costs u.
* (c) Correctness needs only W ≥ 0 and W(p^j) ≥ L₁² for R < p ≤ u. Both hold exactly, with no error terms. Only
  positivity of the top interval uses analysis, and it holds for any fixed A above threshold.
* (d) Prior art: Polymath lists Strategy B (smooth intervals) and C, but never a bisection over a long interval, which
  needs counts. Web search found no counting-oracle version (weak negative).
* (e) Consequence for the strong problem. It gives a prime in [N, N^c] in N^{2ρ} with c = (1+ρ²)/(2ρ). That is below √N
  only for c > 2.125. It is not a prime in [N, 2N].

### 7.3 Obstruction for [N, 2N] by this route [R] for Λ_R², [C] for general Type-I
* To force a prime factor in T = [N, 2N], the certificate's budget is the harmonic Λ-mass of T, Σ_{p∈T} log p/p = log 2.
  The majorant W ≥ Λ off T must have harmonic excess < log 2.
* For Selberg weights of level R the excess is ∫ (log t/log R − 1) d log t over t ∈ (R, N) = log N·(1−ρ)²/(2ρ). This is
  < log 2 only if R ≥ N^{1−O(1/√log N)}. The cost is then min(u, R²) ≥ N^{1−o(1)}.
* General Type-I majorants W(d) = Σ_{e|d, e≤D} λ_e: Selberg's parity example (Liouville; Bombieri–Vinogradov for λ makes
  Σ W λ negligible when D ≤ t^{1/2−ε}) forces mass ≥ 2× truth on every dyadic scale t ≥ D^{2+ε}. So the excess is
  ≳ log(N/D^{2+ε}), which forces D ≥ N^{1/2−o(1)}.
* **Verdict:** Type-I certificates reproduce the √N wall exactly. To go further one needs a bilinear (Type-II) or μ-type
  cheap weight, which is node's Heath-Brown route.

### 7.4 The w1 lead (Q3): no
* I1 needs Σ_J R_z(1 − s_z) with exact z-roughness at z = x^{1/5.5}.
* Factoring is pointwise and cannot produce an aggregate. Engine counts give positive witnesses, never "no divisor < z".
* Replacing R_z with sieve weights ρ⁻ ≤ R_z ≤ ρ⁺ of level D = z^s needs f(s)/F(s) > (Σ_rough s_z)/(#rough).
  Using w1's exact x = 10¹² totals and Buchstab ω:

  | u | f/F must exceed | s needed | D needed |
  |---|---|---|---|
  | 3 | 0.41 | 2.5 | x^{0.83} |
  | 4 | 0.68 | ≈ 3.0 | x^{0.75} |
  | 5 | 0.95 | ≥ 3.6 | ≳ x^{0.72} |

  These figures use f/F = log(s−1) and are optimistic for s > 3. [C]
* Never below x^{0.7}, so this is dead. And the exact R_z is a Legendre φ(J, z) sum, which no known method computes
  below x^{1/2}.
* So nothing at N^{1/5.5}. I agree the record for [N, 2N] is N^{1/2+o(1)} (LO/HKM, or Cramér under RH).
