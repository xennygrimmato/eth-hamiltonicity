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
