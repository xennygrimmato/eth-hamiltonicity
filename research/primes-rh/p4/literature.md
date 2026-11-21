# p4 literature notes (subtask 8, also feeds subtask 4)

Read 21 Nov 2026. [K] = known with citation. Anything I did not read in the primary source is marked "(secondary)".

## 1. Polymath4 "Finding primes" (2009–2011) and Tao–Croot–Helfgott

The wiki page michaelnielsen.org/polymath1/index.php?title=Finding_primes now returns 404. I used the blog threads
(polymathprojects.org/category/finding-primes) and the paper.

**Paper.** D.H.J. Polymath (Tao, Croot, Helfgott), *Deterministic methods to find primes*, Math. Comp. 81 (2012)
1233–1246, arXiv 1009.3956. I read the PDF (local copy in scratchpad).
* Conj. 1.1 (open): decide in N^{1/2−c+o(1)} whether an interval [a,b] ⊂ [N,2N] of length ≤ N^{1/2+c} contains a prime.
* Thm 1.2: decide in N^{1/2−c+o(1)} whether such an interval has an **odd** number of primes.
* Thm 1.3: P_{a,b}(t) = Σ_{a≤p≤b} t^p mod 2 has circuit complexity N^{1/2−c+o(1)}. So P mod (2,g) is computable in
  N^{1/2−c/2+o(1)} for any g ∈ F_2[t] of degree ≤ N^{c/4}. With g = t−1 this is Thm 1.2. With g cyclotomic it gives
  π(x;a,q) mod 2 for q ≤ N^{c/10}.
* Why parity did not give finding, in their words: "we do not know of a method to quickly and deterministically locate an
  interval with an odd number of primes"; and "it is a priori conceivable (but quite unlikely) that an interval [a,b] might
  contain a non-zero number of primes, but have an even number of primes in every residue class mod q with q = O(N^{c/10})".
* Ideas they list for going further (§1, §4):
  1. Test P mod (2,g) with a **random** g of degree ≤ N^{c/4}. A positive proportion of such g do not divide P (unique
     factorisation in F_2[t]). This gives a BPP decision procedure in N^{1/2−c/2}. It does not give P, because the running
     time is not polylog, so P = BPP gives nothing.
  2. Evaluate P mod (2,g) for many g at once (FFT, Borodin–Moenk multipoint evaluation), or P(t^j) mod (2,g).
  3. Find a small set of g such that P mod 2 cannot be divisible by all of them without vanishing. They note this is
     "similar to the heart of AKS". The obstruction is that P could be divisible by up to N^{1−c/4} irreducibles of degree
     N^{c/4}.
  4. π mod q for every prime q ≤ O(log N), then CRT. Already mod 3 needs Σ τ_3, which costs N^{2/3−c} by the 3-D
     hyperbola method, which is worse than √N.
  5. Better approximations of the hyperbola (piecewise polynomial in place of piecewise linear).
  6. Circuit complexity of Σ t^{p²} and Σ t^{h(p)}. Croot–Hollis–Lowry was announced as forthcoming.
* Other routes in §1. A sparse set known to contain primes gives a finding algorithm: Heath-Brown a³+2b³ gives N^{2/3}.
  Schinzel H would give N^{1/k} via n^k+1. BHP gives N^{0.525}. RH gives N^{1/2+o(1)}. Cramér's conjecture would give
  polylog. P = NP would give polylog. Lagarias–Odlyzko (LO) gives N^{1/2+o(1)} unconditionally.

**Blog threads.**
* Thread II (9 Aug 2009) lists six strategies:
  1. sparse explicit sets (a²+b⁴ Friedlander–Iwaniec; a³+2b³);
  2. Euclid-type recursion with a factoring oracle;
  3. non-S-smooth numbers in short intervals (Gowers: iterated sumsets of log-primes);
  4. pseudoprimes;
  5. avoiding a set of divisors;
  6. Croot: a Siegel zero gives a dichotomy via x²−My².
  Also: the oracle counterexample to finding pseudoprimes, and P = NP ⇒ polylog.
* Thread III (13 Aug 2009) states two open problems, both **with a factoring oracle**:
  * Problem 1: find a prime with ≥ k digits in o(√n) time, assuming RH.
  * Problem 2: O(n^{1/2+o(1)}) unconditionally. This was later answered by LO.
  Strategies listed there:
  * A. Use the zeros of ζ to find a short interval with π > 0. A Siegel zero might help, or RH at the other extreme.
  * B. Show that [n,n+a] cannot consist entirely of u-smooth numbers, with a = o(√u) and n subexponential in u.
  * C. Distance from n to the nearest integer with a factor near u: trivial u/2; O(n/u) for 2u ≤ n ≤ u²; O(u^{0.4}) for
    n ~ u², conditional on an exponential-sum estimate. Ford's paper on integers with a divisor in an interval is cited
    (K. Ford, Ann. of Math. 168 (2008)).
  * D. Special sequences.
  * E. Pseudoprimes.
* Thread IV (28 Aug 2009) names the square-root barrier and the reduction from finding to counting. It notes that the
  parity of π(x) is computable in x^{1/2+o(1)}, and suggests π mod 3 and AKS-style polynomial extensions.
* Thread V (27 Oct 2009) sets up the polynomial method. Goal 1: a small family of pairs (n,g) whose simultaneous vanishing
  forces P̃ = 0. Goal 2: test them all fast. Comments:
  * M. Lewko (28 Apr 2010): parity of π in x^{0.45}; find an AP with q ≤ x^{0.01} whose intersection with [x,2x] has an
    odd count. He retracted his sieve inequality the same night.
  * T. Tao (30 Apr 2010): g = x^q − 1 gives π(x;a,q). Heuristically a random-like set in [N, N+N^{0.51}] can have even
    counts in every class mod q ≤ N^{0.01}, because there are about 2^{N^{0.51}} candidate sets. He also says this
    "should not actually occur" for the primes, but cannot prove it.
  * E. Croot: Weyl differencing for Σ t^{p²}, matrix rings in place of polynomial rings, exponential exponents 2^p.
  * W.D. Smith (2010 draft thread): count mod 2^m with m > log₂(b−a+1). Nobody made it efficient.
  * G. Kalai (28 Jan 2015): "once you find a single interval with an odd number of primes you can divide and conquer".
    He asks whether [a_n, 2a_n] provably has an odd count for special sequences (APs, p_n, n², 2^n), and asks about a
    signed zeta-like product.

**What our team has beyond this.** Our engine computes P mod (2,g) for all g of degree x^{o(1)} in x^{o(1)}, and π mod M.
So we sit exactly at TCH's "Goal 1" obstruction, with Goal 2 solved. See notebook.md §2 for the GF(2) count of how much
AP-parity information is worth.

## 2. Deterministic prime-finding and π(x) records

| method | time | reference |
|---|---|---|
| Sieve / Bertrand | N^{1+o(1)} | — |
| Heath-Brown a³+2b³ | N^{2/3+o(1)} | Acta Math 186 (2001) |
| BHP gap + AKS | N^{0.525+o(1)} | Baker–Harman–Pintz, PLMS 83 (2001) |
| RH gap (Cramér) + AKS | N^{1/2+o(1)} | Cramér 1920/1936 |
| LO analytic π(x) + bisection | N^{1/2+o(1)} unconditional | Lagarias–Odlyzko, J. Algorithms 8 (1987) 173–191 |
| Combinatorial π(x), elementary | Õ(√N) | Hirsch–Kessler–Mendlovic, arXiv 2212.09857 (Mertens function also in Õ(√N)) |
| Meissel–Lehmer / LMO / Deléglise–Rivat | x^{2/3}/log² x | LMO Math Comp 1985; DR 1996 |
| Pseudodeterministic, randomised | poly(n) for infinitely many n | Chen–Lu–Oliveira–Ren–Santhanam, FOCS 2023, arXiv 2305.15140 (improves Oliveira–Santhanam 2017, subexp) |

Nothing deterministic is below N^{1/2+o(1)} for all N, under any proved hypothesis. Under Cramér's conjecture the time
would be polylog.

**LO in detail.** π(x) to accuracy L takes x^{1+o(1)}/L time via a contour integral of ζ of height T ≈ x/L. Quadrature on a
vertical line uses T log x samples, amortised by Odlyzko–Schönhage to T^{1+o(1)}. For exact π, smooth at scale x/T and
sieve the window of length x/T. The balance is T = √x. Space is x^{1/4+o(1)}.

**Implementations.**
* Platt, *Computing π(x) analytically*, Math. Comp. 84 (2015) 1521–1535 (arXiv 1203.5712): rigorous LO with interval
  arithmetic, π(10^24) unconditional.
* Büthe–Franke–Jost–Kleinjung, *A practical analytic method for calculating π(x)*, Math. Comp. 86 (2017) 2889–2909:
  π(10^24) under RH (2010), then π(10^25) = 176,846,309,399,143,769,411,680 unconditional.
* Büthe, *An improved analytic method for calculating π(x)*, arXiv 1410.7008.
* Büthe, *An analytic method for bounding ψ(x)*, Math. Comp. 2018: partial RH verification gives explicit bounds.
* All of these are √x-type in time.

## 3. RH: explicit statements (all now unconditional if the proof stands)

* Schoenfeld, Math. Comp. 30 (1976): |π(x) − li(x)| < √x log x/(8π) for x ≥ 2657, and |ψ(x) − x| < √x log² x/(8π)
  for x ≥ 73.2. von Koch 1901 gives the O-form.
* Gaps: Cramér, p_{n+1} − p_n ≪ √p_n log p_n. Explicit: Carneiro–Milinovich–Soundararajan, Comment. Math. Helv. 94
  (2019), arXiv 1708.04122: for x ≥ 4 there is a prime in (x − (22/25)√x log x, x]. A later SDP improvement gives
  constant 0.8358 (secondary: Quesada-Herrera survey). Earlier constants: Dudek (2015) 4/π; Ramaré–Saouter.
* Under RH plus the pair-correlation conjecture (not implied by RH), gaps are o(√x log x) (Heath-Brown–Goldston) and
  ≪ √x √log x (Heath-Brown). These are still √x-scale.
* Selberg (1943), under RH: ∫_X^{2X} |ψ(x+h) − ψ(x) − h|² dx ≪ h X log² X. So almost all intervals [x, x+f(x) log² x],
  with f → ∞, contain primes. This is a measure statement with an exceptional set of size ≪ X log² X/h.
  Unconditionally, Guth–Maynard (Ann. of Math. 203 (2026), arXiv 2405.20552) give almost all intervals of length
  x^{2/15+ε}, and all intervals of length x^{17/30+ε} with the asymptotic.
* Montgomery pair correlation (1973), under RH: F(α) asymptotics for 0 ≤ α ≤ 1. This is now unconditional. It gives
  ≥ 2/3 of zeros simple, improved later under RH. The full conjecture (all α) is NOT a consequence of RH. Goldston–
  Montgomery (1987): the pair-correlation conjecture is equivalent to the variance of primes in short intervals, under RH.
* Landau–Gonek formula: Σ_{0<γ≤T} x^ρ = −(T/2π)Λ(x) + O(x log(2xT) log log 3x) + … (Gonek 1993). So a sum over zeros
  detects whether x is a prime power, but only once T ≫ x log x. Useless algorithmically.
* GRH, which is not part of the Lean-checked statement, would add: Miller's deterministic primality test (moot after
  AKS); least quadratic non-residue ≤ 2 log² p (Bach), giving deterministic square roots mod p; least prime in an AP
  ≪ q² log⁴ q; Chebotarev with explicit error terms. None of these is known to give prime *finding* below √x.

## 4. Status of the claimed RH proof (as of 21–22 Nov 2026; news sources, secondary)

* 20 Nov 2026: L. Alpöge (Anthropic) posted a 4-page note and a Lean 4 archive: 175,187 files, about 17M lines,
  239 MB compressed. The proof was developed with Claude. The note claims that the method extends to GRH.
* Kevin Buzzard's caveat (Lean Zulip / blog): the question is whether the Lean statement is the actual RH, i.e. no
  redefined symbols and no kernel bugs. "We still await a successful comparator run."
* 21 Nov 2026: a joint Lean FRO / Mathlib Initiative statement reports that the comparator passed, with only the 3
  standard axioms, and that the statement matches Mathlib's `RiemannHypothesis`. Sources differ on details. One says a
  second tool ("con-leche") was also used. Pebblous reports that A. Sutherland independently compiled the archive and
  checked the axioms. Claims that Sutherland verified the GRH case for Dirichlet L-functions are unconfirmed.
* The Lean-certified statement is RH for ζ only. GRH is claimed, not certified.
* Masullo: an all-human competing draft from Stanford. Per the brief and nacionale.com it claims GRH. It is not in Lean.
  Brian Conrad gave feedback, and the draft is "undergoing major revision". Problems were reportedly found in it.
  Not confirmed.
* Coverage: Nature d41586-026-03812-7 (Maynard: "suspects correct"); Scientific American (updated 21 Nov);
  blog.pebblous.ai; nacionale.com.
* **Algorithmic consequences:** I found no post-20-Nov work on consequences for algorithms. A targeted search for
  "RH proved, prime gaps, algorithms, Miller test" returned nothing relevant. The standard consequences are §3.
  Practically: Miller's test needs GRH, so it remains conditional; AKS and BPSW make the question moot. Prime finding
  stays at N^{1/2+o(1)}.
