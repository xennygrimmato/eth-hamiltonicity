# Deterministic prime finding on the counting engines (Polymath4 target 2^{o(n)})

Status: working notes, 4 Nov 2026. Verdict is in §0 (written last, placed first). Sections are appended incrementally.

## 1. What Tao–Croot–Helfgott actually prove (arXiv 1009.3956, read 4 Nov 2026)

Correction to the task statement: TCH do **not** find a prime in x^{1/2-c}. Precisely:
* Conjecture 1.1 (open): decide whether [a,b] ⊂ [N,2N], b−a ≤ N^{1/2+c}, contains a prime in time N^{1/2−c+o(1)}.
* Theorem 1.2 (proved): decide whether such an interval contains an **odd** number of primes in N^{1/2−c+o(1)}.
* Best deterministic prime *finding* remains Lagarias–Odlyzko/Odlyzko: π(x) exactly in N^{1/2+o(1)} (contour integral,
  smoothing at scale N^{1/2}), then bisection: N^{1/2+o(1)}. TCH: "we do not know of a method to quickly and
  deterministically locate an interval with an odd number of primes."

Identities (TCH §2): 2^{ω(n)} = Σ_{d²|n} μ(d) τ(n/d²) (2.1); Σ_{a≤n≤b} 2^{ω(n)} ≡ 2·#{prime powers in [a,b]} (mod 4)
(since 4 | 2^{ω} unless ω ≤ 1); hence
  Σ_{a≤n≤b} 2^{ω(n)} = Σ_{d ≤ √b} μ(d) · D([a/d², b/d²]),  D(J) := Σ_{m∈J} τ(m)   (2.2).
Cost accounting: D(J) by the hyperbola method is x^{1/2}; TCH partition the hyperbola into x^{0.49} arithmetic
progressions on which ⌊x/n⌋ is linear (Dirichlet approximation + Strassen for quadratic exponent sums) to get
D in x^{1/2−c₀}. Summed over d ≤ N^{0.49} this gives N^{1/2−c₀/10}; large d cost N^{0.27+c}. μ(d) for d ≤ √N is a
sieve, O(N^{1/2}) — note this is *also* an N^{1/2} step, hidden because TCH only need d ≤ N^{0.49} explicitly.

**With a D-oracle (any interval J, x^{o(1)} time), what does (2.2) cost?** The d-sum still has √N terms and needs
μ(d) for every d ≤ √N: N^{1/2+o(1)}. So the oracle alone does not help: the cost moves entirely into the Möbius
weights μ(d), d ≤ √N — exactly the "∀" of the survey agent (μ(d) needs the factorisation of d). Any route must
remove the μ-sum, not speed up D. §2 does this.
