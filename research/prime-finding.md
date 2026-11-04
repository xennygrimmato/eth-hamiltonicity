# Deterministic prime finding on the counting engines (Polymath4 target 2^{o(n)})

Status: working notes, 4 Nov 2026. §0 is the verdict; §§1–5 the supporting analysis. Lean checks: lean/EthFollowup/Scratch/Primes/Check.lean.

## 0. Verdict

**(ii)+(iii).** No route to 2^{o(n)} prime finding is found; the engine does give a sharp improvement of the *parity*
half of Tao–Croot–Helfgott, and the obstruction to finishing is pinned down to one network-size question.

1. **Correction of the target.** TCH (Math. Comp. 81 (2012), arXiv 1009.3956) prove only that the *parity* of π on an
   interval of length ≤ N^{1/2+c} is computable in N^{1/2−c} (their Thm 1.2); deciding whether such an interval contains a
   prime (their Conj. 1.1) is open, and deterministic prime finding is still Lagarias–Odlyzko's x^{1/2+o(1)}.
2. **Proved here (§2, Lean-checked on instances):** π(I) mod 2 for *every* interval (or cheap set) I ⊂ [1, 2^n] is an
   engine count with cut O(n): π(I) ≡ ½(Σ_{m∈I} τ(m)C_L(m) − Σ_{m∈I square} τ(m)C_L(m)) (mod 2), where C_L(m) is the number
   of chains d_1² | m, d_2² | d_1, …, d_L² | d_{L−1}, L = ⌈log₂ n⌉, and C_L(m) ≡ [m squarefree] (mod 2). So the survey's
   "∀ barrier" (ambitious-targets.md §2.7) is wrong for parities: TCH Thm 1.2 goes from N^{1/2−c} to 2^{O(n/√log n)} =
   x^{o(1)}. More generally π(I) mod k for k ≤ 2^{o(√log n)} (Thm B′), hence π(I) mod M for M up to 2^{2^{o(√log n)}}, and
   exact π(I) for |I| ≤ H₀ = x^{o(1)} (superpolylogarithmic); TCH Conj. 1.1 holds for intervals of length ≤ H₀.
3. **Prime finding does not improve.** With residues mod M = x^{o(1)} as the only information, a prime is found in O(n)
   bisection steps as soon as one queried cheap set has π ≢ 0 (mod M); but a set consistent with every known theorem
   on primes can have all x^{o(1)} queried counts ≡ 0 (mod M), and then x^{0.525}/H₀ block queries are needed (BHP). Result
   x^{0.525+o(1)} (x^{1/2+o(1)} under RH), not better than Lagarias–Odlyzko. The oracle's "x^{o(1)}" is 2^{Θ(n/√log n)},
   so sub-polynomial savings cannot be traded against LO either.
4. **Barrier statement (§4).** Any engine-based 2^{o(n)} prime finder needs π(I) mod M for M ≥ x^{0.525}, i.e. the exact
   isolation of ω(m) = 1, which within O(1)-multiplication weights means k-fold divisor counts with k = Θ(n/log n) or more.
   That is an iterated product of Θ(n) factors of total size n, whose verifier has cut Θ(n log n) in every known network
   (product tree), giving 2^{Θ(n√log n)}. **Needed: a parsimonious iterated-multiplication network with cut o(n √log n)**
   (nodes of n^{4/5} bits), or a non-counting (analytic, LO-type) component. Neither is available; no lower bound is known.
5. **Worth publishing on its own:** "parity of π on any interval, and π mod M for M = exp(exp(o(√log log x))), in
   x^{o(1)} deterministically" (unconditional; galactic constants as for factoring), as a corollary of the factoring network
   (one extra chain of O(log n) squarings). It is a clean strengthening of TCH Thm 1.2 and the first unconditional
   x^{o(1)} bound on any nontrivial prime-counting functional.


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

## 2. The engine's reach, and the identity that removes the Möbius sum

**Model (from factoring-note §2–§4, factoring-engine.md §5).** The engine computes Z = Σ_z Π_a W_a(z_a) Π Ψ_ab for a
label system: wires of O(n) bits total, nodes of load P ≤ n/K⁷ (n^{4/5} at K = n^{1/40}), each node checking any
poly-time predicate on its bits, cut U = Σ shared bits; cost 2^{O(U/√log n)}. The AK/SS multiplication network has
U = O(size), so any count of tuples of O(n)-bit integers subject to **O(1) multiplications, comparisons, divisibility
checks and congruences** costs x^{o(1)} = 2^{O(n/√log n)}. Integer weights W_a ∈ ℤ are allowed, but a weight that is a
function of a large integer d can only be applied if d fits in one node, i.e. d ≤ x^{1/K⁷} = x^{o(1)}. In Dirichlet-series
language: coefficient sums over intervals of products of O(1) factors from {ζ(s), interval/progression truncations of ζ,
ζ(js) (perfect powers), Σ_{a≤x^{o(1)}} g(a)a^{-s} for arbitrary g}. **No negative powers of ζ** — that is the ∀ barrier
of ambitious-targets.md §2.7, correctly stated for *exact* counts. Also k-fold products cost cut Θ(n log k) (product
tree; a one-shot DFT costs nk²), so k ≤ 2^{o(√log n)} factors keep x^{o(1)}.

**The ∀ is false for parities.** The agent's claim "every de-duplication of compositeness witnesses is a ∀" overlooks
that the squarefree indicator is a *parity* of an ∃-count, through a chain of geometrically shrinking witnesses:

Lemma A (squarefree chain). For n ≥ 1 let C_L(n) := #{(d_1,…,d_L) : d_1² | n, d_2² | d_1, …, d_L² | d_{L-1}}.
If n < 2^{2^L} then C_L(n) ≡ [n squarefree] (mod 2).
Proof. Write n = s t² with s squarefree. {d : d² | n} = {d : d | t}, so #{d squarefree : d² | n} = 2^{ω(t)} ≡ [t = 1].
Induction on L: C_0 ≡ 1 = [1 squarefree] (n < 2 forces n = 1); C_L(n) = Σ_{d²|n} C_{L-1}(d) with d < 2^{2^{L-1}}, so
C_L(n) ≡ #{d squarefree : d² | n} ≡ [n squarefree]. ∎
Witness size: Σ_i bits(d_i) ≤ n/2 + n/4 + … ≤ n; verifier: L ≈ log₂ n squarings and divisions of geometrically
decreasing size, total cut O(n). So n ↦ τ(n)·C_L(n) is a cheap weight (witness (a,b,d_1,…,d_L), ab = n).

Theorem B (parity of π on any interval, x^{o(1)}). For an interval I ⊂ [1, 2^n] and L = ⌈log₂ n⌉,
   π(I) ≡ ½ · ( Σ_{m∈I} τ(m) C_L(m) − Σ_{m∈I, m=k²} τ(m) C_L(m) )   (mod 2),
and both sums are engine counts with O(1)+O(L) multiplications of total cut O(n), hence x^{o(1)} = 2^{O(n/√log n)}.
Proof. For non-square m, τ(m) is even; τ(m) ≡ 2 (mod 4) iff m = p^e r² with p ∤ r, e ≡ 1 (mod 4), else 4 | τ(m).
So ½(Σ − Σ_squares) ≡ Σ_{m∈I, τ(m)≡2 (4)} C_L(m) ≡ #{m ∈ I : τ(m) ≡ 2 (4), m squarefree} = #{m ∈ I : m prime} (mod 2),
since a squarefree m with τ(m) = 2^{ω(m)} ≡ 2 (mod 4) has ω(m) = 1. ∎
This replaces TCH (2.2) (Möbius over d ≤ √N, cost N^{1/2}) and TCH Theorem 1.2 (N^{1/2−c}) by x^{o(1)}, for intervals
of *any* length and also for any cheap weight / cheap set (progressions, quadratic families, prefix sets).

Lemma A′ (mod k). For an integer k ≥ 2 and all d: μ(d) ≡ τ_{k−1}(d)·[d squarefree] (mod k)  (both sides vanish off
squarefree d; on squarefree d, τ_{k−1}(d) = (k−1)^{ω(d)} ≡ (−1)^{ω(d)}). Hence [n squarefree] = Σ_{d²|n} μ(d) ≡
Σ_{d²|n} τ_{k−1}(d)[d squarefree] (mod k), and iterating as in Lemma A, the τ_{k−1}-weighted chain count
W_k(n) := Σ_{chains} Π_i τ_{k−1}(d_i) ≡ [n squarefree] (mod k), with cut O(n log k) ((k−1)-fold products on geometrically
shrinking d_i).
Theorem B′ (π mod k). With W := W_{k²} (≡ [sqf] mod k²), Σ_{m∈I} τ_k(m) W(m) ≡ [1∈I] + k·π(I) (mod k²), because for
squarefree m, τ_k(m)W(m) ≡ k^{ω(m)} (mod k²) and k^{ω} ≡ 0 for ω ≥ 2. Cost 2^{O(n log k/√log n)}: x^{o(1)} iff
log k = o(√log n). By CRT: **π(I) mod M for every M | lcm(1..K₀), K₀ = 2^{o(√log n)}, i.e. M up to 2^{2^{o(√log n)}}**,
for any interval I, in x^{o(1)}. (TCH remark: mod 3 was N^{2/3} for them.)

**Lean feedback** (lean/EthFollowup/Scratch/Primes/Check.lean, #eval, all `true`): Lemma A for n ≤ 255 (L = 3);
Theorem B on every interval [a,b] ⊂ [1,120]; Lemma A′ for k = 3 and k = 9 on n ≤ 255; Theorem B′ for k = 3 (W = W_9)
and k = 2 (W = W_4) on every interval ⊂ [1,100]. Status: Lean-checked on instances; the general proofs above are
three-line and I have no doubt about them (not formalised in general).

## 3. What the mod-M information buys, and what it does not

(a) **TCH Theorem 1.2 improved from N^{1/2−c} to x^{o(1)}**, for every interval (TCH needed length ≤ N^{1/2+c}).
(b) **Exact π(I) on short intervals.** Montgomery–Vaughan: π(I) ≤ 2|I|/log|I|. If 2|I|/log|I| < M then π(I) mod M is
    π(I). With M = lcm(1..K₀), K₀ = 2^{ε√log n}: |I| ≤ H₀ := 2^{2^{ε√log n}}·(small) — a window far beyond poly(log x) but
    x^{o(1)}. So TCH Conjecture 1.1 ("does [a,b] contain a prime?") is settled in x^{o(1)} for b − a ≤ H₀, not for
    b − a ≤ N^{1/2+c} as conjectured.
(c) **Bisection works from any set with nonzero residue.** If π(A) ≢ 0 (mod M) for a cheap set A, a half with nonzero
    residue exists at every step, and at size < H₀ the residue is the exact count: a prime in O(n) queries. So
    prime *finding* in [x, 2x] costs x^{o(1)} **unless π(A) ≡ 0 (mod M) for every cheap set A we query** (all
    intervals, progressions, bit-prefix sets, polynomial weights — all x^{o(1)} of them). The all-residues-zero case is
    the only obstruction, and it cannot be excluded: a "prime-like" set satisfying every known theorem about primes
    (BHP gaps ≤ x^{0.525}, Brun–Titchmarsh upper bounds, Huxley short-interval asymptotics with their error terms) may
    have every queried count ≡ 0 (mod M) as long as consecutive query endpoints are ≫ M log M apart: the adversary
    puts 0 or ≥ M primes between them. Against this adversary any deterministic strategy needs ≥ x^{0.525}/(M log M)
    queries (scan blocks of length H₀ from x; the first block with nonzero residue contains a prime). This is
    information-theoretic within the "residues of cheap counts" oracle model, not a conjecture.
(d) **Resulting prime-finding bound: x^{0.525+o(1)}** (BHP gap / H₀ blocks, each x^{o(1)}), which is *worse* than
    Lagarias–Odlyzko's x^{1/2+o(1)} (exact π via the explicit formula, then bisection). Under RH (gaps ≤ √x log x) the
    scan gives x^{1/2+o(1)}, matching but not beating LO. Hybrid LO + residues: LO at accuracy L costs x/L and localises a
    prime to a window of length x^{o(1)}L; scanning that window costs L/H₀; optimum L = √(xH₀), total x^{1/2}/√H₀ — but
    every engine query costs 2^{Θ(n/√log n)} = x^{Θ(1/√log n)}, which exceeds the saving √H₀ = 2^{2^{O(ε√log n)}} by far.
    No improvement over x^{1/2+o(1)}. (The oracle's x^{o(1)} is 2^{Θ(n/√log n)}: any gain must be a power of x.)

## 4. What would be needed (the barrier, precisely)

Prime finding in 2^{o(n)} by *this* route needs π(I) mod M for M ≥ x^{0.525} (then [x, x + M] has exact count ≥ 1 and
bisection finishes), i.e. Theorem B′ with k ≈ 0.525·n·ln 2 — or any other identity isolating ω(m) = 1 exactly.
* Functions of ω realisable with O(1) multiplications lie in the span of {k^{ω}} (k-fold divisor counts, ordered or with
  order constraints, powers τ^j = 2^{jω}); [ω = 1] on ω ∈ [0, n/log n] needs ≥ n/log n such terms (Vandermonde), and the
  only shortcut is the vanishing k^{ω} ≡ 0 (mod k^2) for ω ≥ 2, which yields residues only. So exactness ⇔ k-fold
  products with k = Θ(n/log n) or more.
* A k-fold product of total size n has cut Θ(n log k) in every known verifier (product tree; one-shot DFT or CRT costs
  nk or nk²; big nodes of n^{4/5} bits remove only the bottom levels, the top n^{1/5} leaves still give (1/5) n log n).
  Engine exponent e_K·U with e_K ≍ 1/√log n: need U = o(n √log n). **Required: an iterated-multiplication network
  (k ≍ n factors, total n bits, nodes of n^{4/5} bits) with cut o(n √log n)** — a √log n factor below the product tree.
  Equivalently a parsimonious network for "Π a_i = m" of size o(n √log n). Not known; no lower bound is known either.
* Alternatives that are *not* counts: LO's analytic approximation. The engine computes exact integers; the parity /
  mod-M route and exact counting are the only two things it offers, and the gap between them is exactly the k-fold
  product.

## 5. The five ideas from the brief, each in two lines

(a) **Parity tricks / squarefree restriction.** Yes — but not by Möbius over d ≤ x^ε plus recursion on m/d² (that
    recursion runs over all d ≤ √x and re-creates μ(d) for large d; the geometric recursion is on *square roots*, not
    on m/d²). The right de-duplication is Lemma A: [sqf] ≡ chain count (mod 2), depth log n, cut O(n). Gives Theorem B.
(b) **Signed weights.** W_a ∈ ℤ is allowed, so μ(d) can be carried in-network only for d ≤ x^{1/K⁷} = x^{o(1)} (d must sit
    in one node; μ needs d's factorisation, computed in node time 2^{o(n)} which is tolerated as τ). Useless for the
    d ≤ √x Möbius sum; subsumed by (a). Lemma A′ shows mod-k signed weights are not even needed: μ ≡ τ_{k−1}·[sqf].
(c) **Least-divisor recursion (Meissel–Lehmer).** Φ(J, z) = Σ_{d|P(z)} μ(d)⌊·⌋ needs the z-smooth squarefree d as an
    r-fold product of primes, r up to n: cut n log n — same barrier as §4. Each Legendre level is one engine call, but the
    number of levels (or the fold of the product) is Θ(n/log n), not O(1). Exact Φ is out; Φ mod M is in (via §2).
(d) **Factor every number in a short interval.** minFac per number is x^{o(1)}; BHP guarantees a prime in [x, x+x^{0.525}];
    so x^{0.525+o(1)} — worse than LO's x^{1/2}. With §3(b) the interval is scanned in blocks of H₀ = x^{o(1)} instead of
    single numbers: same exponent. Only a gap bound x^{θ} with θ < 1/2 would help, and even RH gives θ = 1/2.
(e) **Progressions / quadratic families.** Theorems B, B′ hold verbatim for any cheap set (n ≡ r mod q, n = a²+b²,
    prefix sets, polynomial weights), since the weight τ(n)C_L(n) composes with any cheap relation. This widens the
    oracle but does not change §3(c): the adversary's zero-residue conspiracy is per query, and Linnik-type lower
    bounds for primes in progressions are far weaker than needed to force a nonzero residue.
