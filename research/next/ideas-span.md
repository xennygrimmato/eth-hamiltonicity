# Ideas: the Span Conjecture, the cofactor problem, and restricted-machine separations

24 Nov 2026. Idea generation only. Inputs read in full: `y2/notebook.md`, `y1/notebook.md`, `ideas-pc-npc.md`.
Tags: **[P]** proved here (short proof given, not refereed), **[N]** checked by script, **[K]** known (from memory unless
stated), **[C]** conjecture / heuristic. Scripts in the scratchpad dir `span/`: `c4.py` (char-2 span), `c3.py` (base-r gadget), `c2.py` (tropical gadget,
Ryser valuations). Notation as in y2: N_g = ∏_e (y − g_e), Q = N_g·H, L / L̄ circuit / border complexity, [T26] the border
bound for per.

## 0. Verdict in one screen

1. **Span Conjecture: not refuted in characteristic 0, but demoted.**
   - It is **false in every characteristic p** [P, §1.2]. Any proof must be specific to characteristic 0.
   - In characteristic 0 it **implies that the ℂ-Knapsack norm has no easy multiple** [P, §1.2], hence P_ℂ ≠ NP_ℂ without
     the permanent bound. So y2 §6(a) ("the conjecture predicts nothing about Knapsack") is wrong, and the referee is right:
     Span is a τ-strength statement in which [T26] plays no role.
   - Every construction I tried either has span ≤ cost or is not known to be easy (§1.3). Structural reason in §1.4.
2. **Decisive negative for valuation counting [P, N]:** a size-O(n) polynomial Q(τ, y) with positive coefficients has 2^n
   distinct root valuations (§2, gadget). An unbounded-degree "τ-conjecture for Newton polygons" is false.
3. **Decisive positive, for pc1 [P, N]:** Newton-polygon slopes are *monotone under multiplication by any cofactor*, and the
   Ryser norm has 2^n − 1 distinct slopes. This gives fully elementary unconditional separations (§3, Ideas 1–2), none
   using [T26]: Theorem S (ΠΣ-sparse tests, R(t−1) ≥ 2^n − 1), Theorem S' (cancellation-free tests of alternation depth Δ,
   T(s/Δ)^Δ ≥ 2^n − 1), Theorem G (tightness: (s/Δ)^{Θ(Δ)} slopes are achievable, so the method stops at Δ = Θ(n/log n)),
   and Theorem 2T (two-term sums of products of powers of sparse polynomials, with cancellation, via a non-archimedean
   Rolle lemma: slopes ≤ 2m·t^{2m} + 4m(t−1) + 2 whatever the exponents).
3b. **Barrier [P, N] (§7):** under pc1's substitution, and under every integral monomial substitution, an O(n)-size positive
   polynomial (the gadget with ε_k = 2^{n−1−k}·c, G_0 = y^{2c}) has a slope set containing that of N_g; also for polynomially
   many substitutions at once. Single valuations cannot prove Gap G. All weights at once (tropical containment) is open.
4. **Referee's test case** Φ = ∏_i (x_i + T^{2^{i−1}}): undecided; my guess is that its cyclic norm has no easy multiple (§1.5).
5. **Is the original problem within reach?** No. See §5.

## 1. Is the Span Conjecture true?

### 1.1 Closure lemma (unconditional)

**Lemma C (correspondence closure) [P].** Let F(x, w) ≠ 0 have size s, and let Ψ(x, w, y) have w-degree δ and size σ. Then
G(x, y) := Res_w(Ψ(x, w, y), F(x, w)) = lc_w(Ψ)^{deg F} · det F(x, C_Ψ), where C_Ψ is the δ×δ companion matrix of Ψ in w
over ℂ(x, y), has size poly(δ)·(s + σ) (evaluate the circuit for F on δ×δ matrices; the scalar lc^{deg F} by repeated
squaring), and G(x, y₀) = 0 whenever Ψ(x, r, y₀) = 0 for a root r of F.
Special case Ψ = ψ(w) − y: G = ∏_{w : ψ(w) = y} F(x, w) has the roots ψ(r). For ψ = w^d: G(x, y) = ± ∏_r (y − r^d).

So "root sets of easy polynomials" are closed under union, substitution in x, border degeneration (y2 §9(2)), and all
low-degree algebraic correspondences in one root variable. They are **not** known to be closed under sumsets or product
sets of two root sets (the double resultant has two high-degree arguments). That is exactly the Knapsack question.

### 1.2 Two consequences

**(i) Span is false in characteristic p [P; span count N for p = 2].** Let V = F_p-span(x_1..x_n), M(w) = ∏_{v∈V}(w − v) the
Moore polynomial, size O(n² log p). For d = p^k − 1 (coprime to p), G(y) = det M(C_y) = ± ∏_{v∈V}(y − v^d) has size
poly(n, d). For p = 2, d = 2^k − 1: (e·x)^d = ∏_{a<k} (Σ_i e_i x_i^{2^a}); the monomials x_{i_0} x_{i_1}² ⋯ x_{i_{k−1}}^{2^{k−1}}
are distinct for distinct tuples, with coefficient e^{supp}; so dim span = Σ_{1≤j≤k} C(n, j). With k = log n: cost and degree
n^{O(1)}, span n^{Θ(log n)} — also above the "barely quasi-polynomial" shape N^{o((log N)^{1/3})} of y2 §9(1).

**(ii) In characteristic 0, Span ⇒ Knapsack multiples are hard [P].** If K = ∏_e (y − e·x) had a multiple F of size s, then
det F(C_y) with C_y the companion of w^d − y has size O(d³ s) and roots (e·x)^d, e ∈ {0,1}^n, whose span has dimension
Σ_{1≤j≤d} C(n, j) (the functions e ↦ e^α, |α| = d, on the cube are the multilinear monomials of degree ≤ d). Superpolynomial
for d = ω(1). The same argument applies to any root set that is Zariski-dense in a linear space of growing dimension.

**Reformulation.** Span is equivalent to its "Hilbert-function" form: for every δ, dim span{r^j : r ∈ Roots_d(Q), j ≤ δ} ≤
p(s·poly(δ), dδ). So root sets of easy polynomials must behave like points on a variety of bounded dimension. In every
known easy example the roots lie on poly(s) rational curves of degree poly(s, d) (orbit closures {λa + λ^{−1}b}, {Φ(x, λ)}).
**Curve form [C]:** Roots_d(Q) lies on ≤ poly(s) curves of degree ≤ poly(s, d). Stronger than Span, equally unsupported.

### 1.3 Constructions tried

| construction | roots | span | cost | status |
|---|---|---|---|---|
| y^D − a^D; ∏_{i≤m}(y^D − a_i^D) | ζ^j a_i | m | m log D | span ≤ cost |
| Dickson D_N(y, ab) − a^N − b^N | ζ^j a + ζ^{−j} b | 2 | O(log N) | span ≤ cost |
| cyclic norm Res_T(T^M − 1, y − Φ), deg_T Φ = d' | Φ(x, ζ^j) | ≤ d'+1 | poly(d') log M | span ≤ cost |
| power/correspondence image of the above (Lemma C) | ψ(r) | ≤ δ·(old span) for curves | poly(δ)·s | span ≤ cost |
| (y−a)^A − (y−b)^A | (a − ζb)/(1 − ζ) | 2 | O(log A) | span ≤ cost |
| quadratic tower ((y² − α_k)² − …)² − α_1 | ±β_{k,j}, nested radicals | k = 3: 4 (8 roots) [P]; k ≥ 4: only Dickson (span 2) and repeated-root solutions found | O(k) + cost(α) | splitting variety is a (2,…,2,4,…,4,8,…) complete intersection of dimension k−1, general type for k ≥ 4–5 [C] |
| Kummer tower (…(y^{D_1} − a_1)^{D_2} − a_2 …) | nested radicals | needs A + ζB = c_ζ^{D'} for all ζ ∈ μ_D: conic for (D, D') = (3, 2), genus ≥ 1 otherwise; Fermat for D = D' ≥ 3 | O(k log D) | killed by Mason–Stothers [K] unless outer exponents are 2 |
| D-th powers on top of a tower: c_1^D + c_1'^D = c_2^D + c_2'^D | — | trivial solutions only for large D (Newman–Slater / Hayman [K]) | — | span ≤ 2 per pair |
| Kronecker sum: det(y − ⊕ A_i) | Σ_i λ_{i,e_i} | ≤ 2n | **= Knapsack norm**, not known easy | no information |
| Kronecker product: det(y − ⊗ A_i) | ∏_i λ_{i,e_i} | 2^n | = multiplicative Knapsack ∏_e (y − x^e); easy ⇒ ∏_{k<M}(y − q^k) easy ⇒ (y = 1 + εt, q = 1 + ε) Pochhammer border-easy | believed hard |
| group determinant of (ℤ/2)^n, generators only | Σ ± x_i | n | = Knapsack norm | no information |
| circulant, lacunary symbol Σ c_i T^{a_i} | Σ c_i ζ^{j a_i} | t | unknown; CRT exponents give sumsets Σ_i ζ_{p_i}^{j_i} c_i | no information |
| sumset of n cyclic sets ∏_{j∈(ℤ/D)^n}(y − Σ ζ^{j_i} a_i) | — | n (but Lemma C: d-th powers span C(n+d−1, d)) | n = 2 is the implicit equation of t ↦ (t^D, (1−t)^D) (ideas-pc-npc Idea 3(i)) | easy ⇒ Span false |
| G-orbit norms, G ⊂ GL_m finite, Q = P(y, invariants) | r∘σ | G-module generated by r | same problem (P must be an easy multiple of the minimal polynomial over ℂ[x]^G) | circular |
| Vandermonde / Moore determinants in char 0 | r_1..r_K | K | poly(K) | no gain |

### 1.4 Structural reason

- The only source of exponential degree in a circuit is iterated powering, whose Galois group is cyclic (Kummer). So the
  easy exponential root families are orbits of **cyclic groups μ_D acting on a space whose dimension is the number of
  additions** (y^D − a^D on a line, Dickson on a plane, cyclic norms on d'+1 dimensions).
- Composition towers have iterated-wreath Galois groups; complete splitting with *polynomial* roots is a ℂ(x)-point of the
  splitting variety of the tower. These are of positive genus / general type outside the torus cases, and function-field abc
  (Mason–Stothers, Brownawell–Masser) forces degenerate solutions, where roots differ by roots of unity.
- A small representation is necessary but not sufficient: (ℤ/2)^n ⊂ GL_n has a 2^n-orbit in dimension n, and its norm is
  Knapsack. What is missing there is a cyclic group of large exponent.
- In characteristic p the extra mechanism is additive: F_p^n acts by translations in dimension n+1. Lemma C turns it into
  large span. Nothing similar exists in characteristic 0 (finite subgroups of (ℂ[x], +) are trivial).

I could not turn this into a theorem. It does say what a counterexample would need: a rational (unirational) piece of a
tower's splitting variety that spans a large linear space.

### 1.5 Referee's test case Φ = ∏_{i≤n} (x_i + T^{2^{i−1}}), M = 2^n

Φ = Σ_{k<2^n} x^{[n]∖bits(k)} T^k, so the 2^n roots Φ(x, ζ^j) span 2^n dimensions (Vandermonde), degree n.
- Sum of roots = 2^n ∏ x_i. Power sums p_k = Σ_j Φ(ζ^j)^k are easy for k ≤ poly(n): the coefficient of T^{0 mod 2^n} in
  ∏_i (x_i + T^{2^{i−1}})^k is a product of n transfer matrices of a carry automaton with ≤ k+1 states [P]. So the norm is
  easy to polynomial order at y = ∞. That says nothing about the whole norm.
- Natural tower u_{i+1} = u_i², with norm of A + B u_i equal to A² − u_{i+1} B²: the u-degree of the intermediate polynomial
  doubles at each level (it is homogeneous of degree 2^k in (y, ∏_{i>k}(x_i + u_i))). No easy route.
- Border degeneration x_i = c_i^{−1}/ε, first order: the lacunary circulant ∏_ζ (y − Σ_i c_i ζ^{2^{i−1}}). Its root span is n,
  but by Lemma C its d-th powers span superpolynomially many dimensions. So: test case has an easy multiple ⇒ the lacunary
  circulant has a border-easy multiple ⇒ border-Span fails.
- The slope method of §3 does not settle it: under x_i = u_i τ^{w_i} the root valuations are Σ_{i ∈ S} w_i over few sets S.
- **Guess: no easy multiple. No proof, no reduction from a named hypothesis.** Cheap experiment: for n ≤ 4 compute the
  norm exactly and compare the rank of its "partial-derivative in y / shifted" matrices with y^{16} − 1 and with the
  Knapsack norm; this only detects gross structure.

## 2. What to avoid: slope counts are exponential for general circuits

**Gadget [P, N for n ≤ 9].** G_0 = y, H_0 = 1, G_{k+1} = τ^{ε_k}(G_k + H_k)², H_{k+1} = G_k·H_k, Q_n = G_n + H_n, with
ε_k = 4^{−k} (multiply all by 4^n to get integer exponents of poly(n) bits). All coefficients are positive, so there is no
cancellation and the Newton polygon is given by the (min,+) evaluation: g_{k+1} = 2 min(g_k, h_k) + ε_k, h_{k+1} = g_k + h_k,
hence g_{k+1} − h_{k+1} = ε_k − |g_k − h_k|. Starting from g_0 − h_0 = val(y), the zeros double at every step. Q_n has size
O(n), y-degree 2^n and **2^n distinct root valuations** Σ_k ± ε_k. Classically z = G/H satisfies z ↦ c(z + 2 + 1/z), a
folding map.

Consequences.
- No statement "a size-s polynomial over ℂ[τ] has poly(s) distinct root valuations" is true. Koiran–Portier–Tavenas–Thomassé's
  τ-conjecture for Newton polygons [K] is about sums of products of sparse polynomials and is not contradicted.
- The roots of Q_n are nested radicals, not polynomials, so this is not a counterexample to Span.
- Z(Q_n) is in P_ℂ and has exponentially many branches with distinct valuations. Any proof of Gap G must separate Ryser
  from these "tower sets".

## 3. Attack ideas

### Idea 1 — Slope monotonicity: unconditional separations for sparse-type tests, and a depth hierarchy  [rank 1]

Throughout, K is the completed algebraic closure of ℂ(u)((τ)) (u = (u_ij) new indeterminates), with valuation v, v(τ) = 1,
v trivial on ℂ(u). The residue characteristic is 0. For 0 ≠ f ∈ K[y], Sl(f) := {v(ρ) : f(ρ) = 0, ρ ≠ 0} (the negatives of
the slopes of the lower Newton polygon of f), and sl(f) := |Sl(f)|.

**Lemma S1 (monotonicity) [P].** Sl(f·h) = Sl(f) ∪ Sl(h). In particular Sl(N) ⊆ Sl(N·H) for every cofactor H ≠ 0, with no
condition on multiplicities. *Proof.* The roots of fh are the roots of f and of h. ∎

**Lemma S2 (sparse polynomials) [P].** If f has ≤ t monomials in y then sl(f) ≤ t − 1. *Proof.* The lower convex hull of
≤ t points (k, v(f_k)) has ≤ t − 1 edges, and the root valuations are the negatives of their slopes. ∎
Hence sl(∏_{j≤m} f_j^{a_j}) ≤ m(t − 1) for t-sparse f_j and any exponents a_j ≥ 1.

**Lemma S3 (Ryser roots) [P; N for n ≤ 8].** Index rows and columns by i, j ∈ {0, …, n−1}. Put ρ_i(j) := (j − i) mod n ∈
{0, …, n−1}, w_ij := n^i·ρ_i(j), and let σ be the substitution X_ij ↦ u_ij τ^{w_ij}. Then the 2^n − 1 polynomials g_E,
∅ ≠ E ⊆ {0..n−1}, satisfy v(σ g_E) = Σ_i n^i · min_{j∈E} ρ_i(j), and these values are pairwise distinct.
*Proof.* σ(Σ_{j∈E} X_ij) = Σ_{j∈E} u_ij τ^{w_ij}. For fixed i the exponents w_ij are distinct (ρ_i is a bijection), so the
valuation is min_{j∈E} w_ij = n^i·m_i(E) with m_i(E) := min_{j∈E} ρ_i(j) ∈ {0..n−1}. Valuations of products add, and the sign
±1 has valuation 0. The digits m_i(E) of the base-n number Σ_i n^i m_i(E) are determined by it. Finally ρ_i(j) = 0 iff
j = i, so i ∈ E iff m_i(E) = 0. Hence E is determined by v(σ g_E). ∎
The exponents w_ij have O(n log n) bits; τ^{w_ij} is never computed by the machine, it only appears in the analysis.

**Lemma S4 (nonvanishing) [P].** σ is injective on monomials of ℂ[X, y] (the u-part records the monomial). So σQ ≠ 0 for
Q ≠ 0, a t-sparse polynomial in (X, y) becomes a polynomial with ≤ t monomials in y over ℂ[u, τ], and σ is a ring
homomorphism, so σ(N·H) = σN·σH.

**Theorem S (ΠΣ-sparse tests) [P].** Let 𝒯 be an algebraic computation tree over ℂ (operations +, −, ×, ÷, constants,
tests "f = 0?") deciding A_g for Ryser g. Along the generic path write each tested function that is not identically zero,
and each divisor, as num/den as in y2 Lemma 1, and let P be the product of these numerators and all denominators. Suppose P
is a product of ≤ R polynomials (with any multiplicities), each with ≤ t monomials in (X, y). Then **R·(t − 1) ≥ 2^n − 1**.
In particular, for trees whose every test and divisor is a product of ≤ m powers of t-sparse polynomials and whose generic
path has T such nodes, T·m·(t − 1) ≥ 2^n − 1.
*Proof.* By y2 Lemma 1, every y − g_E divides P. By S4, σP ≠ 0 and y − σg_E divides σP in K[y], so by S1 and S3
sl(σP) ≥ 2^n − 1. By S1, S2 and S4, sl(σP) ≤ R(t − 1). ∎
Remarks. (i) The degrees of the tests are unbounded, so tests such as y^D − x^D are allowed and degree counting gives
nothing. (ii) The argument is blind to multiplicities and to the cofactor. (iii) It works verbatim over any algebraically
closed field of any characteristic. (iv) The same proof gives the bound 2^n for the multiplicative Knapsack
{(x, y) : ∃e ∈ {0,1}^n, y = ∏ x_i^{e_i}} with x_i ↦ u_i τ^{2^i}. It gives nothing for additive Knapsack (n valuations).
(v) pc1's Descartes bound (a polynomial with τ distinct powers of y contains ≤ 2τ − 2 Ryser branches) counts powers of y
only, with arbitrary coefficients; S2 has the same feature: "t-sparse" may be read as "≤ t distinct powers of y".

**Theorem S' (cancellation-free tests of alternation depth Δ) [P].** Call a circuit *cancellation-free* if it uses +, × and
positive real constants only. Let C be a cancellation-free circuit in (X, y) with unbounded fan-in gates arranged in Δ
alternating layers of sums and products (a product gate may raise its inputs to arbitrary powers), with s wires in total,
whose inputs are variables and constants. Then sl(σC) ≤ (s/Δ)^Δ. Consequently a tree deciding A_g whose generic path
consists of T tests, each computed by such a circuit, satisfies **T·(s/Δ)^Δ ≥ 2^n − 1**, i.e. s ≥ Δ·((2^n − 1)/T)^{1/Δ}.
*Proof.* For a gate w let φ_w(θ) := v(σC_w(η)) for η ∈ K generic of valuation θ. Since all coefficients of σC_w as a
polynomial in (u, τ, y) are positive reals, no cancellation occurs and φ is computed by the (min, +) circuit: φ = Σ a_i φ_i
at a product gate, φ = min_i φ_i at a sum gate, φ linear at inputs. Each φ_w is concave piecewise linear; let p(w) be its
number of linear pieces, so sl(σC_w) = p(w) − 1. At a product gate the breakpoints are the union of those of the inputs:
p(w) ≤ Σ_i p(w_i). At a sum gate: on a linear piece of φ_{w_i} the set where φ_{w_i} ≤ all other φ_{w_l} is a sublevel set of a
convex function, hence an interval; so each piece of each input contributes at most one piece of the minimum, and again
p(w) ≤ Σ_i p(w_i). By induction p(w) ≤ the number of input-to-w paths, which is ≤ ∏_ℓ s_ℓ ≤ (s/Δ)^Δ, s_ℓ the number of
wires into layer ℓ. ∎

**Theorem G (tightness; "what to avoid") [P; N by `c2.py`, `c3.py`].** For all r ≥ 2 and L ≥ 1 there is a cancellation-free
circuit Q_{r,L}(τ, y) with 2L alternating layers and O(rL) gates such that sl(Q_{r,L}) ≥ r^L.
*Construction.* G_0 = y, H_0 = 1. Given (G, H) put M_j := c_j G^j H^{r−j} (j = 0..r, c_j = τ^{γ_j}), G' := Σ_{j even} M_j,
H' := Σ_{j odd} M_j, and Q := G_L + H_L. Tropically, with δ = g − h: g' − h' = ψ_ev(δ) − ψ_od(δ) where
ψ_ev = min_{j even}(jδ + γ_j), ψ_od = min_{j odd}(jδ + γ_j). Choosing the γ_j so that the lines jδ + γ_j are consecutive tangents
of a concave function with r equally spaced breakpoints in (−ω, ω), the difference ψ_ev − ψ_od changes sign r times on
(−ω, ω). If δ sweeps (−ω, ω) monotonically K times, then δ' changes sign rK times, each time sweeping an interval
(−ω', ω') with ω' = ω/(4r). So δ_L has r^L sign changes, each a breakpoint of min(g_L, h_L). The γ's are rationals with
denominator (4r)^L; clear them by rescaling τ. For r = 2 this is the gadget of §2. ∎ [N: r^L edges exactly for
(r, L) = (2,5), (3,4), (4,3), (5,3).]

**Where the depth hierarchy stands (answer to the lead's question 3).**
- *Lower bound.* Depth Δ, size s, T tests: T·(s/Δ)^Δ ≥ 2^n − 1. So polynomial size forces Δ ≥ (n − log T)/log s =
  Ω(n / log n); size is 2^{Ω(n/Δ)}; it is 2^{n^{Ω(1)}} for every Δ ≤ n^{1−ε}, and superpolynomial for every Δ = o(n / log n).
- *Limit of the method.* Theorem G with r = s/Δ gives (s/2Δ)^{Δ/2} slopes at depth Δ and size s. So the maximal number of
  slopes at depth Δ and size s is (s/Δ)^{Θ(Δ)}, and slope counting cannot give more than the bound above; at
  Δ = 2n / log n and size n^{O(1)} a cancellation-free circuit already has 2^n slopes.
- *So the largest depth with an exponential lower bound is Δ = n^{1−ε} (bound 2^{Ω(n^ε)}), the largest depth with a
  superpolynomial bound is Δ = o(n / log n), and at Δ = Θ(n / log n) the method provably stops.* This is tight for the
  *method*; whether A_g itself has polynomial-size cancellation-free tests at depth Θ(n / log n) is open (Idea 7).
- *Hierarchy statement for sets in P_ℂ.* Z(Q_{2,n}) is decided by one cancellation-free test of depth 2n and size O(n),
  while by S' and S1 every depth-Δ cancellation-free tree for it has T·(s/Δ)^Δ ≥ 2^n. (For the lower bound one needs
  that a tree deciding Z(Q) has a generic-path product divisible by each irreducible factor of Q; take Q_{2,n} with generic
  constants, or use its radical.) So "depth 2n, size O(n)" is not contained in "depth o(n / log n), polynomial size"
  for cancellation-free decision trees. A fine hierarchy (Δ versus Δ/4) only separates s from about s².

**Why.** Elementary, unconditional, unbounded degree, multiplicity-blind. It is the first invariant in this project that
the cofactor cannot damage and that is exponential for the Ryser norm.
**Main risk.** Strength, not correctness. The models are weaker than P_ℂ (Theorem G gives sets in P_ℂ outside them), the
sparse case has a folklore real analogue (Descartes), and [T26] is not used.
**First step (≤ 3 h).** pc1 checks S1–S4, S, S', G line by line (the only analytic input is "root valuations = slopes of
the Newton polygon" over a valued field) and writes the tree model precisely.

### Idea 2 — Slopes with cancellation: sums of k products of powers of sparse polynomials  [rank 2]

Same K and notation. The class: Q = Σ_{i≤k} c_i ∏_{j≤m} f_ij^{a_ij}, f_ij ∈ K[y] with ≤ t monomials, c_i ∈ K, exponents a_ij ∈ ℤ
arbitrary (negative allowed; then Q is a rational function and Sl counts zeros).

**Lemma R (non-archimedean Rolle, residue characteristic 0) [P, uses standard Newton-polygon theory on annuli].** Let
J ⊂ ℝ be an open interval and g a rational function over K with no poles of valuation in J. Then
#(Sl(g) ∩ J) ≤ #(Sl(g') ∩ J) + 2.
*Proof.* On the annulus {v(y) ∈ J}, g is a convergent Laurent series Σ_{k∈ℤ} g_k y^k, and the valuations in J of its zeros
are the breakpoints in J of φ_g(θ) = min_k (v(g_k) + kθ). Since v(k) = 0 for every integer k ≠ 0, φ_{y g'}(θ) =
min_{k≠0}(v(g_k) + kθ), so φ_g = min(φ_{yg'}, v(g_0)). The minimum of a concave function and a constant has the breakpoints
of the concave function (some of them) and at most 2 crossing points. ∎
(This fails in residue characteristic p, as it must: Frobenius and the Moore polynomial.)

**Theorem 2T (two terms) [P].** For Q = A − B with A = c ∏_{j≤m} f_j^{a_j}, B = c' ∏_{j≤m} h_j^{b_j}, all f_j, h_j t-sparse:
**sl(Q) ≤ sl(P) + 4m(t − 1) + 2 ≤ 2m·t^{2m} + 4m(t − 1) + 2**, independently of the exponents, where
P := Π · (Σ_j a_j f_j'/f_j − Σ_j b_j h_j'/h_j), Π := ∏_j f_j h_j, is a polynomial with ≤ 2m·t^{2m−1}·t monomials.
*Proof.* Let g := A/B − 1 = Q/B. Its poles lie among the zeros of the h_j (and f_j with a_j < 0): at most 2m(t − 1)
valuations in general, m(t − 1) if all exponents are positive; they cut ℝ into ≤ m(t − 1) + 1 open intervals J
(positive-exponent case). On each J, g' = (A/B)·P/Π, whose zeros have valuations in Sl(P) or among the f_j-slopes. Apply
Lemma R on each J and add the endpoints:
sl(Q) ≤ [sl(P) + m(t − 1)] + 2[m(t − 1) + 1] + m(t − 1). ∎
*Special case, sharper.* a^D − c·b^D = ∏_{ζ^D = c}(a − ζb): the coefficient of y^e in a − ζb has valuation
min(v(a_e), v(ζ b_e)) except for at most one ζ per exponent e; so all but ≤ t factors have the same Newton polygon and
sl ≤ (t + 1)(2t − 1) [P].

**Theorem kT (k terms) [P sketch: same step iterated].** Dividing by the last term and differentiating turns a k-term sum
Σ_i R_i into (1/Π)·Σ_{i<k} R_i P_i, a (k−1)-term sum over the enlarged family {f_ij} ∪ {P_i}, where P_i has ≤ M·t^M
monomials, M := km. Lemma R costs 3·(number of slopes of the current family) + 2 per step. Hence
sl(Q) ≤ F(k, m, t), a function independent of the exponents; crude bookkeeping gives F ≤ t^{(2km)^{k}}.
**Corollary (machines).** A tree deciding A_g whose generic-path tests are sums of ≤ k products of ≤ m powers of t-sparse
polynomials needs T·F(k, m, t) ≥ 2^n − 1 tests. For constant k, m this is exponential in n for t up to 2^{cn}. These tests
may cancel and have unbounded degree; this is the "shallow circuits with high-powered inputs" class of Koiran [K].
The sparse polynomial P is itself a sum of 2m products of 2m sparse polynomials without powers, so the bounds of
Koiran–Portier–Tavenas–Thomassé for Newton polygons [K] improve sl(P) below t^{2m}.

**Exact conjecture [C] (function-field τ-conjecture for slopes).** sl(Σ_{i≤k} ∏_{j≤m} f_ij^{a_ij}) ≤ (k·m·t)^{c} for an absolute
constant c, for all exponents. By Theorem G it is false without the depth-4 shape: Q_{2,n} has depth 2n and 2^n slopes
(written as a 2-term sum its inner polynomials have sparsity 2^{n−1} + 1, consistently). The conjecture would give
A_g ∉ P for all depth-4 "ΣΠ^{pow}Σ^{sparse}" tests of polynomial size, a KPTT-type statement that is now a statement about
valuations only, with no real roots and no permanent.

**Why.** First restricted model with cancellation. The exponent-independence is the whole point, and the Rolle step
handles it in two lines.
**Main risk.** (i) The annulus Newton-polygon theory must be quoted correctly (Lazard; completeness and algebraic closure
of K). (ii) The k-term bookkeeping is only sketched and the bound is a tower in k. (iii) Polynomial dependence on k, m is
as hard as KPTT.
**First step (≤ 3 h).** Write Lemma R and Theorem 2T in full; sanity-check 2T numerically on a^D − b^D and on
(1 + τy)^a (1 + y²)^b − (1 + y)^c with moderate exponents (exact Newton polygons); then do the k = 3 bookkeeping.

### Idea 3 — [T26]-based "controlled cofactor" theorems (degree-tight machines)  [rank 3]

**Theorem D [P from y2 Cor. 3.2 + T26].** If a tree decides A_g (Ryser) and the product P of its generic-path tests satisfies
deg_y P ≤ #{distinct g_e} + c, then P = N^red·H with deg_y H ≤ c, H has ≤ c irreducible factors of y-degree ≤ c, and (if also
their total degree is poly) L̄(H) ≤ poly(T, c); Lemma 3 gives L̄(per_n) ≤ poly(T, c, n). So T is superpolynomial for c = n^{O(1)}.
**Threshold for bounded-degree tests (answer to (d)).** Below Σ deg < 2^n the statement is trivial by counting branches,
with no [T26]. Bürgisser's factor theorem buys exactly an *additive* poly(n) window above the branch count, or more
generally any cofactor that is a product of poly many factors of poly degree with arbitrary multiplicities. At
deg P = 2·2^n the cofactor can be another norm and the full problem is back. There is no multiplicative threshold 2^{o(n)}.
**Why.** It is the only restricted statement here that uses the permanent bound.
**Main risk.** The model ("degree budget") is artificial; x-degree of the factors of H must be controlled as well.
**First step (≤ 3 h).** State it for machines that output a certificate for their cofactor, and for "almost exact" tests
f_i = (product of branches)·(low-degree junk). Check multiplicities via N^red versus N.

### Idea 4 — Wronskian / differential form of span (a)  [rank 4]

**Setup [P].** Restriction to lines is useless (span ≤ d+1 in one variable). Use instead the derivation
D = Σ_i λ_i x_i ∂_i with λ_i linearly independent over ℚ; its field of constants in ℂ(x) is ℂ. Then r_1..r_k are linearly
independent over ℂ iff the ordinary Wronskian W_D(r_1..r_k) ≠ 0. On Z(Q) the lifted field D̃ = D − (DQ/Q_y)∂_y is tangent,
and y_j := D̃^j y ∈ ℂ(x, y) has size poly(s, j) (Baur–Strassen plus series composition). So
**dim span Roots(Q) = the least k such that y_0, …, y_k are ℂ(x)-linearly dependent on the union B of the polynomial
branches** — the order of the linear ODE satisfied by y on B. For y^D = x_1^D: D̃y = λ_1 y, order 1.
**Why.** It turns span into the rank of an easily computed family of functions on Z(Q), and it is the right tool for Idea 2:
for a root r of Σ_i T_i with T_i = ∏_j f_ij^{a_ij}, the terms T_i(x, r) are dependent and DT_i/T_i has low degree whatever
the exponents, which is the Wronskian proof of function-field abc.
**Main risk.** Nothing links the order of that ODE to L(Q) for general circuits; for N_g itself the order is 2^n − 1 and
N_g is merely hard, not impossible. I expect it to prove sparse / few-term Span bounds only, with a loss exponential in
the number of terms (y2 §9(4) met the same wall).
**First step (≤ 3 h).** Prove: a root r of a trinomial-type Q = T_1 + T_2 + T_3 (products of powers of polynomials of degree
≤ δ in (x, y)) has either bounded exponents' effect (abc) or all T_i/T_l constant; in the second case show the roots lie on
≤ poly curves.

### Idea 5 — Galois / representation form (b)  [rank 6]

**Assessment.** The Galois group of N_g over the invariant field does not constrain multiples: an easy Q need not be
invariant, making it invariant costs |G|, and a circuit polynomial can have any monodromy. What survives is the
representation: the roots span a G-module V, and Span says dim V is small. For G = (ℤ/2)^n acting by column signs (Glynn's
formula: g(δ) = χ(δ)∏_i Σ_j δ_j z_j x_ij, sum 2^n (∏z_j)² per X) the statement becomes "easy multiple ⇒ Fourier-sparse root
function". For cyclic G it is "easy ⇒ low T-degree symbol", and sparse symbols of high degree are open (lacunary circulant).
**Usable part.** For norms with a large *reductive* symmetry (resultant of n quadrics under GL_n × GL_n) the cofactor may
be assumed a highest-weight vector, at border cost poly(n): lowest term under a generic one-parameter subgroup, then
lim ε^{a} exp(ε^{−1}E_α)·Q for each simple root. For the Ryser norm only a torus is available (y2 §9(3)).
**Main risk.** Highest-weight cofactors are still an infinite family; no mechanism forces H = invariant·power.
**First step (≤ 3 h).** n = 2 (two binary quadrics): list the covariants and check whether an HWV multiple of Res can have
a cofactor outside ℂ[Res, basic covariants]. Drop the idea if the answer is "anything".

### Idea 6 — Non-hypersurface sets (e)  [rank 5]

**Assessment [P sketch].** High codimension does not escape the y1 barrier. If cl(A) has an irreducible component W of any
codimension and low degree, the generic point of W follows a path whose zero-tests cut out W as a component, and Newton
tracking as in Lemma L recovers W (its generic projections) when the scheme is reduced or curvilinear. So the escape
hatches are the same two: exponential degree, or Jacobian defect ≥ 2. Also, in codimension ≥ 2 the ideal has many elements
and the machine supplies just one, of uncontrolled order; when I(W) is graded, lowest homogeneous components stay in I(W)
but may have exponential degree.
**Positive by-product.** Dual hypersurfaces Y^∨ of easy varieties Y are in NP_ℂ with a reduced verifier (the conormal
variety is generically smooth and birational onto Y^∨), so by Lemma L every dual hypersurface of polynomial degree is
exactly easy. That is a clean corollary for y1, not a route to P_ℂ ≠ NP_ℂ.
**Candidate.** W = σ_r, tensors of rank ≤ r in ℂ^n ⊗ ℂ^n ⊗ ℂ^n: membership is NP_ℂ-hard (Schaefer–Štefankovič [K]), the ideal
is GL_n³-stable, and Idea 5's highest-weight reduction applies. P_ℂ(nu) = NP_ℂ(nu) would give a border-easy highest-weight
equation of every σ_r. A theorem "every nonzero element of I(σ_r) is hard" in the style of Andrews–Forbes for determinantal
ideals [K] would finish; nothing connects it to [T26].
**Main risk.** Equations of σ_r are unknown even in low degree; this replaces one open problem by a harder-looking one.
**First step (≤ 3 h).** Check whether the Andrews–Forbes reduction for determinantal ideals survives unbounded degree in the
border model (it uses group actions and limits, which are free there). If yes, it is a degree-free "all multiples hard"
template, the first of its kind.

### Idea 7 (wild) — The tropical cofactor problem

For a cancellation-free Q, val Q = (min,+)-circuit value, so Q = N_g·H gives
**F(w, τ) = Σ_E min(τ, h_E(w)) + C(w, τ)**, h_E(w) = Σ_i min_{j∈E} w_ij, with F computed by a small (min,+) circuit and C an
arbitrary concave piecewise-linear function. Prove that no polynomial-size (min,+) circuit computes such an F. This is a
monotone circuit lower bound "up to an arbitrary concave cofactor", a toy model of Gap G in which the cofactor problem is
present but the objects are polyhedral. Jerrum–Snir and Jukna-type arguments [K] give exponential (min,+) lower bounds for
the tropical permanent; here the target is the corner locus, not the function.
Sanity: for one row (additive Knapsack) F = 2^n Σ_j min(τ, w_j) works, so the problem is easy exactly where it should be;
the gadget of §2 shows fold sets {Σ ± ε_k} are easy, so the proof must use that {h_E(w)} is not a fold set uniformly in w.
**Why.** A full solution is "P ≠ NP for cancellation-free BSS machines of unbounded depth", beyond Idea 1's depth bound, and
it would show what a cofactor-proof argument looks like.
**Main risk.** Tropical circuits with arbitrary concave slack may be much stronger than expected; the statement may be false.
**First step (≤ 3 h).** n = 2, 3: enumerate the cells of w-space, write the constraint "breakpoints of F(w, ·) ⊇ {h_E(w)}" and
search for small (min,+) circuits by hand or by brute force; decide whether a fold construction exists for n = 2.

## 4. Ranking (probability × value)

| rank | idea | probability of a theorem | value |
|---|---|---|---|
| 1 | Idea 1: slope monotonicity, Theorems S, S', G (depth hierarchy) | proofs written here, ≈ 0.9 they survive refereeing | modest but real: first cofactor-proof invariant, unconditional restricted separation |
| 2 | Idea 2: slopes with cancellation (Theorem 2T proved here; k terms sketched; polynomial bound conjectured) | ≈ 0.8 for 2T, 0.6 for fixed k, < 0.1 for the polynomial conjecture | medium: a model with cancellation and unbounded degree |
| 3 | Idea 3: degree-tight / controlled-cofactor theorems from [T26] | ≈ 0.8 | low–medium: uses the permanent bound, artificial model |
| 4 | Idea 4: Wronskian form of span | ≈ 0.3 (few-term cases) | medium as a tool for Idea 2 |
| 5 | Idea 6: non-hypersurface sets; dual-variety corollary; AF template | ≈ 0.6 for the corollaries, < 0.05 for the target | low–medium |
| 6 | Idea 5: Galois / highest-weight reduction | ≈ 0.2 | low |
| 7 | Idea 7: tropical cofactor problem | ≈ 0.15 | high if true |
| — | Lemma C and its two consequences (§1) | proved | calibration: retire Span as a target |

**Top two: Idea 1 and Idea 2.**

## 5. Honest assessment of the original problem

Not within reach. After this round the picture is:
- The Span Conjecture does not use [T26], implies Knapsack-multiple hardness, and fails in characteristic p. It is a
  τ-type conjecture and should be dropped as a "reduction".
- The one invariant that survives every cofactor (Newton-polygon slopes) is exponential for easy polynomials (§2).
- [T26] enters only through Lemma 3 (the cofactor is border-hard), and hard × hard = easy is possible.
- So Gap G still needs an idea that separates the Ryser norm from tower sets and from char-p additive structure at
  exponential degree. I do not see one. Restricted-model theorems (Ideas 1–3) are what can be proved now.

## 6. Checks

- `span/c2.py` [N]: gadget, Newton polygon edges = 2^k for k = 1..9 (exact rational tropical arithmetic); Ryser valuations,
  2^n − 1 distinct for n = 2..8.
- `span/c3.py` [N]: base-r gadget of Theorem G, r^L edges for (r, L) = (2,5), (3,4), (4,3), (5,3).
- `span/c4.py` [N]: char 2, dim span{(e·x)^d} = Σ_{j≤k} C(n, j) for d = 2^k − 1, (n, k) = (3..5, 2), (4..6, 3) (6, 10, 15; 14, 25, 41).
  The identity det M(C_y) = ± ∏_v (y − v^d) is the standard resultant formula Res_w(w^d − y, M(w)); the sympy script `c1.py`
  that was to confirm it symbolically did not finish in time and was stopped, so that identity is [P], not [N].
- Not verified first-hand: Mason–Stothers / Newman–Slater statements, KPTT, Schaefer–Štefankovič, Andrews–Forbes (all from
  memory). The general-type claim for the quadratic tower (§1.3) is a canonical-class count on a singular complete
  intersection, hence [C].

## 7. Barrier: single valuations cannot prove Gap G (answer to pc1's question: **yes**)

Added after pc1's question. Notation of Idea 1 (K, v, Sl, σ_w : X_ij ↦ u_ij τ^{w_ij}). All statements [P]; script `span/c5.py` [N].

### 7.1 Exact slope set of the gadget

Generalised gadget. Fix p ≥ 1, a constant H_0 with v(H_0) = η_0, constants c_k with v(c_k) = ε_k > 0 (k = 0..n−1), all with
positive coefficients (monomials in τ, or in the X_ij). G_0 := y^p, G_{k+1} := c_k (G_k + H_k)², H_{k+1} := G_k H_k,
Q := G_n + H_n. Then deg_y Q = p·2^n and Q(0) ≠ 0.

**Proposition 7.1.** If the ε_k are strictly superdecreasing, ε_k > Σ_{l>k} ε_l for all k, then
**Sl(Q) = { (η_0 + Σ_k σ_k ε_k)/p : σ ∈ {±1}^n }**, exactly 2^n values, each carried by p roots.
*Proof.* No cancellation, so with g_k, h_k the (min,+) values at θ = v(y) and δ_k := g_k − h_k:
δ_0 = pθ − η_0 and δ_{k+1} = ε_k − |δ_k| (because g_{k+1} = 2 min(g_k, h_k) + ε_k, h_{k+1} = g_k + h_k). Let P_n := {0} and
P_k := {δ : ε_k − |δ| ∈ P_{k+1}}, so that δ_n = 0 iff δ_k ∈ P_k iff δ_0 ∈ P_0. By downward induction P_k is symmetric, equals
{Σ_{l≥k} σ_l ε_l}, has 2^{n−k} elements, and every c ∈ P_{k+1} has |c| ≤ Σ_{l>k} ε_l < ε_k; so ε_k − |δ| = c has the two
solutions ±(ε_k − c), and {±(ε_k − c)} = {±ε_k + c'} by symmetry. The sums are pairwise distinct by superdecrease. δ_n is
piecewise linear in θ with all slopes ±p, so it changes sign at each of its 2^n zeros, and each is a breakpoint of
min(g_n, h_n), i.e. a root valuation of Q. Q is a polynomial in y^p of degree 2^n in y^p with nonzero constant term, so
there are at most 2^n distinct root valuations. ∎ [N: random rational superdecreasing ε, n ≤ 7, exact agreement.]
Without superdecrease the slope set is smaller and I have no closed form (my guess "preimage recursion with the
constraint c ≤ ε_k" failed a random test; with ε_k = 2^k increasing most sign patterns are lost). So take ε_k = 2^{n−1−k}·c,
decreasing, not ε_k = 2^k.

**Corollary 7.2 (arithmetic progressions).** With v(M) = c > 0, c_k := M^{2^{n−1−k}}, H_0 := M^{2^n − 1}, G_0 := y^p:
Sl(Q) = {(2c/p)·k : k = 0, 1, …, 2^n − 1}. Size O(n + log p) with shared squarings.
*Proof.* Σ_k σ_k 2^{n−1−k} runs over the odd integers m with |m| ≤ 2^n − 1, and (c(2^n − 1) + cm)/p = (2c/p)·k. ∎

### 7.2 The barrier

**Theorem 7.3 (pc1's substitution).** Let w_ij = 2^i for j ≠ i, w_ii = 0 (i, j = 1..n), so that Sl(σ_w N_g) =
{Σ_{i∉E} 2^i : E ≠ ∅} = the even integers in [0, 2^{n+1} − 2). Let M := X_12 (v(σ_w M) = 2) and
B(X, y) := Q of Corollary 7.2 with p = 2: G_0 = y², H_0 = X_12^{2^n − 1}, c_k = X_12^{2^{n−1−k}}.
Then B has positive integer coefficients, circuit size O(n), and **Sl(σ_w B) = all even integers in [0, 2^{n+1}) ⊇
Sl(σ_w N_g)**. [N: n ≤ 8.] B is not a multiple of N_g (it involves one variable X_12 only).
So no argument that uses only the set of root valuations under this substitution can show that N_g has no easy multiple;
it cannot even distinguish N_g from a factor of an O(n)-size positive polynomial.

**Theorem 7.4 (every integral monomial substitution, and polynomially many at once).**
(a) For every weight matrix w with non-negative integer entries of ≤ b bits, not all zero, there is a positive polynomial
B_w(X, y) of size O(n(b + log n)) with Sl(σ_w B_w) ⊇ {0, 1, …, 2^L − 1} ⊇ Sl(σ_w N_g), where 2^L > Σ_i max_j w_ij.
*Proof.* Pick X_ij with c := w_ij > 0, M := X_ij, p := 2c, and L levels in Corollary 7.2: the slope set is {0, …, 2^L − 1}.
Every v(σ_w g_E) = Σ_i min_{j∈E} w_ij is an integer in that range. y^{2c} and the powers of M cost O(b + L) gates. ∎
Rational weights reduce to integer ones by rescaling τ. Any ring-valued "monomial" substitution X_ij ↦ u_ij τ^{w_ij} is
covered; so is any substitution after which the root valuations lie in a cyclic group and a poly-bit range.
(b) For any polynomially many such weight matrices w^{(1)}, …, w^{(q)}, the product B := ∏_r B_{w^{(r)}} has size
O(q·n(b + log n)) and Sl(σ_{w^{(r)}} B) ⊇ Sl(σ_{w^{(r)}} N_g) for every r (Lemma S1: slopes of a product are the union).
(c) The same holds on whole cones of real weights when the rows are hierarchically scaled: the base-r gadget of Theorem G
with symmetric zero sets D_i = ±{w_ij − w_i1 : j} (constants are monomials X_ij/X_i1 after clearing denominators) realises
the sumset Σ_i (w_i1 + D_i) ⊇ Sl(σ_w N_g), by the same proof as 7.1, provided max D_{i+1} < ½·(minimal gap of D_i) and the
order of the entries in each row is fixed. One polynomial per chamber; exponentially many chambers.

**What is not covered: all weights simultaneously.** A single B with Sl(σ_w B) ⊇ Sl(σ_w N_g) for *all* w is, for generic
coefficients, the same as the containment of tropical hypersurfaces Trop(B) ⊇ Trop(N_g) = ∪_E graph(h_E),
h_E(w) = Σ_i min_{j∈E} w_ij, in ℝ^{n²+1}. The constructions above do not give this: B_w uses the arithmetic of one w
(a monomial of valuation c and the exponent 2c), and (c) uses one chamber. What I can say:
- Trop(N_g) ⊆ Trop(M_n) for the multiplicative n-ary Knapsack norm M_n = ∏_{j∈[n]^n} (y − ∏_i X_{i j_i}) (the minimum is
  attained by some j). So a small B with Trop(B) ⊇ Trop(M_n) — for instance an easy multiple of M_n, a Kronecker-product
  characteristic polynomial — would be a universal barrier. M_n is believed hard, and Theorem S applies to it.
- For one row (additive Knapsack) the universal B exists trivially: ∏_j (y + X_j), n roots, because there are only n
  functions h_E.
- For positive B the question is exactly Idea 7 (the tropical cofactor problem): is Σ_E min(θ, h_E(w)) + (concave) computed
  by a small (min,+) circuit?
**So "many valuations at once" is the next method, and it must use super-polynomially many weight vectors, or the
piecewise-linear dependence on w itself.** Any argument that looks at poly(n) integral valuations, one at a time or jointly
through their slope sets, is blocked by 7.4(b). A concrete formulation of the next step: prove that no polynomial of size
n^{O(1)} has a tropical hypersurface containing ∪_E graph(h_E) unless it is "N_g-like"; first for positive polynomials
(Idea 7), where it is a monotone-circuit statement.

**Robustness summary.** One substitution: barrier, O(n) size (7.3). Every integral monomial substitution: barrier, with a
polynomial depending on w (7.4a). Polynomially many at once: barrier (7.4b). All real weights at once / the tropical
variety: open, equivalent to a tropical containment problem; not a barrier yet and not a proof method yet.
Theorems S, S′, 2T are unaffected: they bound the slope count of *restricted* tests, and 7.3 only says that the
restriction cannot be removed.
