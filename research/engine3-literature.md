# Engine 3 literature: what is known about beating e(K) ≈ 1/log K for the clique sum

Date 5 Nov 2026. Scope: the four items of the research brief (asymptotic spectrum of graph
tensors; beyond-rank evaluation of tensor networks; sums-of-squares composition and crossings;
Oct–Nov 2026 preprints). Sources were read from arXiv full texts (CVZ19, CVZ18, AKK22, HWY11,
Hrubeš CCC'24 and ECCC TR24-099, Christandl–Zuiddam surgery, Zhou 2610.34273, Brand et al.
2602.11975), from the arXiv API abstracts of the rest, from the Hexagon API, and from the local
texts of hexagon:2610.00577 (App. B, G, H) and arXiv:2610.41622 (§2, §4, §5). Tags: **[R]**
statement sourced from the paper (section/theorem given); **[C]** my assessment or derivation.

Problem recalled (Majdoddin 2610.41622, §2.1, Prop. 2.4) [R]: the (K, λ)-clique sum Z is the
contraction of T_K = GT_2(K_K)^{⊗λ} (edge dimension N = 2^λ) against K arbitrary tables; cost
2^{eS}, S = C(K,2)λ. Ladder: input floor e ≥ 2/K (every algorithm); flattening floor
e ≥ ⌊K²/4⌋/C(K,2) → 1/2 for rank, border rank and asymptotic rank alike; width bound
e ≥ ⌈K/3⌉(K−⌈K/3⌉)/C(K,2) → 4/9 for contraction trees (the AKK branchwidth bound). Signed Network
Sums (Def. 2.3) contain both and have no lower bound above 2/K at any fixed K. Anthropic's
recursion gives e(K) ≈ (3x₀+6)/log K with per-level factor ρ = 1/√2 (Theorem A(a), App. B);
Majdoddin proves 1/e(K) ≤ log₂K for grid algorithms (Thm 4.13) and ≤ (log₂K)³ for balanced
homogeneous two-merge rewrite-and-merge (Thm 4.12), with the hyperedge configurations of his
Open Problems 1 and 5 as the only door.

**[C] Framing that the literature makes precise.** A polynomial decay e(K) ≤ K^{−β} with
K ≤ m^{1/q} nodes available at m clauses gives time 2^{s n m^{−β/q}} = 2^{n^{1−β/q}} at linear
density; that is exactly a refutation of the Satisfiability Hypothesis / Weak ETH of the MIT
Hardness Group's 2611.02650 (§4 below). Majdoddin's Cor. 4.21(a) says rewrite-and-merge gives at
best 2^{Ω(sn/log³n)}, so "beat 1/log K" = "break SH inside Signed Network Sums"; every obstacle
below should be read at that altitude.

---------------------------------------------------------------------------------------------------

## 1. Asymptotic spectrum and asymptotic rank of graph and complete-graph tensors

### 1.1 Christandl–Vrana–Zuiddam, "Asymptotic tensor rank of graph tensors: beyond matrix multiplication", Comput. Complexity 28 (2019) 57–111, arXiv:1609.07476

* **[R] Objects.** T(G) = ⊗_{edges} (2-dimensional identity), legs grouped at vertices
  (Thm 1.1.1); T(K₃) is the 2×2 matrix multiplication tensor; τ(T(G)) = ω(T(G))/|E| is the
  exponent per edge, ω(T(G)) = log₂ of the asymptotic rank of T(G). Our T_K at N = 2^λ is
  T(K_K)^{⊗λ}, so Majdoddin's e_rank(K) is exactly τ(T(K_K)).
* **[R] Results on K_k.** Theorem 1.2.2: for k ≥ 2 and q ≥ 1, τ(T(K_k)) ≤ log_q of
  ((q+2)/2) divided by the monomial subexponent q_M(D_{(2,k−2)}) of the weight-(2,k−2) Dicke
  tensor (a k-party Coppersmith–Winograd construction); Corollary 1.2.5: q_M(D_{(2,2)}) =
  q(D_{(2,2)}) = 1; **Corollary 1.2.6: for every k ≥ 4, τ(T(K_k)) ≤ min_{q≥2} log_q((q+2)/2) =
  log₇(9/2) ≈ 0.772943** (ω(T(K₄)) ≤ 4.63766,
  the "N^{4.638}" of Majdoddin's Table 2). Theorem 1.1.25 (covering): τ(T(K_k)) is nonincreasing
  in k; eq. (8) (flattening, Thm 1.1.19/1.1.20): τ ≥ 1/2 + 1/(2(k−1)) (k even), 1/2 + 1/(2k)
  (k odd); hence if ω = 2 then τ(T(K₃)) = τ(T(K₄)) = 2/3 (the K = 4 rank floor N⁴ is tight at
  ω = 2 in the rank model).
* **[R] Questions.** Problem 1.2.1 (value of τ(T(K_k)), k ≥ 4); Question 1.3.1: is there k ≥ 5
  with τ(T(K_k)) < 2/3?; Question 1.3.2: is ω(T(G)) = maxcut(G) for every G? (known for
  bipartite G; for G = C₃ it is ω = 2). Both are now answered: see Zhou (§1.6).
* **[R] Cycles.** Via Christandl–Zuiddam, "Tensor surgery and tensor rank", Comput. Complexity 28
  (2019) 27–56, arXiv:1606.04085: Theorem 3.1 R(T₂(C_k)) ≤ 2^k − 1 for odd k; Theorem 3.5
  ω_{k+ℓ−1} ≤ ω_k + ω_ℓ for odd k, ℓ; Cor. 3.6 ω_k ≤ ω_{k−2} + ω; Cor. 3.7: if ω = 2 then
  ω(T(C_k)) = k − 1 (= maxcut) for all odd k. Asymptotic subrank of graph tensors is governed
  by the minimum cut (CVZ19 Thm 1.1.37, citing Vrana–Christandl, Commun. Math. Phys. 352 (2017)
  621–627, arXiv:1603.03964).
* **[R] Tight tensors.** Theorem 1.2.4 extends Strassen's lower bound on the asymptotic monomial
  subrank of tight 3-tensors (Thm 1.1.31) to k-tensors with a tightness map α; Example 1.1.38:
  Strassen's theorem does not generalise verbatim to k ≥ 4.
* **Relevance.** Neutral for beating 1/log K: everything here lives inside the rank model, which
  pays the flattening floor 1/2 (Prop. 2.4(b)). It fixes the numbers in Majdoddin's Table 2 and
  tells us that any rank-one base method for a merged sub-clique costs at least 1/2 per edge bit,
  worse than a tree (4/9). **[C] Adaptable:** the k-party CW analysis (Theorem 1.2.2/1.2.4) is
  the template for "laser-type analysis of tensor powers" that Majdoddin's Remark 2.9 says gives
  nothing beyond the constructions inside Signed Network Sums; the useful residue is the tight
  support + Dicke-tensor bookkeeping, which Brand et al. (§1.7, Theorem 52) turn into a
  "fixed-marginal laser method bound" for tight k-tensors.

### 1.2 Christandl–Vrana–Zuiddam, "Universal points in the asymptotic spectrum of tensors", STOC 2018; J. Amer. Math. Soc. 36 (2023) 31–79, arXiv:1709.07851

* **[R] Content.** Theorem 1.1 (Strassen's spectral theorem, restated): asymptotic restriction
  is governed by the spectral points (monotone under restriction, additive, multiplicative,
  normalised). The quantum functionals F^θ (θ a probability vector on the k legs) are the first
  universal spectral points over ℂ, defined by entropy optimisation on the moment (entanglement)
  polytope; F^θ(t) ≤ ∏_x R_x(t)^{θ_x} with R_x the flattening rank of leg x against the rest;
  Theorem 5.3: asymptotic subrank Q ≤ asymptotic slice rank ≤ F^θ; Theorem 4.4: on tight
  supports the support functionals and quantum functionals agree; Theorem 4.20 for free tensors.
  The quantum functionals characterise asymptotic slice rank.
* **[R] Use in Majdoddin §4.4.** Lemma 4.11 (configurations with ≤ 3 cells do not trade) is
  proved with θ = (1/2, 1/2, 0) on the two isolated cells; Example 4.10 shows flattening-rank
  inequalities alone are too weak (a triangle = matrix multiplication tensor admits a fake
  two-piece family passing every flattening test). Remark 2.9: the quantum functionals of T₄ are
  ≤ N³ = the input floor, so they give no lower bound above the input floor at K = 4.
* **[R] 2026 follow-ups.** Sakabe–Doğan–Walter, "Strassen's support functionals coincide with the
  quantum functionals", arXiv:2601.21553 (FOCS 2026): support functionals are universal spectral
  points over ℂ, via a minimax formula on moment polytopes (Hirai's Fenchel duality); also
  gives a unified treatment of asymptotic slice rank, G-stable rank, non-commutative rank.
  Doğan–Sakabe–Walter, arXiv:2609.06633: efficient algorithms (Hadamard mirror descent) for
  quantum functionals. Botero–Christandl–Fraser–Leigh–Nieuwboer, "On quantum functionals for
  higher-order tensors", arXiv:2604.18283 (v2 Apr 2026): for k ≥ 4 and non-singleton
  weightings the upper and lower quantum functionals do **not** coincide in general, but they
  "anchor" new spectral points agreeing with them on embedded 3-tensors and W-like states, for
  all laminar weightings; these give obstructions to asymptotic restriction beyond the previously
  known spectral points.
* **Relevance.** This is the lower-bound (obstacle) toolbox: every piece family must pass every
  spectral point. Helps indirectly: a candidate family for Open Problem 1 or 5 can be filtered by
  computing F^θ (now efficiently, 2609.06633) and the new laminar spectral points of 2604.18283
  before any search; a family that survives all of them is the one worth building. **[C]** The
  laminar weightings are exactly the weightings adapted to merges (groups of groups), so the
  Botero et al. points are the natural invariant for "hyperedge" pieces meeting ≥ 3 groups, where
  Majdoddin says the four-party rank inequalities are incomplete (§4.8).

### 1.3 Strassen's support functionals, asymptotic rank conjecture and its consequences

* **[R] Christandl–Hoeberechts–Nieuwboer–Vrana–Zuiddam, "Asymptotic tensor rank is characterized
  by polynomials", arXiv:2411.15789:** sublevel sets of asymptotic rank are Zariski-closed; the
  set of values of asymptotic rank is well-ordered ("discreteness from above"): any close enough
  upper bound on ω snaps to ω. Neutral; it is a structural fact about the rank model only.
* **[R] Björklund–Kaski, "The asymptotic rank conjecture and the set cover conjecture are not
  both true", STOC 2024, arXiv:2310.11926:** ARC ⇒ O((2−δ)^n) for k-Set Cover and (via
  Krauthgamer–Trabelsi) randomized (2−δ)^n directed Hamiltonicity. **Pratt, "A stronger
  connection…", STOC 2024, arXiv:2311.02774:** ARC ⇒ (3/2^{2/3}+ε)^n set cover; conversely the
  set cover conjecture ⇒ an explicit family T_n ∈ ℂ^N⊗ℂ^N⊗ℂ^N has asymptotic rank > N^{1.08}.
  **Björklund–Curticapean–Husfeldt–Kaski–Pratt, "Fast deterministic chromatic number under the
  ARC", SODA 2025, arXiv:2404.04987:** ARC ⇒ deterministic O(1.99982^n) chromatic number.
  **Björklund–Kaski–Koana–Nederlof, "Kronecker scaling of tensors…", arXiv:2504.05772:** low rank
  of the balanced tripartitioning tensor P_d ⇒ permanent circuits exponentially below Ryser
  (ARC ⇒ 2^{0.9183n}, cf. Brand et al. footnote 1); "Steinitz balancing". **Kaski–Michałek,
  arXiv:2404.06427:** explicit universal sequence U_d with σ(U_d) = worst-case exponent σ(d);
  ARC for d ⇔ σ(T_d) = 1. **Brand–Curticapean–Li–Pratt, arXiv:2505.22410:** convolutions in
  O*(|B|^{2ωk/3}); ARC ⇒ quasi-linear. **Lee, arXiv:2601.08119:** numerical census of asymptotic
  rank bounds via vanishing polynomials.
* **[R] Alman–Li, "Asymptotic rank speedup theorems, revisited", arXiv:2605.21738:** general
  speedup theorems extracting extra terms from border-rank bounds ("Strassen calculus"); asymptotic
  rank of cw₂ < 3.931 (border rank 4; = 3 would give ω = 2); below d^{2ω/3} for every d×d×d
  tensor. Majdoddin §2.3 uses their bound for the octonion tensor (≈ 21.94 at ω = 9/4) and notes
  the eight-square construction gains at ω > 2 only if that rank were below ≈ 10.03–12.34.
* **Relevance.** Neutral-to-negative. All ARC consequences are rank-one methods for a *different*
  tensor (tripartitioning, convolution); applied to T_K they cannot pass the flattening floor
  1/2 (Prop. 2.4(b): asymptotic rank obeys every flattening rank). **[C]** The ARC-style
  "assume low asymptotic rank of a constant-size base tensor and amortise over Kronecker powers"
  is exactly the amortisation that Signed Network Sums lack (see §2.3, Brand et al. Theorems 2–4:
  circuit complexity of d-mode tensors is provably not submultiplicative under standard
  hypotheses), so the asymptotic-spectrum machinery does not transfer to our model.

### 1.4 Amanov–van den Berg–Zuiddam, "Multiplying matrices via polynomials: exposition and barriers", arXiv:2610.30054 (21 Oct 2026)

* **[R]** Exposition of OpenAI's ω_ℂ ≤ 9/4, extended to ω_F ≤ 9/4 over every field; rectangular
  curve ω(1,k,1) = 2 for 0 ≤ k ≤ 1/2 and ≤ 1 + k + 1/(4k) for k ≥ 1/2; for a ≥ b ≥ c ≥ 0,
  ω(a,b,c) = a + b if c(a+b) ≤ ab, else ≤ (a+b+c)/2 + (ab/c + ac/b + bc/a)/4. Language:
  degeneration inequalities among polynomial multiplication tensors + Strassen's spectral duality.
  **Operational barrier:** the current analysis of all these bounds is optimal and the current
  degeneration ingredients cannot improve them.
* **Relevance.** This is Majdoddin's "current curve" (α ≥ 1/2 makes the K = 4 tree cost exactly
  N^{2ω(1,1/2,1)} = N⁴, i.e. trees sit on their floor at K = 4). Rules something out: every
  construction of Majdoddin §2 is non-decreasing in the curve, so on the current ingredients the
  curve-dependent values (3.9305 at K = 4, 8.017 at K = 6) are final until new degeneration
  ingredients appear.

### 1.5 Uznański, "Rectangular matrix multiplication from polynomial products", arXiv:2610.10494 (v2, 7 Oct 2026)

* **[R]** Same curve (ω(1,k,1) ≤ 2 for k ≤ 1/2, ≤ 1 + k + 1/(4k) for k ≥ 1/2; α ≥ 1/2) via explicit
  degenerations of convolution tensors, multinomial counting and Strassen's spectral theorem; an
  "angular constraint" on three dot-product parameters gives both the curve and ω(a,b,c); Zwick's
  APSP in O(n^{2.5}), O(n^{2.4999}) with Alman–Vassilevska Williams. Relevance: as 1.4.
  Related expositions: Pass arXiv:2610.28627 (constructive Strassen-style identity, O(n^{9/4+γ})
  integer operations; "polynomial packings"); Lü arXiv:2610.18914 (shared-leg separation with
  2M−1 copies instead of 5M, any characteristic); **Li, "Semidirect sums of tensors and the matrix
  multiplication exponent", arXiv:2611.04175 (3 Nov 2026):** the heart of the OpenAI method is an
  "untwisting lemma for semidirect sums of tensors", presented as a generally applicable method.
  **[C]** The crossing identity 2[x=v][y=u] = R + C is a sum of two tensors each cheap in one
  flattening; whether the untwisting lemma says anything about such sums is worth one afternoon.

### 1.6 Zhou, "Asymptotic rank of weighted graph tensors via completely positive covers", arXiv:2610.34273 (v2, 3 Nov 2026; 80 pp.)

* **[R] Theorem 1.1 (complete graph tensors).** For every field F and n ≥ 2,
  ⌊n²/4⌋ ≤ log₂ R̃_F(GT₂(K_n)) ≤ n²/4. Hence τ_F(K_n) ≤ n/(2(n−1)) → 1/2, exact for even n;
  below 2/3 for every n ≥ 5. **Answers CVZ19 Question 1.3.1 affirmatively and Question 1.3.2
  for every K_{2n}.** Table 1: Γ(K₄) ≤ 4.000000 (CVZ 4.637658, Brand et al. 4.633908), Γ(K₆) ≤ 9,
  Γ(K₈) ≤ 16. Concurrent: Khoruzhii, "A square-root bound for asymptotic tensor rank", Lemmata
  Repository (Lean, over ℂ).
* **[R] Method.** Higher-order version of OpenAI's polynomial multiplication method: a separation
  theorem that separates blocks on n−2 shared legs at cost linear in the number of blocks
  (Lemma 3.2: the tensor C_n(a₁,…,a_{n−1}) with a sum leg has asymptotic rank D), an entropy
  inequality, polynomial degenerations forcing "diagonal growth" of a symmetric spectral profile,
  interpolation ("discrete concavity", "shifted tripling", §4).
* **[R] Theorem 1.2 (weighted graph tensors).** MaxCut(W) ≤ log₂ R̃_F(WT(Q)) ≤ U_CP^Δ(W), the
  latter a conic program (P ≥ 0 symmetric, J − 2P copositive, triangle inequalities
  P_ij ≤ P_ik + P_kj). Corollary 1.3 for unweighted graphs. Odd cycles: ≤ m − 1 + 1/(m+1)
  (gap 1/(m+1) above maxcut); weighted triangles recover the Uznański/ABZ rectangular curve;
  CP and SDP programs give 9/4 on the triangle; complete multipartite, split, wheel graphs.
* **Relevance.** Rules out (definitively) the rank route: e_rank(K) = ⌊K²/4⌋/C(K,2) is attained
  for even K; rank-one methods are now exactly understood and stuck at 1/2 > 4/9 > 1/log K.
  **[C] Derived:** with Brand et al. Theorem 1 (asymptotic rank exponent of any d-mode tensor
  ≤ (d−1)·τ(K_d)), Zhou gives ≤ d/2 for every d-mode tensor, matching the ⌊d/2⌋ lower bound of
  the matching tensor — the rank theory of d-mode tensors is closed at the level of exponents.
  **[C] Adaptable:** (i) Theorem 1.2's conic program is an exact-rank analogue of Majdoddin's
  "size game" for weighted (merged) instances; for a merged instance whose top is solved by a
  rank-one base method the CP value is the right cost, and the path constraints are the rank
  analogue of "routing an edge through an intermediate vertex" — the same move as merging.
  (ii) The separation/interpolation machinery turns a concave growth profile into degenerations;
  Majdoddin's Prop. 4.24 says going below 1/√2 inside the App. B shape needs a *kinked* profile
  D(E) — Zhou's §4.2 "discrete concavity" is the only place in the literature that manipulates
  such profiles with full control, and is worth reading for Open Problem 1.

### 1.7 Brand–Curticapean–Kaski–Li–Orzel–Seppelt–Wang, "Beyond bilinear complexity: what works and what breaks with many modes?", arXiv:2602.11975 (Feb 2026)

* **[R] Theorem 1:** asymptotic rank exponent of every d-mode tensor ≤ 0.772318(d−1), via
  **Theorem 48 (App. C): τ(K₄) < 0.772318** (big CW tensors in k modes; improves CVZ19
  0.772943); Lemma 20 generalises Strassen's 2ω/3 to (d−1)ω/3 by a graph-theoretic proof.
  Remark 21: open whether some d has τ(d) < 2/3 (answered by Zhou two months later).
* **[R] Theorems 2–4 (no submultiplicativity):** if circuit complexity C were submultiplicative on
  d-mode tensors then VP = VNP (Thm 2), permanents in O(2^{cn}) for d = ⌈4/c⌉² (Thm 3), and the
  (d/2−1, d/2)-hyperclique conjecture fails for every even d ≥ 8 (Thm 4). Theorem 5 (mixed):
  rank exponent r of T and circuit exponent s of U give circuit exponent ≤ r + s for T ⊗ U.
  Theorem 6: circuit exponent of every d-mode tensor < d/2 + 1 via the line-treewidth
  ltw(K_d) ≈ d²/4 + d − 2 (Theorem 29). Theorem 7: every 4-mode tensor has asymptotic circuit
  exponent ≤ 2.2967 (< rank bound 2.317), every 5-mode ≤ 2.8774, via computer-found fractional
  decompositions of graphs into low-rank and low-treewidth parts. Key observation: T_G ⊗ T_H ≅
  T_{G+H}, with fractional graphs allowed.
* **Relevance.** Helps as a *language*: "weighted clique sum" = T_{G} for a fractional multigraph
  G, merges = contracting vertex sets, trees = treewidth of the line graph, and the mixing of
  rank decompositions with tree contraction (Theorem 5) is Majdoddin's "covering hybrid" in
  general form. Their Theorem 7 is the cleanest published statement that for d ≥ 4 modes
  circuits beat (asymptotic) rank — the same phenomenon as Majdoddin's Theorem 2.7 (N^{23/6} vs
  N⁴ at K = 4). Theorems 2–4 are also a warning (§Obstacles 5): there is no submultiplicative
  cost for d-mode tensors, so no asymptotic-spectrum theory of Signed Network Sums should be
  expected; a lower bound for the full model is as hard as circuit lower bounds.

---------------------------------------------------------------------------------------------------

## 2. Beyond-rank evaluation of tensor networks

### 2.1 Austrin–Kaski–Kubjas, "Tensor network complexity of multilinear maps", Theory of Computing 18(16) (2022) 1–54; ITCS 2019; arXiv:1712.09630

* **[R] Model.** A tensor network for a multilinear map, executed along one contraction order
  (the cost is the largest intermediate tensor, up to fast matrix multiplication); captures every
  algorithm from a low border-rank decomposition. Theorem 1.1 (upper bounds): matrix
  multiplication O(n^{ω+ε}); counting v-cliques O(n^{(ω+ε)⌊v/3⌋ + (v mod 3)}) although the clique
  tensor has border rank n^{3t} for v = 3t ≥ 6; homomorphisms of pattern P in
  O(n^{(ω+ε)bw(P)/2}) (bw = branchwidth); permanent O(2^n n). Theorem 1.2 (lower bounds):
  Ω(n^{bw(P)}) for P-homomorphism counting (Ω(n^{⌈2v/3⌉}) for v-cliques, Ω(n^v) for k-uniform
  v-hypercliques, k ≥ 3, ruling out tensor networks for hyperclique and Max-3-CSP);
  Ω(C(n,n/3)) = Ω(2^{0.918n}) for the permanent/determinant. Theorem 1.3/5.1: cost is
  submultiplicative. Theorem 1.4: c(A) ≥ w(A), a rank-based width — the authors note their
  lower-bound method "is inherently rank-based and cannot go beyond C(n, n/3)".
* **[R] For the clique sum** (Anthropic App. G; Majdoddin Prop. 2.4(c)): the hypergraph has
  C(K,2) vertices (edge strings) and K star hyperedges (tables); every branch decomposition has
  an edge with ≥ K/3 stars per side sharing ≥ 2K²/9 vertices, so e ≥ 4/9 asymptotically and the
  tree floor is N^{⌈K/3⌉(K−⌈K/3⌉)}.
* **Relevance.** Rules out trees; and because the lower bound is a rank bound across one cut per
  tree edge, it is exactly what a signed sum of networks with term-dependent contraction orders
  escapes. **[C]** The one structural fact worth keeping: Theorem 1.3 (submultiplicativity of
  tree cost) is what makes AKK's model amenable to Kronecker amortisation; Signed Network Sums
  are not known to have it (and Brand et al. Theorems 2–4 suggest the full circuit model does
  not), so amortising a per-level gain over levels — Anthropic's recursion — is the only known
  way to compound gains, and it is what forces the squaring K_{ℓ+1} = K_ℓ² (Majdoddin §4.5).

### 2.2 Signed sums / inclusion–exclusion precedents

* **[R] Anthropic App. G:** the closest algorithmic precedent for expanding a non-existent gadget
  as a signed combination of O(1) gadgets and solving every term the same way is
  Curticapean–Xia (FOCS 2015, counting perfect matchings in K_{3,3}-free/non-planar classes)
  after Galluccio–Loebl (1999); rank-based dynamic programming (Bodlaender–Cygan–Kratsch–Nederlof
  2012/15) factorises across one fixed family of cuts. Anthropic states they know no prior
  combination of an exact signed low-rank expansion of crossings with a per-term choice of
  contraction direction and recursion.
* **[R] Nothing found (Oct–Nov 2026 arXiv/Hexagon search) that proves a lower bound for signed
  sums of tensor networks.** The STOC 2025 / PRX Quantum 2025 "sign problem in tensor network
  contraction" line (Jiang–Chen–Schuch–Hangleiter) concerns approximate contraction of random
  networks with positive bias and is not relevant to exact exponents. **[C]** Majdoddin's §4 is
  the first lower bound of any kind for a signed-sum class, and it is a class barrier
  (rewrite-and-merge), not a model barrier.

### 2.3 Border rank, degeneration, laser method vs. exact decompositions for graph tensors

* **[R] Floors.** Majdoddin Prop. 2.4(b): border rank is bounded below by every flattening rank
  (lower semicontinuity of matrix rank) and so is asymptotic rank (multiplicativity of flattening
  ranks under tensor powers), so degeneration/interpolation can never pass 1/2 on T_K. Alman–Li
  2605.21738 extract more from border rank than CW/Strassen but stay inside this. Brand et al.
  Theorem 52 is a "fixed-marginal laser-method bound" for tight k-tensors (their App. C.2).
  Majdoddin Remark 2.9: a laser-type analysis of tensor powers gives nothing beyond the K = 4
  constructions, "inside the rank model it is bounded by the flattening floor, and inside the
  model of Signed Network Sums its type-and-entropy half is what the constructions already do
  (argued)".
* **Verdict [C].** Degeneration cannot beat exact decompositions on the rank ladder for graph
  tensors (Zhou shows exact asymptotic-rank methods already hit the floor); where degeneration
  could matter is *inside a piece*: Definition 7 of Anthropic requires exact integer identities
  with factorisations computable in poly time, whereas a border-rank piece (R_ε + C_ε → crossing)
  would need interpolation across the whole network, which costs a polynomial factor per
  crossing — λ^{O(1)} per block, i.e. 2^{o(λ)}, admissible in (L2) of Majdoddin's class
  (|I_C| ≤ 2^{o(m)}) only if the number of interpolation points is subexponential in the block
  length. Nobody has tried border-rank pieces; the pigeonhole floor (Prop. 4.6) applies to them
  unchanged, so they cannot beat 1/2 either, but they might reach it where exact pieces cannot.

### 2.4 Related: Kassabov–Landsberg–Souza–Speegle, arXiv:2608.27434; Chang–Gesmundo–Zuiddam, arXiv:2604.19872

* **[R]** Centroids as a geometric tool for border-rank decompositions and better laser tensors;
  border subrank of higher-order structure tensors (k-fold matrix multiplication, sl₂). Neutral;
  recorded for completeness.

---------------------------------------------------------------------------------------------------

## 3. Sums-of-squares composition, Hurwitz's problem and the crossing

### 3.1 Hrubeš–Wigderson–Yehudayoff, "Non-commutative circuits and the sum-of-squares problem", J. Amer. Math. Soc. 24 (2011) 871–898; STOC 2010; ECCC TR10-021

* **[R] Statements.** SOS_k = (Σx_i²)(Σy_j²); S_F(k) = least number of squares of bilinear forms,
  B_F(f) = least number of products of two bilinear forms. Theorem 1.1 (Hurwitz 1898):
  S_ℝ(k) > k unless k ∈ {1,2,4,8}; Theorem 1.2: S_ℝ(k) ≥ (2−o(1))k. **Theorem 1.4:** over an
  algebraically closed field, S_F(k) ≥ Ω(k^{1+ε}) ⇒ the non-commutative permanent needs circuits
  of size 2^{Ω(n)}. **Theorem 1.6:** non-commutative circuit size of ID_k = Σ_{i,j} x_i y_j x_i y_j
  is ≥ Ω(B_F(SOS_k)). Theorem 1.7 (B version of 1.4); Theorem 1.8 (any explicit biquadratic
  family); Theorem 1.10: S_ℤ(k) ≥ Ω(k^{6/5}) for integer coefficients; Theorem 1.11/1.12
  (ordered polynomials, unconditional bounds). Lemma 3.5: the *width* w(f) of a degree-4
  polynomial f[X₁,X₂,X₃,X₄] is the least n with f = Σ_{t≤n} f_t, each f_t of one of two
  product shapes; Proposition 4.1: B(f^{(c)}) ≤ w(f) ≤ 4B(f^{(c)}) for (X,Y)-symmetric f,
  char ≠ 2.
* **[R] The dictionary (Anthropic App. G/H, (71)–(75)).** The crossing [x=v][y=u] is ID_N
  read as a 4-tensor; P(N) := least number of functions each of row-wise or column-wise rank 1
  summing to the crossing = w(ID_N) (HWY Lemma 3.5); s ≤ P(N) ≤ 4s with s the bilinear
  composition number (Prop. 4.1). The eight-square identity in matrix form is the Hurwitz–Radon
  relation L_v^T L_x + L_x^T L_v = 2[x=v]·Id (74), i.e. Clifford relations; "directions are
  orders" (75): row-wise = operator from x acts first, column-wise = operator from v acts first.
  Pieces A_i with parameter ρ give functions of row/column rank product ≤ N^{4ρ}·poly; repo
  `pieces.md` §0 records P(N) ≤ N^{2ρ}polylog, hence σ_ℂ(N) ≤ N^{√2+o(1)} from App. B [R, own].
* **Relevance.** Two-way but asymmetric: a lower bound P(N) ≥ N^{1+ε} (Naslund's Problem 12)
  gives ρ ≥ (1+ε)/2 for *all* pieces, hence a floor strictly above 1/2 and, with Majdoddin's
  Thm 4.13, 1/e(K) ≤ log K/(…) unchanged in type; a construction with ρ → 1/2 refutes Problem 12
  and kills the HWY route to non-commutative lower bounds. **[C]** So "pieces at ρ = 1/2" is at
  least as strong as "σ_ℂ(n) = n^{1+o(1)}", a 128-year-old open problem's asymptotic form; this is
  the right calibration for Open Problem 1's window [1/2, 1/√2].

### 3.2 Hrubeš, "A subquadratic upper bound on sum-of-squares composition formulas", CCC 2024, LIPIcs 300, 12:1–12:11; ECCC TR24-026

* **[R]** Theorem 1: σ_F(n) ≤ O(n^c), c < 1.62, over ℂ (indeed ℚ(i)) and over positive
  characteristic; Theorem 12: the bilinear-product variant β_F(n) ≤ O(n^{1.62}) over *any* field;
  previously O(n²/log n) (Hurwitz–Radon). Construction: products of anticommuting Hurwitz–Radon
  matrices e_A indexed by subsets with a "parity representation" ξ (Lemma 7/Theorem 9/11).
  §5.2 "tensor product construction": H_a = H_{a₁}⊗…⊗H_{a_ℓ}, anticommuting at odd Hamming
  distance, gives σ_ℂ(n^ℓ, m^ℓ) ≤ σ_ℂ(n,m)^ℓ (4m)^{ℓ/2}; from σ(8,8) = 8:
  **σ_ℂ(8^ℓ,8^ℓ) ≤ 8^{11ℓ/6}** — the same 11/12 as Anthropic's Lemma 2 (ρ = 11/12), as App. G
  notes. §6 Problem 1: a t-parity representation of dimension 2^{(0.5+o(1))t} would give
  σ_ℂ(n,n) ≤ n^{1.5+o(1)} and σ_ℂ(n,n²) ≤ n^{2+o(1)}; 0.5 is optimal.
* **[R] Hrubeš, "Non-commutative circuits for ID_n…", ECCC TR24-099 (2024):** Theorem 3/25:
  ID_n has non-commutative circuits of size O(n^{1.96}) (char ≠ 2), via Lemma 22 (from a
  composition formula with a *computable* structure to a circuit); same for S_{4,n} and the
  4×n rectangular permanent.
* **Relevance.** Hrubeš's constructions are *weaker* than App. B (1.62 > √2) and in the same
  family as the eight-square block product, so they give no new pieces. Helps on a side question:
  Lemma 22 of TR24-099 is a template for "tables buildable near their size" (Majdoddin Open
  Problem 1 asks for pieces whose tables are built near their size; TR24-099 turns an SOS
  identity into a subquadratic circuit, exactly the bilinear-complexity question). Problem 1
  (parity representations) is a concrete combinatorial target whose solution would still be
  above √2, so it cannot help the rate; recorded to avoid re-deriving it.

### 3.3 Hurwitz–Radon, twisted group algebras, field dependence

* **[R]** Hurwitz–Radon: an identity of type [r,s,n] with s = n exists iff r ≤ ρ(n), ρ(n) ∈
  [2log₂n, 2log₂n+2] for n a power of 2 (Hrubeš CCC'24 §1, §3); the solutions are Clifford
  modules. Lenzhen–Morier-Genoud–Ovsienko, "New solutions to the Hurwitz problem on square
  identities", arXiv:1007.2337 (J. Pure Appl. Algebra 2011): new infinite series of [r,s,n] via
  ℤ₂ⁿ-graded quasialgebras (twisted group algebras with a cubic cocycle; the octonions are
  ℤ₂³ twisted by a cubic form, and Anthropic's σ(p,q) = (−1)^{φ(p,q)} with cubic φ is exactly
  this); Morier-Genoud–Ovsienko, arXiv:1304.0949 (cubic forms on 𝔽₂ⁿ and Hurwitz identities);
  Hu–Huang–Zhang arXiv:1506.01502; Shapiro's monograph (Compositions of Quadratic Forms, 2000).
  **Zhang–Zhu, "The Hurwitz sum-of-squares problem depends on the base field", arXiv:2605.00590
  (2026):** an explicit [12,12,18] formula exists over every field with √−1 and char ≠ 2 (so
  over ℚ(i), ℂ) but over no formally real field; refutes Shapiro 1984 and Adem 1975.
  Jun Zhu, arXiv:2606.10391: no integral [10,10,16] formula is a restriction of a Hurwitz–Radon
  formula (Shapiro's conjecture).
* **[C] Relevance.** (i) The ℤ₂ⁿ-graded quasialgebras give, for every n, sign functions σ on
  {0,1}ⁿ with R(x,y,u,v) = [x⊕y⊕u⊕v = 0]σ(x,y)σ(v,u) of row rank 2ⁿ; but the two-term identity
  R + C = 2·crossing holds only for n ≤ 3 (Hurwitz), and for larger n the column rank of R is
  the full 2^{2n}, so no gain over eight squares — this family is the "first guess" of App. H and
  is exhausted. (ii) Zhang–Zhu says identities over ℂ can be strictly cheaper than over ℝ; Signed
  Network Sums over ℤ[i] cost a factor 2, so **candidate pieces should be searched over ℤ[i], not
  ℤ**; the Anthropic/Majdoddin integrality requirement (Def. 7(c)) is not a restriction to ℝ.
  (iii) HWY Theorem 1.10 (S_ℤ(k) ≥ Ω(k^{6/5})) does not bite: it bounds the number of squares
  with integer coefficients, while a piece needs small *ranks*, and App. B's integer pieces
  already give N^{√2}.

### 3.4 Pfister's sixteen-square identity and composition algebras

* **[R]** Pfister (1965): for every 2ⁿ, (Σ_{2ⁿ} x_i²)(Σ_{2ⁿ} y_j²) = Σ_{2ⁿ} z_k² with z_k
  linear in y and *rational* in x (denominators); bilinear identities with s = n exist only for
  n ∈ {1,2,4,8} (Hurwitz). Setting the last eight variables to zero in the 16-square identity
  recovers Degen's eight-square identity.
* **[C] Relevance: rules out.** The passage (72) ⇒ (71) in App. H extracts the coefficient of
  a_x b_y a_v b_u from a polynomial identity bilinear in a and b; with rational coefficients in a
  there is no coefficient to extract and no 4-tensor identity results. One could evaluate a Pfister
  identity at integer points, but the resulting functions of (x,y,u,v) are not of the form
  "sum over few θ of products", i.e. not pieces. Composition algebras stop at the octonions
  (Hurwitz's theorem on normed division algebras); the only way past N = 8 within the two guesses
  of App. H is Hurwitz–Radon with s > n, and that is what Hrubeš and App. B's graded operators
  already exploit.

### 3.5 Three-party analogues: multiquadratic sums of squares

* **[R] Rossman–Zhu, "Multiquadratic sum-of-squares lower bounds imply VNC¹ ≠ VNP",
  arXiv:2512.01227:** the SoS complexity of a d-multiquadratic polynomial (quadratic in each of
  d blocks of n variables) is the least s with f = Σ_{i≤s} g_i², g_i d-multilinear; for d = 2 this
  is HWY; an n^{d−o(log d)} lower bound for explicit d-multiquadratic polynomials, for
  ω(1) ≤ d ≤ O(log n/log log n), separates VNC¹ from VNP.
* **[C] Relevance (helps as a definition).** Majdoddin's Open Problem 5 asks for an exact identity
  whose configurations meet ≥ 3 groups of a merge with cheap pieces, and says the class "does not
  yet define" the cost of such a piece (§4.8). The d-block multiquadratic composition
  (Σ_{i}x_i²)(Σ_j y_j²)(Σ_k z_k²) = Σ g_ℓ² with g_ℓ trilinear is the natural three-party
  generalisation of (72): by the same coefficient extraction it is an identity for the
  three-way "crossing" [x=v][y=u][z=w] as a sum of terms each a product of a function of
  (x,y,z) and of (v,u,w) — i.e. cheap across the *one* split that separates the two copies — and
  the cost model for a hyperedge piece across d groups is the d-tuple of flattening ranks in the
  d "orders" of a d-fold product of operators (the "directions are orders" reading of App. H
  generalises verbatim: a d-fold product can be bracketed in several orders, one per merge).
  Nothing in the literature computes these numbers; the trivial bound is s ≤ σ(n)^{d−1}·n^{…}
  and no lower bound beyond the obvious is known (Rossman–Zhu's point).

### 3.6 Naslund's problems

* **[R] (as cited by Anthropic App. G and by Rossman–Zhu / "The interplay between bounded ranks of
  tensors arising from partitions", arXiv:2310.11356):** Naslund [Nas20], Problem 12: is
  P(N) ≥ N^{1+ε} for the width of ID_N (equivalently of the crossing)?; Problem 13: for a family
  R of partitions of [d] and a partition P not finer than any member of R, what is the rank of
  Δ_P with respect to R-rank? A counting argument gives order-4 tensors of R-rank Ω(n²) but no
  explicit Ω(n^{1+ε}) is known. **[C]** Problem 13 with d = 4, R = {rows, columns} and P = the
  crossing pairing is precisely the piece problem at one block; with d = 6 or 8 and R = the
  three or four merges of a hyperedge configuration it is the cost question of Open Problem 5.
  The partition-rank literature (Naslund 2020; Kazhdan–Ziegler; the 2310.11356 survey) is the
  closest existing *formalism* for "rank with respect to several partitions at once" and should
  be the first place to look for inequalities between the costs under different merges.

---------------------------------------------------------------------------------------------------

## 4. October–November 2026 preprints (Hexagon and arXiv)

Hexagon API coverage [C]: `search_query=all:<term>` returned 0 entries for several multi-word
terms ("clique sum tensor", "Hurwitz problem", "sum of squares composition", "quantum
functionals graph tensor", "eight-square identity", "asymptotic rank conjecture") while
single-word queries returned matches; I treat the Hexagon search as incomplete. Queried terms:
clique, Hurwitz, tensor rank, asymptotic rank, matrix multiplication, Exponential Time
Hypothesis, 3-SAT, refutation, octonion, tensor network, sum of squares, composition algebra,
Fock, vertex algebra, partition, pieces, crossover, Hamiltonian, Majdoddin, Degen, Clifford,
Heisenberg, rank floor, contraction tree, signed network sums, complete graph tensor.

### 4.1 Hexagon, on the rate or on pieces

* **hexagon:2610.00692v1, de Brito, "The partition exponent in the graded pieces of the Claude
  3-SAT algorithm is optimal for pieces of that shape" (30 Oct).** [R] For graded families of
  App. B's shape, ρ ≥ max(2^{α−1}, 2^{−α}) − o(1) ≥ 1/√2 for growth log dim V_{≤W} ~ W^α; with
  the identity on all of V_h, ρ ≥ 2^α/(2(4^α−1)), > 1 for α < 0.357; Theorem B is rank-tight up
  to a polynomial factor; sparse-mode Heisenberg Fock spaces do not carry Lemma 9; **the floor
  ρ ≥ 1/2 remains open.** Already digested in `hexagon-related.md` §1. Consistent with Majdoddin
  Prop. 4.24 (ρ_B ≥ 2/3 for concave profiles within the shape; 1/√2 optimal among power profiles;
  below 1/√2 needs a kinked profile, "we know no such algebra"; fermionic Fock gives ρ → 1).
* **hexagon:2611.00004v1, Nguyen, "A sublinear treewidth exponent for binary CSP" (1 Nov).** [R]
  Uses the Claude recursion as a black box (D^{O(k/√log k)} counting of complete-table binary CSP)
  to contradict Marx's Conjecture 1.4 literally; Lean 4. Does not touch the rate.
  Digested in `hexagon-related.md` §3.
* **hexagon:2610.00594v1, Bhattacharjee** (weighted counting; digested, `hexagon-related.md` §2);
  **2610.00613v2 Li** (learning theory); **2610.00572 O'Donnell** (exposition of the OpenAI
  refutation); **2610.00574 Kominers** (polynomial separation); **Tulsyan 2610.00672, 2611.00088,
  2611.00090, 2611.00115, 2611.00116** (own, conditional on the #SAT engines). None attacks e(K).
* Unrelated but adjacent: **2610.00548 Tomar** (rank of 3×3 MM over 𝔽₂ is 23, Lean);
  **2610.00671 Nielsen** (basis changes for 2×2 MM). Neutral.
* **Verdict [C]:** on Hexagon, de Brito's note is the only item on the rate besides our own, and it
  is a within-shape barrier, not a construction.

### 4.2 arXiv, October–November 2026

* **Majdoddin, arXiv:2610.41622 (30 Oct)** — the reference point (§0). Key theorem numbers for
  citation: Prop. 2.4 (ladder), Thm 2.5 (three-table collapse: on K = 3 Signed Network Sums are
  rank-one, e ≥ ω/3), Thm 2.7 (K = 4 in N^{23/6+ε} at ω = 2), Cor. 2.8 (N^{3.9305} on the
  current curve, N^{3.631} with App. B pieces on 256-bit blocks at ω = 2), Remark 2.9 (window
  [3, 3.547]; quantum functionals of T₄ ≤ N³), Table 3 (one-level grids: K = 6: 0.4907 vs tree
  0.533; K = 9: 0.437; K = 16: [0.416, 0.483], vs. ideal pieces 0.444–0.449 at K = 6), Def. 4.2
  (rewrite-and-merge; (L3) a merge is usable only if every configuration meets ≤ 2 of its
  groups), Remark 4.5 (hyperedges are outside the class), Prop. 4.6 (pigeonhole), Prop. 4.7
  (sharing cap), Prop. 4.8 (two-merge floor ρ ≥ 1/2), Lemma 4.11 (≤ 3 cells do not trade),
  Thm 4.12 (RM₂^{bh}: 1/e ≤ log³K), Thm 4.13 (grids: 1/e ≤ log₂K), Thm 4.18/Cor. 4.19 (single
  block, the recursion as written, loss δ < 8.5·10⁻²²), Prop. 4.22 (Song–Chen–Sun–Hu four-party
  rank inequality rank(BC|AD) ≤ rank(AB|CD)·rank(AC|BD), hence internal cost r ≥ |p − q|),
  Prop. 4.23 (AG(2,3) configuration: ρ = 1 for k-local pieces), Prop. 4.24 (App. B shape:
  ρ_B ≥ 2/3), §4.8 (AG(2,4) translation matching: product pieces cannot go below 1/2; the open
  door is a hyperedge piece over four blocks of the third merge). Open Problems 1–7 in §5.
* **Dias–Lima, arXiv:2611.00517 (31 Oct)** — known; constants of OpenAI's refutation.
* **MIT Hardness Group (Brunner, Demaine, Frei, Gomez, Hecher, Li, Lynch), "ETH is dead, long live
  SH", arXiv:2611.02650 (2 Nov).** [R] SH (Stearns–Hunt 1990) ⇔ Weak ETH (no O(2^{n^{1−ε}})L^{O(1)}
  3SAT algorithm for any ε > 0); a polynomial-time reduction with blowup N ≤ s^{b+o(1)} rules out
  O(2^{N^{1/b−ε}}) algorithms; parameterized analogue; #SH ⇔ Weak #ETH, ruling out
  2^{(n+m)^{1−ε}} for #2SAT. **[C] Relevance:** this names our target hypothesis. Polynomial decay
  e(K) ≤ K^{−β} with K ≤ m^{1/q} would give 3SAT in 2^{n^{1−β/q}} at bounded density, refuting SH;
  Majdoddin Cor. 4.21(a) shows rewrite-and-merge cannot. So Engine 3's "beat 1/log K" is exactly
  "attack SH with Signed Network Sums", and SH is the hypothesis the community now treats as the
  plausible floor.
* **Wu–Wang, arXiv:2611.02548 (2 Nov):** FVS counting in 2^{O(n(log log n)²/√log n)} assuming
  OpenAI's Theorem D.1 (Boolean tensor contraction). Uses the engine; no rate work.
* **Zhou, arXiv:2610.34273 (v2 3 Nov)** — §1.6; **Amanov–van den Berg–Zuiddam 2610.30054;
  Uznański 2610.10494; Pass 2610.28627; Lü 2610.18914; Li 2611.04175** — §1.4–1.5.
* **Curticapean, "Get permanent results faster by counting stars", arXiv:2611.03636 (2 Nov):**
  permanents in O*((2−ε)^n) ring operations, ε = 10⁻⁴⁰, via Binet–Minc with dynamic programming;
  answers Knuth's TAOCP problem unconditionally (Brand et al. had it only under ARC). Relevant to
  the permanent track, not to e(K).
* Searches that returned nothing on topic: "signed sum/inclusion–exclusion tensor network lower
  bound" (2025–26), "swap tensor rank", "operator Schmidt rank partial transpose" (nothing on
  simultaneous low rank across several cuts), "Hurwitz tensor rank algorithm", "quantum
  functionals graph tensor" (only the items in §1.2), "tensor network contraction exponent".

---------------------------------------------------------------------------------------------------

## 5. Ranked lists

### Five most promising mathematical tools (ranked; all [C] unless noted)

1. **Kinked growth profiles via the polynomial-method/degeneration machinery (Zhou §3–4;
   ABZ 2610.30054; Li's untwisting lemma).** Majdoddin Prop. 4.24 and de Brito reduce Open
   Problem 1 to: find a graded space with Lemmas 9–10 of App. B whose profile D(E) = log dim V_{≤E}
   grows fast up to the string weight h and slowly beyond (ρ_B ∈ [1/2, 2/3) needs pieces of a
   different shape, [2/3, 1/√2) a kink). Zhou's "discrete concavity/shifted tripling/diagonal
   growth" is the only published control of exactly such profiles under degeneration, and
   Khoruzhii's Lean files exist. First concrete task: redo App. H's "directions are orders" count
   for the polynomial-multiplication tensors C_n(a₁,…) of Zhou Lemma 3.2 in place of the
   Heisenberg Fock space.
2. **Spectral points as a design filter (CVZ18 quantum functionals; Sakabe–Doğan–Walter
   2601.21553; Botero et al. 2604.18283; Doğan–Sakabe–Walter 2609.06633).** Every candidate piece
   family must pass every spectral point under every grouping of its legs; for hyperedge
   configurations (≥ 3 groups) the laminar-weighting spectral points of 2604.18283 are the
   invariant Majdoddin lacks ("rank inequalities for six or more parties are incomplete"). Use:
   compute F^θ of candidate pieces numerically before searching for identities, as Lemma 4.11
   does by hand for three cells.
3. **Multi-partition rank / d-multiquadratic composition as the cost model for hyperedge pieces
   (Naslund Problem 13; Rossman–Zhu 2512.01227; HWY Lemma 3.5 and Prop. 4.1).** Open Problem 5
   needs a definition of the cost of a piece meeting d ≥ 3 groups; "directions are orders" for a
   d-fold operator product, equivalently the width of the d-block identity polynomial
   Σ x_i y_j z_k x_i y_j z_k with respect to the d bracketings, is that definition, and the
   partition-rank literature has the inequalities (and the sub-additivity under restriction)
   ready-made.
4. **Weighted graph-tensor calculus: fractional graph tensors T_G ⊗ T_H = T_{G+H} with mixed
   rank+tree costs (Brand et al. Thm 5–7) and Zhou's conic program U_CP^Δ (Thm 1.2) for weighted
   instances.** Majdoddin's merged instances are weighted clique sums solved by trees; both
   papers give LP/conic machinery (computer-aided fractional decompositions; copositive + path
   constraints) that computes exponents of weighted graph tensors. Adapt: replace the "best
   contraction tree on top" by the optimum of a fractional decomposition into rank and tree
   parts; this is the systematic version of the covering hybrid and may lower Table 3's top
   costs (the ideal-pieces values are held near the tree by the top instance, §2.5).
5. **Hurwitz–Radon/Clifford families over ℤ[i] with controlled two-order ranks (Hrubeš CCC'24
   Thm 11, parity representations; Lenzhen–Morier-Genoud–Ovsienko ℤ₂ⁿ-quasialgebras;
   Zhang–Zhu field dependence).** A structured search space for sign functions and operator
   families generalising the octonion σ; the lesson of Zhang–Zhu is to search over ℂ/ℤ[i]; the
   lesson of Hrubeš §5.2 is that plain tensor powers of eight squares stay at 11/12, so the search
   must be over *graded* Clifford-type families (fast growth up to weight h), which is tool 1 in
   another guise. Lowest ranked because App. H already exhausted the two natural guesses here.

### Five strongest known obstacles (ranked by how much they rule out)

1. **The two-merge pigeonhole floor ρ ≥ 1/2 and the grid/two-merge class barriers (Majdoddin
   Prop. 4.6, 4.8, Thm 4.12, 4.13, 4.18; Anthropic App. H).** [R] Any identity rewriting a
   configuration into pieces has a piece of near-full rank across each split; with two merges a
   configuration can at best split its bits evenly, so per level ρ ≥ 1/2 and squaring of K is
   forced; every grid algorithm has 1/e(K) ≤ log₂K, every balanced homogeneous two-merge
   algorithm 1/e(K) ≤ (log₂K)³. Polynomial decay therefore needs configurations meeting ≥ 3
   groups of a merge (Remark 4.5, §4.8) — outside every existing construction.
2. **Quantum-functional barriers on small configurations (Lemma 4.11; Prop. 4.23; §4.8 AG(2,4)).**
   [R] Configurations with ≤ 3 cells do not trade; on the AG(2,3) six-edge configuration every
   k-local piece has ρ = 1; on the AG(2,4) translation matching product pieces cannot go below
   ρ = 1/2 and the uniform quantum functional gives ρ ≥ 1/2 whenever the nodes split into two
   halves meeting every block of every merge at most once. What survives is only a non-product
   piece on a configuration without such halves.
3. **Within App. B's shape, ρ ≥ 2/3 for concave profiles and 1/√2 is optimal among power profiles
   (Majdoddin Prop. 4.24; de Brito hexagon:2610.00692).** [R] The known pieces are optimal in
   their shape; fermionic Fock spaces give ρ → 1; no graded algebra with a kinked profile and
   Lemmas 9–10 is known.
4. **Rank-side floors are tight and exhausted; no lower-bound tool exceeds the input floor at fixed
   K.** [R] Flattening floor 1/2 is attained by asymptotic rank (Zhou Thm 1.1, even K); tree floor
   4/9 (AKK Thm 1.2/1.4; Prop. 2.4(c)) binds every contraction tree; quantum functionals of T₄ are
   ≤ N³ (Remark 2.9) and the size game at K = 4 with ideal pieces reaches the input floor exactly
   (§4.6), so neither upper- nor lower-bound tools say anything in the window [3, 3.547] at K = 4
   — the problem is genuinely about the existence of pieces, and a bound above N³ for Signed
   Network Sums would be a superlinear lower bound for an explicit degree-4 polynomial.
5. **Calibration against open problems in algebraic complexity.** [R] ρ → 1/2 implies
   P(N) = N^{1+o(1)} for the width of ID_N (HWY Lemma 3.5/Prop. 4.1; Anthropic App. G), answering
   Naslund's Problem 12 negatively and closing the HWY route to non-commutative permanent lower
   bounds (Theorem 1.4/1.7); any hyperedge analogue with polynomial decay would refute SH/Weak ETH
   (2611.02650) via Majdoddin's threshold model; and Brand et al. Theorems 2–4 say no
   submultiplicative cost exists for d ≥ 8-mode tensors under the hyperclique conjecture, so no
   asymptotic-spectrum amortisation theory of Signed Network Sums should be expected, and the
   ABZ operational barrier caps every curve-dependent construction on current degeneration
   ingredients. None of these forbids the construction; they set the bar at breakthrough level.

---------------------------------------------------------------------------------------------------

## 6. Citation list (as used above)

* Christandl, Vrana, Zuiddam. Asymptotic tensor rank of graph tensors: beyond matrix
  multiplication. Comput. Complexity 28 (2019) 57–111. arXiv:1609.07476. [Thm 1.1.19/20/25,
  1.2.2, 1.2.4; Cor. 1.2.5, 1.2.6; Problem 1.2.1; Questions 1.3.1, 1.3.2]
* Christandl, Vrana, Zuiddam. Universal points in the asymptotic spectrum of tensors. STOC 2018;
  J. Amer. Math. Soc. 36 (2023) 31–79. arXiv:1709.07851. [Thm 1.1, 4.4, 4.20, 5.3]
* Christandl, Zuiddam. Tensor surgery and tensor rank. Comput. Complexity 28 (2019) 27–56.
  arXiv:1606.04085. [Thm 3.1, 3.5; Cor. 3.6, 3.7]
* Vrana, Christandl. Entanglement distillation from GHZ shares. Commun. Math. Phys. 352 (2017)
  621–627. arXiv:1603.03964.
* Sakabe, Doğan, Walter. Strassen's support functionals coincide with the quantum functionals.
  FOCS 2026. arXiv:2601.21553. Doğan, Sakabe, Walter. arXiv:2609.06633.
* Botero, Christandl, Fraser, Leigh, Nieuwboer. On quantum functionals for higher-order tensors.
  arXiv:2604.18283 (v2).
* Christandl, Hoeberechts, Nieuwboer, Vrana, Zuiddam. Asymptotic tensor rank is characterized by
  polynomials. arXiv:2411.15789.
* Björklund, Kaski. STOC 2024. arXiv:2310.11926. Pratt. STOC 2024. arXiv:2311.02774.
  Björklund, Curticapean, Husfeldt, Kaski, Pratt. SODA 2025. arXiv:2404.04987.
  Kaski, Michałek. arXiv:2404.06427. Björklund, Kaski, Koana, Nederlof. arXiv:2504.05772.
  Brand, Curticapean, Li, Pratt. arXiv:2505.22410. Lee. arXiv:2601.08119.
* Alman, Li. Asymptotic rank speedup theorems, revisited. arXiv:2605.21738 (v2, May 2026).
* Amanov, van den Berg, Zuiddam. arXiv:2610.30054. Uznański. arXiv:2610.10494 (v2).
  Pass. arXiv:2610.28627. Lü. arXiv:2610.18914. Li, B. arXiv:2611.04175.
* Zhou, H. Asymptotic rank of weighted graph tensors via completely positive covers.
  arXiv:2610.34273 (v2, 3 Nov 2026). [Thm 1.1, 1.2; Cor. 1.3; Lemma 3.2; Thm 5.6]
  Khoruzhii, K. A square-root bound for asymptotic tensor rank. Lemmata Repository (Lean), 2026.
* Brand, Curticapean, Kaski, Li, Orzel, Seppelt, Wang. Beyond bilinear complexity. arXiv:2602.11975.
  [Thm 1–7, 29, 48, 52; Remark 21; Lemma 20, 30]
* Austrin, Kaski, Kubjas. Tensor network complexity of multilinear maps. Theory of Computing
  18(16) (2022); ITCS 2019. arXiv:1712.09630. [Thm 1.1, 1.2, 1.3/5.1, 1.4]
* Hrubeš, Wigderson, Yehudayoff. Non-commutative circuits and the sum-of-squares problem. J. Amer.
  Math. Soc. 24 (2011) 871–898; STOC 2010; ECCC TR10-021. [Thm 1.1, 1.2, 1.4, 1.6, 1.7, 1.10;
  Lemma 3.5; Prop. 4.1]
* Hrubeš. A subquadratic upper bound on sum-of-squares composition formulas. CCC 2024, LIPIcs 300,
  12:1–12:11; ECCC TR24-026. [Thm 1, 9, 11, 12; §5.2; Problem 1]. Hrubeš. ECCC TR24-099 (2024).
  [Thm 1, 3, 17, 25; Lemma 22]
* Rossman, Zhu. Multiquadratic sum-of-squares lower bounds imply VNC¹ ≠ VNP. arXiv:2512.01227.
* Lenzhen, Morier-Genoud, Ovsienko. arXiv:1007.2337. Morier-Genoud, Ovsienko. arXiv:1304.0949.
  Zhang, Zhu. The Hurwitz sum-of-squares problem depends on the base field. arXiv:2605.00590.
  Zhu, J. On a conjecture of D. B. Shapiro. arXiv:2606.10391.
* Cadney, Huber, Linden, Winter. Linear Algebra Appl. 452 (2014) 153–171. arXiv:1308.0539.
  Song, Chen, Sun, Hu. IEEE Trans. Inf. Theory 69 (2023) 2385–2399. arXiv:2105.07679. [Thm 9]
* Naslund [Nas20], Problems 12 and 13, as cited in hexagon:2610.00577 App. G and arXiv:2310.11356.
* Claude (Anthropic). A 2^{o(n)} time algorithm for 3-SAT. hexagon:2610.00577v1. [§2.4 Lemma
  (eight-square), Lemma 2, Def. 7, Thm A, App. B Thm B/Lemma 9–10, App. G, App. H (71)–(77)]
* Majdoddin. Lowered crossover points of Anthropic's subexponential 3-SAT algorithm.
  arXiv:2610.41622 (30 Oct 2026). [see §4.2 for theorem numbers]
* de Brito. hexagon:2610.00692v1. Nguyen. hexagon:2611.00004v1. MIT Hardness Group et al.
  arXiv:2611.02650. Wu, Wang. arXiv:2611.02548. Curticapean. arXiv:2611.03636. Dias, Lima.
  arXiv:2611.00517.
