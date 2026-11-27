# ideas-round2: routes past 2^{O(n/√log n)} outside the proved barriers, with kill tests

27 Nov 2026. Machine-generated, not refereed, nothing here is checked by a person. Tags as elsewhere:
[R] proved here (short argument given), [D] derived, unreviewed, [N] numerical (script named), [K] from the
literature (as far as read), [C] conjecture, [X] dead with reason. "Paper" = `paper-barriers/main.tex`;
AN-ETH / AN-VP = Anthropic's two papers; OA-HC etc. = OpenAI's release.

Scripts: `ideas2/fullplane.py`, `ideas2/fam.py`, `ideas2/hill.py` (outputs `ideas2/*.out`); they reuse
`podprod.py` and were calibrated against known values (3-net of order 4: 0.54104; of order 3: 0.52022, flat
0.49789; K₄: 0.47140).

## 0. Summary

No idea below has a construction. One new gap in the barrier list was found (§1: nets with more than √g + 1
classes, in particular full affine planes; also Latin-square nets without group structure), five proposed
escapes were killed by calculation (§§5–8), one by a literature check (§4, half of it), and one modest target
that does not touch the exponent 1/2 is recorded (§3, the factor log log n in the bound in n).

Ranked list (odds = my probability that the route yields an algorithm beating exponent 1/2, i.e.
2^{O(n/(log n)^α)} with α > 1/2 or better; "result odds" = probability of a stateable theorem either way).

| # | idea | evades | first test | outcome of the test done | odds |
|---|---|---|---|---|---|
| 1 | Designs without elementary-abelian structure: **full affine planes (p = g+1 classes), nets with p > √g+1 classes, Latin-square nets of non-group type**; nested crossing covers there | Theorem A / B / C / D′ (need m ≥ 2, p ≤ q+1, generic edges); Theorem W gives only ≥ F_CAT, unknown there | placement values on full AG(2,g) | [N]/[R] flat value √g/(g+1), node pods √(2g−2)/(g+1), both → 0; pair cap g/((g+1)√2); nothing above node pods at g = 3, 4 in a weak local search. **Window open, wider than the cyclic one** | 1–2% (result odds 50%) |
| 2 | True costs of crossing pieces under a third / foreign merge; finite criterion on E_D (H44, funded) | Theorem W (certified only); price barrier only if contracting fails | exact ranks on E_D at λ ≤ 3 | not mine; §2 gives the weakest sufficient statements | 1–2% |
| 3 | Remove log log n from the bound in n (AN-ETH App. D) | not an exponent-1/2 question; no barrier applies | locate the source of log Δ | [D] it is the O(n) marks of the parity checks at log Δ address bits each; entropy bound shows marks must drop to O(n/log Δ); a CRT variant fails (§3) | 5–8% for 2^{O(n/√log n)} in n; 0 for α > 1/2 |
| 4 | Other free resources than merges: sums of Pfaffians (matchgates), sums of Gauss sums (stabilizer rank), as leaves or as the whole engine | Theorem T (not a program for f_{K,λ}); all price statements (no wires, no merges) | literature: growth of Gaussian / stabilizer rank of tensor powers | [K] Gaussian rank: an October 2026 preprint claims unconditional exponential lower bounds → depth-2 Pfaffian sums [X]. Stabilizer rank: exact lower bound still linear, upper 2^{0.396t}: open, but only as a depth-2 object | < 1% |
| 5 | Short wires (λ ≪ K) and identities with 2^{Θ(λ)} terms | Theorem T (needs λ ≥ CK log^{3/2}K); price barrier as stated (2^{o(λ)} terms) | does the price bound survive a term rate η > 0? | [D] the price bound on (terms + cost) degrades to 1/√2 − Θ(√η); but [X] for towers: terms are paid at rate 1 and costs at rate e_ℓ (`ports/c1d1/notes.md`), gain is a constant factor. Whole-level non-product identities at moderate λ remain formally uncovered, no mechanism | < 0.5% |
| 6 | Node growth β < 2 with two-way crossings; unbalanced grids; larger base K | — | counting | [R] a pair of merges covers at most a g^{β−2} fraction of edge pairs; unbalanced g₁ × g₂ grids are exactly neutral at α = 1/2; K ≤ √(6m). [X] | 0 within crossing designs |
| 7 | Approximate / probabilistic rank on bounded integer tables; hashed wires | Theorem T (not a polynomial identity) | error budget | [X] needs entrywise error < 2^{−2S}, where the ε-rank of the wire is full; hashed wires count 2^{2S−r·#edges} pseudo-solutions | 0 |
| 8 | Hypergraph-native recursion (GHZ marks on triples instead of pairwise wires) | price barrier as stated (D1 cost is pairwise) | conversion factor | [D] a GHZ of d bits is a restriction of two wires of d bits: costs differ by a factor ≤ 2, exponent unchanged; could only help item 3 | 0 for the exponent |
| 9 | Branching + engine hybrids, decision instead of counting, sampling of terms | — | arithmetic | [X] branching pays 1 bit to remove ≤ d bits worth e each: gain only for degree d > 1/e = √log n, which is what sparsification already does; isolation for 3-CNF costs 2^{Ω(n)}; sampling signed terms needs additive error 2^{−n} | 0 |
| 10 | Dichotomy from outside (H47, funded): prove contracting or ports in one characteristic | all barriers (they assume ¬contracting or ¬ports) | — | §2 lists the weakest finite statements; nothing new tested | 1% |

Fund: **#1** (new, cheap, both outcomes are results, tooling exists) and, of the things not yet funded,
**#3** as the low-risk target; #2 and #10 stay the highest-value items and are already funded.

## 1. Designs outside Theorem A: full planes, many classes, Latin squares

**The gap [R].** Theorems A, B, C, D′ and the positive-target corollary of the paper concern nets 𝒩(q, m, P) with m ≥ 2 and
P ⊆ P¹(F_q): g = q^m, at most q + 1 ≤ √g + 1 classes, and they use generic edges (rank 2 over F_q). A net on
g² points with more than √g + 1 classes is not of this form. The extreme case is the full affine plane AG(2, g)
with all g + 1 parallel classes (m = 1, P = P¹(F_g)): every edge lies on a line, so there are no generic edges
at all. The paper's §"What is open" names cyclic nets only. Also uncovered: 3-nets of Latin squares that are
not group tables (no quotient onto F_q^m; a random Latin square has almost no subsquares, so no copies of X₄).

More classes never hurt an engine: a term may use any merge, K′ = g² and K = g as before, β = 2.

**Why Theorem A's construction cannot extend [R].** In Theorem A a node is a 2-space W_a, a line of class x is
a point of W_a, and collinear nodes share exactly that point. If every two nodes are collinear, every two of
the W_a meet, so the W_a are coplanar: the realisation is the plane PG(2, g) itself, where q1-notes §2.3
already records Σ_k s^k_e ≤ √2. This is the obstruction of the paper's proposition on Z₃ (cyclic nets) in a second family.

**Numbers [N, R].** E = g²(g²−1)/2; under merge k a fraction 1/(g+1) of the edges is internal.

- Flat placement (one regular simplex per class, orthogonal classes): every edge sees g crossing classes with
  orthogonal unit differences, value **√g/(g+1)** per edge and merge [R; script agrees].
- Node pods (one (g+1)-pod per node, the g+1 lines through it at radius 1 on distinct arms):
  **√(2g−2)/(g+1)** [N for g = 2..5: 0.4714, 0.5000, 0.4899, 0.4714; formula fitted, not proved].
- Upper bound for every CAT(0) placement, from the two-merge inequality summed over all pairs of classes: each
  edge crossing k is internal to exactly one other class, so (g−1)Σ_k b_k ≤ Σ_{k<l} √2·E(g−1)/(g+1), i.e.
  value ≤ **g/((g+1)√2)** [R, given the paper's two-merge cap (`thm:cap2`) for each pair].
- Best known cover (two classes only, App. B pieces): (g−1)/((g+1)√2) + 1/(g+1).

| g | flat | node pods | pair cap | two-class cover |
|---|---|---|---|---|
| 2 (K₄) | 0.4714 | 0.4714 | 0.4714 | 0.5690 (three classes: 0.4714, attained) |
| 3 | 0.4330 | 0.5000 | 0.5303 | 0.6036 |
| 4 | 0.4000 | 0.4899 | 0.5657 | 0.6243 |
| 5 | 0.3727 | 0.4714 | 0.5893 | 0.6381 |
| 8 | 0.3143 | 0.4157 | 0.6285 | 0.6611 |
| g → ∞ | → 0 | → 0 | → 0.7071 | → 0.7071 |

(The value 0.6381 at g = 5 is the two-merge corner 0.638071 of the paper's depth-two table: calibration.)
At g = 2 everything coincides and the floor 0.4714 < 1/√2 is attained by the three crossings of K₄. For g ≥ 3
the price method can never certify the two-class cover on the full plane (pair cap < cover), and the known
placements tend to 0, where for the F₂^m nets with three classes Theorem A gives 1/√2 − O(1/g).

Searches [N, weak]: mixtures of node pods with flat factors and off-centre hubs give nothing above node pods
for g = 3, 4, 5 (`ideas2/fam.py`); a hill climb over products of pods (`ideas2/hill.py`, 10 minutes each, outputs
`ideas2/hill3.out`, `ideas2/hill4.out`), started from node pods with extra random factors or with perturbed
radii, came back to at most 0.4998 (g = 3) and 0.4880 (g = 4): node pods are a local optimum in this model and
nothing above them was seen. Only one fully random start completed (g = 3: 0.4512). This search is far weaker
than the Rust models of the cone and filtration runs; it is not evidence about the supremum.

**What it would mean.** If lim_g F_CAT(AG(2,g), all classes) < 1/√2, Theorem W leaves room for nested crossing
covers on full planes with certified value below 1/√2, and certified values are true upper bounds: an
improvement of the exponent (by Theorem T it would give ports). If the limit is 1/√2, there is a placement
of a new kind (not by subspaces with W_a ∩ W_{a′} minimal), and Theorem A extends to all nets of
characteristic 2. I expect the second, or that attainment fails; the K₄ case shows that the first is not
absurd at small order.

**Why it might die.** (i) Small orders carry O(1/g) effects only (side edges become crossable when their own
class is present; that is all K₄ shows), and a tower needs g → ∞. (ii) At level 1 a crossing piece of classes
(k, l) costs at least max(c_k, c_l) under every foreign class (ideas-threeway Lemma 1.1), so with g + 1 classes
the uniform game value tends to 1 and the game sits at a two-class corner, as on the Z₅ net. (iii) Depth-2
nesting gained 0.1–1% on the testbeds.

**First tests, in order.** (a) Run `piecefloor` (FiltSpace, ConeGraph, tree products) and the finite CAT(0)
relaxation of `q1c/relax.py` on full AG(2,3) (12 hubs, 36 edges) and AG(2,4) with 4 and 5 classes: does
anything exceed 0.5000 / 0.4899, does the relaxation go below the pair cap? (b) The level-1 and depth-2
certified games on full AG(2,3) and AG(2,4) with all classes (`attain/depth2*.py`): compare with 0.6036 and
0.6243 and with the pair caps. (c) Theory: either a placement with value bounded below for g → ∞, or an upper
bound on F_CAT that uses complete collinearity. (d) Add the family to §"What is open" of the paper.

## 2. Contracting and ports: weakest sufficient statements (for H44, H47)

No test done; this section only fixes targets.

- [R, from imp. (d) of the paper] If contracting fails over k, √rk is a price on Mat_μ(F₂) for every μ ≥ 3,
  hence on Mat₂(F₂) by restriction. So **"the 16-point space (Mat₂(F₂), √rk) is not a price over k" implies
  contracting over k**. Conversely contracting at μ = 2 says exactly that no price on these 16 points has
  D(2) = √2·D(1). Any inequality valid for all spectral points on 16 parties and violated by √rk suffices;
  CAT(0) inequalities cannot do it (Theorem B places the space in a CAT(0) cube complex).
- [R, the paper's positive-target corollary] Identities for the eight wires E_D with 2^{o(λ)} pieces, all below
  (1/√2 − η)·8λ under some merge.
- One characteristic is enough for a randomised power-saving algorithm (README result 4); characteristic 0 for
  a deterministic one.
- Sources of a three-way identity not yet in the files: (i) triality. The eight-square identity is the
  two-merge shadow, at λ = 3, of the octonion product, and on K₄ the three matchings are the wires, the row
  pairs and the column pairs; the identity is one of three relabelled forms 2W_i = P·(Σ_j + Σ_l). On K₄ this is
  already optimal (flat floor attained), so the test is on E_D or X₄ at λ = 3: 24 bits, three merges into four
  groups, exact ranks under the third merge of the products of row and column choices on its four crossings. This is an H44
  computation; I did not run it. (ii) The full plane of order 4 (§1) is the smallest configuration where a
  three-way law would be visible in a level and not only in an O(1/g) fraction.
- Known and not re-proposed: Hadamard-universal expanders ⇒ ports (`ports/ideas-ports.md`), characteristic 2
  special (H34), Pfaffian and triangle identities (H33, H36), tensor powers of tiny identities (H38).

## 3. The factor log log n (a target below the exponent)

AN-ETH proves 2^{O(km/√log m)} and 2^{O(k² n log log n/√log n)} and says: "we do not know whether the factor
log log n can be removed". For general 3-CNF the bound in n is the theorem. Removing the factor gives
#3-SAT in 2^{O(n/√log n)}; it does not change α = 1/2.

Where it comes from [D, from App. D]: sparsification with ε ≈ (log n)^{−1/2} leaves degree
Δ = (k/ε)^{O(k)}; nodes hold variables; [no clause violated] is expanded by inclusion–exclusion over marked
violated clauses, cut off at n̄ ≈ n/log Δ marks (O(n) bits); assignments violating more than n̄ clauses are
killed by r = O(n) sparse parity checks, expanded 2-adically, which leaves up to n + r marks at log Δ bits
each. That term, O(n log Δ), is the whole loss.

Kill tests [D]:
- Entropy: M marks among m = Δn clauses cost log C(m, M) ≈ M log(m/M) bits however they are routed, so one
  needs M = O(n/log Δ) marks in the checks, not cheaper marks.
- CRT over the first log Δ primes with ℓ-adic checks ([ℓ | q] = ℓ^{−1}Σ_ζ Σ_i (ζ−1)^i C(q, i), valuation ≈
  i/(ℓ−1)): the marks per prime are ≈ (ℓ−1)·n′/log ℓ for modulus 2^{n′}, and with n′ = n/log Δ and
  ℓ ≈ log Δ·log log Δ this is ≈ n again. [X]
- Fermat checks 1 − v_w^{ℓ−1} with random weights: n·ℓ/log ℓ marks. [X]
- Decision only, count mod 2 after isolation: no isolation lemma for 3-CNF with success above 2^{−Θ(n)}. [X]
Not tested: checks that each kill all but a 2^{−c} fraction at fewer than c marks; a sparsification whose
output has O(n) marks' worth of structure (few variables of high degree, handled by a second branching);
replacing truncation by a direct count of heavy assignments. Odds 5–8%.

## 4. Other free resources: Pfaffians and Gauss sums

Mechanism. The engine's only free operation is merging (a term is cheap if few bits cross the groups).
Counting has two other classical free families: Pfaffians (matchgate networks on any graph, as Grassmann
integrals) and Gauss sums of quadratic forms over F₂/Z₄/Z₈ (stabilizer networks). #3-SAT is a network of O(n)
non-free vertices on a free background, and the cost of "expand every non-free vertex" is the rank of a tensor
power of the vertex in the free family. A sub-exponential growth of that rank would give 2^{o(n)} without clique
sums. Theorem T does not apply (no program for f_{K,λ}; the tables are not arbitrary), nor does any price
statement.

Literature check (two searches, abstracts only) [K]:
- Fermionic Gaussian rank: a preprint of October 2026 (arXiv 2610.03699) claims unconditional exponential lower
  bounds for k copies of a magic state; the extent is multiplicative for 4-qubit magic states (2407.20934). So
  sums of Pfaffians at depth 2 are [X], if that preprint holds.
- Stabilizer rank of T^{⊗t}: upper bound 2^{0.396t} (2106.07740); exact lower bound Ω(t) (2106.03214,
  2110.07781); approximate Ω(t²/log t) (2610.06819). Open by an exponential margin. The lower bounds that were
  believed here were conditional on ETH.
What the autumn results already give [D]: an amplitude of a Clifford+T circuit with t T-gates is a bounded-arity
#CSP on O(t) variables with weights in Z[ω], so the clique engine (integer tables, four components) evaluates
it in 2^{O(t/√log t)}: strong simulation in 2^{o(t)}. This is a deep circuit, not a stabilizer decomposition,
and it says nothing about stabilizer rank.
Why it dies: the depth-2 object (rank) is the wrong one, as for clique sums, where the generalised asymptotic
rank is 2^{S/2} (largest flattening) and all the gain is in depth; a recursive engine with Gauss-sum leaves has
no merge-like step that keeps arbitrary tables free. First test if pursued: stabilizer rank of CCZ^{⊗2}, CCZ^{⊗3}
against the product bound, by the existing exact-search tooling. Odds < 1%.

## 5. Short wires and many terms

- Theorem T needs λ ≥ CK(log K)^{3/2}. The engine itself needs only λ ≳ √log K·log log K (so that (λ²)^{|R|}
  terms cost less than e·S) [D]. A clique (K, λ) with short wires does not embed a long-wire clique (a group of
  s nodes has s²λ inner bits against s(K−s)λ boundary bits), so Theorem T says nothing there [R].
- The price method with a term rate: for an exact spectral point, log|I| + max_i log φ(A_i) ≥ log φ(f), and
  log φ(A_i) ≤ λ·Σ d_φ(leg, hub) + δ_k(φ)·c_k(A_i) with all d_φ ≤ 1. Far legs force δ_k(φ) ≈ 1/(2t) when the
  legs are at distance t·δ, so the bound on (log|I| + cost)/bits is b(t) − (2t−1)η for 2^{η·bits} terms. For the
  crossing square, b(t) = 2t − 2√(t² − t/√2 + ¼): the bound is 0.676, 0.610, 0.501 at η = 0.001, 0.01, 0.05,
  i.e. 1/√2 − Θ(√η) [N, one-line script]. So as a statement about one level the barrier does not cover
  η > 0.
- [X] for towers, already in `ports/c1d1/notes.md` (after EG 1.2): terms are paid at rate 1, cost bits at rate
  e_ℓ, so the gain per level is at most O(e_ℓ²λ) per copy, a constant factor in total.
- Left formally open: one identity for a whole level at moderate λ whose terms are not products over copies
  (the paper's "rate" gap). No mechanism known.

## 6. What fixes β = 2 and the exponent's shape

- e = ρ^ℓ and log K = β^ℓ·log K₀ give e = (log K)^{−log_β(1/ρ)}; K²λ ≈ 6m forces K ≤ √(6m), so "a larger base"
  changes constants only. A better base case (ω, triangles) changes e₀ only. [R]
- Unbalanced grids g₁ × g₂ with g₁ = K′^a: a term at angle θ costs min(cos θ·e(g₁), sin θ·e(g₂)); the worst
  angle gives e(K′) = e₁e₂/√(e₁²+e₂²), and with e(K) = (log K)^{−α} this is self-consistent iff
  a^{2α} + (1−a)^{2α} ≥ 1, i.e. α ≤ 1/2, with equality for every a at α = 1/2. Neutral. [R]
- β < 2 with two-way crossings: put the K′ = g^β nodes in the g × g array of a pair of merges (k, l), n_rc nodes
  in cell (r, c), row and column sums s = K′/g. A wire pair can be crossed for (k, l) only on a rectangle with
  all four cells occupied, and the number of such pairs is at most Σ √(n_rc n_r′c′ n_rc′ n_r′c) = s²·tr(M²),
  M_cc′ = Σ_r √(n_rc n_rc′)/s. M has unit diagonal and row sums ≤ s, so tr(M²) ≤ g·s and the pair (k, l) covers at
  most a fraction s/g = g^{β−2} of the edge pairs. With p merges, coverage needs C(p,2)·g^{β−2} ≳ 1, and then a
  merge sees crossings on a fraction ≈ 2/p only: ρ ≥ 1 − (2/p)(1 − 1/√2), α′ = O(1/(p log β)). [R] So β = 2 is
  forced by the rectangle, not by the grid; a design with β < 2 needs pieces that fuse wires along something
  other than rectangles (no candidate; Theorem T covers any such design conditionally).
- Overlapping clusters: a node in two clusters is two nodes joined by its full state; the copy wire costs
  what the overlap would save. [D]

## 7. Approximate and probabilistic rank [X]

Tables bounded by 2^B and an integer answer allow an entrywise error ε in each wire, but the error multiplies
through 2^{2S} index settings and K tables: ε < 2^{−2S−BK}, and the ε-rank of the 2^λ × 2^λ identity is Ω(2^λ) once
ε < 2^{−λ/2} (it is O(λ/ε²) only above that). Hashed wires ([h(x) = h(y)] with r bits) are one-sided but admit 2^{2S − r·#edges} pseudo-solutions,
so r ≈ λ. With nodes holding variables the supports are small (2^{n/K} per node), but then the instance is a
dense 2-CSP with domain 2^{n/K}, where only the matrix-multiplication saving is known.

## 8. Hybrids, decision, sampling [X]

Branching on a variable of degree d costs one bit and removes at most d − 1 edge bits worth e each: useful
only for d > 1/e ≈ √log n, which is the regime sparsification handles and the source of §3. Working mod 2
needs isolation, unavailable for 3-CNF. Sampling the signed terms estimates Z/2^n to additive error, never to
2^{−n}. Value-dependent branching on table entries at inner levels has no worst-case handle: the tables there
are sums over inner variables of signed terms and are not sparse.

## 9. Challenges to the list of open routes in the brief

- (3) "cyclic designs" should read "designs without a rank-2 elementary abelian quotient acting on few
  classes": cyclic nets, Latin-square nets, and every net with more than √g + 1 classes (§1).
- (4) short wires and exponential term counts are open only for single levels; towers are closed by the
  rate argument (§5). Non-algebraic escapes by approximation are closed (§7).
- (5) is closed for crossing-based designs by counting (§6); β and the base are not free parameters.
- Not on the list and real, though below the exponent: the log log n of the bound in n (§3).
- Under OpenAI's two theorems every algebraic clique engine in the long-wire regime is capped at 1/2 whatever
  the design, so (2), (3) and §1 are, in that world, routes to ports and not to a moderate gain; the only
  unconditional-in-kind escapes are tables with structure and non-algebraic steps, for which this round found
  no mechanism that survives a first calculation.
