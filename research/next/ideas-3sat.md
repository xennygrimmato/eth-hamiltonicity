# Faster 3-SAT: eight routes past 2^{O(n/√log n)} (24 Nov 2026)

Idea generation only. Nothing here is proved, and no script was run. Tags: **[K]** stated in our notes or a cited
source; **[D]** derived here by a short calculation that an executor should re-check; **[C]** conjecture.

Sources read: `engine3-STATUS.md`, `engine3-openai-route.md` (§0–1), `engine3-p2.md` (§0), `engine3-open-door.md`
(index lines only), `engine3-literature.md` (§1.5–1.6), `vpvnp/b1/notebook.md` (§0), `vpvnp/b2/notebook.md` (§0–3),
`next/two-proofs.md` (§0–2), `pieces.md` (§2.2–2.3), `sat-width.md` (§0), `barrier-note/main.tex` (§2, §4.3, §5, §8).
I did not read OpenAI's ETH preprint itself: all statements about it come from `engine3-openai-route.md`.

Targets: (T1) any rate α′ > 1/2, i.e. 2^{O(n/(log n)^{α′})}; (T2) α′ = 1, i.e. 2^{O(n/log n)}; (T3) 2^{n^{1−ε}}.

---------------------------------------------------------------------------------------------------

## 0. Three observations that shape the list

**O1. The arithmetic permits far more than the current rate [K + D].**
- The reading floor of the (K,λ)-clique is e_K ≥ (K−1)/K² (barrier note, Prop. `prop:exponent`). With K ≈ n^{1/9}
  (forced by g = 3K⁸ and the K^g overhead) an ideal clique solver would give 2^{n^{8/9}}. So the clique target itself
  does not block T3.
- b1's conditional floor for oblivious algebraic algorithms is e_K ≥ 1/(16√K) (flat case). That is still polynomial
  decay. Nothing in our notes excludes e_K = K^{−c}, 0 < c ≤ 1/2, even for oblivious algebraic algorithms.
- A tower can never give T3: log K ≤ log n, so e = (log K)^{−α′} ≥ (log n)^{−α′}. T3 needs polynomial decay inside
  one level, hence growing arity (`engine3-open-door.md` §1.10).

**O2. Both labs' engines obey one law: saving 1/√p per p-th root of K [D, heuristic].**
- Anthropic: p = 2 merges, K → K^{1/2}, ρ = 1/√2, repeated log log K times: e = (log K)^{−1/2}.
- OpenAI engine I: the label space ([r]×[r])^Q is a Q-dimensional product grid, the partition at point s is the
  coordinate-s partition, and the cost is ≈ 1/√Q (parity approximate degree). With K = r^{2Q} cells this is
  e ≈ √(2 log r)/√log K. One level, p = Q merges, K → K^{1/p}, saving ≈ 1/√p.
- b2's flat floor is ρ ≥ 1/√p for p fully crossing merges. So OpenAI's √Q cap and Anthropic's 1/√2 are the same
  Pythagorean statement, and a level with p merges that takes the p′-th root of K has α′ = log_{p′}√p. Orthogonal
  (product) merges have p′ = p and always give 1/2. **The law is beaten only by having more merges than dimensions**
  (p > p′): rows, columns and diagonals of one g×g grid have p = 3, p′ = 2, floor α′ ≤ log₂√3 ≈ 0.79; p parallel
  classes of AG(2,g) have floor α′ ≤ ½ log₂ p.

**O3. App. B's pieces lie on a sphere [D from `pieces.md` §2.3].** Row middle weight ≤ E+h+s and column middle
weight ≤ E+h−s give c_row ≈ c√(E+h+s), c_col ≈ c√(E+h−s), so c_row² + c_col² ≈ 2c²(E+h) = (2λ)², the square of the
trivial cost. The flat floor Eλ/√p is exactly what a family with Σ_k c_k² ≤ (Eλ)² would achieve. So "is the flat
floor tight for p merges" is the question "is there a p-merge family with cost vectors on the sphere of radius Eλ".

**Known asymmetry worth using.** In characteristic 0, ρ → 1/2 would give nearly linear sum-of-squares composition
formulas (HWY; barrier note §8 change (ii)). In characteristic 2 that consequence is vacuous:
(Σx_i²)(Σy_j²) = (Σ_{ij} x_i y_j)². The corresponding identity has d = 2 = 0, so it gives no pieces by itself, but
the main external evidence against ρ = 1/2 disappears over F₂ [D].

---------------------------------------------------------------------------------------------------

## Route 1. Three-merge pieces graded by the A₂ weight lattice (covers (v)) — target T1

**Idea.** Build pieces for Δ_q (smallest case Δ₃) under rows, columns and diagonals whose cost vectors satisfy
c_r² + c_c² + c_d² ≤ (Eλ)². App. B grades Fock space by one integer s (a U(1) charge) and the two costs are
c√(w ± s). Replace s by a charge in the A₂ lattice: three weights w_k = w + ⟨v_k, s⟩ with v_r + v_c + v_d = 0, the
v_k at 120°. This is the primal object suggested by b2's extremal price, whose hubs sit on one equilateral triangle
in the plane. The balanced piece would cost 3√3λ in every merge, i.e. ρ = 1/√3.

**Re-aim.** STATUS frames the Δ₃ search as "find ρ < 1/2". **Any three-merge family with ρ < 1/√2 already beats the
current refutation**: α′ = log₂(1/ρ) > 1/2, up to 0.79 at the floor. The ALS runs looked for few-term identities at
N₀ = 2; the effect sought here is asymptotic and has 2^{o(λ)} terms.

**Floors evaded.** Theorem 1 (two merges, ρ ≥ 1/2) allows everything in [1/2, 1/√2). `prop:covering` (any number of
groupings) is for rectangle configurations only. The flat floor for Δ₃ with three merges is 1/√3 < 1/√2, so the
window (1/√3, 1/√2) is open even under FH/PH. The graded two-order floor (spread lemma, 1/√2) is for two orders.

**Most likely failure.** App. B may depend on having exactly two linear orders (row order and column order of one
chain of products); three directions may force "four-block" behaviour and cost vectors on an ℓ₁ ball instead of a
sphere. Then the true three-merge value stays at 1/√2 and the flat floor is simply not tight.

**First experiment (≤ 3 h).** Pure bookkeeping, no tensor optimisation.
1. Calibrate: for the rectangle, take pieces A_s = (charge-s sector of the wire product) in a bosonic occupation
   encoding, compute the row and column flattening ranks by counting boundary states (a DP over partitions), and
   reproduce ρ → 1/√2 and the sphere law of O3 at sizes E ≤ 200.
2. Same code on Δ₃ with a two-component charge and the three weights above; cost of a sector under merge k is the
   log of its number of distinct boundary charge configurations across the three groups.
- **Pass:** max over sectors of min_k c_k, divided by 9λ, is below the calibrated two-merge value by a gap that does
  not shrink with E (extrapolated limit < 0.69).
- **Fail:** the ratio tends to ≥ 1/√2, or no grading commuting with the wire product has three independent weights.

## Route 2. Many parallel classes: p merges in two dimensions (covers (v)) — targets T2, T3

**Idea.** In AG(2,g) all g+1 parallel classes are merges of the same g×g grid into g groups, so K → √K whatever p
is. Use p of them. Edges in the other classes form configurations Δ_g^{(c)} that cross all p merges; an edge whose
class is a merge is internal to that merge and free there. If the sphere law held, ρ_p ≈ 1/√p and α′ = ½ log₂ p:
p = 4 gives 2^{O(n/log n)}, p ≥ 5 beats it. With p = g+1 = √K+1 one level would give e_K ≈ K^{−1/4}, which is
polynomial decay, has growing arity as required, and stays above b1's floor K^{−1/2}/16 [D, C].

**Floors evaded.** `prop:multigroup` (each extra cut costs a factor K in node count) assumes gadgets meeting two
classes per grouping; parallel classes meet g. b2's Theorem 3 gives only 1/√p, and its hypothesis "every edge crosses
every merge" fails once the edge's own class is a merge — b2 names "edges internal to merges" as an exit. The core
floor for a full class is 1/q (`engine3-open-door.md` table), which vanishes.

**Most likely failure.** Same as Route 1, more so: no construction is known for p > 2. Also the price method is only
a lower-bound method; a floor that drops below 1/2 shows the door is open, not that anything walks through it.

**First experiment (≤ 3 h).** Run b2's `far_opt.py` / `metric_lp.py` on AG(2,3) with 4 merges, and on AG(2,4),
AG(2,5) with p = 3, 4, 5, 6 merges, *including the internal-edge accounting* (an edge of class c costs 0 under
merge c), and report the best Euclidean-price lower bound on V/(Eλ).
- **Pass (door open):** the bound falls below 1/2 for some (q, p). Then the A_{p−1} version of Route 1 is the next
  step, and the smallest such (q, p) is the instance to attack.
- **Fail (door closed in the flat case):** the bound stays ≥ 1/2 for all p with internal edges. That is a theorem
  worth writing: under FH, affine-plane levels cannot beat 1/log K.

## Route 3. Measure, do not certify: adaptive bond compression (covers (i)) — target T1

**Idea.** Every floor is about identities Σ A_i = d·f_C for the *full* wire product, valid for all tables. A 3-SAT
instance needs the identity only on the span of the label vectors its tables actually use. Make the level
non-oblivious: after each merge, compute the true rank of every bond of every term (pivoted elimination over a
finite field) and re-encode it; allow pieces chosen per instance for the restricted target. Add branching on heavy
label values (sparsification inside the level) as a second adaptive move.

**Why it could matter [D].** A constant-factor gain per level compounds. If the true bond exponent is (1−δ) times
the certified one at every level, e_K gains a factor (1−δ)^{log log K} = (log K)^{−log₂(1/(1−δ))}: δ = 0.05 raises α′
by 0.074. A rate gain does not need a new identity, only a per-level deficit that holds on every 3-SAT instance.

**Floors evaded.** All of §4 of the barrier note and b1/b2 are statements about the clique polynomial P_K in generic
table entries, or about oblivious circuits. Change (iii) of the barrier note ("eliminates variables or adapts to the
tables") is exactly this.

**Most likely failure.** Supernode tables may be generic enough that true ranks equal certified ranks (block-internal
clauses are rare at the bottom level, so there is no entropy deficit there). Known dead sub-routes, so nobody
re-tries them: branching alone is resolution, 2^{Ω(n)} on random 3-CNF; Gaussian elimination on monomials is
polynomial calculus, degree Ω(n) on random 3-CNF, size 2^{Ω(n)}. Adaptivity has to live inside the counting algebra.

**First experiment (≤ 3 h).** Random and structured 3-CNF, n = 24–36, embedded as a (4,λ)-clique on the 2×2 grid
with λ = 3…8. For the one rectangle, compute over GF(p): (a) the best split R + C of the wire product restricted to
the reachable label subspaces (minimise OSR(R)·rank(C) over the App. B thresholds); (b) the same for random tables of
equal support size.
- **Pass:** the exponent of (a) is at least 5 % below (b) and below the certified App. B value, with the gap not
  shrinking as λ grows, on the worst instance tried (not the average).
- **Fail:** (a) = certified value on some instance family for every λ. Then record that family as the adversary.

## Route 4. Parity world: run the whole engine over F₂ (covers (ii)) — target T2

**Idea.** Decision needs only the count mod 2 after isolation, and isolation is free here: put random weights
α^{w_i} from GF(2^k), k = O(log n), into the variable tables; by the isolation lemma the generating polynomial is
non-zero mod 2. No XOR constraints, no extra shared bits. The engine then needs pieces **over F₂ only** (d = 1).
Search for a two-merge rectangle family over F₂ with ρ < 1/√2, ideally ρ = 1/2 (T2).

**Floors evaded.** Over every field only Theorem 1 (ρ ≥ 1/2) is unconditional. The sharp rectangle floor 1/√2 is
[R|PH] and PH may fail over F̄₂ while holding over ℂ; if a sub-flat trade exists over F₂, b2 says that proves the
contracting hypothesis in characteristic 2 — a win either way. The HWY obstruction is vacuous in characteristic 2
(§0). OpenAI's M₀-template floor (`thm:triangular`) is field-independent, so this route is for Anthropic-type pieces.

**Most likely failure.** Strassen's support functionals behave the same over F₂, and the true rectangle value is
1/√2 over every field. Two sub-ideas I checked and discard [D]: (a) hashing wires to t < λ bits (probabilistic rank
of the identity is O(1/ε)) fails by counting, because exponentially many configurations violate a single wire, so
t ≈ λ; (b) Razborov–Smolensky plus "a polynomial of degree < m sums to 0 over F₂^m" gives nothing inside the clique,
because every label bit is summed and the total degree must then be at least the number of label bits; at the
formula level it is Björklund–Kaski–Williams, a 2^{cn} bound. Also already explored: identities mod 2^P with 2-adic
rank (D.1, P3) land on the flattening floor at K₄.

**First experiment (≤ 3 h).** Exact search over F₂ (SAT solver or exhaustive with symmetry) for SWAP_N = Σ_{i≤T} A_i
at N = 4 and N = 8, T ≤ 4, minimising max_i (log rank A_i + log OSR A_i); the same search over GF(3) as the control
for "characteristic 0 behaviour".
- **Pass:** F₂ admits a strictly smaller optimum than GF(3) at N = 4 or N = 8 for some T.
- **Fail:** equal optima for all T ≤ 4 at both sizes.

## Route 5. A target shaped like the contracting case: the bilinear-forms grid Mat_μ(F₂) (covers (iii)) — T1

**Idea.** Replace the g×g grid by the point set Mat_μ(F₂) with wires along rank-one differences and merges given by
quotients (row space, column space). The VP ≠ VNP dichotomy says: either the rank metric √rk is a price for every μ
(flat: all our floors hold), or for some μ wires at rank distance μ cost s·D(1) with s² < μ — shorter than
Pythagoras. If the second case yields pieces, the distance exponent γ = log_μ s < 1/2 would give ρ = 2^{γ−1} and
α′ = 1 − γ > 1/2. This is the only geometry where the theory says sub-Euclidean trades can exist at all.

**On the other targets asked about [K + D].** Fast matrix multiplication is the K = 3 case of the clique (e₃ = ω/9).
Any algorithm whose saving is an asymptotic rank has e ≥ 1/4 (flattening floor; Zhou closes the rank theory at
⌊K²/4⌋). So ω ≤ 9/4, α ≥ 1/2 and Zwick's n^{2.5} APSP change constants in the exponent, never the rate. What may
transfer is the *method* behind ω ≤ 9/4 (the separation theorem and "untwisting", Li 2611.04175) as a source of
pieces. Hyperedge (GHZ) marks would remove one factor k from the k² in #k-SAT (`sat-width.md`), which widens the
range of k but does not change the 3-SAT rate; Theorem 1 already covers hyperedge pieces.

**Floors evaded.** All flat-case floors, by assumption: the route only works in the contracting case and is
otherwise a proof of flatness on that configuration.

**Most likely failure.** The duality that turns "not a price" into covers is non-constructive and asymptotic
(`two-proofs.md`, "Converse direction [C]"); and the contracting case may simply be false.

**First experiment (≤ 3 h).** μ = 2 (16 points). Run the b2 price LP on the quadrilateral a, a+W, a+W+W′, a+W′
(W, W′ rank one) with row-space and column-space merges, and an exact GF(2) search for a two- or three-term
identity whose cost beats the Euclidean value 2‖λ‖₂ of that quadrilateral.
- **Pass:** any exact identity below the Euclidean value (this is also a √D-shortening certificate, Cor. 1′).
- **Fail:** the LP floor equals the Euclidean value and the search is exhausted at bond dimension ≤ 4.
(This overlaps with idea 1 of `ideas-big.md`; the new part is using it as a level of the engine.)

## Route 6. Combining the two labs: transplant OpenAI's interpolation to non-product merges (covers (iv)) — T1/T2

**What OpenAI does differently [K].** One level, no tower; Q interpolation points, each with its own partition;
the saving is one factor 1/√Q from the approximate degree of parity, with Q ≤ log n/(2 log r) because the label
space is a product. Engine II (D.1) has a third square root (Hardy–Ramanujan count of mode monomials, 2-adic depth
u ≤ log₂ L). By O2 the bottleneck is the same Pythagorean law, reached by a different mechanism.

**Combinations that give nothing [D], recorded so they are not redone.**
- Anthropic's engine in place of OpenAI's brute-force group sums: allows r = O(1), removes only the log log n.
- Anthropic's engine to evaluate the separated sum H(t): shifts the admissible measurement fraction ε by a factor
  √log n, and R depends on ε only through √ln(1/ε).
- D.1 as the leaf solver of the tower: its degree condition forces λ ≤ K₀⁸, so the two logarithms are tied and the
  product of savings is a constant.
- "Runs instead of windows" with fixed r: closed by the (ρ+1)-minor lemma (`engine3-p2.md`).

**The combination still open.** OpenAI's deformation X_v → ⟨P_{e,v}(T), X⟩ is a way to manufacture a p-merge family
for p = Q *commuting* swaps. Transplant it to merges that are not coordinates of a product: the three directions of
Δ₃, or p parallel classes, where the direction projections of AG(2,q) are orthogonal after removing constants
(Radon decomposition) and the label "code" has distance Q − 1. The template (T2) is dead there by the triangular
bound, so this must use the general interface or be re-expressed as pieces.

**Most likely failure.** P2's numerics: in every search the best designs measured single variables, i.e. nothing
beyond the naive route; and Dias–Lima's 2^{Ω(√tw)} still stands for clause-product schemes.

**First experiment (≤ 3 h).** (a) Write OpenAI's window construction M₀ = V₀f(W₀) as an explicit piece family on the
antipodal p-cube configuration (2^{p−1} wires, p coordinate cuts) and compute its ρ_p for p = 2…8.
(b) Replace the p commuting swaps by the three direction-swaps of Δ₃ and recompute at Q = 3.
- **Pass:** (a) ρ_p·√p stays bounded (confirms O2), and (b) gives a three-merge profile with ρ < 1/√2.
- **Fail:** (a) fails (then O2 is wrong and Route 2's heuristic loses its support), or (b) ≥ 1/√2.

## Route 7. Simplex routing: read an algorithm off b1's extremal configuration (covers (i)/(v)) — target T3

**Idea.** b1 shows the flat-case floor is ℓ·|Z_S| with Z_S the *resultant* of the unit directions of the wires
crossing a balanced cut S, and that the simplex configuration attains Λ_k ≈ k^{3/2}/3. The gap to the engine
(k²/√log k) is the gap between a resultant and a count. Look for a divide-and-conquer on the node set (balanced
cuts, not grid groupings) whose terms pay the resultant: pieces graded by A_{K−1} charges, one occupation number per
node, so that a cut sees only the net charge it separates. Success would be e_K = O(K^{−1/2}), i.e. 2^{n^{1−ε}}.

**Floors evaded.** `prop:twogroup`, `prop:covering` and Majdoddin's Thm 4.13 concern grid algorithms that expand
into terms and pick a grouping; a cut hierarchy on the nodes is not of that form. It respects b1's floor by design.

**Most likely failure.** In a cut hierarchy a term must be cheap on *all* cuts of the tree at once, while the sphere
law (O3) says a piece cheap in one direction is expensive in the orthogonal ones. This is the reason the tower takes
a minimum over groupings; the route needs a cut family whose directions are far from orthogonal.

**First experiment (≤ 3 h).** For K = 4…8 and the simplex configuration, compute with b1's scripts the vectors
(|Z_S|)_S over all balanced S in a binary cut tree, and solve the small LP: is there a distribution over "charge
sectors" whose cost on every cut of some tree is ≤ (1+o(1))·ℓ|Z_S|?
- **Pass:** feasible for some tree at K = 6 and K = 8 with total cost below the best contraction tree
  (min(ω/9, 1/4)·K²ℓ).
- **Fail:** infeasible for every tree; record the dual certificate as a new floor for cut-tree algorithms.

## Route 8 (wild). Geometry-free evaluation: pay for nonlinearity, not for cuts (covers (vi), (ii)) — target T3

**Idea.** Some tensor classes contract in polynomial time on *any* graph: affine indicators with quadratic phases
(stabilizer tensors, Gauss sums over Z₄), and, mod 2, determinantal tensors (perfect matchings mod 2 are a
determinant on non-planar graphs too; more generally the permanent mod 2^k costs n^{O(k)}, Valiant). In the standard
network of a 3-CNF every wire is an equality, which is affine. So write the clause layer as a sum of χ tensors from
such a class; the count (mod 2 or mod 2^k, enough for decision after the free isolation of Route 4) costs χ·poly(n)
with no shared-bit cost at all. The question becomes the class-rank of the clause layer of an n-variable formula:
is it 2^{o(n/√log n)}, or even 2^{n^{1−ε}}?

**Floors evaded.** Every floor in our notes is a cut-rank or spectral-point bound on wires, or a bound on the clique
polynomial with generic tables. Here cuts are free and the clique polynomial is never formed. The only known lower
bounds on stabilizer rank are linear or quadratic in the number of magic gadgets, and the old conditional barriers
(strong simulation hardness) assumed ETH.

**Most likely failure.** Known sub-multiplicativity is a constant in the exponent (2^{0.396t} for t T-gates), and a
3-CNF has m > n clauses, so a constant per clause loses to 2^n. Gadget-by-gadget reductions must pay per clause
(otherwise ⊕P = P). A win needs class-rank that is sub-multiplicative without bound on clauses sharing variables.

**First experiment (≤ 3 h).** Exact search (meet in the middle over GF(2) truth tables, ≤ 9 bits) for the rank of
the "variable star" tensors S_d = (one variable shared by d clauses OR₃, other literals free), d = 1…4, in the class
of affine-quadratic tensors over Z₄ and in the class of determinantal tensors mod 2.
- **Pass:** log χ(S_d)/d decreases with d over the range (per-clause cost falls as clauses share variables).
- **Fail:** χ(S_d) = χ(S_1)^d, or a constant per-clause cost ≥ 1 bit.

---------------------------------------------------------------------------------------------------

## Ranking by (probability) × (value)

Probabilities are my guesses for "the first experiment passes and the route then delivers its target".

| rank | route | target | prob. | why this rank |
|---|---|---|---|---|
| 1 | **1. A₂-graded three-merge pieces** | T1 (α′ up to 0.79) | ~10 % | only route where the floor leaves a known open window and a concrete ansatz exists; any ρ < 1/√2 is a new record |
| 2 | **2. p parallel classes** | T2, T3 | ~4 % | the experiment is an LP with existing scripts and both outcomes are results; if open, value is the largest of the piece routes |
| 3 | 3. adaptive compression | T1 | ~5 % | cheap, and compounding makes small gains count; the adversary instance is likely to exist |
| 4 | 4. engine over F₂ | T2 | ~3 % | finite decisive search; win–win with the dichotomy in characteristic 2 |
| 5 | 6. OpenAI transplant | T1/T2 | ~3 % | mainly a second construction method for Routes 1–2, and a test of O2 |
| 6 | 5. Mat_μ(F₂) target | T1 | ~2 % | works only in the contracting case |
| 7 | 7. simplex routing | T3 | ~1 % | highest value among algebraic routes; the sphere law argues against it |
| 8 | 8. geometry-free classes | T3 | <1 % | no floor known at all; no mechanism known either |

**Top two: Route 1, then Route 2.** They share one question (is the flat floor tight beyond two merges) and one
ansatz (charges in A_{p−1}); Route 2's LP should run first because it takes an hour and tells Route 1 which p to aim
for. Route 6(a) is the cheapest independent check of the heuristic O2 on which both rest.

**Caveats.** O2 and O3 are my reading of secondary notes, not of the two papers; if O3's sphere law is not what
App. B's Lemma 9 gives, Routes 1, 2 and 7 lose their ansatz but not their floors. Route 2's polynomial-decay
arithmetic assumes the level's term count stays subexponential when p grows with K, which I did not check.
