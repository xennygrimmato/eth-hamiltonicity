# Research tracks (27 Oct 2026, after Anthropic's paper)

Coordinator notes. Each track has its own file; this file records cross-cutting facts and leads.
Tags as in `findings.md`: **[Lean]**, **[Paper]** (a lab's manuscript), **[Mine]**.

## What Anthropic's paper changes

Source: `anthropics/formal-math`, folder `eth` (paper `paper.pdf`, statements `MainResults.lean`).

* **Main Theorem [Lean].** One deterministic machine counts the models of every k-CNF with m clauses
  on n variables within `2^{C·min(km/√log m, k²·n·log log n/√log n)}` steps. The constant C is
  absolute and k is part of the input. Compare `findings.md` Task 1: OpenAI's Lean constants grow
  like `k·k!`. For our encodings, what matters is total length, not width.
* **The engine [Paper, §2].** It evaluates `Z = Σ_z Π_a W_a(z_a) Π Ψ_ab` with arbitrary integer node
  functions `W_a` and equality-test edges. The running time is `2^{O(S/√log S)}` times the cost of
  evaluating `W`, where S is the total number of bits on the edges. An edge function "costs c bits"
  if its integer rank across the edge is at most `2^c`.
* **Exponent ↔ pieces [Paper, Theorem A, Def. 7].** Suppose the crossing `[x=v][y=u]` on λ-bit
  strings splits into poly(λ) integer pieces, each factoring through `c_row` bits as a function of
  (x,y) vs (u,v) and through `c_col` bits as a function of (x,u) vs (y,v), with
  `c_row + c_col ≤ 4ρλ + O(log λ)`. Then #k-SAT runs in `2^{O(km/(log m)^{log₂(1/ρ)})}`. Known values:
  * eight-square identity, ρ = 11/12;
  * single-bit `SWAP = I − 2·singlet`, ρ = log₂12/4 ≈ 0.896;
  * partition operators (App. B), ρ = 1/√2, which gives √log.

  The definition allows ρ ≥ 1/2, and ρ → 1/2 would give `2^{O(m/log m)}`. → **Track H**
  (`pieces.md`).
* **Consequences claimed [Paper, §7]:** Independent Set, Clique, Vertex Cover, Dominating Set,
  k-Colouring, and E^NP ⊄ linear-size circuits. **No Hamiltonicity / Cut&Count problems**, and
  likewise none in OpenAI's paper. Our `hamiltonicity.md` results are not covered by either.

## State of the art for Hamiltonicity (prior work, all `c^n` with c > 1)

| Setting | Best previously known | Ours |
|---|---|---|
| general undirected, decision | Björklund `O*(1.657^n)` randomized; `O*(2^n)` deterministic | — (no gain on dense graphs) |
| bounded degree Δ | Björklund–Husfeldt–Kaski–Koivisto `(2−ε_Δ)^n` (TSP) | randomized `2^{o(n)}` |
| max degree 3 | Eppstein `O(2^{n/3}) ≈ 1.26^n` deterministic | randomized `2^{o(n)}` |
| directed, average outdegree δ | Björklund (arXiv 2009.11780) `2^{n−Ω(n/δ)}` poly space, Monte Carlo | randomized `2^{o(n)}` (δ = O(1)) |
| parity of #HC, directed | Björklund–Husfeldt FOCS'13 `O*(1.619^n)` deterministic | deterministic `2^{O(|E|/√log|E|)}` |

So for bounded average degree our bounds are the first subexponential ones. This is asymptotic
only: the crossover is astronomically large, as for the SAT algorithms themselves.

## Leads opened today

1. **Exact #HC via low rank over ℚ (Track C).** Raz–Spieker (Combinatorica 1995): the matrix
   `[P ∪ Q is one Hamiltonian cycle]` on perfect matchings has real rank only `2^{O(n)}` (a
   binomial coefficient), against `n!` rows. So across one cut, connectivity costs O(b) bits over
   ℚ, not `b log b`. The colouring barrier (`hamiltonicity.md` §8) is specific to colourings. Open
   question: do the per-cut decompositions compose into one sum of products with O(|E|) edge bits?
2. **Short certificates (Track D).** A CNF verifier for "X is a Hamiltonian cycle" of length
   `L = o(n√log n)` would give deterministic decision in `2^{O(L/√log L)}` via the Lean Main
   Theorem. Raz–Spieker also proves nondeterministic communication `Ω(n log log n)` for the same
   function. That lower bound is compatible with `L = O(n log log n)` but excludes O(n).
3. **Derandomization barriers (Track E).** Deterministic parity-to-decision for HC versus
   derandomized Valiant–Vazirani.
4. **Denser graphs, for free [Mine].** The Lean n-bound is uniform in k. Encode each vertex's two
   cycle neighbours by binary indices: `V = O(n log d)` variables, width `O(log d)`, any number of
   clauses. Cut&Count parity then runs in time `2^{O((log d)³·n·log log n/√log n)}`. That is
   subexponential for average degree `d ≤ 2^{c((log n)^{1/2}/log log n)^{1/3}}`, i.e. up to
   `2^{(log n)^{1/6−ε}}`. Dense graphs stay out of reach: positions need `log n` bits per vertex.

## Track E result (derandomization; `derandomization.md`) — not Lean-checked

* **Better randomized decision, top-level theorem only [Mine, written proof].** `P_G(w) = Σ_H Π_{e∈H} w_e`
  is multilinear with 0/1 coefficients, so it is nonzero as a function on `F_p^E` iff G is Hamiltonian.
  Alon–Füredi: a uniform `w` gives `P_G(w) ≠ 0` with probability `≥ p^{−n/(p−1)−1}`. The value mod p is
  the model count of a CNF with p colours per vertex plus weight gadgets: width `O(log p)`, length
  `O((|E|+n) log p)`. With `p ≈ √log n`, Anthropic's uniform-in-k Main Theorem gives one-sided
  randomized decision in `2^{O(n (log log n)²/√log n)}`, which improves the Lean-verified `2^{δn}` of
  `hamiltonicity.md` §5a. **Candidate for formalisation** (Alon–Füredi is not in Mathlib as far as I
  know).
* **Barrier.** Suppose an algorithm sees S only through weighted residues mod `q ≤ Q`, adaptively. Then
  it needs `≥ (|U|/lcm(1..Q) − 1)/ln Q` queries, by a Davenport-constant argument; this generalises §8.
  Non-uniformly, a fixed list of `2^{o(n)}` weight vectors works for all bounded-degree graphs (union
  bound). So the open problem is *explicit* hitting sets. Conditionally (E needs `#P`-oracle circuits of
  size `2^{Ω(ℓ)}`), relativised Impagliazzo–Wigderson gives a deterministic `2^{o(n)}` algorithm.
* **Structure.** `t_q(G)` = the least size of an edge restriction with a nonzero residue. Restriction
  search is deterministic `2^{o(n)}` iff `t_Q(G) = o(n)`, and `t_p(G) ≤ log₂ #HC(G)`, tight.
  Conjecture R: `t_Q(G) ≤ n·f(Q)` with `f → 0` for bounded degree.

## Track H result (pieces / exponent; `pieces.md`) — not Lean-checked

* **No piece decomposition with ρ < 1/√2 found; no lower bound beyond the trivial ρ ≥ 1/2.**
  * Commutative tensor-power classes are solved exactly by a quantile formula. The bit-symmetric
    span{I, SWAP} class has limit ρ ≈ 0.869 (better than the paper's 0.896, worse than 1/√2).
  * The Bell/Pauli class comes out ≈ 0.70 at λ = 20 by exact computation, with a generic-formula limit
    of 0.804.
  * Conjecture: commutative classes stay ≳ 0.8.
* **Side result: Appendix B → sum-of-squares bound [Mine, short proof, to double-check].** Pieces with
  parameter ρ give Naslund/HWY width `P(N) ≤ poly(log N)·N^{2ρ}`: each piece is a sum of `2^{min(c_row,c_col)}`
  rank-1 terms in its cheaper direction. With Anthropic's ρ = 1/√2 this is `P(N) ≤ N^{√2+o(1)}`. Via
  HWY11 Prop. 4.1 (`s ≤ P(N) ≤ 4s`) the composition number is then `s ≤ N^{1.4143+o(1)}`, against Hrubeš's
  `O(N^{1.62})` (CCC'24). Before claiming this, check:
  1. that HWY's `s` and Hrubeš's `s` are the same variant (bilinear products vs. squares, and the field);
  2. Appendix B's correctness, since it is an unreviewed paper.
  The paper itself only uses the converse direction (Hrubeš ⇒ ρ ≈ 0.905).
* **Consequence for strategy.** Beating √log within Anthropic's framework ⇔ pieces with ρ < 1/√2, which
  would also push the sum-of-squares upper bound below `N^{1.414}`. That suggests a genuinely new
  algebraic structure is needed (the agent's heuristic: Appendix B's loss comes from the `exp(c√E)`
  growth of partitions).

## Track C result (exact #HC; `exact-count-lowrank.md`) — REFEREED: SOUND, conditional on Anthropic's paper

* **Construction [Mine, numerically verified on 40 instances, not yet refereed].**
  * Matrix-tree on 2-factors: `n·#HC = Σ_{2-factors X} τ(X)`, because τ is n for a Hamiltonian cycle
    and 0 for a disconnected 2-factor.
  * τ is a Berezin integral `∫ Π_e (1 + x_e(ψ̄_i−ψ̄_j)(ψ_i−ψ_j))`.
  * Splitting V into g blobs costs `log₂5` bits per crossing edge, plus a fermionic sign
    `(−1)^{Σ_{a<c<b<d} P_ab P_cd}` paid with O(g³) parity-copy bits.
  * The result is a network with arbitrary integer node tables and about `2.32|E| + O(g⁴)` edge bits.
* **Consequence if sound:**
  * exact #HC, hence deterministic decision and search, for bounded average degree in `2^{δn}` for
    every δ > 0;
  * possibly `2^{O(n/√log n)}`, though that bookkeeping is unchecked.
* **What it rests on.** Anthropic's clique algorithm with table queries, Theorem A(b), which is
  **proved in their Lean** as `ExplicitCost.recursionSolves`. The top-level CNF Main Theorem does not
  suffice: the sign is non-local at vertex level.
* **Supporting facts computed:**
  * bipartite Raz–Spieker ranks are `C(2n−2, n−1)` over ℚ and `2^{n−1}` over GF(2);
  * the non-bipartite matching-cycle matrix is rank-deficient first at t = 6 (kernel 462 = dim S^{(4,4,4)});
  * cut ranks are about `5^b/2`.
* **Status:** an independent referee is re-deriving the construction with fresh code
  (`review-exact-count.md`).

## Exact-count extensions (`exact-extensions.md`) — numerically verified, unrefereed

All of these use one template: local tables × a Berezin/determinant factor, split over blobs. Each
problem was checked exactly three ways: brute force = determinant identity = blob network. The
checks used random partitions with K = 2–4 blobs. The agent ran seeds 1–3; I re-ran seed 7 and got
"ALL OK".

* **Fits the template:**
  * directed HC (3 labels per arc, 1.58 bits);
  * TSP and ATSP with poly(n) weights (optimum and number of optimal tours, via Kronecker substitution);
  * s–t and all Hamiltonian paths, directed paths;
  * spanning trees with local degree constraints (leaf distribution, max-leaf);
  * Steiner tree (count, minimum weight, number of optima);
  * connected vertex cover and connected dominating set (decision and minimum size; counts only τ-weighted);
  * induced forests, i.e. exact minimum feedback vertex set and its count, via a new
    "2−deg mass" identity;
  * all forests T_G(2,1);
  * Steiner forest with O(1) pairs;
  * counting k-paths and k-cycles.
* **Fails:** exact counts of connected vertex covers, connected dominating sets and connected
  subgraphs (T_G(1,2)). There τ acts as a weight, not as a 0/1 connectivity test.
* **Caveat (Lemma 8):** the cost depends on P, the maximum number of bits at one blob, so a vertex of
  degree Θ(n) breaks the bound. Fixes:
  * a ghost/root vertex is free;
  * hubs in degree-≤2 problems compress to O(log d) bits;
  * hubs in tree problems split into a path of copies.
* **Claim if the core holds:** deterministic `2^{δn}` for all these problems on graphs with
  |E| = O(n). This depends on Anthropic's Theorem A(b) and Lemma 8 for general networks.

## Catalogue of contradicted bounds (`sharp-eth-catalogue.md`), assuming the engine

A bound counts as *contradicted* only when there is an explicit `2^{δn}` algorithm on the same
instance class. The bounds' implications ("#ETH ⇒ …") stay true; they are vacuous once #ETH is false.

* **Already contradicted by the labs' papers (local encodings):** sparse permanent and #PM
  (DHMTW14, Curticapean), #IS and #2SAT, and Tutte points on the hyperbolas H_q for integer q ≥ 2.
* **New, from our template:**
  * **T(x,1) for every x ≠ 1, including counting forests.** Brand–Dell–Roth (arXiv 1606.06581) show
    no `exp(εn)` on sparse simple graphs under #ETH; this was the last open line of the #ETH Tutte
    dichotomy. Our forests-by-edge-count identity computes all of T(x,1).
  * ETH-hardness of sparse Hamiltonian Path (LMS11) and the standard sparse `2^{Ω(n)}` bounds for TSP,
    Steiner tree, FVS, connected VC/DS, Max-Leaf and Longest Path. These are exact and deterministic.
* **Still open (frontier):**
  * dense graphs;
  * the x = 1 line, T(1,2) and reliability;
  * generic Tutte points such as T(2,0);
  * exact counts of connected sets;
  * Steiner forest or disjoint paths with ω(1) pairs;
  * directed FVS;
  * embedding problems;
  * planar `2^{o(√n)}`.
* **Prior best results:** all `c^n`. Examples:
  * #DHC `2^{n−Ω(n/δ)}` (Björklund–Williams);
  * #HC `6^{pw}`;
  * cubic TSP `1.2312^n`;
  * Steiner tree `1.36^n`;
  * CDS `1.8619^n`;
  * FVS `1.7548^n`.

## Rigorous write-up of exact #HC (`exact-hc-theorem.md`) — written proofs, referee pending

* **Theorem 1.** For every δ > 0 and D, deterministic `O(2^{δn})` exact #HC for |E| ≤ Dn.
* **Theorem 2.** One deterministic algorithm computes #HC in `2^{C*·max(m,n)/√log n}` for every graph.
  Corollary: decision, search, and exact counting of Hamiltonian paths in the same time.
* **Proofs given in full:**
  * the identity;
  * τ as the top Grassmann coefficient, via a Grassmann Cauchy–Binet (no Gaussian sign conventions);
  * the Koszul / blob factorisation;
  * the sign rule, for arbitrary partitions, edge orders and generator orders;
  * the exact network (W_a, Ψ_ab, f_ab);
  * the bookkeeping against Lemma 8(i) and Theorem A(a),(b), with Theorem B for √log.
* **Gaps found and fixed:**
  * the per-node bit bound P: branch on cycle edges at vertices of degree > n/g;
  * the sign costs O(g³) bits in total, at most g² per node;
  * K_ℓ ≤ n^{1/30} for the sharp bound.
* **Depends on [A]:** Lemma 8, Theorem A(b) and Theorem B. All three are in Anthropic's Lean
  (`ExplicitCost.groupingExplicit`, `ExplicitCost.recursionSolves`, `PiecesCounted.halfPieces`), but
  there they are applied only to CNF networks. Applying them to this network is a paper argument.
* **Checks** (`proof_checks.py`): all intermediate identities, the network value by brute force, and
  [A]'s grouping; dropping a sign term breaks them. Coordinator re-run with seed 23 on 30 instances:
  ALL CHECKS PASSED; dropping signs gives wrong values on 20 of 30.

## Meta-theorem (`meta-theorem.md`), assuming (A1) Anthropic's network theorem and (A2) the Grassmann blob construction

* **Class.** Sparse graph or digraph; local integer tables; an objective with poly range; O(1) global
  predicates on label-selected subgraphs. Predicate types:
  * connected, tree, path, single cycle, forest, minimum number of components;
  * directed: branchings, reachability, strongly connected, directed cycle or path.

  Each predicate is a determinant that is > 0 exactly when it holds, with its own Grassmann field.
* **Result.** Deterministic `2^{δn}` for:
  * decision with a witness;
  * min/max of the objective;
  * determinant-weighted counts;
  * exact counts when every predicate is tree-like.

  Needed: |E| ≤ cn, bounded degree (or the hub condition), poly weights, w ≥ 0.
* **Coverage of Cut&Count Thm 1.2.** Covered: everything except cycle packing, max cycle cover and
  maximally disconnected DS, which need the *maximum* number of components. New relative to the
  earlier list: connected FVS/OCT, min cycle cover, k-leaf outbranching, max full-degree spanning
  tree, graph-metric TSP, edge-disjoint spanning trees, min strongly connected spanning subgraph.
* **Checks.** 9 new families pass (`meta_problems.py`). Ablation: dropping the sign or merging the
  fields breaks it. These are small instances that check the algebra, not the asymptotic bit counts.

## Referee verdict on exact #HC (`review-exact-count.md`)

**Sound, conditional on Anthropic's paper [A]** (Theorem A(b), Lemma 8(i), existence of pieces). The
referee derived the sign rule independently and wrote the code from scratch before reading the
write-up.

* **Tests:** about 500 Berezin-equals-determinant checks; about 790 blob evaluations and 297 literal
  [A]-style network evaluations (g ≤ 5, random/unequal/empty blobs, random roots, random integer
  weights); 0 failures. Removing the global sign gives wrong answers on 8 instances.
* **Model fit:**
  * all edges are genuine equality tests;
  * `U ≤ 2·log₂5·m + g³`;
  * the exponent is at most δn for `e ≤ δ/40D`, `K ≥ 60D/δ`, `g = 3K⁸`;
  * no hidden blow-up (the interleaving costs O(g³) bits).

  The unbounded-degree trap is handled correctly by the write-up's branching (Lemma 6.1).
* **Minor wording point:** the alphabet must merge two terms (labels {N,0,1,2,3}). This only changes
  a constant.
* **Literature:**
  * identity (1) is elementary folklore;
  * the Grassmann matrix-tree theorem is Caracciolo–Jacobsen–Saleur–Sokal–Sportiello (2004), and
    should be cited;
  * Björklund's determinant sums (arXiv 1008.0541) use a related pattern.

  No robust lower bound other than ETH, #ETH or SETH is contradicted.
* **Still open:** human expert review, and checking that [A]'s Lean statements of
  `recursionSolves` / `groupingExplicit` cover general networks.
