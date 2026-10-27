# Which published (#)ETH lower bounds are now contradicted by explicit algorithms?

27 Oct 2026. This is a literature catalogue plus analysis. It **assumes** that the algorithms of
`exact-extensions.md` are correct: deterministic `2^{δn}` for every δ > 0 on graphs with |E| = O(n),
conditional on Anthropic's Theorem A(b) and Lemma 8 for general networks.

Tags:

* **[Lit]** a statement checked against the cited abstract or full text (via ar5iv/arXiv) today;
* **[Lit?]** recalled or secondary, not re-checked against the text;
* **[Inf]** my inference;
* **[Lab]** follows from the labs' #SAT theorems through a linear-size *local* encoding;
* **[Ours]** follows from `exact-extensions.md`.

**What "contradicted" means here.** A theorem of the form "#ETH ⇒ no 2^{o(n)} algorithm for X"
stays a true implication. Now that #ETH is false (Anthropic Cor. 6; OpenAI), it is *vacuous*. It is
*contradicted* in the sense we care about only once someone exhibits an explicit 2^{o(n)} or
2^{δn}-for-all-δ algorithm for X, on the same instance class (sparse, simple, bounded degree, and
so on). Refuting ETH alone does **not** give such algorithms for connectivity problems, because no
SERF reduction *from* Hamiltonicity, FVS or Steiner Tree *to* 3-SAT is known. The reductions of
Impagliazzo–Paturi–Zane go the other way: [IPZ01](https://doi.org/10.1006/jcss.2001.1774). The
earlier note `findings.md` §2 makes the same direction point. [Inf]

---

## 1. Catalogue: published lower bounds versus explicit algorithms

"Local" means that the solution has an O(n)-bit certificate checkable by O(n) bounded-width clauses
when |E| = O(n). Such problems are already settled by the labs: Anthropic Cor. 6/7
(`paper.txt` lines 1176–1222) or OpenAI's Cor. 1.3 (`findings.md` §2). "Global" means that the
property needs connectivity or acyclicity, which is where our contribution lies.

| # | Published lower bound (exact statement) | Source | Instance class | Contradicted by | Who |
|---|---|---|---|---|---|
| 1 | #ETH ⇒ the permanent with entries in {−1,0,1} (and the general permanent) has no exp(o(m)) algorithm, where m = #nonzeros; 0/1 entries: no exp(o(m/log n)) under #ETH, no exp(o(m)) under rETH (Thm 1.3) | Dell–Husfeldt–Marx–Taslaman–Wahlén, TALG 2014, [arXiv 1206.1775](https://arxiv.org/abs/1206.1775) [Lit] | sparse matrices | a variable per nonzero, "exactly one" per row and column, and a parity chain for signs: #SAT with O(m) variables [Inf] | **Lab** (already) |
| 2 | #ETH ⇒ #PM has no 2^{o(n)} algorithm even on bipartite graphs of max degree 3 (Thm 1.1, Cor. 4.1); same for the matching polynomial μ(G;ξ) and the independent-set polynomial I(G;ξ) at every fixed rational ξ (≠0) on sparse graphs (Thm 1.2); also #min VC and #max IS on line graphs of max degree 4, and #monotone 2-SAT | Curticapean, *Block interpolation*, ICALP 2015 / Inf. Comput. 261 (2018), [arXiv 1511.02910](https://arxiv.org/abs/1511.02910) [Lit] | sparse, bounded degree | local CNF; OpenAI §1.1.2 explicitly says it refutes Curticapean's #PM bound (per `findings.md` §2); Anthropic Cor. 7 counts IS/VC of each size | **Lab** |
| 3 | #2SAT and #IS: no exp(o(m)) under rETH (Thm 1.2) | DHMTW14 [Lit] | sparse | Anthropic Cor. 7 | **Lab** |
| 4 | Tutte T(x,y) on **simple sparse** graphs: no 2^{o(n)} under #ETH when y ≠ 1, (x−1)(y−1) ≠ 1 and (x,y) ∉ {(1,1),(−1,−1),(0,−1),(−1,0)} (Thm 1.3) | Curticapean 2015 [Lit] | simple, O(n) edges | **only the points with q = (x−1)(y−1) ∈ {2,3,…}**: the q-state Potts sum over colourings, counted by the number of monochromatic edges, is a local #CSP with O(m log q) variables. On y = 0 (q-colourings) Anthropic Cor. 7 works at **any** density. Nowhere-zero k-flows, T(0,1−k), are also on H_k and local. All other points stay open (§2) [Inf] | **Lab** (H_q only) |
| 5 | DHMTW Thm 1.4: (i) multigraphs, no exp(o(n)) for (x−1)(y−1) ≠ 1 and y ∉ {0,±1}; (ii) simple, no exp(o(n)) at y = 0, x ∉ {0,±1}; (iii) simple, no exp(o(m/log²m)) on x = 1, y ≠ 1; (iv) simple, no exp(o(m/log³m)) at (x−1)(y−1) ∉ {0,1} minus 3 points; line y = 1 left open | DHMTW14 [Lit] | (i) dense multigraphs; (ii)–(iv) simple | (ii) at x = 1−k, k ≥ 3 integer: Anthropic Cor. 7 (any density). (iv) only on H_q, q integer ≥ 2, sparse. (i) and (iii) **not** contradicted | **Lab**, partial |
| 6 | **#forests T(2,1), and more generally T(x,1) for every x ≠ 1: no exp(o(n)) (stated as exp(εn)) under #ETH on simple graphs with ≤ C·n edges** (Thm 1/Thm 6). This completes the #ETH Tutte dichotomy (Cor. 2), whose easy set is H_1 ∪ {(1,1),(−1,−1),(0,−1),(−1,0)} | Brand–Dell–Roth, IPEC 2016 / Algorithmica 2019, [arXiv 1606.06581](https://arxiv.org/abs/1606.06581) [Lit] | **simple, |E| = O(n)**, the same class as ours | row 4d′: forests counted by number of edges gives the whole polynomial T(x,1) = Σ_F (x−1)^{r−|F|}, hence every x, deterministic 2^{δn} [Ours] | **Ours (new)** |
| 7 | ETH ⇒ no 2^{o(n)} for Hamiltonian Path (Thm 3.3); the standard 3-SAT reductions give graphs with O(n+m) vertices *and* edges [Inf] | Lokshtanov–Marx–Saurabh, *Lower bounds based on ETH*, BEATCS 105 (2011), [arXiv 1007.5450](https://arxiv.org/abs/1007.5450) [Lit] | sparse / bounded degree [Inf] | rows 0, 1, 3a–3b: #HC, #DHC and #HP, exact and deterministic; hence decision and search | **Ours (new)**. Labs: no. Our earlier Cut&Count route (`hamiltonicity.md`) gave only parity, plus randomized decision |
| 7′ | the same for TSP, Longest Path/Cycle, Max-Leaf Spanning Tree, Steiner Tree, FVS, Connected VC and Connected DS: 2^{Ω(n)} under ETH on sparse graphs, via standard linear reductions from bounded-degree VC/3-SAT (FVS: a triangle per edge; Steiner: terminal per edge plus root; Max-Leaf = n − γ_c) | folklore; LMS11 §3 and Cygan et al., *Parameterized Algorithms* (Springer 2015) Ch. 14 [Lit?, exact theorem numbers unverified] | sparse | rows 2, 4a, 4b, 4c, 4c′, 4d, 4f [Ours] | **Ours (new)**. The labs give only plain VC/DS/IS |
| 8 | planar HC, Steiner, FVS, CVC: no 2^{o(√n)} under ETH (LMS11 Thm 3.5 for planar HC) | [arXiv 1007.5450](https://arxiv.org/abs/1007.5450) [Lit] | planar | **not contradicted**: 2^{δn} is worse than the known 2^{O(√n)} | — |
| 9 | #k-path / #k-cycle: no f(k)·n^{o(k/log k)} under #ETH | Curticapean–Marx FOCS 2014, [arXiv 1407.2929](https://arxiv.org/abs/1407.2929) [Lit?] | general (dense) graphs, parameter k | **not contradicted**. That bound concerns k ≪ n; on bounded-degree graphs #k-path is trivially FPT. Ours matters for k = Θ(n) on sparse graphs | — |
| 10 | the modular-counting analogues (⊕ / #_p k-paths, matchings) | Curticapean–Dell–Husfeldt ESA 2021, [arXiv 2107.00629](https://arxiv.org/abs/2107.00629) [Lit?] | parameterized in k | **not contradicted** (same reason as row 9) | — |
| 11 | Boolean #CSP: all #P-hard cases need exp(Ω(n)) under #ETH | Brand–Dell–Roth [Lit] | n variables, any density | Anthropic Main Theorem (n-bound) | **Lab** |
| 12 | Jaeger–Vertigan–Welsh: T(x,y) is #P-hard off H_1 ∪ {8 special points} (a #P statement, not ETH) | Math. Proc. Camb. Phil. Soc. 108 (1990), [doi](https://doi.org/10.1017/S0305004100068936) [Lit?] | — | the map of §2 below | — |

**Honest summary.**

* Everything about permanents, matchings, independent sets, #2SAT, Boolean #CSP and the Potts or
  colouring or flow hyperbolas H_q with integer q ≥ 2 was settled by the labs' theorems, through
  local encodings. Some of it is written down in their papers: Anthropic Cor. 7, and OpenAI §1.1.2
  for #PM.
* The **new** contradictions are these:
  1. Brand–Dell–Roth's y = 1 line (#forests), the last line of the #ETH Tutte dichotomy. Because of
     our result, that line is *not* hard on sparse graphs.
  2. ETH 2^{Ω(n)} bounds on sparse graphs for HC/HP (directed and undirected), TSP with poly weights,
     Steiner Tree, FVS, Connected VC, Connected DS, Max-Leaf, Longest Path/Cycle, and their exact
     counting versions where `exact-extensions.md` gives exact counts.
* I found **no** published #ETH lower bound specific to *counting* HC, Steiner trees or minimum
  FVS. Counting inherits the decision bound. [Lit?: searched, not exhaustive.]

## 2. Frontier: what the method does *not* cover

| Problem | Why not | Relevant hardness |
|---|---|---|
| **Dense graphs** (all problems above) | the network has U ≈ 2.32·2|E| bits, so the time is 2^{δ|E|}. If the sharper 2^{O(|E|/√log|E|)} holds, the time is subexponential in n iff average degree d = o(√log n) [Inf]. The `hamiltonicity.md` log-encoding trick (d up to 2^{(log n)^{1/6−ε}}) helps only the Cut&Count *parity/decision* route, not the exact Berezin counts, because the per-edge Grassmann factor costs Θ(|E|) | dense #HC: best is 2^{n−Ω(√n)} ([Li 2023, arXiv 2309.15422](https://arxiv.org/abs/2309.15422)) |
| **T(1,2) connected spanning subgraphs; reliability; the whole line x = 1** | τ is a weight, not a 0/1 connectivity test (row 5 fails) | DHMTW Thm 1.4(iii): exp(Ω(m/log²m)), simple graphs; exp(Ω(n)) on multigraphs; Curticapean Thm 1.3 for sparse simple graphs |
| **Tutte at generic points**: q = (x−1)(y−1) ∉ {1,2,3,…}, y ≠ 1, e.g. acyclic orientations T(2,0), totally cyclic T(0,2), chromatic polynomial at non-integer q or q = ω(1) | needs q^{k(A)} with k(A) global, or orderings | Curticapean Thm 1.3, Brand–Dell–Roth Cor. 2 (sparse simple, 2^{Ω(n)}) |
| **Exact counts of connected VC, connected DS, connected induced subgraphs (connected sets)** | the same τ-weight issue | #P-hard; no specific #ETH paper found |
| **Steiner forest / disjoint paths with p = ω(1) pairs** | there are Bell(p) networks and log(4c+1) bits/edge, so the time degrades to 2^{O(δ n log p)} (`exact-extensions.md` §3) | Steiner forest contains Steiner tree; k-disjoint paths is ETH-hard for large k [Lit?] |
| **Multiway cut** | *covered by the labs*, not a frontier item: edge/node multiway cut with t = O(1) terminals is a t-label local CSP, and minimum cuts ↔ labelings 1-1 because every component contains a terminal [Inf]. For t = ω(1) the cost is n log t bits | — |
| **Directed FVS, DAG/acyclic-orientation problems, Directed Steiner** | no determinant indicator for directed acyclicity of *induced* subgraphs is known to us (the directed matrix-tree gives arborescences, i.e. DHC works, but not "S induces a DAG") [Inf] | DFVS: best (2−ε)^n, e.g. Razgon 1.9977^n [Lit?] |
| **Embedding / ordering problems** (Subgraph Isomorphism, bandwidth, treewidth computation) | the hardness comes from permutations, not connectivity: 2^{Ω(n log n)} under ETH | Cygan et al., *Tight lower bounds on graph embedding problems*, JACM 2017, [arXiv 1602.05016](https://arxiv.org/abs/1602.05016) [Lit?]. Now vacuous; not contradicted |
| **Planar / minor-free** | 2^{δn} does not beat 2^{O(√n)}. Open: does the blob network compose with balanced separators to give 2^{o(√n)}? [Inf] | LMS11 Thm 3.5 |
| **Exponential weights (TSP, Steiner)** | B becomes exponential, so the method is exact only for poly(n) weights | — |

## 3. Prior state of the art for the covered problems (sparse or bounded degree)

All prior bounds are c^n with c > 1. Ours is deterministic 2^{δn} for every δ, exact counting, for
|E| = O(n).

| Problem | Best prior known | Det/rand, count/decide |
|---|---|---|
| #HC directed | 2^{n−Ω(n/δ)} for average degree δ: Björklund–Williams ICALP 2019, [doi](https://doi.org/10.4230/LIPIcs.ICALP.2019.25) [Lit]. General: 2^{n−Ω(√n)}, [Li 2023](https://arxiv.org/abs/2309.15422) [Lit] | det, counting |
| #HC undirected, bounded degree | 6^{pw}·poly by Bodlaender–Cygan–Kratsch–Nederlof, [arXiv 1211.1505](https://arxiv.org/abs/1211.1505), tight under SETH by Curticapean–Lindzey–Nederlof SODA 2018, [arXiv 1709.02311](https://arxiv.org/abs/1709.02311) [Lit]. With pw(cubic) ≤ n/6 + o(n) (Fomin–Høie, IPL 2006, [doi](https://doi.org/10.1016/j.ipl.2005.10.012)) this gives ≈1.348^n on cubic graphs; with pw ≤ m/5.769 + O(log n) (Kneis–Mölle–Richter–Rossmanith, SIDMA 2009, [doi](https://doi.org/10.1137/080715482)) it gives c_d^n [Inf] | det, counting |
| HC / TSP decision | cubic: O*(1.2312^n), Xiao–Nagamochi, Algorithmica 2016, [arXiv 1212.6831](https://arxiv.org/abs/1212.6831) [Lit]. Max degree Δ: (2−ε_Δ)^n, BHKK TALG 2012, [doi](https://doi.org/10.1145/2151171.2151181) [Lit]. Average degree d: (2−ε_d)^n, Cygan–Pilipczuk, [arXiv 1302.3763](https://arxiv.org/abs/1302.3763) [Lit]. General: 1.657^n randomized, Björklund FOCS 2010, [arXiv 1008.0541](https://arxiv.org/abs/1008.0541) [Lit?] | det (except Björklund) |
| TSP, poly weights, #optimal tours | as above; BCKN's rank/determinant methods give det c^{tw} for weighted and counting variants [Lit] | det |
| Ham paths, k-paths/k-cycles (k = Θ(n)) | the same pathwidth DPs; for fixed k, #k-path in n^{0.174k+o(k)} (Curticapean–Dell–Marx STOC 2017, [arXiv 1705.01595](https://arxiv.org/abs/1705.01595)) [Lit?] | det, counting |
| Steiner tree (min weight) | O(1.36^n) exp. space, O(1.60^n) poly space: Fomin–Grandoni–Kratsch ESA 2008 [Lit, secondary]. O*(2^k) with bounded weights: BHKK STOC 2007, [arXiv cs/0611101](https://arxiv.org/abs/cs/0611101) [Lit?]. **Counting** Steiner trees: c^{tw} by the BCKN determinant approach [Lit?, check Steiner explicitly] | det |
| #s–t paths (Steiner, T = {s,t}, no non-terminal leaves) | #P-complete (Valiant 1979, [doi](https://doi.org/10.1137/0208032)); prior exact algorithms are pathwidth DP [Inf] | det |
| Degree-constrained / max-leaf spanning trees | Max-Leaf = n − γ_c, so O(1.8619^n) via CDS [Lit]; no exact-count algorithm for the leaf distribution found [Inf] | det, decision |
| Connected DS | O(1.8619^n), Abu-Khzam–Mouawad–Liedloff, JDA 2011, [HAL](https://hal.archives-ouvertes.fr/hal-00607125) [Lit] | det, decision |
| Connected VC | O*(2^k) det (Cygan SWAT 2012, [arXiv 1202.6642](https://arxiv.org/abs/1202.6642)) [Lit?]; Cut&Count 2^{O(tw)} randomized ([arXiv 1103.0534](https://arxiv.org/abs/1103.0534)) [Lit]; rank-based det c^{tw} (BCKN). Sparse graphs: c_d^n [Inf] | det, decision |
| Min FVS / #min FVS | O(1.7548^n) det, Fomin–Gaspers–Pyatkin–Razgon, Algorithmica 2008, [doi](https://doi.org/10.1007/s00453-007-9152-0) [Lit?], which also enumerates the ≤ 1.8638^n minimal FVSs (this gives the count of minimum ones) [Lit?]. Randomized improvement by monotone local search, [arXiv 1512.01621](https://arxiv.org/abs/1512.01621) (1.7217^n [Lit?, not in abstract]) | decision det/rand; counting via enumeration |
| #forests T(2,1), T(x,1) | 2^n·poly, more precisely poly × #connected vertex sets: BHKK FOCS 2008, [arXiv 0711.2585](https://arxiv.org/abs/0711.2585) [Lit]. That is (2−ε_Δ)^n for max degree Δ, by the connected-set bound of BHKK TALG 2012 [Inf] | det, counting |
| Steiner forest, O(1) pairs | decision and min weight are **polynomial** (Dreyfus–Wagner, O(1) terminals), so our gain is only for *counting* [Inf] | — |

### Notes

* **Raz–Spieker and CLN.** CLN18 prove that the matchings-connectivity matrix has rank 4^k/poly(k)
  over ℚ, consistent with `README.md` Track C's C(2n−2,n−1). Their (6−ε)^{pw} SETH lower bound for
  counting HC is about pathwidth, not n, so our result does not contradict it, since pw = Θ(n) for
  expanders. [Inf]
* **Wording of claims.** Contradicting Brand–Dell–Roth means "#forests on sparse simple graphs is
  computable deterministically in 2^{δn} for every δ". It does not mean that the published
  implication is false.
