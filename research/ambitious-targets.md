# Ambitious targets: which decades-old bounds can our tools plausibly move, and which are provably out of reach

4 Nov 2026. Informal survey and ranking. Read after `fine-grained-map.md` (the 60-row map), `factoring-engine.md`,
`dense-structured.md`, `permanent/barrier.md`, `tutte-plane.md`, `engine2-*.md`, `kstar.md`, `NEXT-STEPS.md`.
Scratch scripts for this note: `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/ambitious/`
(`euler_check.py`: ALL PASS; `subsetsum_accounting.py`: the formula of §2.5).

Tags. **[known]**: literature, checked against the source named in the row (abstract level unless stated).
**[proved here]**: a derivation in this note (none is Lean-checked; §2.9's identity is checked numerically).
**[heuristic]**: an inference, an accounting estimate, or a judgement.
**[repo]**: established earlier in this repository (file named).

---------------------------------------------------------------------------------------------------

## 0. The yardstick: what the tools give and what they cannot

Everything below is measured against three facts.

**T1 (what a positive result needs) [repo: `anthropic-api.md`, `permanent/barrier.md` Lemma 2.1].** Anthropic's engine
computes the value of a network `Net g` (nodes with private settings of ≤ P bits, pairwise factors routed through
c_ab shared bits, U = Σ c_ab) in time 2^{e_K (U + gP/K) + 2gP/K}·poly, with g = 3K⁸ nodes (Lemma 8 case (i)),
K ≥ 2^{18}, e_K ≈ (3x₀+6)/√log K. So a problem on parameter n beats a known bound 2^{αn} only if
(i) the **witness** has O(n) bits (the engine's exponent is at least U/(2√(log U + 2x₀)), and U is at least the
witness bits that must cross node boundaries); (ii) the **verifier's cut** U is O(n) once the witness is split
over g ≥ 3K⁸ ≈ 2^{146} nodes; (iii) every **node load** P is ≤ n/K⁷ (a node that must see Θ(n) bits is
inadmissible for every K); (iv) the problem is a **count** (sum of products), not a ∀-statement: an existential
quantifier is fine (prefix search turns counting into search), a universal one is not. OpenAI's Boolean tensor
network bound (Thm D.1, unverified) has the same shape: s edges, degree ≤ s^{0.9}, time 2^{O(s/√log s)}.

**T2 (what is already taken) [repo: `fine-grained-map.md` §4].** The labs' top-level theorems already give 2^{δn}
for every problem with an O(n)-bit witness checkable by an O(n)-size circuit or bounded-width clauses on O(n)
variables (IPZ's SERF class): k-SAT, #k-SAT, IS, Clique, VC, DomSet and k-Colouring *at any density* (Cor. 7),
#2-SAT, k-Hitting Set, sparse permanent, #PM, Boolean #CSP, CNF-SAT with O(n) clauses of any width. Our own
machine-checked results add the sparse connectivity problems (#HC, TSP with poly weights, directed HC, ATSP,
quantum amplitudes) and the E^NP ⊄ SIZE(εn√log n) bound. Three Hexagon preprints (Bhattacharjee 2610.00594,
Nguyen 2611.00004, de Brito 2610.00692) and the factoring preprints (Rudich–Rousseau 2610.00600, Shunia
2610.00711, Akshima et al. ECDL) cover poly-weight sparse Max-Cut/Max-k-SAT, Tutte on H_q, bounded-degree binary
CSP by treewidth, factoring (2^{n/k} in Lean; 2^{O(n/√log n)} conditionally).

**T3 (what is provably out of reach for the engine) [repo: `permanent/*.md`, `tutte-plane.md`, `engine2-*.md`].**
*Dense* problems — permutation-type witnesses (permanent, dense HC/TSP, orderings) and Θ(n²)-term objectives
(dense Max-Cut) — need U = Θ(n log n) in every vertex-local network (cut-rank theorems; Tutte off the hyperbolas
needs (1−o(1)) n log n), so the engine's guarantee is ≥ 2^{(1/2−o(1)) n √log n} ≫ 2^n. Reaching them would need an
engine rate e_K = o(1/log K); every mechanism tried (pieces, groupings, randomisation, FMM, characteristic p,
correlated decompositions) is capped at ρ ≥ 1/2 or 3/8, i.e. α′ ≤ 1 (2^{O(U/log U)} at the very best), and an
*unconditional* proof that no oblivious algorithm beats c/log K would separate VP from VNP (`engine2-algebraic.md`
M6). The key phrase for the rest of this note: **dense ⇒ blocked; sparse or linear-witness ⇒ taken or takeable.**

Two more standing caveats on every positive item: constants are galactic (first crossover n ≈ 2^{55 000} for #HC,
`crossover.md`), and Anthropic's engine uses exponential space.

---------------------------------------------------------------------------------------------------

## 1. Candidate table

Columns: best known bound and how long it has stood; why it matters; engine fit (witness bits / U / P / rate);
status of the Oct–Nov 2026 wave; feasibility for us (0–10); verdict.

| # | problem | best bound, standing since | value | engine fit | 2026 wave | feas. | verdict |
|---|---|---|---|---|---|---|---|
| 1 | **Integer factoring**, n-bit N, deterministic | N^{1/5+o(1)} deterministic (Harvey 2021; Pollard–Strassen N^{1/4} 1974/76); L(1/3) heuristic NFS [known] | cryptography, number theory | witness n bits (p); verifier = one multiplication = Schönhage–Strassen BTN with O(n) edges, degree n^{3/4} → g ≤ 3n^{1/5} clusters, U, gP = O(n) → **2^{O(n/√log n)}** (`factoring-engine.md` §3) | RR: Lean, ∀k ∃C 2^{n/k}; Shunia: 2^{O(n/√log n)} conditional on OpenAI D.1 + AK Thm 3, no Lean | 8 | **go**: Lean-verify the rate on Anthropic's engine (F1–F6, ≈10–15k lines) |
| 2 | **Square roots / least quadratic non-residue / roots of fixed-degree f mod p**, deterministic unconditional | non-residue p^{1/(4√e)+ε} (Burgess 1957/62); Shanks–Tonelli needs a non-residue; Schoof poly only for fixed a; Shoup ~p^{1/2} for root finding [known] | classic "derandomise without GRH" problems | y² ≡ a: one modular ×; non-residue: count #{x<B, y: y² ≡ x} and binary-search B; Horner for degree d: O(dn) → 2^{O(dn/√log n)} = p^{o(1)} | nothing found | 8 | **go** (reuses #1's `MulNet`) |
| 3 | **Exact Σ_{m≤x} d(m), Σ σ(m), Gauss circle, lattice points under O(1) polynomial inequalities** | x^{1/3} (Sladkey 2012 and classical); x^{9/28} expected (Li, arXiv 2609.29949, Sept 2026, randomised) [known] | computational number theory | ab ≤ x: one × + one <: U = O(n) → x^{o(1)} deterministic | nothing found | 8 | **go** (cheap corollary of #1) |
| 4 | **Class number h(D)** of an imaginary quadratic field, deterministic unconditional | |D|^{1/2}-type unconditional; |D|^{1/4..1/5} under GRH / Shanks [heuristic: from `factoring-engine.md`, not re-checked] | number theory | #reduced forms (a,b,c): b²−4ac = D, |b| ≤ a ≤ c: 2 ×, comparators → |D|^{o(1)} | nothing found | 6 | go, after #1; the TM statement is cheap, the Mathlib class-group link is not |
| 5 | **Deterministic prime finding / π(x) exactly** (Polymath4) | π(x) in x^{1/2+ε} (Lagarias–Odlyzko 1987), x^{2/3} elementary (Deléglise–Rivat); a prime in [x,2x] in x^{1/2+o(1)} (Tao–Croot–Helfgott 2012) [known] | the Polymath4 problem | **blocked**: primality has no known certificate with O(n) total arithmetic (Pratt/AKS/ECPP use n multiplications → U = Θ(n²)); "N composite" is ∃(a,b) but counting pairs overcounts by d(N), and every de-duplication (lpf, largest divisor ≤ √N, Legendre φ) is a ∀ → Meissel–Lehmer; one big node = brute force (§2.7) | being investigated by another agent | 1 | rank only; blocked unless a new O(1)-multiplication primality certificate appears |
| 6 | **Discrete log in (Z/p)^* deterministic; order finding** | p^{1/2} deterministic (BSGS/Pollard); L(1/3) heuristic | crypto | g^x: n modular × → U = Θ(n²) → 2^{O(n²/√log n)} useless; order of a via factoring p−1 (#1) is fine | AK: ECDL 2^{O(b/(log b)^{1/4})} randomised, conditional on D.1 | 1 | blocked (direct); order-finding is a corollary of #1 |
| 7 | **Subset Sum / Partition / Equal Subset Sum, b-bit weights** | 2^{n/2} time (Horowitz–Sahni 1974), 2^{n/4} space (Schroeppel–Shamir 1981), space 2^{0.246n} (Nederlof–Węgrzycki 2021); polynomial shave only (Chen–Jin–Randolph–Servedio 2023) [known] | the central "meet-in-the-middle" barrier; crypto (knapsack) | **blocked**, §2.5: g clusters sharing partial sums give U ≈ 4g(b+log n), P ≈ 3b, exponent ≈ (4e_K + 6/K)·g·b with g = 3K⁸, so beating 2^{n/2} needs b < n/(36K⁷) ≤ n/2^{131}, where the O(n2^b) DP is already far better. OpenAI's model: s ≥ n + n^{0.1}b. CRT/mod-p variants need log(modulus) ≥ b per cluster | Randolph–Węgrzycki Nov 2025 (subset balancing, not Subset Sum); Salas 2025 arXiv claims unverified | 0 | **blocked**, robustly; a clean negative for the barrier paper |
| 8 | **Bin Packing / P‖C_max with k bins, exponential sizes** | 2^n (BHK 2009); 2^{(1−σ_k)n} randomised for fixed k (Nederlof–Pawlewicz–Swennenhuis–Węgrzycki SODA'21/SICOMP'23); ESA 2026: (2−ε)^n under ARC [known] | scheduling | same as #7 (k partial sums per cluster): blocked for b = Θ(n); poly sizes are in P by DP | ESA 2026 (Dhar et al.) | 0 | blocked |
| 9 | **Scheduling with precedence / permutation problems** (1|prec|ΣwC, bandwidth, treewidth, GI) | 2^n DPs; Cygan et al. "slightly superexponential"; GI quasi-poly | scheduling | witness is an ordering: n log n bits → blocked by T1(i) | — | 0 | blocked |
| 10 | **Held–Karp dense TSP / dense HC**, n vertices, Θ(n²) edges | 2^n n² (Bellman, Held–Karp 1962); 2^n n²/2^{Ω(√log n)} (Stoian 2024); undirected decision 1.657^n randomised (Björklund 2010); counting 2^{n−Ω(√n)} (Li, ICALP 2026) [known] | the headline bound of exact algorithms | **blocked** (T3): any vertex-local HC network on a dense graph has U = Θ(m) = Θ(n²); permutation witness; `permanent/barrier.md` Thm 6.1/6.2, `tutte-plane.md` Thm B. Exception: dense graphs that are rank-r up to a sparse edit set (`dense-structured.md`, 2^{o(n)} when edits have average degree 2^{o(√log n)}) | Stoian 2024; Li 2026 | 0 (general) / 7 (structured) | blocked in general; structured case is written up, publishable |
| 11 | **Directed HC below 2^n in general digraphs** | 2^n (1962); 2^{n−Ω(√n)} counting (Li 2026); bipartite digraphs 1.888^n (BKK 2017); parity 1.619^n (Björklund–Husfeldt 2013) [known] | the undirected/directed gap | dense ⇒ blocked exactly as #10; sparse digraphs: **done** (`theoremDHC`, 2^{O((m+n)/√log n)}); average degree d̄: 2^{O(n log d̄/√log n)} by the rank encoding (undirected machine-checked; directed by splitting) | — | 0 / done | blocked in general |
| 12 | **Permanent / #PM / hafnian below Ryser** | 2^n n (Ryser 1963); 2^{n−Ω(√n)} (Li 2026); **(2−10^{-40})^n over any commutative ring (Curticapean, arXiv 2611.03636, 2 Nov 2026, Binet–Minc + DP; independent of the engines)** [known] | Knuth's question; #P | blocked: Θ(n log n) shared bits in every row-local network (`barrier.md` Thm 6.1, Lean `Barriers/`), rate cap | Li 2026 | 0 | blocked; sparse/bounded degree is lab-local; low-rank + sparse edits done (`dense-structured.md` T3) |
| 13 | **Chromatic number below 2^n** | 2^n (Björklund–Husfeldt–Koivisto 2006/09); fixed k: (2−ε_k)^n randomised (Zamir 2026, arXiv 2607.25973 per lacker.io, ID unverified; Pratt 2026, arXiv 2607.27159, fetched), ε_k → 0; conditional 1.99982^n under Strassen's asymptotic rank conjecture (BCHKP SODA'25) [known] | colouring | fixed k: [A] Cor. 7 already gives deterministic 2^{δn} at any density (stronger than Zamir/Pratt in that regime). Growing k: n⌈log k⌉ variables, width 2⌈log k⌉ clauses → [A]'s explicit bound 2^{O(log³k · n loglog n/√log n)}: 2^{o(n)} iff log k = o((log n)^{1/6}/(loglog n)^{1/3}) (§2.6) [heuristic]. Beyond that: network encodings have P = Θ(n log k) on dense graphs (matching crossing patterns have rank (k−1)^s) → blocked | Zamir, Pratt (July 2026) | 6 (small χ) / 0 (general) | χ(G) exactly in 2^{o(n)} when χ ≤ 2^{(log n)^{1/6−ε}}: a remark, not a headline; general χ stays at 2^n |
| 14 | **Set Cover / Set Partition by universe size n** | 2^n (BHK; Fomin et al. 2004); Set Cover Conjecture (CDLMNOPSW 2012/16) [known] | the SeCoCo hypothesis | witness: set selection (m bits, m up to n^k) or element→set (n log m bits): blocked for m ≫ n. **m = O(n) sets: 2^{δn}** by the linear-density width reduction (F2, `quantum-note` cor:density) [heuristic, direct]. Parity: CDLMNOPSW's abstract gives only "⊕Set Cover fast ⇒ SETH fails"; whether Thm 1.3 is an iff (then ⊕k-Set Cover ∈ 2^{εn} is free) must be read off the paper | lacker.io mentions a 2026 ARC-conditional 1.8899^n (unverified) | 2 | blocked in the conjecture's regime; linear-m regime is a cheap corollary |
| 15 | **Max-Cut / Max-2-SAT exact, dense** | 2^{ωn/3} ≈ 1.73^n (Williams 2005); the 2024 combinatorial 2^{7n/9} claim (arXiv 2403.01085) is **withdrawn** [known] | the "split-and-list" barrier | blocked (A27): Θ(n²) edge indicators; cluster-pair interaction w^{x_Aᵀ E x_B} has rank 2^{rank E} (a crossing matching gives 2^s) → P = Θ(n). Sparse, poly weights: done (B15, Bhattacharjee) | Bhattacharjee (sparse) | 0 | blocked |
| 16 | **Steiner Tree / FVS / CVC / CDS / Max-Leaf / T(x,1)** on sparse graphs | 1.36^n Steiner (FGK 2008), 1.7548^n FVS (FGPR 2008), 1.8619^n CDS; Brand–Dell–Roth's #ETH line y = 1 | exact algorithms staples | **done on paper** (`exact-extensions.md` rows 4a–4f, `tutte-plane.md` P2), conditional on (H_A); not Lean-verified | — | 7 | Lean-verify (closes the Brand–Dell–Roth line formally) |
| 17 | **Counting Eulerian circuits**, bounded-degree undirected graphs | #P-complete (Brightwell–Winkler 2005; 4-regular: Ge–Štefankovič; planar: Creed); no sub-brute-force exact algorithm found in the literature [known, search only]; brute force Π(d_v−1)!! | enumeration classic | **new**, §2.9 [proved here, checked numerically]: #EC = #{transition systems whose transition 2-factor on E(G) is one cycle} (Kotzig); the connectivity indicator is our HC determinant on the transition graph, whose vertices are G-edges → U = O(m_×) bits, 2^{O(m/√log m)} under (H_A) | nothing found | 9 | **go** (cheap positive) |
| 18 | **Directed Steiner tree / max-leaf out-branching / arborescence problems**, sparse digraphs | Dreyfus–Wagner 3^k; 2^n-type in n | directed graphs | directed matrix-tree: Σ_{S⊇T} Σ_{arborescences} z^w, 3 states per arc (`exact-extensions.md` row 1 machinery) → 2^{δn} under (H_A) [heuristic, direct] | — | 8 | go (bundle with #16) |
| 19 | **Directed FVS / feedback arc set / max induced DAG**, sparse digraphs | (2−ε)^n (Razgon 1.9977^n) | directed graphs | **blocked for now**: "S induces a DAG" has no local certificate (topological order = n log n bits); Σ_{|S|=s} det(I − tA_S) is a local Grassmann sum but equals #{acyclic S} + Σ_{cyclic}(p_S(t) − 1) and separating needs degree-(q−1) powers of the determinant → U = Θ(nm) (§2.8) [proved here] | — | 2 | blocked unless a new acyclicity indicator appears |
| 20 | **Circuit lower bounds** | E^NP ⊄ SIZE(εn√log n) i.o. [repo, Lean, row C]; explicit functions 3.1n (Li–Yang 2022) | complexity | beyond n√log n: Circuit-SAT of size n·polylog has Tseitin size n·polylog → no 2^{n}/n^{ω(1)} algorithm from either engine (`circuit-lower-bounds.md` §3) | — | done / 0 | done; the rest blocked |
| 21 | **CNF-SETH frontier** (m = poly(n) clauses of unbounded width) | survives; our frontier m ≤ n·2^{o((log n)^{1/4}/√loglog n)} (F2) | fine-grained | the m-route 2^{km/√log m} is useless at m = n²; needs a rate improvement that is capped | — | 1 | blocked |
| 22 | **Problems in P** (3SUM, APSP, edit distance, OV, k-Clique, ω) | — | fine-grained | the engine saves 1/√log in the exponent of exponential-time problems only; `engine2-probabilistic.md` §6: pairwise-check witnesses cost n^{Ω(k)} | — | 0 | out of scope |
| 23 | **Derandomisation / PIT** | — | — | nothing: the engine is a deterministic counter for local constraints; no PIT instance is local | — | 0 | out of scope |
| 24 | **Sparse LPN / noisy k-XOR with O(n) samples; LDPC minimum distance and ML decoding; sparse 0/1 ILP with O(1)-bit coefficients** | 2^{Θ(n)} folklore (BKW needs 2^{n/log n} samples) | crypto (Alekhnovich-type assumptions), coding | all linear-size local CNFs with a counter → 2^{δn} from the Main Theorem alone (F3) [heuristic, direct] | Bhattacharjee claims LDPC min distance / ML decoding (intro, unverified) | 9 | cheap corollaries; low novelty, galactic |
| 25 | **TSP with exponential weights on sparse graphs** | Held–Karp 2^n handles any weights | TSP | our poly-weight machine needs B = poly; weights 2^{Θ(n)} make the adder transcript Θ(nb) bits (same wall as #7) | — | 1 | open for us; likely blocked |

---------------------------------------------------------------------------------------------------

## 2. Assessments (details behind the table)

### 2.1 Factoring and the "O(n) unknown bits + O(1) cheap operations" family (#1–#4)

Everything here is in `factoring-engine.md`; this note only re-weighs it. The decisive fact is that the witness is
tiny (an n-bit divisor) and the whole Θ(n log n)-bit FFT transcript hides inside big nodes with linear cut
(AK Thm 3: < 1100(d+1) edges, degree < 136(d+1)^{3/4}). On Anthropic's `Net g` the packing g ≤ 3n^{1/5},
P = O(n^{4/5}), K = K_ℓ ≤ n^{1/40} gives U, gP = O(n) and 2^{O(n/√log n)}, which is RR's own `SqrtLogLogConjecture`
proved unconditionally on a verified engine. Rate honesty: via Tseitin/#3-SAT the same instance costs
2^{O(n√log n)}, worse than N^{1/5}; the large-node model is essential.

The family splits sharply [heuristic, but the reason is structural]:
* **∃-type counts** (a divisor exists; a representation ab ≤ x exists; a reduced form exists; y² ≡ a has a root) are
  lattice-point counts with O(1) multiplications → x^{o(1)}. Items #1–#4 and `factoring-engine.md` #6 (small roots
  of f(x,y) ≡ 0 mod N in a box of any size).
* **∀-type counts** (N prime; N squarefree; N y-smooth; μ(N); Mertens M(x); π(x)) need "no divisor in a range",
  and every known de-duplication of the ∃-count reintroduces a universal quantifier or an exponentiation. These
  stay at their classical bounds (§2.7).

Impact: factoring in N^{o(1)} deterministic, machine-checked, is the single result on this list that a general
audience would recognise; the rest of the family (least non-residue below Burgess, roots mod p below Shoup,
divisor sums below x^{1/3}, h(D)) are clean "first unconditional deterministic x^{o(1)}" statements for
computational number theorists. All are galactic.

### 2.2 Held–Karp, Ryser, directed HC, Max-Cut: the dense wall (#10–#12, #15)

Nothing new to add to T3 except to state the per-problem reason in one line each.
* Dense HC/TSP: U ≥ (2−o(1))n is all a single cut proves in Model V (`barrier.md` Thm 6.2, Prop. 3.5), but U = Θ(m)
  for every network we can write, and the rate cap makes even U = Θ(n log n) fatal. Stoian's 2^{Ω(√log n)} shave and
  Li's 2^{n−Ω(√n)} are the real frontier; neither is reachable by a local-network method.
* Directed HC on general digraphs: identical; the sparse case is machine-checked (`theoremDHC`). The one genuinely
  new dense statement we have is the structured one (`dense-structured.md` T2: rank-r plus sparse edits, including
  tournaments that are blow-ups of small tournaments).
* Permanent: `permanent/*.md`; the Lean-checked row-cut rank C(n,k) and Model-R bound U ≥ n log(n/s).
* Max-Cut / Max-2-SAT dense: the cut value is a Θ(n²)-term sum; the pair interaction [w^{x_Aᵀ E_AB x_B}] has rank
  2^{rank E_AB} (a crossing perfect matching gives Π_i w^{x_i y_i}, rank 2^s), so P = Θ(n) [proved here, one line].
  The LVWW hyperclique hypothesis survives for the same reason (A26). Williams' 2^{ωn/3} stands (the 2024
  combinatorial 2^{7n/9} preprint is withdrawn).

### 2.3 Set Cover (#14)

Witness options: (a) selection vector over the m sets, m bits — the engine gives 2^{o(m)}, useful only when
m = O(n); (b) element → covering set, n⌈log m⌉ bits — at least n log n for m ≥ n, blocked by T1(i). So in the Set
Cover Conjecture's regime (sets of size ≤ k, m up to n^k) nothing follows, consistent with A21. What does follow
[heuristic, direct from F2]: Set Cover, Set Partition, Exact Cover with **m ≤ cn sets** are CNFs with O(n)
variables and n clauses of unbounded width, hence 2^{δn} for every δ (count by size with a counter). For c < 1
brute force over sets already beats 2^n, so the new regime is c ≥ 1 with unbounded frequency. Modest. Parity: the
CDLMNOPSW abstract states only "⊕Set Cover in 2^{εn} ⇒ SETH fails"; our map row A7 records Thm 1.3 as an
equivalence. If it is an iff, ⊕k-Set Cover in 2^{εn} for every fixed k is a free corollary of the k-SAT refutation
and worth one paragraph; read the theorem before claiming it.

### 2.4 Chromatic number and k-colouring (#13)

Fixed k is already settled by [A] Cor. 7 (deterministic 2^{δn}, any density), which is stronger than the July 2026
(2−ε_k)^n results of Zamir and Pratt in that regime; the survey already records this (B13). For growing k the
binary encoding has n⌈log k⌉ variables and width 2⌈log k⌉; [A]'s explicit n-bound 2^{C k'² n loglog n/√log n}
with k' = 2⌈log k⌉ is 2^{o(n)} iff log³k · loglog n = o(√log n), i.e. **χ(G) is computable exactly in 2^{o(n)}
whenever χ(G) ≤ 2^{o((log n)^{1/6}/(loglog n)^{1/3})}** [heuristic; the width constraint k' ≤ c(log n)^{1/4}/√loglog n
of `sat-width.md` §5.1 is weaker]. For larger χ: network encodings on dense graphs need P = Θ(n log k) (a crossing
matching between clusters gives interaction rank (k−1)^s), and the BHK inclusion–exclusion over 2^n subsets is not
a network at all. So the 2^n bound for chromatic number is untouched; the conditional 1.99982^n (BCHKP) is a
different kind of mechanism (asymptotic tensor rank), which our M1 analysis says cannot change e_K either.

### 2.5 Subset Sum, Partition, Bin Packing, scheduling: the exact accounting (#7–#9) [proved here]

Take n items with b-bit weights, g clusters of s = n/g items, each cluster holding its items privately and
sharing only its partial sum (b + log s bits), the partial sums added along a binary tree of g leaves.
* Shared bits: U ≈ 2·(2g − 2)·(b + log n) ≈ 4g(b + log n). Node load: P ≈ 3(b + log n) (an adder sees two inputs
  and its output). Private settings s ≤ P hold once g ≥ n/(3b).
* Engine exponent (Lemma 8 (i), g = 3K⁸): e_K(U + gP/K) + 2gP/K ≈ (4e_K + 6/K)·g·b ≥ 18K⁷·b ≥ 2^{130}·b at K = 2^{18}.
  To beat 2^{n/2} one needs b < n/(36K⁷) ≤ n/2^{131}; the algorithm-independent floor U/(2√(log U + 2x₀)) alone
  needs b ≲ n√log n/(2·10⁴·K⁸). In that regime the O(n·2^b) dynamic programme costs 2^{n/2^{131}} and wins.
* Case (ii) of Lemma 8 (small g): routing the sum along a path of K nodes gives U ≈ 2Kb, P ≈ 2b, exponent
  ≈ 2e_K K b + 4b + …; the 4b term alone needs b < n/8 and e_K K ≥ 2^{17}. Dead.
* OpenAI's model: cluster degree s + b ≤ s_tot^{0.9} forces g ≥ n^{0.1}, so s_tot ≥ n + n^{0.1} b ≥ n^{1.1} at b = Θ(n);
  with b ≤ n^{0.9} the DP wins (`factoring-engine.md` §5 says the same).
* Modular tricks: counting solutions mod a small prime p costs only O(g log p) bits and is subexponential, but
  pinning the sum needs a modulus with log(modulus) ≥ b per cluster, which is the same U; counts for different
  primes cannot be combined into a count of exact solutions.
Conclusion: **beating 2^{n/2} at b = Θ(n) is impossible by any clustered-partial-sum network, in both engines**, and
for b small enough that the network becomes cheap the DP is cheaper still. The structural reason is that the
verifier of Subset Sum has a Θ(b)-bit communication bottleneck per party (the partial sum carries b bits of
entropy), so U ≥ (#parties)·b, while the engine needs ≥ 2^{146} parties. Bin Packing with k bins is the same with
k sums per cluster; permutation-type scheduling fails earlier (n log n witness).

### 2.6 Sparse families that remain (#16, #18, #24)

Steiner tree, FVS, CVC, CDS, max-leaf, forests/T(x,1), directed Steiner/arborescence problems: identities checked
numerically (`exact-extensions.md`), conditional on (H_A), not Lean-verified. The Brand–Dell–Roth y = 1 line is the
one with a named #ETH lower bound, so its formal verification is the most citable. The LPN/LDPC/ILP bundle is
immediate from the Main Theorem (F3) and partly claimed by Bhattacharjee; it is "value" only in the sense that
Alekhnovich-type sparse assumptions with O(n) samples are formally 2^{o(n)}-breakable.

### 2.7 Why prime counting is blocked (#5) [proved here, informal]

Let r(N) = #{(a,b): 2 ≤ a ≤ b, ab = N}. The engine computes A_j = Σ_{N≤x} r(N)^j for each fixed j (j coupled
multiplications, U = O(jn)), but π(x) = x − 1 − Σ_N [r(N) ≥ 1] needs [r ≥ 1], and r(N) ranges up to 2^{(1+o(1))n/log n}:
no bounded-degree polynomial in r works. De-duplicating by the least prime factor gives [a = lpf(N)] =
[a | N][a prime][lpf(N/a) ≥ a], a ∀-condition whose unrolling is Legendre's φ(x,a) recursion (Meissel–Lehmer,
x^{2/3}); by the largest divisor ≤ √N, a ∀ over an interval (inclusion–exclusion is exponential). A chain of
nested divisors N > a_1 > a_2 > … with a_{i+1} ≤ √a_i has only O(n) total bits (geometric), which is tempting, but
the chain counts the number of prime factors ≤ √N, not an indicator. Primality certificates (Pratt, AKS, ECPP) use
Θ(n) modular multiplications → U = Θ(n²) → p^{n/√log n}. A single node evaluating [N prime] has P = n, i.e. brute
force 2^n = x. So the Polymath4 problem is out of reach of the counting engines unless someone finds a
primality (or compositeness-with-multiplicity-one) certificate with O(n) total arithmetic transcript; that would be
a result in its own right.

### 2.8 Directed acyclicity (#19) [proved here, informal]

D[S] is acyclic iff A_S is nilpotent iff det(I − tA_S) ≡ 1. The sum f(t) = Σ_{|S|=s} det(I − tA_S) is a local
Grassmann sum (one membership bit per vertex, 3 monomials per arc) and the engine computes it; but
f(t) = #{acyclic S} + Σ_{cyclic S}(p_S(t) − 1) with p_S(0) = 1, and extracting [p_S ≡ 1] needs
1 − (p_S(t) − 1)^{q−1} over F_q with q > n (Schwartz–Zippel), i.e. q−1 coupled copies of the determinant,
U = Θ(nm). Powers det(·)^j for fixed j are local (j Grassmann copies) and give Σ_S p_S(t)^j, which does not
separate either. So DFVS/FAS keep their (2−ε)^n bounds for us; the undirected forest trick works because for a
forest |F| = n − c(F) turns connectivity into a lowest-degree coefficient, and no analogous extremal identity
exists for directed acyclicity of induced subgraphs that we know of.

### 2.9 Counting Eulerian circuits (#17) [proved here; numerically checked]

A transition system of an even connected multigraph G pairs the edge-ends at every vertex (one perfect matching of
the d_v ends per vertex; Π_v (d_v − 1)!! systems). It induces a 2-regular graph on the vertex set E(G) (each
G-edge is paired once at each endpoint); Eulerian circuits (closed trails up to rotation and reversal) are in
bijection with the transition systems whose transition graph is a single cycle (Kotzig's classical observation).
`euler_check.py` verifies #EC = #{connected transition systems} by brute force on K₃, K₅ (132) and 10 random even
multigraphs with n ≤ 6, m ≤ 9: ALL PASS. The connectivity indicator is exactly the one in our #HC network: for a
2-regular graph H on m vertices, [ε¹] det(L_H + εI) = m·τ(C_m) = m² when H is one cycle and 0 otherwise, so
m²·#EC = Σ_T [ε¹] det(L_{H(T)} + εI). Locality: the Grassmann generators ψ̄_e, ψ_e live on G-edges; a transition
{e,f} at v is an edge of H and contributes a factor local to v's blob; the only non-locality is that a crossing
G-edge's generators are touched from both endpoint blobs — a 4-state alphabet per crossing edge (which of
1, ψ̄_e, ψ_e, ψ̄_eψ_e has been consumed) plus the O(g³) sign bookkeeping of `exact-count-lowrank.md` §2. With
bounded degree, U = O(m_×) + O(g³), P = O(m/g), and (H_A) gives 2^{O(m/√log m)}, 2^{δn} for every δ.
Degree hubs are the failure mode ((d−1)!! transitions and Θ(d) crossing edges at one blob): bounded or
2^{o(√log n)}-ish degree only, as for #HC. Literature check: #EC is #P-complete (Brightwell–Winkler 2005), exact
counting is known only for bounded treewidth / series–parallel (Chebolu–Cryan–Martin) and via a 2025 trace
formula on structured classes; we found no general exact algorithm faster than enumeration. A 2^{o(n)} count for
bounded degree would be new, but it is a corollary-level result (same template as rows 0–4f).

---------------------------------------------------------------------------------------------------

## 3. Ranking (impact × feasibility for us)

| rank | target | impact | feas. | one-line reason |
|---|---|---|---|---|
| 1 | **Factoring in 2^{O(n/√log n)} Lean-verified on Anthropic's engine, plus sqrt / non-residue / roots mod p, divisor sums, h(D)** | 9 | 8 | the only linear-witness, O(1)-operation family not yet taken with a verified rate; plan F1–F6 exists |
| 2 | **Barrier paper: "what the refutations do not give"** (dense HC/TSP/permanent/Max-Cut, Tutte off H_q, Subset Sum accounting §2.5, chromatic number, Set Cover, prime counting §2.7, DFVS §2.8) | 7 | 8 | material and 39 Lean theorems exist; a well-argued wall is the most useful thing we can publish about the "decades-old" bounds |
| 3 | **Counting Eulerian circuits in bounded-degree graphs** (§2.9) | 4 | 9 | new, #P-complete classic, same machinery as #HC; one network file and one identity |
| 4 | **Lean-verify the sparse rows: Steiner, FVS, CVC/CDS, max-leaf, forests T(x,1), directed Steiner** | 5 | 7 | closes Brand–Dell–Roth's #ETH line formally; template `TSP.lean` |
| 5 | **Dense graphs of low rank up to sparse edits** (`dense-structured.md`) as a short paper | 4 | 8 | the one honest dense-regime positive result; unconditional n^{O(r)}2^{|V(S)|} by-product |
| 6 | **χ(G) exactly in 2^{o(n)} for χ ≤ 2^{(log n)^{1/6−ε}}; #k-colourings for growing k** (§2.4) | 4 | 9 | a remark on [A]'s explicit k-dependence; beats Zamir/Pratt in that regime, leaves 2^n untouched |
| 7 | **Linear-size set systems and sparse coding/crypto bundle** (Set Cover with O(n) sets, sparse LPN with O(n) samples, LDPC min distance, sparse 0/1 ILP) | 3 | 9 | immediate from F2/F3; partly claimed by Bhattacharjee; galactic |
| 8 | **Deterministic prime finding / π(x)** (Polymath4; other agent) | 10 | 1 | blocked: no O(1)-multiplication primality certificate; ∃-counts overcount, ∀-fixes are Meissel–Lehmer |
| 9 | **Subset Sum / Partition / Bin Packing below 2^{n/2} (resp. 2^n) at b = Θ(n)** | 9 | 0 | blocked by U ≥ (#parties)·b with ≥ 2^{146} parties; record the formula in #2 |
| 10 | **Held–Karp, Ryser, directed HC, dense Max-Cut, chromatic number in general** | 10 | 0 | the dense wall (T3); record in #2; the only live route is e_K = o(1/log K), which is capped in every model we can analyse and VP-vs-VNP-hard to rule out in general |

Not ranked (out of scope or done): problems in P, ω, PIT (nothing); circuit lower bound E^NP ⊄ SIZE(εn√log n)
(done, Lean; nothing beyond); quantum amplitudes (done); CNF-SETH frontier (blocked).

---------------------------------------------------------------------------------------------------

## 4. Attack plans for the top three

### 4.1 Factoring family (rank 1)

* **Key lemma.** `mulNet_value`: for n-bit N and a prefix word u, the Schönhage–Strassen BTN (one level over
  Z/(2^J+1), J ≈ 16√n, four-step DFT with power-of-two twiddles, canonical residues, carry chain) has value
  #{a : a | N, word_n(a) ⊒ u}, i.e. it is **parsimonious**: every auxiliary bit is a function of (a, N/a). Then the
  packing lemma: its ≤ 2200(n+1) edge-ends, each vertex of degree ≤ 136 n^{3/4}, pack first-fit into g = 3K⁸ ≤ 3n^{1/5}
  bins with P ≤ 4400(n+1)/g + 136n^{3/4}, giving a `Net g` with `Is P B`, U ≤ 2s = O(n), gP = O(n), and
  `groupingExplicit` + `CountedRoute.onTheCountedRecursion` at K = K_ℓ ≤ n^{1/40} give 2^{Cn/√log n}.
* **First experiment.** (a) Python, exact integers: build the SS network for n ∈ {16, 32, 64}, check parsimony by
  enumerating all (a, b) with ab = N and confirming that exactly one assignment of the transcript variables
  satisfies every vertex predicate (and none when ab ≠ N), and print the edge/degree table against AK's constants.
  (b) Lean scratch (`lean/EthFollowup/Scratch/MulNet/`): state the negacyclic-convolution identity
  Σ_i x_i y_{k−i} − Σ x_i y_{L+k−i} as the coefficient of X^k in xy mod X^L+1 over ZMod (2^J+1) and prove it for
  L = 4, J = 8 by `decide`/`norm_num`, then the general statement with `Finset.sum` manipulations; this is the
  F1 risk item.
* **Likely failure mode.** The PolyT certificates for the stage-wise DFT procedures and the polynomial state bound
  S (the `Procs.Give` obligations, `anthropic-api.md` §4.1): a dense table of 2^{P} integers in a node's state
  destroys the bound. The procedure must be a poly(n)-state loop over the node's private bits. Secondary risk:
  the pickOf exponent 1/40 (node load P ≥ n^{3/4} forces K ≤ n^{1/32}); a three-stage DFT (degree n^{2/3}) is the
  fallback. Everything else (prefix search = minFac, the n-round outer machine, the TM2 bridge) follows
  `Theorem2.lean`/`UPackage.lean` templates.

### 4.2 Barrier paper (rank 2)

* **Key lemma.** Two theorems carry the paper. (i) The Tutte cut-rank theorem (`tutte-plane.md` Thm B): off
  𝓗 ∪ 𝓛 every vertex-local network needs Σ log₂ Bell(b_G) ≥ (1−o(1)) n log n bits, via the rank of
  [q^{|P∨Q|}] on partition lattices (Lindström); with Lemma 2.1 the engine's guarantee is ≥ 2^{(1/2−o(1))n√log n}.
  (ii) The rate caps: ρ ≥ 1/2 for product and two-rectangle/3×2 correlated decompositions (Lean), 3/8 for full
  levels, α′ ≤ 1 for every grouping family (covering bound), plus the VP≠VNP meta-barrier. New sections from this
  note: the Subset Sum accounting (§2.5), the Max-Cut interaction-rank line (§2.2), prime counting (§2.7), DFVS (§2.8).
* **First experiment.** The smallest open rank instance: the full 3×3 grid level (Q = 9; S ≥ N⁸ proved, N⁹ wanted;
  `engine2-decorrelated.md` §7.9). Set it up as a GF(2) SAT / exact-rank search at λ = 1 for a decomposition with
  rank sum < N⁹ = 512 (the 2-party lossy method is capped at 8 there, so a certificate needs an m-party functional or a
  non-flattening contraction). In parallel, Lean-formalise the Tutte cut-rank theorem's rank step (the partition-lattice
  rank of [q^{|P∨Q|}] for small b by `decide`, then general).
* **Likely failure mode.** The two loopholes recorded in `NEXT-STEPS.md`: sums over many different clusterings (the rank
  argument loses log(#networks) per cut), and skeletons that depend on private edges. A referee will also ask whether
  "vertex-local" is the right model: in Anthropic's general Definition 2 a node may be any poly-time function of the
  whole input (barrier.md Prop. 4.1), so the honest theorem is about the information the engine can *route*, not about
  all algorithms; the paper must say so in the first paragraph.

### 4.3 Counting Eulerian circuits (rank 3)

* **Key lemma.** m²·#EC(G) = Σ_{transition systems T} [ε¹] det(L_{H(T)} + εI), where H(T) is the transition
  2-factor on E(G) (§2.9), realised as an even Grassmann product with one pair of generators per G-edge, a transition
  factor at each vertex (local), and the universal "ε-mass" term per G-edge; the sign rule is the one of
  `exact-count-lowrank.md` §2 (even pieces, O(g³) parity bits). Equivalently: #EC(G) = #HC-type count of the
  4-regular-like "transition graph", with the 2-factor chosen by local matchings at the vertices of G instead of by
  edge membership.
* **First experiment.** Add a `euler` problem family to `research/scripts/ext_problems.py`: local states = the
  matching chosen at each vertex, Grassmann factors on the transition edges, and check brute force = determinant
  identity = blob network on random partitions with K = 2, 3, 4 (n ≤ 6, m ≤ 9, the instances of `euler_check.py`).
  Then count the per-crossing-edge labels (expect 4 + sign bookkeeping, i.e. 2 bits) and the per-blob load.
* **Likely failure mode.** Vertex degree: a vertex of degree d has (d−1)!! transitions and its blob touches Θ(d)
  crossing edges, so U/m and P blow up with Δ; the result is for bounded (or slowly growing) degree only. Also check
  the multigraph case (parallel edges are distinct vertices of H, fine) and loops (an end-pairing at the same vertex;
  exclude or handle). Nothing here needs a new Anthropic-side fact; the Lean route is a copy of `HCNetwork.lean`
  with the 2-factor supplied by local matchings.

---------------------------------------------------------------------------------------------------

## 5. Sources consulted for this note (4 Nov 2026)

Primary (abstract pages fetched): arXiv 2405.03018 (Stoian, TSP 2^n n²/2^{Ω(√log n)}); arXiv 2309.15422 v2 (Li, ICALP
2026: hafnian and directed #HC in 2^{n−Ω(√n)}); arXiv 2607.27159 (Pratt, k-colouring (2−ε_k)^n, cites Zamir 2026 as
concurrent); arXiv 2404.04987 (BCHKP, chromatic number 1.99982^n under the asymptotic rank conjecture); arXiv 1112.2275
(CDLMNOPSW abstract: Set Cover parity direction); arXiv 2007.08204 (NPSW, bin packing 2^{(1−σ_m)n} randomised); arXiv
2403.01085 (withdrawn Max-Cut claim). Secondary: lacker.io/complexity problem pages (chromatic number, directed
Hamiltonicity, subset sum; all three list the problems as open as of 2026, with Chen–Jin–Randolph–Servedio 2023 as the
last Subset Sum entry); Dagstuhl ESA 2026 (Dhar et al., scheduling, ARC-conditional bin packing); arXiv 2511.10823
(Randolph–Węgrzycki, subset balancing); arXiv 2609.29949 (Li, divisor summatory function x^{9/28} expected). Hexagon's
listing pages require an ORCID sign-in; the three Hexagon papers of `hexagon-related.md` and the factoring preprints
of `factoring-engine.md` were not re-fetched. Web searches on 4 Nov 2026 found no further October–November 2026 follow-up
paper on factoring, Hamiltonicity, set cover, permanent, subset sum or Eulerian circuits beyond those already recorded
in this repository; the Hexagon JSON API is behind a login, so this negative is weak.
