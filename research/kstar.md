# The turn-labelling invariant k*: growth on bounded-degree graphs

Status (2026-11-04). This continues `linear-encoding-2.md` (§4.2–4.4, Theorem G, Open (N)).

**Main result: (N) has a negative answer.** There are bounded-degree graphs with
`k* ≥ (log₂ m)/32 − O(1)`. These are the "crossing grids" `H_t` (max degree 3, `2t²` vertices), every
bounded-degree expander, and a.a.s. every random cubic graph. A labelling with `k = o(√log m)` is impossible
for them, and the GF(2)^k gap gadget of Theorem G can never be smaller than `Θ(m log m)` on expanders.
The old lower bound was `Ω(log log log n)`, from hypergraph Ramsey. The new one is `Ω(log n)` and uses
only the Kővári–Sós–Turán theorem. The best upper bound is still linear, `O(m)`.

Lean (scratch, Mathlib, `lean/EthFollowup/Scratch/Kstar/`): see §6.

Scripts (python-sat is used only as a search tool; every SAT answer is re-verified on all cycles):
* `research/scripts/kstar_grid.py`: the graph `H_{p,q}`, and a search for balanced cycles.
* `research/scripts/kstar_lower.py`: checks the decomposition lemma, the lifting and the planted-zero
  property. Output is in `kstar_lower.out`, **ALL PASS**.
* `research/scripts/kstar_lean_data.py` (+`.out`): produces the tables and certificates used by the Lean instances.
* `research/scripts/kstar_sat.py`: computes `k*` by CEGAR SAT for grids, random cubic graphs and `K_t`.

## 1. Definitions and reformulation

Let `G` be a simple graph with root `r`, and put `G' = G − r`.
* A **turn** is a triple `(v; u, w)` with `u ≠ w` both neighbours of `v`.
* A directed simple cycle `C = (v_0 … v_{L−1})` with `L ≥ 3` uses the turns `(v_i; v_{i−1}, v_{i+1})`.
* For `F : turns → GF(2)^k`, put `F(C) = ⊕_i F(v_i; v_{i−1}, v_{i+1})`. Call `F` **good** if
  `F(C) ≠ 0` for every directed simple cycle of `G'`.
* `k*(G) = k*_r(G)` is the least such `k`.

Let `x_C ∈ GF(2)^{turns}` be the turn vector of `C`, and let `X = {x_C}` and `W = span X`. Then `F(C) = L(x_C)`
for the linear map `L` that `F` defines. Every linear map `W → GF(2)^k` extends to all turns, so:

**Proposition 1 (critical problem).** `k*(G)` is the *critical exponent* (Crapo–Rota) of the binary
matroid `M_T(G)` represented by the vector set `X`. This is the least `k` such that some `k` hyperplanes
of `W` have intersection disjoint from `X`. By the critical theorem, the number of good `L : W → GF(2)^k`
is `p(M_T; 2^k)`, where `p` is the characteristic polynomial. For comparison, the graphic matroid has
critical exponent `⌈log₂ χ⌉`. [Crapo–Rota 1970; see Kung's survey, "Critical problems", in *Matroid
Theory*, Contemp. Math. 197 (1996).]

The obvious lower-bound tools for critical exponents fail here:
* **Projective-geometry bound.** A subspace `U ≤ W` with `U∖0 ⊆ X` would give `k* ≥ dim U`. But no three
  cycles satisfy `x_1 + x_2 = x_3`. A cycle uses at most one turn at each vertex. If `C_1` and `C_2` share a vertex,
  then `x_1 + x_2` is a cycle vector only if they use the same turn there. That turn determines both
  neighbours, and the agreement propagates around the cycle, so `C_1 = C_2`. Otherwise
  `x_1 + x_2 = C_1 ⊔ C_2`, which is not a cycle. So `dim U ≤ 1`.
* **Fourier bound.** For any distribution `μ` on cycles and a good `F`, we have
  `Σ_{a≠0} μ̂(a·F) = −1`, so `k* ≥ log₂(1 + 1/ε*)`, where `ε*` is the least achievable max-bias. Single-turn
  tests have bias `≥ 1 − 2/(d(d−1))`, so this gives only `O(1)`.

This explains why Ramsey arguments are needed below.

## 2. Upper bounds (all elementary)

Let `n' = |V(G')|` and `m' = |E(G')|`.

* **U1 (non-tree edges).** `k* ≤ m' − n' + c(G')`. Label each turn `(v; u, w)` with the basis vector of
  the edge `vw` if `vw ∉ T`, for a spanning forest `T`, and with `0` otherwise. A cycle sums to the indicator
  of its non-tree edges, which is nonempty.
* **U2 (peaks).** `k* ≤ n' − 1`. Order `V(G')` and label `(v; u, w)` by `e_v` when `v > u, w` (a peak).
  Every cycle has a peak (its maximum), and the minimum vertex is never a peak, so `n' − 1` coordinates suffice.
* **U3 (deletion).** `k*(G) ≤ k*(G−v) + 1` and `k*(G) ≤ k*(G−e) + 1`. The extra bit indicates the turns at `v`
  (or the turns entering along `e`). Hence `k* ≤ 1 + (apex number)` and `k* ≤ 1 + (skewness)`.
* **U4 (sums).** `k*` of a 1-sum is the max over the blocks. For a 2-sum along `{a,b}`:
  `k* ≤ max(k*(G_1+ab), k*(G_2+ab)) + 1`. Pull `F_1` and `F_2` back into the same coordinates, and add one bit
  that marks the turns at `a` which go from `G_1` to `G_2`. A crossing cycle passes `a` once, so this bit is `1`.
* **U5 (topology, from part 2).** `k* ≤ g + 2`, and `k* ≤ 1 + rank/2`. Note that the polarisation of the crossing
  form on the cycle space is, mod 2, the intersection form of the surface defined by the drawing's rotation
  system. (By Jordan, the crossing parity of two cycles is a sum of local terms at shared vertices.) So
  rank/2 is at least the genus, and the two bounds are essentially the same. Every topological labelling
  gives `≈ g = Θ(m)` on expanders.

None of these is sublinear on expanders. No construction with `k = o(m)` for all bounded-degree graphs is
known. The truth is between `Θ(log m)` (§3) and `O(m)`.

**Minor universality (why expanders are the worst case).**
* Let `K(N) = max{k*(H) : |V(H)| + |E(H)| ≤ N}`.
* Bounded-degree `α`-expanders on `n` vertices contain every graph with `≤ n/(c log n)·(α/d)^c` vertices and
  edges as a minor (Chuzhoy–Nimavat, arXiv:1901.09349; Krivelevich–Nenadov independently, with
  `Ω(nα²/(d² log n))`).
* `k*` is minor-monotone.
* Hence `K(c'n/log n) ≤ k*(expander) ≤ K(O(n))`. On expanders, `k*` is the worst case over *all* graphs of
  size `≈ n/log n`.
* The bounded-degree restriction costs nothing either. Every graph is a minor of a max-degree-3 graph of
  linear size: split each vertex into a path.

## 3. Theorem L: k* = Ω(log m) on bounded-degree graphs

**The crossing grid `H_{p,q}`.**
* Vertices `r_{a,b}` and `c_{a,b}`, for `a < p`, `b < q`.
* Row paths `r_{a,0} − … − r_{a,q−1}` and column paths `c_{0,b} − … − c_{p−1,b}`.
* Rungs `r_{a,b} − c_{a,b}`.
* Max degree 3, `2pq` vertices, `3pq − p − q` edges. Contracting rows and columns gives a
  `K_{p,q}` minor, so `H` is nonplanar for `p, q ≥ 3`.
* Write `H_t = H_{t,t}`, with root a new vertex attached to `r_{0,0}` (degree stays ≤ 3).

A directed cycle of `H` is a closed rectilinear curve that alternates between row segments and column
segments through rungs. It may pass straight through a crossing point `(a,b)` along both the row and the
column, since `r_{a,b}` and `c_{a,b}` are different vertices. Each rung visit is a **corner** of
**type** `κ = (order, h, v)`:
* the order is `HV` (row to column) or `VH` (column to row);
* `h = ±1` is the horizontal direction of motion;
* `v = ±1` is the vertical direction.

**Lemma L1 (decomposition).** For every `F : turns(H) → GF(2)^k` there are functions
`φ_κ : [p]×[q] → GF(2)^k` such that `F(C) = ⊕_{corners (a,b,κ) of C} φ_κ(a,b)` for every directed cycle `C`.

*Proof.* Let `s^±_a(x)` be the label of the straight turn at `r_{a,x}` in direction `±`, and put
`P^+_a(y) = ⊕_{x≤y} s^+_a(x)` and `P^−_a(y) = ⊕_{x≥y} s^−_a(x)`.
* A rightward row segment between corners at columns `b_0 < b` contributes `P^+_a(b−1) ⊕ P^+_a(b_0)`.
  Assign the first term to its end corner and the second to its start corner. Leftward segments are
  handled symmetrically, and so are columns, with `Q^±_b`.
* Each corner also contributes its two rung turns: at `r_{a,b}` and at `c_{a,b}`, determined by `(a,b,κ)`.
* Collecting these terms, `φ_κ(a,b)` is the sum of the two rung-turn labels and of the row and column prefix terms of the
  corner, which are determined by `κ`. ∎

`kstar_lower.py` (a) checks this against all directed cycles of `H_{3,4}`, `H_{4,4}` and `H_{4,5}` (108,
760 and 4984 cycles), with 3 random `F` each. **PASS.**

**Lemma L2 (balanced cycle, by computer search, `kstar_grid.py`).** `H_{4,4}` has a directed 24-cycle
`B` that uses only the four corner types `VH+−, HV++, VH−+, HV−−`, each exactly twice. The corner word is
`(VH+− HV++ VH−+ HV−−)²`. It is a doubled spiral with one self-crossing. As a vertex list in `(row, column)` coordinates:

  `r00 r01 r02 r03 c03 c13 c23 c33 r33 r32 r31 c31 c21 c11 r11 r12 c12 c22 r22 r21 r20 c20 c10 c00`.

No such cycle exists in `H_{p,q}` with `p, q ≤ 3`, or in `H_{3,4}`. `B` is checked in `kstar_lower.py` (b).

**Lemma L3 (lifting).** Take rows `a_1 < … < a_4` and columns `b_1 < … < b_4` of `H_t`. Replace the abstract
grid points of `B` by `(a_i, b_j)`, and fill in segments through the intermediate vertices. The result is a simple directed cycle of `H_t` with the
same corners and corner types. The reason is that intervals keep their order and disjointness, and rows and columns meet only at distinct
vertex pairs. `kstar_lower.py` (b) checks this on 200 random lifts into `H_9`. **PASS.**

**Theorem L.** Let `t ≥ 48·2^{16k} + 2`. Then `H_t` has no good labelling with `k` bits. Hence
`k*(H_t) ≥ (log₂(t−2) − log₂ 48)/16`, which is `≥ (log₂ m)/32 − 1` for `m = |E(H_t)|`.

*Proof.* Let `F` be a `k`-bit labelling.
1. Colour each interior cell `(a,b) ∈ [1,t−2]²` by the four vectors `φ_κ(a,b)` for the four types of `B`. That is
   `c = 2^{4k}` colours.
2. Some colour class has `≥ t'²/c` cells, where `t' = t − 2`. View it as a bipartite graph between rows and
   columns.
3. By Kővári–Sós–Turán, `z(t'; 4,4) ≤ 3^{1/4} t'^{7/4} + 3t'`. This is less than `t'²/c` once `t' ≥ 48c⁴`.
4. So there is a monochromatic `4×4` combinatorial subgrid `A×B'`.
5. Lift `B` there (L3). By L1, `F(C)` is the sum of `φ_κ` over its 8 corners. All corner cells have the same
   colour and every type occurs twice, so `F(C) = 0`. ∎

`kstar_lower.py` (c) plants a cell-homogeneous `F` (50 trials) and confirms that `F(lift B) = 0`. **PASS.**

**Corollaries.**
1. **Expanders.** Bounded-degree `α`-expanders contain `H_t` as a minor with `t² = Ω_{α,d}(n/log n)`
   (§2). So `k* ≥ (log₂ n)/32 − O(log log n)`. Random cubic graphs are expanders a.a.s., so the same
   bound holds for them a.a.s.
2. **Complete graphs.** `H_t ⊆_minor K_{2t²}`, so `k*(K_s) = Ω(log s)`. The old bound here was
   `Ω(log log log s)`.
3. **Beyond GF(2).**
   * The proof uses only that the corner word is a fixed word `g` repeated `e` times, with `g^e = 1`.
     Lemma L1 holds verbatim for labels in any group `Γ`, multiplied along the cycle: segment products
     are `P(b_0)^{-1}P(b−1)`. So the argument kills every turn labelling into a finite group `Γ` of exponent
     `e` for which an `e`-fold balanced spiral exists. The holonomy is then the identity, and
     `tr ρ = dim ρ ≠ −1`.
   * Spirals with corner word `(VH+− HV++ VH−+ HV−−)^e` were found for `e = 2, 3` (in `H_{4,4}`) and for
     `e = 4, 5` (in `H_{6,6}`, a 58-cycle and a 62-cycle). For `e = 4` and `e = 5` there is none in `H_{5,5}`.
   * With `|Γ|^4` colours, a gadget needs `log|Γ| ≥ (log t)/16 − O(1)` for those exponents. So the
     non-abelian "`tr ρ(hol C) = −1`" generalisation of Theorem G (part 2, §4.1) **also** needs group size
     `m^{Ω(1)}` on these graphs, provided `e`-fold spirals exist for its exponent. That is verified for
     `e ≤ 5`. That they exist for every `e` is conjectured but not proved.

## 4. Computations (exact k*, CaDiCaL via CEGAR)

| graph | n | m | directed cycles | k* | note |
|---|---|---|---|---|---|
| H_{3,3} | 18 | 21 | 30 | 2 | |
| H_{3,4} | 24 | 29 | 108 | 2 | |
| H_{4,4} | 32 | 40 | 760 | 2 | k=2 SAT after 557 s; contains the balanced cycle B, but too small for Theorem L |
| H_{4,5} | 40 | 51 | 4984 | ≥ 2 | k=2 undecided within budget |
| random cubic n=22, 24, 26 (seed 1) | 22–26 | 33–39 | 4000, 8420, 15500 | ≥ 2 | k=1 UNSAT; k=2 undecided within budget (CPU-starved) |
| (part 2) K5…K7, K4,4, K4,5, Heawood | ≤14 | ≤21 | ≤2344 | 2 | |
| (part 2) cubic n=18, `rep2` | 18 | 27 | 1448 | 3 | solver UNSAT for k=2 |

The small values give no usable growth rate. The constant in Theorem L (`t ≳ 2^{16k}`) means the bound is
only `≥ 2` beyond `t ≈ 2^{21}`. The data are consistent with `k*` growing like `c·log n` with a moderate `c`,
but they cannot distinguish that from faster growth. CPU time in this session was very limited, which
is why the SAT data stop where they do.

## 5. Verdict

* **Growth (proved):** `Ω(log m) ≤ max{k*(G) : G bounded-degree, m edges} ≤ O(m)`. The lower bound is
  attained by explicit graphs (`H_t`), by every bounded-degree expander, and by a.a.s. every random cubic graph.
* **Conjectured:** I cannot decide between `Θ(log m)` and `m^{Ω(1)}`.
  * The Ramsey/KST method is capped at `log`, because colours are `2^{O(k)}` per cell.
  * Every known construction (topological, peak, edge) is linear.
  * No sublinear upper bound is known even for `H_t`. This is the cleanest remaining question: is
    `k*(H_t) = O(log t)`?
* **Best explicit upper bound:** `k* ≤ min(g+2, n'−1, m'−n'+1, 1 + apex, 1 + skewness)`. For bounded-degree expanders, every one of these is `Θ(m)`.
* **Consequence for #HC.**
  * Open (N) of part 2 is **refuted**. No labelling with `k = o(√log m)` exists on bounded-degree expanders,
    so Theorem G cannot produce a signed CNF of size `o(m √log m)` there.
  * The best it can give is `Θ(m log m)` (if `k* = Θ(log m)`), which is far beyond what the labs' top-level
    theorems can use. This closes Loophole 2 in its abelian form.
  * By Corollary 3, the non-abelian holonomy version is closed too, for groups whose exponent admits a
    balanced spiral (verified for exponents up to 5). What remains open there: non-abelian gadgets whose
    exponent has no spiral (if any exist), and gadgets that are not of the "local turn label + per-cycle
    character sum" form at all.

## 6. Lean status (`lean/EthFollowup/Scratch/Kstar/`, no `native_decide`)

`Basic.lean` (sorry-free) gives the definitions: graphs on `Fin n` with Boolean adjacency, directed
cycles as duplicate-free lists, turns, `F : Fin n → Fin n → Fin n → (Fin k → ZMod 2)`, and `Good`
(quantified over **all** lists). `Instances.lean` is sorry-free. `Unproved.lean` contains one marked `sorry`.

| claim | status |
|---|---|
| `Good` reduces to a finite check over all duplicate-free lists (`good_of_check`) | Lean-proved (general) |
| Subgraph monotonicity (`good_mono`) | Lean-proved (general) |
| Minor monotonicity, the contraction half | not yet formalised |
| Odd cancelling cycle family ⇒ no good 1-bit labelling (`not_good_one`) | Lean-proved (general) |
| Theorem G core: `Σ_χ(−1)^{χ·y} = 0` and `Σ_{χ≠0} = −1` for `y≠0`; independent colours on `c` cycles give `(−1)^c` (`coloured_sum`) | Lean-proved (general) |
| Rest of Theorem G (CNF, gap = n·#HC) | not yet formalised |
| k* = 1 for planar (⇐) | Lean-checked on instances (K₄, prism: explicit 1-bit good labellings) |
| k*(K₅) = k*(K₃,₃) = 2 | Lean-checked on instances: explicit 2-bit good labellings, and no good 1-bit labelling for *any* F (odd certificates of 11 and 5 cycles) |
| Lemma L2: B is a directed cycle of H_{4,4}, with corner word (VH+− HV++ VH−+ HV−−)² | Lean-checked on instance (`B44_cycle`, `B44_balanced`) |
| Lemmas L1 (for the lifted cycles) and L3, and Theorem L | **Lean-proved (general)**, `lean/EthFollowup/Barriers/KstarLower.lean`: `Kstar.theoremL` (a good k-bit labelling of H_t forces t < 2^(20k+10)) and `theoremL_log`; iterated pigeonhole replaces Kővári–Sós–Turán, so the constant is 1/20 in log₂ t instead of 1/16. Standard axioms only. L1 for arbitrary cycles and the corollaries (expanders, K_s, non-abelian gadgets) are not formalised. |
| k*(rep2) ≥ 3 | stated with `sorry`; it stands for the SAT UNSAT result |

## References (checked)

* J. Chuzhoy, R. Nimavat, *Large minors in expanders*, arXiv:1901.09349 (2019). Every bounded-degree
  `α`-expander contains every graph with `n/(c log n)·(α/d)^c` vertices and edges as a minor. The
  paper also reports the stronger independent Krivelevich–Nenadov bound `Ω(nα²/(d² log n))`.
* M. Krivelevich, R. Nenadov, *Complete minors in graphs without sparse cuts*, IMRN 2021,
  arXiv:1812.01961; and *Minors in small-set expanders*, arXiv:2503.06826 (2025).
* T. Kővári, V. T. Sós, P. Turán, *On a problem of K. Zarankiewicz*, Colloq. Math. 3 (1954) 50–57.
* H. Crapo, G.-C. Rota, *On the Foundations of Combinatorial Theory: Combinatorial Geometries*, MIT
  Press 1970 (critical problem); J. Kung, *Critical problems*, Contemp. Math. 197 (1996).
