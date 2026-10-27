# Short certificates for Hamiltonicity: CNF verifiers of length o(n·√log n)

27 Oct 2026. Tags: **[Lit]** published or preprint result (URL given), **[Proved]** proved here
(proof written out below, not machine-checked), **[Verified]** checked by a script in
`research/scripts/`, **[Conj]** conjecture or heuristic.

## 0. What the target actually is

**Main Theorem, second branch [Lit, paper.txt l. 45–60, 2510].** The time bound is
`2^{C·min{km/√log m, k²·N·loglog N/√log N}}`, where `N` is the number of variables that occur.
The second branch does not involve the number of clauses `m` (and `m ≤ (2N+1)^k` anyway).
So a verifier `Φ_G(X,Y)` gives deterministic `2^{o(n)}` decision when **either**

* (L) the total length is `L = o(n√log n)`, **or**
* (V) the width `k` and variable count `N = |E| + |Y|` satisfy `k²·N·loglog N = o(n√log n)`.

(V) is more permissive than (L). Clauses are free: you can use `n^{O(k)}` clauses, for example
"for every path P of length ≤ k/log Δ in G: [succ follows P] → …". Constant width plus
`N = o(n√log n/loglog n)` suffices.

**Equivalence with nondeterministic circuits [Proved, standard].** A nondeterministic circuit
of size `s` gives (V) with `N = s`, `k = 3` (Tseitin). Conversely a `k`-CNF on `N` variables
becomes, after sparsification (IPZ01, as used in Cor. 6 of the paper), `2^{εN}` CNFs with
`O_{k,ε}(N)` clauses, that is, circuits of size `O(N)`. The outside enumeration this costs is
allowed in the user's setting. So, up to such enumerations, the question is:

> Does "X is a Hamiltonian cycle of G" (G fixed, bounded degree) have nondeterministic circuits
> of size `o(n·√log n/loglog n)`?

## 1. Literature

* **Raz–Spieker 1995** [Lit], *On the "log rank" conjecture in communication complexity*,
  Combinatorica 15, https://link.springer.com/article/10.1007/BF01192528 . For two perfect
  matchings (equivalently permutations `a, b` of `[N/2]`; accept iff `b⁻¹a` is one cycle), the
  nondeterministic CC is `Ω(N log log N)` and the real rank is `2^{O(N)}`. They conjectured
  `Θ(N log N)`.
* **Zhang, arXiv 2610.32346 (23 Oct 2026)** [Lit, preprint, 4 days old, unrefereed],
  *Settling Nondeterministic Communication Complexity of Graph Connectivity*,
  https://arxiv.org/abs/2610.32346 . Thm 4.1: `N(bConn_N) = Θ(N log N)` for exactly the
  two-permutations problem, regardless of rounds. Also randomized `Ω(N log min(1/ε, N))`, and
  r-round `Ω(N log N/r)`.
  **So the answer to "is O(n log log n) achieved?" is no: the truth is Θ(n log n)**, provided
  the preprint is correct. RS95 alone gives only `Ω(n log log n)`.
* **Hajnal–Maass–Turán STOC'88** [Lit, as cited by Zhang and by RRV, ITCS'26,
  https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2026.110]: deterministic CC of
  connectivity is `Θ(N log N)`. The upper bound is "send a spanning forest".
* **Caveat for us.** All these bounds are for the complete-graph host, with `Θ(N log N)`-bit
  inputs. For bounded-degree `G` the input is `O(n)` bits, so every communication bound is
  `O(n)`. **Communication complexity cannot by itself rule out anything for bounded degree.**
  It can do so only combined with locality (§3).
* **Göös–Suomela**, *Locally checkable proofs in distributed computing*, ToC 12(19) 2016,
  https://theoryofcomputing.org/articles/v012a019/ [Lit]. In their table, "Hamiltonian cycle (on
  connected graphs)" is in LogLCP with `Θ(log n)` (§5). The lower bounds glue short cycles with
  identifiers into a long one, which is a graph-family argument. s–t reachability is in `LCP(O(1))`.
* **Korman–Kutten–Peleg**, *Proof labeling schemes*, Distributed Computing 22 (2010) [Lit, from
  memory]: spanning tree certification needs `Θ(log n)` bits. Survey: Feuilloley,
  *Introduction to local certification*, DMTCS 23(3) 2021, https://arxiv.org/abs/1910.12747 .
* **Grandjean–Olive**, *Graph properties checkable in linear time in the number of vertices*,
  JCSS 68 (2004), https://pageperso.lis-lab.fr/~frederic.olive/Materiel/Publis/GO04.pdf [Lit].
  Hamiltonicity and connectivity are in vertexNLIN (nondeterministic RAM, `O(n)` steps). These
  are word steps, so `n log n` guessed bits, and they do not help here.
* Circuit lower bounds: the best known for explicit functions is `3.1n − o(n)` (Li–Yang STOC'22,
  [LY22] in paper.txt). Nothing superlinear is known, even for functions in L.

## 2. Constructions tried

| scheme | N or L | why it fails or works |
|---|---|---|
| positions mod n | `N = Θ(n log n)`, k = O(1) | works; too big by a factor √log n·loglog n |
| CRT residues mod p₁…p_r with one root defect | `Σ log p_i ≥ log n` bits per vertex | same as positions |
| landmarks every B carrying log n bits, linked by path-check clauses (width ≈ B log Δ) | `k²N ≥ B²·(n/B)·log n = B·n log n` | (V) is worse than positions; (L) needs Δ^B clauses per landmark |
| landmarks (set and cyclic order) enumerated outside, B = ω(log n) | enumeration `2^{(n/B)log n} = 2^{o(n)}` | you still have to certify that "the segment from s_i ends at s_{i+1}" across ≥ log n steps. The segment colour must differ for any two landmarks within G-distance B; in an expander every pair is that close, so you need log(n/B) bits per vertex. Hash colours do not work: the end-hash is enumerated, so the adversary picks it. This is the user's tension, and §3 shows it is real for local schemes |
| hierarchical: level-j stations store the *global* name of the next level-(j−1) station | `(n/B_j)·log n` per level, with comparisons done bitwise (width B_j log Δ + 2) | the lowest level has `B ≤ k`, so `N ≥ n log n/k` and `k²N ≥ k·n log n` |
| q-colour Cut&Count with **vertex-dependent ℚ-weights** (exact, via Prop. 3.4 rather than CNF) | `log q` bits per vertex | **works with `q = 1 + td(G−r)`** (below). For expanders `td = Θ(n)`, so this is useless there |

**Signed colour filter [Proved; Verified].** Take an elimination forest of `G − r`, so that
every edge joins an ancestor and a descendant, with depth ≥ 1. Use colours `0..D`. Set
`w(v,0) = 1`, and for `j ≥ 1` set `w(v,j) = 0, −j, 1` according as `depth(v) <, =, > j`.
A cycle `C` has a unique shallowest vertex, at depth `d₀`. Colours `1..d₀−1` give `1` each,
colour `d₀` gives `−d₀`, colours above `d₀` give `0`, and colour 0 gives `1`. The sum is `0`.
Hence `Σ_{X} Σ_{colourings} Π w = #HC(G)` exactly, with `q = D+1`.
`cert_treedepth_filter.py` checks this on 30 random 3- and 4-regular graphs with n ≤ 14: the
signed sum equals #HC every time.
Consequence: hamiltonicity.md §8's bound `q ≥ n−4` does **not** extend to non-uniform weights.
Ladders need only `O(log n)` colours (numerically, q = 4 suffices for 14 rungs:
`cert_interval_colours.py`). For complete graphs `K_{m+1}` the numerics give `q = m−1`
(m = 4, 5, 6), which matches the construction exactly (the shallowest vertex of a cycle has depth
≤ m−2). [Conj] In this model `q ≥ td(G)^{Ω(1)}`, so for expanders it gives nothing.

## 3. Lower bound for layer-local verifiers on a fixed bounded-degree graph [Proved, modulo Zhang]

**Graph `G_{s,t}` (thick ring), degree 4, n = st.** Layers `V_0..V_{t−1}` (indices cyclic), each
with `s = 2^μ` vertices (tracks). Between `V_j` and `V_{j+1}` put disjoint `K_{2,2}` blocks
pairing tracks `i` and `i ⊕ 2^{ℓ(j)}`, where `ℓ(j)` runs periodically through the Beneš sequence
`0,1,…,μ−1,μ−2,…,0` (period `P = 2μ−1`). Restrict `X` to choices of one perfect matching (straight
or cross) per block. One switch bit selects it, and every X-edge is a literal of that bit. Such
an `X` is a 2-factor whose cycles are the cycles of the product of the `t` layer permutations.
So `X` is a Hamiltonian cycle iff that product is an `s`-cycle (the problem `IPC_{s,t}`).

**Locality notion.** Every variable (X or Y) gets a layer, and every clause's variables lie in
`r` cyclically consecutive layers. Positions-mod-n and the "origin label" scheme are layer-local
with `r = 1`. So are path-check clauses of length ≤ r.

**Theorem.** Let `Φ_e`, `e ∈ [2^E]`, be layer-local verifiers of span `r` with
`X ∈ HC ⇔ ∃e ∃Y Φ_e(X,Y)`, on `G_{s,t}` with `t ≥ 3L`, `L = 2P`. Then
`|Y| ≥ t·(c·s log s − O(rs) − E)/(4r+2)`. For `r ≤ c′ log s` and `E ≤ (c/3)·s log s` this is
`Ω(n log s / r)`. With RS95 in place of Zhang, replace `s log s` by `s log log s`, which gives
`|Y| = Ω(n log log s / r)` for `r ≤ c′ log log s`. That version needs no preprint. (Take
`P | t` so the cyclic stage pattern is consistent.)

*Proof.* For each `p ∈ Z_t`, give Alice the switch bits of the window `W_p = [p, p+L)` and Bob
the rest. The window contains an aligned Beneš block, and so does the complement, so Alice's
product `a` and Bob's `b⁻¹` range over all of `S_s`. On these inputs the function is `bConn`.
Protocol: guess `e`, all Y-variables with layer within `r` of the two window boundaries, and the
X-bits there (`O(rs)` bits). Each player privately guesses the rest of Y on their side and checks
every clause touching their side. A span-`r` clause that touches both sides has all its variables
in the guessed band. So `N(bConn_s) ≤ E + O(rs) + y(∂W_p)`, where `y(∂W_p)` is the number of
Y-variables within `r` of `∂W_p`. Sum over `p`: each layer lies within `r` of at most `4r+2`
boundary instances. ∎

*Tight:* origin labels (the track at layer 0 from which the path came, log s bits per vertex)
plus positions of `s` items give `|Y| = O(n log s)`, `r = 1`.
*Note:* the theorem holds in the user's (V) measure even with path-check clauses: `r ≤ k`
forces `k²N ≥ k·n log s`.

**What it does not cover.** (i) Clauses linking far-apart layers, i.e. genuinely global
verifiers such as sorting or routing networks laid across the ring. (ii) Global enumeration
`E ≥ s log s`. [Conj: a direct-sum version of Zhang for alternating products `a₁b₁…a_kb_k`
would extend this to any `E ≤ cn`.] (iii) Signed or ℚ-weighted local schemes: the real rank of
bConn is only `2^{O(s)}` (RS95), so the same argument yields only `|Y| = Ω(n)`. This is exactly
the log-rank gap. (iv) Expanders: they have no small cuts, so cut-based communication arguments
are vacuous and **no lower bound technique applies**, even for G-local schemes.

## 4. Barrier for the general (non-local) question [Proved reductions]

* `G_{s,t}` has pathwidth `O(s)`, so HC on it is easy by DP. But take `G = G_{s,t} ∪ H` for any
  bounded-degree expander `H` on the same vertex set. Then any `Φ_G`, with the non-ring X-bits
  set to 0, is a verifier for `IPC_{s,t}` with the same `N` and `k`. So **the CNF route on all
  bounded-degree graphs requires nondeterministic circuits (or ∃-k-CNFs) of size
  `o(n√log n/loglog n)` for `IPC_{s,t}`, for every `s` up to `n/log² n`.** All known methods
  cost `n log s`: tracking labels through `t` butterfly stages, or guessing composites. By §3,
  any improvement must be non-local.
* Proving impossibility would need a superlinear (`ω(n)`) nondeterministic circuit lower bound
  for `IPC`, a logspace function. That is beyond current techniques (best explicit bound
  `3.1n`). So neither direction is likely to be settled soon.
* Sorting and routing ideas cost `Θ(n log n)` wires or more (AKS: `n log n` comparators of
  `log n`-bit keys). No sub-`n log n` deterministic verification of "C = π(B)" is known
  without randomness. Polynomial-identity tests are randomized, and the user wants
  determinism.

## 5. Honest odds

* Constructing a CNF with `L = o(n√log n)` (or (V)) for all bounded-degree G: **≈ 5%**. It
  would need a new non-local idea that beats `n log s` for iterated permutation-product
  cyclicity.
* A clean impossibility for unrestricted CNFs: **< 2%** (circuit-lower-bound barrier).
* Most promising escape, outside the CNF/Lean theorem: signed bounded-scope factor models via
  Prop. 3.4. NCC lower bounds do not apply there, and rank allows `O(1)` "bits" per vertex
  across cuts. The colour model needs only `td(G)+1` colours, but for expanders that is
  `Θ(n)`. Odds of an `O(n)`-variable signed exact local scheme for expanders: unknown, maybe
  10%.

## Scripts

* `scripts/cert_treedepth_filter.py`: exact check of the signed treedepth colour filter.
* `scripts/cert_interval_colours.py`: ladder (interval) system, minimum q by numerics.
* `scripts/cert_colour_graphs.py`: minimum q for K_m and random cubic graphs (numerics; a
  residual below 1e-9 counts as solvable, and failure to find a solution is heuristic, not
  proof).
