# The Tutte plane on sparse graphs and the network engine

29 Oct 2026. Scope: evaluate T_G(x,y) on graphs with m = O(n) edges, or with bounded degree, using
the network engine of the 2026 refutations ([A]: Lemma 8 + Theorem A + Theorem B, as quoted in
`exact-hc-theorem.md` §1 and pinned in `anthropic-api.md`). Every algorithmic statement below is
**conditional on [A]**, exactly like our #HC theorem. The barrier statements are unconditional
theorems about a stated class of networks.

Tags: **[Proved]** means a full proof is given here. **[Computed]** means checked in exact
arithmetic by a `research/scripts/tutte_*.py` script. **[Cited]** means a literature statement,
checked against the source as noted in §7. **[Conj]** means a conjecture.

Scripts (all print PASS/FAIL; outputs saved as `*.out`):

* `tutte_lib.py`: brute-force Tutte (subset expansion and, independently, deletion–contraction),
  the FK/Potts polynomial, colouring and flow sums, set partitions, and exact ranks over Q and F_p.
* `tutte_identities.py`: identities I1–I8 (1212 checks).
* `tutte_network.py`: the H_q colour network and flow network, the Kronecker decoding of the
  whole hyperbola, hub splitting, and the forest network on y = 1 (130 checks).
* `tutte_ranks.py`: rank of M_q, of the connectivity matrix and of the acyclicity matrix, cut
  matrices on subcubic test graphs, and the HC contrast.
* `tutte_ranks_connected.py`: the same cut ranks on *connected* subcubic test graphs, which makes
  them independent of the normalisation.
* `tutte_catalan.py`: the y = 1 acyclicity matrix has rank Catalan(b) mod 1000003 for b ≤ 7
  (needs numpy).

---------------------------------------------------------------------------------------------------

## 0. Result: a sharp dichotomy for the engine

Write u = x − 1, v = y − 1 and q = uv. Let 𝓗 := ⋃_{q ∈ {1,2,3,…}} H_q, where
H_q = {(x,y) : (x−1)(y−1) = q}, and let 𝓛 := {y = 1}.

**Theorem P (positive, conditional on [A]).** On graphs with m edges:

* (P1) For every integer q ≥ 1, the whole restriction T_G|_{H_q} (a univariate Laurent
  polynomial) is computed deterministically in time 2^{O(m·log(q+1)/√log m)}. The constant is
  absolute and uniform in q.
* (P2) The whole polynomial T_G(x,1) is computed in time 2^{O(m/√log m)}. This is the forest
  network of `paper/main.tex` lem:forest; it is not new here.

So for m = O(n) the engine gives 2^{o(n)}, indeed 2^{δn} for every δ, on 𝓗 ∪ 𝓛, and also for
q = q(n) as long as log q = o(√log n). §2 has the proof.

**Theorem B (barrier, unconditional).** Fix a point (x,y) ∈ ℂ² **off** 𝓗 ∪ 𝓛, that is, y ≠ 1 and
(x−1)(y−1) ∉ {1,2,3,…}. Let N be a *vertex-local* network family on subcubic graphs (Model V(s),
§3.1: each node's tables depend only on the edges at one cluster of ≤ s ≤ n/log₂ n vertices,
and the skeleton g, (c_{a,b}) is fixed). Suppose N computes c(n, m, k(G))·T_G(x,y) for an
arbitrary nonzero normalisation c, for example T itself, the FK form Z = u^{k}v^{n}T, or the forest
form. Then

```
U(N) ≥ Σ_groups log₂ Bell(b_G) ≥ (1 − o(1)) · n·log₂ n,
```

and the engine's own guarantee is at least 2^{(1/2 − o(1))·n·√(log n)} ≫ 2^n (Lemma 2.1 of
`permanent/barrier.md`). The same bound holds, with constant 1/4 in place of 1/2, for a sum of up
to 2^{o(n log n)} such networks that share one clustering. §3 has the proof.

**On 𝓗 ∪ 𝓛 the barrier is provably absent, and sharply so.**

* On H_q the cut rank across b boundary vertices is exactly Σ_{j≤q} S(b,j) ≤ q^b. The same
  argument gives U = Ω(n log q) for q ≤ n/8, which matches (P1) up to a constant factor.
* On 𝓛 the cut rank is Catalan(b). This was computed on the connected test families for b ≤ 4,
  and for the acyclicity matrix for b ≤ 6 (≥ Catalan(7) at b = 7). The upper bound 2^{2b−1}
  (Grassmann) is proved.

**Theorem P3 (the matching upper bound everywhere).** At every point, Z_G(q,v) is the Lagrange
combination in q of the n+1 colour networks with 1…n+1 colours. That is a sum of n+1 vertex-local
networks with U ≤ 2m log₂(n+1) + g² ([Computed] N7). So the minimal vertex-local resource is
U* = Θ(n log n) off 𝓗 ∪ 𝓛, Θ(n log q) on H_q, and O(n) on 𝓛. The engine pays e_K·U*.

* With [A]'s pieces (ρ = 1/√2), e_K = Θ(1/√log K), so the rest of the plane costs
  2^{Θ(n√log n)}.
* With **any** pieces, ρ ≥ 1/2 is forced (`permanent/rate.md`: the framework's ceiling is
  2^{O(U/log U)}). Then e_K ≥ 1/(2(log K + 2x₀)), and Theorem B gives an engine exponent
  ≥ (½ − o(1))·n.

So [A]'s recursion can **never** reach 2^{o(n)} off 𝓗 ∪ 𝓛. A 2^{o(n)} algorithm through networks
needs a clique algorithm *outside* that framework, with exponent e_K = o(1/log K), which
`barrier.md` Lemma 2.2 allows information-theoretically. Given such an algorithm, Theorem P3
puts the whole plane in 2^{o(n)} (§4.1, §5).

The dichotomy is governed by **q alone**, plus the q → 0 limit along v → 0. This fits a classical
fact: every 2-terminal substitution, that is, stretching, thickening or a tensor product, preserves
q. No local gadget moves a point off its hyperbola.

### The map (figure-like table)

| Region of the (x,y)-plane | Best classical bound, m = O(n) | Engine (refutation world) | Status |
|---|---|---|---|
| H_1: (x−1)(y−1) = 1 | poly: T = y^m (y−1)^{−r(E)} | poly | [Cited] JVW; [Computed] I6 |
| JVW special points (1,1), (−1,−1), (0,−1), (−1,0), (±i,∓i), (j,j²), (j²,j) | poly | poly. All lie on H_1…H_4 or on 𝓛 | [Cited]; [Computed] I7 |
| H_q, q ∈ {2,3,4,…} (Ising q = 2, Potts, chromatic at y = 0, flow polynomial at x = 0, (−1,−1) ∈ H_4) | 2^n·poly (BHKK08); q^{tw}·poly with tw ≤ m/5.77 (q^{n/6} cubic) | **2^{O(m log q/√log m)}**, whole hyperbola (P1) | [Proved] conditional on [A]; network [Computed] |
| line y = 1 (forests; T(2,1) = #forests) | 2^n·poly | **2^{O(m/√log m)}**, whole line (P2) | lem:forest; network [Computed] (ext 4d′) |
| (1,1) spanning trees | poly (matrix-tree) | poly | classical |
| line x = 1, y ≠ 1 (connected spanning subgraphs; T(1,2)) | 2^n; Bell(tw)·poly exact; **p^{tw} mod p** (GMNS22) | **barrier**: cut rank Bell(b); exact counting not reachable; mod p it is local (log p bits per vertex) | Thm B [Proved]; ranks [Computed] |
| y = 0, x ∉ {1−q : q ∈ ℤ≥1} (chromatic polynomial at non-integer or negative λ) | 2^n | barrier | Thm B |
| x = 0, y ∉ {1, 0, −1, −2, …} (flow polynomial at non-integer λ) | 2^n | barrier (triangle gadget) | Thm B; [Computed] b ≤ 3 |
| every other point: q ∉ ℤ≥0, y ≠ 1 (e.g. (2,2) is H_1; (3,1/2), (−2,3), (1/2,3)) | 2^n | barrier: U ≥ (1−o(1)) n log n, engine ≥ 2^{(1/2−o(1)) n√log n} | Thm B [Proved] |

"Barrier" means that no vertex-local network family with a fixed skeleton, and no sum of
2^{o(n log n)} of them on one clustering, lets the engine certify a running time below 2^n. It
does **not** mean hardness: in the general model (tables are arbitrary poly-time functions) no
unconditional barrier is possible (`permanent/barrier.md` Prop. 4.1). §5 lists what is open.

---------------------------------------------------------------------------------------------------

## 1. Setup

T_G(x,y) = Σ_{A⊆E} (x−1)^{r(E)−r(A)} (y−1)^{|A|−r(A)}, with r(A) = n − k(A). The FK
(Fortuin–Kasteleyn / multivariate-Potts, Sokal 2005) form is

```
Z_G(q,v) = Σ_A q^{k(A)} v^{|A|},       T_G(x,y) = u^{−k(G)} v^{−n} Z_G(uv, v)      (u = x−1, v = y−1).   (1.1)
```

[Computed] I2 checks (1.1) on 50 random multigraphs. k(G) and n are poly-time *global* scalars, so
computing T and computing Z are the same problem algorithmically. They are **not** the same for a
cut-rank argument. Under the T-normalisation, forest test families have higher cut rank even at
the positive points: `tutte_ranks.py` R4 gives rank 15 > Catalan(4) = 14 at (1,1) and (5/2,1),
because the factor u^{−k(G)} = u^{−|σ∨τ|} is a Hadamard multiplier of rank Bell(b). §3.3 removes
this effect with connected test graphs.

**Engine cost** (`exact-hc-theorem.md` (6.2); `permanent/barrier.md` Lemma 2.1). A network on g
nodes with total U (every shared bit counted from both ends) and per-node size P costs
2^{e_K(U + gP/K) + 2gP/K}·τ·poly. Conversely, the engine's guarantee is always
≥ 2^{U/(2√(log U + 2x₀))}. So the engine beats 2^n **iff** some network has
U < (2+o(1))·n√log n. **A barrier is a proof that U = ω(n√log n).**

---------------------------------------------------------------------------------------------------

## 2. Positive results

### 2.1 Integer hyperbolas (H1 confirmed)

**Identities.** [Computed] I3, I4.

* For integer q ≥ 1: Z_G(q,v) = Σ_{c:V→[q]} Π_{ij∈E}(1 + v[c_i = c_j]). Expand the product over
  the edges; then Σ_c Π_{e∈A}[c constant on e] = q^{k(A)}.
* For q prime or a prime power (checked for q = 2,3,4,5, with GF(4) as Z₂²):
  #{F_q-flows on A} = q^{|A|−n+k(A)}, and therefore

  ```
  q^{m−n}·Z_G(q,v) = Σ_{f : E→F_q a flow} (q+v)^{#{e: f_e=0}} v^{#{e: f_e≠0}}.
  ```

  This is a local sum: flow conservation at each vertex, and a weight on each edge.

**The network** (`tutte_network.py` N1, [Computed] by *honest* summation over all settings of all
nodes with the Ψ-product). Blobs β: V → [g], with the crossing edges oriented from the low blob
to the high blob.

* *Labels.* The Schmidt decomposition 1 + v[c_i=c_j] = Σ_{t∈[q]} [c_i=t]·(1+v[t=c_j]) has q
  terms. A crossing edge e = (i ∈ V_a, j ∈ V_b), a < b, gets the label ℓ_e ∈ [q] (meaning c_i).
* *Settings.* Node a's setting is the labels of its crossing edges, written for each b as one
  base-q block.
* *Edges.* Ψ_{a,b} is equality of the two blocks; c_{a,b} = ⌈e_{ab} log₂ q⌉.
* *Node tables.* W_a(ℓ) = Σ_{c:V_a→[q]} Π_{internal e}(1+v[=]) · Π_{e: a low}[ℓ_e = c_i] ·
  Π_{e: a high}(1+v[ℓ_e = c_j]).
* There are no signs: the network is bosonic. Value = Z_G(q,v).

The flow network (N3) is the same, with ℓ_e = f_e ∈ F_q, and has value q^{m−n}Z.

**Accounting** (same bookkeeping as Prop. 5.4 of `exact-hc-theorem.md`):

```
U = 2 Σ_{a<b} ⌈e_ab log₂ q⌉ ≤ 2 m_× log₂ q + g²,      P ≤ μ log₂ q + g,      log τ ≤ μ_a log₂ q + O(log n),
```

where μ = max blob degree-sum ≤ 2m/g + Δ (Lemma 6.2 of the HC note). The HC note's degree
branching (Lemma 6.1) is not needed. Hub splitting is free here: replace a vertex of degree d by
a path of d copies joined by *equality constraints* [c = c′]. These are local, of Schmidt rank q,
and keep Z ([Computed] N4). So Δ ≤ 3, with n′ ≤ n + 2m.

**Theorem P1.** For integer q ≥ 1 and any graph with m edges, Z_G(q,·) as a polynomial in v,
and hence T_G on all of H_q (through T(1+q/v, 1+v) = Z(q,v)/(q^{k}v^{n−k})), is computed within
2^{C·m·log₂(q+1)/√log m} operations, with C absolute.

*Proof.*

1. Run the HC note's §6.4 with log 5 replaced by log q, on the hub-split graph.
2. The whole polynomial is handled by Kronecker substitution. Set v := 2^{b₀} with
   b₀ = n log q + m + 2; all coefficients are nonnegative and < 2^{b₀}. Then W_a has
   O(μ(n log q + m)) bits, so B = poly(n). B enters (1.2) only as (λ+B)^{C₀K²} = 2^{O(K² log n)}.
3. Decode Z(q, 2^{b₀}) in base 2^{b₀} ([Computed] N2). The univariate Laurent polynomial T|_{H_q}
   follows; N2 checks it at random rational points of H_q.

The leading term is e_ℓ·U ≤ e_ℓ(2m log q + g²) with e_ℓ = O(1/√log n). All other terms are
o(m/√log n), exactly as in the HC proof. ∎

Remarks.

* q = 1 is trivial. q = 2 is the whole Ising line (x−1)(y−1) = 2, including (0,−1), (−1,0) and
  (±i,∓i).
* On y = 0 we have q = 1 − x = λ, so the chromatic polynomial P(G,λ) = (−1)^{r}λ^{k}T(1−λ,0) is
  reached exactly at the positive integers λ.
* On x = 0 we have q = 1 − y = λ, so the flow polynomial is reached exactly at the positive
  integers λ.
* Everything extends verbatim to Sokal's multivariate Z(q, {v_e}) with integer edge weights.

### 2.2 The forest line (H2, first half: confirmed)

lem:forest of `paper/main.tex` reads
[z^{|S|−|X|}] det(L_H + z·diag(2 − deg_H)) = 2^{c(H)}[H forest]. [Computed] I5 checks it on 50
graphs. Spread over the edges in Grassmann form, it is a vertex-local fermionic network with
**4 labels per crossing edge**. Its values are [Computed] `ext_problems.py` 4d′, re-run inside
N5. Counting forests by edge number (Kronecker) gives T(x,1) = Σ_k f_k (x−1)^{r(E)−k}, checked
in N5. Hub splitting by forced edges keeps forest counts (`exact-extensions.md` §3). Hence (P2):
U ≈ 4m_× + O(g³) and time 2^{O(m/√log m)}.

### 2.3 What the fermions reach (CJSSS)

Caracciolo–Jacobsen–Saleur–Sokal–Sportiello (PRL 93, 2004) obtain the q → 0 limit of the Potts
model with v ∝ q, that is, forests weighted by w^{|F|}, from a free fermion plus a 4-fermion term
(OSp(1|2) symmetry). With u = 1/w and v = wq → 0, this is exactly the line y = 1. The fermionic
toolbox (matrix-tree, matrix-forest, the 4-fermion term) therefore reaches 𝓛 and (1,1), and
nothing more. That matches Theorem B: the line x = 1, which is q → 0 at fixed v ≠ 0, is not
reachable.

### 2.4 Everything is local modulo a small prime (but this does not give exact values)

Z_G(q,v) ∈ ℤ[q,v], so Z_G(q,v) ≡ Z_G(q mod p, v) (mod p) for p-integral q. The right side is a
(q mod p)-colouring sum, local with log p bits per vertex. This is the mechanism behind the
p^{tw} algorithm of Groenland–Mannens–Nederlof–Szilágyi for counting connected spanning edge
sets mod p. Equivalently, over F_p one has rank M_q ≤ Σ_{j<p} S(b,j) < p^b, because (q)_j ≡ 0 for
j ≥ p ([Computed] R2: the connectivity matrix has rank Σ_{j≤min(b,p)} S(b,j) over F_p, against
Bell(b) over Q). **Exact values need p (or p^k) ≳ 2^{Ω(m)} in total.** §4.2 shows that every
CRT or p-adic assembly pays log₂(min(b,m)) bits per boundary vertex, which is the barrier again.

---------------------------------------------------------------------------------------------------
## 3. The barrier (H3 confirmed, made rigorous)

### 3.1 Model

**Definition (Model V(s), following `permanent/barrier.md` §5).**

* A *network family* is a map G ↦ N(G) on the graphs of an input class 𝓖 with vertex set [n]
  (here: subcubic graphs, or max degree ≤ 6 at x = 0).
* [n] is partitioned into clusters of size ≤ s. Each node is assigned to one cluster, or is a
  routing node that reads nothing.
* The data (S_a, W_a, f_{a,·}) of a node depends on G only through the edges with an end in its
  cluster.
* The skeleton (g, c_{a,b}) does not depend on G within 𝓖.
* N *computes the point (x,y) in normalisation c* if value(N(G)) = c(n, |E(G)|, k(G))·T_G(x,y)
  for all G ∈ 𝓖, for some fixed function c ≠ 0.

Both our HC network and [A]'s 3-SAT network are vertex-local in this sense. Our skeletons depend on
the input only through crossing-edge counts, and those are *fixed* in the test families below, so
Gap A of `barrier.md` does not arise for skeletons of that kind.

**Lemma 3.1 (cut lemma; `barrier.md` Lemma 3.1).** Split the nodes into L and R. Then
value(N) = Σ_{θ ∈ {0,1}^{w}} F_L(θ) F_R(θ), with w = w(L,R) = Σ_{a∈L,b∈R} c_{a,b}. So if the data of
L depends only on X and the data of R only on Y, the matrix [value(N(X,Y))]_{X,Y} has rank ≤ 2^w.

### 3.2 The gluing matrices (Lindström factorisation)

Let Π_b be the set partitions of [b], ordered by refinement (1̂ = one block), and let ζ[P,S] =
[P ≤ S]. ζ is unitriangular. Every f on Π_b with f(P) = Σ_{S ≥ P} g(S) gives
[f(P∨Q)]_{P,Q} = ζ·diag(g)·ζᵀ (Lindström 1969, Wilf 1968). Hence:

**Lemma 3.2.** [Proved; Computed R1, R2 for b ≤ 6.]

* (a) M_q := [q^{|P∨Q|}] = ζ diag((q)_{|S|}) ζᵀ, because q^{|P|} = Σ_{S≥P} (q)_{|S|}: count the
  colourings of the blocks of P by their kernel. So rank_Q M_q = #{S : (q)_{|S|} ≠ 0}. This is
  Bell(b) for q ∉ {0,1,…,b−1}, and Σ_{j≤q} S(b,j) for q ∈ {0,…,b−1}. Values for b ≤ 6:

  | q | b=3 | b=4 | b=5 | b=6 |
  |---|---|---|---|---|
  | 2 | 4 | 8 | 16 | 32 |
  | 3 | 5 | 14 | 41 | 122 |
  | 4 | 5 | 15 | 51 | — |
  | −1, ½, 7/3, … | 5 | 15 | 52 | 203 |

  These are the classical rank drops of the Potts transfer / "chromatic" Gram matrix at integer q.
  This is the connection-rank statement for the chromatic polynomial in Freedman–Lovász–Schrijver
  (JAMS 2007) and Lovász's book (2012).
* (b) C := [P∨Q = 1̂] = ζ diag(μ(S,1̂)) ζᵀ with μ(S,1̂) = (−1)^{|S|−1}(|S|−1)! ≠ 0, so
  rank_Q C = Bell(b). Over F_p, (k−1)! ≡ 0 exactly when k > p, so
  rank_{F_p} C = Σ_{j≤min(b,p)} S(b,j). ([Computed] for p = 2, 3, 5 and b ≤ 6.)
* (c) The whole-plane kernel. Gluing two sides along b boundary vertices with induced partitions P
  and Q creates |P∨Q| components and a cycle rank b − |P| − |Q| + |P∨Q|. So the kernel is
  K_{u,v}[P,Q] = u^{|P∨Q|} v^{b−|P|−|Q|+|P∨Q|} = diag(v^{−|P|})·M_{uv}·diag(v^{b−|Q|}). Its rank is
  rank M_q for v ≠ 0 ([Computed] R3). At v = 0 only the acyclic gluings survive:
  A_u[P,Q] = u^{|P∨Q|}[|P|+|Q|−|P∨Q| = b]. **[Computed] rank A_u = rank A_1 =
  1, 2, 5, 14, 42, 132 = Catalan(b) for b ≤ 6, and ≥ 429 = Catalan(7) (mod 1000003).** The rank is
  ≤ 2^{2b−1} [Proved]: the forest network factors every y = 1 gluing through the even part of the
  Grassmann algebra on the 2b boundary generators. [Conj] rank A_u = Catalan(b) for all b and all
  u ≠ 0; the non-crossing partitions are the natural basis (compare the Temperley–Lieb remark in
  §4.3).

### 3.3 Realisability by bounded-degree gadgets

Fix a set S = {u_1,…,u_b} (the group) and disjoint vertices w_1,…,w_b outside S.

* **L side.** F_σ is the linear forest on S with one path per block of σ (in index order).
* **Crossing.** The matching u_i w_i (x ≠ 0), or the triangle gadget u_i w_i, u_i w′_i, w_i w′_i
  (x = 0).
* **R side.** F_τ is the linear forest on the w's. For the robust version, *connectors* join
  consecutive τ-blocks: an edge E, w–w′, or a path P, w–h–w′ (x ≠ 0); or a pendant triangle plus
  an edge, T, or a triangle on w, w′, h′, T2 (x = 0).

All degrees are ≤ 3 for x ≠ 0, and ≤ 6 for x = 0 (checked by enumeration for b ≤ 5). For a side X containing the boundary U, let z_X(Q) = Σ_{A⊆E(X),
A induces Q on U} q^{#comps of A avoiding U} v^{|A|}. Then Z(G) = Σ_{P,Q} z_L(P) q^{|P∨Q|} z_R(Q),
or with C in place of M_q, and the "no internal component" vectors z⁰, on x = 1.

**Lemma 3.3 (triangularity).** [Proved]

* (i) z_{F_σ}(P) ≠ 0 only for P ≤ σ, and z_{F_σ}(σ) = v^{b−|σ|}.
* (ii) For the R-forest family with the matching, z_{R_τ}(Q) ≠ 0 only for Q ≤ τ. The diagonal
  entry is v^{2b−|τ|−#singletons}(q+v)^{#singletons}, where q + v = xv.
* (iii) With the triangle gadget, the diagonal entry is
  Π_{blocks |B|≥2} v^{|B|−1}(qv+3v²+v³)^{|B|} · Π_{singletons}(q²+3qv+3v²+v³). At x = 0 (q = −v)
  this is a nonzero multiple of (y+1)^{·} y^{·}.
* (iv) On x = 1, z⁰_{R_τ} is triangular with diagonal v^{2b−|τ|}.

*Proof.*

* (i) A subset of a path through a block can only split the block, and only the full subset keeps
  it whole.
* (ii) The u's can be joined only through the w's of one τ-block, so Q ≤ τ. Inducing exactly Q = τ
  forces every edge of each block of size ≥ 2. A singleton block either uses its crossing edge (v)
  or does not, leaving w_i as an internal component (q).
* (iii) The same argument with the rooted triangle: there are qv + 3v² + v³ ways for u to reach w
  inside the triangle, and Z(K₃)/q in total.
* (iv) Internal components are forbidden, so singleton crossing edges are forced. ∎

**Lemma 3.4 (connected families span the same space).** [Proved; Computed b ≤ 4]

* For a non-boundary vertex w of R: z_{R+pendant edge at w} = (q+v)·z_R.
* Deletion–contraction z_R = z_{R−e} + v·z_{R/e} holds for every edge e with a non-boundary end,
  and also for z⁰.

Applying it to e = hw′ in R + (w–h–w′) gives (q+v)·z_R = z_{R+P} − v·z_{R+E}. With a pendant
triangle in place of the pendant edge, (Z(K₃)/q)·z_R = z_{R+T} − v·z_{R+T2}. Induction over the
|τ|−1 connectors gives (q+v)^{|τ|−1} z_{R_τ} = Σ_{choices}(−v)^{#E} z_{R_τ+choices}: the forest
vectors lie in the span of vectors of **connected** subcubic R-graphs. On x = 1 use z⁰, where the
pendant factor is v. ∎

**Proposition 3.5 (cut rank).** Let (x,y) be off 𝓗 ∪ 𝓛. Over the L-family {F_σ : σ ∈ Π_b} and
the connected R-family, the matrix [c(n,m,k(G))·T_G(x,y)] has rank exactly Bell(b) whenever
q ∉ {1,…,b−1}. At a point of H_q it has rank Σ_{j≤q} S(b,j). This holds for every normalisation c
(after the padding remark below).

*Proof.* All test graphs are connected, so k(G) = 1, and n and m split into an L part and an R
part. So c·T = (row scalar)·(column scalar)·Z for x ≠ 1, or ·Σ_{A conn.} v^{|A|} for x = 1.

* The matrix is A·M·Bᵀ: A is invertible (Lemma 3.3(i), v ≠ 0), M is M_q or C (Lemma 3.2), and the
  rows of B span R^{Π_b} (Lemmas 3.3(ii)–(iv) and 3.4; this needs x ≠ 0, or the triangle gadget
  with y ∉ {0,−1}). Off 𝓗 ∪ 𝓛 every such exception lies on H_1 or H_2.
* So rank = rank M, and Lemma 3.2 finishes. ∎

*Padding remark.* If one insists on a fixed vertex set [n] and an arbitrary c(n,m,k), hang the
unused vertices as pendant paths, or pendant cycles at x = 0, and equalise m_L with pendant
cycles. A pendant gadget H multiplies T by T(H), a nonzero constant for a suitable cycle length.
That is a row or column scaling, so the rank is unchanged.

[Computed] `tutte_ranks.py` R4 (forest family, b ≤ 4, both normalisations) and
`tutte_ranks_connected.py` (connected family, b ≤ 4; x = 0 for b ≤ 3; gluing formula
cross-checked by brute-force Tutte):

| point | q | b=3 | b=4 | predicted |
|---|---|---|---|---|
| (3,½), (−2,3), (½,3), (2,0), (−½,−½) | −1, −6, −1, −1, 9/4 | 5 | 15 | Bell |
| (1,2), (1,−1), (1,0) | 0 (x=1) | 5 | 15 | Bell |
| (0,½), (0,3) | ½, −2 (x=0) | 5 | 15 (forest family) | Bell |
| (−1,0), (0,−2), (3,3), (−1,−1) | 2, 3, 4, 4 | 4, 5, 5, 5 | 8, 14 (forest family), 15, 15 | Σ_{j≤q}S(b,j) (= Bell for b ≤ q; at b = 5, q = 4 it is 51 < 52, R1) |
| (2,1), (5/2,1), (1,1) | y=1 | 5 | **14** | Catalan |

### 3.4 Summing the cuts

**Theorem B.** Let (x,y) be off 𝓗 ∪ 𝓛, and let N be a Model V(s) family on subcubic graphs
(Δ ≤ 6 when x = 0) that computes (x,y) in some normalisation, with s ≤ k := ⌈n/log₂ n⌉. Then
U ≥ (1 − o(1))·n log₂ n. For a sum of N_net such networks on a common clustering, some summand has
U ≥ 2(log₂ Bell(⌊n/4⌋) − log₂ N_net) = (½ − o(1))·n log₂ n − 2 log₂ N_net.

*Proof.*

1. *Groups.* Group consecutive clusters, closing a group once its size is ≥ k. Every group then
   has size b_G ∈ [k, k+s] ⊆ [k, 2k] ≤ n/4, and the leftover has size < 2k.
2. *One group.* For a group G put L := its nodes and R := all other nodes, including routing
   nodes. Build the test family of §3.3 on S = V(G). This needs 3b_G ≤ n vertices for W, the h's
   and the gadgets, and fixes the crossing edges. L reads only edges at S, which are F_σ plus
   fixed edges; R reads only the R-graphs plus fixed edges. By Lemma 3.1 and Prop. 3.5,
   2^{w(L,R)} ≥ Bell(b_G).
3. *Sum.* As in `barrier.md` Thm 6.1, Σ_G w(L_G, R_G) ≤ U, since each ordered pair of nodes is
   charged to at most one group. With log₂ Bell(b) = b log₂ b − b log₂ log b − O(b):
   U ≥ Σ_G b_G(log₂ k − log₂ log₂ n − O(1)) ≥ (n − 2k)(log₂ n − O(log log n)) = (1 − o(1)) n log₂ n.
4. *Sums of networks.* With one group of size ≈ n/4, Σ_t 2^{w_t} ≥ Bell(b), so
   max_t w_t ≥ log₂ Bell(b) − log₂ N_net, and U_t ≥ 2w_t. ∎

**Corollary B′ (no subexponential certificate).** By Lemma 2.1 of `barrier.md`, the engine's
guarantee on any such network is ≥ 2^{U/(2√(log U + 2x₀))} = 2^{(½−o(1))·n·√(log₂ n)}, and for a
sum of 2^{o(n log n)} networks it is ≥ 2^{(¼−o(1))·n√log n}. Both are ≫ 2^n.
With hypothetical pieces of the optimal ratio ρ = 1/2, the same computation gives
e_K ≥ 1/(2(log K + 2x₀)) and hence a guarantee ≥ 2^{(½−o(1))·n}. So [A]'s framework never
certifies 2^{o(n)} off 𝓗 ∪ 𝓛.

**Sharpness on H_q.** The same proof gives U ≥ Σ_G log₂ S(b_G, q) ≥ (n − 2k)(log₂ q − o(1)) for
q ≤ k^{1−ε}. Theorem P1 gives U ≤ 2m log₂ q + g² = O(n log q) on subcubic graphs. So on H_q the
engine's resource is **Θ(n log q)**, and the dichotomy is quantitative: U ≈ n·log₂(min(q, n)),
with q = ∞ for non-integer q.

**Comparison with the permanent barrier.** In `barrier.md`, Model V only gives U ≥ 2n
(Prop. 3.5 there), because the information sits in the *shared* edges between the two sides. For
the Tutte plane the information is the *connectivity pattern* of the private parts. The shared
edges can be fixed to a matching, and the single-cut method already yields b log b per group.
Gap B (sums of networks) also closes here for a common clustering: one cut of size n/4 already
carries Θ(n log n) bits.

---------------------------------------------------------------------------------------------------
## 4. Why the barrier is sharp, and why HC and y = 1 escape

### 4.1 The upper bound Θ(n log n) holds everywhere (H4: the interpolation route, quantified)

**Proposition P3.** [Proved; Computed N7] For **every** point, Z_G(q,v) is a polynomial of degree
≤ n in q. So it is the Lagrange combination of the n+1 colour networks of §2.1 with
N = 1, …, n+1 colours, which is a sum of n+1 vertex-local networks on one clustering, each with

```
U ≤ 2 m_× log₂(n+1) + g²,
```

and T(1,y) = v^{−(n−1)}·[q¹]Z for connected G. Fewer hyperbolas suffice for T itself:
T|_{H_1}, …, T|_{H_N} with N = min(r(E), m − r(E)) + 1 determine T. In the coordinates
(s,t) = ((x−1)(y−1), y−1), the diagonal t^d of T = Σ c_{ij}s^i t^{j−i} has at most
min(r, nullity) + 1 unknowns, so a Vandermonde system per diagonal recovers it ([Computed] I8).
For m = Dn with D > 1 this is still Θ(n) hyperbolas. Counting dimensions, each hyperbola gives
≤ m+1 numbers against ≈ r·nullity unknowns, so N ≥ Ω(n) is unavoidable for generic coefficient
vectors.

Together with Theorem B: **the minimal vertex-local resource is**

| region | U* (subcubic, up to constants) |
|---|---|
| H_1 | 0 |
| H_q, q ∈ {2,3,…} | Θ(n log q) |
| y = 1 | O(n) (4 labels per edge). Lower bound Ω(n) holds if rank = Catalan(b) [Conj; checked b ≤ 4 on connected families, b ≤ 7 for A_u] |
| everything else | **Θ(n log n)** |

The engine turns U into 2^{e_K·U}.

* With the pieces of Theorem B of [A] (ρ = 1/√2, α′ = ½), e_K = Θ(1/√log K), and the rest of the
  plane costs 2^{Θ(n√log n)}.
* The pieces framework forces ρ ≥ 1/2 (`permanent/rate.md` §0, rank argument; the ceiling is
  2^{O(U/log U)}). Theorem A(a) gives e_ℓ ≥ ½ρ^ℓ ≥ ½·2^{−ℓ} ≥ 1/(2(log K_ℓ + 2x₀)). The argument of
  `barrier.md` Lemma 2.1 then gives E(N) ≥ U/(2(log U + 2x₀)), which is ≥ (½ − o(1))·n by
  Theorem B.

**So no choice of pieces makes the engine subexponential off 𝓗 ∪ 𝓛;** at best it reaches
2^{Θ(n)}, with an unknown constant. The true dividing line is the exponent of the *clique
algorithm*. Suppose some algorithm evaluated (K,λ)-cliques in 2^{e K²λ} with e = o(1/log K) at
K = n^{Θ(1)}, which Lemma 2.2 of `barrier.md` does not exclude (it only forces e ≳ 1/K). Then
Proposition P3 plus Lemma 8 would give **2^{o(n)} for the whole Tutte plane on sparse graphs**,
because U* = O(n log n) everywhere.

### 4.2 Contrast with Hamiltonian cycles (the escape that HC used)

HC partial solutions induce *perfect matchings* on the boundary, not arbitrary partitions. The
matchings-connectivity matrix M_k[M,M′] = [M ∪ M′ is one cycle] on b boundary vertices has rank
4^b/poly(b) over Q (Curticapean–Lindzey–Nederlof, SODA 2018), despite (b−1)!! rows. [Computed] R5:
for b ≤ 8 it has full rank (b−1)!! = 1, 3, 15, 105. These are still below 4^b; CLN show the
rank is 4^b/poly(b) asymptotically. That is why one label of log 5 bits per crossing edge sufficed
for HC. For the Tutte plane the boundary states are *all*
set partitions, every partition is realised by subcubic linear forests (Lemma 3.3), and the rank
is genuinely Bell(b) (Lemma 3.2), so no analogous escape exists. Degree constraints are what made
HC low-rank; Tutte has none.

### 4.3 The y = 1 escape, planarity, and the invariance of q

* On y = 1 only *acyclic* gluings survive (Lemma 3.2(c)), and the cut rank collapses to Catalan(b)
  (computed for b ≤ 7). Catalan(b) is the number of non-crossing partitions. That is the same
  count as for planar gluing, where boundary partitions on a face are non-crossing for *every* q.
  This is the cut-rank shadow of the planar Temperley–Lieb / loop representation: Baxter–Kelland–Wu
  (1976) write the planar Potts model as a local vertex model with complex weights, √q per loop
  realised by local turning angles. So on planar graphs the *whole* plane is local, but planar
  graphs are classically 2^{O(√n)} anyway (Sekine–Imai–Tani 1995; treewidth O(√n)).
* q is invariant under k-stretching, k-thickening and every 2-terminal (tensor-product)
  substitution (Jaeger–Vertigan–Welsh 1990, Brylawski). These are the only gadget moves in all
  known Tutte reductions. So no gadget maps a barrier point onto 𝓗 ∪ 𝓛. This is consistent with
  Theorem B, which depends on (x,y) only through q and through [v = 0].

---------------------------------------------------------------------------------------------------

## 5. Attempts to break the barrier (H4)

| idea | outcome |
|---|---|
| Interpolation over hyperbolas H_1…H_N | Works (P3), but needs N = min(r,nullity)+1 = Θ(n), so q up to Θ(n), so U = Θ(n log n). This matches Thm B, which covers sums of networks on one clustering. For m − n = d small, N = d+1, but then the classical kernel (strip pendant trees, suppress degree-2 vertices into weighted edges, giving ≤ 2d vertices and ≤ 3d edges) is already 2^{O(d)}. |
| Degree bounds on T (deg_x ≤ r, deg_y ≤ nullity) | Only reduces the count of hyperbolas to min(r, nullity)+1 (I8). No sub-logarithmic colour count. |
| Modular arithmetic: T mod p, CRT, p-adic | Locally T mod p costs log p bits per vertex (§2.4). A network valued in ℤ/M must factor M_q over ℤ/M. The minimal inner dimension is the number of invariant factors (q)_{|S|} ≢ 0 mod M, at least max_{p∣M} rank_{F_p}. For p^k, v_p((q)_j) ≈ j/(p−1), so all |S| < (p−1)k survive. Exact recovery needs M ≥ 2^{Ω(m)}, so either primes up to Θ(m) or k(p−1) ≥ b. Either way U = Θ(n log n). [Proved by the Smith-form argument; no new script.] |
| Deletion–contraction plus the engine | Branching moves along the graph, not along the point (q is fixed). It is a sum of networks on one clustering, covered by Thm B up to 2^{o(n log n)} branches. |
| Activities with a local edge order (T = Σ_trees x^{ia}y^{ea}) | The matrix-tree fermions give trees locally, but internal and external activity read the fundamental cut or cycle, which is global. Any vertex-local encoding would contradict Thm B at, for example, (1,2) or (3,½). |
| Fermionic / determinantal tricks on x = 1 (T(1,2)) | Ruled out *within Model V*: rank_Q C = Bell(b). Only τ-weighted counts (Σ_A τ(A)v^{|A|}) and counts mod p are local. **H2 answered: exact on y = 1, impossible on x = 1 in this model.** |
| Sums of networks with *different* clusterings | **Not covered.** Lemma 3.1 needs a cut that is a union of clusters for every summand. This is the analogue of sums of ROABPs in different variable orders, where lower bounds are known only for few summands. Open. |
| Skeletons depending on private edges (Gap A) | Not covered, but our constructions do not need this (their skeletons depend only on crossing counts). |
| General model (tables are arbitrary poly-time functions) | No unconditional barrier is possible (`barrier.md` Prop 4.1). "U + ΣP + log τ = o(n)" is equivalent to a 2^{o(n)} algorithm. |
| Reduce to sparse #SAT and use [A] directly | Encoding connectivity in CNF needs ≈ n log n auxiliary variables (parent pointers), giving 2^{O(n log n/√log n)}. This is the same n√log n threshold, as the barrier predicts, since [A]'s CNF network is vertex-local. |

**Single most promising route.** Inside Model V no point resists *both* arguments. Every point
off 𝓗 ∪ 𝓛 has U* = Θ(n log n): the lower bound is Theorem B, the upper bound Proposition P3. So
the whole question is the exchange rate e_K between U and time.

* [A]'s recursion has e_K ≥ 1/(2(log K + 2x₀)) for any pieces (ρ ≥ 1/2), so it is stuck at
  ≥ 2^{(½−o(1))n} there.
* The one concrete route to the major result is therefore a **(K,λ)-clique algorithm with
  exponent o(1/log K)**, breaking [A]'s 2^{O(U/log U)} ceiling. With Proposition P3 (n+1 colour
  networks, U = O(m log n)) it would give 2^{o(n)} at every point, including T(1,2) and T(3,½).
* Nothing information-theoretic forbids it (`barrier.md` Lemma 2.2: e ≥ (K−1)/K² only). The same
  improvement would also be needed for the permanent and dense HC. So it is a question about the
  engine, not about Tutte.

Within today's engine, the formal loopholes of the barrier are sums over many *different*
clusterings and skeletons that depend on private edges. We see no construction exploiting either.

---------------------------------------------------------------------------------------------------

## 6. Literature (what each source actually says)

* **Jaeger–Vertigan–Welsh 1990** (Math. Proc. Camb. Phil. Soc. 108:35–53). T is #P-hard at every
  (x,y) ∈ ℂ² except on H_1 and at (1,1), (−1,−1), (0,−1), (−1,0), (i,−i), (−i,i), (j,j²), (j²,j)
  (j = e^{2πi/3}), where it is poly-time. [Cited, standard.] All exceptional points lie on H_1–H_4
  or are (1,1) ([Computed] I7).
* **Björklund–Husfeldt–Kaski–Koivisto FOCS 2008.** T_G at every point in 2^n·poly(n), that is,
  vertex-exponential. This is the best general classical bound, also for sparse graphs. [Cited.]
* **Dell–Husfeldt–Marx–Taslaman–Wahlén, TALG 10(4) 2014** (ICALP/IPEC 2010; checked on arXiv
  1206.1775, Thm 1.4). Under #ETH, rational (x,y):
  * (1) multigraphs: no exp(o(n)) if (x−1)(y−1) ≠ 1 and y ∉ {0, ±1};
  * (2) simple graphs, y = 0: no exp(o(n)) for x ∉ {0, ±1};
  * (3) simple graphs, x = 1: no exp(o(m/log² m)) for y ≠ 1;
  * (4) simple graphs: no exp(o(m/log³ m)) if (x−1)(y−1) ∉ {0,1} and
    (x,y) ∉ {(−1,−1), (−1,0), (0,−1)}.
  * The line y = 1 is left open. Ising: the coefficients of Z(G;2,·) take exp(Ω(m)).
  [Cited.] **In the refutation world #ETH is false** (the engine counts #SAT), so these bounds are
  vacuous; their reductions use stretching and thickening, which preserve q (§4.3).
* **Brand–Dell–Roth, IPEC 2016 / Algorithmica 2019** (arXiv 1606.06581). Counting forests, that is
  T(x,1) for x ≠ 1, has no exp(o(n)) algorithm under #ETH. This closed the #ETH dichotomy for the
  Tutte plane. [Cited.] Again vacuous here, and our P2 is the positive counterpart.
* **Groenland–Mannens–Nederlof–Szilágyi, STACS 2022** (arXiv 2110.02730; the authors are
  Groenland, Mannens, Nederlof and **Szilágyi**, not Piecyk–Rzążewski, who wrote the ICALP 2024
  homomorphism/cutwidth follow-up).
  * Counting list q-colourings mod p: (q−1)^{ctw} when p | q−1, with matching SETH lower bounds.
  * Connected spanning edge sets **mod p**: p^{tw}·poly, and no (p−ε)^{ctw} under SETH.
  * All of this is modular. The compatibility-matrix ranks are over F_p; nothing is claimed for
    exact counting. [Cited, from the arXiv text.] This matches Lemma 3.2(b): rank_{F_p} C ≈ p^b,
    against Bell(b) over Q.
* **Curticapean–Lindzey–Nederlof, SODA 2018** (arXiv 1709.02311). The matchings-connectivity
  matrix has rank 4^k/poly(k) over Q, giving tight (6−ε)^{pw} SETH bounds for counting HC. Over F_2
  the rank is Θ(√2^k) (Cygan–Kratsch–Nederlof STOC 2013). [Cited.]
* **Lindström 1969 / Wilf 1968.** det[f(P∨Q)] = Π g over semilattices, which is the factorisation
  of Lemma 3.2. **Freedman–Lovász–Schrijver, JAMS 2007; Lovász, *Large networks and graph limits*
  2012.** Connection matrices; the chromatic polynomial at non-integer q has connection rank
  Bell(k). [Cited from memory, consistent with R1.]
* **Sokal 2005** (Surveys in Combinatorics), the multivariate Tutte / Potts form (1.1).
  **Caracciolo–Jacobsen–Saleur–Sokal–Sportiello, PRL 93 (2004) 080601**: fermionic field theory
  for trees and forests, which is the q → 0, v ∝ q limit, that is, y = 1 (§2.3). [Cited.]
* Treewidth and cutwidth upper bounds for Tutte points:
  * exact DP with Bell(tw)-type states (Noble 1998; Andrzejak 1998);
  * q^{tw} on H_q (colourings);
  * the sparse-graph treewidth bound tw ≤ m/5.769 + O(log n) (Kneis–Mölle–Richter–Rossmanith 2009)
    and pw ≤ n/6 + o(n) for cubic graphs (Fomin–Høie 2006).
  On sparse graphs the exact treewidth DP (2^{O(tw log tw)}) is *worse* than 2^n, which is the
  classical face of the Bell barrier. [Cited from memory; not re-checked online.]
* "Brennan–Hollingsworth": not identified. No source by these names on the Tutte polynomial was
  found, so nothing is attributed to it.

---------------------------------------------------------------------------------------------------

## 7. Status checklist

Proved here:
* Theorem P1 (conditional on [A]; HC-note bookkeeping with log q in place of log 5) and P3.
* Lemmas 3.2–3.4, Proposition 3.5 and Theorem B with Corollary B′ (unconditional, Model V, common
  clustering).
* The H_q sharpness Θ(n log q), and the Smith-form remark on modular routes.
* The Grassmann upper bound 2^{2b−1} for y = 1 gluings.

Imported:
* [A]'s Lemma 8 and Theorems A and B (positive side only).
* `barrier.md` Lemma 2.1 (engine exponent).
* lem:forest from the paper, for P2 (written proof; its network values were checked by
  `ext_problems.py`).

Computed (exact): I1–I8, N1–N7, R1–R5 (`tutte_ranks.py`: R1–R3 for b ≤ 6, R4 for b ≤ 4) and the connected-family ranks
(b ≤ 4; b ≤ 3 at x = 0); see the `*.out` files.

Conjectured or open:
* rank A_u = Catalan(b) for all b (checked for b ≤ 7).
* Sums of networks with different clusterings.
* Skeletons that depend on private edges.
* Whether a clique algorithm with exponent o(1/log K) exists. This is outside [A]'s pieces
  framework, whose ceiling is ρ = 1/2, giving 2^{Θ(n)} at best off 𝓗 ∪ 𝓛. It would make the
  whole plane 2^{o(n)} on sparse graphs.
