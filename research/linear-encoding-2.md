# Linear signed encodings, part 2: drawings, surfaces and gap gadgets

Status (2026-11-04). This continues `linear-encoding.md` (cited as [LE1]). **No linear-size encoding
for general bounded-degree graphs is constructed.** What is new, proved and checked exactly:

1. **Theorem D (any drawing).** For every generic straight-line drawing `D`,
   `c(η) ≡ Σ_v N_v(η) + Q_D(x(η)) (mod 2)`. Here `N_v` is a local "passes north" bit, and `Q_D` counts
   crossing pairs of mixed edges. Two drawings differ only by local terms on valid inputs, so the
   *function* complexity does not depend on the drawing. Planar graphs get a linear encoding, and a
   drawing with `cr` crossings gives size `O(m + cr)`.
2. **Theorem J (surfaces).** For a graph cellularly embedded in `S_g`, `c(x) ≡ W(x) + q(Hx)`. Here `W` is
   local, `Hx ∈ (Z/2)^{2g}` is the homology class, and `q` is a quadratic refinement of the
   intersection form (Johnson's spin quadratic form). The resulting size is `O(m(1+g))`.
3. **Theorem G (gap gadget, the main new lead).** Suppose `F : turns → GF(2)^k` is *nowhere-zero*, that is,
   `F(C) ≠ 0` for every directed cycle of `G − r`. Then a signed CNF of size `O(k·m)` (bounded degree)
   satisfies `gap = n·#HC(G)`. The invariant `k*(G)` (the least such `k`) has the following properties:
   * it is `1` iff `G − r` is planar;
   * it is minor-monotone;
   * it is at most `g+2` and at most `1 + rank/2` of any crossing form;
   * it is unbounded, by a Ramsey argument (`Ω(log log log n)` on expanders);
   * it equals `2` on K5, K3,3, K6, K7, K4,4, K4,5, Heawood and most random cubic graphs with
     `n ≤ 20`, and `3` on one cubic graph with `n = 18`.

   **The open statement is:** *is there an efficiently computable nowhere-zero labelling with
   `k = o(√log m)` for every bounded-degree graph?* If so, the labs' top-level theorems give #HC in
   `2^{o(m)}`. If `k = O(1)`, they give `2^{O(m/√log m)}`.

Scripts (standard library only, each prints PASS/FAIL, outputs in `.out`):
`research/scripts/linenc2_lib.py`, `linenc2_A_drawing.py`, `linenc2_B_rank.py`,
`linenc2_C_surface.py`, `linenc2_D_gadget.py`. The values of `k*` were computed with a SAT solver
(python-sat, used only as a search tool). The helper scripts for that are `z2k_sat.py`, `zp_sat.py`,
`grp_sat.py` and `cubic_k.py`, and they are in the session scratchpad, not in the repo. Every solution found was re-checked in plain Python against
all cycles, and the UNSAT answers are labelled as solver results.

---

## 1. Theorem D: the sign from an arbitrary straight-line drawing

**Setting.** A drawing `D` puts vertex `v` at a point `P_v ∈ Z²` and every edge on a straight segment.
It is *generic* if:
* the x-coordinates are distinct, so no edge is vertical;
* no three points are collinear, so no vertex lies on a non-incident edge and two edges sharing a
  vertex meet only there;
* no three edges pass through one crossing point.

For a valid labelling `η` the mixed arcs form vertex-disjoint directed cycles of length `≥ 3`.
* They avoid `r`: no monomial mentions `r`.
* The other vertices are fixed points (labels `D_v` or `one`) and lie on no mixed arc.
* Each mixed vertex `v` has a unique `pred(v)` (its ψ-giving in-arc) and `succ(v)` (its ψ̄-giving out-arc).

**Definition.** For a mixed vertex `v` with `u = pred v` and `w = succ v`, put `d₁ = P_v − P_u` and
`d₂ = P_w − P_v`, and let `κ = det(d₁,d₂) ≠ 0`. The local bit is

  `N_v := [κ>0 ∧ d₁ₓ>0 ∧ d₂ₓ<0] ∨ [κ<0 ∧ d₁ₓ<0 ∧ d₂ₓ>0]`,

which says whether the short turn (`|angle| < π`) from direction `d₁` to direction `d₂` sweeps
through north `(0,1)`. `N_v` depends on the drawing and on the *ordered* pair (in-edge, out-edge), so it
is a function of the local primary variables at `v` (`b_{e,v}`, `p_{e,v}`). Put
`Q_D(x) := #{ {e,f} : x_e = x_f = 1, |e ∪ f| = 4, the segments e, f cross } mod 2`.

**Theorem D.** `c(η) ≡ Σ_{v mixed} N_v(η) + Q_D(x(η)) (mod 2)`, hence
`κ(η) = (−1)^{c(η)} = Π_v (−1)^{N_v} · (−1)^{Q_D(x)}`.

*Proof.* Take a mixed cycle `γ = (v₁ → … → v_L)` drawn as a closed polygon, and smooth every corner
inside a disc of radius `ε` around `v_i`.
* The discs meet no other edge, by genericity, so smoothing creates or destroys no intersection.
* The tangent direction is constant on the segments and is never north, since no edge is vertical.
* At the corner `v` the direction sweeps the short arc from `d₁` to `d₂`. The arc is short because
  `u ≠ w` and `u, v, w` are not collinear, so the turn is never `±π`.

The rotation number `rot(γ)` is the degree of the tangent map `γ → S¹`. It equals the signed number of
times the direction passes north, so `rot(γ) ≡ Σ_{v∈γ} N_v (mod 2)`.

The smoothed polygon is a normal closed curve. Its double points are exactly the proper crossings
of two non-adjacent edges of `γ`. Adjacent edges meet only at their common vertex, and no three edges
are concurrent. Whitney's theorem gives `rot(γ) ≡ 1 + sc(γ) (mod 2)`.

Two distinct mixed cycles are vertex-disjoint closed curves in general position, so they cross an even
number of times (Jordan curve theorem). Hence
`Q_D(x) ≡ Σ_γ sc(γ) + Σ_{γ<γ'} cr(γ,γ') ≡ Σ_γ sc(γ)`. Summing `1 ≡ rot(γ) + sc(γ)` over the `c` cycles
gives `c ≡ Σ_v N_v + Q_D`. The root and the fixed points carry no mixed arc and contribute nothing.
Pairs of edges sharing a vertex never cross, so they are correctly excluded from `Q_D`. ∎

[LE1, Lemma W] is the case of a convex drawing. There `N_v` becomes `ρ_v` after a rotation of the
reference direction (both are `≡ rot`, by the same argument).

**Corollary D1 (drawing invariance).** For two generic drawings `D, D'` of `G`,
`Q_D(x) ⊕ Q_{D'}(x) = Σ_v (N_v ⊕ N'_v)` on every valid `x`. So, up to `O(m)` local gates, all drawings
define *the same function* on valid inputs: the parity of `c`. Choosing a drawing cannot change the
circuit complexity of that function. It can only change how well a particular construction (rank,
sparsity, factorisation) works.

**Corollary D2.**
* A planar `G` with a Fáry drawing has `Q_D ≡ 0`, so `(−1)^c` is a product of local signs. That gives a
  linear-size signed CNF.
* In general the size is `O(m + cr(D))`: one AND gate per crossing pair.
* Bounded-degree expanders have `cr(G) = Θ(n²)`, since `cr + n ≥ Ω(bw²)` (Leighton). So this gives
  nothing for them. For planar graphs nothing is gained either: they already have `2^{O(√n)}`
  algorithms.

**Verification** (`linenc2_A_drawing.out`, **ALL PASS**):
* 150 random graphs (`n ≤ 9`) with random generic integer drawings, 11 134 valid labellings:
  * `κ = (−1)^c` (Koszul sign, 60 graphs);
  * Theorem D;
  * Corollary D1 with a second drawing.
* All 14 208 vertex-disjoint directed cycle systems of `K_5, K_6, K_7` under 12 random drawings.

Ablations (both must fail somewhere, and both do):
* dropping `N` is wrong on 1666 labellings;
* dropping `Q` is wrong on 310 labellings.

## 2. The matrix formulation, and crossing matrices of drawings

Following the coordinator's reformulation, take `U_D` to be the upper-triangular crossing matrix (in a
fixed edge order). Then `Q_D(x) = ⟨x, U_D x⟩`, and its cost is `L(U_D) + O(m)`, where `L` is the GF(2)
linear circuit complexity. (Mirwald–Schnorr: a degree-2 form needs only `m + O(n)` AND gates, so all of the
difficulty is in the XOR part.) The free moves that leave the function unchanged on valid `x` are:

* **star moves** `U ← U + e ⊗ δ(v)` with `v ∉ e`. On valid `x`, `δ(v)·x = #mixed edges at v ∈ {0,2}`, so
  `x_e·(δ(v)·x) ≡ 0`. This is a vertex dragged across an edge.
* **adjacent entries** `(e,f)` with `e ∩ f ≠ ∅`: these are local ANDs, `O(m)` in total for bounded degree.
* **restriction to the cycle space.** Valid `x` lie in `Z(G)`. Fix a spanning tree `T` and write
  `x = Z_T y`, where `y = x|_{E∖T}` is a sub-vector, so it costs nothing to form. Then
  `Q_D(x) = y^T M_T y` with `M_T := Z_T^T U_D Z_T` of size `(m−n+1)²`. Star moves vanish identically on
  `Z`. The off-diagonal entry `(e,f)` of `M_T + M_T^T` is the crossing parity of the fundamental cycles
  `C_e` and `C_f`. By Jordan, this equals the local "cross versus touch" pattern of the two cycles where
  their shared tree path ends. So `M_T` is an interlacement matrix: compare Cohn–Lempel/Traldi,
  `#cycles = 1 + nullity(interlace matrix)`.

So the target is a single matrix-complexity statement:

> **(M)** For bounded-degree `G`, does some drawing `D` and some tree `T` give
> `L(M_T) = O(m)`, or `L(U_D + star moves + adjacent part) = O(m)`?

**Rank experiments** (`linenc2_B_rank.out`). The table gives `rank_{GF(2)} C_D` (with
`C_D = U_D + U_D^T`), minimised by hill-climbing within each drawing family, for random cubic graphs.
The circuit cost is `O(m · rank)`. The families are:
* convex: a vertex order;
* 2 lines and 3 lines: vertices on parallel lines. Each line is a very flat convex arc, to stay
  generic. This is the 2- or 3-page/level picture;
* random points;
* a 6×6 cluster grid;
* two nested parabolas: the concentric-circles analogue;
* DFS-convex: the DFS order of a spanning tree, so the tree is drawn crossing-free.

`rank*` adds greedy star moves and adjacent-entry flips to the best drawing found.

| n | m | convex | 2 lines | 3 lines | random | grid | 2 parab. | DFS-convex | rank* (best) | m/2 |
|---|---|---|---|---|---|---|---|---|---|---|
| 8 | 12 | 4 | 4 | 0 | 0 | 0 | 0 | 4 | 0 | 6 |
| 8 | 12 | 2 | 2 | 0 | 0 | 0 | 2 | 4 | 0 | 6 |
| 12 | 18 | 4 | 6 | 4 | 4 | 6 | 4 | 6 | 4 | 9 |
| 12 | 18 | 6 | 4 | 4 | 4 | 6 | 2 | 4 | 2 | 9 |
| 16 | 24 | 8 | 10 | 8 | 6 | 10 | 8 | 8 | 6 | 12 |
| 16 | 24 | 8 | 10 | 6 | 4 | 8 | 6 | 6 | 4 | 12 |

The script is set to cover `n = 24, 32, 48` as well. The run finished (37 min, exit code 0), but it
printed no rows past `n = 16`. The most likely cause is that those writes failed while the temp
volume was full, but that is not confirmed. The rows above are everything the run printed. The star-move
sanity check (star moves leave `Q_D` unchanged on every valid labelling) passed.

Reading the table: across every family, the minimum rank grows **linearly**, at about
`m/4` to `m/3`, with no family clearly better. That is the expected behaviour: the minimum crossing
rank is the Schaefer–Štefankovič / Fulek–Kynčl `Z₂`-genus (a minimum rank of partial symmetric matrices
up to star moves), and that is `Θ(m)` for expanders. The DFS-convex drawing, with the tree planar
and the chords arbitrary, is no better than random orders.

On the other questions (few sparse factors, sparse plus low rank), no exhaustive test is feasible
beyond toy sizes. The star and adjacent moves are exactly a sparse correction, and they cut the rank
only by about 1/3. For every structured family the crossing predicate of two segments is decided by
the order relations of `O(1)` coordinates per edge. On a page or a line it is interleaving or inversion,
which is 2D dominance. On `k` lines it is a union of `O(k²)` dominance patterns. Every known linear
circuit for such a matrix is a range tree, with `Θ(m log m)` gates. A drawing in which crossings are
"governed by few coordinates" is exactly a semi-algebraic range-searching matrix of bounded description
complexity. No `o(m log m)` GF(2) linear circuit is known for any non-trivial such family. (Lower
bounds for offline range counting exist only in monotone/semigroup or bounded-coefficient models,
from Chazelle's work; there is none for XOR circuits.)

## 3. Surfaces: Johnson's quadratic form makes the global part `2g`-dimensional

On an orientable surface the Jordan argument fails for non-separating curves. The repair is not the
bilinear form `Σ_{C<C'} ω(h_C,h_{C'})`: that is `0` here anyway, because distinct mixed cycles are
disjoint embedded curves. The repair is its **quadratic refinement**.

**Theorem J.** Let `G` be cellularly embedded in a closed orientable `S_g` (a rotation system, no
crossings). Choose a smooth vector field `ξ` with zeros only inside faces, each face of even total
index. This is possible because `χ = 2 − 2g` is even. Combinatorially: local edge directions at each
vertex, plus edge twists `k_e ∈ GF(2)` solved so that every face boundary has odd winding. Let `W(C)` be
the winding of a directed cycle relative to `ξ`. Mod 2, `W` is a sum of per-edge and per-corner "passes
north" bits, so it is **local**. Then there is a quadratic form `q` on `H₁(S_g; Z/2) = (Z/2)^{2g}` with
`q(a+b) = q(a)+q(b)+a·b` such that, for every disjoint system `x` of directed cycles,

  `c(x) ≡ W(x) + q(Hx)`, where `Hx = Σ_C [C] = (⟨x, α_i⟩)_{i≤2g}` is linear in `x`.

*Proof.* Johnson (1980) showed that, for a spin structure given by such a `ξ`, the function
`q(Σ_i [γ_i]) := Σ_i (wind_ξ(γ_i) + 1)`, defined on disjoint simple closed curves, is well defined on
`H₁(S;Z/2)` and is a quadratic refinement of the intersection form. Mixed cycles are disjoint simple
closed curves in `S_g`, so `q(Hx) = W(x) + c(x)`. ∎

The point is that `Σ_C 1 = c` is recovered as `q(ΣC) − Σ_C wind(C)`. The quadratic form absorbs the
"+1 per component" that a bilinear form cannot express. (That is why the guess `½[ω(Σh,Σh) − Σω(h,h)]`
was ill-defined.)

**Cost.** Choose cocycles `α_1..α_g, β_1..β_g` that are symplectically dual (tree–cotree: each is a
cotree path plus one leftover edge). Then `q(Hx) = Σ_i α_i(x)β_i(x) + Σ_i (q(a_i)α_i(x) + q(b_i)β_i(x))`.
This costs `Σ|supp α_i| + Σ|supp β_i| + O(g) ≤ O(g·(f+1))`, and the total is `O(m + g·m)`.
* Bounded genus gives a linear encoding.
* Every bounded-degree graph has genus `≤ (m−n+1)/2`, and expanders have genus `Θ(m)`, which gives
  `O(m²)`.
* Graphs of genus `g` already have `2^{O(√(gn))}` algorithms (separators), so **Theorem J has no new
  algorithmic consequence**. What matters is rank or linear complexity, not `g`. It does supply the
  bound `k* ≤ g+2` in §4.

Non-orientable surfaces would need Pin⁻ structures and `Z/4`-valued Brown forms. That case was not pursued.

**Verification** (`linenc2_C_surface.out`, **ALL PASS**). There were 70 random graphs with random
rotation systems, of genus 0–5, with exact rational angles:
* (a) the local north-bit sum equals the exact winding mod 2 (6198 cycles);
* (b) `1 + W(C)` depends only on `[C]`;
* (c) a quadratic fit exists, and its polarisation has full rank `2g` whenever all classes occur;
* (d) `c ≡ W + q(Hx)` on all 7194 disjoint cycle systems;
* (e) the planar case `g = 0` is `c ≡ W`.

Ablation: `W` alone is wrong on 3780 systems.

## 4. Gap gadgets (Loophole 2)

### 4.1 Mahajan–Vinay and transfer matrices

For `A = P_π`, every clow is forced to follow `π`, and the head occurs only once. So the only clow
sequence is the cycle cover itself, with heads equal to the cycle minima, and MV's sum has one term.
The non-local datum *is* "the head is the minimum of its cycle". Removing the head ordering leaves a sum
over marked vertices per cycle. A signed marked sum `Σ_{∅≠S⊆C} (−1)^{|S|} = −1` would be perfect, but
"every cycle is marked" is again a connectivity constraint. Any local automaton along a cycle gives
`tr(Π_{v∈C} T_v)`. With the same `T` at every vertex this is `Σλ_i^L`, and `−1` for all `L` would need
an eigenvalue of multiplicity `−1` (generating-function argument), as in [LE1, §4.3].

**But the `T_v` may depend on the turn.** The weight of a cycle is then the trace of a holonomy, and
it is enough that `tr ρ(hol C) = −1` for every cycle.

### 4.2 Theorem G: nowhere-zero turn labellings

A *turn* is `(v, e_in, e_out)` with `e_in ≠ e_out` edges at `v`. For `F : turns → GF(2)^k`, put
`F(C) = ⊕_{turns of C} F`. `F` is *nowhere-zero for r* if `F(C) ≠ 0` for every directed simple cycle
`C ⊆ G − r`.

**Theorem G.** If `F` is nowhere-zero for `r`, then

  `n·#HC(G) = Σ_{η valid} Σ_{χ} (−1)^{Σ_v χ(v)·F_v(η)}`,

where `χ` assigns to every mixed edge a colour in `GF(2)^k ∖ {0}`, equal on the in-arc and the out-arc
at every mixed vertex. This gives a width-3 CNF with output bit `z` and `gap = #(φ∧¬z) − #(φ∧z)` of
size `O(m) + O(k·Σ_v d_v²)`, that is `O(k·m)` for bounded degree. It is made of:
* [LE1, §5]'s primary, edge and vertex clauses;
* `k` colour bits per edge, forced to `0` on non-mixed edges, with the colour nonzero and equal along arcs;
* `z = ⊕_v ⊕_i χ_i ∧ F_{v,i}(turn)`, where `F_{v,i}(turn)` is a lookup table on the `O(d_v²)` (in, out) pairs.

*Proof.* The colour is constant on each mixed cycle and free across cycles. The weight factorises, and
`Σ_{χ≠0} (−1)^{χ·y} = −1` for `y ≠ 0`. So each cycle contributes `−1`, the total is `(−1)^{c(η)}`, and
[LE1, Lemma S2] and §1 finish the proof. ∎

(This is the abelian, 3-colour case of "`tr ρ(hol) = −1`". For `k = 2` it is the 3-dimensional
representation of `A₄` restricted to `V₄`: diagonal `±1` matrices of trace `−1`. The 2-dimensional
`Z/3` representation `[[0,−1],[1,−1]]` gives the analogous criterion over `Z/3`, which fails on
`K_{4,4}`, `K_7` and Heawood. The `S₃` criterion (holonomy a 3-cycle) also fails on `K_{4,4}` and Heawood.)

**Verification** (`linenc2_D_gadget.out`, **ALL PASS**).
* (a) `k = 1` labellings exist for planar graphs, and do not exist for `K₅`, `K_{3,3}`, their
  subdivisions, or random supergraphs of them. This is an exact GF(2) linear system.
* (b) For 40 random graphs (`n ≤ 8`, random root), a `k = 2` labelling was found by local search. Then,
  for every one of the 4376 valid labellings, the explicit sum over colourings equals `(−1)^c`, and the
  total is `n·#HC`.
* (c) The Ramsey witness below.

### 4.3 The invariant k*(G)

`k*_r(G)` is the least `k` for which a nowhere-zero labelling for `r` exists. Facts:

1. **`k* = 1` iff `G − r` is planar.** (⇐) Theorem D with a Fáry drawing: every cycle has
   `Σ N_v = 1`. (⇒) Use Kuratowski together with the next item and check (a), which shows that `K₅` and
   `K_{3,3}` have no `k = 1` labelling.
2. **Minor-monotone.** For a subgraph, restrict `F`. For a contraction `G/e`, a turn at the merged
   vertex lifts to one turn at `u` or `v`, or to two turns joined by `e`, and `F` of the lift serves.
   Hence `k*(G) ≤ k*(K_n)`, and by Robertson–Seymour each class `{k* ≤ k}` is characterised by finitely many
   excluded minors (for `k = 1`: `K₅`, `K_{3,3}`).
3. **`k* ≤ g + 2`** (orientable genus `g`). Take `F = (W, ℓ_1..ℓ_j)`, where the `ℓ_i` are cocycles
   cutting out a `q`-singular subspace `K` (so `j = 2g − dim K ≤ g+1`). If `F(C) = 0`, then `[C] ∈ K`, so
   `q([C]) = 0`, and `W(C) = 0`. That contradicts `W(C) = 1 + q([C])` (Theorem J). Similarly, if
   `Cross ≡ Σ_{j≤s} a_j b_j` (rank `2s`), then `F = (Σρ, a_1..a_s)` works, so **`k* ≤ 1 + rank/2`**.
4. **Unbounded.** Colour each 3-set of `K_t` by the values of `F` on its 6 turns. Hypergraph Ramsey gives
   an `F`-homogeneous 6-set `S`, on which `F(turn)` depends only on the order type of the turn. The
   cycle `(0,1,3,5,2,4)` uses each of the 6 order types an even number of times (check (c); 6 is the
   least size for which this happens), so `F(C) = 0`. Hence `k*(K_t) > k` once
   `t ≥ R₃(6; 2^{6k})`, which is at most triply exponential in `k` (Erdős–Rado). So
   `k*(K_t) = Ω(log log log t)`. Bounded-degree expanders have `K_t` minors with `t = Ω(√(n/log n))`
   (Krivelevich–Sudakov), so by item 2 `k* = Ω(log log log n)` on expanders too.
5. **Computed values** (all cycles, no root; CaDiCaL via python-sat, with solutions re-verified):

| graph | genus | directed cycles | k* | (Z/3, 2-dim rep) | (S₃) | (A₄ ⊃ V₄) |
|---|---|---|---|---|---|---|
| K₅, K₃,₃ | 1 | 74, 30 | 2 | yes | – | – |
| K₆ | 1 | 394 | 2 | yes | – | – |
| K₄,₄ | 1 | 408 | 2 | **no** | no | yes |
| Heawood | 1 | 426 | 2 | **no** | no | yes |
| K₇ | 1 | 2344 | 2 | **no** | – | – |
| K₄,₅ | 2 | 1320 | 2 | – | – | – |
| random cubic, n = 10…16 (12 graphs) | – | 102–688 | 1 (planar ones) or 2 | – | – | – |
| random cubic, n = 18 (3 graphs) | – | 1230, 832, **1448** | 2, 2, **3** | – | – | – |
| random cubic, n = 20 | – | 2346 | 2 | – | – | – |

The `k* = 3` entry rests on a solver UNSAT answer for `k = 2` (2196 s). It is the graph `rep2` at
`n = 18` from `random_regular(·,3, Random(11))`, the third graph generated in that sequence. `K₅,₅`
and `K₈` were still running when the session's disk filled up.

So the small cases sit at `k* = 2`, with one cubic graph on 18 vertices that needs `k* = 3`.
`K_{4,5}` (genus 2) already beats the bound `g + 2 = 4`. **There is growth, but it is slow.**

### 4.4 What a constant or slowly growing k* would and would not give

* By item 2, `{k* ≤ k}` is a proper minor-closed class. It excludes some `K_{t(k)}`, and so has
  `O(√n)`-separators. For such graphs `#HC` is already `2^{O(√n)}` by DP. **So `k* = O(1)` cannot hold for
  all bounded-degree graphs (item 4), and where it holds it gives nothing new.**
* What would matter: `k*(G) ≤ κ(m)` with `κ(m) = o(√log m)` (Anthropic `MainTheorem`) or
  `o(√log m/(log log m)²)` (OpenAI), for **every** bounded-degree `G`, **with an `F` computable in time
  `2^{o(m)}`**. The encoding then has `O(m·κ)` variables, and [LE1, §6] gives `#HC` in `2^{o(m)}` from the
  top-level theorems alone.
* The best upper bounds known here are `k* ≤ min(g+2, 1 + rank*/2) = Θ(m)` for expanders. The best lower
  bound is `Ω(log log log m)`. So the truth is completely open, anywhere between those two. The single
  measured jump (`k* = 3` at cubic `n = 18`) gives no usable growth rate. A random `F` needs `k ≈ log₂ #cycles = Θ(m)`. The small cases succeed
  far beyond that first-moment prediction: for cubic `n = 18` there are 1230 cycles, and the first moment
  predicts about `2^{216}·(3/4)^{1230} ≈ 2^{−295}` solutions for `k = 2`. So the solutions are structured.
  No structure was identified.

## 5. Verdict

**Not constructed.** Both loopholes reduce to one statement each, and they are related:

* **Loophole 1 (drawings):** all drawings give the same function up to `O(m)` (Corollary D1). What is
  left is the matrix statement **(M)**, that is, whether the crossing/interlacement matrix of some drawing has
  an `O(m)` GF(2) linear circuit. The rank is `Θ(m)` in every family tried. Structured families reduce to
  dominance matrices, whose best circuits are `Θ(m log m)`. Surfaces help only for genus `o(1)`-relative
  sizes (`O(m(1+g))`).
* **Loophole 2 (gap gadgets):** the new and sharper target is the following.

> **Open (N).** For every bounded-degree graph `G` (and a root `r`), is there a turn labelling
> `F : turns → GF(2)^k` with `F(C) ≠ 0` on every directed cycle of `G − r`, with `k = o(√log m)` and `F`
> computable in time `2^{o(m)}`?

A yes answer gives a signed CNF with `O(m·k)` variables (Theorem G), and hence `#HC` in `2^{o(m)}`
through the top-level theorems alone. `k*` is minor-monotone, equals 1 exactly on planar graphs, equals 2 or 3 on
the small nonplanar graphs tested, and is unbounded (Ramsey). (N) and (M) are incomparable as stated.
A rank-`2s` decomposition of the crossing form gives both `k ≤ s+1` and a circuit with `O(ms)` gates.
An `O(m)` linear circuit for `U_D` does not obviously give a small `k`, and a small `k` gives no circuit at
all, only a gap formula.
