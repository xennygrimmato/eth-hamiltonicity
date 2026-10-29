# Dense graphs with simple structure: exact #HC, #PM and per for "low rank + sparse"

29 Oct 2026. Read after `hc-degree-theorem.md` (cited as [HD]), `exact-hc-theorem.md` ([HC]),
`permanent/wild-ideas.md` (E1, E2), `permanent/barrier.md`, `anthropic-api.md`. Conventions as there: log = log₂,
the engine is Lemma 8 + Theorem A(b) + Theorem B of [A], and every algorithmic statement below is **conditional
on (H_A)** exactly as [HD] Theorem A is. The identities and the n^{O(r)} counts are unconditional.
Scripts: `research/scripts/dense_*.py` (run with `python3 -I`), outputs `dense_*.out`; all print ALL PASS.

---------------------------------------------------------------------------------------------------

## 0. Results in one screen

Notation. A ∈ ℤ^{n×n}; HC(A) := Σ_{directed Hamiltonian cycles C} Π_{(i,j)∈C} A_ij (the diagonal is never used).
For an undirected graph G, #HC(G) = HC(A_G)/2 (n ≥ 3). We assume

```
A_ij = L_ij + D_ij  for all i ≠ j,     L = U Vᵀ  (U, V ∈ ℤ^{n×r}),     D sparse,
```

and write n_D = number of vertices incident to supp(D), m_D = |supp D| (arcs), and d̄_D = 2|E_D|/n_D the
average degree of the undirected support graph (V_D, E_D) of D (|E_D| ≤ m_D).
The parameter is **rk*(L) := min over diagonal completions of rank_ℚ(L)** (the diagonal is free because no
cycle uses it). For 0/1 graphs: rk* ≤ number of twin classes ≤ neighbourhood diversity, so
"nd ≤ r up to edge edits S" is the special case U = M·B, V = M (M = class indicator, B = type graph with loops),
D = ±1 on the edited pairs.

| # | statement | outer terms | network on supp(D) | verified |
|---|---|---|---|---|
| **T1** (identity) | HC(L+D) = HC(D) + Σ_{R⊆[r]} Σ_{T∈Arb(R)} Σ_d Π_{a∈R}(d_a−1)! [w^d x^0 t_T] Q_{R,T} | Σ_s C(r,s)s^{s−2} ≤ (r+1)^r pairs (R,T); E(r) ≤ (r+1)^r(2n+1)^{3r}(2n_D+1) evaluations | Q_{R,T}: Grassmann + label network, 1+10\|R\| states per D-edge | `dense_lowrank_hc.py`, `dense_locality.py`, `dense_pipeline.py` |
| **T2** (algorithm, (H_A)) | HC(A) in **(r+1)^r (2n+1)^{3r+1} · 2^{C·n_D·log(20e·r·d̄_D)/√log n_D} · poly** (refined encoding); crude encoding: 2^{C·log(11r)(m_D+n_D)/√log n_D} | — | U ≤ 2n_D log(2e d̄_D) + 2n_D log(10r) + g³ | identity yes; network accounting by transfer from [HC]/[HD] |
| **T3** (#PM, haf) | haf(L+D), L = UCUᵀ: (n+1)^r evaluations of the vertex-weighted matching network on supp D | (n+1)^r | 2 states per D-edge | `dense_lowrank_pm.py` |
| C (profiles) | nd-form: #HC = Σ_F D^F Φ_H(prof F); #PM = Σ_M D^M PM_H(c) (closed form) | n^{O(r²)} (HC), n^r (PM) | label = endpoint-class pair | `dense_nd_graphs.py` |

**Best theorem (T2, regime).** Assume (H_A). Directed or undirected Hamiltonian cycles of a graph (or integer
matrix) that is "rank ≤ r up to a sparse perturbation" are counted exactly in
n^{O(r)} · r^{O(r)} · 2^{O(n_D log(r·d̄_D)/√log n_D)}. In particular, for r = O(1) and every graph obtained from
a graph with ≤ r twin classes (e.g. K_n, K_{a,b}, complete r-partite graphs, r cliques joined by bicliques) by
adding/removing a set S of edges whose graph has average degree 2^{o(√log n)} — so **|S| up to n·2^{o(√log n)}
edits, minimum degree of G up to n − 2^{o(√log n)}** — the count takes 2^{o(n)}; with bounded maximum degree of S,
2^{δn} for every δ > 0. r may grow up to r = o(n/log n) for the n^{O(r)} part and r = 2^{o(√log n)} for the
network part. (The crude, fully re-checked accounting gives the same for |S| = o(n√log n / log r).)

What is new and what is not (details §7): the S = ∅ case (HC of a fixed-rank matrix in n^{O(r)}) is in the
spirit of Barvinok (permanent of fixed rank, 1996) and of Barvinok–Johnson–Woeginger (max-TSP of fixed
tropical rank via Eulerian multigraphs); we found no explicit statement for HC counting but would not claim it.
The reduction of the perturbed problem to a *local* sparse quantity is new as far as we can tell, gives
unconditionally n^{O(r)}·2^{n_D}·poly (or n^{O(r)}·2^{O(tw(S) log tw(S))}), and, with the engine,
the first (conditional) 2^{o(n)} counting algorithm for these dense classes. Known FPT algorithms for HC by
neighbourhood diversity, modular-width, cluster vertex deletion are for *decision* and, if one treats the
edited vertices as a modulator, exponential in n_D.

---------------------------------------------------------------------------------------------------

## 1. Theorem 1 (the identity)

Let A_ij = L_ij + D_ij (i ≠ j), L = UVᵀ. A *directed linear forest* F ⊆ supp(D) is a set of arcs with
in- and out-degree ≤ 1 at every vertex and no directed cycle; its *units* are its maximal directed paths
(tail u, head w), an F-isolated vertex v being the unit (v, v). There are n − |F| units.
Arb(R) = in-arborescences of the complete digraph on R ⊆ [r] rooted at min R (|Arb(R)| = |R|^{|R|−2}).

**Theorem 1.**
```
HC(A) = HC(D) + Σ_{∅≠R⊆[r]} Σ_{T∈Arb(R)} Σ_{d∈ℕ^R} Π_{a∈R} (d_a − 1)! · [ w^d x^0 Π_{(a→b)∈T} t_ab ] Q_{R,T}(w,x,t),

Q_{R,T} = Σ_{F directed linear forest ⊆ supp D} D^F Π_{units (u,w) of F} ℓ_{R,T}(u,w),

ℓ_{R,T}(u,w) = α_R(u) β_R(w) + Σ_{(a→b)∈T} t_ab · V_ua w_a x_a · U_wb / x_b,
α_R(u) = Σ_{a∈R} V_ua w_a x_a,          β_R(w) = Σ_{b∈R} U_wb / x_b ,
```
where [w^d x^0 t_T] means the coefficient of w^d, of x_a^0 for every a, and of t_ab^1 for every arc of T
(other t-degrees discarded). HC(D) = Σ over directed Hamiltonian cycles inside supp(D) of D^C.

*Proof.* **Step 1 (expansion over the sparse part).** For a Hamiltonian cycle C,
Π_{e∈C}(L_e + D_e) = Σ_{F⊆C} D^F L^{C∖F}. Exchanging sums, only F ⊆ supp D ∩ C contribute. If F = C this is
HC(D). Otherwise F is a directed linear forest and the cycles C ⊋ F are exactly the cyclic orders of its
units, C ∖ F being the arcs head_i → tail_{i+1}. So HC(A) = HC(D) + Σ_F D^F N_L(F) with
N_L(F) = Σ_{cyclic orders} Π_i L_{head_i, tail_{i+1}} (identity I1).

**Step 2 (labels = Eulerian circuits, BEST).** Expand L_{w,u} = Σ_k U_wk V_uk: every completion arc gets a label
k ∈ [r]; unit i gets in-label a_i and out-label b_i and weight V_{tail_i,a_i} U_{head_i,b_i}; consistency is
b_i = a_{i+1}. Read unit i as an arc a_i → b_i of a multigraph Γ on [r] with distinguishable arcs: the
consistent cyclic orders are exactly the Eulerian circuits of Γ. Hence
N_L(F) = Σ_N ec(N) [z^N] Π_units ℓ(z), ℓ_unit(z) = Σ_{a,b} V_{u a} U_{w b} z_ab, where N ∈ ℕ^{r×r} is the arc
multiplicity matrix. By the BEST theorem ec(N) = t(N) Π_{a∈R(N)} (d_a − 1)! for N balanced (in = out at every
node) and connected on its support R(N), d_a its out-degrees, t(N) the number of in-arborescences of Γ on R(N)
rooted at min R(N); ec(N) = 0 otherwise (identity I2).

**Step 3 (n^{O(r)} coefficient extraction).** Fix R. By the matrix-tree theorem for multigraphs,
Σ_{T∈Arb(R)} Π_{(a→b)∈T} N_ab = t(N) when R(N) = R, and = 0 when N is supported in R but some node of R is
isolated (every arborescence uses an arc at every node when |R| ≥ 2; N ≠ 0 because there is ≥ 1 unit), and
also = 0 when N is not connected on R. So summing over R counts each N once, with the right t(N). For each T,
Π_T N_ab · c_N is the coefficient [t_T] of P(z_ab(1 + t_ab)) (ab ∈ T); the substitution z_ab = w_a x_a/x_b maps
z^N to w^{out(N)} x^{out(N) − in(N)}, so [w^d x^0] keeps exactly the balanced N with out-degree vector d; the
remaining weight Π (d_a − 1)! depends only on d. Restricting labels to R (z_ab = 0 for a or b ∉ R) gives
α_R, β_R. Linearity in F gives Q_{R,T}. ∎

*Remarks.* (i) No 1/N or 1/2 symmetry factors appear: BEST counts cyclic sequences directly. (ii) For r = 1,
L = J: R = {1}, T = ∅, and Theorem 1 is E2 (`wild-ideas.md` §7) for D = −A_{D}; the script checks this.
(iii) For n ≥ 3 and symmetric A, #HC = HC(A)/2.

**Verification** (`dense_lowrank_hc.py`, exact integers, brute force over (n−1)! orders): 10 random instances
n ∈ [4,7], r ∈ {1,2,3}, U,V ∈ [−2,2], m ≤ 9 signed arcs; I1 = I2 = I3 = brute force in all (e.g. n=7, r=3:
−1 560 800); plus 3 E2 instances K_n − D (n = 6,7,8; #HC = 4, 27, 268). Outer pairs printed: 1, 3, 9 (and 38
for r = 4 in `dense_nd_graphs.py`) = Σ_s C(r,s)s^{s−2}. `dense_pipeline.py` runs the algorithm literally —
evaluate Q at the tensor grid, exact Lagrange interpolation, extract — and matches brute force
(n ≤ 6, r ≤ 2; evaluation counts 1135, 2388 = the formula of §2.2).

---------------------------------------------------------------------------------------------------

## 2. Locality: the network that evaluates Q_{R,T}, and the exact accounting

### 2.1 Lemma 2 (Q_{R,T} at a numeric point is a local Grassmann–label sum on supp D)

Fix (R, T) and numbers (w, x, t). For F ⊆ supp(D) with in/out-degree ≤ 1 put τ_v = [indeg_F(v) = 0] (exactly one
such vertex per unit: the tail or the isolated vertex). Then

```
Q_{R,T} = [ε^{n}] Σ_{F: in,out ≤ 1} Σ_{λ: F → Λ} D^F ε^{|F|} det( Lap(F_und) + ε·diag(τ) ) Π_v φ_v ,    Λ = {0} ∪ T,
```

and the coefficients of ε^j, j < n, vanish. Here φ_v depends only on the arcs of F at v and their labels:
isolated v: ℓ_{R,T}(v,v); tail with out-label 0: α_R(v); tail with out-label (a→b): V_va w_a x_a t_ab;
internal vertex: [in-label = out-label]; head with in-label 0: β_R(v); head with in-label (a→b): U_vb/x_b.

*Proof.* Label consistency forces one label per path; the path's weight is then α(u)β(w) (label 0) or
t_ab V_ua w_a x_a U_wb/x_b (label a→b), whose sum over labels is ℓ_{R,T}(u,w). The determinant is E2's
indicator in directed form: by the all-minors matrix-tree theorem det(Lap(F_und) + ε diag τ) =
Σ_{spanning forests R' ⊆ F_und} Π_{trees} (ε Σ_{v∈tree} τ_v), of ε-degree n − |R'|; times ε^{|F|} this has
degree n + |F| − |R'| ≥ n, with equality iff R' = F, i.e. F acyclic (a 2-cycle i→j→i is a double edge, hence a
cycle); then each tree is a directed path or an isolated vertex with Σ τ = 1. ∎ (`dense_locality.py`: 6 random
instances, n ≤ 6, r ≤ 3, exact rationals, lowest coefficients vanish and [ε^n] = Q; ALL PASS.)

The determinant is the Berezin integral ∫ Π_{arcs of F} (1 + (ψ̄_i − ψ̄_j)(ψ_i − ψ_j)) Π_v (1 + ε τ_v ψ̄_v ψ_v)
of [HC] §4 / `exact-count-lowrank.md`: the edge factor has 5 monomials. Vertices outside V_D are isolated in every
F and contribute the global constant Π_{v∉V_D} ℓ_{R,T}(v,v), so **the network lives on the n_D vertices of D
only.** Integrality: multiply each F-arc by X := Π_{b∈R} x_b and each β/U-entry by X (then every unit carries X
exactly once and the total is X^n·Q — n units minus |F| arcs is the unit count), and choose integer
evaluation points; all weights are integers of B = O(n log(n·‖U‖·‖V‖·‖D‖)) bits.

### 2.2 Exact accounting

*Outer terms.* Pairs (R,T): Σ_{s=1}^{r} C(r,s) s^{s−2} = 1, 3, 9, 38, 250 for r = 1..5, ≤ (r+1)^r.
*Interpolation.* Q_{R,T}·Π x^n is a polynomial of degree ≤ n in each w_a (|R| variables), ≤ 2n in each x_a with
x_{min R} := 1 (|R| − 1 variables; the x-exponents of every monomial sum to 0), ≤ n in each t_ab (|R| − 1), and
≤ 2n_D in ε. Evaluations per pair: (n+1)^{s}(2n+1)^{s−1}(n+1)^{s−1}(2n_D+1). Total

```
E(r) = (2n_D+1) · Σ_{s=1}^{r} C(r,s) s^{s−2} (n+1)^{2s−1} (2n+1)^{s−1}   ≤   (r+1)^r (2n+1)^{3r} (2n_D+1).
```
(r = 1: (n+1)(2n_D+1), the same as E2's (m+1)(n+1); `dense_pipeline.py` prints E(2)/(2n_D+1) = 1135 for n = 4.)

*Local alphabet.* One undirected D-edge {i,j} carries: absent, or (i→j or j→i) × label ∈ Λ (|Λ| = |R| ≤ r) × one
of the 5 Grassmann monomials: **σ_r = 1 + 10|R| ≤ 1 + 10r states** (r = 1: 11, against [HC]'s 5 for an
undirected 2-factor; the 2-cycle state "both arcs" is excluded locally). Vertex tables: degree constraints,
label consistency, φ_v, D-weights of out-arcs, X, ε, the Berezin vertex factor — all functions of the states of
δ(v), as in [HC] §5.

*Shared bits, crude encoding* ([HC] §5 verbatim with 5 → σ_r): for a blob partition of V_D into g blobs,
w_ab = ⌈e_ab log σ_r⌉, **U = 2Σ_{a<b} w_ab + 2C(g,3) ≤ 2 log(1+10r)·m_× + g³**, **P ≤ log(1+10r)·μ + 2g²**
(μ = max blob volume, m_× crossing D-edges). Per evaluation: 2^{C·log(11r)·(|E_D| + n_D)/√log n_D}·poly (the
[HC] Theorem bound with m+n → |E_D| + n_D and the factor log σ_r/log 5).

*Shared bits, refined encoding* ([HD] §1–3): a vertex has ≤ 2 F-edges, so a blob pair shares the rank-encoded set
of used crossing edges plus, per used edge, orientation × label × monomial (log(10r) bits instead of [HD]'s 2):
**U ≤ 2n_D log(2e·d̄_D) + 2n_D log(10r) + g³**, P ≈ (2n_D/g)(log(2e d̄_D) + log(10r)) + g², summed over
≤ (2n_D/g + 3)^{g²/2} profiles. This transfer is the same argument as [HD] (the profile sizes s_ab are now
"≤ 2 per vertex" instead of "= 2"; the bound used there is the ≤ form), but we did **not** re-run
`hc_degree_network.py` with labels; treat it as a careful transfer, not a re-verified statement.

---------------------------------------------------------------------------------------------------

## 3. Theorem 2 (the algorithm, conditional on (H_A))

**Theorem 2.** Assume (H_A). Given U, V ∈ ℤ^{n×r} and D, HC(UVᵀ + D) is computed exactly within

```
E(r) · 2^{ C · n_D · log(20e · r · d̄_D) / √(log n_D) } · poly(n, B)       (refined encoding),
E(r) · 2^{ C · log(11r) · (|E_D| + n_D) / √(log n_D) } · poly(n, B)        (crude encoding, fully as in [HC]),
```
plus one call for HC(D) (only if n_D = n; the sparse weighted #HC network of [HD] Theorem A on supp D),
E(r) ≤ (r+1)^r (2n+1)^{3r+1}. If n_D < n_0 (an absolute constant) use 2^{n_D}·poly brute force.

*Proof.* Theorem 1, Lemma 2, the accounting of §2.2 and, per evaluation, Lemma 8 / Theorems A(b), B of [A]
exactly as in [HC] §6 and [HD] §4 (the network differs only in the local alphabet and the vertex tables). ∎

**Corollary 2.1 (undirected; 0/1 graphs).** If G is a graph and S a set of vertex pairs such that G Δ S has at
most r twin classes (more generally: A_G = L + D off the diagonal with rk*(L) ≤ r, D = ±1 on S), then #HC(G) =
HC(A_G)/2 within the bound of Theorem 2 with n_D = |V(S)| and d̄_D = 2|S|/|V(S)|. Regime: 2^{o(n)} whenever
r log n = o(n), log r = o(√log n) and log d̄_S = o(√log n); for r, max degree of S bounded: 2^{δn} for every δ
(fixed achievable (K,e) as in [HD] Corollary C(a), since then U = O(n) with a constant depending on r, Δ(S)).
Directed graphs: the same, with HC(A_G) directly.

Examples (all dense, minimum degree Θ(n)): K_n − D (E2, r = 1); K_{n/2,n/2} ± S (r = 2); complete r-partite
graphs ± S (J − Σ_i J_{V_i} has r distinct rows, so rk* ≤ r); r cliques with arbitrary bicliques between them
± S; directed: tournaments that are blow-ups of an r-vertex tournament, ± S.

---------------------------------------------------------------------------------------------------

## 4. The class-profile form (the hint), and why rank beats it

For 0/1 blow-ups (type graph H on [r] with loops, classes V_1..V_r, edits S with D = ±1) one can avoid BEST:
by Step 1, #HC(G) = Σ_{F lin. forest ⊆ S} D^F Φ_H(prof F) + Σ_{F = HC of S} D^F, where prof F = (number of
F-isolated vertices per class; number of F-paths per unordered endpoint-class pair {a,b}) ∈ ℕ^{r + r(r+1)/2}, and
Φ_H(prof) = number of Hamiltonian completions, a function of the profile only (completion edges depend only on
classes). Φ_H for all profiles: a DP over (remaining unit counts, current exit class, first entry class),
n^{O(r²)} states (`Phi_H` in `dense_nd_graphs.py`). The profile is non-local (a path's two endpoint classes),
made local by an ordered endpoint-class label propagated along the path with an orientation (2 configurations
per path, a known factor), plus the determinant indicator: r² labels per edge, (n+1)^{r + r(r+1)/2} evaluations.

Verified (`dense_nd_graphs.py`, n ≤ 9, r ≤ 4, |S| ≤ 10, 15 instances; brute #HC up to 2316): profile form =
rank form (Theorem 1 with U = MB, V = M) / 2 = brute force; ALL PASS.

So the hinted "class profile + multinomial/transfer count + inclusion–exclusion over S" works, at n^{O(r²)}
outer terms. Theorem 1 replaces the r(r+1)/2 path-type counts by the out-degree vector d (r numbers) and the
balance x^0 (r − 1), at the price of the arborescence sum Σ_T (r^{O(r)}) and r − 1 marking variables:
n^{O(r)}·r^{O(r)} instead of n^{O(r²)}. Locality degree: the label carries one arborescence arc (|Λ| ≤ r) instead
of an endpoint-class pair (r²).

---------------------------------------------------------------------------------------------------

## 5. Perfect matchings and the permanent

**Theorem 3 (hafnian / #PM of general graphs).** Let A = L + D off the diagonal, L = U C Uᵀ (C symmetric r×r),
D symmetric. Then
```
haf(A) = Σ_{M matching of supp D} D^M haf(L[V∖V(M)]),
haf(L[W]) = Σ_{|α| = |W|} g^{(|W|)}_α · α! · [x^α] Π_{i∈W} (u_i · x),     g^{(2k)}(y) = (yᵀCy/2)^k / k!,
haf(A) = Σ_α g^{(|α|)}_α α! [x^α] P_D(x),     P_D(x) = Σ_M D^M Π_{i∉V(M)} (u_i · x).
```
*Proof.* Multilinear expansion in D (Step 1 with matchings); haf(B) = [Π s_i] (sᵀBs/2)^k/k! (the diagonal only
produces non-multilinear terms), with Uᵀs = y; [Π_{i∈W} s_i] y^α = α! [x^α] Π (u_i·x). ∎

P_D is a vertex-weighted matching polynomial of supp D (no cycles to exclude, no labels): local alphabet
2 states per D-edge, U = 2m_× + O(g²) crude, ≈ n_D log(e d̄_D) refined; (n+1)^r evaluations (|α| fixes |M|).
Time (n+1)^r · 2^{O(n_D log(2e d̄_D)/√log n_D)} · poly under (H_A). Verified `dense_lowrank_pm.py` (n ≤ 10,
r ≤ 3, 8 instances, H1 = H3 = brute force; ALL PASS). The 0/1 nd version has the closed form
PM_H(c) = Σ_t Π_a multinom(c_a; 2t_aa, (t_ab)_{b≠a}) · Π_{a<b} t_ab! · Π_a (2t_aa − 1)!! (checked in `dense_nd_graphs.py`).
Bipartite #PM / per(L + D) with rank L ≤ r is E1 (`wild-ideas.md` §6): (n+1)^{2r} evaluations. The S = ∅
cases are Barvinok (per, 1996) and Björklund–Gupt–Quesada (haf, JEA 2019, appendix: C(2n+r−1, r−1)·poly).

---------------------------------------------------------------------------------------------------

## 6. Which parameter? (target 2)

| parameter of the dense part L | fits the method? | why |
|---|---|---|
| **rk*(L)** (rank over ℚ, diagonal free) | **yes — the clean theorem** | Step 2 needs exactly a rank-r factorisation; works for weights, signs, directed graphs |
| number of twin classes / neighbourhood diversity r | yes, special case (rk* ≤ nd) | U = MB, V = M; also the elementary profile form of §4 (n^{O(r²)}) |
| rank over 𝔽_p | yes, for HC(A) **mod p** | Theorem 1 holds over any commutative ring (BEST and matrix-tree are integer identities) |
| modular-width, distance to cograph | no | cographs / modular-width 2 graphs have rank Θ(n) (e.g. n/2 disjoint edges, their complement); Step 2 would need Θ(n) labels |
| cluster vertex deletion k (and any vertex modulator) | only trivially | a k-vertex modulator changes rk* by ≤ 2k, so rk* ≤ r + 2k gives n^{O(r+k)}: worse than the known FPT algorithms |
| clique-width / rank-width of G | no | an edit set S that is a bounded-degree expander makes cw(G) = Θ(n) (e.g. K_n − expander), while our bound is 2^{o(n)} |

So the right statement is two-parameter: **(rk* of the dense part, sparsity of the edge perturbation)**.
Vertex perturbations are already handled by FPT algorithms; edge perturbations touching Θ(n) vertices are not,
and that is the only place the network engine adds something.

---------------------------------------------------------------------------------------------------

## 7. Comparison with the literature (checked 29 Oct 2026; abstracts/surveys only)

* **Decision, structural parameters.** Hamiltonian Cycle is FPT by neighbourhood diversity (Lampis,
  Algorithmica 2012, which introduced nd), by modular-width (Gajarský–Lampis–Ordyniak, IPEC 2013, ILP + DP), by
  cluster vertex deletion (Doucha–Kratochvíl, MFCS 2012); W[1]-hard by clique-width (Fomin–Golovach–Lokshtanov–
  Saurabh, SICOMP 2010) with an n^{O(cw)} algorithm (Espelage–Gurski–Wanke 2001; Bergougnoux–Kanté–Kwon 2020)
  and an n^{o(cw)} ETH lower bound (FGLS, SICOMP 2014). These are decision algorithms; we found no counting
  version for nd. None applies to G = L Δ S with S an expander on Θ(n) vertices (cw(G) = Θ(n); a vertex
  modulator to bounded nd has size ≈ |V(S)|, and modulator-based algorithms are exponential in it).
* **Fixed rank.** Barvinok (Math. Oper. Res. 21, 1996; DIMACS TR 93-13): permanent of a fixed-rank matrix in
  polynomial time; the report also lists "new polynomially solvable classes of TSP". Barvinok–Johnson–
  Woeginger (1998): max-TSP for fixed tropical rank / polyhedral norms by counting arc types in an Eulerian
  multigraph and enforcing connectivity — the (max,+) twin of our Step 2. Björklund–Gupt–Quesada (JEA 2019,
  appendix): hafnian of rank r in C(2n+r−1, r−1)·poly. We did **not** find an explicit statement "HC of a
  rank-r matrix in n^{O(r)} by BEST + arborescence marking"; it is a short derivation from these and we would
  call it folklore-level, not a contribution.
* **Dense counting in general.** O*(2^n) (Karp / Bax inclusion–exclusion), Björklund's O*(1.657^n) (decision,
  Monte Carlo), and the degree-dependent (2 − ε_d)^n bounds (Björklund–Husfeldt–Kaski–Koivisto, Cygan–Pilipczuk,
  Björklund–Williams) — the latter are useless at degree Θ(n). Li (arXiv 2309.15422) shaves a 2^{Ω(√n)}-type
  factor off general hafnian / #HC counting; still exponential.
* **Unconditional by-product of Theorem 1.** Q_{R,T} is a sum over partitions of V_D into directed paths of D,
  computable by Held–Karp + subset convolution in 2^{n_D}·poly, so HC(L + D) in **(r+1)^r n^{O(r)} 2^{n_D}·poly
  unconditionally** (and n^{O(r)}·2^{O(tw(S) log tw(S))} via a path-cover DP on a tree decomposition of S).
  For |V(S)| ≤ (1−ε)n this beats 2^n; we did not find this reduction in the literature, but it is easy.
* **What only the engine gives.** 2^{o(n)} when S touches all n vertices (|S| between n/2 and n·2^{o(√log n)}),
  conditional on (H_A), with the inherited astronomical constants (`crossover.md`).

---------------------------------------------------------------------------------------------------

## 8. Verification summary

| script | checks | instances | result |
|---|---|---|---|
| `dense_lowrank_hc.py` | I1 (expansion), I2 (labels + BEST), I3 (Theorem 1 form), E2 as r = 1 | 10 + 3, n ≤ 8, r ≤ 3 | ALL PASS |
| `dense_locality.py` | Lemma 2: local labels + determinant indicator, lowest ε-coefficient | 6, n ≤ 6, r ≤ 3 | ALL PASS |
| `dense_pipeline.py` | the algorithm end-to-end: grid evaluation, exact interpolation, extraction | 5, n ≤ 6, r ≤ 2 | ALL PASS |
| `dense_nd_graphs.py` | 0/1 graphs with ≤ r twin classes ± S: profile form, rank form, #PM closed form | 15, n ≤ 9, r ≤ 4, \|S\| ≤ 10 | ALL PASS |
| `dense_lowrank_pm.py` | Theorem 3 (hafnian) H1, H3 | 8, n ≤ 10, r ≤ 3 | ALL PASS |

Shared library `dense_lib.py` (exact Fractions; BEST with loop-corrected Laplacian — an earlier version without
the loop correction failed I2, which is how the loop case was caught). Not verified by script: the Grassmann
sign bookkeeping of the network (reused from [HC], unchanged) and the refined [HD] encoding with labels (§2.2).

---------------------------------------------------------------------------------------------------

## 9. Verdict

* **Target 1 (unify, generalise): done.** One identity (Theorem 1) covers K_n − D (E2), nd/twin-class blow-ups
  ± edits, complete multipartite graphs ± edits, weighted and directed versions, all with n^{O(r)}·r^{O(r)} outer
  terms (better than the n^{O(r²)} of the hinted class-profile form, which is also correct and verified).
  #PM/haf (Theorem 3) and per (E1) fit the same template with simpler networks. Locality is explicit: per
  D-edge 1 + 10r states (HC) or 2 states (PM); U ≤ 2 log(1+10r)·m_× + g³ (crude) or ≈ 2n_D log(20e r d̄_D) + g³
  (refined); per-node P ≈ U/g + O(g²).
* **Target 2 (parameter): rk* of the dense part + sparsity of the edge perturbation.** nd is a special case;
  modular-width, cograph distance, cluster deletion do not fit (unbounded rank) or are already FPT.
* **Is it new?** The S = ∅ case is folklore-level (Barvinok, BJW, BGQ). The reduction of the edge-perturbed
  problem to a local sparse sum is, to our knowledge, new but elementary; unconditionally it yields
  n^{O(r)}2^{|V(S)|}. The 2^{o(n)} statement for dense graphs with Θ(n)-vertex perturbations is new but only
  as strong as (H_A) and the engine.
* **Is it interesting?** Moderately. It shows that the Θ(n log n)-shared-bits barrier for dense permanents is
  about *entropy*, not density: structured density costs only polynomial interpolation (n^{O(r)}), and the
  network only ever sees the sparse perturbation. It does not move the generic dense case: a random graph is at
  edit distance ≥ n²/2 − O(r n^{3/2}) from every rk* ≤ r matrix (`wild-ideas.md` §6), so either r or |S| is Θ(n)·(large), and
  both terms of the bound become 2^{Ω(n)}. The honest frontier is the trade-off curve
  r log n + n_D log(r d̄_D)/√log n = o(n).
