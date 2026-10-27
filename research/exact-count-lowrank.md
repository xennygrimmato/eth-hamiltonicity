# Exact #HC via low-rank connectivity: testing the Raz–Spieker hunch

27 Oct 2026. Tags: **[Computed]** means a script in `research/scripts/lowrank_*.py` checked it exactly.
**[Paper]** means it comes from the Anthropic manuscript. **[Mine]** means a derivation I have not
machine-checked. **[Conj]** means a conjecture.

## TL;DR

The hunch survives, though not in the form it was proposed. Raz–Spieker ranks are the right
*count*, but they do not give a construction, because a single low-rank cut does not compose
across a non-tree network. What does compose is the **fermionic form of the matrix-tree theorem**:

```
n · #HC(G) = Σ_{x 2-factor of G} τ(G[x]) = Σ_{x 2-factor} det L_x^{(r)}
           = Σ_x Π_v [deg_x v = 2] ∫ dψ̄ dψ Π_e (1 + x_e (ψ̄_i − ψ̄_j)(ψ_i − ψ_j)),   ψ_r = ψ̄_r = 0.
```

The identity holds because τ(cycle on n vertices) = n and τ(disconnected) = 0. Cut V into g blobs.
Each crossing edge then splits into 5 product terms (Schmidt rank 5 = x_e ∈ {0,1} plus 4 terms
when x_e = 1). Reordering the Grassmann factors blob by blob costs a sign
`(−1)^{local} · (−1)^{Σ P_ab P_cd}`. The sum runs over pairs of blob pairs whose chords interleave
on the circle 1..g, and `P_ab` is the parity of the "odd" labels on the pair ab. This is a network
in the sense of Def. 2 of the paper, with `c_ab = log₂5 · e(a,b) + O(g)` and blob tables
computable in `2^{O(n/g)}`. **[Computed]**: the identity holds exactly on 40 (graph, partition)
instances with K = 2..5. The sign is necessary: dropping it gives wrong values.

Plugging this into Lemma 1 [Paper], with e* = 0, should give **exact #HC, deterministically, in
2^{δn} for every δ > 0 on graphs with |E| = O(n)** [Mine, conditional on the paper's Lemma 1 for
general networks]. That also gives deterministic decision and search.

## 1. Raz–Spieker and relatives [Computed: `lowrank_rs.py`, `lowrank_hecke.py`, `lowrank_hrank_formula.py`]

Bipartite case (permutations; entry `[s⁻¹t is an n-cycle]`):

| n | #PM | rank_Q | C(2n−2,n−1) | rank_GF2 |
|---|---|---|---|---|
| 2..7 | 2, 6, 24, 120, 720, 5040 | 2, 6, 20, 70, 252, 924 | same | 2, 4, 8, 16, 32, 64 = 2^{n−1} |

The formula rank_Q = Σ_k C(n−1,k)² = Σ_k (dim hook_k)² holds because only hooks have
χ_λ((n)) ≠ 0. The indicator expands as 1_{n-cycle} = (1/n) Σ_k (−1)^k χ_{Λ^k std}, checked for
n ≤ 7 (`lowrank_hooks.py`).

Non-bipartite case, H_t (matchings on 2t points), computed in the Hecke algebra of (S_2t, B_t):

| t | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| #PM | 1 | 3 | 15 | 105 | 945 | 10395 |
| rank_Q | 1 | 3 | 15 | 105 | 945 | **9933** |
| rank_GF2 | 1 | 2 | 4 | 8 | 16 | – |

At t = 6 the zero eigenspace has dimension 462 = dim S^{(4,4,4)}. This fits the rule
rank_Q(H_t) = Σ_{λ⊢t, λ₃≤1} f^{2λ}: the zonal spherical function at the cycle type (t) is
proportional to Π_{cells≠(1,1)} (2(j−1) − (i−1)), which vanishes iff (3,2) ∈ λ. That rule is
[Mine], checked for t ≤ 6. From the formula, the ratios rank(t+1)/rank(t) are 10.5, 11.5, …, 13.4
at t = 12 and rise towards 16. There is also an elementary upper bound of 16^t·poly, so
rank_Q(H_t) ≈ 16^t = 4^{#points}.

**Cut matrix with b crossing edges.** States are (X ⊆ crossing edges, pairing of X, no closed
cycle), and the matrix is block-diagonal in X, so rank = Σ_k C(b,2k)·rank(H_k) ≈ 5^b/2. Measured
log₂(rank)/b is 1.20 at b = 8, 1.58 at b = 16, 1.89 at b = 32 and 2.06 at b = 60, tending to
log₂5 ≈ 2.32. So, over Q, connectivity across a cut costs Θ(b) bits, about 2.32 per crossing edge.
The Grassmann construction uses exactly 5 labels per crossing edge, so it is rank-optimal to
leading order.

**Real small graphs** (`lowrank_cuts.py`; cubic graphs with n ≤ 16, grids, Heawood,
Möbius–Kantor). Flattening ranks are at most 24, so log₂rank/b ≤ 0.58. These numbers are
uninformative: the rank is bounded by #HC, and with a universal right side the realizable left
states are simply linearly independent. Small graphs cannot probe the asymptotics. The K=3 blob
flattenings, for example Heawood with e = (5,6,2) and ranks (24,17,17), are equally
uninformative.

## 2. K-party composition: answered positively by fermions

Flattening (single-cut) bounds never rule out the hunch. For a path or tree of blobs, the minimal
bond dimensions equal the flattening ranks, but tree networks are useless on expanders, because
the paper needs the total S to be O(|E|). The obstruction was the cycles in the blob graph, and
the Grassmann construction removes it.

**Labels.** Write e = (i ∈ a, j ∈ b) with a < b. The terms (α, β) are
`(1, 1+ψ̄_jψ_j)`, `(ψ̄_iψ_i, 1)`, `(ψ̄_i, −ψ_j)` and `(ψ_i, ψ̄_j)`, plus "N" for x_e = 0. The odd
labels are {2, 3}.

**Sign.** Fix the order of the crossing edges. Then
ε = (−1)^{Σ_{k<l} π_k π_l c_kl} with c_kl = [a_l<a_k]+[a_l<b_k]+[b_l<a_k]+[b_l<b_k] mod 2.
For edges on four distinct blobs, c_kl = [the chords interleave], independent of the order. All
other pairs are local to a shared blob. So
ε = (local) · (−1)^{Σ_{a<c<b<d} P_ab P_cd} **[Computed: identity checked on every labelling]**.
Each interleaving term is implemented by copying P_cd (1 bit) onto the pair (a,c). That adds at
most g bits per pair, and g³ bits in total.

**Blob table.** `W_a = Σ_{internal x} [deg = 2 on a] · top-coefficient_a(Π_int(1+q_e) · ordered pieces of a)`.
It is an integer of O(n/g + log) bits, and the cost is 2^{#internal edges}·poly (or a sum of
Laplacian minors).

**Verification** (`lowrank_grassmann.py`, all exact): K4, prism, K3,3, Q3, K5, W6, C8+chords,
2×4 grid, Petersen and random cubic graphs on 8 and 10 vertices, with K = 2..5 random blobs and up
to 9 crossing edges. All 40 instances give Z = n·#HC = Σ_x τ(x).

**Ablation** (`lowrank_grassmann_ablate.py`): with no sign the results are wrong (prism 30 vs 18,
Q3 80 or 96 vs 48). With local signs only, Q3 with K = 5 gives 64 vs 48. The interleaving term is
therefore needed.

## 3. Representation-theoretic reason [Mine]

Connectivity lives on the hook isotypic components. The hook representations are Λ^k(std), the
fermionic Fock space, and Raz–Spieker's binomial is dim(Λ std)². Fock spaces factor over a
partition of the generators as a **graded** tensor product,
Λ(V_A ⊕ V_B) = Λ V_A ⊗̂ Λ V_B. The grading is exactly what produces the sign, and it is controlled
by one parity bit per blob pair, which is why the low rank composes on any network. Characters
alone give only a ring MPS: χ_λ(σ₁⋯σ_K) = tr Πρ_λ(σ_a) has bond dim λ ~ 2^{#strands}. That works
for a cyclic chain but not for general blob graphs. Murnaghan–Nakayama gave nothing beyond this.

## 4. Reconciling with the §8 barrier [Mine]

§8 assumes commuting local weights, so a component gets h(C) = Σ_j m_j Π_v z_j with multiplicities
m_j ≥ 0. Grassmann colours behave like negative multiplicities (superdimension). A non-root
component gets h(C) = det L_C = 0 exactly, using only 2 generators per vertex.

In bosonic form the price is a non-local sign. At vertex granularity it costs one bit per
interleaving pair of edges, which is Θ(cr(G)) and can be Θ(m²) on expanders. So **§8, and the
lack of a linear-size CNF, still apply to anything that goes through the top-level #k-SAT
theorem.** Only at blob granularity does the sign collapse to O(g³) bits. The construction
therefore needs the paper's Lemma 1 for general networks, with arbitrary integer W, not the Lean
Main Theorem.

## 5. What needs proving or checking

1. Lemma 1 plus achievability with e* → 0 (Prop 3) for general networks, as stated (Def. 2,
   arbitrary W, τ-cost oracle) [Paper]. Check whether the Lean development exposes this. If it
   does not, the result is "conditional on the paper's internal lemma", like result 3 in
   `hamiltonicity.md`.
2. Bookkeeping: P ≤ 2.32·Δn/g + g², U ≈ 4.64|E|+O(g⁴), τ = 2^{O(Δn/g)}, B = O(n). This gives
   time 2^{e(4.64|E|+O(|E|/K))+O(Δn/K)}, hence 2^{δn}. For the sharper n/√log n bound, g grows,
   and the O(g³)–O(g⁴) sign overhead has to stay o(|E|/√log) [unchecked].
3. Extensions [Conj, easy]:
   * directed HC, using the directed matrix-tree theorem with factors 1 + ψ̄_i(ψ_i − ψ_j), 4 labels
     per arc;
   * Hamiltonian paths;
   * TSP or #HC by weight, with polynomial weights;
   * a deterministic version of `hamiltonicity.md` results 3/3′.
