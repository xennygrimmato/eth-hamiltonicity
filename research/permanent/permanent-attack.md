# The 0/1 permanent through the network engine: bit accounting, barriers, verdict

28 Oct 2026. Goal: write per(A) (A a dense n×n 0/1 matrix, = #perfect matchings of a dense bipartite
graph) as the value of a network in the sense of Definition 2 of [A] (nodes with integer tables,
pairwise factors that factor through c_{ab} shared bits, total U = Σ_{a≠b} c_{ab}, max node load P), so
that Lemma 8 / Lemma 1 of [A] evaluate it in 2^{e(U + gP/K) + 2gP/K}·τ·poly with g = 3K⁸ and
e = e_K ≈ c/√log K. To beat Ryser's 2^n one needs e·U < n, i.e. **U = o(n·√log K)** together with
**P = o(n/K⁷)** (the gP/K term) and tables computable in τ = 2^{o(n)}.

Everything below was checked in exact integer arithmetic on random 0/1 matrices with n ≤ 7; the
scripts live in `scripts/` and each prints PASS/FAIL:

| script | network | result |
|---|---|---|
| `perm_laplace.py` | Laplace / column-partition network, pattern-wise | PASS |
| `perm_ryser_block.py` | Ryser with row→block labels | PASS |
| `perm_degree_block.py` | bounded-degree profile network (coordinator's candidate (a)) | PASS |
| `perm_bosonic_pm.py` | commutative-nilpotent local product (= Godsil–Gutman sign average) | PASS |
| `perm_rank_barrier.py` | cut ranks behind the two barriers; Godsil–Gutman identity | PASS |
| `perm_exponent.py` | the engine's actual exponent per level for each network | PASS |

Summary of the bit counts (n rows/columns, h row groups = h column blocks, p = n/h, q = block size,
Δ = max degree of the bipartite graph, g = 3K⁸ engine nodes):

| network | bijection-term? | U | max node load P | admissible (P ≤ n/K⁷)? | e·U |
|---|---|---|---|---|---|
| Ryser broadcast (row nodes see all of x) | no | 2hn | n | **no** | – |
| Ryser, rank-compressed (c_{ab} = min(p,q)) | no | 2n²/q | ≥ n at a column node | **no** | – |
| Ryser with row→block labels | no (row→block maps) | 2nh_c, or 2n lg(e h_c) pattern-wise | n at a column node | **no** | – |
| Laplace / partition, pattern-wise | yes | 2n lg(e h) | (n/h) lg(e h) | yes for h ≥ K⁷ | ≳ 14c·n√log K |
| bounded degree Δ, profile-wise | yes | 2 lg C(\|E\|,n) ≤ 2n lg(eΔ) | (2n/g) lg(eΔ) | yes | c·2n lg(eΔ)/√log K |
| local product / Godsil–Gutman | yes | 2 m_cross (= Θ(n²) dense) | crossing edges at a blob | yes for sparse | Θ(n²/√log n) dense |

**Headline.** The best admissible network for a dense matrix has U = 2n·log₂(e·h) with h ≥ K⁷ nodes
on each side, i.e. U ≈ 14 n log K + O(n), and the engine's exponent is e_K·U ≈ 14c·n·√(log K) ≥ 147 n
at the smallest level (K = 2¹⁸, e = ½) and increasing with the level (`perm_exponent.py`). For
bounded degree Δ the same network gives #PM in 2^{O(n log Δ/√log n)}, which is 2^{o(n)} iff
log Δ = o(√log n). **No candidate has U = o(n log(n/P))**, and the only non-bijection
representations we know (inclusion–exclusion over Ryser's S, or over marks) force a node to see Θ(n)
bits, which Lemma 8 cannot absorb at all.

---------------------------------------------------------------------------------------------------

## 1. The model, restated as a factor graph

Because Ψ_{a,b}(z_a,z_b) = Σ_θ f_{ab}(z_a,θ) f_{ba}(z_b,θ), every network is equivalent to

```
value = Σ_{θ ∈ {0,1}^{U/2}} Π_a W̃_a(θ|_a),      W̃_a(θ_a) = Σ_{z_a ∈ S_a} W_a(z_a) Π_b f_{ab}(z_a, θ_{ab}),
```

a factor graph whose edge labels θ_{ab} have c_{ab} bits and whose node a sees Σ_b c_{ab} ≤ P bits. The
node's own setting z_a is private and free (it costs only τ: we may sum over 2^{P_a} private settings
when building the table). So the question is purely: **how many bits must cross node boundaries** in a
sum-of-products representation of per(A), with no node seeing more than P ≈ n/K⁷ of them.

The engine's charges (Lemma 8 with Theorem A, anthropic-api.md §2, exact-hc-theorem.md §1):
exponent e_K(U + gP/K) + 2gP/K, with g = 3K⁸, e_K ≈ 0.85((3x₀+6)/log K)^{α′}, α′ = log(1/ρ) = ½ for
Theorem B's pieces, K ≥ 2^{18}. Two consequences used throughout:

* **(P)** every node must have Σ_b c_{ab} ≤ P with 3K⁷P = o(n·e): P ≤ n/K⁷ up to constants. A node that
  sees Θ(n) bits is inadmissible for every K.
* **(U)** the exponent is ≥ e_K·U, so we need U = o(n/e_K) = o(n√log K).

## 2. Candidate 1: Ryser / inclusion–exclusion

per(A) = Σ_{x∈{0,1}^n} (−1)^{n−|x|} Π_i (Ax)_i. The sum over x has n bits. The weight is a product of
n linear forms, each depending on all of x.

**1a. Broadcast.** Column blocks C_b (q bits of x each) and row groups R_a (p rows). Row node a needs
F_a(x) = Π_{i∈R_a}(Ax)_i. `perm_rank_barrier.py` (1): as a matrix indexed by (x_b ; x_rest), F_a has
rank exactly 2^{min(p,q,n−q)} for generic entries (0/1 matrices can be degenerate, but a network must
serve every A). So pair (a,b) needs c_{ab} ≥ min(p,q) bits, and a column node sees
Σ_a c_{ab} ≥ (n/p)·min(p,q) = n bits when p ≤ q (and the row node sees n bits when p ≥ q). Hence
**U ≥ 2n²/max(p,q) ≥ 2n²/P and some node sees ≥ n bits**. Fails (P) outright. Not a bijection-term
network (terms are subsets x), but a "broadcast" network: U·P ≥ n².

**1b. Row→block labels** (`perm_ryser_block.py`). Expand Π_{i∈R_a} Σ_b s_{ib}(x_b) with
s_{ib} = Σ_{j∈C_b}A_{ij}x_j: every row chooses a block. Label on {a,b} = L_{ab} = rows of R_a that chose b
(p bits); column node b holds x_b privately, W̃_b = Σ_{x_b}(−1)^{q−|x_b|}Π_{i∈∪_a L_{ab}} s_{ib}(x_b);
row node a checks that the L_{ab} partition R_a. Verified = per(A) for n ≤ 7. U = 2 n h_c = 2n²/q;
P_col = q + Σ_a p = q + n: the column node still sees all n row-choice bits. Restricting to patterns
(|L_{ab}| = N_{ab} fixed, summed outside) gives c_{ab} = lg C(p,N_{ab}) and U = 2 Σ lg C ≤ 2n lg(e h_c),
P_col = q + Σ_a lg C(p, N_{ab}) ≤ q + lg C(n, q) ≈ q lg(en/q) — admissible, but now this is exactly the
Laplace count of Candidate 2: the row→block assignment of n rows into h_c blocks carries n lg h_c bits,
whether or not the terms are bijections. **Not bijection-term, but "assignment-term": same entropy.**

**1c. Sum-of-vectors variant.** Instead of a product split, send the partial-sum vectors
(s_{ib})_{i∈R_a} ∈ {0..q}^p from b to a and let a add them: c_{ab} = p lg(q+1), row node sees
(n/q)·p lg q, column node sees (n/p)·p lg q = n lg q. Worse than 1a. Also broadcast.

**1d. Fourier / Walsh.** Σ_x(−1)^{|x|}Π_a F_a(x) = ±2^n Σ_{S_1Δ⋯ΔS_h=[n]} Π_a F̂_a(S_a); deg F_a = p so
|S_a| ≤ p; sharing S_a ∩ C_b costs lg C(q, |S_a∩C_b|): pattern-wise U ≈ 2n lg(e h) again. Same number.

**1e. Characters over F_p, Glynn's ±1 version, Kronecker substitution x_j = y^{2^j}.** All keep the
property that every row factor depends on every column variable, and either broadcast (1a) or split
(1b) — Kronecker makes it worse (rank n^p instead of 2^p across a cut of t's bits).

**Exact U for the task's question 1.** With column blocks of size b and row→block labels:
U = n·(Ryser bits, private at the column nodes, so free) + 2n lg(e·n/b) (block ids, pattern-wise) and
P_col ≈ b lg(en/b). Condition (P) forces b ≤ n/(K⁷ log n), hence U ≥ 14 n lg K − O(n). Block ids cannot
be avoided: any representation in which the x-bits live at the column nodes must either hand the row
nodes all of x (1a, rank argument) or distribute the product over blocks (1b). The Grassmann /
determinant trick does not remove the assignment (Candidate 4), and multi-level inclusion–exclusion
only re-encodes it (1d).

## 3. Candidate 2: Laplace / partition network (bijection-term) — the best admissible one

`perm_laplace.py`. For a pattern N (h×h contingency table with margins n/h), label T_{ab} ⊆ C_b of size
N_{ab} on {a,b}; row node a: W_a = per(A[R_a, ∪_b T_{ab}]) (computed in 2^{n/h} time), column node b:
[the T_{ab} partition C_b]. per(A) = Σ_N value(N). Verified for n ≤ 7, h ∈ {2,3}.

```
c_ab(N) = ⌈lg C(n/h, N_ab)⌉,   U(N) = 2 Σ_ab lg C(n/h, N_ab) ≤ 2 lg C(n, n/h)·h ≈ 2n(lg h + lg e),
P_a = Σ_b c_ab ≤ lg C(n, n/h) ≈ (n/h) lg(e h),      #patterns ≤ (n/h+1)^{h²} = 2^{O(h² log n)}.
```

Taking h ≈ g/2 = 1.5K⁸ groups per side: P ≈ (n/K⁸)·8 lg K, gP/K ≈ 16 n lg K / K = o(n) ✓,
U ≈ 16 n lg K + 3n. Exponent e_K·U ≈ 16·0.85·√(3x₀+6)·n·√lg K. `perm_exponent.py`: 147n at level 0,
410n at level 1, growing like √log K. **Never below n.** The same network is the "surjection network"
(private maps j: R_a → [n] at the row nodes, private Ryser variables x_b at the column nodes, shared hit
sets im(j_a)∩C_b): the Ryser sum at a column node collapses to the covering test, covering forces a
partition, and the two networks coincide — a nice illustration that "non-bijection" sums can quietly
be bijection sums.

**Why U ≈ n lg h is forced here.** Each of the h factors F_a(z) = Π_{i∈R_a} L_i(z) (Candidate 4 makes
this literal) is a polynomial of degree p in all n column variables; extracting [z_1⋯z_n] of the
product picks one monomial per factor; a degree-p monomial in n variables costs lg C(n,p) ≈ p lg(n/p)
bits; total n lg(n/p) = n lg h. This is the coordinator's Ω(n log g): the block pattern of a random
bijection has entropy n lg h, and every bit of it must cross a node boundary.

**What would make it work.** Exponent e_K · 16 n lg K = o(n) iff e_K lg K → 0 iff α′ > 1 iff pieces
with ρ < ½ exist (Theorem A(a): e_ℓ ≥ ½ρ^ℓ, so Theorem A with ρ ≥ ½ cannot reach it). With ρ = 0.4
(`perm_exponent.py`, hypothetical) e_ℓ lg K_ℓ decreases from level 2 on and the dense permanent would be
2^{o(n)}. So: **the dense permanent through a bijection-term network is 2^{o(n)} iff the clique
exponent satisfies e_K = o(1/log K)**; Theorem B's ρ = 1/√2 gives e_K = Θ(1/√log K), off by exactly a
√log K factor.

## 4. Candidate 3: bounded degree Δ (coordinator's (a)) — works for log Δ = o(√log n)

`perm_degree_block.py`. g blocks, block a owns R_a and C_a. Profile μ_{ab} = rows of R_a matched into C_b.
Labels: M_{ab} ⊆ E(R_a, C_b) of size μ_{ab} (the matched cross edges), rank-encoded among the μ_{ab}-subsets
of the edge set: c_{ab} = ⌈lg C(e_{ab}, μ_{ab})⌉ + ⌈lg C(e_{ba}, μ_{ba})⌉. Node a: distinct rows in its
outgoing M_{ab}, distinct columns in its incoming M_{ba}, times #PM of the leftover of block a (2^{n/g}
time). Verified = #PM for n ≤ 7, g ∈ {2,3}, Δ ∈ {2,3,6}. Exact accounting printed per profile; the
bound U(μ) ≤ 2 lg C(|E|, n) ≤ 2n lg(eΔ) holds in every run (e.g. n=6, Δ=3: max U = 12 ≤ 30 ≤ 36.3).
P_a ≤ 2 lg C(Δn/g, n/g) ≈ (2n/g) lg(eΔ); gP/K = O(n lg Δ/K) = o(n). Profiles: ≤ (n/g+1)^{g²}.

Exponent: e_K · 2n lg(eΔ) + o(n) = O(n lg Δ/√log n) with K = n^{Θ(1)} as in exact-hc-theorem.md §6.4.
So **#PM of a bipartite graph of maximum degree Δ in 2^{O(n log Δ/√log n)}**, 2^{o(n)} iff
lg Δ = o(√log n). This is m-independent and needs no sparsification, marks or parity checks; for
Δ = n (dense) it is 2^{Θ(n log n/√log n)}, worse than Ryser. Bijection-term network (nonzero terms ↔
perfect matchings). Side remark: the same rank encoding applied to the HC network's labels on E(a,b)
replaces w_{ab} = e_{ab} lg 5 by lg C(e_{ab}, μ_{ab}) + 2μ_{ab} and gives #HC in 2^{O(n log Δ/√log n)}.

## 5. Candidate 4: determinant sieves (Godsil–Gutman, Grassmann) — bijection-term in disguise

For 0/1 A, per(A) = 2^{−n²} Σ_{S∈{±1}^{n×n}} det(A∘S)² exactly (`perm_rank_barrier.py` (3), n ≤ 3). Written
with two Grassmann copies and averaging each sign independently,

```
per(A) = [top] Π_{i,j} (1 + A_ij ε_i z_j),   ε_i := ψ̄_i φ̄_i,  z_j := ψ_j φ_j,   ε_i² = z_j² = 0, all commuting.
```

So the sign average *is* the commutative-nilpotent local product Z[ε,z]/(ε_i², z_j²) — the bosonic
twin of det = [top] Π(1 + A_ij ψ̄_i ψ_j) — with no signs at all. `perm_bosonic_pm.py` turns it into a
blob network exactly as in exact-hc-theorem.md §4–5 minus the sign rule: 1 bit per crossing edge,
U = 2 m_cross, verified = #PM for n ≤ 7 including complete bipartite graphs. For sparse graphs this is
the simplest route to #PM in 2^{O(m/√log n)}; for dense graphs m_cross = Θ(n²).

Can the all-pairs structure be compressed? `perm_rank_barrier.py` (2): the factor of a block pair
(R_a, C_b) is Σ_{I,J} per(A[I,J]) ε_I z_J, and its (I ; J) matrix has rank Σ_s min(C(p,s), C(q,s)) = 2^p
(p = q) for generic entries — identical to the Grassmann det(A[I,J]) factor. So c_{ab} ≥ min(p,q) and
U ≥ 2h²·min(p,q) = 2hn with every node seeing n bits: the determinant representation of a dense
matrix is the broadcast network of §2 again, and after pattern restriction it is the Laplace network
of §3. Nonzero terms are (partial) bijections: **bijection-term**. Determinant sieves buy nothing
because the only thing the determinant computes cheaply (Gaussian elimination) is not a sum over
labellings with small tables; as a tensor network det has the same bond ranks as per.

Random-sign families smaller than 2^{n²} (2n-wise independent signs, size (n²)^{2n}) reduce the label
to 2n lg n bits but the determinant node sees all of them: P = Θ(n log n). Inadmissible.

## 6. Candidate 5: marks / truncated inclusion–exclusion (Appendix D style)

Σ_{j: rows→cols} Π_c [c hit] = Σ_j Σ_{M} (−1)^{|M|} [M unhit] with M a set of marked (unhit) columns.
A marked column must be checked by every node owning a row adjacent to it: arity Δ = n in the dense
case, so each mark costs ~g bits and the O(n) marks of the cut-off cost Θ(gn) (anthropic-m-independence.md
§4(c)). Dually (Ryser) the marks are columns outside S and the row factors are the width-n constraints
— this is §2 again. The IPZ/Calabro sparsification has nothing to branch on (distinct columns share
no literals). Not bijection-term, but broadcast: U ≥ 2(g−1)n, P ≥ n.

## 7. Stepping stones mod small primes

per mod 2 = det mod 2 (poly time); per mod 2^k in n^{O(k)} (Valiant), useless for k ≈ n log n;
per mod 3 is Mod₃P-hard. Reducing mod p does not change U: the labels are the same, only B shrinks.
Björklund's "below all subsets" 2^{n−Ω(√(n/log n))} (arXiv 1211.0391) works mod primes p = poly(n) by
reducing per(G_n) to 2^{n−k} weighted permanents of k×k matrices (kernel K, ranked walks through X ⊆ V∖K,
interpolation in the rank variable) and tabulating the ≤ p^{k²} distinct small matrices with
k = c√(n/log n). The weights per(G_k, f_X) depend on all n−k bits of X: as a network this is one node of
P = n − k. The gain comes from collisions among small instances, not from locality, so the engine cannot
amplify it. Björklund–Kaski–Williams (Kakeya sets) improve to 2^{n−Ω(√n/log log n)} by faster multipoint
polynomial evaluation, again not a locality structure.

## 8. The barrier, stated

All candidates fall into two classes, each with a clean quantitative obstruction.

1. **Broadcast class** (Ryser, characters, sum-of-vectors, determinant block factors, marks): the
   information that reaches a node about the other side is a function of all n column bits whose cut
   rank is 2^{min(p,q)}; hence c_{ab} ≥ min(p,q), U ≥ 2n²/P and some node sees ≥ n bits. Violates (P) for
   every K. (`perm_rank_barrier.py` (1),(2).)
2. **Assignment class** (Laplace, surjection, Ryser with block ids, Fourier, profile networks, local
   products after pattern restriction): the labels determine how many and which rows of each group use
   each column block; for a random bijection this pattern has entropy n lg h, and with h ≥ n/P ≥ K⁷
   groups U ≥ 2n lg(e h) ≥ 14 n lg K. Then e_K·U ≈ 14·0.85√(3x₀+6)·n√lg K ≥ 147 n. Violates (U) by a
   factor √lg K, and the factor grows with K.

The two classes are the two ways of distributing Π_i Σ_b s_{ib}: keep the sum inside (broadcast) or
expand it (assignment). I found no third way. The arithmetic is sharp enough to say exactly what would
break it: either a representation with o(n lg(n/P)) shared bits and P ≤ n/K⁷ — which would be a new
exact formula for the permanent, not just a new encoding — or a clique exponent e_K = o(1/log K)
(pieces with ρ < ½, α′ > 1), which is a different theorem about [A]'s engine. With e_K = Θ(1/√log K)
the dense permanent needs log(n/P) = o(√log K), impossible since P ≤ n/K⁷.

## 9. Verdict and most promising next step

**Verdict.** No encoding of the dense permanent with U = o(n log n) was found; every admissible one has
U = 2n lg(e h) + O(h² log n) with h ≥ K⁷ (Θ(n log n) once K is allowed to grow, ≥ 14 n lg K for fixed
K), and the engine then costs 2^{≥147 n} — strictly worse than Ryser at every level. The non-bijection
representations (Ryser's S, determinant sieves, marks) are even worse: they force a node to see Θ(n)
bits, which Lemma 8 rejects regardless of U. What *does* work is the bounded-degree profile network:
#PM (and, with the same rank trick, #HC) of an n-vertex bipartite graph of maximum degree Δ in
2^{O(n log Δ/√log n)}, i.e. 2^{o(n)} iff log Δ = o(√log n), m-independent and without sparsification.

**Most promising next step.** Two honest options, in order:

1. Pin down whether pieces with ρ < ½ (equivalently a clique exponent e_K = (log K)^{−α′} with α′ > 1)
   are possible in Anthropic's framework (their Appendix H / our Track H). If yes, the Laplace network
   of §3 gives the dense permanent, dense #HC and ATSP in 2^{o(n)} immediately — the network side is
   finished and verified here. If a lower bound ρ ≥ ½ holds for pieces, the dense permanent is out of
   reach of Definition 2 + Lemma 8 by the arithmetic of §8, and that is worth writing down as a theorem
   about the model ("every network for per(A) has U·P ≥ n² or U ≥ n lg(n/P)" is the conjecture to prove;
   the rank computations of `perm_rank_barrier.py` are the first step).
2. Independently of (1), write up the bounded-degree result of §4 against `Net g`/`Net.Is` (it is a
   clean, m-independent corollary with a 60-line proof: no Grassmann algebra, no sign rule), and port the
   rank encoding into the HC network to replace O(m) by O(n log Δ) bits.
