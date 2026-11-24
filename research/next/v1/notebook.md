# v1 notebook: three probes after the VP ≠ VNP round (24 Nov 2026, late)

Tags: **[R]** proved here on paper (one author, unreviewed). **[N]** computed; script and output in this folder.
**[K]** known, source named. **[C]** conjecture or reading that still needs a check.
Nothing here is Lean-checked. Nothing here is a claim in the sense of the top-level README.

Run order for the scripts: `gf2_d2.py` first (it writes `par_gf2_d2.pkl`, which `sum_d2.py` and `gf2_d3b.py` read).
`cube2.py`, `cube3.py` need `scipy`.

## 0. Summary

| # | Statement | Tag |
|---|---|---|
| 1 | Certificate (cover) algorithms for Orthogonal Vectors need (4/3)^{d/2} = (2/√3)^d work per vector; this matches the known algorithm exactly. The same bound holds for exact signed decompositions with bounded coefficients. | R |
| 2 | Small gadgets over GF(2) (exhaustive on 2 coordinates, annealing on 3) do not beat the 2^{d/3} product baseline. | N |
| 3 | Cube instance, bond dimension 2: best two-cut splitting 7, best three-cut splitting 6. K₄ instance: two cuts 8, no three-cut splitting below 8 found. | N |
| 4 | Every three-cut identity found is useless under tensor powering (exponent 4.32 against trivial 4); two-cut identities give 3.75–3.78. | N |
| 5 | The contracting case of the VP ≠ VNP proof gives a lower bound for circuits that are only right on 0/1 inputs, provided their formal degree is at most about n^{1+γ}. | R from the paper's Lemma K.2 and Theorem K.6; C until re-read against the Lean |

## 1. Orthogonal Vectors: a tight wall for cover algorithms

Notation: R_d = [[1,1],[1,0]]^{⊗d} is the 2^d × 2^d disjointness matrix, R_d[a,b] = 1 iff a ∩ b = ∅.

**Known [K].** Dürr, Kipouridis, Lampis, Węgrzycki (arXiv 2507.11098, ICALP 2026) and independently Alman–Li solve
OV in randomized time Õ((4/3)^{d/2} · n) ≤ O(1.16^d n). The method: sample certificate sets c; a pair (a,b) is
detected when some sampled c has a ⊆ c and b ∩ c = ∅. It cannot count. Their analysis has its maximum at
|a| = |b| = d/3. Exact (counting) decompositions: degree 2^{0.3199 d} over {0,±1} (Ye, arXiv 2603.15565).

**Lemma 1 [R].** Let S be a real 2^d × 2^d matrix with S[a,b] = 0 when a ∩ b ≠ ∅ and S[a,b] ≥ 0 otherwise. Then

  γ₂(S) ≥ (2/(3√3))^d · Σ_{a∩b=∅} S[a,b].

*Proof.* γ₂(S) ≥ ‖S ∘ uvᵀ‖_tr for unit vectors u, v (dual form of the factorisation norm). Take u = v = w^{⊗d},
w = (√(2/3), √(1/3)). Let M = R₁ ∘ wwᵀ and let W be its orthogonal polar factor, so ⟨W, M⟩ = ‖M‖_tr = 2/√3.
W = [[1/√3, √(2/3)], [√(2/3), −1/√3]], and (W ∘ wwᵀ) equals 2/(3√3) on each of the three support entries of R₁.
Since ‖W^{⊗d}‖_op = 1, ‖S ∘ uuᵀ‖_tr ≥ ⟨W^{⊗d} ∘ uuᵀ, S⟩. On disjoint pairs the witness equals (2/(3√3))^d;
on intersecting pairs S vanishes. ∎ (`wall_check.py`, `gamma2.py`: numerical check for d ≤ 5.)

The same holds for any submatrix (pad with zeros), so it applies to one weight class at a time.

**Corollary 2 [R] (covers).** Suppose every a is given a list L(a) and every b a list L′(b) of certificates, with
L(a) ∩ L′(b) ≠ ∅ whenever a ∩ b = ∅ and L(a) ∩ L′(b) = ∅ otherwise. Let s = max|L(a)|, s′ = max|L′(b)|. Then
√(s s′) ≥ (2/√3)^d. Restricted to |a| = |b| = d/3 the bound is (2/√3)^d / poly(d).

*Proof.* S = PQ with P, Q the 0/1 incidence matrices; rows of P have norm ≤ √s, columns of Q norm ≤ √s′, so
γ₂(S) ≤ √(s s′). S ≥ 1 on the 3^d disjoint pairs and 0 elsewhere. Apply Lemma 1. For a randomized family, apply it
to the expectation. ∎

So the (4/3)^{d/2} algorithm is optimal in its class, up to poly(d). I did not find this bound stated; the paper says
only that 1.16 is "very close to the barrier achievable with current techniques". **Check the literature before
quoting it as new** (Alman–Li, Williams FOCS 2024).

**Corollary 3 [R] (exact, bounded coefficients).** If R_d = PQ over ℝ with entries of absolute value ≤ 1, at most s
nonzeros per row of P and s′ per column of Q, then √(s s′) ≥ (2/√3)^d. Best known: 2^{0.3199 d} [K].

**What the wall does not cover.** Decompositions over GF(2) (or with large coefficients) in which terms also touch
intersecting pairs and cancel there. Lifted to the integers, S is then nonzero on intersecting pairs, where the
witness has both signs. A lower bound there is the open depth-2 XOR-circuit problem for the disjointness matrix.

**Consequence for the low-dimension OV hypothesis.** The cover family tops out at n^{1+0.2075c} for d = c log n,
subquadratic only for c < 4.82. It cannot refute the hypothesis for large c.

### 1.1 Gadget experiments [N]

Model (`ovgame.py`): a gadget is a factorisation R_{d0} = PQ; r[a], c[b] are the row and column sparsities. Blocks of
coordinates are tensored; for vectors of relative weights (α, β) the per-coordinate costs are the expected log
sparsities; τ* is the max over (α, β) of the best mixture. This is weaker than the rebalancing analyses in the
literature (they reach 0.3199; this model reaches 1/3 with the three one-coordinate gadgets).

| Library | τ* |
|---|---|
| one coordinate (three gadgets) | 0.3331 (= 1/3 up to grid) |
| two coordinates, no cancellation, exhaustive (`sum_d2.py`) | 0.3332 |
| two coordinates, GF(2), exhaustive: 9,734 profiles, 123 Pareto (`gf2_d2.py`) | 0.3325 |
| three coordinates, GF(2), 26 annealing rounds (`gf2_d3b.py`) | no improving gadget found |

109 of the 123 Pareto profiles over GF(2) need cancellation, but they move τ* by under 0.001. Read this as a weak
negative: the model is crude, and the three-coordinate search is a heuristic.

## 2. Splitting numbers and the three-way law

Setting (`split.py`): a tensor Ω and cuts C₁..C_p. A splitting is Ω = X₁ + … + X_p; its cost is Σ_k rank_{C_k}(X_k).
This is what merge-by-merge accounting needs: each term cheap across its own cut. Exact solutions are found by
alternating least squares (residual ≤ 1e-10); "not found" is not a proof.

**Crossing (two wires, two cuts)** (`crossing.py`). The antisymmetriser gives N(N−1)/2 + 1 [R]: with Y the other
wiring, Ω − Y has rank N(N−1)/2 across one cut and Y has rank 1 across the other.

| N | trivial N² | best found | N^{√2} |
|---|---|---|---|
| 2 | 4 | 2 | 2.67 |
| 3 | 9 | 4 | 4.73 |
| 4 | 16 | 7 | 7.10 |

Nothing below the antisymmetriser was found for N ≤ 4. So at these sizes the graded pieces of the engine cannot be
told apart from this elementary identity.

**Cube** (`cube.py`): 8 parties at the vertices of {0,1}³, a wire of dimension 2 on each of the four body diagonals,
cuts = the three coordinate bipartitions. Every wire crosses every cut (rank 16).
- Two cuts: best found 7 = (6,1). Nothing at 6.
- Three cuts: **6 = (4,1,1), exact.** Nothing at 5.

So a third cut helps at the smallest size. The identity has the form I − (A⊗B)π₁ − (C⊗D)π₂ on four qubits arranged in
a 2×2 grid, π₁, π₂ the row and column swaps [R]. If the solution is SU(2)-invariant, rank 4 = 3 + 1 forces it to kill
the spin-2 sector and to have rank 1 on spin 1 and on spin 0 [C: invariance of the numerical solution not checked].

**K₄** (`k4.py`): four nodes, a wire of dimension 2 on each edge, the three 2|2 cuts. Two cuts: 8 = (4,4). Three cuts:
nothing at 7 (4 restarts × 800 sweeps per profile, a lighter search than for the cube).

**Under tensor powering** (`cube2.py`, `cube3.py`). A fixed identity with rank matrix M[k][j] (cut k, piece j) gives,
for the t-th tensor power, cost exponent E = max_τ [H(τ) + min_k Σ_j τ_j log₂ M[k][j]] per factor, against log₂ 16 = 4.

| Identity | Rank matrix (rows = cuts) | E |
|---|---|---|
| crossing, N = 2, antisymmetriser | [[1,4],[3,1]] | 1.8745 (trivial 2) |
| cube, two cuts (6,1) | [[6,16],[16,1],[16,16]] | 3.7835 |
| cube, two independent crossings | — | 3.749 |
| cube, three cuts (4,1,1), all 9 solutions sampled | [[4,16,9],[16,1,16],[10,16,1]] | 4.3195 |
| cube, three cuts (4,2,1) | [[4,7,16],[8,2,16],[16,16,1]] | 4.3398 |

Every three-cut identity found is worse than doing nothing once powered: its pieces have nearly full rank across the
cuts they are not assigned to. This is the same obstruction as on K₄ (composing pairwise identities fails because of
the rank across the third cut). **The experiment does not decide the three-way law.** It shows that group-algebra
identities at bond dimension 2 save a constant, not an exponent, and that the quantity to control is the cross-rank.

## 3. A Boolean reading of the contracting case

Source: Anthropic, "VP ≠ VNP over every field", Appendix K (paper text fetched 24 Nov 2026).

- **Lemma K.2 [K]** evaluates, in (d + |z| + 1)·polylog steps, the sum of the homogeneous parts of degree ≤ d of *any*
  polynomial with a circuit of L gates, at the indicator assignment of the word of z.
- **Theorem K.6 [K]**: in the contracting case no nonzero commutative A-algebra has an accelerator of size v^a at scale
  v, whenever (lg v)^{Ca} ≤ v. An accelerator has value sum(z) on every short (|z| ≤ v^{H−32}) v^H-plain instance z and
  accepting runs of at most v^{H−16} steps. H is a fixed multiple of 16 with H ≥ 272.
- The paper applies K.2 with d = n = v^{H−32} + 1 to a polynomial Φ obtained from a permanent circuit. Its proof of
  Lemma K.3 uses the circuit only through the values of its degree-≤ d part at indicator assignments.

**Corollary B [R from K.2 + K.6; C until checked against the Lean].** Contracting case over k, A ⊂ k the finitely
generated ring of Theorem G.2, R a field that is an A-algebra. For a ≥ 0 and v large with (lg v)^{C′(a+1)} ≤ v, put
n = v^{H−32} + 1 and d = ⌊v^{H−16} / ((a+1) lg v)^{C′}⌋. There is no arithmetic circuit over R with at most v^a gates,
in the variables (place, symbol) on n places, whose degree-≤ d part takes the value sum(z) at the indicator assignment
of every short v^H-plain instance z.

*Proof.* Lemma K.2 turns such a circuit into a program with these values, all runs halting, accepting runs of at most
(d + |z| + 1)(log(L+n+d))^{O(1)} ≤ v^{H−16} steps, names of constants only. As in the proof of Lemma K.3 this is an
accelerator of size v^{C(a+1)} at scale v, which Theorem K.6 excludes. ∎

Consequences, with n the input length and γ = 16/(H−32) ≤ 1/15:
1. No circuit of formal degree ≤ n^{1+γ−o(1)} and quasi-polynomial size that merely *agrees* with z ↦ sum(z) on
   one-hot 0/1 inputs. The paper's §2.5 says the proof says nothing about circuits correct only on 0/1; that remains
   true for unbounded formal degree.
2. No weighted (counting) branching program over R of length ≤ n^{1+γ−o(1)} and quasi-polynomial size computes
   sum(z): an iterated matrix product of ℓ matrices with entries linear in the one-hot variables has formal degree ℓ.
   Known lower bounds for general branching programs stop near length n·√(log n) [K: Ajtai; Beame–Saks–Sun–Vee].
3. With Theorem D.2 (one of the two cases holds over every field): **either the flat hypothesis holds over k, or
   statements 1–2 hold over every field quotient of A.** For k = F_p this is a statement about counting accepting runs
   mod p.
4. [C] Boolean circuits of size ≤ n^{1+γ−o(1)}, by hard-wiring and evaluating gate by gate. Needs the program model of
   Appendix I checked (cost of a hard-wired straight-line program on the pointer machine).

Open points before this can be claimed: quantifiers of K.6 as formalised; the encoding of all input lengths < n in
one device; whether H or the margins 16/32 can be re-parametrised to raise γ.

## 4. Candidates for the next adjacent problem

1. **Give the flat/contracting dichotomy a Boolean side** (§3): machine-check Corollary B on Anthropic's Lean, then
   ask what replaces "formal degree" as the gap to general Boolean circuits. Fits this repository's method.
2. **Mod-2 degree of the disjointness matrix below (4/3)^{d/2}** (§1): the only route left to the low-dimension OV
   hypothesis through decompositions.
3. **Subexponential Extended Frege refutations of random 3-CNFs**: resolution, polynomial calculus and sum-of-squares
   need 2^{Ω(n)} there [K], while the counting engines run in 2^{o(n)}; which proof system holds their certificates?
4. **k-Clique in n^{o(k)}**: its ETH-based lower bound is gone and the new algorithms are not known to give it.
