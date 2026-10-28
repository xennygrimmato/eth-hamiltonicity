# A barrier for the 0/1 permanent in the network engine

Target: the engine of [A] (Lemma 8 + Theorem A + Theorem B, in the form quoted in
`research/exact-hc-theorem.md` §1 and pinned to Lean in `research/anthropic-api.md`) applied to a
network whose value is per(A) = #perfect matchings of the bipartite graph with biadjacency matrix
A ∈ {0,1}^{n×n}. The question is whether the engine's *own guarantee* can ever be below 2^n.

Conventions: log = log₂; C(n,k) binomial; [·] Iverson bracket; ranks are over ℚ. "The engine" means
the bound (1.1) of `exact-hc-theorem.md` §1 with the clique algorithm of Theorems A(b)+B.

---------------------------------------------------------------------------------------------------

## 0. Summary: what is proved, what is conjectured

Proved (full proofs below):

* **Lemma 2.1 (engine exponent).** For every network N with total U ≥ 1 and every admissible
  choice of K, the engine's guaranteed running time is at least 2^{E(N)} with
  E(N) ≥ U/(2√(log U + 2x₀)) (x₀ ≥ 18 is the absolute constant of Theorem A). So the engine beats
  2^n on a network only if U < (2+o(1))·n·√(log n). Any conceivable clique algorithm (not just the
  one of Theorem A) still forces E(N) ≥ √(2U) (Lemma 2.2), which is a much weaker, but
  algorithm-independent, statement.
* **Proposition 4.1 (general model: no unconditional barrier).** In Definition 2 as pinned in Lean,
  node tables are arbitrary polynomial-time functions of the whole input. Then (a) per(A) has a
  network with U = 0, g = 1 and one setting iff per ∈ FP, so every unconditional lower bound on U in
  the general model would imply P ≠ P^{#P}; (b) Ryser's formula is a network with U = 0 and one
  node with n-bit settings; (c) "U + Σ_a P_a + log τ = o(n)" is *equivalent* to a 2^{o(n)}-time
  algorithm for the permanent, so in the general model the barrier question *is* the open
  algorithmic question. The only meaningful resource in the general model is the engine exponent
  E(N) ≥ e_K·U + 2gP/K, in which the per-node setting length P enters through the forced number of
  nodes g (g = 3K⁸ in case (i); g ≥ K·log(2gK)/(2ζ²) in case (ii)).
* **Theorem 6.1 (row-local networks, "Model R(s)").** If the rows of A are partitioned into
  clusters of size ≤ s and every node's data depends on A only through the rows of one cluster
  (the skeleton g, c_{a,b} being independent of A), then U ≥ Σ_j log C(n, |V_j|) ≥ n·log(n/s). In
  particular U ≥ n log n when every node reads a single row. With Lemma 2.1 this gives
  E(N) ≥ (½ − o(1))·n·√(log n) for s ≤ n^{1−ε}, i.e. **the engine cannot beat 2^n on any row-local
  network** (Corollary 6.3). The proof is a cut/rank argument; it is the exact analogue of Nisan's
  1991 bound for noncommutative ABPs, with the row-locality replacing Nisan's variable ordering.
* **Theorem 6.2 (vertex-local networks, "Model V(s)", the analogue of our HC network and of [A]'s
  3-SAT network).** If each node reads all entries in the rows *and columns* of one cluster of
  ≤ s left/right vertices, then U ≥ 2n − 2k − (n/k)(log(2k+s+1) + 8s²/k) for every k with 4s ≤ k and
  2k + s ≤ n; so U ≥ (2 − o(1))·n for s ≤ n^{1/3}. **This is only Ω(n) and does not give a barrier**: the
  engine's guarantee is then only ≥ 2^{(1−o(1))n/√log n}.
* **Proposition 3.5 (why Theorem 6.2 stops at 2n).** For a vertex-local cut with k rows and k
  columns on the small side, the best rank bound obtainable from *any* single cut is exactly
  C(2k,k) < 4^k, so no single-cut argument can give more than 2 bits per owned vertex in Model V.
  Getting n log n in Model V needs a genuinely multi-cut (information-flow) argument.

Conjectured (clearly marked, §6.5):

* **Conjecture 6.5.** In Model V(s), U ≥ (1 − o(1))·n·log(n/s). Evidence: it holds in Model R;
  every construction we know of pays ≥ log n per row node; the natural "address routing" obstacle.
* **Gap B (sums of networks).** The theorems are for one network. The engine as used in [A] and in
  our HC paper sums values of polynomially (even n^{O(g)}) many networks. The rank argument loses
  log(#networks) per cut and does not control a single network's U; see §6.6.

Barrier map: §8. Numerical checks of the two rank lemmas: §9 and `scripts/barrier_rank.py`.

---------------------------------------------------------------------------------------------------

## 1. The model, pinned to the Lean definitions

`proof/networks/Eight/SecNetworks_Defs.lean` (quoted in `anthropic-api.md` §1.3):

```
structure Net (g : ℕ) where
  len : Fin g → ℕ                              -- P_a
  S   : Fin g → Finset (List Bool)             -- S_a ⊆ {0,1}^{P_a}
  W   : Fin g → List Bool → ℤ                  -- W_a
  Ψ   : Fin g → Fin g → List Bool → List Bool → ℤ
  c   : Fin g → Fin g → ℕ                      -- c_{a,b}
  f   : Fin g → Fin g → List Bool → List Bool → ℤ
value := Σ_{z ∈ Π S_a} (Π_a W_a(z_a)) · Π_{a<b} Ψ_{a,b}(z_a, z_b)
U     := Σ_a Σ_{b≠a} c_{a,b}                                   -- ordered pairs: every shared bit twice
Is P B: len ≤ P; Ψ symmetric; c symmetric; fact: Ψ_{a,b}(z,z') = Σ_{θ∈{0,1}^{c_{a,b}}} f_{a,b}(z,θ) f_{b,a}(z',θ);
        (i) Σ_{b≠a} c_{a,b} ≤ P; (ii) |W|,|Ψ|,|f| < 2^B.
```

Three facts about the model that decide what a barrier can say.

**(M1) The tables are arbitrary polynomial-time functions of the whole input.** Definition 2(iii)
is `Procs.Give c N P B τ S`: four step machines, given a *context* c ("whatever the calling
algorithm holds in memory", `SecNetworks_Defs.lean` header), answer membership, W, Ψ, f within τ
steps. In the 3-SAT instance the context is the formula (`Given.onFormula`, `formulaProcs`); in
our HC instance it is the prepared graph. Nothing restricts W_a(z_a) to depend on a part of the
input: it is any function of (c, a, z_a) computable within τ steps on states of size ≤ S. The
locality of the known networks (`occNet`: W_a depends on the clauses of cluster a; our Definition
5.1: W_a depends on the edges inside and at V_a) is a feature of the constructions, not of the
model.

**(M2) The skeleton may depend on the input.** In `Coding.occNet g Φ` the number of shared bits
c_{a,b} = |testsBetween Φ a b| is the number of variables shared by clusters a and b; in our HC
network c_{a,b} = w_{ab} + (g − b) with w_{ab} = ⌈e_{ab} log 5⌉ depending on the number of
crossing edges. So "a network for per" means a map A ↦ N(A) with value(N(A)) = per(A), and U, P,
g may vary with A. The engine's bound then holds for each A with that A's U(A); a barrier must
bound U(A) for *some* A in every family of inputs on which the engine is claimed to be fast.

**(M3) The engine's cost is not a function of U alone.** Lemma 8, case (i): g = 3K⁸,
L = ⌈(U + gP/K)/K²⌉, and the time is (K^g + T·2^{2gP/K}·τ)·(g(P+B))^{C₁} with
T = 2^{e_K K² L}(K(L+B′))^{C₀K²} (Theorem A(b)). Case (ii): K | g, c_{a,b} ≤ P/g, K log(2gK) ≤ 2ζ²g,
L = ⌈(U + 2ζgP)/K²⌉, same time formula (`AppRunningTimeStatement.lean` l.102–109,
`GroupingExplicit`). So the exponent is at least e_K·U + 2gP/K in both cases, and P (the per-node
setting length) is charged through g/K.

Standing assumptions for the barrier: P, B, log τ ≤ poly(n) ("tables of poly(n) bits"), so that
the polynomial factors in (1.1) are 2^{O(log n)} and only the exponents matter.

---------------------------------------------------------------------------------------------------

## 2. The engine's exponent

Write e_K for the e_ℓ of Theorem A at the level ℓ with K_ℓ = K.

**Lemma 2.0 (e_K from below).** With ρ = 1/√2 (Theorem B), e_ℓ ≥ ½·2^{−ℓ/2} and
2^ℓ ≤ log K_ℓ + 2x₀, hence e_K ≥ 1/(2√(log K + 2x₀)).

*Proof.* Theorem A(a) (as quoted in `exact-hc-theorem.md` §1): ½ρ^ℓ ≤ e_ℓ and
log K_ℓ = (3x₀+6)2^ℓ − 6ℓ − 2x₀ − 6. So log K_ℓ + 2x₀ − 2^ℓ = (3x₀+5)2^ℓ − 6ℓ − 6 ≥ 59·2^ℓ − 6ℓ − 6 ≥ 0
for all ℓ ≥ 0 (x₀ ≥ 18). ∎

**Lemma 2.1 (engine exponent).** Let N be a network (Definition 2) with U ≥ 1, to which Lemma 8 is
applied with some K in case (i) or case (ii), with the clique algorithm of Theorems A(b)+B. Then the
running time guaranteed by (1.1) is at least 2^{E(N)} with

```
E(N) ≥ e_K·U + 2gP/K ≥ U / (2√(log U + 2x₀)).
```

*Proof.* (1.1) ≥ T·2^{2gP/K} ≥ 2^{e_K K² L + 2gP/K} and K²L ≥ U in both cases, so
E ≥ e_K U + 2gP/K. Lower-bound the second term. Case (i): g = 3K⁸ and P ≥ 1, so 2gP/K ≥ 6K⁷ ≥ 2K.
Case (ii): U ≥ 1 gives some c_{a,b} ≥ 1, and c_{a,b} ≤ P/g gives P ≥ g; K | g gives K ≤ g; so
2gP/K ≥ 2g²/K ≥ 2K. Now if 2K ≥ U/(2√(log U + 2x₀)) we are done; otherwise K < U, so
log K < log U and e_K U ≥ U/(2√(log K + 2x₀)) ≥ U/(2√(log U + 2x₀)) by Lemma 2.0. ∎

Consequence: the engine's guarantee is below 2^n only if U/(2√(log U + 2x₀)) < n, i.e.
U < (2 + o(1))·n·√(log n). **A lower bound U ≥ C·n√(log n) with C > 2 (for large n), or
U = Ω(n log n), is a barrier.** (The o(1) hides x₀; with x₀ = 18 and U ≈ n log n the threshold is
reached for log n ≳ 40.)

**Lemma 2.2 (any clique algorithm).** Replace Theorem A(b) by *any* algorithm that outputs the
value of every (K,λ)-clique within 2^{eK²λ}·poly(K, λ, B) table queries. Then e ≥ (K−1)/K² − o(1)
(as λ → ∞), and consequently E(N) ≥ U(K−1)/K² + 2K ≥ √(2U)·(1 − O(1/K)) for the resulting engine.

*Proof.* In the (K,λ)-clique with Ψ_{w,w′} = [z_w(w′) = z_{w′}(w)], every table entry W_w(z_w),
z_w ∈ {0,1}^{(K−1)λ}, occurs in the value with the nonzero coefficient
Σ (products of the other tables) when all other tables are the constant 1. An algorithm that does
not query it cannot distinguish two table families differing only there, so it makes ≥ K·2^{(K−1)λ}
queries; thus 2^{eK²λ}·poly ≥ 2^{(K−1)λ}. The rest is Lemma 2.1 with e_K replaced by
(K−1)/K² and minimised over K (K ≈ √(U/2)). ∎

So the engine's 1/√log K is what makes the barrier bite; with a hypothetical optimal clique
solver the engine's exponent could in principle drop to Θ(√U), and no U-lower bound of the kind
proved below (U ≤ n²) would be a barrier. We flag this in the barrier map (§8).

---------------------------------------------------------------------------------------------------

## 3. Cuts, ranks, and the permanent

**Lemma 3.1 (cut lemma).** Let N be a network on [g] and (L, R) a partition of [g]. Put
w(L,R) := Σ_{a∈L, b∈R} c_{a,b} (each crossing bit once). Then there are functions
F_L : Θ → ℤ, F_R : Θ → ℤ on Θ := Π_{a∈L,b∈R} {0,1}^{c_{a,b}} with

```
value(N) = Σ_{θ∈Θ} F_L(θ) F_R(θ),
F_L(θ) = Σ_{z_L ∈ Π_{a∈L} S_a} Π_{a∈L} W_a(z_a) Π_{a<a′ ∈ L} Ψ_{a,a′}(z_a,z_{a′}) Π_{a∈L,b∈R} f_{a,b}(z_a, θ_{a,b}),
```

and symmetrically F_R with f_{b,a}. In particular F_L depends only on the data (S_a, W_a, f_{a,·})
of the nodes a ∈ L and on Ψ_{a,a′} for a, a′ ∈ L, which by `fact` is determined by f_{a,a′}, f_{a′,a}.

*Proof.* In `value`, replace each Ψ_{a,b} with a ∈ L, b ∈ R (or b ∈ L, a ∈ R; use `Ψ_symm` and
`fact` for the pair in the order (L-node, R-node)) by Σ_θ f_{a,b}(z_a,θ) f_{b,a}(z_b,θ), and
exchange the finite sums. ∎

So whenever the data of the nodes in L is a function of a part A_L of the input and the data of
the nodes in R of a part A_R, the matrix M[A_L, A_R] := value(N(A)) has rank ≤ 2^{w(L,R)} as a
matrix indexed by (A_L, A_R) (it is Σ_θ u_θ v_θ^T with u_θ = F_L(·,θ), v_θ = F_R(·,θ)). Without such
locality the lemma says nothing: every integer is a rank-1 product.

**Lemma 3.2 (row cut).** Let I ⊆ [n], |I| = k, and let M_I be the matrix indexed by
X ∈ {0,1}^{I×[n]} (rows I of A) and Y ∈ {0,1}^{([n]∖I)×[n]} with M_I[X,Y] := per(A), A = (X;Y).
Then rank M_I = C(n,k).

*Proof.* Laplace expansion along the rows I: per(A) = Σ_{S⊆[n], |S|=k} per(X[I,S])·per(Y[I^c,S^c]).
The functions u_S : X ↦ per(X[I,S]) (|S| = k) are linearly independent: at X = a matching matrix
of I onto S₀ (one 1 per row, columns S₀), u_S(X) = [S = S₀]. Likewise v_S : Y ↦ per(Y[I^c,S^c]).
A bilinear form Σ_S u_S ⊗ v_S with both families independent has rank exactly the number of terms
(it is UV^T with U, V of full column rank). ∎

Remark. Only the matrices with exactly one 1 per row were used for the lower bound, so Lemma 3.2
holds for the matrix restricted to that family 𝓕₁ (on which per(A) = [A is a permutation matrix]).

**Lemma 3.3 (independence of minors).** Let I₀ × J₀ be a rectangle. The functions
X ↦ per(X[I,J]), over pairs (I ⊆ I₀, J ⊆ J₀, |I| = |J|), are linearly independent as functions of
X ∈ {0,1}^{I₀×J₀} (per of the empty matrix is 1).

*Proof.* Order the pairs by |I|. Evaluate at X = a matching matrix M between I and J (zeros
elsewhere): per(M[I′,J′]) ≠ 0 forces I′ ⊆ I and J′ = M(I′), so |I′| ≤ |I| with equality only for
(I′,J′) = (I,J). The evaluation matrix is triangular with unit diagonal. ∎

**Lemma 3.4 (vertex cut).** Let I_L, I_R ⊆ [n] be disjoint sets of rows and J_L, J_R ⊆ [n]
disjoint sets of columns, with |I_L| = |J_L| = k, |I_R| = |J_R| = m ≥ k and k + m ≤ n. Fix the
entries outside I_L×J_L and I_R×J_R as follows: a fixed injection β : I_L → J_R with A[i, β(i)] = 1,
a fixed injection γ : J_L → I_R with A[γ(j), j] = 1, a fixed perfect matching between the n − k − m
remaining rows and the n − k − m remaining columns, and 0 everywhere else. Let M be the matrix
indexed by X ∈ {0,1}^{I_L×J_L} and Y ∈ {0,1}^{I_R×J_R} with M[X,Y] = per(A). Then rank M = C(2k,k).

*Proof.* A perfect matching of A uses, in I_L × J_L, a matching of some I ⊆ I_L onto some
J ⊆ J_L with |I| = |J|; the rows I_L ∖ I must use their only other 1, β; the columns J_L ∖ J
must use γ; the remaining rows I_R ∖ γ(J_L∖J) and columns J_R ∖ β(I_L∖I) (equally many) are matched
inside Y; the rest is matched by the fixed matching. So

per(A) = Σ_{I ⊆ I_L, J ⊆ J_L, |I| = |J|} per(X[I,J]) · per(Y[I_R ∖ γ(J_L∖J), J_R ∖ β(I_L∖I)]).

The X-family is independent by Lemma 3.3; the Y-family too, because (I,J) ↦ (I_R∖γ(J_L∖J),
J_R∖β(I_L∖I)) is injective (β, γ injective) and Lemma 3.3 applies to the rectangle I_R × J_R. The
number of terms is Σ_i C(k,i)² = C(2k,k). ∎

**Proposition 3.5 (the vertex cut cannot give more).** In the setting of Lemma 3.4 with *any*
fixing of the entries outside the two rectangles (or any family of fixings), rank M ≤ C(2k,k).
Moreover, for the partial matrix indexed by (A_L, A_R) with A_L = (X, shared), A_R = (Y, shared′),
defined iff shared = shared′, the minimum rank of a completion equals max over fixings of the
rank, so no single-cut rank argument can beat C(2k,k).

*Proof.* With any fixing, per(A) = Σ_{(I,J)} per(X[I,J]) · c_{I,J}(Y) by the same expansion, so
rank ≤ #{(I,J)} = C(2k,k). For the completion statement: if the block for fixing σ is
U_σ V_σ^T with r columns (r = max rank), the completion [U_σ V_{σ′}^T]_{σ,σ′} has rank ≤ r, and
every completion contains the diagonal blocks. ∎

(Lemmas 3.2 and 3.4 and the maximum in 3.5 are checked numerically for n ≤ 6 in §9.)

---------------------------------------------------------------------------------------------------

## 4. The general model: no unconditional barrier

**Proposition 4.1.** In the model of Definition 2 with tables given by polynomial-time procedures
(M1):

(a) There is a network for per with g = 1, one setting, U = 0, τ = poly(n) if and only if
per ∈ FP. Hence any unconditional lower bound "U ≥ 1" for the general model implies
per ∉ FP, i.e. P ≠ P^{#P} (the 0/1 permanent is #P-complete).

(b) Ryser's formula per(A) = (−1)^n Σ_{S⊆[n]} (−1)^{|S|} Π_i Σ_{j∈S} A_{ij} is a network with
g = 1, S₁ = {0,1}^n, W₁(S) = (−1)^{n−|S|} Π_i (Σ_{j∈S} A_{ij}), U = 0, P = n, τ = poly(n). The
engine's guarantee on it is useless (Lemma 2.1: g must be padded to 3K⁸ nodes, giving
2gP/K = 6K⁷n), but the network exists.

(c) For any network family with U(A), Σ_a P_a ≤ T(A) and τ(A): value(N(A)) is a sum of at most
2^{T} products of poly-time-computable integers, so per(A) is computable in time
2^{T + O(log n)}·τ·poly. Conversely any algorithm with time 2^{t(n)} is a g = 1 network with
U = 0, P = 0 and τ = 2^{t(n)}. Hence in the general model "a network with
U + T + log τ = o(n)" is the same statement as "per ∈ TIME(2^{o(n)})".

*Proof.* (a) W₁(ε) := per(A) is computable within τ steps iff per ∈ FP (modulo the step/time
bookkeeping of `Paper.steps_to_time`). (b), (c) are immediate. ∎

So in the general model the honest statement is: **the engine is a specific way of evaluating the
sum in (c); its guarantee is 2^{E(N)} ≥ 2^{U/(2√(log U + 2x₀))} (Lemma 2.1), and whether a network
with E(N) < n exists is exactly the open question whether this engine beats 2^n for the
permanent.** No lower-bound technique applies without a structural restriction, because Lemma 3.1
needs both sides of a cut to see different parts of the input. Note also that the conditional
lower bound of Dell–Husfeldt–Marx–Taslaman–Wahlén (no 2^{o(n)} algorithm for the 0/1 permanent
under #ETH) cannot be invoked here: [A]'s machines compute the number of satisfying assignments
(`StOccNetCounts`; counting forms in `proof/consequences/ThmCount`, `CountKSat`), so the same
engine that refutes ETH refutes #ETH, and the DHMTW hypothesis is false in this world.

The restriction that makes lower bounds possible, and that every known construction satisfies, is
locality: §5.

---------------------------------------------------------------------------------------------------

## 5. Local-gadget models

A *network family for per* is a map A ↦ N(A) (A ∈ {0,1}^{n×n}) with value(N(A)) = per(A) and
N(A).Is P B for all A, P, B, log τ ≤ poly(n). Its *skeleton* is (g, (c_{a,b})). The data of node a
is (P_a, S_a, W_a, (f_{a,b})_{b≠a}); by `fact` it determines Ψ_{a,b} together with the data of b.

**Definition 5.1 (Model R(s), row-local).** The rows [n] are partitioned into clusters
V_1, …, V_t with |V_j| ≤ s; every node a has a cluster j(a) (or is a *routing node*, reading
nothing); the skeleton is independent of A; the data of node a depends on A only through the rows
V_{j(a)} of A (through nothing, for a routing node).

**Definition 5.2 (Model V(s), vertex-local).** The 2n vertices [n] ⊔ [n]′ (rows and columns)
are partitioned into clusters V_1, …, V_t of size ≤ s, with k_j rows and k′_j columns in V_j;
the skeleton is independent of A; the data of node a depends on A only through the entries
(i, j) with i ∈ V_{j(a)} or j′ ∈ V_{j(a)} (the edges incident to the cluster). Routing nodes as
before.

Model R(s) ⊆ Model V(s) (clusters with k′_j = 0), but Theorem 6.2 is weaker than 6.1 on it; the
two theorems have different hypotheses and the stronger one applies when it applies.

Where the known networks sit:

* Our HC network (Definition 5.1 of `exact-hc-theorem.md`): node a = vertex cluster V_a; W_a =
  σ_a χ_a I_a depends on the edges inside V_a and the crossing edges at V_a; f_{a,b} depends on
  the labels of E(a,b). For a bipartite graph with left and right vertices this is Model V with
  the cluster V_a; for a cluster of left vertices only it is Model R. **Its skeleton depends on
  the input** (c_{a,b} = w_{ab} + g − b, w_{ab} = ⌈e_{ab} log 5⌉, through the number of crossing
  edges) — see Remark 6.4 for what that costs.
* [A]'s 3-SAT network (`Coding.occNet`): node a = block of m̄ consecutive clauses; W_a depends
  on the clauses of the block; c_{a,b} = number of variables with consecutive occurrences in blocks
  a and b, so again an input-dependent skeleton; in the "incidence-matrix" picture (clauses ×
  variables) it is clause-row-local with the variable identities shared through the tests.
* The "permutation network" (row node i chooses σ(i), column node j holds s_j, 1-bit edge tests,
  U = n(n−1)): Model R ⊔ C with s = 1 for the row part; not Model R (column nodes read columns),
  but Model V(1).
* Ryser's single node (§4(b)): Model R(n), one cluster — Theorem 6.1 gives U ≥ n log(n/n) = 0,
  consistent.

---------------------------------------------------------------------------------------------------

## 6. Theorems

**Theorem 6.1 (Model R).** Let A ↦ N(A) be a network family for per in Model R(s) with clusters
V_1, …, V_t. Then

```
U ≥ Σ_{j=1}^{t} log C(n, |V_j|) ≥ n · log(n/s).
```

In particular U ≥ n log n if every node reads one row (s = 1). The bound holds already if
value(N(A)) = per(A) only for the matrices A with exactly one 1 per row (and the skeleton is
constant on them).

*Proof.* Fix j and cut [g] into L := {a : j(a) = j} and R := the other nodes together with the
routing nodes. The data of every a ∈ L is a function of X := A[V_j, ·], the data of every b ∈ R a
function of Y := A[V_j^c, ·] (routing nodes: constant). By Lemma 3.1, M_{V_j}[X,Y] = per(A) is
Σ_θ F_L(X,θ) F_R(Y,θ) over θ ∈ {0,1}^{w_j}, w_j := Σ_{a∈L, b∉L} c_{a,b}; so
2^{w_j} ≥ rank M_{V_j} = C(n, |V_j|) (Lemma 3.2). Summing over j: the ordered pair (a,b) with
j(a) = j, j(b) ≠ j (or b routing) is counted in w_j and in no other w_{j′}, so
Σ_j w_j ≤ Σ_{(a,b): a≠b} c_{a,b} = U. Finally C(n,k) ≥ (n/k)^k gives log C(n,k_j) ≥ k_j log(n/k_j)
≥ k_j log(n/s), and Σ_j k_j = n. (Every row lies in a cluster: a row read by no node would make
the value independent of that row, but per is not.) The last sentence: Lemma 3.2's lower bound
only evaluates at one-1-per-row matrices. ∎

**Theorem 6.2 (Model V).** Let A ↦ N(A) be a network family for per in Model V(s). Then for every
integer k with 4s ≤ k and 2k + s ≤ n,

```
U ≥ 2n − 2k − (n/k) · ( log(2k + s + 1) + 8s²/k ).
```

Hence U ≥ 2n − o(n) whenever s ≤ n^{1/3} (take k = ⌈s² log n⌉ + 4s), and for s = 2 (one left and
one right vertex per node) U ≥ 2n − O(n log log n / log n). The bound holds already if
value(N(A)) = per(A) only for partial permutation matrices A.

*Proof.* Step 1 (grouping). Process the clusters in an order chosen on the fly, maintaining the
imbalance D := Σ (k_j − k′_j) over the clusters processed so far; |D| ≤ s is kept as follows: if
D > 0 take next an unprocessed cluster with k′_j ≥ k_j (one exists, since the unprocessed
clusters have total imbalance −D < 0), if D < 0 one with k_j ≥ k′_j, if D = 0 any. Cut the
sequence into consecutive groups G, closing a group as soon as its total size s_G = k_G + k′_G
reaches 2k; so 2k ≤ s_G < 2k + s for every closed group, the groups' imbalances satisfy
|k_G − k′_G| ≤ 2s, the number of closed groups is ≤ 2n/(2k) = n/k, and the unclosed remainder has
size < 2k.

Step 2 (one group). Let G be a closed group, L the nodes of its clusters, R the rest (routing nodes
to R). Let I_L (k_G rows) and J_L (k′_G columns) be its vertices, I_R := I_L^c, J_R := J_L^c. The
data of L depends only on entries in rows I_L or columns J_L, the data of R only on entries in
rows I_R or columns J_R; private to L is I_L × J_L, private to R is I_R × J_R. Fix the shared
blocks as in Lemma 3.4: an injection β : I_L → J_R (possible since k_G ≤ n − k′_G, i.e. s_G ≤ n,
which holds as s_G < 2k + s ≤ n), an injection γ : J_L → I_R, zeros elsewhere. Exactly as in
Lemma 3.4, per(A) = Σ_{I⊆I_L, J⊆J_L, |I|=|J|} per(X[I,J]) · per(Y[I_R∖γ(J_L∖J), J_R∖β(I_L∖I)])
(the two index sets have sizes (n−k_G)−(k′_G−|J|) and (n−k′_G)−(k_G−|I|), equal), and no extra
matching is needed. Both families are independent (Lemma 3.3), so on this family of inputs the
matrix (X,Y) ↦ per(A) has rank Σ_i C(k_G,i)C(k′_G,i) = C(s_G, k_G), while by Lemma 3.1 it has
rank ≤ 2^{w(L,R)}. Hence w(L,R) ≥ log C(s_G, k_G). With d := |k_G − k′_G| ≤ 2s:
log C(s_G, k_G) ≥ s_G·H(k_G/s_G) − log(s_G+1) ≥ s_G − 4d²/s_G − log(s_G+1) for d ≤ s_G/4, using
H(½ + x) ≥ 1 − 3.85x² for |x| ≤ ¼. Since d ≤ 2s ≤ s_G/4 (k ≥ 4s) and s_G ≥ 2k:
w(L,R) ≥ s_G − log(2k + s + 1) − 8s²/k.

Step 3 (sum). As in Theorem 6.1, Σ_G w(L_G, R_G) ≤ U (each ordered pair between different groups
is counted once; pairs inside a group or involving the remainder are dropped). Σ_{closed G} s_G ≥
2n − 2k and there are ≤ n/k closed groups. ∎

**Corollary 6.3 (barrier for row-local networks).** Let A ↦ N(A) be in Model R(s) with
s ≤ n^{1−ε}. Then for every admissible K the engine's guarantee satisfies

```
E(N) ≥ n·log(n/s) / (2√(log(n log n) + 2x₀)) ≥ (ε/2 − o(1)) · n · √(log n)  ≫  n,
```

so the engine's own bound is 2^{ω(n)}: **it cannot certify a running time below 2^n on any
row-local network, for any choice of K and any clique algorithm of the Theorem A type.** With
Lemma 2.2 instead (any clique algorithm whatsoever): E(N) ≥ √(2n log(n/s)) only — no barrier.

*Proof.* Theorem 6.1 and Lemma 2.1, U ≤ gP ≤ poly(n) so log U = O(log n). ∎

**Remark 6.4 (input-dependent skeletons).** Theorems 6.1 and 6.2 assume the skeleton is constant
on the test family (one-1-per-row matrices, resp. partial permutation matrices). For an HC-style
skeleton, c_{a,b} is a function of the number of 1s of A in the block V_a × V′_b, which is not
constant on the test families. What survives: for any fixed *profile* (number of 1s in every
block), the test family of Lemma 3.2 restricted to that profile still contains all S whose
intersection with each column cluster has the prescribed size, so for Model R with one row per
node and column clusters of size ≥ n^{δ} the rank is still n^{Ω(1)} per row cut and the bound
becomes U ≥ Ω(δ·n log n) for the worst A of that profile. We have not written this out in
general; it is a routine but tedious refinement and is listed as Gap A in §8.

**Conjecture 6.5 (Model V).** Every network family for per in Model V(s) has
U ≥ (1 − o(1))·n·log(n/s); in particular U ≥ (1−o(1)) n log n for s = O(1).

Evidence and obstacle. (i) The statement holds in Model R (Theorem 6.1). (ii) Every construction
we know in Model V pays ≥ log n per row vertex: the row node must "address" the column node it
is matched to, and the address has log n bits; Ryser/Glynn-type formulas replace the address by an
n-bit set S that every node must see. (iii) Proposition 3.5 shows that the single-cut rank method
is *exactly* exhausted at 2 bits per vertex, because the other side of the cut reads the whole
row and column of each vertex of the small side except the diagonal entry — the cut is a
"number-on-forehead" situation (the cut around vertex i hides from the rest only A_{ii}). A
proof of 6.5 must use several cuts jointly; the natural candidate is an information-flow /
pebbling argument along the lines of Hrubeš–Wigderson–Yehudayoff's treatment of noncommutative
*circuits* (as opposed to ABPs), where exactly this difficulty (no single cut sees a variable
partition) is what blocks lower bounds for the noncommutative permanent (their reduction to the
sum-of-squares problem). We regard 6.5 as plausible but it is not within reach of the methods
here.

**6.6 Gap B (sums of networks).** [A]'s algorithm and ours sum the values of several networks
(our Lemma 6.1 branches over n^{O(g)} networks). If per(A) = Σ_{t≤T} value(N_t(A)) with every N_t in
Model R(s) with the same clusters, Lemma 3.1 only gives Σ_t 2^{w_j^{(t)}} ≥ C(n,k_j) for each
cluster j, hence max_t w_j^{(t)} ≥ log C(n,k_j) − log T per cluster, but the maximising t may differ
across j and we cannot conclude that one network has U ≥ n log(n/s) − n log T. (Encoding the sum as
one network with a selector node costs 2(g+1)⌈log T⌉ shared bits, which is too much when g ≈ n.)
So the barrier in Corollary 6.3 is for one network; whether polynomially many row-local networks
can jointly compute per with max_t U^{(t)} = o(n log n) is open. We expect not.

---------------------------------------------------------------------------------------------------

## 7. Relation to noncommutative / read-once lower bounds

* **Nisan 1991** (Lower bounds for non-commutative computation, STOC'91). For a noncommutative
  polynomial f of degree n, the width of an ABP computing f at layer k equals the rank of the
  matrix M_k(f) (rows: prefixes of length k, columns: suffixes of length n − k, entry = coefficient
  of the concatenation). For the permanent with the rows in the order 1, …, n, M_k has rank C(n,k)
  (prefix = a partial injection of rows 1..k, suffix of rows k+1..n, nonzero iff the images are
  complementary), so the width at the middle is ≥ C(n, n/2) and the size is 2^{Ω(n)}. **Lemma 3.2
  is exactly Nisan's rank computation**, read as a statement about functions on 0/1 matrices (we
  need only the one-1-per-row matrices, on which the prefix/suffix split is the row split). What
  replaces Nisan's ordering is row-locality: in Model R every cluster cut *is* a prefix/suffix cut
  of the variables, in any topology. The n log n (rather than Nisan's n) comes from summing n
  unbalanced cuts of width log n each, which is available because U charges every cut of the
  network and not only the widest layer.
* **Any-order ROABPs / partial derivatives.** For a read-once oblivious ABP in an arbitrary
  variable order, the relevant quantity is the rank of the coefficient matrix for the induced
  variable partition; Nisan's argument extends to any order via the dimension of partial
  derivatives (Bhargava–Tengse, FSTTCS 2024, note this connection and strengthen it to commutative
  ROABPs). Model V is the analogue of an *unknown and non-row-aligned* partition, and
  Proposition 3.5 is the statement that for the permanent the row/column-overlapping partitions
  that Model V induces have rank only C(2k,k): the permanent is *not* "hard under every
  partition" in the sense needed, which is exactly why Model V resists.
* **Raz–Shpilka 2005** (deterministic PIT for noncommutative formulas and ABPs) is an upper
  bound using the same partial-derivative matrices; it is relevant only as a reminder that the
  rank characterisation is tight for ABPs, i.e. that in Model R an *upper* bound would have to come
  from a network whose every cluster cut has rank exactly C(n, k_j) — a tree of row-cuts with
  log C(n,k) bits each; U = Θ(n log n) is the natural guess for the truth in Model R(1), but we
  have not constructed a network with U = O(n log n) (the obvious routing constructions give
  O(n log² n), the pairwise-test construction n²).
* **Hrubeš–Wigderson–Yehudayoff 2011** (JAMS): lower bounds for general noncommutative *circuits*
  for the permanent reduce to the sum-of-squares problem and are open; general circuits have no
  single cut that separates variables. Our general model (§4) and Model V (Conjecture 6.5) are
  the analogues: in the general model nothing is provable without separating P from P^{#P}; in
  Model V the single-cut method is exhausted (Proposition 3.5).
* **Dell–Husfeldt–Marx–Taslaman–Wahlén 2014** (ACM TALG): no 2^{o(n)} algorithm for the 0/1
  permanent under #ETH. Not usable here (§4), since the engine refutes #ETH.

Sources checked by web search (statements only): Nisan's result and the rank characterisation
([survey](https://arxiv.org/pdf/2406.06217), [lecture notes](https://www.csa.iisc.ac.in/~chandan/courses/arithmetic_circuits/notes/noncomm.pdf)),
any-order ROABPs and partial derivatives ([Bhargava–Tengse](https://arxiv.org/html/2407.10143v1)),
HWY ([JAMS](https://www.doi.org/10.1090/S0894-0347-2011-00694-2)),
DHMTW ([arXiv 1206.1775](https://ar5iv.arxiv.org/html/1206.1775)).

---------------------------------------------------------------------------------------------------

## 8. Barrier map

| Model (what the tables may depend on) | Lower bound on U | Engine exponent (Lemma 2.1) | Barrier? | Status |
|---|---|---|---|---|
| General (Def. 2 as in Lean: any poly-time function of A) | none possible unconditionally (Prop. 4.1); U = 0 networks exist (Ryser) | ≥ U/(2√log U), but U can be 0 with P = n | no; the question is the open problem itself | proved |
| Model R(s), one network, skeleton fixed on one-1-per-row matrices | U ≥ Σ_j log C(n,|V_j|) ≥ n log(n/s) (Thm 6.1) | ≥ (ε/2 − o(1)) n√log n for s ≤ n^{1−ε} | **yes** (Cor. 6.3) | proved |
| Model R(1) with any clique algorithm (Lemma 2.2) | n log n | ≥ √(2 n log n) | no | proved (no barrier) |
| Model R, input-dependent skeleton (HC-style c_{a,b}) | Ω(δ n log n) expected via profiles | — | expected yes | Gap A (sketched, Rem. 6.4) |
| Model R, sum of T networks | per cut: max_t w ≥ log C − log T | — | unknown | Gap B (§6.6) |
| Model V(s), s ≤ n^{1/3} (HC-type, SAT-type) | U ≥ (2 − o(1)) n (Thm 6.2); single cuts exhausted (Prop. 3.5) | ≥ (1 − o(1)) n/√log n | **no** | proved bound; n log n conjectured (6.5) |

Which assumptions the known networks satisfy: our HC network and [A]'s SAT network are vertex-
/clause-local (Model V type) with input-dependent skeletons and are used inside a sum over
networks; so a barrier that covers them needs Conjecture 6.5 **and** Gaps A and B closed. The
row-local Theorem 6.1 covers the natural "row node chooses its column" designs for the permanent
and every design in which a node's table is computed from the rows of a cluster of left vertices.

What this means for the 2^{o(n)} attempt (the other agent's job): a network for per that the engine
can certify below 2^n must either (i) let some node's table depend on more than the rows of a
cluster of n^{1−o(1)} rows — e.g. on rows *and* columns (Model V), where only Ω(n) is proved — or
(ii) use a sum of many networks, or (iii) leave the engine (a better clique algorithm, Lemma 2.2).
Within Model R(s) it needs s ≥ n·2^{−(2+o(1))√log n}, i.e. clusters of almost all rows.

---------------------------------------------------------------------------------------------------

## 9. Numerical checks

`scripts/barrier_rank.py` computes exact ranks over ℚ (Fractions):

* row cut (Lemma 3.2): rank M_I = C(n,k) for (n,k) ∈ {(3,1),(4,1),(4,2),(5,1),(5,2)} (sampled rows/
  columns give the lower bound, which meets the proven upper bound C(n,k));
* vertex cut (Lemma 3.4): rank = C(2k,k) = 2, 6, 6, 20 for (n,k) = (4,1), (4,2), (5,2), (6,3);
* maximum over all 2^{2k(n−k)} fixings of the shared blocks (Prop. 3.5) is C(2k,k) for
  (n,k) = (4,1), (4,2).

Output is in `scripts/barrier_rank.out`.

---------------------------------------------------------------------------------------------------

## 10. What is proved, what is not (checklist)

Proved here: Lemmas 2.0–2.2, 3.1–3.4, Proposition 3.5, Proposition 4.1, Theorems 6.1, 6.2,
Corollary 6.3. Inputs taken from [A] without re-proof: the quoted forms of Lemma 8 (case (i)/(ii)
parameters, (1.1)) and Theorem A(a),(b) (as in `exact-hc-theorem.md` §1; the Lean statements
`groupingExplicit`, `recursionSolves`, `Cases`, `Lof` are the ones summarised in
`anthropic-api.md` §2), in particular the lower bound e_ℓ ≥ ½ρ^ℓ of Theorem A(a) and the
constant x₀ ≥ 18.

Not proved: Conjecture 6.5 (Model V, n log n); Gap A (input-dependent skeletons, sketched);
Gap B (sums of networks); any upper bound U = O(n log n) in Model R.
