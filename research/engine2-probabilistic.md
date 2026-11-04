# The engine rate, probabilistic / structural side: six mechanisms, two new negative theorems, one ranking

4 Nov 2026. Companion to `permanent/clique-evaluation.md` (direct attacks, §4.3 the two-grouping cap),
`permanent/rate.md` (α' = log₂(1/ρ)), `permanent/rho-lower-bound.md` (ρ ≥ 1/√2 for graded pieces),
`permanent/parity-barrier.md` (OpenAI's template), `permanent/permanent-attack.md` §3/§8 (what the dense
permanent needs), `tutte-plane.md` §4.1 (what e_K = o(1/log K) unlocks). Algebraic routes (tensor rank,
representation theory, new pieces) are the other agent's; nothing here duplicates them.
Scripts: `scripts/engine2p_*.py` (outputs `.out`, each prints PASS/FAIL). Lean (scratch, all `sorry`-free,
no `native_decide`): `lean/EthFollowup/Scratch/Engine2p/Accounting.lean`, `Instances.lean`.
Tags: **[R]** proved here, **[L]** Lean-proved (general), **[Li]** Lean-checked on instances, **[N]** numerical,
**[C]** heuristic.

## 0. Summary

**Problem.** (K,λ)-clique: Z = Σ_{x ∈ ({0,1}^λ)^E} Π_a T_a(x|_{δ(a)}), cost 2^{e_K K²λ}. Brute force e = (K−1)/(2K);
query bound (K−1)/K²; Anthropic e_K = Θ((log K)^{−1/2}); proved cap e_K ≥ c/log K for every recursion of
Theorem A's shape (two groupings, min, 2^{o(λ)} pieces per rectangle). Target: e_K = o(1/log K), or a proof that
no "oblivious" algorithm has it.

**Verdict.** None of the six mechanisms asked for (randomised hashing / isolation / collision sieves;
structural restriction to low-rank tables; communication / oblivious lower bounds; representative sets;
non-uniform dense/sparse schedules; fine-grained hypotheses) changes the rate, and for each the reason is an
exact accounting (§1–§6). Two of the kills are new theorems that go beyond what the project had:

* **Theorem A (covering bound, §7) [R]+[N].** The two-grouping cap ρ ≥ 1/2 of `clique-evaluation.md` §4.3
  extends to *every* family 𝒢 of groupings of the g² grid nodes (all set partitions, chosen adaptively per
  term, randomised or not): the level saving is ρ_eff ≥ 1/2 − O(√(log|𝒢|/|R|)) − (free fraction) ≥
  1/2 − O(√(log g)/g) for |𝒢| ≤ Bell(g²). Proof: probabilistic method (random term ι, Hoeffding, union bound
  over 𝒢) plus a counting lemma: under any grouping into blocks of size ≤ g at most a 2/g fraction of the
  rectangles see the free cut (xv|yu). Checked exactly at g = 3 (all 12 644 partitions) and on all
  2 627 625 balanced partitions at g = 4, where the adversary still forces exactly |R|/2 (`engine2p_covering.py`).
  Consequence: **α' ≤ 1 for every "expand into 2^{o(N)} terms, pick the best grouping" level**, randomised
  included; the ceiling 2^{O(U/log U)} of the framework is not a feature of the row/column pair.
* **Lemma B (decomposition convexity, §1) [L].** Any algorithm that decomposes the equality tensor on edges
  into terms of smaller rank (random hashes, prefix fixing, random projections, Walsh slices) and recurses on
  each term as a *general* clique instance has exponent ≥ e K²λ, with equality only at brute force. Randomness
  cannot enter through the equality tensor; it can only enter through structure of the *tables*, which the
  model treats as black boxes. Every "sieve" (Björklund's collision gain included) is a multiplicative
  2^{−o(N)} saving, never a rate.

Smaller exact facts: the schedule is irrelevant to the rate (optimal schedules beat Anthropic's by a factor
1.7 in e, never in α'; §5, [L] for the inequality, [N] for the DP); structural restriction to low cut rank gives
exactly the subset DP (e = Θ(κ), κ = cut-rank fraction) and the permanent sits at κ = Θ(1/log K), so
"e = o(κ) for low-rank tables" is per(A) ∈ 2^{o(n)} restated (§2); decision instead of counting does not lower
the cap (supports of permutation matrices force full rank; §4); isolation costs only O(K(λ + log K)) extra
bits, so randomised decision reduces to ⊕-clique evaluation — but the ρ ≥ 1/2 and covering caps are
field-independent (§1.4); no standard hypothesis gains or loses from e_K = o(1/log K): "global witness"
problems (OV, k-SUM, Subset Sum, k-Clique, Hyperclique) cost n^{Ω(k√K)}-type factors in any clique encoding
(the pairwise-check lemma of §6), while local ones are already subexponential.

**Ranking (§8):** (1) Theorem A → write the general "expansion-class" lower bound (the negative result the
brief asks for; the remaining gap is non-product terms and sub-instances not arising from groupings);
(2) ⊕-pieces over F₂ (the only place where randomisation changes the *problem*; open, but capped at α' = 1);
(3)–(6) closed. **Single most promising next step:** §8.

## 1. Mechanism 1: randomised algorithms (hashing, restrictions, isolation, collision sieves)

### 1.1 What randomness can act on [R]
Z is linear in each table and in the equality tensor 𝒯 = ⊗_e I_D. An algorithm that is "oblivious" to the
tables (reads them, does arithmetic) can randomise only (a) the decomposition of 𝒯, (b) the grouping /
contraction schedule, (c) the arithmetic itself (e.g. modular reduction, interpolation points). (c) is
constant-factor: Z is an integer < 2^{B+E λ}·…, CRT over poly many primes or one random prime of poly bits
changes nothing in the exponent; interpolation (T_a ↦ T_a + tS_a, Z(t) of degree K) needs K+1 equally hard
evaluations. (b) is §7. (a) is Lemma B:

**Lemma B (decomposition convexity) [L: `Engine2p.split_exponent_ge`, `brute_force_is_E`].** Suppose on every
edge I_D = Σ_{j≤m} A_j with rank A_j ≤ D/m (any field; m ≥ 2^{λ−λ'} terms of rank 2^{λ'}), and each of the m^E
resulting instances is evaluated as a (K, λ − log₂m)-clique at exponent e. Then the total exponent is
E log₂m + eK²(λ − log₂m) ≥ eK²λ, because E = K(K−1)/2 ≥ eK² for every achievable e (e ≤ (K−1)/(2K)). Equality iff
e is brute force. The same inequality with "λ₁ bits brute-forced per edge" is the prefix lemma of §5. ∎
`engine2p_schedule.py` (A),(B): minimum of the difference over a grid of (K, e, λ, split) is exactly 0 (PASS).

Random *hashes* h_e : {0,1}^λ → [m]: the collision matrix E_h = [h(x) = h(v)] has rank m and I = E_h − (E_h − I);
the correction E_h − I is block-diagonal with blocks J_s − I_s, det = (−1)^{s−1}(s−1) ≠ 0 for s ≥ 2
[Li: `detJI2/3/4`], so it has *full* rank D: the "colliding pairs" carry all the information. Averaging over a
pairwise-uniform family gives E_h[E_h] = I + (J − I)/m exactly [Li: `hash_identity_m2`, m = 2, all 16 maps
Fin 4 → Fin 2], hence I = (m/(m−1))(E_h[E_h] − J/m); expanding the product over edges gives 2^E signed terms,
each an expectation over independent hashes on its edges — the expectation is a sum over the family
(size ≥ D² per edge), i.e. ≥ 2^{2λE} terms: worse than brute force. Walsh/Fourier slices are the same (Lemma B
with A_j = projectors; `clique-evaluation.md` §4.4). **Dead.**

### 1.2 Björklund's collision gain and "below all subsets" [R]
Fix the labels outside a node set S: Z = Σ_{x_out} (Π_{c∉S} T_c)·Z_S(T|_{x_out}), Z_S an (|S|,λ)-clique with
restricted tables. The gain of arXiv 1211.0391 is that the number of *distinct* small instances
(p^{|S|·2^{(|S|−1)λ}} over F_p) is below the number 2^{λ(E − C(|S|,2))} of outer labellings, so one tabulates and
counts multiplicities. Here that requires |S| = 2 and 2^{λ+1} log p < λK²/2, i.e. λ ≤ 2 log K − O(log log K),
and the multiplicity vector c(f,g) = Σ_{x_out} Π_{c∉S}T_c·[T_a|_{x_out} = f][T_b|_{x_out} = g] is itself a
(K,λ)-clique with two vector-valued tables of output dimension p^{2^{λ+1}} — as hard as Z (Z is a linear
functional of c). Björklund computes c by a DP that uses the *linear* structure of walk counts in the
permanent; general tables have no such structure, and for #SAT tables the same gain is the Chan–Williams
2^{n − n/O(k)}: a saving of rate 1, i.e. a factor 2^{−o(N)} on top of any exponent. Iterating it inside the
recursion: the level's sub-instances are the ι-terms, 2^{Θ(N)}-bit objects, pairwise distinct; no collisions.
**Constant-factor at best; the rate is untouched.**

### 1.3 Isolation for decision (SAT, Hamiltonicity) [R]
Decision needs Z ≠ 0 for non-negative tables. Valiant–Vazirani / Mulmuley–Vazirani–Vazirani: random weights
w_e : {0,1}^λ → [2ED] on (edge,label) pairs isolate a unique minimum-weight satisfying labelling w.p. ≥ 1/2.
The constraint "total weight = W" is a global linear constraint, but in a clique it is cheap: route partial sums
along a Hamiltonian cycle of K_K (node a adds w_{ab}(x_{ab}) for b > a), adding log(K²·2ED) = λ + O(log K) bits to
K edges: U' = U(1 + O(1/K)) (Lemma 8 regroups). W ranges over ≤ K²·2ED = 2^{λ+O(log K)} values, a factor
negligible against 2^{eK²λ}. So **randomised decision at rate e reduces to evaluating Σ_x [w(x)=W]Π T_a mod 2
at rate e**: a ⊕-(K,λ)-clique. This is the one place where randomisation changes the *problem*: over F₂.

### 1.4 ⊕-cliques: pieces over F₂ [R]+[N]
Everything in Theorem A is field-agnostic except Theorem B's pieces: Σ_s Q_s = h!·Id (Lemma 10), and h! ≡ 0
mod 2 for h ≥ 2 (`engine2p_f2pieces.py`), so the Appendix-B pieces do not exist over F₂ (nor over F_p for p ≤ h);
their binomial coefficients C(2h,i) collapse by Lucas. Conversely the caps are field-independent: ρ ≥ 1/2
(rank subadditivity over any field, `rho-lower-bound.md` Cor. 2.2) and Theorem A below. So ⊕-pieces could at
best give α' = 1 (2^{O(U/log U)}), a landmark but not the target. Exhaustive data at λ = 1 (SWAP on two bits,
all 65 536 two-piece decompositions over F₂; 3-piece with two low-rank pieces; F₃ restricted): the optimum
is the trivial row split (two pieces of row-rank 2 and col-rank 2, product 4 = N²), the ρ = 1/2 profile, over
every field — the question only becomes field-sensitive at λ ≥ 2 with |I| ≪ 2^λ pieces, beyond exhaustive
search. **Open, algebraic, flagged for the other agent; capped at α' = 1 regardless.**

**Mechanism 1 verdict: killed for the rate.** Lean status: Lemma B [L]; hash identity and J−I invertibility
[Li]; isolation bit-count [R, not formalised]; ⊕-pieces: not formalised (open).

## 2. Mechanism 2: structural restriction to "low piece-rank" tables

### 2.1 Which parameter the permanent's tables have [R]
Laplace network (`permanent-attack.md` §3): row node a (rows R_a, p = n/h) sees the labels T_{ab} ⊆ C_b
(pattern-wise, Σ_b lg C(q, N_{ab}) ≈ P = (n/h) lg(eh) bits) and has table per(A[R_a, ∪_b T_{ab}]). Across any
cut of its legs into (L | R): per(A[R_a, S_L ∪ S_R]) = Σ_{I ⊆ R_a} per(A[I, S_L])·per(A[R_a∖I, S_R]), so
**cut rank ≤ 2^{p} = 2^{P/lg(eh)}** (and this is a nonnegative factorisation, so nonnegative rank is the same;
the column node [T_{·b} partition C_b] has Boolean cut rank ≤ 2^{q}). A generic table has cut rank 2^{P/2}.
Define κ := (log cut rank)/P; the permanent's tables have κ ≈ 1/lg(eh) ≈ 1/lg K. In the Walsh basis the same
table is a degree-p multilinear polynomial in the n column indicators ("Walsh sparsity" C(n,p) ≤ 2^{p lg(eh)}),
and the partition constraint relaxed by inclusion–exclusion over sets is Ryser. CP (tensor) rank, by contrast,
is full: Σ over ordered partitions of R_a into labelled blocks, h^{p} = 2^{P}.

### 2.2 What low cut rank buys, exactly [R]
Hierarchical (tree-tensor) cut rank 2^{κP} at every node lets a contraction order keep intermediate
tensors T_S of rank ≤ 2^{κ Σ_{a∈S} P_a} across (S | S^c) *provided the hidden indices are explicit and
consistent along the order*; for the Laplace network the hidden index is "set of columns used so far" and the
order is the row groups: this is the 2^n subset DP (Bellman–Held–Karp / Ryser's twin). In clique units
U ≈ 16 n lg K, so e_DP = n/(K²λ) ≈ 1/(16 lg K) = Θ(κ). Hence:

**Proposition 2.1.** For tables of cut-rank fraction κ, e_K(𝒞_κ) ≤ O(κ) + O(1/K) by the DP along the explicit
factorisation, and the dense permanent is the instance κ = Θ(1/log K). Reaching per(A) ∈ 2^{o(n)} through the
engine needs e_K(𝒞_κ) = o(κ) on that instance — which *is* the statement "beat the subset DP by an unbounded
factor in the exponent". No parameter among {cut rank, nonnegative rank, Boolean rank, Walsh sparsity, CP
rank} separates the permanent's tables from the hardness: each one recovers exactly one classical 2^{Θ(n)}
algorithm (DP, Ryser) and nothing below. ∎

Could a restricted-class rate improvement still be *useful* if it reached only e = o(1/log K) for κ ≤ 1/log K?
Yes — that is precisely the target restricted to the only instance we care about; but there is no reason
the restriction makes it easier: the general ρ ≥ 1/2 and covering caps (§7) hold for the equality tensor and
never look at the tables. **Mechanism 2 verdict: no useful restriction; equivalent to the problem.**
Lean: not formalised (Proposition 2.1 is an accounting statement about a model, not a finite identity).

## 3. Mechanism 3: communication / oblivious lower bounds

### 3.1 What the model is [R]
"Access tables by point queries, do arithmetic" = arithmetic circuits (over ℚ or ℤ) for the degree-K
set-multilinear form Z in N_in = K·2^{(K−1)λ} inputs. Anthropic's algorithm is a *set-multilinear circuit*
(every gate is multilinear and homogeneous in the partition of inputs by node: modified tables are linear in
one table, supernode tables are products over disjoint node sets, sums over ι add such terms). So the natural
lower-bound model is set-multilinear circuits of unbounded depth.

### 3.2 What is provable, and what the target costs [R]
* Query model: e ≥ (K−1)/K² (tight for queries). Nothing more in that model (`barrier.md` Lemma 2.2).
* Set-multilinear **ABPs / ROABPs** in any order (Nisan's rank method): the partial-derivative matrix between
  nodes S and S^c has rank 2^{λ|S||S^c|} (the labels of the crossing edges are read on both sides), so width
  ≥ 2^{λK²/4}: e ≥ 1/4 — the flattening bound of `clique-evaluation.md` §4.2, and the FMM level stays at 2/9.
* Unbounded-depth set-multilinear circuits: the best known lower bounds for *any* explicit polynomial are
  Ω(n^{4/3}/log² n) for multilinear circuits (Raz–Yehudayoff) and superpolynomial only at constant depth
  (Limaye–Srinivasan–Tavenas). The target "e_K ≥ c/log K for all algorithms" at λ = 1 is a lower bound of
  2^{cK²/log K} = N_in^{Ω(K/log K)} for a degree-K polynomial in N_in = K2^{K−1} variables: a super-polynomial
  circuit lower bound for an explicit family (growing degree), far beyond current technique even in the
  set-multilinear model. At K = 3 it contains ω > 2.
* Adversary arguments for sums over cliques work only against algorithms whose sub-computations are
  themselves clique sums with the same equality structure — that is the expansion class, and there the bound
  is Theorem A (§7), which is the honest "oblivious" lower bound we can prove: it covers any family of
  groupings, adaptive or randomised, but not non-product terms.

**Mechanism 3 verdict:** the unconditional version for all algorithms is out of reach (it would be a
breakthrough in algebraic complexity by itself); the structured version is Theorem A. Lean: the Nisan
flattening rank 2^{λ|S||S^c|} is a one-line fact, not formalised; Theorem A's ingredients are in §7.

## 4. Mechanism 4: representative sets / colour coding over shared blocks

* Representative families (Fomin–Lokshtanov–Saurabh; Marx's matroid version) replace a family of independent
  sets by a q-representative subfamily of size C(p+q, p): an *existence* tool, it loses counts, so it cannot
  touch Z. The equality constraints have no matroid: the solution space is a product (free), and "x_{ab} = x_{ba}"
  is a partition-type identification, not independence.
* For **decision** with 0/1 tables (SAT, HC via §1.3) the question becomes whether *decision pieces* can beat
  ρ = 1/2: nonnegative A_s with Σ_s A_s having the support of F = [x=v][y=u]. Both flattenings of F are permutation
  matrices; any matrix with that support is P·D with D diagonal positive, of full rank N². So the rank
  subadditivity argument (`clique-evaluation.md` §4.3, `rho-lower-bound.md` Cor. 2.2) applies verbatim: some
  piece has row rank ≥ N²/|I|, some has col rank ≥ N²/|I|, and the adversary of §7 forces ρ_eff ≥ 1/2 − o(1).
  **Decision does not lower the cap** — and with §1.3 it cannot be easier than ⊕-counting anyway.
* Colour coding over blocks (random colouring of the D labels into few classes, require "colourful"
  labellings) is Lemma B with A_j = colour-class projectors plus a correction of full rank. Dead.

**Mechanism 4 verdict: killed.** Lean: the support-rank fact (permutation support ⇒ full rank) not
formalised; the adversary half is `adversary_two_groupings` [L] (general n).

## 5. Mechanism 5: dense/sparse splits and non-uniform schedules

### 5.1 Bit splits [L]
Brute-forcing λ₁ bits of every edge and recursing on λ − λ₁ costs 2^{λ₁E + eK²(λ−λ₁)} ≥ 2^{eK²λ}
(`Engine2p.split_exponent_ge`, with E ≥ eK² from `brute_force_is_E`). Splitting by *nodes* (fix all labels at
a node set S) is sequential contraction, e ≥ 1/4 + 1/(2K) − 1/K². Anthropic's own level structure is not a
dense/sparse bit split: it is the pieces (bits saved multiplicatively) plus the Four-Russians regrouping
(bits conserved). `engine2p_schedule.py` (A): PASS, minimum gap 0.

### 5.2 Schedules [L]+[N]
General level recurrence (Theorem A(b), g×g grid, g ≥ K any power of two): e' = (ρ + aK/g)e + b/K, K' = g².
Lower bound for *every* schedule: e_{ℓ+1} ≥ ρe_ℓ gives e_ℓ ≥ ρ^ℓ e_0 (`schedule_lower` [L]) and lg K_{ℓ+1} ≥ 2 lg K_ℓ
gives lg K_ℓ ≥ 2^ℓ lg K_0 (`lgK_lower` [L]); so ℓ ≤ log₂(lg K/lg K₀) levels can reach K and
**e(K) ≥ e_0·(lg K₀/lg K)^{log₂(1/ρ)}** for any schedule. DP over all schedules (jumps j = lg g − lg K ∈ [0,200],
lg K ≤ 4000, ρ = 1/√2): the optimum obeys the bound at every reachable K (PASS); the product
e·(lg K)^{1/2} over optimal schedules lies in [2.5, 3.0] for lg K ≥ 200 (spread factor 1.27); Anthropic's fixed
schedule g = 2^{3ℓ+x₀}K gives e = 0.080 at lg K = 3762 against the optimum 0.047 — a constant factor 1.7, the
same rate. Pieces count 2^{tλ}: fixed point t/(4(1−ρ)) reproduced (PASS). **The rate agent was right: the
schedule is pure balancing.**

## 6. Mechanism 6: fine-grained hypotheses, both directions

### 6.1 Encoding cost of pairwise-checked witnesses [R]
Let a problem have a witness made of k "names" of log n bits each with all C(k,2) pairs to be checked
(k-Clique; k-SUM with k summands checked jointly is similar; OV is k = 2 with a d-bit check; Hyperclique: all
k-subsets of ℓ names). In a (K,λ)-clique each check must happen at a node that *sees* all names involved
(labels are the only inter-node information; a global shared value costs λ ≥ its length on every pair that
needs it, and consistency of a value spread over a matching of edges is uncheckable locally). If node a sees
s_a names, Σ_a C(s_a, 2) ≥ C(k, 2) and (K−1)λ ≥ s_a log n. Cost ≥ query bound 2^{(K−1)λ} ≥ n^{max s_a}, and with
e_K = c/log K the exponent is eK²λ ≥ cK·s·log n/log K with Ks² ≥ k²: **≥ n^{ck√K/log K} ≥ n^{1.36ck}**. So even
e_K = Θ(1/log K) at the best K yields nothing below n^{Ω(k)} for k-Clique; n^{(ω/3−ε)k} is untouched, and k-SUM,
OV (any d), Hyperclique, Subset Sum (2^{(1/2−ε)n}; its check is an n·log t-bit global sum, λ ≥ log t on a
chain) are untouched a fortiori. Problems that *do* embed cheaply are those with local constraints and
witness ≈ U bits (CNFs, networks), where ETH/#ETH/SETH are already false.

### 6.2 Conversely [R]
A hypothesis implying e_K ≥ c/log K would have to say "some problem needs 2^{Ω(n/log n)}" — none exists; ETH
implies inf e_K > 0 and is false. CNF-SETH (unbounded width, m = poly(n)) survives: the m-route gives 2^{o(km/log m)}
at best, useless at m = n²; the n-route needs k ≤ polylog. What e_K = o(1/log K) *does* give is listed in
`tutte-plane.md` §4.1 and `permanent-attack.md` §3: dense per / #PM / #HC / ATSP in 2^{o(n)}, the whole Tutte
plane on sparse graphs in 2^{o(n)}, and (the only "hypothesis-flavoured" consequence) the DHMTW
#ETH-permanent bound falls — whose premise is already false. **No conditional barrier and no conditional
breakthrough is available.** Lean: the inequality Ks² ≥ k² ⇒ Ks ≥ k√K is trivial; not formalised.

## 7. Mechanism 7 (new): many / random / adaptive groupings — the covering bound

### 7.1 Setting [R]
One level of Theorem A on the g×g grid: N = g⁴λ bits, |R| ≈ g⁴/4 rectangles q = (i<i', j<j') with corners
x=(i,j), y=(i,j'), u=(i',j), v=(i',j'), crossing tensor F = [x=v][y=u], pieces F = Σ_{s∈I} A_s, |I| = 2^{o(λ)}.
A term ι ∈ I^R is evaluated as a network on the blocks of *some* partition π of the g² nodes (blocks of size
≤ g, so that the sub-network has ≥ g nodes and its tables are cheap). Theorem A uses the family
𝒢₀ = {rows, columns}; here 𝒢 is **any** family, and the algorithm may pick π = π(ι) adaptively, or at random.
π induces on q a type: `row` if x~y, u~v in two distinct blocks; `col` if x~u, y~v; `free` if x~v, y~u (F has rank 1
there); `int` if all four corners share a block; `other` if ≥ 3 blocks are touched. One-ended cost of q in
(ι, π): log rank of A_{ι(q)} across the induced cut when the type is row/col/free; ≥ max of the row and col
log-ranks when `other` (the 4-party network must pay every coarsening of its partition); 0 when `int`.

### 7.2 Two counting lemmas [R]
**Lemma 7.1 (free rectangles).** Under any partition π into blocks of size ≤ g, #free ≤ Σ_B C(|B|,2) ≤ g²(g−1)/2 ≤
(2/g)·|R|. *Proof.* A free rectangle is determined by its two corners x, v in the same block (distinct row and
column); each unordered pair in a block gives at most one rectangle. ∎ (Lean: the block-pair count
`internal_pairs_le` [L]; the identification "pair ↦ rectangle" is injective by construction.)
**Lemma 7.2 (int rectangles).** #int ≤ #free bound as well (same pairs), and both are o(|R|).

### 7.3 Theorem A (covering bound) [R]
Let s_r, s_c ∈ I have row rank ≥ N²/|I| and col rank ≥ N²/|I| respectively (they exist by subadditivity, since
both flattenings of F are permutation matrices of size N² = 2^{2λ}). Let 𝒢 be any family of partitions into
blocks of size ≤ g, M = |𝒢|. Then there is a term ι ∈ {s_r, s_c}^R with

    min_{π∈𝒢} cost(ι, π) ≥ 2λ(1 − o(1))·( |R|/2 − |R|/g − √(|R| ln(2M)/2) )   (one-ended; both ends: ×2),

i.e. ρ_eff ≥ 1/2 − 1/g − √(ln(2M)/(2|R|)) − o(1). For 𝒢 = all partitions, ln M ≤ g² ln g², so
ρ_eff ≥ 1/2 − O(√(log g)/g).

*Proof.* For the adversary's pieces, cost(ι, π) ≥ 2λ(1−o(1))·agree(ι, π) where agree counts rectangles q with
(ι(q) = s_r and type ∈ {row, other}) or (ι(q) = s_c and type ∈ {col, other}); free and int rectangles contribute
≥ 0 and there are ≤ 2|R|/g of them (Lemma 7.1). Draw ι uniformly from {s_r, s_c}^R. For a fixed π, every
row/col-type rectangle agrees with probability exactly 1/2, independently, and other-type ones always; so
agree(ι,π) ≥ Bin(|R| − 2|R|/g, 1/2) stochastically, and Hoeffding gives Pr[agree < (|R| − 2|R|/g)/2 − t] ≤ e^{−2t²/|R|}.
Union bound over the M partitions with t = √(|R| ln(2M)/2): with probability ≥ 1/2 the random ι satisfies the
bound for all π simultaneously. The term count being 2^{o(N)}, the level cost is dominated by the worst ι. ∎

**Corollary.** For every level of this shape, ρ ≥ 1/2 − o(1) and hence α' ≤ 1 (with K' ≥ K² forced as in
`rate.md` §3.4), **whatever grouping family is used, deterministically, adaptively or at random**. The
randomised variants of mechanisms 1 and 5 ("pick a random grouping per term") are special cases.

### 7.4 Exact check [N] (`engine2p_covering.py`, PASS)
* g = 3: 9 rectangles; all 12 644 partitions into blocks ≤ 3 (and the 280 balanced ones): the adversary's
  value is max_ι min_π agree = 4/9 (two groupings: 5/9). At g = 3 the free fraction bound 2/g = 2/3 is vacuous,
  so the small deficit is the expected small-g artefact.
* g = 4: 36 rectangles; **all 2 627 625 balanced partitions** into 4 blocks of 4 (average 1.42 free, 0.08 int
  rectangles each); a local-search adversary reaches min_π agree = 18 = |R|/2, exactly the two-grouping value:
  the full family of groupings buys nothing at g = 4.
* Lean: Hoeffding/union bound not formalised; the base case (two complementary patterns, adversary gets
  ⌈n/2⌉ and ⌊n/2⌋) is `adversary_two_groupings` [L, general n] and `adversary_two_groupings_6` [Li].

### 7.5 What Theorem A does not cover [R]
(i) *Non-product terms*: pieces decomposing the whole F^{⊗m} between two blocks jointly rather than per
rectangle. The averaging-over-cuts argument (sum over all balanced bipartitions of the columns; each edge
crosses half of them) gives the adversary's lower bound λm − 2 log|I| on the total column bits of a joint piece
with high row rank, so ρ ≥ 1/2 persists for joint pieces under the two groupings; combining this with the
covering argument for arbitrary 𝒢 is routine but not written. (ii) *Sub-instances not arising from groupings*
(e.g. tables transformed non-linearly, elimination-like steps): no bound, and `wild-ideas.md` §8 argues this
is the only unexplored kind of algorithm. (iii) 2^{Θ(N)} terms: fixed point t/(4(1−ρ)) > 0, no e → 0 at all.

## 8. Ranking and the single most promising next step

| # | mechanism | status | what kills it / what remains |
|---|---|---|---|
| 7 | covering bound (new) | **proved** (α' ≤ 1 for all grouping families) | extend to non-product terms → full "expansion-class" lower bound |
| 1 | randomisation (hash / sieve / isolation) | killed for the rate | residue: ⊕-pieces over F₂ (open, capped at α' = 1) |
| 5 | splits / schedules | killed [L]+[N] | constant factor 1.7 available by rescheduling |
| 4 | representative sets / decision | killed | decision pieces obey ρ ≥ 1/2 |
| 2 | low-rank table classes | killed | equivalent to the problem (subset DP ↔ κ) |
| 6 | hypotheses | no barrier, no breakthrough | pairwise-check lemma: n^{Ω(k√K/log K)} |
| 3 | unconditional oblivious LB | out of reach | would be N^{Ω(K/log K)} set-multilinear circuit lower bounds |

**Most promising next step.** Turn Theorem A into the theorem the brief asks for on the negative side: *every
algorithm that evaluates a (K,λ)-clique as a sum of 2^{o(N)} clique-type sub-instances whose tables are linear
in the original tables (any pieces, any field, any family of groupings, adaptive or randomised) has
α' ≤ 1, i.e. e_K ≥ c/log K.* Two concrete sub-steps, both finite and Lean-checkable on instances: (a) the joint-
piece version of §7.5(i) (state the averaging identity Σ_{cuts} #crossing edges = 2^{g−2}·m as a Finset identity
and the adversary's two inequalities); (b) a formal model of "linear sub-instance" general enough to contain
Theorem A's ι-terms, with the rank-subadditivity adversary as the only tool. If that theorem holds, the
positive route to e_K = o(1/log K) is confined to algorithms whose sub-computations are not clique sums at all
(elimination-like, adaptive in the tables), which no one has for any dense counting problem; the honest
positive residue of this note is the ⊕-pieces question (§1.4), where randomisation changes the field but not
the cap.

## Lean status (per claim)
| claim | file / name | status |
|---|---|---|
| bit-split & decomposition convexity (Lemma B, §1.1, §5.1) | `Accounting.lean: split_exponent_ge, brute_force_is_E` | Lean-proved (general) |
| schedule bound e_ℓ ≥ ρ^ℓ e_0, lg K_ℓ ≥ 2^ℓ lg K_0 (§5.2) | `schedule_lower, lgK_lower` | Lean-proved (general) |
| block-pair count behind Lemma 7.1 | `internal_pairs_le` | Lean-proved (general) |
| two-grouping adversary ⌈n/2⌉/⌊n/2⌋ (§4, §7.4) | `Instances.lean: adversary_two_groupings` (+ `_6`) | Lean-proved (general); instance n = 6 by `decide` |
| hash averaging identity E_h[E_h] = I + (J−I)/m (§1.1) | `hash_identity_m2` | Lean-checked on instance (m = 2, all maps Fin 4 → Fin 2) |
| collision correction J_s − I_s nonsingular (§1.1) | `detJI2, detJI3, detJI4` | Lean-checked on instances s = 2,3,4 |
| covering bound Theorem A (Hoeffding + union) (§7.3) | — | not yet formalised; Python-exact at g = 3, 4 |
| Prop. 2.1, §3, §6 accounting | — | not formalised (model statements) |
| ⊕-pieces over F₂ (§1.4) | — | open; exhaustive λ = 1 only |
