# Exact counting of Hamiltonian cycles in sparse graphs in time 2^{δn}

27 Oct 2026. This is the referee-ready write-up of the Track C construction
(`exact-count-lowrank.md`). The construction is re-derived here from scratch, with full proofs.
Conventions are fixed explicitly, and the parameter bookkeeping is done against the exact
hypotheses of the imported results. The algorithmic theorems are **conditional**: they import a
clique-evaluation algorithm and a network-to-clique reduction from Anthropic's manuscript
*A 2^{o(n)} time algorithm for 3-SAT* (cited as [A]). §9 says exactly what is imported.
Everything else is proved here.

Verification scripts, all in exact integer arithmetic: `research/scripts/proof_lib.py`,
`proof_checks.py` and `proof_params.py`. §8 gives the details.

---------------------------------------------------------------------------------------------------

## 0. Results

Graphs are finite, simple and undirected. Throughout, G = (V, E), n = |V| and m = |E|. #HC(G) is
the number of Hamiltonian cycles of G, each counted once as a subgraph (so #HC(K_4) = 3), and
#HC(G) = 0 for n ≤ 2. Time is counted as in [A, §3]: operations on words long enough to hold an
address, plus table queries.

**Theorem 1.** For every real δ > 0 and every D ≥ 1 there is a deterministic algorithm that, given
a graph G with n vertices and at most D·n edges, outputs #HC(G) within O(2^{δn}) operations.

**Theorem 2.** There are an absolute constant C\* and one deterministic algorithm that, given any
graph G with n ≥ 2 vertices and m edges, outputs #HC(G) within 2^{C\*·max(m,n)/√(log n)}
operations. In particular it runs in time 2^{O(D·n/√log n)} on graphs with m ≤ D·n, where the
O-constant is absolute and D may depend on n.

**Corollary 3** (decision, search and paths). Within the same time bounds, multiplied by m + 1,
one can also do the following, deterministically:

* decide Hamiltonicity;
* output a Hamiltonian cycle if one exists;
* count, decide and find Hamiltonian paths. For paths, apply the bounds to m + n edges and n + 1
  vertices.

**Conditionality.** Theorems 1 and 2 and Corollary 3 assume three results of [A]:

* Lemma 8, case (i): the reduction from general networks to cliques;
* Theorem A(a),(b): one algorithm for the (K_ℓ, λ)-cliques of all levels ℓ;
* the existence of pieces (Definition 7): Theorem B, with ρ = 1/√2, for Theorem 2; for Theorem 1,
  Lemma 2's pieces with ρ = 11/12 also suffice.

For Theorem 1 the main-text pair Lemma 1 + Proposition 3 of [A] can replace all of these. Nothing
else from [A] is used, in particular not its CNF Main Theorem. §9 lists the Lean counterparts of
the imported statements. The statements are recalled verbatim in §1.

**Gaps found while writing this up.** The original note has no gap in its mathematics. Three
points needed care, and are handled below:

1. Definition 2 bounds the *largest* node (P), not just the total. With unbounded maximum degree,
   one blob may have to carry Θ(n) crossing-edge bits, and then 2gP/K is not small. This is fixed
   by branching on the two cycle edges at each vertex of degree > n/g (Lemma 6.1, at most n^{4Dg}
   branches), followed by a degree-balanced partition (Lemma 6.2).
2. The interleaving sign costs O(g³) bits in total, not O(g⁴), and at most g² bits per node
   (Proposition 5.4).
3. For the sharper bound, g = 3K⁸ must stay at most n^{8/30}, so that the g³ copy bits and the
   n^{O(Dg)} branching are o(n/√log n). Then K ≥ n^{1/300}, which still gives
   e_ℓ = O(1/√log n) (§6.4).

---------------------------------------------------------------------------------------------------

## 1. Imported definitions and results (from [A], quoted)

Conventions of [A]: log = log₂, [x = u] ∈ {0,1}, [K] = {1,…,K}.

**Definition 1 [A].** F : X × X′ → Z *factors through c bits* if there are f : X × {0,1}^c → Z and
f′ : X′ × {0,1}^c → Z with F(z,z′) = Σ_{θ∈{0,1}^c} f(z,θ) f′(z′,θ). Observation (b) of [A]: for
any π : X → {0,1}^c and π′ : X′ → {0,1}^c, [π(z) = π′(z′)] = Σ_θ [π(z)=θ][π′(z′)=θ] factors through
c bits.

**Definition 2 [A].** Let P, B, τ ≥ 1 be integers. A *network on J with parameters P, B, τ* has:

* for each node a ∈ J, a finite set S_a of settings, encoded as bit strings of one fixed length
  P_a ≤ P, and a function W_a : S_a → Z;
* for each unordered pair {a,b}, a function Ψ_{a,b} : S_a × S_b → Z (symmetric), an integer
  c_{a,b} = c_{b,a} ≥ 0, and a factorization (f_{a,b}, f_{b,a}) of Ψ_{a,b} through c_{a,b} bits.

The conditions are:

* (i) Σ_{b≠a} c_{a,b} ≤ P for every a;
* (ii) all values of all W_a, Ψ_{a,b}, f_{a,b} are below 2^B in absolute value;
* (iii) an algorithm receives P, B, P_a and c_{a,b}, and decides membership in S_a or computes any
  value of W_a, Ψ_{a,b}, f_{a,b} within τ operations.

The value is Z = Σ_{z∈ΠS_a} Π_a W_a(z_a) Π_{{a,b}} Ψ_{a,b}(z_a,z_b). The total is
U = Σ_{(a,b): a≠b} c_{a,b}, which counts every shared bit from both of its ends.

**Definition 3 [A].** In the (K,λ)-clique with tables W_1,…,W_K, a setting of node w is a tuple
(z_w(w′))_{w′≠w} of λ-bit strings, and Ψ_{w,w′} = [z_w(w′) = z_{w′}(w)]. The tables are queried at
unit cost.

**Lemma 8 [A, App. A], case (i).** Let K ≥ 2, g = 3K⁸, ζ = 1/(2K). Take a network on [g] with
parameters P, B, τ and total U. Put

```
L = ⌈(U + gP/K)/K²⌉,        B′ = ⌈2gP/K⌉ + g²B.
```

Suppose an algorithm outputs the value of every (K,L)-clique with |W_w| < 2^{B′} within T
operations. Then the value of the network is computed within

```
(K^g + T · 2^{2gP/K} · τ) · (g(P+B))^{C₁}                                                   (1.1)
```

operations, by one procedure, for an absolute constant C₁. The printed statement reads
K^g + T·2^{2gP/K}·τ·(g(P+B))^{C₁}. (1.1) is the form proved in Lean as
`ExplicitCost.groupingExplicit`, and it is weaker by at most a polynomial factor, which is
irrelevant below.

**Theorem A [A, App. A].** Suppose there are pieces with parameters (ρ, c) (Definition 7 of [A]),
and let α′ = log(1/ρ). Fix an integer x₀ ≥ 18 with 2^{x₀} ≥ c + 5, and define K_ℓ, e_ℓ by (40) of
[A]: K₀ = 2^{x₀}, K_{ℓ+1} = g_ℓ², g_ℓ = 2^{3ℓ+x₀} K_ℓ, e₀ = ½, e_{ℓ+1} = (ρ + 3ζ_ℓ)e_ℓ + 3/K_ℓ.

* (a) log K_ℓ = (3x₀+6)2^ℓ − 6ℓ − 2x₀ − 6, so K_ℓ < K_{ℓ+1} ≤ K_ℓ^{10}; and
  ½ρ^ℓ ≤ e_ℓ ≤ 0.85 ρ^ℓ, where ρ^ℓ ≤ ((3x₀+6)/log K_ℓ)^{α′}.
* (b) One deterministic algorithm, given ℓ ≥ 0, λ, B ≥ 1 and query access to tables with
  |W_w| < 2^B, outputs the value of the (K_ℓ, λ)-clique within

  ```
  2^{e_ℓ K_ℓ² λ} · (K_ℓ(λ+B))^{C₀ K_ℓ²}                                                  (1.2)
  ```

  operations, with C₀ depending only on c.

**Theorem B [A].** There are pieces with parameters (1/√2, c) for an absolute constant c. Lemma 2
of [A] gives pieces with parameters (11/12, c) for some c ≥ 8.

**Lemma 1 / Proposition 3 [A] (alternative route for Theorem 1).** If (K,e) is achievable and
g = 3K⁸, every network on [g] is evaluated within C₁·2^{e(U+gP/K)+2gP/K}·(P+B)^{C₁}·τ operations,
with C₁ = C₁(K,e). For every η > 0, (K,η) is achievable for infinitely many K.

---------------------------------------------------------------------------------------------------

## 2. Grassmann algebra: the facts used

Let Γ be a finite set of *generators* with a total order ≺ (any order). The exterior algebra
Λ(Γ) over Z is the free Z-module with basis {e_S : S ⊆ Γ} and product

```
e_S · e_T = 0 if S ∩ T ≠ ∅,        e_S · e_T = (−1)^{#{(s,t) ∈ S×T : t ≺ s}} e_{S∪T} otherwise.
```

This is the exterior algebra of Z^Γ (Bourbaki, *Algebra* III §7). It is associative with unit e_∅.
Writing γ for e_{{γ}}, we have γγ′ = −γ′γ and γ² = 0, and e_S is the product of the elements of
S in increasing ≺-order. A product of generators therefore does not depend on ≺. All statements
below are about products and sums of generators, so they do not depend on ≺: changing ≺ only
re-signs the basis. (The scripts randomize ≺ on purpose.)

*Parity.* Λ = Λ⁰ ⊕ Λ¹ with Λ^p spanned by the e_S with |S| ≡ p (mod 2). An element of Λ⁰ or Λ¹ is
*homogeneous*, and 0 is homogeneous of both parities. Λ⁰ is a subring.

**Fact 2.1 (graded commutativity).** For x ∈ Λ^p and y ∈ Λ^q, xy = (−1)^{pq} yx. In particular
Λ⁰ is central.

*Proof.* For disjoint S, T, every pair in S × T is counted in exactly one of the two exponents
#{t ≺ s} and #{s ≺ t}, so e_S e_T = (−1)^{|S||T|} e_T e_S. Extend bilinearly. ∎

**Lemma 2.2 (Koszul sign rule).** Let y_1,…,y_M be homogeneous of parities p_1,…,p_M, and let σ
be a permutation of [M]. Then

```
y_{σ(1)} y_{σ(2)} ⋯ y_{σ(M)} = (−1)^{N(σ)} y_1 y_2 ⋯ y_M,
N(σ) = Σ_{s<t, σ⁻¹(s) > σ⁻¹(t)} p_s p_t.
```

The sum runs over the pairs whose relative order σ reverses.

*Proof.* Induct on the number of reversed pairs. If σ ≠ id, some adjacent positions j, j+1 have
σ(j) > σ(j+1). Exchanging these two factors multiplies the product by (−1)^{p_{σ(j)} p_{σ(j+1)}}
(Fact 2.1). It removes exactly the pair {σ(j), σ(j+1)} from the set of reversed pairs and changes
no other relative order. ∎

*Sub-algebras and top coefficients.* For Γ′ ⊆ Γ, Λ(Γ′) ⊆ Λ(Γ) is the span of the e_S with
S ⊆ Γ′. Let |Γ′| be even and ω = ±e_{Γ′}. For x ∈ Λ(Γ′), [ω](x) denotes the coefficient c with
x − cω ∈ span{e_S : S ⊊ Γ′}.

**Lemma 2.3 (block factorization of the top coefficient).** Let Γ = Γ_1 ⊔ ⋯ ⊔ Γ_g with every
|Γ_a| even (blocks may be empty). Let ω_a = ±e_{Γ_a}, Ω = ω_1 ω_2 ⋯ ω_g, and x_a ∈ Λ(Γ_a). Then

```
[Ω](x_1 x_2 ⋯ x_g) = Π_a [ω_a](x_a).
```

*Proof.* Ω = ±e_Γ, so [Ω] is defined. Write x_a = [ω_a](x_a)·ω_a + r_a, where r_a is a combination
of e_S with S ⊊ Γ_a. Expand the product. The term with no r_a is Π_a[ω_a](x_a)·Ω. Every other term
is a combination of products e_{S_1}⋯e_{S_g} with S_b ⊆ Γ_b and S_a ⊊ Γ_a for some a. Such a
product is 0 or ±e_{∪S_b}, with ∪S_b ≠ Γ, so it does not contribute to [Ω]. ∎

---------------------------------------------------------------------------------------------------

## 3. Hamiltonian cycles through spanning trees

Fix G = (V,E) with n ≥ 3 and a root r ∈ V. A *2-factor* is X ⊆ E such that every vertex has degree
exactly 2 in (V,X). τ(V,X) denotes the number of spanning trees of the graph (V,X).

**Lemma 3.1.** n·#HC(G) = Σ_{X 2-factor of G} τ(V,X).

*Proof.* A 2-factor X makes (V,X) a disjoint union of cycles covering V. If (V,X) is connected it
is a single n-cycle, that is, a Hamiltonian cycle. Its spanning trees are obtained by deleting one
of its n edges, so τ = n. If (V,X) is disconnected, τ = 0. Conversely, the edge set of every
Hamiltonian cycle is a connected 2-factor, and distinct Hamiltonian cycles have distinct edge sets.
∎

*Generators.* Γ = {ψ̄_v, ψ_v : v ∈ V∖{r}}, in any order. We put ψ̄_r = ψ_r := 0 (the zero element),
ω_v := ψ̄_v ψ_v ∈ Λ⁰, and for S ⊆ V

```
Ω_S := Π_{v ∈ S∖{r}} ω_v ,        q_e := (ψ̄_i − ψ̄_j)(ψ_i − ψ_j) ∈ Λ⁰    for e = {i,j}.
```

The order of the factors of Ω_S does not matter, because they are even and central. Ω_S = ±e_{Γ_S},
where Γ_S is the set of generators of the vertices of S. q_e does not depend on the orientation of
e, since both factors change sign.

**Lemma 3.2 (Berezin form of Cauchy–Binet).** Let N = n − 1 and b_1,…,b_N ∈ Z^{V∖{r}}. Put
θ̄(b) = Σ_u b(u)ψ̄_u and θ(b) = Σ_u b(u)ψ_u. Then

```
[Ω_V]( θ̄(b_1)θ(b_1) · θ̄(b_2)θ(b_2) ⋯ θ̄(b_N)θ(b_N) ) = det(B)²,
```

where B is the N×N matrix with columns b_k. Its rows are taken in any fixed order of V∖{r}, and
det(B)² does not depend on that order.

*Proof.* Enumerate V∖{r} as u_1,…,u_N.

1. Lemma 2.2: moving each θ̄(b_k) to the left past θ(b_1),…,θ(b_{k−1}) gives
   Π_k θ̄(b_k)θ(b_k) = (−1)^{N(N−1)/2} θ̄(b_1)⋯θ̄(b_N) · θ(b_1)⋯θ(b_N).
2. Expanding multilinearly, θ̄(b_1)⋯θ̄(b_N) = Σ_{φ:[N]→[N]} Π_k b_k(u_{φ(k)}) ψ̄_{u_{φ(1)}}⋯ψ̄_{u_{φ(N)}}.
   Only bijections φ survive, because ψ̄² = 0. For those, ψ̄_{u_{φ(1)}}⋯ψ̄_{u_{φ(N)}} =
   sgn(φ) ψ̄_{u_1}⋯ψ̄_{u_N} by Lemma 2.2. Hence θ̄(b_1)⋯θ̄(b_N) = det(B)·ψ̄_{u_1}⋯ψ̄_{u_N}, and
   likewise θ(b_1)⋯θ(b_N) = det(B)·ψ_{u_1}⋯ψ_{u_N}.
3. Undoing step 1 for the standard vectors gives
   ψ̄_{u_1}⋯ψ̄_{u_N} ψ_{u_1}⋯ψ_{u_N} = (−1)^{N(N−1)/2} ω_{u_1}⋯ω_{u_N} = (−1)^{N(N−1)/2} Ω_V.
4. The two signs cancel, and the product is det(B)²·Ω_V. ∎

**Lemma 3.3 (fermionic matrix-tree theorem).** For every X ⊆ E,
[Ω_V] Π_{e∈X}(1 + q_e) = τ(V,X).

*Proof.* The factors are even and commute, so Π_{e∈X}(1+q_e) = Σ_{F⊆X} Π_{e∈F} q_e. The term for F
lies in the span of the e_S with |S| = 2|F|, while Ω_V = ±e_Γ with |Γ| = 2N. So only |F| = N
contributes. For e = {i,j}, q_e = θ̄(b_e)θ(b_e) with b_e = 1_i − 1_j restricted to V∖{r} (that is,
1_i if j = r). By Lemma 3.2, F contributes det(B_F)², where B_F is the reduced incidence matrix of F.

* If F (with |F| = n − 1) is not a spanning tree, then (V,F) is disconnected. A connected graph on
  n vertices with n − 1 edges is a tree. Let C be a component with r ∉ C. The rows u ∈ C of B_F
  sum to 0: a column of an edge inside C has +1 and −1 there, and other columns vanish on C. So
  det B_F = 0.
* If F is a spanning tree, then det B_F = ±1, by induction on n. For n = 1 the matrix is empty. For
  n ≥ 2, pick a leaf v ≠ r (a tree has ≥ 2 leaves). Row v has one nonzero entry, ±1, in the column
  of its edge f. Expanding along it gives det B_F = ±det B_{F−f}, the reduced incidence matrix of
  the spanning tree F − f of V − v.

Hence the coefficient is #{spanning trees F ⊆ X} = τ(V,X). ∎

(By Cauchy–Binet this also gives τ(V,X) = det L_X^{(r)}, Kirchhoff's theorem. That is not needed,
but it is checked numerically, as C2 in §8.)

**Corollary 3.4.**

```
n·#HC(G) = Σ_{x∈{0,1}^E} Π_{v∈V}[deg_x(v) = 2] · [Ω_V] Π_{e: x_e=1}(1 + q_e).
```

---------------------------------------------------------------------------------------------------

## 4. Blobs, pieces and the sign rule

**Conventions (fixed once and for all).**

* *Partition.* β : V → [g] is an arbitrary map, and the blobs are V_a = β⁻¹(a). Blobs may be empty,
  and r may lie in any blob. The blob indices 1 < 2 < ⋯ < g are the "line" on which chords
  interleave.
* *Edges.* An edge is *internal* to a if both ends lie in V_a; the set of these is E_int(a). The
  other edges are *crossing*.
* *Crossing order.* The crossing edges are listed in an arbitrary but fixed total order e_1,…,e_m.
  Write k < l for e_k before e_l.
* *Ends.* A crossing edge e_k has a *low end* s_k and a *high end* t_k, with
  a_k := β(s_k) < b_k := β(t_k). Its *chord* is {a_k, b_k}.
* *Incidences.* δ(a) := {k : a ∈ {a_k, b_k}} is the set of crossing edges at a. For a < b,
  E(a,b) := {k : (a_k, b_k) = (a,b)}, e_{ab} := |E(a,b)|, and e_{ba} := e_{ab}.
* *Algebras.* Γ_a is the set of generators of V_a∖{r}, Λ_a := Λ(Γ_a) and ω_a := Ω_{V_a}. Then
  Ω_V = ω_1⋯ω_g, and Lemma 2.3 applies to the partition Γ = ⊔_a Γ_a.

**Labels and pieces.** The label set is L = {N, 0, 1, 2, 3}, and π(ℓ) := [ℓ ∈ {2,3}] is the
*parity* of ℓ. For the crossing edge e_k (ends s = s_k, t = t_k):

| ℓ | α_ℓ(k) ∈ Λ_{a_k} | β_ℓ(k) ∈ Λ_{b_k} | parity π(ℓ) |
|---|---|---|---|
| N | 1 | 1 | 0 |
| 0 | 1 | 1 + ψ̄_t ψ_t | 0 |
| 1 | ψ̄_s ψ_s | 1 | 0 |
| 2 | ψ̄_s | −ψ_t | 1 |
| 3 | ψ_s | ψ̄_t | 1 |

Label N means "e_k ∉ X", and labels 0–3 mean "e_k ∈ X" together with one term of 1 + q_{e_k}.

**Lemma 4.1.**

* (a) α_ℓ(k) and β_ℓ(k) are homogeneous of parity π(ℓ). This includes the cases s = r or t = r,
  where some pieces are 0 or reduce to 1.
* (b) α_N β_N = 1 and Σ_{ℓ∈{0,1,2,3}} α_ℓ(k) β_ℓ(k) = 1 + q_{e_k}.

*Proof.* (a) Read off the table. (b) By bilinearity,
q_e = ψ̄_sψ_s − ψ̄_sψ_t − ψ̄_tψ_s + ψ̄_tψ_t for any elements, zero included, and
−ψ̄_tψ_s = ψ_sψ̄_t. The four products in the table are 1 + ψ̄_tψ_t, ψ̄_sψ_s, −ψ̄_sψ_t and ψ_sψ̄_t,
which sum to 1 + q_e. ∎

For a labelling ℓ ∈ L^m, write π_k := π(ℓ_k). Define the piece of k at a,
γ_{k,a}(ℓ) := α_{ℓ_k}(k) if a = a_k and β_{ℓ_k}(k) if a = b_k, and the ordered product of a's
pieces:

```
Γ_a(ℓ) := Π→_{k∈δ(a)} γ_{k,a}(ℓ)      (factors in increasing crossing order k) ∈ Λ_a,

c_{kl} := #{(x,y) ∈ {a_k,b_k} × {a_l,b_l} : y < x},       ε(ℓ) := (−1)^{Σ_{k<l} π_k π_l c_{kl}}.
```

**Proposition 4.2 (sign rule).** For every partition, every crossing order and every ℓ ∈ L^m:

```
Π_{k=1}^{m} α_{ℓ_k}(k) β_{ℓ_k}(k) = ε(ℓ) · Γ_1(ℓ) Γ_2(ℓ) ⋯ Γ_g(ℓ).
```

*Proof.* The left side is the product of the sequence Y = (α(1), β(1), α(2), β(2), …, α(m), β(m)).
Give the piece α(k) the key (a_k, k) and the piece β(k) the key (b_k, k). Sorting Y by key,
lexicographically, lists blob 1's pieces in increasing k, then blob 2's, and so on. So its product
is Γ_1⋯Γ_g. By Lemma 4.1(a) all pieces are homogeneous, so Lemma 2.2 applies, and the sign counts
the pairs of pieces whose relative order is reversed:

* *Two pieces of the same k.* In Y, α(k) comes first. Its key is also smaller, since a_k < b_k.
  Not reversed.
* *A piece x of k and a piece y of l, with k < l.* In Y, x comes first. The keys are (blob(x), k)
  and (blob(y), l). Since k < l, the pair is reversed iff blob(y) < blob(x). The parity product is
  π_kπ_l.

So Γ_1⋯Γ_g = (−1)^{Σ_{k<l} π_kπ_l c_{kl}} · Π_k α(k)β(k). Multiply both sides by ε(ℓ) = ±1. ∎

**Lemma 4.3 (c_kl for disjoint chords).** If {a_k,b_k} ∩ {a_l,b_l} = ∅, then c_{kl} ≡ I(k,l)
(mod 2), where I(k,l) := [a_k < a_l < b_k < b_l or a_l < a_k < b_l < b_k] is the indicator that the
chords interleave. In particular c_{kl} mod 2 is symmetric and independent of the crossing order.

*Proof.* Put Y = {a_l, b_l}, whose elements differ from a_k and b_k. Then
c_{kl} = #{y∈Y: y<a_k} + #{y∈Y: y<b_k} = 2#{y∈Y: y<a_k} + #{y∈Y: a_k<y<b_k}. The last number is
odd iff exactly one endpoint of chord l lies strictly between a_k and b_k, which is iff the chords
interleave. ∎

**Local and interleaving parts.** Two crossing edges k < l *share* a blob if their chords meet. For
such a pair put s(k,l) := min({a_k,b_k} ∩ {a_l,b_l}); then k, l ∈ δ(s(k,l)). Define

```
σ_a(ℓ) := (−1)^{ Σ_{k<l: chords meet, s(k,l)=a} π_k π_l c_{kl} }        (a function of ℓ|δ(a)),
P_{ab}(ℓ) := Σ_{k∈E(a,b)} π_k  mod 2        for a < b                     (a function of ℓ|E(a,b)).
```

**Proposition 4.4 (sign factorization).**

```
ε(ℓ) = Π_{a=1}^{g} σ_a(ℓ) · (−1)^{ Σ_{a<c<b<d} P_{ab}(ℓ) P_{cd}(ℓ) }.
```

*Proof.* Split Σ_{k<l} π_kπ_l c_{kl} into the pairs whose chords meet and the pairs whose chords are
disjoint.

* *Meeting chords.* Each such pair has exactly one s(k,l), so these pairs give Π_a σ_a.
* *Disjoint chords.* By Lemma 4.3 these pairs give, mod 2, Σ_{k<l: I(k,l)=1} π_kπ_l. Take an
  unordered pair {k,l} with disjoint interleaving chords, and let {a,b} (a < b) be the chord with
  the smaller minimum and {c,d} the other. Interleaving means a < c < b < d. Conversely, every
  quadruple a < c < b < d with k ∈ E(a,b) and l ∈ E(c,d) gives such a pair. This is a bijection,
  so the sum equals Σ_{a<c<b<d} (Σ_{k∈E(a,b)} π_k)(Σ_{l∈E(c,d)} π_l) ≡ Σ_{a<c<b<d} P_{ab}P_{cd}
  (mod 2). ∎

**Parity copies.** Let Q_a := {(c,d) : a < c < d ≤ g}, so |Q_a| = C(g−a, 2). For y ∈ {0,1}^{Q_a}
put

```
χ_a(ℓ, y) := (−1)^{ Σ_{(c,d)∈Q_a} y_{cd} · Σ_{b: c<b<d} P_{ab}(ℓ) }     (a function of ℓ|δ(a) and y).
```

**Lemma 4.5.** If y^{(a)}_{cd} = P_{cd}(ℓ) for all a and all (c,d) ∈ Q_a, then
Π_a χ_a(ℓ, y^{(a)}) = (−1)^{Σ_{a<c<b<d} P_{ab}P_{cd}}.

*Proof.* Σ_a Σ_{a<c<d} P_{cd} Σ_{c<b<d} P_{ab} = Σ_{a<c<b<d} P_{ab}P_{cd}. ∎

So every interleaving pair of chords {a,b}, {c,d} with a < c < b < d is charged to node a, which
knows P_{ab}. Node a receives a copy of P_{cd} from node c, over the pair {a,c}.

**Blob sums.** For v ∈ V_a let deg_ℓ(v) := #{k ∈ δ(a) : v ∈ {s_k,t_k}, ℓ_k ≠ N}. Define

```
I_a(ℓ) := Σ_{x∈{0,1}^{E_int(a)}} Π_{v∈V_a}[deg_x(v) + deg_ℓ(v) = 2] · [ω_a]( F_a(x) Γ_a(ℓ) ),
F_a(x) := Π_{e∈E_int(a): x_e=1} (1 + q_e) ∈ Λ_a ∩ Λ⁰.
```

I_a depends only on ℓ|δ(a). An empty blob has I_a = 1, and so does a blob consisting of r alone
with no edges.

**Theorem 4.6 (blob factorization).** For every partition and every crossing order,

```
n·#HC(G) = Σ_{ℓ∈L^m} ε(ℓ) Π_a I_a(ℓ) = Σ_{ℓ∈L^m} Π_a σ_a(ℓ) χ_a(ℓ, P(ℓ)) I_a(ℓ),
```

where P(ℓ) means y^{(a)}_{cd} = P_{cd}(ℓ).

*Proof.* The second equality is Proposition 4.4 with Lemma 4.5. For the first:

1. Expand Π_a I_a. It becomes a sum over x_int ∈ {0,1}^{∪_a E_int(a)} of the degree indicators
   times Π_a [ω_a](F_a Γ_a).
2. By Lemma 2.3 (F_aΓ_a ∈ Λ_a), Π_a [ω_a](F_a Γ_a) = [Ω_V](Π_a F_aΓ_a).
3. The F_a are even and central, so Π_a (F_aΓ_a) = (Π_a F_a)·Γ_1⋯Γ_g.
4. By Proposition 4.2, ε(ℓ)Γ_1⋯Γ_g = Π_k α_{ℓ_k}(k)β_{ℓ_k}(k).
5. Fix x_int and the support T := {k : ℓ_k ≠ N}. The degree indicators say exactly that
   x := x_int ∪ 1_T is a 2-factor, and they do not depend on the labels in T.
6. By distributivity and Lemma 4.1(b), Σ_{ℓ: supp ℓ = T} Π_k α(k)β(k) = Π_{k∈T}(1+q_{e_k}).
7. Hence Σ_ℓ ε Π_a I_a = Σ_{x∈{0,1}^E} [x 2-factor] [Ω_V] Π_{x_e=1}(1+q_e) = n·#HC(G), by
   Corollary 3.4. ∎

---------------------------------------------------------------------------------------------------

## 5. The network

Fix G, r, β and a crossing order as in §4. κ : L → {0,…,4} is the encoding κ(N) = 0, κ(j) = j+1.
For e ≥ 0, w(e) := min{w ≥ 0 : 2^w ≥ 5^e} = ⌈e log 5⌉, and w_{ab} := w(e_{ab}).

**Definition 5.1 (the network N(G,r,β,order) on [g]).**

**Settings.** A setting of node a is a pair (ℓ^{(a)}, y^{(a)}) with ℓ^{(a)} ∈ L^{δ(a)} and
y^{(a)} ∈ {0,1}^{Q_a}. It is encoded as the concatenation of:

* for each b ∈ [g]∖{a}, in increasing order, the *block* block_b(z_a), which is the w_{ab}-bit
  binary representation (lowest bit first) of Σ_{t=1}^{e_{ab}} κ(ℓ^{(a)}_{k_t})·5^{t−1}. Here
  k_1 < ⋯ < k_{e_{ab}} enumerate E(min(a,b), max(a,b)) in crossing order;
* the bits y^{(a)}_{cd}, for (c,d) ∈ Q_a in lexicographic order.

P_a := Σ_{b≠a} w_{ab} + |Q_a|. S_a is the set of strings of length P_a whose every block is
< 5^{e_{ab}}. These are exactly the encodings, and the encoding is a bijection, so
|S_a| = 5^{|δ(a)|} 2^{|Q_a|}.

**Node functions.** W_a(z_a) := σ_a(ℓ^{(a)}) · χ_a(ℓ^{(a)}, y^{(a)}) · I_a(ℓ^{(a)}).

**Edges, for a < b.** The edge function is

```
Ψ_{a,b}(z_a, z_b) := Π_{k∈E(a,b)} [ℓ^{(a)}_k = ℓ^{(b)}_k] · Π_{d=b+1}^{g} [y^{(a)}_{bd} = P_{bd}(ℓ^{(b)})],
```

and Ψ_{b,a}(z_b, z_a) := Ψ_{a,b}(z_a, z_b). The number of shared bits is
c_{a,b} = c_{b,a} := w_{ab} + (g − b). The factorization is

```
π_{ab}(z_a) := ( block_b(z_a), y^{(a)}_{b,b+1}, …, y^{(a)}_{b,g} ) ∈ {0,1}^{c_{a,b}},
π_{ba}(z_b) := ( block_a(z_b), P_{b,b+1}(ℓ^{(b)}), …, P_{b,g}(ℓ^{(b)}) ) ∈ {0,1}^{c_{a,b}},
f_{a,b}(z_a, θ) := [π_{ab}(z_a) = θ],     f_{b,a}(z_b, θ) := [π_{ba}(z_b) = θ].
```

**What each bit means.** The w_{ab} block bits on {a,b} are the base-5 code of the labels of the
crossing edges between V_a and V_b. Both ends hold a copy, and Ψ tests that the copies are equal.
For a < b, the g − b remaining bits on {a,b} are copies, held by a, of the parities P_{bd} for
d > b. Node b computes these parities from its own labels on E(b,d).

**Lemma 5.2.** (f_{a,b}, f_{b,a}) factors Ψ_{a,b} through c_{a,b} bits.

*Proof.* Both ends list E(a,b) in the same order, and the base-5 encoding is injective. So
block_b(z_a) = block_a(z_b) iff ℓ^{(a)} and ℓ^{(b)} agree on E(a,b). The remaining coordinates of
π_{ab} and π_{ba} agree iff every copy is correct. Hence Ψ_{a,b} = [π_{ab}(z_a) = π_{ba}(z_b)], and
Observation (b) after Definition 1 applies. ∎

**Theorem 5.3.** The value of N(G,r,β,order) is n·#HC(G), for every n ≥ 3, every β : V → [g],
every root r and every crossing order.

*Proof.* A term Π_a W_a Π_{a<b} Ψ_{a,b} is nonzero only if all Ψ equal 1 (they are 0/1-valued).
This means two things:

* (i) There is ℓ ∈ L^m with ℓ^{(a)} = ℓ|δ(a) for every a. Each k lies in exactly δ(a_k) and
  δ(b_k), and Ψ_{a_k,b_k} tests agreement on k.
* (ii) y^{(a)}_{cd} = P_{cd}(ℓ) for all a < c < d. Ψ_{a,c} tests this, and
  P_{cd}(ℓ^{(c)}) = P_{cd}(ℓ).

Conversely, every ℓ ∈ L^m determines exactly one z with (i) and (ii). So
Z = Σ_ℓ Π_a σ_a(ℓ) χ_a(ℓ, P(ℓ)) I_a(ℓ) = n·#HC(G) by Theorem 4.6. ∎

**Proposition 5.4 (parameters).** Let μ_a := Σ_{v∈V_a} deg_G(v) and μ := max_a μ_a, and suppose
min-degree(G) ≥ 2. Then N(G,r,β,order) is a network in the sense of Definition 2 with

```
P := w(μ) + g + g²,       B := 2μ + 1,       τ := 2^{1.5μ} · n^{C₂}    (C₂ absolute),
U = 2 Σ_{a<b} w_{ab} + 2·C(g,3)  ≤  2 log5 · m_× + g² + g³/3  ≤  2 log5 · |E| + g³,
```

where m_× is the number of crossing edges and τ is counted after a polynomial-time preparation. In
particular P ≤ log5·μ + 2g² and gP ≤ log5·gμ + 2g³.

*Proof.*

*Counting.* Each crossing edge at a has exactly one end in V_a and each internal edge two, so
2|E_int(a)| + |δ(a)| = μ_a. Also w(e) ≤ e log5 + [e > 0] and w(x) ≥ x log5, so

```
Σ_{b≠a} w_{ab} ≤ |δ(a)|·log5 + (g−1) ≤ w(μ) + g − 1.
```

*P_a ≤ P.* P_a = Σ_b w_{ab} + C(g−a,2) ≤ w(μ) + g − 1 + g²/2 ≤ P.

*(i).* The copy bits on pairs at a number Σ_{b>a}(g−b) + Σ_{b<a}(g−a) = C(g−a,2) + (a−1)(g−a) ≤ g².
So Σ_{b≠a} c_{a,b} ≤ w(μ) + g − 1 + g² ≤ P.

*U.* U = 2Σ_{a<b} c_{a,b}. Use Σ_{a<b}(g−b) = Σ_b (b−1)(g−b) = C(g,3) (choose the middle element of
a triple) and #{a<b : e_{ab} > 0} ≤ g²/2. Finally g² + g³/3 ≤ g³ for g ≥ 2.

*(ii).* Ψ and f take values in {0,1}. |σ_a χ_a| = 1. In I_a, the product F_a(x)Γ_a(ℓ) has at most
|E_int(a)| factors with ≤ 5 signed monomials each and |δ(a)| factors with ≤ 2 each, and there are
at most 2^{|E_int(a)|} choices of x. So

```
|W_a| ≤ 10^{|E_int(a)|} 2^{|δ(a)|} ≤ 2^{(log 10/2)·2|E_int(a)| + |δ(a)|} ≤ 2^{1.67 μ_a} < 2^B.
```

*(iii).* The preparation stores the graph, β, the crossing order, the lists E(a,b), w_{ab} and Q_a.
Then:

* membership in S_a, decoding and encoding, π_{ab}, Ψ and f take poly(n + g) operations (base-5
  arithmetic on ≤ P-bit numbers, with P ≤ poly(n));
* σ_a takes O(|δ(a)|²) and χ_a takes O(g³);
* I_a loops over ≤ 2^{|E_int(a)|} ≤ 2^{μ/2} vectors x. For each, it multiplies at most μ factors
  (≤ 5 monomials each) in Λ_a, represented densely by 2^{|Γ_a|} ≤ 4^{|V_a|} ≤ 2^{μ} integers of
  ≤ B = O(n) bits (|V_a| ≤ μ_a/2 because the minimum degree is ≥ 2), and reads one coefficient.

Altogether τ ≤ 2^{μ/2}·2^{μ}·poly(n). ∎

---------------------------------------------------------------------------------------------------

## 6. The algorithm and its running time

### 6.1 Preprocessing

**Lemma 6.1 (degree reduction).** Let Θ ≥ 2 and H := {v : deg(v) > Θ}. For each choice
π = (π_v)_{v∈H} of a 2-element subset π_v of the edges at v, let G_π be G minus every edge e at a
vertex v ∈ H with e ∉ π_v. Then:

* #HC(G) = Σ_π #HC(G_π);
* there are at most Π_{v∈H} C(deg v, 2) ≤ n^{2|H|} branches, and |H| < 2m/Θ;
* every G_π has vertex set V, at most m edges and maximum degree ≤ Θ.

*Proof.* Map a Hamiltonian cycle C of G to π(C) := (E(C) ∩ δ(v))_{v∈H}. C survives in G_{π(C)},
since every edge of C at v ∈ H lies in π_v(C). Conversely, let C be a Hamiltonian cycle of G_π.
For v ∈ H, E(C) ∩ δ(v) is a 2-set contained in δ_{G_π}(v) ⊆ π_v, so π = π(C). Thus the pairs (π, C)
with C a Hamiltonian cycle of G_π correspond bijectively to the Hamiltonian cycles of G. The
remaining claims hold because Σ deg = 2m and vertices of H keep degree ≤ 2. ∎

**Lemma 6.2 (degree-balanced partition).** List V as v_1,…,v_n in any order and let
S_t := Σ_{s<t} deg(v_s). Put β(v_t) := min(g, ⌊g S_t/(2m)⌋ + 1). Then every blob has
μ_a ≤ 2m/g + Δ, where Δ is the maximum degree.

*Proof.* β is nondecreasing in t, so each blob is a segment v_t,…,v_{t′}.

* If a < g, the segment satisfies (a−1)·2m/g ≤ S_t ≤ S_{t′} < a·2m/g, so
  μ_a = S_{t′} − S_t + deg(v_{t′}) < 2m/g + Δ.
* If a = g, then μ_g = 2m − S_t ≤ 2m/g. ∎

**The algorithm, on input G.**

0. If n ≤ 2, or some vertex has degree < 2, output 0.
1. Choose ℓ (see §6.3 and §6.4). Put K := K_ℓ and g := 3K⁸.
2. Apply Lemma 6.1 with Θ := max(2, ⌈n/g⌉). For each branch G_π, do steps 3–4. If G_π has a vertex
   of degree < 2 its count is 0, so skip it.
3. Take β from Lemma 6.2, any root r and any crossing order. Build N(G_π, r, β, order) implicitly:
   the preparation of Proposition 5.4, with P, B, P_a and c_{a,b} computed exactly.
4. Run the procedure of Lemma 8(i) on it, with the algorithm of Theorem A(b) at level ℓ as the
   clique algorithm. Lemma 8 calls it on a (K, L)-clique with B′ in the role of B. Divide the
   result by n.
5. Output the sum over the branches.

Correctness follows from Lemma 6.1, Theorem 5.3, Lemma 8 and Theorem A(b).

**Bounds for every branch.** Write m for |E(G)|; then |E(G_π)| ≤ m and min-degree(G_π) ≥ 2. By
Lemma 6.2, Δ ≤ Θ ≤ n/g + 2 and so μ ≤ (2m + n)/g + 2. Using log5 ≤ 2.33 and g ≥ 3, Proposition 5.4
gives:

```
gP  ≤ 2.33(2m + n) + 3g³,        U ≤ 4.65 m + g³,        B ≤ 2(2m+n)/g + 5,
log τ ≤ 1.5(2m+n)/g + 3 + C₂ log n,        L ≤ gP + 1,        B′ ≤ 2gP + 1 + g²B.        (6.1)
```

By (1.1) and (1.2), with e := e_ℓ ≤ 1 and K²L ≤ U + gP/K + K², the time of steps 3–4 for one branch
is 2^{X}, where

```
X ≤ 1 + max{ g log K,  e(U + gP/K + K²) + C₀K² log(K(L+B′)) + 2gP/K + log τ } + C₁ log(g(P+B)) + O(log n).
                                                                                             (6.2)
```

There are at most n^{2|H|} ≤ n^{4mg/n} branches, because |H| < 2m/Θ ≤ 2mg/n.

### 6.2 Imported hypotheses, checked

Lemma 8(i) needs a network on [g] with integer parameters P, B, τ ≥ 1, total U, and g = 3K⁸.
Proposition 5.4 supplies these, with all values of all functions in Definition 2(ii) bounded and
(iii) met with the stated τ.

Lemma 8 then needs an algorithm for every (K, L)-clique with |W| < 2^{B′}. Theorem A(b) at level ℓ,
with λ = L and B = B′, gives T = 2^{e_ℓK²L}(K(L+B′))^{C₀K²}. Its hypotheses are λ, B ≥ 1, which
hold because P ≥ 1. Theorem A needs pieces: Theorem B, or Lemma 2 of [A]. Nothing in the clique
algorithm depends on the graph, which reaches it only through the tables W̃_γ that Lemma 8 builds
from W_a and f_{a,b}. "Balancing" is done by Lemma 8 itself: it searches the K^g groupings for one
with ≤ 2g/K nodes per group and Y_{γ,γ′} ≤ L, which exists by the proof of Lemma 1 of [A].

### 6.3 Proof of Theorem 1

Let D ≥ 1, δ ∈ (0,1] and m ≤ Dn. Then 2m + n ≤ 3Dn. By Theorem A(a), e_ℓ → 0 and K_ℓ → ∞, so
there is an ℓ, depending only on (δ, D), with e := e_ℓ ≤ δ/(40D) and K := K_ℓ ≥ 60D/δ. Fix it, and
put g = 3K⁸, a constant. By (6.1), the terms of (6.2) are:

```
e·U          ≤ (δ/40D)(4.65 Dn + g³)          ≤ 0.12 δn + g³,
(e+2)·gP/K   ≤ 3(2.33·3Dn + 3g³)/K            ≤ 21 Dn/K + 9g³ ≤ 0.35 δn + 9g³,
log τ        ≤ 4.5 Dn/g + O(log n)            ≤ 0.075 δn + O(log n),
the rest     = O_{δ,D}(log n)        (g, K constant; L, B′, P, B = O_{δ,D}(n)).
```

So each branch costs 2^{0.55δn + O_{δ,D}(log n)}. There are at most n^{4Dg} = n^{O_{δ,D}(1)}
branches, and the preparation is polynomial. The total is 2^{0.55δn + O_{δ,D}(log n)} = O(2^{δn}). ∎

*Alternative route.* Replace steps 1 and 4 by Lemma 1 + Proposition 3 of [A]: (K, e) achievable with
e ≤ δ/(40D) and K ≥ 60D/δ. The exponent C₁2^{e(U+gP/K)+2gP/K}(P+B)^{C₁}τ is bounded by the same
three lines.

### 6.4 Proof of Theorem 2

Use the pieces of Theorem B (ρ = 1/√2, α′ = ½, with c and x₀ absolute).

* *Small inputs.* For n < n₀ := K₀³⁰, where n₀ is an absolute constant, any exact method takes O(1)
  time.
* *Trivial cases.* Step 0 disposes of n ≤ 2 and of minimum degree < 2. Otherwise m ≥ n.
* *Choice of ℓ.* For n ≥ n₀, let ℓ be the largest index with K_ℓ³⁰ ≤ n. K_ℓ is computable from the
  formula in Theorem A(a). Then K_{ℓ+1} > n^{1/30}, and K_{ℓ+1} ≤ K_ℓ^{10} gives
  n^{1/300} < K := K_ℓ ≤ n^{1/30}. So g = 3K⁸ ∈ [3n^{8/300}, 3n^{8/30}], and by Theorem A(a)

  ```
  e = e_ℓ ≤ 0.85 ((3x₀+6)/log K)^{1/2} ≤ 0.85 (300(3x₀+6))^{1/2} / √(log n) =: c_e/√(log n).
  ```

With 2m + n ≤ 3m, the terms of (6.2) and the branching are:

```
e·U                  ≤ c_e(4.65 m + 27 n^{0.8}) / √log n,
(e+2)·gP/K           ≤ 3(7m + 81 n^{0.8}) / n^{1/300}       = O(m · n^{−1/300}),
log τ                ≤ 4.5 m / g + O(log n)                 = O(m · n^{−8/300}),
e K² + C₀K² log(K(L+B′)) = O(n^{1/15} log n)               (L, B′ ≤ poly(n), as m ≤ n²),
g log K              = O(n^{8/30} log n),       C₁ log(g(P+B)) = O(log n),
log(#branches)       ≤ 4(m/n) g log n                       = O(m · n^{8/30−1} log n).
```

Every term except the first is O(m/√log n) uniformly, because m ≥ n and n^{0.8}, n^{1/15}log n and
n^{8/30}log n are all o(n/√log n). Hence the total time is 2^{C\*·m/√log n} for an absolute C\*. ∎

*Remarks.*

* With the pieces of Lemma 2 of [A] only (ρ = 11/12), the same argument gives
  2^{O(m/(log n)^{0.125})}.
* The leading term is e_ℓ·U ≈ e_ℓ·4.64|E|. Every other term is lower order, so any improvement of
  e_ℓ in Theorem A, for example better pieces (Track H), transfers verbatim.
* Like the bounds of [A], these are purely asymptotic. For Theorem 2 the bound beats 2^n only when
  e_ℓ·4.64m < n, which needs log n in the thousands even for m = 2n.

---------------------------------------------------------------------------------------------------

## 7. Corollaries

**Corollary 7.1 (decision).** G is Hamiltonian iff #HC(G) > 0. This takes one call of Theorem 1 or 2.

**Corollary 7.2 (search, by self-reduction).** Let H := G. For each edge e of G in turn: if
#HC(H − e) > 0, set H := H − e. At the end, H is a Hamiltonian cycle.

*Proof.* The invariant is #HC(H) > 0. Let C be a Hamiltonian cycle of the final H. Every
intermediate H contains the final H, hence C. Suppose some edge f of the final H were not in C.
When f was examined, H − f contained C, so f would have been deleted. Hence the final H = C.
There are m + 1 calls, each on a graph with n vertices and ≤ m edges. ∎

**Corollary 7.3 (Hamiltonian paths).** Let G⁺ be G plus a new vertex w adjacent to all of V. The
undirected Hamiltonian paths of G correspond bijectively to the Hamiltonian cycles of G⁺, so
#HP(G) = #HC(G⁺). G⁺ has n + 1 vertices and m + n ≤ (D+1)(n+1) edges. The apex w has degree n and is
handled by Lemma 6.1. Search works as in Corollary 7.2. For s–t paths, join one new vertex to s and
t only. ∎

---------------------------------------------------------------------------------------------------

## 8. Numerical verification (exact integers)

**Scripts.** `research/scripts/proof_lib.py` implements §§2–5 literally and independently of
`lowrank_grassmann.py`:

* an exterior algebra over Z with a *randomized* generator order;
* the pieces table, ε, σ_a, P_{ab} and χ_a;
* the network of Definition 5.1, with fixed-length bit-string settings, base-5 blocks, copy bits,
  W_a, Ψ_{a,b}, c_{a,b} and f_{a,b} via the projections π_{ab};
* two network evaluators that use W, Ψ and f only as black boxes. One is brute force over
  Π_a S_a; it is exact and stops extending a partial product only when it is already 0. The other
  is the Lemma 1/Lemma 8 grouping into K = 2 or 3 groups, which builds the tables W̃_γ and sums the
  clique.

**Runs.**

* `python3 proof_checks.py 11 60`: 60 instances, n ≤ 12, all identities. Prints ALL CHECKS PASSED,
  in about 2 minutes. Smaller runs with seeds 1, 3, 5 and 7 also pass.
* `python3 proof_params.py 7`: prints ALL CHECKS PASSED.

**Instances.** There are five kinds:

* random graphs (n = 4..9) with *arbitrary* random maps β, empty blobs allowed;
* planted blob graphs with random blob relabelling;
* planted Hamiltonian cycles;
* g ∈ {4,5} instances whose planted Hamiltonian cycle visits the blobs in an interleaving cyclic
  order;
* g ∈ {4,5} instances with a planted *disconnected* 2-factor, whose non-root cycle visits the blobs
  in interleaving order (0,2,1,3,…).

Every instance uses a random root, a random crossing order and a random generator order.

**Checks.** The number in parentheses is the count of individual checks in the run with seed 11.

| check | identity | count |
|---|---|---|
| C1 | n#HC = Σ_X τ(V,X) and τ ∈ {0,n}, with τ by brute-force spanning-tree enumeration (Lemma 3.1) | 60 / 135 |
| C2 | τ = det L_X^{(r)} (Bareiss) = [Ω_V]Π(1+q_e) (Lemma 3.3) | 135 |
| C3 | Lemma 3.2 on random integer matrices | 200 |
| C4 | Koszul rule on random homogeneous sequences and permutations (Lemma 2.2) | 300 |
| C5 | block factorization of [Ω] on random elements (Lemma 2.3) | 180 |
| C6 | Lemma 4.1 (a), (b), for both orientations and with root ends | 1304 / 5216 |
| C7 | Proposition 4.2 as an *equality of algebra elements*, over all labellings when 5^m ≤ 4000, else 4000 random ones | 162 875 |
| C8 | Proposition 4.4, and Π χ_a = interleaving sign (Lemma 4.5) | 162 875 each |
| C9 | Proposition 4.2 with fresh generators, so that nothing cancels, for random g ≤ 7, ≤ 8 chords, random parities and orders; Lemma 4.3 | 400 / 1033 |
| C10 | Definition 2 for the network: P_a ≤ P, (i), symmetry, U = 2Σw_{ab} + 2C(g,3), w_{ab} = ⌈e log5⌉, \|S_a\| = 5^{\|δ(a)\|}2^{\|Q_a\|}, \|W_a\| ≤ 10^{\|E_int\|}2^{\|δ\|} < 2^B, and Ψ = Σ_θ f f′ (on all θ ∈ {0,1}^{c} when small) | ≈ 594 000 |
| C11 | Σ_ℓ ε Π I_a = n#HC (Theorem 4.6); value of the network by brute force = n#HC (Theorem 5.3); value via the K-grouping = n#HC | 60 / 60 / 103 |
| C12 | ablations: without the interleaving sign 20/60 instances are wrong, without the local signs 8/60, without any sign 18/60 | — |

C12 shows that the interleaving sign is needed. It matters exactly when odd labels sit on
interleaving chords, which in practice happens on disconnected 2-factors whose non-root cycle winds
through the blobs in interleaving order. There the odd terms are what cancel τ to 0.

`proof_params.py` checks the following:

| check | identity |
|---|---|
| P1 | Lemma 6.1 (#HC(G) = Σ_π #HC(G_π), maximum degree and edge count of the branches), 109 random graphs, thresholds 2–5 |
| P2 | Lemma 6.2 in the exact form g·μ_a ≤ 2m + gΔ, 400 graphs, g ≤ 12 |
| P3 | Σ_b(b−1)(g−b) = C(g,3), \|Q_a\| = C(g−a,2), copy bits at a ≤ 3g²/4, g² + 2C(g,3) ≤ g³, Σ_b w(e_b) ≤ w(Σe_b) + #b |
| P4 | the self-reduction of Corollary 7.2 returns exactly a Hamiltonian cycle (34 graphs) |
| P5 | \|H\|·Θ < 2m |

---------------------------------------------------------------------------------------------------

## 9. What is proved, what is assumed, what is conjectural

**Proved here** (paper level, complete proofs above):

* Lemma 3.1, Lemma 3.2 and Lemma 3.3 (matrix-tree theorem via Grassmann/Cauchy–Binet, with no
  Gaussian-integral conventions needed), and Corollary 3.4;
* the Grassmann facts 2.1–2.3, proved;
* the pieces (Lemma 4.1), the sign rule for arbitrary partitions and crossing orders
  (Proposition 4.2), and its factorization into blob-local signs and the interleaving form
  (Lemma 4.3, Proposition 4.4, Lemma 4.5);
* the blob factorization (Theorem 4.6);
* the network, its factorization, its value (Lemma 5.2, Theorem 5.3) and all its parameters
  (Proposition 5.4);
* the reductions (Lemmas 6.1 and 6.2) and the corollaries;
* the parameter bookkeeping (6.1)–(6.2) and the derivations of Theorems 1 and 2 *from* the
  imported statements.

**Assumed** (imported from [A]; we use nothing else of [A]):

1. **Lemma 8, case (i)**, in the form (1.1). In Lean this is `ExplicitCost.groupingExplicit`
   (`proof/rates/ExplicitCost/GroupingLemma.lean`). Lean's model differs: operations are
   polynomial-time steps or queries, there are memory bounds, and K, g, P, B are given in unary.
   Our network fits the query model: W_a, Ψ and f are oracles of cost τ.
2. **Theorem A(a),(b)**. (b) is `ExplicitCost.recursionSolves` in Lean
   (`PaperIndex.cliquesOfAllLevelsInCountedOperations`). (a) is elementary arithmetic on (40) of
   [A].
3. **Pieces.** Theorem B (`PiecesCounted.halfPieces` in Lean) for Theorem 2. Lemma 2 of [A] or
   Theorem B for Theorem 1.
4. For the alternative route to Theorem 1: Lemma 1 (`Printed.groupingLemma`, with Lean's memory
   caveat) and Proposition 3 of [A].

Composing items 1 and 2 with *our* network is done here on paper only. [A]'s Lean instantiates the
chain only for CNF networks. The cost model is that of [A] (operations on words). Our big-integer
arithmetic on O(n)-bit numbers costs poly(n) operations and is absorbed in τ and in the polynomial
factors. If [A]'s Theorem A(b) or Lemma 8 failed, Theorems 1 and 2 would lose their proofs, while
§§2–5 would be unaffected. Uniformity in Theorem 2 uses the constant c of Theorem B (through x₀).
If c is not explicit, the statement still asserts the existence of one algorithm, as in [A].

**Not claimed / conjectural:**

* *Practicality.* The crossover point is astronomically large, as in [A].
* *Extensions* (`exact-extensions.md`): directed HC (directed matrix-tree theorem, 4 labels per
  arc), weighted/TSP counting by polynomial weights, and other problems. These are plausible by the
  same template, but are not proved here.
* *Better exponents.* Whether e_ℓ, and hence the exponent, can be improved below 1/√log n is open.
  It is tied to better pieces (ρ → ½ would give 2^{O(m/log m)}).
* *Dense graphs.* Theorem 2 beats 2^n only for m = o(n√log n). Nothing is claimed for dense graphs
  beyond the classical O*(2^n).

**Gaps.** None found in the mathematics of §§2–6. The points that needed care are listed at the end
of §0. No independent referee report exists yet; see the addendum below.

---------------------------------------------------------------------------------------------------

## Addendum: referee report

No referee report was produced. The first referee session was lost in a container restart before it
wrote `review-exact-count.md`, and a new referee is being started. This write-up has therefore
**not yet been independently refereed**. Any issues the new report raises should be answered here.
A repeat run after the restart (`proof_checks.py 3 12`, `proof_params.py 7`) still prints ALL
CHECKS PASSED.
