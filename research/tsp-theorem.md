# TSP, ATSP and graphic TSP on sparse graphs in time 2^{δn}

28 Oct 2026. This note extends the exact-#HC theorem of `exact-hc-theorem.md` (cited as [E]) to
weighted problems. It is written at the level of [E]: every statement that is not in [E] or in
[A] (Anthropic's manuscript *A 2^{o(n)} time algorithm for 3-SAT*) is proved here. Statements of
[E] are reused by number, in the form "[E, Lemma 3.2]". The algorithmic theorems are **conditional**
in exactly the way [E, §0 and §9] describes: they import [A, Lemma 8(i)], [A, Theorem A(a),(b)]
and the pieces of [A, Theorem B / Lemma 2], and nothing else. The paper `paper/main.tex` states
[E]'s Theorems 1 and 2 as its Theorems 1 and 2; the hypothesis (H_A) there is the same import.

Verification scripts, all in exact integer arithmetic (brute force = identity = literal network):
`research/scripts/tsp_lib.py`, `tsp_check.py` (TSP-1), `tsp_atsp.py` (TSP-2), `tsp_graphic.py`
(TSP-3), `tsp_largew.py` (§5). See §8.

---------------------------------------------------------------------------------------------------

## 0. Results

Graphs are finite and simple; digraphs are finite, loopless, with at most one arc per ordered pair.
n = |V|, m = |E|. Weights are integers given in binary. For a weight function w on the edges and a
Hamiltonian cycle H, w(H) := Σ_{e∈H} w_e. Time is counted as in [A, §3] and [E]: operations on
words long enough to hold an address, plus table queries; arithmetic on B-bit integers costs
poly(B) operations.

**Definition 0.1.** For a graph G with edge weights w, the *tour polynomial* is
T_G(z) := Σ_{H Hamiltonian cycle of G} z^{w(H)} ∈ Z[z]. For a digraph, T⃗_G(z) is the same sum over
directed Hamiltonian cycles. For a connected graph G with edge lengths ℓ, the *walk polynomial* is

```
Φ_G(z) := Σ_{x ∈ {0,1,2}^E : deg_x(v) even for all v}  z^{ℓ·x} · τ(V, supp x),
```

where deg_x(v) = Σ_{e∋v} x_e, supp x = {e : x_e ≥ 1}, ℓ·x = Σ_e ℓ_e x_e and τ(V, F) is the number
of spanning trees of (V, F). T_G determines the optimum of TSP (its lowest exponent), the number
of optimal tours (the coefficient there) and the number of tours of every weight. Φ_G determines
the optimum of the graphic TSP (§4), but only a τ-weighted count of optimal solutions.

**Theorem TSP-1 (TSP, fixed density).** For every real δ > 0 and every D ≥ 1 there are a
constant C = C(δ, D) and a deterministic algorithm that, given a graph G with n vertices and at
most Dn edges, and integer edge weights 0 ≤ w_e ≤ W, outputs T_G(z) within
O(2^{δn}·(nW)^{C}) operations. In particular:

* (a) if W ≤ poly(n), the time is O(2^{δn}) for every δ > 0;
* (b) if W = 2^{o(n)}, the time is still 2^{δn} for every δ > 0 (for n ≥ n₀(δ, D, W(·)));
* (c) in general the time is 2^{δn}·W^{O_{δ,D}(1)}, pseudo-polynomial in W.

**Theorem TSP-1′ (TSP, explicit rate).** There are an absolute constant C\* and one deterministic
algorithm that, given any graph G with n ≥ 2 vertices and m edges and integer weights
0 ≤ w_e ≤ W, outputs T_G(z) within

```
2^{ C* · ( max(m,n)/√(log n)  +  n^{1/15} · log(nW) ) }
```

operations. For log W ≤ n^{14/15}/√(log n) this is 2^{O(max(m,n)/√log n)}, the rate of
[E, Theorem 2].

**Theorem TSP-2 (ATSP).** The statements of TSP-1 and TSP-1′ hold for digraphs with n ≥ 2
vertices, at most Dn arcs (resp. m arcs) and integer arc weights 0 ≤ w_e ≤ W, with T⃗_G in place
of T_G. With W = 0 this is exact counting of directed Hamiltonian cycles, which `exact-extensions.md`
stated only as [Computed].

**Theorem TSP-3 (graphic TSP).** The statements of TSP-1 and TSP-1′ hold for connected graphs G
with integer edge lengths 0 ≤ ℓ_e ≤ W and Φ_G in place of T_G (in TSP-1′ with
max(m,n)^{1/15} log(nW) as the second term of the exponent). The lowest exponent of Φ_G is the
optimum of the metric TSP on (V, d), where d is the shortest-path metric of (G, ℓ); equivalently,
the minimum length of a closed walk in G visiting every vertex. An optimal closed walk is found
within the same bound multiplied by 3m + 1. The coefficient at the optimum is
Σ_{x optimal} τ(V, supp x), not the number of optimal walks (§4.5).

**Corollary 0.2 (decision, search, weight classes).** Within the bounds of TSP-1/TSP-2 multiplied
by m + 1 one can find a minimum-weight tour (self-reduction, [E, Corollary 7.2] with "T_G has the
same lowest exponent" as the test), count the tours of every weight class, and decide whether a
tour of weight exactly t, or at most t, exists, for every t at once.

**Large weights (§5).** The network theorem of [A] tolerates node tables of B bits for *any* B,
with B entering only through polynomial factors (Proposition 1.4 and §5.1); this is what gives the
(nW)^C factor in TSP-1 and makes W = 2^{o(n)} exact. It does **not** make arbitrary binary weights
W = 2^{poly(n)} exact: the Kronecker integer n·T_G(2^b) has about b·nW bits (§5.2), counting tours
by weight residues modulo polynomially many small moduli cannot determine the optimum
(Proposition 5.2), and reading the optimum off evaluations T_G(z) mod p is sparse interpolation
with up to #HC(G) = 2^{Ω(n)} terms (§5.3). What is obtained for arbitrary binary weights is a
deterministic (1+ε)-approximation in time (m+1)·2^{δn}·(n/ε)^{C} (Proposition 5.4). Exact TSP on
sparse graphs with weights up to 2^{poly(n)} in time 2^{δn} is **open**; the specific claim in the
task description that Kronecker substitution with b = n log W + O(n) bits keeps B polynomial is
false, and §5.2 says exactly why.

**Barrier (§6).** The cost is per edge, 2^{δ|E|}; for dense graphs (K_n, general metric TSP) nothing
beyond Held–Karp's O\*(2^n) is obtained, and the (2−ε)^n question for TSP on general graphs is
untouched. With the explicit rate the method beats 2^n iff the average degree is o(√log n).

---------------------------------------------------------------------------------------------------

## 1. Labelled Berezin networks: the template behind all three theorems

This section isolates what [E, §§4–6] actually uses about the Hamiltonian-cycle pieces, and
restates [E]'s blob factorisation, network and parameter bounds for an arbitrary finite label
alphabet with scalar weights on the pieces. Everything is proved by pointing at the line of [E]
that changes; no proof of [E] is reproduced. The Grassmann facts [E, §2] are used as they stand.

### 1.1 Data

Fix a graph G = (V, E) with n ≥ 2, a root r ∈ V, the generators Γ = {ψ̄_v, ψ_v : v ≠ r}
(ψ̄_r = ψ_r = 0) and Ω_S, ω_v, q_e as in [E, §3]. The following data is given:

* a finite set X of *edge states* with 0 ∈ X and |X| ≤ 3, and a finite *label alphabet* L with a
  distinguished label N ∈ L, |L| =: λ ≤ 9, and a *state map* st : L → X with st(N) = 0 and
  st⁻¹(0) = {N} (labels outside the image of the pieces of an edge are simply dead: their pieces
  are 0 for that edge);
* a *parity* π : L → {0,1} with π(N) = 0;
* for each edge e and each state x ∈ X an *edge factor* F_e(x) ∈ Λ({ψ̄_i,ψ_i,ψ̄_j,ψ_j}) ∩ Λ⁰ (even),
  with F_e(0) = 1, having at most 5 monomials, with integer coefficients of absolute value ≤ 2^{β₀};
* for each edge e, each ordered pair (s,t) with {s,t} = e, and each label ℓ ∈ L, *pieces*
  α_ℓ(s,t) ∈ Λ({ψ̄_s,ψ_s}) and β_ℓ(s,t) ∈ Λ({ψ̄_t,ψ_t}), each a sum of at most 2 monomials with
  integer coefficients of absolute value ≤ 2^{β₀}, such that
  * (Π1) α_ℓ(s,t) and β_ℓ(s,t) are homogeneous of parity π(ℓ) (zero allowed);
  * (Π2) α_N(s,t) β_N(s,t) = 1 and, for every x ∈ X, Σ_{ℓ: st(ℓ)=x} α_ℓ(s,t) β_ℓ(s,t) = F_e(x),
    for both orientations (s,t);
* for each vertex v a *constraint* C_v : X^{δ_G(v)} → {0,1}, where δ_G(v) is the set of edges at v.

The *sum* of the data is

```
Z := Σ_{x ∈ X^E}  Π_{v∈V} C_v(x|δ_G(v)) · [Ω_V] Π_{e∈E} F_e(x_e).                           (1.1)
```

(The factors F_e(x_e) are even, hence central, so the product is unordered.) The *maximum degree*
Δ and the *degree sums* μ_a = Σ_{v∈V_a} deg_G(v) of a partition are as in [E].

**Example (HC).** X = {0,1}, L = {N,0,1,2,3}, st(ℓ) = [ℓ ≠ N], π(ℓ) = [ℓ ∈ {2,3}],
F_e(1) = 1 + q_e, pieces as in the table of [E, §4], C_v = [Σ_{e∋v} x_e = 2], β₀ = 0. Then Z =
n·#HC(G) by [E, Corollary 3.4]. (Π1), (Π2) are [E, Lemma 4.1].

### 1.2 Blob factorisation

Fix a partition β : V → [g], a crossing order e_1 < ⋯ < e_{m_×} of the crossing edges, low ends
s_k, high ends t_k, a_k = β(s_k) < b_k = β(t_k), δ(a), E(a,b), e_{ab}, Λ_a, ω_a exactly as in
[E, §4]. For a labelling ℓ ∈ L^{m_×} put π_k = π(ℓ_k), γ_{k,a}(ℓ) := α_{ℓ_k}(s_k,t_k) if a = a_k
and β_{ℓ_k}(s_k,t_k) if a = b_k, Γ_a(ℓ) := Π→_{k∈δ(a)} γ_{k,a}(ℓ) (increasing k), c_{kl} and
ε(ℓ) := (−1)^{Σ_{k<l} π_kπ_l c_{kl}} as in [E, §4], and σ_a, P_{ab}, χ_a, Q_a as in [E, §4].

**Proposition 1.1 (sign rule).** Π_{k=1}^{m_×} α_{ℓ_k}(s_k,t_k) β_{ℓ_k}(s_k,t_k) = ε(ℓ)·Γ_1(ℓ)⋯Γ_g(ℓ).

*Proof.* The proof of [E, Proposition 4.2] uses only that every piece is homogeneous with the
parity π_k of its label, which is (Π1), and the Koszul rule [E, Lemma 2.2]. ∎

Likewise [E, Lemma 4.3, Proposition 4.4, Lemma 4.5] are statements about π and the chord positions
only, so they hold verbatim: ε(ℓ) = Π_a σ_a(ℓ)·(−1)^{Σ_{a<c<b<d} P_{ab}P_{cd}} and
Π_a χ_a(ℓ, P(ℓ)) is the interleaving sign.

**Blob sums.** For v ∈ V_a and ℓ, let x_ℓ(v) ∈ X^{δ(v) ∩ crossing} be the states st(ℓ_k) of the
crossing edges at v. Define

```
I_a(ℓ) := Σ_{x_int ∈ X^{E_int(a)}} Π_{v∈V_a} C_v(x_int|δ(v), x_ℓ(v)) · [ω_a]( F_a(x_int) Γ_a(ℓ) ),
F_a(x_int) := Π_{e∈E_int(a)} F_e(x_e) ∈ Λ_a ∩ Λ⁰.
```

I_a depends only on ℓ|δ(a), because C_v for v ∈ V_a reads only edges at v, which are internal to
a or in δ(a).

**Theorem 1.2 (blob factorisation).** Z = Σ_{ℓ∈L^{m_×}} ε(ℓ) Π_a I_a(ℓ) = Σ_ℓ Π_a σ_a(ℓ) χ_a(ℓ,P(ℓ)) I_a(ℓ).

*Proof.* Follow the seven steps of the proof of [E, Theorem 4.6]. Steps 1–3 are unchanged (F_a is
even and central; [E, Lemma 2.3]). Step 4 is Proposition 1.1. In step 5, fix x_int and the states
x_× := (st(ℓ_k))_k of the crossing edges; the constraints Π_v C_v depend on ℓ only through x_×,
and x := x_int ∪ x_× ranges over X^E. Step 6: by distributivity and (Π2),
Σ_{ℓ: st(ℓ_k)=x_k ∀k} Π_k α_{ℓ_k}β_{ℓ_k} = Π_k F_{e_k}(x_k). Step 7: the result is the right side
of (1.1). ∎

### 1.3 The network

Let w_λ(e) := min{w ≥ 0 : 2^w ≥ λ^e} = ⌈e log₂ λ⌉ and w_{ab} := w_λ(e_{ab}); let
κ : L → {0,…,λ−1} be any bijection with κ(N) = 0.

**Definition 1.3 (the network N(data, β, order) on [g]).** Exactly [E, Definition 5.1] with the
base-5 blocks replaced by base-λ blocks: a setting of node a is (ℓ^{(a)}, y^{(a)}) ∈ L^{δ(a)} ×
{0,1}^{Q_a}, encoded as the blocks block_b(z_a) = the w_{ab}-bit representation of
Σ_t κ(ℓ^{(a)}_{k_t}) λ^{t−1} (k_1 < ⋯ enumerating E(min(a,b), max(a,b))), followed by the copy
bits; S_a is the set of strings whose blocks are < λ^{e_{ab}}; W_a := σ_a χ_a I_a; Ψ_{a,b}, c_{a,b},
π_{ab}, f_{a,b} as in [E, Definition 5.1] with these blocks.

**Theorem 1.4 (value).** The value of N(data, β, order) is Z, for every β, every root and every
crossing order.

*Proof.* [E, Lemma 5.2] (factorisation of Ψ through c_{a,b} bits) only uses that the base-λ code of
a block is injective. [E, Theorem 5.3] then applies with Theorem 1.2 in place of [E, Theorem 4.6]. ∎

**Proposition 1.5 (parameters).** Let μ := max_a μ_a and suppose every vertex has degree ≥ 1. Then
N(data, β, order) is a network in the sense of [A, Definition 2] with

```
P := w_λ(μ) + g + g²,     B := (2 + β₀)·μ + 1,     τ := 2^{3μ} · (n + B)^{C₂}    (C₂ absolute),
U = 2 Σ_{a<b} w_{ab} + 2·C(g,3)  ≤  2 log₂λ · m_× + g² + g³/3  ≤  2 log₂ λ · m + g³,
```

τ being counted after a polynomial-time preparation that stores the graph, the data (pieces,
factors, constraints, as tables or as procedures that evaluate them in poly(n + β₀) operations),
β, the order, the lists E(a,b), w_{ab} and Q_a.

*Proof.* *P_a ≤ P, (i), U:* as in [E, Proposition 5.4], with log₂ 5 replaced by log₂ λ, using
w_λ(e) ≤ e log₂λ + [e > 0] and w_λ(x) ≥ x log₂ λ.

*(ii).* Ψ, f ∈ {0,1} and |σ_aχ_a| = 1. For the top coefficient of a product of algebra elements,
|[ω](f_1⋯f_s)| ≤ Π_i ‖f_i‖₁, where ‖f‖₁ is the sum of the absolute values of the coefficients of
f, because every monomial of the product is a signed product of one monomial from each factor. In
I_a there are at most |X|^{|E_int(a)|} ≤ 3^{|E_int(a)|} choices of x_int; each term is a product of
≤ |E_int(a)| factors F_e with ‖F_e‖₁ ≤ 5·2^{β₀} and ≤ |δ(a)| pieces with ‖·‖₁ ≤ 2·2^{β₀}. Since
2|E_int(a)| + |δ(a)| = μ_a,

```
|W_a| ≤ 15^{|E_int(a)|} · 2^{|δ(a)|} · 2^{β₀(|E_int(a)| + |δ(a)|)} ≤ 2^{(log₂15/2)·2|E_int(a)| + |δ(a)| + β₀μ_a} < 2^{(2+β₀)μ_a + 1}.
```

*(iii).* Membership, encoding, decoding, π_{ab}, Ψ, f, σ_a, χ_a: as in [E] (base-λ arithmetic on
P-bit numbers). I_a loops over ≤ 3^{|E_int(a)|} ≤ 2^{0.8μ_a} vectors x_int; for each it multiplies
≤ μ_a factors in Λ_a, represented densely by 4^{|V_a|} integers; |V_a| ≤ μ_a because every degree is
≥ 1; each partial product obeys the bound of (ii) (the same ‖·‖₁ argument), so all integers have
< B bits. Altogether 2^{0.8μ}·4^{μ}·μ·poly(n + B) ≤ 2^{3μ}(n + B)^{C₂}. ∎

### 1.4 Evaluation

**Theorem 1.6 (evaluation, fixed density).** For every δ > 0 and D ≥ 1 there are K = K(δ,D),
g = 3K⁸, and C = C(δ,D) such that, assuming [A, Lemma 8(i)], [A, Theorem A(a),(b)] and the pieces
of [A, Theorem B] (or of [A, Lemma 2]), the following holds. For every data as in §1.1 on a graph
with n vertices, m ≤ Dn edges, minimum degree ≥ 1 and maximum degree Δ ≤ n/g + 2, and every
β₀ ≥ 0, the sum Z is computed deterministically within 2^{δn/2}·(n(β₀+1))^{C} operations, after the
polynomial-time preparation of Proposition 1.5.

*Proof.* Take ℓ with e := e_ℓ ≤ δ/(60D) and K := K_ℓ ≥ 120D/δ ([A, Theorem A(a)]: e_ℓ → 0,
K_ℓ → ∞), g := 3K⁸. Let β be the degree-balanced partition of [E, Lemma 6.2], so
μ ≤ 2m/g + Δ ≤ (2m + n)/g + 2 ≤ 3Dn/g + 2. Run [A, Lemma 8(i)] on N(data, β, order) with
[A, Theorem A(b)] at level ℓ as the clique algorithm, as in [E, §6.1, steps 3–4]; the hypotheses are
checked exactly as in [E, §6.2], with Proposition 1.5 in place of [E, Proposition 5.4]. The cost is
2^X with X bounded by [E, (6.2)]:

```
X ≤ 1 + max{ g log K, e(U + gP/K + K²) + C₀K² log(K(L+B′)) + 2gP/K + log τ } + C₁ log(g(P+B)) + O(log n),
```

where L ≤ gP + 1 and B′ ≤ 2gP + 1 + g²B. With λ ≤ 9, log₂ λ ≤ 3.17, and gμ ≤ 2m + n + 2g:

```
U        ≤ 6.34 m + g³ ≤ 6.34 Dn + g³,
gP       ≤ 3.17(2m + n + 2g) + 3g³ ≤ 9.51 Dn + 10 g³,
B        ≤ (2 + β₀)(3Dn/g + 2) + 1,
log τ    ≤ 9Dn/g + 6 + C₂ log(n + B).
```

Hence e·U ≤ 0.106 δn + g³, (e+2)gP/K ≤ 3(9.51Dn + 10g³)/K ≤ 0.238 δn + 30g³, log τ ≤ 0.01 δn +
O(log(n(β₀+1))) (g ≥ 3(120D/δ)⁸ makes 9D/g < 0.01δ), and the remaining terms eK², g log K,
C₀K² log(K(L+B′)), C₁ log(g(P+B)) are O_{δ,D}(log(n(β₀+1))), because K, g are constants and L, P,
B, B′ ≤ poly(n)·(β₀+1). So X ≤ 0.36 δn + C log(n(β₀+1)) + O_{δ,D}(1). ∎

**Theorem 1.7 (evaluation, explicit rate).** There are an absolute constant C\* and one
deterministic algorithm such that, under the same imports with the pieces of [A, Theorem B], for
every data as in §1.1 on a graph with n ≥ n₀ vertices, m edges, minimum degree ≥ 1 and maximum
degree ≤ n/g(n) + 2, where g(n) := 3K_ℓ⁸ for the level ℓ = ℓ(n) chosen in [E, §6.4] (the largest ℓ
with K_ℓ³⁰ ≤ n), the sum Z is computed within

```
2^{ C* ( max(m,n)/√(log n) + n^{1/15} log(n(β₀+1)) ) }
```

operations, after the preparation of Proposition 1.5.

*Proof.* As in [E, §6.4]: n^{1/300} < K ≤ n^{1/30}, g ≤ 3n^{8/30}, e ≤ c_e/√log n. With
M := max(m,n) and the bounds above: eU ≤ c_e(6.34M + 27n^{0.8})/√log n; (e+2)gP/K =
O(M n^{−1/300}); log τ ≤ 9M/g + O(log(n(β₀+1))) = O(M n^{−8/300}) + O(log(n(β₀+1)));
eK² + C₀K² log(K(L+B′)) = O(n^{1/15} log(n(β₀+1))), since L, B′ ≤ poly(n)(β₀+1);
g log K = O(n^{8/30} log n) = o(n/√log n); C₁ log(g(P+B)) = O(log(n(β₀+1))). ∎

*Remark 1.8 (where B enters).* B enters the cost only through (g(P+B))^{C₁} in [A, Lemma 8],
through (K(λ+B′))^{C₀K²} in [A, Theorem A(b)] with B′ = ⌈2gP/K⌉ + g²B, and through τ (arithmetic
on B-bit integers). [A, Definition 2] puts no upper bound on B, and neither statement has a term
exponential in B. This is the whole content of the "large weights" question of §5.1.

---------------------------------------------------------------------------------------------------

## 2. Theorem TSP-1: the tour polynomial

### 2.1 The weighted identity

Fix G = (V,E), n ≥ 3, integer weights w_e ≥ 0 and a root r. A 2-factor is X ⊆ E with every
degree 2.

**Lemma 2.1.** n · T_G(z) = Σ_{X 2-factor} z^{w(X)} τ(V,X) in Z[z].

*Proof.* [E, Lemma 3.1] is proved termwise: τ(V,X) = n if X is the edge set of a Hamiltonian cycle,
τ(V,X) = 0 otherwise, and the Hamiltonian cycles correspond bijectively to the connected
2-factors. Multiply the term of X by z^{w(X)}; for X = E(H), w(X) = w(H). ∎

**Lemma 2.2 (weighted Berezin form).** For every X ⊆ E and every integer (or indeterminate) z,
[Ω_V] Π_{e∈X} z^{w_e}(1 + q_e) = z^{w(X)} τ(V,X).

*Proof.* Scalars are central, so Π_{e∈X} z^{w_e}(1+q_e) = z^{w(X)} Π_{e∈X}(1+q_e); apply
[E, Lemma 3.3]. ∎

**Corollary 2.3.** n·T_G(z) = Σ_{x∈{0,1}^E} Π_v [deg_x(v) = 2] · [Ω_V] Π_{e: x_e=1} z^{w_e}(1+q_e).

### 2.2 Weighted pieces and the Kronecker integer

Let b := m + ⌈log₂ n⌉ + 1 and Y := 2^b.

**Lemma 2.4 (coefficients).** Every coefficient of n·T_G(z) is an integer in [0, 2^b), and
deg T_G ≤ nW. Hence T_G is recovered from the integer n·T_G(Y) by reading its base-2^b digits:
digit t equals n·#{H : w(H) = t}, t = 0, …, nW.

*Proof.* The coefficient of z^t is n·#{H : w(H) = t} ≤ n·#HC(G) ≤ n·#{2-factors} ≤ n·2^m < 2^b.
A tour has n edges of weight ≤ W. ∎

**Weighted data.** Take the HC data of the Example in §1.1 with the scalar Y^{w_e} on the
*low-end* piece: for e = {s,t} and ℓ ≠ N put α^w_ℓ(s,t) := Y^{w_e}·α_ℓ(s,t), α^w_N := 1, β^w := β
(the pieces of [E, §4]); F_e(1) := Y^{w_e}(1 + q_e), F_e(0) = 1; C_v = [deg = 2]; β₀ := bW.

**Lemma 2.5.** The weighted data satisfies (Π1) and (Π2) of §1.1, with λ = 5, |X| = 2.

*Proof.* Multiplying by a scalar preserves homogeneity and parity, so (Π1) is [E, Lemma 4.1(a)].
(Π2): α^w_Nβ^w_N = 1, and Σ_{ℓ=0}^{3} α^w_ℓβ^w_ℓ = Y^{w_e} Σ_ℓ α_ℓβ_ℓ = Y^{w_e}(1+q_e) by
[E, Lemma 4.1(b)], for either orientation. Each piece has ≤ 2 monomials with coefficients of
absolute value ≤ Y^{W} = 2^{β₀}; F_e(1) has 5 monomials with coefficients ≤ Y^W. ∎

**Theorem 2.6.** For every partition β and crossing order, the value of the network
N(weighted data, β, order) of Definition 1.3 is n·T_G(Y), and it is a network with the parameters
of Proposition 1.5: P = w_5(μ) + g + g², B = (2 + bW)μ + 1, τ = 2^{3μ}(n+B)^{C₂},
U ≤ 2 log₂5·m + g³.

*Proof.* By Theorem 1.4 the value is the sum (1.1) of the weighted data, which is the right side of
Corollary 2.3 at z = Y. Proposition 1.5 applies (minimum degree ≥ 2 is checked in step 0 below). ∎

*Remark.* [E, Proposition 5.4] has the sharper τ = 2^{1.5μ}·poly for the HC data (there |V_a| ≤
μ_a/2); the cruder 2^{3μ} of Proposition 1.5 changes nothing, as log τ is a lower-order term.

### 2.3 Degree reduction

**Lemma 2.7.** Let Θ ≥ 2, H := {v : deg(v) > Θ}, and for each π = (π_v)_{v∈H} with π_v a 2-subset
of δ(v) let G_π be G minus every edge at a vertex v ∈ H not in π_v (as in [E, Lemma 6.1]). Then
T_G(z) = Σ_π T_{G_π}(z), there are at most n^{2|H|} branches with |H| < 2m/Θ, and every G_π has
maximum degree ≤ Θ and at most m edges.

*Proof.* The bijection (π, C) ↔ C of [E, Lemma 6.1] between pairs with C a Hamiltonian cycle of
G_π and the Hamiltonian cycles of G preserves edge sets, hence weights. ∎

### 2.4 Proof of Theorems TSP-1 and TSP-1′

**Algorithm.** On input (G, w, W):

0. If n ≤ 2 or some vertex has degree < 2, output T_G = 0. Compute b, Y.
1. Choose ℓ, K, g as in Theorem 1.6 (resp. 1.7). Apply Lemma 2.7 with Θ := max(2, ⌈n/g⌉).
2. For each branch G_π with minimum degree ≥ 2: build the weighted data on G_π and compute
   Z_π := n·T_{G_π}(Y) by Theorem 1.6 (resp. 1.7).
3. Output the digits of (Σ_π Z_π)/n in base 2^b (Lemma 2.4).

*Correctness* is Lemma 2.7, Theorem 2.6 and Lemma 2.4. *Time.* For TSP-1: there are at most
n^{2|H|} ≤ n^{4Dg} = n^{O_{δ,D}(1)} branches, each costing 2^{δn/2}(n(bW+1))^{C} by Theorem 1.6
(β₀ = bW ≤ (Dn + log n + 1)W = poly(n)·W); the preparation and the final digit extraction on an
integer of ≤ b(nW+1) + log n bits are polynomial in nW. Total O(2^{δn}(nW)^{C′}). Parts (a)–(c) of
the statement follow: (nW)^{C′} = 2^{O(log n)} for W = poly(n), and 2^{o(n)} for W = 2^{o(n)}.
For TSP-1′: branches ≤ n^{4mg/n} = 2^{O(m n^{8/30−1} log n)} = 2^{o(m/√log n)}, and Theorem 1.7
gives the exponent C\*(max(m,n)/√log n + n^{1/15} log(n(bW+1))); log(bW+1) ≤ log(nW) + O(log n).
Absorb constants into C\*. ∎

*Remark 2.8 (negative weights).* Weights in [−W₀, W] are handled by w_e + W₀: every tour weight
shifts by nW₀.

---------------------------------------------------------------------------------------------------

## 3. Theorem TSP-2: directed tours

Let G = (V, A) be a digraph, n ≥ 2, with integer arc weights w ≥ 0, a root r, and the same
generators Γ (ψ̄_r = ψ_r = 0). For an arc a = (i → j) put

```
p_a := ψ̄_i (ψ_i − ψ_j) = ψ̄_iψ_i − ψ̄_iψ_j ∈ Λ⁰.
```

L_out(F) := D_out − A_F is the out-degree Laplacian of an arc set F (row i: out-degree of i on the
diagonal, −1 in column j for each arc i → j), and L_out(F)^{(r)} its reduced form (row and column
r deleted). An *in-arborescence towards r* is a set of n − 1 arcs in which every v ≠ r has
out-degree exactly 1, r has out-degree 0, and every vertex reaches r by following arcs. A *cycle
cover* is X ⊆ A with in- and out-degree 1 at every vertex; it is a disjoint union of directed
cycles (2-cycles allowed) covering V.

### 3.1 Directed matrix-tree theorem in Berezin form

**Lemma 3.1 (two-matrix Berezin form).** Let N = n−1 and b_1,…,b_N, c_1,…,c_N ∈ Z^{V∖{r}}. Then
[Ω_V]( θ̄(b_1)θ(c_1) ⋯ θ̄(b_N)θ(c_N) ) = det(B)·det(C), where B, C have columns b_k, c_k (rows
in any fixed order of V∖{r}; the product of the determinants does not depend on it).

*Proof.* The four steps of the proof of [E, Lemma 3.2] never use b_k = c_k: step 2 gives
θ̄(b_1)⋯θ̄(b_N) = det(B) ψ̄_{u_1}⋯ψ̄_{u_N} and θ(c_1)⋯θ(c_N) = det(C) ψ_{u_1}⋯ψ_{u_N}. ∎

**Lemma 3.2 (directed fermionic matrix-tree theorem).** For every arc set F ⊆ A,
[Ω_V] Π_{a∈F}(1 + p_a) = det L_out(F)^{(r)} = #{in-arborescences towards r contained in F}.

*Proof.* The factors are even, so Π_{a∈F}(1+p_a) = Σ_{F′⊆F} Π_{a∈F′} p_a, and only |F′| = N
contributes to [Ω_V]. For a = (i→j), p_a = θ̄(1_i)θ(1_i − 1_j), where 1_r := 0 and vectors are
restricted to V∖{r}. By Lemma 3.1, F′ contributes det(M_{F′})·det(N_{F′}), where M_{F′} has
columns 1_{tail(a)} and N_{F′} columns 1_{tail(a)} − 1_{head(a)}, a ∈ F′. Also
L_out(F) = M_F N_Fᵀ (the (u,v) entry is Σ_{a=(i→j)} [u=i]([v=i] − [v=j])), so by Cauchy–Binet
det L_out(F)^{(r)} = Σ_{|F′|=N} det(M_{F′})det(N_{F′}) as well. It remains to evaluate each term.

* If some arc of F′ has tail r, M_{F′} has a zero column; if two arcs share a tail, two equal
  columns. Either way the term is 0. Otherwise the tails of the N arcs are N distinct vertices
  of V∖{r}, i.e. every v ≠ r is the tail of exactly one arc of F′ and r of none. Reordering the
  arcs permutes the columns of M_{F′} and N_{F′} by the same permutation, so we may assume arc
  a_k has tail u_k, the k-th row. Then M_{F′} = I and N_{F′} = I − Π, where column k of Π is
  1_{head(a_k)} (zero if the head is r): Π is the matrix of the map "parent" u_k ↦ head(a_k) on
  V∖{r}, with r acting as 0.
* If F′ is an in-arborescence, every vertex reaches r in ≤ N steps, so Π^N = 0: Π is nilpotent,
  all its eigenvalues are 0, and det(I − Π) = Π_i(1 − 0) = 1.
* If F′ is not an in-arborescence, some vertex does not reach r, so following parents from it
  stays in V∖{r} and eventually repeats: there is a directed cycle c_1 → c_2 → ⋯ → c_L → c_1 in
  F′. Let x := 1_C ∈ Z^{V∖{r}}, C = {c_1,…,c_L}. Then (Πx)_v = #{u ∈ C : parent(u) = v} = [v ∈ C],
  because each c_i has exactly one in-neighbour in C (namely c_{i−1}) and vertices outside C have
  none within C. So (I − Π)x = 0 and det(I − Π) = 0.

Hence each term is 1 if F′ is an in-arborescence towards r and 0 otherwise. ∎

**Lemma 3.3 (the directed identity).** For a cycle cover X, det L_out(X)^{(r)} = 1 if X is a single
cycle (a directed Hamiltonian cycle) and 0 otherwise. Consequently

```
T⃗_G(z) = Σ_{X cycle cover} z^{w(X)} · det L_out(X)^{(r)} = Σ_{x∈{0,1}^A} Π_v [out_x(v) = in_x(v) = 1] · [Ω_V] Π_{a: x_a=1} z^{w_a}(1 + p_a).
```

*Proof.* By Lemma 3.2 we count in-arborescences F′ ⊆ X. Every v ≠ r has exactly one out-arc in X,
which must belong to F′, and the out-arc of r must not; so the only candidate is
F′ = X ∖ {out-arc of r}, which has n − 1 arcs. If X is a single cycle through all vertices, F′ is
the path along the cycle ending at r, an in-arborescence. If X has ≥ 2 cycles, the cycle not
containing r lies in F′, and its vertices never reach r. The displayed formula follows termwise as
in Lemma 2.1 and Lemma 2.2 (scalars are central). No factor n appears. ∎

### 3.2 Directed pieces

Label alphabet L_d := {N, 0, 2} with st(N) = 0, st(0) = st(2) = 1, π(0) = 0, π(2) = 1; X = {0,1};
F_a(1) := Y^{w_a}(1 + p_a) for the arc a = (i → j), with Y = 2^b, b := m + 1 (the coefficients of
T⃗_G are ≤ #cycle covers ≤ 2^m). For the orientation (s,t) with {s,t} = {i,j}:

| | tail is the low end (s = i, t = j) | head is the low end (s = j, t = i) |
|---|---|---|
| ℓ = 0 | α = Y^{w_a}(1 + ψ̄_sψ_s), β = 1 | α = Y^{w_a}, β = 1 + ψ̄_tψ_t |
| ℓ = 2 | α = Y^{w_a} ψ̄_s, β = −ψ_t | α = Y^{w_a} ψ_s, β = ψ̄_t |

and α_N = β_N = 1.

**Lemma 3.4.** This data satisfies (Π1) and (Π2) with λ = 3, β₀ = bW, including root ends.

*Proof.* (Π1) by inspection. (Π2): tail low: α_0β_0 + α_2β_2 = Y^{w}(1 + ψ̄_iψ_i − ψ̄_iψ_j).
Head low: α_0β_0 + α_2β_2 = Y^{w}(1 + ψ̄_iψ_i + ψ_jψ̄_i) and ψ_jψ̄_i = −ψ̄_iψ_j. With a root end
the same bilinear computation holds with the zero generators: if i = r then p_a = 0 and
F_a(1) = Y^{w_a}, and the table gives α_0β_0 = Y^{w_a}, α_2β_2 = 0 (the arc is in X and carries
its weight, while its Laplacian contribution sits in the deleted row r); if j = r then
F_a(1) = Y^{w_a}(1 + ψ̄_iψ_i), and the odd pieces vanish because ψ_r = ψ̄_r = 0. ∎

(The weight sits on the low-end piece, which may be at the head; this is still a scalar on α.)

### 3.3 Network, degree reduction, proof

The constraints are C_v = [out_x(v) = 1 ∧ in_x(v) = 1], reading the states of the arcs at v. By
Theorem 1.4 and Lemma 3.3 the value of N(directed data, β, order) is T⃗_G(Y); by Proposition 1.5 it
has P = w_3(μ) + g + g², B = (2 + bW)μ + 1, τ = 2^{3μ}(n+B)^{C₂}, U ≤ 2 log₂3·m + g³ (here μ_a
sums in- plus out-degrees).

**Lemma 3.5 (degree reduction).** Let Θ ≥ 2 and H := {v : d⁺(v) + d⁻(v) > Θ}. For each choice
π = (π_v)_{v∈H} of one out-arc and one in-arc at each v ∈ H, let G_π be G minus the other arcs at
these vertices. Then T⃗_G = Σ_π T⃗_{G_π}, there are ≤ Π_v d⁺(v)d⁻(v) ≤ n^{2|H|} branches,
|H| < 2m/Θ, and G_π has total degree ≤ Θ at every vertex (≤ 2 at vertices of H).

*Proof.* As [E, Lemma 6.1]: map a directed Hamiltonian cycle C to its out- and in-arc at each
v ∈ H; C survives exactly in G_{π(C)}, and a Hamiltonian cycle of G_π determines π. ∎

*Proof of Theorem TSP-2.* Step 0: if n ≤ 1 or some vertex has in- or out-degree 0, output 0.
Otherwise minimum total degree ≥ 2 ≥ 1. Steps 1–3 as in §2.4 with Lemma 3.5, b = m + 1, and the
digits of Σ_π Z_π (no division by n); branches G_π with a vertex of in- or out-degree 0 have
T⃗_{G_π} = 0 and are skipped, so Theorem 1.6/1.7 is only applied with minimum degree ≥ 1. The time bounds are those of Theorems 1.6 and 1.7 with
λ = 3, exactly as in §2.4. ∎

---------------------------------------------------------------------------------------------------

## 4. Theorem TSP-3: graphic TSP

### 4.1 Walks, Eulerian multi-subgraphs and the metric TSP

Let G = (V,E) be connected, n ≥ 2, with integer lengths ℓ_e ≥ 0, and d(u,v) the length of a
shortest u–v path. A *closed spanning walk* is a sequence v_0, v_1, …, v_L = v_0 (L ≥ 1) with
{v_{i−1}, v_i} ∈ E for all i and {v_0,…,v_L} = V; its length is Σ_i ℓ_{\{v_{i−1},v_i\}}. The
*metric TSP optimum* is OPT_d := min over cyclic orderings (u_1, …, u_n) of V of
Σ_{i=1}^{n} d(u_i, u_{i+1}) (indices mod n).

**Lemma 4.1.** Let n ≥ 2. The following three quantities are equal:

* (a) OPT_d;
* (b) the minimum length of a closed spanning walk;
* (c) min{ ℓ·x : x ∈ {0,1,2}^E, deg_x(v) even for every v, (V, supp x) connected }.

*Proof.* (b) ≤ (a): given a cyclic ordering, replace each pair (u_i, u_{i+1}) by a shortest path;
the concatenation is a closed walk of length Σ d(u_i,u_{i+1}) visiting every vertex. (a) ≤ (b):
given a closed spanning walk, let u_1 = v_0 and let u_2, …, u_n be the other vertices in the
order of their first visits. The walk splits into n consecutive segments, from the first visit of
u_i to the first visit of u_{i+1} (the last segment from the first visit of u_n to v_L = u_1); the
i-th segment is a u_i–u_{i+1} walk, of length ≥ d(u_i,u_{i+1}). Summing, length ≥ OPT_d.

(c) ≤ (b): for a closed spanning walk let x_e be the number of traversals of e, so ℓ·x is the
length. Every visit to a vertex enters it along one traversal and leaves along another (for v_0,
pair the last step with the first), so deg_x(v) = 2·#visits is even; supp x is connected and
spanning, because the walk visits every vertex along edges of supp x. If some x_e ≥ 3, replace x_e
by x_e − 2: degrees stay even, supp x is unchanged, and ℓ·x does not increase. Repeating gives a
feasible x ∈ {0,1,2}^E of length ≤ that of the walk. (b) ≤ (c): let x be feasible for (c). The
multigraph (V, x) (edge e taken x_e times) is connected — its vertex set is V and every vertex has
degree ≥ 1 since supp x is connected spanning and n ≥ 2 — and all degrees are even, so by Euler's
theorem it has an Eulerian circuit: a closed walk traversing every edge of the multigraph exactly
once, i.e. each e exactly x_e times. It visits every vertex and has length ℓ·x. ∎

(Euler's theorem for connected multigraphs with all degrees even is classical; a proof: a maximal
trail from v_0 must end at v_0 by the parity, and if it misses an edge, some vertex on it is
incident to a missed edge, and a maximal trail of missed edges from that vertex can be spliced in.)

### 4.2 The identity

**Lemma 4.2.** Φ_G(z) = Σ_{x even} [Ω_V] Π_{e: x_e ≥ 1} z^{x_eℓ_e}(1 + q_e) in Z[z]; all its
coefficients are ≥ 0; the coefficient of z^t is > 0 iff there is a feasible x for (c) of Lemma 4.1
with ℓ·x = t. Hence the lowest exponent of Φ_G is OPT_d, and its coefficient is
Σ_{x optimal} τ(V, supp x) ≥ #{optimal x}.

*Proof.* Lemma 2.2 with the weight x_eℓ_e on e gives the Berezin form. τ(V, supp x) ≥ 0, and
τ(V, supp x) > 0 iff (V, supp x) is connected. ∎

**Coefficient bound.** Φ_G has ≤ 3^m terms x and τ(V,F) ≤ n^{n−2} (Cayley), so every coefficient is
< 3^m n^{n−2} ≤ 2^{b} with b := ⌈m log₂ 3⌉ + ⌈(n−2) log₂ n⌉ + 1 = O(m + n log n). The degree is
≤ 2mW. Put Y := 2^b.

### 4.3 Splitting vertices: constant degree without branching

The constraint C_v = [deg_x(v) even] reads *all* edges at v, and a walk may use many of them, so
the branching of Lemma 2.7 is not available. Instead every vertex is split.

**Construction.** Order the edges at each vertex v as e_{v,1}, …, e_{v,d_v} (d_v = deg_G(v) ≥ 1).
The graph G′ = (V′, E′) has the *copies* v_1, …, v_{d_v} for each v; the edge e = {u,v} = e_{u,i} =
e_{v,j} of G becomes the *original edge* e′ = {u_i, v_j}; and for each v and 1 ≤ i < d_v there is
the *path edge* p_{v,i} = {v_i, v_{i+1}}. G′ is simple (an original edge joins copies of distinct
vertices, each copy meets exactly one original edge, and path edges join consecutive copies of one
vertex), n′ = Σ_v d_v = 2m, m′ = m + (2m − n) = 3m − n, every copy has degree ≤ 3 and ≥ 1, and
m′ ≤ (3/2)·n′. Let P ⊆ E′ be the set of path edges; P is a disjoint union of paths, hence a forest,
and G′/P = G (contracting each path to the vertex v). Root: r′ := r_1 for a fixed r ∈ V.

**Lemma 4.3 (forced edges).** For every X ⊆ E, with X′ the corresponding set of original edges of
G′, and generators Γ′ for V′ ∖ {r′},

```
[Ω_{V′}] ( Π_{p∈P} q_p · Π_{e′∈X′} (1 + q_{e′}) ) = τ(V, X).
```

*Proof.* Expand: Π_p q_p Π_{e′∈X′}(1+q_{e′}) = Σ_{F ⊆ X′} Π_{f ∈ P ∪ F} q_f, and by
[E, Lemma 3.3] (applied to the edge set P ∪ F, through the expansion in that proof the term of
the full set P ∪ F), [Ω_{V′}] Π_{f∈P∪F} q_f = [P ∪ F is a spanning tree of G′] when |P ∪ F| =
n′ − 1 and 0 otherwise (the term has 2|P ∪ F| generators). It remains to see that F ↦ P ∪ F is a
bijection between spanning trees of G with F ⊆ X and spanning trees of G′ containing P and
contained in P ∪ X′. If T := P ∪ F is a spanning tree of G′, then T/P is connected, has
|T| − |P| = (n′−1) − (n′−n) = n − 1 edges on the n vertices of G′/P = G, and is acyclic (a cycle in
T/P lifts to a closed trail in T using some edge outside P, hence to a cycle), so F is a spanning
tree of G. Conversely if F is a spanning tree of G, then P ∪ F is connected (every copy reaches its
path, and the paths are joined by F) with n′ − 1 edges, hence a spanning tree of G′. ∎

**Parity along the path.** Give each path edge p_{v,i} a state σ ∈ {0,1} and each original edge
its state x_e ∈ {0,1,2}. At the copy v_i (1 ≤ i ≤ d_v), with σ_{v,0} := 0, impose

```
C_{v_i} := [ σ_{v,i} ≡ σ_{v,i−1} + x_{e_{v,i}}  (mod 2) ]   for i < d_v,
C_{v_{d_v}} := [ σ_{v,d_v−1} + x_{e_{v,d_v}} ≡ 0  (mod 2) ].
```

**Lemma 4.4.** For fixed x ∈ {0,1,2}^E, Σ_{σ ∈ {0,1}^P} Π_{v′∈V′} C_{v′} = Π_{v∈V} [deg_x(v) even].

*Proof.* For each v the constraints at v_1, …, v_{d_v−1} determine σ_{v,i} = Σ_{j≤i} x_{e_{v,j}}
mod 2 uniquely, and the constraint at v_{d_v} then reads Σ_{j≤d_v} x_{e_{v,j}} ≡ 0. ∎

**The data on G′.** Edge states X = {0,1,2} for every edge of G′. On an original edge e′ of e the
state is the multiplicity x_e, with F_{e′}(x) := Y^{xℓ_e}(1 + q_{e′}) for x ∈ {1,2} and
F_{e′}(0) = 1. On a path edge p the state x ∈ {1,2} encodes σ := x − 1, with F_p(1) = F_p(2) := q_p;
the state 0 ("p absent") has F_p(0) = 1 as §1.1 requires, and is *forbidden by the constraints*:
every C_{v′} is 0 whenever a path edge at v′ has state 0 (the constraints of "Parity along the
path" are read with σ = x − 1). Alphabet L of size 9: N and the pairs (x, j) with x ∈ {1,2},
j ∈ {0,1,2,3}; st((x,j)) := x, st(N) = 0; π((x,j)) := [j ∈ {2,3}], π(N) = 0. Pieces: for an
original edge with low end s, high end t, α_{(x,j)} := Y^{xℓ_e} α_j(s,t), β_{(x,j)} := β_j(s,t),
with the pieces α_j, β_j of [E, §4]; for a path edge p = {s,t} and x ∈ {1,2} the four labels
(x, j) encode the four terms of q_p = ψ̄_sψ_s·1 + 1·ψ̄_tψ_t − ψ̄_s·ψ_t + ψ_s·ψ̄_t:
α_{(x,0)} = ψ̄_sψ_s, β = 1; α_{(x,1)} = 1, β = ψ̄_tψ_t; α_{(x,2)} = ψ̄_s, β = −ψ_t;
α_{(x,3)} = ψ_s, β = ψ̄_t; and α_N = β_N = 1.

**Lemma 4.5.** This data satisfies (Π1), (Π2) with λ = 9, |X| = 3, β₀ = 2bW, and its sum (1.1) on
G′ equals Φ_G(Y).

*Proof.* (Π1): the pieces are scalar multiples of those of [E, §4], or the monomials ψ̄_sψ_s, 1,
ψ̄_s, ψ_s (resp. 1, ψ̄_tψ_t, −ψ_t, ψ̄_t), homogeneous with the parities [j ∈ {2,3}]. (Π2): for an
original edge, Σ_j α_{(x,j)}β_{(x,j)} = Y^{xℓ_e}(1+q_{e′}) by [E, Lemma 4.1(b)]; for a path edge
the four products are ψ̄_sψ_s, ψ̄_tψ_t, −ψ̄_sψ_t, ψ_sψ̄_t, whose sum is q_p (as in that proof).
Coefficients ≤ Y^{2W} = 2^{β₀}; F has ≤ 5 monomials. In the sum (1.1) over X^{E′}, the
configurations with a path edge in state 0 have Π C_{v′} = 0; the others are pairs (x, σ) with
x ∈ {0,1,2}^E and σ ∈ {0,1}^P, and the sum is
Σ_{x,σ} Π_{v′} C_{v′} · [Ω_{V′}] Π_p q_p Π_{x_e≥1} Y^{x_eℓ_e}(1+q_{e′}) = Σ_x Π_v[deg_x(v) even] ·
Y^{ℓ·x} τ(V, supp x) by Lemma 4.4 (the σ-sum) and Lemma 4.3 with X = supp x (scalars central).
This is Φ_G(Y). ∎

### 4.4 Proof of Theorem TSP-3

*Algorithm.* If n = 1 output Φ_G = 1 (OPT = 0, empty walk). Otherwise build G′, the data of §4.3
and Y; evaluate Z = Φ_G(Y) by Theorem 1.6 applied to G′ (n′ = 2m ≤ 2Dn vertices, m′ ≤ (3/2)n′
edges, degrees in [1,3] ⊆ [1, n′/g + 2] once n′ ≥ g; smaller inputs take O(1) time) with
δ′ := δ/(2D) and D′ := 3/2; read the digits in base
2^b (coefficients < 2^b, degree ≤ 2mW). *Time:* 2^{δ′n′/2}(n′(β₀+1))^{C} ≤ 2^{δn/2}·(nW)^{C′},
since β₀ = 2bW = poly(n)·W. *Explicit rate:* Theorem 1.7 on G′ gives
2^{C*(max(m′,n′)/√log n′ + n′^{1/15} log(n′W))} = 2^{O(m/√log n + m^{1/15} log(nW))}, as
n′ = 2m ≤ n², m′ ≤ 3m, so log n′ ≥ log n, m′/√log n′ ≤ 3m/√log n, and n′^{1/15} ≤ (2m)^{1/15}
(for m ≥ n − 1 ≥ n/2, max(m′,n′) = O(max(m,n)) = O(m)). *Correctness:* Lemma 4.5, Theorem 1.4, Lemma 4.2, Lemma 4.1.

*Witness.* Self-reduction with pinning: for e ∈ E in turn and x ∈ {0,1,2} in increasing order,
restrict the state set of e to {x} (replace the data by the same data with C_v := 0 whenever
e's state differs from x at an endpoint v; this is again data of §1.1 with the same bounds) and
recompute the lowest exponent; keep the first x for which it still equals OPT_d. The invariant
"some optimal x extends the pins" holds initially and is preserved (one of the three values works);
after m edges the pins form an optimal x, from which an Eulerian circuit, i.e. an optimal closed
walk, is produced in polynomial time. At most 3m + 1 evaluations. ∎

### 4.5 What is exact and what is not

* **Exact:** OPT_d (the optimum of the metric TSP on the shortest-path metric of a sparse graph,
  the classical "graphic TSP" being the unit-length case), a witness walk, and for every t the
  τ-weighted count Σ_{x: ℓ·x = t, even, connected} τ(V, supp x).
* **Not obtained:** the number of optimal x, the number of optimal closed walks (as walks, or as
  Eulerian multi-subgraphs). The certificate τ(V, supp x) varies with x; this is the same
  limitation as rows 4c/5 of `exact-extensions.md` and the CONN type of `meta-theorem.md`. Exact
  counting would follow from a τ-free local connectivity indicator, which is open.
* The decision "is there a closed spanning walk of length ≤ t" is exact for every t (coefficients
  are ≥ 0 and lowest exponents are read off).

---------------------------------------------------------------------------------------------------

## 5. Weights beyond poly(n)

### 5.1 B is polynomial in the input length; the network theorem does not care

In Theorems TSP-1/2/3 the weights enter the network only through the scalars Y^{w_e} on the pieces
and the internal factors, i.e. through β₀ = bW (resp. 2bW) and B = (2 + β₀)μ + 1. The input length
is N_in ≥ m log₂(W+1). The three places where B enters the cost (Remark 1.8) are polynomial in B.
So the evaluation costs 2^{δn/2}·poly(n, B) = 2^{δn/2}·(nW)^{O_{δ,D}(1)}, which is **Theorem
TSP-1 (c)**: the dependence on W is pseudo-polynomial, not polynomial in log W. Concretely:

* W = poly(n): the (nW)^C factor is n^{O(1)}: Theorem TSP-1 (a), [E]-style "2^{δn} for every δ".
* W = 2^{εn}: (nW)^C = 2^{Cεn + O(log n)}: still 2^{δn} if ε ≤ δ/(2C(δ/2, D)); hence
  **W = 2^{o(n)} is exact**, Theorem TSP-1 (b).
* W = 2^{n^{c}} with c > 1, or W = 2^{poly(n)} in general: (nW)^C = 2^{Ω(n^{c})}: the bound is
  useless, although the algorithm remains correct.

So the question of the task ("does [A]'s network theorem tolerate B polynomial in the input length,
including the weight bits?") has the answer **yes, and that is not the obstacle**. The obstacle is
that B is not polynomial in the input length: B ≈ b·W·μ is polynomial in W, i.e. exponential in
the weight bits. The next subsection shows that no choice of Kronecker encoding avoids this.

(The Lean model of [A] receives K, g, P, B in unary; for B = poly(n)·W with W exponential this
input is exponential. The statements above are in the operation-count model of the printed [A],
as are [E]'s Theorems 1 and 2.)

### 5.2 Why Kronecker substitution needs W = 2^{o(n)}

The tour polynomial T_G has degree up to nW and up to min(nW + 1, #HC(G)) nonzero terms. Kronecker
substitution z = 2^b is a ring homomorphism Z[z] → Z that is injective on polynomials with
coefficients in [0, 2^b) and degree ≤ d only through integers of b(d+1) bits. The network's value
is one integer Z = Σ Π W_a Π Ψ, and the node tables are integers < 2^B, so Z < |Π S_a|·2^{gB} has at
most gB + gP bits. Hence recovering T_G (or any polynomial with ≥ nW/poly distinct possible
degrees) from Z forces B ≥ b·nW/poly(n). The proposal in the task description, "b = n log W + O(n)
bits", confuses the digit width b (which indeed only needs m + log n + 1 bits) with the number of
digits nW + 1, which is exponential. `tsp_check.py` (T7) and `tsp_largew.py` (L2) measure this:
on a fixed 6-vertex graph the table bit-length is 57, 113, 225, 449, 897 for W = 1, 2, 4, 8, 16,
and the Kronecker integer has b(nW+1) − O(b) bits.

The same applies to any ring homomorphism φ : Z[z] → R into a ring whose elements have poly(n)
bits: the optimum is min{t : [z^t]T_G ≠ 0}, and φ(T_G) = Σ_t c_t φ(z)^t. If R is finite with
poly(n)-bit elements, the sequence φ(z)^t is eventually periodic with preperiod + period at most
|R| = 2^{poly}; two natural choices are φ(z) nilpotent (R = Z[z]/(z^{T+1}): reads the lowest T
exponents, useless for T < nW), or φ(z) of finite order q (R ⊇ Z[z]/(z^q − 1): residue counts).
The latter is analysed next.

### 5.3 Residue counts and sparse interpolation do not give the optimum

For a modulus q, counting tours by weight residue, N_q(j) := #{H : w(H) ≡ j (mod q)}, is a
product-form sum: replace w_e by w_e mod q (exponents < nq), compute T with those weights, and fold
the exponents mod q. It costs B = O(b·nq·μ), polynomial for q = poly(n).

**Proposition 5.2.** Let Q be a finite set of pairwise coprime moduli, each ≥ 2, with |Q| ≥ 2, and
N := Π_{q∈Q} q. There are two 2-element sets S, T ⊆ {0, …, N−1} with the same residue counts modulo
every q ∈ Q (indeed modulo every divisor of every q ∈ Q) and min T < min S. Consequently, for every
graph with exactly two Hamiltonian cycles H_1 ≠ H_2 (e.g. the 6-vertex, 8-edge graph found by
`tsp_largew.py`) there are two weightings w, w′ with w_e, w′_e < N, tour weights S and T, such
that N_q(w) = N_q(w′) for every q ∈ Q but the optima differ.

*Proof.* Pick q_1 ∈ Q and put N_1 := q_1, N_2 := N/q_1 ≥ 2, coprime. Let S := {N−2, N−1}, and by
the Chinese remainder theorem let t_1, t_2 ∈ [0, N) be defined by t_1 ≡ N−2 (mod N_1),
t_1 ≡ N−1 (mod N_2), t_2 ≡ N−1 (mod N_1), t_2 ≡ N−2 (mod N_2). Every q ∈ Q divides N_1 or N_2
(pairwise coprimality), and modulo N_1 as well as modulo N_2 the multisets {t_1,t_2} and
{N−2, N−1} coincide, so they coincide modulo every divisor of every q ∈ Q. Also t_1 ≠ N−1 (they
differ mod N_1 since N_1 ≥ 2), t_1 ≠ N−2 (mod N_2), and likewise t_2 ∉ {N−2, N−1}; so
T := {t_1, t_2} ⊆ [0, N−3], min T < N−2 = min S, and t_1 ≠ t_2 (they differ mod N_1). For the
graph: H_1 and H_2 have private edges f_1 ∈ H_1 ∖ H_2, f_2 ∈ H_2 ∖ H_1; put w = s_1 on f_1, s_2 on
f_2, 0 elsewhere (and likewise w′ with t_1, t_2). ∎

Example (Q = {2,3}, N = 6): S = {4,5}, T = {1,2}; residue counts (1,1) mod 2 and (0,1,1) mod 3
agree; checked by `tsp_largew.py` L1 through the product-form computation. The modulus 6 = N
distinguishes them, but it exceeds the weight range, which is the exponential-degree Kronecker
case. (The restriction to pairwise coprime Q is for the proof; L1-type examples exist for
non-coprime sets too, e.g. {9,11} and {3,5} modulo 4 and 6.) So polynomially many residue oracles,
or equivalently T_G modulo (z^q − 1) for poly-size q, cannot determine the optimum in general.

**Evaluations modulo primes.** The network can also compute T_G(z) mod p for any integers z and
poly-bit prime p (reduce all tables mod p; B = log p). T_G is a sparse polynomial with
T := #HC(G) terms and degree ≤ nW. Deterministic sparse interpolation over F_p (Garg–Schost,
Giesbrecht–Roche, Ben-Or–Tiwari with discrete logarithms in a smooth-order group) recovers *all*
exponents from O(T) evaluations, or from residues modulo O(T² log(nW)) good primes; T can be
2^{Ω(n)} on sparse graphs (cubic graphs with exponentially many Hamiltonian cycles exist), so this
costs 2^{Ω(n)}·2^{δn}, worse than Held–Karp. Whether the *lowest* exponent alone can be read off
from 2^{δn} such evaluations is open; we know no method and no lower bound. (If G has exactly one
tour, T_G(3) mod 2^k = 3^{w(H)} mod 2^k, and the 2-adic logarithm gives w(H) mod 2^{k−2} in
polynomial time; with two or more tours this becomes the "sum of powers" problem.)

**Binary search with a threshold oracle.** "#{H : w(H) ≤ t}" is not a product-form sum: the
indicator [w(H) ≤ t] of a sum is not a product of per-edge factors, and the only product-form
truncations are T_G mod z^{t+1} (B ≈ bt, exponential) or the residue counts above.

**Scaling with exactness recovery.** Scaling preserves the optimum only up to additive error n·2^s
(Lemma 5.3); the standard exactness-recovery arguments (for shortest paths, matchings, flows) use LP
duality or a decision oracle for the exact problem, neither of which is available here. We record
what scaling does give.

### 5.4 What is obtained for arbitrary binary weights

**Lemma 5.3 (window).** Let w ≥ 0, s ≥ 0, w′_e := ⌊w_e / 2^s⌋, OPT := min_H w(H) and
h\* := min_H w′(H). Then 2^s h\* ≤ OPT < 2^s(h\* + n).

*Proof.* For every tour H, 2^s w′(H) ≤ w(H) < 2^s(w′(H) + n), since each of the n edges loses less
than 2^s. Apply the left inequality to an optimal H (w′(H) ≥ h\*) and the right one to a tour
achieving h\*. ∎

**Proposition 5.4 ((1+ε)-approximation, deterministic).** Fix δ > 0, D ≥ 1. There is an algorithm
that, given G with ≤ Dn edges, integer weights 0 ≤ w_e ≤ W given in binary, and ε ∈ (0,1], outputs
a tour H with w(H) ≤ (1+ε)·OPT, or reports that G has no tour, within
(m+1)·2^{δn}·(n/ε)^{C(δ,D)}·poly(log W) operations.

*Proof.* For each edge f: let G_f := (V, {e : w_e ≤ w_f}), let s_f := max{s ≥ 0 : 2^s·n ≤ ε w_f}
(s_f := 0 if ε w_f < n), w̃_e := ⌊w_e / 2^{s_f}⌋ for e ∈ G_f. Then w̃_e ≤ w_f/2^{s_f} < 2n/ε + 1
(by maximality, 2^{s_f+1} n > ε w_f, or s_f = 0 and w_f < n/ε), so W̃ = O(n/ε) and Theorem TSP-1
computes T_{G_f}(z) with weights w̃ in 2^{δn}(n/ε)^{C}; by Corollary 0.2 a tour H_f of minimum
w̃-weight h_f is found with m + 1 further evaluations. Output the H_f with the smallest w(H_f).
Let H\* be optimal for w and f\* a heaviest edge of H\*. Then H\* ⊆ G_{f\*}, so
h_{f\*} ≤ w̃(H\*) ≤ w(H\*)/2^{s_{f\*}}, and by the right inequality of Lemma 5.3 (applied in
G_{f\*}) w(H_{f\*}) < 2^{s_{f\*}}(h_{f\*} + n) ≤ OPT + n·2^{s_{f\*}} ≤ OPT + ε w_{f\*} ≤ (1+ε) OPT,
using w_{f\*} ≤ w(H\*) = OPT (weights ≥ 0). If ε w_{f\*} < n then s_{f\*} = 0 and H_{f\*} is
exactly optimal in G_{f\*}, hence for G. Arithmetic on the original weights is polynomial in
log W. ∎

Checked numerically on 40-bit weights (`tsp_largew.py` L3, L4, ε = 1/2, 1/4, 1/8).

**Verdict.** For sparse graphs: the tour polynomial is exact for W = 2^{o(n)}, with the explicit
rate for log W ≤ n^{14/15}/√log n (TSP-1, TSP-1′); for W = 2^{poly(n)} the method gives a
deterministic (1+ε)-approximation in 2^{δn}·poly(n/ε) and exact residue/evaluation oracles, but
**not** the exact optimum; that remains open, and the reason is structural (ring-valued
product-form sums versus a min-plus quantity), not a bookkeeping issue in [A].

---------------------------------------------------------------------------------------------------

## 6. Barrier: dense graphs and the (2 − ε)^n question

Everything above is per edge. In the exponent of Theorems 1.6 and 1.7 the leading term is
e_ℓ·U with U ≈ 2 log₂λ·m_×, where m_× is the number of crossing edges of a degree-balanced
partition; for every term of the cost the relevant quantity is |E|, not n:

* **Crossing edges.** For [A, Lemma 8] the partition must keep every μ_a ≤ O(m/g) (the per-node
  bound P). In a graph whose every balanced partition into g parts cuts Θ(m) edges (expanders, and
  K_n with m_× ≥ (1 − 1/g)·n²/2), U = Θ(m) and the clique term is 2^{e_ℓ·Θ(m)}.
* **Blob tables.** τ = 2^{Θ(μ)} = 2^{Θ(m/g)}, and B′ ≥ 2gP/K with gP = Θ(m): the second term of
  [A, (1.1)] is 2^{Θ(m/K)}.

So the time is 2^{δ·m} for every δ (Theorem 1.6) and 2^{O(m/√log n)} (Theorem 1.7); nothing better
is obtained by this method. Consequences:

1. **K_n and general metric TSP.** m = n(n−1)/2 gives 2^{δn²}, resp. 2^{O(n²/√log n)}, far above
   Held–Karp's O(2^n n²). Theorem TSP-3 covers only metrics whose shortest-path support is a sparse
   graph; a general metric on n points has no such support. Nothing is claimed for metric TSP,
   Euclidean TSP, or TSP on K_n with arbitrary weights.
2. **Average degree.** Writing m = dn/2: Theorem TSP-1 costs 2^{δ d n} for every δ, which is
   2^{δn} for every δ iff d = O(1), and with the explicit rate 2^{O(dn/√log n)}, which is below 2^n
   iff **d = o(√log n)**, i.e. m = o(n√log n). For √log n ≪ d ≪ n the bounds of Cygan–Pilipczuk
   (2^{(1−ε_d)n}, average degree d) and Björklund et al. (bounded maximum degree) are not improved,
   and for d = Θ(n) nothing beats Held–Karp.
3. **Position-based encodings do not help.** An encoding of a tour by vertex positions
   (a permutation) is a local CSP with n⌈log₂ n⌉ bits; evaluating such a network costs
   2^{e_ℓ·Θ(n log n)} = 2^{Θ(n√log n)} with the pieces of [A, Theorem B], and 2^{δ n log n} in the
   fixed-density form, both worse than 2^n. Cut&Count-style encodings (connectivity marks per
   vertex plus one bit per edge) still carry Θ(m) edge bits. The Berezin factor 1 + q_e has Schmidt
   rank 4 across any cut separating its ends, so every edge of the 2-factor must transmit
   ≥ log₂ 4 bits in any blob network of this kind; the per-edge cost is intrinsic to the template,
   not to the bookkeeping.
4. **The (2 − ε)^n question.** Whether TSP on n-vertex graphs (or Hamiltonicity deterministically)
   can be solved in (2−ε)^n time for some ε > 0 has been open since Bellman and Held–Karp (1962)
   and is listed in Woeginger's 2003 survey; the best general results are Björklund's randomised
   O\*(1.657^n) for unweighted undirected Hamiltonicity and Nederlof's conditional randomised
   O(1.9999^n) for bipartite TSP. Our theorems say **nothing** about it: they are subexponential
   exactly in the regime d = o(√log n) where the per-edge cost is below one bit per vertex. They
   do supersede the (2 − ε_Δ)^n bounds for bounded degree, and the exact-counting bounds
   parameterised by pathwidth on sparse graphs, as explained in `sharp-eth-catalogue.md`.
5. **Planar graphs.** 2^{δn} does not beat the known 2^{O(√n)}.

---------------------------------------------------------------------------------------------------

## 7. State of the art for TSP, with verified citations

All bounds are deterministic unless marked. Citations were checked on 28 Oct 2026 against the
linked pages (publisher, arXiv, dblp or author pages). "Ours" bounds are conditional on the imports
of [A] listed in §0, like [E].

| Setting | Best previous bound | Source | Ours |
|---|---|---|---|
| TSP, general graphs/metrics, exact | O(2^n n²), exponential space | Bellman, J. ACM 9 (1962) 61–63, https://doi.org/10.1145/321105.321111 ; Held–Karp, J. SIAM 10 (1962) 196–210, https://doi.org/10.1137/0110015 ; https://en.wikipedia.org/wiki/Held%E2%80%93Karp_algorithm | none (§6) |
| TSP, (2−ε)^n for general graphs | **open** | Woeginger, *Exact algorithms for NP-hard problems: a survey*, LNCS 2570 (2003) 185–207, https://doi.org/10.1007/3-540-36478-1_17 ; https://research.tue.nl/en/publications/exact-algorithms-for-np-hard-problems-a-survey/ | untouched |
| Undirected Hamiltonicity, general | O\*(1.657^n) randomised; bipartite O\*(1.415^n) | Björklund, SIAM J. Comput. 43(1) (2014) 280–299 (FOCS 2010), https://arxiv.org/abs/1008.0541 | none for dense graphs |
| Bipartite TSP | O(1.9999^n) randomised, assuming ω = 2 | Nederlof, STOC 2020, https://doi.org/10.1145/3357713.3384264 | none |
| TSP, maximum degree Δ | O((2 − ε_Δ)^n), ε_Δ > 0 depending only on Δ; polynomial space for bounded integer weights | Björklund–Husfeldt–Kaski–Koivisto, ACM Trans. Algorithms 8(2) (2012) 18:1–18:13, https://doi.org/10.1145/2151171.2151181 (ICALP 2008, https://doi.org/10.1007/978-3-540-70575-8_17) | deterministic 2^{δn}·(nW)^{C} with the whole weight distribution (TSP-1); explicit rate 2^{O(Δn/√log n)} |
| TSP, average degree d | O\*(2^{(1−ε_d)n}), exponential space | Cygan–Pilipczuk, Inf. Comput. 243 (2015) 75–85, https://arxiv.org/abs/1302.3763 | 2^{δn} for d = O(1); 2^{O(dn/√log n)} in general, better than 2^n iff d = o(√log n) |
| TSP, cubic graphs | O(2^{n/3}) ≈ 1.260^n (Eppstein; degree 4: ≈ 1.890^n); O(1.2553^n) (Liśkiewicz–Schuster, correcting Iwama–Nakashima's 1.251^n); O\*(1.2312^n) polynomial space (Xiao–Nagamochi); degree 4: 1.692^n | Eppstein, J. Graph Algorithms Appl. 11(1) (2007) 61–81, https://doi.org/10.7155/jgaa.00137 , https://arxiv.org/abs/cs/0302030 ; Liśkiewicz–Schuster, J. Discrete Algorithms 27 (2014) 1–20, https://arxiv.org/abs/1207.4694 ; Xiao–Nagamochi, Algorithmica 74 (2016), https://arxiv.org/abs/1212.6831 ; Xiao–Nagamochi, Theory Comput. Syst. 58 (2016) 241–272 | deterministic 2^{δn} for every δ, exact tour polynomial |
| #HC and TSP by pathwidth | 6^{pw}·poly counting (rank-based), tight under SETH | Bodlaender–Cygan–Kratsch–Nederlof, https://arxiv.org/abs/1211.1505 ; Curticapean–Lindzey–Nederlof, https://arxiv.org/abs/1709.02311 | 2^{O(m/√log n)} regardless of pathwidth |
| #HC, general graphs | 2^{n−Ω(√n)} (Li 2023), improving 2^{n−Ω(√(n/log log n))} (Björklund–Kaski–Williams, Algorithmica 2019) | https://arxiv.org/abs/2309.15422 ; https://doi.org/10.4230/LIPIcs.IPEC.2017.6 ; directed, average degree d: 2^{n−Ω(n/d)}, Björklund–Williams, https://doi.org/10.4230/LIPIcs.ICALP.2019.25 | none for dense graphs |
| ATSP, sparse digraphs | Held–Karp 2^n; BHKK-type (2−ε)^n bounds for bounded degree | as above | 2^{δn}·(nW)^{C} exact T⃗_G (TSP-2) |
| Graphic TSP, exact | Held–Karp O\*(2^n) on the metric closure (dense), nothing specific to sparse supports found | as above | 2^{δn}·(nW)^{C} optimum and witness (TSP-3) |
| Graphic TSP, approximation (context) | 3/2 (Christofides 1976 / Serdyukov 1978); 3/2 − ε₀ (Oveis Gharan–Saberi–Singh, FOCS 2011); 1.461 (Mömke–Svensson, FOCS 2011); 13/9 (Mucha, STACS 2012); **7/5** (Sebő–Vygen, Combinatorica 34 (2014) 597–629) | Mömke–Svensson https://arxiv.org/abs/1108.1130 ; Sebő–Vygen https://arxiv.org/abs/1201.1870 (whose introduction is the source checked for the OSS, Mucha and Christofides/Serdyukov attributions) | exact, but 2^{δn} time |
| Metric TSP, approximation (context) | 3/2 − ε, ε > 10^{−36}, randomised | Karlin–Klein–Oveis Gharan, STOC 2021, https://arxiv.org/abs/2007.01409 (Oper. Res. 72(6) (2024) 2543–2594) | none |

Notes. (i) The task description lists "BHKK TALG 2012" and "Eppstein cubic TSP 1.26^n / 2^{n/3}";
both check out as stated. Eppstein's own publication page notes that his cycle-listing analysis
misses a case and that his TSP bound has been improved (Liśkiewicz–Schuster, Xiao–Nagamochi).
(ii) The Björklund 1.657^n bound is for Hamiltonicity (decision, unweighted), not TSP. (iii) The
degree-4 bound 1.692^n of Xiao–Nagamochi appeared in Theory of Computing Systems, not Algorithmica.
(iv) Lower bounds: Hamiltonian cycle/path and TSP on sparse graphs have 2^{Ω(n)} lower bounds under
ETH (Lokshtanov–Marx–Saurabh, https://arxiv.org/abs/1007.5450), now vacuous; the counting lower
bound (6 − ε)^{pw} under SETH is about pathwidth and is not contradicted (pw = Θ(n) on expanders).

---------------------------------------------------------------------------------------------------

## 8. Numerical verification (exact integers)

All scripts use Python integers only, randomise the root, the crossing order and the generator
order, and compare three independent computations: combinatorial brute force, the determinant /
polynomial identity, and the literal network (settings as fixed-length bit strings, base-λ blocks,
copy bits, W_a, Ψ_{a,b}, f_{a,b}), evaluated by the black-box brute-force evaluator and by the
Lemma 1/Lemma 8 grouping of `proof_lib.py` (`eval_network_brute`, `eval_network_grouped`). The
graphic-TSP network uses the generic exact-Schmidt-rank engine `ext_engine.py` on the split graph.

| script | checks | run |
|---|---|---|
| `tsp_check.py` (TSP-1) | T1 Lemma 2.1 as polynomials; T2 Lemma 2.2 on all 2-factors and random subsets; T3 Lemma 2.5 for both orientations and root ends; T4 Theorem 1.2 (sum over all 5^{m_×} labellings); T5 Theorem 2.6: brute-force network = K-grouping (K = 2, 3) = n·T_G(2^b), decoded optimum, #optimal, distribution; T6 Proposition 1.5: P_a ≤ P, (i), U, \|W_a\| < 2^B; T7 table bits double with W | seeds 1 (24 instances, n ≤ 9, g ≤ 5, random/planted/interleaving partitions, W ≤ 4; 88 s) and 3 (13 instances, n ≤ 8): ALL CHECKS PASSED. (A run with seed 5 and no size cap reached n = 9–10 instances, completed 13 of them without failure and timed out at 20 min; the generator now caps n ≤ 8.) |
| `tsp_atsp.py` (TSP-2) | A1 Lemma 3.2 (det = #in-arborescences, brute force) on random arc sets; A2 Lemma 3.1 on random integer matrix pairs; A3 Berezin form of det L_out^{(r)}; A4 Lemma 3.3 as polynomials and termwise; A5 Lemma 3.4 pieces; A6 blob factorisation and the base-3 network, brute force = grouping = T⃗_G(2^b), decoding; A7 U = 2Σ⌈e log₂3⌉ + 2C(g,3), \|W_a\| < 2^B | seeds 1 (16 instances, n ≤ 6) and 3 (12): ALL CHECKS PASSED |
| `tsp_graphic.py` (TSP-3) | G1 Lemma 4.1 (metric closure by permutations = closed-walk optimum over {0,1,2}^E; multiplicity 3 never helps); G2 Lemma 4.2 (lowest exponent, coefficient = Σ τ ≥ #optimal x); G3 Lemmas 4.3–4.5 (the split-graph Berezin sum equals Φ_G(Y)); G4 networks on the original graph (9 labels) and on the split graph (≤ 9 labels), K = 2, 3; G5 witness by self-reduction | seeds 1 and 2 (6 instances each, n ≤ 6, unit and random lengths 1..3): ALL CHECKS PASSED (43 s and 11 s); run log in §8.1 |
| `tsp_largew.py` (§5) | L1 Proposition 5.2 on an actual two-tour graph (residue counts agree mod 2 and 3, optima 4 vs 1; mod 6 = full distribution distinguishes); L2 Kronecker integer bits ≈ b(nW+1); L3 Lemma 5.3; L4 Proposition 5.4 with ε = 1/2, 1/4, 1/8 on 40-bit weights, self-reduced tours checked to be Hamiltonian cycles | seed 1: ALL CHECKS PASSED |

Run logs: `python3 tsp_check.py 1 24`, `python3 tsp_atsp.py 1 16`, `python3 tsp_atsp.py 3 12`,
`python3 tsp_largew.py 1` each print ALL CHECKS PASSED (about one minute each or less). The
literal network evaluators enumerate every setting of every node (|S_a| = λ^{|δ(a)|}2^{|Q_a|}),
so `tsp_check.py` skips the network part (T5, T6's table bound) on instances with
max_a |S_a| > 40000 and still checks T1–T4 and the remaining parameters there. The graphic-TSP
results are recorded in §8.1.

### 8.1 Run log, graphic TSP

`python3 tsp_graphic.py 1 6` (43 s), columns: n, m, lengths, OPT_d, number of optimal x,
τ-weighted coefficient Φ_G[OPT], split graph (n′, m′), network rows (K, #crossing edges, max
labels per crossing edge) on the original and on the split graph:

```
[0] n=5 m=4 unit  OPT=8  #opt x=1 tau-weighted=1  split n'=8  m'=7   orig [(2,2,9),(3,2,9)] split [(2,2,8),(3,3,9)]
[1] n=4 m=6 rand  OPT=6  #opt x=2 tau-weighted=5  split n'=12 m'=14  orig [(2,3,3),(3,5,9)] split [(2,3,8)]
[2] n=6 m=7 unit  OPT=7  #opt x=1 tau-weighted=5  split n'=14 m'=15  orig [(2,4,9),(3,4,9)]
[3] n=4 m=4 rand  OPT=8  #opt x=1 tau-weighted=1  split n'=8  m'=8   orig [(2,1,3),(3,4,9)] split [(2,2,8),(3,4,9)]
[4] n=4 m=6 unit  OPT=4  #opt x=3 tau-weighted=12 split n'=12 m'=14  orig [(2,3,9),(3,5,9)] split [(2,3,9)]
[5] n=5 m=7 rand  OPT=10 #opt x=1 tau-weighted=5  split n'=14 m'=16  orig [(2,4,9),(3,5,9)]
ALL CHECKS PASSED
```

Instances [1] and [4] show the non-exactness of §4.5 concretely: 2 (resp. 3) optimal
multi-subgraphs, but coefficient 5 (resp. 12). The split-graph networks were evaluated only when
the random partition had ≤ 4 crossing edges (engine cost); the single-blob split sum (G3) was
checked on every instance.

---------------------------------------------------------------------------------------------------

## 9. What is proved, what is assumed, what is open

**Proved here (complete proofs above, on top of [E, §§2–5] which are reused by reference):**

* the template of §1: sign rule, blob factorisation, network value and parameters for arbitrary
  label alphabets with weighted homogeneous pieces (Proposition 1.1, Theorems 1.2, 1.4,
  Proposition 1.5), and the two evaluation theorems 1.6, 1.7 *from* the imported statements;
* TSP-1/1′: Lemmas 2.1–2.7 and §2.4;
* TSP-2: the directed fermionic matrix-tree theorem (Lemmas 3.1, 3.2), the directed identity
  (Lemma 3.3), the 3-label pieces (Lemma 3.4), degree reduction (Lemma 3.5);
* TSP-3: Lemma 4.1 (walks = Eulerian multi-subgraphs with multiplicities ≤ 2 = metric TSP),
  Lemma 4.2, the splitting Lemmas 4.3–4.5 and the witness procedure;
* §5: Proposition 5.2 (residue counts do not determine the optimum), Lemma 5.3,
  Proposition 5.4, and the analysis of where B enters.

**Assumed:** exactly the three imports of [E, §0]: [A, Lemma 8(i)], [A, Theorem A(a),(b)], and
pieces ([A, Theorem B] for the explicit rate; [A, Lemma 2] suffices for the fixed-density
theorems, as does the pair [A, Lemma 1 + Proposition 3]). The composition with our networks is on
paper only, as in [E, §9].

**Not claimed / open:**

* exact TSP with weights 2^{poly(n)} on sparse graphs in 2^{δn} (§5);
* the number of optimal closed walks in graphic TSP (§4.5);
* anything on dense graphs, metric TSP in general, or the (2 − ε)^n question (§6);
* practicality: as in [A] and [E], the constants are astronomical.

**Relation to the existing notes.** `exact-extensions.md` row 2 (TSP/ATSP) and
`meta-theorem.md` row 13 (graph-metric TSP) were [Computed] sketches; this note is their proof,
with the bit bookkeeping and the hub handling (branching for degree-2 problems, splitting for the
walk problem) written out. `exact-extensions.md` §3's "Weights must be poly(n)" is sharpened to
W = 2^{o(n)} and the large-weight question is settled in the negative for the Kronecker route.
