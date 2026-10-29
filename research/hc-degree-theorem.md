# Exact counting of Hamiltonian cycles in time 2^{O(n log Δ / √log n)}: bits per vertex, not per edge

29 Oct 2026. This note upgrades the exact #HC theorem of `exact-hc-theorem.md` (cited as [HC];
`paper/main.tex` Theorems 1.1–1.2 are its polished form) from a bound in the number of edges,
2^{O((m+n)/√log n)}, to a bound in the number of vertices times the logarithm of the degree,
2^{O(n log Δ/√log n)}. The only change is in §5 of [HC], the network: a pair of blobs no longer
shares one base-5 label per crossing edge, but only the *set* of crossing edges between them that
lie in the 2-factor, rank-encoded among the subsets of the right size, together with the labels of
those edges. This is the device of Anthropic's manuscript [A], Appendix D, Step 3 (`VariableBound.
Net.rank`, `cw t μ = ⌈log C(t,μ)⌉`; see `research/permanent/anthropic-m-independence.md` and
`research/permanent/scripts/perm_degree_block.py`, where it is applied to the permanent). Everything
of [HC] up to Theorem 4.6 (fermionic matrix-tree theorem, pieces, sign rule, blob factorisation) is
reused verbatim. The theorems remain **conditional on (H_A)**, exactly as in [HC] §0 and
`paper/main.tex` §1.2: Lemma 8 case (i), Theorem A(a),(b) and Theorem B of [A].

Verification: `research/scripts/hc_degree_network.py` (exact integers, PASS; §6).

---------------------------------------------------------------------------------------------------

## 0. Results

Conventions as in [HC]: G = (V,E) simple, n = |V|, m = |E|, Δ the maximum degree, d̄ := 2m/n the
average degree, log = log₂, #HC(G) counts Hamiltonian cycles as subgraphs, #HC(G) = 0 for n ≤ 2.
Time is counted as in [A, §3]. Throughout, λ(x) := log(2e·x) = log x + 2.4427 for x ≥ 2.

**Theorem A (maximum degree).** Assume (H_A). There are an absolute constant C_A and one
deterministic algorithm that, given any graph G with n ≥ 2 vertices and maximum degree Δ ≥ 2,
outputs #HC(G) within

```
2^{ C_A · n · log(2eΔ) / √(log n) }   ≤   2^{ 3.5 C_A · n · log Δ / √(log n) }
```

operations. In particular the time is 2^{o(n)} whenever log Δ = o(√log n), that is, for every
Δ = 2^{o(√log n)}; this includes Δ = (log n)^{O(1)} and Δ = 2^{(log n)^{0.49}}.

**Theorem B (average degree).** Assume (H_A). There are an absolute constant C_B and one
deterministic algorithm that, given any graph G with n ≥ 2 vertices and m ≥ n edges, outputs
#HC(G) within 2^{C_B · n · log(2e·2m/n)/√(log n)} = 2^{O(n log d̄/√log n)} operations. (If m < n
some vertex has degree < 2 and #HC(G) = 0.) Since d̄ ≤ Δ, Theorem B implies Theorem A.

**Corollary C (fixed rate).** Assume (H_A), or only [A, Lemma 1 and Proposition 3].

* (a) For every δ > 0 and every Δ₀ ≥ 2 there is a deterministic algorithm that outputs #HC(G)
  within O(2^{δn}) operations on every graph of maximum degree ≤ Δ₀. The achievable pair (K, e)
  of [A] it needs satisfies only e ≤ δ/(8 log(2eΔ₀)) and K ≥ 24 log(2eΔ₀)/δ, instead of
  e ≤ δ/(20Δ₀), K ≥ 30Δ₀/δ in [HC] §6.3.
* (b) For every δ > 0 there is c_δ > 0 and one deterministic algorithm that outputs #HC(G) within
  O(2^{δn}) operations on every graph with maximum degree Δ ≤ 2^{c_δ √log n} (and, by Theorem B,
  on every graph with average degree d̄ ≤ 2^{c_δ √log n}).

Decision, search and Hamiltonian paths follow as in [HC] §7, with the factor m + 1.

**Comparison.**

| regime | [HC] / paper Thm 1.2 | this note |
|---|---|---|
| leading exponent term | e_ℓ · 2 log5 · m ≈ 2.32 e_ℓ Δn (Δ-regular) | e_ℓ · 2n log(2eΔ) ≈ 2 e_ℓ n(log Δ + 2.44) |
| subexponential iff | m = o(n √log n), i.e. d̄ = o(√log n) | log d̄ = o(√log n), i.e. d̄ = 2^{o(√log n)} |
| dense graphs (Δ ≈ n) | 2^{Θ(n²/√log n)}, useless | 2^{O(n log n/√log n)}, still above 2^n |
| per-node bits P | ≈ log5 · (2m/g) : needs Lemma 6.1 branching at Θ = n/g | ≈ (2n/g) log(2eΔ) + g² : no branching |

The new leading term is smaller than the old one for every Δ ≥ 4 (2 log(2eΔ) < 2.32Δ), and
exponentially so for large Δ. Against the literature (`paper/main.tex` Table 1): Björklund's
O*(1.657^n) randomized decision algorithm [SICOMP 2014] and the deterministic O*(2^n) bound are
unconditional and work for all graphs; Björklund–Husfeldt–Kaski–Koivisto [TALG 2012] count
Hamiltonian cycles (and solve TSP) in O*((2 − ε_Δ)^n) for maximum degree Δ, and Cygan–Pilipczuk
[Inf. Comput. 2015] solve TSP in 2^{(1−ε_d)n}·poly(n) for average degree d, with ε → 0 as the
degree grows;
Björklund–Williams [ICALP 2019] count in 2^{n−Ω(n/d)} for average degree d. All of these are
(2 − ε)^n with ε → 0 as the degree grows. Conditionally on (H_A), Theorems A and B are 2^{o(n)} for
every degree up to 2^{o(√log n)}, and they beat 2^n exactly when C_A log(2eΔ) < √log n. Like all
bounds inherited from [A], they are asymptotic only: the crossover is astronomically far.

---------------------------------------------------------------------------------------------------

## 1. The accounting, in one paragraph

A 2-factor X uses exactly 2 of the deg(v) edges at every vertex v. So the information "which
crossing edges at V_a are in X" is at most Σ_{v∈V_a} log C(deg v, 2) ≤ 2 Σ_{v∈V_a} log deg(v) ≤
2|V_a| log Δ bits, and the fermionic labels on the ≤ 2|V_a| used crossing edges cost 2 bits each.
The network of [HC] §5 instead spends log 5 bits on *every* crossing edge, whether or not it is
in X, which is why its total is 2 log5·m. The repair is to let a pair of blobs {a,b} share the set
S_ab ⊆ E(a,b) of used crossing edges between them, as its rank among the subsets of E(a,b) of the
same size s_ab (⌈log C(e_ab, s_ab)⌉ bits), plus the 2-bit labels of its elements. The size s_ab
must be fixed in advance, because shared bit strings have fixed length and because the per-pair
widths must not over-count a node's global budget of 2|V_a| used edges: this is done by summing
over *profiles* (s_ab)_{a<b}, of which there are at most (n+3)^{g²/2} = 2^{o(n/√log n)}, exactly as
in [A, App. D, Step 3] and in `perm_degree_block.py`. Everything else, in particular the sign rule
and the parity copies, is untouched, because (S_ab, labels) is a re-encoding of the labels on
E(a,b) and all signs are functions of the labels.

---------------------------------------------------------------------------------------------------

## 2. Profiles and the network N_s

Fix G with n ≥ 3 and minimum degree ≥ 2, a root r, a partition β : V → [g] and a crossing order, with
all the conventions of [HC] §4 (blobs V_a, crossing edges e_1 < ⋯ < e_{m_×}, low/high ends, E(a,b)
for a < b, e_ab := |E(a,b)|, δ(a), labels L = {N,0,1,2,3}, pieces, π, σ_a, P_ab, Q_a, χ_a, I_a).
Write ν_a := |V_a|, ν := max_a ν_a, μ_a := Σ_{v∈V_a} deg(v), μ := max_a μ_a, and m_× for the number
of crossing edges.

**Definition 2.1 (profiles).** A *profile* is an integer vector s = (s_ab)_{a<b} with
0 ≤ s_ab ≤ e_ab. Put s_ba := s_ab, the *row sums* s_a := Σ_{b≠a} s_ab and the *total*
|s| := Σ_{a<b} s_ab. The profile of a labelling ℓ ∈ L^{m_×} is s(ℓ)_ab := #{k ∈ E(a,b) : ℓ_k ≠ N}.
A profile is *admissible* if s_a ≤ 2ν_a for every a.

**Combinatorial number system.** For 0 ≤ s ≤ e, the map {t_1 < ⋯ < t_s} ⊆ {0,…,e−1} ↦
Σ_{i=1}^{s} C(t_i, i) is a bijection from the s-subsets of {0,…,e−1} onto {0,…,C(e,s)−1} (colex
rank; Lehmer, Knuth TAOCP 7.2.1.3). Its inverse is computed greedily with ≤ e binomial
comparisons. Write cw(e,s) := ⌈log C(e,s)⌉ (so cw = 0 when C(e,s) = 1).

**Definition 2.2 (the network N_s = N_s(G,r,β,order) on [g]).** Fix a profile s.

*Settings.* A setting of node a is a pair (ℓ^{(a)}, y^{(a)}) with ℓ^{(a)} ∈ L^{δ(a)} such that
#{k ∈ E(a,b) : ℓ^{(a)}_k ≠ N} = s_ab for every b ≠ a, and y^{(a)} ∈ {0,1}^{Q_a}. It is encoded as
the concatenation of

* for each b ≠ a in increasing order, the *block* block_b(z_a) of width
  c′_ab := cw(e_ab, s_ab) + 2 s_ab: let k_1 < ⋯ < k_{e_ab} enumerate E(a,b) in crossing order and
  S_ab := {i : ℓ^{(a)}_{k_i} ≠ N} (so |S_ab| = s_ab); the block is the colex rank of S_ab in
  cw(e_ab, s_ab) bits (lowest first), followed by, for each i ∈ S_ab in increasing order, the 2-bit
  binary code of ℓ^{(a)}_{k_i} ∈ {0,1,2,3};
* the bits y^{(a)}_{cd}, (c,d) ∈ Q_a in lexicographic order.

P_a := Σ_{b≠a} c′_ab + |Q_a|. S_a is the set of strings of length P_a whose rank field in every
block is < C(e_ab, s_ab).

*Node functions.* W_a(z_a) := σ_a(ℓ^{(a)}) · χ_a(ℓ^{(a)}, y^{(a)}) · I_a(ℓ^{(a)}), as in [HC] Def. 5.1.

*Edges, for a < b.* Ψ_ab, c_ab := c′_ab + (g − b), π_ab, π_ba and f_ab, f_ba are those of [HC]
Def. 5.1 with the new blocks:

```
Ψ_ab(z_a,z_b) := Π_{k∈E(a,b)} [ℓ^{(a)}_k = ℓ^{(b)}_k] · Π_{d=b+1}^{g} [y^{(a)}_{bd} = P_{bd}(ℓ^{(b)})],
π_ab(z_a) := (block_b(z_a), y^{(a)}_{b,b+1}, …, y^{(a)}_{b,g}),   π_ba(z_b) := (block_a(z_b), P_{b,b+1}(ℓ^{(b)}), …, P_{b,g}(ℓ^{(b)})),
f_ab(z_a,θ) := [π_ab(z_a) = θ],   f_ba(z_b,θ) := [π_ba(z_b) = θ].
```

**Lemma 2.3 (encoding).** The encoding is a bijection from the settings of a onto S_a; hence
|S_a| = Π_{b≠a} C(e_ab, s_ab) 4^{s_ab} · 2^{|Q_a|}. Moreover block_b(z_a) = block_a(z_b) if and only
if ℓ^{(a)} and ℓ^{(b)} agree on E(a,b).

*Proof.* Both ends list E(a,b) in the same (crossing) order. The block determines (S_ab, labels on
S_ab), hence ℓ|E(a,b) (the labels off S_ab are N); conversely a restriction with exactly s_ab non-N
labels gives exactly one block, and every rank < C(e_ab, s_ab) is the rank of exactly one subset.
The y bits are free. ∎

**Lemma 2.4 (= [HC] Lemma 5.2).** (f_ab, f_ba) factors Ψ_ab through c_ab bits: by Lemma 2.3,
Ψ_ab = [π_ab(z_a) = π_ba(z_b)], and Observation (b) after Definition 1 of [A] applies. ∎

**Theorem 2.5 (value).** For every profile s,

```
Z_s := value(N_s) = Σ_{ℓ ∈ L^{m_×} : s(ℓ) = s} Π_a σ_a(ℓ) χ_a(ℓ, P(ℓ)) I_a(ℓ).
```

Consequently Σ_{s profile} Z_s = n·#HC(G). Moreover Z_s = 0 unless s is admissible, so

```
n·#HC(G) = Σ_{s admissible} Z_s .
```

*Proof.* As in [HC] Thm 5.3: a term is nonzero only if all Ψ equal 1, which means (i) there is a
global ℓ ∈ L^{m_×} with ℓ^{(a)} = ℓ|δ(a) for all a, and (ii) y^{(a)}_{cd} = P_{cd}(ℓ) for all
a < c < d. By the constraint in Definition 2.2 such an ℓ has s(ℓ) = s, and conversely every ℓ with
s(ℓ) = s determines exactly one z with (i) and (ii). This gives the formula. The profiles partition
L^{m_×} by ℓ ↦ s(ℓ), so Σ_s Z_s = Σ_ℓ Π_a σ_a χ_a(P) I_a = n·#HC(G) by [HC] Theorem 4.6. If s is not
admissible, say s_a > 2ν_a, then every ℓ with s(ℓ) = s has Σ_{v∈V_a} deg_ℓ(v) = s_a > 2ν_a, so some
v ∈ V_a has deg_ℓ(v) ≥ 3, every indicator [deg_x(v) + deg_ℓ(v) = 2] in I_a(ℓ) vanishes, I_a(ℓ) = 0,
and Z_s = 0. ∎

---------------------------------------------------------------------------------------------------

## 3. Parameters

**Lemma 3.1 (binomial estimates).**

* (a) (Vandermonde) Π_i C(e_i, s_i) ≤ C(Σ_i e_i, Σ_i s_i): the left side is one term of the
  coefficient of t^{Σs_i} in Π_i (1+t)^{e_i}.
* (b) For integers 0 ≤ M ≤ N, log C(N, M) ≤ M log(eN/M) (with the convention 0 for M = 0), since
  C(N,M) ≤ N^M/M! and M! ≥ (M/e)^M. The function F_N(M) := M log(eN/M) + 2M is nondecreasing on
  [0, N], because its derivative is log(N/M) + 2 ≥ 0.
* (c) Σ_i ⌈x_i⌉ ≤ Σ_i x_i + #{i : x_i > 0}.

**Proposition 3.2 (parameters of N_s).** Let n ≥ 3, minimum degree ≥ 2 (so m ≥ n), Δ ≥ 2, and let s
be admissible. Put λ := log(2eΔ) and

```
Λ := min( 2ν·λ ,  3.45·μ ),        P := ⌈Λ⌉ + g + g²,        B := ⌈Λ⌉ + 1,        τ := 2^{Λ} · n^{C₂},
```

with C₂ absolute. Then N_s is a network in the sense of Definition 2 of [A] with parameters P, B, τ
(τ counted after a polynomial-time preparation, and realised by procedures with poly(n) memory),
and

```
Σ_{b≠a} c′_ab ≤ min(2ν_a λ, 3.45 μ_a) + g − 1                          for every node a,
U = 2 Σ_{a<b} c′_ab + 2·C(g,3) ≤ 2 log C(m_×, |s|) + g² + 4|s| + 2·C(g,3)
  ≤ 2n·log(2e·d̄) + g³ ≤ 2n·log(2eΔ) + g³ = 2n(log Δ + 2.443) + g³ .
```

*Proof.*

*Per node.* Fix a and let N_a := |δ(a)| = Σ_{b≠a} e_ab. Each crossing edge at a has one end in V_a and
each internal edge two, so 2|E_int(a)| + N_a = μ_a; also N_a ≤ Σ_{v∈V_a} deg v ≤ Δν_a. Thus
N_a ≤ min(Δν_a, μ_a). By admissibility and s_ab ≤ e_ab, s_a ≤ min(2ν_a, N_a). By Lemma 3.1 (c), (a),

```
Σ_{b≠a} c′_ab = Σ_b cw(e_ab, s_ab) + 2s_a ≤ log C(N_a, s_a) + (g−1) + 2s_a ≤ F_{N_a}(s_a) + g − 1 .
```

*Route Δ.* If 2ν_a ≤ N_a, monotonicity gives F_{N_a}(s_a) ≤ F_{N_a}(2ν_a) = 2ν_a log(eN_a/(2ν_a)) +
4ν_a ≤ 2ν_a log(eΔ/2) + 4ν_a = 2ν_a log(2eΔ) = 2ν_a λ. If N_a < 2ν_a, then F_{N_a}(s_a) ≤
F_{N_a}(N_a) = N_a(log e + 2) < 2ν_a(log e + 2) ≤ 2ν_a λ, because λ ≥ log(4e) = 2 + log e for Δ ≥ 2.
*Route μ.* F_{N_a}(s_a) ≤ F_{N_a}(N_a) = (log e + 2) N_a ≤ 3.443 μ_a ≤ 3.45 μ_a.

*P_a ≤ P and (i).* P_a = Σ_b c′_ab + C(g−a, 2) ≤ Λ + g − 1 + g²/2 ≤ P. The copy bits on pairs at a
number C(g−a,2) + (a−1)(g−a) ≤ g² ([HC] Prop. 5.4), so Σ_{b≠a} c_ab ≤ Λ + g − 1 + g² ≤ P.

*U.* U = 2Σ_{a<b} c_ab = 2Σ_{a<b} c′_ab + 2Σ_{a<b}(g−b) = 2Σ_{a<b} c′_ab + 2C(g,3). By Lemma 3.1 (c), (a),
Σ_{a<b} cw(e_ab, s_ab) ≤ log C(m_×, |s|) + C(g,2), which gives the first bound. Admissibility gives
2|s| = Σ_a s_a ≤ 2Σ_a ν_a = 2n, so |s| ≤ n, and |s| ≤ m_× ≤ m. By monotonicity of F_{m_×}:
if n ≤ m_× then log C(m_×,|s|) + 2|s| ≤ F_{m_×}(n) = n log(e m_×/n) + 2n ≤ n log(em/n) + 2n; if
m_× < n then it is ≤ F_{m_×}(m_×) = (log e + 2) m_× < (log e + 2) n ≤ n log(em/n) + 2n, because
m ≥ n. Hence Σ_{a<b} c′_ab ≤ n log(em/n) + 2n + g²/2 = n log(4em/n) + g²/2 = n log(2e d̄) + g²/2, and
U ≤ 2n log(2e d̄) + g² + 2C(g,3) ≤ 2n log(2e d̄) + g³ for g ≥ 2. Finally d̄ ≤ Δ.

*(ii).* Ψ and f are 0/1-valued and |σ_aχ_a| = 1. In I_a(ℓ) = Σ_x [deg] [ω_a](F_a(x)Γ_a(ℓ)), the sum
runs over x ⊆ E_int(a) with deg_x(v) ≤ 2 for all v ∈ V_a (other x give 0). The map
x ↦ (x ∩ δ(v))_{v∈V_a} is injective, and each coordinate is a subset of size ≤ 2 of the ≤ deg(v)
internal edges at v, so the number of such x is at most Π_{v∈V_a}(1 + deg v + C(deg v, 2)) ≤
Π_v (deg v)² ≤ Δ^{2ν_a} (for d ≥ 2, 1 + d + d(d−1)/2 ≤ d²); it is also at most 2^{|E_int(a)|} ≤
2^{μ_a/2}. For each x, |x| ≤ ν_a (because 2|x| = Σ_v deg_x(v) ≤ 2ν_a) and exactly s_a ≤ 2ν_a of the
pieces in Γ_a(ℓ) are not 1. The ℓ¹-norm of coefficient vectors is submultiplicative in Λ(Γ) (the
structure constants are 0, ±1), each factor 1 + q_e has ℓ¹-norm ≤ 5 and each non-trivial piece
ℓ¹-norm ≤ 2, so |[ω_a](F_a(x)Γ_a(ℓ))| ≤ 5^{|x|}·2^{s_a} ≤ 20^{ν_a}. Hence

```
|W_a| ≤ min(Δ^{2ν_a}, 2^{μ_a/2}) · 20^{ν_a},
log|W_a| ≤ min( 2ν_a(log Δ + 2.161), μ_a/2 + 2.161 μ_a ) ≤ min(2ν_a λ, 2.67 μ_a) ≤ Λ < B .
```

*(iii).* The preparation stores the graph, β, the crossing order, the lists E(a,b), the binomials
C(e_ab, s_ab) (≤ 2^m), the widths and the layout: polynomial. Membership in S_a, decoding (one
unranking per block, ≤ e_ab binomial comparisons), encoding, π_ab, Ψ, f take poly(n + g)
operations; σ_a takes O(|δ(a)|²) and χ_a O(g³). For I_a, enumerate the x of (ii) — either as
subsets of E_int(a), or as tuples (x_v)_{v∈V_a} of ≤ 2-subsets of the internal edges at v, kept when
they are consistent — in at most min(2^{μ_a/2}, Δ^{2ν_a}) iterations; for each x test the degree
condition and compute [ω_a](F_a(x)Γ_a(ℓ)) by choosing one monomial from each of the ≤ 3ν_a
non-trivial factors (≤ 5^{|x|}2^{s_a} ≤ 20^{ν_a} choices), multiplying the chosen monomials (sign by
inversion count) and adding the coefficient when the product is ±ω_a. The state is a tuple of
counters, one monomial and one accumulator of O(Λ) bits: poly(n) memory. Altogether
τ ≤ min(2^{μ/2}, Δ^{2ν}) · 20^{ν} · n^{C₂} ≤ 2^{Λ} n^{C₂}, by the arithmetic of (ii). ∎

**Lemma 3.3 (profiles).** The number of admissible profiles is at most
Π_{a<b}(min(e_ab, 2ν) + 1) ≤ (2ν + 1)^{C(g,2)}, and the number of all profiles is at most
(m+1)^{C(g,2)}. They are enumerated in polynomial time each, and admissibility is tested in
polynomial time.

---------------------------------------------------------------------------------------------------

## 4. The algorithms and their running times

### 4.1 Theorem A

**Lemma 4.1 (vertex-balanced partition).** List V as v_1,…,v_n and put β(v_t) := ⌈tg/n⌉. Then
β(V) ⊆ [g] and ν_a ≤ ⌈n/g⌉ for every a (blobs may be empty).

*Proof.* β⁻¹(a) = {t : (a−1)n/g < t ≤ an/g} is the set of integers in a half-open interval of
length n/g, which has at most ⌈n/g⌉ elements. ∎

**Algorithm A, on input G.**

0. If n ≤ 2, or some vertex has degree < 2, output 0. (Otherwise m ≥ n and Δ ≥ 2.)
1. Choose the level ℓ as in [HC] §6.4: for n ≥ n₀ := K₀^{30}, ℓ is the largest index with
   K_ℓ^{30} ≤ n; put K := K_ℓ, g := 3K⁸. (For n < n₀, any exact method: O(1) time.)
2. Take β from Lemma 4.1, any root r and any crossing order. Do the preparation of Prop. 3.2.
3. For each admissible profile s (Lemma 3.3): build N_s implicitly, with P, B, P_a, c_ab computed
   exactly; run the procedure of Lemma 8(i) of [A] on it with the algorithm of Theorem A(b) at level
   ℓ as the clique algorithm (on a (K, L)-clique with B′ in the role of B); call the result Z_s.
4. Output (Σ_s Z_s)/n.

Correctness: Theorem 2.5, Lemma 8 and Theorem A(b) of [A]. The imported hypotheses are checked
exactly as in [HC] §6.2, with Prop. 3.2 in place of Prop. 5.4.

**Bounds for one profile.** By [HC] §6.4, n^{1/300} < K ≤ n^{1/30}, g ∈ [3n^{8/300}, 3n^{8/30}] and
e := e_ℓ ≤ c_e/√log n with c_e absolute. By Lemma 4.1, ν ≤ n/g + 1, so Λ ≤ 2νλ ≤ (2n/g + 2)λ, and
Prop. 3.2 gives, using λ ≤ log(2en) ≤ 2 log n,

```
U ≤ 2nλ + g³,      gP ≤ 2(n+g)λ + 3g³,      B ≤ Λ + 2,      log τ ≤ Λ + C₂ log n,
L = ⌈(U + gP/K)/K²⌉ ≤ U + gP + 1 = poly(n),      B′ = ⌈2gP/K⌉ + g²B = poly(n).
```

By (1.1) and (1.2) of [HC] the time for one profile is 2^X with X bounded by (6.2) of [HC]:

```
X ≤ 1 + max{ g log K,  e(U + gP/K + K²) + C₀K² log(K(L+B′)) + 2gP/K + log τ } + C₁ log(g(P+B)) + O(log n),
```

and the terms are

```
e·U                      ≤ c_e (2nλ + 27 n^{0.8}) / √log n,
(e+2)·gP/K               ≤ 3(2(n+g)λ + 3g³) / n^{1/300}  =  O(nλ · n^{−1/300}),
log τ                    ≤ (2n/g + 2)λ + C₂ log n        =  O(nλ · n^{−8/300}) + O(log n),
eK² + C₀K² log(K(L+B′))  =  O(n^{1/15} log n),
g log K = O(n^{8/30} log n),      C₁ log(g(P+B)) = O(log n),
log(#profiles)           ≤ C(g,2) log(2ν+1)              =  O(n^{16/30} log n)        (Lemma 3.3).
```

Every term is O(nλ/√log n) uniformly in Δ, because λ ≥ log(4e) > 3.4 and n^{1−1/300}, n^{0.8},
n^{16/30} log n, n^{8/30} log n are all O(n/√log n). Summing over the profiles multiplies the time by
2^{O(n^{16/30} log n)}. Hence the total is 2^{C_A nλ/√log n} for an absolute C_A, and
λ = log Δ + 2.443 ≤ 3.443 log Δ for Δ ≥ 2. This proves Theorem A. ∎

### 4.2 Theorem B

Let d̄ := 2m/n ≥ 2 (as m ≥ n) and λ̄ := log(2e d̄) ≥ log(4e) > 3.4.

*Case 1: λ̄ ≥ √log n.* Run a deterministic exact #HC algorithm with 2^n n^{O(1)} operations
(dynamic programming over subsets, counting Hamiltonian paths from a fixed vertex, Bellman 1962 /
Held–Karp 1962; or inclusion–exclusion, Karp 1982). This is 2^{n + O(log n)} ≤ 2^{2nλ̄/√log n}.

*Case 2: λ̄ < √log n*, so d̄ < 2^{√log n}/(2e). Let n₁ be an absolute constant with
2^{√log n} ≤ n^{1/1000} for n ≥ n₁ (log n ≥ 10⁶ suffices); for n < n₁ use any exact method. For
n ≥ n₁:

* Apply [HC] Lemma 6.1 (degree reduction) with Θ := ⌈n^{0.6}⌉. Then |H| < 2m/Θ = d̄n/Θ ≤
  n^{0.4 + 1/1000}, so there are at most n^{2|H|} = 2^{O(n^{0.401} log n)} branches, and each branch
  G_π has n vertices, m_π ≤ m edges and maximum degree Δ_π ≤ Θ ≤ n^{0.6} + 1. Skip a branch with a
  vertex of degree < 2 (its count is 0); otherwise m_π ≥ n.
* In each branch take β from [HC] Lemma 6.2 (degree-balanced), so μ ≤ 2m_π/g + Δ_π ≤
  d̄n/g + n^{0.6} + 1, and run steps 1–4 of Algorithm A on G_π with this β. Use route μ of Prop. 3.2:
  Λ ≤ 3.45μ. Then

```
e·U          ≤ c_e(2n log(2e·2m_π/n) + g³)/√log n ≤ c_e(2nλ̄ + 27n^{0.8})/√log n,
(e+2)·gP/K   ≤ 3(3.45(d̄n + g n^{0.6} + g) + 3g³)/n^{1/300}  =  O(n^{1 + 1/1000 − 1/300}) + O(n^{0.87}) = o(n/√log n),
log τ        ≤ 3.45(d̄n/g + n^{0.6} + 1) + C₂ log n       =  O(n^{1 + 1/1000 − 8/300}) + O(n^{0.6}) = o(n/√log n),
```

  and the remaining terms, the profile count (now with ν ≤ n: C(g,2) log(2n+1) = O(n^{16/30} log n))
  and the branching are as before. Each branch costs 2^{O(nλ̄/√log n)}, so does the total, and the
  outputs of the branches are summed ([HC] Lemma 6.1). ∎

### 4.3 Corollary C

(a) Fix δ ∈ (0,1], Δ₀ ≥ 2, λ₀ := log(2eΔ₀). By [A] (Theorem A(a), or Proposition 3) there is an
achievable (K, e) with e ≤ δ/(8λ₀) and K ≥ 24λ₀/δ; fix it and g := 3K⁸, a constant. Run Algorithm A
with this K (or its Lemma 1 variant, [HC] §6.3). With ν ≤ n/g + 1 and Prop. 3.2 the exponent terms are
e·U ≤ 2enλ₀ + eg³ ≤ δn/4 + g³; (e+2)gP/K ≤ 6nλ₀/K + O_{δ,Δ₀}(1) ≤ δn/4 + O_{δ,Δ₀}(1);
log τ ≤ 2nλ₀/g + O_{δ,Δ₀}(log n) ≤ δn/4 + O_{δ,Δ₀}(log n) (since g ≥ 24λ₀/δ ≥ 8λ₀/δ); the rest,
including the profile count C(g,2) log(2n/g + 3), is O_{δ,Δ₀}(log n). Total O(2^{δn}).

(b) Theorem A gives 2^{C_A nλ/√log n} ≤ 2^{δn} as soon as log(2eΔ) ≤ (δ/C_A)√log n, so
c_δ := δ/(2C_A) works for large n; Theorem B likewise with d̄. ∎

---------------------------------------------------------------------------------------------------

## 5. Is the degree reduction still needed?

**For Theorem A: no.** Neither Lemma 6.1 (branching on vertices of degree > n/g) nor Lemma 6.2
(degree-balanced partition) is used; Lemma 4.1 (equal-size blobs) replaces both. The reason is
the shape of the per-node bound in Prop. 3.2. In [HC] Prop. 5.4 a node's bits are P_a ≈ log5·|δ(a)|,
one base-5 digit per crossing edge at the node, so a single vertex of degree d adds log5·d bits to
P, and the term 2gP/K of Lemma 8 forced μ ≤ (2m+n)/g + 2, hence Δ ≤ n/g (branching, n^{4mg/n}
branches) and degree balance. Now a vertex of degree d adds at most log C(d, 2) + 4 ≤ 2 log d + 4
bits: Σ_b c′_ab ≤ 2ν_a log(2eΔ) + g for *every* blob, whatever the degrees of its vertices. Since
Δ ≤ n, even a blob of ⌈n/g⌉ vertices of degree n − 1 has only (2n/g + 2) log(2en) + g² + g bits, and
gP/K = O(n log n/K) is o(n log Δ/√log n) for every Δ ≥ 2. High-degree vertices hurt only
logarithmically, so there is nothing to branch on.

**For Theorem B: yes, but differently.** To state the bound in the average degree d̄ one needs the
per-node bits to be controlled by the blob's degree sum rather than by Δ. This is route μ of
Prop. 3.2: Σ_b c′_ab ≤ 3.45 μ_a + g, and Lemma 6.2 still gives μ_a ≤ 2m/g + Δ, so it still gives
blobs with bounded crossing information, as asked. The Δ in this bound is what Lemma 6.1 removes,
but the threshold can now be Θ = n^{0.6} instead of n/g: the branched vertices number at most
d̄n^{0.4} and the branching cost 2^{O(d̄ n^{0.4} log n)} is negligible, whereas in [HC] it was
n^{O(mg/n)}. (A partition balanced in both vertex count and degree sum — deal the vertices in order
of decreasing degree round-robin into g blobs, giving ν_a ≤ ⌈n/g⌉ and μ_a ≤ 2m/g + Δ simultaneously —
would allow the still larger threshold Θ ≈ n d̄/g, but it is not needed.)

The regime split in Theorem B (Case 1: d̄ ≥ 2^{√log n}/(2e), use the 2^n·poly algorithm) is only
there because the gP/K term, O(d̄n/K), exceeds the claimed bound O(n log d̄/√log n) when d̄ is
polynomial in n; in that regime the claimed bound exceeds 2^n anyway. Theorem A needs no such
split.

---------------------------------------------------------------------------------------------------

## 6. Numerical verification (exact integers)

`research/scripts/hc_degree_network.py [seed] [instances]` imports the Grassmann algebra, pieces,
σ_a, P_ab, χ_a and I_a of `proof_lib.py` (the independent implementation of [HC] §§2–4, already
verified by `proof_checks.py`) and implements Definition 2.2 on top of them: the colex rank/unrank,
the blocks, fixed-length bit-tuple settings, W_a, Ψ_ab, π_ab, f_ab, c_ab, the profiles, and a
brute-force evaluator over Π_a S_a that uses W and Ψ only as black boxes (settings with W_a = 0 are
dropped, which is exact). Instances: random graphs with min-degree ≥ 2 and arbitrary or
vertex-balanced blobs (g ∈ {2,3,4}); "hub" graphs (a cycle plus a vertex of degree n − 1, so
Δ = n − 1 while m ≈ 2n); planted Hamiltonian cycles visiting four blobs in interleaving order
(0,2,1,3) (the case where the interleaving sign matters, [HC] C12); planted blob graphs with random
crossing edges. Random root, crossing order and generator order throughout; n ≤ 9.

| check | what is verified |
|---|---|
| D1 | colex rank is a bijection onto [0, C(e,k)) and unrank inverts it, all e ≤ 8 |
| D2 | every setting has length P_a; decode∘encode = id; strings with an invalid rank field are rejected; P_a ≤ P; (i) Σ_b c_ab ≤ P |
| D3 | Ψ_ab = Σ_θ f_ab f_ba (exhaustive over θ ∈ {0,1}^{c_ab} when c_ab ≤ 10, else on the two projections and 20 random θ); Ψ symmetric; c symmetric; \|W_a\| < 2^B; \|I_a\| ≤ Δ^{2ν_a}20^{ν_a} and ≤ 2^{\|E_int(a)\|}20^{ν_a} |
| D4 | per node: Σ_b cw(e_ab,s_ab) ≤ cw(\|δ(a)\|, s_a) + #{b : C(e_ab,s_ab) ≥ 2}; Σ_b c′_ab ≤ 2ν_a log(2eΔ) + g − 1 and ≤ 3.45 μ_a + g − 1 |
| D5 | U = 2Σ c′_ab + 2C(g,3); Π C(e_ab,s_ab) ≤ C(m_×, \|s\|); \|s\| ≤ n; U ≤ 2cw(m_×,\|s\|) + 2C(g,2) + 4\|s\| + 2C(g,3); U ≤ 2n log(2e d̄) + g³ ≤ 2n log(2eΔ) + g³ |
| D6 | #admissible profiles ≤ (2ν+1)^{C(g,2)} |
| D7 | Σ_{s admissible} Z_s = n·#HC(G) (brute force) and every inadmissible profile has Z_s = 0 (so the sum over all profiles is n·#HC too) |

**Runs** (all print PASS):

| command | instances | checks |
|---|---|---|
| `python3 hc_degree_network.py` (seed 2026) | 24 | D1 135, D2 554 939, D3 168 176, D4 7 359, D5 4 080, D6 24, D7 211 |
| `python3 hc_degree_network.py 11 40` | 40 | D1 135, D2 833 277, D3 162 735, D4 7 797, D5 4 608, D6 40, D7 288 |
| `python3 hc_degree_network.py 7 30` | 30 | D1 135, D2 583 856, D3 106 217, D4 5 535, D5 3 414, D6 30, D7 182 |

**U table** (excerpt of the seed-2026 run; U_new = max over admissible profiles of U(N_s), U_old =
2Σ w_ab + 2C(g,3) of [HC] Def. 5.1 on the same partition and order, "exact" = the integer bound
2cw(m_×, min(n,m_×)) + 2C(g,2) + 4n + 2C(g,3), "Δ-bound" = 2n log(2eΔ) + g³):

| instance | n | m | Δ | g | ν | m_× | #HC | profiles / admissible | U_new | U_old | exact | Δ-bound |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| random, arbitrary blobs | 5 | 9 | 4 | 3 | 2 | 7 | 6 | 30 / 20 | 28 | 38 | 38 | 71.4 |
| random, balanced blobs | 6 | 9 | 4 | 4 | 2 | 7 | 1 | 72 / 47 | 30 | 46 | 50 | 117.3 |
| random, balanced blobs | 8 | 11 | 4 | 4 | 2 | 9 | 0 | 216 / 185 | 40 | 56 | 60 | 135.1 |
| hub (Δ = n−1) | 6 | 10 | 5 | 3 | 2 | 8 | 5 | 45 / 32 | 32 | 42 | 42 | 84.2 |
| hub (Δ = n−1), seed 11 | 8 | 14 | 7 | 2 | 7 | 3 | 7 | 4 / 3 | 12 | 14 | 34 | 92.0 |
| planted HC, interleaving | 5 | 7 | 3 | 4 | 2 | 6 | 2 | 64 / 45 | 24 | 44 | 46 | 104.3 |
| random, balanced blobs | 9 | 9 | 2 | 4 | 3 | 7 | 0 | 72 / 72 | 36 | 46 | 56 | 126.0 |
| random, balanced blobs | 8 | 13 | 4 | 3 | 3 | 9 | 2 | 64 / 52 | 38 | 44 | 48 | 98.1 |

At these sizes U_new < U_old on every instance, but the asymptotic gain only appears for larger
degrees; the script also prints the two leading terms for Δ-regular graphs, 2n log(2eΔ) versus
2 log5·m = log5·nΔ: for n = 1000, Δ = 3: 8 055 vs 6 966 (old smaller); Δ = 10: 11 529 vs 23 219;
Δ = 100: 18 173 vs 232 193; for n = 10⁶, Δ = 1000: 2.5·10⁷ vs 2.3·10⁹.

---------------------------------------------------------------------------------------------------

## 7. Formalising this in Lean, on top of the existing files

The Lean development (`lean-bridge-anthropic/bridge/EthFollowup/ExactHC/`, symlinked into
`/home/user/anth-build/bridge/…`; status in `research/lean-blueprint.md`) proves Theorems 1 and 2 of
[HC] at TM level (`Package.lean: theorem1`, `UPackage.lean: theorem2`). What stays and what changes:

**Unchanged (the mathematical layer).** `Grassmann.lean`, `Fermion.lean`, `MatrixTree.lean`,
`SignRule.lean`, `Incidence.lean`, `Blobs.lean`, `Main.lean` (`blob_factorisation`: Theorem 4.6).
Also unchanged: the `LabelSystem` *data* `hcSystem` in `HCNetwork.lean` (items, lo/hi, holder/
source, `par`, `T = σ·χ·I`, locality lemmas), the ℓ¹-norm theory `norm1_*` there, and the whole
imported side (`groupingExplicit`, `recursionSolves`, `halfPieces`, `Printed.groupingLemma`,
`CountKSat.exists_tmW`, …): nothing downstream of `Net.Is` moves.

**`LabelNetwork.lean` (the generic label-sharing network).** `LabelSystem.net` encodes every item
with one fixed-width `LabelCode L w` (`encL`, `decL`, `proj` concatenate per-item codes along
`pairItems a b`). The new network needs a *per-pair* code: a structure `PairCode` giving, for each
pair (a,b) and the fixed profile entry `s a b`, an injective encoding of the fibre
{ℓ : pairItems a b → L | #{k : ℓ k ≠ dflt} = s a b} into words of length `cap a b` = cw(e,s) + 2s,
with a decoder returning `none` off the image. `enc`/`dec`/`proj` and `net` are rewritten with it;
`S a` becomes the image of the local states whose row is the profile row. The lemmas `dec_enc`,
`length_enc`, `length_proj`, `mem_S`, `Ψ_symm`, `c_symm`, `fact` (Ψ = Σ_θ f f′) use only
injectivity and fixed length, so their proofs transfer. `value_net` becomes
`value_net_profile : (X.net C s).value = Σ_{ℓ : profile ℓ = s} Π_a T a ℓ (par · ℓ)` (Theorem 2.5,
first part), proved exactly like `value_net` with the fibre condition carried along. The rank code
itself goes in a new file `Unrank.lean`: colex rank of an s-subset of `Fin e` (Mathlib has
`Finset.Colex`; the rank is Σ_i C(t_i, i+1)), `rank_lt_choose`, `unrank_rank`, `rank_unrank`, the
2-bit label code (`finCode 3`), and `PolyT` for rank and unrank.

**`HCNetwork.lean`.** Add `profile (ℓ) a b`, `Admissible s`, `I_eq_zero_of_not_admissible`
(pigeonhole on `deg_ℓ`, from the existing degree indicator in `I`), and
`sum_admissible_value : Σ_{s admissible} (net s).value = n·#HC` (Theorem 2.5) from
`value_net_profile`, `blob_factorisation` and `Finset.sum_fiberwise`. Replace the parameter
theorem `abs_hcT_le` (|T| ≤ 2^{3|E_int|+|δ|}) by `abs_I_le_degree : |I_a| ≤ Δ^{2ν_a}·20^{ν_a}` and
`abs_I_le_mu : |I_a| ≤ 2^{|E_int(a)|}·20^{ν_a}` — the ℓ¹ facts `norm1_one_add_qEdge_le`,
`norm1_pieceA_le/B_le`, `norm1_list_prod_le`, `abs_topCoeff_le` are already there; new is the
counting lemma `card_degLeTwo_le` (injection x ↦ (x ∩ δ(v))_v). The per-node and total bit bounds
(Prop. 3.2) need Vandermonde (`Nat.add_choose_eq` in Mathlib, iterated) and log C(N,M) ≤ M log(eN/M)
— Anthropic's development has exactly these as `sum_lg_choose_le` and display (59) in
`variables/VariableBound/Net/SizeU.lean` (see `anthropic-m-independence.md` §2); the monotonicity
of F_N is a one-line real inequality. The copy-bit count `card_copy_le` is unchanged.

**`LabelProcs.lean` (C1b: mem/Ψ/f procedures).** `memF`, `psiF`, `fF`, `projF` read fixed blocks
`blk w z i` of a layout `Lay` with one width `w` for all items. The layout gets per-pair widths
`cap a b` and the profile row; decoding a block calls the unrank procedure; `Describes` gains the
clauses `cap a b = cw(e_ab, s_ab) + 2 s_ab` and `len a = Σ_b cap a b + nh a`. The poly-time proofs
(`memF_polyT`, …) extend with `unrank_polyT`.

**`TableProc.lean` (C1c: the table procedure for W_a).** `tableStream_eq` (streamed sum =
σ·χ·I) is semantic and stays. `tableMachine_runs` bounds the steps by 2·8^{μ_a} with linear state;
this is route μ and already suffices for Theorem B (3μ ≤ 3.45μ). For Theorem A the enumeration of
x must be the degree-pruned one of Prop. 3.2(iii) (per-vertex ≤ 2-subsets, `digR`-style mixed-radix
digits, consistency check), with a new cost lemma `tableMachine_runs_degree : steps ≤
Δ^{2ν_a}·20^{ν_a}·poly`, keeping the poly-size state.

**`Preprocess.lean`.** Lemma 6.1 (`card_hamCycles_eq_sum_reduced`, `card_choices_le`) and Lemma 6.2
(`blob_degree_sum_le`) stay for Theorem B, with Θ := ⌈n^{0.6}⌉ instead of n/g + 2 (`thetaW`). Add
`vertexBalanced g : Fin n → Fin g` with `card_fiber_le : ν_a ≤ ⌈n/g⌉` (Lemma 4.1), the finset of
profiles bounded by e_ab with `card_profiles_le` (Lemma 3.3) and a poly-time mixed-radix
enumeration of it (as `digitW`/`nBr` do for the branches in `Assembly.lean`).

**`Package.lean`, `UPackage.lean`, `Assembly.lean`, `Theorem2.lean` (the packages and the outer
machine).** The package interface carries `PW = 3μ + g² + 1`, `BW = 2μ + 1` and the per-pair
widths; these become functions of (n, Δ, g) — in ℕ use `2ν·(Nat.clog 2 Δ + 3) + g + g²`, which
dominates ⌈2ν log(2eΔ)⌉ + g + g². The outer machine `bodyM2`/`mainM2` sums over the profile index
with `sumRange` (as it now sums over `nBr` branches), and over branches too for Theorem B. The
exponent arithmetic of `Theorem2.lean` (currently C(m+n)/√log(n+2)) is redone for
C·n·(log Δ + 3)/√log(n+2) along §4.1; Case 1 of Theorem B additionally needs a 2^n·poly exact #HC
machine (subset DP), which does not exist in the development yet — brute force over orderings is
2^{Θ(n log n)} and is not enough there.

Order of work: `Unrank.lean` → `PairCode` in `LabelNetwork.lean` → `HCNetwork.lean` (Theorem 2.5 and
Prop. 3.2) → `LabelProcs.lean` → `Preprocess.lean` additions → packages. The mathematical layer and
the imports do not move; the bulk is the per-pair encoding and its procedures.

---------------------------------------------------------------------------------------------------

## 8. What is proved, what is assumed, what is open

**Proved here (paper level):** the network N_s (Definition 2.2), its encoding and factorisation
(Lemmas 2.3, 2.4), its value and the vanishing of inadmissible profiles (Theorem 2.5), its
parameters including the two per-node routes and the total U ≤ 2n log(2e d̄) + g³ (Prop. 3.2), the
profile count (Lemma 3.3), the vertex-balanced partition (Lemma 4.1), and the derivations of
Theorems A, B and Corollary C from the imported statements. Reused from [HC] by reference:
§§2–4 (Theorem 4.6), Lemmas 6.1 and 6.2, and the parameter choices of §6.4.

**Assumed:** exactly the three statements of [A] listed in (H_A) ([HC] §1, §9). Nothing new is
imported. The rank-encoding device itself is proved here from scratch (Lemma 2.3, Prop. 3.2); [A]
is credited for the idea.

**Numerically verified:** §6 (three runs, PASS).

**Not formalised:** the Lean development proves the [HC] theorems, not these; §7 is the plan.

**Open.** (1) The exponent is still e_ℓ·U with e_ℓ = Θ(1/√log n); the leading term is now
2e_ℓ n log(2eΔ), so better pieces in [A] transfer verbatim, and ρ → ½ would give
2^{O(n log Δ/log n)}. (2) Dense graphs: U ≈ 2n log n bits is the information content of a Hamiltonian
cycle, so within Definition 2 of [A] the dense case cannot go below 2^{Ω(e_K n log n)}, which is above
2^n unless e_K = o(1/log K) (`permanent/anthropic-m-independence.md` §4(b)). (3) The same rank
encoding applies to the TSP/weighted and directed extensions of [HC] (`exact-extensions.md`,
`tsp-theorem.md`), where the labels are still per crossing edge; the accounting is identical.
