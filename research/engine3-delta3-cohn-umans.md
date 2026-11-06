# Engine 3, Δ_3: does Cohn–Umans group-theoretic matrix multiplication give a trade?

6 Nov 2026. Setting and criterion: `engine3-open-door.md` §1.6–1.7 (D1 network cost, piece types, ν_3 = 3/2), §3.2–3.2a
(Δ_3, the known negatives); `engine3-delta3.md`, `engine3-delta3b.md`. Sources read for this note: Cohn–Umans, *A
group-theoretic approach to fast matrix multiplication*, FOCS 2003, arXiv math/0307321 (local text
`scratchpad/cu/cu03.txt`); Cohn–Kleinberg–Szegedy–Umans, *Group-theoretic algorithms for matrix multiplication*, FOCS 2005,
arXiv math/0511460 (`scratchpad/cu/cksu05.txt`); Hedtke–Murthy, *Search and test algorithms for triple product property
triples*, Groups Complexity Cryptology 2012, arXiv 1104.5097 (`scratchpad/cu/hm12.txt`). Scripts and outputs:
`research/scripts/engine3-cu/` (`fourier_pieces.py/.out`, `blocks_C.py/.out`, `cu_numbers.py/.out`, `tpp_check.py/.out`).
Tags: **[R]** proved here, **[K]** known (source named), **[N]** exact or numerical computation (script named), **[C]**
heuristic/conjecture.

## 0. Verdict

* **The group-algebra route is a one-sided construction, and its only two-sided form is provably at ρ_Δ = 1 (no trade).**
  A Cohn–Umans embedding of f_Δ = ⟨N³,N³,N³⟩ (its row reading) into ℂ[G] = ⊕_ρ M_{d_ρ}(ℂ) decomposes f_Δ into Fourier
  pieces A_ρ, each a **row** network with bonds (d_ρ, d_ρ, d_ρ) — exactly a restriction of ⟨d_ρ,d_ρ,d_ρ⟩ to the three rows
  [R, §3]. It says nothing about the column cost of A_ρ. The one case in which the same pieces are also column networks is
  the product case G = G_0 × G_1 × G_2, one triple-product-property triple per triangle (CU03 Lemma 2.2, CKSU Lemma 1.5):
  then every piece is a tensor network on the nine edges of Δ_3 itself ("edge-local"), equally cheap under rows and
  columns. **Theorem A [R, §4.1]: any identity f_Δ = Σ_{i∈I} A_i whose pieces are products over the three triangles has
  max_i (c_row + c_col)(A_i) ≥ 18λ − 9 log₂|I|.** With poly(λ) pieces this is the raw cost under both merges: no trade at
  all, not even ρ_Δ < 1. The proof is the core-floor mechanism (uniform CVZ functional) with every node its own party,
  which the product structure makes available although rows and columns have a trivial join on Δ_3. This is the first
  piece class on Δ_3 proved to sit at ρ = 1, i.e. exactly where the hyperedge rectangle-content conjecture predicts, far
  above the flattening floor 4/9 and the rank floor 1/2.
* **Non-product groups give no column network, and the construction's own accounting is at raw anyway [R, §4.3].**
  For any TPP realisation of ⟨N³,N³,N³⟩ in any G: |G| ≥ N⁶ (CU03 Lemma 3.1), so Σ_ρ d_ρ ≥ max(d_max, |G|/d_max) ≥ N³, and
  grouping the irreps into T blocks leaves a block with bond D(B) = Σ_{ρ∈B} d_ρ ≥ N³/T: its constructed row network costs
  ≥ 9λ − 3 log₂T = raw. Fixed-alphabet form: k(G) ≥ |G|/d_max², so the naming charge (3/2)log₂k(G) plus the row cost of
  the heaviest type is ≥ 9λ. The reason is structural: **the network cost of a direct sum is the logarithm of the sum of
  the bond dimensions**, so Schönhage's asymptotic sum inequality — the mechanism that makes CKSU work for ω — has no
  analogue once the number of pieces must be poly(λ). The simultaneous triple product property (CKSU Def. 5.1, Thm 5.3)
  realises direct sums; here a direct sum is a *block* of pieces, and CKSU Thm 7.1 (STPP in H ⟺ TPP in H ≀ Sym_n) adds
  nothing: Δ_3 is a tensor product of three ⟨N,N,N⟩'s, not a direct sum.
* **Computation at N₀ = 2 [N, `fourier_pieces.out`, `blocks_C.out`].** (i) S_3³ (one TPP ⟨2,2,2⟩ per triangle): the 27
  product pieces have (c_row, c_col) cut bounds exactly (3m, 3m), m = number of 2-dim factors, equal to the network
  bound; the piece (std,std,std) has all ranks full, 9 + 9 = 18 = raw. Every non-product grouping B_m has true costs
  ≥ (4.5, 4.5), (7.5, 7.5), (8.71, 8.71), (9, 9) with construction bounds 3 log₂D(B) = 9, 13.75, 13.75, 9 — the direct
  sum is *more* expensive than its parts. (ii) The CKSU §2 group G = (Cyc_3³)² ⋊ Cyc_2 (|G| = 1458, degrees ≤ 2) realising
  ⟨12,12,12⟩ ⊇ ⟨8,8,8⟩ under rows, 405 Fourier pieces, Σ_ρ A_ρ = f_Δ exactly: the 351 degree-2 pieces are row networks
  of cost 3 (row ranks 4, 4, 4) and, with the coordinatewise identification [N]³ → S, have column ranks 4 or 16, column
  cut bound 5–6 (not generic: random row-(2,2,2) networks have column ranks 64, `engine3-delta3b.md` §2); with random
  identifications the column ranks are generic (64 in 73–96% of the flattenings). Every grouping of the 405 pieces into
  2, 4 or 8 blocks (by degree, by a character coordinate, random) has blocks with ranks 64/64/64 under rows and columns:
  c_row + c_col ≥ 17.7–18 = raw, and the finite criterion value is 10.5–12.5 against 9.
* **Where the route escapes rank, and where it lands [R, §6].** A Fourier block ⟨d,d,d⟩ kept as a network costs 3 log₂d,
  against (3/2)log₂R(⟨d,d,d⟩) ≥ 3 log₂d for its rank-one terms (equality would need R = d², i.e. ω = 2): network pieces
  do escape the rank/flattening floor of Zhou (asymptotic rank of GT(K_n) = 2^{⌊n²/4⌋}, e = 1/2), by the factor ω/2 in
  the exponent, and this is the same escape that Anthropic's recursion makes (a ⟨d,d,d⟩ block handled at exponent e costs
  d^{3e}, beating d^ω iff e < ω/3). But the escape is one-sided; two-sidedness is the whole problem on Δ_3, and the group
  route provides it only in the product form, which Theorem A puts at ρ = 1.
* **Modified versions [R + C, §5].** "Fourier transform as the merge" has no content: a Fourier transform on ℂ[G] is a
  row-local change of basis, which preserves c_row and is simply part of the piece. "Three alignments ↔ three subgroups or
  coset structures": the group word of a triangle is the same under every merge; a merge only decides which node elements
  are multiplied into one party element, and party elements exist in both readings iff the node elements lie in
  independent factors — the product case. A "doubly Fourier" piece (a restriction of ⟨d,d,d⟩ under rows and of ⟨d′,d′,d′⟩
  under columns with dd′ < N³) is exactly the general open problem of §3.2a with nothing group-theoretic attached.
  Abelian groups give the trivial N⁹-term rank-one decomposition. Degenerations do not change any bound (§5.3 there).
* **What stays open:** everything that was open in `engine3-open-door.md` §3.2a; the route adds one closed class (product
  pieces, Theorem A) and one structural insight (direct sums are the wrong operation for network pieces).

---------------------------------------------------------------------------------------------------

## 1. f_Δ as a bilinear object, in both readings [R]

**Index-array form.** Write the strings of Δ_3 as an array x_{ℓ,s} ∈ [N], (ℓ, s) ∈ Z_3², ℓ = row of the node, s = triangle
(s = r + c). Node (ℓ, s) = grid node (r, c) = (ℓ, s − ℓ) holds the vertical domino (x_{ℓ,s}, x_{ℓ+1,s}), and

  f_Δ = Σ_{x ∈ [N]^{Z_3²}} ⊗_{(ℓ,s)} e_{x_{ℓ,s}} ⊗ e_{x_{ℓ+1,s}}   (the 9 equalities: slot 1 of (ℓ,s) = slot 0 of (ℓ+1,s)).

Row ℓ holds the array rows X_ℓ = (x_{ℓ,0}, x_{ℓ,1}, x_{ℓ,2}) and X_{ℓ+1}; column c = {(ℓ, ℓ+c)} holds the array diagonals
D_c = (x_{ℓ,ℓ+c})_ℓ and D_{c−1}. Hence

  rows:     f_Δ = Σ_{X_0,X_1,X_2 ∈ [N]³} e_{X_0X_1} ⊗ e_{X_1X_2} ⊗ e_{X_2X_0} = ⟨N³,N³,N³⟩,
  columns:  f_Δ = Σ_{D_0,D_1,D_2 ∈ [N]³} e_{D_2D_0} ⊗ e_{D_0D_1} ⊗ e_{D_1D_2} = ⟨N³,N³,N³⟩,

the matrix multiplication tensor of N³ × N³ matrices read along the rows of the index array, and the same tensor read along
its diagonals. Each row and each column of the grid meets each triangle in exactly one node (the three alignments: under
rows, party r of every triangle is row r; under columns, party r of triangle s is column s − r, three different
reflections). The row-pair bond (ℓ, ℓ+1) carries X_{ℓ+1}, one string of each triangle; the column-pair bond (c, c+1)
carries D_c, one string of each triangle.

**Lemma 1.1 (D1 cost = matrix-multiplication-restriction cost) [R].** A triangle network on three groups with bonds
(d_01, d_12, d_20) and node tensors g_0, g_1, g_2 is Σ_θ g_0(ℓ_0; θ_01, θ_20) g_1(ℓ_1; θ_01, θ_12) g_2(ℓ_2; θ_12, θ_20) =
(g_0 ⊗ g_1 ⊗ g_2)(Σ_θ e_{θ_20 θ_01} ⊗ e_{θ_01 θ_12} ⊗ e_{θ_12 θ_20}) = (g_0 ⊗ g_1 ⊗ g_2)⟨d_20, d_01, d_12⟩, the matrix
multiplication tensor with group-local linear maps applied; conversely every such restriction is a network with those
bonds. Hence

  c_k(A) = min { log₂(abc) : A ≤_k ⟨a,b,c⟩ },  ≤_k = restriction with respect to the three groups of merge k.

The cut bound of §1.6 reads: rk(A; G_i | rest) ≤ product of the two bonds at G_i, so c_k(A) ≥ ½ Σ_i log₂ rk_i(A) and
c_k(A) ≥ max_S log₂ rk_S(A). For f_Δ: ranks N⁶ on every row and every column, c_row = c_col = 9λ (raw), and the
criterion of §1.7 is: poly(λ) pieces A_i with Σ A_i = f_Δ, each a restriction of ⟨a_i,b_i,c_i⟩ under rows and of
⟨a_i′,b_i′,c_i′⟩ under columns with log₂(a_ib_ic_i a_i′b_i′c_i′) < 18λ − o(λ) (any trade), < 9λ − o(λ) (ρ_Δ < 1/2).

Cohn–Umans' Theorem 2.3 (CU03) states precisely a restriction of this kind: "if G realizes ⟨n,m,p⟩ then ⟨n,m,p⟩_F ≤ F[G]",
with ≤ the restriction relation of Bürgisser–Clausen–Shokrollahi §14.3. So **a Cohn–Umans embedding is, by definition, a
row network of f_Δ**, and the question of this note is what it does under columns.

## 2. What Cohn–Umans and CKSU state, exactly [K]

* **TPP (CU03 Def. 2.1 = CKSU Def. 1.3).** G realizes ⟨n_1,n_2,n_3⟩ if there are S_1, S_2, S_3 ⊆ G, |S_i| = n_i, such that
  for q_i ∈ Q(S_i) = {s s′^{-1} : s, s′ ∈ S_i}, q_1q_2q_3 = 1 implies q_1 = q_2 = q_3 = 1. For subgroups: h_1h_2h_3 = 1 ⟹
  all trivial. Symmetric in the three sets (CU03 Lemma 2.1); products: if N ⊲ G realizes ⟨n_i⟩ and G/N realizes ⟨m_i⟩
  then G realizes ⟨n_im_i⟩ (Lemma 2.2), in particular G_1 × G_2 realizes ⟨n_1n_2, m_1m_2, p_1p_2⟩ (CKSU Lemma 1.5).
* **Embedding (CU03 Thm 2.3).** A ↦ Σ_{s,t} A_{st} s^{-1}t, B ↦ Σ_{t′,u} B_{t′u} t′^{-1}u; the coefficient of s^{-1}u in
  the product is (AB)_{su} because (s^{-1}t)(t′^{-1}u) = s′^{-1}u′ iff s = s′, t = t′, u = u′. Hence ⟨n,m,p⟩ ≤ ℂ[G] ≅
  ⊕_ρ ⟨d_ρ,d_ρ,d_ρ⟩ (Wedderburn; Σ_ρ d_ρ² = |G|).
* **Size (CU03 Lemma 3.1).** (x, y) ↦ x^{-1}y is injective on S_1 × S_2, so |G| ≥ n_1n_2, with equality only if n_3 = 1;
  pseudo-exponent α(G) = min 3 log|G|/log(nmp) > 2 for every finite group; **abelian G forces |G| ≥ n_1n_2n_3** (α = 3).
* **Exponent bound (CU03 Thm 4.1 = CKSU Thm 1.8).** If G realizes ⟨n,m,p⟩ with character degrees {d_i} then (nmp)^{ω/3}
  ≤ Σ_i d_i^ω; nontrivial iff nmp > Σ d_i³ (CU03 Question 4.1, answered by CKSU §2). Proof: ⟨n,m,p⟩ ≤ ⊕⟨d_i,d_i,d_i⟩,
  tensor powers, R(⟨k,k,k⟩) ≤ Ck^{ω+ε}, (n′m′p′)^{ω/3} ≤ R(⟨n′,m′,p′⟩).
* **Smallest examples.** CU03 §3: S_3 realizes ⟨2,2,2⟩ through its three subgroups of order 2, pseudo-exponent log₂6;
  Sym(Δ_n) with Δ_n the triangular array of n(n+1)/2 points and H_i the subgroup fixing the i-th barycentric
  coordinate realizes ⟨1!2!⋯n!⟩³ (CU03 Thm 3.3, CKSU Thm 1.7). CKSU §2: H = Cyc_n³, G = H² ⋊ Cyc_2 (z swaps the factors),
  S_i = {(a,b)z^j : a ∈ H_i∖{0}, b ∈ H_{i+1}, j ∈ {0,1}}, |S_i| = 2n(n−1), |G| = 2n⁶, degrees ≤ 2, Σd³ ≤ 4n⁶ < 8n³(n−1)³
  for n ≥ 5, ω < 2.9088 at n = 17 (the first group beating the sum of cubes). Hedtke–Murthy Table 1 (all nonabelian
  groups of order < 25): β(G) = max nmp ranges from |G| to 1.6|G| (C_5 ⋊ C_4 of order 20 realizing ⟨4,4,2⟩); Table 2:
  β_g/|G| = 2 for D_8² (order 64, ⟨8,4,4⟩) and several groups of order 128; SL_3(F_2) realizes ⟨8,7,7⟩.
* **STPP (CKSU Def. 5.1).** n triples A_i, B_i, C_i ⊆ H satisfy the simultaneous triple product property if each triple
  has the TPP and a_i(a_j′)^{-1} b_j(b_k′)^{-1} c_k(c_i′)^{-1} = 1 implies i = j = k. Then (Thm 5.3) the n **independent**
  products A_iB_i are read off one multiplication in ℂ[H] (coefficients of s^{-1}u with s ∈ A_i, u ∈ C_i); (Thm 5.5)
  Σ_i (a_ib_ic_i)^{ω/3} ≤ Σ_k d_k^ω via Schönhage's asymptotic sum inequality; (Thm 7.1) the STPP in H is a TPP in
  Sym_n ⋉ Hⁿ through H_1 = {hπ : h_i ∈ A_i}, etc., and (§7) "any bound provable via the simultaneous triple product
  property can in fact be proved using only the approach of [2]". Examples: Prop. 5.2 (H = Cyc_n³, two triples, ω < 2.93),
  Thm 6.2 (local strong USPs in Cyc_ℓ^k, ω < 2.48), Thm 6.6 (H-charts, local USPs: ω < 2.41; a 24-symbol chart recovers
  Coppersmith–Winograd 2.376). Every construction is "a semidirect product of a permutation group with an abelian
  group" (CKSU §5 opening).

The direct-sum structure of the STPP is the right object for *blocks* of pieces (§3.3 below) and the wrong object for
Δ_3 itself, which is ⟨N,N,N⟩^{⊗3} = ⟨N³,N³,N³⟩ (a Kronecker product) under rows and again under columns.

## 3. f_Δ over a group algebra: the Fourier pieces [R]

### 3.1 Row embedding and the explicit pieces

Let G realize ⟨N³,N³,N³⟩ through S, T, U with bijections σ: [N]³ → S, τ: [N]³ → T, υ: [N]³ → U. Embed row 0 by
e_{X_0X_1} ↦ σ(X_0)^{-1}τ(X_1), row 1 by e_{X_1′X_2} ↦ τ(X_1′)^{-1}υ(X_2), row 2 by e_{X_2′X_0′} ↦ υ(X_2′)^{-1}σ(X_0′).
The group algebra multiplication tensor, as a trilinear form, is M_G(a,b,c) = Σ_{ghk=1} a_gb_hc_k = (1/|G|)Σ_ρ d_ρ
Tr(ρ(a)ρ(b)ρ(c)), since (1/|G|)Σ_ρ d_ρχ_ρ(x) = [x = 1]. Define

  A_ρ(X_0,X_1; X_1′,X_2; X_2′,X_0′) := (d_ρ/|G|) · χ_ρ( σ(X_0)^{-1}τ(X_1) · τ(X_1′)^{-1}υ(X_2) · υ(X_2′)^{-1}σ(X_0′) ).

**Lemma 3.1.** Σ_ρ A_ρ = [word = 1] = [X_0 = X_0′][X_1 = X_1′][X_2 = X_2′] = f_Δ (the TPP, after conjugating the word to
(τ(X_1)τ(X_1′)^{-1})(υ(X_2)υ(X_2′)^{-1})(σ(X_0′)σ(X_0)^{-1})), and A_ρ is a row network with bonds (d_ρ, d_ρ, d_ρ):
χ_ρ(ghk) = Σ_{αβγ} ρ(g)_{αβ}ρ(h)_{βγ}ρ(k)_{γα} with node tensors ρ(σ(X_0)^{-1}τ(X_1))_{αβ} etc. So c_row(A_ρ) ≤ 3 log₂d_ρ,
and rk(A_ρ; row r | rest) ≤ d_ρ². A_ρ is (π_0 ⊗ π_1 ⊗ π_2)⟨d_ρ,d_ρ,d_ρ⟩ with π_r the row-r embedding composed with the
ρ-block of the Fourier transform: the restriction of Lemma 1.1. ∎

Checked exactly at N = 2 [N, `fourier_pieces.out`]: for S_3 on one triangle the three pieces sum to ⟨2,2,2⟩; for S_3³ the
27 product pieces sum to f_Δ; for the CKSU §2 group with n = 3 the 405 pieces sum to f_Δ for every identification tried
(`tpp_check.out` verifies the TPP of the 8- and 12-subsets with right quotient sets).

### 3.2 Blocks

Pieces must be poly(λ) in number, and k(G) (the number of irreps) is not (§4.3), so the irreps are grouped into blocks B
and the pieces are A_B = Σ_{ρ∈B} A_ρ. A_B is the restriction of the block ⊕_{ρ∈B}⟨d_ρ,d_ρ,d_ρ⟩ of M_G, which is a row
network with block-diagonal bonds D(B) := Σ_{ρ∈B} d_ρ (the block label travels on every bond): c_row(A_B) ≤ 3 log₂D(B).
Before restriction the block has row ranks w(B) := Σ_{ρ∈B} d_ρ² (its dimension), so its own D1 cost is between
(3/2)log₂w(B) (cut bound) and 3 log₂D(B); after restriction the ranks can only drop. Note (Σ d_ρ)² ≥ Σ d_ρ² ≥ Σ d_ρ.

### 3.3 Where the STPP lives

A block is "several independent matrix multiplications realised as one network": exactly the object of CKSU Thm 5.3. So
the STPP describes the pieces after grouping, and its cost law is the one that matters: **as a network, a direct sum
⊕_{ρ∈B}⟨d_ρ,d_ρ,d_ρ⟩ costs 3 log₂Σ_B d_ρ, not log of a sum of powers.** In the exponent world the direct sum costs
Σ_B R(⟨d_ρ,d_ρ,d_ρ⟩) ≈ Σ_B d_ρ^ω (sub-additivity of rank, Schönhage), and CKSU's Lemma 1.1 / Thm 5.5 turn many small blocks
into a bound on ω. In the piece world the same many small blocks must be merged into poly(λ) networks whose bonds add
up. This is the whole difference, and §4.3 quantifies it.

### 3.4 The product case is the "one TPP per triangle" case

If G = G_0 × G_1 × G_2 with S = Π_s S_s etc. and σ, τ, υ coordinatewise, then ρ = ρ_0 ⊗ ρ_1 ⊗ ρ_2, χ_ρ factors, the word
factors into three triangle words, and A_ρ = ⊗_s A^{(s)}_{ρ_s}, with A^{(s)}_{ρ_s} the Fourier piece of triangle s for the
TPP ⟨N,N,N⟩ in G_s. A^{(s)}_{ρ_s} is a triangle network on the three *nodes* of T_s with bonds d_{ρ_s}. Hence A_ρ is a
tensor network on the graph Δ_3 itself (bond d_{ρ_s} on every edge of triangle s): **edge-local**. Since every row pair
and every column pair receives exactly one edge of each triangle, an edge-local network with bonds d_e is simultaneously
a row network and a column network with the same bond products: c_row(A_ρ), c_col(A_ρ) ≤ Σ_e log₂d_e = 3 Σ_s log₂d_{ρ_s}.
These are the only pieces the group route makes cheap in both directions.

## 4. The column side

### 4.1 Product pieces: no trade at all [R]

**Theorem A.** Let f_Δ = Σ_{i∈I} A_i with every piece a product over the three triangles, A_i = ⊗_s X_i^{(s)}, X_i^{(s)}
an arbitrary tensor on the three nodes of T_s. Then

  max_{i∈I} ( c_row(A_i) + c_col(A_i) ) ≥ 18λ − 9 log₂|I|.

*Proof.* (i) Flattening ranks multiply over tensor factors on disjoint parties, and each row and each column meets each
triangle in one node, so rk(A_i; R_r | rest) = Π_s rk_{(r,s−r)}(X_i^{(s)}) and rk(A_i; C_c | rest) = Π_s rk_{(s−c,c)}(X_i^{(s)}).
By the cut bound c_k ≥ ½Σ_groups log₂rk, c_row(A_i) + c_col(A_i) ≥ ½Σ_r log₂rk_{R_r} + ½Σ_c log₂rk_{C_c} = Σ_v log₂rk_v(A_i),
the sum over all nine nodes (each node lies in one row and one column). (ii) Let F be the uniform quantum functional
(CVZ) on the nine nodes as parties, θ_v = 1/9. F(f_Δ) = N^{Σ_e(θ_u+θ_v)} = N² (f_Δ is a product of nine EPR pairs of
dimension N between distinct parties; every node marginal of f_Δ is uniform of rank N², so E^θ ≥ 9·(1/9)·2 log N, and the
rank bound below gives ≤). For any tensor, F(A) ≤ Π_v rk_v(A)^{θ_v} (local ranks are GL-invariant and lower
semicontinuous, so every marginal spectrum in the moment polytope has support ≤ rk_v and entropy ≤ log rk_v). Hence
F(A_i) ≤ 2^{(1/9)Σ_v log₂rk_v(A_i)} ≤ 2^{(c_row+c_col)(A_i)/9}. (iii) Subadditivity: N² = F(f_Δ) ≤ Σ_i F(A_i) ≤
|I| · 2^{max_i(c_row+c_col)/9}. ∎

Remarks. (a) This is Theorem 2.3 of `engine3-open-door.md` (the core floor) with H = all nine nodes and the *discrete*
partition in place of the join of rows and columns: on Δ_3 the join is trivial (the incidence graph of rows and columns
is connected), which is why the core floor gives only 1/3 for general pieces; the product structure supplies the
missing "every node is its own group", because for product pieces the row and column flattening ranks are products of
node ranks. (b) Node-local maps change nothing, and X_i^{(s)} is arbitrary (sums, degenerations, anything on the
triangle), so the theorem covers every "one group per triangle" Fourier family, every product grouping of it, every
Strassen-type decomposition tensored over triangles, and every ansatz of the form "cheap network on T_0 ⊗ cheap network
on T_1 ⊗ cheap network on T_2". (c) It is the first class of pieces on Δ_3 with a proved value **ρ = 1**; the general
floors are 4/9 (flattenings) and 1/3 (core), and the rank-one class is at 1 by the §1.7 counting. (d) At N₀ = 2 the
theorem is visible exactly [N]: the piece (std, std, std) of S_3³ has all nine node ranks 4 = N², all row and column
ranks 64, c_row = c_col = 9. (e) The rank bound in (ii) needs only the flattening ranks, but the step from "some piece
has a large product of node ranks" to a single piece is exactly what the functional buys; a pure pigeonhole gives only
6λ (the maximum cut of three disjoint triangles has six edges), which is why the general flattening floor is 4/9.

### 4.2 Non-product groups: no column network is provided, and the pieces are column-expensive [N]

For a non-product G the word σ(X_0)^{-1}τ(X_1)⋯ does not split into node elements, and the column reading has no group
element at all: the construction produces a row network and no column network. What the column flattenings of a
row-Fourier piece look like was computed at N = 2 for the CKSU §2 group G = (Cyc_3³)² ⋊ Cyc_2 (|G| = 1458; 54 characters
of degree 1, 351 irreps of degree 2; S_i = {(a,b)z^j : a ∈ H_i∖{0}, b ∈ H_{i+1}, j}, 8-subsets a ∈ {1,2}, b ∈ {0,1})
[N, `fourier_pieces.out`]:

| identification [N]³ → S,T,U | degree-1 pieces: column ranks | degree-2 pieces (row ranks 4,4,4; c_row ≤ 3): column ranks (1053 flattenings) | c_col cut bound |
|---|---|---|---|
| coordinatewise (a−1, b, j) ↔ (i_0,i_1,i_2) | all 1 (products) | 4 (81), 16 (972) | 5.00–6.00 |
| random #0 | 1…64, 98 of 162 at 64 | 16 (3) … 64 (964) | 6.73–9.00 |
| random #1 | 1…64, 70 at 64 | 32 (18) … 64 (1011) | 7.50–9.00 |
| random #2 | 1…64, 24 at 64 | 16 (3) … 64 (764) | 6.72–9.00 |

The coordinatewise identification is special: its degree-2 pieces are row-(2,2,2) networks with column cut bound 5–6,
below the generic 9 of a random row-(2,2,2) network (`engine3-delta3b.md` §2, `generic_ranks.py`); they lie on the proper
subvariety where a trade would have to live, but they are 405 in number. Generic identifications give generic (full)
column ranks. Control: f_Δ under random invertible row-local maps has column ranks 64.

### 4.3 The heaviest block: the construction's own accounting is at raw [R + N]

**Proposition 4.3.** Let G realize ⟨N³,N³,N³⟩ and let Irr(G) be partitioned into T blocks (or, more generally, let the
pieces be linear combinations Σ_ρ c_{iρ}A_ρ with Σ_i c_{iρ} = 1). Then some block has D(B) ≥ N³/T, so its constructed row
network costs 3 log₂D(B) ≥ 9λ − 3 log₂T.
*Proof.* |G| ≥ |S||T| = N⁶ (CU03 Lemma 3.1); Σ_ρ d_ρ ≥ Σ_ρ d_ρ²/d_max = |G|/d_max and Σ_ρ d_ρ ≥ d_max, so Σ_ρ d_ρ ≥ N³;
the blocks cover Irr(G). ∎

Fixed-alphabet form (§1.7 with the irreps as types): k(G) ≥ |G|/d_max² ≥ N⁶/d_max², so the naming charge satisfies
(3/2)log₂k(G) + 3 log₂d_max ≥ 9λ: the heaviest type's row cost plus the charge for naming the types is already raw. The
exact value is V = (game value) + (3/2)log₂k(G) ≥ (game value) + 9λ − 3 log₂d_max, and the adversary may put all weight
on the heaviest type, so the game value is ≥ min(c_row, c_col) of that type; a trade (V < 9λ) therefore needs
min(c_row, c_col)(A_{ρ_max}) < 3 log₂d_max — the heaviest Fourier type must be strictly cheaper, under one of the merges,
than the row network the construction gives it. Numbers [N, `cu_numbers.out`]: S_3³ (N = 2):
k = 27, (3/2)log₂k + 3 log₂d_max = 7.13 + 9 = 16.1 against 9; the CKSU §2 group: 12.99 + 3 = 16.0; S_6 (Sym(Δ_3),
realizing ⟨12,12,12⟩ ⊇ ⟨8,8,8⟩, d_max = 16 > 8): 5.19 + 12 = 17.2. For the product route (one TPP ⟨N,N,N⟩ per triangle,
blocks B ⊆ Irr(G)³, c_row = c_col ≤ 3 log₂D(B)): Σ_B D(B) = (Σ_ρ d_ρ)³, which is N^{8.0} for the CKSU §2 family
(N = 2n(n−1), Σd = n⁶ + n³), N^{7.9–8.1} for n = 5…17, N^{5.2}, N^{4.9}, N^{4.6} for Sym(Δ_n) = S_6, S_10, S_15; a trade
needs every D(B) < N³ and ρ < 1/2 every D(B) < N^{3/2}, so the number of blocks would have to be ≥ N⁵ (resp. N^{1.6–2.2}) —
polynomial in N, not in λ. The true costs behave the same way at N = 2 [N, `blocks_C.out`]: every grouping of the 405
pieces of the CKSU §2 family into 2, 4 or 8 blocks (by degree; degree-1 block plus degree-2 irreps split by a character
coordinate; random) has blocks with ranks 64/64/64 under rows and 60–64 under columns, c_row + c_col ≥ 17.7–18, and the
finite criterion value (c_row + c_col)/2 + (3/2)log₂T is 10.5, 11.85, 12.0, 13.5 against 9; the degree-1 block (54
rank-one pieces) alone has ranks 24/24/24 and 18/18/18 (costs ≥ 6.9 and 6.25). For S_3³ the non-product blocks B_m have
true costs (4.5, 4.5), (7.5, 7.5), (8.71, 8.71), (9, 9) and construction bounds 9, 13.75, 13.75, 9: grouping makes the
network *worse* than its parts, as 3 log₂Σd must.

Why the ω-mechanism does not transfer, in one line: CKSU need Σ_ρ d_ρ^ω ≪ (N³)^ω with many ρ; a network needs Σ_B d_ρ ≪ N³
for every block with few blocks; the first is sub-additivity of rank over a direct sum, the second is additivity of
bond dimension over a direct sum, and poly(λ) blocks cannot bridge Σ_ρ d_ρ ≥ N³.

### 4.4 Which flattening blows up

Under rows nothing blows up: every A_ρ has row ranks ≤ d_ρ². Under columns, for non-product G the column-group
flattenings of A_ρ are generically full (64 of 64 at N = 2, §4.2), and even for the special coordinatewise identification
they are 4–16 against the row ranks 4; after grouping into few blocks both row and column ranks are full (§4.3). For
product G nothing blows up per piece — every piece is cheap both ways — and the identity dies on the *number* of pieces
through Theorem A: the node-rank functional forces one piece to carry all 18λ bits.

## 5. Modified versions, and what would be needed [R + C]

1. **Fourier transform as the merge.** A merge is a partition of the nodes; the Fourier transform on ℂ[G] is a change of
   basis on the row party ⊗_s V_{(r,s−r)}. Node-local changes of basis leave every rank invariant (`engine2-algebraic.md`
   M2 (ii)); a row-local change preserves c_row and changes c_col arbitrarily, i.e. it is part of the choice of piece, not
   of the merge. Nothing is gained by renaming it. [R]
2. **Three alignments ↔ three subgroups / coset structures.** The alignments live in which nodes a merge collects; a
   triangle's group word σ(x)^{-1}τ(y)·τ(y′)^{-1}υ(z)·υ(z′)^{-1}σ(x′) is the same cyclic word under every merge. A party
   element exists in the row reading because the three row-node elements of a triangle multiply in a fixed order; in the
   column reading the three nodes of a column come from three different triangles and would have to multiply in three
   different groups — which is what the product group does. For a non-product G there is no column party element, and
   choosing S, T, U as products of three subgroups or as unions of cosets (s_I = s_{i_0}s_{i_1}s_{i_2}) puts the node pairs
   of a column adjacent in the word only for one node per party, not for all three. [R] A G with three exact
   factorizations G = A_sB_sC_s could encode three *row-type* readings, but Δ_3 has one row reading and one column
   reading, and the column reading is not a reading of the same word. [C: no construction of this kind exists; none is
   excluded in principle, but it would have to be a "doubly Fourier" tensor, item 4.]
3. **Abelian and commutative algebras.** For abelian G the TPP forces |G| ≥ N⁹ (CU03 Lemma 3.1), all d_ρ = 1, and the
   Fourier pieces are the N⁹ rank-one product terms of f_Δ — the trivial decomposition, dead by §1.7 (grouping into
   poly(λ) pieces leaves full group ranks). Commutative semisimple algebras are the same statement. [K + R]
4. **Doubly Fourier pieces.** What a trade needs is a tensor A on the nine nodes with A ≤_rows ⟨a,b,c⟩ and A ≤_cols
   ⟨a′,b′,c′⟩, log₂(abca′b′c′) < 18λ (trade) or < 9λ (ρ < 1/2), in a poly(λ) family summing to f_Δ. The group route
   provides A ≤_rows ⟨d,d,d⟩ and, in the product case, A ≤_cols ⟨d,d,d⟩ with the same d; Theorem A then applies. A
   non-product "doubly Fourier" piece would be a row-Fourier block of one embedding that is also a column-Fourier block
   of another; no group-theoretic mechanism produces one, and the question is just §3.2a restated. It is not excluded
   that row-local maps collapse column ranks (the 2 × 2 example: SWAP on one row turns EPR(a,d)⊗EPR(b,c), column rank
   N², into EPR(a,c)⊗EPR(b,d), column rank 1), so the heaviest block A_{B} — which for S_3³ is a row-local image of f_Δ
   itself — is not a priori column-full; but the Fourier maps are not of that kind (§4.2), and the family as a whole
   is caught by Prop. 4.3 regardless. [C]
5. **Border / degeneration versions** (CKSU's use of the asymptotic sum inequality and border rank) change no bound:
   Theorem A uses CVZ functionals and flattening ranks, both monotone under degeneration (`engine3-open-door.md` §5.3).
6. **Hurwitz–Radon / Clifford, simultaneous version.** The eight-square identity is the two-sided (rows = one order,
   columns = the other order) decomposition of a *single* crossing (App. H). Its analogue on Δ_3 would be an identity
   whose terms are row networks plus column networks, and §3.2 of the open-door note states the exact finite target
   (R + C with bonds (2,2,2) is refuted at N₀ = 2, etc.). Group algebras of Q_8, S_3, S_4 as *rectangle* pieces (Open
   Problem 1) are a different target (`engine3-open-door.md` §5.2) and are not touched here.

## 6. Rank, flattening floor, and where the group route escapes it [R]

* Zhou (arXiv 2610.34273, Thm 1.1): log₂R̃(GT(K_n)) = ⌊n²/4⌋ exactly for even n, so rank-one methods on cliques are at e =
  1/2 per edge bit, the flattening floor (`engine3-literature.md` §1.6). Cohn–Umans/CKSU is a rank-type method (it bounds
  R via Σ d^ω); applied to the clique sum directly it inherits this cap.
* As pieces, Fourier blocks are **not** rank-one: a block ⟨d,d,d⟩ costs 3 log₂d as a network, against (3/2)log₂R(⟨d,d,d⟩)
  for its rank-one terms (hyperedge naming, ν_3 = 3/2); R(⟨d,d,d⟩) ≥ d² always and ≥ 3d² − o(d²) (Bläser), asymptotically
  d^ω, so the network is strictly cheaper, by the factor ω/2 in the exponent (d = 2: 3 vs 4.21 bits; d = 3: 4.75 vs 6.79;
  d = 4: 6 vs 8.42 [N, `cu_numbers.out`]). This is the escape from rank, and it is the same escape the recursion makes:
  handing a ⟨d,d,d⟩ block to the merged instance at exponent e costs d^{3e}, which beats fast matrix multiplication's d^ω
  iff e < ω/3 — the D2 reading "ρ_Δ ≤ ω/3" of `engine3-delta3.md` §0 in another guise.
* The escape is one-sided. On Δ_3 the raw f_Δ is already a (N³,N³,N³) network under rows (ρ = 1 on that side is free);
  the content of a trade is the *second* merge. Theorem A says the group route's two-sided form is at ρ = 1, above the
  rank floor 1/2 and the flattening floor 4/9: the hyperedge rectangle-content prediction (no trade on Δ_3) holds for
  it. Nothing in this note moves the proved general floor (4/9) or the upper bound (raw).

## 7. Computations [N]

| script | what | result |
|---|---|---|
| `fourier_pieces.py` | f_Δ at N = 2 (2¹⁸ entries); S_3 TPP ⟨2,2,2⟩ (three order-2 subgroups); 27 product Fourier pieces of S_3³; blocks B_m | Σ = f_Δ exactly; (c_row, c_col) cut bounds (0,0), (3,3), (6,6), (9,9) for m = 0..3 2-dim factors = network bounds; blocks: (4.5,4.5), (7.5,7.5), (8.71,8.71), (9,9) vs 3log₂D = 9, 13.75, 13.75, 9 |
| `fourier_pieces.py` | CKSU §2 group (Cyc_3³)² ⋊ Cyc_2, 405 Fourier pieces of ⟨8,8,8⟩ under rows, 4 identifications | Σ = f_Δ exactly each time; degree-2 pieces: row ranks 4 (c_row = 3), column cut bounds 5–6 (coordinatewise) / 6.7–9 (random, 73–96% of the column flattenings full) |
| `fourier_pieces.py` | control: f_Δ under random invertible row-local maps | column ranks 64/64/64 |
| `tpp_check.py` | TPP (right quotient sets) of the 8- and 12-subsets | True, True; control (S,S,S) False |
| `blocks_C.py` | groupings of the 405 pieces into T = 2, 4, 4, 8 blocks | all heavy blocks 64/64/64 rows, 60–64 cols; worst c_row + c_col ≥ 17.7–18; criterion value 10.5–13.5 vs 9 |
| `cu_numbers.py` | Σd, k(G), d_max for S_3, CKSU §2 (n = 3…17), Sym(Δ_n) = S_3, S_6, S_10, S_15 (hook lengths) | Σ_B D(B) = (Σd)³ = N^{4.6–8.1}; naming charge + heaviest row cost ≥ raw in every case |

The erroneous line "TPP of the three 8-subsets: False" of the first run of `fourier_pieces.py` came from a left-quotient
implementation of the TPP test; the function was corrected (right quotients, CU03 Def. 2.1) and the run repeated; the
piece sums, which prove the TPP directly, were unaffected.

## 8. Where this leaves Δ_3

1. Closed classes on Δ_3, with proved values: rank-one / Strassen-type (ρ = 1, §1.7 counting); **product pieces over the
   three triangles, hence every one-group-per-triangle Fourier family (ρ = 1, Theorem A)**; two- and three-piece
   identities at N₀ = 2 and the ρ < 1/2 criterion at N₀ = 2, 4 for every T (`engine3-delta3.md`, `engine3-delta3b.md`).
2. Group-algebra constructions with a single non-product group provide row networks only; their blocks are at raw by
   their own accounting (Prop. 4.3) and column-full in the computed example; a trade from them would need a column
   network found by other means for the heaviest block, at which point the group is irrelevant.
3. The finite problem is unchanged: §3.2a(a) (N₀ = 2, T = 4 types, any trade) and the N₀ ≥ 8 alphabets for ρ < 1/2. A
   useful by-product for the search side: the coordinatewise CKSU pieces are explicit row-(2,2,2) networks with column
   cut bound 5–6, i.e. explicit points on the subvariety where a T = 4 solution would have to lie; they can seed ALS.
4. For a proof of ρ_Δ ≥ 1/2 (Conjecture 8.1 type), Theorem A shows what the product structure buys (node-wise functional)
   and what the general case lacks (rows and columns have trivial join); the bond-triple information of §3.2a remains the
   only identified route.
