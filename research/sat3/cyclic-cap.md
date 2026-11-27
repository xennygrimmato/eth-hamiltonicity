# F_CAT on cyclic designs: Δ₃, the nets of Z_g, full planes

Theory and computation notes, 27 Nov 2026. Not committed, not machine-checked, not refereed. Sequel to
`q1-cyclic.md`; conventions of `notes.md` §2 and `q1-notes.md` §0–§1.

Tags: **[R]** proved here in full from the cited inputs; **[D]** derived here, proof written, unreviewed; **[N]**
numerical (script named; "exact" = exact rank computations over a finite field or Q); **[C]** conjecture or
heuristic; **[X]** dead, with reason.

Scripts (`cyc/`, outputs in `cyc/out/`):

| script | what it does |
|---|---|
| `filt_search.rs` | one-factor ratio Γ of Δ₃ (and X₄, for calibration) in Cone(building of GL_N(F₂)), hubs arbitrary points of the cone (complete flag with weights), legs exact for N ≤ 4 |
| `hyp_search.py` | Γ of Δ₃ in the hyperbolic plane |
| `polymatroid_lp.py`, `ansatz_lp.py`, `ansatz_lp_sym.py` | Shannon LP for the subspace ansatz (§3), plain and orbit-reduced |
| `z3_arrangement.py` | the arrangement (k,w,N) = (2,5,10) for Δ₃ over Q, exact |
| `atom_fw.py` | polymatroid relaxation of the ansatz with level shifts (one factor), local search |
| `cyclic_octa.py`, `cyclic_octa_coll.py`, `cyclic_octa_char2.py` | the octahedron arrangement for the net of Z_g: exact checks over F_q (q ≡ 1 mod g) and over F_{2^s} |
| `cyclic_octa_dist.py` | savings of sample edges of that placement computed from the definition of the filtration metric (no lemma used) |
| `cyclic_blocks.py`, `block_test.py`, `octa_test.py`, `octa_scan.py` | K_{2,2,1} blocks; exploratory scans |

Normalisation. Δ₃ in "hub coordinates": hubs A_i, B_j, C_k (i, j, k ∈ Z₃; three classes = the three merges);
nodes = triples (i,j,k) with i+j+k = 0 (hubs A_i, B_j, C_k); edges (i,j,k) — (i+1,j+1,k+1): three triangles
T₀, T₁, T₂. Equivalently the hubs are the points (u,v) of AG(2,3), classes = vertical lines, nodes = the nine
non-vertical lines, edges = pairs of parallel non-vertical lines. Two nodes that are not joined by an edge share
exactly one hub: **Δ₃ is the set of all non-collinear pairs of the Z₃ net.** Records: Σ_k b_k = 18 (trees, value
2/3, Γ = 36), cap 27/√2 (value 1/√2, Γ = 40.5), flat 9√3 (Γ = 27).

---

## 0. Results in brief

1. **Δ₃: no cap below 1/√2 and no placement above 2/3.** F_CAT(Δ₃) ∈ [2/3, 1/√2] stands.
2. **The tripod branch of the equality analysis is empty for every finite ρ [D].** `q1-cyclic.md` §3 left the
   intermediate arm lengths open. With the lune lemma in its distance form (Lemma 2.1, proved here) the configuration
   of step 6 there is contradictory for every φ₀ < π/2: the geodesic q₁–a–b–p₀ and the half circle q₁–q₂–p₀ span a
   lune, which forces d(b,q₂) = φ₀, while the structure needs π − φ₀. In two-merge form (Proposition 2.2): six points
   A_i, B_j with same-class distances 1, cross distances 2ρ, edge bimedians 1/√2 **and anti-diagonal bimedians 1/2** do
   not exist in any CAT(0) space. So an equality configuration must have ½ < κ ≤ 1/√2 (κ = the bimedian of two
   collinear nodes for the two classes they do not share), i.e. the three hub-pair midpoints of a node are distinct.
   That branch is open (§2.4). The compactness argument for strict inequality is valid only with two additions that
   are missing: boundedness of the cross-class hub distances along a maximising sequence, and the open branch (§2.5).
3. **Subspace ansatz: exact value √(2/5) = 0.6325 on Δ₃ [R for the bound, N exact for the arrangement].** Hubs = k-dimensional subspaces of K^N (as 0/1
   filtrations), node space W_n = sum of the three hubs of n, W_n ∩ W_n′ = 0 on edges; value √(k/w), w = dim W_n. This
   is the class of Theorem A (there k = 1, w = 2). Proposition 3.2: **w ≥ 5k/2** whenever a non-collinear pair of
   nodes has the other two corners of its rectangle collinear (a five-line rank argument); for Δ₃ every edge is of
   that kind. Attained: an explicit arrangement over Q with (k,w,N) = (2,5,10) (`z3_arrangement.py`, exact). So the
   quantitative form of Prop. 6.2 of `q1-notes.md` is "w/k ≥ 5/2 instead of 2", and inside this class Δ₃ stays
   below the tree value. With level shifts (the class then contains the tripod factor, Γ = 36) a local search over
   the polymatroid relaxation finds 27, 32.4 and 36 and nothing else (§3.4) [N].
4. **Cyclic nets: a placement above the record for large g [N exact; D for the value formula].** For the 3-net of
   Z_g, every 4 ≤ g ≤ 40, there is an arrangement in F_q^12 (q ≡ 1 mod g prime) with 2-dimensional hubs and
   5-dimensional node spaces, pairwise independent on **all** non-collinear pairs, and meeting exactly in the common
   hub on collinear pairs (`cyclic_octa.py`, `cyclic_octa_coll.py`). Level value

       min_k b_k / E = ((g−2)·√(2/5) + 1)/(g+1):   0.4829 (g=5), 0.5203 (7), 0.5876 (19), 0.6044 (31), 0.6106 (40), → 0.6325,

   against the tree floor 0.5857 for cyclic groups (`attain-notes.md`, `review-sat3.md`). It is below the tree
   records at g = 4, 5 (0.5410, 0.5519) and above 0.5857 from g = 19 on. The same arrangement exists over F_{2^s} for
   the odd g tested (`cyclic_octa_char2.py`), so by Theorem B of `q1-notes.md` [D there] it is a price when contracting
   fails. By Proposition 3.2 and the Shannon LP (5/2 for Z₃, …, Z₇) the value √(2/5) is optimal inside the ansatz
   **if every non-collinear pair is to be independent**. Dropping the three "special" difference classes (a fraction
   3/(g−2) of the non-collinear pairs) one gets √(5/12) = 0.6455 on the rest (three K_{2,2,1} blocks, k = 5, w = 12,
   exact for 6 ≤ g ≤ 40). Whether the cyclic limit is 1/√2 is open; §4.4 says why I now think it may be [C].
5. **Full planes (coordinator's question).** F_CAT(AG(2,3), four classes) ≤ (3/4)·F_CAT(Δ₃) [R], and the node-pod
   value 0.5000 is exactly (3/4)·(2/3): the window [0.5000, 0.5303] of the full plane of order 3 is the Δ₃ window
   scaled by 3/4. In general F_CAT(AG(2,g), g+1 classes) ≤ (g/(g+1))·F̄(Δ_g), Δ_g = the edges inside the lines of one
   class with the g other merges (§5).
6. **Computed, nothing above the records on Δ₃ [N].** Cone(A₃ building over F₂) with arbitrary hub points and exact
   legs: Γ ≤ 35.9975 in 8 chains (the executor's 33.75 was under-converged; the sup is 36 from below as in N = 3);
   two short chains in N = 5 reach 35.90.
   Hyperbolic plane: Γ between 22.6 and 36, the supremum only in the tree limit.
7. **Not done.** C4 (Γ_trees = 36 by hand) is not proved; §1.2 gives the reduction to hub gates and the form of the
   inequality. C2 (legs as points) was not implemented: §2.3 explains why I expect it to return the cap at any
   affordable depth.

Single best next step: §6.

---

## 1. The one-factor form of the Δ₃ problem

### 1.1 Statement [R, from the one-factor lemma of `s3-experiments.md` §5b]

For nine points h_{uv} of a CAT(0) space Y labelled by AG(2,3) put

    P = Σ over the nine same-class pairs of |h h′|²,
    c(n,n′) = sup over x, y in CAT(0) spaces Y′ ⊇ Y (Y convex in Y′) of [3|xy| − Σ_{h∈n}|xh| − Σ_{h′∈n′}|yh′|]₊,
    S_t = Σ over the three edges of the triangle T_t of c(n,n′)²,   t = 0, 1, 2.

Then Γ(Y, placement) = 9(S₀+S₁+S₂)/P and F_CAT(Δ₃) = sup √Γ/9 (products of the orbit of one factor). Known values
of κ* := sup (S₀+S₁+S₂)/P:

| class | κ* | reason |
|---|---|---|
| any metric space | ≤ 9 | c(n,n′) ≤ W₁(n,n′) ≤ sum of the three same-class distances |
| CAT(0) | ≤ 9/2 | pairwise midpoints (`notes.md` Cor. 3.4) |
| trees | 4 (conjecture 5.3 of `notes.md`; ≥ 4 by the tripod) | — |
| Euclidean, far legs | **= 3 for every placement** | below |

c does not depend on a matching between the hubs of n and of n′: it is a function of the two triples. Each
triangle T_t uses every same-class pair exactly once.

*Euclidean identity [R].* With far legs c(n,n′) = 3|β_n − β_n′| (barycentres), so
S_t = Σ_i |a_i + b_{i+t} + c_{i+2t}|², a_i = A_{i+1} − A_i etc., and Σ_t S_t = 3P + 2Σ_{i,j}⟨a_i,b_j⟩ + … = 3P because
Σ_i a_i = 0. The split between the triangles is arbitrary ((3P,0,0) when the hubs of each node of T₀ coincide). The
tripod factor has (S₀,S₁,S₂) = (0, 2P, 2P).

### 1.2 Trees: gates at hubs [R]; C4 not proved

**Lemma 1.1 [R].** In a tree, c(n,n′) = max(0, max over hubs a ∈ n, a′ ∈ n′ of 3|aa′| − Σ_{h∈n}|ah| − Σ_{h′∈n′}|a′h′|).

*Proof.* Let H_n be the hull of the hubs of n (a tripod with centre m_n and total length |n|). For a point g,
Σ_{h∈n}|gh| = |n| + |p m_n| + 3|gp|, p the projection of g to H_n. Moving g towards H_n lowers this sum by 3 per unit
and 3|gg′| by at most 3; inside H_n, moving g away from the projection of g′ raises 3|gg′| by 3 and the sum by at most
1. So the supremum is attained with g and g′ at tips of the hulls, i.e. at hubs. ∎

So Conjecture 5.3 is a statement about tree metrics on nine points:

    Σ_e [max_{a,a′}(3|aa′| − π_n(a) − π_n′(a′))]₊² ≤ 4·Σ_{same-class pairs} |hh′|²,   π_n(a) = Σ_{h∈n}|ah|.

In cut coordinates (a tree = nested cuts c with weights w_c) the coefficient of w_c in the bracket is
|n∩X_c| − |n′∩X_c| if c separates the gates (X_c = the side of a), and −|n∖X_c| − |n′∖X_c| otherwise. The diagonal
part Σ_e ε_c(e)² ≤ 3·N_cc (N_cc = same-class pairs cut by c) has the slack that the off-diagonal part uses; on the
tripod the matrix 4N − E is (4,−2,−2; −2,4,−2; −2,−2,4), positive semidefinite with kernel (1,1,1). For a star with
radii r_h the formula is c(n,n′) = (ε_n + ε_n′)₊, ε_n = 2max_{h∈n} r_h − Σ_{h∈n} r_h. I have no proof beyond the
three-arm family of `notes.md` §5.3 and no new inequality extracted from it. **C4 remains open.** What the
tree optimum uses, in the language of §3: a leg sits at one hub of a node and pays the two other distances; there is
no "median" inequality that I could state for general CAT(0) spaces, and §3–§4 show that the natural class beyond
trees (type-A building cones) has a different mechanism (rank inequalities) with a different constant.

---

## 2. Equality in the cap: the tripod branch is empty

### 2.1 Lune lemma, distance form [R]

**Lemma 2.1.** Let Λ be a CAT(1) space, x, y ∈ Λ with d(x,y) = π, and σ₁, σ₂ two geodesics of length π from x to y
with Alexandrov angle α < π at x. Then for all s, t ∈ [0,π]

    cos d(σ₁(s), σ₂(t)) = cos s cos t + sin s sin t cos α.

*Proof.* (i) The angle at y is < π: otherwise σ₁(s) → y → σ₂(s) is a local geodesic of length 2(π−s) ≤ π for
s ≥ π/2, hence a geodesic, so d(σ₁(π/2),σ₂(π/2)) = π; but α < π gives d(σ₁(s),σ₂(s)) < 2s for all s ≤ π/2 (a
concatenation through x that is geodesic has angle π at x). (ii) Hence every triangle (x, σ₁(s), σ₂(t)) and
(y, σ₁(s), σ₂(t)), 0 < s,t < π, has perimeter < 2π: the perimeter is at most 2π, with equality only if the path
through y, or through x, is geodesic. (iii) Let h(s) be the spherical comparison angle at x of (x; σ₁(s), σ₂(s)). By
B–H II.3.1 it is non-decreasing in s. The comparison angle at y of (y; σ₁(s), σ₂(s)) is non-decreasing in π − s. The
two isosceles triangles have the same base and legs s and π − s, and cos d = cos²s + sin²s·cos(angle) is the same
equation for both: the two comparison angles are equal. So h is non-decreasing and non-increasing, hence constant,
and its limit at s → 0 is α. (iv) For s ≤ t monotonicity in each variable gives α = h(s) ≤ ∠̃_x(σ₁(s),σ₂(t)) ≤ h(t) = α. ∎

(The full lune lemma also gives an embedded spherical lune; only the distances are used below. `q1-cyclic.md` §3
step 4 uses the same fact.)

### 2.2 The two-merge lemma [D]

**Proposition 2.2.** Let ρ > 0. No CAT(0) space contains points A₀, A₁, A₂, B₀, B₁, B₂ with

    |A_iA_i′| = |B_jB_j′| = 1,   |A_iB_j| = 2ρ,
    |m_ij m_{i+1,j+1}| = 1/√2,   |m_ij m_{i+1,j−1}| = 1/2      for all i, j,

m_ij the midpoint of [A_i, B_j].

Without the last condition such points exist (two orthogonal equilateral triangles: there the anti-diagonal
bimedian is 1/√2). The first three conditions are the equality structure of the two-merge cap on Δ₃ for the pair
(A,B); the last one is what a third class adds in the tripod branch.

*Proof.* Write z_ij = m_ij, call (i,j) a node, the pairs {(i,j),(i+1,j+1)} edges, and note that the three
(1,1)-cosets are triangles of edges.

1. *Flat triangles.* CN three times: |z z′|² ≤ ½|zA′|² + ½|zB′|² − ρ², |zA′|² ≤ ½ + 2ρ² − ρ², the same for B′; so
   |zz′|² ≤ ½ on edges, and equality makes all three CN equalities: the triangles (A′;A,B), (B′;A,B), (z;A′,B′) and,
   by the symmetry of the edge, (A;A′,B′), (B;A′,B′), (z′;A,B) are flat (B–H II.2.9/2.10), and |z(n) H|² = ½ + ρ²
   for the four hubs H not at n. In particular every triangle with two hubs of one class and one of the other is
   flat, so nodes in a common row or column have |zz′| = ½. With the hypothesis all 27 non-edge pairs are at ½.
2. *Common centre.* For z₀, z₁ in one triangle and z₃, z₄ in another, the quadrilateral z₀z₃z₁z₄ has sides ½ and
   diagonals 1/√2. With c the midpoint of z₀z₁: |z₃c|² ≤ ⅛, |z₄c|² ≤ ⅛ (CN) and |z₃z₄| = 1/√2, so c is the midpoint
   of z₃z₄ and the CN inequalities are equalities. Hence the midpoints of all edges of all triangles are one point
   c₀, |c₀z(n)| = 1/(2√2), the angle at c₀ between two nodes is π inside a triangle and π/2 (flat triangle)
   otherwise.
3. *Hubs seen from c₀.* CN at c₀ on [z(n),z(n′)] (H at n): |c₀H|² ≤ ρ² + ⅛; CN at z(n″) on [H′,H″]:
   |c₀H′|² + |c₀H″|² ≥ 2ρ² + ¼. So |c₀H|² = ρ² + ⅛ for all hubs, the triangles (c₀;H′,H″) (two hubs of a node) and
   (H; z(n), z(n′)) (an edge) are flat. In the space of directions L at c₀ (CAT(1), B–H II.3.19):

       (I1) d(ẑ,ẑ′) = π in a triangle, π/2 otherwise;
       (I2) d(Ĥ, ẑ(n)) = θ if H is at n, π − θ otherwise,   tan θ = 2√2·ρ;
       (I3) d(Â, Â′) ≤ ψ for two hubs of one class,   cos ψ = 1 − 4cos²θ   (Alexandrov ≤ comparison angle, sides R, R, 1).

4. *The link of L at a node.* Let Q = ẑ(0,0), Q′ = ẑ(1,1) (antipodal), A = Â₀ (at Q), A′ = Â₁ (at Q′), and
   N₁ = ẑ(0,1), N₂ = ẑ(0,2) (the other nodes at A₀), P₁ = ẑ(1,2), P₂ = ẑ(1,0) (the other nodes at A₁). By (I1), (I2)
   all six points X satisfy d(Q,X) + d(X,Q′) = π, so they lie on geodesics from Q to Q′, at latitudes θ (A), π − θ
   (A′), π/2 (the four nodes). Let a, a′, n₁, n₂, p₁, p₂ be their directions at Q, in the space of directions Λ of L
   at Q (CAT(1)). Lemma 2.1 in L, applied to pairs of these geodesics (the angle is < π whenever the distance in L
   is smaller than the distance through Q or Q′), translates (I1)–(I3) into

       d(n₁,n₂) = d(n₂,p₁) = d(p₁,p₂) = d(p₂,n₁) = π/2,   d(n₁,p₁) = d(n₂,p₂) = π
       [N₁ = ẑ(0,1) and P₁ = ẑ(1,2) are in one triangle, as are N₂ and P₂; all other pairs are in different ones];
       d(a,n_i) = φ₀, d(a,p_i) = π − φ₀,  d(a′,p_i) = φ₀, d(a′,n_i) = π − φ₀,   cos φ₀ = cot θ;
       d(a,a′) ≤ π − 2φ₀.

   (φ₀ ≥ π/4 because d(n₁,n₂) = π/2 ≤ 2φ₀; so ρ ≥ ½.)
5. *Contradiction.* d(a,a′) ≥ d(n₁,p₁) − d(n₁,a) − d(a′,p₁) = π − 2φ₀, so γ₁ = n₁ → a → a′ → p₁ is a geodesic of
   length π. γ₂ = n₁ → n₂ → p₁ is another one (π/2 + π/2). Their angle at n₁ is at most the comparison angle of the
   triangle (n₁; a, n₂) with sides φ₀, π/2, φ₀, which is arccos(cot φ₀) ≤ π/2. By Lemma 2.1 in Λ, with α that angle,
   cos d(a,n₂) = sin φ₀ cos α and cos d(a′,n₂) = sin(π−φ₀) cos α: **d(a′,n₂) = d(a,n₂) = φ₀.** But d(a′,n₂) = π − φ₀
   and φ₀ < π/2 (θ < π/2). ∎

Remarks. (a) For ρ = ½ (φ₀ = π/4) this is the case treated in `q1-cyclic.md` step 4, where the conclusion was
"same-class distance √(3/2)"; for intermediate ρ it replaces step 6 ("neither a contradiction nor a space") by a
contradiction. (b) The proof uses the hub metric only, no legs. (c) Steps 1–3 are the notes' steps 1–3 restricted to
two classes; the new step is 5. (d) Needs a referee on: the flat-triangle consequences of CN equality, and the use
of Lemma 2.1 in the two iterated spaces of directions.

**Corollary 2.3 (tripod branch) [D].** Let a G-symmetric configuration (hubs in a CAT(0) space, convex
1-Lipschitz pairs f_e^±, f⁺ + f⁻ ≥ 0, cross-class distances 2ρ < ∞) attain 27/√2 on Δ₃. Then for nodes n, ñ with a
common C-hub the bimedian κ := |m_AB(n) m_AB(ñ)| satisfies ½ < κ ≤ 1/√2. In particular the three hub-pair midpoints
of a node are pairwise distinct: if two of them coincide, all three do (the stabiliser of a node acts as S₃ on its
hubs), and then κ = |m_AC(n)m_AC(ñ)| = ½ by the flat triangle (C; A, A′).

*Proof.* κ ≤ 1/√2 is the bimedian inequality; κ ≥ ½ follows from the quadrilateral M₀M₃M₁M₄ of step 2 with one side
κ (diagonals 1/√2, three sides ½: 1 ≤ ¾ + κ²); κ = ½ is Proposition 2.2. ∎

### 2.3 Consequence for relaxations (spec C2)

The contradiction of step 5 lives in the space of directions of a space of directions. A finite relaxation that
imposes CN on iterated midpoints sees it only at a depth where midpoints approximate two nested infinitesimal
structures; the runs of `q1-cyclic.md` §1.2 (up to 1665 points in the tripod branch, value 27/√2 throughout) are
consistent with that. The legs do not enter Proposition 2.2 at all, so adding the legs as points (C2) cannot
exclude the tripod branch sooner, and in the open branch the relaxed optimum of `q1-cyclic.md` (cross distance²
7.55, node midpoints at distance² 1.74: ρ = 1.37, nearly flat hub triangles) is of the kind described in §2.4. I
did not implement C2.

### 2.4 The open branch ½ < κ ≤ 1/√2 [D for the listed facts, C for the last item]

G-symmetric equality configuration, hubs A, B, C of a node n, midpoints m_c, m_b, m_a of AB, AC, BC pairwise at
distance μ > 0, e the edge from n to n′, e′ the edge into n.

- By the stabiliser of the directed edge (≅ S₃ on the classes) f⁺_e(A) = f⁺_e(B) = f⁺_e(C) =: α, so f⁺_e ≡ α on the
  three sides of the hub triangle of n, and f⁻_e is constant on the sides of the hub triangle of n′. The three
  midpoints lie in the parallel set P_e = {f⁺_e + f⁻_e = 0} at equal height; those of n′ are their translates by 1/√2.
- With β_n the barycentre of the hubs: |β_nβ_n′| ≥ 1/√2 on edges (Jensen, both ends), while the barycentre chain
  (`notes.md` Prop. 3.5) gives |ββ′|² ≤ ⅓ + 2X, X = (4/3)ρ² − |β_nA|². So **X ≥ 1/12**: the hub triangle is not flat,
  with a defect that is absolute, not relative to ρ. For a pod (X = ρ²/3) this is ρ ≥ ½ again.
- AB-midpoints of two nodes: ½ in a common row or column, 1/√2 on edges, κ on the pairs sharing C; AC- and
  BC-midpoints of the latter pairs are at ½; κ ≤ ½ + 2μ.
- κ = 1/√2 [C, sketch only]: then every tetrahedron A_iA_i′B_jB_j′ has both cross bimedians 1/√2 with a common
  midpoint and is flat; the six hubs of two classes span a flat 4-dimensional body F_AB (two orthogonal triangles).
  If the leg rays from A_i stay in such flats, the direction of the leg of the edge at (i,j,k) seen from A_i is the
  bisector of â_i and b̂_j in F_AB and of â_i and ĉ_k in F_AC; the identification of F_AB and F_AC near the A-triangle is
  one affine map, whose linear part would have to send b_j to c_{−i−j} for every i. That is the cyclic obstruction in
  flat form. It is not a proof (the legs need not stay in the flats when f⁺ + f⁻ > 0 at the hubs).
- For ½ < κ < 1/√2 I have nothing. The hub conditions alone are consistent at κ = 1/√2 (three orthogonal triangles
  in R⁶), so any contradiction in this branch must use the legs (three parallel bimedian segments per edge).

### 2.5 Is the compactness argument valid?

Scheme: symmetrise a maximising sequence (ℓ₂-product over the automorphism group: Σ_k b_k is not decreased, and the
group acts by isometries permuting hubs and legs), pass to an ultralimit based at a hub, replace the legs by
f^± = lim (|x_e,·| − ½|x_ey_e|), |y_e,·| − ½|x_ey_e|. If F_CAT(Δ₃) = 1/√2 the limit attains 27/√2 in the relaxed problem
(convex 1-Lipschitz pairs with f⁺ + f⁻ ≥ 0), to which the proof of the cap applies verbatim, so the equality
structure (E1), (E2) of `q1-cyclic.md` holds in the limit. A contradiction in every branch then proves
F_CAT(Δ₃) < 1/√2, with no constant.

This is valid **provided** (i) the hubs stay at bounded distance from the base point when δ = 1. Same-class
distances are ≤ 1 and the values of f^± at hubs are bounded, but the cross-class distance 2ρ is not controlled by
anything in the chain (in the exact structures ρ is a free parameter ≥ ½, and the relaxed optimum of `q1-cyclic.md`
has ρ = 1.37). If ρ → ∞ along the sequence the limit has to be taken at the midpoints (the nine AB-midpoints stay
within distance 1 of each other), the hubs become points at infinity, flat triangles become flat strips, and the
equality analysis has to be redone in that setting (step 5 of `q1-cyclic.md` sketches the pod case only). (ii) All
branches are excluded; the limit objects are convex functions, not points, so arguments that use geodesic rays to
the legs are not available. As it stands: the pod branch with ρ < ∞ is excluded (Cor. 2.3); the branch ½ < κ ≤ 1/√2
and the regime ρ = ∞ are open. **So the strict inequality is not proved.**

---

## 3. The subspace ansatz: a rank inequality that is exactly the cyclic obstruction

### 3.1 The class

Let K be a field and V_h ⊆ K^N subspaces of dimension k, one for each hub, W_n := Σ_{h at n} V_h. Call a pair of
nodes *independent* if W_n ∩ W_n′ = 0. Place the hub h at the 0/1 filtration "V_h at level 1" of 𝒞_N(K) (cone over the
spherical building of GL_N(K), times R; CAT(0) for every field).

**Lemma 3.1 (value) [R; the computation of `q1-notes.md` Prop. 2.1].** For an independent pair (n,n′) with
dim W_n = dim W_n′ = w, the legs x = (W_n at level Ta, K^N at level −Ta below a complement at 0), y the same with W_n′,
a = 1/√(2w), give |xy| = 2T, |x,V_h| = T − ka + O(1/T) for every hub at n, the same at n′, so

    s^k_e → 2ka = k·√(2/w)   for all merges at once,   and δ ≤ √(2k):   s/δ ≥ √(k/w).

(Any basis of W_n extends to a basis adapted to x, so every V_h ⊆ W_n is a coordinate subspace of an adapted basis.)
Theorem A is k = 1, w = 2. In a product (block sum) of arrangements the dimensions add, so only Σw/Σk matters.

All distinct hubs are then pairwise independent as soon as they lie on two independent nodes; on Δ₃ any two hubs do.
The cap says w ≥ 2k, which is trivial here. `q1-notes.md` Prop. 6.2 says w = 2k is impossible on cyclic nets.

### 3.2 The bound w ≥ 5k/2 [R]

**Proposition 3.2.** Let n = (r,c), n′ = (r′,c′) be an independent pair of nodes of a 3-net such that the two other
corners m = (r,c′), m′ = (r′,c) of the rectangle lie on a common line D of the third class, and suppose
V_{R_r} ∩ V_{C_c} = 0. Then max(dim W_m, dim W_m′) ≥ 5k/2.

*Proof.* V_D ⊆ W_m ∩ W_m′. In W_m the sum V_{R_r} + V_{C_c′} is direct (the first lies in W_n, the second in W_n′), so
dim(V_D ∩ (V_{R_r} ⊕ V_{C_c′})) ≥ 3k − w, and likewise dim(V_D ∩ (V_{R_r′} ⊕ V_{C_c})) ≥ 3k − w. A vector in both is
a + b′ = a′ + b with a ∈ V_{R_r}, b ∈ V_{C_c} (in W_n) and a′, b′ in W_n′; then a − b = a′ − b′ ∈ W_n ∩ W_n′ = 0, so
a = b ∈ V_{R_r} ∩ V_{C_c} = 0. Two subspaces of V_D with trivial intersection: 2(3k − w) ≤ k. ∎

For a group net with classes r, c, r+c the hypothesis on the corners is "difference (a,a) with 2a ≠ 0"; by the
symmetry of the three classes the same holds for the differences (a,−2a) and (−2a,a). Call these three difference
classes **special**. On Δ₃ = Z₃ every non-collinear difference is special (it is (1,1) or (2,2)). In F₂^m there is
none (2a = 0), in agreement with Theorem A.

A weaker bound comes from the closure argument of Prop. 6.2 made quantitative: start from two collinear nodes
(span ≤ 2w − k), add hubs one at a time through nodes with two known hubs (each adds at most ε = w − 2k); if an
independent pair is reached after m additions, 2w ≤ 2w − k + mε, i.e. **w ≥ (2 + 1/m)k** [R]. Difference (1,1): m = 2
(the bound above); difference (1,2): m = 4, w ≥ 9k/4. For a prime p most slopes need many additions.

### 3.3 Shannon LP and attainment [N; exact where stated]

`ansatz_lp.py`: minimise w over polymatroids r on the hubs with r(h) = 1, r(n) ≤ w and r(n ∪ n′) = r(n) + r(n′) on the
chosen pairs (a lower bound for w/k over all subspace arrangements, all fields). `ansatz_lp_sym.py`: the same LP
reduced by the automorphism group of the net (the two agree on Z₃, Z₄).

| net | pairs required independent | min w/k (Shannon) | attained by subspaces |
|---|---|---|---|
| F₂² (12 hubs) | all 48 generic | **2** | Theorem A |
| Z₃ = Δ₃ | all 9 | **5/2** | yes: (2,5,10) over Q, `z3_arrangement.py` |
| Z₄, Z₅, Z₆, Z₇ | all non-collinear | **5/2** | yes: (2,5,12), §4 |
| Z₆ | non-collinear, not special | 9/4 | not known (graph blocks give 12/5) |
| Z₇ | non-collinear, not special | 9/4 | not known |

**Δ₃ in Q^10.** Take X = Q⁵ with V_{A0} = ⟨a,a′⟩, V_{B0} = ⟨b,b′⟩, V_{C0} = ⟨c,c′⟩ and the single relation
a+a′+b+b′+c+c′ = 0, a second copy Y for A₁, B₁, C₁, and

    V_{C2} = ⟨a₀ + b₁′, a₁ + b₀′⟩,   V_{A2} = ⟨b₀ + c₁, b₁ + c₀⟩,   V_{B2} = ⟨a₀′ + c₁′, a₁′ + c₀′⟩.

Exact check: all hubs have dimension 2, all nine node spaces dimension 5, all nine edges have W_n ⊕ W_n′ = Q^10.
Intrinsically [D]: K^10 = H¹(Levi graph of the configuration; K) = K^{27 flags}/(star relations of the 18 vertices),
V_h = the image of the flags at h, the Betti number of the Pappus graph is 27 − 18 + 1 = 10. Every hub is a
projective line with three marked points, every node a line through three marked points.

**Consequence [R + N exact].** In the subspace ansatz the value of Δ₃ is exactly √(2/5) = 0.63246 (Γ = 32.4): above the flat
0.5774, below the tree 0.6667. The class that reaches the cap on F_q^m is, on Δ₃, worse than trees, by a rank
inequality that does not degenerate (w/k = 5/2 against 2).

### 3.4 Level shifts and non-uniform factors [N]

The tripod factor is in the larger class "subspaces of unequal dimensions, hub point = 1_V − (dim V/N)·1 (the
R-factor of 𝒞_N removed), legs ±1 on W_n, W_n′": three points of K² for the hubs of one node, 0 for the others,
Γ = 36. For this class (formula in the header of `atom_fw.py`), with the rank function relaxed to a polymatroid and
N free, Frank–Wolfe ascents from 70 random LP vertices end at Γ = 27 (one hub), 32.4 (uniform 5/2) or 36 (tripod),
never above. Together with `filt_search.rs` (§5) this is the evidence that type-A building cones stop at 36 on Δ₃; it
is a local search, not a bound.

---

## 4. Cyclic nets Z_g: arrangements from characters

### 4.1 The construction [D; checked exactly, see 4.2]

Γ = Z_g, classes r, c, r+c. Let K contain a primitive g-th root of unity ζ. For a finite set Ξ ⊂ Z_g² (frequencies
ξ = (α,β)) let K^Ξ have basis e_ξ and let ρ(t₁,t₂) e_ξ = ζ^{αt₁+βt₂} e_ξ. A vector supported on a row (β fixed) is an
eigenvector of ρ(0,·); on a column (α fixed), of ρ(·,0); on a diagonal (α − β fixed), of the antidiagonal
{ρ(t,−t)}. So if V_R, V_C, V_D are spanned by row, column and diagonal vectors and W₀ = V_R + V_C + V_D, then

    V_{R_r} := ρ(r,0)V_R,  V_{C_c} := ρ(0,c)V_C,  V_{D_d} := ρ(d,0)V_D,   W_{(r,c)} = ρ(r,c)W₀

is a well-defined arrangement with all incidences of the net, and (n,n′) is independent iff W₀ ∩ ρ(t)W₀ = 0 for
t = n′ − n. Everything is decided inside W₀ and by the frequencies.

**Graph blocks.** Choose some rows, columns and diagonals of the dual group whose pairwise intersection points are
distinct and lie on exactly two chosen lines each. Ξ := these points; M := an oriented incidence matrix (lines ×
points) of the graph "lines, joined when they meet"; W₀ := row space of M (the cut space, dimension #lines −
#components); V_R, V_C, V_D := the spans of the rows of M of each type.

- **Octahedron K_{2,2,2}**: two rows, two columns, two diagonals; 12 points; (k,w,N) = (2,5,12).
- **K_{2,2,1}**: two rows, two columns, one diagonal (and the two rotations); 8 points, rank 4; the sum of the three
  rotations has (k,w,N) = (5,12,24).

A block with v lines needs at least 2(v−1) points for independence, which for simple tripartite graphs forces
v ≥ 5; the ratio is w/k = 3 − 3/v, so K_{2,2,1} (12/5) is the best graph block and the octahedron (5/2) the next.
For g = 3 the dual group is too small for twelve distinct intersection points; there the arrangement of §3.3 (ten
dimensions, not of this translation-diagonal form) does the same job.

### 4.2 What is verified [N, exact]

`cyclic_octa.py` (F_q, q the least prime ≡ 1 mod g; exact Gaussian elimination): for every 4 ≤ g ≤ 40 there are
parameters (rows {0,b₂}, columns {0,a₂}, diagonals {γ₁,γ₂}) such that rank M = 5, the three hub spaces are
2-dimensional and invariant as required, and **W₀ ∩ ρ(t)W₀ = 0 for every non-collinear t**. The parameters
(1,1,2,3) work for all g ≤ 40 prime to 3 (g ≥ 5), (1,1,2,4) for the multiples of 3 that are not multiples of 4,
(1,1,2,7) for g = 12, 24, 36; the failures of a fixed parameter set occur at finitely many torsion points of fixed
order (for (1,1,2,3): two points of order 3), as expected for the zero set of a fixed Laurent polynomial in
(ζ^{t₁}, ζ^{t₂}). A proof for all g would need that torsion analysis; I have not done it, so **the statement is
for g ≤ 40**. `cyclic_octa_coll.py`: for collinear pairs dim(W_n ∩ W_n′) = 2 exactly (g = 5, 7, 12, 19, 24, 31, 40).
`cyclic_octa_char2.py`: the same independence over F_{2^s} for g = 5, 7, 9, 11, 13, 15, 17, 21, 23, 31, 33, 35, 39.
`cyclic_blocks.py`: for 5 ≤ g ≤ 40 each K_{2,2,1} block fails only on special differences, and the three-block sum is
independent on exactly the non-collinear, non-special differences (at g = 5 every non-collinear difference is
special, so on none).

### 4.3 Values [D]

*Non-collinear edges.* Lemma 3.1: s^k = δ√(2/5) for the three merges.

*Collinear edges.* Let n, n′ share V₀ (class k₀) and W_n ∩ W_n′ = V₀. Pick k₁ ≠ k₀, V, V′ the hubs of class k₁, and
write W_n = V₀ ⊕ V ⊕ L, W_n′ = V₀ ⊕ V′ ⊕ L′ (dim L = dim L′ = 1); these five spaces are independent because
dim(W_n + W_n′) = 8. In a basis through V, V′ and a complement M ⊇ V₀ + L + L′ take d = ½ on V, −½ on V′, 0 on M. Then
s^{k₁} → 2 = δ, and the two other merges get 0: the common hub lies in M, and the third hubs lie in V ⊕ M, resp.
V′ ⊕ M, and meet V, resp. V′, trivially. Choosing k₁ = the successor of k₀ gives every merge the collinear edges of
one class.

**Proposition 4.1 [D, with 4.2].** For 4 ≤ g ≤ 40 the 3-net of Z_g has a placement in 𝒞_12(F_q) with

    min_k b_k / E = ((g−2)·√(2/5) + 1)/(g+1).

| g | 4 | 5 | 7 | 11 | 13 | 19 | 23 | 31 | 40 | ∞ |
|---|---|---|---|---|---|---|---|---|---|---|
| this placement | 0.4530 | 0.4829 | 0.5203 | 0.5577 | 0.5684 | 0.5876 | 0.5951 | 0.6044 | 0.6106 | 0.6325 |
| trees (records) | 0.5410 | 0.5519 | | | | | | | | 0.5857 |
| cap (Cor. 3.4) | 0.6325 | 0.6455 | 0.6614 | 0.6770 | 0.6814 | 0.6892 | 0.6922 | 0.6960 | 0.6984 | 0.7071 |

So the cyclic floor 0.5857 is exceeded from g = 19 on (already with the collinear edges set to zero from g = 40
on), not at small g. Independent check (`cyclic_octa_dist.py`, g = 5, 7, T = 10⁴, distances from the definition of
the metric with exact ranks): non-collinear edges s^k/δ = 0.63238 in the three merges (limit 0.632456), collinear
edges (−0.0001, 0.99995, −0.0001). For odd g the arrangement over F_{2^s} is a finite subset of 𝒞_12(2^s); by Theorem B of
`q1-notes.md` [D there] it is a price if contracting fails, with the usual per-level form (λ₀ depending on g).

With the three K_{2,2,1} blocks the non-special non-collinear edges get s/δ = √(5/12) = 0.6455, and the special ones
(3(g−1) of (g−1)(g−2) differences) get (0.474, 0.474, 0.632)·δ from the two blocks that stay independent. Hence
**liminf_{g→∞} F_CAT(net of Z_g) ≥ √(5/12) = 0.6455**, as far as the scan (g ≤ 40) represents all g [N].

### 4.4 What is the limit? [C]

Upper side: only the cap. Inside the ansatz, Prop. 3.2 and the closure bound say that a difference class that is
reached after m closure steps costs w ≥ (2 + 1/m)k; the special classes have m = 2, the classes of (1,2) have m = 4,
and for prime g → ∞ all but a vanishing fraction of the slopes have m → ∞. The Shannon LP agrees on the small cases
(5/2 with the special pairs; 9/4 without them on Z₆ and Z₇, where the remaining classes have m = 4). So there is no known obstruction to w/k → 2, i.e. to
**lim F_CAT(Z_p) = 1/√2**, on all but a vanishing fraction of the edges. Lower side: 12/5 is the best that graph
blocks can do. Going below needs blocks in which frequencies lie on three chosen lines (columns of M with three
entries); plain incidence matrices of triple points in Z² have rank #lines − 3 but too few points (a parallelogram
m × m needs m ≥ 7 and gives 8/3). I did not find a block below 12/5. Conjecture, weakly held: the limit is 1/√2,
by blocks adapted to slopes of growing height; Δ₃ and the small cyclic nets are then exceptional because all their
slopes are special.

---

## 5. Full affine planes and "every two nodes collinear" (coordinator's question)

AG(2,g) with all g+1 classes: E = g²(g²−1)/2, every edge is internal to exactly one class j(e), and s^{j(e)}_e ≤ 0.
For a class j let Δ_g^{(j)} be the configuration "edges internal to j, the g other merges" (E_Δ = g²(g−1)/2 edges:
the cliques on the g lines of class j; E = (g+1)·E_Δ). Δ_3^{(j)} is Δ₃.

**Proposition 5.1 [R].** For every CAT(0) placement of the full plane,
Σ_k b_k ≤ Σ_j Σ_k b_k(restriction to Δ_g^{(j)}). Hence

    F_CAT(AG(2,g), g+1 classes) ≤ (g/(g+1))·F̄(Δ_g),     F̄ := sup of the merge average,

and for g = 3 (where F̄ = F_CAT by symmetrisation): **F_CAT(AG(2,3), 4 classes) ≤ (3/4)·F_CAT(Δ₃).**

*Proof.* Drop the non-positive terms s^{j(e)}_e and regroup the edges by j(e); each group, with the hubs of the other
g classes and its own legs, is a placement of Δ_g^{(j)} with the same δ_k. Each group contributes at most
g·E_Δ·F̄(Δ_g), and the value is at most (1/(g+1))·Σ_k b_k/E with E = (g+1)E_Δ. ∎

Consequences.
- g = 3: pair cap 0.5303 = (3/4)/√2, node pods 0.5000 = (3/4)(2/3). **The window of the full plane of order 3 is the
  Δ₃ window times 3/4**; a cap c for Δ₃ gives (3/4)c, and if F_CAT(Δ₃) = 2/3 the node pods are optimal on the full
  plane. Proposition 2.2 applies to each of the four Δ₃'s inside an equality configuration.
- General g: the pod values √(2g−2)/(g+1) are (g/(g+1))·√(2g−2)/g; the question is F̄(Δ_g) ∈ [√(2g−2)/g, 1/√2].
- The subspace ansatz has a version for collinear edges (legs ±a on complements of the common hub inside W_n, W_n′;
  value (g/(g+1))·√(k/w′), w′ = dim of the span of the g other hubs of a node, required independent of the common
  hub and of the corresponding span at n′). Flat is w′ = gk, node pods correspond to w′/k = g²/(2g−2) (9/4 at
  g = 3). For odd g Proposition 3.2 applies to every edge and every two merges R, C other than j (the corners m, m′
  are collinear in a class different from R, C and j), but it bounds a three-hub span by 5k/2, which for g > 3 is
  far from the g-hub span w′ that enters the value. I did not run the LP for more than three merges or look for
  arrangements. The character construction of §4 does not apply as it stands (it uses non-collinear pairs).
- No better placement and no cap below the pair cap follows for full planes from this note.

---

## 6. What to do next

**The single best next step: decide the limit for cyclic nets inside the ansatz.** It is now a finite-dimensional
linear algebra problem with a clear target: find finite Ξ ⊂ Z², a subspace W₀ ⊂ C^Ξ with row-, column- and
diagonal-graded parts of dimension k each and W₀ ∩ ρ(t)W₀ = 0 for generic t ∈ T², with dim W₀/k < 12/5; or prove a
lower bound for w/k on slopes of large height. Either outcome is a result: w/k → 2 gives lim F_CAT(Z_p) = 1/√2 (and,
over F_{2^s}, the price statement when contracting fails), a bound w/k ≥ c > 2 uniform in the slope would be the first
quantitative obstruction for cyclic groups beyond Δ₃ and would say what to prove in general CAT(0) spaces.
Concretely: (a) run the Shannon LP for Z₇, Z₈, Z₉ with the special classes and then the m = 4 classes removed
(orbit-reduced LP, minutes); (b) search blocks with triple points (columns of M with three entries) over small line
sets; (c) do the torsion-point analysis that turns §4.2 into a statement for all g.

For Δ₃ itself:
- **E-a (referee, 1–2 h).** Lemma 2.1, Proposition 2.2 (steps 3–5), Proposition 3.2, Lemma 3.1, §4.3 (collinear
  legs), Proposition 5.1.
- **E-b.** The open branch of §2.4: either make the κ = 1/√2 sketch a proof and extend it, or find the
  corresponding structure. The regime ρ = ∞ needs its own limit object (§2.5).
- **E-c.** C4 as a computer proof (135135 trivalent trees modulo 216, copositivity per gate assignment); Lemma 1.1
  removes the leg variables.
- **E-d.** Γ on Δ₃ in 𝒞_5(F₂), 𝒞_4(F₃), 𝒞_3(F₄) with arbitrary hub points (the present code is F₂ only; N = 5 with
  two-step legs runs at 0.07 s per move).

---

## 7. Computations on Δ₃ [N]

- `filt_search delta3 4 3 400000 2 SEED` (seeds 11–14): Cone(building of GL₄(F₂)), hubs = complete flags with
  three non-negative weights (all points of the cone), legs = all 31040 pairs of opposite partial flags with the
  optimal weights (exact). Best Γ per chain: 35.64, 35.9975, 35.36, 35.70, 35.9974, 34.62, 35.9961, 35.9972. Optimum
  shape: three pairwise skew lines of PG(3,2) for the hubs of one node, the rest at the apex: the tripod. Calibration
  (`filt_search check`): tripod in N = 2 gives 36; the placement of `q1-notes.md` §2.2 for X₄ gives 216 = cap.
- N = 3 (all legs): 35.995. N = 5 (legs with ≤ 2 steps, 1.03·10⁶ records; two chains of 9000 moves only): 34.64, 35.90.
  Short runs; they show no value above 36 and prove nothing for N = 5.
- `hyp_search.py`: in H² the tripod-like family has Γ = 26.9, 22.6, 30.1, 34.5 at radius 0.01, 1, 5, 20 (→ 36);
  annealing from six scales ends at 27. Negative curvature at finite scale is worse than both limits.
- `atom_fw.py` (§3.4): 27 / 32.4 / 36.

## 8. Dead ends [X]

- Pure subspace ansatz on Δ₃: capped at √(2/5) (Prop. 3.2).
- Cones over a flat torus carrying the Pappus graph as a hexagonal tiling: systole ≥ 2π forces edge length ≥ 69°,
  value 0.41.
- A product tripod³ × Y, or any join with the link of tripod³, for intermediate ρ: the same-class angle is
  π − 2α > π − 2φ₀ (cos φ₀ = cos α/√2); a product never beats its factors.
- The one-Lipschitz-projection relaxation for trees (c_e ≤ sum over the cuts of one geodesic): 26 on the tripod
  instead of 24.
- Direct sums of two planar realisations of the net (hubs of dimension 2 in K³ ⊕ K³): node spaces of dimension 4
  that always meet (`q1-notes.md` §6 item 5); the octahedron needs the fifth dimension.
