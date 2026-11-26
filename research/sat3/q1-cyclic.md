# F_CAT on cyclic nets: Δ₃ first

Theory notes, 27 Nov 2026. Not committed, not machine-checked, not refereed. Sequel to `q1-notes.md`.

Tags: **[R]** proved here in full from the cited inputs; **[D]** derived here, proof written or sketched, unreviewed;
**[N]** numerical (script named); **[C]** conjecture; **[X]** dead, with reason.

Scripts (`q1c/`): `relax.py` (the convex relaxation, reduced by the automorphism group), `run_tripod.py`,
`run_tripod2.py` (the tripod branch), `flat_sanity.py` (validation), `inspect_sol.py`, `inspect_tripod.py`
(what the relaxed optimum looks like). Outputs: `q1c/out_flat_sanity.txt`, `q1c/out_tripod_l3.txt`.

Normalisation as in `q1-notes.md` §0. Δ₃: nodes Z₃², merges r, c, r−c, the nine edges {n, n+(1,−1)} (three
triangles, the lines of the fourth class r+c). Known: tree products give Σ_k b_k = 18 (6 per merge, value 2/3); the
cap of `notes.md` Cor. 3.4 is 27/√2 = 19.0919 (6.3640 per merge, value 1/√2).

---

## 0. Results in brief

1. **The relaxation asked for does not go below the cap [N].** The convex program "squared distances on hubs and
   iterated midpoints subject to all CN (four-point) inequalities, leg functions convex and 1-Lipschitz" gives
   Σ_k b_k ≤ 19.091883 = 27/√2 at every depth run (36 to 1665 points), also on the branch where every node has a
   common midpoint of its three hub pairs. It is a rigorous upper bound, and it is exactly the cap. So this test
   neither proves 6 nor anything below 9/√2.
2. **Why [R + N].** The loss is in the leg functions, not in the metric: with every CN inequality imposed as an
   equality (Euclidean point set) the bound is still 19.0919 unless the node barycentres are included, and then it is
   the flat value 9√3 = 15.5885 exactly. A relaxed leg function is tested for convexity only on the listed midpoints.
   The relaxation is as strong as the chains of inequalities it contains (pairwise-midpoint chain = cap; barycentre
   chain = flat value when the hub triangle is flat), and a bound below the cap needs a new chain, which I do not have.
3. **Two lemmas that restrict where a gain can come from [R].**
   - Lemma 2.1 (sandwich): if the convex hull of the hubs is flat, the value is at most the flat value, wherever the
     legs are (inside or outside the flat, in any CAT(0) space containing it).
   - Lemma 2.2 (fins): legs may be replaced by closed convex sets: s = d(K⁺,K⁻) − d(o,K⁺) − d(o′,K⁻) is a legitimate
     saving for any closed convex K^± in the hub space.
4. **Equality structure on Δ₃ [D].** If the cap were attained (in a limit) in the branch where every node's hubs
   form a symmetric tripod with centre z(n) and arm ρ: collinear centres are at δ/2, edge centres at δ/√2, all nine
   centres have one common centre c₀ (three mutually perpendicular tripods of centres), every hub is at
   |c₀H|² = ρ² + δ²/8. At ρ = δ/2 and in the limit ρ → ∞ the links force the angle at c₀ (resp. at the limit point)
   between two same-class hubs to be π, which makes the same-class distance √(3/2)·δ: the configuration is tripod³,
   value 1/√3. For intermediate ρ, and for the branch in which the three hub-pair midpoints of a node are distinct
   (on parallel lines of the edge), I have no contradiction.
5. **Status.** F_CAT(Δ₃) ∈ [2/3, 1/√2], unchanged. No cap below 1/√2 is proved for any cyclic net, and no placement
   beats the tree-product records. My belief [C]: F_CAT(Δ₃) < 1/√2 (the two ends of the tripod branch die for the
   same reason, and every model computed lands on 2/3), but the evidence is not a proof.

---

## 1. The relaxation

### 1.1 Definition and validity [R]

Point set P = hubs ∪ auxiliary points (midpoints, barycentres, defined formally and closed under the automorphism
group G of the configuration; |G| = 108 for Δ₃). Unknowns, all reduced modulo G:

- D(p,q) ≥ 0 for pairs of points of P (squared distances); dd(p,q) ≥ 0 with dd² ≤ D;
- for each edge end ε = (e, n) and p ∈ P a number f_ε(p) (meaning |leg_ε, p| − ½|legs of e|).

Constraints, each valid for every placement in a CAT(0) space Y with the auxiliary points placed at the true
midpoints / barycentres:

- midpoint m of x, v: D(x,m) = D(v,m) = D(x,v)/4, and D(z,m) ≤ ½D(z,x) + ½D(z,v) − ¼D(x,v) for all z ∈ P (C.4(a));
- barycentre b of x₁..x_r: D(z,b) ≤ mean_i D(z,x_i) − mean_i D(b,x_i) for all z (C.4(c));
- f_ε(m) ≤ ½f_ε(x) + ½f_ε(v), f_ε(b) ≤ mean f_ε(x_i) (the distance to a point is convex; Jensen);
- f_ε(p) − f_ε(q) ≤ dd(p,q); f_{(e,n)}(p) + f_{(e,n′)}(p) ≥ 0 (triangle inequality);
- D(o,o′) ≤ δ_k² for hubs of the same merge; triangle inequalities √D_xz ≤ √D_xy + √D_yz (convex; added lazily).

Objective: Σ_k δ_k⁻¹ Σ_e s^k_e with s^k_e = −f_{(e,n)}(o^k(n)) − f_{(e,n′)}(o^k(n′)), which equals Σ_k b_k.

Convexity: squared metrics of CAT(0) spaces form a convex cone (ℓ₂-products add them), the constraints above are
linear in (D, f) except dd² ≤ D and the triangle inequalities, which are convex. So the program is convex, a
symmetric optimum exists, and its value is an upper bound for Σ_k b_k over all CAT(0) placements with the given δ_k
(up to solver tolerance, about 1e-6 here). Legs at any distance, including far legs, are covered: only the functions
f_ε enter. Runs use δ_k = 1; unequal δ_k were not scanned (the bound is then for placements with equal δ_k, which is
where the records are).

### 1.2 Values for Δ₃ [N]

`python3 relax.py <spec>`; `python3 run_tripod2.py <level>`.

| point set | points | D-orbits | bound on Σ_k b_k |
|---|---|---|---|
| hubs only | 9 | 2 | 27.000 |
| + 27 node midpoints m_kl(n) | 36 | 13 | 19.091883 |
| + same-class midpoints | 45 | 22 | 19.091883 |
| + node barycentres | 45 | 21 | 19.091883 |
| + midpoints along edges between node midpoints | 117 | 89 | 19.091883 |
| + same-class midpoints + node barycentres | 135 | 127 | 19.091883 |
| + midpoints between node midpoints of collinear nodes | 360 | 677 | 19.091883 |
| tripod branch (one centre z(n) per node), hubs + centres | 18 | 6 | 19.091884 |
| tripod branch, + all midpoints of hubs and centres | 171 | 208 | 19.091883 |
| tripod branch, + midpoints of the edge centres c₀ with hubs and centres | 333 | 692 | 19.091883 |
| tripod branch, + midpoints of c₀ with all first-level midpoints | 1665 | 13722 | 19.091883 (status "inaccurate", 488k inequalities) |

27/√2 = 19.0918831. Lazy triangle inequalities (up to 800 orbit types) never changed the value.

What the relaxed optimum looks like (`inspect_sol.py`, `inspect_tripod.py`): same-class D = 1; cross-class hub
distances are large (D = 7.55 in the free branch, 5.30 in the tripod branch, i.e. arm ρ = 1.15 δ); the three
midpoints of a node are far apart in the free branch (D = 1.74); edge-neighbour midpoints have D = ½ and collinear
ones D = ¼ exactly, as the cap chain demands; in the tripod branch all edge centres coincide (D = 0 between the c₀'s)
and D(c₀, hub) = ρ² + ⅛ as in §3.

### 1.3 Validation and diagnosis [N + R]

`flat_sanity.py`: impose every CN and variance inequality as an equality (then D is Euclidean on P).

| point set (all CN as equalities) | bound |
|---|---|
| node midpoints | 19.091883 |
| node midpoints + same-class midpoints + edge midpoints | 19.091883 |
| node barycentres | 15.588458 |
| node midpoints + node barycentres (+ edge barycentre midpoints) | 15.588457 |

9√3 = 15.5884573 is the true value for a flat hub hull (Lemma 2.1). So the code reproduces the flat value once the
barycentre chain (Σ_k s^k_e ≤ 3|β(n)β(n′)|, `notes.md` Prop. 3.5) is available, and without it stays at the cap even
on a Euclidean point set. Conclusion: the finite relaxation does not enforce convexity of the leg functions on the
hull, only along the listed geodesics. In the relaxed optimum the function f⁻ of an edge decreases at unit rate along
the three segments [m_kl(n), m_kl(n′)], which are not parallel; in a flat this contradicts the subgradient inequality
(for the orthogonal-simplex configuration it fails by 0.707 against 0.530 at the pair m₁₃(n), m₁₂(n′)), but that
inequality is not a midpoint condition on a finite set: it needs the whole backward ray, i.e. the leg itself.

Consequence for the method. The relaxation equals the best of the inequality chains whose points it contains. To
certify a value below the cap on Δ₃ one has to add a constraint that is (a) valid in every CAT(0) space, (b) not a
consequence of CN on midpoints plus convexity along them, and (c) tight on the nine-tripod product. The natural
candidates are statements about the pair (f⁺, f⁻) of one edge: both are Busemann-type functions of the two ends of
one line, f⁺ + f⁻ vanishes exactly on the parallel set Z × ℝ of that line, and on it f⁺ = −f⁻ is the ℝ-coordinate
(flat strip theorem). I did not find a convex formulation of this.

---

## 2. Two lemmas

**Lemma 2.1 (flat hub hull) [R].** Let the hubs lie in a CAT(0) space Y and suppose their closed convex hull C is flat
(isometric to a convex subset of a Euclidean space). Then for every placement of the legs in Y,
Σ_k b_k ≤ √(E·Σ_k E_k) as in `notes.md` Prop. 2.2 (for Δ₃: 9√3), whether or not the legs lie in a flat.

*Proof.* For an edge with legs x, y put f⁺ = |x,·| − ½|xy| and f⁻ = |y,·| − ½|xy| on C. Both are convex and 1-Lipschitz
and f⁺ + f⁻ ≥ 0. So the convex function f⁺ lies above the concave function −f⁻ on the Euclidean convex set C, and
there is an affine ℓ with f⁺ ≥ ℓ ≥ −f⁻ on C; its gradient w has |w| ≤ 1 (ℓ ≤ f⁺ grows at most at unit rate; if C is
not full-dimensional take w in its affine hull). Then s^k_e = −f⁺(o) − f⁻(o′) ≤ −ℓ(o) + ℓ(o′) = ⟨w, o′ − o⟩, and the
proof of Prop. 2.2 applies verbatim with u_e replaced by w_e. ∎

So Prop. 2.2 is a statement about the hubs only: a gain over the flat value needs a non-flat hub hull, however the
legs are placed. (Legs outside a flat can have non-affine functions on it, e.g. max of two Busemann functions, by
bending the flat along a hyperplane inside tripod × ℝ^{d−1}; the lemma says this does not help.)

**Lemma 2.2 (fins) [R].** Let Y₀ be a CAT(0) space containing the hubs and K⁺, K⁻ ⊆ Y₀ closed convex. Then there is a
CAT(0) space Y ⊇ Y₀, in which Y₀ is convex, with legs x_T, y_T such that for all hubs o, o′

    |x_T y_T| − |x_T o| − |y_T o′|  →  d(K⁺,K⁻) − d(o,K⁺) − d(o′,K⁻)     (T → ∞).

*Proof.* Glue K⁺ × [0,∞) to Y₀ along K⁺ × {0} = K⁺, and likewise K⁻ × [0,∞) (Reshetnyak gluing along complete convex
subsets, B–H II.11.1; Y₀ stays convex, so the second gluing is again along a convex set). Take x_T = (k⁺, T),
y_T = (k⁻, T). A path from x_T to p ∈ Y₀ leaves the fin through K⁺, so
|x_T p| = inf_k (√(T² + |k⁺k|²) + |kp|) = T + d(p,K⁺) + O(1/T), and |x_T y_T| = 2T + d(K⁺,K⁻) + O(1/T). ∎

So in the definition of F_CAT the legs of an edge can be taken to be a pair of convex sets of the hub space. With
K^± points this is the original definition; with K⁺ = conv(hubs of n), K⁻ = conv(hubs of n′) one gets
Σ_k s^k_e = 3·d(K⁺,K⁻), all three merges at once. In a flat this is at most the flat value (Lemma 2.1), in
𝒞_N on the nets of `q1-notes.md` it is again 3δ/√2 on generic edges. It is a convenient way to state placements:
"the three hubs of a node as one convex body, edges pay the gap between bodies".

---

## 3. What equality on Δ₃ would force [D]

Assume a sequence of placements with Σ_k b_k → 27/√2 and pass to a limit configuration (hubs in a CAT(0) space,
horofunction pairs for the legs; this step is not written out). Normalise δ = 1. Equality in the chain of Cor. 3.4
for every edge e = (n,n′) and every pair of merges gives, as in `q1-notes.md` §5:

(E1) all same-class hub distances are 1; triangles (o^k_G; o^l_H, o^l_{H′}) are flat (CN equality);
(E2) for each pair (k,l): f⁺_e is affine on [o^k(n), o^l(n)], the midpoints m_kl(n), m_kl(n′) lie on one line parallel
     to the line of e, at distance 1/√2.

**Tripod branch.** Suppose in addition that the three midpoints of each node coincide: z(n), arms ρ (all cross-class
hub distances 2ρ). Then:

1. Collinear nodes (common hub h): z(n), z(n′) are midpoints of two sides of the flat isosceles triangle with apex h,
   so |z(n)z(n′)| = ½. Edge-neighbours: |z(n)z(n′)| = 1/√2. Also |z(n), o|² = ½ + ρ² for the six hubs o not at n.
2. For two class-4 triangles T, T′ and z₀, z₁ ∈ T, z₃, z₄ ∈ T′: the quadrilateral z₀z₃z₁z₄ has sides ½ and diagonals
   1/√2, equality in C.4(b), so it is a flat square (C.4(f)) and its diagonals have the same midpoint. Hence the three
   centres of each class-4 triangle form a tripod (not a flat triangle), with one centre **c₀ common to all nine**,
   |c₀z(n)| = 1/(2√2), and centres of different class-4 triangles are perpendicular at c₀.
3. CN at c₀ (midpoint of two centres of one triangle) and at z(n) (midpoint of two hubs) give |c₀H|² = ρ² + ⅛ for
   every hub, with flat triangles (c₀; H, H′) for cross-class pairs and (c₀, H, z(n)) for n ∋ H. In the link L of c₀:
   d(Ĥ, ẑ(n)) = θ for n ∋ H and π − θ otherwise, tan θ = 2√2ρ; d(ẑ,ẑ′) = π inside a class-4 triangle and π/2
   otherwise. This is the incidence pattern of points and lines of a 3-dimensional projective geometry seen from the
   centre of a 4-cube (compare `q1-notes.md` §5), with the Pappus configuration in place of 16 lines of PG(3,2).
4. **ρ = ½ is impossible.** Fix a row hub A = R̂₀, another B = R̂₁, and Q = ẑ(0,c). Its antipode in L is ẑ(1,c−1), and A, B,
   ẑ(0,c±1), ẑ(1,c), ẑ(1,c+1) all lie on geodesics from Q to that antipode. Lune comparisons give, in the link Λ of L at
   Q, for the directions a, b, q₁, q₂, p₀, p₁ of these six points: q₁, q₂, p₀, p₁ are the quarter points of a closed
   geodesic of length 2π; d(a,q_i) = d(b,p_i) = φ₀ with cos φ₀ = cot θ. For ρ = ½, φ₀ = π/4, so a and b are the
   midpoints of [q₁,q₂] and [p₀,p₁], the path a–q₂–p₀–b is a local geodesic of length π, d_Λ(a,b) = π, the path A–Q–B is
   a local geodesic of length π in L, and the angle at c₀ between R₀ and R₁ is π. Then |R₀R₁| = 2√(3/8) = √(3/2) > 1,
   against (E1). The space forced up to this point is tripod³ with the hubs at nine of its 27 octant points; its
   value is 1/√3.
5. **ρ → ∞ is impossible for the same reason.** The hubs of one class converge to one point Ω of L at distance π/2 from
   all ẑ; their first-order positions ν_r in the tangent cone at Ω satisfy ⟨ν_r, u_n⟩ = ±1/(2√2) against the nine
   directions u_n of the ẑ's, which again form three mutually perpendicular tripods; step 4 applies verbatim in the
   link of Ω and gives |ν_r − ν_{r′}| = √(3/2).
6. **Intermediate ρ.** The same computation gives the necessary condition d_Λ(a,b) = π − 2φ₀ with φ₀ ∈ (π/4, π/2): a and
   b lie on both geodesics q₁ → p₀ and q₂ → p₁, an H-shaped tree inside Λ together with the closed geodesic through
   q₁, q₂, p₀, p₁. A round sphere does not contain this (it would need cos φ₀ = cos φ₀/√2); a CAT(1) disc with two
   singular points might. I have neither a contradiction nor a space. The relaxed optimum of §1.2 sits here
   (ρ = 1.15).

**Other branch.** If the three midpoints of a node are distinct they lie on three parallel lines of the parallel set
Z_e × ℝ of each edge at the node. For a single edge this is realisable (two triangles in Z_e with the same side
midpoints: a 6-pod, or tripod × tripod). I did not analyse the consistency around a node or a triangle.

So the statement "F_CAT(Δ₃) < 1/√2" is reduced, in the tripod branch, to the non-existence of a CAT(1) space Λ as in
step 6 for all φ₀ simultaneously with the rest of the structure; and the other branch is open. **Not proved.**

---

## 4. Cyclic nets of larger order, and placements

- **Upper bounds.** The relaxation gives the cap for every balanced configuration at the depths that are affordable
  (it contains only the pairwise chain), so I did not run Z₅, Z₇: the answer would be the cap. A cap below 1/√2 for
  cyclic nets needs the new inequality of §1.3.
- **What a proof would have to use.** `q1-notes.md` Prop. 6.2 (corrected): with pairwise transversal hubs at every
  node, a cyclic net has no realisation with skew node-planes; the sub-net generated by two collinear nodes is
  everything. The CAT(0) analogue would be: "the flat triangles (h; z, z′) around the hubs and the tripods at the
  nodes generate, from two collinear nodes, a configuration in which all centres are close" (for Δ₃: all nine
  centres within 1/(2√2) of c₀, step 2 above). On F₂^m the generated sub-net has order 2 and nothing follows.
- **Placements [X so far].** Tried by hand, none above the tree-product value 2/3 on Δ₃: tripod³ (1/√3);
  point hubs on the Pappus configuration in Cone(A₂) (≤ 1/3 by Lemma 6.1 of `q1-notes.md`); coinciding hubs at
  nodes in 𝒞_N (the referee's configuration R_r = D_d: only one merge has spread hubs, flat value at best); flat
  hubs with fins or bent flats (flat value, Lemma 2.1); pod × ℝ^M (a product). The executor's searches in
  𝒞_3(F₂), 𝒞_3(F₃) land on 36 exactly.
- **Limit value 0.5857 for cyclic nets.** Nothing here confirms or refutes it. The quotient construction of
  `q1-notes.md` Cor. 2.2 needs an elementary abelian quotient of rank ≥ 2 and gives nothing for Z_g.

---

## 5. Specs

- **C1 (referee, 1 h).** Lemma 2.1, Lemma 2.2; §3 steps 1–5 (press on step 4: the lune computations and "a local
  geodesic of length π is a geodesic"); validity of the relaxation (§1.1), in particular convexity of the feasible
  set and Jensen at barycentres.
- **C2 (stronger relaxation, open-ended).** Keep `relax.py`, add the legs as points at distance T from a base point
  with |x_e y_e| = 2T exactly (always possible by gluing rays), variables F_ε(p) = (D(leg_ε,p) − T²)/(2T), the points
  c_{e,τ} on the leg line with D(z, c_{e,τ}) ≤ (T−τ)F_x(z) + (T+τ)F_y(z) + τ² (CN on [x,y]), CN of the legs against all
  midpoints F(m) ≤ ½F(p) + ½F(q) − D(p,q)/(8T), and the objective bounded by chords of the square root. This carries
  the parallel-set information (W(z) = T(F_x+F_y)(z) − u(z)² is the squared transverse distance to the line) that the
  far-leg version loses. Whether it cuts below 19.09 is unknown; run T = 10³, τ ∈ {0, ±¼, ±½, ±1/√2, ±1}.
- **C3 (existence side).** Search for a CAT(1) 2-complex Λ as in §3 step 6 for some φ₀ ∈ (π/4, π/2), or prove there is
  none; this decides the tripod branch.
- **C4 (trees first).** Conjecture 5.3 of `notes.md` (Γ_trees(Δ₃) = 36) is still unproved; a proof for trees would
  show which inequality is tight on the nine-tripod product and is the natural candidate for the missing chain.
