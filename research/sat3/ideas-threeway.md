# ideas-threeway: candidates for a three-way identity on 3-nets, first-pass verdicts

26 Nov 2026. Nothing here is committed, machine-checked or refereed. Notation and inputs as in `notes.md`
(K-AN = the VP ≠ VNP paper; M = Majdoddin, arXiv:2610.41622, §4). Tags: [R] proved here, [D] derived, unreviewed,
[N] numerical (script named), [C] conjecture, [X] dead with reason.

Units: costs of a term are normalised by the trivial cost of the configuration, c ∈ [0,1]³; a *law* is the set C of
cost vectors of a family; value V(C) = min_{q∈Δ₃} max_{c∈C} ⟨q,c⟩ (= max_C mean(c) for symmetric C).
Target: V < 1/√2 = 0.7071. Filters: F1 (V ≥ 0.6124 on large nets, ≥ 2/3 on Δ₃ unless contracting), F2 (no
projector families on finite shells), F3 (small sizes say nothing about values), F4 (M Prop. 4.23: pieces must
couple different bundles).

Scripts: `ideas/third_point.py` (outputs `ideas/third_point_*.out`).

## 0. Ranked list

| # | candidate | value it would give | filters | verdict |
|---|---|---|---|---|
| 1 | Nested two-way crossings, arbitrary depth (N) | = sup over CAT(0) placements, ρ_CAT ∈ [0.6124, 0.7071] on nets, [2/3, 0.7071] on Δ₃ | passes F1 automatically and unconditionally, F2, F4 | OPEN, the only candidate not killed; decided by a metric question (Q1 over all CAT(0) spaces, §3). My guess [C]: ρ_CAT → 1/√2, i.e. dead |
| 2 | Three-wire fusion on a ladder of count exponent α (w1's door) | 3^{α−1}; F1 gives the new lower end α ≥ log₃2 = 0.631, so window α ∈ [0.631, 0.685); α = 2/3 (2D ladder) gives 0.693 and passes F1 | F1 ok, needs 2D pole wires | no construction; dead in the two classes w1 checked; F1 does not exclude it [C] |
| 3 | Three-point ("tripod") ladder: one variable, expansions at three points of P¹ | complementary law c_k = F(n_k), Σn_k = 2: (2/3)^α; 0.816 for partition ladders; < 1/√2 only for α > 0.855 | F1 ok for every concave F | the third ladder EXISTS in App. B at X = ±1 for the third matching cut [N, exact]; as a source of gain [X] for α = 1/2 (K₄: never below trivial; nets: 0.816) |
| 4 | Idealised tripod-indexed law (three arms, sum-preserving) | max(t, 2/3), t the central term | on the F1 boundary | no identity; arms with the two-way 1:1 trade bulge to 0.759 [R]; needs trade rate 1 : (½,½) |
| 5 | Shifted sphere c_k² = t + (1−t)n_k | √((1+2t)/3); window t ∈ [1/6, 1/4) | violates w1's conjectural c₁ ≤ c₂ + c₃ exactly on the window | [X] if that conjecture holds |
| 6 | Product of two-way problems (direction 4) | ≥ 1/√2 always; uniform split (1+√2)/3 = 0.8047 | — | [X] [R] |
| 7 | Rewiring covers (pieces = wires along merge-class lines) | 2θ/3 with θ ≥ √(3/2) under Euclidean prices: ≥ 0.816 | — | [X under FH] |
| 8 | Direction decomposition of a wire over F_q² (c) | 1 | commuting projectors: counting trap | [X] [R] |
| 9 | Pfaffian / three-term Plücker on K₄ (b) | — | finite version = SU(2) recoupling (F2); Gaussian version = same ladder as App. B | [X] finite; Gaussian: not separately covered by the old no-go, but see #3 for what the existing determinant already contains |
| 10 | Laser-type grouping of powers of a finite identity (direction 5) | log Σ_j Π_k R_k(π_j)^{q_k} / log(trivial) | — | not a mechanism; gives a finite criterion (§8) |
| 11 | Sphere laws, A₂ form X·Y·Z = 1 | 1/√3 | fails F1 | [X] unless contracting |

No candidate with a computed value below 1/√2 survives.

## 1. Direction 4: product of two-way problems [R]

Wires split in fractions f_12, f_13, f_23; on part (k,l) a two-way term θ costs (cos θ, sin θ) in merges k, l and
τ in the third merge m.

1. Constant τ: V(f,q) = Σ f_kl (√(q_k²+q_l²) + τ q_m). Uniform f: (√2 + τ)/3; τ = 1 gives 0.8047; below 1/√2 iff
   τ < 1/√2; τ = 0 is K₄ (√2/3, z1's three-rank object). V is linear in f, so the best f is pure: min(1/√2, τ).
2. **Lemma 1.1.** For every tensor A on the four nodes of a generic rectangle of the pair (k,l) (four distinct
   groups of merge m): c_m(A) ≥ max(c_k(A), c_l(A)).
   *Proof.* A network on four groups costs ≥ ½Σ_x ρ_x (ρ_x the log-rank of party x against the rest; every bond
   has two ends). rank(ab|cd) ≤ ρ_a+ρ_b and ≤ ρ_c+ρ_d; rank(ad|bc) ≤ ρ_a+ρ_d and ≤ ρ_b+ρ_c. ∎
   Hence each factor is, for every q, at least a two-merge problem with weights (q_k + s q_m, q_l + (1−s) q_m), and
   the product has V ≥ 1/√2 for all f, q (for circle-law families: θ = π/4 everywhere; for arbitrary two-way
   families whenever the two-merge floor holds).
3. K₄-type positions (rectangle of (k,l) with both wires internal to m) are a fraction ≤ 3/(g+1) of a net level
   (characteristic 2 only) and ≤ 3/K of any level with groups of size ≤ K [D]. Non-transversal third merges (nodes
   A×B×C×D, merges (a,b), (c,d), (a,c)) are unbalanced, flat floor ≥ (1+√2)/3 [D].
4. Relation to F4: M's class charges rank across pairs of groups and forbids configurations meeting ≥ 3 groups
   of a merge (L3); there the third merge is simply unusable on a rectangle. In our accounting (any network on the
   groups, hubs, time-sharing) it is usable and Lemma 1.1 is what kills it. The two statements agree; F4 does not
   void the calculation. Lemma 1.1 is about tensors on ONE rectangle: it kills products, not nested pieces.

## 2. Structure of Δ₃ in wire terms [R]

- The nine wires w_{s,r} (triangle s, edge r → r+1) are the points of AG(2,3); the three bonds of merge k are the
  lines of one parallel class; the triangles are the fourth class. Two wires of different triangles share a bond in
  exactly one merge. Merge R aligns the triangles, C and D rotate T_1, T_2 by ∓1, ±1. After any merge the level is
  the matrix-multiplication tensor ⟨N³,N³,N³⟩.
- **Node-centred crossings.** No pair of merges is in rectangle position, but for every node n and classes k ≠ l the
  cuts L_k(n)|rest and L_l(n)|rest cross: a′ = {n}, b′ = L_k∖n, d′ = L_l∖n, c′ = the other four nodes; 2λ of wires
  a′–c′, 2λ of wires b′–d′, 2λ straight on each cut. In wire terms: for w_{0,0} = (a,c), w_{1,0} = (b,d) the cut
  ab|cd is the row bond, and the other cut ad|bc has {a,d} = one column group and {b,c} = one diagonal group.
  A term with log-ranks (r, r′) costs r on the row bond and, in each of C and D, between λ + r′/2 (singleton-rank
  bound) and min(2λ, λ + r′) (hub network: bond {a,d}–c of r′ bits and bond b–c of λ bits). Per pair of wires, in
  units 2λ: (x, ≤ min(1, ½+y), same). Endpoint y = 0: (1, ½, ½), a product of two new wires a–d (internal to C)
  and b–c (internal to D), on the plane Σc = 2. One crossing alone: V = 0.9115 (q = (0.69, 0.155, 0.155)).
  This piece is not k-local in M's sense for k = C, D: it couples two bundles through their common group.
- For a tensor on three groups: ½Σ_j ρ_j ≤ c ≤ min_{i≠j}(ρ_i + ρ_j) (triangle network; path network i–l–j).
  "Sum of two" is the path network.
- Restricting to one triangle: every piece restricts to a tensor on three nodes that lie in three different groups
  of every merge, so a family of pieces each exactly a product across the groups of some merge would write
  ⟨N,N,N⟩ as a sum of 2^{o(λ)} rank-one tensors. So the "all corners" family {(0,1,1), (1,0,1), (1,1,0)} of the
  tripod plane does not exist [R].

## 3. (N) Nested crossings: what they can and cannot give [D]

Class 𝒞: families generated by wires, restrictions, hub networks, time-sharing, covers and the crossing cover
(K-AN B.2), nested to any depth (S. Sra's Lemma 4.2 is an instance).

1. Every metric that satisfies all instances of K-AN (B.3) acts as a formal price for 𝒞: each move of 𝒞 is
   bounded by it. Every CAT(0) space satisfies (B.3) for p = q (Theorem 3.2 of `notes.md` holds with arbitrary
   weights λ_k: Σ_k ν_k b_k ≤ E·‖ν‖₂, so (b_1,b_2) lies in the disc); for p ≠ q I rely on K-AN C.1–C.3 [C].
   Hence V_𝒞 ≥ ρ_CAT := sup over placements in CAT(0) spaces of (1/3)Σ_k b_k/E, with no hypothesis.
   Trees are CAT(0), so **F1 holds unconditionally for 𝒞**: V_𝒞(Δ₃) ≥ 2/3, V_𝒞(nets) ≥ 0.6124.
2. Conversely [C] (the analogue of `ports/protocol` Conj. 4.3): V_𝒞 = ρ_CAT in the limit of deep nesting.
3. So nesting beats 1/√2 iff ρ_CAT(3-net) < 1/√2 in the limit g → ∞. This is `notes.md` Q1 with "prices" replaced
   by "all CAT(0) spaces"; it no longer depends on contracting. Lemma 1.1 does not decide it.
4. What I can say about ρ_CAT:
   - Exact equality in Cor. 3.4 is impossible at fixed g: with the tripod of §5.5 at every node, two nodes n, n′ on
     one line of class 3 share o³; the triangle (o³, o¹(n), o¹(n′)) has sides 2h, 2h, δ, and the midpoints of its
     two long sides are the tripod centres, which must be δ/√2 > δ/2 apart for the pair (1,2). But these pairs are
     a fraction 1/(g+1) of the edges, so this says nothing about the limit.
   - The local configuration that equality needs (three pairwise antipodal directions with a common perpendicular
     direction) exists in links of Ã₂ buildings: three pairwise opposite flags (p_i, ℓ_i) with ℓ_1, ℓ_2, ℓ_3
     concurrent; the common point is at distance π/2 from the three flag midpoints. Vertices of the link cannot
     serve (opposite vertices have opposite types). So nothing local forbids ρ_CAT → 1/√2 [C].
   - Cheapest decisive test: maximise the far-leg value over hub placements in (Ã₂ building) × ℝ^M and in products
     of such, for Δ₃ and for the limit model of §5.4; or minimise over finite metrics on hubs and legs subject to
     all four-point CAT(0) inequalities (a relaxation: any value < 1/√2 there proves ρ_CAT < 1/√2).
   If ρ_CAT < 1/√2 the candidate is alive and what is missing is a finite-depth version of K-AN C.2/C.1.
   If ρ_CAT = 1/√2 then no nesting of the two-way identity, of any shape, beats 1/2 [R given item 1].

## 4. Laws (direction 1 and (a)) [R for the values]

| law | value | window where it is in [2/3, 0.7071) (Δ₃) |
|---|---|---|
| sphere Σc² = 1 | 1/√3 | none (fails F1) |
| circle × trivial third | 1/√2 | — |
| ℓ_p: Σc^p = 1 | 3^{−1/p} | p ∈ [2.71, 3.17) (large nets: p ≥ 2.24) |
| shifted sphere c_k² = t + (1−t)n_k, Σn = 1 | √((1+2t)/3) | t ∈ [1/6, 1/4); corner piece (1, √t, √t) violates c₁ ≤ c₂+c₃ iff t < 1/4 |
| fused additive, count exponent α | 3^{α−1} | α ∈ [0.631, 0.685) |
| tripod plane Σc = 2 (c = (y+z, x+z, x+y), x+y+z = 1) | 2/3 | boundary |
| complementary c_k = n_k^α, Σn = 2, n ≤ 1 | (2/3)^α | α > 0.855; any concave F satisfies F1 automatically |
| tripod-indexed, arm k from (t,t,t): dc_k = −ds, dc_l = dc_m = κ ds | max(t, 2/3) if κ ≤ ½; circle-type arms (κ = 1 at the centre) give (2t + √(t² + 4(1−t)²))/3 = 0.759 at t = 2/3 | κ ≤ ½ and t < 0.7071 |

Reading: the conjectural inequality c₁ ≤ c₂ + c₃ says that cost vectors are the pairwise distances of a tripod
(c_k = sum of the two arms other than k). With the pigeonhole piece (c₁ = 1) it gives mean ≥ 2/3 for symmetric
families. The tripod plane is the law of "wire-like" pieces: a wire internal to merge k costs in the other two.
Both natural algebraic laws with partition ladders miss the window from opposite sides: two variables with three
gradings (sphere, 0.577, excluded by F1) and one variable with three points (complementary, 0.816, useless).

## 5. (a) Three points of P¹: the third ladder exists [N, exact mod p]

`ideas/third_point.py`: with Ψ(X) = Σ_N Ψ_N X^N the crossing-identity polynomial of `crossing_identity_modp.py`,
Φ_M := coefficient of (X − 1)^M = Σ_N C(N,M) Ψ_N. Ranks of Φ_M across the third cut ac|bd (both wires internal):

| classes (dims) | M = 0, 1, 2, … |
|---|---|
| (1,6,1,6) (3,3) | 1, 1, 1, 2, 4, 5, 7, 8, 9 (full) |
| (2,12,2,12) (5,5) | 1, 1, 1, 2, 4, 6, 10, 13, 18, 21, 24, 25 (full) |
| (1,8,2,14) (4,8) | 1, 1, 1, 2, 4, 6, 9, 11, 14, 15, 16 (full) |

The same at X = −1; at X = 2 all Φ_M are full on all three cuts. The X^N coefficients are full on ac|bd except
N = Θ/2 in class (2,12,2,12) (rank 15). On the two crossing cuts the Φ_M are full for small M.
So Ψ carries three rank ladders, at X = 0 (cut ad|bc), X = ∞ (cut ab|cd) and X = ±1, i.e. y = 1 (cut ac|bd): the
three matchings of K₄ are three points of P¹, and the evaluation point is the third one. Small sizes; the
asymptotic count of the third ladder is not known.

Consequence [R given the jet bounds]. A piece is ℓ(Ψ) for a functional ℓ on polynomials of degree ≤ Θ; its ranks
are bounded by the jet orders (N₁, N₂, N₃) of ℓ at the three points, and a functional with jet orders (N₁,N₂,N₃)
exists only if N₁+N₂+N₃ ≥ 2Θ − 1 (jets at three points are independent). So the law is complementary, Σn_k = 2:
- K₄: per crossing F(n₁) + F(n₂) + G(n₃) ≥ 2 = trivial for concave ladders (minimum at the corner (1,1,0), which is
  the target itself). App. B pieces are (n, 1−n, 1). No gain; z1's three-rank object would need cancellations that
  the jet bounds do not see. [X]
- Nets: (2/3)^α; 0.816 for α = 1/2. [X]; in the window only for α > 0.855 (level density ε^D with D ≥ 6), where the
  wires would need the same exponent and three of them would have to fuse on one bond. No such object is known.

## 6. (b) Pfaffians on K₄

- The three-term Plücker/Pfaffian relation as a tensor identity is the d = 2 identity δ_acδ_bd − δ_adδ_bc =
  ε_abε_cd (`ports/protocol` §3.4); its powers and symmetric powers are the SU(2) recoupling families (w1 §3). [X]
  by F2 and by the naming trap.
- A Bogoliubov (Pfaffian) Gaussian family has the same bond Fock space as the determinant (x6 row a: class T).
  w1's no-go (Prop. 2.1, Prop. A) is written for number-conserving Möbius generating functions; it does not
  formally cover the O(2∞) case [C: same outcome]. Nothing constructed.
- What §5 adds: the existing determinant already treats the three matchings as three points of P¹, with the
  complementary law. A K₄ identity at the flat floor needs the sphere law (Σn = 1) on a support avoiding the
  corners (w1 §4), i.e. a genuinely two-variable family; a Pfaffian in one variable would again be complementary.

## 7. (c) Direction decomposition of a wire [X] [R]

I = P_const + Σ_{d∈P¹(F_q)} P_d on functions on F_q². The P_d are the spectral projectors of the translation group
on the q+1 punctured lines of the dual plane; they commute. A projected wire has rank q−1 across every cut that
separates its ends, whatever the direction, so nothing is aligned with a merge at the level of one wire, and there
are q+1 = 2^{λ/2} terms. For sums over sets S of pairs (d,d′) on two crossing wires the ranks across both crossing
cuts are exactly |S|(q−1)² (orthogonal ranges), so rank × number of pieces ≥ q⁴: the counting trap of z1 §4 (cosets
of Weyl subgroups: row·col = N²). This is stronger than Donoho–Stark and holds for any number of directions. The
pods behind the floors come from spread sets in the rank metric (Lemma P), not from projector decompositions.

## 8. Direction 5: laser-type grouping gives a finite criterion [D]

Take a finite identity f₀ = Σ_{j≤T} π_j and its n-th power with pieces grouped by type τ (poly(n) pieces). A type
costs ≤ n[H(τ)·(naming) + Σ_j τ_j c_k(π_j)] in merge k, and the adversary's best type gives, by the Gibbs
variational principle, V ≥ log₂ Z(q), Z(q) = Σ_j Π_k R_k(π_j)^{q_k} (R_k the cost of π_j in merge k as a
dimension), with equality when naming costs one index. So tensor powers gain iff a finite identity has
min_q Z(q) < (trivial dimension)^{1/√2}; examples: the d = 2 identity has Z = 4 = trivial; App. B has
Z ≈ 2^{√2λ}·poly. By K-AN A.6 this loses nothing: an asymptotic family exists iff a finite certificate does.
On Δ₃ = ⟨N,N,N⟩^{⊗3} with rotated factors the laser method proper (zeroing out to a subtensor) does not apply: a
cover must keep the whole tensor. [X as a separate mechanism.]

## 9. Other items

- Rewiring covers [X under FH]: pieces that are restrictions of wires along rows, columns, diagonals with total
  w bits have Σ_k c_k = 2w. By K-AN A.6 against Euclidean prices, w ≥ θ·9λ with
  θ = sup mean(d on triangle pairs)/max(d on merge-class pairs) ≥ √(3/2) (three orthogonal centred simplices), so
  V ≥ 2θ/3 ≥ 0.816.
- Direction 2 (Fay, Frobenius–Stickelberger): the genus-0 three-term relation is Plücker (§6). §5 shows that the
  third ladder point coincides with the evaluation point because the target has rank 1 on the third matching cut;
  on a net no cut has this property, so a three-point identity for a net would need a third ladder at a point
  where the polynomial is not the target. An elliptic deformation has room for this (the evaluation point and the
  ladder points are then four points with a modulus), but the law would still be complementary. Not pursued.
- Direction 3 beyond §3: no "Yang–Baxter" closure found; the group generated by the three partner involutions on
  slopes (t ↦ −t, 2−t, t/(2t−1)) is the (∞,∞,∞) triangle group, a free product, so pairwise applications never
  close up on a generic net: the partner graph on slope classes is a quotient of the 3-regular tree.

## 10. Dead ends not to retry

- [X] Mixing the three pairs on disjoint rectangles (§1).
- [X] The all-corners family on Δ₃ (§2).
- [X] Jet-bounded pieces of App. B on K₄ (§5).
- [X] Arms with the circle trade at the centre of a tripod-indexed family (§4).
