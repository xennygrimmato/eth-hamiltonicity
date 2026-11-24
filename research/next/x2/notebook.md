# x2 notebook: the exponent ω through "price geometry"

24 Nov 2026. Sources:
- VP≠VNP paper (scratchpad `vpvnp/paper.txt`): Lemma A.2, Lemma A.3, Def. A.4, Prop. A.5–A.8, Thm A.6, B.3, D.1–D.3.
- OpenAI, "An upper bound of 9/4 for the matrix multiplication exponent" (oamath `preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/paper.pdf`; text in scratchpad `mm94.txt`).
- Our notes: `research/vpvnp/c1`, `research/vpvnp/b2`, `research/engine3-literature.md` §1.6 (Zhou).

Tags: [R] proved here, [K] known (cited), [N] computed (`checks.py`), [C] conjecture.

## 0. Verdict

**The dichotomy is not decided.** Price geometry cannot see ω, and there is a clean reason for it.
1. Every 3-point pseudometric is, up to scale, the metric of a genuine spectral point (a quantum functional on a tripod).
2. Prices form a cone, so they keep the *shape* of d_φ and throw away its *scale*. ω is a statement about the scale of a
   normalised point (d ≤ 1, g(123) = 1).
3. Every inequality that comes from rank upper bounds, i.e. from routing through unit tensors and hubs, already holds in every
   pseudometric space. So no rank bound — ω ≤ 2.3714, OpenAI's 9/4, Zhou's K_n bounds — puts any constraint on prices.

Hence neither the flat hypothesis nor the contracting hypothesis can contradict a known bound on ω or on asymptotic ranks.
Neither one implies any bound on ω either, at least through any argument that uses only prices.

OpenAI's 9/4 proof *is* a dual, perimeter-type argument. It uses no curvature. It works with Strassen's additive,
normalised characters and with the non-graph tensor of polynomial multiplication (§4).

## 1. The dictionary (Q1)

**[K] Lemma A.2.** For a spectral point φ (in the paper's class) on I, φ(⟨q⟩_P) = q^{g(P)}, with d(u,v) = g({u,v}) ∈ [0,1].
These satisfy the triangle inequality and g(P) ≤ (the length of any tree on P).

**[R] Perimeter formula.** ⟨n,n,n⟩ = ⟨n⟩₁₂⟨n⟩₂₃⟨n⟩₁₃, and φ is multiplicative, so log_n φ(⟨n,n,n⟩) = d₁₂ + d₂₃ + d₁₃ =: Per.
This is exactly OpenAI's (2.3)–(2.4): B_X(m) = x·Σ yᵢzᵢ is the wire ⟨m⟩_{YZ}, so p_X = d(Y,Z) and λ(T_m) = m^{p_X+p_Y+p_Z}.

**[R] Per ≤ ω·g(123) ≤ ω for every point in the paper's class.**
- From R(T_n^N) ≤ n^{(ω+ε)N}, T_n^N is a restriction of ⟨n^{(ω+ε)N}⟩_{123}.
- Also Per ≥ 2g, because the asymptotic subrank of T_n is n² [K, Strassen] and φ is monotone under degeneration
  (OpenAI Lemma 2.3).

**[R] ω = sup Per over normalised (Strassen) characters on 3 parties.**
- This is Strassen duality [K Str88], or Thm A.6 applied to C = T_2^b, A = ⟨2^a⟩_{123}.
- In the paper's class, ω = sup Per/g(123).

**[R] The known region for normalised points is exactly {d ∈ [0,1]³ : 2 ≤ Per ≤ ω}.**
- The triangle inequalities and the tree bound d_uv + d_vw ≥ g = 1 are already *implied* by d ≤ 1 and Per ≥ 2.
  For example, d₁₃ + d₂₃ = Per − d₁₂ ≥ 1 ≥ d₁₂.
- The slice Per = 2 is exactly the set of quantum functionals F^θ, with d_uv = θ_u + θ_v and Σθ = 1 [K, CVZ]. All of it is
  realised.
- Points with Per > 2 have tripod weights θ_u = Per/2 − d_vw ≥ 0 that sum to Per/2 > 1.
- OpenAI's theorem, if correct, says Σθ ≤ 9/8.

**[R] Every 3-point pseudometric is a price, unconditionally.** Every 3-point metric is a tripod: set
θ_u = (d_uv + d_uw − d_vw)/2 ≥ 0 ([N] check 3). After scaling θ to a probability vector, d = c·d_{F^θ}.

Consequences:
- No inequality valid for prices, however it is derived, can restrict the triangle (d₁₂, d₂₃, d₁₃) beyond the triangle
  inequality. This includes the crossing inequality B.3, CAT(0), the hub lemma, and pulling back to sub-parties or larger
  networks that contain ⟨n,n,n⟩^{⊗k} regrouped.
- Splitting parties into sub-parties is a pull-back, so the sub-parties sit at distance 0. The extensions of A.8 / C.3 add hubs,
  but the 3-point restriction is still a tripod. B.3 bites only on non-tree configurations: c1 found the gap is 0 on trees.

**[R] Graph tensors on 3 parties.** For graph tensors s, t on 3 parties: s^N is covered by 2^{o(N)} restrictions of t^N
(paper Thm A.6) ⇔ every vertex degree of s is ≤ the corresponding vertex degree of t (flattening domination).
- (⇐) The length in a tripod metric is Σ_v θ_v deg(v), and every 3-point metric is a tripod. So length(s) ≤ length(t) for
  all φ, and Thm A.6 applies.
- (⇒) Use the flattening ranks.

So matrix multiplication is "price-trivial" among graph tensors. ω enters only through the unit tensor ⟨q⟩₁₂₃, which is not a
graph tensor.

## 2. Dual upper bounds on Per from curvature/hub/crossing inequalities (Q2)

**[R] Lemma (rank bounds are invisible to metrics).** Take:
- a graph tensor t on V with log-weights w_e;
- any grouping of V into groups G (for example 3 groups, so that the grouped tensor is a rectangular MM);
- any upper bound r on the rank of the grouped tensor;
- hubs o_G anywhere, and a central hub o.

The routing inequality from Lemma A.3 (with ⟨r⟩ among the group hubs replaced by a star at o) is

  Σ_e w_e|u_e v_e| ≤ Σ_p deg(p)|p o_{G(p)}| + log r · Σ_G |o o_G|.

It holds in **every** pseudometric space.

*Proof.* Route each crossing edge u → o_{G(u)} → o_{G(v)} → v and each internal edge through its hub. What remains is
Σ_{G<H} W_{GH}|o_G o_H| ≤ Σ_G deg_G·|o o_G| ≤ (max_G deg_G)·Σ_G|o o_G|. Here max_G deg_G is a flattening exponent of the
grouped tensor, so it is ≤ log r. ∎ ([N] check 2: 3000 random metric spaces, 0 violations.)

Consequences [R]:
- The ungrouped triangle case reads Per ≤ ω·FW(1,2,3). In every metric space FW ≥ Per/2, with equality on tripods; [N] the
  Euclidean supremum of Per/FW is 2 (degenerate triangles), and the equilateral triangle gives √3. So the inequality is
  equivalent to ω ≥ 2 and gives nothing.
- The bound R̃(K_k) = 2^{k²/4} (Zhou [K, engine3 §1.6]) is a rank bound of the same kind. It gives Σ_{u<v} d_uv ≤ k²/4 for
  *normalised* points, which is a constraint on scale, not on prices.

Every candidate network (K_k, the tetrahedron, MM regrouped into more parties, 3-hub routing) gives **no upper bound below
3 on the shape**. The bound d ≤ 1 is the only scale information a price ever had, and prices discard it.

The crossing identity B.2 is a cover between graph tensors. It produces genuinely non-metric constraints (CAT(0)), but on
3 points it is void (§1).

**Why a dual ω bound must leave price geometry [R].** Every inequality the paper proves about prices is positively
homogeneous in the distances (A.8, B.2/B.3, C.1, C.4, Def. D.1). Per ≤ ω is not homogeneous: it is relative to the
normalisation g(123) = 1. A dual proof has to track an invariant that a price does not record:
- the unit-tensor exponent g, or
- additivity on direct sums.

OpenAI uses the second. Its Corollary 3.2 needs λ(A^{⊕5M}) = 5M·λ(A) and λ(⊕ blocks) = Σ λ(blocks). The paper's class has
only subadditivity, so that argument does not run there as written.

## 3. Lower bounds; the flat and contracting hypotheses (Q3)

- **The equilateral triangle.** It is a price under *no* hypothesis: it equals (3/2)·d_{F^(1/3,1/3,1/3)}, where the quantum
  functional F^(1/3,1/3,1/3) has side 2/3 and Per = 2.
  - The paper's normalisation is d_φ ≤ 1 together with a free constant c in c·d_φ. Def. A.4 allows any c ≥ 0, and φ^a
    (0 < a ≤ 1) is again a spectral point.
  - "Equilateral side 1 = d_φ" for an *unscaled* φ would mean Per = 3 ≤ ω, which is false. Realising it as a price only
    needs c ≥ 3/ω.
  - What blocks ω = 3 is exactly this scale freedom.
- **Flat hypothesis ⇒ ω?** Nothing. It is a statement about the cone of prices. Realising a Euclidean X as c·d_φ only forces
  c ≥ max over triangles of Per(X)/ω, and more generally c ≥ length_X(t)/log R̃(t). Nothing bounds c above: Theorem D.2 is a
  compactness argument with no control on scale.
- **Contracting hypothesis ⇒ ω?** Nothing, for the same reason. It is homogeneous in D(·).
- **Contradiction with known bounds?** Checked carefully: **none is possible through prices.**
  - Known upper bounds (CW-type ω < 2.3714; OpenAI 9/4; Zhou K_{2m}; CVZ / Christandl–Zuiddam cycle bounds) are rank bounds.
    By the §2 Lemma they hold in every pseudometric space.
  - Known lower bounds (flattening, subrank = min-cut) are realised by cut and tripod metrics, which are prices
    unconditionally.
  - Only graph→graph *covers* that are not routed through unit tensors (such as B.2) can constrain prices, and no such cover
    involves ω.
- **[R] Reformulation of ω > 2.** ω > 2 ⇔ some normalised φ has g(123) = 1 < Per/2 ≤ FW in every extension. In words: the
  unit tensor is strictly cheaper than any hub star.
  - Suppose one could show that g(S) ≤ Fermat–Weber(S) in the CAT(0) price space, *with the normalisation preserved*. Then
    ω = 2 would follow, since Per/FW ≤ 2.
  - The paper does not give this. A.7/A.8 preserve g only at random hubs placed on old points, which gives just the tree
    bound. C.3 loses the scale.

## 4. What OpenAI's 9/4 actually does with spectral points [K, read]

- It uses Strassen characters λ (additive, multiplicative, monotone, normalised), with p_X, p_Y, p_Z = wire exponents and
  t = Per/3.
- It forms the profile P(a,b) = Π_{π∈S₃} λ_π(C(a,b))^{1/(6t)} of the polynomial multiplication tensor C(a,b). This tensor
  has rank a+b−1 and is not a graph tensor.
- Two degenerations, combined with the shared-leg separation (Prop. 3.1, which is Fourier plus weights) and the entropy
  Corollary 3.2, give:
  - concavity, 2P(a,b) ≥ P(a,b+1) + P(a,b−1);
  - tripling, P(a,3h+a−1) ≥ 3P(a,h).
- Together with P(1,b) = b these force P(a,a) ≥ a^{4/3}. Comparing with P ≤ (2a−1)^{1/t} gives t ≤ 3/4, i.e. Per ≤ 9/4.
- In our language this is a perimeter bound for every normalised spectral point. It is proved by a profile/growth argument on
  a non-graph tensor, not by geometry of the wire metric.
- The number 9/4 is the case n = 3 of Zhou's n²/4 bound for K_n, which uses the same method (engine3 §1.6).
- I did not verify the proof. It contradicts nothing in this notebook: Per ≤ 9/4 is a scale bound.

## 5. Concrete inequalities linking ω and the geometry (Q4)

1. [R] Per(d_φ) ≤ ω·g_φ(123) ≤ ω for every φ in the paper's class, and for every triple of parties of a spectral point on
   any V. Equivalently, the unscaled spectral metrics have all triangle perimeters ≤ ω. Under OpenAI's theorem this reads
   ≤ 9/4.
2. [R] If c·d_φ realises a configuration X (flat case), then c ≥ max_{triangles} Per_X/ω, and more generally
   c ≥ length_X(t)/log R̃(t) for every graph tensor t. These are lower bounds on c only, and c is unconstrained above.
3. [R] g(123) ≥ Per/ω. A spectral point that realises a Euclidean equilateral triangle of side s has g(123) ≥ 3s/ω
   (≥ 4s/3 under 9/4) and g(123) ≤ 2s (tree bound). This interval is nonempty for every ω ≥ 3/2, so there is no
   contradiction.
4. No inequality between ω and the flat/contracting dichotomy follows from the paper's toolkit [R, by §1–§2 and homogeneity].

## Run log
`python3 -I checks.py`:
1. sup Per/FW over Euclidean triangles = 2.0000 (degenerate triangles; √3 at the equilateral triangle).
2. 0 violations of the routing inequality in 3000 random metric spaces.
3. All tripod weights ≥ 0.
