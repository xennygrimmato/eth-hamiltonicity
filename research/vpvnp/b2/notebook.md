# b2 notebook: the VP ≠ VNP price framework applied to direction B (Δ₃, three merges)

24 Nov 2026. Source: Anthropic, "VP ≠ VNP over every field" (paper.txt in the scratchpad: §2.1–2.2, App. A–D).
Our side: `engine3-STATUS.md`, `engine3-delta3-proof.md` (Theorem 1), `engine3-open-door.md` §1.6–1.7, §2.3, §3.2, and
`pieces.md` §2.3 (the rectangular cost function).

Tags: **[R]** proved here, **[K]** known (cited), **[N]** computed, **[C]** conjecture.
**[R|FH]** means proved assuming the paper's *flat hypothesis* (Def. D.1), and **[R|PH]** means proved assuming only the weaker
*planar hypothesis* PH: "every finite subset of the Euclidean plane is a price".

Scripts in this folder: `metric_lp.py` (LP over all metrics), `euclid_opt.py` (Euclidean configurations, local optimisation),
`far_opt.py` (far-leg reduction), `spider.py` (tree-like prices), `verify_flat.py` (exact finite-M check of the flat-case
constructions). Outputs: `e6_012.out`, `e6_01.out`.

## 0. Verdict

1. **Q1 [R].** Theorem 1 is the special case of the price method that uses one *star price*: put every leg at its group's point
   of a tripod metric. Over ℂ the star price is the uniform CVZ functional. Over every field, Strassen's upper support functional
   works directly (§2); with the paper's Prop. A.5/A.7 it even gives a genuine spectral point. So the flag on Theorem 1 can be
   lifted: it holds over every field, with [K] input only from Strassen 1991.
2. **Q2: yes in the flat case, and it is much stronger than ρ ≥ 1/2.** The main result is the *flat floor* (Theorem 3 below).
   - **Statement [R|FH].** Take a configuration with E edges, each crossing every one of p merges. Every identity
     Σ_{i≤T} A_i = d·f_C with T = 2^{o(λ)} has a piece with c_k(A_i) ≥ Eλ/√p − o(λ) for every merge k at once.
   - **Δ₃ with three merges [R|PH].** Every family has V ≥ 3√3·λ, so ρ ≥ 1/√3 ≈ 0.577 > 1/2. Under FH a single piece costs
     ≥ 3√3λ under all three merges at once.
   - **Δ₃ with two merges [R|FH].** Some piece has min(c_row, c_col) ≥ (9/√2)λ ≈ 6.36λ. The best previous floor was 4λ (the
     flattening floor). This also gives φ ≥ 6.36, i.e. it settles the min-floor part of (A) in the flat case.
   - **The rectangle crossing F_{n1,n2} [R|PH].** Every family has max_i (c_row + c_col) ≥ 2√(λ1² + λ2²) − o(λ). That is *exactly*
     the App. B / Fock upper bound of `pieces.md` §2.3, on the whole curve. So, under PH, ρ = 1/√2 is optimal for
     Anthropic's rectangle levels.
   - **Unconditional part.** What the method gives without FH/PH is the flattening floor, and the reason is clean.
     - Prices on a line or a tree reproduce exactly the known 4/9 [N].
     - CAT(0) curvature alone forbids the "all merges full" metric that an LP over all metrics finds, but it proves nothing by
       itself.
     - The lower bound comes from *flatness*: Pythagoras lets one edge direction see three orthogonal hub displacements, each at
       cosine 1/√3.
3. **Q3 [R, short].** The contracting-case bound is about Φ, through a diagonal argument. It says nothing about f_{k,ℓ} = P_K or
   about the engine's rate: no tensor statement for f_{k,ℓ} comes out of it, and a bound of that strength would be false for
   f_{k,ℓ} in the engine's regime (§5). The useful link runs the other way: **a trade beating the flat floor would prove the
   contracting hypothesis over that field.** For example ρ < 1/√2 on the crossing, or ρ < 1/√3 on Δ₃ with three merges.

**What this means for direction B.** If the field is in the flat case, or merely satisfies PH, these levels cannot reach
ρ < 1/2: two-merge levels made of crossings and Δ₃ with three merges. Their exponent is then pinned at α′ ≤ 1/2 (rectangles) and
≤ log₂√3 ≈ 0.79 (Δ₃ with three merges). Under FH any level all of whose configurations have every edge crossing every one of
p ≤ 4 merges has ρ ≥ 1/2. So α′ > 1 needs p ≥ 5 merges, or configurations with edges internal to some merges, or the
contracting case. The door does not close unconditionally, but it is now conditional on the open dichotomy of the VP paper.

## 1. The price method for pieces (the multi-hub form of lem_hubs) [R, from K]

**Facts used [K, paper App. A].**
- A *spectral point* φ on a finite party set is multiplicative, has φ(1) = 1, and is subadditive on covers. A *cover* of s is
  s = Σ_j s_j with each s_j a restriction of t_j.
- On a wire, φ(⟨q⟩_{uv}) = q^{d_φ(u,v)}, where d_φ is a pseudometric with values in [0,1] (lem_exponents, Lemma A.2).
- A *price* is a pointwise limit of c·d_φ (Def. A.4). Prices are pseudometrics and are closed under pull-back, scaling and
  limits.
- Every price embeds in a CAT(0) price space (Prop. C.3, from the curvature theorem C.1).
- FH: every finite Euclidean set is a price (Def. D.1). By Theorem D.2, FH or the contracting hypothesis holds over every field;
  which one is unknown.

**Lemma 1 (network routing) [R; the K_r version of Lemma A.3].** Fix a merge with groups G_1, …, G_r. Let A be a D1 network on
the groups with bonds d_{GG′}, a tensor on the legs (strings) ℓ of the configuration, each leg of dimension N = 2^λ. Then A is a
restriction of the graph tensor Π_ℓ ⟨N⟩_{ℓ, o_{G(ℓ)}} · Π_{G<G′} ⟨d_{GG′}⟩_{o_G o_{G′}}, with one new hub party o_G per group.
*Proof.* The node tensor W_G(bonds; legs of G) is read as a functional at o_G on its wire ends, exactly as in the proof of
Lemma A.3. ∎

Let φ be a spectral point on the legs plus all hubs of all merges. Let A_1, …, A_T sum to d·f_C, where f_C = Π_e ⟨N⟩_e is the
product of the edge wires. Write |·| for c·d_φ, which we take to be within ε of a target price.
- **Selection.** By lem_exponents and subadditivity, some i has log φ(A_i) ≥ λ Σ_e d_φ(e) − log T.
- **Upper bound for every merge k, for that same i:** log φ(A_i) ≤ λ Σ_ℓ d_φ(ℓ, o^k_{G_k(ℓ)}) + δ_k(φ)·c_k(A_i), where δ_k is the
  largest hub–hub distance of merge k.
- Multiply by c. The scale c depends only on the finite configuration and on ε, not on λ. Since T = 2^{o(λ)}, this gives

  **c_k(A_i) ≥ λ (L − H_k)/δ_k − o(λ)  for all k at once,**  where L = Σ_e |e| and H_k = Σ_ℓ |ℓ, o^k_{G_k(ℓ)}|.   (★)

One price yields one piece with the lower-bound vector b = ((L − H_k)/δ_k)_k. Several prices yield several pieces. The adversary
mixes them, so V/λ ≥ max over x ∈ conv{b's} of min_k x_k. If the configuration has a symmetry group acting transitively on the
merges, applying it to one price and averaging gives **V/λ ≥ (Σ_k b_k)/p.** Δ₃ has such a group: the stabiliser of the
anti-diagonal class in AGL(2,3) acts on rows, columns and diagonals as S₃.

**Far-leg reduction [R].**
- Place the two legs of edge e at p_e ± M u_e, with u_e a unit vector, and let M → ∞.
- Then |p + Mu − h| = M + ⟨u, p − h⟩ + O(1/M), so L − H_k → Σ_e ⟨u_e, h^k_{G_k(e⁺)} − h^k_{G_k(e⁻)}⟩.
- The centres p_e drop out. With hubs normalised to δ_k ≤ 1, the method's best value at fixed hubs is
  Σ_k b_k = Σ_e |Σ_k Δ^k_e|, where Δ^k_e = h^k(e⁺) − h^k(e⁻).

## 2. Q1: Theorem 1 in price language [R]

**Theorem 1 (restated).** Under a merge with r ≤ 3 groups, every family has a piece with c_k ≥ Eλ − O(log T).

*Price proof.* Take the star price: points P_G with |P_G P_{G′}| = θ_G + θ_{G′}, θ uniform. Pull it back to the legs (leg ↦ its
group) and put the hubs o_G at P_G. Then H_k = 0, L = E·(2θ) and δ_k = 2θ, so (★) gives c_k ≥ Eλ. Mixing the full pieces of the
two merges gives V ≥ Eλ/2. This is Theorem 1. For two groups the star price is just the cut metric of one flattening.

**Over every field (lifting the flag) [R from K].** The argument never needs a spectral point, only an *upper functional* in the
sense of App. A.4 whose value on f_C is known exactly. Let ζ^θ be Strassen's upper support functional [K: Strassen, J. reine
angew. Math. 413 (1991)]. Its properties:
- monotone under restriction;
- ⊕-additive, hence subadditive on covers;
- submultiplicative;
- ζ^θ(⟨q⟩_{uv}) = q^{θ_u+θ_v};
- on oblique tensors (every graph tensor is free, hence oblique) it equals the lower support functional, so it is multiplicative
  there.

The chain is ζ(f_C) ≤ Σ_i ζ(A_i) ≤ T·max_i ζ(hub tensor) = T·max_i 2^{(2/3)c_k(A_i)} for three groups. This is the whole proof over
every field.

If one wants an honest spectral point anyway, apply the paper's Prop. A.5 (prop_gauge) with the "respects the triple" trick of
Prop. A.7 to p = ζ^θ and C = the product of all wires. This yields φ ≤ ζ^θ with φ(C) = ζ^θ(C), hence d_φ(u,v) = θ_u + θ_v on
every pair. So **star metrics are prices over every field.**

**What the framework adds.** It does not add a cleaner proof of Theorem 1 itself; it is the same proof. It does add three things:
- the realisation that Theorem 1 is the zero-dimensional (tree) case of a method;
- the dichotomy that supplies Euclidean prices;
- with those, the much stronger flat floor (§3).

## 3. Q2: the flat floor and Δ₃

**Theorem 3 (flat floor) [R|FH].**
- *Hypotheses.* C is any configuration with E edges of λ bits, every edge crossing every one of the merges P_1, …, P_p (any
  number r_k of groups). Σ_{i≤T} A_i = d·f_C with d ≠ 0 and T = 2^{o(λ)}.
- *Conclusion.* Some i has c_k(A_i) ≥ Eλ/√p − o(λ) for all k simultaneously.

*Proof.*
- Work in ⊕_k ℝ^{r_k−1}, an orthogonal sum. Put the hubs of merge k at the vertices of a regular simplex of side 1 in block k.
- An edge e crosses merge k, so Δ^k_e is a vector of length 1 in block k. The blocks are orthogonal, so |Σ_k Δ^k_e| = √p.
- Take u_e = Σ_k Δ^k_e/√p. Then ⟨u_e, Δ^k_e⟩ = 1/√p for every k and every e, so each b_k → E/√p.
- By FH, the finite set (legs at ±M u_e, the hubs) is approximately a price c·d_φ with error ε. Apply (★), then let M → ∞ and
  ε → 0. ∎

*Exact finite-M check [N, `verify_flat.py`].* On Δ₃, M = 10⁶: p = 1 gives b = 9; p = 2 gives (6.36396, 6.36396) = 9/√2;
p = 3 gives 5.19615 three times, which is 3√3.

**Corollaries.**
- (a) Δ₃ with three merges: ρ ≥ 1/√3 [R|FH]. With the planar configuration below it is [R|PH] for the game value.
- (b) Δ₃ with two merges: min-floor φ ≥ 9/√2 ≈ 6.364 [R|FH]. The previous bound was 4, the flattening floor; the known upper
  bound is 9 − 0.585, from the straightened-edge family. Consistency: for the straightened family f = R + C, the selected piece
  must be C. That is fine, because Theorem 1 already forces C to be row-full.
- (c) For a p-merge level whose configurations all have every edge crossing every merge: ρ ≥ 1/√p [R|FH]. This beats
  pigeonhole (1/p) for every p, reaches 1/2 at p = 4, and needs p ≥ 5 for α′ > 1.

**Rectangular crossing (sharp) [R|PH].**
- *Configuration.* Wires x–v (λ1 bits) and y–u (λ2 bits). Rows are {x,y} | {u,v}; columns are {x,u} | {y,v}.
- *Hubs.* Row hubs at ±a/2, column hubs at ±b/2, with |a| = |b| = 1 at an angle θ.
- *Edge directions.* u₁ = (a+b)/|a+b|, u₂ = (a−b)/|a−b|.
- *Bound.* (★) gives c_row + c_col ≥ λ1|a+b| + λ2|a−b|. Since |a+b|² + |a−b|² = 4, the best angle gives exactly 2‖(λ1,λ2)‖₂. This
  was checked numerically for (1,1), (1,½) and (1,0.1).
- *Comparison.* `pieces.md` §2.3 proves the upper bound c ≤ 2‖λ‖₂ by App. B / Fock pieces. So under PH the rectangular cost
  function is exactly 2‖λ‖₂ and **App. B is optimal**. Two remarks:
  - The match on the whole curve is the strongest sanity check of the method: any error in (★) of the wrong sign would have
    contradicted App. B.
  - It also explains why "Fock is second-order tight at the axes": the price norm is ‖·‖₂.

**Δ₃ in the plane [N + R|PH].**
- *Optimum.* The far-leg optimum in ℝ² is already 9√3 (`far_opt.py`, m = 2). It is attained with every merge's hubs on one
  equilateral triangle {A, B, C} of side 1:
  - rows 0, 1, 2 ↦ A, B, C;
  - columns ↦ B, A, C;
  - diagonals (r − c) ↦ A, C, B.
- *Per edge.* Each edge's three hub displacements are two equal unit sides plus one other. Their sum has length √3.
- *Conclusion.* So Σ_k b_k = 9√3. The S₃ symmetrisation of §1 gives V ≥ 3√3λ, i.e. ρ ≥ 1/√3. This configuration is in the plane,
  so it needs only PH (one piece is no longer full in all three merges at once; that version needs ℝ⁶).
- *Two merges in ℝ².* The value is 12, i.e. ρ ≥ 2/3; ℝ⁴ is needed for 9√2.

**Optimality of the orthogonal construction [N].**
- `far_opt.py` (SLSQP, 60 random restarts, m = 2, 4, 6) never exceeds 9√p for p = 1, 2, 3.
- `euclid_opt.py` (general Euclidean positions, no far-leg ansatz, m = 6, 20 restarts each) reaches 15.37 for p = 3 and 12.53
  for p = 2, both below 9√p.
- [C]: the Euclidean optimum of the method on Δ₃ is 9√p, so ρ_flat-method = 1/√p.

**Why the method gives nothing more unconditionally (the clean reason for "no").**
- (i) An LP over *all* pseudometrics (`metric_lp.py`) finds Σ_k b_k = 27, with every merge full. The witness has edges of length 2
  and every leg at distance ½ from each of its three hubs. It is not a price: in a CAT(0) space, equality in the triangle
  inequality forces all hubs of a node onto its edge geodesics, the hubs of all merges coincide, and δ → 0. So curvature is what
  *limits* the method. Curvature can never *produce* a bound.
- (ii) Prices known unconditionally:
  - star metrics (§2);
  - cut metrics (flattenings);
  - segments. The cut metric gives two points at distance 1; its CAT(0) completion contains the geodesic [x, v], which is
    isometric to an interval (Prop. C.3, Lemma C.4(a)). So every finite subset of ℝ¹ is a price over every field [R].
- (iii) With line prices the far-leg optimum on Δ₃ with three merges is exactly 12 [N, 300 restarts]. That gives V ≥ 4λ, i.e.
  ρ ≥ **4/9**, the known flattening floor. On spider (tree) prices a local search also stops at 12 [N, heuristic].
- So the unconditional price method on Δ₃ lands exactly on the flattening floor 4/9. Every gain above it comes from a
  2-dimensional flat. The obstruction is concrete: an edge direction must see the row, column and diagonal displacements at
  cosine 1/√3 each, which needs Pythagoras. On a line or a tree, Σ_e |Σ_k Δ^k_e| ≤ 12. The reason is that a Z₃-labelling has no
  nonzero homomorphism Z₃ → ℝ, so the three displacements cannot be aligned on all edges; this was checked as an exact
  impossibility in the computation of §3 scratch.

**The contracting case.** In it, Euclidean prices may fail to exist (Theorem D.2 proves only the disjunction). Its tools
(Poincaré inequality, laws, trees, cutting) are duality statements: they *produce* covers and identities (Theorem A.6). In our
setting they point to the construction side.
- **Proposition 4 [R].** Over a field k, if some family of pieces beats the flat floor, then k is not in the flat case, so the
  contracting hypothesis holds over k (Theorem D.2). "Beats the flat floor" means: ρ < 1/√2 on a crossing, or (under PH) game
  value < 3√3λ on Δ₃ with three merges, or a family with all pieces below Eλ/√p in some merge.

  This holds even with PH in place of FH for the planar statements: such a family refutes PH.
- So a counterexample to "ρ ≥ 1/2", or even to "ρ ≥ 1/√2 for the crossing", is at least as hard as deciding the VP paper's open
  dichotomy.

## 4. What remains open [C]

- An unconditional proof of ρ ≥ 1/2 on Δ₃ with three merges would need prices of dimension ≥ 2 that exist without FH. One example
  would be the planar hypothesis PH itself. Another would be a weaker statement: "the Euclidean equilateral triangle with nine
  far directions is a price".
- Is PH implied by the failure of contracting at μ = 2, or by explicit points such as quantum functionals (over ℂ)? CVZ
  functionals give only star metrics on wires; I found no explicit spectral point with a planar metric.
- Under FH, is 1/√p optimal? Construction-side counterpart: are there levels with p ≥ 5 merges and every edge crossing all of
  them where pieces reach 1/√p?

## 5. Q3: the contracting-case bound and P_K [R, short]

- **What thm_noacc bounds.** It refutes small circuits for Φ, the weighted-run polynomial of a universal automaton, through
  accelerators and a diagonal argument. The permanent enters only as Φ ≤_proj PERM. No lower bound on f_{k,ℓ}, on its tensor or
  on any spectral value of it is produced.
- **Why it cannot transfer.** A bound of the form 2^{c(kℓ)²/log(kℓ)} cannot hold for f_{k,ℓ} once ℓ ≫ k: brute force gives
  f_{k,ℓ} circuits of size 2^{O(k²ℓ)}, and here log m ≈ kℓ.
- **Engine rate.** The engine's cost 2^{e(K)·K²λ/2} on P_K is therefore unconstrained by the contracting case. The flat-case bound
  log L ≥ ℓk^{3/2}/16 gives e(K) ≳ K^{−1/2}; that is b1's topic.
- **The only interaction** is Proposition 4: engine trades below the flat floor would place the field in the contracting case.

## Log

- 0:00–0:25. Read STATUS, Theorem 1, open-door §1.6–1.7, §2.3, §3.2, and paper §2.1–2.2 and App. A–D.
- 0:25–0:40. The LP over all metrics gives 27, the "no trade" metric. Dead end: it is not CAT(0).
- 0:40–1:05. Euclidean local search finds about 15 for three merges and about 12.5 for two. A symmetric ansatz with legs pushed
  outwards gives the far-leg limit 3√3 per merge; derived the far-leg reduction.
- 1:05–1:20. Rectangle check: the bound equals App. B's 2‖λ‖₂ exactly. Planar Δ₃ gives 9√3. Line and spider prices give 12,
  i.e. 4/9.
- 1:20–1:40. Verification script, Q1 lift over every field, notebook, comic.
