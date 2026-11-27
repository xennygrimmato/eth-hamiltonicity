# sat3 / attainment: the three-class crossing game on nets, and what nested crossing covers can and cannot do

Working notes, 26 Nov 2026. Nothing here is committed.

**Referee.** §5 (Theorem W, Lemma S, the class), §1.2, §1.3 and §2 were refereed: `sat3/review-thmW.md`. Lemma S stands
[R there]; its core is in Lean (`ports/lean/PortsLean/Bimedian.lean`, `LemmaS.lean`; note `sat3/lean-lemmaS.md`).
Changes made after the report: (1) Theorem W and everything derived from it is a statement about **certified** costs
and is now worded so ("certified level value"; new paragraph in §5.3); (2) the class is enlarged to all
circle-covering crossing identities — Khoruzhii's identity is a different identity, not a coarsening of B.2, and is
inside for that reason; (3) the leg invariant is repaired (§5.1); (4) the accumulation of ε over a branch: Theorem W
is now stated with zero loss, by a new zero-loss lemma (Lemma 5.3, proved for all energies from a quoted two-sided
bound on p(n) plus exact finite computations, `attain/zeroloss.py`), and with the ε-form as fallback; (5) completeness
in the projection step; table §1.2 row "four different groups" (S = p+q+min(p,q)) and §2.2 (3/2 at p = q); the
triangle case in §1.3; "stuck at exactly 1/√2" replaced by the window with its O(1/g) width.

Tags: **[R]** proved here in full from the cited inputs; **[D]** derived here, proof written, unreviewed;
**[N]** numerical (script named); **[K]** quoted; **[K-unverified]** quoted from third-party texts nobody here has
checked; **[C]** conjecture; **[X]** dead, with reason.

Inputs. AN = Anthropic, "VP ≠ VNP over every field" (`scratchpad/fm/paper.txt`): Lemma A.2, Lemma A.3, Prop. B.2,
Prop. B.3, Lemma C.4. Engine: `research/engine3-open-door.md` §1.3–1.7 (class RM_p, the D1 cost), `ports/c1d1` D1.1,
`vpvnp/b2` (price method (★)). `sat3/notes.md` (floors; Prop. 3.1, Thm 3.2, Cor. 3.4, Thm 5.1). `ports/protocol/notes.md`
(the K_{2,3} game). Majdoddin, arXiv:2610.41622 (`scratchpad/pb/arx/p.txt`). Sra, hexagon:2611.01066
(`scratchpad/hx/pdf/2611.01066.txt`), Khoruzhii (`scratchpad/hx/kh.txt`). The Q1 agent's message on F_CAT (its notes:
`sat3/q1-notes.md`).

Scripts (`research/sat3/attain/`): `game1.py` (level-1 game, one LP per weight vector), `game1sym.py` (the same with
translation symmetry), `inspect1.py` (optimal designs), `lemmaS.py` (depth-2 game in products of pods and lines, conic
duality), `lemmaS_step.py` (stepwise Steiner crossing inequality on random parents; `TIE=1` for degenerate parents),
`zeroloss.py`, `zeroloss_sample.py` (the finite parts of the zero-loss lemma, 60-digit arithmetic). Outputs
in `attain/out2/` (`attain/out/` holds a first run made with a bug in the constant of finite wires; ignore it).

---

## 0. Summary

| Item | Result | Status |
|---|---|---|
| Level-1 game (crossing identity on arbitrary pairs of edges, arbitrary splits p:q, two-hub realisations at groups, per-term choice of merge) on full 3-net levels | value = the two-merge rectangle value, → 1/√2; the third class gives nothing; uniform weights give ≈ 0.75–0.78 | [N], LP, g = 2, 3, 4 (both groups), 5 |
| Calibrations | two merges: exactly the rectangle value for g = 2…5; one merge: exactly raw; K₄ with three matchings: 0.5690 (two-merge corner), uniform weights = raw 2/3 | [N] |
| Δ₃ alone (no rectangles inside) | 0.9085 with two merges, 0.8929 with three (weights (0.6,0.2,0.2)); below the previous 0.935; far above the floors | [N] |
| Why level 1 fails | a crossing piece is not the wire pair: under a merge for which its legs are not aligned it costs more than raw (K₄-network on four groups) | [R] |
| Two-sided cuts on a net | a piece certified across two-sided cuts aligned with two merges lives on a rectangle; with three merges on a K₄ of the net (characteristic 2 only, all edges merge-class) | [R] |
| Sra's nested identity (Lemma 4.2), Khoruzhii's lemma | statements about PT rank = max_i min_cut; the engine needs min_w max_i ⟨w, c⟩; nested terms control 2 of the 2^{k−1} cuts; nothing for nets | [D] |
| Majdoddin Prop. 4.23 | does not apply as a theorem (it charges a bundle-local piece only under its own merge); its mechanism is the reason above | [D] |
| Weak duality, depth 1 | every metric with B.3 (in particular every CAT(0) placement) bounds every level-1 cover | [R] (Theorem W1) |
| Lemma S (Steiner crossing inequality) | in every CAT(0) space: after crossing two wires of a network with free hubs there is an N for which neither child is below the parent's Steiner value | [D], proof in §5.3 |
| **Theorem W** (weak duality for certified costs, all depths) | for every placement in a CAT(0) space, every crossing-generated cover, of any nesting depth, has a term whose **certified** cost is ≥ λ(L−H_k)/δ_k under every merge at once; no spectral point, no hypothesis, no count of terms, no error term (zero-loss lemma). It bounds the realisation inherited from the derivation, not the true D1 cost of the leaf tensor | [D], §5.3; refereed (`review-thmW.md`), Lemma S in Lean |
| Zero-loss lemma (Lemma 5.3) | for all classes of B.2 some N has certified bonds dominating any point of the circle arc: no ε per crossing | [D]: analytic for max energy ≥ 62 from the quoted Lehmer/Bessenrodt–Ono bounds [K, checked for n ≤ 10⁴], exact computation below (`zeroloss.py`) |
| Numerical test of Lemma S | stepwise form on 2800 parents in ℝ³ and products of tripods and lines, incl. degenerate ones; depth-2 game with all 15 second crossings: no violation, tight cases on the circle | [N]; §5.5 |
| Floor for the **certified** level value of the crossing-generated family, any depth | F_CAT(configuration): ≥ 1/√3 on 3-nets, ≥ 2/3 on Δ₃, ≥ 0.6124 on nets of F₃^M, F₄^M; on nets of F₂^m, if the Q1 placement stands, ≥ 1/√2 − 1.121/(g+1), against the level-1 value → 1/√2: the window closes only as g → ∞ (g = 4: 0.4828 against 0.6243) | [D] |
| Depth-2 certified game (§10) | type-A nesting (bond of a level-1 piece crossed with a third wire, adaptive stop/nest): on Δ₃ strictly below level 1 (0.8919 → 0.8910; 1% at uniform weights); on the full Z₅ net the game value stays 0.638071 (no gain near the two-merge corner, 0.35% at uniform weights) | [N], verified strategies; type B not computed |
| P4 | the adversary of level 1 at the two-merge corner is the flat orthogonal-simplex metric; nesting cannot beat any CAT(0) placement (Theorem W); the Q1 agent reports a CAT(0) space (filtrations of F₂^N) in which F₂^m-nets have value exactly 1/√2 and which is a price if contracting fails | [D]; the placement is the Q1 agent's claim, unreviewed |

No value below 1/√2 was found on nets of growing order. No construction.

---

## 1. P1: what the engine needs, what the crossing identity provides

### 1.1 The level and its value [K + D]

Configuration: nodes V (|V| = g², the 3-net of a group G: nodes (r,c), merges k = 1,2,3 = partitions by r, c, r−c),
edges E, every edge e = {n,n′} carries a string of λ bits with one copy (leg) e⁺ at n and e⁻ at n′. Level tensor
f = Π_e ⟨2^λ⟩_{e⁺e⁻}, a tensor on the legs. A node holds an arbitrary table of all its legs, so in every evaluation all
legs of a node are processed together: a merge is a partition of nodes.

**D1 cost.** For a tensor A on the legs and a merge k, c_k(A) is the least Σ_{G<G′} log₂ d_{GG′} such that the push-forward
of A to the groups of k (group G holds all indices of the legs of its nodes) is a restriction of the graph tensor
Π ⟨d_{GG′}⟩_{GG′}. This is the network cost of `engine3-open-door` §1.6 (the node tensors are the maps of the restriction),
equal to (L4) of Majdoddin's class when A meets two groups, and it is the cost the recursion pays: the merged instance
is a weighted clique sum on g nodes.

**Level value.** A family Σ_i A_i = d·f whose terms are products of pieces over factors (2^{o(λ)} pieces per factor); a
term is evaluated under one merge. V = max_i min_k c_k(A_i). If the family is a product over many factors or blocks,
the adversary's mixed strategies are realised by terms, and
V = min_{w∈Δ₃} max_i ⟨w, c(A_i)⟩ (von Neumann). ρ = V/(λ|E|); exponent α′ = log₂(1/ρ*) (node growth 2).

**Differences from the K_{2,3} protocol game** (`ports/protocol`): (i) the cost of a term under a merge is the *sum* of
all bond bits (the merged instance is a clique sum on the groups and is charged e_K per bit; balance comes from the
symmetry of the net as in AN's level), not the largest load on an edge; (ii) there is no shared GHZ index: terms are
enumerated, and their number multiplies the running time by 2^{o(λ|E|)}; (iii) **the only adaptivity is the choice of
one merge per term.** Time-sharing between merges inside a term does not exist, because a merge is a global partition
of the nodes. In the protocol game every factor chooses its own routing; here all factors of a term are routed in the
same hub family.

### 1.2 What "the crossing identity with respect to classes k, k′" is on a net [R]

AN Prop. B.2 for wires a–c (p bits) and b–d (q bits): pieces Ψ_N, N = 0…Θ, with certified log-ranks r_N across ab|cd and
r′_N across ad|bc, r_N² + r′_N² ≤ 2(p²+q²) + o, and the trivial bounds r, r′ ≤ p+q. Nothing is known about the third cut
ac|bd beyond the trivial 2·min(p,q).

Under merge k a piece Ψ_N is a tensor on the (at most four) groups of a, b, c, d. Lemma A.3 with hubs identified with
groups gives the realisations (constants = bits that have to be moved to another group):

    c_k(Ψ_N) ≤ min( S,  A_c + min(r_N, p+q),  A_b + min(r′_N, p+q),  A_3 + 2 min(p,q) ),          (1.1)

S = all four legs gathered at one group, A_c = cheapest way to bring a, b to one group and c, d to another, A_b the
same for (a,d | b,c), A_3 for (a,c | b,d). Table (a ≁ c and b ≁ d under k, else see `game1.py::consts`):

| position of the legs under merge k | certified cost |
|---|---|
| a ∼ b, c ∼ d ("aligned for cut c") | min(r, p+q) |
| a ∼ d, b ∼ c ("aligned for cut b") | min(r′, p+q) |
| a ∼ b only (three groups) | min(p+q, min(p,q) + r, 2 min(p,q) + r′) |
| a ∼ d only | min(p+q, min(p,q) + r′, 2 min(p,q) + r) |
| four different groups | min(p + q + min(p,q), 2 min(p,q) + min(r, r′)) |
| a ∼ c, b ∼ d (both wires internal) | 2 min(p,q) — against raw 0 |

A pair is aligned for cut c under k and for cut b under k′ iff a,b,c,d is a (k,k′)-rectangle with the two wires as its
diagonals. On a 3-net the rectangle partner of a generic edge for (rows, columns) has the reflected slope, and under
the third class its four nodes lie in four different groups (three, if the partner is a diagonal-class edge). So:

- for a rectangle piece the cost vector is (r, r′, min(p+q+min(p,q), 2min(p,q) + min(r,r′))): **under the third merge
  the piece costs more than the raw wires** (raw = p+q; at p = q the certified third cost is 3p, i.e. 3/2 per bit). The last row is the K₄ case: the X_j-crossing of K₄ costs up to 2 under the
  merge to which both its edges are internal, where the raw wires cost 0. This is what `sat3/notes.md` Cor. 3.3 calls
  "no price sees the cost of a crossing piece across the merge that contains both its edges".
- pairs that are aligned for one merge only (e.g. two Δ₃-edges from different anti-diagonals: aligned for one class,
  "a ∼ d only" for the second, "b ∼ c only" for the third) have a gain only with unequal splits p ≠ q, because at
  r′ = p+q the circle gives r = |p−q|.

**Accounting [R].** A term is a product of pieces on disjoint legs; a product of networks is a network, so certified
costs add over the factors of a term, exactly as in AN App. B / Thm A for two merges. Nothing else is used at level 1.

### 1.3 Lemma (two-sided cuts have no purchase on a net) [R]

Let A be a tensor on legs of a net, and suppose its only rank certificates are across two-sided cuts (bipartitions of
its legs). Call a cut *aligned with merge k* if each side lies in one group of k. If two cuts are aligned with two
different merges, every cell (intersection of a side of one with a side of the other) lies in one group of both
merges, i.e. in one node. So A lives on at most four nodes forming a rectangle, with bundles of parallel edges: it is
the level-1 rectangle piece. If three cuts are aligned with three merges, the cells are single nodes with sign vectors
in {±}³, any two nodes share at most one line, so the vectors differ pairwise in ≥ 2 places: at most four nodes,
pairwise collinear in the three classes. Three nodes: a triangle of the net (two in a row, two in a column, two on a
diagonal), which exists in every Latin square. Four nodes: (r,c), (r,c′), (r′,c′), (r′,c) with r−c = r′−c′ and
r−c′ = r′−c, i.e. 2(c−c′) = 0: a K₄ of the net, which exists only if G has 2-torsion. In both cases all edges among the
nodes are merge-class edges. ∎

Consequence: every identity whose terms are "rank one across one transversal two-sided cut" (PT-rank identities,
§4.2) produces, on a net, nothing beyond rectangle pieces unless its terms are evaluated through non-aligned,
multi-group realisations as in (1.1).

---

## 2. P2: the level-1 game

**Design.** Split the λ bits of every edge among *factors*; a factor is an unordered pair of distinct edges {e, e′}
with p bits of e = (a,c) and q bits of e′ = (b,d) (both orientations give the same pair of cuts), plus raw bits.
**Adversary.** One N (an angle θ: r = R cos θ, r′ = R sin θ, R = √(2(p²+q²)), capped at p+q) per factor.
**We.** One merge per term.

    h(w) = min over designs of  Σ_f x_f · max_θ Σ_k w_k c_k(f, θ)  +  Σ_e raw_e Σ_k w_k [e crosses k],      V₁ = min_{w∈Δ₃} h(w).

For fixed w this is a linear programme in the design; its dual is

    max Σ_e y_e   s.t.   y_e ≤ Σ_k w_k [e crosses k],    p·y_e + q·y_{e′} ≤ max_θ Σ_k w_k c_k({e,e′}; p, q; θ)  for all pairs and all p, q.   (2.1)

**Metric reading [D].** If d is a pseudometric on legs and hubs, with hub distances δ_k inside merge k and savings
s^k_e = |e⁺e⁻| − |e⁺ o^k(e⁺)| − |e⁻ o^k(e⁻)|, then y_e = Σ_k w_k s^k_e/δ_k is feasible for (2.1) as soon as d satisfies
B.3 with a common (r,r′) for all hub choices and the triangle inequality (Theorem W1 below). So (2.1) is "maximise the
price-method value over metrics satisfying triangle + all instances of B.3 with the four wire ends at legs and the hubs
at merge hubs", in the weighted form; the LP is the exact value of the game and the metrics are a (possibly proper)
subset of its dual solutions.

h is not convex in w (it is a minimum over designs of functions convex in w), so the symmetric point need not be the
minimiser, and it is not.

**Maximisation over θ** is exact: c_k is a minimum of a constant, A + R cos θ and A′ + R sin θ, so the maximum is at a
breakpoint or at tan θ = (sum of weights of sin-branches)/(sum for cos-branches); `game1.py::mval`. The split p:q runs
over a grid (9 or 19 ratios); a finer grid can only lower h.

### 2.1 Values [N]

ρ = h/|E|; "two-merge" = [g²(g−1)²/2 · (1/√2) + g²(g−1) · (1/2)]/|E| (rectangles for generic edges, straight edges raw at
weights (½,½,0)).

| level | \|E\| | w = (½,½,0) | two-merge formula | w uniform | (0.45,0.45,0.1) | (0.5,0.45,0.05) | (0.6,0.2,0.2) | (1,0,0) | raw at uniform w |
|---|---|---|---|---|---|---|---|---|---|
| K₄, three matchings (g = 2) | 6 | 0.569036 | 0.569036 | 0.666667 | 0.609666 | — | 0.666667 | 0.666667 | 0.6667 |
| AG(2,3), three classes | 36 | 0.603553 | 0.603553 | 0.695399 | 0.643198 | 0.623841 | 0.701245 | 0.750000 | 0.7500 |
| net of Z₂² (AG(2,4)) | 120 | 0.624264 | 0.624264 | 0.775805 | 0.680358 | 0.653609 | 0.758156 | — | 0.8000 |
| net of Z₄ | 120 | 0.624264 | 0.624264 | 0.752489 | 0.674678 | 0.650275 | 0.743412 | — | 0.8000 |
| net of Z₅ (AG(2,5)) | 300 | 0.638071 | 0.638071 | 0.773945 | 0.690931 | 0.665121 | 0.762598 | — | 0.8333 |
| Δ₃ alone (9 anti-diagonal edges) | 9 | 0.9085 | (1) | 0.9395 | 0.9183 | — | 0.8929 | 1.000000 | 1 |

Reading.
- **Calibration.** With two merges the game returns exactly the rectangle value for every g, although all pairs, all
  splits and all hub choices are available: nothing in level 1 beats App. B's rectangles with two merges. With one merge
  it returns exactly raw (the pigeonhole floor is respected; this is the test that caught the first version of
  `mval`, which used a θ-grid and missed the kink at r′ = |p−q|).
- **K₄.** min_w h = 0.5690 = (2+√2)/6 at the two-merge corner; uniform weights give raw. The price floor is 0.4714
  (`notes.md` Cor. 3.3). The gap is the uncontrolled third rank (z1's three-rank object), as expected.
- **Nets.** h increases away from the two-merge corner in every case computed. V₁(3-net of order g) = two-merge value,
  which tends to 1/√2. For uniform weights the value tends to about 0.77–0.80, the number (2√2+2)/6 = 0.805 of "every
  generic edge in one rectangle, third merge at cost ≥ raw" less small gains from non-aligned pairs. Against 1/√3 =
  0.5774 (flat), 0.6124 (tripod floor), 0.7071: **level 1 is on the wrong side of 1/√2 for every weight except the
  two-merge corners, where it is exactly on it** (in the limit g → ∞).
- **Δ₃ alone.** No rectangles; the gain comes from pairs aligned for one merge with p:q ≈ 0.35:0.65, cost vector
  (0.817, 1, 1) per bit at the adversary's θ (r′ = max(p,q)). 0.9085 with two merges improves the straightened-edge
  bound 0.935 of `engine3-open-door` §3.2 [N; not refereed]; the floors are 9/√2/9 = 0.7071 (two merges, FH) and 2/3
  (three merges, ¬contracting). Δ₃ is not a level of a tower.

Large-net limit: no separate limit formulation is needed. In the limit only rectangles contribute at order 1 (every
other pair type with a gain needs a coincidence of groups of codimension ≥ 2 or an unequal split with a gain of lower
order), and the rectangle design has value min over pairs of classes of √(w_k²+w_{k′}²) + (cost ≥ 1)·w_{k″} ≥ 1/√2.

### 2.2 Why [R]

For a rectangle piece the adversary's θ = π/4 gives (1/√2, 1/√2, 3/2) per bit of raw 1 (certified costs, p = q). For any weights
⟨w, c⟩ ≥ (w_k + w_{k′})/√2 + w_{k″} ≥ 1/√2 with equality only at w_{k″} = 0. Splitting the bits of an edge among the three
rectangle types is worse for the same reason. The same holds for p-nets with any p: a rectangle piece is cheap for two
of the p merges only. So **the third class cannot help any cover built from pieces that are cheap for two merges and
at least raw for the others**, whatever the adaptivity.

---

## 3. Verdict on the brief's question, and on H29

The value of the three-class level-1 game is not below 1/√2: on nets of growing order it is exactly the two-merge
value. [X] "crossing identity for each pair of classes + adaptive choice of merge per term" as a route below 1/√2:
dead, by §2.2 (proved for rectangle pieces) and by the LP (all other level-1 pairs, [N] for g ≤ 5).

What is left is nesting (§5) or pieces that are not built from two-way crossings at all (§7).

---

## 4. Prior work

### 4.1 Majdoddin, arXiv:2610.41622, §4 [K, read: Def. 4.2, Prop. 4.6–4.8, §4.7 with Prop. 4.23 and its proof, §4.8]

- Prop. 4.23 concerns the six-edge configuration C (two lines x+y = const of AG(2,3)) with rows, columns, diagonals.
  A piece is *k-local* if it is a product of one factor per bundle of merge k, and it is charged c_k = the sum of the
  factors' log-ranks across their pairs of groups — **only under the merge for which it is local**: under another merge
  it meets three groups, which (L3) excludes and (L4) does not price. (c) says that the piece which is full across
  the forward/backward split Q is full under its own merge.
- In our accounting (D1) a k-local piece has a certified cost under the other merges, by (1.1). For a merge-1 bundle of
  C or Δ₃ it is min(p+q, min(p,q)+r′, …), and the game value is below 1 (0.89–0.94 on Δ₃; `engine3-open-door` §2.1
  already has ρ_C ≤ ρ_x + 1/4). So Prop. 4.23 is not a barrier for the game: same objects, different cost model; what
  it leaves open ("pieces coupling different bundles, hyperedges under the merge") is exactly "evaluate a merge-k
  crossing piece under merge k′".
- Prop. 4.8 (two-merge floor 1/2) and the argued 1/2 for pair products on the AG(2,4) translation matching are floors at
  1/2 and do not touch the window (0.61, 0.71).
- What carries over is the mechanism: a piece that is local for one merge is expensive for the others. On nets this
  kills level 1 (§2.2), by computation and not by Prop. 4.23.

### 4.2 Sra, hexagon:2611.01066, Lemma 4.2; Khoruzhii's integral crossing lemma [K-unverified; read at the cited lines]

- Sra's object (Def. 3.1, l. 227–239): PT rank P_F(n) = least number of tensors, "each of rank one across a transversal
  cut … different terms may choose different cuts", summing to k identity wires. Lemma 4.2 (l. 424–440): for a cut of
  group A₀ and a cut of group B₀ the product of the two summands is a linear image of a two-factor identity I_r ⊗ I_s;
  hence P(n) ≤ 2^{k−2} P(P_A, P_B) and exponent ‖β‖₂.
- Khoruzhii (kh.txt, eq. (5), (6)): δ_{ik}δ_{jl} = Σ_s (A_s)_{ij}(B_s)_{kl} + (C_s)_{il}(D_s)_{kj}, r ≤ 2H·Q(H+E): two pieces R + C, R with
  bounded rank across one cut and C across the other. Nothing is stated about rank of R across the second cut.
- **Measure [D].** PT rank is max_i min_cut c_cut(T_i): every term is charged under its own cheapest cut. The engine's
  level value is min_w max_i ⟨w, c(T_i)⟩: in different factors of one term the adversary takes pieces assigned to
  different cuts, and the term is evaluated under one merge. AN's Ψ_N carry both ranks (r_N, r′_N) on a circle, which
  is what Def. 7 of the 3-SAT paper needs (c_row + c_col ≤ 4ρλ per piece). The two-piece form R + C is the "two-bucket"
  form of `ports/protocol` §2.2 and gives (1 + 1/√2)/2 = 0.854 on a rectangle if the uncontrolled ranks are full.
  Nested terms have certificates across the two cuts (ε_A, ±ε_B) only, 2 of the 2^{k−1}. So "the nested identity attains
  1/√k" holds in the PT measure; for the engine game nothing below the two-merge value follows.
- **Coordinator's check confirmed [D].** The configuration is the cross-polytope a_i = c + t e_i, b_i = c − t e_i with
  hyperplane classes of normal ε: it sits in AG(k,g), node growth β = k, value 1/√k, exponent log_k √k = 1/2.
- **On nets**: §1.3. Khoruzhii's identity is not a coarsening of B.2 (it comes from a fermionic Fock-space identity,
  its pieces are not sums of the Ψ_N); it is a circle-covering crossing identity in the sense of §5.1, and Sra's
  nesting crosses two hub–hub bonds with it. Both are inside the class of §5, so Theorem W
  applies to it: evaluated in the engine game it can never go below the flat floor.

---

## 5. Weak duality for certified costs: Theorem W

### 5.1 The class of covers

Parties: the legs, and a set Aux of auxiliary parties created at will. A **wire system** W is a finite list of wires
(u, v; β), β bits, between parties, with the

**Leg invariant.** The wires at each leg carry exactly the leg's λ bits in total. A leg is never used as a hub and a
wire at a leg is never enlarged. This is a normalisation, not a restriction [R, referee]: a leg wire (ℓ,y;M) with
M > λ is a restriction of ⟨2^λ⟩_{ℓz}⟨2^M⟩_{zy} with a new auxiliary z, and a hub identified with a leg ℓ is a restriction
of an auxiliary z joined to ℓ by a λ-bit wire (z applies ℓ's map); with π(z) = π(ℓ) in (5.1) the leaf cost is unchanged,
and v is unchanged. So "enlarge at a leg" and "hub at a leg" mean: route through an auxiliary party placed at the
leg's group.

W₀ = the edges. GT(W) is the graph tensor of W.

Moves (each replaces a wire system by one or several wire systems, and the tensor on the legs it stands for by a
cover whose members are restrictions of the new graph tensors):

- (M0) split a wire into wires of smaller bits; route a wire through an auxiliary party ((u,v;β) → (u,y;β), (y,v;β),
  Lemma A.2); increase the bits of a wire between auxiliary parties; identify two auxiliary parties.
- (M1) **crossing**: choose two wires (a,c;p), (b,d;q) between any parties (legs or auxiliary: a hub–hub bond is
  allowed, which is Sra's nesting) and a **circle-covering crossing identity** for them: an identity writing
  ⟨2^p⟩_{ac}⟨2^q⟩_{bd} as a sum of pieces i, each with certified log-ranks (ρ_i, ρ′_i) across ab|cd and ad|bc, such that the
  boxes [0,ρ_i] × [0,ρ′_i] cover the arc {r² + r′² = 2(p²+q²)} ∩ [0,p+q]² (up to a stated ε ≥ 0). For every piece i the cover
  chooses a cut, and the new system is W without the two wires plus
  cut c: (a,o;p), (b,o;q), (c,o′;p), (d,o′;q), (o,o′; ρ_i);   cut b: (a,w;p), (d,w;q), (b,w′;q), (c,w′;p), (w,w′; ρ′_i),
  with new auxiliary o, o′ (w, w′), bonds as certified or larger, capped at p+q if the cover wishes.
  Instances: **Prop. B.2** with b_c(N) = log₂((Θ−N+1)P(Θ−N)), b_b(N) = log₂((N+1)P(N)) (circle covering with ε = 0:
  Lemma 5.3); **Khoruzhii's two-piece identity** (= Sra's (CR)), pieces R, C with certified bonds (log₂ r, p+q) and
  (p+q, log₂ r), log₂ r ≈ √(p²+q²): every point of the arc has min(r_c, r_b) ≤ √(p²+q²), so the two boxes cover it (ε =
  the lower-order terms of his count, not checked here); any sum Σ_{N∈S} Ψ_N with the sum of the certificates.
  The "third cut" ac|bd with its trivial 2min(p,q) bits and single-hub realisations are (M0)-consequences of the
  trivial bounds.
- Sums and regroupings of leaves, certified by direct-sum networks, are allowed: the certified cost of a sum is at
  least that of each summand [referee §4].

By induction (a cover of a tensor restricts to a cover of each of its restrictions) a tree of moves writes
f = Σ_leaves t_leaf with t_leaf a restriction of GT(W_leaf). **Nesting depth** = the largest number of (M1) moves on a
branch. A leaf is evaluated under a merge k chosen at the leaf, at the **certified cost**

    cost_k(W) = min over π: Aux → groups of k of  Σ_{wires} β·[π(u) ≠ π(v)]      (π = the group of the node on legs),   (5.1)

a 0-extension: every auxiliary party is executed at some group of the merge. c_k(t_leaf) ≤ cost_k(W_leaf) [R: push
forward along π] — an **upper** bound on the true D1 cost. The **certified level value** of a cover is
max_leaf min_k cost_k(W_leaf)/(λ|E|). A *crossing-generated cover with certified costs* is such a tree with its costs
(5.1). Level 1 (§2) is depth 1 with hubs at groups. Not in the class: covers that are not trees of moves; identities
that are not circle-covering crossing identities for two wires; and — the main limitation, see the paragraph after
Theorem W — any evaluation of a leaf tensor by a network other than the one inherited from its derivation.

**Placements.** A placement P of the configuration in a metric space X: a point for every leg and a point o^k_G for
every group of every merge. L = Σ_e |e⁺e⁻|, H_k = Σ_legs |ℓ o^k(ℓ)|, δ_k = max_{G≠G′} |o^k_G o^k_{G′}|, b_k = (L − H_k)/δ_k,
**price value** = min_k b_k/|E|. F_X = supremum over placements in spaces of class X (F_flat = 1/√3 on 3-nets;
F_CAT ∈ [0.6124, 0.7071]).

**Steiner value.** v_X(W) = inf over positions of the auxiliary parties in X of ℓ(W, pos) = Σ β·|pos(u) pos(v)|.
Two facts hold in every metric space [R]:

- (S1) v(W₀) = λL, and (M0) moves do not decrease v (triangle inequality; fewer positions).
- (S2) for every leaf and every merge k: v(W) ≤ λH_k + δ_k·cost_k(W). (Put each auxiliary party at the hub o^k_{π(y)} of an
  optimal π of (5.1); a wire (u,v) then has length ≤ [leg-to-own-hub distances] + δ_k[π(u) ≠ π(v)], and the wires at a
  leg carry its λ bits.)

So a metric space X bounds a cover as soon as the adversary can keep **v_X(W) ≥ λL − o(λ)** down to some leaf. (With
fixed positions for the auxiliary parties the quantity ℓ(W, pos) is easy to keep, by B.3 alone, but then (S2) fails:
a hub created for a row cut and later evaluated under the column merge sits at the wrong hub point. The intrinsic
potential is v; its behaviour under (M1) is Lemma S, §5.3.)

### 5.2 Theorem W1 (depth 1, every metric with B.3) [R]

**Condition (B).** A pseudometric space X satisfies (B) if for all x, v, y, u ∈ X and p, q ≥ 0 there are r, r′ ≥ 0 with
r² + r′² ≤ 2(p²+q²) such that for all o, o′, w, w′ ∈ X both inequalities of AN Prop. B.3 hold.

**Lemma 5.1 [R].** Every CAT(0) space satisfies (B).
*Proof.* Let ρ_c = sup over o ≠ o′ of S_c/|oo′|, S_c = p(|xv| − |xo| − |vo′|) + q(|yu| − |yo| − |uo′|), and ρ_b the same for
S_b = p(|xv| − |xw| − |vw′|) + q(|yu| − |uw| − |yw′|). Fix o, o′, w, w′ and a₁, a₂ ≥ 0; put λ₁ = a₁/|oo′|, λ₂ = a₂/|ww′|,
Λ = λ₁+λ₂, t = λ₂/Λ and β_x = γ_t(o,w), β_v = γ_t(o′,w′), β_y = γ_t(o,w′), β_u = γ_t(o′,w) (γ_t = point at t on the geodesic).
Convexity of the distance from a point along a geodesic (C.4(a)) gives λ₁|xo| + λ₂|xw| ≥ Λ|xβ_x| and the three analogues,
so λ₁S_c + λ₂S_b ≤ Λ(p|β_xβ_v| + q|β_yβ_u|) ≤ Λ√(p²+q²)·(|β_xβ_v|² + |β_yβ_u|²)^{1/2}, and by the two-bimedian inequality
(`notes.md` Prop. 3.1) the last bracket is ≤ 2(1−t)²|oo′|² + 2t²|ww′|² = 2(a₁²+a₂²)/Λ². Hence
a₁S_c/|oo′| + a₂S_b/|ww′| ≤ √(2(p²+q²))·|a| for all hubs; taking suprema, a₁ρ_c + a₂ρ_b ≤ √(2(p²+q²))|a| for all a ≥ 0,
i.e. ρ_c² + ρ_b² ≤ 2(p²+q²). Take (r, r′) = (ρ_c, ρ_b). ∎

**Lemma 5.2 (discretisation) [D].** For classes Σ₁, Σ₂ with p = log₂|Σ₁|, q = log₂|Σ₂| and every (r, r′) with
r² + r′² ≤ 2(p²+q²) there is N with b_c(N) ≥ r − ε and b_b(N) ≥ r′ − ε, where ε = ε(p,q) = o(p+q) as p+q → ∞.
*Proof.* Put κ′ = κ/ln 2 and η(E) = 1 − log₂P(E)/(κ′√E) ∈ [0,1), η̄(N₀) = sup_{E ≥ N₀} η(E) → 0 (Lemma B.1). From
ln|Σ_i| ≤ ln P(e_i) ≤ κ√e_i: 2(p²+q²) ≤ κ′²Θ. Take N = min(Θ, ⌈r′²/κ′²⌉). Then b_b(N) ≥ log₂P(N) ≥ (1 − η(N))r′ and, since
Θ − N ≥ r²/κ′² − 1, b_c(N) ≥ (1 − η(Θ−N))(r − κ′). If N ≤ N₀ then r′ ≤ κ′√N₀ and the deficit r′η(N) is at most κ′√N₀; if
N > N₀ it is at most r′η̄(N₀); the same for Θ − N. So ε ≤ κ′(1 + √N₀) + (p+q)·η̄(N₀) for every N₀. ∎
(Only the certificates' lower bounds b ≥ log₂P are used; the factor N+1 in the certificate and the cover's trivial
cap p+q are harmless, the latter because the thresholds of Lemma 5.1 and Lemma S are ≤ p+q.)

**Lemma 5.3 (zero loss for the certificates of B.2) [D; exact computations in `attain/zeroloss.py`].**
Let Σ₁, Σ₂ be classes of energies e₁ = 2m₁, e₂ = 2m₂ (m_i ≥ 1), p = log₂|Σ₁|, q = log₂|Σ₂|, Θ = 2(e₁+e₂), and
f(E) = log₂((E+1)P(E)), so that b_b(N) = f(N), b_c(N) = f(Θ−N). For every (r, r′) with r² + r′² = 2(p²+q²) and
0 ≤ r, r′ ≤ p+q there is N ∈ {0,…,Θ} with f(N) ≥ r′ and f(Θ−N) ≥ r. So Lemma 5.2 holds with ε = 0.

*Inputs.* P(E) = Σ_{m ≤ E/2} p(m) (symbols of energy 2m ↔ partitions of m), |Σ_i| ≤ p(m_i); κ = π/√3, κ′ = κ/ln 2 = 2.61676;
(K1) p(m) ≤ e^{π√(2m/3)} for m ≥ 0, and (K2) the two-sided bound
(√3/(12n))(1 − 1/√n) e^{μ(n)} < p(n) < (√3/(12n))(1 + 1/√n) e^{μ(n)}, μ(n) = (π/6)√(24n−1), n ≥ 1
[K: Lehmer 1938 in the form of Bessenrodt–Ono 2016, eq. (2.1), checked against the source on 27 Nov by the coordinating session: Bessenrodt–Ono, "Maximal multiplicative properties of partitions", arXiv:1403.3352 (Ann. Comb. 2016), in the proof of Theorem 2.1, the displayed inequality after Theorem 2.2, stated for every positive integer n with μ(n) = (π/6)√(24n−1), in exactly this form (it is the display before their (2.1), not (2.1) itself);
N: verified here for 1 ≤ n ≤ 10⁴]. (K1) follows from (K2).

*Step 1: (Z′) (E+1)P(E) ≥ exp(κ√(E+½)) for every integer E ≥ E₀ = 44.* For 44 ≤ E < 800: exact integers against a
60-digit evaluation, smallest ratio 1.0075 [N, exact]; the last failure of (Z′) is E = 43. For E ≥ 800, E ∈ {2M, 2M+1},
M ≥ 400, J = ⌊√M⌋: by (K2), P(E) ≥ Σ_{j ≤ J} p(M−j) ≥ (J+1)(4√3·M)^{−1}(1 − (M−J)^{−1/2}) e^{μ(M−J)}, so
(E+1)P(E)·e^{−μ(M−J)} ≥ c₁√M with c₁ = (1 − (M−√M)^{−1/2})/(2√3) ≥ 0.27386, while
κ√(2M+3/2) − μ(M−J) = π(19/36 + 2J/3)/(√(2M/3+½) + √(2(M−J)/3 − 1/36)) ≤ c₂ := (π/√6)(1 + 19/(24√M))(1 − M^{−1/2} − (24M)^{−1})^{−1/2} ≤ 1.36803.
c₁√M increases and c₂ decreases with M, and ln(0.27386·20) = 1.7006 > 1.36803. (Cross-check: no failure of (Z′) for
800 ≤ E < 20000 by direct computation.) Equivalently **f(E)² ≥ κ′²(E + ½) for E ≥ 44**.

*Step 2: the case max(m₁,m₂) ≥ 31.* Put a_i = κ′√(2m_i), so p ≤ a₁, q ≤ a₂ by (K1) and κ′²Θ = 2(a₁²+a₂²) ≥ 2(p²+q²) =: R².
Let S = κ′²Θ − (p+q)² ≥ 2(a₁² − p²) + 2(a₂² − q²). For the larger m, (K2) gives p ≤ a − d with
d ≥ d₀(m) = log₂(4√3·m/(1 + m^{−1/2})), hence S ≥ 2d₀(m)·a = 2d₀(m)κ′√(2m) ≥ κ′²(E₀ + ½) for every m ≥ 31 (checked for
31 ≤ m < 2000; the left side increases). Also Θ ≥ 2E₀. Now fix (r, r′) on the arc and let N be the least integer
with f(N) ≥ r′; it exists because f(Θ)² ≥ f(Θ−E₀)² ≥ κ′²(Θ − E₀ + ½) ≥ κ′²Θ − S = (p+q)² ≥ r′².
- N = 0: f(Θ) ≥ p+q ≥ r.
- 1 ≤ N ≤ E₀: f(Θ−N) ≥ f(Θ−E₀) ≥ p+q ≥ r (f is non-decreasing).
- N > E₀: f(N−1) < r′ ≤ p+q, and N−1 ≥ E₀ gives κ′²(N − ½) ≤ f(N−1)² < (p+q)² = κ′²Θ − S, so Θ − N > S/κ′² − ½ ≥ E₀ and
  f(Θ−N)² ≥ κ′²(Θ − N + ½) = κ′²Θ − κ′²(N − ½) > R² − r′² = r².

*Step 3: the case max(m₁,m₂) ≤ 30.* The property is monotone in (p,q) at fixed Θ (a point of the arc of (p̃,q̃) ≤ (p,q)
is dominated by a point of the arc of (p,q): take x ∈ [max(r,|p−q|), min(√(R²−r′²), p+q)], which is non-empty). So it
suffices to take p = log₂p(m₁), q = log₂p(m₂), which dominate every class. For these, the exact finite criterion
(for every N in the range: f(Θ−N) ≥ p+q or f(Θ−N)² ≥ R² − max(f(N−1), |p−q|)²) was verified in 60-digit arithmetic
for all 7260 pairs 1 ≤ m₁ ≤ m₂ ≤ 120: no failure [N, exact]. ∎
(Cross-check of Step 2: the same criterion on 120 pairs with m up to 1500, `zeroloss_sample.py`: no failure, smallest
margin among the pairs where the cap is not reached 2806 squared bits. The certificates are far from tight.)

Status: the proof is complete given (K2). What is proved by hand: Steps 1 (E ≥ 800) and 2. What is computed: (Z′) on
44 ≤ E < 800, the threshold m ≥ 31, and Step 3 (m ≤ 120, four times the needed range). What is quoted: (K2). The
referee's independent computation (`refW/disc_loss.py`: loss 0 for all pairs of energies ≤ 300 and on a grid to 1200,
with the true largest classes) agrees. For circle-covering identities other than B.2 the ε of the identity remains.

**Theorem W1.** Let d be a pseudometric on legs and hubs satisfying (B) and the triangle inequality (for instance the
restriction of a CAT(0) placement). For every crossing-generated cover of depth 1 in which the crossed wires are edge
wires (any pairs, any splits, hubs anywhere), some term has, for every merge k at once,

    cost_k(term) ≥ λ(L − H_k)/δ_k − o(λ).

*Proof.* For each factor the four ends are legs, so (B) at these four points gives one (r,r′) valid for all hubs; the
adversary takes N from Lemma 5.2. For any positions of the two new hubs, the five new wires are at least as long as
the two old ones: ℓ does not decrease **for every position**, hence v does not decrease. Other moves: (S1). Leaf: (S2). ∎

For level 1 the LP of §2 gives the exact value, so W1 is only the statement that the dual solutions coming from
metrics are valid; it is the base case of the following.

### 5.3 Lemma S and Theorem W (all depths, every CAT(0) placement) [D]

**Lemma S (Steiner crossing inequality).** Let X be a CAT(0) space (geodesic; completeness is not used), W a wire
system with legs in X, and (a,c;p), (b,d;q) two wires of W between any parties (legs or auxiliary). Let r_c be the
least bond for which the c-child has v_X(W^c) ≥ v_X(W), and r_b the same for the b-child. Then

    r_c² + r_b² ≤ 2(p²+q²),   0 ≤ r_c, r_b ≤ p+q.

So there are (r,r′) on the circle such that, after re-optimising the positions of **all** auxiliary parties, neither
child is below the parent.

*Proof.* Write rest(pos) for the total length of the wires of W other than the two, as a function of the positions
of the auxiliary parties, and v = v_X(W). The c-child with bond r has value ≥ v iff
rest(pos) + p|a o| + q|b o| + p|c o′| + q|d o′| + r|oo′| ≥ v for all positions (pos, o, o′); for o = o′ this holds by the
triangle inequality, so

    r_c = sup over (pos¹, o ≠ o′) of N₁/|oo′|,   N₁ = v − rest(pos¹) − (p|a¹o| + q|b¹o| + p|c¹o′| + q|d¹o′|),
    r_b = sup over (pos², w ≠ w′) of N₂/|ww′|,   N₂ = v − rest(pos²) − (p|a²w| + q|d²w| + q|b²w′| + p|c²w′|)

(a¹ = pos¹(a), or the fixed point if a is a leg; negative suprema are replaced by 0). N₁ ≤ p|a¹c¹| + q|b¹d¹| − (…) ≤
(p+q)|oo′| gives r_c ≤ p+q. Fix two configurations and a₁, a₂ ≥ 0, not both 0; put λ₁ = a₁/|oo′|, λ₂ = a₂/|ww′|,
Λ = λ₁+λ₂, t = λ₂/Λ, and interpolate everything along geodesics:

    pos^t(y) = γ_t(pos¹(y), pos²(y)) for every auxiliary y;   β_x = γ_t(o,w), β_v = γ_t(o′,w′), β_y = γ_t(o,w′), β_u = γ_t(o′,w).

(i) The metric of a CAT(0) space is convex along pairs of geodesics (C.4(a)), and rest is a positive combination of
distances between interpolated or fixed points: rest(pos^t) ≤ (1−t)rest(pos¹) + t·rest(pos²).
(ii) pos^t is a configuration of the parent: rest(pos^t) + p|a^t c^t| + q|b^t d^t| ≥ v.
(iii) The same convexity: (1−t)|a¹o| + t|a²w| ≥ |a^t β_x|, (1−t)|b¹o| + t|b²w′| ≥ |b^t β_y|, (1−t)|c¹o′| + t|c²w′| ≥ |c^t β_v|,
(1−t)|d¹o′| + t|d²w| ≥ |d^t β_u|.
(iv) |a^t c^t| ≤ |a^t β_x| + |β_xβ_v| + |β_v c^t| and |b^t d^t| ≤ |b^t β_y| + |β_yβ_u| + |β_u d^t|.
Hence
λ₁N₁ + λ₂N₂ = Λ[v − (1−t)rest(pos¹) − t·rest(pos²)] − Λ[(1−t)(legs of Z¹) + t(legs of Z²)]
 ≤ Λ[p|a^tc^t| + q|b^td^t|] − Λ[p|a^tβ_x| + p|c^tβ_v| + q|b^tβ_y| + q|d^tβ_u|] ≤ Λ[p|β_xβ_v| + q|β_yβ_u|]
 ≤ Λ√(p²+q²)·(|β_xβ_v|² + |β_yβ_u|²)^{1/2} ≤ Λ√(p²+q²)·(2(1−t)²|oo′|² + 2t²|ww′|²)^{1/2} = √(2(p²+q²))·|a|,
the last inequality being the two-bimedian inequality (`notes.md` Prop. 3.1) for o, w, o′, w′. Taking suprema over the
two configurations, a₁r_c + a₂r_b ≤ √(2(p²+q²))|a| for all a ≥ 0. ∎

Lemma 5.1 is the case in which the four ends are legs. The step that has no analogue in a potential with fixed hub
positions is (ii): one does not look for one N that is good at the parent's optimum; one interpolates the two bad
child configurations, and the interpolated configuration is again a parent configuration.

**Theorem W (weak duality for the certified costs of crossing-generated covers).** Let P be a placement of a
configuration (nodes, merges, edges with λ bits) in a CAT(0) space X. For every crossing-generated cover (§5.1) there
is a leaf with, for every merge k at once,

    cost_k(W_leaf) ≥ [ λ(L − H_k) − D·Σ_{crossings s on the branch} ε_s ] / δ_k,

where ε_s is the covering defect of the crossing identity used at s and D the diameter of the set of leg points.
- For covers whose crossings use Prop. B.2: ε_s = 0 (Lemma 5.3), so **cost_k(W_leaf) ≥ λ(L − H_k)/δ_k exactly, for any
  nesting depth, any number of crossings on a branch and any number of terms.** This rests on Lemma 5.3, i.e. on the
  quoted bound (K2) and the finite computations listed there.
- Without Lemma 5.3 (ε_s = ε(p_s,q_s) ≥ κ′ bits from Lemma 5.2) the bound is non-trivial only for branches with o(λ)
  crossings; "any depth" does **not** follow from Lemma 5.2 alone [referee, item 5].
- For other circle-covering identities ε_s is whatever their certificates give.
Hence the certified level value of the cover is ≥ (price value of P) − (D/λ|E|δ)·Σε.

*Proof.* v(W₀) = λL (S1). The adversary answers a crossing of (a,c;p), (b,d;q) in the current system W with a piece
whose box contains (r_c − ε, r_b − ε) (Lemma S and circle covering; the cover's cap p+q is harmless because
r_c, r_b ≤ p+q). If ε = 0 neither child is below the parent, whichever cut is chosen. If ε > 0: pass to the
completion of X (CAT(0), same Steiner values by density); near-optimal positions may be projected to the closed
convex hull of the leg points (nearest-point projections onto closed convex sets of a complete CAT(0) space are
1-Lipschitz; the hull has diameter ≤ D because closed balls are convex), so a bond smaller by ε lowers v by at most
ε·D. The other realisations available in the class (single hub, the cut ac|bd, trivial bonds, (M0) moves, sums) never
lower v, by the triangle inequality. At the leaf, (S2) with the leg invariant. ∎

**What Theorem W bounds, plainly.** It bounds cost_k(W_leaf): the cost of the realisation that the leaf inherits
from its derivation (rank certificates of the crossing identities, Lemma A.3 networks, routing, identification,
nesting). This is an upper bound on the true D1 cost c_k(t_leaf) of the leaf tensor, and Theorem W says nothing about
c_k(t_leaf). It is a barrier for a **proof method** — any engine analysis whose cost bounds come only from B.2-type
certificates, A.3 networks, routing, identification and nesting cannot certify a level value below F_CAT — and not a
barrier for the tensors. The gap is real: for classes (2,12), (2,12) (dimension 5, Θ = 48) the piece Ψ₄ has true rank
7 across ad|bc against the certificate 20, and Ψ₂₄ has rank 15 across the third cut ac|bd against the trivial 25
[R, referee's exact computation `refW/psi_ranks.py`; `ports/protocol` §1.3]; and the D1 cost of a leaf tensor minimises
over all networks on the groups, not only over the inherited one. True costs are bounded from below only through
prices: `q1-notes.md` Theorem B (refereed): if contracting fails, on nets of F₂^m the true level value is
≥ 1/√2 − c/g. In that statement Theorem W is not needed.

What else the theorem is and is not.
- It is unconditional: no spectral point, no FH/EP, no contracting hypothesis, no bound on the number of terms. The
  last point is not vacuous: a rank-one decomposition is not generated by the moves (its boxes are {(0,0)} and do not
  cover the arc); circle covering is the operative hypothesis, and the theorem is tight on the rectangle (App. B).
- Inside the class: AN App. B levels, the level-1 game of §2, Khoruzhii's two-piece identity (a different identity,
  inside by circle covering), Sra's Lemma 4.2 nesting (crossing of hub–hub bonds with it).
- It only gives the inequality "certified value ≥ sup over CAT(0) placements". Nothing says that nested covers attain
  it (in the K_{2,3} protocol problem the explicit level-1 protocols stay below the CAT(0) bound).
- The bimedian step of Lemma S needs only the CN inequality [referee §2]; `notes.md` Prop. 3.1 is that computation.
- A second proof for Hilbert space, by duality (it shows where the adversary's piece comes from): v(W) = max of
  Σ ⟨F_w, constants⟩ over flows F_w ∈ 𝓗 with |F_w| ≤ β_w in equilibrium at the auxiliary parties; with f₁, f₂ the optimal
  flows on the two wires take r = |f₁+f₂|, r′ = |f₁−f₂| (parallelogram law), and the children inherit feasible flows.

**Consequences [D]** (all for **certified** level values of crossing-generated covers, any depth, B.2 certificates;
F_X(config) = supremum of price values over placements in spaces of class X):
1. certified level value ≥ F_CAT ≥ F_flat: ≥ 1/√2 on balanced two-merge configurations, ≥ 1/√3 on 3-nets, ≥ 0.4714 on K₄,
   ≥ 2/3 on Δ₃ (nine tripods, `notes.md` Thm 5.2 — a CAT(0) placement, used here without any price hypothesis),
   ≥ 0.6124 on 3-nets of F₃^M, F₄^M (subgroup tripods);
2. with the Q1 placement (§6; value (g−2)/(√2(g+1)) + 1/(g+1) on all edges of the 3-net of F₂^m, g = 2^m) the certified
   level value of the family is ≥ 1/√2 − (3/√2 − 1)/(g+1) = 1/√2 − 1.121/(g+1), and ≤ the level-1 value (two-merge
   rectangle value). **Both tend to 1/√2; for finite g there is a window of width O(1/g)** (g = 4: 0.4828 against
   0.6243). So three merges cannot bring the certified value of this family below 1/√2 − O(1/g). This uses only that
   the filtration space is CAT(0), not that it is a price; at finite leg distance T the placement consists of actual
   points and Theorem W applies for each T, then T → ∞.
3. Sra's nested identity, evaluated in the engine game with its certificates, obeys the same floors.

### 5.4 What went wrong on the way (kept for the referee)

- A potential with **fixed** positions of the auxiliary hubs is non-decreasing by B.3 alone, at every depth, but
  the leaf step (S2) fails: a hub created for a row cut and evaluated under the column merge sits at the wrong hub
  point. My first note claimed weak duality on that basis; withdrawn.
- **Linearising at the parent optimum is false [R].** With z* a parent minimiser, first variation (exact in CAT(0) for
  both ends moving) reduces Lemma S to p|xo| + q|yo| + p|x′o′| + q|y′o′| + r|oo′| ≥ p·L₁(x,x′) + q·L₂(y,y′) with
  L₁(x,x′) = |α*γ*| − |α*x| cos∠_{α*}(γ*,x) − |γ*x′| cos∠_{γ*}(α*,x′). In a tripod with both base wires starting at the centre
  (O → arm 1, O → arm 2) this needs r ≥ p+q (o on arm 3, o′ = O) and r′ ≥ p+q (w on arm 3 near O, w′ on arm 1): off the
  circle. It is not a counterexample to Lemma S: it would need the rest-function to decrease when b moves into arm 3
  and when b moves into arm 1, against its convexity along arm 1 – O – arm 3.
- **Products of pods as Banach spaces.** A pod embeds in (ℝ^m, ℓ₁) and 0-extension on a tree is exact, so Steiner values
  in a product of pods can be computed in E = ℓ₂-sum of the (ℝ^m, ℓ₁) (v_E ≤ v_X always), with linear duality: flows in
  ℓ₂(ℓ_∞). There the parallelogram law fails and the image of the parent's optimal flow can be infeasible for a child
  (path ℓ –(p+q)– h, h –p– c, h –q– d on a tripod, b-child at r′ = p−q), yet the child has other feasible flows. This is
  the formulation used for the numerical test.

### 5.5 Numerical tests of Lemma S [N] (run before the proof was found; they agree with it)

Conic programmes (Clarabel through cvxpy) in the Banach relaxation E of products of pods and lines; "no violation"
is then rigorous for the pod products up to solver accuracy.

**(a) Stepwise form on random parents** (`lemmaS_step.py`): hubs h₁, h₂ (identified in 30% of the cases, joined by a
wire in 40% of the rest), each attached to 1–3 finite legs (30% with pod coordinates at the branch point), bits in
[0.2, 1.5]; crossed wires (h₁,c;p), (h₂,d;q), c, d legs or a third hub with 2–3 legs.
gap = 1 − (r_c² + r_b²)/(2(p²+q²)), thresholds computed with a slack 10⁻⁶(1+|v|) on the parent value.

| space | parents | min gap | gaps < 10⁻³ (tight cases) | negative |
|---|---|---|---|---|
| ℝ³ | 300 | 8.8·10⁻⁶ | 4 | 0 |
| tripod × ℝ | 300 | 3.4·10⁻⁶ | 7 | 0 |
| tripod × ℝ² | 300 | 8.4·10⁻⁶ | 4 | 0 |
| tripod × tripod | 300 | 3.3·10⁻⁶ | 13 | 0 |
| tripod, degenerate ("tie") parents: integer bits, unit positions | 400 | 2.6·10⁻⁶ | 45 | 0 |
| tripod × ℝ, tie | 400 | 4.1·10⁻⁶ | 18 | 0 |
| tripod × tripod, tie | 400 | 3.0·10⁻⁶ | 12 | 0 |
| tripod × tripod × ℝ, tie | 400 | 4.0·10⁻⁶ | 9 | 0 |

(The positive minimum is the slack; the tight cases have r_c² + r_b² = 2(p²+q²) to 10⁻⁵.)

**(b) Depth-2 game on three wires** (`lemmaS.py`): step 1 crosses wires 1, 2; at step 2 the cover may stop or cross
any two of the six wires of the resulting system (15 options, among them the bond with wire 3 = Sra's nesting and
pairs sharing a hub); the adversary wins a subtree iff some (ρ,ρ′) on the second circle makes both leaves ≥ T.
R_c, R_b = least first bonds for which the adversary wins against all options; margin = 1 − (R_c²+R_b²)/(2(p²+q²)).

| space, legs | instances | min margin | max (R − depth-1 threshold) |
|---|---|---|---|
| ℝ³, far legs (calibration) | 2 | −8·10⁻⁶ | 5·10⁻⁶ |
| tripod × ℝ, far legs (lines through the origin) | 19 | −9·10⁻⁶ | 7·10⁻⁶ |
| tripod × tripod, far legs | 14 | −8·10⁻⁶ | 7·10⁻⁶ |
| tripod × ℝ, finite legs | 14 | −4·10⁻⁶ | 8·10⁻⁶ |
| tripod × tripod, finite legs | 14 | +4·10⁻⁶ | 8·10⁻⁶ |

(Tolerance of the bisection: 2·10⁻⁵.) With far legs through one point the game is exactly tight, as in Hilbert
space; in every instance the nested options require no larger bond than depth 1. No candidate violation; nothing to
confirm in exact arithmetic.

---

## 6. P4: the adversary, and what the sequence of levels can converge to

- **Level 1.** At the two-merge corner the adversary's metric is the flat one of `vpvnp/b2` (orthogonal simplices for
  rows and columns, far legs): CAT(0), and a price under FH. At uniform weights level 1 has value ≈ 0.77 and the
  binding dual solutions are not metrics of the price type at all (the third-merge cost of a rectangle piece is
  ≥ raw, a constraint no price sees). So level 1 is stuck for a reason that has nothing to do with the geometry.
- **Depth ≥ 2.** By Theorem W every depth has certified value ≥ F_CAT(configuration), unconditionally, and the
  best certified value is ≤ the level-1 value.
  I did not compute a depth-2 game on a net: for nets with F_CAT = 1/√2 there is nothing to find, and for the others
  the design space (which hub–hub bonds to cross with which wires, evaluated under which later merge) is large;
  §1.3 shows that nested pieces certified by aligned cuts reduce to rectangles, so a gain could only come from
  non-aligned evaluations (5.1) of nested pieces.
- **F_CAT.** The Q1 agent reports [D, unreviewed; `sat3/q1-notes.md`] that for nets of F₂^m the space of real
  filtrations of F₂^N (cone over the spherical building of GL_N(F₂), times ℝ; CAT(0) unconditionally) carries a
  placement of value exactly 1/√2 on generic edges, with the equality structure of §7, and that every finite subset
  of it is a price when contracting fails. If the placement stands, then for 3-nets of F₂^m:
  (i) **the certified level value of crossing-generated covers of every depth is in
  [1/√2 − 1.121/(g+1), level-1 value], both ends → 1/√2** (Theorem W; needs only CAT(0)); this is a statement
  about what the certificates can prove, not about the true costs of the terms;
  (ii) if moreover its price claim stands and contracting fails, **no engine of any kind** with three net merges
  has true level value below 1/√2 − c/g (price method, all covers; `q1-notes.md` Theorem B, refereed): Q1 of `notes.md` is answered for these nets and the window
  closes at exponent 1/2; (iii) if contracting holds, 3-SAT is power-saving by other means.
  Nets of Z₃^m, Z_p^m, Z₄ are not covered by that construction (its message: no realisation for Z₃). There the
  floors are the tree-product ones (0.6124 for F₃^M, F₄^M; 0.5857 for cyclic groups by the referee's correction of
  `notes.md`), valid for crossing-generated covers unconditionally (Theorem W) and for all covers when contracting
  fails; the window up to 0.7071 is open, and by §2.2 it cannot be entered by pieces that are "cheap for two merges,
  raw or worse for the third".
- **Can the levels converge below 1/√2?** For F₂^m-nets, as far as certified values go: no (given the Q1 placement),
  up to the O(1/g) window. In general the certified value of the nested crossing family cannot go below F_CAT, and nothing computed here suggests that it goes below the level-1 value
  at all: in the depth-2 tests of §5.5 the nested options never forced the adversary to a larger bond than depth 1.
- **So which way is the barrier question settled?** For the crossing-generated family on F₂^m-nets, in terms of
  certified costs: there is a barrier at exponent 1/2, and its extremal metric is a genuine CAT(0) placement. Whether that metric is a price is
  the Q1 agent's claim and decides the statement for all covers.

**Addendum (after the hand-back; the Q1 agent's correction of scope, its claims, unreviewed; `sat3/q1-notes.md`).**
The filtration construction works over every finite field F_q (V = F_q² ⊕ F_q^m, hubs = points ⟨(x,y)⟩, nodes = graphs
of a ∈ Mat_{m×2}(F_q); the filtration space of F_q^N is CAT(0) for every q), and pulls back along quotients
Γ → F_q^m with F_CAT(net of Γ) ≥ (1/√2)(1 − q^{−m})(1 − q^{1−m}). So the sentences above that exclude Z₃^m, Z_p^m, Z₄ are
superseded: with Theorem W, the certified level value of crossing-generated covers is ≥ 1/√2 − O(1/g) on the 3-nets of
Z_p^m (m ≥ 2, any prime p),
and of Z_4^m, Z_n^m, Z_p × Z_p in the limit. Not covered: cyclic groups (hence Δ₃ and K₄), perfect groups, Latin
squares that are not group tables; there the floors of this note stand (Δ₃: 2/3; cyclic: 0.5857) and the window to
0.7071 is open. Its proposed finite testbed for a depth-2 computation: the translation class E_D of the order-4 net
X₄ (8 disjoint wires, three merges into 4 groups, F_CAT = 1/√2, four AN crossings for any two merges); by Theorem W no
crossing-generated cover can go below 1/√2 there, so a depth-2 computation on it can only confirm the barrier.


---

## 7. Equality structure for value 1/√2 (sent to the Q1 agent) [D]

Normalise δ = 1. Equality in the pairwise cap (`notes.md` Cor. 3.4) for all three pairs forces:
(a) for every node the three hubs are pairwise at distance 1 with a common midpoint z(n) (symmetric tripod, arms ½;
from Prop. 3.5: the mean tripod excess must be δ²/12 and X = ρ²/3 for arm ρ);
(b) for every generic pair |z(n)z(n′)| = 1/√2, the edge's legs lie far out on a line through z(n), z(n′), and the three
arms at z(n) are horizontal for both ends; locally tripod × flat;
(c) the flat two-merge optimum has this for rows and columns (R_r = (ξ_r, 0, h), C_c = (0, ξ_c, −h), z = (ξ_r/2, ξ_c/2, 0));
(d) the diagonal hub D_d cannot be attached by gluing along a convex set containing the g centres of its nodes
(the distance from D_d would be convex, equal to ½ at the centres with non-negative derivative inwards, hence
constant, contradicting CN at a midpoint): seen from each hub the centres of its nodes lie in pairwise "opposite"
directions; (e) in products of trees exact equality forces, in every factor, each node's hubs to form a symmetric
tripod or to coincide, and the resulting families give at most 1/3 per merge in the cases I worked out; (f) the cone
over the incidence graph of the net with edges π/3 gives Φ = 9/4 < 3.
The Q1 agent's space realises (a)–(c) with branching along every segment [hub, z(n)], consistent with (d).

---

## 8. Dead ends

- [X] Level-1 three-class game below 1/√2 (§2, §3).
- [X] Splitting the bits of an edge among the three rectangle types: worse than one type for every w (§2.2).
- [X] p-nets with more classes for level-1 pieces: a rectangle piece is cheap for two merges only; more merges
  dilute (§2.2).
- [X] Sra/Khoruzhii identities as engine pieces on nets (§1.3, §4.2).
- [X] Majdoddin Prop. 4.23 as a barrier for the D1 game (§4.1).
- [X] Weak duality for all CAT(0) placements at all depths by a potential with fixed hub positions: the leaf step
  fails across merges (§5.1). Withdrawn from my first note.
- [X] Lemma S via a crossing inequality linearised at the parent optimum: false in a tripod (§5.4). The proof
  interpolates two child configurations instead (§5.3).
- [X] A violation of the depth-2 game in pod × ℝ (which would have been a contracting-proof candidate): none in the
  tests, and Lemma S excludes it for crossing-generated covers.
- [X] θ-grid for the adversary in the LP: misses the kink at r′ = |p−q| and reports values below the pigeonhole
  floor with one merge (3.9993 against 4 on K₄). Use breakpoints.

---

## 9. Next steps and specs

1. **Referee** for §5 (weakest points first): (a) Lemma S — the identification of r_c as a supremum, steps (i)–(iv),
   the use of `notes.md` Prop. 3.1; (b) the class of §5.1: is every realisation a cover can certify from B.2 + A.3
   really one of the moves, and is (5.1) the right leaf cost (legs never used as hubs; the bits at a leg);
   (c) Lemma 5.3 (zero loss): check the quoted bound (K2) against Lehmer / Bessenrodt–Ono, rerun `zeroloss.py`, and
   the case analysis of Step 2; (d) §1.3. [Done once: `review-thmW.md`; (c) is new since that report.] A Lean statement of Lemma S is short: CAT(0) space,
   finite weighted graph with some vertices fixed, the two children, the inequality r_c² + r_b² ≤ 2(p²+q²).
2. **Referee for the Q1 placement** (CAT(0)-ness of the filtration space, the placement, the value on generic
   edges, the far-leg limit in the normalisation of §5.1). Theorem W turns it into an unconditional statement about
   the crossing-generated family, so it should be checked independently of the price claim.
3. **Depth-2 game on a net**, restricted: after a rectangle step for (k,k′), cross the hub–hub bond of one rectangle
   with the bond of a second rectangle sharing a line of a third class, evaluate all leaves by (5.1) under the three
   merges (a small LP per term type; g = 3, 4). This is the only nested shape I can name that is not reduced to
   rectangles by §1.3. Expected: no gain; value needed for a gain: any term type with ⟨w, c⟩ < 1/√2 for a w with all
   w_k > 0.
4. **Exact certificates** for the table of §2.1 (rational LP over ℚ(√2): the two-merge values and K₄), through the
   executor (`tools/tensorlab`, modules `opt`): the dual solutions are y ≡ 1/√2 on generic edges and ½ on straight ones.
5. Other groups: F_CAT for 3-nets of Z₃^m, Z_p^m, Z₄ (the Q1 agent's problem). Any value < 1/√2 there leaves the
   window open for those nets and makes the depth-2 game of item 3 worth computing; a value of 1/√2 closes the
   crossing-generated family on all nets.
6. Outside the class: identities not generated by B.2, and true ranks of Ψ_N below the certificates (`ports/protocol`
   §1.3 found the certificates nearly sharp at small sizes). `notes.md` §7 item 5 (a three-way identity on a
   translation class) is unchanged and is the only route that Theorem W does not touch.

---

## 10. The depth-2 certified game on small nets (added after the referee round) [N unless marked]

Question: by Theorem W (now without loss) the certified value of nested crossing covers is ≥ F_CAT at every depth.
On cyclic nets F_CAT is not known to reach 1/√2 (tree-product records 0.5519 at g = 5, 2/3 on Δ₃). Is there a nested
cover with certified value below the level-1 value?

### 10.1 What can be said before computing [R/D]

- **At the two-merge corners no depth helps.** For w = (½,½,0) the flat orthogonal-simplex placement gives
  Σ_k w_k b_k = (E_gen/√2 + E_straight/2), which is the level-1 value h₁(½,½,0) (0.638071 at g = 5). Theorem W: every
  crossing-generated cover of any depth has a term with ⟨w, cost⟩ ≥ that. So V₂ < V₁ requires an **interior** weight
  vector w with h₂(w) < V₁, i.e. a drop from h₁(w) ≈ 0.66–0.77 to below 0.638 at g = 5 (in the limit: from ≈ 0.8 at
  uniform weights to below 0.7071).
- **Near a corner** (w = (½−ε, ½−ε, 2ε)) the first-order change of the value is 2ε·(c₃ − 1/√2) per generic bit, c₃ = the
  third-merge cost of the pieces that realise (1/√2, 1/√2) for rows and columns. A gain needs pieces certified below
  1/√2 under all three merges. Level-1 rectangles have c₃ = 3/2. Nested pieces are worse placed: a nested piece
  commits to ONE cut of its first piece (the factorisation U_α(a,b)V_α(c,d) whose index is crossed), so it loses the
  second alignment of a rectangle; its certificates are across {a,b,x | c,d,y} and {a,b,y | c,d,x}, and by §1.3 these
  can be aligned with two different merges only if a = b and c = d.
- So a gain can only come from non-aligned evaluations (0-extensions that move bits), as on Δ₃ at level 1.

### 10.2 The game computed (type A) and how

**Strategies.** F = (e, e′, e″; p, q, s): step 1 crosses e = (a,c) [p bits] and e′ = (b,d) [q bits]. After seeing θ₁ the
cover either *stops* (level-1 realisation of Ψ_{θ₁} per merge, the s bits of e″ = (x,y) stay raw), or *commits* to cut c
(hubs O ∋ a,b; O′ ∋ c,d; bond r = r(θ₁)) or to cut b (O ∋ a,d; O′ ∋ b,c; bond r′(θ₁)) and crosses that hub–hub bond with
e″: adversary θ₂, (ρ, ρ′) on the circle of radius² 2(r²+s²). The leaf is the tree
legs → O — U — U′ — O′ ← legs with x, y attached to U, U′ (cut c′) or to U′, U (cut b′); under merge k its certified cost is
the min 0-extension of O, U, U′, O′ to the groups, an exact DP, of the form min(M_c, S_c + ρ, M_b, S_b + ρ′) (second cut
chosen per merge). Value

    val_w(F) = max_{θ₁} min( stop(θ₁) + s·raw_w(e″),  max_{θ₂} Σ_k w_k cost_k [cut c],  max_{θ₂} Σ_k w_k cost_k [cut b] ).

**LP.** Dual variables y constant on translation classes of edges (and on scalar orbits for prime g); rows: y ≤ raw,
the level-1 rows of §2 (9 split ratios), and p·y_e + q·y_{e′} + s·y_{e″} ≤ val_w(F) for generated strategies. Value =
h₂ᴬ(w), the certified value at weights w when the cover may use level-1 factors and type-A strategies with one third
wire, t = p/(p+q) ∈ {0.2, 0.35, 0.5, 0.65, 0.8}, s/(p+q) ∈ {0.25, 0.5, 1, 1.5, 2.5, 5}.

**Generation and verification.** A coarse sweep (17 × 65 adversary grid) over all (e up to symmetry, e′, t, s, e″)
proposes candidates; coarse values are below the true ones, so every true violation is among the candidates. A
candidate is added only if its **accurate** value (exact maximisation over θ₂ at breakpoints and stationary points,
161-point grid over θ₁ with two zooms; `depth2acc.py`) is below its priced bits. This matters: on Δ₃ at the corner
the coarse sweep "found" 0.9007 against level-1 0.9093, and the accurate value of that strategy is 0.9099.
Scripts: `depth2b.py` (strategy values, LP), `depth2acc.py`, `depth2c.py` (driver); outputs `attain/out3/`.
A first test `depth2.py` (the adversary keeps the level-1 maximiser θ₁*) is too rigid and is superseded.

**Not covered.** Crossing two hub–hub bonds (two level-1 pieces: three adversary angles, pairs of pairs of edges);
strategies whose third wire depends on θ₁; routing before crossing ("bundles": checked only as the r = p+q special
case, which is never better than the adaptive strategy); depth ≥ 3; continuous t, s.

### 10.3 Results

Δ₃ standalone (9 edges; floor 2/3 by Theorem W):

| weights | level 1 (9 ratios) | level 1 (39 ratios) | with type-A depth 2 |
|---|---|---|---|
| (⅓,⅓,⅓) | 0.939512 | — | **0.929966** |
| (0.56, 0.22, 0.22) | 0.899041 | 0.897537 | 0.896035 |
| (0.60, 0.20, 0.20) | 0.895391 | 0.892861 | 0.891594 |
| (0.62, 0.19, 0.19) | 0.893587 | 0.892067 | **0.891022** |
| (0.64, 0.18, 0.18) | 0.892844 | **0.891902** | 0.891518 |
| (0.66, 0.17, 0.17) | 0.893131 | 0.892778 | 0.893056 |
| (0.70, 0.15, 0.15) | 0.896660 | 0.896660 | 0.896660 |
| (½, ½, 0), (0.5, 0.3, 0.2) | 0.909268 | — | 0.909268 (no verified strategy) |

Game value (min over weights): level 1 = 0.89190; with type-A depth 2 ≤ 0.89102. **Depth 2 is strictly below
level 1 on Δ₃, by 0.1%** (1% at uniform weights). Binding strategy at uniform weights: one edge from each
anti-diagonal triangle, e = (0,0)–(1,2), e′ = (1,1)–(2,0), e″ = (0,1)–(1,0), p = q = ½, s = 1; at the adversary's θ₁ = 0.952
the three options tie (stop + raw third wire = nest via cut c = nest via cut b = 1.85993 for 2 bits). It is genuine
adaptivity: the non-adaptive bundle versions give 0.971 and 1.000.

Full net of Z₅ (300 edges; two-merge value 0.638071 = V₁; tree-product record for F_CAT 0.5519):

| weights | level 1 | with type-A depth 2 | verified strategies |
|---|---|---|---|
| (½, ½, 0) | 0.638071 | 0.638071 (Theorem W: no depth can go lower) | — |
| (0.48, 0.48, 0.04) | 0.659215 | 0.659215 | 0 (12 coarse candidates, none survives accurate evaluation) |
| (0.45, 0.45, 0.10) | 0.690931 | 0.690931 | 0 (12 coarse candidates, none survives) |
| (⅓, ⅓, ⅓) | 0.773945 | 0.771218 | 36 (108 coarse candidates; second round: none) |

The 36 strategies at uniform weights are the Δ₃ strategy transplanted: three generic edges, p = q = ½, s = 1, value
1.85993 for 2 bits (e.g. e = 0–8, e′ = 6–15, e″ = 5–18 in the numbering node = 5r + c).

### 10.4 Reading

1. **On the tower level (Z₅) depth 2 of type A does not lower the game value.** The value of the game is the
   minimum over weights; it stays at the two-merge corner, 0.638071, where no depth can help (§10.1). Near the corner
   no type-A strategy beats level 1 at all (h₂ᴬ = h₁ at (0.48,0.48,0.04) and (0.45,0.45,0.1)); at uniform weights
   nesting gains 0.35% (0.7739 → 0.7712), far from the 17% that would be needed to get below 0.638.
   So: depth-1 value 0.638071, depth-2 (type A) value 0.638071, CAT(0) record 0.5519. The room [0.5519, 0.6381]
   allowed by Theorem W is not entered by these strategies.
2. **Nesting is not empty.** On Δ₃ alone, where level 1 has no rectangles and sits far from its floor, an adaptive
   depth-2 strategy is strictly better than level 1: 0.8919 → 0.8910 for the game value, 0.9395 → 0.9300 at uniform
   weights. The mechanism is the choice, after θ₁, between stopping and nesting through either cut; it trades the
   adversary's level-1 optimum against the nested costs. It is a second-order effect of the same kind as the level-1
   gain on Δ₃ (non-aligned evaluations with moved bits), it does not need three merges to be cheap at once, and it
   disappears where rectangles are available and tight.
3. **What an exponent gain would need, honestly.** In the limit g → ∞ the two-merge corner value is 1/√2 and is
   protected at every depth. A gain needs some interior w with certified value below 1/√2; level 1 has ≈ 0.80 at
   uniform weights and slope 2ε(3/2 − 1/√2) > 0 at the corner. The nested strategies found change the uniform value in
   the third digit and the near-corner values not at all. Nothing computed here points to an interior value below
   the corner value; the first-order obstruction of §10.1 (a nested piece keeps one alignment, not two) is the
   reason I expect none from type A at any g.
4. **What would decide it.** (a) The type-B game (two hub–hub bonds crossed) at g = 5 near the corner: the only
   depth-2 move in which both first pieces keep an alignment each; if it also returns h₂ = h₁ at (0.48,0.48,0.04),
   depth 2 is closed on Z₅ for all practical purposes. Size: pairs of rectangles sharing a line, three adversary
   angles; an afternoon for the executor with the DP of `depth2b.py` extended to six hubs. (b) Z₇ with the present
   code at (0.48,0.48,0.04) and uniform weights (about 8 times the Z₅ work) to see that the uniform-weight gain does
   not grow with g. (c) The Q1 agent's cap for cyclic nets: if F_CAT(cyclic) = 1/√2 − O(1/g) after all, Theorem W
   closes the question without any game.
5. **Caveat on "exact".** h₂ᴬ is exact for the stated strategy class up to the grids in t and s and up to candidates
   below the coarse threshold 10⁻⁶ per bit; it is an upper bound on the certified value at each w (every added
   strategy was verified accurately) and, being a restricted class, not a lower bound for all depth-2 covers.

## 11. Type B on Z₅ and Δ₃: crossing two hub–hub bonds (executor run) [N unless marked]

### 11.1 Strategy class (exact statement)

F = (P₁, P₂; t₁, t₂, u). P₁ crosses e₁ = (a₁,c₁) [p₁ = t₁ bits] with e₁′ = (b₁,d₁) [q₁ = 1−t₁]. P₂ crosses
e₂ = (a₂,c₂) [p₂ = u·t₂] with e₂′ = (b₂,d₂) [q₂ = u(1−t₂)]. The adversary picks θ₁ and θ₂. Bonds follow §1.2: r_c = min(R cos θ, p+q)
across ab|cd and r_b = min(R sin θ, p+q) across ad|bc, with R² = 2(p²+q²).
After seeing (θ₁, θ₂) the cover chooses one of five options:
- **stop**: both pieces are realised at level 1 under each merge, with the cost table of §1.2 including the corrected row S = p+q+min(p,q).
  This is `game1.consts`, cost stop₁(θ₁) + stop₂(θ₂).
- **nest**: commit to a cut of each piece (4 choices). This gives hubs O₁ | O₁′ with bond r₁ and O₂ | O₂′ with bond r₂. Then cross the two
  hub–hub bonds. The adversary picks θ₃, with R₃² = 2(r₁²+r₂²) and cap r₁+r₂. ρ is the rank across O₁O₂ | O₁′O₂′ (cut c′)
  and ρ′ the rank across O₁O₂′ | O₁′O₂ (cut b′).
- **leaf** under merge k: the tree legs → O₁ −r₁− U −ρ− U′ −r₁− O₁′ ← legs, with O₂ −r₂− U and O₂′ −r₂− U′ (cut c′), or O₂ at U′ and O₂′ at U
  (cut b′). Its cost is the exact minimum 0-extension of the six hubs to the g groups, computed by a tree DP and
  checked against brute force over all g⁶ placements. The second cut is chosen per merge, so
  cost_k = min(M_k, Sc_k + ρ, Sb_k + ρ′).

  val_w(F) = max_{θ₁,θ₂} min( stop₁ + stop₂,  min over the 4 cut pairs of max_{θ₃} Σ_k w_k cost_k ).

The third wire of type A does not appear here. There is no adaptivity beyond the choice after (θ₁, θ₂) and the
choice of the second cut per merge. Grids: t₁, t₂ ∈ {0.2, 0.35, 0.5, 0.65, 0.8} and u ∈ {0.25, 0.5, 1}. The first two
are the type-A t grid. Because val is homogeneous and symmetric under P₁ ↔ P₂, the u grid covers u ∈ {0.25, 0.5, 1, 2, 4}.
All unordered pairs of distinct edges are allowed for P₁ and for P₂, and P₂ may reuse edges of P₁ (other bits).
On Z₅, P₁ runs over the orbit representatives of pairs under translations × scalars × (r,c)↦(c,r). The last map is used only when
w₀ = w₁; there are 270 orbits, or 504 without the swap. P₂ runs over all 44850 pairs.
The LP is the dual of §10.2 with y constant on translation classes and symmetrised. Its rows are y ≤ raw, level 1 with
**11** ratios (the 9 of §2 plus 0.35 and 0.65, so that every t used by type B is also a level-1 row; this moves
the uniform level-1 value from 0.773945 to 0.773799 and nothing else in the tables), type A (the §10 code,
`depth2c.sweep/verify`), and type B. Each verified row is added together with all its images.

**Maximisation and verification.** θ₃ is maximised exactly in every evaluation: the candidates are the breakpoints and
the stationary points of a·cos + b·sin, and this is tested against a 20001-point grid. A type-B strategy passes three stages.
1. Filter, a valid lower bound on val. The adversary plays the level-1 maximisers (θ₁*, θ₂*) and θ₃ is exact, so the bound is
   min(m₁ + m₂, nests at θ*). It runs over all quadruples and all 75 splits.
2. Coarse lower bound: a 17×17 grid plus θ*.
3. Certified bracket [lo, hi] by branch and bound on (θ₁, θ₂), tolerance 10⁻⁶. The upper bound per box is rigorous by
   monotonicity: each nest option is nondecreasing in the bonds (r₁, r₂), and r_c, r_b are monotone in θ. The stop
   term is bounded the same way.

A strategy is counted, and its row added with right-hand side **hi**, only if (priced − hi)/(bits) > 10⁻⁶.
Lower bounds can only produce false candidates, never false rows. Constraint generation repeats (type A and type B)
until a round adds nothing.

Tests (`depth2B_tests.py`): piece constants and level-1 maxima are identical to `game1` (0 mismatches in 200). The leaf DP
equals an independent brute force over 5⁶ hub placements in 200 of 200 random cases. Exact θ₃ is ≥ every grid value and
matches a refined grid to within 1e-7. The B&B bracket contains the 241² grid maximum.
`depth2B_check.py` re-evaluates a strategy with independent code (brute-force leaf, θ₃ grid, `game1.consts`). For the Z₅
uniform strategy below it gives 1.8503961 on a fine local grid, against the certified [1.850397, 1.850398].

### 11.2 Results

Z₅ (300 edges; two-merge value 0.638071; CAT(0) record 0.5519). Each "+type B" run used the LP with level-1 and type-A rows:

| w | level 1 (9 / 11 ratios) | + type A | + type B | verified strategies A / B | type-B filter: quadruples with a lower bound below priced |
|---|---|---|---|---|---|
| (½, ½, 0) | 0.638071 | 0.638071 | **0.638071** | 0 / 0 | 0 (anchor (a): Theorem W) |
| (0.49, 0.49, 0.02) | 0.648643 | — (not run) | 0.648643 | — / 0 | 0 |
| (0.48, 0.48, 0.04) | 0.659215 | 0.659215 (§10) | **0.659215** | 0 / 0 | **0** |
| (0.47, 0.47, 0.06) | 0.669787 | — | 0.669787 | — / 0 | 0 |
| (0.50, 0.46, 0.04) | 0.659608 | — | 0.659608 | — / 0 | 0 |
| (0.52, 0.44, 0.04) | 0.660784 | — | 0.660784 | — / 0 | 0 |
| (0.55, 0.40, 0.05) | 0.670049 | — | 0.670049 | — / 0 | 0 |
| (0.45, 0.45, 0.10) | 0.690931 | 0.690931 (§10) | **0.690931** | 0 / 0 | 0 |
| (0.40, 0.40, 0.20) | 0.740858 | 0.740858 | **0.740858** | 0 (18 coarse) / 0 | 258 → 0 at the coarse grid |
| (⅓, ⅓, ⅓) | 0.773945 / 0.773799 | 0.771218 | **0.769856** | 24 rows (36 strategies) / 44 | 636 → 112 coarse → 44 certified; second round 452 → 24 → 0 |

"—" = type A not rerun at that w. Type B finds nothing there, so y is the level-1 y, and type A's absence does not affect the type-B column.
At (0.48,0.48,0.04), (0.45,0.45,0.1) and (½,½,0) no strategy gets past even the filter. With the adversary simply
repeating its level-1 angles, every nested option of every quadruple costs at least the priced bits.

**Game values on Z₅ (min over w):** level 1: 0.638071; with type A: 0.638071; with types A and B: **0.638071**. In each case
the minimum is at the two-merge corner, where Theorem W forbids any gain. No verified value anywhere is below 0.638071
or below the CAT(0) record 0.5519.

Binding type-B strategy at uniform weights (44 of them, all one orbit type): three generic classes,
P₁ = (0,7)×(1,5) with t₁ = ½ and P₂ = (6,20)×(7,21) with t₂ = 0.8, u = 1. The value is 1.850397 for 2 bits, at θ₁ = 0.683, θ₂ = 0.843,
where the stop option ties with the nest (b,b) option. This is exactly the Δ₃ strategy (below) transplanted onto
generic edges, as in §10 for type A. The final y gives every generic class 0.9252, which is the Δ₃ uniform value with type B.

Δ₃ standalone (9 edges, floor 2/3; LP with 11 level-1 ratios; type A rows from the §10 code):

| w | level 1 (11 ratios) | + type A | + type B | verified A / B |
|---|---|---|---|---|
| (⅓, ⅓, ⅓) | 0.939002 | 0.929966 | **0.925198** | 18 / 648 |
| (0.40, 0.30, 0.30) | 0.926803 | 0.923920 | **0.920820** | 8 / 144 |
| (0.45, 0.275, 0.275) | 0.917653 | 0.917653 | 0.917653 | 0 / 0 |
| (0.50, 0.25, 0.25) | 0.908503 | 0.908503 | 0.908503 | 0 / 0 |
| (0.56, 0.22, 0.22) | 0.897537 | 0.896035 | 0.896035 | 2 / 0 |
| (0.60, 0.20, 0.20) | 0.892861 | 0.891594 | 0.891594 | 4 / 0 |
| (0.62, 0.19, 0.19) | 0.892205 | **0.891022** | 0.891022 | 4 / 0 |
| (0.64, 0.18, 0.18) | 0.892634 | 0.891518 | 0.891518 | 4 / 0 |
| (½, ½, 0) | 0.908503 | — | 0.908503 | — / 0 |

Δ₃ game value: level 1 ≈ 0.8919 (39 ratios, §10); type A 0.891022; types A and B **0.891022** (not lowered). All values are ≥ 2/3.
Type B helps on Δ₃ only near uniform weights. There it is stronger than type A (0.9300 → 0.9252), with the binding
strategy P₁ = (2,6)×(5,7) at t₁ = 0.2 and P₂ = (2,4)×(3,8) at t₂ = ½, u = 1, value 1.850397 for 2 bits. It does not
help where the game value is decided.

Restriction (c): with the cover forced to stop, val = m₁ + m₂. Since the level-1 rows contain every split used,
priced − m₁ − m₂ ≤ 0 holds for all P₁, P₂; the run reports 0.0. So the stop-only class reproduces level 1 exactly.

Z₇ (item 5, partial): level-1 values only. Two-merge 0.655330 (rectangle formula); (0.48,0.48,0.04) 0.679117; uniform
0.815337 (`out4/level1_z7.txt`). Type A and type B were not run at g = 7. Cost estimates from the Z₅ timings: type A about
20× the Z₅ sweep (2–3 h per round on 4 cores), type B about 70× (≈ 8–12 h per round). So the question "does the
uniform-weight gain grow with g" stays open. The mechanism found here (the Δ₃ strategy transplanted onto
generic triangles) is available at every g. Its effect on the uniform value is bounded by the share of generic edges
that can be placed in such triangles at the Δ₃ rate.

### 11.3 Reading

1. **Type B does not move the Z₅ game value.** Near the corner (w₃ ∈ {0.02, 0.04, 0.06, 0.10}, and two asymmetric
   points) no type-B strategy beats level 1. The reason is strong and simple: even if the adversary just repeats its
   level-1 angles, every one of the four nested options costs at least the priced bits for every quadruple and
   split. The expectation of §10.4(4a) that type B is "the one that could matter" is not borne out. Both first pieces
   keep an alignment each, but no nested option is cheaper than the priced bits. I have not separated which leaf terms
   cause this; the first-order argument of §10.1 (positive slope 2ε(c₃ − 1/√2)) is consistent with it. With (a) and (b) of §10.4, depth 2 is closed on Z₅ for the classes A and B: value 0.638071.
2. At uniform weights type B adds a further 0.18% (0.771218 → 0.769856), by the same Δ₃ mechanism. The total depth-2
   gain at uniform is 0.5% of the ≈17% that would be needed.
3. **Not covered:** a third wire whose choice depends on the angles; mixed moves (type A on one piece and type B on the
   other; three bonds); depth ≥ 3; continuous t, u (finer grids can only lower values); the trivial third-cut bound
   2·min(r₁, r₂) for the bond crossing (not used, following §10's leaf convention); Z₇ beyond level 1. The type-A rows
   are verified by §10's accurate grid evaluation (`depth2acc`), not by the certified bracket used for type B.

Scripts: `attain/depth2B_core.py` (numba kernels), `depth2B_run.py` (driver), `depth2B_tests.py`, `depth2B_check.py`.
Outputs: `attain/out4/` (`run_*.stdout`, `B_*.txt`, `repro_*.txt`, `level1_z7.txt`, `check_z5_uniform_strategy.txt`).
