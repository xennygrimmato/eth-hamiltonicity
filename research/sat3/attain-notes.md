# sat3 / attainment: the three-class crossing game on nets, and what nested crossing covers can and cannot do

Working notes, 26 Nov 2026. Nothing here is committed, machine-checked or refereed.

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
duality), `lemmaS_step.py` (stepwise Steiner crossing inequality on random parents; `TIE=1` for degenerate parents). Outputs
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
| **Theorem W** (weak duality, all depths) | for every placement in a CAT(0) space, every crossing-generated cover with certified costs, of any nesting depth, has a term costing ≥ λ(L−H_k)/δ_k − o under every merge at once; no spectral point, no hypothesis, no count of terms | [D], §5.3; to be refereed |
| Numerical test of Lemma S | stepwise form on ≈ 2200 parents in ℝ³ and products of tripods and lines, incl. degenerate ones; depth-2 game with all 15 second crossings: no violation, tight cases on the circle | [N]; §5.5 |
| Floor for the crossing-generated family, any depth | F_CAT(configuration): ≥ 1/√3 on 3-nets, ≥ 2/3 on Δ₃, ≥ 0.6124 on nets of F₃^M, F₄^M; = 1/√2 on nets of F₂^m if the Q1 placement stands: there the family is stuck at the two-merge value | [D] |
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
| four different groups | min(p + q + 2min(p,q), 2 min(p,q) + min(r, r′)) |
| a ∼ c, b ∼ d (both wires internal) | 2 min(p,q) — against raw 0 |

A pair is aligned for cut c under k and for cut b under k′ iff a,b,c,d is a (k,k′)-rectangle with the two wires as its
diagonals. On a 3-net the rectangle partner of a generic edge for (rows, columns) has the reflected slope, and under
the third class its four nodes lie in four different groups (three, if the partner is a diagonal-class edge). So:

- for a rectangle piece the cost vector is (r, r′, ≥ 2min(p,q) + min(r,r′)): **under the third merge the piece costs
  more than the raw wires** (raw = p+q). The last row is the K₄ case: the X_j-crossing of K₄ costs up to 2 under the
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
pairwise collinear in the three classes: (r,c), (r,c′), (r′,c′), (r′,c) with r−c = r′−c′ and r−c′ = r′−c, i.e.
2(c−c′) = 0. This is a K₄ of the net; it exists only if G has 2-torsion, and all its six edges are merge-class edges. ∎

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

For a rectangle piece the adversary's θ = π/4 gives (1/√2, 1/√2, ≥ 1 + 1/√2) per bit of raw 1. For any weights
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
- **On nets**: §1.3. The nested identity is inside the class of §5 (crossing applied to a hub–hub bond), so Theorem W2
  applies to it: evaluated in the engine game it can never go below the flat floor.

---

## 5. Weak duality: what is proved, and the lemma that is missing

### 5.1 The class of covers

Parties: the legs, and a set Aux of auxiliary parties created at will. A **wire system** W is a finite list of wires
(u, v; β), β bits, between parties, in which the wires at each leg carry exactly the leg's bits in total (a leg is
never used as a hub; use an auxiliary party instead). W₀ = the edges. GT(W) is its graph tensor.

Moves (each replaces a wire system by one or several wire systems, and the tensor on the legs it stands for by a
cover whose members are restrictions of the new graph tensors):

- (M0) split a wire into wires of smaller bits; route a wire through an auxiliary party ((u,v;β) → (u,y;β), (y,v;β),
  Lemma A.2); increase bits; identify two auxiliary parties.
- (M1) **crossing**: choose two wires (a,c;p), (b,d;q) between any parties (legs or auxiliary: a hub–hub bond is
  allowed, which is Sra's nesting). For every N = 0…Θ the system W_N^{cut}, cut ∈ {c, b} chosen by the cover
  depending on N, is W without the two wires plus
  cut c: (a,o;p), (b,o;q), (c,o′;p), (d,o′;q), (o,o′; b_c(N));   cut b: (a,w;p), (d,w;q), (b,w′;q), (c,w′;p), (w,w′; b_b(N)),
  with new auxiliary o, o′ (w, w′) and the **certified** bonds b_c(N) = log₂((Θ−N+1)P(Θ−N)), b_b(N) = log₂((N+1)P(N))
  of Prop. B.2, or any larger numbers. (Coarsenings such as Khoruzhii's two pieces are covers by sums of the Ψ_N
  with bonds at least these; the "third cut" and single-hub realisations are (M0)-consequences of the trivial bounds.)

By induction (a cover of a tensor restricts to a cover of each of its restrictions) a tree of moves of depth m writes
f = Σ_leaves t_leaf with t_leaf a restriction of GT(W_leaf). **Nesting depth** = the largest number of (M1) moves on a
branch. A leaf is evaluated under a merge k chosen at the leaf, at the certified cost

    cost_k(W) = min over π: Aux → groups of k of  Σ_{wires} β·[π(u) ≠ π(v)]      (π = the group of the node on legs),   (5.1)

a 0-extension: every auxiliary party is executed at some group of the merge. c_k(t_leaf) ≤ cost_k(W_leaf) [R: push
forward along π]. A *crossing-generated cover with certified costs* is such a tree with its costs (5.1). Level 1
(§2) is depth 1 with hubs at groups. Not in the class: realisations that use the true ranks of the Ψ_N where these
are smaller than the certificates of B.2, and any identity that is not produced by B.2.

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
r² + r′² ≤ 2(p²+q²) there is N with b_c(N) ≥ r − ε and b_b(N) ≥ r′ − ε, where ε/(p+q) → 0 as min(e₁,e₂) → ∞.
*Proof.* ln|Σ_i| ≤ ln P(e_i) ≤ κ√e_i, so 2(p²+q²) ≤ κ′²Θ with κ′ = κ/ln 2; b_b(N) ≥ log₂P(N) ≥ (κ′ − o(1))√N and
b_c(N) ≥ (κ′ − o(1))√(Θ−N) (Lemma B.1); take N = ⌈r′²/κ′²⌉ (for bounded N or Θ−N use b ≥ 0 and absorb the loss in ε). ∎
(For the referee: the uniformity of o(1) for N in the middle range is all that is used; at the ends the trivial
bound p+q is available to the cover as well, which only lowers the needed r.)

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

**Theorem W (weak duality for crossing-generated covers).** Let P be a placement of a configuration (nodes, merges,
edges with λ bits) in a CAT(0) space X. For every crossing-generated cover with certified costs (§5.1), of any nesting
depth, there is a leaf with, for every merge k at once,

    cost_k(W_leaf) ≥ [ λ(L − H_k) − D·Σ_{crossings s on the branch} ε(p_s, q_s) ] / δ_k,

D = diameter of the set of leg points, ε as in Lemma 5.2 (ε(p,q) = o(p+q)). In particular, for covers of bounded
depth whose crossings use classes of size → ∞, the level value is ≥ λ|E|·(price value of P) − o(λ|E|).

*Proof.* v(W₀) = λL (S1). The adversary answers a crossing of (a,c;p), (b,d;q) in the current system W with an N such
that b_c(N) ≥ r_c − ε and b_b(N) ≥ r_b − ε (Lemma S, Lemma 5.2; the cover's trivial cap p+q is harmless because
r_c, r_b ≤ p+q). Whichever cut and whichever further (M0) moves the cover makes, v drops by at most ε·D: near-optimal
positions may be projected to the closed convex hull of the leg points (projections onto convex sets are 1-Lipschitz
in CAT(0) spaces, and that hull has diameter D), so a bond smaller by ε costs at most ε·D. The other realisations of
Ψ_N available in the class (single hub, the cut ac|bd, trivial bonds) never lower v, by the triangle inequality. At
the leaf, (S2). ∎

What the theorem is and is not.
- It is unconditional: no spectral point, no FH/EP, no contracting hypothesis, no bound on the number of terms.
- Its class is "everything generated from Prop. B.2 with its rank certificates, Lemma A.3, routing and nesting":
  AN App. B levels, the level-1 game of §2, Khoruzhii's two-piece form (a coarsening), Sra's Lemma 4.2 nesting
  (crossing of hub–hub bonds) are inside. Covers that use true ranks of the Ψ_N below the certificates, or any identity
  not generated by B.2, are outside; for those the bound is the ordinary price method and needs the placement to be
  a price.
- It only gives the inequality "value ≥ sup over CAT(0) placements". Nothing says that nested covers attain it
  (in the K_{2,3} protocol problem the explicit level-1 protocols stay below the CAT(0) bound).
- A second proof for Hilbert space, by duality (it shows where the adversary's N comes from): v(W) = max of
  Σ ⟨F_w, constants⟩ over flows F_w ∈ 𝓗 with |F_w| ≤ β_w in equilibrium at the auxiliary parties; with f₁, f₂ the optimal
  flows on the two wires take r = |f₁+f₂|, r′ = |f₁−f₂| (parallelogram law), and the children inherit feasible flows
  (f₁+f₂, resp. f₁−f₂, on the bond).

**Consequences [D].** With F_X(config) the supremum of price values over placements in spaces of class X:
1. every crossing-generated cover of any depth has level value ≥ F_CAT − o(1) ≥ F_flat: ≥ 1/√2 on balanced
   two-merge configurations, ≥ 1/√3 on 3-nets, ≥ 0.4714 on K₄, ≥ 2/3 on Δ₃ (nine tripods, `notes.md` Thm 5.2 — a CAT(0)
   placement, here used without any price hypothesis), ≥ 0.6124 on 3-nets of F₃^M, F₄^M (subgroup tripods);
2. with the Q1 agent's placement (§6) F_CAT = 1/√2 on generic edges of 3-nets of F₂^m, so **on these nets the
   crossing-generated family is stuck at exactly the two-merge value 1/√2 at every nesting depth**: three merges do not
   help this family at all. This uses only that the filtration space is CAT(0), not that it is a price.
3. Sra's nested identity, evaluated in the engine game, obeys the same floors.

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
| tripod, degenerate ("tie") parents: integer bits, unit positions | 347 | 2.6·10⁻⁶ | 40 | 0 |
| tripod × ℝ, tie | 253 | 4.1·10⁻⁶ | 12 | 0 |
| tripod × tripod, tie | 235 | 3.0·10⁻⁶ | 5 | 0 |
| tripod × tripod × ℝ, tie | 205 | 4.0·10⁻⁶ | 6 | 0 |

(The positive minimum is the slack; the tight cases have r_c² + r_b² = 2(p²+q²) to 10⁻⁵.)

**(b) Depth-2 game on three wires** (`lemmaS.py`): step 1 crosses wires 1, 2; at step 2 the cover may stop or cross
any two of the six wires of the resulting system (15 options, among them the bond with wire 3 = Sra's nesting and
pairs sharing a hub); the adversary wins a subtree iff some (ρ,ρ′) on the second circle makes both leaves ≥ T.
R_c, R_b = least first bonds for which the adversary wins against all options; margin = 1 − (R_c²+R_b²)/(2(p²+q²)).

| space, legs | instances | min margin | max (R − depth-1 threshold) |
|---|---|---|---|
| ℝ³, far legs (calibration) | 2 | −8·10⁻⁶ | 5·10⁻⁶ |
| tripod × ℝ, far legs (lines through the origin) | 13 | −9·10⁻⁶ | 6·10⁻⁶ |
| tripod × tripod, far legs | 9 | −8·10⁻⁶ | 7·10⁻⁶ |
| tripod × ℝ, finite legs | 9 | +1·10⁻⁶ | 8·10⁻⁶ |
| tripod × tripod, finite legs | 9 | +0.15 | 8·10⁻⁶ |

(Tolerance of the bisection: 2·10⁻⁵.) With far legs through one point the game is exactly tight, as in Hilbert
space; in every instance the nested options require no larger bond than depth 1. No candidate violation; nothing to
confirm in exact arithmetic.

---

## 6. P4: the adversary, and what the sequence of levels can converge to

- **Level 1.** At the two-merge corner the adversary's metric is the flat one of `vpvnp/b2` (orthogonal simplices for
  rows and columns, far legs): CAT(0), and a price under FH. At uniform weights level 1 has value ≈ 0.77 and the
  binding dual solutions are not metrics of the price type at all (the third-merge cost of a rectangle piece is
  ≥ raw, a constraint no price sees). So level 1 is stuck for a reason that has nothing to do with the geometry.
- **Depth ≥ 2.** Unconditionally (W2) the value of every depth is in [1/√3, 1/√2]. If Lemma S holds in a CAT(0)
  space X, every depth is ≥ F_X. I have **no depth-2 cover with a computed value below 1/√2**, and I did not compute the
  full depth-2 game on a net (the design space — which hub–hub bonds to cross with which wires, under which later
  merge — is far larger than level 1; §1.3 shows that the natural nested pieces reduce to rectangles when they are
  certified by aligned cuts, so a gain would have to come from non-aligned evaluations (5.1) of nested pieces).
- **F_CAT.** The Q1 agent reports [D, unreviewed, its notes] that for nets of F₂^m the space of real filtrations of
  F₂^N (cone over the spherical building of GL_N(F₂), times ℝ) carries a placement of value exactly 1/√2 on generic
  edges, with the equality structure of §7, and that every finite subset of it is a price when contracting fails.
  If that stands, then for F₂^m-nets: (i) when contracting fails, **no engine of any kind** with three net merges has
  level value below 1/√2 (price method, all covers), i.e. Q1 of `notes.md` is answered and the three-merge window
  closes at exponent 1/2 for these nets; (ii) when contracting holds, 3-SAT is power-saving by other means. For
  crossing-generated covers the same conclusion would be unconditional if Lemma S holds in that space.
  Nets of Z₃^m, Z_p^m, Z₄ are not covered by that construction (its message: no realisation for Z₃); there the window
  [0.6124 or less, 0.7071) for all covers under ¬contracting, and [0.5774, 0.7071] unconditionally for
  crossing-generated covers, stays open.
- **Can the levels converge below 1/√2?** For F₂^m-nets: no, if the Q1 construction and its price claim are right
  (or if Lemma S holds there). For other groups: open; and by §2.2 any gain must come from pieces that are not
  "cheap for two merges, raw or worse for the third".

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
- [X] Lemma S via the linearised crossing inequality: false in a tripod (§5.4, item 3).
- [X] θ-grid for the adversary in the LP: misses the kink at r′ = |p−q| and reports values below the pigeonhole
  floor with one merge (3.9993 against 4 on K₄). Use breakpoints.

---

## 9. Next steps and specs

1. **Lemma S in products of pods** (the open point of §5). Either a proof in the Banach form — flows in ℓ₂(ℓ_∞)
   with legs on the pods; the tree structure must be used, e.g. through the laminar family of minimum cuts of each
   pod factor — or a violation found by a search aimed at tight parents (hubs at branch points, equal bits, several
   pod factors). Spec for the executor: `lemmaS.py`/`lemmaS_step.py` with (i) 10⁴ instances per space in
   {3,1}, {3,3}, {3,3,1}, {4,1}; (ii) structured parents: every pod coordinate of every hub's legs on a different arm,
   bits tuned so that the parent optimum is at the branch point of all factors (degenerate optimum); (iii) exact
   confirmation of any margin < −10⁻³ by enumeration of arm assignments (the true pod product, not the relaxation) and
   by rational arithmetic on the resulting SOCP certificate.
2. **Referee** for §5.2–5.3 (Lemma 5.1, Lemma 5.2's uniformity, Lemma 5.3, the bookkeeping (S1), (S2)) and for §1.3.
3. **Depth-2 game on a net**, restricted: after a rectangle step for (k,k′), cross the hub–hub bond of one rectangle
   with the bond of a second rectangle sharing a line of a third class, evaluate all leaves by (5.1) under the three
   merges (a small LP per term type; g = 3, 4). This is the only nested shape I can name that is not reduced to
   rectangles by §1.3. Expected: no gain; value needed for a gain: any term type with ⟨w, c⟩ < 1/√2 for a w with all
   w_k > 0.
4. **Exact certificates** for the table of §2.1 (rational LP over ℚ(√2): the two-merge values and K₄), through the
   executor (`tools/tensorlab`, modules `opt`): the dual solutions are y ≡ 1/√2 on generic edges and ½ on straight ones.
5. The Q1 construction should be refereed before anything is built on §6.
