# hunch-triangle: is the ω = 9/4 triangle the missing three-wire piece?

Theory notes, 26 Nov 2026. Nothing here is committed, machine-checked or refereed.

Tags: **[K]** quoted, with location (K-OA = OpenAI's release of 24 Nov 2026 and its 2 Oct paper, unrefereed and
machine-generated: every use is flagged; K-AN = Anthropic's paper; K-M = Majdoddin arXiv:2610.41622, text at
`scratchpad/pb/arx/p.txt`); **[R]** proved here in full from the cited inputs; **[D]** derived here, unreviewed;
**[N]** numerical (script named); **[C]** conjecture; **[X]** dead, with reason.

Sources read for this note. K-OA Oct ("An Upper Bound of 9/4 …", `preprints/Matrix-Multiplication-Nine-Fourths-
October-2-2026/paper.txt`): all of it. K-OA Nov MM ("The matrix multiplication exponent is nine fourths",
`…/paper.txt`): §§1, 2, 3, 4, 7 (statement, 7.1, 7.4), 8 (statement, 8.1), 11 (start, 11.3), 12 (statement). Not
read: §§5–6, 9–10, 13–27. K-OA HC ("Circuit lower bounds for Hamiltonian cycle and the permanent"): §1.3, §2.2–2.3,
§3.1–3.2, statement of Thm 7.1. K-M: §4.2–4.4, 4.6–4.8. Third-party texts supplied by the coordinator, tagged
[K-unverified]: Liu, hexagon:2611.00994 (§§1–5), Sra, hexagon:2611.01066 (§§1–4). Ours: `sat3/notes.md` (with the
referee's correction to §6), `ports/c1d1/notes.md` D1, `mm/why-nine-fourths.md`, `engine3-STATUS.md`,
`ports/note-k23-rate.md` §0.

Scripts: `hunch/law.py` (output `hunch/law.out`), `hunch/hubfloor.py` (output `hunch/hubfloor.out`).

Convention after the referee's remark: comparisons are in **level values** ρ, not in exponents α′.

---

## 0. Verdict in brief

1. **(c) Dead as a piece [D].** The identity behind ω ≤ 9/4 is a decomposition of the triangle into 2^{(9/4)λ}
   terms that are rank one across all three cuts at once (one label seen by all three parties). The engine needs
   2^{o(λ)} terms that are cheap under *different* merges. The only interpolating family (rectangular partial
   application) is linear: sub-exponentially many terms buy nothing (§1). The degenerations used in the proof have
   exponential error degree, so interpolation does not turn them into few-term identities (§1.4).
2. **The one place where the identity is native is a hub under the merge** (a label shared by three groups = the
   hyperedge K-M leaves uncosted). There the number 9/4 fixes an exchange rate, not a level value: a hub bit is
   worth κ ∈ [3/ω, 3/2] = [4/3, 3/2] pair bits, and the triangle identity trades 3 pair bits for 9/4 hub bits,
   i.e. it has value (3/4)κ ∈ [1, 9/8] in the engine's units. "3/4 against 1/√2" compares a base exponent
   (e₃ = ω/3) with a level factor; it is a units error (§2).
3. **(b) A small barrier [R given K].** Hubs of arity three cannot lower a level value by more than the factor
   2/ω = 8/9: ρ_hub(κ) ≥ (2κ/3)·ρ_pair. With our floors: Δ₃ ≥ 16/27 = 0.5926 and nets of F₂^M, F₄^M ≥ 0.5443 if
   contracting fails; ≥ 0.5132 from flats alone. On Δ₃ with Euclidean prices the hub floor at κ = 4/3 is
   0.5208…0.5212 ([N] below, [R] above). In a tower hubs are native only directly above a rank base (K = 3), so
   the effect is at most one constant factor in e, never a change of ρ* (§2.5).
4. **No value below 1/√2 is attained anywhere in this note.** Everything below 0.7071 is a floor.
5. **The tripod inequality and our tripod prices are not the same object [D]** (§3): ours is a statement about
   wire distances of four or more sites (non-flat CAT(0) metric); theirs links the three-site datum D (label rate)
   to wire distances and holds at every spectral point, flat or not. They meet in exactly one formula, the hub
   floor B_k/max(δ_k, D_k/κ).
6. **No collision** between K-OA's ω = 9/4 and our floors, the CAT(0) property or the K_{2,m} rates (§4).
   ω = 9/4 is claimed in both worlds (ports and no ports).
7. **What the survey of tools gives for P3 [D]:** there are now three tools that bound spectral points on non-wire
   tensors from below (K-OA triangle; Liu's uncrossing at flat points; K-OA HC Thm 11.2, exterior tensors at cone
   placements). None evaluates the attainment condition for a net level. The exact gap is stated in §3.4.
8. **Next step** (§5): decide the label rate of three tips of our √rk pod (contact or not in the sense of K-OA
   Prop. 8.1).

---

## 1. What the upper-bound construction is

### 1.1 The statement [K-OA Oct, Thm 1.1, §§2–5]

Over ℂ: every tensor character (spectral point) λ has λ(T_n) ≤ n^{9/4}. With Strassen duality (their Lemma 2.2,
App. A) this gives ν = inf log_n R(T_n) ≤ 9/4: for every ε some fixed T_u is a sum of fewer than u^{9/4+ε}
**rank-one** tensors. The argument is non-constructive (Pass, arXiv:2610.28627, and Shpilka are cited by K-OA Nov
§1.5 as constructive versions; not read). Over every field: Amanov–van den Berg–Zuiddam [K via K-OA Nov §1].

The ingredients, as tensor statements:
- **Finite separation** (Oct Prop. 3.1): if A = Σ_{h≤M} A_h with the A_h sharing the first leg and living in
  disjoint sectors on the other two, then A^{⊕5M} ⇝ ⊕_h (A_h ⊗ B_X(M)), B_X(M) = a wire of size M between the
  second and third party. Degeneration of degree (M−1)². In prices: a block label seen at two sites is worth
  their distance per bit.
- **Polynomial multiplication** C(a,b) = Σ x_i y_j z_{i+j}, rank a+b−1 by evaluation: it is a restriction of a
  three-way label.
- **Determinant filtration** (Lemma 4.1): C(a,b) ⊗ B_X(2) ⇝ C(a,b+1) and C(a,b−1) sharing the first leg.
  **Shifted tripling** (Lemma 4.2): C(a, 3h+a−1) ⇝ three copies of C(a,h) sharing the first leg.
- Growth lemma 5.1: the symmetrised value P(a,a) ≥ a^{4/3}, against P(a,a) ≤ (2a−1)^{1/t}; so t ≤ 3/4.

In price language (K-OA Nov Prop. 8.1, first part; (11.6)): at every spectral point, three sites at pairwise
distances a_i + a_j have common-label rate

    D(a) ≥ D*(a) = Σa − 1/Σ(1/a) ≥ (8/9)·Σa,        Σa = half the perimeter.

No hub network, no ports, no terms of low rank across one cut appear. The words "hub", "ports", "tripod" of the
24 Nov release belong to the lower-bound side (§3).

### 1.2 Number and kind of terms

2^{(9/4+o(1))λ} terms for the triangle with λ bits per wire (N = 2^λ). Each term is rank one across each of the
three cuts {party} | {other two}. Equivalently: one hub with (9/4)λ bits, joined to the three parties.

### 1.3 The interpolating family and its law [D + N]

The only family I can extract. Split the thicknesses (1,1,1) = x + (1−x), x ∈ [0,1]³, and decompose the x-part
(a rectangular product) into rank-one terms:

    log_N #terms = ω(x),     residual cut rank at party A: r_A = 2 − (the two coordinates of x at A),

    ω(x₁,x₂,x₃) = (x₁x₂+x₂x₃+x₃x₁)²/(4x₁x₂x₃) if each 1/x_i ≤ sum of the other two reciprocals,
                 = sum of the two largest x_i otherwise.

Upper bound: published (AvdBZ, Uznański; via `mm/why-nine-fourths.md` §7). Equality: K-OA Lean claim only
(`why-nine-fourths.md` §7 on paper versus Lean). The law [N, `law.py`]:

- ω is homogeneous of degree 1 and convex (200 000 random pairs, worst violation −4·10⁻¹⁵), hence subadditive.
  So ω(x) + ω(1−x) ≥ 9/4 with equality exactly on the diagonal x = (s,s,s): **partial application never beats
  proportional splitting**, and proportional splitting is linear: τ = (9/4)s label bits for cut ranks 2(1−s).
- Label efficiency: 2(x₁+x₂+x₃)/ω(x) = cut bits removed (summed over the three one-party cuts) per label bit.
  Maximum 8/3 at the square shape (sampled maximum 2.666666). One wire alone: 2. So **one label bit removes at
  most 8/9 of a bit per cut**; conditioning on a wire removes 2/3; the ideal would be 1.
- Legendre duality max{Σ c_k a_k : D*(a) ≤ 1} = ω(x) (300 random shapes, relative error 3·10⁻¹³): the tripod
  inequality and the rectangular formula are one statement.

There is no member of this family with 2^{o(λ)} terms and reduced cut ranks.

### 1.4 Why the degenerations do not give few-term pieces [D]

A degeneration A ⇝ B of error degree L gives B = Σ_{j ≤ L+1} c_j·(restriction_j of A): L+1 terms, each a
restriction of A (Oct Lemma 2.3). This is the one mechanism in the proof that produces "few terms, each cheap".
But (i) in the separation step L = (M−1)² with M = N!/Π(Nq_i)! = 2^{Θ(N)} sectors, so the interpolated identity
has exponentially many terms; (ii) all terms are restrictions of the *same* tensor under the *same* party
structure, so they are cheap or expensive together. An engine identity needs terms that are restrictions of
*different* networks (one per merge). Nothing in the Oct paper has two party structures.

### 1.5 Three numbers that get confused [R for the first, K for the second]

For the triangle with one bit per wire (3 raw bits):

| count | value | of 3 | status |
|---|---|---|---|
| terms of rank one across **one** cut of their choice (few terms, cost = cut rank; or slice rank) | 2 | 2/3 | [R] below |
| terms of rank one across **all** cuts (tensor rank; a hub) | 9/4 | 3/4 | [K-OA] |
| trivial | 3 | 1 | |

**Proposition 1.1 [R, from the quantum functionals as used in K-M Lemma 4.11].** Let T_N = Σ_{i∈I} A_i over ℂ.
Some A_i has rank ≥ N²/|I|³ across each of the three one-party cuts.
*Proof.* For θ = (1/3,1/3,1/3): F^θ(T_N) = N^{Σ_edges (θ_x+θ_y)} = N², F^θ is subadditive on sums, and
F^θ(A) ≤ (R_A R_B R_C)^{1/3}. So some i has R_A R_B R_C ≥ N⁶/|I|³, and each rank is at most N². ∎

So the triangle's own cut configuration **has no trade**: its few-term value is exactly 2/3, the flattening value,
attained by the trivial piece. This is also the Euclidean label floor (perimeter/D = 2 in flats, K-OA EG
Thm 1.1/5.3). The squashed number 3/4 lives in the other row. In the normalisation suggested by the coordinator:

    truth / Euclidean floor = (3/4)/(2/3) = 9/8 for the triangle (label count),

against Sra's nested k-wire crossing [K-unverified, 2611.01066 Thm 1.1], where the Euclidean floor 1/√k is
attained (ratio 1), and against 3-nets, where our floors give ratio ≥ 1.0607 (pods, F₂^M/F₄^M), ≥ 1.1547 on Δ₃,
cap 1.2247, all under ¬contracting. Δ₃ exceeds 9/8, so **there is no universal 9/8 law**; the value
(9/8)/√3 = 0.6495 for nets is numerology and I do not claim it. [C: nothing.]

---

## 2. Translation to the engine

### 2.1 What a three-sided merge is [D]

Under merge k the level tensor of a 3-net of order g is the graph tensor of K_g on the groups with g²λ bits per
pair (plus factors inside groups). For g = 3 it is ⟨N⁹,N⁹,N⁹⟩, and Δ₃ alone is ⟨N³,N³,N³⟩ **under each of the
three merges** (each triangle x+y = const meets every row, column and diagonal once). So the triangle is the
coarse view of the level, three times, on three different triples of groups.

**Definition (hub level).** As `c1d1` D1.1 / `notes.md` §1.1, except that the representation of a piece under
merge k is a network on the groups of merge k with
- pair bonds b_{GG′} (bits), and
- hubs: labels of t_T bits shared by a triple T of groups (arity three only in this note).
The merged instance is then a sum over a hypergraph with edges and 3-hyperedges. Its cost for the downstream
solver is modelled as e_K·(Σ b + κ Σ t), κ = κ_K the **exchange rate** (cost of a hub bit in pair bits). The level
value ρ_hub(κ) is (worst term's Σ b + κ Σ t)/(raw bits). ρ_pair := ρ_hub with hubs forbidden; this is the
quantity ρ* of `notes.md` (pieces may couple bundles; K-M's Prop. 4.23 concerns the smaller class of k-local
pieces).

What it costs is the whole question, and K-M says so ("whose cost the model does not yet define"). Three facts
fix it.

### 2.2 The exchange rate [R given the two K inputs]

**Proposition 2.1.** For every downstream cost that does not increase under restriction (in the asymptotic sense:
tensor powers, 2^{o(λ)} overhead), 3/ω ≤ κ ≤ 3/2. With ω = 9/4: κ ∈ [4/3, 3/2].
*Proof.* A hub of ωλ bits restricts to a bond triangle with λ bits per side (definition of ω; needs only
R(T_N) ≤ N^{ω+o(1)}, the Oct bound [K, re-derived by several groups]). So ωκ ≥ 3. A bond triangle with λ bits per
side restricts to a hub of (2−o(1))λ bits (Strassen: asymptotic subrank of T_N is N² [K, classical]). So
2κ ≤ 3. ∎

In prices the same statement reads (8/9)·hp ≤ D*(a) ≤ D ≤ hp for an equilateral triple (hp = half perimeter =
(3/2)δ): κ_price = D/δ ∈ [4/3, 3/2]; flats sit at 3/2 (K-OA EG), the K-OA optimal point (Nov Cor. 11.1) at 4/3.

**At K = 3 the rate is exact.** With a rank base (matrix multiplication), a merged network on three groups with
bonds (b₁₂,b₂₃,b₃₁) and a hub of t bits costs t + ω(b₁₂,b₂₃,b₃₁) [K: upper bound published, equality K-OA Lean
claim]. A hub bit costs 1, a pair bit of a symmetric triangle costs ω/3: κ₃ = 3/ω = 4/3 iff ω = 9/4.

Remark. ω = 2 would give κ = 3/2 exactly and hubs would be worthless at every level. ω = 9/4 opens the interval
[4/3, 3/2], and its width is the tripod discount 1/9.

### 2.3 The value of the triangle identity [R given 2.2]

The identity replaces a bond triangle (3λ pair bits) by a hub (ωλ hub bits). In the engine's units its value is

    (ω/3)·κ ∈ [1, ω/2] = [1, 9/8].

It equals 1 exactly where κ = 3/ω, i.e. at the K = 3 base, where it is not a piece but the way the base evaluates
a triangle. Everywhere else it is a loss. Consequences for the numerology in the brief:

- "9/4 against 3 is 3/4": this is e₃ = ω/3, the cost exponent per pair bit of the 3-node clique sum, against
  the input floor 2/K = 2/3 (K-M §4.2). ω = 9/4 says the input floor is **not** attained at K = 3. It is a base
  constant e₀ of a tower, not a factor ρ.
- "flattening 2 against 3 is 2/3 = the Δ₃ floor": half coincidence. The Δ₃ pod floor is "6λ of bond bits in every
  merge", and 6λ is also the rank of Δ₃ across one group against the other two. Whether the floor 2/3 is the
  flattening value for a structural reason is w1's conjectural inequality c₁ ≤ c₂ + c₃ (`notes.md` §5.3 remark);
  the triangle adds nothing to it.
- "3/4 > 1/√2, fatal?": not comparable. A level factor multiplies e; 3/4 is a value of e.

### 2.4 How much hubs can gain: the simulation bound [R given 2.2] and the price floor [D]

**Proposition 2.2 (hubs are worth at most 2/ω).** ρ_hub(κ) ≥ (2κ/3)·ρ_pair for κ ≤ 3/2, and ρ_hub(κ) = ρ_pair for
κ ≥ 3/2. In particular ρ_hub ≥ (2/ω)·ρ_pair = (8/9)·ρ_pair for every admissible κ.
*Proof.* Replace every hub of t bits by a bond triangle with (1/2+o(1))t bits per side (subrank, as above; the
conversion is a degeneration of bounded degree per tensor power followed by interpolation, poly(λ) extra terms).
A piece with cost Σb + κΣt becomes a pair piece with cost Σb + (3/2)Σt ≤ (3/(2κ))(Σb + κΣt). ∎

With the floors of `notes.md` (referee-confirmed: 2/3 on Δ₃; 0.6124 on nets of F₂^M, F₃^M, F₄^M):

| configuration | ρ_pair floor | ρ_hub floor at κ = 4/3 | hypothesis |
|---|---|---|---|
| Δ₃ | 2/3 | 16/27 = 0.5926 | ¬contracting (Thm 4.3 of notes, [D]) |
| nets, index-4 subgroup tripod | 0.6124 | 0.5443 | ¬contracting |
| any 3-net, g → ∞ | 1/√3 = 0.5774 | 0.5132 | flats (FH, or K-OA EG) |
| cap for all prices | 0.7071 | 0.7071 | none |

**Proposition 2.3 (price floor with hubs) [D].** Let d be a price on legs and hubs and D_k(T) the common-label
rate of the hub triple T of merge k. For every family Σ A_i = d·f with 2^{o(λ)} terms some piece has, for all k,

    Σ_{GG′} b_{GG′}·|o_G o_{G′}| + Σ_T t_T·D_k(T) ≥ λ(L − H_k) − o(λ)

for every hub network representing it under merge k; hence cost_k ≥ λ·B_k/max(δ_k, D_k/κ), B_k = L − H_k,
D_k = max over triples. *Proof.* As b2 (★): the piece is a restriction of the hub network composed with wires
from the legs to their hubs; prices are monotone and additive; a label on T costs D_k(T) per bit by definition. ∎

What enters about a triple of hubs is only D_k: (8/9)hp ≤ D*(a) ≤ D_k ≤ hp, flats at hp. So:
- against a price whose hub triples are "label-flat" (D = hp), hubs help by at most δ·κ/hp;
- against a price whose hub triples are at the K-OA optimum (D = D*), hubs at κ = 4/3 help by nothing;
- the tripod inequality says no price can do better than that against hubs. **This is the exact role of the
  tripod inequality in the engine: it is the law of the exchange rate.**

**Δ₃ with Euclidean prices [R upper bound, N lower bound; `hubfloor.py`].** By the argument of `notes.md` Prop. 2.2
(balance kills the cross terms) with m_k = max(δ_k, W_k/κ) in place of δ_k:

    (1/3)Σ_k B_k/m_k ≤ 3·√(max over triangles of Σs²/m²) = 3·√(2 + 4(κ−1)²)     (1 ≤ κ ≤ 3/2),

the maximising hub triangle being isosceles with sides (1, 1, 2κ−2). The optimiser attains this to 0.1 %:

| κ | found (per merge, of 9λ) | bound 3√(2+4(κ−1)²) | equilateral hubs (2κ/3)·3√3 |
|---|---|---|---|
| 3/2 | 5.181 | 5.196 | 5.196 |
| 1.4 | 4.869 | 4.874 | 4.850 |
| 4/3 | 4.687 (ρ = 0.5208) | 4.690 (ρ = 0.5212) | 4.619 (ρ = 0.5132) |

(The optimiser undershoots the known value 3√3 at κ ≥ 3/2 by 0.3 %; the printed values are attained by explicit
placements and are valid lower bounds on the supremum. Rows κ = 1.2, 1.0 and the time mode: see `hubfloor.out`.)
So against Euclidean prices the adversary answers hubs by making the hub triangle of each merge isosceles; the
flat hub floor on Δ₃ at κ = 4/3 is ρ = √22/9 = 0.5212 [C for equality, N to 0.1 %].

**The smallest three-sided level in time units [D + N].** Δ₃ → three groups → rectangular matrix multiplication,
everything measured in label bits (no κ): cost of a piece under merge k = min over hub networks of t + ω(b);
for any price, t + ω(b) ≥ λB_k/D_k (because D·ω(b) ≥ Σ b_{ij}d_{ij} at every spectral point, by the rank bound).
- no pieces: (9/4)·3λ = 6.75λ;
- Euclidean floor: sup min_k B_k/W_k ∈ [TIME_LO, 4.243]λ (upper end 3√2: hub triangles collapsed to segments,
  i.e. the price sees merge k as a cut; lower end found by the optimiser);
- a hypothetical pair family at the flat pair floor with symmetric bonds would cost (3/4)·3√3 λ = 3.897λ, below
  this floor: such a family does not exist. In time units the binding flat prices are the collapsed ones.
The window for the smallest three-sided level is therefore [4.15, 6.75]λ of 9λ raw bits, and it contains no
construction (the ALS searches of `engine3-STATUS.md` item 2 found no three-merge identity on Δ₃ at N₀ = 2).

### 2.5 Towers [D]

Let c₂(K), c₃(K) be the downstream costs of a pair bit and of a hub bit on a generic triple, κ_K = c₃/c₂. One
level K′ → K with value ρ on pair bits: c₂(K′) = ρ·c₂(K). A hub on a generic triple of a large net stays a hub
under every merge (two of its nodes share a line of a given class with probability 3/g), so unless hubs can be
rewritten, c₃(K′) = min(c₃(K), (3/2)·c₂(K′)), and

    κ_{K′} = min(3/2, κ_K/ρ).

With κ₃ = 4/3 and ρ ≤ 0.71 the second level already has κ = 3/2, where hubs give nothing (Prop. 2.2). So hubs
matter only at the level directly above a rank base, and the gain is one constant factor ≥ 8/9 in e₀.
Exception: hubs could themselves be traded by "hub-crossing" pieces. At flat points a hub is price-equivalent to
a triangle of wires of half thickness, so flat prices do not forbid a hub trade at the pair rate; I know no such
identity and none follows from the MM papers. [C: open, no candidate.]

Higher arity. A label on m groups: κ_m ≥ 2(m−1)/m from the K_m rank bound 2^{m²/4} (Zhou, arXiv:2610.34273,
third-hand via `why-nine-fourths.md` §15), flat label rate of m equidistant hubs W_m/δ = √π·E max of m standard
normals = 1.5, 1.82, 2.06, 2.25 for m = 3, 4, 5, 6. The ratio κ_m/(W_m/δ) at the lower end of κ_m is 0.889,
0.822, 0.776, 0.742 and tends to 0: **flat prices lose their grip on hubs of large arity priced at the K_m rank
rate.** That rate is realised only by a rank base on exactly those m nodes (e_m = m/(2(m−1)) → 1/2, worse than
trees for large m), so I do not read this as an opening; but the statement "hyperedge floor > 1/2" above is
proved for arity three only. [D]

### 2.6 The other reading of "triangles of hubs" [X]

Three lines of the three classes through a node n give the hub triple (o¹(n), o²(n), o³(n)), one hub from each
merge. A network that uses hubs of different merges at once has 3g line-nodes, and each node table must be
multiplied into one of its three lines: this is an ordinary merge by a partition into partial lines of mixed
classes, not a new operation. It is covered by the price method as it stands (any partitions). The label rate of
(o¹(n), o²(n), o³(n)) never enters a cost. Dead as a separate idea; the mixed partitions themselves are an
unexplored design family. [C]

---

## 3. The lower-bound side

### 3.1 What K-OA's lower bound is [K, statements only]

Nov Thm 2.1: if ω_k < 9/4 over a finite field, every trivalent network of size m ≤ n^{1.05} with e ≥ n exterior
bits has a power V^{⊗d} with a network of size d(m·h^{−γ} + e·h^η), h = log n. Thm 2.2: the list-distinctness
tensor D_w^{⊗t} has volume > t·n_w·w^σ. Iterating 2.1 contradicts 2.2. Part I (§§5–15): a dichotomy on whether a
price-minimising site of a parametrised family moves. If it moves (Thm 7.1, unconditional): a disk tree appears,
a four-tip label has rate ≤ 3/2 of the diameter (7.8), and with a rectangular decoder (Lemma 8.2) and the tripod
principle (Prop. 8.1) the three-tip label rate is 8/3 on the unit tripod, so R(T_n) ≥ n^{9/4}. If nothing moves
(Thm 12.1, needs ω < 9/4): sphere tensors attain the transport bound (Thm 14.1), giving sorting, concentration
and the compression of Thm 2.1.

### 3.2 Tripod inequality versus our tripod prices: not the same object [D]

| | ours (`notes.md` §§3–5) | K-OA tripod principle (Nov Prop. 8.1) |
|---|---|---|
| data | wire distances among ≥ 4 sites (legs, hubs) | three wire distances **and** the label rate D of the triple |
| non-flatness | in the metric: the three hubs of a node span a tripod, X(n) = W − Var > 0 (Prop. 3.5) | invisible to the metric (any three distances are flat); it is D < half perimeter |
| inequality valid everywhere | CAT(0): two bimedians, cap 1/√2 | D ≥ Σa − 1/Σ(1/a) |
| where the extremal geometry comes from | √rk on Mat_μ(F₂) if contracting fails (Thm 4.3) | duality from ω ≥ 9/4 (Cor. 11.1), or a moving family (Thm 7.1) |
| numbers at the symmetric tripod | X/W = 1/4 | discount 1/9 |

The pair-bond cost of the engine never sees D; K-OA's rank never sees more than three sites. They meet in
Prop. 2.3, where both enter. There is one honest bridge:

**Observation 3.1 [D].** Our pods are metric tripods inside price spaces (if contracting fails), so K-OA Prop. 8.1
applies to them as it stands: the label rate at three tips satisfies D*(a) ≤ D(a) ≤ Σa; if the prices on the pod
are radially homogeneous (they can be made so: K-OA HC §2.3, limit H(T; sx)/s), then either D ≡ D* on the whole
pod or D > D* everywhere. In the first case the pod is a spectral point with perimeter/D = 9/4, so
**¬contracting + contact on the √rk pod ⇒ ω ≥ 9/4**, by AN's objects alone and without K-OA Parts II–IV. In the
second case hubs at κ = 4/3 gain against pod prices (by δκ/D < 1). Which case holds is not decidable from the
wire metric; it needs the spectral point behind `thm_alt_rank_price`.

### 3.3 Does their argument transplant to a barrier for three-merge values? [X, with the exact point of failure]

- **The tripod inequality gives no cap on pair-bond floors.** A cap needs an inequality valid at all prices that
  bounds B_k/δ_k. The tripod inequality bounds D from below; D enters only when hubs are allowed, and there it
  bounds what hubs can gain (Prop. 2.2), not what prices can prove. The trivial use (the level tensor under merge
  k is a restriction of a hub with (9/4)·3λ bits) gives B_k ≤ 6.75·D_k ≤ 10.1·δ_k, weaker than B_k ≤ 9δ_k.
- **The dichotomy does not transplant.** Horn (a) produces a spectral point with tree geometry, i.e. more prices.
  That is our Thm 4.3 with "moving family" in place of "¬contracting", and K-OA do not decide whether a moving
  family exists (their proof needs only the implication). Horn (b) needs the false hypothesis to synchronise
  prices; an analogue "three-merge value below X ⇒ synchronisation" has no starting point, because the engine's
  cost is not a rank on one party structure.
- **Thm 2.2 / Lemma 4.1 as an unconditional replacement for WETH** in our dichotomy: Lemma 4.1 (no ports: a fixed
  trivalent topology that routes r wires to uniform destinations among q has size Ω(r√log q)) is the 1/√log law
  as a lower bound. It needs one fixed topology for all permutations. A rewriting level has one layout per term.
  K-OA convert many layouts into one network (Nov Part IV, §26), but they pay for routing records with the
  sorting cost u^p, p < 2, that comes from the false hypothesis. With honest routing the overhead per level is
  polylogarithmic and eats a constant-factor saving. This is the obstruction already recorded in `c1d1` D1.6;
  K-OA's Part IV does not remove it. (I read the statements and §1.4, not §26.)
- **K-OA HC Part I is the nearest relative of our price floors [K, statements; D for the comparison].** In a
  characteristic without ports, HC Thm 7.1 gives, for any L balanced bipartitions of n unit sites in a Hadamard
  cone, two suppliers per cut with simultaneous first-order saving ≥ c·n/√log n. In Euclidean space L cuts give
  n/(2√L). So for L ≫ log n cuts the no-ports floor c/√log n replaces the flat 1/√L. For **three** merges the
  Euclidean value n/(2√3) is larger than c·n/√log n: the theorem says nothing about Q1. For engines with many
  merges (p ≳ log of the number of legs, e.g. p-nets with p ~ g) it would replace the flat floor 1/√p by
  c/√log: a pointer, not a result. [C]

### 3.4 Can their method evaluate the attainment condition for a net? [D]

The condition (K-AN A.6, `notes.md` §7): for every spectral point φ on the fine parties,
φ(f) ≤ max_k sup{φ(A) : A a restriction, with respect to the groups of merge k, of the hub network N_k(c)}.
The left side is trivial (f is a product of wires). The right side asks for the **most expensive** fine tensor
that factors through a cheap coarse network. The price method uses the upper bound "transport + network";
attainment is the statement that this bound is reached at every φ. So:

    level value = price floor   ⟺   at every spectral point there are tensors that nearly attain the
                                     network-transport bound through the hubs of some merge.

Tools that give lower bounds on prices of non-wire tensors, and what each covers:
1. K-OA triangle (Nov Cor. 11.1): one tensor family (the label on three sites) at all spectral points; exact
   range of (wires, label) on three sites if the rectangular formula is exact. No fine structure inside a party.
2. Liu's two-site uncrossing [K-unverified, 2611.00994 Lemma 3.1, Thm 3.2]: at Euclidean planar prices the
   one-excitation tensor V_S and the balanced partition tensors attain the full mean-width price (the label
   price). Evaluates r-party non-wire tensors, flat points only, single hub. Comparison with 1: Liu's tensors are
   as expensive as a label per unit of rank at flat points; K-OA say how cheap a label can be relative to wires
   at non-flat points. Disjoint information; both are about a single hub.
3. K-OA HC Thm 11.2 (statement at HC §3.2): an explicit binary tensor that comes within O(1) per row of the star
   bound d·F(1) at prescribed placements in a Hadamard cone. Single hub (the cone tip), unconditional.
4. K-OA Nov Thm 14.1: sphere tensors attain the transport bound for prescribed leg widths **and expand into
   contractions through legs of controlled width when marked points collide**. This is the shape of tensor that
   attainment needs (max price and a cheap network at once). It is proved under ω < 9/4, which K-OA refute.
5. Sra's Lemma 4.2 [K-unverified]: attainment for k parallel wires and the 2^{k−1} transversal two-sided cuts,
   by composing two-wire crossings; value 1/√k. It works because every transversal cut is two-sided for every
   wire, so the two-wire identity composes. On a net no merge is two-sided for a triangle; K-M Prop. 4.23 is the
   statement that products of two-wire pieces then give ρ = 1.

None of 1–5 evaluates the right-hand side for a hub network with **several hubs** at **every** spectral point.
The triangle computation is the case "one hub, three legs, the tensor is forced (a label)". Verdict for the
second half of the hunch: the machinery does not evaluate the net condition; item 4 shows what a tool of the
right shape looks like and why it is not available.

---

## 4. Consistency checks

1. **CAT(0) [R].** Our refereed statement (prices are CAT(0), `note-k23-rate.md`) and K-OA Nov §3.2 agree. The
   tripod law is consistent with joint geodesic convexity: D* is convex (harmonic mean is concave; `law.py` item
   4) and homogeneous; on a metric tripod, contracting the tips to the centre, convexity with δ(0) = 0 forces
   δ(s) ≤ s·δ(1), and D* gives ≥, so the law is linear along that geodesic, as it must be.
2. **K_{2,m} rates [R].** In the S₃ price of `note-k23-rate` (v's pairwise at √2a, each at a from n and s) the
   tripod inequality gives D(v₁,v₂,v₃) ≥ (8/9)(3a/√2) = 1.886a; the hub bound through n gives D ≤ 3a and the
   subrank bound D ≤ 2.121a. No contradiction, and no information on f*: Theorem K_m involves no label.
3. **Floors against ω = 9/4 [R].** A rank decomposition of Δ₃ under merge k has τ = 6.75λ and no bonds. The price
   bound with 2^τ terms is c_k δ_k + D_S·τ ≥ λB_k (D_S = label rate of all sites, ≥ D of any hub triple
   ≥ (4/3)δ_k). At the pod price B_k = 6δ_k: 6.75·D_S ≥ 6δ_k holds with room. The floor 2/3 concerns 2^{o(λ)}
   terms and pair bonds; ω concerns 2^{Θ(λ)} terms and no bonds. They are the two ends of one inequality.
4. **Does 9/4 hold in both worlds? [K]** Yes as claimed: Nov Thm 1.1 is "over every field". The compression
   (Thm 2.1) does not use ports. The obstruction (Thm 2.2) is proved twice: "fields without ports" (Lemma 4.1,
   σ < 1/2, using HC Thm 6.1 and Cor. 5.2) and "finite fields with ports" (HC Thm 12.1, batch lower bound for a
   signed counting tensor, and the descent of the Euclidean paper Prop. 14.1). The upper bound is field-free.
   I found no notion "no cube" in the texts read; the only world-split is ports / no ports (a Poincaré
   inequality for expanders in all Hadamard spectral spaces of the characteristic).
5. **What ω = 9/4 changes in our numbers.** Only base constants: every "at ω = 2" figure in K-M §4.6 (3.547 at
   K = 4, etc.) is unattainable if K-OA's lower bound holds; e₃ = 3/4, not 2/3. α′ and all level values are
   unaffected.
6. **Sra's attained Euclidean floor against K-OA HC Thm 7.1 [D].** HC 7.1 gives savings c·n/√log n for all
   balanced cuts at once, which for Sra's 2k index sites would force PT-rank exponent ≳ k/√log k, above the
   attained √k, **if** the k wires were star-tight (length 2) in that placement. They are not forced to be:
   CAT(0) only gives mean squared pairwise distance ≥ 2. HC uses a non-wire target (Thm 11.2) for that reason.
   Consistent, and it is `notes.md` §7 item 2 again (attainment is about non-wire tensors).

**Collisions: none found.**

---

## 5. Verdict and next step

**(a)** No three-wire piece family. The triangle identity is not one and does not produce one.

**(b)** Barrier of modest size: arity-three hubs under the merge are worth at most the factor 2/ω = 8/9 per level
(Prop. 2.2, [R given K-OA Oct and Strassen's subrank]), so hub levels on 3-nets have ρ ≥ 0.5132 (flats),
≥ 0.5443 (nets, ¬contracting), ≥ 0.5926 (Δ₃, ¬contracting); in a tower only the level above a rank base is
affected. This gives K-M's "hyperedges under the merge" a cost model and replaces his 1/2 by these numbers for
arity three. It does not close the three-merge window [0.6124, 0.7071) for pair networks.

**(c)** The hunch as stated is dead. Exact reasons: (i) label terms are the wrong corner of the trade (§1.3–1.4);
(ii) as a hub, 9/4 is an exchange rate and the identity has value ≥ 1 (§2.3); (iii) the triangle has no trade of
its own (Prop. 1.1); (iv) the evaluation method covers one hub and a forced tensor, the net condition needs
several hubs and a free tensor (§3.4).

**Single most informative next step.** Decide Observation 3.1: the common-label rate of three (or four) tips of
the √rk pod S_m ⊂ Mat_{2r}(F₂) under the price of `thm_alt_rank_price`, i.e. whether min over spectral points
with that wire metric of D(tips) equals D* = (8/9)·hp (four tips: 3/2 of the diameter, K-OA (7.8)).
- Contact ⇒ ω ≥ 9/4 follows from ¬contracting by a two-page argument (K-OA Prop. 8.1 only), an independent
  check on K-OA's most doubtful claim, and hubs gain nothing against pod prices.
- No contact ⇒ the pods are label-flat, K-OA's optimal point is a different geometry from ours, and the hub
  floor on Δ₃ under ¬contracting is 16/27 and not 2/3.
Concretely: unfold K-AN's proof of `thm_alt_rank_price` to see which tensors certify the rank price, and compute
the value it assigns to the diagonal on {0, I, ι₂(t_p)}; the K_{2,m} structure (Lemma P) gives the four-tip
configuration of K-OA §7.4 directly.
Second choice (computation, 2 h): the flat hub floor for the full AG(2,3) and AG(2,4) levels with hubs of arity
3 and 4 (`hubfloor.py` generalises), to see whether arity-4 hubs at κ₄ = 3/2 push the flat floor below 1/2.

---

## 6. Dead ends

- [X] "3/4 is a level value": units (§2.3).
- [X] Partial application / rectangular shapes as an interpolating piece family: ω is convex and homogeneous
  (§1.3).
- [X] Interpolating the separation degeneration: error degree (M−1)² with M exponential (§1.4).
- [X] A trade on the triangle's own three cuts: Prop. 1.1.
- [X] A cap on three-merge price floors from the tripod inequality: D does not enter pair-bond floors (§3.3).
- [X] Transplanting Lemma 4.1 through K-OA's Part IV: needs the sorting cost that comes from ω < 9/4 (§3.3).
- [X] HC Thm 7.1 for Q1: for three cuts its bound is below the Euclidean one (§3.3).
- [X] Re-running an identity search for bundle-coupling pieces on Δ₃ at N₀ = 2: already done
  (`engine3-STATUS.md` item 2, best residual 0.63); not repeated.
- Not done: reading K-OA Nov §§9–10 (proof of the tripod principle), §§13–27; the Euclidean-geometry paper beyond
  what Liu, Sra and HC quote from it; any check of K-OA proofs.
