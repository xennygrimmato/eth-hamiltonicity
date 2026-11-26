# Explicit protocols on K_{2,3} above the routing rate 3/4

Working notes, 26 November 2026. Tags: [R] proved here (proof given or exact computation), [D] derived here,
not refereed, [N] numerical, [C] conjecture, [X] dead, with the reason. [AN] = Anthropic, "VP ≠ VNP over every
field"; line numbers are those of our text copy. Setting and notation as in `../note-k23-rate.md`.

Scripts (this directory): `crossing_identity_modp.py`, `level1_lp.py`, `level1_game.py`, `level1_dual.py`,
`level1_instance.py`, `square_level2.py`.

---

## 0. Summary

| Item | Value | Status |
|---|---|---|
| Explicit asymptotic protocol, two buckets per crossing ("level 1, coarse") | rate 1/1.20291 = **0.83132** | [D]; needs [AN] Prop. B.2 and two finite LPs |
| Same construction with fine buckets | rate 6/(4+√10) = **0.83772** | [D]; the maximum of the game over term types is [N] |
| Optimality of 0.83772 for "crossing identity with hubs at real parties" | min R over five-point metrics with triangle + all instances of [AN] B.3 on the five points = 0.83772 | [N] (SLSQP, 19/19 starts) |
| Smallest instance with proved rate > 3/4 | classes (n,e) = (8,436) and (21,3000): demand wires of about 2^128 per block, rate 0.7529 as the number K of blocks → ∞ | [D] (exact integer arithmetic for the dimensions and rank bounds) |
| Crossing identity itself | identity (a) and degree ≤ Θ confirmed mod p for classes of dimensions (2,2), (3,3), (5,5), (4,8); all middle terms have full rank at these sizes | [R] (exact computation mod 2147483629) |
| Rates between 0.83772 and 3/√10 | need nested use of the crossing identity (the fan / parallelogram part of thm_cn); indicative value 0.854 for one nesting step | [N], heuristic; no protocol written |
| Lower bound on block length for an arbitrary protocol | none beyond: single-shot uniform needs D_s ≥ 4; in the form T^{⊗m} ≤ S^{⊗n} the first open case is (m,n) = (4,5) | [R] (from the two known obstructions) |

No protocol with rate above 0.83772 is constructed here. No finite instance small enough for a dense check has
rate above 3/4; §5 explains why this construction cannot give one.

---

## 1. What the crossing identity says, as a statement about tensors

### 1.1 The statement [AN, Prop. B.2, l. 1295–1305]

Four parties a, b, c, d. Σ₁, Σ₂ are classes of Frobenius symbols of fixed (size, energy) = (n₁,e₁), (n₂,e₂);
Θ = 2(e₁+e₂); P(N) is the number of symbols of energy ≤ N, and ln P(N) ≤ κ√N, ln P(N) ≥ (κ−o(1))√N.
There are integer tensors Ψ₀,…,Ψ_Θ with index set Σ₁ at a, c and Σ₂ at b, d such that

- (a) Σ_N Ψ_N = ⟨|Σ₁|⟩_{ac} ⟨|Σ₂|⟩_{bd} (the two crossing wires);
- (b) rank of Ψ_N across {a,d} | {b,c} is at most (N+1)·P(N);
- (c) rank of Ψ_N across {a,b} | {c,d} is at most (N′+1)·P(N′), N′ = Θ − N.

In logarithmic units (κ√n₀ nats; wire a–c has log-dimension p, wire b–d has q): term N has log-ranks
r′_N across ad|bc and r_N across ab|cd with **r_N² + r′_N² ≤ 2(p²+q²)**. The trivial bound is r, r′ ≤ p+q, and
√(2(p²+q²)) ≥ p+q, so the ends of the range are trivial; the content is the middle, r = r′ = √(p²+q²) < p+q,
with only Θ+1 = poly(log dimension) terms.

By Lemma A.3 (l. 1085–1113) a tensor of rank ρ across I₁|I₂ is a restriction of the two-hub network
Π_{x∈I₁}⟨n_x⟩_{x o₁} · ⟨ρ⟩_{o₁o₂} · Π_{x∈I₂}⟨n_x⟩_{x o₂}, and the hubs may be existing parties. So:

> **Crossing cover.** The product of the crossing wires a–c (dimension D₁) and b–d (dimension D₂) is a sum of
> Θ+1 tensors Ψ_N. Each Ψ_N is a restriction of **both**
> Net_c(N) = ⟨D₁⟩_{a o}⟨D₂⟩_{b o}⟨D₁⟩_{c o′}⟨D₂⟩_{d o′}⟨ρ_c(N)⟩_{o o′} and
> Net_b(N) = ⟨D₁⟩_{a w}⟨D₂⟩_{d w}⟨D₂⟩_{b w′}⟨D₁⟩_{c w′}⟨ρ_b(N)⟩_{w w′},
> for any choice of the parties o, o′, w, w′, with log ρ_c² + log ρ_b² ≲ 2(log² D₁ + log² D₂).

This is a cover (sum of restrictions), not a restriction. A cover by M restrictions of one tensor X is a
restriction of X ⊗ ⟨M⟩_{all parties}.

The spectral consequence is Prop. B.3: for points of a price and weights p, q there are r, r′ on the circle with
p|xv| + q|yu| ≤ p|xo| + q|yo| + p|vo′| + q|uo′| + r|oo′| and ≤ the same with (w,w′,r′) for the other pairing.
The pair (r,r′) comes from the index N that maximises φ(Ψ_N); it is **the same for all choices of hubs**.

### 1.2 How CN follows in [AN], and which steps are constructive

Chain: B.2 → B.3/(B.2) → Lemma C.2 (parallelogram law for an averaged seminorm) → Theorem C.1 (CN) → C.3, C.4.

| Step | Content | Constructive? |
|---|---|---|
| B.2 | determinant of a polynomial matrix; Ψ_N = coefficient of X^N | yes, explicit integer tensors |
| A.3 | hub networks | yes |
| A.8 / A.7 | new point o placed at old points at random: \|oo′\| ≤ E\|σ(o)σ(o′)\| | as a statement about protocols it is time-sharing: a tensor on the enlarged party set is realised copy by copy by its push-forwards π_i t. The existence of the spectral point φ′ uses Zorn (Prop. A.5). The protocol counterpart of "φ′ is multiplicative" is the adaptive choice of §2.3 |
| C.2 | (B.2) applied to eight lattice points P+g, averaged over boxes, then to long vectors Mc+ie, R → ∞ | only in the limit; each truncation gives a weaker inequality with error O(1/R) |
| C.1 | fan of n²·Tn² random points, four estimates, A → ∞, θ → 0 | only in the limit |
| Strassen duality (note §1.1) | from "all prices satisfy Σ_S ≥ f Σ_T" to a protocol | not constructive; replaced below by an explicit game when the inequality has a finite derivation |

A virtual point is a bookkeeping device: in every copy it sits at a real party. A crossing instance between
virtual points is, copy by copy, a crossing instance between real wires with real hubs. So everything [AN] uses
to prove CN is, on the protocol side, generated by four moves on the real parties: routing, time-sharing,
covers, and the crossing cover of §1.1. "Level k" below means nesting depth k of the crossing cover (the wires
to which it is applied are wires of networks produced at depth k−1).

### 1.3 Reading of the matrix M, and checks [R]

The table of M in our text copy is damaged. The reading implemented in `crossing_identity_modp.py`
(rows I_a, I_d, I_c, I_b; columns J_a, J_d, J_c, J_b; y = X²):

    (a,d): C(i,j)        (a,c): [i=j]X^{2i+1}       (a,b): (y−1)X^{2i+1}B(i,j)
    (d,a): −C(j,i)       (d,c): X^{2j+1}B(j,i)      (d,b): −[i=j]X^{2i+1}
    (c,a): −[i=j]X^{2i+1} (c,d): −X^{2i+1}B(i,j)    (c,b): −(y−1)C(i,j)
    (b,a): −(y−1)X^{2j+1}B(j,i)  (b,d): [i=j]X^{2i+1}  (b,c): (y−1)C(j,i)

With this reading, for (n₁,e₁,n₂,e₂) = (1,4,1,4), (1,6,1,6), (2,12,2,12), (1,8,2,14):
deg Ψ ≤ Θ, and Σ_N Ψ_N = [J_c=I_a, I_c=J_a, J_b=I_d, I_b=J_d] with sign +1, exactly mod p.

Ranks of Ψ_N across ad|bc for (2,12,2,12), dimensions 5 × 5, N = 0, 2, 4, …:
1, 3, 7, 11, 16, 21, 23, 24, 25, 25, …, 25 (and the mirror sequence across ab|cd).
Compare P(N) = 1, 2, 4, 7, 12, 19, 30. So the true ranks are about 1–1.75 × P(N) until they saturate, and
**at these sizes all middle terms have full rank on both cuts: no gain.**

---

## 2. The level-1 protocol

### 2.1 Construction

Split the demand wire u₁u₂ into three factors, one for each pair e = {i,j} ⊂ {1,2,3}. For each e apply §1.1
with (a,c,b,d) = (u₁,u₂,v_i,v_j), D₁ = |Σ₁|, D₂ = |Σ₂|, where log D₁ : log D₂ → 1 : 3 (p = 1/3, q = 1).
One *block* is the tensor ⊗_e C_e, C_e = ⟨D₁⟩_{u₁u₂}⟨D₂⟩_{v_iv_j}; it has u₁u₂ of dimension D₁³ and each v_iv_j of
dimension D₂. Write P = log₂ D₁, Q = log₂ D₂, and for a term its log-ranks r (cut {u₁,v_i}|{u₂,v_j}) and r′
(cut {u₁,v_j}|{u₂,v_i}).

Options for one term of the pair e, all with hubs at real parties (loads in bits on supply edges):

| name | hubs | u₁v_i | u₁v_j | u₂v_i | u₂v_j |
|---|---|---|---|---|---|
| c via u₁ | o = u₁, o′ = v_j | Q | r | – | P |
| c via u₂ | o = v_i, o′ = u₂ | P | – | r | Q |
| b via u₁ | w = u₁, w′ = v_i | r′ | Q | P | – |
| b via u₂ | w = v_j, w′ = u₂ | – | P | Q | r′ |

Meaning of "c via u₁": Ψ = Σ_k α_k(s_a,s_b)β_k(s_c,s_d); v_i sends s_b to u₁ (Q bits), u₁ sends k to v_j
(r bits), u₂ sends s_c to v_j (P bits). With the trivial bound r = P+Q this is routing (v_iv_j through u₁,
u₁u₂ through v_j). So **every bit saved in the rank is a bit saved against routing.** The LP below also allows
all other hub pairs and routes non-edge wires through K_{2,3}.

### 2.2 The game

Take K blocks. T_K = ⊗_{k≤K}⊗_e C_e^{(k)} = Σ_words ⊗_{k,e} Ψ^{e}_{N_{k,e}}. For each word we may choose the
option of every factor separately, knowing the whole word. A word is realised inside S^{⊗n} if the total load
on each of the six edges is ≤ n. Grouping the blocks of a word by their type τ = (N_{12}, N_{23}, N_{13}), what
is needed is: for every type τ there is a **mixture** of options whose average load is ≤ n/K on every edge.
This is a zero-sum game; for fixed τ it is the LP in `level1_lp.py` / `level1_game.py` (variables: weights of
(type c/b, o, o′) for each pair, flows for wires u₁u₂ through v_k and v_iv_j through u_k).

Results, in units where Q = 1, P = 1/3, ρ := √(P²+Q²) = √10/3, A := P+Q = 4/3:

- All-middle type (r = r′ = ρ for all three pairs): value (A+ρ)/2 = (4+√10)/6 = 1.19371. Optimal mixture:
  pairs (1,2) and (2,3) of type c, pair (1,3) of type b (a cyclic orientation 1→2→3→1), each ½ via u₁ and ½
  via u₂. Every edge then carries A/2 from one cycle and ρ/2 from the other. [R: the mixture is explicit;
  the matching lower bound is the uniform edge price.]
- Maximum over all types τ ∈ [0,π/2]³ (r = min(√2ρ cos θ, A), r′ = min(√2ρ sin θ, A)): 1.19371, attained at
  all-middle. [N: 7³ grid and 30 local searches.]
- Two buckets per pair (only "r ≤ ρ, r′ trivial" or "r′ ≤ ρ, r trivial" is known): cyclic types 1.19371,
  acyclic types **1.20291**. [R up to LP arithmetic: two finite LPs; the acyclic optimum mixes the four
  options above with plain routing of pair (1,3); dual edge prices (0.2075, 0.1179, 0.1746, 0.1746, 0.1179,
  0.2075).]

### 2.3 Statement and proof sketch [D]

> **Proposition P1.** For every ε > 0 there are m, n with m/n > 6/(4+√10) − ε and T^{⊗m} ≤ S^{⊗n}, over every
> field, by the explicit construction above. With two buckets per pair the same holds with 1/1.20291 = 0.83132
> and uses only the two LPs of §2.2.

Sketch.
1. *Classes.* As in the proof of B.3: E₁ = ⌊p²n₀⌋, E₂ = ⌊q²n₀⌋; choose classes containing a fraction
   ≥ (E_i+1)^{-2} of the symbols of energy ≤ E_i. Then ln|Σ₁| = (p+o(1))κ√n₀, ln|Σ₂| = (q+o(1))κ√n₀,
   Θ ≤ 2(p²+q²)n₀, and the rank bounds give r_N² + r′_N² ≤ 2(p²+q²) + o(1) in units of κ√n₀.
2. *Buckets.* Cut {0,…,Θ} into B intervals. Ψ_β := Σ_{N∈β} Ψ_N has ranks at most the sums of the bounds, which
   changes the logarithms by O(log Θ) = o(√n₀). So per pair there are B tensors with known (r̄_β, r̄′_β), and a
   block is a sum of B³ terms; T_K is a sum of B^{3K} terms.
3. *Strategy.* For each of the B³ block types fix an optimal mixture, written as a distribution over pure
   choices (one option per pair, integral routing). In a word with g_τ blocks of type τ, give ⌊λ_π g_τ⌋ or
   ⌈λ_π g_τ⌉ blocks to the pure choice π. The load on an edge is ≤ K·n* + B³·M·L, with n* the game value for
   the bucket boxes, M the support size and L the largest load of a pure choice. Take K ≫ B³.
4. *Cover.* T_K is covered by B^{3K} restrictions of S^{⊗n′}, n′ = ⌈(K n* + B³ML)·(unit in bits)⌉. Hence
   T_K ≤ S^{⊗n′} ⊗ ⟨B^{3K}⟩_{five parties} ≤ S^{⊗(n′ + ⌈3K log₂ B⌉)}, because ⟨2⟩ on five parties is a
   restriction of S.
5. *Rate.* m = ⌊K·min(3 log₂ D₁, log₂ D₂)⌋. As n₀ → ∞ first, then K → ∞: m/n → 1/n*(B). The game value is
   monotone and Lipschitz in the (r, r′), so n*(B) → max_τ LP(τ) = (4+√10)/6 as B → ∞, and n*(2) = 1.20291.

What is not checked by a second reader: the whole sketch. What is numerical: max_τ LP(τ). What is imported:
B.2 (in [AN] it is `prop_identity`, Lean-checked by them, not rebuilt by us; §1.3 checks (a) on four small cases
and the rank bounds are consistent with the computed ranks).

### 2.4 Level 1 cannot do better [N]

`level1_dual.py`: minimise R(d) over pseudometrics on the five parties subject to the triangle inequalities
and to **all** instances of Prop. B.3 with all eight points among the five parties (45 pairs of wires, all
weights p:q, all 20 ordered hub pairs for each pairing, common (r,r′)). Result: 0.83772 (0.8371 on a 12-point
grid of p:q, 0.83765 on 24 points) in 19 of 19 SLSQP runs from random and perturbed starts, always at the
symmetric metric

    |u_kv_i| = 1,   |u₁u₂| = 1 + 1/√10,   |v_iv_j| = 1 + 3/√10,   R = 6/(4+√10).

For symmetric metrics the binding instances are (u₁u₂; v_iv_j): pD₁ + qD₂ ≤ (p+q+√(p²+q²))·s, and the support
function at (1,3) gives D₁ + 3D₂ ≤ (4+√10)s [R for the symmetric family]. So the game of §2.2 and this dual
agree: **6/(4+√10) is exactly what the crossing identity gives with hubs at real parties and no nesting.**
W5(ℓ,ℓ/3) satisfies all these level-1 inequalities (minimum slack → 0⁺ only as q/p → 0) [N], as it must if it
is a price.

For comparison, for symmetric metrics Euler's inequality D₁² + D₂² ≤ 4s² alone gives D₁ + 3D₂ ≤ 2√10·s, i.e.
3/√10 [R]. The gap between level 1 and the theorem is the gap between (p+q+√(p²+q²))·s and 2√(p²+q²)·s on a
square.

---

## 3. Finite size: where the gain starts, and why small searches see nothing

### 3.1 Accounting for the two-bucket protocol [D]

Per block: demand m_blk = min(3P, Q) bits; supply n*(P,Q,ρ) + 3 bits per edge, where ρ = log₂ R,
R = max(Σ_{N≤Θ/2}(N+1)P(N), Σ_{N′<Θ/2}(N′+1)P(N′)) is the proved bucket rank bound, n* is the larger of the two
LP values, and 3 = log₂ 8 pays for the cover by 8 terms per block. With ρ = P+Q both LPs give the routing value (4/3 per demand bit when P = Q/3),
and the +3 makes the scheme worse than routing. The scheme beats 3/4 only when
(saving P+Q−ρ) × (about 0.47) > 3 bits, i.e. D₁D₂/R ≳ 2^{6.4}.

`level1_instance.py` (exact integers for D₁, D₂, R; float LP):

| classes (n₁,e₁), (n₂,e₂) | log₂D₁, log₂D₂ | saving P+Q−ρ | rate, K → ∞ |
|---|---|---|---|
| (8,436), (21,3000) | 42.56, 127.81 | 7.74 bits | **0.7529** |
| (10,698), (27,5000) (float) | 56.2, 168.6 | 17.3 | 0.7684 |
| (13,1080), (34,8000) (float) | 72.3, 216.8 | 29.0 | 0.7795 |
| limit | | | 0.8313 |

With e₂ = 2500 the rate is 0.747. So with the proved rank bounds the first instance above 3/4 has demand
wires of dimension about 2^{128} per block (≈ 128 EPR pairs per demand wire and ≈ 170 per supply edge), and it
needs K blocks with K in the thousands for the rounding in step 3 (the margin is 0.4%). At e₂ = 8000 the
margin is 4% and K of order 10³ suffices: m ≈ 2·10⁵, n ≈ 2.8·10⁵. If the true ranks are about P(N) (as §1.3
suggests at tiny sizes) the threshold moves down to wires of about 2^{50}–2^{60} [N, extrapolation].

None of this is within reach of a dense check. What can be checked exactly is: (i) B.2 (in Lean in [AN]; mod p
here for small classes), (ii) the two LPs, (iii) the integer arithmetic. That is a proof, not a dense
verification.

### 3.2 Why single-shot searches at dimension ≤ 5 fail [D]

1. The saving of this mechanism is the ratio D₁D₂/rank(Ψ_middle). Asymptotically it is
   exp((p+q−√(p²+q²))κ√n₀), i.e. it grows like exp(c·√(log-dimension scale)) only because the number of
   symbols grows like exp(κ√E). At dimension 5 × 5 it is exactly 1 (§1.3).
2. The protocol is a cover: a sum over term types, each routed differently. Converting a cover into a
   restriction costs a shared index (GHZ) of log₂(#types) bits per block. The gain per block must exceed that.
3. The term types are adversarial, so the routing is time-shared over many blocks. A single-shot map would
   have to implement type-dependent routing coherently.

This is a property of the only mechanism we have, not a lower bound for all protocols.

### 3.3 What is proved about small sizes for arbitrary protocols [R]

- Every flattening or support-functional obstruction is an ℓ₁ price, and ℓ₁ prices have R ≥ 1 (note §6(c)).
  So no obstruction of that kind excludes any rate below 1 at any size, beyond the cut conditions.
- Single-shot uniform D_s → d: D_s = 2 allows only d = 2 (excluded, rate 1); D_s = 3 allows d = 2 (rate
  0.63 < 3/4) or d = 3 (excluded by tight v-cuts). So **D_s ≥ 4**, and 4 → 3 (rate 0.79) is not excluded by
  anything proved; ALS found residual 0.64 there.
- In the form T^{⊗m} ≤ S^{⊗n}: m = n is excluded, so rate > 3/4 needs n ≥ 5, first case (m,n) = (4,5),
  wires 32 → 16, not excluded and not searched (the dense target has 4.3·10⁹ entries).
- The border-rank argument (compose with functionals at u₁, u₂; brank⟨d,d,d⟩ ≤ g(D)²) gives nothing for D ≥ 3.

So the honest lower bound on block length is n ≥ 5 (binary) or D_s ≥ 4, and the honest upper bound from an
explicit construction is of order 10⁵.

### 3.4 A reformulation, and a toy identity [R]

Reorder the indices of the crossing wires with d₁ = d₂ = d as an operator (a,b) → (d,c): it is SWAP on
k^d ⊗ k^d. A two-term crossing decomposition C = Ψ_b + Ψ_c is the same as

    SWAP = X + Y,   operator-Schmidt rank(X) ≤ R_b,   matrix rank(Y) ≤ R_c.

- X = 1 gives Y = −2·P_antisym: (R_b, R_c) = (1, d(d−1)/2). For d = 2 this is δ_{ac}δ_{bd} − δ_{ad}δ_{bc} =
  ε_{ab}ε_{cd}: two crossing qubit wires are the sum of the two perfect matchings of the 4-cycle, each of
  rank 1 on its own cut.
- This does not help asymptotically [X]: the n-th power has 2^n terms, the cover index costs as much as it
  saves, and for large d the saving of X = 1 is one bit. Block constructions (SWAP on a subspace) save a
  constant factor ≈ 3.
- The crossing identity says that R_b = R_c = d^{√2+o(1)} is possible with poly(log d) terms. The smallest d
  at which some decomposition has d²/R ≥ 2^{6.4} is the real "smallest instance" question for this family.
  Open.

---

## 4. Beyond level 1

### 4.1 Where the remaining gap is

Level 1 treats each square (u₁,v_i,u₂,v_j) with hubs at its corners. The theorem needs, for each square, the
ℓ₂ bound (Euler / CN at the centre): three Euler equalities are exactly the active constraints at W5
(multiplier 2√10 each, e3 notebook). In [AN] that bound is produced only by Lemma C.2 and the fan, i.e. by
applying the crossing cover to wires between time-shared points at many scales.

On the protocol side this means nesting: a network produced by the first crossing cover contains wires
(between real parties, in each copy) to which the cover is applied again, with types chosen adaptively.

### 4.2 Numerical indications [N, heuristic]

`square_level2.py`: one square with sides s = 1, virtual points on a g × g grid placed by Prop. A.8 with the
monotone coupling, all level-1 crossing inequalities among all grid points, extension metric restricted to be
symmetric. Maximum of D₁ + D₂:

| grid | max (D₁+D₂)/2 | |
|---|---|---|
| 2 × 2 (level 1) | 1.7071 | = 1 + 1/√2 |
| 3 × 3 | 1.6745 | |
| 4 × 4 | 1.6614 | |
| Euler | 1.4142 | |

With weights (1,3) and the 3 × 3 grid: max(D₁+3D₂) = 7.022 (level 1: 7.162; Euler: 6.325). Used on the three
squares of a symmetric five-point metric this gives R ≥ 6/7.022 = **0.854**.

Caveats: the extension is restricted to symmetric metrics (the constraints are not convex, so this is not a
valid bound over all extensions); only per-square constraints are used; no protocol has been written for it.
Adding only the midpoint c of u₁u₂ to the five parties changes nothing (0.8371 on the same grid) [N].
Convergence in the grid size is slow, as the proof of C.2 suggests (error O(1/R) for vectors of length R²).

### 4.3 Conjecture [C]

The supremum of the rates of protocols generated by routing, time-sharing, covers and the crossing cover,
with arbitrary nesting, is 3/√10 over every field. Reason: Theorem 5 of the note uses only CN, and [AN] derives
CN from B.2, A.8 and closure under pull-backs, multiples and limits. What is missing for a proof is a
finite-depth version of C.2/C.1 with explicit error terms and the corresponding game.

A protocol above 3/√10 cannot come from this family if W5 is a price (it satisfies every inequality the
family can use).

---

## 5. Answers to the questions of the brief

1. *Which restriction does the crossing identity encode?* §1.1: a cover of two crossing wires by Θ+1 tensors,
   each a restriction of two two-hub networks, with hub-wire exponents on a circle of radius √(2(p²+q²)).
   Not "a wire through a midpoint": the hub/midpoint statement (CN) appears only after the limit in C.2/C.1.
2. *Virtual hub at the midpoint of u₁u₂.* A virtual party is time-sharing between u₁ and u₂; by itself it
   gives |cv_i| ≤ ½(|u₁v_i|+|u₂v_i|), no gain. The gain is Pythagorean sharing of a leg: in "c via u₁" the edge
   u₁v_j carries both the v_iv_j wire and the u₁u₂ wire at cost √(P²+Q²) instead of P+Q. Level 1 does this on
   one edge per square; CN would do it at the centre of the square.
3. *Matrix multiplication / laser method on the v-side.* [X] as a source of gain: for the triangle alone,
   rate 1 is already routing, and with u₁, u₂ projected out the u₁u₂ demand is lost. All of the gain is in the
   coupling of u₁u₂ with the triangle, which is the crossing structure. Not explored further.
4. *Dualising the proof.* §1.2. The calibration at W5 says each supply bit u_kv_i is worth 3/√10 bits towards
   the hub from v_i and 1/√10 bits from u_k; a protocol realising this needs the ℓ₂ bound on each square.
5. *Smallest instance, verification.* §3.1 and §6.

---

## 6. Verification plan and requests

Exact checks that exist:
- `python3 crossing_identity_modp.py n1 e1 n2 e2`: builds M, computes all Ψ_N mod p, checks (a), prints the
  three flattening ranks of every Ψ_N. (5,5) takes seconds, (4,8) about two minutes.
- `python3 level1_game.py 7`: the game over a 7³ grid of types; `level1_lp.py` holds the bucket LP.
- `python3 level1_dual.py seed nstarts ngrid`: the five-point dual.
- `python3 level1_instance.py 8 436 21 3000`: exact dimensions and rank bounds, rate 0.7529.

Requests to main (none is blocking):
1. Optional dense check with tensorlab, a test of the mechanism and not of the rate: parties
   (a,b,c,d) = (u₁,v₁,u₂,v₂), classes (2,12,2,12) (dimensions 5,5). The tensor Ψ₈ from
   `crossing_identity_modp.py` has rank 16 across ad|bc. Check that Ψ₈ is the image of
   Net_b = ⟨5⟩_{d w}⟨5⟩_{c w′}⟨16⟩_{w w′} with w = a, w′ = b under the hub maps of Lemma A.3 built from a
   rank-16 factorisation of the ad|bc flattening. This is Lemma A.3 itself, so the residual must be 0.
2. Rational LP: solve the two bucket LPs of `level1_lp.py` in exact arithmetic over Q(√10) and record the
   optimal mixtures (the acyclic value 1.2029076 has no closed form here yet).
3. A referee for §2.3, in particular step 3 (adaptive rounding) and step 4 (cover → restriction).
4. If a larger computation is affordable: `crossing_identity_modp.py` vectorised, for classes of dimension
   20–60, to see how fast rank(Ψ_N)/P(N) settles. This fixes the true threshold of §3.1.

---

## 7. Dead ends

- [X] Level-1 scheme without adaptivity (one fixed network that dominates every term edge by edge): needs
  P/3 + √(P²/9+Q²) per edge, worse than routing (P/3 + Q) for all P, Q. The gain exists only after mixing
  options per term type.
- [X] Gain on a single 4-cycle: routing already meets the cut bound there (p+q ≤ 2·capacity). The gain on
  K_{2,3} comes from each edge lying in two squares.
- [X] Midpoint c of u₁u₂ as the only virtual point: no change of the level-1 dual value.
- [X] The ε-identity (d = 2) and its powers: exponentially many terms, no asymptotic gain.
- [X] Small dense instance of rate > 3/4 from the crossing identity: impossible, all middle ranks are full
  up to dimension 5 × 5 and the proved bounds need 2^{128}.
- Not attempted: a three-wire analogue of the determinant (u₁u₂ against the whole triangle at once); a
  finite-depth version of Lemma C.2 with explicit constants.
