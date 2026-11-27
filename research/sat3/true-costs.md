# sat3 / true costs of the crossing pieces Ψ_N

Working notes, 27 Nov 2026. Machine-generated, not refereed. Nothing here is committed.

Tags: **[K]** quoted, with location; **[R]** proved here in full from the cited inputs; **[D]** derived here, proof
sketched, unreviewed; **[N]** numerical (exact rank computations modulo the prime 2147483629, script named);
**[C]** conjecture; **[X]** dead, with the reason.

Inputs. [AN] = Anthropic, "VP ≠ VNP over every field", App. B (`scratchpad/fm/paper.txt` l. 1251–1434): Prop. B.2
(crossing identity), its proof B.3, Prop. B.3. `sat3/attain-notes.md` §1.2, §2, §5 (Theorem W), `sat3/review-thmW.md`
(true ranks below certificates), `sat3/hunch-char2.md` §2.2 (arc lemma), `sat3/q1-notes.md` Theorem B.

Scripts: `research/sat3/truecost/` (list in §7); raw tables in `research/sat3/truecost/out/`.

Notation. Classes Σ₁ = Σ(n₁,e₁) at a, c and Σ₂ = Σ(n₂,e₂) at b, d; dᵢ = |Σᵢ|; D = d₁d₂; Θ = 2(e₁+e₂);
Ψ_N = coefficient of X^N in det M (only even N occur; y = X², N = 2k). Σ(n,e) is in bijection with the partitions of
e/2 with Durfee square n, so dᵢ = [q^{eᵢ/2 − nᵢ²}] 1/(q;q)²_{nᵢ}. fᵢ = eᵢ/2 − nᵢ² (the number of free quanta of the
class). p(m) = partition numbers; p_{[s,t]}(m) = number of partitions of m with Durfee square in [s,t].
Certificates of Prop. B.2: cert_b(N) = (N+1)P(N) across ad|bc, cert_c(N) = cert_b(Θ−N) across ab|cd,
P(N) = Σ_{m≤N/2} p(m).

---

## 0. Answers

| Question | Answer | Status |
|---|---|---|
| What is Ψ? | The free-fermion (Wick/Szegő) four-point function of the Riemann sphere with the parties at a = 0, d = 1, b = 1/y, c = ∞, in Möbius local coordinates; classes are L₀-weight spaces of Λⁿ D_{1/2} ⊗ Λⁿ D_{1/2}. The expansion of B.3 is the sewing expansion in the channel ad\|bc, T the intermediate Fock state | [R] §2 |
| True rank across ad\|bc (and, by reflection, ab\|cd) | ≤ C_ref(k) = Σ_{m≤k} (k−m+1)·p_{[\|n₁−n₂\|, n₁+n₂]}(m) for N = 2k, always [R]; **equality** exactly for k ≤ min(f₁,f₂) + (n₁−n₂)² in all 16 class pairs computed with (n₁,n₂) ≠ (1,1) [N]; three of them were predictions. Generating function (1−q)⁻² Σ_t q^{t²}/(q;q)_t². For n₁ = n₂ ≥ 2 and small k: 1, 3, 7, 14, 26, 45, 75, 120, … against the certificate 1, 6, 20, 49, 108, 209, 390, 675 | [R] bound, [N]/[C] equality, §3 |
| Beyond the stable range | rank = dimension of the jet space of the three-point vertex (equality in every computed case but one, which has n₁ ≠ n₂ and is 4 below) [N]; the vertex has rank = number of T that are reachable, up to explicit Ward-identity corrections [N] | §3.3, §3.4 |
| log(true)/log(certified) | → 1. In the stable range true = C_ref [N], and ln C_ref/ln cert → 1 is elementary (0.76 at k = 10, 0.95 at k = 10³, 0.99 at k = 10⁵: the certificate is off by a polynomial factor only). In the regime that matters (energies → ∞, popular classes, N ≍ Θ) it is [R] under the flat hypothesis (arc lemma) and [C] unconditionally; all structural evidence points to → 1. **No computation of feasible size can see this regime**: at every computable size the middle terms have full rank | §3.5 |
| Is the true two-cut law inside the circle? | No evidence for it, and a mechanism against it. No contradiction with the arc lemma; nothing new about flat/contracting | §3.5 |
| Single-party cuts | full (rank d₁, d₁, d₂, d₂) for all N except the first/last few when the classes differ | [N] §4 |
| Third cut ac\|bd | **full**: min(d₁², d₂²) for all N away from the two ends when n₁ = n₂, except exactly N = Θ/2, where it is min(dᵢ(dᵢ+1)/2) (reflection symmetry). No certificate exists and none is possible from energy truncation. For n₁ ≠ n₂ it is limited by the size window of the third channel | [N], mechanism [D], §4 |
| True four-party (third-merge) cost | between the cut-LP bound and the certified cost. At every computed size and every N in the middle range the two coincide: **exactly 3/2 per bit** at d₁ = d₂ (LB = UB). In the asymptotic regime at the balanced term (p = q, r = r′ = √2·p, third rank full): **between (1+√2)/2 = 1.2071 and 3/2 per bit**; not decided. In every case ≥ 1 (raw), because the single-party ranks are full | [R] given the ranks, §4 |
| Level-1 game with true costs | **Lemma G [R given (A)]:** if the middle term of every factor has full single-party ranks and two-cut ranks at their certified value, the level-1 value of every 3-net of order g is ≥ g/(√2(g+1)), whatever the third cut and whatever the multi-group networks cost. So it cannot go below 1/√2 on large nets, cyclic or F₂^m. LP with flattening lower bounds in place of certified costs, third-cut rank as measured (O1): the minimum over merge weights stays at the two-merge corner and equals the certified value on K₄, Z₃, Z₂² (scans of the weight simplex) and Z₄, Z₅ (five weight vectors): 0.5690, 0.6036, 0.6243, 0.6243, 0.6381. With the third-cut rank set to 0 (O2, refuted by the tables) the bound would drop to 0.4714 on K₄ (the price floor) and a few % below the two-merge value for g = 3, 4, 5 | [R]+[N], §5 |

Nothing was found that triggers the alarm of the brief: the two-cut law does not beat the circle, and the level-1
value with true costs does not drop below the two-merge value on any family.

---

## 1. What was computed

- `psi_build.py`: Ψ(X; s_a,s_b,s_c,s_d) = det M is evaluated modulo P₀ = 2147483629 at e₁+e₂+2 values of y and
  interpolated (numba); all seven flattening ranks of every Ψ_N with FLINT. Checks: identity (a) holds in all 16
  class pairs; the extra interpolation point confirms deg ≤ Θ; the ranks for (2,12)×(2,12) and (1,8)×(2,12) agree
  with the referee's independent integer computation `refW/psi_ranks.py`; rank_{ab|cd}(Ψ_N) = rank_{ad|bc}(Ψ_{Θ−N})
  in every table. Ranks modulo one 31-bit prime are lower bounds for the ranks over ℚ and equal them unless the
  prime is unlucky; no value was contradicted by the second, independent method below.
- `factored.py`: the same rank across ad|bc from the two-hub expansion of B.3 without building the 4-tensor
  (§3.1); agrees with `psi_build.py` wherever both were run (six class pairs, all N computed).
- `vertex_rank.py`, `vertex0.py`: ranks of the three-point vertex.
- Class pairs with all seven ranks, all N (16): (1,40)², (1,60)², (1,20)×(1,40), (2,16)², (2,16)×(2,20),
  (2,18)×(2,22), (2,20)², (2,22)², (3,24)², (3,26)², (3,28)², (1,16)×(2,20), (1,30)×(2,16), (2,16)×(3,24),
  (1,24)×(3,26), (2,20)×(3,28); dimensions up to 40×40 (tensors with up to 2.56·10⁶ entries per N, Θ up to 240).
  Summary: `summarize.py`. Rank across ad|bc only, small N (`factored.py`): also (2,28)² (d = 91), (3,30)² (d = 49),
  (2,24)×(3,30) (55×49).

Honest limit of all this: the certificate (N+1)P(N) is below D at N = Θ/2 only when e ≳ 200, where d ≈ 10⁸. Every
table below is in the regime where the middle terms have full rank on both controlled cuts. The asymptotic
statements rest on the structure (§2, §3.4), not on extrapolating tables.

---

## 2. Structure: Ψ is a free-fermion four-point function [R]

**Proposition 2.1 [R].** Let M̃ be the infinite matrix with rows (P,i) and columns (Q,j), P, Q ∈ {a,d,c,b},
i, j ∈ ℕ, whose entries are those of M in [AN] B.3 with the rows (d,i), (b,i) multiplied by (−1)^i and the columns
(d,j), (b,j) by (−1)^j. Put x = X, y = x², ω(u,v) = u₁v₂ − u₂v₁ and

    G_a = 1,   G_d = [[1,−1],[y,−1]],   G_c = [[0,−1/x],[−x,0]],   G_b = [[y,−1],[y,−y]] / ((y−1)x).

Then M̃ is antisymmetric and, for P ≠ Q,

    Σ_{i,j} M̃[(P,i),(Q,j)] s^i t^j = ε_{PQ} / ω(G_P (s,1)ᵗ, G_Q (t,1)ᵗ),

with ε = +1 if a ∈ {P,Q} and −1 otherwise (P before Q in the order a, d, c, b; the other half by antisymmetry),
and M̃[(P,·),(P,·)] = 0. Multiplying the rows and columns of a by −1 makes ε ≡ −1.

*Proof.* Σ_{r,n} C(r,n) s^r t^n = Σ_r s^r (1+yt)^r/(1+t)^{r+1} = 1/(1 + t − s − yst) and likewise
Σ B(r,n) s^r t^n = 1/(1 + yt − s − st). Substituting the signs and the factors X^{2i+1} = x y^i gives the six kernels
1/(1−s−t+yst) (ad), x/(1−yst) (ac), (y−1)x/(1−ys−yt+yst) (ab), x/(1−ys−yt+yst) (dc), −x/(1−yst) (db),
−(y−1)/(1−s−t+yst) (cb); each equals ε/ω(G_P(s,1), G_Q(t,1)) by a 2×2 computation. Checked symbolically to order 6
in both variables for all twelve blocks: `szego_check.py` [N]. ∎

So, up to diagonal signs at the parties and factors that are constant on the classes, **Ψ is the Wick determinant
of the Szegő kernel 1/(z−w)**: in the coordinate z of a the parties sit at a = 0, d = 1, b = 1/y, c = ∞, with the
Möbius local coordinates s_a = z, s_d = (z−1)/(yz−1), s_b = (yz−1)/(y(z−1)), s_c = 1/(yz). Each party sees itself
at 0, its ad/bc-partner at 1, its ab/cd-partner at 1/y and its wire partner at ∞. A symbol (I,J) is the Fock state
with particles at I and holes at J; modes carry the lowest-weight representation D_{1/2} of sl₂ (L₀ = i + ½,
L₋₁|i⟩ = (i+1)|i+1⟩, L₁|i⟩ = i|i−1⟩), the energy of a symbol is 2L₀, and L_{±1} preserve the size n. Hence

    Σ(n,e) = the L₀-weight space e/2 of Λⁿ D_{1/2} ⊗ Λⁿ D_{1/2},

and it splits into quasi-primaries (L₁φ = 0) of weights h ≤ e/2 and their L₋₁-descendants;
#QP of weight h = d(n,2h) − d(n,2h−2).

Consequences.

- **[R] Symmetries.** The Klein four-group acts (z ↦ 1/(yz) exchanges a ↔ c, b ↔ d together with their local
  coordinates): Ψ_N(s_a,s_b,s_c,s_d) = Ψ_N(s_c,s_d,s_a,s_b), checked entrywise on three class pairs [N]. The reflection of
  [AN] (X ↦ 1/X, b ↔ d) is the exchange of the channels. At N = Θ/2 the tensor is symmetric under b ↔ d and under
  a ↔ c; this is why the third-cut rank halves exactly there (§4).
- **[R] Three channels.** y → 0: b, c collide (channel ad|bc); y → ∞: a, b collide (channel ab|cd); y → 1: the discs
  of b and d shrink onto each other and Ψ becomes the two wires. The crossing identity is crossing symmetry of a
  free-fermion correlator, cut into X-degrees.
- **[R] The expansion of B.3 is sewing.** Over ℤ[[X]]: Ψ = Σ_T ±X^{E(T)} P_T(s_a,s_d;y) Q_T(s_b,s_c;y), T a symbol
  (the intermediate Fock state), P_T, Q_T ∈ ℤ[y] the two three-point functions (determinants printed in [AN] B.3).
  P_T ≡ 0 unless |n₁−n₂| ≤ |T| ≤ n₁+n₂ (count the rows and columns that meet the zero blocks).
- **[R] The vertex at y = 0.** V(s_a,s_d,T) := P_T(0) is the determinant with rows I_a, I_d, T₂, columns J_a, J_d, T₁
  and blocks [[0, ±C(i+j,j), [i=r]], [∓C(i+j,i), 0, C(r,i)], [[r=j], C(r,j), 0]] (C = binomial coefficient). So a
  particle of T is a particle of a at the same mode or a particle of d at a mode ≤ its own; the other particles of a
  annihilate holes of d through the Pascal matrix C(i+j,i), all of whose minors are positive.
  For |T| = n₁+n₂ nothing annihilates: V = ±[I_a ⊆ T₁][J_a ⊆ T₂]·det C(r,i)_{I_d×(T₁∖I_a)}·det C(r,j)_{(T₂∖J_a)×J_d}, which
  vanishes unless E(T) ≥ e₁+e₂, and for E(T) = e₁+e₂ equals ±[T = s_a ⊔ s_d].
- **[D] Ward identities.** With d inserted at 1 in the coordinate 1−z, L₋₁ at d acts on the vertex by the scalar
  e₁/2 + E(s_d)/2 − E(T)/2. Hence V(s_a, L₋₁^j φ, T) = (e₁/2 + h_φ − E(T)/2)_j · V(s_a, φ, T) (rising factorial), which
  vanishes for all descendants (j ≥ 1) when E(T)/2 = m* − 1, m* = (e₁+e₂)/2. Prediction: the vertex block at level
  m* − 1 has rank ≤ d₁·#QP_top(Σ₂). **Verified exactly** [N, `vertex0.py`]: (2,20)²: 300 = 30·10 (of 490 columns);
  (2,28)²: 1911 = 91·21 (of 3005 columns).
- **[D] y-dependence.** P_T(s_a,s_d;y) = (1−y)^{e₂/2} Σ_k (y/(1−y))^k V(s_a, L₁^k s_d/k!, T) up to class constants
  (the local coordinate of d is the standard one composed with a dilation and a special conformal map), and Q_T has
  the same form at b. This is where the degree splitting of [AN] (the factor N+1 in the certificate) comes from; it
  costs a polynomial factor, not an exponent. Used below only through the jet spaces, which are computed, not
  through this formula.

---

## 3. The two controlled cuts

### 3.1 The refined certificate [R]

From Ψ ≡ Σ_T ±X^{E(T)} P_T Q_T with P_T, Q_T ∈ ℤ[y] and the size window, for N = 2k:

    Ψ_N = Σ_{T : |n₁−n₂| ≤ |T| ≤ n₁+n₂, E(T) ≤ N}  Σ_{i+j = k − E(T)/2}  ± [y^i]P_T ⊗ [y^j]Q_T,

    rank_{ad|bc}(Ψ_{2k}) ≤ rank PP_k ≤ C_ref(k) := Σ_{m≤k} (k−m+1) · p_{[|n₁−n₂|, n₁+n₂]}(m)  ≤  (2k+1)P(2k) = cert_b.     (3.1)

PP_k is the matrix whose columns are the coefficient vectors [y^i]P_T, E(T)/2 + i ≤ k (the k-jets of the vertex).
Σ_k C_ref(k) q^k = (1−q)⁻² Σ_{t=|n₁−n₂|}^{n₁+n₂} q^{t²}/(q;q)_t². This is the count of [AN]'s own proof done exactly
((N−E(T))/2 + 1 splits instead of N+1, and the size window).

### 3.2 Tables [N] (`psi_build.py`, `factored.py`; all seven ranks in `out/r_*.txt`)

rank_{ad|bc}(Ψ_{2k}), k = 0, 1, 2, …, until it reaches D (then it stays at D up to dips of 1–4 units, see below);
rank_{ab|cd}(Ψ_N) = rank_{ad|bc}(Ψ_{Θ−N}).

| classes | d₁×d₂ | rank_{ad\|bc}(Ψ_{2k}), k = 0, 1, … | = C_ref up to k |
|---|---|---|---|
| (2,16)² | 14×14 | 1 3 7 14 26 42 65 99 147 181 191 195 196 | 4 |
| (2,16)×(2,20) | 14×30 | 1 3 7 14 26 44 72 110 165 242 340 407 420 | 4 |
| (2,18)×(2,22) | 20×40 | 1 3 7 14 26 45 74 117 177 262 381 544 739 800 | 5 |
| (2,20)² | 30×30 | 1 3 7 14 26 45 75 117 177 263 385 551 760 887 896 900 | 6 |
| (2,22)² | 40×40 | 1 3 7 14 26 45 75 120 184 274 402 580 823 1149 1528 1600 | 7 |
| (2,28)² | 91×91 | 1 3 7 14 26 45 75 120 187 284 423 615 880 (k ≤ 12, `factored.py`) | 10 |
| (3,24)² | 10×10 | 1 3 7 14 23 35 54 75 91 96 99 100 | 3 |
| (3,26)² | 18×18 | 1 3 7 14 26 42 65 99 149 208 266 304 319 324 | 4 |
| (3,28)² | 30×30 | 1 3 7 14 26 45 72 110 166 246 358 497 644 788 877 894 900 | 5 |
| (3,30)² | 49×49 | 1 3 7 14 26 45 75 117 177 263 385 553 (k ≤ 11, `factored.py`) | 6 |
| (1,16)×(2,20) | 8×30 | 0 1 4 10 21 39 68 112 174 239 240 | 7 |
| (1,30)×(2,16) | 15×14 | 0 1 4 10 21 39 64 87 117 164 202 209 210 | 5 |
| (2,16)×(3,24) | 14×10 | 0 1 4 10 21 38 63 87 111 133 140 | 4 |
| (1,24)×(3,26) | 12×18 | 0 0 0 0 1 4 12 28 58 102 121 129 147 183 216 | 8 |
| (2,20)×(3,28) | 30×30 | 0 1 4 10 21 39 68 111 173 246 339 462 633 820 900 | 6 |
| (2,24)×(3,30) | 55×49 | 0 1 4 10 21 39 68 112 177 270 385 533 (k ≤ 11, `factored.py`) | 7 |
| (1,40)² | 20×20 | 1 3 7 13 22 33 46 61 78 97 118 141 166 193 222 253 286 321 358 389 400 | 2 (see below) |
| (1,60)² | 30×30 | (k+1)² − 3 for 3 ≤ k ≤ 28, then 884, 900 | 2 |
| (1,20)×(1,40) | 10×20 | 1 3 7 13 22 33 46 61 78 97 117 138 158 177 195 200 | 2 |

C_ref for the three size windows that occur: [0, ≥4]: 1 3 7 14 26 45 75 120 187 284 423 618 890 1263;
[1, ≥3]: 0 1 4 10 21 39 68 112 178; [2,4]: 0 0 0 0 1 4 12 28 58 109. Certificate (N+1)P(N): 1 6 20 49 108 209 390 675 1139.

Reading.

- **Stable formula [N → C].** In all sixteen pairs other than n₁ = n₂ = 1,

      rank_{ad|bc}(Ψ_{2k}) = C_ref(k)   for k ≤ min(f₁,f₂) + (n₁−n₂)²,

  and the first k beyond this bound is always the first deviation (last column; e.g. (2,22)²: f = 7, 120 = C_ref(7)).
  The rule was read off the classes of dimension ≤ 40 and then predicted three new cases correctly: (2,28)²
  (d = 91, f = 10): 423 = C_ref(10), then 618 − 3 and 890 − 10; (3,30)² (f = 6): 75, then 120 − 3, 187 − 10, 284 − 21,
  423 − 38; (2,24)×(3,30) (min f + 1 = 7): 112 = C_ref(7), then 178 − 1.
  **In the stable range the expansion of B.3 has no linear relation at all: the true rank is the exact number of its
  terms.** Second differences give the partition numbers themselves (2, 3, 5, 7, 11, 15 for n₁ = n₂; p(k) − [k=0] for
  |n₁−n₂| = 1; the partitions with Durfee square ≥ 2 for |n₁−n₂| = 2).
- **n₁ = n₂ = 1** is degenerate: rank = (k+1)² − 3 exactly for 3 ≤ k ≤ f − 1 ((1,40)²: f = 19; (1,60)²: f = 29, up to
  838 = 29² − 3), against C_ref of order k⁴.
  Reason [D]: Λ¹D_{1/2} ⊗ Λ¹D_{1/2} has exactly one quasi-primary per weight, so the tensor is a matrix of sl₂ conformal
  blocks, with polynomially many degrees of freedom. Size-1 classes have dimension e/2 and are useless for the
  engine: in units of ln d both ranks are 2 − o(1) for every N in the bulk (the same L-shaped law as found mod 2 in
  `hunch-char2.md` §2.3).
- **Deficits past the stable range** are nearly the same for all classes with n₁ = n₂ ≥ 2: C_ref − rank = 3, 10, 21 at
  k = f+1, f+2, f+3 in (2,16)², (2,20)², (2,22)², (3,26)², (3,28)²; then 38, 67, 114 for (2,22)² (38, 67 for (2,20)²,
  38, 65 for (3,28)², 40 for (2,16)², which is close to saturation there). They are finite-class effects of
  polynomial size (the jets of a low T run out of weight blocks of the classes); not explained in closed form.
- **Monotonicity.** rank_{ad|bc}(Ψ_N) is nondecreasing in N for N ≤ Θ/2 whenever n₁ = n₂. For n₁ ≠ n₂ there are dips
  of 1–4 units after saturation ((1,30)×(2,16): 210 at N = 24, 209, 208, 207 at N = 28, 30, 32, 210 again at 46).

### 3.3 rank = jet rank [N]

`factored.py` computes rank(Ψ_{2k}) = rank(PP_k J QQ_kᵗ) and rank PP_k separately:

- rank_{ad|bc}(Ψ_{2k}) = rank PP_k = rank QQ_k for all k computed in (1,40)² (k ≤ 21), (2,20)² (k ≤ 15),
  (3,26)² (k ≤ 13), (2,16)×(2,20) (k ≤ 13), (2,16)×(3,24) (k ≤ 10), (2,28)² (k ≤ 12), (3,30)² (k ≤ 11),
  (2,24)×(3,30) (k ≤ 11); see `out/f_*.txt`;
- one exception: (1,30)×(2,16), k = 10: rank Ψ = 202 < 206 = rank PP (the same place as the dips above).

So for n₁ = n₂ the rank of the piece is, in every case computed, the dimension of the span of the functions
(s_a,s_d) ↦ V(s_a, L₁^i s_d, T) with E(T)/2 + i ≤ k [N]. Not proved: PP J QQᵗ pairs the jets by an indefinite form.

### 3.4 The vertex: which T count [N + R]

`vertex0.py`, `vertex_rank.py`: rank of the block (Σ₁×Σ₂) × {T of energy 2m} of V = P_T(0).

| classes | m | p(m) | T with \|T\| ≤ n₁+n₂ | rank | reading |
|---|---|---|---|---|---|
| (2,20)², D = 900, m* = 20 | ≤ 15 | | | = p(m) | full column rank |
| | 16, 17, 18 | 231, 297, 385 | all | 230, 294, 378 | minus the 1, 2, 5 symbols of size 4 (unreachable below m*), minus 0, 1, 2 |
| | 19 = m*−1 | 490 | all | 300 | Ward identity: d₁·#QP = 30·10 |
| | 20 = m* | 627 | all | 623 | all 20 symbols of size 4 split as s_a ⊔ s_d; minus 4 |
| (2,28)², D = 8281, m* = 28 | 24, 25, 26 | 1575, 1958, 2436 | 1575, 1957, 2434 | 1426, 1732, 2098 | minus the 149, 224, 334 symbols of size 4, minus 0, 1, 2 |
| | 27 = m*−1 | 3010 | 3005 | 1911 | = 91·21 |
| | 28 = m* | 3718 | 3708 | 3642 | 3023 of size ≤ 3 + 623 of size 4 that split (of 685) − 4 |
| | 29, 30 | 4565, 5604 | 4545, 5568 | 4485, 5494 | |

Cumulative (all levels ≤ m): (2,20)²: rank = number of T for m ≤ 12 (272), 371/373, 504/508, 678/684 for m = 13, 14, 15.
(1,40)²: rank = 1 + m(m+1)/2 = number of T of size ≤ 1 (a symbol of size 2 must contain s_a, so it needs E ≥ e₁).

So the vertex is as non-degenerate as it can be: **its rank at level m is the number of reachable T** (those for
which the determinant is not identically zero for combinatorial reasons: size window, and for size n₁+n₂ the
splitting condition of §2), up to the Ward-identity cap at m* − 1 and corrections of 0, 1, 2, 4 units. [N] at these
sizes; (2,28)² is the first case with p(m*) < D (3718 against 8281).

### 3.5 Asymptotics, and the arc

Regime: e₁ = p²n₀, e₂ = q²n₀, popular classes (nᵢ = c*·√(eᵢ/2), c* = √6 ln 2/π = 0.5404, ln dᵢ = κ₀√(eᵢ/2)(1−o(1)),
κ₀ = π√(2/3)); r′(N) := ln rank_{ad|bc}(Ψ_N) and r(N) := ln rank_{ab|cd}(Ψ_N) in units of κ₀√(n₀/2).

1. **Upper bound [R].** r′ ≤ ln C_ref ≤ ln cert_b = √(N/n₀) + o(1). The refinement (3.1) is polynomial: ln C_ref / ln cert_b → 1
   (`asymptotics.py`, exact integers: 0.758 at k = 10, 0.880 at 100, 0.947 at 10³, 0.979 at 10⁴, 0.992 at 10⁵).
2. **Stable range [N → C].** There the true rank *is* C_ref, so true/certified → 1 in the exponent with exactly this
   slow convergence. The stable range is k ≤ f ≈ (1 − c*²)e/2, i.e. N ≤ 0.71·e ≈ 0.18·Θ for e₁ = e₂: it covers the
   part of the circle with r′ ≤ 0.42·(p+q), not the balanced point.
3. **The balanced point and the arc: [R] under flat, [C] without.** By the arc lemma (`hunch-char2.md` §2.2), if the
   flat hypothesis holds over k then for every point of the arc some term has both ranks ≥ that point − ε. The
   certified pairs (r_N, r′_N) lie on the same circle, and true ≤ certified; so the term can only be an N whose
   certified point is within O(√ε) of the given one, and **under flat, near every point of the arc there are N for
   which the true ranks of Ψ_N equal the certified ones in the exponent**, on both cuts at once.
4. **Mechanism for [C] without flat [D + N].** By §3.3–3.4 the rank is governed by the number of reachable T of energy
   ≤ N. A T is unreachable only if its size is outside the window or its size is so close to n₁+n₂ that too little
   can annihilate. A typical T of energy N has size c*√(N/2), which is ≤ n₁+n₂ = c*(√(e₁/2)+√(e₂/2)) exactly when
   N ≤ (√e₁+√e₂)² = (p+q)²n₀ — the range in which the certificate is below the full rank D; beyond it the window
   cuts the count down to D, as it must. For N ≤ Θ/2 the
   splitting T = A ⊔ R (A ⊆ s_a, R dominating a part of s_d, the rest annihilated) exists for typical T by counting
   energies. No conserved quantity other than the size is visible in the vertex (all minors of the Pascal kernels are
   nonzero), and the two Ward-identity effects found (the cap at m* − 1 on exact levels, deficits of ≤ 4 units)
   are invisible in the cumulative ranks that enter Ψ_N.
5. **What is proved without flat.** Only statements about the expansion, not about Ψ_N itself. [R]: at the middle
   level the vertex block has rank ≥ #{T of size n₁+n₂, energy e₁+e₂, that split as s_a ⊔ s_d} (these columns have
   disjoint supports, §2; (2,28)²: 623 of the 685 such T split). [D]: for popular classes and p = q this number has
   exponent s(√2c*)/κ₀ = 0.869 of the certified one, if most such T split (`entropy.py`; s(c) = entropy of the
   partitions with Durfee square c√m). So the jet space of the middle term has exponent at least 0.869 times the
   certified one; the remaining 13 % is the contribution of T with fewer than n₁+n₂ particles, which the tables
   show to be present (§3.4) but for which no triangular family was found. An unconditional lower bound for
   rank(Ψ_{Θ/2}) itself would be a lower bound for two-term covers W = A + B of the wire pair with rank_{ad|bc}(A),
   rank_{ab|cd}(B) small — a special case of flat that nobody has; the trivial bound is useless
   (D ≤ rank A + rank B·min(d₁,d₂)²).
6. **Other classes do not help [D].** For classes of size n = c√(e/2) (p = q) the number of T at the middle level
   inside the size window has exponent ρ(c) = s(min(√2c, c*))/(√2 s(c)) relative to D:
   ρ = 0.905, 0.882, 0.842, 0.797, 0.753, 0.721, 0.7071, 0.713, 0.729, 0.756 for
   c = 0.05, 0.1, 0.2, 0.3, 0.38, 0.45, c*, 0.6, 0.65, 0.7. The minimum 1/√2 is at the popular class. So if the count of
   reachable T is the truth, the family of Prop. B.2 cannot go inside the circle by choosing atypical classes
   either; in their own units atypical classes are strictly worse.

**Verdict on step 2 of the brief.** The premise fails: nothing indicates a true two-cut law strictly inside the
circle. In the stable range the certificate is tight up to a polynomial factor by exact computation; at the
balanced point tightness is equivalent, for this family, to the two-term-cover case of the arc lemma and holds
under flat. The gap seen by the referee at small sizes (7 against 20, etc.) is the polynomial factor
C_ref/cert, not an exponent. **No claim about flat or contracting follows.**

---

## 4. All seven flattening ranks, the third cut, and the four-party cost

### 4.1 Tables [N] (`summarize.py` on `out/r_*.txt`)

| classes | single cuts a, b, c, d | third cut ac\|bd, generic N | at N = Θ/2 |
|---|---|---|---|
| (1,40)², (1,60)², (2,16)², (2,20)², (2,22)², (3,24)², (3,26)², (3,28)² | full for every N | d² (400, 900, 196, 900, 1600, 100, 324, 900) for every N ≠ Θ/2 | d(d+1)/2 (210, 465, 105, 465, 820, 55, 171, 465) |
| (2,16)×(2,20), (2,18)×(2,22) | full for 4 ≤ N ≤ Θ−4 | d₁² (196, 400) = min(d₁²,d₂²) | 105, 210 = d₁(d₁+1)/2 |
| (1,20)×(1,40) | full for 10 ≤ N ≤ Θ−10 | 100 = d₁² | 55 |
| (1,16)×(2,20) | full for 8 ≤ N ≤ Θ−8 | 64 = d₁² | 36 |
| (2,16)×(3,24) | full for 4 ≤ N ≤ Θ−4 | 100 = d₂² | 55 |
| (1,24)×(3,26) | full for 18 ≤ N ≤ Θ−18 | 144 = d₁² | 78 |
| (1,30)×(2,16) | full for 12 ≤ N ≤ Θ−12 | 112 < 196 = min(d₁²,d₂²) | 59 |
| (2,20)×(3,28) | full for 4 ≤ N ≤ Θ−4 | 898 of 900 | 464 |

- **Third cut [N], mechanism [D].** In the channel ac|bd the wire pair is the vacuum term and every Ψ_N contains all
  intermediate states: (1−y)^m has all coefficients, so extracting a power of y truncates nothing. The rank is the
  number of states T′ through which the pair (a,c) and the pair (b,d) can communicate: all of min(d₁²,d₂²) when
  n₁ = n₂, fewer when the sizes differ (T′ has size ≤ 2 min(n₁,n₂); (1,30)×(2,16): 112 of 196). **No certificate
  below the trivial 2 min(p,q) exists for the third cut, and the true rank is the trivial one** for classes of equal
  size; [C] for popular classes in the limit (their sizes are proportional to √energy, so the size window does not
  bind on the smaller side).
- The value at N = Θ/2 is forced by the symmetries of §2 (the flattening is symmetric under the swap in both index
  pairs). It is one term and a factor 2.
- **Single cuts** are full wherever both controlled ranks are large; they drop only in the first/last few terms of
  unequal classes, where the rank across one controlled cut is below max(d₁,d₂)/min(d₁,d₂).

### 4.2 The four-party network cost [R, given the ranks]

A piece with its four legs in four groups is paid by the cheapest K₄ network (bonds x_{ab}, …, x_{cd} ≥ 0, cost Σx).

*Lower bound (cut LP).* Every cut S needs Σ_{e crossing S} x_e ≥ ρ(S) = log-rank across S. Dual vertices
(`game_true.py::dual_vertices`) give

    c₄ ≥ max( p+q,  (r + r′ + r₃)/2,  max(p,q) + r₃/2,  (p + q + max(r,r′))/2,  r, r′, r₃ )

for ρ(a)=ρ(c)=p, ρ(b)=ρ(d)=q, ρ(ab)=r, ρ(ad)=r′, ρ(ac)=r₃ (these are all the vertices); the first comes from the four
single cuts, the second from the three pair cuts.

*Upper bound.* The realisations of Lemma A.3 with the true ranks: gather (p+q+min(p,q)); two hubs across ab|cd or
ad|bc (2 min(p,q) + r or r′); two hubs across ac|bd (p+q+r₃).

*At the computed sizes* (`four_party.py`, exact ranks, cost divided by raw = log d₁ + log d₂): for n₁ = n₂ and every N
in the range where both controlled ranks are full, LB = UB = 3/2 exactly — the certified third-merge cost is the
true one. At N = Θ/2 exactly: 1.4515 ≤ c₄/raw ≤ 1.5 for d = 30 (the factor 2 of the symmetric term). Towards the
ends LB < UB (e.g. (2,20)², N = 8: 1.24 against 1.48).

*In the asymptotic regime*, balanced term, p = q: r = r′ = √2·p, r₃ = 2p, single ranks p:

    (1+√2)/2 = 1.2071  ≤  c₄ / (p+q)  ≤  3/2.

**Is the true third-merge cost below 3/2?** Not decided. The lower bound 1.2071 is all that flattening ranks give
(and the quantum functionals give nothing beyond the three one-party cuts of any coarsening, since their values on
graph tensors are the same linear forms). No network below the certified ones was found: the natural candidate
(route the intermediate state T typed by origin a/d and destination b/c over the four cross bonds, the annihilated
parts over a–d and b–c) is not consistent with the cut LP if entropies are assumed additive, so it pays an
unknown splitting entropy [X as a construction; open as a question]. By how much it could be lower: at most 0.293
per bit; at the sizes computed, 0.

**It does not matter for the engine:** c₄ ≥ p+q from the single cuts alone, i.e. the third merge never costs less
than the raw wires, and §5 needs nothing else.

---

## 5. The level-1 game with true costs

Model as in `attain-notes.md` §2 (`attain/game1.py`): factors = pairs of edges with p:q bits, the adversary picks
the term (θ), we pick one merge per term; value h(w) for merge weights w by LP, V = min_w h(w).

### 5.1 Lemma G [R, given (A)]

**(A)** For every factor the middle term Ψ_{Θ/2} has single-party ranks d₁, d₂ (exponents p, q) and
rank_{ab|cd} = rank_{ad|bc} with exponent ≥ √(p²+q²) − o(1) (its certified value; the two are equal by reflection).

**Lemma G.** Under (A), for every 3-net of order g (any group, any Latin square in fact) and all merge weights w,
the level-1 value with true D1 costs satisfies h(w) ≥ (1/√2)·raw_w = E·g/(√2(g+1)); hence V/E ≥ g/(√2(g+1)) → 1/√2.

*Proof.* Let the adversary answer every factor by its middle term. Under merge k the piece is a tensor on the blocks
of {a,b,c,d}; its cost is at least the cut-LP value. If both wires cross k the blocks are one of:
{ab|cd} (cost ≥ r), {ad|bc} (≥ r′), {ab},{c},{d} or {cd},{a},{b} (≥ (r+p+q)/2), {ad},{b},{c} or {bc},{a},{d}
(≥ (r′+p+q)/2), four singletons (≥ p+q). With r, r′ ≥ √(p²+q²) ≥ (p+q)/√2 each is ≥ (p+q)/√2. If only the wire a–c
crosses k, then b, d lie in one block B and a, c in different blocks; the block of a, or the block of c, does not
contain B, so one of the single-party cuts a | bcd, c | abd is a union of blocks: cost ≥ p. If neither crosses, raw
is 0. So c_k(piece) ≥ raw_k(piece)/√2 for every k and every position of the legs, and
y_e = raw_w(e)/√2 is feasible in the dual LP (2.1) of `attain-notes.md`. Σ_e raw_w(e) = E − Σ_k w_k·g²(g−1)/2
= E·g/(g+1). ∎

Remarks. (i) The lemma uses no information about the third cut and none about how cheap multi-group networks are:
the single cuts make every non-aligned position cost at least raw, and aligned positions cost r or r′. This is
§2.2 of `attain-notes.md` with true costs, extended from rectangles to all pieces. (ii) (A) is [N] for the single
cuts (every table) and, for the two-cut exponent, [R] under flat (arc lemma at its balanced point) and [C]
otherwise (§3.5). If (A) failed for the two-cut exponent, flat would fail and thm_alt would give contracting; so
**"level-1 value with true costs below 1/√2 − 1/(√2(g+1)) on any net" ⇒ flat fails**, for cyclic nets as well as for
F₂^m. On F₂^m nets Theorem B of `q1-notes.md` gives the same floor for all piece families when contracting fails;
Lemma G adds the cyclic nets and needs only the two-term case. (iii) The upper bound is the two-merge design:
V/E ≤ [g²(g−1)²/(2√2) + g²(g−1)/2]/E → 1/√2. The window between the two is O(1/g): straight edges only.

### 5.2 The LP with lower bounds in place of certified costs [N] (`game_true.py`, `game_scan.py`)

Costs: cert = certified (reproduces `attain/game1.py` to all digits); O1 = cut-LP lower bound for every block
pattern with ρ(a,c) = p, ρ(b,d) = q, r, r′ on the arc of the circle, r₃ = 2 min(p,q) (the measured values); H = certified
except four-block patterns, which get the O1 bound; O2 = as O1 with r₃ = 0 (abstractly consistent with the other
ranks, contradicted by every table). O1 ≤ true ≤ cert pointwise, so h_{O1} ≤ h_true ≤ h_cert.

h(w)/E, t-grid 9:

| net | w | cert | H | O1 | O2 | two-merge formula | g/(√2(g+1)) |
|---|---|---|---|---|---|---|---|
| K₄ (g = 2) | (½,½,0) | 0.569036 | 0.569036 | 0.569036 | 0.569036 | 0.569036 | 0.4714 |
| | uniform | 0.666667 | 0.666667 | 0.666667 | 0.471405 | | |
| | (0.45,0.45,0.1) | 0.609666 | 0.609666 | 0.609666 | 0.519450 | | |
| Z₃ | (½,½,0) | 0.603553 | 0.603553 | 0.603553 | 0.603553 | 0.603553 | 0.5303 |
| | uniform | 0.695399 | 0.695399 | 0.681033 | 0.586050 | | |
| | (0.4,0.4,0.2) | 0.682843 | 0.682843 | 0.673703 | 0.574264 | | |
| Z₂² | (½,½,0) | 0.624264 | 0.624264 | 0.624264 | 0.624264 | 0.624264 | 0.5657 |
| | uniform | 0.775790 | 0.741777 | 0.703985 | 0.604738 | | |
| | (0.4,0.4,0.2) | 0.728608 | 0.706296 | 0.705852 | 0.598297 | | |
| Z₄ | (½,½,0) | 0.624264 | 0.624264 | 0.624264 | 0.624264 | 0.624264 | 0.5657 |
| | uniform | 0.752481 | 0.731207 | 0.703985 | 0.604738 | | |
| | (0.4,0.4,0.2) | 0.721304 | 0.705795 | 0.701259 | 0.607798 | | |
| Z₅ | (½,½,0) | 0.638071 | 0.638071 | 0.638071 | 0.638071 | 0.638071 | 0.5893 |
| | uniform | 0.773934 | 0.747342 | 0.720777 | 0.638071 | | |
| | (0.45,0.45,0.1) | 0.690931 | 0.681168 | 0.681168 | 0.631338 | | |
| | (0.4,0.4,0.2) | 0.740858 | 0.722265 | 0.715802 | 0.638071 | | |
| | (0.6,0.2,0.2) | 0.762598 | 0.751839 | 0.743336 | 0.680981 | | |

(More weights in `out/game_*.txt`, weight scans in `out/scan_*.txt`.)

Reading.

- **O1 (measured ranks, every network as cheap as its flattening bound).** At the two-merge corners O1 = cert = the
  two-merge formula, and h_{O1} increases away from the corners in every case (scan of the weight simplex for K₄:
  minimum 0.569036 at (½,½,0); Z₃, Z₂²: `out/scan_3.txt`, `out/scan_2x2.txt`). Hence
  **min_w h_true = min_w h_cert = the two-merge value on these nets: true costs change nothing at level 1**, even
  under the most favourable assumption about the unknown multi-group networks, as long as the third-cut rank is what
  the tables say. (The script asserts O1 ≤ cert for every block pattern, split and angle; this also re-checks the
  cost table of `attain-notes.md` §1.2 against the cut LP.) Away from the corners O1 is below cert by up to 0.07 (three-block positions, where the
  flattening bound (r+p+q)/2 is below the certified min(p,q)+r), but never below the corner value.
- **O2 (third-cut rank ignored).** The bound drops to 0.4714 on K₄ — exactly the price floor of `notes.md` Cor. 3.3
  and exactly g/(√2(g+1)) — and to 0.574, 0.598, 0.605, 0.631 on Z₃, Z₂², Z₄, Z₅, i.e. 5 %, 4 %, 3 %, 1 % below the
  two-merge value, always above g/(√2(g+1)). So the only way true costs could beat the two-merge value on a small
  net is through the third cut, and there the true rank is full (§4.1). The margin shrinks with g and vanishes in
  the limit by Lemma G.
- **Answer to the brief.** With true costs the level-1 value cannot go below 1/√2 on large nets: not on F₂^m nets
  (so no proof of contracting comes out of this), and not on cyclic nets either, where no price barrier was known
  — unless (A) fails, which would refute flat. On the nets of order ≤ 5 it equals the certified value under O1.

---

## 6. Open, and dead ends

- [C] rank_{ad|bc}(Ψ_{2k}) = C_ref(k) for k ≤ min f + (n₁−n₂)², (n₁,n₂) ≠ (1,1). A proof needs the independence of the
  jets of the vertex in the stable range; the antidiagonal structure of the pairing (§2, y-dependence) suggests an
  induction on the weight blocks.
- [C] rank(Ψ_N) = rank PP for n₁ = n₂ (the pairing J is nondegenerate on the jet space).
- [C] exponent of rank(Ψ_{Θ/2}) = certified, without flat. Equivalent to a lower bound for two-term covers of the
  wire pair by this particular family. A triangular family for T of size < n₁+n₂ at the middle level would give it
  for the jet space.
- The true K₄-network cost of the balanced piece, between 1.2071 and 1.5 per bit. Irrelevant for level 1 (Lemma G);
  it would matter only for an engine that pays the third merge on purpose.
- [X] "True ranks below certificates give a better law": the gap is the polynomial factor between C_ref and
  (N+1)P(N), at the sizes where it was seen.
- [X] Size-1 classes, or any classes of atypical size: worse in their own units (§3.2, §3.5.6).
- [X] Lower bound for rank(Ψ_N) from the lowest intermediate energy of a row (to make the flattening triangular):
  every a-particle can annihilate every d-hole (Pascal minors are positive), so every row starts at T = ∅ when
  n₁ = n₂ (indeed Ψ₀ has no zero entry).
- [X] Exact-level ranks as a proxy for the pieces: they have Ward-identity dips (m* − 1) that the cumulative ranks do
  not have.
- Not done: ranks in characteristic 2 for the larger classes (the scripts work for any 31-bit prime only);
  two independent primes for the large tables (the two methods agree, each with one prime).

## 7. Scripts (`research/sat3/truecost/`)

| script | what |
|---|---|
| `psi_build.py n1 e1 n2 e2` | Ψ_N mod P₀ by evaluation/interpolation (numba, 4 threads); identity (a); all seven flattening ranks |
| `factored.py n1 e1 n2 e2 kmax` | rank across ad\|bc from the expansion of B.3; rank of the jet matrices PP, QQ; number of columns |
| `vertex_rank.py`, `vertex0.py` | ranks of the three-point vertex (cumulative; exact levels at y = 0, with the count of splitting T) |
| `szego_check.py` | Prop. 2.1, symbolic |
| `summarize.py` | summary of `out/r_*.txt` |
| `four_party.py out/r_*.txt` | cut-LP lower bound and realisation upper bound for the K₄ cost, from the exact ranks |
| `entropy.py`, `asymptotics.py` | s(c); ln C_ref / ln cert to k = 2·10⁵; ρ(c) |
| `game_true.py NET`, `game_scan.py NET step` | level-1 game with certified costs / lower bounds O1, H, O2 |
| `batch*.sh` | the runs behind the tables |
