# Engine 3, Proposal P3: D.1's 2-adic mode decompositions as pieces for the K_4 clique sum

Implements P3 of `engine3-openai-route.md`. Scripts are in `research/scripts/engine3-p3/`. Tags: [N] computed (the
script is named), [P] short proof given here, [C] heuristic or argued.

## 0. Verdict

**Nothing beats N^4.** I instantiated D.1's construction for the K_4 clique sum: packets, Cauchy kernel, tapered
Hermite recovery and mode expansion, with the three perfect matchings as label coordinates. In Majdoddin's
Signed-Network-Sum cost model I then computed the exact minimal number of names, meaning the 2-adic rank modulo
2^{p_t} across the merge cut, for every interpolation node. At every N tested, 2^1 to 2^128, and for every
multiplicity profile tried, the dominant node costs **exactly N^4**. That is the flattening floor: above 23/6 ≈ 3.833
(ω = 2), above 3.9305 (current curve), and above the input floor 3 [N, `k4_cost.py`]. The extrapolated exponent is
4.000. The D.1 bookkeeping itself (counting mode monomials) is far worse, above brute force per edge [N,
`k4_modes.py`]. No brute-force "beats 4" check was needed. I still checked the whole pipeline (Hermite recovery from
perturbed jets, and Signed-Network-Sum evaluation at nodes) exactly against the direct sum at N = 2 and 4 [N,
`k4_verify.py`].

**Bottleneck.** Steps (a)–(c) of §2.1 cause it: the degree count and Hermite multiplicity, which set the precision.
Steps (e)–(f), the partition count and the depth cap, play no part. At a node of level i, keeping a mode costs
w_0 = v_2(α/t) = a+1−i powers of 2 per crossing excitation. The evaluation loss per jet order is exactly the same
w_0. So D.1's 2-adic budget Σ w β < p_t is a jet-order budget in disguise. To save anything, a node must keep fewer
than about half of the 4λ crossing wires excited, i.e. multiplicity q_t ≲ 2λ. But Σ q_t > deg F = 6λ(2L−1) forces an
average multiplicity of about 6λ per node.

**The open door.** At K = 4 the r-way product of D.1 has r = 2 groups per coordinate, so its pieces meet only two
groups of a merge. The 4-way split (singleton groups) is rank-one and provably ≥ N^4 even modulo 2^p [P].
Majdoddin's hyperedge door is therefore **not** reached at K = 4 by this tool.

## 1. The decomposition (task step 1)

**Dictionary to K_4** (`k4lib.py`):

| D.1 object | K_4 instance |
|---|---|
| vertices | the 4 tables a, b, c, d. Each holds row ports and column ports, so A(Y)B(X) becomes Π_u W_u. D.1's bipartiteness is never used. |
| label coordinates, r = 2 | coord 0 = rows {a,b}\|{c,d}, coord 1 = columns {a,c}\|{b,d}, coord 2 = diagonals {a,d}\|{b,c}. Labels: a = 000, b = 011, c = 101, d = 110. For A > 3, the extra coordinates are constant, i.e. pure copy bits. |
| wire | one bit of an edge string, λ wires per K_4 edge |
| packet | L = 2^A slots of one K_4 edge (each edge is its own pair-label class). Bit i of a slot is the orientation if the endpoints differ in coordinate i, and a copy bit if they agree. At A = 3, 4 of the 8 slots are usable. |
| kernel | W_xy(T) = C(T)/(C′(0)(T−(y−x))), S = [−L, L), α = 2^{A+1} |
| node t, v_2(t) = i < 3 | a merge along matching i |

**What D.1 gives here.** The deformed constraint tensor is a product of per-edge tensors, F(T) = Σ Π_u W_u Π_e G_e(T).
Here G_e(T) is the 2^λ×2^λ matrix Π_x l_{Y_x}((W(T)X)_x) on the ports of edge e, and G_e(0) is the equality
[verified]. At every node, G_e(t) has rank 1 for every crossing edge [N, `k4_modes.py`]; in fact all six edges are
rank 1 there at λ ≤ 2.

**Mode expansion.** Near t, eq. `tensor-mode-expansion` gives modes Z = (tile y_0, b) with weight b+1. Each mode
monomial β yields a piece f_β(u-ports) ⊗ g_β(v-ports): rank 1 across the edge, and hence across the cut.
G_e(t+αζ) ≡ Σ_{Σwβ<p} f_β ⊗ g_β mod 2^p was verified for λ = 2 and 4, at levels 0, 1, 2, for p = 4..16.

Piece counts for one packet with λ = 4, against 2^λ = 16 [N, `k4_modes_lam4.out`]:

| level (edge) | p | D.1 β-tuples | nonzero pieces | true 2-adic rank |
|---|---|---|---|---|
| 0 (ac) | 8 | 120 | 24 | 5 |
| 0 (ac) | 16 | 1200 | 686 | 15 |
| 1 (ab) | 16 | 11044 | 708 | 16 |
| 2 (ab) | 16 | 127353 | 36 | 16 |

D.1's own count exceeds brute force per edge. Only the Smith-optimal grouping (Anthropic's "grouping counted by
ranks") stays at or below 2^λ.

**Per-edge Smith valuations** at λ = 4 (ζ = 1 and 3 give identical results):
* level 0: [0,4,4,6,6,8,9,9,10,10,12,13,13,15,15,18]
* level 1: [0,3,3,3,3,6,…,12]
* level 2: [0,2,2,2,2,4×6,6×4,8], i.e. exactly 2·(number of excited wires), binomially distributed.

So a crossing excitation costs about w_0 = a+1−i per wire.

## 2. Cost across the merges (task steps 2–3)

**What is computed.** At node t (level i), across the cut of matching i, the term F(t+αζ) is a Kronecker product of
the 4 crossing edges' matrices; the internal edges sit on one side. Its exact minimal number of names modulo
2^{p_t} is therefore
R_t = #{(k_1..k_4) : Σ v_e(k_e) < p_t} [P: Smith normal form is multiplicative under ⊗ over ℤ_2].

The precision p_t is the exact one from Lemma `tapered-hermite`: p_t = p − v_2(E_t(0)) + (q_t−1)(a+1−i). This is
tighter than D.1's bound p + 8hD + 8M(a+1).

**What is reported.** The exponent is max_t log_N R_t, the naming bits of the dominant term. Majdoddin's cost is at
least this; building the merged tables adds ⟨N², N, N²⟩, which is N^5 naively.

Results [N, `k4_cost.py` → `k4_cost.out`; `k4_cost_extra.py` → `k4_cost_extra_A3.out`, `_A4.out`]:

| setting | N = 2, 4, 8, 16 | N = 2^8 … 2^128 | extrapolated |
|---|---|---|---|
| D.1 taper q(i) = M(3−i), M = 6λ, A = 3, p = 1 or 6λ+1 | 4.0000 | 4.0000 | 4 |
| best uniform-per-level (q_0, q_1, q_2) with Σq > deg F, exhaustive grid | 4.0000 | 4.0000 (to 2^32) | 4 |
| A = 4 (L = 16), uniform or taper | 4.0000 | 4.0000 (to 2^64) | 4 |
| Majdoddin Table 2, K = 4: input 3; 23/6 = 3.833 (ω = 2); 3.9305 (current curve); flattening 4; CVZ 4.638 | | | |

Example at λ = 64 (A = 3, uniform q = 412):

| level | p_t | maximal total crossing valuation |
|---|---|---|
| 0 | 2881 | 1152 |
| 1 | 2058 | 832 |
| 2 | 1235 | 512 |

Every name survives, so R_t = N^4 exactly. The pipeline was checked at N = 2 and 4 [N, `k4_verify.py`]:
* F(T) has degree 75 at λ = 1 and 180 at λ = 2; the bound M(2L−1) is tight at λ = 2.
* Hermite recovery from jets perturbed by multiples of 2^{p_t} returns Z mod 2^p (p = 1, 8) for the taper and for the
  near-minimal profile.
* At nodes t = 1, 2, 4, the merged evaluation Σ_k T_0[k] T_1[k] with truncated Smith pieces equals F(t+α) mod 2^p.

## 3. The gap and where it sits (task step 5)

**Hypothetical degree needed.** Keep the kernel's Smith profiles and the 14-node grid, but suppose the deformation had
total degree D = cλ. The best exponent would then be [N, `k4_cost_extra_A3.out`]:

| c | 22 | 20 | 17 | 15 | 12 | 10 |
|---|---|---|---|---|---|---|
| exponent | 3.9999 | 3.997 | 3.935 | 3.835 | 3.544 | 3.280 |

D.1's kernel has c = 90 at A = 3 and c = 186 at A = 4. Even the idealised kernel I could think of, which decouples
each crossing wire only at the nodes where it crosses, has c = 56 on this grid. On one node per matching, its average
q equals 4λ, the number of crossing wires per node, which sits on the saturation boundary [C].

**Gap.** Any saving needs a degree about 4× smaller than D.1's. Reaching 23/6 needs about 6× smaller.

**Bottleneck.** Steps (a) deg F ≤ M(2L−1), (b) Σ q_t > deg F, and (c) loss (q_t−1)·v_2(α/t) together put
p_t/w_0 ≥ q_t − 1 ≈ M. A term then keeps about q_t crossing excitations out of 4λ. The scaling by α cancels, so the
2-adic truncation gives exactly the jet-order rank and no more [C, numerically exact here]. Steps (e) and (f) are
irrelevant at K = 4: u ≤ 3 is fixed by the three matchings, so D.1's 1/√u gain is a constant.

**4-way split [P].** If every term is a product of single-table factors, then
2^m T_4 ≡ Σ_{k≤R} (rank one) mod 2^{m+p} with p ≥ 1. Since 2^m(I + 2^p E) has full rank over ℚ_2, R ≥ N^4.
3-group merges such as {ab}, {c}, {d} coarsen to a 2|2 cut and are no cheaper [C].
