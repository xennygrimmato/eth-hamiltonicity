# Engine 3: can OpenAI's mechanisms decay faster than 1/log K? Rate analysis of the interpolation route and of Theorem D.1

5 Nov 2026. Research note, no code committed. Read after `permanent/openai-math-scout.md` §2 (first description of the
two OpenAI engines), `permanent/parity-barrier.md` (the M₀-template is closed at √Q), `permanent/rate.md` and
`permanent/rho-lower-bound.md` (Anthropic's ρ ≥ 1/√2), `ambitious-targets.md` §0 (the dense wall), `sat-width.md` §4.
Scripts for this note: `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/engine3/smith_kernel.py`,
`.../engine3/smith_tensor.py` (outputs quoted in §2.4; raw run log
`/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/tasks/b3drvdf0r.output`).

Sources (quoted by label and line): [O] OpenAI, *The Exponential Time Hypothesis is false*, `main_full_version.tex`
(main text), `quantitative-reduction.tex` (Appendix D statement, labelled `app:quantitative`/`thm:tensor-contraction`),
`quantitative-contraction.tex` (proof, `app:tensor`); [M] Majdoddin arXiv 2610.41622; [DL] Dias–Lima arXiv 2611.00517;
[OD] O'Donnell hexagon:2610.00572; [K] Kominers hexagon:2610.00574.

Tags: **[R]** proved in a source (theorem cited) or by a short argument given here; **[C]** conjecture/heuristic;
**[N]** computed (exact arithmetic, script named) or to be computed.

---------------------------------------------------------------------------------------------------

## 0. Verdict

1. **Both OpenAI mechanisms are single-level, not towers.** Anthropic's exponent is e_K = ρ^{#levels} with
   #levels = log log K (K squares per level), so e_K = (log K)^{−log₂(1/ρ)}; the 1/√log is 2^{−1/2} per level. OpenAI's
   two engines have **no per-level factor at all**: the whole saving is one factor 1/√(#interpolation levels), and the
   number of levels is at most logarithmic in the instance — Q ≤ log n points in the main text (product label space
   D = r^{2Q} ≤ n), u ≤ log₂ L ≤ 0.9·log₂ s two-adic valuation levels in D.1 (a packet of L slots has shifts in
   [−L, L), whose 2-adic filtration has depth log₂ L; L ≤ s^{0.9} because the packet vertex has degree 2L). [R: §2.1–2.2]
   This is why [M] finds OpenAI's crossover "polynomial in the exponent it must save": there is nothing to compound, and
   also nothing that compounds the loss.
2. **The caps are of a different nature from Anthropic's, but have the same strength.** Anthropic: a rank/flattening fact
   (ρ ≥ 1/2, Prop. 4.8 of [M]; ρ ≥ 1/√2 for graded two-order pieces, `rho-lower-bound.md`). OpenAI I: the approximate
   degree of parity under Bin(Q, p) (R ≥ c√(Q log(1/ε)), `parity-barrier.md` Thm 1) times the product-set structure of
   the label space (Q ≤ log n/(2 log r)). OpenAI II: the Hardy–Ramanujan partition count of mode monomials,
   exp(O(√(N·p))) with N·p = Θ(M²/u) *independent of the packet size*, times the filtration depth u ≤ log₂ L. [R]
   In all three the exponent is (size)/√(#levels) with #levels ≤ log(size); three different reasons give three
   square roots. None of the three is a reason the others can circumvent: a hybrid of I and II (low-degree kernel with
   2-adically small non-local part) is impossible because 2-adic smallness of a polynomial kernel at a node needs the
   full Lagrange product (§2.3 (c)). [R for the hybrid's failure; C for "none can circumvent"]
3. **Numerical anchor [N].** The 2-adic Smith invariants of D.1's deformed packet tensor (L = 16, flattening 2^16 × 2^8,
   exact mod 2^30) match D.1's mode-monomial bookkeeping to within 0–40 % at every precision p ≤ 30 (e.g. p = 26: 28 true
   invariants vs 31 monomials at valuation level i = 0; 123 vs 209 at i = 1). So the mode expansion is essentially the
   optimal rank-type decomposition **of this kernel**; the only lever left in D.1 is a different kernel, and the kernel is
   forced (it is the unique degree-(2L−1) interpolant of the shift permutations through the 2L nodes; adding C(T)G(T) is
   2-adically negligible near every node). [R for uniqueness; N for the invariants]
4. **Dias–Lima's floor is weak and specific.** Their 2^{Ω(√tw)} (Thm 8.1) bites through Lemma 6.2 (a product of
   own-coefficients equal to 1 at T = 0 cannot vanish to high order at every node) and needs (H1) polynomial restoration,
   (H2) recovery exact for all polynomials of degree ≤ MR, (H3) decomposition-priced evaluation. It leaves open, *inside*
   the clause-product scheme, a design on expanders costing 2^{Õ(√n)}, which would be **polynomial decay** (e = n^{−1/2}
   per variable) and would beat the dense wall for everything with an O(n)-bit witness. Nothing in [DL], [M], [O] or our
   notes excludes it; `parity-barrier.md` Thm 2 excludes it only for OpenAI's own template (measurement part polynomial
   in T). This is the clause-product analogue of Majdoddin's open door, and it is Proposal P2. [R/C]
5. **Proposals (§4).** P1: decide the D.1 cap by 2-adic Smith ranks of deformed packet tensors (finite, L = 16–32; a
   superlinear valuation growth would be the gain; a proof of linear growth for every integral kernel would be the D.1
   analogue of ρ ≥ 1/2). P2: the general-interface design with t-dependent measurement spaces on bounded-occurrence
   expanders, as a finite linear-algebra feasibility problem at n = 16–24, Q = 4–8. P3: 2-adic mode decompositions as
   hyperedge pieces for Majdoddin's open door (K₄ clique sum, target below N^{23/6} at ω = 2). P4 (negative): grafting
   D.1 on Anthropic's tower cannot help, because the root call sets the rate.

---------------------------------------------------------------------------------------------------

## 1. The two mechanisms, precisely

### 1.1 Mechanism (a): the main-text interpolation algorithm

**Object.** [O] l.590 (eq. `overview-direct-count`): #F = Σ_{x∈{0,1}^n} Π_{e∈𝓕} Φ_e((x_v)_{v∈I_e}), Φ_e = 1 − Π_{v∈I_e}(1 − L_{e,v}(X_v)),
total degree ≤ M = Σ|I_e| ≤ 3n in the bounded-occurrence case. The general case multiplies instead one factor per *parity
test* P_i(x) = 0 over 𝔽₂ (polylog-sparse, degree ≤ k), lifted to the integers by the complemented Beigel–Tarui
idempotent p_ℓ and truncated *globally* in 𝒜_ℓ = ℚ[V]/(V^ℓ) so that the input degree stays k(m_test + 2(ℓ−1)) = O(n)
(Lemma `lem:total-order`, l.2958). [R]

**Deformation.** l.642–668: every *occurrence* X_v in factor e is replaced by a linear form ⟨P⃗_{e,v}(T), X⃗⟩ with
P⃗_{e,v}(0) = e_v and deg_T P⃗_{e,v} ≤ R, giving H(T) = Σ_x Π_e Φ_e(⟨P⃗_{e,v}(T), x⟩) with
"H(0) = #F, deg H ≤ MR ≤ 3nR" (eq. `overview-value-degree`). [R]

**Design at a point (the "designated points" where counts factor into local sums).** Definition `(r,τ,D)-design`,
l.690–721: a partition into r groups of size ≤ 2n/r, one assigned group σ_e(t) per clause, integer measurement matrices
C_g with ≤ 2τn rows in total and row ℓ₁-norm ≤ D, and the separation condition (eq. `outline-separation`)
"⟨P⃗_{e,v}(t), x⟩ = ⟨P⃗_{e,v}(t)|_{S_g}, x_g⟩ + Σ_{h≠g}⟨λ⃗_{e,v,h}, y_h⟩", i.e. P⃗_{e,v}(t)|_{S_h} ∈ rowspace(C_h) for h ≠ g.
Then (eq. `outline-separated-sum`) H(t) = Σ_{y⃗} Π_g Σ_{u: C_g u = y_g} A_{t,g}(u; y⃗), at cost (2D+1)^{2τn}·2^{2n/r}. [R]

**Recovery (Hermite interpolation + inclusion–exclusion).** l.813–944: with q = ⌊3nR/Q⌋, the jets H(t+z) mod z^{q+1} at
t = 1..Q determine H (QJ > deg H). The jets are computed by introducing a formal copy X⃗ of x in the increments
ΔP⃗(z) = P⃗(t+z) − P⃗(t); since every entry of ΔP⃗ is divisible by z, "deg_X⃗([z^j]𝓖_x(X⃗, z)) ≤ j", and Boolean Möbius
inversion gives (eq. `outline-taylor-recovery`) H(t+z) ≡ Σ_{|E|≤q} Σ_{U⊆E} (−1)^{|E|−|U|} 𝓩_{t,E,U}(z), each 𝓩 a separated
sum with the formal input fixed to 1_U. This costs the "Taylor data" factor C_q = Σ_{j≤q} 2^j C(n,j). [R]

**The three costs** (Prop. `prop:general-count`, eq. `three-costs`, l.2055), exactly:
> 2^{O(n[(R/Q)·log(2Q/R) + τ·log(2D+1) + 1/r])}.

**Construction of the forms (the parity-approximation step, l.1022–1428).** Auxiliary labels 𝓑 = ([r]×[r])^Q, D = r^{2Q}
("one replacement row for every such index"); swaps Π_s (exchange the pair at position s); V₀ = Π_s Π_s, W₀ = ½Σ_s(I−Π_s);
**M₀ = V₀ f(W₀)** with f the degree-(R−1) interpolant of (−1)^j on a window 𝓘 of R consecutive integers around Qp,
p = (r−1)/(2r). In the product eigenbasis (entries in {0,±1}) a basis vector with j antisymmetric positions has
M₀ψ⃗ = (−1)^j f(j) ψ⃗, so M₀ fixes every ψ⃗ with j ∈ 𝓘; the remaining basis vectors are the measurement rows, "c = D·Pr[W ∉ 𝓘]
≤ 2D exp(−R²/(8Q)) ≤ Dτ/(3r)". The support of M₀ is on pairs (u,w) whose schedules disagree in |E_{u,w}| ≤ R−1 positions
(eq. `overview-partial-swaps`), each killed at its bad points by φ_{u,w}(T) = Π_{s∈E_{u,w}}(1 − T/s) (Step 3). The parameters
(eq. `overview-explicit-parameters`): r = ⌊√λ/ν²⌋, Q = ⌊λ/(128ν)⌋, R = 4⌈√λ⌉, τ = 1/(rλ), D = r^{2Q} ≤ (2n)^{1/128},
with λ = ⌈log₂ n⌉, ν = ⌈log₂ λ⌉, and the balancing requirement "12D² ≤ M, 2Qr² ≤ n" (eq. `overview-balance-requirements`). [R]

The polynomial f is the Alman–Williams typical-weight interpolant ([OD] Lemma 2.1, eq. (2.2)):
f(z) = (−1)^a Σ_{j≤b} (−2)^j C(z−a, j), error Pr[f(J) ≠ (−1)^J] ≤ 2exp(−b²/(8n)) for J ~ Bin(n,p). In Newton form it is the
truncation of the 2-adically convergent series (−1)^z = Σ_j C(z,j)(−2)^j, i.e. the Mahler expansion of (−1)^z on ℤ₂, whose
coefficients have valuation j: this is the same "linear weight growth" that governs D.1's modes (§2.3). [R]

### 1.2 Mechanism (b): Theorem D.1, Boolean tensor contraction

**Statement** (`quantitative-reduction.tex` l.26–49, verbatim):
> **Theorem (Boolean tensor contraction).** Fix positive constants C, A, b. Let s ≥ 2 be an integer, and let 𝓛 be the total
> length of the graph and tensor descriptions of a bipartite tensor network with at most Cs edges and maximum degree at most
> ⌈s^{9/10}⌉. Suppose that the number of vertices is bounded by a fixed polynomial in s, and that the entries belong to
> 𝓑_{P₀,ℓ} = (ℤ/2^{P₀}ℤ)[V]/(V^ℓ), 1 ≤ P₀, ℓ ≤ Cs. Suppose, uniformly for every vertex and Boolean choice of its ports,
> that its entry can be computed from the description in time (s+𝓛)^b 2^{A s^{9/10}} and space (s+𝓛)^b. Then the
> contraction can be computed deterministically in (s+𝓛)^{O(1)} 2^{O(s/√log s)} bit operations and (s+𝓛)^{O(1)} bits of
> space. Constants depend only on the fixed bounds in the hypotheses. In particular, ℓ = 1 is permitted.

Here the network is a bipartite multigraph with one bit per edge, Z = Σ_{x∈{0,1}^{E}} Π_v T_v(x|_{δ(v)}); the fixed-density
#k-SAT bound follows by giving each clause a vertex, each variable an equality tree, subdividing every edge, s = n + m,
P₀ = n+1, ℓ = 1 (l.65–98); the general bound encodes the retained monomials of the truncated parity-test product with
O(n log log n) wires on 2⌈n^{1/4}⌉ group vertices (Lemma `lem:tensor-sparse-query`). [R]

**Proof structure** (`quantitative-contraction.tex`), with the dictionary to Anthropic's engine:

| step | D.1 | Anthropic's counterpart |
|---|---|---|
| coefficient ring | 𝒪 = ℤ_(2)[U]/(f), f irreducible mod 2 of degree e = 4λ; 𝒜_p = 𝒪[V]/(V^ℓ)/(2^p); 2^e residue-field lifts give interpolation points with pairwise unit differences ("fewer than s^4 points") | none (exact integers) |
| recursive unit | a *call*: a bipartite network with M wires at precision p; leaf if M ≤ H = ⌈s/⌊√λ⌋⌉ (brute force 2^H) | a level: a (K, L)-clique, brute-force base case |
| grouping | labels in [r]^a, r = 64, a = a_d = 2Σ_{j≤d} u_j; edges packed into ≤ 3M/L packets of L = 2^a slots (Lemma `tensor-packets`, conditional expectations) | the g × g grid of nodes, rows/columns as the two merges |
| deformation | Cauchy kernel W_{xy}(T) = 𝒞(T)/(𝒞′(0)(T − (y−x))), 𝒞(T) = Π_{t∈S}(T − t), S = [−L, L); W(0) = I; F(T) = Σ_{X,Y} A(Y)B(X) Π_x l_{Y_x}((W(T)X)_x), deg F ≤ M(2L−1) (eq. `tensor-deformed-contraction`) | the eight-square / Appendix-B piece identity for a crossing |
| where locality comes from | at a node t with v₂(t) = i, W(t) = (𝒞′(t)/𝒞′(0))·(shift by t): adding t flips bit i of the slot, so row and column ports of a packet are paired *within* the group defined by label coordinate i; near t (T = t + αz, α = 2^{a+1}) cross-group entries expand as Σ_b (2^{i+1}/(T−y₀+x))^b j^b (eq. `tensor-mode-expansion`) | a term of the identity is local to a row (or column) merge |
| "pieces" | **mode monomials** Z^β: one mode Z per (packet, tile, b) of weight w_Z = b+1, ≤ 6M/D_t modes of each weight (eq. `tensor-mode-multiplicity`), D_t = L/2^i; only Σ w_Z β_Z < p_t survive (eq. `tensor-mode-budget`), number exp(O(√(M p_t/D_t))) = exp(O_C(M/√u)) (eq. `tensor-partition-count`) | the pieces A_s, |I| ≤ (2λ)^c per crossing |
| "merging" | for each β and each group g a *child*: all vertices of group g on one side, one new vertex per packet on the other, edges = retained ports of the packet in g; F(t+αζ) = Σ_β Π_g Z_{g,β} mod 2^{p_t} (eq. `tensor-recursion-identity`); child has ≤ 6M/r = 3M/32 < M/8 wires, packet vertex degree ≤ 2L ≤ Δ | merged node tables, merged instance on g nodes |
| recovery | **tapered Hermite** (Lemma `tapered-hermite`): multiplicities q_t = h·max(0, u − v₂(t)), h = ⌈3M/u⌉, Σ_{t≠0} q_t ≥ Lhu > deg F; precision loss v₂(E_t(0)) ≥ −6D_t h; children run at p_t = p + 8hD_t + 8M(a+1) = O_C(M D_t/u) (eq. `tensor-precision-bound`); jets F(t+αz) mod 2^{p_t} by Lagrange at M(2L−1)+1 unit-difference points | exact (no interpolation) |
| schedule | u_d = ⌊ελ/2^d⌋, ε = 1/(128·1024); M ≤ Cs 8^{−d}; depth ≤ (log₂ λ)/6 + O(1); L, D_arr ≤ s^{1/1000} | K_{ℓ+1} = K_ℓ², e_{ℓ+1} = ρ e_ℓ + … |

What plays Anthropic's ρ: nothing. The per-call branching exp(O(M/√u)) does not multiply a rate; it is paid once per
call, and calls shrink geometrically (M by 8, u by 2), so the cost at depth d is exp(O((s/√λ)(√2/8)^d)) and **the root
alone sets the rate** (l.590–605 of the proof: "Multiplying these bounds over the O_C(log λ) depths … gives at most
exp(O_C(s/√λ) + O_C(λ log λ)) calls"). The leaf threshold H = s/√λ is chosen to match. [R]

---------------------------------------------------------------------------------------------------

## 2. Rate analysis

### 2.1 D.1: the inequality chain and the one capping step

Per active call with M wires, u retained valuation levels, packet size L = 2^a, D_t = L/2^{v₂(t)}:

(a) deg_T F ≤ M(2L−1) — each of the M row forms has degree 2L−1 (a Lagrange basis polynomial through 2L nodes). [R]
(b) recovery needs Σ_t q_t > deg F; with multiplicities tapering linearly in the level, slope h ≈ 3M/u. [R]
(c) 2-adic Hermite loss ≥ −6D_t h ⇒ children precision p_t = Θ(M D_t/u) (the taper buys exactly the 1/u: the proof
    remarks that constant multiplicity q_* = Θ(M) on u levels would lose Θ(M D_t), l.350–360). [R]
(d) crossing entries at T = t + αζ are 2-adically small: mode of weight b+1 per (packet, tile, b); N = 6M/D_t modes per
    weight. [R]
(e) number of mode monomials of total weight < p_t with N colours per weight (a coloured partition count):
    exp(O(√(N p_t))) = exp(O(√((M/D_t)(M D_t/u)))) = **exp(O(M/√u))**; the packet size D_t cancels. [R, eq. `tensor-partition-count`]
(f) **u ≤ a ≤ log₂ L**: a level is a 2-adic valuation of a shift t ∈ [−L, L); and L ≤ Δ/2 = s^{0.9}/2 because the new
    packet vertex has 2L ports, and its entries cost exp(O(L log s)) ≤ 2^{O(s^{0.9})} only for L ≤ s^{0.9}. Hence
    **u = O(log s)** whatever the constants. [R, eqs. `tensor-parameters`, `tensor-packing-conditions`]
(g) total: calls ≤ Π_d exp(O(s 8^{−d}/√(λ 2^{−d}))) = exp(O(s/√λ)); leaves 2^H = 2^{s/√λ}. [R]

The exponent is therefore E(s) = Θ(s/√u₀), u₀ = ελ, and the two facts that cap it are **(e) Hardy–Ramanujan with linear
weights** and **(f) filtration depth ≤ log(packet size)**. Neither is a rank or flattening fact. (f) is group theory: the
shifts of a packet form ℤ/2L and any filtration of a group of order 2L has depth ≤ log₂(2L); indexing slots by 𝔽₂^a or
by a non-abelian 2-group changes nothing. (e) is the 2-adic analogue of Anthropic's Fock-space growth: the weights are
linear in b because (T − y₀ + x)^{−1} restricted to a tile is locally analytic of fixed order, hence has Mahler
coefficients of linearly growing valuation (Amice); `openai-math-scout.md` §2.3 states this heuristically [C]; §2.4 below
confirms it numerically for L ≤ 16 [N].

Where exactly the 1/u would have to become 1/u^{1+δ}: in (c)–(e), the product N·p_t = Θ(M²/u). Polynomial decay
e = s^{−β} needs √(N p_t) = M^{1−β}, i.e. either p_t = O(M D_t /M^{2β}) (a recovery with loss sublinear in the degree;
impossible for Hermite data at 2-adically clustered nodes [C]), or weights growing like b^{1+δ} so that the coloured
partition count is exp(O((N p)^{1/(2+δ)})) [C: excluded for this kernel by §2.4].

### 2.2 The main-text route: the inequality and its cap

Exponent/n = (R/Q)·log(2Q/R) + τ·log(2D+1) + 1/r subject to [R, l.1360–1428]:
(i) tail: 2e^{−R²/(8Q)} ≤ τ/(3r) ⇒ R ≥ √(8Q ln(6r/τ)) = √(8Q ln(6r²λ)) at τ = 1/(rλ);
(ii) label space: D = r^{2Q}, 12D² ≤ M ≤ 3n ⇒ **Q ≤ log₂ n/(4 log₂ r) + O(1)**;
(iii) measurements: τ log(2D+1) ≈ 2Qτ log r ≈ 1/r at τ = 1/(rλ).
So R/Q ≥ √(8 ln(6r²λ)/Q) ≥ √(32 ln(6r²λ) log₂ r / log₂ n) = Θ((log log n)/√log n) at r = Θ(√λ/ν²), and the group term 1/r
is of the same order: exponent n(log log n)²/√log n. [R]

The two capping facts: **(i) is the approximate degree of parity on the weight distribution**, tight for every M₀ in the
template (`parity-barrier.md` Thm 1: ε ≥ Pr[Bin(2Q,½) ≥ Q+R], i.e. R ≥ (1−o(1))√(Q ln(1/ε)); the elementary form is a
sign-change count: a univariate polynomial agreeing with (−1)^j on a set that contains k pairs of adjacent integers has
degree ≥ k, and a set of binomial mass 1−ε inside the central window contains ≳ √(Q log(1/ε)) such pairs). **(ii) is the
product structure of the labels**: the swap algebra generated by Π_s maps a label (α, β) to every hybrid (α|_{T^c}β|_T, …),
so the label set must be closed under partial swaps, i.e. a product set, of size ≥ 4^Q; with the balancing requirement
D ≤ n/12 this forces Q ≤ log n/(2 log r). [R, short argument; C that no other embedding avoids it]. `parity-barrier.md`
Thm 2 strengthens (i)+(ii) to R ≥ cQ/√log n for *any* label structure and any Q in the template, via Hamming-cube
isoperimetry/ARV: so the template is closed at 2^{Θ̃(n/√log n)} regardless of how the two constraints are traded.

In D.1 the Taylor cost is absent (jets come from polynomially many Lagrange points because the mode expansion holds on the
whole 2-adic ball t + α𝒪, not only at t) and is replaced by the mode count — of the same order s/√log s. Two unrelated
costs, same magnitude. [R]

### 2.3 Answers to the specific questions

*Same nature as Anthropic's cap (rank/flattening)?* **No.** Anthropic: subadditivity of rank across a split (Prop. 4.6 of
[M], ρ ≥ 1/2 Prop. 4.8), refined by quantum functionals. OpenAI I: concentration of measure (binomial tail / isoperimetry)
plus product-set combinatorics. OpenAI II: coloured-partition growth plus filtration depth. The three caps do share one
abstract shape — the saving is 1/√(#levels), #levels ≤ log(size) — and in two of the three (Anthropic's Fock space and
D.1's modes) the square root is literally Hardy–Ramanujan's exp(c√E). [R/C]

*Could a better approximating polynomial give o(1/log)?* No, inside the template: symmetric or not, every M₀ has
R ≥ c√(Q log(1/ε)) (`parity-barrier.md` Thm 1), and any label structure has R ≥ cQ/√log n (Thm 2). The gain of the
Newton/Mahler form over the window is that its error is 2-adically small (divisible by 2^{b+1}) at *every* integer, not
only on the window — but only in eigen-coordinates; in the standard basis I − M₀ has entries ±1 (e.g. Q = 1, b = 0:
I − Π), so this smallness cannot be used without the projectors' 2^{−Q} denominators. [R, computed by hand] 

*A different deformation?* The open space is Definition `def:layout` with **t-dependent, non-polynomial measurement
subspaces** (`parity-barrier.md` §5: strictly stronger than the template, "runs instead of windows" gives constant-factor
gains only in the regime the engine needs; no lower bound known). This is also exactly the space [DL] §9 leaves open
(§2.5). [R]

*A different interpolation scheme?* Hermite over ℚ exact for all polynomials of degree ≤ MR is [DL]'s (H2). The 2-adic
taper of D.1 is a recovery exact only for polynomials with F(t+αz) ∈ 𝒜[z], and it already escapes (H2); its price is the
precision budget p_t = Θ(MD/u). A recovery that used the special form of F (a Boolean sum of products) rather than its
degree is not excluded by anything; we have no candidate. [C]

*(c) Hybrid "low-degree kernel + 2-adic grading" fails.* [R] One might hope to lower deg_T F from M(2L−1) to MR with
R ≈ √L (so that the taper slope and p_t drop by R/L, giving exponent M√(R/(Lu)) — polynomial decay in L). But 2-adic
smallness of the non-local entries of a *polynomial* kernel at a node is a Lagrange phenomenon: W_{xy}(t+αz) is divisible
by 2^{a+1−i} because 𝒞(t+αz)/𝒞′(0) carries the valuations of all 2L−1 other nodes (Lemma `tensor-integrality`). A kernel of
degree R ≪ 2L can vanish at ≤ R points per entry and is otherwise a unit; "zero at the bad points" (the main text's
φ_{u,w}) is the cheapest smallness, and its non-local remainder (I − M₀)ζ is then not small but *measured*, which is
mechanism (a) again with its measurement cost. The degree-(2L−1) Cauchy kernel is the unique polynomial of that degree
with W(0) = I and W(t) ∝ shift_t for t ∈ S\{0}; any other kernel differs by 𝒞(T)G(T), which is ≡ 0 modulo a power of 2
larger than every precision in use near every node. So within D.1's architecture the kernel is canonical.

*Compounding (P4, negative).* Grafting D.1 on Anthropic's tower, or Anthropic's levels under D.1's root, cannot change
the rate: D.1's cost is dominated by its root call (geometric decay (√2/8)^d below it), and any first step on s wires
costs e(s)·s with e(s) ≥ c/√log s for both engines. A tower helps only if each level's loss factor ρ < 1, which D.1 does
not have (and Anthropic's ρ ≥ 1/√2 is its own cap). [R]

### 2.4 Numerical anchor: 2-adic Smith invariants of D.1's kernel and packet tensor [N]

`smith_kernel.py` computes the Cauchy kernel at T = t + αζ (ζ = 1, 3) for L = 8, 16 exactly over ℚ, extracts the
*crossing* block (row slots x and column slots y with equal bit i, where i = v₂(t)), and takes its Smith normal form over
ℤ_(2). Results (L = 16, a = 4, α = 32):

| node t (i) | min entry valuation (D.1 bound a+1−i) | Smith valuations of the 8×8 crossing block |
|---|---|---|
| 1 (0) | 5 (5) | 5, 7, 11, 13, 19, 21, 25, 27 |
| 2 (1) | 4 (4) | 4, 4, 6, 6, 10, 10, 12, 12 |
| 4 (2) | 3 (3) | 3, 3, 3, 3, 5, 5, 5, 5 |
| 8 (3) | 2 (2) | 2, 2, 2, 2, 2, 2, 2, 2 |

(ζ = 3 gives identical valuations.) Reading: at level i the invariants come in 2^i-fold copies (D.1's "tiles"), and the
distinct values grow as base + 2(b + v₂(b!)) ≈ 4b: **linear growth** in the index b, slope ≈ 4 instead of D.1's nominal
weight b+1 (D.1 over-counts by a constant factor, consistent with [DL] E5's constant 16077 bits per edge). The number
of invariants with valuation ≤ w is ≈ 2^i·w/4 per packet, i.e. Θ(M/D_t) per weight across the 3M/L packets — D.1's N up to
a constant. So the mode expansion is a constant factor away from the Smith-optimal bilinear decomposition of this
kernel, and the coloured-partition count exp(√(Np)) is forced for it.

`smith_tensor.py` goes from the kernel matrix to the object that actually governs the branching: the flattening of the
deformed packet factor P_g(Y_g, X_g; X_{g′}) = Π_{x∈g} l_{Y_x}((W(T)X)_x) across (group g's row ports and local column
ports | crossing column ports), L = 16, |g| = 8: a 2^16 × 2^8 matrix over ℤ/2^30, Smith-eliminated with exact 2-adic
pivoting. Number of invariants with valuation < p (= minimal number of rank-one terms modulo 2^p across the split) versus
D.1's mode-monomial count (monomials in the kernel-block modes of total weight < p, degree ≤ |g|) versus brute force 2^8:

| p | i = 0: tensor / monomials | i = 1: tensor / monomials | brute force |
|---|---|---|---|
| 2 | 1 / 1 | 1 / 1 | 256 |
| 8 | 3 / 3 | 5 / 5 | 256 |
| 14 | 7 / 7 | 23 / 23 | 256 |
| 20 | 14 / 15 | 62 / 74 | 256 |
| 26 | 28 / 31 | 123 / 209 | 256 |

At i = 2 (modes of weights 3,3,3,3,5,5,5,5) the counts are 19/19 at p = 8, 102/180 at p = 14, 202/940 at p = 20 and
251/3526 at p = 26: there the trivial bound 2^{|g′|} = 256 binds and the monomial count exceeds brute force, so at L = 16
only the levels i = 0, 1 are informative (the monomial count is an upper bound; D.1 only uses it where it is below 2^{M}).
The true 2-adic rank of the tensor equals the mode-monomial count exactly up to p ≈ 14 and is below it by at most 40 %
at p = 26 at the informative levels (where the degree cap |g| = 8 already bites). **Conclusion [N→C]:** for the Cauchy kernel the mode expansion is
essentially the optimal rank-type decomposition; there is no hidden slack of the kind Anthropic's "grouping counted by
ranks" exploits ([M] §2.3), and the only remaining lever for D.1 would be a kernel with superlinear invariant growth,
which §2.3 (c) argues does not exist among polynomial kernels. Caveat: L = 16 is far from asymptotic; P1 proposes L = 32.

### 2.5 Where Dias–Lima's 2^{Ω(√tw)} bites, and what escapes it

**Their scheme** (Def. 5.1): (a) deformation P_o(T) ∈ ℚ[T]^n, deg ≤ R, P_o(0) = e_v, own coefficient c_o(T) = (P_o(T))_v with
c_o(0) = 1, deg H ≤ MR; (b) recovery: a functional Λ on Hermite data at X ⊂ ℚ\{0} with "Λ(f) = f(0) for every f ∈ ℚ[T]
of degree at most MR"; (c) designs: per point, groups S_{t,h}, assigned group α_t(e), *arbitrary* subspaces R_{t,h} with
P_{e,v}(t)|_{S_{t,h}} ∈ R_{t,h} for h ≠ α_t(e). Cost model (§5.2): per point κ(t) ≥ max(2^{s_t}, 2^{w_t}, C(n, min(q_t,⌊n/2⌋)))
(DP-type) and additionally 2^{ρ_t} (product-type). [R]

**The bite.** Lemma 6.2: "G(T) = Π_o c_o(T). Then deg G ≤ MR and G(0) = 1. At every t ∈ X, G vanishes to order at least
|Z_t|. If |Z_t| ≥ q_t + 1 for all t, all Hermite data of G are zero, so Λ returns … 0; but it must return G(0) = 1."
Hence a point t with ≤ q_t occurrences losing their own variable; Lemma 6.1: every other foreign occurrence is absorbed by
a *measured* group adjacent to the clause's group; Theorem 7.1: tw(Pr(F)) ≤ (w_t+1)s_t − 1 + q_t; Theorem 8.1:
"every DP-type (hence every product-type) scheme on F costs at least 2^{min(√((tw+1)/2) − 1, (tw+1)/2, ⌊n/2⌋)}";
Theorem 8.3: random 3-CNF at density ∆ > 3 has tw = Ω_∆(n) w.h.p., so the clause-product scheme costs 2^{Ω_∆(√n)} on the
preprint's bounded-occurrence formula and on every sparsification leaf. [R]

**Assumptions it needs** (their §9, verbatim labels): (H1) "Polynomial restoration at a point. Each occurrence's
dependence on its own variable is a polynomial in the deformation parameters, equal to 1 at the restoration point."
(H2) "Generic-degree recovery. H(0) is recovered by a rule exact for all polynomials up to the a priori degree bound,
not only for those of the special form (2)." (H3) "Decomposition-priced evaluation." Plus the degree bound deg H ≤ MR
of Def. 5.1(a). Remark 6.3: the lemma "applies verbatim to multi-parameter deformations T ∈ ℚ^d with any recovery set
that determines f(0) for polynomials of total degree at most MR. It fails as soon as the exactness degree falls below
deg G, which is what happens in the parity form." [R]

**What escapes (their own words, §5.1 and §12):** the parity form, because "the product Π_o c_o of own coefficients then
has degree up to MR, far above the degree of exactness" (M = n(log n)^{O(1)} incidences, exactness O(nR)); and D.1,
because tapered Hermite "is not a functional exact for all polynomials of bounded degree, so it violates (b). It also
replaces inclusion–exclusion Taylor data by an expansion in 'mode' variables". Conclusion §12: "whether similar limits
hold for them is the natural next question." [R]

**The analogue of Majdoddin's open door.** Two doors, one inside and one outside the scheme:
* *Inside* (their §9): the bound cannot exceed 2^{Õ(√n)}, "its only constraint is (w+1)s + q ≳ tw, which s = w = q = √n
  satisfies", and "a design on an expander with √n groups, O(√n) interaction width, Taylor order O(√n) and O(1) or
  polylogarithmically many rows per measured group would bring the scheme to 2^{Õ(√n)}". That is e = n^{−1/2}: polynomial
  decay, *without* leaving the clause-product scheme. The only quantitative obstruction they have is the 2×2-minor fact:
  a one-dimensional measured space absorbs two foreign occurrences (e,v), (e′,v′), v ≠ v′, at ≤ 2R points. Counting
  (pair, point) incidences, Q·Σ_h C(f_{t,h}, 2) ≤ 2R·C(M,2) with Σ_h f_{t,h} ≈ M, gives only r ≳ Q/R — no contradiction with
  2^{Õ(√n)}. [R, counting done here] Dimension counting of the linear constraints is uninformative (OpenAI's own rows
  satisfy Q constraints of codimension ≈ n with degree √Q, so the constraints are highly dependent for coordinate-type
  designs). What is known on the negative side is only for OpenAI's template (`parity-barrier.md` Thm 2). This is P2.
* *Outside*: (H1) is violated by any restoration that holds only modulo 2^p (D.1-style), and (H2) by any recovery that
  uses the Boolean-sum-of-products form of H. A "non-product deformation" in the sense of the question — e.g. replacing
  clause inputs by expressions whose own coefficient is not a polynomial equal to 1 at T = 0 (rational, or an element of
  a truncated algebra as in the parity form) — escapes Lemma 6.2 by construction; whether it also escapes the treewidth
  bound is open. [C]

---------------------------------------------------------------------------------------------------

## 3. The three mechanisms side by side

| | Anthropic: signed network sums | OpenAI I: interpolation (main text) | OpenAI II: Theorem D.1 |
|---|---|---|---|
| object decomposed | weighted clique sum on K nodes, S = λ·C(K,2) edge bits; a crossing (two equality tests) is rewritten as Σ of pieces, terms merged by rows/columns, recursion on the merged clique | H(T) = Σ_x Π_e Φ_e(⟨P⃗_{e,v}(T), x⟩), deg ≤ MR; at Q points the sum factors over r groups after fixing ≤ 2τn integer measurements | F(T) = Σ_{X,Y} A(Y)B(X) Π_x l_{Y_x}((W(T)X)_x) on a bipartite one-bit-wire network; at 2-adic nodes it factors over r = 64 groups modulo 2^{p_t} up to mode monomials |
| cost model | time ≥ Σ_terms (size of merged tables) + cost of merged instance; piece cost = log₂ rank across the split ([M] Def. 4.2 (L4)–(L5)) | (2D+1)^{2τn}·2^{2n/r}·C_q per point ([O] Prop. `general-count`); [DL] §5.2: κ(t) ≥ max(2^{s_t}, 2^{w_t}, C(n,q_t), 2^{ρ_t}) | exp(O(√(N p_t)))·(children) per call; leaf 2^H; entries 2^{O(s^{0.9})} |
| source of the √log | ρ = 1/√2 per level with K_{ℓ+1} = K_ℓ²: e = (log K)^{−log₂(1/ρ)}; ρ = f(2h)/(2f(h)), f = log p(E) ≈ c√E (Fock space, Hardy–Ramanujan) | R ≥ √(8Q ln(1/ε)) (binomial tail) with Q ≤ log n/(2 log r) (product label space) | #monomials = exp(O(√(N p_t))), N p_t = Θ(M²/u) (coloured partitions, linear weights), u ≤ log₂ L ≤ 0.9 log₂ s (filtration depth) |
| proved floor | e(K) ≥ 1/log₂ K for every grid algorithm ([M] Thm 4.13); e(K) ≥ (log₂ K)^{−3} for balanced homogeneous two-merge levels ([M] Thm 4.12); ρ ≥ 1/2 for every two-merge identity ([M] Prop. 4.8); ρ ≥ 1/√2 − O(log λ/λ) for graded two-order pieces (`rho-lower-bound.md` Thm 3.2) | template: R ≥ (1−o(1))√(Q ln(1/ε)) for every M₀, and R ≥ cQ/√log n for every label structure (`parity-barrier.md` Thms 1–2, this repo) ⇒ 2^{Θ̃(n/√log n)}; clause-product scheme in the cost model: 2^{Ω(√tw)} ([DL] Thm 8.1), 2^{Ω(√n)} on random 3-CNF ([DL] Thm 8.3) | **none** ([DL] §12: "whether similar limits hold for them is the natural next question"; [M] Remark 4.3: "uses the polynomial method and is not in the class") |
| who proved it | Majdoddin (class); this repo (graded pieces) | this repo (template); Dias–Lima (treewidth, cost model) | — |
| what escapes the floor | configurations meeting ≥ 3 groups of a merge / non-product groupings of terms ([M] §4.8 "the open door"); unconditional bounds beyond c/log K would separate VP from VNP (`engine2-algebraic.md` M6) | the general interface with t-dependent measurement spaces (`parity-barrier.md` §5, [DL] §9); the parity form and D.1 (break deg H ≤ MR or (H2)); inside the scheme, 2^{Õ(√n)} designs on expanders are not excluded | by §2.1–2.4 [C]: only a kernel with superlinear 2-adic invariant growth or a recovery with loss o(MD/u) would help; both look closed for polynomial kernels and Hermite data |

---------------------------------------------------------------------------------------------------

## 4. Proposals (outside Majdoddin's RM class and outside the clause-product scheme unless stated)

### P1. The D.1 cap as a finite 2-adic rank problem (decide the one unproved cap of mechanism (b))

*Mechanism.* D.1 with an arbitrary deformation kernel: W(T) ∈ 𝒪[T]^{L×L}, W(0) = I, W(t) = (unit)·(a permutation pairing
each row slot with a column slot of the same group in coordinate i(t)) at a set of nodes t with prescribed 2-adic
valuations, and W(t + αz) ∈ 𝒪[z] (integrality). The branching at a node modulo 2^p is at least the 2-adic rank (Smith
count below 2^p) of the deformed packet tensor across (group | rest), and the exponent per call is log of the number of
such terms summed over valuation levels with the taper. Outside RM (identity holds only mod 2^{p_t}, pieces are not
rank-costed exact tensors; [M] Remark 4.3) and outside clause-product ((H1), (H2) fail; [DL] §5.1).

*Smallest instance.* One packet, L = 16 (done, §2.4) and L = 32 slots (a = 5), r = 2 groups via one label bit, nodes
t = 1, 2, 4, 8, 16, ζ ∈ {1, 3}, precision p ≤ 40. For L = 32 the full flattening is 2^{32} × 2^{16}; restrict to a
sub-packet of 4–6 row slots of the group (2^{8..12} × 2^{16} entries, 16–256 M, feasible with the int64 mod-2^30 elimination
of `smith_tensor.py`, or exactly with p-adic Smith over ℤ/2^60 in Python ints on a 2^8 × 2^16 slice).

*What to compute.* (i) For the Cauchy kernel: the Smith valuations of the crossing blocks and of the tensor flattenings;
fit #invariants(val ≤ w) against w (linear ⇒ exp(√(Np)) is tight) and the tensor count against the monomial count.
(ii) Then the optimisation: over kernels W(T) = Cauchy(T) + 𝒞(T)G(T) with G ∈ (2^{−k}𝒪)[T]^{L×L} for small k (controlled
denominators, so that integrality near nodes still holds mod 2^{p−k}), and over node sets S′ ⊂ ℤ that are not complete
residue systems, maximise the minimal valuation growth of the crossing-block invariants. (iii) The lower-bound side:
prove that for every integral polynomial kernel with W(0) = I and W(t) local at nodes of valuations 0..a−1 the crossing
block at t + αζ has ≥ c·(L/2^i)·w invariants of valuation ≤ w. That statement would be the D.1 analogue of ρ ≥ 1/2 and
would close mechanism (b) at e = Θ(1/√log s) for every kernel; by §2.3 (c) I expect it to hold [C].

*Evidence of a gain.* A kernel or node set whose crossing-block invariants have #{val ≤ w} = O(w^{1−δ}·L/2^i) uniformly
in i (then the coloured-partition count becomes exp(O((Np)^{1/(2+δ)}))·…, and the exponent per call M/u^{(1+δ)/2}), or a
tensor 2-adic rank growing polynomially in p while the monomial count grows like exp(c√p). Negative evidence (expected):
both counts stay within a constant factor at L = 32 as at L = 16.

### P2. The general interface on expanders: a clause-product design with 2^{Õ(√n)} cost (the Dias–Lima gap)

*Mechanism.* OpenAI's Definition `def:layout` / [DL] Def. 5.1 with **t-dependent measurement subspaces R_{t,h} that are not
the restriction of one T-polynomial measurement part** — the part `parity-barrier.md` §5 shows is strictly stronger than
the template and for which no lower bound exists. Target parameters (from [DL] §9): r ≈ √n groups of size s ≈ √n,
interaction width w = O(√n), Taylor order q = O(√n) (so R/Q ≈ n^{−1/2}), ρ_{t,h} = O(1) rows per measured group of height
2^{o(√n)}; cost 2^{Õ(√n)}. Status: inside [DL]'s scheme but **not excluded** by Thm 8.1 (their bound is ≤ 2^{Õ(√tw)}); outside
OpenAI's template (so `parity-barrier.md` Thms 1–2 do not apply); outside RM. Polynomial decay e = n^{−1/2} per variable
would beat the dense wall for every problem with an O(n)-bit local witness (Held–Karp, Ryser via the sparse encodings of
`ambitious-targets.md` §2.2 need only e = o(1/log n)).

*Smallest instance.* Bounded-occurrence 3-CNF on n = 16, 20, 24 variables with Pr(F) a 3- or 4-regular expander-like graph
(random cubic graph with girth ≥ 4, or the Tovey copy of a random 3-CNF at density 4.26 on 6–8 original variables); Q = 4,
6, 8 points; r = 4 groups of size n/4 (partitions and assignments chosen at random per point, then by local search).
Unknowns: the coefficient vectors c_1..c_R of P_o(T) = e_v + Σ_k T^k c_k for the M ≈ 3n occurrences; constraints: for every
t and every h ≠ α_t(e), P_o(t)|_{S_{t,h}} ∈ R_{t,h}. For *fixed* subspaces R_{t,h} this is a linear system over ℚ, so the
search is over the subspaces: candidates of height ≤ 2 (group sums Σ_{v∈S_{t,h}} x_v, signed sums, pairs), ρ_{t,h} ≤ 2.

*What to compute.* min R such that the linear system is feasible, as a function of (n, Q, r, ρ); compare with the template
bound R ≥ cQ/√log n (`parity-barrier.md` Thm 2) and with OpenAI's R ≈ √(8Q ln(6r²λ)). Also the measurement heights that
appear (the design is useless if a row's range is 2^{Θ(n)}: "A single integer linear form, such as Σ 2^{i−1}x_i, can
encode the entire Boolean assignment", [K] §2.2).

*Evidence of a gain.* Feasible designs with R ≤ Q/4 at Q = 8 and ρ_{t,h} ≤ 2, heights O(n), on the expander instances, with
R/Q not increasing from n = 16 to n = 24 at fixed Q/√n. Evidence against: infeasibility at R < Q(1 − 1/r) − O(1) whenever
ρ_{t,h} ≤ 2 for every expander instance tried (that would suggest the 2×2-minor obstruction of [DL] §9 generalises to
"measurements cannot absorb the cut", which is their open lower-bound direction).

### P3. 2-adic mode decompositions as hyperedge pieces (Majdoddin's open door with OpenAI's tool)

*Mechanism.* [M] §4.8: polynomial decay of e(K) inside signed network sums needs "pieces whose configurations meet three
or more groups of a merge (equivalently, non-product groupings of terms)", and "no current tool decides" their
realisability. D.1's recursion identity F(t+αζ) = Σ_β Π_{g=1}^{r} Z_{g,β} mod 2^{p_t} *is* a decomposition of the deformed
clique sum into exp(O(M/√u)) terms each of which is a product over all r = 64 groups at once — a rank-one decomposition
across an r-way split, valid modulo 2^{p_t} at a node, with exp(O(M/√u)) ≪ 2^{Θ(M)} terms (the flattening floor for the
undeformed network). As a piece family for Majdoddin's model it is a hyperedge configuration (every packet meets all
groups), costed not by rank but by 2-adic rank at precision p_t, and paid for by the tapered recovery. The question is
whether such pieces can be *combined* with a tower: use D.1's node-local decomposition as the "identity" of one level of
Anthropic's recursion on a 3-merge design (three pairwise orthogonal partitions), so that the per-level factor ρ is
replaced by a 2-adic count.

*Smallest instance.* [M]'s own: the K₄ clique sum (two merges = the three perfect matchings of K₄; input floor N³;
best known N^{23/6} at ω = 2, N^{3.93} on the current curve, N⁴ for every rank-one method and contraction tree, [M] Thm 2.7,
Cor. 2.8), and AG(2,4)'s translation matching with three other parallel classes as merges ([M] §4.8). Deform the K₄
network's equality tests by the Cauchy kernel on a packet of L = 2^a slots per edge (λ = a bits per edge string), take the
three matchings as the three label coordinates, and compute at each node the 2-adic rank of the deformed network across
each of the three 2|2 splits (and the 4-way split).

*What to compute / evidence.* For λ = 4, 5 (N = 16, 32) and p ≤ 40: the number of terms needed modulo 2^p across the
4-way split at the nodes, summed with the taper, against N^{23/6}·poly and against the rank-one floor N⁴. A gain is a
total term count below N⁴ at some λ with the recovery accounted for; this would be the first non-rank piece family for
the K₄ window ([M] Open problem 1). Honest expectation: the deformation/recovery overhead (constants 10^4 in [DL] E5)
swamps N⁴ at every λ one can compute, so the test must be done on the *rate* (slope of log(terms) in λ) rather than on
absolute counts. [C]

### P4 (negative, for the record). Towers do not rescue D.1

Any recursion whose root step costs e(s)·s with e(s) ≥ c/√log s has exponent ≥ c·s/√log s whatever happens below the
root. D.1's root is such a step (§2.1 (e)–(f)); Anthropic's first level costs e_0·S with e_0 ≤ 1/2 only, but every later
level pays ρ ≥ 1/√2 ([M] Prop. 4.8; `rho-lower-bound.md`). So neither "D.1 at the root, Anthropic below" nor "Anthropic at
the root, D.1 below" changes the type of decay. [R]

---------------------------------------------------------------------------------------------------

## 5. Precise open statements

* **(O1) [C, for P1]** For every L = 2^a, every node set S ⊂ ℤ of size 2L with the complete-residue property, every
  W(T) ∈ 𝒪[T]^{L×L} with W(0) = I, W(t) ∝ shift_t for t ∈ S\{0}, and W(t+αz) ∈ 𝒪[z]: the crossing block of W(t + αζ)
  (ζ a unit) at a node of valuation i has at least ⌊L/2^{i+1}⌋·⌊w/4⌋ invariant factors of valuation ≤ a+1−i+w, for every
  w. Verified for the Cauchy kernel at L ≤ 16 [N]; if true for all kernels, D.1's architecture has e ≥ c/√log s.
* **(O2) [C, for P2]** For bounded-occurrence formulas with tw(Pr F) ≥ cn, every design in Definition `def:layout`
  (t-dependent measurement spaces allowed) with ρ_{t,h} ≤ ρ₀ rows of height ≤ 2^{o(n)} per group has R ≥ Q/polylog(n).
  Known: for OpenAI's template R ≥ cQ/√log n (`parity-barrier.md` Thm 2); for the general interface only the 2×2-minor
  bound ([DL] §9), which gives r ≳ Q/R and nothing more.
* **(O3) [C]** Dias–Lima's conclusion (2^{Ω(√tw)}) for the parity form and for D.1. Their Remark 6.3 says the vanishing
  lemma needs exactness up to deg G; for the parity form deg G ≈ MR ≫ exactness degree O(nR). A replacement for
  Lemma 6.2 would have to use the truncation structure (the V-grading) instead of degree.

## Scripts

* `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/engine3/smith_kernel.py a` — Cauchy kernel
  at T = t + αζ for L = 2^a, exact Smith valuations of the crossing blocks (sympy over ℤ). Run: a = 3, 4.
* `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/engine3/smith_tensor.py a i` — flattening of
  the deformed packet factor Π_{x∈g} l_{Y_x}((W(T)X)_x) across (group | crossing columns), 2-adic Smith elimination mod
  2^30 in numpy int64, compared with the mode-monomial count and brute force. Run: (a, i) = (4, 0), (4, 1), (4, 2);
  output in `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/tasks/b3drvdf0r.output`.
  Note: W(t) for t ≠ 0 equals (𝒞′(t)/𝒞′(0))·shift_t, a unit multiple of the permutation, not the permutation itself
  (the script's last line prints `False` for an equality test that expected the bare permutation; harmless).
