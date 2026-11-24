# x6 notebook: a kernel in the target region ρ < 1/√2?

24 Nov 2026. Tags: [R] proved here, [N] computed, [C] conjecture, [K] known/cited. Code in `code/`, outputs `*.out`.
Inputs read: x5 notebook (all), x3 §1–4, x4 §1, §4, b2 §0–3, VP paper App. B (B.1–B.4).



## 1. Re-derivation of the (α, β) region (Task 1)

**Where Prop. B.2 uses the degree [K, re-read].**
- The reflection identity X^Θ Ψ(1/X; a,b,c,d) = Ψ(X; a,d,c,b) does two jobs at once:
  - it gives deg Ψ ≤ Θ, so there are Θ+1 pieces, ln(Θ+1) = o(λ), and Σ_N Ψ_N = Ψ(1);
  - it gives (c) from (b): the ab|cd bound of Ψ_N is the ad|bc bound of Ψ_{Θ−N}, i.e. (Θ−N+1)P(Θ−N).
- **Reflection degree** := the total X-exponent of the monomial row/column multipliers that turn M(1/X) into M with b↔d.
  In the paper these are X^{2i+1} on the rows and columns of a and c, (y−1)y^i at d and y^{i+1} at b. They total
  e_a + e_c + (e_2 − 2n_2) + (e_2 + 2n_2) = 2(e_1+e_2) = Θ, which is the sum of the four party energies.
- Θ enters the price inequality only in B.3's proof: r² = (Θ−N)/n_0 and r′² = N/n_0, so r² + r′² = Θ/n_0. **Θ is the
  squared radius of the B.3 disc.** That is the exact place where "degree = total energy" becomes the √2.

**Why a–c forces "multipliers = energies" [R, small lemma].** The a–c block of M is diag(X^{ε(i)}) (it is the a–c block of
F·D·G, with unit rows of F for a and unit columns of G for c). The reflection fixes a and c. A monomial multiplier X^{h_a(i)}
on row i of a and X^{h_c(j)} on column j of c maps X^{−ε(i)} to X^{ε(i)} only if h_a(i) + h_c(i) = 2ε(i). Summed over the
matched symbols, a and c contribute exactly e_a + e_c to Θ. The same holds for b and d. So **in the paper's template
(party levels = bond levels, monomial reflection), β = 4 is forced**, not just observed.

**The two inequalities (own words).** Suppose the wires are classes with ln Q = λ, the bond count is F(N) = ln P(N),
rk_{ad|bc}Ψ_N ≤ poly·e^{F(N)}, rk_{ab|cd}Ψ_N ≤ poly·e^{F(Θ−N)}, Θ = βE, and λ ≤ F(E).
- *Flattening.* Σ_N rk_{ad|bc}Ψ_N ≥ rk_{ad|bc}(crossing) = Q². So e^{F(Θ)}·poly ≥ Q², i.e. F(Θ) ≥ 2λ − o(λ). For F = κx^α this
  is β^α ≥ 2.
- *Middle piece.* ρ_cert ≥ [F(Θ/2) + F(Θ/2)]/(4λ).
  - Using λ ≤ F(E): ρ_cert ≥ F(βE/2)/(2F(E)) = (β/2)^α/2.
  - Using 2λ ≤ F(Θ): ρ_cert ≥ F(Θ/2)/F(Θ) = 2^{−α}.
- *Region.* ρ_cert < 1/√2 needs (β/2)^α < √2, i.e. β < 2^{1+1/(2α)}, and 2^{−α} < 1/√2, i.e. α > 1/2. Flattening adds
  β ≥ 2^{1/α}. The interval is nonempty iff 1/α < 1 + 1/(2α), i.e. iff α > 1/2. This agrees with x5 §3b.

**Check on x5's d = 2 oscillator [N] (`code/ladder.py`, `ladder.out`).**
- Formula: α = 2/3 and β = 4 give max(2^{−2/3}, 2^{2/3}/2) = max(0.630, 0.794) = 0.794 = 2^{−1/3}. Flattening holds:
  4^{2/3} = 2.52 ≥ 2.
- Exact counts (symbols over the 2D levels, Θ = 4E): ρ_cert = 0.815, 0.804, 0.800 at E = 50, 150, 300, tending to 0.794.
  F(4E)/2F(E) = 1.32 → 1.26 = 4^{2/3}/2.
- x5's exact d = 2 identity at e = 8 (Q = 10, Θ = 32) has full-rank pieces at this size, so it carries no asymptotic
  information. The exponent check is the counting above.

## 2. Reduction: every identity is a chain of two-term splittings [R]

Let C = ⟨Q⟩_{ac}⟨Q⟩_{bd} and λ = ln Q. For t ∈ [0, 2] define the **two-term trade-off**

  σ(t) := lim inf_Q (1/λ)·ln min{ rk_{ab|cd}(L) : C = R + L, rk_{ad|bc}(R) ≤ Q^{t+o(1)} }.

**Proposition 1.** ρ_× = (1/4)·sup_{t∈[0,2]} (t + σ(t)). Here ρ_× is the crossing exponent of x5 §1: the inf over families
with 2^{o(λ)} pieces of max_i (c_{ad|bc} + c_{ab|cd})/(4λ).

*Proof.*
- (≥) Take any family Σ_{i≤T} Ψ_i = C with costs (c_i, c′_i) (log-ranks over λ) and T = Q^{o(1)}, and any t.
  - Put R = Σ_{c_i ≤ t} Ψ_i and L = the rest. Then rk(R) ≤ T·Q^t, and rk_{ab|cd}(L) ≤ T·Q^{max_{c_i>t} c′_i}.
  - Every piece with c_i > t has c′_i ≤ 4ρ − c_i < 4ρ − t. So σ(t) ≤ 4ρ − t.
- (≤) Choose splittings C = R_k + L_k at t_k = 2k/K, k = 0..K, with R_0 = 0 and L_K = 0.
  - Set Ψ_k := R_k − R_{k−1} = L_{k−1} − L_k. These telescope to C.
  - Then c(Ψ_k) ≤ t_k + o(1) and c′(Ψ_k) ≤ σ(t_{k−1}) + o(1). So 4ρ ≤ sup_t (t + σ(t)) + 2/K.
  - Let K → ∞ slowly. ∎

**Consequences.**
1. **The degree budget is a gauge.** Any identity can be regraded: the grading is just the index k of the chain. So "β < 4"
   has no intrinsic meaning. The intrinsic object is the curve σ, and the (α, β) language describes the special curve
   σ(t) = (β − t^{1/α})^α (units λ = E = 1). The paper's curve is the circle σ = √(4 − t²). Flattening and x3's Lemma′
   (rk·opSR ≥ Q²/4) give σ(t) ≥ 2 − t, i.e. ρ ≥ 1/2. Under PH (b2), sup(t + σ) ≥ 2√2.
   - So mechanism (b), "cancellation in the sum", is not a separate mechanism. It is exactly the freedom to choose the
     splittings R_k independently. Only σ matters.
2. **Balanced form of the target.** Let τ := inf{t : σ(t) ≤ t}. Then ρ_× < 1/√2 implies τ < √2.
   - Conversely, a *single* splitting C = R + L with both ranks ≤ Q^{τ}, τ < √2, already satisfies x5's D = 2 criterion
     max_a g(min(ℓ_row, ℓ_col)) + 2·log₂A < 2√2·m: here A = 2, g(τm) < g(√2m) = 2√2m, and g is increasing on [0, √2m].
   - So the smallest object that would prove contracting via two-proofs Prop. 1 is: **SWAP_Q = R + L with rank(R) and
     opSR(L) both ≤ Q^{√2−δ}**. Under FH it cannot exist (b2's flat floor: some piece has min(c_row, c_col) ≥ √2λ).
3. **x3's conjecture min max(r,s) = ⌈n²/4⌉ is false asymptotically [R].** The paper's identity, cut at K = Θ/2, gives
   max(r, s) ≤ n^{√2+o(1)}. The crossover is around n ≈ 11 (n^{√2} < n²/4 iff n > 4^{1/(2−√2)} ≈ 10.7), which is above
   x3's tested range n ≤ 5. So that conjecture should not be used as evidence.

[N] Partial sums of the paper's own pieces (`code/partial.py`, `partial_*.out`): over ℚ, rk_{ad|bc}(Σ_{N≤K}Ψ_N) equals
rk_{ad|bc}(Ψ_K) (1, 3, 7, 13, 21, … for (1,10)). So the ranks do not add up, but they do not cancel below the top piece
either. Results at larger classes are in §3(b).

## 3. Mechanisms

### 3.0 The common obstruction: the ladder theorem [R]

**Scaling lemma.** Let N(ε) be the number of single-particle levels of energy ≤ ε. Let ln Z(β) = ∫ ℓ(βε) dN(ε), with
ℓ(x) = 2 ln(1 + e^{−x}) for the fermion pair (I, J) (or −2 ln(1 − e^{−x}) for bosons), and Ŝ(E) = inf_β [βE + ln Z(β)].
If N(ε)/ε is non-decreasing, then **Ŝ(sE) ≥ √s·Ŝ(E) for all s ≥ 1.**

*Proof.*
1. Integrating by parts, ln Z(β/s) = ∫ N(su)·β|ℓ′(βu)| du ≥ s·∫ N(u)·β|ℓ′(βu)| du = s·ln Z(β).
2. Substitute β → β/√s in the infimum: Ŝ(sE) = inf_β [√s·βE + ln Z(β/√s)] ≥ √s·inf_β [βE + ln Z(β)]. ∎

The symbol count satisfies F(E) = ln P(E) ≤ Ŝ(E) exactly (Chernoff), and F = Ŝ·(1 − o(1)) asymptotically. So
**F(2E) ≥ √2·F(E)·(1 − o(1)).**

**Theorem (class T).** Take a Prop.-B.2-type identity with the following properties:
- (T1) party levels are bond levels, i.e. unit rows of F for a and unit columns of G for c;
- (T2) a monomial reflection fixes a and c;
- (T3) piece ranks are bounded by the symbol count P of the bond spectrum;
- (T4) the bond spectrum has N(ε)/ε non-decreasing.

Then ρ_cert ≥ 1/√2 − o(1).

*Proof.* By the a–c lemma of §1, (T1) and (T2) force Θ = e_a + e_b + e_c + e_d = 4E. Party classes give λ ≤ F(E). So
ρ_cert ≥ 2F(2E)/(4λ) ≥ F(2E)/(2F(E)) ≥ 1/√2 − o(1). ∎

**(T4) is automatic for ladder-closed kernels [R].**
- In the template, the d–b block congruence for all truncations R is the power-series identity
  (1 − X²)·Σ_r X^{ε(r)} B(r,i) B(r,j) = δ_{ij} X^{ε(i)}.
- Its right side divided by (1 − X²) has a pole at X = 1, so the bond spectrum is infinite.
- With a constant ground column B(r,0) = 1 (the paper; any flavour-diagonal sum), the case i = j = 0 reads
  Σ_r X^{ε(r)} = X^{ε_0}/(1 − X²). So the levels coupled to a ground mode form exactly one ladder ε_0, ε_0+2, ….
- A union of ladders with offsets o_f has N(ε)/ε = Σ_f (1 − o_f/ε)/2 + O(1/ε), which is non-decreasing.

The class covers the paper, flavours, offsets, x5's d-dimensional product kernels (whose energy multiset is a union of
ladders), and su(1,1) discrete-series / Schur–Cauchy free-fermion constructions.

**Numerics [N] (`ladder.out`).** Exact symbol counts, Θ = 4E, λ = F(E) (this choice favours the target):

| spectrum | R2 = F(2E)/F(E), E = 300 | ρ_cert |
|---|---|---|
| one ladder (the paper) | 1.446 | 0.723 → 0.707 |
| 5 flavours | 1.430 | 0.715 |
| 2D oscillator | 1.600 | 0.800 |
| offsets k² / 2^k / random | 1.53 / 1.53 / 1.62 | 0.76 / 0.76 / 0.81 |

All R2 > √2.

**Sharpness in counting.** With (T4) dropped, and the template kept only as a counting device, two-band spectra pass
flattening and do better. Example: 8 modes at energy 3 plus 128 at energy 90, E = 120. This gives F(4E)/2F(E) = 1.03 and
**ρ_cert = 0.652**; several other band spectra reach 0.65–0.69. But the pole/ground-column lemma forbids such spectra in
the template. So (T4) is the binding hypothesis besides β = 4.

**Answer to the lead's question on (b) cancellation.** The certified bound uses the coefficients of the **sum**, Ψ_N = [X^N]Ψ.
Their ad|bc bound comes from the Schur-complement truncation at order N. Their ab|cd bound comes from the reflection,
which needs the sum's degree Θ.
- If Ψ = Σ_j Ψ^{(j)} with deg Ψ^{(j)} > Θ, and the top parts cancel, the identity's pieces are still the coefficients of the
  total. Only the total's reflection degree enters. So a cancellation is "free" only if it also lowers the reflection
  degree of the total.
- In the template that degree is fixed by the a–c lemma: Θ = Σ party energies, whatever the decomposition.
- More fundamentally, by Prop. 1 the degree is a gauge. What any decomposition must deliver is pairs (rk_{ad|bc} A_K,
  rk_{ab|cd} B_K) below the circle, and a cancellation in a sum is exactly a choice of splitting.

### 3.1 Mechanism by mechanism

| # | mechanism | what was checked | killing inequality | status |
|---|---|---|---|---|
| a | non-product determinants / Pfaffians, Schur and dual Cauchy, plane-partition counts | MacMahon = 2D bosonic ladder; Schur–Cauchy and BdG Pfaffians = free-fermion ladder kernels; finitely many variables gives a polynomial count | class T: F(2E) ≥ √2F(E) and Θ = 4E ⇒ ρ ≥ 1/√2 (2D: 0.794). Finite-variable Schur: α = 0, so flattening F(4E) ≥ 2F(E) fails | killed in T [R] |
| b | cancellation of top degrees | exact partial sums A_K, B_K (below) | the pieces are the sum's coefficients; the degree is a gauge (Prop. 1); only σ(t) matters | not a separate mechanism [R] |
| c | two commuting gradings | (i) reflection in X only: the Y-information crosses both cuts in full. With F(N₁,N₂) ≈ κ(N₁N₂)^{1/3}, the middle piece costs 2F(2E,4E) = 4λ, so ρ = 1. (ii) reflection in both: F(N₁,N₂) is concave (a sup-convolution of entropies), so the worst piece is the centre and ρ = 2^{2/3}/2 = 0.794. (iii) X controls ad|bc and Y controls ab|cd independently: the corner piece (Θ_X, Θ_Y) is full in both, ρ = 1, unless the support is anticorrelated, which is a one-parameter chain again | concavity / corner piece | killed [R, asymptotic counting] |
| d | q-deformation, roots of unity | X^K = 1 is folding: the folded piece j contains Ψ_N for N ≡ j, so its bounds are ≥ F(max N) and ≥ F(Θ − min N). For K = o(Θ) this gives ρ ≥ F(Θ)/(2λ) ≥ 1. Folding is a coarsening of the chain and cannot lower sup(t+σ). A q independent of X leaves the X-spectrum, hence (T4) and Θ, unchanged | Prop. 1 plus class T | killed [R] |
| e | characteristic p | reducing existing pieces mod p (below; z1: the Fock identity vanishes mod q ≤ h). A Frobenius-linear kernel where degree p^k costs k makes the energy logarithmic, i.e. the spectrum much denser (N(ε)/ε increasing). Under the template's Θ = 4E that is the losing direction: ρ ≥ 2^{α−1} → 1 | class T with β = 4 | killed as a regrading. A genuinely char-p identity with sub-additive reflection degree (Moore/Dickson type) is not constructed: open [C] |

**[N] Exact partial sums (mechanism b).**
- Class (1,10) at d = 1 (Q = 5), and (1,8) at d = 2 (Q = 10, Θ = 32).
  - Over ℚ the partial sums do **not** beat the per-piece ranks, apart from a small drop at d = 2, K = 14:
    rk A_14 = 66 < rk Ψ_14 = 72 and rk B_14 = 69 < 96.
  - The best balanced split has max rank Q^{1.84} at d = 2 and Q^{1.98} at d = 1. Both are saturated sizes.
  - Over F_2 and F_5 the balanced split drops to Q^{1.65–1.68} at d = 2 and Q^{1.43} at d = 1 (F_5).
  - These are finite-size numbers. All of them are above x3's Lemma′ floor rk·opSR ≥ Q²/4 and carry no asymptotic weight.
- The class (2,14) at d = 1 (Q = 8) did not finish in the time box.

## 4. Verdict

- **No kernel in the target region was found.** Nothing proves contracting.
- **[R] Prop. 1 (§2).** ρ_× = ¼·sup_t (t + σ(t)), where σ is the two-term trade-off for C = R + L. Consequences:
  - the degree budget β is a gauge;
  - cancellation is not a mechanism;
  - the minimal sufficient object for contracting (D = 2, x3 vocabulary) is one splitting **SWAP_Q = R + L with rank(R),
    opSR(L) ≤ Q^{√2−δ}**. That is bond < √2·m with A = 2. A ρ_× < 1/√2 family gives exponent α′ = log₂(1/ρ) > 1/2 for
    #3-SAT;
  - x3's ⌈n²/4⌉ conjecture is false asymptotically (the paper gives n^{√2+o(1)}).
- **[R] Candidate theorem, proved for class T.** In the B.2 template:
  - the a–c block forces Θ = Σ party energies (β = 4);
  - the Gram pole at X = 1 with a ground column forces ladder-closed spectra, so N(ε)/ε is non-decreasing;
  - these two facts give F(2E) ≥ √2·F(E), hence ρ_cert ≥ 1/√2.
- **Sharpness.** In pure counting, (T4) is the binding hypothesis: two-band spectra give ρ_cert ≈ 0.65.
- **Where an escape must come from.** It must break T1/T2 (a non-reflection mechanism for the ab|cd bound) or T4 (a template
  without the (y−1)-pole, finite bands). Under FH both are impossible, so either would refute PH.
