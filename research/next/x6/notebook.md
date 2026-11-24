# x6 notebook: a kernel in the target region ρ < 1/√2?

24 Nov 2026. Tags: [R] proved here, [N] computed, [C] conjecture, [K] known/cited. Code in `code/`, outputs `*.out`.
Inputs read: x5 notebook (all), x3 §1–4, x4 §1, §4, b2 §0–3, VP paper App. B (B.1–B.4).

(Work in progress — sections are filled in as they are done.)

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

TODO

## 4. Verdict

TODO
