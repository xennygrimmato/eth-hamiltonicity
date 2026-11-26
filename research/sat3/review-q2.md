# Referee report on `q2-notes.md` (Theorem T and its by-products)

Adversarial review, 26 Nov 2026. Nothing here is committed or machine-checked. Tags: **[K]** quoted, with location;
**[R]** proved or re-proved here in full; **[D]** derived here, unreviewed; **[N]** numerical (script named);
**[C]** conjecture or open; **[X]** wrong or dead.

Sources (relative to the session scratchpad). HC = `survey/oa/preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-…/paper.txt`;
IM = `…/The-logarithmic-exponent-of-integer-multiplication-on-tapes-…/paper.txt`; EG = `…/Euclidean-geometry-in-the-asymptotic-spectrum-…/paper.txt`;
OA Lean = `survey/oa/lean` (read, not built); AN-ETH = `pb/aneth/paper.txt`. Line numbers are those of these text files.
All of HC, IM, EG and AN-ETH are machine-generated and unrefereed.

My scripts are in `scratchpad/refQ2/`. I wrote them from the statements and did not reuse the note's scripts:
- `star_lemma.py`: Lemma S by explicit contraction, plus the gate count of Lemma L;
- `lemmaN_E2_E3.py`: Lemma N (random and adversarial tests, plus the K = 2 counterexample), E2 and E3;
- `k3_trace.py`: the K = 3 normalisation;
- `lemma22.py`: HC Lemma 2.2's constant.

---

## Summary

| item | verdict |
|---|---|
| 7. Trust in HC Thm 3.1 itself | **The only real risk.** I found no break in the three load-bearing steps. The arithmetic of each closes, and the simple obstructions I tried fail. One harmless typo. Unformalised (OA's own docs say so). |
| 4. Is the engine an arithmetic circuit for f_{K,λ}; regime; "α > 1/2" | **Correct for AN-ETH's engine; gap in the stated class.** "Oblivious algebraic" must be defined as "straight-line program whose output is f_{K,λ} as a polynomial identity". The char-p sentence of Cor. T2 has no source. |
| 1. Does HC Thm 3.1 say what is used; is "ports" one notion | **Correct.** HC, IM and EG use the same notion (equivalent up to pigeonhole on degrees). The chain composes with no parameter loss. The second half (ports ⇒ power-saving 3-SAT) even has a Lean counterpart in OA's release. |
| 2. Is f_{K,λ} = f_{T_K(λ)}; Lemma L; gate costs; non-vacuity | **Correct.** AN-ETH Def. 3 has one table per node, not per pair. |
| 3. Lemma S and the bookkeeping | **Correct**, verified exactly by my own contraction. |
| 5. Sanity against known upper bounds | **No contradiction.** The K = 3 normalisation gives e = ω/9 (1/4 with ω = 9/4), but Theorem T says nothing about fixed small K. |
| 6. Lemma N, E2, E3 | **Correct, with one repair:** Lemma N needs K ≥ 4, and it is false at K = 2. |

---

## Item 7 (weakest): how much of HC Thm 3.1 can be trusted

**What is formalised [K].** `lean/docs/379.md`, section "Hamiltonian cycle and the permanent": "Lean proves that for every
exponent C and characteristic q, there is a common threshold beyond which directed Hamiltonian cycle requires more than
N^C exact arithmetic gates … The paper's stronger exp(c(log N)²/(log log N)²) lower bound for circuits approximating
only the degree-N coefficients of these polynomials remains unformalized." Thm 3.1 is the source of that stronger bound,
so its quantitative content (the rate d/√log d, the explicit T_d, the grouped powers) is outside the formalised scope.
The note's §1.6 is accurate.

**The proof skeleton (HC l. 594–655) checks out [R, arithmetic only].**
- I recomputed (3.3) → (3.4) → (3.5).
- With τ = η/(d√m), the cone law r_i = 1 − τ⟨x_i,Z⟩ + O(τ²d) holds. Together with F′(1) ≥ cw, |F″| ≤ Cw and (3.1), it gives the linear saving c·c₀·η·w/m and the error O(η²w/m).
- Summing the 2^d terms costs D_x·d·log 2 = O(d√m). HC Lemma 2.2's constant checks out: `lemma22.py` gives a bound/exact ratio of 0.90–0.97 for n = 16…4096 orthonormal sites, so the constant is sharp to leading order, as claimed.
- The target deficit is O(hd).
- With w = ⌈a d m^{3/2}⌉ we have c₁hw/m = c₁·a·h·d·√m, which absorbs O(hd) + O(d√m) for every h ≥ 1. Dividing by τ gives log s ≳ (c₁a/η)·h·d²·m = c·h·d·w/√m.
- So the theorem follows from three inputs: (3.1), (3.2) and the Lemma 3.3 decomposition.

**Load-bearing step A: the saving c₀d/√m for all balanced cuts at once (Thm 7.1, via Lemma 7.2, §7.3).**
- The 1/√m comes from one inequality, HC l. 1813–1815: "c₁√S ≤ 2J√log(1/δ) Σ_a √r_a + √(δS) + …", with Σ_a √r_a ≤ Cm√r and S = rm.
- The batch lengths decay geometrically with ratio 1 − (1/2+δ)/m (l. 1614), so P = O_δ(m) and Σ√r_a ≈ 4m√r. [R]
- The L² triangle inequality (Minkowski) adds the P replacement lengths linearly. Hence J ≥ c₁/(2C√(m log(1/δ))), with δ absolute. I checked this arithmetic.
- The loss from adding lengths linearly, rather than as √(Σ r_a) = √(2S), is exactly the factor √m. The note's Cor. T4 argues, conditionally on AN-ETH, that this loss cannot be avoided.
- Not verified: (i) Lemma 7.3, which rests on Thm 5.1 and hence on the whole of §§4–6; (ii) the claim that the averages "are precisely a test for J" (l. 1800–1806). J is defined as a supremum over placements, and the argument needs the inner configuration to satisfy Lemma 7.2's distance bounds after rescaling by 1/√log(1/δ). It is plausible, but I did not check it line by line.
- I found no small counterexample. The obvious caps are consistent with the claimed rate:
  - Euclidean cap O(√d): HC l. 166 and the note's E2;
  - pod and tree placements, which save nothing or are negative for most cuts;
  - the trivial cap Σ_i⟨x_i, Z_{b(i)}⟩ ≤ |B|·d(Z₀, Z₁)·(Lipschitz bound), barycentre at the tip.

**Load-bearing step B: the near-star witness (Thm 8.1 → Thm 11.2), deficit O(d) per copy.**
- [K, HC l. 1930–1937] Thm 8.1: "0 ≤ Σ_i A(1,θ_i) − λ(C; y, θ) ≤ C₀ M (1 + N/q²) log N".
- The use in Thm 11.2 (l. 2819–2822): with b = m³ copies per batch, M = 500m, q = ⌈w/m²⌉, N = n = dq, the deficit per batch is b·C₀M(1 + d/q)·log n.
  - w ≥ dm gives d/q ≤ m, and log n = O(m). So the deficit is O(m⁶) = o(d). [R]
  - M ≥ 100 log N holds because 100·ln(dq) ≤ 300 ln d ≈ 208m < 500m. [R]
  - F′(1) = Θ(w): there are Ω(q/M) slots with |θ_j| ≤ 1, and b·q/M = w/500. [R]
- Typo (harmless). The displayed inequality before l. 2819 reads "b λ(C_V) − d Σ_j max(θ_j, 0) ≤ B_x(U) + d log 2". The shift in (11.7) sums over the b copies as well, so the subtracted term must be b·d·Σ_j max(θ_j, 0). With that correction the left side equals d·F(1) − O(m⁶) by (11.8), since log(1 + e^θ) − max(θ, 0) = log(1 + e^{−|θ|}).
- Other costs are fine:
  - the sign correction costs d log 2 per batch, which is O(d);
  - the alphabet compression costs O(m^{3/2}) + O(d), and w ≥ dm absorbs it.
- A stress test that could have broken it. I tried a two-supplier network for the exterior tensor itself: Laplace expansion of det C_I across a row cut, with the shared index S ⊂ [b], at most 2^{N/2} values.
  - Its wire costs τ·(N/2)·log 2 per copy.
  - Its first-order transport saving is τ·(q/M)·Σ_i⟨x_i, Z_{b(i)}⟩ ≤ τ·(q/M)·c·d/√m.
  - Ratio saving/cost = O(1/(M√m)) ≪ 1, so this network does not undercut the near-star bound. No contradiction.
- I did not verify §§9–10 (flags, threshold ranks, the second-moment estimate), which prove Thm 8.1.
- One point to keep in mind [C]: Thm 8.1 and 11.2 are stated for every Hadamard cone with homogeneous prices, Euclidean flats included. In a Euclidean flat, a hyperplane-average heuristic for prices of non-diagonal tensors would suggest a deficit of order log q per row, not O(1). But that average is not a spectral point (EG §1.1 says so explicitly), so the heuristic proves nothing. The cleanest independent test of HC is Thm 8.1 in a Euclidean flat at simplex sites. I could not carry it out.

**Load-bearing step C: Lemma 3.3 and the closure [K + R].** The balanced-gate argument is standard. I re-read it (l. 516–532) and agree with the note. "Applying the local maps … preserves this conclusion" (l. 596–598) is correct: legwise linear maps do not raise any cut rank, and they are Zariski-continuous.

**Verdict on item 7.** No error found. The theorem rests on Thm 5.1, Thm 6.1 (the product-closed subclass M), Lemma 7.3 and §§9–10, none of which I verified. Treat HC Thm 3.1 as an unrefereed, unformalised claim whose final arithmetic is right.

---

## Item 4: does the engine give an arithmetic circuit of the kind HC needs?

**AN-ETH's engine: yes [D, re-read].** The time model is the word RAM, AN-ETH l. 752–754: "Time is counted in operations: operations on words … and table queries."
- The recursion uses only polynomial identities in the table entries, with integer constants that do not depend on table values:
  - the expansion d^{|R|} Z = Σ_ι Z_ι (Prop. 3, l. 1004–1012; Thm A(b), l. 1622–1626);
  - the row or column choice by U_row and U_col, which depend on ι and the c_{a,b} only;
  - the grouping search over K^g groupings, which depends on the c_{a,b} only (Lemma 1/8);
  - the group tables W̃_γ, which are sums of products of table values times fixed values of Ψ and f (l. 860–866);
  - brute force at ℓ = 0;
  - one division per level by the integer d^{|R|}.
- Recomputing an entry at each query only duplicates subcircuits.
- So for each (λ, B) the engine is a circuit over ℚ with at most as many gates as operations. Its output equals f_{K,λ} as a polynomial, not only on integer tables. It works over F_p for p ∤ d.
- Theorem B's pieces are fixed integer functions of strings, so the same holds with ρ = 1/√2.

**Gap: the class in Cor. T1/T2 is not defined tightly enough.**
- Def. 4 only asks for correctness on integer tables with |W_w| < 2^B, and B is an input.
- A straight-line program that agrees with f_{K,λ} on the box {−2^B+1, …, 2^B−1}^N need not compute f_{K,λ}, nor have it as its degree-K component: add (x³ − x)·g with B = 1.
- Choosing B ≥ the formal degree (up to 2^size) is not affordable, because the cost factor (B + λ)^C would then dominate.
- The note lists this case (§5, "Not covered" 4). But Cor. T2's sentence "every oblivious algebraic clique-sum algorithm … refutes Weak ETH" needs the definition built in.
- Repair: "an algorithm that, for each (λ, B), is a straight-line program in the table entries (over ℤ, constants and divisions by fixed nonzero integers allowed) whose output equals f_{K,λ} as a polynomial".

**Divisions.** For general programs with divisions by non-constant polynomials, the note invokes Strassen's elimination, which costs a factor poly(K) (degree K, infinite field). That is standard and harmless here. AN-ETH divides only by integers.

**Regime [R].**
- Def. 4 quantifies over all λ at fixed K, so letting λ → ∞ puts every achievable (K, e) inside λ ≥ λ₀(K) = 2⌈C₀w⌉ = Θ(K(log K)^{3/2}).
- AN-ETH's K_ℓ = 2^{log K_ℓ} are even.
- Thm A(c) uses K ≤ m^{1/9} and L ≥ m^{7/9} ≫ λ₀(K) [K, l. 1675–1680], but Cor. T2 does not need this.

**"α > 1/2" and "one (K, λ) suffices" [R].** Theorem T holds for every pair (K, λ) in its regime, so a single circuit below 2^{c_T K²λ/√⌈log₂K⌉} at one such pair contradicts no ports. Two points the note should say plainly:
- c_T and the threshold d₀ are unspecified absolute constants, since HC gives none. So "one circuit" means beating an unknown bound at an unknown size. The usable form is asymptotic: e(K)√log K → 0 along a sequence of even K, which (log K)^{−α} with α > 1/2 gives. Odd K follow by Remark 2.
- Through Def. 4: an algorithm of cost C·2^{eK²λ}(B + λ)^C at B = 1, λ → ∞, with e < c_T/√⌈log₂ K⌉, contradicts Theorem T. So e(K) ≥ c_T/√log K, as stated in Cor. T1. [R]

**Char p [X as stated].** Cor. T2's last sentence ("In characteristic p the same with 'randomised' … and rWETH") cites no quoted source. IM Thm 7.1 is a characteristic-zero theorem [K, IM l. 1686–1690]. Strike the sentence, or mark it [C] and give a source.

---

## Item 1: what HC Thm 3.1 says, and whether "ports" is one notion

**The statement [K, HC l. 475–483]:** "There are an absolute positive integer a and absolute constants c, C > 0 with the
following property. For every sufficiently large even d, set m = ⌈log₂ d⌉ and w = ⌈adm^{3/2}⌉. There is a tensor T_d with
entries in {0, 1} on d rows of common side q₀, with w ≤ log q₀ ≤ Cw, such that over every field F whose characteristic
has no ports, L_F^{[d]}(f_{T_d^{⊗h}}) ≥ exp(chdw/√m) (h ≥ 1)."
- The polynomial is f_T(X) = Σ_j T_{j₁…j_d} X_{1,j₁}⋯X_{d,j_d}, with one variable array per ROW (l. 464–470).
- T^{⊗h} is the grouped power: row index = word of length h, degree still d (l. 471–474).
- L^{[D]} is the degree-component border size (l. 49–58).
- The threshold on d is absolute: it does not depend on the field.
- q₀ = 2^{⌈C₀w⌉} (l. 2883 and Cor. 3.2's proof, l. 659–661).
- The note quotes all of this correctly.

**"No ports" is one notion in all three uses [K + R].**
- HC §2.2, l. 348–352: "A class of metric spaces admits ports if regular multigraphs of a single positive degree and unbounded orders satisfy a uniform Poincaré inequality for squared distances in all its spaces … The condition for X_χ is precisely port admission by χ [44, Definition 11.1]." X_χ is the class of Hadamard spaces admitting spectral prices in characteristic χ (l. 337).
- IM §7, l. 1676–1684: "Characteristic zero admits ports when there are symmetric regular multigraphs of arbitrarily large order, with a common bound on their degrees, and a constant C such that E d(x_U, x_V)² ≤ C E d(x_I, x_J)² for every placement of every such graph in X … [48, Definition 11.1]."
- EG Def. 11.1 (l. 2820–2823): bounded degree; V(x) ≤ γ E_G(x), with V and E_G the mean squared distances over independent pairs and along steps (l. 2814–2818).
- "Single degree" and "bounded degree" are equivalent: an infinite family with bounded degrees has an infinite subfamily of one degree (pigeonhole), and EG l. 2831–2846 also pads to a fixed degree. Loops and diagonal arcs are treated the same way in all three. Both use the same metric class up to scalar extension and Hadamard completion (HC l. 330–347; EG Thm 4.3).
- So the contrapositive chain composes with no loss of parameters: a small circuit for f_{K,λ} over a char-0 field ⇒ (Thm T) char 0 admits ports ⇒ (IM 7.1) 3-SAT in 2^{O(v^{1−δ})}·poly.

**New point: the IM half has a Lean counterpart.** OA Lean, `OAI/Computability/MultitapeWeakETH/Price.lean` and `MiddleDecision.lean` (read only, not built):
- `def PortZero` is the port property over `AlgebraicClosure ℚ`: fixed degree D, orders 2^exponent, connected, every complete metric space with `RealizableConfigurations`;
- `def WeakETH : Prop := ¬ PowerSavingDecision satAnswer`, the variable-count, deterministic multitape form;
- `theorem middle_count_bridge : MiddleCountBridge`, i.e. `PortZero → PowerSavingDecision …`;
- `theorem price_of_variable_weakETH (weak : WeakETH) : PriceZero`.

grep finds no `sorry` in that folder; the `sorry` in `ComparatorChallenges/MultitapeWeakETH.lean` is the challenge statement. The docstring cites "Theorem 3.2 of the middle-bit paper", a different source from IM 7.1. Matching `PortZero` to HC's "ports in characteristic 0" needs one step: HC l. 330 says "Every spectral space extends isometrically to a Hadamard spectral space", so a Poincaré inequality for Hadamard spectral spaces gives it for all realizable ones. I mark this identification [D]. The earlier review `research/ports/review-theoremAB.md` §1 compares the same definitions and reaches the same conclusion. The note's table in §6.1 ("IM Thm 7.1 … [K], unrefereed") should add: "a Lean form (`middle_count_bridge`) exists in OA's release, not built by us".

**Verdict on item 1: correct.** Theorem T itself uses neither Anthropic's Theorem A nor any port notion of ours, so the bookkeeping issue raised for Theorem A does not arise here. Theorem A appears only in the case table of §4.

---

## Item 2: is f_{K,λ} = f_{T_K(λ)}, and is Lemma L right?

**Variables [K + R].** AN-ETH Def. 3 (l. 800–812): "A setting z_w of node w is a (K−1)-tuple of strings z_w(w′) ∈ {0,1}^λ, one for each w′ ∈ [K] \ {w}, and S_w = ({0,1}^λ)^{K−1} … The W_w : S_w → Z are arbitrary functions" and "the value is the sum, over all choices of one string in {0,1}^λ per edge, of ∏_{w∈[K]} W_w evaluated at the strings on the edges at w".
- So there is one table per node, not per pair.
- With variables X_{w,z} = W_w(z), the value is Σ_{(z_w)} ∏_{u<v}[z_u(v) = z_v(u)] ∏_w X_{w,z_w} = f_T for T = ⊗_{u<v}⟨2^λ⟩_{uv} on K rows of side 2^{λ(K−1)}. This is exactly HC's format.
- The brief's worry, that the engine's input is tables on edges, does not apply to Def. 3. A pairwise-constraint presentation (Def. 2's Ψ_{a,b}) is not the polynomial in question.

**Lemma L [R].** If U = (⊗_u M_u)T, then f_U(X) = Σ_i T_i ∏_u (Σ_j (M_u)_{j,i_u} X_{u,j}) = f_T(Y(X)), a homogeneous linear substitution.
- Form (a): a circuit for f_T gives one for f_U with extra gates for the Y.
- Degree components: substitution commutes with taking the degree-K component, because Y is homogeneous linear.
- Closure: g ↦ g∘Y is linear, hence Zariski-continuous, so the image of the closure lies in the closure of the image.
- Form (b) is HC's own sentence (l. 596–598) and is also fine.

**The gate count [R + N].**
- For the star restriction, Y_{u,(j,ℓ)} = Σ_i A_{i,j} X_{u,(i,ℓ)}, with j the own-star part ((2^a)^{K−1} values) and ℓ the leaf part (Q^{K−1} values, Q = q₀^{h₀} = 2^a). Each Y has at most Q terms.
- Total ≤ K·2^{a(K−1)}·Q^{K−1}·Q = K·2^{a(2K−1)} ≤ K·2^{λ(K−½)}.
- `star_lemma.py` counts it and the bound holds; it is attained when λ = 2a and Q = 2^a.

**Non-vacuity [R].**
- Lower bound: log₂ L ≥ c_T K²λ/√m (form (a) needs c_T K/√m > 1 to absorb K·2^{λ(K−½)}).
- Brute force: λK(K−1)/2 + O(log K).
- AN-ETH: e_ℓ K²λ with e_ℓ ≤ 0.85((3x₀+6)/log K_ℓ)^{1/2} [K, l. 1592–1593 with Thm B l. 1723 and l. 2410–2412].
- So the bound is non-trivial, compatible with both upper bounds, and forces c_T ≤ 0.85√(3x₀+6) (and c_T < 1/2 from brute force). Neither HC nor the note fixes c_T, so there is no tension.
- In the number n = K·2^{λ(K−1)} of variables the bound is n^{c_T K/√log K}, the same shape as HC Cor. 3.2.

**Verdict on item 2: correct.**

---

## Item 3: the star lemma

**Proof [R].**
- (i) Split each edge's 2a bits into two a-bit blocks, one given to the star of each endpoint.
- (ii) M_v: |j⟩ ↦ Σ_i A_{i,j}|i⟩ at the centre, coordinate inclusion or projection at the leaves; then (M_v ⊗ id)Star_v(a) = A.
- (iii) Tensoring over v gives ⊗_v A^{(v)}.
- (iv) With A^{(v)} = T^{⊗h₀} for every v, the result is T^{⊗Kh₀} up to a row-local permutation of letters.
- λ > 2a is handled by projecting the extra bits to 0.

**Explicit computation [N, `star_lemma.py`].** I enumerated the support of T_K(λ), applied my own local maps and compared the result with the grouped power entry by entry. Exact equality in every case, with random integer T:
- K = 3: (q, h₀, a, λ) = (2, 1, 1, 2), (3, 1, 2, 4) (q not a power of two, so leaf projection is used), (2, 2, 2, 4) (h₀ = 2, giving T^{⊗6}) and (2, 1, 1, 3) (λ > 2a);
- K = 4: (2, 1, 1, 2), giving T^{⊗4}.

**Bookkeeping.**
- Row bits: 2a(K−1) for T_K(2a) against K·h₀·log₂ q ≤ Ka for the hosted power. The ratio is exactly 2(K−1)/K when q^{h₀} = 2^a, as printed by the script.
- h = K·h₀ with h₀ = ⌊⌊λ/2⌋/b₀⌋, b₀ = ⌈log₂ q₀⌉ = ⌈C₀w⌉ [K, HC l. 2883: "Pad each leg with zero coordinates to q₀ = 2^{⌈C₀w⌉}"]. HC's T_d has the required form: d rows of common side q₀.
- The arithmetic: ⌊λ/2⌋ ≥ λ/3, ⌊x/b₀⌋ ≥ x/(2b₀) for x ≥ b₀, and w/b₀ ≥ 1/(2C₀) give hKw/√m ≥ K²λ/(12C₀√m). I checked this. [R]

**Constraints.** λ ≥ 2b₀ is the only constraint on λ. The others are on K: K = d even, K ≥ d₀, and K large enough that c_T K/√m > 1 for form (a). The note states all of them in the theorem. Its §0 wording "λ ≥ λ₀(K) … the only constraint" should read "the only constraint on λ".

**Verdict on item 3: correct.**

---

## Item 5: sanity against known upper bounds

- **K = 3 [N, `k3_trace.py`].** With W₁(x,y), W₂(x,z), W₃(y,z), the value f_{3,λ} = Σ W₁W₂W₃ equals tr(W₁W₃W₂ᵀ), checked numerically. So a circuit of size O(2^{ωλ}) exists and e(3) ≤ ω/9: 1/4 with OA's ω = 9/4, 0.2635 with ω ≈ 2.3716, against brute force 1/3 (Def. 4's trivial 1/2 is loose).
- **Fast matrix multiplication for general K.** Group the nodes into three groups and multiply. The group tables already have 2^{λ·2K²/9} entries, so this route never gets below e = 2/9, a constant. It cannot beat c/√log K for large K. Theorem T says nothing for fixed small K, so there is no conflict.
- **Other known bounds.**
  - AN-VP E.10: e ≥ 1/(8√K), flat and unconditional (given AN-VP).
  - AN-ETH: e ≤ C/√log K.
  - Theorem T: e ≥ c/√log K under no ports.
  - These are mutually consistent. I know of no unconditional algorithm with e(K) = o(1/√log K).
- **Grouped-power counting.** Cor. T3's upper bound n^{O(d/√log d)} for T^{⊗dh₀}, against the parameter count q^d of a generic T, needs 2eK ≥ 1, which holds. HC's lower bound exp(chdw/√m) also lies below the generic dimension-count bound exp(Θ(hdw)). No inconsistency.
- **Verdict on item 5: no contradiction and no normalisation error.**

---

## Item 6: Lemma N, E2, E3

**Lemma N: correct for K ≥ 4; false for K = 2 [R + N].**
- The proof is right: the same-side triangle inequality gives (K/2 − 1)·star, and a pair is on the same side with probability (K/2 − 1)/(K − 1).
- The proof divides by K/2 − 1, so it needs K ≥ 4.
- At K = 2, take A = {1}, B = {2}, y₀ = x₁, y₁ = x₂: the left side is 0 < d(x₁, x₂). `lemmaN_E2_E3.py` prints −1.
- Repair: "K even, K ≥ 4". Every use in the note has K large, so nothing downstream changes.
- Tests: 600 random spaces (graph, tree, ℓ₁, ℓ₂, ℓ_∞; K = 4, 6, 8; suppliers over all points) give a minimum normalised slack of −6·10⁻¹⁶ (rounding). Four adversarial hill-climbs on graph metrics (K = 6) stay ≥ 1.5·10⁻⁵. The K-pod equality case (K = 8) gives slack 0.
- Cor. N1–N3 and §2.1's algebra: re-derived, correct [R]. N3's σ_ℓ is the best saving on Lemma N's cut, which is ≥ min_ℓ σ_ℓ, so the inequality goes the stated way.

**E2: correct [R + N].**
- The tangent inequality |x_e − x_ē| − |x_e − y| − |x_ē − y′| ≤ ⟨ν, y′ − y⟩ holds.
- w = ½ Σ_u s_u X_u, by antisymmetry.
- E|w|² = (K/(4(K−1)))·Σ|X_u|², using E[s_u s_{u′}] = −1/(K−1) and Σ_u X_u = 0.
- Tests: the formula matched to 10⁻⁸ on every random trial (K = 4, 6, 8). min_cut|w| is at most 0.63 of the cap. The placement (e_u − e_v)/√2 has |w| = K^{3/2}/(2√2) on every exactly balanced cut (5.196 for K = 6, 8.000 for K = 8).
- E2 is only an upper bound. On one cut at K = 6, a supplier search along the cut direction reached V = 5.05 < |w| = 5.20.
- The restriction to exactly balanced cuts only strengthens the min.

**E3: correct [R + N].** It uses the barycentre contraction in Hadamard spaces, d(x, bar μ) ≤ ∫ d(x, y) dμ (Sturm; quoted by HC l. 1213–1215 as stated in the note), and then the triangle inequality. A Euclidean test (barycentre = mean, 300 trials) gives max(LHS − RHS) = −34.7 < 0.

E1 is the triangle inequality and is correct. I did not referee E4–E6 or X′, which are [D]/[X]/[C] and not used for Theorem T.

---

## By-products and other remarks

- **Cor. T3** is correct as a derivation [D]: Lemma S plus Lemma L in the upper-bound direction (f_U = f_{T_K}∘Y), with the extra cost ≈ n^{(2K−1)/K} and the main term n^{2e_ℓK}. It is conditional on AN-ETH Thm A(b) and Thm B, which are unrefereed. For general tensors T, the Y have coefficients from T, which is fine.
- **Cor. T4** is [D] and doubly conditional (HC Thms 8.1/11.2 and AN-ETH). One unstated hypothesis: HC's sharing bound O(d√m) needs the spare Hilbert coordinates of Lemma 2.2 (a product of the cone with ℓ₂). Without it the tree bound gives O(d²), which is absorbed only as h → ∞. Since Cor. T4 lets h grow, the statement survives, but the hypothesis "the class contains Y × ℓ₂ with prices" should be added.
- **Remark 4** (hubs, short wires): the arithmetic e ≳ λ/(K(log λ)²) is right. Substituting constants lowers the degree, so in the border model it needs the same homogenisation step as Remark 2 [D].
- **§4 tower statement** (liminf of the geometric mean ≥ 1/√2): correct given Theorem T, for towers realised as polynomial-identity circuits [R].
- **§3.3 Remark 3** (uniformity in h): correct. Thm 3.1 is stated for every h ≥ 1.

---

## What may be claimed publicly

Lemma N (for K ≥ 4), E2, E3 and Lemma S are unconditional. The negative answer to the literal Q2 of `prior-barriers.md` §5.3 and the star restriction can therefore be stated as proved, short results.

**Final sentence.** Publicly one may claim only the following. If OpenAI's unrefereed and unformalised HC Thm 3.1 holds as printed, then over any field whose characteristic has no ports (in HC's sense, the same notion as EG Def. 11.1), every straight-line program that computes AN-ETH's clique polynomial f_{K,λ} as a polynomial identity needs 2^{c·K²λ/√log K} gates, for all sufficiently large even K and all λ ≥ C·K(log K)^{3/2}, with unspecified absolute constants. Consequently, if in addition OpenAI's IM Thm 7.1 holds (unrefereed; a Lean counterpart `middle_count_bridge` exists in their release, which we did not build), then any such polynomial-identity algorithm over ℚ with e(K)·√log K → 0 along even K would give 3-SAT in deterministic time 2^{O(v^{1−δ})} and refute variable-count Weak ETH. Nothing may be claimed in positive characteristic, for algorithms that are correct only on bounded integer tables, for non-algebraic algorithms, or for wires shorter than C·K(log K)^{3/2}.
