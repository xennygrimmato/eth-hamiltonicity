# Referee report: Theorems A and B and the case table of `ideas-ports.md`

Adversarial review, 26 Nov 2026. Scope: §0, Part 1 and Part 2 of `research/ports/ideas-ports.md`.
Sources read (pdftotext copies in the scratchpad):
- AN = Anthropic, "VP ≠ VNP over every field": Def. 2.1, App. A.1–A.3, D.1–D.3, F (whole), G.1, K.1, K.4–K.7, M intro, the formalisation notes.
- OA: EG §1, §2.1–2.4 (Lemmas 2.2 and 2.3); HC §1, §2.2, §4 (Lemma 4.1, Theorem 4.2 with full proof, Cor. 4.3), Thm 12.2; IM §7 (Thm 7.1 with proof).
- OA Lean (read, not built): `Price.lean` (PortZero, PriceZero, WeakETH), `Cloud.lean` (`exists_logarithmic_placement`), `WalkEnergy.lean`, `WireSpectrum.lean` (SpectralPoint), `SpectralRealizable.lean`, `WireGeodesic.lean`, `WireExpanders.lean`, `MiddleDecision.lean`.
- Ours: `vpvnp/c1/notebook.md` §1–4, `vpvnp/b2/notebook.md` §0–3.

Numerical sanity check (new): `scratchpad/refAB/gap2.py`, the spectral gap of the walk on U_h(F₂) with the generators x_j.

## Summary of verdicts

| Claim | Verdict | Confidence |
|---|---|---|
| Theorem A (contracting over k ⇒ ports in char k) | **CORRECT**, with presentational fixes (Lean side condition, quote of HC 4.2, field step) | 85% that the argument is right, given AN F.6 and HC 4.2 as published; most of the residual risk is in those two cited theorems, not in the deduction |
| Consequence: contracting over ℚ ⇒ 3-SAT in 2^{O(v^{1−δ})}; Weak ETH ⇒ contracting fails in char 0 | **CORRECT** (conditional on IM 7.1 = HC 13.1, i.e. OpenAI's whole compression chain) | 85% for the deduction; IM 7.1 itself is unreviewed by us (Lean `middle_count_bridge` exists, not built) |
| Theorem B (i), (ii) | **CORRECT** | 90% |
| Theorem B (iii) | **CORRECT WITH FIXES**: "spectral point" must be read as AN's spectral point (Strassen points only via the unreviewed Prop. 11.2′) | — |
| {contracting, no ports} impossible | **CORRECT** (= Theorem A), stated per field and characteristic | 85% |
| Rest of the table | **CORRECT WITH FIXES** (wording) | — |
| "OA's unconditional permanent bound is essentially AN's contracting-case bound" | **CORRECT WITH FIXES**: OA's bound is weaker by a factor log log N in the exponent, and the circuit models differ | — |
| "the ports algorithm is a piece family, obeys all flat floors, wins by iterating the √ trade" | **heuristic, not a theorem**. "Obeys the floors" is automatic under FH (which OA's EG 1.1 supplies). "Is a piece family" in b2's sense (T = 2^{o(λ)} terms) is not established. | — |
| "No LP/SDP over known necessary conditions can exclude M5 or ρ₃" | **CORRECT WITH FIXES**: true for *metric-only* CAT(0)-valid conditions. Not shown for B.3 (CAT(0)-validity is [C]) or for conditions involving non-wire tensors (δ(S), joint convexity). | — |
| Tension check (attack point 6): does contracting refute itself? | **No contradiction found.** | 80% |

**Weakest link.** It is not in the deduction; it is the two big imported theorems:
- AN F.6 (in Lean, by AN's statement);
- HC 4.2 (one page; I re-read it and found no gap).

For the 3-SAT conclusion, the whole of OpenAI's enumerable-contraction chain (HC 13.1 → IM 7.1) also enters; we have not checked it. Inside the deduction the fragile item is purely presentational: the Lean form of HC 4.2 carries a side hypothesis (`scalar`) that the note omits.

---

## 1. Attack point 1: are the two classes of "spectral" objects the same, and which way does containment go?

**The definitions differ.**
- AN Def. 2.1 / A.1 asks for: φ ≥ 0, φ(1) = 1, multiplicative, and subadditive on covers (s = Σ s_j, s_j ≤ t_j ⇒ φ(s) ≤ Σ φ(t_j)).
- AN states explicitly (after Def. A.1): "This class is larger than Strassen's asymptotic spectrum, whose points are in addition additive under direct sums and normalized on unit tensors, and for example φ^a is again a spectral point for 0 < a ≤ 1."
- OA's spectral point (EG §2.1, Lean `WireTensor.SpectralPoint`) is exactly Strassen's: it preserves 0 and 1, is monotone, ⊕-additive and ⊗-multiplicative, and hence F(Δ_J(r)) = r.

**Containment: OA ⊆ AN.**
- Let s = Σ s_j with s_j ≤ t_j.
- s is a restriction of ⊕_j s_j: at each party, apply the map that adds the blocks; the cross blocks of ⊕ vanish.
- So F(s) ≤ F(⊕ s_j) = Σ F(s_j) ≤ Σ F(t_j).
- The converse fails: φ^a with a < 1 is AN but not additive.

**This is the direction Theorem A needs.** F.6 is a statement about all AN prices on U_h. We need it for every placement x : U_h → X into a Hadamard spectral space X of characteristic χ.

**Normalisations.**
- OA: d(a,b) = H(E_ab(2)) = log₂ F(E_ab(2)).
- AN: φ(⟨q⟩_uv) = q^{d_φ(u,v)}, so d_φ = log₂ φ(⟨2⟩_uv).
- These are identical; the [0,1] range is automatic on both sides.

**Spectral spaces are not a larger class at the finite level.**
- EG §2.2 requires every finite S ⊂ X of positive diameter to carry prices δ(S)·log₂ F_S for one Strassen point F_S on S. On S, therefore, the metric is δ(S)·d_{F_S}.
- The placement's pull-back to U_h is (u,v) ↦ δ(S)·d_{F_S}(x_u, x_v). This is c·d_φ for the AN spectral point φ(t) = F_S(x_* t) (push-forward; AN A.1 and A.3 record that push-forward preserves 1, products, restrictions and covers).
- Diameter-0 images are trivial.
- So every finite configuration of every OA spectral (or Hadamard spectral) space is exactly an AN price. No limit is needed, though AN prices are closed under limits anyway.
- The Hadamard completion (EG Thm 4.3) adds points but not new finite configuration types beyond those with the same property.

**The field.** HC §2.2 lets X_χ carry prices over any field of characteristic χ, and OA "may work over an uncountable algebraically closed field".
- **k = ℚ (the case that matters).** A Strassen point over K ⊇ ℚ, restricted to tensors defined over ℚ, is a Strassen point over ℚ. Restrictions over ℚ are restrictions over K, and ⊕, ⊗ commute with base change. Wires are defined over ℚ. So the ℚ case needs **no** Lemma 2.3.
- **General k.** Restrict F_S to the prime field P, then use EG Lemma 2.3 (with P ⊆ k) to find a Strassen point over k with the same values on the finitely many wires of S. I read the proof of Lemma 2.3. It separates by a rational polynomial, applies Lemma 2.2 over k, specialises by Zariski's lemma to a finite extension L/P, and descends with a P-linear functional L → P. The [L:P]^{|J|} loss is killed by the n-th root. It is sound given Lemma 2.2 (Strassen duality via Zorn).
- The strategist's bookkeeping paragraph is therefore correct. It slightly overstates the need for Lemma 2.3 in the ℚ case.
- **Side remark.** AN prices over K ⊆ AN prices over k for k ⊆ K (by restriction), so contracting over k ⇒ contracting over K. The converse would need an AN analogue of Lemma 2.3, which AN does not state. Not needed here.

## 2. Attack point 2: F.6, its quantifiers, and the degree issue

**F.6 verbatim (AN App. F.3).**
> "Theorem F.6 (Poincaré inequality). There are an integer u ≥ 2 and a real number C₀ ≥ 0 such that for every l ≥ 2, h = lu, and every price on U_h
> E_{g,a} |a, ga|² ≤ C₀ Σ_{j<h−1} E_a |a, x_j a|²."

Context:
- Standing assumption of App. F (verbatim): "In this section and in Sections G to K we are in the contracting case, and we fix μ and s as in Definition D.1."
- The prose says "C₀ does not depend on h". In the proof, C₀ = 32C(2u)/(1−2c), with u fixed from C(n) = o(n²).
- So C₀ and u depend only on (μ, s); the statement holds for every price on U_h over the field k.
- AN App. M: "Sections A to L use nothing about k except that it is a field, apart from the element ½ in Prop. E.1". So F.6 holds over an arbitrary field k in the contracting case over k.
- Lean name thm_poincare. AN notes that Lean states Lemma F.3 with different explicit numbers, which does not affect the statement.

**Translation into the HC normalisation.**
- V_π(x) = Σ π_i π_j d² over ordered pairs; with π uniform it equals E_{g,a}|a,ga|², since (a, ga) is a uniform independent pair.
- G_h = Cayley graph of U_h with left multiplication by the x_j:
  - each x_j is an involution over F₂;
  - x_j a ≠ a, and different j give different neighbours;
  - so G_h is a simple (h−1)-regular graph, with walk P = (1/(h−1)) Σ_j L_{x_j}.
- Then Σ_j E_a|a,x_j a|² = (h−1)·E_P(x), so V ≤ C₀(h−1)·E_P on every placement in X_χ, by §1.

**HC 4.2 is a single-graph certificate. Growing degree is harmless.**
- Statement (verbatim): "Let P be the walk on a d-regular multigraph with n ≥ 2 vertices, d ≥ 1, and uniform stationary law π. Suppose that V_π(x) ≤ β E_P(x) for every placement x in every member of a class of Hadamard spaces without ports. Then β ≥ c log n / log(d+1) for an absolute constant c > 0."
- The quantifier is over ONE graph H.
- The proof:
  - takes H with too small a β;
  - smooths the walk on the previous graph (Lemma 4.1, barycentric, valid in any Hadamard space);
  - replaces each old vertex by a copy of H, joined through an involution realising R;
  - gets degree 2d, order n^k, and constant ≤ 2Bb whenever Bb/t ≤ 1/2, with t ≈ log(n/2)/log(2d+1);
  - "These graphs would be ports for the class."
- So one graph G_h, of degree h−1 for one fixed large h, certifies a bounded-degree (degree 2(h−1)) family of unbounded order.
- Ports (EG Def. 11.1: "bounded degree, unbounded order, one γ for all spectral spaces") does not need the certificate's degree to be bounded across h. Only one h is used.
- The strategist's reading is correct.

**I checked the proof of HC 4.2 line by line** and found nothing missing:
- β ≥ ½ from a two-point space;
- the padding m_uv = ⌈nS_uv/2⌉, with row sum ≤ n/2 + (2d+1)^t ≤ n;
- R ≥ S/2 gives ρ ≤ 2C(1+γ/t);
- v₀ ≤ b·E_in, by minimising against a uniform point of the copy;
- E_R(z) ≤ 3(2v₀+E_match) and V(x) ≤ 3(2v₀+V(z));
- the iteration bound Bb(1+γ/t) ≤ 2Bb.

It uses only barycentres inside each single space, and the hypothesis on H inside the same class. No closure property of X_χ is used (in particular not ℓ₂ products), so the unresolved product question (HC 6.1) does not enter.

**Lean form, and a missing side condition in the note.** `exists_logarithmic_placement (price : PriceZero) (s e) (large : 10000*(e+3) ≤ s) (H) (symm) (rows : row sums 2^e) (scalar : HasPoincareBound ℝ (normalizeArcs H (2^e)) (s/(10000*(e+3))))` concludes that some SpectralTarget placement has (s/(10000(e+3)))·walkEnergy < (ΣΣ d²)/2^s.
- **Fix 1.** The Lean theorem has the extra hypothesis `scalar`: the same bound for real-valued placements. The paper version has no such hypothesis, because ℝ ∈ X_χ (HC §2.3: segments, then a pointed limit). For Theorem A it is satisfied:
  - finite subsets of a line are AN prices over every field (b2 §3(ii), from AN Prop. C.3 + Lemma C.4(a); also from EG Thm 1.1);
  - so F.6 gives the scalar bound C₀(h−1) ≤ the threshold.
  - The note should say this when it cites the Lean constant.
- **Normalisation.** `HasPoincareBound` is (ΣΣd²)/N ≤ γ·walkEnergy, with walkEnergy = Σ_i Σ_j A_ij d². This is N·V ≤ γ·N·E_P, i.e. the paper's form ("multiplying the paper's variance and edge energy by the order").
- **Padding.** Adding 2^e − (h−1) holding arcs multiplies E_P by (h−1)/2^e ≥ ½, so β ≤ 2C₀(h−1).
- The order 2^{h(h−1)/2} is a power of 2, as Lean's PortZero needs.
- PortZero also demands connectivity. Connectivity holds for the produced family (and EG notes every port graph is connected).

## 3. Attack point 3: the arithmetic

- n = |U_h| = 2^{h(h−1)/2}, d = h−1.
- Paper form: c·log n/log(d+1) = c·(h(h−1)/2)/log₂h (base change absorbed in c), which exceeds C₀(h−1) as soon as h/log₂h > 2C₀/c.
- Lean form, with s = h(h−1)/2 and e = ⌈log₂ h⌉ ≤ log₂h + 1:
  - s/(10000(e+3)) ≥ h(h−1)/(20000(log₂h+4));
  - the condition `large` holds for large h;
  - 2C₀(h−1) < threshold ⇔ h/(log₂h+4) > 40000·C₀.
- All correct. h must be a multiple u·l with l ≥ 2. Large multiples exist.

**Sanity check of F.6 against scalars (new, [N]).** If F.6 failed for real-valued placements, then, since lines are prices, the contracting hypothesis itself would be refuted. That would be a major finding, so I checked it. F.6 for scalars says the walk on G_h has spectral gap ≥ 1/(C₀(h−1)).

Power iteration (`scratchpad/refAB/gap2.py`, 4000 iterations; the estimate is an upper bound on the gap):

| h | |U_h| | gap | gap·(h−1) |
|---|---|---|---|
| 3 | 8 | 0.2929 (exact: the 8-cycle) | 0.586 |
| 4 | 64 | 0.0969 | 0.291 |
| 5 | 1024 | 0.0501 | 0.200 |
| 6 | 32768 | 0.0312 | 0.156 |
| 7 | 2097152 | 0.0220 | 0.132 |

- The fit gap·(h−1) ≈ 0.074 + 2.05/(h−1)², made on h = 3 and 6, predicts 0.302, 0.202 and 0.131 at h = 4, 5, 7 (observed 0.291, 0.200, 0.132).
- gap·(h−1)² rises again at h = 7 (0.78 → 0.79), which a gap of order 1/h² would not produce.
- This is consistent with gap ≍ 1/h, as in Stong's eigenvalue bounds that AN cite in F.4.
- **So no contradiction.** The data are not a proof; small h cannot separate 1/h from 1/(h log h).

## 4. Attack point 4: IM Theorem 7.1

**Statement (verbatim).**
> "Theorem 7.1 (Expansion and 3-SAT). If characteristic zero admits ports, then for some δ > 0 a deterministic algorithm decides 3-SAT on v variables in 2^{O(v^{1−δ})} bit operations times a polynomial in the input length. In particular, under variable-count Weak ETH, characteristic zero does not admit ports."

**IM's definition of ports** (§7.1):
- The class X = complete CAT(0) spaces carrying compatible Strassen-type spectral prices "for rational tensors on all finite subsets".
- Ports means: symmetric regular multigraphs of arbitrarily large order, with a common bound on their degrees, and one C with E d(x_U,x_V)² ≤ C·E d(x_I,x_J)² for every placement in X.
- So IM works over ℚ directly. Contracting over ℚ gives F.6 for AN ℚ-prices ⊇ OA ℚ-spectral metrics (§1). The certificate then gives IM-ports, again via HC 4.2, whose proof works in any class of Hadamard spaces.
- "Characteristic zero" is matched by "contracting over ℚ", and also by contracting over any char-0 field via Lemma 2.3.
- Lean: PortZero is stated over AlgebraicClosure ℚ, and ℚ̄ ⊇ ℚ, so §1's restriction argument covers it.

**Proof status.**
- The proof in IM is short. It combines HC Thm 13.1 (enumerable contraction, under ports, 2^{O(s^{1−η})}) with standard sunflower sparsification, and the sparsification part looks fine.
- All the weight is in HC 13.1, i.e. EG §§12–13 and HC §§13–15, which we have NOT reviewed.
- Lean: `middle_count_bridge : MiddleCountBridge` (PortZero → PowerSavingDecision for "count > 0") is a theorem in `MiddleDecision.lean`, and `price_of_variable_weakETH : WeakETH → PriceZero`. The MultitapeWeakETH directory contains no `sorry`/`axiom` hits. We did not build it.
- So the Consequence is correct *conditional on OpenAI's release*. Tag it [K-OA, Lean-unbuilt], as the strategist did.

## 5. Attack point 5: Theorem B

- **Restriction.** M5 ⊂ Mat₂(F₂). I recomputed the ten ranks:
  - rank 2 on 0–I, e₁₁–e₂₂, (e₁₁+e₁₂)–e₂₂;
  - rank 1 on the other seven.
  Pull-backs along injections are prices (AN A.3), so ρ₂ a price ⇒ M5 a price. ✓
- **Pull-back from μ = 2 to μ = 3.** a ↦ diag(a,0) preserves rk(a−b), so ρ₃ a price ⇒ ρ₂ a price. Contrapositive: ρ₂ not a price ⇒ ρ₃ not a price. ✓
- **The D.2 direction needed.** "Contracting fails ⇒ ρ_μ is a price (μ ≥ 3)". This is the direction actually used, and it is AN's own argument:
  - Step 2 uses failure *at this μ only*: "for every s with 1 ≤ s < √μ there is a price with D(μ) > s D(1)", then compactness.
  - Steps 3–7 give |a,a′|² = rk(a−a′); Step 5 needs μ ≥ 3.
  - So the sharp form is: **for each μ ≥ 3, contracting fails at μ ⇔ ρ_μ is a price.** (⇐ holds because ρ_μ has D(r)² = r.)
  - Hence ρ₃ not a price ⇒ contracting holds at (μ, s) = (3, some s < √3) ⇒ Theorem A.
  - Remark D.3 confirms the reading ("for μ ≥ 3 the price √rk(a−a′) of the proof above is not [Euclidean]").
  - c1 Prop. 1 states exactly this.
- **Field.** "Not a price over ℚ" ⇒ contracting over ℚ ⇒ (Theorem A) ports in char 0 ⇒ (IM 7.1) fast 3-SAT. ✓
- **The caveat is honest.** The object is finite, but deciding whether it is a price is an asymptotic cover question (c1's characterisation). "A single cheaper cover would prove (i) or (ii)" should read "a family of covers of the powers C^m with exponential saving (c1 §1 characterisation)". Scale freedom (c·d_φ with c arbitrary) means one fixed identity in fixed dimensions constrains d_φ, not the price up to scale.
- **Fix for (iii).**
  - What Weak ETH gives (via ¬contracting over ℚ and D.2) is that ρ_μ is an **AN price** over ℚ: a limit of c·d_φ with φ only cover-subadditive and multiplicative.
  - The note says "a spectral point over ℚ on 2^{μ²} parties whose wire metric is … √rk"; to be correct it must say AN spectral point, with limits.
  - A Strassen (OA) point realising ρ_μ under Weak ETH would follow only from the strategist's Prop. 11.2′ ("σ_m not OA-spectral ⇒ ports"). That is a [D] reading of the inside of EG Lemma 11.3, unreviewed, and stated only for m a power of two.
  - The "existence theorem" paragraph after (iii) inherits this caveat.

## 6. Attack point 6: tension, and whether contracting refutes itself

I looked for a route "contracting ⇒ contradiction", which would make ¬contracting, and hence √rk being a price for every μ, an unconditional theorem. **None found.** In detail:

1. **AN's contracting case.** It refutes *accelerators* (Def. K.1): programs that evaluate sums over runs of v^H steps within v^{H−16} steps, a polynomial speed-up of counting. Thm K.6 kills them by an indirect diagonal argument (V = 1 + V in a finite field).
   - Contracting ⇒ ports ⇒ an enumerable contraction in 2^{O(s^{1−η})}, an exponential-time power saving.
   - An exponential-time power saving is not an accelerator, so there is no clash.
   - The same holds for the strategist's §2.5 sketch (cutting + brute force = 2^{τ^{1−12/H}}).
2. **OA's ports branch.** It yields lower bounds (HC 12.1, 12.2: 2^{N^ε}) via a counting diagonal, not a contradiction.
   - A 2^{N^ε} circuit lower bound for HC_N is consistent with Ryser/Valiant upper bounds of 2^{O(N)}.
   - The only "contradictions" of ports are with conjectures: Weak ETH and ETH in char 0, and in char p with count-mod-p hypotheses.
3. **EG's proof of Thm 1.2 (flats exist)** derives a contradiction from "a largest flat", using cube exclusion **twice**:
   - once for ports (§11);
   - once for the local routing tests of §9 ("A transverse segment in the limit would produce the excluded cube").
   Ports alone do not suffice, so contracting ⇒ ports does not feed into that contradiction. Cube exclusion is false given EG 1.1, so it cannot be supplied.
4. **Contracting is compatible with flats.** Euclidean pull-backs to Mat_μ(F₂) have D(μ)²/D(1)² ≤ R_μ < 2 (c1 §4). With μ = 3 this is below 3, so Hilbert space and lines satisfy the contracting inequality. F.6 for scalars matches the numerics (§3).
5. **Product structure.** AN's contracting hypothesis is a statement about all prices. Since OA ⊆ AN, it implies the OA statement, never conversely. No OA theorem asserts the existence of a Strassen point with D(μ) = √μ·D(1), which would refute contracting. ρ_μ being OA-spectral is unknown (Part 4 of the note).

**Conclusion.** The joint picture "contracting ∧ flat ∧ ports" is not refuted by anything either lab proves. It contradicts Weak ETH in char 0, and that is all.

## 7. The table of cells and its remarks

- **{contracting, no ports} impossible.** Correct = Theorem A. It should be stated per field: "contracting over some field of characteristic χ ⇒ χ has ports".
- **Row "contracting, ports", column (b).** AN's thm_contracting (Thm K.7) is verbatim 2^{c(log m)²/log log m}. AN's Theorem 1.1 is m^{c(log m)^{1/3}} = 2^{c(log m)^{4/3}}. HC 12.2: L_F^{[N]}(HC_N) > 2^{N^ε} "over every field F of characteristic χ, including χ = 0", in port characteristics. ✓
- **"OA's unconditional bound is essentially AN's contracting-case strength."** OA HC 1.1: exp(c(log N)²/(log log N)²). AN contracting: 2^{c(log m)²/log log m}.
  - The two are equal only up to a factor log log in the exponent; OA's is the weaker.
  - Both are N^{Θ̃(log N)}, so "essentially" is fair only with that qualifier stated.
  - The models also differ: OA counts degree-component border size, while AN counts exact circuits and separately approximate ones (Thm 1.4). The bounds are comparable but not literally the same quantity.
  - OA's unconditional bound does strictly exceed AN's unconditional 2^{c(log m)^{4/3}}. ✓
- **"AN's contracting bound is weaker than what contracting gives (2^{m^ε} via Theorem A + HC 12.2)."** Correct, conditional on HC 12.2.
- **Cell (d): "a ports algorithm is a piece family and obeys all our flat floors."**
  - "Obeys the floors" is not a finding: b2 Theorem 3 holds for *every* identity under FH, and FH holds unconditionally given OA EG 1.1 + §1 containment.
  - "Is a piece family": b2's floors need T = 2^{o(λ)} terms and the merge/hub format. The EG 12.1 / 13.1 rewriting is a sum over shared bits whose count is itself the cost being traded. Whether it fits b2's (★) format was not shown.
  - The explanation that the port configuration's Euclidean floor is harmless is right: the Hilbert Poincaré constant of an expander is 1/gap = O(1).
  - The story that the gain comes from bounded degree, allowing a·log s iterations, matches EG 13.1's √L_T ≤ 2^{−T}(√L₀ + O(P₀)).
  - Label the cell [D-heuristic].

## 8. "No LP/SDP over known necessary conditions can exclude M5 or ρ₃"

- c1 §2 is checked: L_a = tL₀ + O·Γ_a, with relative position (1^r, 0, (−1)^r) of length √(2r). So √2·ρ_μ is isometric to a vertex set of the Bruhat–Tits building of GL_{2μ}(F₂((t))), which is complete CAT(0).
- Hence every inequality valid in all CAT(0) spaces holds on ρ_μ and on M5. That part is a tautology plus a correct embedding.
- **Overstatement 1: B.3.** The crossing inequality is a metric-only 8-point condition. Its validity in all CAT(0) spaces is only [C] (c1 proves it in Hilbert space; numerics on trees, H², ρ₂, ρ₃ find no violation). So "cannot exclude" holds for B.3 only numerically.
- **Overstatement 2: non-wire tensors.** Conditions involving other tensors are not metric-only and are not covered by the CAT(0) argument:
  - shared-label prices δ(S) with diam ≤ δ ≤ tree length;
  - mean width on flat pieces (EG 5.2/5.3);
  - submodularity;
  - joint convexity along geodesics (EG 3.3).
  An LP in the unknowns (d, δ(S), …) over these constraints could in principle exclude M5. The strategist's own table says "Untested systematically".
- **Corrected statement.** "No metric-only inequality valid in all CAT(0) spaces can exclude M5 or ρ_μ. Among the known necessary conditions this covers all except the crossing inequality B.3 (CAT(0)-validity conjectural, no violation found) and the conditions that involve diagonal or other non-wire tensors (not tested)."

## 9. Corrected statements, ready for a paper

**Theorem A.** Let k be a field of characteristic χ, and suppose the contracting hypothesis (AN Def. D.1) holds over k. Then the class X_χ (equivalently, by EG Thm 4.3, all spectral spaces of characteristic χ) admits ports in the sense of EG Def. 11.1. More precisely:
- for every sufficiently large multiple h of the constant u of AN Thm F.6, the Cayley graph of U_h(F₂) with generators 1 + E_{j,j+1} is a certificate in the sense of HC Thm 4.2;
- the certified family has degree 2(h−1).

*Proof.* Step 1: OA spectral metrics are AN prices (§1; for k ≠ prime field use EG Lemma 2.3). Step 2: F.6 gives β ≤ C₀(h−1). Step 3: HC Thm 4.2. In the Lean form, the `scalar` hypothesis holds because lines are prices.

**Corollary A′.** If contracting holds over ℚ (or any field of characteristic 0), then 3-SAT is decidable deterministically in 2^{O(v^{1−δ})}·poly (IM Thm 7.1, resting on HC Thm 13.1). Under variable-count Weak ETH, the contracting hypothesis fails over every field of characteristic 0, and then (AN D.2, Steps 2–7) √rk on Mat_μ(F₂) is an AN price over that field for every μ.

**Theorem B.** If for some μ ≥ 2 the metric √rk on Mat_μ(F₂), or the five-point metric M5, is not an AN price over ℚ, then the conclusion of Corollary A′ holds.
*Proof.* Restriction and diag pull-back give that ρ₃ is not a price. Then contracting holds at μ = 3 (D.2, Steps 2–7, which use failure at μ = 3 only), and Theorem A and IM 7.1 finish.
Converse form: under Weak ETH, these metrics are AN prices over ℚ. They are Strassen-spectral only if the [D] Prop. 11.2′ holds.

## 10. Open items for the executor

1. If Theorem A goes in a note, cite HC 4.2 from the paper rather than the Lean (because of the `scalar` hypothesis), or add the one line about lines being prices.
2. Re-check Prop. 11.2′ before using the Strassen-point version of B(iii).
3. Independent review of HC 13.1 / EG §§12–13 is the only route to making Corollary A′ more than conditional on OpenAI.
