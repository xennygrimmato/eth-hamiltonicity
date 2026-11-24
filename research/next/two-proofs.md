# Two proofs of VP ≠ VNP, side by side

24 Nov 2026. Sources:
- **[A]** Anthropic, *VP ≠ VNP over every field* (scratchpad `vpvnp/paper.txt`). Bound m^{c(log m)^{1/3}} = 2^{c(log m)^{4/3}}.
- **[O]** OpenAI, *VP and VNP are different*, November 23 edition (openai/math, `preprints/VP-and-VNP-are-different-November-23-2026/paper.pdf`,
  read via pdftotext). Bound exp(Ω((log n)^{5/4})). Lean scope note `lean/docs/379.md`: Lean proves only the exact (non-border),
  non-quantitative superpolynomial separation. The border bound and the 5/4 exponent are paper-only.
- Our notebooks: `research/vpvnp/{b1,b2,c1,c2}/notebook.md`.

Tags: [R] proved here (proof given or spelled out by citation); [K] known (section cited); [C] conjecture or unverified.

## 0. Verdict

1. **The dichotomies are different statements, and one implies the other.** [A]'s *flat* hypothesis implies [O]'s *rigid*
   hypothesis ("no strict shortening"). In fact it implies a stronger rigidity, where the selector costs 2√D·log A instead of
   2D·log A (Prop. 1). So [O]'s shortening case lies inside [A]'s contracting case. Combining them gives a three-way split:
   shortening ⊂ contracting, rigid ∧ contracting, and flat (⊂ rigid).
2. **No strict improvement on both papers.** The worst cell is *flat*. There [A] gives 4/3. [O] gives only 5/4, because
   flat ⇒ rigid and [O]'s stretch theorem needs a shortening, which then fails. So the best-of-both bound is [A]'s
   2^{c(log m)^{4/3}}. It does, however, transfer to [O]'s own family f_n, which improves [O]'s stated 5/4 to 4/3 there (Prop. 4).
3. **Both exponents come from one formula.** The two flat/rigid arguments are the same hub-rerouting argument. They differ only
   in what it costs to *name* a balanced cut: [O] pays D^{1} per named bit (a star selector), [A] pays D^{1/2} (the spectral
   exponent of the facet-centre set, Prop. E.9). With naming cost D^β per bit, the method gives exponent 1 + 1/(2+2β), which
   is 5/4 at β = 1 and 4/3 at β = 1/2 (Prop. 3). Prop. E.9's √D is optimal for [A]'s midpoint-convexity toolkit (Prop. 2). So
   beating 4/3 needs a new upper bound on g_φ(P), and b1's cap shows that even β = 0 would stop at 3/2.
4. **Neither paper decides the other's dichotomy.** [A]'s Lemma E.7 and Prop. E.9 decide one direction (flat ⇒ rigid). That
   gives c1's open problem a concrete new sufficient condition for *contracting*: a single finite tensor identity
   (Cor. 1′). Nothing in [O] breaks b1's k^{3/2} cap or c1's "toolkit cannot decide" result.

## 1. Side by side (Q1)

| | Anthropic [A] | OpenAI [O] |
|---|---|---|
| Dichotomy | Def. 2.1 / D.1, Thm D.2 (thm_alt). **Flat**: every finite Euclidean set is a *price* (a limit of c·d_φ, φ a spectral point: multiplicative, normalised, subadditive on covers). **Contracting**: ∃ μ ≥ 2, s² < μ, with D(μ) ≤ s·D(1) for all prices on Mat_μ(F₂). At least one holds over every field. Which one holds is unknown, and so is whether they exclude each other. | §2 Def. 2.1. **Strict shortening**: for some D ≥ 2, m, the tensor C_{D,m} (D width-m cables on the coordinate diameters of the unit ball) is a sum of A bit-tensor networks in the ball, each of Euclidean wire cost ≤ w, with w + 2D·log₂A < 2Dm (closure allowed). **Rigid** (my name for "no strict shortening", §2.1): none exists for any D, m over the algebraically closed field of that characteristic. The case split is the excluded middle. |
| Hard polynomial, case 1 | Flat: f_{k,ℓ}, the partition function of K_k with ℓ bits per edge (2.1). log m ≈ kℓ (Lemma E.3). | Rigid: partition function g of a bounded-degree expander on d ≈ a√log n vertices with m = ⌊c log n⌋ bits per edge. It is a projection of f_n (§2.1). |
| Hard polynomial, case 2 | Contracting: Φ = Σ_w U_t(w) y^w, the values of a universal weighted automaton (2.2). | Shortening: f_n itself (§1). Its coefficients c_x count accepting paths of a universal machine running the program in the prefix of x on input x. |
| Tensor / spectral tools | Spectral points (Zorn, Prop. A.5); wires ↦ q^{d_φ} (A.2); two-hub routing (A.3); duality (A.6); random points (A.8); crossing identity ⇒ CAT(0) (B.2, C.1, C.3); rank metric √rk ⇒ flat cube (D.2); GHZ cost via midpoints (E.7–E.9). | No spectral points. Euclidean wire cost of explicit networks; balanced-cut decomposition with 2^{O(d)} overhead; hub moved toward the resultant of the cut wires (§2.1); profile/selector juxtaposition (§2). |
| Diagonalisation | Contracting case only. Poincaré inequality → rerouting laws via duality → tree networks → cutting theorem (thm_cut). A small circuit gives an accelerator (lem_lowdeg). Constants are postponed by name, reduced to a finite field, and a self-applied program gives V = 1 + V (thm_noacc). | Shortening case only (Thm 3.1, the "stretch theorem"). The replay lemma 3.2 has a contraction replay every processor with the circuit substituted, saving wire iteratively on ribbon hosts (§6–9). The boundary lemma 3.3 realises border points through matrix weights (residues, Cartier operators, §4–5). Then e*Ω = 0, a contradiction. |
| Rate, case 1 | log L ≥ ℓk^{3/2}/16 for ℓ ≥ 100√k (Prop. E.10). With k = r², ℓ = 100r: **(log m)^{4/3}** (Thm E.11). | log s ≳ h ≳ m√(γd) = (log n)^{1+1/4}, under the constraint that the selector cost 2D·d = O(d²) stays below the saving, which is Θ(m) (§2.1). **(log n)^{5/4}**. |
| Rate, case 2 | 2^{c(log m)²/log log m} (Thm K.7). Limited by the (log v)^{O(a)} loss per cut. | **2^{n^σ}** (Thm 3.1): stretched exponential. |
| Overall | min = 4/3 (flat case) | min = 5/4 (rigid case) |
| Border, fields | k((ε)) approximation (Def. 1.3, Thm 1.4). All fields, via HC; PERM for char ≠ 2. | Zariski-closure border, even "approximation in degree n only". All fields; HC; PERM for char ≠ 2. |
| Effectivity | Flat-case constants are explicit. m₀ is ineffective (μ, s unknown). | Rigid case: explicit absolute constants. Shortening case: depends on the unknown identity. Overall ineffective. |

**Where each exponent comes from [R, recomputed from both papers].** Both case-1 arguments have the same form. Wires carry
ℓ bits (ℓ = m for [O]). For a balanced cut, the hub is displaced by η, which saves ℓ·(2η|R| − Nη²): R is the resultant of the
crossing ends and N the number of ends. The bridge then costs η·log L. This forces log L ≳ ℓ|R|. The saving has to pay for
naming the cut: V bits (the number of vertices), each charged G.
- [A]: |R| ≈ k^{3/2}, N ≈ k², saving ≈ ℓk, naming k·G with G = c·g_φ(ends) ≤ √k. So ℓ ≳ √k, log m ≈ kℓ ≳ k^{3/2}, and
  log L ≈ ℓk^{3/2} = √k·log m ≤ (log m)^{4/3}.
- [O]: |R| = √(γd), N ≈ d, saving ≈ ℓ, naming d·2D = Θ(d²). So ℓ ≳ d², log n ≈ ℓ, and log L ≈ ℓ√d ≤ (log n)^{5/4}.

## 2. The two dichotomies compared (Q2)

**Proposition 1 (flat ⇒ spectral rigidity) [R].** Let K be algebraically closed, and suppose [A]'s flat hypothesis holds over K.
Let C_{D,m} = Σ_{a=1}^{A} N_a, where each N_a is a bit-tensor network in the unit ball of Euclidean cost ≤ w (exactly, or in
the closure). Then

  **2Dm ≤ w + 2√D·log₂A.**

In particular, no strict shortening in the sense of [O] Def. 2.1 exists over K (since 2√D < 2D for D ≥ 2).

*Proof.*
1. *Setting.* Let V be the finite set of all node positions of all N_a, together with the 2D terminals P = {±e_i}. The points
   of P are the facet centres of [−1,1]^D.
2. *The spectral point.* By [A] Prop. E.9 (rescaled by 2), for every ε > 0 there are a spectral point φ on V and c ≥ 0 with
   |c·d_φ − ‖·‖| < ε on V and c·g_φ(P) ≤ 2√D + ε.
3. *Each network is a wire product.* N_a is a restriction of the product of its cables, viewed as wires ⟨2^{width}⟩ between
   node positions. Each node table acts as a linear map at its position: inner nodes contract to a functional, and terminal
   nodes are maps at P. So c·log φ(N_a) ≤ Σ width·(|xy| + ε) ≤ w + O(ε) ([A] Lemma A.2).
4. *The target.* log φ(C_{D,m}) = m·Σ_i d_φ(e_i, −e_i), so c·log φ(C) ≥ 2Dm − O(ε).
5. *The sum.* [A] Lemma E.7 gives φ(C) ≤ A^{g_φ(P)}·max_a φ(N_a). Its proof also works when each term additionally applies
   linear maps at the parties of P: the party that holds the word number applies the corresponding maps blockwise. Multiplying
   by c and letting ε → 0 gives the inequality.
6. *Closure.* For closure membership, [O] §2 turns the identity into an exact one at the t-th tensor power, with poly(t)·A^t
   terms of cost tw. Divide by t and let t → ∞.
7. *Strict shortening is excluded.* Suppose w + 2D·log A < 2Dm. Then 2D·log A < 2√D·log A. This is impossible if A ≥ 2, and
   if A = 1 it contradicts 2Dm ≤ w. □

**Corollary 1 [R].** In each characteristic: strict shortening (over K̄) ⇒ not flat over K̄ ⇒ contracting over K̄ ([A] Thm D.2).
So [O]'s stretch case is a sub-case of [A]'s contracting case, and [O]'s rigid case contains [A]'s flat case.

**Corollary 1′ (a new certificate for c1's question) [R].** By c1 Prop. 1, if ρ_μ = √rk is a price for every μ, then
contracting fails, so flat holds and Prop. 1 holds. So an exact identity C_{D,m} = Σ_{a≤A} N_a with w + 2√D·log A < 2Dm
(a "√D-shortening") proves that ρ_μ is *not* a price for some μ, and hence that the contracting hypothesis holds. This is
a finite object, so it can be checked by computer. It is weaker than what [O]'s stretch theorem needs (selector cost 2D). c1
§5 asked for exactly this kind of "new tensor identity".

**Converse direction [C].** By duality ([A] Thm A.6: covers with 2^{εN} terms) and c1's characterisation of prices by
covers, "not flat" gives a cheap asymptotic cover of the complete network on *some* Euclidean set, with selector cost
essentially zero. It does not give one of C_{D,m} with selector cost 2D. Whether contracting ⇒ strict shortening is open.
If it held, [A]'s contracting case would upgrade to 2^{n^σ}. That would not change the worst case, which is flat.

**Do the tools break c1's or b1's limits?**
- c1 (the toolkit of Sections A–D cannot decide flat vs contracting): unchanged. Prop. 1 uses Section E (E.7–E.9) and decides
  only one implication between the *two papers'* hypotheses. It does not decide either dichotomy. [O] decides nothing: its
  argument is the excluded middle on shortening.
- b1 (the hub method's ratio is capped at Λ_k ≈ k^{3/2}/3): [O]'s rigid case is the same hub method, on orthogonal
  diameters, so b1 Theorem A applies to it as well. [O] has no tool that raises the ratio.

## 3. Best of both (Q3)

The combined split, with the best available rate in each cell:

| cell | [A] | [O] | best |
|---|---|---|---|
| shortening (⊂ contracting) | (log m)²/log log m | 2^{n^σ} | **stretched exponential** |
| rigid ∧ contracting | (log m)²/log log m | (log n)^{5/4} | **(log m)²/log log m** |
| flat (⊂ rigid) | (log m)^{4/3} | (log n)^{5/4} | **(log m)^{4/3}** |

**Answer: there is no strict improvement on both papers.** The minimum over cells is [A]'s 2^{c(log m)^{4/3}}, because flat is
consistent with every known fact (c1 §4) and both papers are weakest there. What the combination does give:

**Proposition 4 (OpenAI's family at rate 4/3) [R by citation].** Over every field, f_n of [O] needs
2^{c'(log n)^{4/3}} gates. Proof: HC_m is a projection of f_n with n = m² + O(1). Fix a constant-length self-delimiting program
that checks deterministically (one accepting path, poly(m) ≤ n^{1000} steps) that the remaining bits are the adjacency matrix
of a directed Hamiltonian cycle, with forced zero padding. Then substitute Z_{i,b} = [b = prefix bit] on the prefix, Z_{i,0} = 1
and Z_{i,1} = X_{edge} on the matrix positions, and Z_{i,1} = 0 on the padding. Apply [A] Thm 1.1, with log m ≈ ½·log n. Border
version: [A] Thm 1.4. That [A]'s k((ε))-approximation matches [O]'s Zariski-closure border is [K] (Bürgisser 2004, cited
as [11] in [O]), but I have not checked it here.

**Proposition 2 (E.9 is optimal for its method) [R].** Let P = {±½e_i} ⊂ ℝ^k. Consider any bound on c·g_φ(P) obtained by
iterating [A] Lemma E.8 (midpoint convexity of c·g along pointwise midpoints of maps P → V), starting from maps f whose image
is spanned by a tree T_f, for which c·g ≤ len(T_f) by Lemma A.2. Every such bound is ≥ √k.

*Proof.*
1. *A linear functional.* Let Ψ(f) = Σ_{p∈P} f(p)·p. It is linear, so it passes exactly through midpoints.
2. *Value at the identity.* Ψ(id) = Σ|p|² = k/2.
3. *Bound on a leaf.* Since Σ_p p = 0, root T_f anywhere and write each f(p) − root as a sum of edge vectors. This gives
   Ψ(f) = Σ_{edges e} e·(Σ_{p beyond e} p) ≤ len(T_f)·M*, where M* = max_{X⊆P} |Σ_X p| = ½√k.
4. *Combine.* Hence id = Σ w_t f_t forces k/2 ≤ (½√k)·Σ w_t len(T_t), that is, Σ w_t len(T_t) ≥ √k. □

**Proposition 3 (unified exponent) [R for β ∈ {1/2, 1}; C in general].** Suppose the case-1 method has ratio |R| ≈ Δ√V or √E
(b1 Theorem A caps it at about √(V)·Δ), and naming costs D^β per named bit. Then, after optimising V, Δ and ℓ, the method gives
log L ≈ (log m)^{1 + 1/(2+2β)}.
- With [O]'s star selector (β = 1) this is 5/4.
- With [A]'s spectral GHZ (β = 1/2) it is 4/3. Under flat this holds for [O]'s expander too: naming V·√E and ℓ ≳ V^{3/2} give
  ℓ^{4/3}.
- With β = 0 it is 3/2, which is b1's cap.

So the gap between 5/4 and 4/3 is entirely the naming cost. Going past 4/3 in the flat case needs a spectral bound
c·g_φ(P) = o(√k), and Prop. 2 shows that this needs something beyond midpoint convexity.

## 4. Open questions stated in the papers (Q4)

| # | Source | Question | Our status |
|---|---|---|---|
| A1 | [A] §1.1, App. L | Is the exponent 1/3 optimal? "We do not know whether the bound in the flat case can be improved." | **Partly.** b1: the hub ratio is capped at ℓk^{3/2}/3 (Thm A [R], and in general Conj. C1). Prop. 2 here: E.9's naming cost is optimal for its method. b1 §4: f_{k,ℓ} has circuits of size 2^{O(ℓk²/√log k)}. The question itself is open. |
| A2 | [A] §2.1, D.3, L | Which case holds, even over ℝ? | **Reduced, not answered.** c1: it is equivalent to "is ρ_μ = √rk a price", and the toolkit cannot decide. New: a √D-shortening would prove contracting (Cor. 1′). |
| A3 | [A] §2.1, D.3, L | Are the two cases mutually exclusive? | **Answered negatively for the toolkit.** c1 §4: a model (Hilbert pull-backs) satisfies both, so the axioms cannot prove exclusivity. Truth unknown. |
| A4 | [A] App. L | Make m₀ effective; find values of μ and s. | Open. c2 records the ineffectivity. The flat case is effective; the contracting case is not. |
| A5 | [A] §1.2 | How does the proof relate to relativisation and algebrisation? | Not addressed in our notebooks. |
| A6 | [A] §1.2 | What does the bound give for PIT derandomisation? | **Answered by c2 §2.** Subexponential black-box hitting sets via KI04, in all characteristics except general circuits for p ≤ d (blocked by p-th roots, Andrews 2020). |
| A7 | [A] §3, Rem. N.6 | The dc consequence is not formalised in Lean. | c2 Cor. 6/6′ gives an explicit (paper-level) dc bound. Lean is still missing. |
| O1 | [O] §1 | No explicit module of equations or representation-theoretic obstruction is given. | Not addressed. |
| O2 | [O] §1 | Harder quasipolynomial questions (VNP vs VQP). | Open. c2 Cor. 7(c): PERM ∉ VQP_α for α < 4/3, and VNP ⊄ VQP remains open. |
| O3 | [O] §1 | No Boolean separation. | Outside scope. |
| O4 | [O] structure (implicit) | Does a strict shortening exist? | **Partly.** Not in the flat case (Prop. 1). Open in the contracting case. |
| O5 | `lean/docs/379.md` | Lean covers only exact superpolynomial; the border bound and 5/4 are unformalised. | Not addressed. |

## 5. What this opens up (next steps)

1. **[C] Test for √D-shortenings by computer.** Search small D for identities C_{D,m} = Σ N_a with w + 2√D·log A < 2Dm,
   for example from [A]'s crossing identity B.2 composed with itself. A hit would decide [A]'s dichotomy (contracting).
2. **[C] Spectral GHZ bound.** Is inf c·g_φ({±½e_i}) over flat-realising φ equal to Θ(√k) or O(1)? An O(1) bound would
   take the flat case, and hence the theorem, to (log m)^{3/2} (b1's cap). A lower bound Θ(√k) for *all* φ would show that
   4/3 is the limit of the balanced-set method.
3. **[C] Contracting ⇒ shortening?** This would make the second-worst cell stretched exponential. Low priority, because it
   does not move the minimum.
