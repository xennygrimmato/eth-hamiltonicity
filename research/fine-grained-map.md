# The fine-grained landscape if the 2026 ETH refutations hold

4 Nov 2026. This note assumes the claimed refutations: Anthropic (**[A]**) and OpenAI (**[O]**), as
described in `anthropic-api.md` and in `quantum-note/main.tex` §1. The table format follows
`quantum-note/main.tex` §"Fine-grained supremacy statements" (Table `tab:conj`).

Tags:

* **[Lit]**: wording checked today against the primary source (abstract or full text, links in §6).
* **[Lit?]**: recalled or taken from a secondary source; theorem numbers are not re-checked.
* **[Inf]**: our own inference.
* **[A-txt]**: stated in Anthropic's paper text (`paper.txt` l.55–100, l.1140–1230).

## 0. What the two engines give, and how uniform they are in k

* **[A] (Main Theorem / Thm D).** #k-SAT in 2^{C·min(km/√log m, k² n log log n/√log n)}, deterministic,
  with C absolute. The n-bound is subexponential while k ≤ c(log n)^{1/4}/√(log log n) (`sat-width.md` §5.1).
  The m-bound is subexponential when km = o(m√log m), i.e. when k = o(√log m).
* **[O].** For **each fixed k**: (n+m)^{O_k(1)}·2^{O_k(n log log n/√log n)} bit operations and polynomial space,
  and 2^{O_k(ρ(n))} with ρ = n(log log n)²/√log n in the interpolation form. When m ≤ Dn the bound is 2^{O_{k,D}(n/√log n)}.
  **No k-dependence is stated** (`sat-width.md` §4). So [O] is not known to be uniform in k.
* **Uniformity does not matter for SETH.** SETH is the statement s_∞ = lim_k s_k = 1. Each engine gives
  s_k = 0 for every fixed k, so both refute SETH. Uniformity matters only for formulas whose width grows
  with n (§1, F2).

**Status labels** (as in the quantum note). The two engines are assumed throughout.

* **Refuted**: the statement itself is false.
* **Refuted (concl.)**: a conditional theorem "H ⇒ X" whose *conclusion* X is now contradicted by an explicit algorithm.
* **Premise refuted**: H is false, but nothing here contradicts X.
* **Survives**: we know of no consequence of the refutations that touches the statement. This includes
  conditional theorems whose premise still stands.

## 1. Four facts used throughout

* **F1 (s_k = 0 for every k).** This kills ETH, SETH, Super-SETH, #ETH, #SETH, ⊕SETH and NSETH in
  their **k-CNF forms** ([A-txt] Cor. 5, Cor. 6, and the NSETH remark after Cor. 5).
* **F2 (the width/density frontier).** The counting width reduction is `quantum-note` Lemma `lem:width`:
  2^{sn}·exp(2^{−sk}(m+n/k)).
  * *Linear density.* With fixed k it gives #CNF-SAT, of **any width**, with m ≤ cn clauses in 2^{εn} for
    every ε, using either engine (`quantum-note` Cor. `cor:density`).
  * *Slightly superlinear density, [A] only* [Inf]. Take [A]'s uniform bound at k = Θ(√σ(log n)^{1/4}/√(log log n)),
    so that the exponent per variable is s(k) ≤ σ. Then #CNF-SAT with m ≤ n·2^{o((log n)^{1/4}/√(log log n))}
    clauses runs in 2^{o(n)}.
  * *Beyond that.* For m = n^{1+Ω(1)}, or for m = n·2^{(log n)^{1/4+Ω(1)}}, nothing follows.
    The m-route 2^{km/√log m} is useless at m = n², and the n-route needs k = O((log n)^{1/4}).
  * **Conclusion: "CNF-SETH", that CNF-SAT is not in 2^{(1−ε)n}·poly(m), survives.** Many famous lower bounds
    are in fact proved from CNF-SETH (§3).
* **F3 (where algorithms do follow).** Take any problem with complexity parameter n whose yes-instances
  have an O(n)-bit witness that can be checked by an O(n)-gate circuit, or by bounded-width clauses over
  O(n) variables. It gets deterministic 2^{δn} for every δ > 0. This is the SERF / Tseitin route
  (IPZ01; [A-txt] Cor. 7). A cardinality check |S| = s costs O(n) gates ([A-txt] Cor. 7 proof).
  Counting versions follow when the encoding is parsimonious.
* **F4 (direction).** A lower bound "SAT ≤ X" is proved by a reduction *from* SAT *to* X. A fast SAT
  algorithm therefore says nothing about X. Faster algorithms arise only through F3, or through the
  general network theorems (H_A)/(H_O) that our own results use.

## 2. Table A: hypotheses

| # | Hypothesis (exact form, source) | Status | Reason | Faster algorithm? |
|---|---|---|---|---|
| A1 | **ETH**: ∃δ>0, 3-SAT ∉ TIME(2^{δn}) (Impagliazzo–Paturi 2001) [Lit] | **refuted** | either engine | yes: 3-SAT/k-SAT in 2^{o(n)} |
| A2 | **SETH**: ∀ε>0 ∃k, k-SAT ∉ TIME(2^{(1−ε)n}), i.e. s_∞ = 1 (IP01, named in CIP09; randomized allowed in CDLMNOPSW) [Lit] | **refuted** | F1; [O] suffices despite non-uniformity in k | yes, for each fixed k |
| A3 | Density-SETH: CNF of any width with ≤ cn clauses needs 2^{(1−ε)n} (CIP06 duality; MT19 Conj. 2) | **refuted** | F2, counting form | yes |
| A4 | **CNF-SETH**: ∀ε, CNF-SAT ∉ 2^{(1−ε)n}·poly(m), clauses of unbounded width (the form used by LMS11, Pătraşcu–Williams 2010, Backurs–Indyk 2015) [Lit] | **survives** | F2: needs m ≤ n·2^{o((log n)^{1/4}/√(log log n))}; poly(n) clauses are out of reach | no |
| A5 | Super-SETH (Vyas–Williams 2021: k-SAT not in 2^{(1−ω(1/k))n}) [Lit?] | **refuted** | it implies SETH | — |
| A6 | **#ETH** (DHMTW14, p. 21:5) [A-txt] | **refuted** | [A] Cor. 6; [O] | yes: #3-SAT |
| A7 | #SETH / ⊕SETH for k-CNF (CDLMNOPSW Thm 1.3 uses ⊕SETH) [Lit] | **refuted** | F1 | yes |
| A8 | #CNF-SETH, ⊕CNF-SETH (poly(m) clauses) | **survives** | as A4 | no |
| A9 | **NSETH**: ∀ε ∃k, k-TAUT ∉ NTIME[2^{(1−ε)n}] (Carmosino–Gao–Impagliazzo–Mihajlin–Paturi–Schneider, ITCS 2016) [Lit] | **refuted** | a deterministic algorithm is a nondeterministic one ([A-txt] after Cor. 5) | — |
| A10 | NSETH for CNF with poly(m) clauses, or for poly-size circuits (MT19a Conj. 3) | **survives** | as A4; note row 3 | no |
| A11 | **MA-SETH / AM-SETH** for k-CNF | **refuted already in 2016** | Williams, CCC 2016: an MA proof of size O*(2^{n/2}) for #SAT of bounded-depth circuits [Lit]; trivially also by F1 | — |
| A12 | **Gap-ETH**: ∃ε>0, no 2^{o(n)} algorithm (randomized allowed) distinguishes satisfiable 3-SAT from not-(1−ε)-satisfiable 3-SAT (Dinur 2016; Manurangsi–Raghavendra 2016; as quoted in Chalermsook et al. FOCS'17) [Lit] | **refuted** | an exact deterministic 2^{o(n)} decider distinguishes the two cases; Gap-ETH ⇒ ETH | — |
| A13 | ETH for Circuit-SAT of **linear** size; VSP-Circuit-SAT of size cn (CDLMNOPSW Thm 1.1, equivalent to SETH) [Lit] | **refuted** | Tseitin gives O(n) variables | yes |
| A14 | Circuit-SETH, NC-SETH, BP-SETH (Abboud–Hansen–V.Williams–Williams, STOC 2016) [Lit] | **survives** | superlinear-size representations | no |
| A15 | FPT ≠ M[1] (equivalent to ETH; Downey–Thilikos survey arXiv 1106.3161, after Chen–Grohe) [Lit] | **refuted: M[1] = FPT** | [A] gives a single algorithm with an explicit o(n) rate, as the equivalence needs | yes (M[1]-complete problems) |
| A16 | FPT ≠ W[1] | **survives** | ETH ⇒ W[1] ≠ FPT, not the converse | no |
| A17 | **OVC**, low dimension: ∀ε ∃c, OV with d = c log n ∉ n^{2−ε} (Williams 2005; Abboud et al.) | **survives, SETH support gone** | OVC follows from SETH via sparsification, but is not equivalent to it. [A]'s paper says explicitly that it does not refute OV ([A-txt] l.79) | no |
| A18 | **Moderate-dimension OVC**: no n^{2−ε}·poly(d) (GIKW, TALG 2019) [Lit] | **survives, premise intact** | still implied by CNF-SETH (A4) through Williams' split-and-list reduction (d = m) [Inf] | no |
| A19 | k-OV (low and moderate dimension) | **survives** | as A17/A18 | no |
| A20 | Hitting Set conjecture (Abboud–V.Williams–Wang SODA 2016) [Lit?] | **survives** | independent; implies OVC | no |
| A21 | **Set Cover Conjecture**: ∀ε<1 ∃k, Set Cover with sets of size ≤ k ∉ 2^{εn}·poly(m), n = universe (CDLMNOPSW Thm 1.2) [Lit] | **survives** | not implied by SETH even before 2026. The natural witness has a variable per set (m ≤ n^k variables), so F3 gives nothing | no |
| A22 | k-Hitting Set, k-Set Splitting, k-NAE-SAT need 2^{(1−ε)n} for large k (CDLMNOPSW Thm 1.1, each equivalent to SETH) [Lit] | **refuted** | equivalent to SETH; also directly by F3 | yes, 2^{δn} for each k |
| A23 | 3SUM conjecture (n^{2−o(1)}) | **survives** | unrelated to SAT; NSETH-based non-reducibility (A9) loses its premise, see B22 | no |
| A24 | APSP conjecture; (combinatorial) BMM; OMv | **survive** | unrelated | no |
| A25 | k-Clique (n^{ωk/3−ε}), Min-/Exact-/Zero-weight k-Clique | **survive** | unrelated to ETH-type statements | no |
| A26 | ℓ-uniform Hyperclique hypothesis (ℓ ≥ 3; Lincoln–V.Williams–Williams SODA 2018) [Lit?] | **survives** | n^{k−ε} would give 3-SAT faster than 2^n, which is now known anyway; there is no converse | no |
| A27 | Max-3-SAT (dense) not in 2^{(1−ε)n}; Max-2-SAT/Max-Cut not beating 2^{ωn/3} (Williams 2005) | **survive** | a counter over m = Θ(n²) clauses has Θ(n²) variables | no |
| A28 | Subset Sum not in 2^{(1/2−ε)n} (meet-in-the-middle optimal) | **survives** | weights are not local | no |
| A29 | basic QSETH (CNF-SAT, Buhrman–Patro–Speelman 2019); its k-CNF variant | **survives / refuted** | `quantum-note` row 23 | — |
| A30 | **PIH** (Lokshtanov et al. 2020) | **survives, unproved again** | both known proofs, from Gap-ETH (A12) and from ETH (Guruswami–Lin–Ren–Sun–Wu, STOC'24 best paper) [Lit], lose their premises | no |
| A31 | ETH for PPAD / End-of-a-Line (Rubinstein FOCS 2016) [Lit?] | **survives** | a different, query-type hypothesis | no |
| A32 | Feige's random 3-SAT and other average-case hypotheses | **survive** | about polynomial-time refutation | no |

## 3. Table B: conditional lower bounds (theorems "H ⇒ X")

| # | Theorem (source) | Status | Reason | Faster algorithm? |
|---|---|---|---|---|
| B1 | **Treewidth bounds**: no (2−ε)^{tw} IS, (3−ε)^{tw} DomSet, (2−ε)^{tw} Max-Cut, (3−ε)^{tw} OCT, (q−ε)^{tw} q-Col, (2−ε)^{tw} Partition into Triangles (Lokshtanov–Marx–Saurabh, SODA'11 / TALG'18, arXiv 1007.5450) [Lit] | **survives** | the premise **as proved** is "SAT ∉ (2−ε)^n·m^{O(1)}", i.e. CNF-SETH (A4), not k-SETH | **no**. No faster treewidth DP follows |
| B2 | Cut&Count-era pathwidth bounds (Cygan et al. 2011, e.g. Steiner Tree, CVC, FVS) and related SETH bounds by pathwidth [Lit?] | **survive if CNF form** | most such reductions use CNF-SAT with m clauses; check case by case | no |
| B3 | Pătraşcu–Williams SODA'10: k-DomSet ∉ n^{k−ε} unless CNF-SAT ∈ 2^{(1−δ)n}poly(m) [Lit?] | **survives** | CNF form | no |
| B4 | Pătraşcu–Williams: ETH ⇒ k-SUM ∉ n^{o(k)} [Lit?] | **premise refuted** | conclusion open | no |
| B5 | **Edit distance** ∉ n^{2−ε} (Backurs–Indyk STOC'15: else CNF-SAT ∈ M^{O(1)}2^{(1−ε)N}) [Lit] | **survives** | CNF form; also from NC-SETH (AHVW16) [Lit] | no |
| B6 | LCS (Abboud–Backurs–V.Williams FOCS'15; Bringmann–Künnemann FOCS'15), DTW [Lit?] | **survive** | through OV with poly(d) blow-up, hence moderate-dimension OVC ⇐ CNF-SETH; BP-SETH too (AHVW16) | no |
| B7 | Discrete Fréchet ∉ n^{2−ε} (Bringmann FOCS'14) [Lit?] | **survives** [Inf] | OV-based with poly(d) blow-up, so it holds under A18 | no |
| B8 | Diameter: no (3/2−ε)-approximation in m^{2−ε} (Roditty–V.Williams STOC'13), and the later tradeoffs [Lit?] | **survives** [Inf] | the graph has m = O(nd) edges, so polylog d suffices (A18) | no |
| B9 | Dynamic problems under SETH (Abboud–V.Williams FOCS'14) [Lit?] | **survive** [Inf] | the same OV route; spot-check any bound whose blow-up is exponential in d | no |
| B10 | Results that need d = c·log n exactly (low-dimension OVC only) | **premise refuted** if stated "under SETH"; **survive** under OVC | A17 | no |
| B11 | CDLMNOPSW Thm 1.2 under SeCoCo: Steiner Tree ∉ 2^{εt}poly, CVC ∉ 2^{εt}poly, Set Partitioning ∉ 2^{εn}poly(m), Subset Sum ∉ t^{ε}poly(n) [Lit] | **survive** | premise A21 intact | no |
| B12 | **Subset Sum** ∉ T^{1−ε}2^{o(n)} (Abboud–Bringmann–Hermelin–Shabtay, SODA'19 / TALG'22; reduces from k-SAT) [Lit] | **premise refuted** | conclusion open; the T^{1−ε}poly(n) form survives under SeCoCo (B11) | no |
| B13 | **ETH ⇒ no 2^{o(n)} for IS, Clique, VC, k-Col, DomSet on n vertices, any density** (IPZ01; LMS11 survey) | **refuted (concl.)** | [A-txt] Cor. 7: deterministic 2^{δn}, counts included | **yes**; beats Xiao–Nagamochi 1.1996^n (MIS), Beigel–Eppstein (3-Col), etc. |
| B14 | ETH ⇒ k-VC ∉ 2^{o(k)}poly(n) | **refuted (concl.)** [Inf] | 2k-vertex kernel, then B13 | **yes**: 2^{o(k)}+poly |
| B15 | ETH ⇒ no 2^{o(n)} Max-Cut / Max-k-SAT with m = O(n) constraints (bounded-degree versions) [Lit?] | **refuted (concl.)** [Inf] | clause indicators plus an O(m)-gate counter give an O(n)-variable 3-CNF; Kronecker weights or the counter count by value | **yes**, exact, deterministic, 2^{δn}; dense cases: A27 |
| B16 | ETH ⇒ no 2^{o(n)} HC/HP, TSP (poly weights), Steiner, FVS, CVC, CDS, Max-Leaf **on sparse graphs** (LMS11 Thm 3.3 and folklore) | **refuted (concl.)**, conditional on (H_A) | ours: `sharp-eth-catalogue.md` rows 7, 7′; `meta-theorem.md` | yes (ours). On dense graphs: premise refuted |
| B17 | #ETH Tutte/permanent (DHMTW TALG'14; Curticapean ICALP'15; Brand–Dell–Roth IPEC'16) [Lit] | **mixed** | refuted (concl.): sparse permanent, #PM, Boolean #CSP, integer H_q, T(x,1) (ours). Premise refuted: the rest (`sharp-eth-catalogue.md` §1–2) | partly |
| B18 | Quantum-supremacy ETH/SETH statements (MT19–20, HNS18–19, DHKL20) | **5 refuted, 6 premise refuted, rest survive** | `quantum-note` Table `tab:conj` | yes: 2^{O(G/√log G)} exact amplitudes |
| B19 | Chen–Huang–Kanj–Xia: ETH ⇒ k-Clique ∉ f(k)n^{o(k)} [Lit?] | **premise refuted** | 2^{δn} does not contradict the bound at small k | no |
| B20 | Marx: ETH ⇒ subgraph iso / PSI ∉ f(k)n^{o(k/log k)}; Curticapean–Marx #k-path [Lit?] | **premise refuted** | | no |
| B21 | LMS SODA'11 "slightly superexponential" (no 2^{o(k log k)}) and ETH ⇒ no 2^{o(tw)} bounds | **premise refuted** | | no |
| B22 | ETH ⇒ 2^{o(√n)} lower bounds for planar problems; 2^{n^{1−1/d}} for Euclidean TSP (de Berg et al.) | **premise refuted** | the refutations give only 2^{n/polylog}, which is worse | no |
| B23 | **Gap-ETH ⇒ FPT inapproximability** of k-Clique, k-DomSet, Balanced Biclique, induced matching, DkS (Chalermsook et al. FOCS'17 / SICOMP'20) [Lit] | **premise refuted** | **partially re-proved** under W[1] ≠ FPT (surviving): constant-factor k-Clique (Lin STOC'21), k-DomSet (Karthik–Laekhanukit–Manurangsi STOC'18) [Lit?] | no |
| B24 | ETH-hardness of approximation: Dinur–Manurangsi ITCS'18 (2-CSP, Directed Steiner Network); Manurangsi STOC'17 (DkS ratio n^{1/(log log n)^c}); Braverman–Ko–Weinstein SODA'15 (best ε-Nash n^{Ω̃(log n)}); Aaronson–Impagliazzo–Moshkovitz (free games) [Lit?] | **premise refuted** | conclusions open | no |
| B25 | GLRSW STOC'24: ETH ⇒ PIH, and the 2^{o(k)} follow-up [Lit] | **premise refuted** | A30 | no |
| B26 | Carmosino et al.: NSETH ⇒ no deterministic fine-grained reduction from SAT to 3SUM, APSP, or first-order model checking [Lit] | **premise refuted** | the barrier is lifted; no reduction follows | no |
| B27 | **Williams 2013 Thm 6.1 / JMV15: ETH false ⇒ E^NP has no linear-size circuits** ([A-txt] l.1171–1175) | **conclusion now holds** | the conditional fires: an *unconditional* circuit lower bound, given the refutations. CGIMPS16 also says that refuting NSETH gives new circuit lower bounds [Lit] | n/a |

## 4. Where the refutations *do* give algorithms (F3 and the network theorems)

Main theorem only (Lean-checked top level):

* k-SAT, #k-SAT, ⊕k-SAT, k-TAUT.
* CNF of any width with O(n) clauses (F2).
* Linear-size Circuit-SAT.
* IS, Clique, VC, DomSet and k-Coloring on n vertices at any density, with counts ([A-txt] Cor. 7).
* k-Hitting Set, k-NAE-SAT, k-Set Splitting.
* Max-k-SAT and Max-Cut with O(n) constraints, exact, and counting by value [Inf].
* Sparse permanent, #PM, Boolean #CSP, integer Potts/flow hyperbolas.
* Parameterized: k-VC in 2^{o(k)}; M[1] = FPT.

General network theorems (H_A)/(H_O) (ours, not formalised):

* #HC/HP on sparse graphs, TSP with poly weights, Steiner, FVS, CVC, CDS, Max-Leaf.
* T(x,1) (forests).
* Exact quantum amplitudes in 2^{O(G/√log G)}.
* Weighted problems whose weights would make a counter superlinear.

**No algorithm follows** for:

* anything parameterised by treewidth;
* problems in P (edit distance, LCS, OV, 3SUM, APSP, k-Clique);
* Set Cover by universe size;
* Subset Sum;
* dense Max-CSP;
* dense HC;
* planar problems.

## 5. Headline counts and surprises

**Counts.** 59 rows in all.

| | Table A (32 rows) | Table B (27 rows) | Total |
|---|---|---|---|
| Refuted | 12 (A1–A3, A5–A7, A9, A11–A13, A15, A22) | — | 12 |
| Refuted (concl.) | — | 4 (B13–B16) | 4 |
| Conclusion now holds | — | 1 (B27) | 1 |
| Premise refuted | — | 11 (B4, B10, B12, B19–B26) | 11 |
| Survives | 19 (A4, A8, A10, A14, A16–A21, A23–A28, A30–A32) | 9 (B1–B3, B5–B9, B11) | 28 |
| Split / mixed | 1 (A29) | 2 (B17, B18) | 3 |

**Surprises.**

1. **LMS treewidth bounds survive.** They are proved from CNF-SETH with m^{O(1)} clauses [Lit], so their premise is not refuted.
2. **Most "SETH-hard" problems in P survive with an intact premise:** Backurs–Indyk, LCS, Fréchet, diameter.
   They go through OV with poly(d) blow-up, hence they need only moderate-dimension OVC, which CNF-SETH implies.
   What actually dies is "k-SETH ⇒ low-dimension OVC".
3. **Gap-ETH is refuted**, so the whole Gap-ETH FPT-inapproximability programme loses its premise.
   PIH reverts to an unproved hypothesis, since its ETH proof (STOC'24 best paper) also goes.
   Only the parts re-proved under W[1] ≠ FPT survive.
4. **M[1] = FPT.**
5. **E^NP ⊄ SIZE(O(n)) becomes unconditional** (Williams 2013).
6. **Real algorithmic fallout:**
   * deterministic 2^{δn} Max-IS, 3-Col and DomSet at any density;
   * 2^{o(k)} Vertex Cover;
   * exact sparse Max-Cut/Max-k-SAT.
7. **The CNF-SAT frontier is sharp in a funny way.** [A]'s uniformity reaches density 2^{o((log n)^{1/4}/√(log log n))} [Inf].
   [O]'s O_k constants give only constant density explicitly.

## 6. Sources checked today

* LMS treewidth: https://arxiv.org/abs/1007.5450 (premise: SAT ∉ (2−ε)^n m^{O(1)}).
* CDLMNOPSW, *On problems as hard as CNF-SAT*: https://ar5iv.arxiv.org/html/1112.2275 (SETH form, Thm 1.1–1.3, SeCoCo).
* Backurs–Indyk: https://arxiv.org/abs/1412.0348.
* AHVW16 (NC-SETH, BP-SETH): https://arxiv.org/abs/1511.06022.
* NSETH (CGIMPS16): https://eccc.weizmann.ac.il/report/2015/148.
* Williams, MA-SETH: https://arxiv.org/abs/1601.04743.
* Chalermsook et al. (Gap-ETH definition): https://arxiv.org/abs/1708.04218.
* GLRSW, PIH under ETH: https://arxiv.org/abs/2311.16587.
* ABHS, Subset Sum: https://arxiv.org/abs/1704.04546.
* GIKW (moderate-dimension OV): https://eccc.weizmann.ac.il/report/2016/053.
* FPT ≠ M[1] ⇔ ETH: Downey–Thilikos, https://arxiv.org/abs/1106.3161.
* IPZ01 SERF-completeness: https://doi.org/10.1006/jcss.2001.1774 (the PDF returned HTTP 503; the statement is taken from secondary summaries and [A-txt] Cor. 7).
* Anthropic paper text: Cor. 5–7 and the circuit lower bound remark. OpenAI .tex: via `sat-width.md` §4.
* Everything tagged [Lit?] is still to be checked against the primary source.
