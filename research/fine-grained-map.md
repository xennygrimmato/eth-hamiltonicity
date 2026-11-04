# The fine-grained landscape if the 2026 ETH refutations hold

4 Nov 2026. This note assumes the claimed refutations: Anthropic (**[A]**) and OpenAI (**[O]**), as
described in `anthropic-api.md` and in `quantum-note/main.tex` §1. The table format follows
`quantum-note/main.tex` §"Fine-grained supremacy statements" (Table `tab:conj`).

Tags:

* **[Lit]**: wording checked against the primary source (abstract or full text); the URL is in the row's
  "Verified against" column. Every row was re-checked on 4 Nov 2026 (second pass, see the changelog).
* **[Sec]**: the primary source could not be fetched; checked against a secondary source named in the row.
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
  (IPZ01, abstract and §1.1.4: SERF reductions keep the complexity parameter linear and allow
  poly(|x|)·2^{εn} time, so the number of edges is irrelevant; [A-txt] Cor. 7). A cardinality check |S| = s
  costs O(n) gates ([A-txt] Cor. 7 proof, citing IPZ01 proof of Thm 5).
  Counting versions follow when the encoding is parsimonious.
* **F4 (direction).** A lower bound "SAT ≤ X" is proved by a reduction *from* SAT *to* X. A fast SAT
  algorithm therefore says nothing about X. Faster algorithms arise only through F3, or through the
  general network theorems (H_A)/(H_O) that our own results use.

## 2. Table A: hypotheses

| # | Hypothesis (exact form, source) | Status | Reason | Faster algorithm? | Verified against |
|---|---|---|---|---|---|
| A1 | **ETH**: ∃δ>0, 3-SAT ∉ TIME(2^{δn}) (Impagliazzo–Paturi 2001) [Sec] | **refuted** | either engine | yes: 3-SAT/k-SAT in 2^{o(n)} | IP01 (doi 10.1006/jcss.2000.1727) not fetched; definition as quoted in [A-txt] l.1140–1146 and LMS https://arxiv.org/abs/1007.5450 p.2 (s_3 > 0) |
| A2 | **SETH**: ∀ε>0 ∃k, k-SAT ∉ TIME(2^{(1−ε)n}), i.e. s_∞ = 1 (IP01, named in CIP09; randomized allowed in CDLMNOPSW) [Lit] | **refuted** | F1; [O] suffices despite non-uniformity in k | yes, for each fixed k | https://arxiv.org/abs/1112.2275 (p.2: bounded-error randomized); [A-txt] l.1140–1151 |
| A3 | Density-SETH: CNF of any width with ≤ cn clauses needs 2^{(1−ε)n} (CIP06 duality; MT19a Conj. 2, deterministic decision) [Lit] | **refuted** | F2, counting form | yes | https://arxiv.org/abs/1901.01637 (Conj. 2, "at most cn clauses"); CIP06 not re-fetched |
| A4 | **CNF-SETH**: ∀ε, CNF-SAT ∉ 2^{(1−ε)n}·poly(m), clauses of unbounded width (the form used by LMS11, Pătraşcu–Williams 2010, Backurs–Indyk 2015, Bringmann 2014 "SETH′", Roditty–V.Williams 2013) [Lit] | **survives** | F2: needs m ≤ n·2^{o((log n)^{1/4}/√(log log n))}; poly(n) clauses are out of reach | no | https://arxiv.org/abs/1404.1448 (SETH′, p.2); https://arxiv.org/abs/1412.0348 (abstract) |
| A5 | Super-SETH (Vyas–Williams, SAT'19 / JAIR 2021): for every unbounded f, k-SAT ∉ 2^{n(1−f(k)/k)} (randomized) [Lit] | **refuted** | it implies SETH | — | https://people.csail.mit.edu/rrw/On_Super_Strong_ETH.pdf (p.1–2) |
| A6 | **#ETH** (DHMTW14, p. 21:5) [Lit] | **refuted** | [A] Cor. 6; [O] | yes: #3-SAT | https://arxiv.org/abs/1206.1775; [A-txt] Cor. 6 |
| A7 | #SETH / ⊕SETH for k-CNF (CDLMNOPSW Thm 1.3: ⊕SETH ⇔ k-⊕Hitting Sets ⇔ k-⊕Set Covers) [Lit] | **refuted** | F1 | yes | https://arxiv.org/abs/1112.2275 (Thm 1.3) |
| A8 | #CNF-SETH, ⊕CNF-SETH (poly(m) clauses) | **survives** | as A4 | no | as A4 (definitional) |
| A9 | **NSETH**: ∀ε ∃k, k-TAUT ∉ NTIME[2^{(1−ε)n}] (Carmosino–Gao–Impagliazzo–Mihajlin–Paturi–Schneider, ITCS 2016) [Lit] | **refuted** | a deterministic algorithm is a nondeterministic one ([A-txt] after Cor. 5) | — | https://eccc.weizmann.ac.il/report/2015/148; [A-txt] l.1166–1169 |
| A10 | NSETH for CNF with poly(m) clauses, or for poly-size circuits (MT19a Conj. 3) [Lit] | **survives** | as A4; note row 3 | no | https://arxiv.org/abs/1901.01637 (Conj. 3: poly-size circuits) |
| A11 | **MA-SETH / AM-SETH** | **refuted already in 2016** | Williams, CCC 2016: MA proofs running in c^n time, c < 2, for #SAT of sublinear-depth circuits (hence of CNFs); "strongly refute" MA- and AM-SETH (abstract) [Lit]; for k-CNF also by F1 | — | https://arxiv.org/abs/1601.04743 |
| A12 | **Gap-ETH**: ∃ε>0, no 2^{o(n)} algorithm (randomized allowed) distinguishes satisfiable 3-SAT from not-(1−ε)-satisfiable 3-SAT (Dinur 2016; Manurangsi–Raghavendra 2016; as quoted in Chalermsook et al. FOCS'17) [Lit] | **refuted** | an exact deterministic 2^{o(n)} decider distinguishes the two cases; Gap-ETH ⇒ ETH. Manurangsi's 2026 revision of arXiv 1611.05991 also records Gap-ETH as false | — | https://arxiv.org/abs/1708.04218 (abstract); https://arxiv.org/abs/1607.02986 |
| A13 | ETH for Circuit-SAT of **linear** size; VSP-Circuit-SAT of size cn (CDLMNOPSW Thm 1.1(v), equivalent to SETH) [Lit] | **refuted** | Tseitin gives O(n) variables | yes | https://arxiv.org/abs/1112.2275 (Thm 1.1(v)) |
| A14 | Circuit-SETH, NC-SETH, BP-SETH (Abboud–Hansen–V.Williams–Williams, STOC 2016) [Lit] | **survives** | superlinear-size representations | no | https://arxiv.org/abs/1511.06022 |
| A15 | FPT ≠ M[1]. M[1] is the closure under fpt-reductions of the "miniaturized" problem: a CNF (circuit) of size k·log n, parameter k (Downey–Thilikos §3.5). Chen–Grohe (CCC'06 / SICOMP'07) prove that miniaturization is an isomorphism mapping SUBEPT to FPT and the degree of 3-SAT (parameter n) to M[1]; hence **M[1] = FPT iff 3-SAT ∈ DTIME(2^{o^eff(n)}·poly)**, with an *effective* little-oh [Lit] | **refuted: M[1] = FPT** | the equivalence is an iff, but with o^eff. [A] (rate C·k²n log log n/√log n, C absolute) and [O] at k = 3 (one algorithm, rate O(n log log n/√log n)) each give an effective rate, so ETH fails in the required sense | yes (M[1]-complete problems, e.g. Mini-3-CNF-SAT, k·log n-Vertex Cover) | https://arxiv.org/abs/1106.3161 (§3.5); https://eccc.weizmann.ac.il/report/2006/011 (Intro, §2.1) |
| A16 | FPT ≠ W[1] | **survives** | ETH ⇒ W[1] ≠ FPT, not the converse; Chen–Grohe list "ETH ⇔ FPT ≠ W[1]?" (equivalently M[1] = W[1]?) as open | no | https://eccc.weizmann.ac.il/report/2006/011 (§6) |
| A17 | **OVC**, low dimension: ∀ε ∃c, OV with d = c log n ∉ n^{2−ε} (Williams 2005; GIKW "LDOVC") [Lit] | **survives, SETH support gone** | OVC follows from SETH via sparsification, but is not equivalent to it. [A]'s paper says explicitly that it does not refute OV ([A-txt] l.79) | no | [A-txt] l.79; https://arxiv.org/abs/1502.01063 (Lemma 2.1, via sparsification) |
| A18 | **Moderate-dimension OVC** (GIKW "MDOVC"): no randomized n^{2−ε}·poly(d) (TALG 2019) [Lit] | **survives, premise intact** | implied by CNF-SETH (A4) through Williams' split-and-list reduction with d = m = poly(n) (ABV15 Thm 3 / Lemma 1) | no | https://eccc.weizmann.ac.il/report/2016/053 (p.5, def. of LDOVC/MDOVC); https://arxiv.org/abs/1501.07053 (Thm 3, Lemma 1) |
| A19 | k-OV (low and moderate dimension) | **survives** | as A17/A18 [Inf] | no | as A17/A18 |
| A20 | Hitting Set conjecture (Abboud–V.Williams–Wang SODA 2016): no ε>0 such that for all c, HS with universe c log n in n^{2−ε} [Lit] | **survives** | not known to follow from SETH; implies OVC (their Prop. 2) | no | https://arxiv.org/abs/1506.01799 (§1, Prop. 2) |
| A21 | **Set Cover Conjecture**: ∀ε<1 ∃k, Set Cover with sets of size ≤ k ∉ 2^{εn}·poly(m), n = universe (CDLMNOPSW Thm 1.2) [Lit] | **survives** | not implied by SETH even before 2026. The natural witness has a variable per set (m ≤ n^k variables), or O(n log n) bits, so F3 gives nothing | no | https://arxiv.org/abs/1112.2275 (Thm 1.2) |
| A22 | k-Hitting Set, k-Set Splitting, k-NAE-SAT need 2^{(1−ε)n} for large k (CDLMNOPSW Thm 1.1, each equivalent to SETH) [Lit] | **refuted** | equivalent to SETH; also directly: they are k-CNFs on the n universe variables (IPZ01's "k-Set Cover" is k-Hitting Set and is SERF-complete) | yes, 2^{δn} for each k | https://arxiv.org/abs/1112.2275 (Thm 1.1); IPZ01 (abstract) |
| A23 | 3SUM conjecture (n^{2−o(1)}) | **survives** | unrelated to SAT; NSETH-based non-reducibility (A9) loses its premise, see B26 | no | — (no SAT premise) |
| A24 | APSP conjecture; (combinatorial) BMM; OMv | **survive** | unrelated | no | — |
| A25 | k-Clique (n^{ωk/3−ε}), Min-/Exact-/Zero-weight k-Clique | **survive** | unrelated to ETH-type statements | no | — |
| A26 | (ℓ,k)-Hyperclique hypothesis (ℓ > k > 2: ℓ-hyperclique in a k-uniform hypergraph needs n^{ℓ−o(1)}; Lincoln–V.Williams–Williams SODA 2018, Hyp. 1.4) [Lit] | **survives** | its refutation would give Max-k-SAT / degree-k CSPs with arbitrarily many constraints in 2^{(1−ε)n} (LVWW §1); that is the dense regime of A27, not touched. There is no converse from SAT | no | https://arxiv.org/abs/1712.08147 (Hyp. 1.4, §1) |
| A27 | Max-3-SAT (dense) not in 2^{(1−ε)n}; Max-2-SAT/Max-Cut not beating 2^{ωn/3} (folklore; the 2^{ωn/3} algorithm is Williams, TCS 2005) | **survive** | a counter over m = Θ(n²) clauses has Θ(n²) variables | no | Williams 2005, doi 10.1016/j.tcs.2005.09.023 (not re-fetched; algorithm only) |
| A28 | Subset Sum not in 2^{(1/2−ε)n} (meet-in-the-middle optimal) | **survives** | weights are not local | no | — (folklore conjecture) |
| A29 | basic QSETH (CNF-SAT, Buhrman–Patro–Speelman 2019); its k-CNF variant [Lit] | **survives / refuted** | `quantum-note` row 23 | — | https://arxiv.org/abs/1911.05686 |
| A30 | **PIH** (Lokshtanov–Ramanujan–Saurabh–Zehavi, SODA 2020) [Lit] | **survives, unproved again** | both known proofs, from Gap-ETH (A12) and from ETH (Guruswami–Lin–Ren–Sun–Wu, STOC'24 best paper), lose their premises | no | https://arxiv.org/abs/2311.16587 (abstract); https://arxiv.org/abs/1704.04249 |
| A31 | ETH for PPAD / End-of-a-Line (Rubinstein FOCS 2016) [Lit] | **survives** | a different, query-type hypothesis | no | https://arxiv.org/abs/1606.04550 |
| A32 | Feige's random 3-SAT and other average-case hypotheses | **survive** | about polynomial-time refutation | no | Feige STOC'02, doi 10.1145/509907.510000 (not re-fetched) |
| A33 | **Almost-ETH** (new): ∀γ>0, 3-SAT ∉ O(2^{n^{1−γ}}) (Manurangsi, arXiv 1611.05991 **v3, 27 Oct 2026**, Hyp. 3, proposed because of [O]) [Lit] | **survives** | [A] and [O] give 2^{n/(log n)^{Θ(1)}}, which is 2^{n^{1−o(1)}}, not 2^{n^{1−γ}} | no | https://arxiv.org/abs/1611.05991 (v3, §2.1) |

## 3. Table B: conditional lower bounds (theorems "H ⇒ X")

| # | Theorem (source) | Status | Reason | Faster algorithm? | Verified against |
|---|---|---|---|---|---|
| B1 | **Treewidth bounds**: no (2−ε)^{tw} IS, (3−ε)^{tw} DomSet, (2−ε)^{tw} Max-Cut, (3−ε)^{tw} OCT, (q−ε)^{tw} q-Col, (2−ε)^{tw} Partition into Triangles (Lokshtanov–Marx–Saurabh, SODA'11 / TALG'18) [Lit] | **survives** | the premise **as proved** is "SAT ∉ O*((2−δ)^n)" for unbounded-width CNF, O* hiding poly(input), i.e. CNF-SETH (A4), not k-SETH; they stress sparsification is not needed | **no**. No faster treewidth DP follows | https://arxiv.org/abs/1007.5450 (abstract, p.1–2, Thm 1) |
| B2 | Cut&Count pathwidth bounds (Cygan–Nederlof–Pilipczuk–Pilipczuk–van Rooij–Wojtaszczyk, FOCS'11, Thm 1.3 / App. D): no (3−ε)^{pw} CVC, FVS, Steiner Tree; no (4−ε)^{pw} CDS, CFVS, COCT; Exact k-Leaf Spanning Tree (pathwidth ≈ n/log 3, resp. n/2, in the constructions) [Lit] | **survive** | every reduction in App. D starts from "an instance Φ of SAT with n variables and m clauses" in polynomial time: CNF-SETH form. (Their Thm 1.4, ETH ⇒ no 2^{o(p log p)} Cycle Packing/Max Cycle Cover, loses its premise; see B21) | no | https://arxiv.org/abs/1103.0534 (Thm 1.3, App. D, Thms D.4–D.17) |
| B3 | Pătraşcu–Williams SODA'10: if k-DomSet ∈ O(n^{f(k)}) then CNF-SAT ∈ O*((m + k2^{n/k})^{f(k)}); so k-DomSet ∉ n^{k−ε} under CNF-SETH [Sec] | **survives** | CNF form | no | primary (SODA'10, doi 10.1137/1.9781611973075.86) not reachable (503 / TLS error at the author copy); statement as quoted in Roditty–V.Williams Thm 7 (https://www.cs.princeton.edu/courses/archive/spring13/cos528/RodittyWilliamsDiameter.pdf) and seminar notes https://kam.mff.cuni.cz/~dsemweb/0910/faster-sat-alg.pdf |
| B4 | Pătraşcu–Williams: d-Sum on N numbers of O(d log N) bits, d < N^{0.99}, in N^{o(d)} ⇒ 3-SAT in 2^{o(n)} [Sec] | **premise refuted** | conclusion open | no | seminar notes https://kam.mff.cuni.cz/~dsemweb/0910/faster-sat-alg.pdf (Thm 4); primary not reached |
| B5 | **Edit distance** ∉ n^{2−ε} (Backurs–Indyk STOC'15: else CNF-SAT ∈ M^{O(1)}2^{(1−ε)N}) [Lit] | **survives** | CNF form; also from NC-SETH (AHVW16) [Lit] | no | https://arxiv.org/abs/1412.0348 (abstract); https://arxiv.org/abs/1511.06022 |
| B6 | LCS, DTW: ABV FOCS'15 Thm 1 refutes their **Conjecture 1** (Most-Orthogonal Vectors with threshold r, no n^{2−ε}·poly(d)); k-LCS ∉ n^{k−ε}. Bringmann–Künnemann FOCS'15 (binary LCS, edit distance with any costs, 1-D DTW) are *stated* under k-SETH but proved from OVH (n^{2−ε}poly(d)) and UOVH (d ≤ n^{o(1)}), as they note [Lit] | **survive** | ABV Lemma 1: Conj. 1 follows from Max-CNF-SAT ∉ 2^{(1−ε)n}poly(m), which CNF-SETH implies; BK's OVH = MDOVC (A18) ⇐ CNF-SETH, and UOVH ⇐ CNF-SETH with d = m = poly(n). The k-SETH statement in BK loses its premise, the OVH one stands. BP-SETH too (AHVW16) | no | https://arxiv.org/abs/1501.07053 (Conj. 1, Thm 1, Lemma 1); https://arxiv.org/abs/1502.01063 (§2, Lemma 2.1 and remark after it) |
| B7 | Discrete and continuous Fréchet ∉ n^{2−ε}, no 1.001-approx in (nm)^{1−δ} (Bringmann FOCS'14) [Lit] | **survives** | stated directly from **SETH′**: "no O*((2−δ)^N) algorithm for CNF-SAT", O* hiding poly(N, M), i.e. CNF-SETH | no | https://arxiv.org/abs/1404.1448 (abstract, Thm 1.1–1.4) |
| B8 | Diameter: no (3/2−ε)-approximation in O(m^{2−ε}) for undirected unweighted graphs (Roditty–V.Williams STOC'13, Thm 1, via 2k-DomSet, Thm 8) [Lit]; later tradeoffs (k-OV based) unchecked | **survives** | Thm 1 is stated as "then CNF-SAT on n variables is in O*((2−δ)^n)", i.e. CNF-SETH | no | https://www.cs.princeton.edu/courses/archive/spring13/cos528/RodittyWilliamsDiameter.pdf (Thm 1, Thm 8); arXiv 1207.3622 |
| B9 | Dynamic problems under SETH (Abboud–V.Williams FOCS'14: #SSR, SubConn, SCC, ST-Reach, …) [Lit] | **survive** [Inf] | *stated* under k-SETH and proved through "k-SAT on O(n) clauses needs 2^{(1−γ)n}" (Prop. 1, via sparsification), which **is refuted** (F2: linear density). But the constructions only use one node per clause, so with m = poly(n) = polylog(N) clauses the same proof runs from CNF-SETH; the Triangle/BMM/3SUM-based bounds of the paper are untouched | no | https://arxiv.org/abs/1402.0054 (Conj. 3, §1 "Lower bounds based on the SETH", §7 Prop. 1) |
| B10 | Results that need d = c·log n exactly (low-dimension OVC only) | **premise refuted** if stated "under SETH"; **survive** under OVC | A17 | no | as A17 |
| B11 | CDLMNOPSW Thm 1.2 under SeCoCo: Steiner Tree ∉ 2^{εt}poly, CVC ∉ 2^{εt}poly, Set Partitioning ∉ 2^{εn}poly(m), Subset Sum ∉ t^{ε}poly(n) [Lit] | **survive** | premise A21 intact | no | https://arxiv.org/abs/1112.2275 (Thm 1.2) |
| B12 | **Subset Sum** ∉ T^{1−ε}2^{o(n)} (Abboud–Bringmann–Hermelin–Shabtay, SODA'19 / TALG'22; reduces from k-SAT) [Lit] | **premise refuted** | conclusion open; the T^{1−ε}poly(n) form survives under SeCoCo (B11) | no | https://arxiv.org/abs/1704.04546 (abstract) |
| B13 | **ETH ⇒ no 2^{o(n)} for IS, Clique, VC, k-Col, DomSet on n vertices, any density** (IPZ01: SERF-complete with parameter n; LMS11 survey) [Lit] | **refuted (concl.)** | [A-txt] Cor. 7: for every δ, deterministic O(2^{δn}), any number of edges, and counts of independent sets / cliques / vertex covers / dominating sets of each size s and of proper k-colorings (fixed k). Decision for IS/Clique/VC/k-Col from IPZ01 Thms 3–5; DomSet and counts are new in [A] | **yes**; beats Xiao–Nagamochi 1.1996^n (MIS), Beigel–Eppstein (3-Col), etc. | paper.txt l.1191–1223; IPZ01 https://khoury.northeastern.edu/~viola/classes/papers/ImpagliazzoPaturiZane01Which.pdf (abstract, §1.1) |
| B14 | ETH ⇒ k-VC ∉ 2^{o(k)}poly(n) (Cai–Juedes, JCSS 2003) | **refuted (concl.)** [Inf] | correct: the LP/crown kernel gives ≤ 2k vertices in poly time; Cor. 7 on it costs 2^{2δk}, so for every δ, 2^{δk} + poly(n). A *single* 2^{o(k)}poly(n) algorithm also exists: the O(k)-variable 3-CNF of Cor. 7's proof, run through [A]'s explicit n-bound (or [O] at k = 3) | **yes**: 2^{o(k)}+poly | paper.txt Cor. 7; Cai–Juedes doi 10.1016/S0022-0000(03)00074-6 (not re-fetched) |
| B15 | ETH ⇒ no 2^{o(n)} Max-Cut / Max-k-SAT (fixed k) with m = O(n) constraints (folklore: linear-size reductions from 3-SAT) | **refuted (concl.)** [Inf] | **Unweighted (or O(1)-bit integer weights) only, from the Main Theorem alone**: n variables, one indicator per constraint (O(1) clauses, forced, so parsimonious), an O(m)-gate adder of the m indicators and a comparison with t, Tseitin: a 3-CNF with O(n) variables whose models are the assignments of value exactly t. [A] Cor. 6 counts them for each t: exact optimum and the number of solutions of each value in 2^{δn}. No Kronecker weights are needed or available here (the Main Theorem counts, it does not weigh). Weights up to W cost O(m log W) gates, so W = poly(n) gives O(n log n) variables: not covered; that needs the network theorem (H_A) with Kronecker weights as in `tsp-theorem.md` §2.2, conditional | **yes**, exact, deterministic, 2^{δn}; dense cases: A27 | paper.txt Cor. 6 (l.1176–1190), Cor. 7 proof (l.1202–1207); `tsp-theorem.md` §2.2, §5.2 |
| B16 | ETH ⇒ no 2^{o(n)} HC/HP, TSP (poly weights), Steiner, FVS, CVC, CDS, Max-Leaf **on sparse graphs** (LMS11 Thm 3.3 and folklore) | **refuted (concl.)**, conditional on (H_A) | ours: `sharp-eth-catalogue.md` rows 7, 7′; `meta-theorem.md` | yes (ours). On dense graphs: premise refuted | internal |
| B17 | #ETH Tutte/permanent/#IS (DHMTW TALG'14; Curticapean ICALP'15; Brand–Dell–Roth IPEC'16) [Lit] | **mixed** | refuted (concl.): DHMTW (a), #2-SAT on n variables and #IS on n vertices, any density ([A] Cor. 6/7); sparse permanent, #PM, Boolean #CSP, integer H_q, T(x,1) (ours). Premise refuted: dense permanent and the rest (`sharp-eth-catalogue.md` §1–2) | partly | https://arxiv.org/abs/1206.1775 (abstract (a)–(c)); https://arxiv.org/abs/1511.02910 |
| B18 | Quantum-supremacy ETH/SETH statements (MT19–20, HNS18–19, DHKL20) | **5 refuted, 6 premise refuted, rest survive** | `quantum-note` Table `tab:conj` | yes: 2^{O(G/√log G)} exact amplitudes | internal; https://arxiv.org/abs/1901.01637 (Conj. 2, 3 re-checked) |
| B19 | Chen–Huang–Kanj–Xia (JCSS 2006): ETH ⇒ k-Clique ∉ f(k)n^{o(k)} [Sec] | **premise refuted** | 2^{δn} does not contradict the bound at small k | no | doi 10.1016/j.jcss.2006.04.007 (abstract via indexers only) |
| B20 | Marx (ToC 2010): ETH ⇒ binary CSP / PSI ∉ f(k)n^{o(k/log k)}; Curticapean–Marx FOCS'14: ETH ⇒ #k-matching in bipartite graphs ∉ f(k)n^{o(k/log k)}, hence #k-path likewise [Lit] | **premise refuted** | | no | https://arxiv.org/abs/1407.2929 (abstract); Marx ToC 6 (2010) not re-fetched |
| B21 | LMS SODA'11 / SICOMP'18 "slightly superexponential": ETH ⇒ no 2^{o(d log d)} Closest String, Distortion, Disjoint Paths by tw, etc.; Cygan et al. Thm 1.4 (no 2^{o(p log p)} Cycle Packing); ETH ⇒ no 2^{o(tw)} bounds [Lit] | **premise refuted** | | no | https://arxiv.org/abs/1902.08723; https://arxiv.org/abs/1103.0534 (Thm 1.4) |
| B22 | ETH ⇒ 2^{o(√n)} lower bounds for planar problems; 2^{Ω(n^{1−1/d})} for fat-object intersection graphs (de Berg–Bodlaender–Kisfaludi-Bak–Marx–van der Zanden, STOC'18) and for Euclidean TSP (de Berg–Bodlaender–Kisfaludi-Bak–Kolay, FOCS'18) [Lit] | **premise refuted** | the refutations give only 2^{n/polylog}, which is worse. Under Almost-ETH (A33) the same reductions give 2^{n^{1/2−γ}}-type bounds [Inf] | no | https://arxiv.org/abs/1803.10633 (abstract); https://arxiv.org/abs/1807.06933 (title/abstract) |
| B23 | **Gap-ETH ⇒ FPT inapproximability** of k-Clique, k-DomSet, Balanced Biclique, induced matching, DkS (Chalermsook et al. FOCS'17 / SICOMP'20) [Lit] | **premise refuted** | **partially re-proved** under W[1] ≠ FPT (surviving): constant-factor k-Clique (Lin STOC'21; Karthik–Khot CCC'22), any-F(k) k-DomSet (Karthik–Laekhanukit–Manurangsi STOC'18). The k^{o(1)} k-Clique bound (Lin–Ren–Sun–Wang ICALP'22) and KLM's n^{o(k)} bound use ETH: premise refuted. Biclique / induced matching / DkS: no W[1]-based re-proof found | no | https://arxiv.org/abs/1708.04218; https://arxiv.org/abs/2102.04769; https://arxiv.org/abs/1711.11029; https://arxiv.org/abs/2304.07516 (abstract summary) |
| B24 | ETH-hardness of approximation: Dinur–Manurangsi ITCS'18 (2-CSP to |V|^{1−o(1)}, Directed Steiner Network k^{1/4−o(1)}); Manurangsi STOC'17 (DkS); Braverman–Ko–Weinstein SODA'15 (poly-time ε-approx best Nash ⇒ SAT in 2^{Õ(√n)}, i.e. n^{Ω̃(log n)} under ETH); Aaronson–Impagliazzo–Moshkovitz CCC'14 (dense CSP / free games need n^{(log n)^{1−o(1)}}) [Lit] | **mixed** | **Manurangsi re-proved under Almost-ETH (A33) in v3 (27 Oct 2026): no poly-time 2^{(log n)^{1−ε}}-approximation of DkS, with perfect completeness: survives.** The original ETH/Gap-ETH ratios n^{1/(log log n)^c}, n^{o(1)} lose their premise (footnote 3 of v3). DM, BKW, AIM: premise refuted, conclusions open; their quasi-polynomial reductions plausibly give weaker n^{(log n)^{1−δ}}-type bounds under Almost-ETH, as Manurangsi notes for BKRW17 [Inf] | no | https://arxiv.org/abs/1805.03867; https://arxiv.org/abs/1611.05991 (v3); https://eccc.weizmann.ac.il/report/2014/092; https://arxiv.org/abs/1401.6848 |
| B25 | GLRSW STOC'24: ETH ⇒ PIH; follow-up GLRSW 2024 (almost optimal f(k)n^{o(k)}-type lower bounds for approximating k-Clique / CSP under ETH) [Lit] | **premise refuted** | A30 | no | https://arxiv.org/abs/2311.16587; https://arxiv.org/abs/2404.08870 |
| B26 | Carmosino et al.: NSETH ⇒ no deterministic fine-grained reduction from SAT to 3SUM, APSP, or first-order model checking [Lit] | **premise refuted** | the barrier is lifted; no reduction follows | no | https://eccc.weizmann.ac.il/report/2015/148 (abstract) |
| B27 | **Williams 2013 Thm 6.1 / JMV15: ETH false ⇒ E^NP has no linear-size circuits** ([A-txt] l.1171–1175) [Lit] | **conclusion now holds** | the conditional fires: an *unconditional* circuit lower bound, given the refutations. CGIMPS16 also say that disproving NSETH gives new circuit lower bounds [Lit] | n/a | paper.txt l.1171–1175; https://arxiv.org/abs/1311.3171; https://eccc.weizmann.ac.il/report/2015/148 |

## 4. Where the refutations *do* give algorithms (F3 and the network theorems)

Main theorem only (Lean-checked top level):

* k-SAT, #k-SAT, ⊕k-SAT, k-TAUT.
* CNF of any width with O(n) clauses (F2).
* Linear-size Circuit-SAT.
* IS, Clique, VC, DomSet and k-Coloring on n vertices at any density, with counts by size ([A-txt] Cor. 7); #2-SAT and #IS (DHMTW (a)).
* k-Hitting Set, k-NAE-SAT, k-Set Splitting.
* Max-k-SAT and Max-Cut with O(n) constraints, unweighted or O(1)-bit weights, exact, and counting by value [Inf] (B15).
* Sparse permanent, #PM, Boolean #CSP, integer Potts/flow hyperbolas.
* Parameterized: k-VC in 2^{o(k)} + poly(n); M[1] = FPT.

General network theorems (H_A)/(H_O) (ours, not formalised):

* #HC/HP on sparse graphs, TSP with poly weights, Steiner, FVS, CVC, CDS, Max-Leaf.
* T(x,1) (forests).
* Exact quantum amplitudes in 2^{O(G/√log G)}.
* Weighted problems whose weights would make a counter superlinear (e.g. sparse Max-Cut with poly(n) weights, via Kronecker weights).

**No algorithm follows** for:

* anything parameterised by treewidth or pathwidth;
* problems in P (edit distance, LCS, Fréchet, diameter, OV, 3SUM, APSP, k-Clique);
* Set Cover by universe size;
* Subset Sum;
* dense Max-CSP;
* dense HC;
* planar problems.

## 5. Headline counts and surprises

**Counts.** 60 rows in all (A33 added in the second pass).

| | Table A (33 rows) | Table B (27 rows) | Total |
|---|---|---|---|
| Refuted | 12 (A1–A3, A5–A7, A9, A11–A13, A15, A22) | — | 12 |
| Refuted (concl.) | — | 4 (B13–B16) | 4 |
| Conclusion now holds | — | 1 (B27) | 1 |
| Premise refuted | — | 10 (B4, B10, B12, B19–B23, B25, B26) | 10 |
| Survives | 20 (A4, A8, A10, A14, A16–A21, A23–A28, A30–A33) | 9 (B1–B3, B5–B9, B11) | 29 |
| Split / mixed | 1 (A29) | 3 (B17, B18, B24) | 4 |

**Surprises.**

1. **LMS treewidth bounds survive**, and so do the Cut&Count pathwidth bounds. Both reduce from CNF-SAT with m clauses in polynomial time [Lit], so their premise is CNF-SETH, which is not refuted.
2. **The best-known "SETH-hard" problems in P survive with an intact premise.** Backurs–Indyk (edit distance), Bringmann (Fréchet) and Roditty–V.Williams (diameter) are *stated* from CNF-SAT with poly(m) clauses. ABV's LCS/DTW bound is stated from Most-OV with poly(d), which Max-CNF-SAT hardness implies. Bringmann–Künnemann and Abboud–V.Williams (dynamic) are stated under k-SETH, but their proofs go through OVH / one node per clause and so run from CNF-SETH. What actually dies is "k-SETH ⇒ low-dimension OVC" and anything that really needs sparsification.
3. **Gap-ETH is refuted**, so the Gap-ETH FPT-inapproximability programme loses its premise. PIH reverts to an unproved hypothesis, since its ETH proof (STOC'24 best paper) also goes. The parts re-proved under W[1] ≠ FPT survive: constant-factor k-Clique (Lin) and any-ratio k-DomSet (KLM).
4. **Almost-ETH is already in use.** Manurangsi's v3 (27 Oct 2026) moves DkS hardness to "3-SAT ∉ 2^{n^{1−γ}}", which survives both engines.
5. **M[1] = FPT.** Chen–Grohe's iff needs an effective o(n); both engines supply one.
6. **E^NP ⊄ SIZE(O(n)) becomes unconditional** (Williams 2013).
7. **Real algorithmic fallout:**
   * deterministic 2^{δn} Max-IS, 3-Col and DomSet at any density, with counts by size;
   * 2^{o(k)} + poly(n) Vertex Cover (2k kernel, then Cor. 7);
   * exact sparse unweighted Max-Cut / Max-k-SAT, with counts by value.
8. **The CNF-SAT frontier is sharp in a funny way.** [A]'s uniformity reaches density 2^{o((log n)^{1/4}/√(log log n))} [Inf].
   [O]'s O_k constants give only constant density explicitly.

## 6. Sources

The per-row "Verified against" column is authoritative. Primary sources fetched on 4 Nov 2026:

* LMS treewidth https://arxiv.org/abs/1007.5450; Cut&Count https://arxiv.org/abs/1103.0534.
* CDLMNOPSW https://arxiv.org/abs/1112.2275; Backurs–Indyk https://arxiv.org/abs/1412.0348; ABV https://arxiv.org/abs/1501.07053; Bringmann–Künnemann https://arxiv.org/abs/1502.01063; Bringmann https://arxiv.org/abs/1404.1448; Roditty–V.Williams (course copy) https://www.cs.princeton.edu/courses/archive/spring13/cos528/RodittyWilliamsDiameter.pdf; Abboud–V.Williams https://arxiv.org/abs/1402.0054; AHVW16 https://arxiv.org/abs/1511.06022; GIKW https://eccc.weizmann.ac.il/report/2016/053; AVWW https://arxiv.org/abs/1506.01799; LVWW https://arxiv.org/abs/1712.08147.
* IPZ01 (JCSS 63:512–530, doi 10.1006/jcss.2001.1774): read through the course copy https://khoury.northeastern.edu/~viola/classes/papers/ImpagliazzoPaturiZane01Which.pdf (the doi PDF still fails; direct curl fails TLS, fetched via a reader service). Abstract, §1.1–§3 start (Thm 1, Cor. 1, Cor. 2) checked.
* Downey–Thilikos https://arxiv.org/abs/1106.3161; Chen–Grohe https://eccc.weizmann.ac.il/report/2006/011.
* Chalermsook et al. https://arxiv.org/abs/1708.04218; Lin https://arxiv.org/abs/2102.04769; KLM https://arxiv.org/abs/1711.11029; GLRSW https://arxiv.org/abs/2311.16587, https://arxiv.org/abs/2404.08870; Dinur–Manurangsi https://arxiv.org/abs/1805.03867; Manurangsi v3 https://arxiv.org/abs/1611.05991; BKW https://eccc.weizmann.ac.il/report/2014/092; AIM https://arxiv.org/abs/1401.6848; Rubinstein https://arxiv.org/abs/1606.04550; PIH https://arxiv.org/abs/1704.04249.
* NSETH https://eccc.weizmann.ac.il/report/2015/148; Williams MA https://arxiv.org/abs/1601.04743; Vyas–Williams https://people.csail.mit.edu/rrw/On_Super_Strong_ETH.pdf; DHMTW https://arxiv.org/abs/1206.1775; MT19a https://arxiv.org/abs/1901.01637; QSETH https://arxiv.org/abs/1911.05686; ABHS https://arxiv.org/abs/1704.04546; JMV https://arxiv.org/abs/1311.3171.
* Anthropic paper text (`.../scratchpad/anth/fm/paper.txt`): l.60–80, l.1140–1223 (Cor. 5–7, circuit remark).
* **Not reached** (rows marked [Sec]): Pătraşcu–Williams SODA'10 (author copy 503 / TLS failure), IP01, Chen–Huang–Kanj–Xia JCSS'06, Cai–Juedes, Marx ToC'10, CIP06, Williams TCS'05, Feige STOC'02.

## 7. Changelog (second pass, 4 Nov 2026)

* **All rows:** added "Verified against" column; removed every [Lit?] tag; [Sec] marks the four rows whose primary source could not be fetched (A1, B3, B4, B19).
* **A3, A5, A6, A10, A20, A26, A31:** [Lit?]/untagged → [Lit] after checking the primary. A5 statement made exact (2^{n(1−f(k)/k)}, f unbounded).
* **A11:** Williams' MA result restated from the abstract (c^n, c<2, sublinear-depth circuits), not "O*(2^{n/2}) bounded depth".
* **A15:** definition of M[1] and the exact Chen–Grohe iff (effective little-oh) added; [O] at k=3 also suffices. Status unchanged.
* **A16:** source added (Chen–Grohe list ETH ⇔ FPT≠W[1] as open).
* **A21, A22:** reasons sharpened (O(n log n)-bit witness; IPZ01's k-Set Cover = k-Hitting Set).
* **A23:** cross-reference corrected from B22 to B26.
* **A26:** reason was wrong ("would give 3-SAT faster than 2^n"); LVWW's consequence is Max-k-SAT/CSPs with many constraints. Status unchanged.
* **A27:** attribution fixed (Williams 2005 is the algorithm; the bound is folklore).
* **A33 (new):** Almost-ETH, from Manurangsi's v3 (27 Oct 2026); survives.
* **B2:** "survive if CNF form" → **survive**: every reduction in Cygan et al. App. D is from CNF-SAT with m clauses; Thm 1.4 moved to B21.
* **B3, B4:** exact Pătraşcu–Williams forms (k-DomSet ⇒ CNF-SAT in (m+k2^{n/k})^{f(k)}; d-Sum with d < N^{0.99}, O(d log N) bits); secondary-only.
* **B6:** reason corrected: ABV is from Most-OV (Conj. 1), not plain OV; BK is stated under k-SETH but proved from OVH/UOVH.
* **B7, B8:** [Inf] removed: both are stated directly from CNF-SAT (Bringmann's SETH′; RVW Thm 1). Later diameter tradeoffs flagged as unchecked.
* **B9:** reason rewritten: as stated the proof uses k-SETH + sparsification to O(n) clauses (refuted by F2); survives only via the CNF-SETH re-derivation [Inf].
* **B13:** Cor. 7 statement made exact; IPZ01 verified (parameter n, poly(|x|) factor allowed).
* **B14:** inference confirmed and stated precisely (2k kernel → 2^{2δk}; a single 2^{o(k)} algorithm via the explicit rate); premise source (Cai–Juedes) added.
* **B15:** restricted to unweighted / O(1)-bit weights; the "Kronecker weights" alternative removed from the Main-Theorem route (the Main Theorem counts, it does not weigh); poly weights need (H_A), cf. `tsp-theorem.md` §2.2.
* **B17:** DHMTW (a) (#2-SAT, #IS on n vertices, any density) added to the refuted-conclusion part.
* **B20:** Curticapean–Marx is #k-matching in bipartite graphs (n^{o(k/log k)}), with #k-path as a consequence.
* **B21:** LMS SICOMP'18 list made exact; Cut&Count Thm 1.4 added.
* **B22:** citation fixed: Euclidean TSP is de Berg–Bodlaender–Kisfaludi-Bak–Kolay FOCS'18; arXiv 1803.10633 is the intersection-graph framework.
* **B23:** re-proofs made exact (Lin; Karthik–Khot; KLM W[1] part vs. ETH part; LRSW k^{o(1)} under ETH).
* **B24:** **premise refuted → mixed**: Manurangsi's DkS bound is re-proved under Almost-ETH (v3) and survives; BKW and AIM statements made exact.
* **B25:** follow-up identified (arXiv 2404.08870).
* **§4, §5:** counts rewritten (60 rows: refuted 12, refuted (concl.) 4, conclusion holds 1, premise refuted 10, survives 29, mixed 4); surprises 2–5 rewritten.
