# Literature and novelty check for the ports / contracting notes

*26 November 2026. Scope: claims A–E as specified in the request. Notes checked: `note-contracting-eth.md` (v2),
`note-k23-rate.md`, `../mm/lab/notebook.md`, `middle/notes.md`.*

**Tools.** Web search and fetch worked: Exa search/fetch, WebFetch, and `curl` + `pdftotext` for arXiv and GitHub PDFs.
GitHub's API was not available for the labs' repositories, so issues and commits were read from the public HTML pages.

**Tags used below.**
- **[read]**: I opened the primary source and read the passage.
- **[snippet]**: seen only in a search-engine excerpt of the source.
- **[recall]**: from memory, not re-checked today.

**Bottom line.**
- **A.** No public statement of claim A was found, and no retraction by either lab. One serious overlap must be cited:
  OpenAI's own EG §11.1 (Lemma 11.3 ⇒ Proposition 11.2) proves "a uniform contracting gap on the F₂-Grassmannian ⇒
  ports". This is the mechanism of our Theorem A, under a different hypothesis.
- **B.** No prior statement found of the K_{2,3} tensor rate, of 3/√10, or of 6/(4+√10). The instance is the classical
  Okamura–Seymour example. There, classical network coding is known to equal routing (3/4). So the gap we claim is
  tensor restriction versus coding as well as routing, which strengthens the note, and it must be cited.
- **C.** "Unrestricted MC(⟨2,2,2⟩ over F₂) = 7" appears to be open in public. One public (unrefereed, machine-generated)
  register states 6 ≤ MC ≤ 7 as of 4 September 2026 and calls 6-versus-7 open. Our lower bound 6 is therefore not new;
  the value 7 would be new.
- **D.** The Lubotzky–Zelmanov attribution is correct. Whether "Hadamard expanders" exist is a stated open problem.
  Several known results bear directly on §5 of `middle/notes.md` and must be cited: Naor–Silberman, Naor's comparison
  paper, Izeki–Kondo–Nayatani and Toyoda all cover bounded rank.
- **E.** Toyoda's theorem is confirmed, but the title in our references is wrong. It fails at six points (Lebedeva).

No SendMessage was triggered. There is no public statement of A or B before us, and no retraction or correction of the
relevant papers was found (details in A.4).

---

## A. "Contracting ⇒ fast 3-SAT", and the link to OpenAI's ports

### A.1 Primary sources: existence, and exact wording [read]

- **[AN]** Claude (Anthropic), "VP ≠ VNP over every field".
  - Paper: https://raw.githubusercontent.com/anthropics/formal-math/main/vp-vnp/paper.pdf. Also on Hexagon as
    hexagon:2611.00954v1 (https://hexagonmath.org/2611.00954v1, v1 of 23 Nov 2026, the only version), and on alphaXiv
    (https://www.alphaxiv.org/abs/2611.vp-vnp-arithmetic-lower-bounds).
  - One commit touches `vp-vnp`: 918c8e2, 23 Nov 2026, "vp-vnp: VP != VNP, paper and Lean proof". No later commit.
  - Wording checked against our quotes in pdftotext:
    - "We do not show that the two cases exclude each other" (D.3);
    - "its F₂ is not the field k";
    - "The exponent 1/3 comes from the flat case alone";
    - "Sections A to L use nothing about k except that it is a field";
    - "…except for the guesses, and every choice in the formula is guessed exactly once";
    - "The proofs in this paper were found and written by AI. No human mathematician has checked the proofs."
  - p. 6 uses different wording: "We do not know which of the two hypotheses holds, even over R, nor do we show that the
    two are mutually exclusive."
  - **[AN] says nothing about SAT, ETH or algorithmic consequences of either case.** Its only statement in that
    direction is §2.5: "Nor can a large Boolean circuit take the place of the program that the contracting case
    refutes, since we know no way to run it faster than gate by gate." So our "which the paper does not mention" is
    accurate.
- **OpenAI release of 24 Nov 2026** (commit 92b516e, merged 25 Nov as PR #6). History:
  https://raw.githubusercontent.com/openai/math/main/history.md. Papers read:
  - EG: …/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/paper.pdf;
  - HC: …/Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026/paper.pdf;
  - IM: …/The-logarithmic-exponent-of-integer-multiplication-on-tapes-November-24-2026/paper.pdf;
  - MM: …/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf.
- **Verbatim checks.** These all match our quotations: EG Def. 11.1 (and the sentence "This property depends only on the
  characteristic"); HC Thm 4.2; IM Thm 7.1. IM adds, which our note does not say, that variable-count Weak ETH "is
  equivalent to the Stearns–Hunt hypothesis for CNF satisfiability [41, Theorem 2.4]". It also says that the October
  subexponential algorithms "refute the original Exponential Time Hypothesis … and are compatible with this weaker
  assumption".

### A.2 The closest prior work, and a substantive overlap with Theorem A [read]

**OpenAI EG §11.1, Lemma 11.3 and Proposition 11.2** (EG pp. 55–58 in our pdftotext).

- **Lemma 11.3.** Fix a power of two m > ℓ and put W = F₂^{2m}. Let B_r be the mean squared distance between
  m-dimensional subspaces U, V with dim(U+V) = m + r, for any map of the Grassmannian into a complete CAT(0) spectral
  space over F. Then there is η > 0 with B_m ≤ (m − η)B₁, uniformly.
  - The proof is the same quadrilateral averaging as [AN] D.2. If equality held in the limit, a Euclidean cube Q_ℓ would
    sit in the space, which the maximal-flat hypothesis forbids.
- **Proposition 11.2.** "If a finite field F has a largest spectral flat dimension k, then F has ports." Its proof
  (§§11.1.2–11.1.3) uses only the conclusion of Lemma 11.3:
  - random linear maps W → E give sparse matrices;
  - then a Reingold–Vadhan–Wigderson replacement product;
  - then Mendel–Naor nonlinear spectral calculus.
- **Why this matters.** Lemma 11.3 is OpenAI's own "contracting" inequality, on Gr(m, 2m) instead of the big cell
  Mat_m(F₂). [AN]'s Mat_μ(F₂) embeds in Gr(μ, 2μ) by graphs, with dim(Γ_a + Γ_b) = μ + rk(a − b). So EG §11 already
  contains **"a uniform contracting gap on F₂-linear configurations ⇒ ports"**. This is the bridge in our Theorem A,
  reached by a different route (Grassmannian gap plus zig-zag, instead of [AN] F.6 on U_h plus HC Thm 4.2).
- **Our inference, unrefereed.** [AN]'s contracting inequality at μ probably implies EG's Grassmannian gap at m = μ for
  [AN]-prices:
  - average the cell inequality over g ∈ GL_{2μ}(F₂);
  - pull back a Grassmannian price along a ↦ gΓ_a;
  - GL acts transitively on pairs of a given sum dimension.
  If so, EG §§11.1.2–11.1.3 gives a second proof of Theorem A. The power-of-two requirement on m needs checking.
- **What OpenAI does not state.** OpenAI never states that [AN]'s contracting hypothesis implies ports, nor that it
  implies anything about 3-SAT. Its use of Prop. 11.2 sits inside the proof by contradiction of EG Thm 1.2 (flats exist
  in every dimension over every field). The sole reference to Anthropic in EG is "The crossing construction originates
  in work of Anthropic [12]" ([12] is Anthropic's ETH paper, hexagon 2610.00577). HC and IM likewise cite only that
  paper.

Other related items:
- **ETH refuted (claimed), October 2026.** These are not prior art for A, but the notes are silent about them:
  - Anthropic, "A 2^{o(n)} time algorithm for 3-SAT", 26 Oct 2026,
    https://raw.githubusercontent.com/anthropics/formal-math/main/eth/paper.pdf (hexagon 2610.00577) [read: abstract
    and §§1, 7];
  - OpenAI, "The Exponential Time Hypothesis is False", 17/25 Oct 2026,
    https://raw.githubusercontent.com/openai/math/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf
    [read: abstract and Theorem 1.1].
  Both run in time 2^{n/(log n)^{1/2+o(1)}}, which is consistent with Weak ETH. OpenAI's history.md says a working group
  led by Impagliazzo, Paturi and Williams is reviewing OpenAI's paper.
- **arXiv:2610.41622** (30 Oct 2026), "Lowered crossover points of Anthropic's subexponential 3-SAT algorithm"
  [snippet].
  - It defines a "rewrite-and-merge" class containing Anthropic's ETH recursion.
  - It proves that for two balanced homogeneous merges the exponent per edge bit is ≥ (log₂K)^{−3}, "which excludes
    running times 2^{n^{1−c}}" within that class.
  - This is not a contradiction: our algorithm is a different (cut-and-enumerate) engine. But it is a published barrier
    against power-saving SAT algorithms of the ETH-paper type, and should be mentioned.
- **arXiv:2611.11832** (Strassle–Subercaseaux, 8 Nov 2026): subexponential deterministic simulation of nondeterministic
  time from the October SAT algorithms [snippet]. Not relevant to A beyond context.

### A.3 Public discussion since 23–24 November 2026: none relates contracting to algorithms or to ports

| Venue | URL | Date | What is said |
|---|---|---|---|
| Shtetl-Optimized (Aaronson) | https://scottaaronson.blog/?p=10362 | 24 Nov | Both proofs "look similar … compression … followed … by a diagonalization". Nothing on the cases. Comments up to #54 (25 Nov) mention the ETH refutation; none on the flat/contracting or ports cases [read] |
| Computational Complexity (Fortnow) | https://blog.computationalcomplexity.org/2026/11/vp-vnp.html | 24 Nov | "uses a variant of Strassen's asymptotic spectrum to split into two cases, one handled by a rank argument and the other by a diagonalization". 13 comments; none on the cases, ETH or SAT [read] |
| Gil Kalai | https://gilkalai.wordpress.com/2026/11/24/… | 24 Nov | Pointer post [snippet] |
| Hacker News | https://news.ycombinator.com/item?id=50620102 (also 50624296, 50632756) | 23–25 Nov | General: P vs NP, Lean. A blind restatement check: https://github.com/2opremio/vp-vnp-statement-check. Nothing on the cases [read, main thread] |
| MathOverflow | https://mathoverflow.net/questions/518140 (24 Nov), https://mathoverflow.net/questions/518197 (25 Nov) | 24–25 Nov | Zorn's lemma / constructivity; "implications of VP ≠ VNP". Nothing on the cases [read, snippets of answers] |
| GitHub anthropics/formal-math issues | #55 (24 Nov), #57 (26 Nov), #52, #53 | 23–26 Nov | #57 asks for clarification of Lemma K.3 (clause polynomial versus displayed word sum) and of zero-weight runs in Prop. I.1 ("exposition", not errors in the main results). #55 is off-topic. None touches D.1, D.2, J.3/J.4 or SAT [read] |
| GitHub openai/math | issues page | — | 0 issues. Commits since 23 Nov: e07100d/f570285 (23–24 Nov), 92b516e/3344da5 (24–25 Nov); no withdrawal or correction [read] |
| alphaXiv (AN page) | link above | 25 Nov | One comment (W. D. Smith) claiming the bound transfers to Boolean circuits; off-topic [read] |
| Hexagon (AN) | link above | — | No comments; v1 only [read] |
| Press, aggregators, trackers | interestingengineering, officechai, datastudios, mlq.ai, vibemathlab.com (status page, 24 Nov 23:30 PT), postcutoff.com, kingy.ai, traictory, maccus.fr, sysnote | 23–26 Nov | All describe the flat/contracting split as "neither lab knows which case holds". OfficeChai and datastudios note the two labs' similar architecture ("strict shortening" versus "flat/contracting"). **None claims an algorithmic consequence or relates contracting to ports** [read/snippet] |
| Tao blog/Mastodon, Lipton–Regan, cstheory.SE, Lean Zulip | — | — | **Nothing found.** No hit in web search. I did not log into Zulip, and Mastodon was not searched directly |

**Verdict for A.**
- **Theorem R** (contracting ⇒ power-saving 3-SAT via [AN]'s cutting theorem plus the guess count): **new as far as
  public sources show**. Confidence: high that no one has posted it; medium that no expert sees it as immediate.
- **Theorem A** (contracting ⇒ ports): **partially anticipated** by EG §11.1 (Grassmannian gap ⇒ ports). The specific
  statement about [AN]'s hypothesis is new. Confidence medium-high.
- **Corollary 1** (Weak ETH ⇒ flat hypothesis via ¬contracting): new as a statement. Confidence medium-high.
- **Contradicted?** No. Nothing claims contracting or ports to be proved or refuted. EG Thm 1.2 (flats in every
  dimension) gives [AN]'s flat hypothesis outright but does not touch contracting, as the note already says.

### A.4 Retractions or corrections

None found:
- [AN]: one commit, v1 only.
- openai/math history.md: the last entry is 24 Nov, and its only withdrawals are of 7 Oct and concern Hodge-conjecture
  papers.
- Anthropic issue #57 (26 Nov) is an exposition request on K.3/I.1, not a correction.

### A.5 Changes to `note-contracting-eth.md`

1. **§0 or §4, add after Theorem A:** "OpenAI's EG proves the analogous implication on its side. EG Lemma 11.3 (a uniform
   gap B_m ≤ (m−η)B₁ on Gr(m, 2m) over F₂, derived from a maximal flat dimension) feeds EG Prop. 11.2 ('then F has
   ports') through a replacement-product construction (EG §§11.1.2–11.1.3). Theorem A is the corresponding statement
   for [AN]'s contracting hypothesis, proved instead from [AN] F.6 and HC Thm 4.2." Optionally add the
   GL-averaging remark of A.2 as a second route, marked [ours, unrefereed].
2. **§1, Hypotheses table:**
   - Add: "Weak ETH in this form is equivalent to the Stearns–Hunt hypothesis [IM, §1, citing their ref. 41, Thm 2.4]."
   - Change "Relations: ETH ⇒ WETH" to: "ETH ⇒ WETH (ETH itself is claimed refuted by both labs in October 2026, in time
     2^{n/(log n)^{1/2+o(1)}}, which is compatible with WETH [cite both ETH papers])."
   As written, a reader may think we assume ETH.
3. **§0, "which the paper does not mention":** keep it. It is accurate (checked by full-text search). Optionally quote
   [AN] §2.5 ("we know no way to run it faster than gate by gate").
4. **§8 or a remark:** cite arXiv:2610.41622 as a barrier (no 2^{n^{1−c}} within the rewrite-and-merge class). Say
   briefly why it does not apply: our algorithm enumerates the runs of [AN]'s cutting program, not a merge recursion.
5. **§1, D.3 quotation:** the wording is confirmed. "Exclude each other" occurs at D.3 and again in App. L/M (l. 4475 of
   our pdftotext).
6. **Provenance paragraph:** add that the ETH papers of both labs are under review (OpenAI's by the
   Impagliazzo–Paturi–Williams group, per history.md).

### A.6 Not accessed

- Lean Zulip and Mastodon (no login, no direct search).
- Content on alphaXiv or X beyond the AN page.
- The HC and IM appendices beyond the cited theorems.
- The full text of arXiv:2610.41622 (abstract only).

---

## B. The tensor rate of K_{2,3}

### B.1 Closest prior work

1. **The Okamura–Seymour example is exactly our instance** [read]. N. J. A. Harvey, R. Kleinberg, A. R. Lehman, "On the
   capacity of information networks", IEEE Trans. Inf. Theory 52(6) (2006); also Adler–Harvey–Jain–Kleinberg–Lehman,
   SODA 2006. https://www.math.uwaterloo.ca/~harvey/Publications/Capacity/Capacity.pdf (§X.B, Thm 27).
   - The setting: K_{2,3}, four commodities (the three pairs of the 3-side and the pair of the 2-side), unit capacities.
     "The maximum concurrent flow in this graph is 3/4". **Theorem 27: "The network coding rate of the Okamura–Seymour
     example is 3/4."** Sparsity (cut) is 1.
   - Theorem 28 extends this to all "special bipartite" instances.
   - The same result was obtained concurrently by Jain–Vazirani–Yuval (SODA 2006, "Input–Output and Crypto
     inequalities", "four-session instance on K_{3,2}") and by Kramer–Savari [read: citations in arXiv:2610.09367,
     arXiv:2610.33655].
   - So for **classical information**, coding = routing = 3/4 on our instance. Our ≥ 3/√10 is a gap between tensor
     restriction and network coding as well as routing. This is not in the note and is the most important missing
     citation for B.
2. **The 2026 refutations of the undirected multiple-unicast conjecture** [read: abstracts].
   - Z. Li, B. Li, "Network coding can beat routing in undirected multiple-unicast networks", arXiv:2610.09367 (7 Oct
     2026, with Lean).
   - Zhongtian He, "The multiple unicast conjecture is false", arXiv:2610.10108 (7 Oct 2026).
   - Liu–Que–Li–Li, "On the multiple-unicast conjecture: beyond cut metrics", arXiv:2608.06070, proves the conjecture
     for networks with at most five terminal locations. That covers K_{2,3} and is consistent with HKL.
   - OpenAI's IM cites these as [11, 58].
   - For our note: K_{2,3} remains a coding = routing instance classically.
3. **Tensor / SLOCC conversions between EPR networks.**
   - Christandl, Lysikov, Steffan, Werner, Witteveen, "The resource theory of tensor networks", Quantum 8, 1560 (2024),
     https://doi.org/10.22331/q-2024-12-11-1560 [read: abstract, §§2, 4.3]. The resource theory of "entanglement
     structures" under restriction, which is our f* framework. It shows "transformations between entanglement
     structures which go beyond edge-by-edge conversions", and asymptotic conversions of graph tensors. No K_{2,3}
     instance, no routing comparison of this kind.
   - Vrana–Christandl, "Entanglement distillation from GHZ shares", arXiv:1603.03964 (CMP 2017) [read: abstract, Thm 1].
     The SLOCC rate from a GHZ hypergraph to a global GHZ is 1/λ(H) (edge connectivity), and EPR_{AB} distillation has
     rate equal to the min cut, with an LOCC counterpart ("localizable entanglement"). For broadcast-type demands,
     tensors reach the cut bound, as multicast network coding does. Our instance is multiple-unicast, where coding gives
     nothing.
   - Christandl–Vrana–Zuiddam, "Asymptotic tensor rank of graph tensors: beyond matrix multiplication",
     arXiv:1609.07476 (Comput. Complexity 28, 2019) [read: abstract and definitions]. Asymptotic rank of T(K_k): GHZ →
     graph tensor, not graph tensor → graph tensor.
   - Christandl–Lucia–Vrana–Werner, arXiv:1809.08185 (SciPost Phys. 9, 042, 2020) [read: abstract and conclusions]. The
     "geometry" there is algebraic (degenerations and orbit closures), not metric. Not prior art for B.
   - Christandl–Zuiddam, "Tensor surgery and tensor rank", Comput. Complexity 28 (2019), arXiv:1606.04253 [recall].
     Rank upper bounds for graph tensors; not conversions.
   - Christandl, "The tensor as an informational resource", PNAS Nexus 3 (2024) [read: abstract, §§1–3]. Hypergraph
     preorders; no K_{2,3}.
4. **Structure of the spectrum on graph tensors** [read].
   - Wigderson–Zuiddam, "Asymptotic spectra: theory, applications and extensions", Bull. AMS (2026),
     https://doi.org/10.1090/bull/1880, Thm 12.23: log-star-convexity of the asymptotic spectrum of graph tensors.
   - Vrana–Zuiddam, "The asymptotic spectrum of tensors is connected", arXiv:2611.34664 (dated 2 Nov 2026, listed 25 Nov
     2026). It reproves WZ 12.23 over every field: log Δ is star-convex about every point of the convex hull of the
     singleton flattening-rank vectors. It also proves that the non-crossing (laminar) upper quantum functionals are
     spectral points on complex tensors.
   - These are relevant to K.4(c): on graph tensors, all these functionals give wire metrics Σ_b θ_b·δ_b (cut metrics),
     hence ℓ₁. This is our computation, not stated there.
   - Botero–Christandl–Fraser–Leigh–Nieuwboer, "On quantum functionals for higher-order tensors", arXiv:2604.18283 (Apr
     2026) [read: abstract, intro]: laminar functionals anchor new spectral points.
   - Sakabe–Doğan–Walter, arXiv:2601.21553: support functionals = quantum functionals, universal [snippet].
   - Alman–Li–Pratt, "The edge of the asymptotic spectrum of tensors", arXiv:2604.01386: spectral points over every field
     with weight zero on one leg [snippet].
5. **LOCC and channel versions.**
   - Leung–Oppenheim–Winter, "Quantum network communication — the butterfly and beyond", IEEE TIT 56 (2010) 3478,
     arXiv:quant-ph/0608223 [read: abstract]. k-pair quantum communication with none, forward, backward or two-way free
     classical communication. Routing is optimal on the butterfly and some classes. With two-way assistance, quantum
     communication is EPR distribution by LOCC. K_{2,3} is not treated.
   - Jain–Franceschetti–Meyer, "On quantum network coding", J. Math. Phys. 52, 032201 (2011) [read: abstract and
     intro]. Directed, fidelity-1. The sparsest multicut bounds the flow when the network is not
     "entanglement-supported".
   - Cui–Ji–Yu–Zeng, "Quantum capacities for entanglement networks", arXiv:1602.00401 [read: abstract]. Single
     source/sink: the regularized LOCC repeater capacity Q equals the tensor-network rank capacity R. One-shot they
     differ.
   - Hayashi–Iwama–Nishimura–Raymond–Yamashita (STACS 2007) and Kobayashi–Le Gall–Nishimura–Rötteler (ICALP 2009;
     ISIT 2010/2011) [recall]: directed quantum network coding, perfect with free classical communication whenever a
     classical (linear) code exists. On K_{2,3} that yields only 3/4.
   - Jensen–Vrana, "The asymptotic spectrum of LOCC transformations", arXiv:1807.05130 (IEEE TIT 2020) [read: abstract].
     LOCC rates with success probability 2^{−rn}. The SLOCC (restriction) rate is the r → ∞ end [recall/inference].
6. **CAT(0) and metric geometry used for the asymptotic spectrum before November 2026.** None found before [AN] and
   OpenAI's EG. EG Thm 4.3 [read]: "Every complete geodesic spectral space X is CAT(0)", with Cor. 3.4 (geodesic
   extension).
   - This is the OpenAI counterpart of [AN] C.1/C.3, and it is stated for points of Strassen's spectrum. Theorem K.1
     needs only this direction, so it could cite EG 4.3 as an independent source for its trust base.
   - OpenAI's MM paper reduces ω = 9/4 to a tripod with unit arms in a spectral space ("The critical ratio occurs at
     three tips of a tripod with unit arms", §1; "Propagation of equality on a tripod"). That is a close cousin of our
     extremal configuration W5 ⊂ tripod × segment, and is worth citing as related geometry.

### B.2 Is the instance, the gap, or the constant known?

- **K_{2,3} with this demand:** classical; it is the Okamura–Seymour example. Studied for flow and coding (rate 3/4 for
  both). **Not found** studied for tensor restriction, SLOCC or LOCC EPR conversion.
- **A gap between routing and tensor conversion on it:** not found. Gaps of the "tensor beats packing" type are known for
  GHZ/multicast demands (Vrana–Christandl), but not for multiple-unicast EPR demands.
- **3/√10, 0.94868, 6/(4+√10), 0.8377:** no occurrence in any network, tensor or CAT(0) context. Searches returned only
  textbook arithmetic.

**Verdict for B.**
- K.1 (f* ≥ 3/√10 unconditionally) appears **new**. Confidence medium-high: the area is active, and a 2026 preprint
  could be missed.
- The conditional equality in K.2 is new; it depends on [AN].
- The explicit family at rate ≥ 0.8367 appears new.
- **Not contradicted.** HKL bound classical entropy. They imply nothing for restriction, which can use exponentially
  small "success probability" in the SLOCC reading.

**Which notion is which** (as requested):

| Result | Notion |
|---|---|
| Ours (f*) | exact asymptotic restriction (SLOCC with post-selection; no fidelity; success probability unconstrained; o(n) overhead) |
| Vrana–Christandl Thm 1; CVZ; CLSWW; Wigderson–Zuiddam; Vrana–Zuiddam | the same restriction or degeneration notion |
| Jensen–Vrana | LOCC with success probability 2^{−rn} and exact (pure) targets |
| Leung–Oppenheim–Winter; Hayashi et al.; KLNR; Jain–Franceschetti–Meyer | channel networks, high fidelity (LOW) or fidelity 1 (JFM, KLNR); with or without free classical communication |
| Cui–Ji–Yu–Zeng | LOCC repeater capacity versus tensor rank, single pair |
| HKL / Jain et al. / Kramer–Savari / Li–Li / He | classical information, zero error or vanishing error, entropy bounds |

Our f* ≥ 3/√10 says nothing about LOCC rates. I found no LOCC result for K_{2,3}; it appears open.

### B.3 Changes to `note-k23-rate.md`

1. **§0.1, the comparison list, after "routing gives exactly 3/4":**
   - add "and so does classical network coding: the network coding rate of this instance, the Okamura–Seymour example,
     is 3/4 [HKL06, Thm 27; also Jain et al. 2006; Kramer–Savari 2006]";
   - replace "the quadrilateral inequality … (an earlier step of this project; we know of no statement of this instance
     in the literature and have not searched it systematically)" with: "The instance is the Okamura–Seymour example
     [OS81], the standard case where the cut condition holds but flows fail. Classically, coding equals routing there
     [HKL06]. We found no treatment of it for tensor restriction, SLOCC or LOCC entanglement conversion (search of
     26 Nov 2026)."
2. **After "Item 1 says that tensor restriction beats routing …":** add "… and beats classical network coding, which
   cannot exceed 3/4 on this instance [HKL06]. The comparison is between different resource models: f* is exact
   asymptotic restriction (SLOCC), not LOCC with fidelity; for LOCC we know no bound better than the cut bound 1."
3. **§0.2:** add a bullet "**Not LOCC.**" with the content of 2.
4. **§6(c), "Which explicit spectral points have ℓ₁ wire metrics":**
   - add "the laminar (non-crossing) upper quantum functionals [BCFLN26, arXiv:2604.18283; Vrana–Zuiddam,
     arXiv:2611.34664, Thm 1.9] and the upper support functionals [SDW26; ALP26]. On graph tensors every one of these
     gives a nonnegative combination of cut metrics";
   - add the log-star-convexity of the spectrum on graph tensors [WZ26, Thm 12.23; VZ26, Thm 4.12] as context.
5. **§1.3 and the trust base §3.3 item 1:** add "Alternatively, OpenAI's EG Thm 4.3 (every complete geodesic spectral
   space is CAT(0)) with Cor. 3.4 gives the CAT(0) embedding for points of Strassen's spectrum directly. Item 1 then uses
   nothing from [AN]." This is an independent source, so it strengthens the trust base.
6. **§2.3 or §8:** cite MM's tripod argument (OpenAI, "The matrix multiplication exponent is nine fourths", §1 and §8)
   as related use of tripods in spectral spaces.
7. **References:**
   - add [OS81] Okamura–Seymour, J. Combin. Theory B 31 (1981) 75–81;
   - add [HKL06]; CLSWW (Quantum 2024); Vrana–Christandl (CMP 2017); LOW (IEEE TIT 2010); Jensen–Vrana (IEEE TIT
     2020); WZ26; VZ26;
   - **fix [Toy]** (see E).

### B.4 Not accessed

- The full texts of the 2026 multiple-unicast papers (abstracts and intros only).
- CLSWW §5 in full.
- No search for LOCC results on K_{2,3} in Chinese or Japanese venues.

---

## C. Multiplicative complexity of 2×2 matrix multiplication over F₂

### C.1 Sources

- **Morse, arXiv:2608.30238 exists** [read: abstract and §1]. Gregory Morse (ELTE), "Unrestricted Boolean
  multiplicative complexity of four-term binary polynomial multiplication: rational places, Hasse jets, and the failure
  of nonlinear feedback", submitted 31 Aug 2026, with Lean 4.
  - It proves MC_∧(Mul₄) = 9 in unrestricted XOR–AND circuits, and the full list (Mul₀, …, Mul₄) = (0, 1, 3, 6, 9),
    formalized in Lean. So **Mul₂ = 3 and Mul₃ = 6, as in our notebook.**
  - It describes itself as resolving the Boyar–Find question "for a natural vector-valued quadratic function".
  - It does not treat matrix multiplication.
- **Boyar–Find** [read: arXiv:1407.6169v3, TCS 2018], "Multiplicative complexity of vector valued Boolean functions",
  §4 (Open Problems), verbatim:
  - "Mirwald and Schnorr showed that for quadratic (n,1)- and (n,2)-functions, quadratic circuits are optimal. It is
    still not known whether this is true for (n,m)-functions in general."
  - Also: "it is unknown whether a similar result [Strassen's homogenization] holds for finite fields and in particular
    for F₂."
  - Matrix multiplication is not mentioned.
- **Mirwald–Schnorr**, TCS 102 (1992) 307–328 [recall, consistent with Boyar–Find's statement].
- **Public statements specific to ⟨2,2,2⟩ over F₂ in the unrestricted model** [read]. All are from "Slop Dealer
  Research", an AI-generated, unrefereed register:
  - MF-149 and MF-180 (4 Sep 2026: https://slopdealer.com/research/papers/mf-149/ and …/mf-180/) claim **MC ≥ 6** and
    say **"Deciding between 6 and 7 remains open"**.
    - Method: restrict to the 2-plane W = {Tr(ΛᵀAB) : Λ ∈ F₄*}; each nonzero form has MC 4; a packing lemma gives
      qMC(W) ≥ 6.
    - The transfer to unrestricted circuits is implicitly Mirwald–Schnorr for 2-output functions. That step is sound in
      principle.
  - ML-088 (4 Sep): a 6-AND SAT instance with 33 345 variables and 155 669 clauses, "open at k = 6".
  - ML-051 and MF-086 (29 Aug): formal-quadratic and bilinear values are 7s for s copies; unrestricted is open.
- **Classical bilinear and quadratic results:**
  - Hopcroft–Kerr 1971 (rank over F₂ ≥ 7) and Winograd 1971 (≥ 7 over any field) [read: as cited in arXiv:1705.09652
    and in arXiv:2603.07280 (Chengu Wang; earlier misattributed here to "Alder–Strassen"), which re-derives R_{F₂}(⟨2,2,2⟩) ≥ 7 automatically].
  - Shpilka, FOCS 2001 (quadratic circuits over GF(2)) [read: abstract].
- **Related 2026 work, different model:** Y. Spiizer, "Partial homogenization and the structure of optimal algebraic
  algorithms", arXiv:2611.23622 (17 Nov 2026) [read: abstract]. Arithmetic circuits with unbounded fan-in products; over
  ℝ, 2×2 needs ≥ 6 such gates. This is not Boolean (no x² = x), so it does not overlap.
- **Häner, arXiv:2307.07424** [snippet]: settles another Boyar–Find question (2n − 3) and shows these questions get
  answered.

### C.2 Verdict

- **"MC(⟨2,2,2⟩, F₂) = 7 in unrestricted XOR–AND circuits":** **open in all public sources found**. As of September 2026
  a public register says the value lies in {6, 7} and calls the question open. No later claim was found. So our
  notebook's result (all 72 first-gate orbits refuted at k = 6) would be **new**, and it is a natural instance of the
  Boyar–Find question for 4 outputs. Confidence medium-high on novelty.
- **The lower bound 6 is not new** (in the public register, by a short argument).
- **Boolean-quadratic MC = 7** (E1b) is almost certainly known in substance (Winograd / Hopcroft–Kerr type arguments for
  quadratic algorithms over F₂). I found no explicit statement for the Boolean variant (x² = x, factors mixing A and B).
- **Caution.** Our proof is a computer search: `mc_span.c`, a 128-bit state hash with collisions ignored, no DRAT or
  proof object. A public claim needs at least one of:
  - an independent re-run without hashing (or with exact state keys);
  - a certificate checkable by an independent program;
  - a Lean proof in the style of Morse's.
  The trust-base paragraph in the notebook is accurate and should be carried into any write-up.

### C.3 Changes to the notes

- **`mm/lab/notebook.md`, E1b:**
  - change "Literature agrees: Winograd 1971 / Hopcroft–Kerr 1971 lower bound 7 for quadratic algorithms; this is an
    independent machine check of the Boolean variant over F₂" so that it cites Hopcroft–Kerr (SIAM J. Appl. Math. 20,
    1971) for F₂ explicitly;
  - add "explicit statement for the Boolean-quadratic model not found".
- **E1c "Results":** after "⟨2,2,2⟩: k = 5 refuted … MC ≥ 6", add "(MC ≥ 6 was stated publicly before us: Slop Dealer
  Research MF-149/MF-180, 4 Sep 2026, via the F₄-trace 2-plane and Mirwald–Schnorr for two outputs; they call 6 vs 7
  open, ML-088)".
- **The UPDATE paragraph:** add "Novelty check of 26 Nov 2026: no public source settles 6 vs 7; Boyar–Find [TCS 2018,
  §4] pose the general question; Morse [arXiv:2608.30238] settles it for Mul₄ only."
- **"Free Mirwald–Schnorr bound … gives only 4":** add that a 2-dimensional subspace of outputs (the F₄-trace forms)
  gives 6 by Mirwald–Schnorr for (n,2)-functions. Worth reproducing as an independent check of the k = 5 refutation.
- **`mm/ideas-n2.md`** (status [S] on Morse): it is now verified to exist and to say what the notes say. Its l. 43 claim
  "Mul₀..Mul₄ = 0, 1, 3, 6, 9 unrestricted" is correct.

### C.4 Not accessed

- Mirwald–Schnorr's paper itself.
- Morse's §§2–9 and its Lean release.
- The Slop Dealer "evidence packs" (not downloaded).

---

## D. Expanders against the rank metric and against Hadamard spaces

### D.1 Lubotzky–Zelmanov [read: full text, arXiv:0804.0481v2]

"Dimension expanders", J. Algebra 319 (2008).
- **Example 4.I:** F[x] does not have (algebra) property τ. Take the span of x, …, x^{⌊n_i/2⌋−1} in F[x]/(f_i). Then
  "dim(W + xW) ≤ 1 + dim W".
- **Example 4.IV:** for 3 ≤ d and a prime p, F_p[SL_d(F_p[x])] maps onto M_d(F_p[x]). The latter lacks τ by 4.III,
  "Hence F_p[SL_d(F_p[x])] does not have τ".
- **Introduction:** "Example 4.IV below implies that there are expander groups whose linear representations over finite
  fields are not dimension expanders … the finite examples … are of groups whose order is divisible by p and the
  representations are over F_p."
- **Attribution:** our attribution in `middle/notes.md` §5.1 is **correct**. Two small points for precision:
  - "property τ" there is the **algebra** property of LZ Def. 4.1, not the group property;
  - LZ's subspace starts at x, ours at 1. This is immaterial.

### D.2 The kernel 2^{−rank(a−b)} and Proposition S

- Positive semidefiniteness via |ker(a − b)| = Σ_x 1[ax = bx] is elementary and standard [recall: Delsarte's
  bilinear-forms scheme, JCTA 25 (1978), whose eigenvalue theory contains it]. No citation is needed beyond "standard".
- Proposition S is the usual trace argument for a PSD kernel with unit diagonal. It is also implicit in Mendel–Naor's
  kernel formalism (arXiv:1207.4705, eq. (3)).
- Both should be labelled standard, not new.

### D.3 Expanders against all Hadamard spaces, or all Euclidean buildings

**Hadamard spaces in general.**
- **Open** [read]. EMN's 2021 Münster workshop slides ask: "Does there exist a sequence of finite 3-regular graphs which
  are expanders with respect to all Hadamard spaces simultaneously? Less ambitiously, does every Hadamard space admit a
  sequence of expanders?"
- Mendel, Oberwolfach Report 19/2018 [read]: "it is natural to ask whether there exist 'CAT(0)-expanders' … While this
  question is still unresolved…".
- arXiv:2510.18722 (Oct 2025), Question 4.17 [read]: "Does a Hadamard expander exist?" It says Gromov [Gro03] and Kondo
  [Kon12] "precluded the possibility that every (classical) expander is a Hadamard expander" by a specific expander
  bi-Lipschitz-embedded in a specific Hadamard space, but that this "does not rule out the existence of Hadamard
  expanders, which remains a compelling open problem".

**Known positive results.**
- **Mendel–Naor**, Duke 164 (2015), arXiv:1306.5434, Thm 1.1 [read]. There are a Hadamard space X and 3-regular {G_n}
  that are X-expanders, while random regular graphs have γ(H, d_X²) ≥ c(log_d n)² a.a.s. Their space is built from
  Euclidean cones over random graphs.
- **Euclidean buildings of bounded type: every classical expander expands against each one.**
  - Naor–Silberman, "Poincaré inequalities, embeddings, and wild groups", Compositio 147 (2011), arXiv:1005.4084, Cor.
    5.2–5.3 [read]. Euclidean buildings have finite Nagata dimension (Lang–Schlichenmaier) and hence padded
    decompositions. Every expander then satisfies the Poincaré inequality against the building, with constant
    depending on the spectral gap and the building's padding parameters.
  - Naor, "Comparison of metric spectral gaps" (AGMS 2014), §7 [snippet]: Euclidean buildings satisfy
    γ(A, d²) ≤ Ψ(1/(1 − λ₂)) with Ψ linear.
  - The constants grow with the Nagata dimension, i.e. with the rank.
- **Fixed points of random groups:**
  - Izeki–Kondo–Nayatani, GGD 6 (2012) [read: abstract]: fixed points on the buildings of PGL(m, ℚ_r) "with m bounded
    from above".
  - Toyoda, Kodai Math. J. 39 (2016) [read: abstract]: δ < 1 for geodesically complete CAT(0) spaces with a proper
    cocompact action, hence every Bruhat–Tits building of a semisimple group, each separately.
  - Toyoda, Kodai Math. J. 33 (2010) [read: abstract]: sup δ < 1 over families whose tangent cones are products of
    cones over a GH-precompact family of CAT(1) spaces.
  - Kondo constructed a CAT(0) space with δ = 1 [read: as cited in Toyoda].
- **Banach-space results that do not reach CAT(0).**
  - Lafforgue, Duke 143 (2008): strong Banach property (T) for SL₃ over non-archimedean local fields; super-expanders
    for uniformly convex spaces [recall].
  - de Laat–de la Salle; de la Salle, Acta Math. 223 (2019) (strong (T) for higher-rank lattices, including
    non-uniform ones) [recall].
  - These are Banach-space statements. No source found extends them to all CAT(0) spaces.
- **Eskenazis–Mendel–Naor**, "Nonpositive curvature is not coarsely universal", Invent. Math. 217 (2019),
  arXiv:1808.02179 [read: slides and Oberwolfach summary]. ℓ_∞ grids do not coarsely embed into any CAT(0) space (metric
  cotype). This is not about expanders. Mendel (2018): "it is unknown whether there exists an expander that does not
  coarsely embed in any CAT(0) space".

**What is known, precisely.**
1. No bounded-degree family is known to be an expander with respect to all Hadamard spaces. This is an open problem,
   stated as such in EMN (2021 slides), Mendel (2018), and arXiv:2510.18722.
2. For each fixed Euclidean building (more generally, each space of finite Nagata dimension), **every** classical
   expander is an expander with respect to it. The constant depends on the building through its dimension and padding
   constants [Naor–Silberman 2011; Naor 2014].
3. Uniformity over buildings of **unbounded** rank was not found in the literature. IKN need m bounded; Toyoda's 2010
   uniformity needs GH-precompact links, and spherical buildings of growing rank are not. So whether some expander family
   is uniform over all Euclidean buildings of all ranks appears open.
4. Our Theorem M2, if correct, says that the (T)-expanders Cay(SL₃(F₂[x]/(p)), S) are **not** uniform over buildings of
   unbounded rank: their Poincaré constant is Θ(log n). This is consistent with (2) and (3). It is a specific negative
   answer for one natural family. Strong (T) does not obviously give such uniformity, which matches our Remark 5.3.1.
   - Compare Gromov–Kondo: a specific expander embedded in its own Euclidean cone. Our mechanism differs: dimension
     non-expansion in characteristic p, LZ 4.IV.
   - I found no source stating M2. **Verdict: probably new** (medium confidence), but it is a short consequence of LZ
     4.IV plus the building embedding of the rank metric. A specialist may see it as folklore.

### D.4 Changes to `middle/notes.md`

- **§5.1:** keep the LZ citation. Write "do not have (algebra) property τ, LZ Def. 4.1". Add LZ's own sentence from the
  introduction (quoted in D.1) as the precise source of the mechanism.
- **§5.3 Remark 1:**
  - add "For each Euclidean building of bounded dimension, every expander is an expander against it, with a constant
    depending on the building [Naor–Silberman 2011, Cor. 5.2–5.3; Naor 2014, §7]; fixed-point results for random groups
    likewise need bounded rank [IKN 2012] or one building at a time [Toyoda 2016]. So 'unbounded rank' is exactly where
    Theorem M2 can bite";
  - "I did not check the non-uniform lattice SL₃(F₂[x])" can now point to de la Salle (Acta 2019) for strong (T) of
    non-uniform higher-rank lattices [recall, to be verified]. Super-expansion is a Banach statement and does not affect
    M2.
- **Table near l. 455, "Mendel–Naor … no statement about buildings":** correct. Add a row "Naor–Silberman 2011 / Naor
  2014: every expander is an expander against each fixed Euclidean building (constant depends on its dimension)". Add the
  open problem "Hadamard expanders?" with the three citations of D.3.
- **Lemma K and Proposition S:** add "(standard)".

### D.5 Not accessed

- Kondo, Math. Z. 271 (2012), and Gromov, GAFA 2003 (cited second-hand).
- The de Laat–de la Salle papers.
- The Eskenazis–Mendel–Naor paper itself (slides and summary only).
- Izeki–Nayatani (2005) directly.

---

## E. Toyoda's five-point theorem and Lebedeva's six points

- **Toyoda, arXiv:1907.09074** [read: abstract and §1]. **Title: "An intrinsic characterization of five points in a
  CAT(0) space"**, Anal. Geom. Metr. Spaces 8 (2020) 114–165.
  - Thm 1.3: "A metric space that contains at most five points admits an isometric embedding into a CAT(0) space if and
    only if it satisfies the ⊠-inequalities."
  - The ⊠-inequalities are the four-point weighted quadruple inequalities of Gromov and Sturm, for all t, s ∈ [0, 1].
    The theorem number "Thm 1.3" in our note is correct.
- **Failure at six points** [read]:
  - Nina Lebedeva's 6-point space (a perturbed non-regular octahedron, d_ε = Euclidean + ε on one diagonal) satisfies the
    ⊠-inequalities, i.e. (2+2)-comparison, and also (4+2)-comparison, but embeds in no CAT(0) space.
  - It appears in the arXiv version of Alexander–Kapovitch–Petrunin, "Alexandrov meets Kirszbraun" (Gökova 2010;
    updated arXiv:1012.5636v2, 2017), §7.2. It is stated as Theorem 3.1 in Toyoda, arXiv:2404.13871 (J. Topol. Anal.,
    2026), and as Theorem 2.4 in Toyoda, arXiv:2411.13877.
  - Toyoda 2404.13871: Lebedeva's space satisfies all Andoni–Naor–Neiman inequalities of their form (1.2).
  - Toyoda 2411.13877, "Inequalities on six points in a CAT(0) space": the first explicit 6-point CAT(0) quadratic
    inequalities not implied by ⊠.
  - Lebedeva–Petrunin, "Trees meet octahedron comparison", arXiv:2212.06445: "Some six-point metric spaces meet the
    (4+2)-point comparison, but do not admit a distance-preserving embedding into a complete length CAT(0)."
- **Consequence for us.** The K_{2,3} cross-check uses five points, so Toyoda applies and the semi-infinite program in
  §3.6 is a valid cross-check of Theorem 5. Any extension to K_{2,m}, m ≥ 4 (open problem 4: m + 2 ≥ 6 points) **cannot**
  use ⊠-inequalities alone. It needs the full CAT(0) quadratic-inequality cone (Andoni–Naor–Neiman, Theorem 1.1 as
  quoted by Toyoda), and Lebedeva-type gaps occur.

**Changes to `note-k23-rate.md`.**
1. References: replace "[Toy] T. Toyoda, 'Five-point CAT(0) spaces' (title as on arXiv), arXiv:1907.09074" with
   "[Toy] T. Toyoda, An intrinsic characterization of five points in a CAT(0) space, Anal. Geom. Metr. Spaces 8 (2020)
   114–165; arXiv:1907.09074, Thm 1.3."
2. §3.6, first bullet: add "This criterion is special to at most five points. Lebedeva's six-point spaces [AKP,
   arXiv:1012.5636v2 §7.2; Toyoda, arXiv:2404.13871, Thm 3.1] satisfy all ⊠-inequalities without embedding in CAT(0)."
3. §8, open problem 4 (K_{2,m}): add "For m ≥ 4 the lower bound cannot be checked with ⊠-inequalities alone (six or more
   points, see [Toy] and Lebedeva). One needs the full CAT(0) quadratic cone [Andoni–Naor–Neiman 2018], or a direct
   argument as in §3."

---

## Process note (no action needed for the literature)

- Search engines index a public GitHub repository of this project: the README of the Hamiltonian-cycle follow-up work.
  I did not open it, so as not to send project identifiers to outside services.
- Before "anything is posted publicly", confirm whether `research/ports/` is already pushed there. If it is, the
  material is already public in effect.

## Sources consulted, in one place

Lab sources:
- Anthropic: vp-vnp paper (raw GitHub; Hexagon 2611.00954v1); README; commits; issues #55, #57; eth paper.
- OpenAI: history.md; EG, HC, IM, MM papers of 24 Nov 2026; ETH paper; 379.md scope note.

Commentary:
- Aaronson ?p=10362; Fortnow 2026/11/vp-vnp; HN 50620102; MO 518140, 518197; vibemathlab status page; officechai;
  datastudios; postcutoff.

arXiv, by topic:
- SAT barrier: 2610.41622.
- Multiple unicast: 2610.09367, 2610.10108, 2608.06070, 2610.33655.
- Graph tensors and the asymptotic spectrum: 1609.07476, 1603.03964, 1807.05130, 1809.08185, 2611.34664, 2604.18283,
  2601.21553, 2604.01386.
- Quantum networks: quant-ph/0608223, 1602.00401.
- Multiplicative complexity: 2608.30238, 1407.6169, 1508.05737, 2307.07424, 2611.23622, 2603.07280, 1705.09652.
- Expanders: 0804.0481, 1306.5434, 1005.4084, 1207.4705, 2510.18722.
- CAT(0) point configurations: 1907.09074, 2404.13871, 2411.13877, 2212.06445.

Journals and other:
- HKL (Capacity.pdf); Jain–Franceschetti–Meyer, JMP 2011; CLSWW, Quantum 2024; Wigderson–Zuiddam, Bull. AMS 2026.
- IKN, GGD 2012; Toyoda, Kodai 2010 and 2016; Fujiwara–Toyoda, PAMS 2012; Oberwolfach Report 19/2018; EMN 2021 slides.
- Slop Dealer Research MF-086, MF-149, MF-180, ML-051, ML-088.
