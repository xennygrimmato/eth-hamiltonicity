# Citation audit (30 Oct 2026)

Scope: `paper/refs.bib` + `paper/main.tex` (exact HC counting) and `quantum-note/refs.bib` +
`quantum-note/main.tex` (exact quantum amplitudes). Each entry was checked against a primary
source (publisher/DOI record via Crossref, arXiv listing or full text, LIPIcs/DROPS page, the
authors' PDF, or the labs' GitHub repositories). Where a cited theorem or bound is quoted in the
text, the statement was checked in the source's full text, unless the table says otherwise.

Both papers recompile with zero undefined references or citations and zero BibTeX warnings. PDFs
are copied to `docs/exact-hc-paper.pdf` and `docs/quantum-note.pdf`.

## 1. `paper/` (Counting Hamiltonian cycles)

### Existing entries (30)

| Key | Source used | What was wrong | Fix |
|---|---|---|---|
| Anthropic26 | https://github.com/anthropics/formal-math/tree/main/eth (paper.pdf, title page: "A 2^{o(n)} time algorithm for 3-SAT", Claude, Anthropic, dated October 26, 2026; Main Theorem checked) | No URL | Added the repository URL; the date and title were already correct |
| OpenAI26 | https://github.com/openai/math (preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; "Date: 17 October 2026, revised 25 October 2026"; Thm 1.1 and the ρ(n) remark checked) | No URL; date given only as "October 2026" | Added the exact dates and the URL |
| ImpagliazzoPaturi01 | https://doi.org/10.1006/jcss.2000.1727 | None | None |
| IPZ01 | https://doi.org/10.1006/jcss.2001.1774 | None | None |
| LMS11 | https://dblp.org/rec/journals/eatcs/LokshtanovMS11 ; full text http://sites.cs.ucsb.edu/~daniello/papers/surveyETH.pdf | Entry correct. The **text** cited Thm 3.3 for "HC has no 2^{o(n+m)}", but Thm 3.3 is stated for Hamiltonian **Path** with 2^{o(n)} | Text fixed (see §3) |
| CyganEtAl15 | https://doi.org/10.1007/978-3-319-21275-3 (Ch. 14 "Lower bounds based on the ETH", pp. 467–521) | None | None |
| Bjorklund14 | https://doi.org/10.1137/110839229 ; arXiv:1008.0541 (Monte Carlo O*(1.657^n)) | None | None |
| BHKK12 | https://doi.org/10.1145/2151171.2151181 ; author PDF https://www.cs.helsinki.fi/u/mkhkoivi/publications/talg-2011.pdf ("Vol. 8, No. 2, Article 18") | None (it is for TSP, i.e. decision, as the text says) | Added a note on the ICALP 2008 version |
| BHKK08Tutte | https://doi.org/10.1109/focs.2008.40 | None | None |
| Eppstein07 | https://doi.org/10.7155/jgaa.00137 ; arXiv:cs/0302030 | Entry correct. The **table** listed O(2^{n/3}) in a row that this paper's column treats as counting, but 2^{n/3} is the decision/TSP bound. Eppstein's counting bound is O(2^{3n/8}) | Table row and prior-work text fixed |
| XiaoNagamochi16 | https://doi.org/10.1007/s00453-015-9970-4 ; arXiv:1212.6831 (TSP, O*(1.2312^n)) | None (TSP bound, now labelled as such) | None |
| BjorklundHusfeldt13 | https://doi.org/10.1109/focs.2013.83 ; arXiv:1301.7250 (deterministic O(1.619^n), poly space) | None | None |
| BjorklundWilliams19 | https://doi.org/10.4230/LIPIcs.ICALP.2019.25 (Thm 3: directed, average degree δ, deterministic 2^{n−Ω(n/δ)}) | None ("stated for digraphs" is accurate) | None |
| CutAndCount11 | https://doi.org/10.1109/focs.2011.23 ; journal https://doi.org/10.1145/3506707 | No mention of the journal version | Added a note: ACM TALG 18(2), 2022 |
| BCKN15 | https://doi.org/10.1016/j.ic.2014.12.008 ; arXiv:1211.1505, Table 1 (#Hamiltonian Cycle Õ(6^pw pw^{O(1)} n^2)) | None. **The 6^pw counting bound (Limitations (g)) is confirmed** | Added a note on the ICALP 2013 version, and "[Table 1]" in the text |
| CLN18 | https://doi.org/10.1137/1.9781611975031.70 ; arXiv:1709.02311 (Thm 1.1: no (6−ε)^pw under SETH; the abstract credits the matching 6^pw upper bound to Bodlaender et al., ICALP 2013) | None (Crossref misspells "Curticapea"; the bib is right) | Added the arXiv id, and "[Thm 1.1]" in the text |
| Curticapean18 | https://doi.org/10.1016/j.ic.2018.02.008 ; arXiv:1511.02910 | None | None |
| DHMTW14 | https://doi.org/10.1145/2635812 ; arXiv:1206.1775 ; https://eprints.sztaki.hu/8205/ (Art. 21) | None | None |
| BrandDellRoth19 | https://doi.org/10.1007/s00453-018-0472-z ; arXiv:1606.06581 (Thm 6) | Issue number missing | Added `number = {2}`; text made precise (see §3) |
| JVW90 | https://doi.org/10.1017/s0305004100068936 | None (not cited in the text, so not printed) | None |
| CJSSS04 | https://doi.org/10.1103/physrevlett.93.080601 ; arXiv:cond-mat/0403271 | Issue number missing. The **text** said the fermionic matrix-tree theorem "is due to" CJSSS. The paper actually proves a *generalisation* of Kirchhoff's theorem to non-Gaussian Grassmann integrals | Added `number = {8}`; text fixed (2 places) |
| CIKP08 | https://doi.org/10.1016/j.jcss.2007.06.015 ; full text https://cseweb.ucsd.edu/~paturi/myPapers/pubs/CalabroImpagliazzoKabanetsPaturi_2008_jcss.pdf (Lemma 3, stated for k-CNF φ, with a proof that uses only the solution set S) | None (the text's claim is confirmed) | Added "[Lemma 3]" in the text |
| AlonFuredi93 | https://doi.org/10.1006/eujc.1993.1011 | None | None |
| RazSpieker95 | https://doi.org/10.1007/bf01192528 (and CLN18 §4, Thm 4.3, which describes it as a bound for the *bipartite* variant of M_k) | Entry correct. The text credited it with a rank bound for the matchings-connectivity matrix itself | Text made precise |
| MVV87 | https://doi.org/10.1007/bf02579206 | None (not cited in the text) | None |
| DKMW13 | https://doi.org/10.1007/s00037-013-0059-7 | None | None |
| ImpagliazzoWigderson97 | https://doi.org/10.1145/258533.258590 | Entry correct. The text applies it to "#P-oracle circuits"; IW97 is stated for plain circuits. The relativised form is due to Klivans and van Melkebeek | Added KvM02 (see §2) |
| Bourbaki89 | Springer TOC https://www.gbv.de/dms/goettingen/248562584.pdf (Ch. III §7 "Exterior algebras", p. 507) | None (the citation "Ch. III, §7" is correct) | None |
| Lean4 | https://doi.org/10.1007/978-3-030-79876-5_37 (CADE-28, LNCS 12699, 625–635) | None | None |
| Mathlib20 | https://doi.org/10.1145/3372885.3373824 | Publisher missing | Added `publisher = {ACM}` |

### Added entries (10)

| Key | Source | Where cited |
|---|---|---|
| Bellman62 | https://doi.org/10.1145/321105.321111 | TSP/Held–Karp sentence after Thm (Sparse TSP); prior work ("Bellman–Held–Karp"); Table 1 |
| HeldKarp62 | https://doi.org/10.1137/0110015 | Same places |
| KGK77 | https://doi.org/10.1145/800179.810218 | Table 1 (polynomial-space O*(2^n)) |
| Karp82 | https://doi.org/10.1016/0167-6377(82)90044-x | Table 1; Open problems ("classical O*(2^n)") |
| Bax93 | https://doi.org/10.1016/0020-0190(93)90033-6 | Table 1; Open problems |
| Bjorklund16 | https://doi.org/10.4230/LIPIcs.SWAT.2016.17 (deterministic 2^{n−Ω(√(n/log n))} for counting directed HC; ATSP corollary) | Table 1 (it replaces the claim that O*(2^n) is the best deterministic bound); TSP "record" sentence; Open problems |
| CKN18 | https://doi.org/10.1145/3148227 (J. ACM 65(3), Art. 12; STOC 2013) | Rank of the matchings-connectivity matrix over F_2 (priority: CKN introduced the matrix) |
| Nederlof20 | https://doi.org/10.1145/3357713.3384264 | TSP "record" sentence (bipartite TSP in O(1.9999^n), assuming ω=2) |
| FominHoie06 | https://doi.org/10.1016/j.ipl.2005.10.012 | Prior work: pw ≤ n/6+o(n) for cubic graphs (the text relied on it without citing it) |
| KvM02 | https://doi.org/10.1137/s0097539700389652 | Open problems: relativised IW97 for oracle circuits |

### Text corrections in `paper/main.tex`

1. Intro: "\cite[Thm 3.3]{LMS11}" now says that it is stated as no 2^{o(n)} algorithm for
   Hamiltonian **Path**. The 2^{o(n+m)} statement for HC remains attributed to Cygan et al. Ch. 14.
2. After Thm (Sparse TSP): "Held–Karp's 2^n remains the record" was inaccurate. It now reads:
   O*(2^n) of Bellman / Held–Karp remains *essentially* the record, improved only to
   2^{n−Ω(√(n/log(nW)))}poly(W) [Bjorklund16], and for bipartite instances to O(1.9999^n)
   assuming quadratic-time matrix multiplication [Nederlof20].
3. Prior work: added the citations for Bellman–Held–Karp. "Counting much faster for small degree"
   now cites Eppstein's O(2^{3n/8}) counting bound, plus the Fomin–Høie pathwidth bound with the
   BCKN 6^pw algorithm.
4. Table 1, row "undirected, general": "O*(2^n) deterministic" now carries citations, and the
   deterministic 2^{n−Ω(√(n/log n))} bound [Bjorklund16] was added.
5. Table 1, row "maximum degree 3": the bounds are now labelled decision/TSP (2^{n/3}, 1.2312^n),
   and the counting bound O(2^{3n/8}) [Eppstein07] was added.
6. Table 1, row "pathwidth": the citations now point to [BCKN15, Table 1] and [CLN18, Thm 1.1].
7. Related work and "What is new": CJSSS04 is now credited with the generalised (non-Gaussian)
   matrix-tree theorem, of which our fermionic form is a special case. Before, the text said the
   fermionic form "is due to" them.
8. Rank bounds: these are now split as F_2 [CKN18] and Q [CLN18], the latter "building on Raz and
   Spieker's bound for its bipartite variant".
9. Extensions (Tutte line y=1): the BDR statement is now quantified correctly, as "for every real
   x≠1 there is ε>0 such that ... no exp(εn)-time algorithm".
10. Randomized decision proof: added "[Lemma 3]" for the CIKP isolation lemma.
11. Open problems: IW97 is now applied "in the relativised form of [KvM02]". "Classical O*(2^n)"
    now cites [Karp82, Bax93] and the [Bjorklund16] refinement.
12. Limitations (g) was rewritten. It now reads "All citations were checked against the primary
    sources on 30 Oct 2026", and it records where the 6^pw bound and its SETH tightness are
    stated. "Verification of the citations written from memory" was removed from "What is
    pending".

## 2. `quantum-note/`

### Existing entries (25)

| Key | Source used | What was wrong | Fix |
|---|---|---|---|
| Anthropic26 | as above | No URL | Added the URL |
| OpenAI26 | as above (Thm 1.1: (n+m)^{O_k(1)}2^{O_k(n log log n/√log n)}, poly space; 2^{O_{k,D}(n/√log n)} for m≤Dn; Appendix D, Thm D.1, Boolean tensor contraction; no occurrence of "quantum", "qubit" or "amplitude" in the text) | Exact date missing | Added the dates and the URL |
| Tulsyan26 | `paper/main.tex` in this repository (title and author match) | Date missing | Added "October 2026; companion paper …" |
| ImpagliazzoPaturi01 | https://doi.org/10.1006/jcss.2000.1727 | None | None |
| IPZ01 | https://doi.org/10.1006/jcss.2001.1774 | None | None |
| CIP06 | https://doi.org/10.1109/ccc.2006.6 ; full text https://courses.cs.washington.edu/courses/cse599i/24sp/papers/Calabro-Impagliazzo-Paturi.pdf (Lemma 5 is the width-reduction lemma, with Schuler's algorithm) | Pages missing | Added pp. 252–260 |
| Schuler05 | https://doi.org/10.1016/j.jalgor.2004.04.012 | None | None |
| Tovey84 | https://doi.org/10.1016/0166-218x(84)90081-7 | None | None |
| DHMTW14 | as above (#ETH introduced there) | None | None |
| MT19a | arXiv:1901.01637v4 (journal_ref QIC 19, 1089–1115). Conj. 1–7 and Thms 6, 7, 8, 10, 12 checked against the text | Journal version not given | Added Quantum Inf. Comput. 19(13&14):1089–1115 |
| MT19b | https://arxiv.org/abs/1902.08382v1 (Morimae, Tamaki; v1 title as in the bib; Conj. 1–6 and Thm 2 checked) | v2 has a new title and an added author (Hayakawa), and this was not noted | Added a note on v2 |
| MT20 | https://doi.org/10.22331/q-2020-09-24-329 ; arXiv:1912.06336v3 (Conj. 1–3) | None | None |
| DHKL20 | https://doi.org/10.22331/q-2020-05-11-264 ; arXiv:1805.05224v3 (Thm 2; 208 IQP qubits and 500 gates) | None | None |
| HNS18 | arXiv:1804.10368v2 (Thm 3: SETH ⇒ precision 2^{-n}/2 needs 2^{n−o(n)}); https://doi.org/10.1109/tit.2020.3004427 | Journal version not given | Added IEEE Trans. Inf. Theory 66(9):5585–5600 (2020) |
| HNS19 | arXiv:1902.04764v2 (Thm 1 and Thm 2, constant 2.2451·10^{-8}, O(1.3^n)) | None | Version pinned to v2 |
| AC17 | https://doi.org/10.4230/LIPIcs.CCC.2017.22 (LIPIcs 79, 22:1–22:67); arXiv:1612.05903v2 (Thm 4.1: O(n(2d)^{n+1}) time, O(n log d) space) | Was an `@misc` entry with no volume or pages | Changed to `@inproceedings` with LIPIcs 79, 22:1–22:67 and a note on theorem numbering |
| BPS19 | arXiv:1911.05686v2 (basic QSETH; footnote 8 checked); https://doi.org/10.4230/LIPIcs.STACS.2021.19 | Published version (new title, STACS 2021) not given | Added a note |
| MarkovShi08 | https://doi.org/10.1137/050644756 | None | None |
| WahlStrelchuk | https://doi.org/10.1103/PhysRevLett.131.180601 ; arXiv:2208.01498v2 | Cited as an arXiv preprint (2022) only; it is PRL 131, 180601 (2023) | Changed to `@article` (PRL 2023), keeping the arXiv id |
| AaronsonArkhipov13 | https://doi.org/10.4086/toc.2013.v009a004 | None | None |
| Ryser63 | MAA Carus Mathematical Monographs No. 14 (1963). The publisher record was not fetched; consistent with Björklund 2016's reference list | None | None |
| BravyiGosset16 | https://doi.org/10.1103/physrevlett.116.250501 ; arXiv:1601.07601 | Issue missing; the entry was in the bib but **never cited** | Added `number = {25}`; now cited in row 24 |
| BSS16 | https://doi.org/10.1103/physrevx.6.021043 ; arXiv:1506.01396 (conjecture χ_n ≥ 2^{Ω(n)} checked) | Issue missing | Added `number = {2}` |
| QPG21 | https://doi.org/10.22331/q-2021-12-20-606 ; arXiv:2106.07740 (α = log₂3/4 ≤ 0.3963) | None | None |
| NielsenChuang | https://doi.org/10.1017/cbo9780511976667 (CUP; 1st ed. 2000) | None | None |

### Added entries (4)

| Key | Source | Where cited |
|---|---|---|
| Bjorklund16 | https://doi.org/10.4230/LIPIcs.SWAT.2016.17 | BosonSampling paragraph: "Ryser is still the best exact method" was inaccurate for poly(n)-bit integer matrices |
| BJS11 | https://doi.org/10.1098/rspa.2010.0301 | First discussion of IQP circuits (§ converse reduction) |
| TD04 | https://doi.org/10.26421/qic4.2-5 | "polynomial-time hardness ... for shallow circuits" (§ Sampling vs exact amplitudes) |
| BGK18 | https://doi.org/10.1126/science.aar3106 | "unconditional separations for shallow circuits" (same sentence) |

### Text corrections in `quantum-note/main.tex`

1. BosonSampling paragraph: "Ryser … is still the best exact method" now reads "still essentially
   the best … (for poly(n)-bit integer matrices improved only to 2^{n−Ω(√(n/log n))} [Bjorklund16])".
2. Converse reduction: "the IQP analogue" now reads "the analogue for IQP circuits [BJS11]".
3. Sampling vs exact amplitudes: "polynomial or unconditional separations for shallow circuits"
   now cites [TD04, BGK18].
4. Table 3, row 24: "best known 2^{0.3963t}poly [QPG21]" now reads "best known exact
   stabilizer-rank simulation … [QPG21], after [BSS16, BravyiGosset16]".
5. Limitations (e): "publication venues are given only where we could confirm them" was replaced
   by a statement that all citations were checked on 30 Oct 2026, and that theorem numbers refer
   to the arXiv versions named in the bibliography.

## 3. Requested checks that led to no addition

- Curticapean–Lindzey–Nederlof, Björklund (determinant sums), BHKK (bounded-degree TSP),
  Cut&Count, BCKN, Caracciolo et al.: already cited. All were verified.
- BHKK "narrow sieves" (arXiv:1007.1161): not added. It concerns k-path and packing, and neither
  paper discusses it.
- Barvinok (low-rank permanent / TSP): not added. Neither paper discusses low-rank instances.
- Valiant (#P-completeness of the permanent): not added. The quantum note makes no #P-hardness
  claim about permanents.
- Wahl–Strelchuk, Markov–Shi, Aaronson–Chen, Dalzell et al., Morimae–Tamaki, Huang–Newman–Szegedy,
  Qassim–Pashayan–Gosset, Aaronson–Arkhipov: already cited. All were verified (Wahl–Strelchuk
  updated to its PRL version).

## 4. Residual items not fully verified

- Ryser63 and NielsenChuang (the 7-T-gate Toffoli circuit, N&C Fig. 4.9): checked only from
  bibliographic records and standard knowledge, not from the book text.
- CIP06 "[proof of Lemma 5]" (the binom(m+r, r) leaf count): the lemma's numbering and role were
  confirmed, but the formula was not readable in the extracted PDF text.
- Research notes (`research/tutte-plane.md`, `research/quantum-circuits.md`) still contain "from
  memory" remarks. They are not part of either paper and were not changed.
