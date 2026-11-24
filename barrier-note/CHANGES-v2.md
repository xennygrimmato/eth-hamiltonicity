# Changes from v1 to v2 (24 Nov 2026)

Hexagon 2611.00149. v2 records two announcements made after v1. Neither is refereed, and we have not
reproduced either.

- **[Ni26]** J. Ni, exact S(N), π(N) and a prime in (N, 2N] in 2^{O(b/√log b)}. Announced 15 Nov 2026.
- **[AnthropicVP26]** Anthropic, VP ≠ VNP over every field. Claimed 24 Nov 2026. Its README says no
  human mathematician has checked it.

The line numbers are those of `main.tex` in v2. The v1 line is given as "was". No theorem,
proposition or equation number changes, because the new section is numbered last (Section 13). The
Lean statements are unchanged. Our summary of Ni's work is `research/primes-rh/NI-2611.md`.

| # | v2 lines (was) | Edit | Rationale |
|---|---|---|---|
| 1 | 72 (72) | `\date` now reads "version 2, 24 November 2026" and points to §13. | Marks the version. |
| 2 | 97–100 (97) | Abstract, last sentence. "would separate VP from VNP" becomes "would imply VP ≠ VNP". Added: VP ≠ VNP is now claimed (unrefereed) but does not give the cap. In one of its two cases (it is unknown which holds) it gives e_K ≥ 1/(16√K). Exact π(x) and prime finding have been announced by a route outside our models, which overtakes two rows of the map if confirmed. | Required update. The wording is shortened so that page 1 has no overfull vbox. |
| 3 | 135–136 (132) | Intro, where exact π(x) is listed among the targets the engines "seem to miss". Added a parenthetical pointing to §13. | Avoids an unqualified claim that is now contested. |
| 4 | 275–277 (271) | Outline. One sentence describing §13. States that the rest of the text is as in v1 except where it points to §13. | Reader orientation. |
| 5 | 1117–1118 (1111–1112) | Table `tab:map`. The rows "prime finding" and "exact π(x)" get the mark †. | The "out of reach" headline of these rows is overtaken if Ni's claim holds. |
| 6 | 1124–1127 (1118) | Caption of `tab:map`, † note: "overtaken by [Ni26], if confirmed (unrefereed)". The "why" and "proved" entries remain true but are route-specific: product-tree verifiers, integer divisor networks, residue queries. | The Lean theorems cited in those rows remain true. Ni's real analytic weights with final rounding were never covered by our models. |
| 7 | 1131 (1122) | Iterated-product paragraph. "the only identities we know" becomes "the only identities we knew when writing version 1". | The claim was too wide. |
| 8 | 1153–1157 (1144) | Iterated-product paragraph, closing parenthetical. The iterated product is not necessary. Ni's route uses Ramanujan sums, quadrature weights and a single rounding step. Thms 7.1, 7.2 and Props 7.3, 7.4 do not apply to it. | Qualifies the paragraph, as requested. |
| 9 | 1201–1202 (1188) | Change (iv) in §8. Added a note that Ni announces a different change that avoids the k-fold product. | (iv) is no longer the only change that brings prime counting into reach. |
| 10 | 1208–1210 (1194) | Meta-barrier lead. Prop. meta is unchanged, but how it should be read is qualified by [AnthropicVP26]. | Signposting. |
| 11 | 1242–1257 (1226–1229) | Paragraph after Prop. meta. The v1 reading is kept and labelled as v1. Added: VP ≠ VNP can no longer be offered as the reason the cap is out of reach, and it does not imply the cap, since (ii) runs only from the cap to the separation. The flat case of [AnthropicVP26, §2.3] bounds exactly P_K = f_{K,λ}. That bound is log₂ L ≥ λK^{3/2}/16 for λ ≥ 100√K, i.e. e_K ≥ 1/(16√K). This is above the query bound (K−1)/K², but far below c/log K, and it does not show that c/log K is optimal. It holds only conditionally, because it is not known which case holds. It is the first bound beyond the query bound in this model. Part (iii), the Boolean case, is unaffected. | Required rewording of Prop. meta's surrounding text. The paper's convention is log = log₂ (its §"Notation"), so the constant transfers exactly. The condition λ ≥ 100√K holds for the λ = K of Prop. meta once K ≥ 10⁴. |
| 12 | 1291–1292 (after 1262) | Question `q:product`. If Ni's claim is confirmed, π(x) and prime finding follow without an answer to this question. | Qualifies the open question, as requested. |
| 13 | 1536–1537 (1506–1507) | Limitations. "would separate" becomes "would imply". VP ≠ VNP is now claimed but does not by itself give the cap. | Consistency with edit 11. |
| 14 | 1567–1568 (1537) | Conclusion, the same change as edit 13, with a citation. | Consistency. |
| 15 | 1573–1575 (1542) | Conclusion, last sentence. The v1 claim that q:product "would decide whether exact π(x) is within the engines' reach" is now stated as v1's, and the conclusion notes that, if Ni's claim is confirmed, the question no longer decides it. | Consistency with edit 12. |
| 16 | 1576–1624 (new) | New §13 "Developments since version 1 (added 24 November 2026)", `\label{sec:v2}`. It summarises both claims, tags each as unrefereed or claimed, and gives three bullet points per claim on what changes here and what does not. It ends before the Acknowledgements. | Requested section. It is placed at the end so that no v1 numbering changes. |
| 17 | 1752–1757; 1884–1891 (new) | `\bibitem{AnthropicVP26}` (after Anthropic26) and `\bibitem{Ni26}` (after Nguyen26). Both are marked unrefereed. | Requested bibliography entries. |
| 18 | `refs.bib`, end | The same two entries as `@misc`. | Keeps `refs.bib` in sync with the inlined bibliography. |

Build: `latexmk -pdf main.tex` in `barrier-note/`. It gives 25 pages (v1 had 24), with no errors,
undefined references or overfull boxes. The three hyperref "Token not allowed" warnings were already
present in v1. `main.pdf` is tracked and has been rebuilt. `main.aux`, `.log`, `.out`, `.fls` and
`.fdb_latexmk` are excluded through `.git/info/exclude`.
