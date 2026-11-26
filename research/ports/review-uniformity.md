# Uniformity audit of the cutting program G (Theorem R)

Audit of 26 Nov 2026, answering item 4 of `review-theoremR.md`.
- Lean paths are relative to `scratchpad/fm/repo/vp-vnp`, where the scratchpad is
  `/tmp/claude-0/-home-user/203603f9-2e73-5176-8be9-30554548bda1/scratchpad/fm/repo/vp-vnp`.
- I worked by reading the sources. Nothing was built.

## Bottom line

**Verdict: (1), uniform with an n-independent table of constants that are not explicit. A Lean-checked version would
need a mechanical refactoring (2) whose correctness is very plausible.** Theorem R does not need to fall back to the
non-uniform version (3).

**1. Nothing the referee feared is genuinely non-constructive.**
- `TT` (from `thm_tree`) and `pc` (from `prop_pieces`) are structure literals: Paper/Tree.lean:1468–1512 and
  Paper/Pieces.lean:765–801.
- Their data fields are explicit functions of a few small combinatorial witnesses. Their sum-identity fields (`value`)
  are not part of any witness. They are theorems, proved for every choice of those witnesses that meets its spec:
  - `value := … tree_value hH hℓ …` (Tree.lean:1511);
  - `value := … lem_runnet … prop_pieces_identity …` (Pieces.lean:862–882).
- So the identities that cannot be checked by search never need to be searched for or checked.

**2. Every remaining v-dependent witness has a finite, decidable, combinatorial spec.**
- Examples: a subgroup chain, short words, an injective embedding, a bijection, a sorted order, a minimum found by
  bounded search, injective codes, a straight-line program (SLP) computing given functions, or the instruction
  decomposition of such an SLP.
- With the obvious algorithms each costs poly(v).
- Even the crudest search (the SLP conversion, which enumerates the input domain) costs 2^{O(v^{2Cp+1} log v)}.
  - Here Cp is the constant C of `prop_pieces`.
  - H = 16(a₀+217), with a₀ = a+e+6b₁+400 and b₁ = 3Cp+3e+a+8 (Cuts.lean:122, 127; Cuts.lean:466–469). So H ≥ 288·Cp.
  - Hence every search fits in the 2^{O(v^H)} budget of Theorem 1.

**3. Nothing depends on the input z.**
- `CutD` is `∀ z, z.size ≤ s → …` *about a fixed G* (NS1/Compose.lean:25–29).
- `thm_onecut` has `∃ G` before that quantifier (Cuts.lean:104–106).
- G depends only on (v, τ, s, k) and the constants. The `choose! R hR using h₂` at Compose.lean:94 is inside the proof
  of `CutD` for the composed program and does not affect the program `compC G₁ G₂` (Compose.lean:53).

**4. The contracting hypothesis enters only through `exists_laws hK`** (Paper/Laws.lean:456; used at Cuts.lean:573).
- It produces h, A, θ (Cuts.lean:574) and `VL : VLaws …`.
- `VLaws` (Nc/Tow/FromPrice.lean:27–56) is a finite object:
  - a finite index type `Di`;
  - for each d, a `Law` (Nc/G/Defs.lean:27–64) with finite types Ro, Sl, Cn, I, the maps a, b, c, d, lam, lab, len
    and a finite table `tab` with entries in A;
  - the integers a₁, G₁ and C₀ (C₁ = 4C₀).
- None of this depends on n or v. Its existence proof (Poincaré bound → Strassen duality, `thm_laws_poincare` and
  `thm_laws_over_field`, Laws.lean:53, 184) may be ineffective, but that concerns only the constant table.
- The two ∀-properties of the laws, L1 ("every load is below one of finitely many") and the identity `law`, are used
  as theorems. At run time they are used only through a bounded, decidable search (`tmin`/`Pick`, below).

**5. The one caveat is meta-level.**
- Replacing each `Classical.choose`/`obtain` by an *explicitly computed* object with the same spec preserves every
  theorem. The reason: `Classical.choose` is opaque, so a proof can use only `choose_spec`, and abstracting it into a
  parameter is a mechanical change.
- That is a statement about the proof terms, not a Lean theorem.
- To get it Lean-checked:
  - turn `Gam`, `host`, `idx`, `coQ`, `FQ`, `FU`, `eE`, the routes' words, `ch`, `Pl`, `Fintype.equivFin` uses and
    the SLP into parameters (or into computable `def`s);
  - restate `thm_onecut` as `∃ a₀ C v₀, ∀ v …, CutD … (Gprog v τ s k)`, with `Gprog` an explicit function of the
    constant table.
- No mathematical step changes.
- "Noncomputable" in these files means "no compiled code", for example `Classical.decEq` on a finite quotient or
  `Fintype.ofFinite`. It never means "mathematically ineffective".

## Classification table

Classes:
- **E**: explicit def.
- **S**: decidable finite spec, so search works.
- **K**: n-independent constant. It belongs in the table and may be non-effective; most K entries are also morally E.

Cost is the cost of producing the witness for one scale v, with M ≈ K+K = 2v^e and |G_n| ≤ c·M.

| # | Witness | Lean location | Class | Depends on | Cost / remark |
|---|---|---|---|---|---|
| 1 | field data h, A, θ, laws `VL`, a₁, C₀, `hgain` | `exists_laws` Laws.lean:456; `exists_setting` Cuts.lean:570–576; θ from `exists_theta` Nc/Dl/Last.lean:31ff | K | field + contracting hypothesis only | finite table: Di, the combinatorics of each law, table entries in A as words `WE` in θ, the generators of A. Ineffective existence (duality), irrelevant for uniformity |
| 2 | universal automaton S, Γ, Q, mu, i, e′, b0, b1, CU | `prop_universal` Paper/Universal.lean:29; used at Cuts.lean:108 | K (morally E) | θ only | fixed finite automaton (`exists_run_val`, Nc/Tape/ProgRun.lean:258) |
| 3 | a, e, Cp, v₁ and all exponents H, C₀, v₀, a₀, C | Cuts.lean:109–127, 466–469; Pieces.lean:667–683 | K | constants | natural numbers; not explicit (H is not explicit) but fixed |
| 4 | evaluators GR c cb, κ, for c ≤ Cp and every code cb | `choose GR κ hGR hGT` Cuts.lean:114–115 (`exists_group`, Nc/Grp/GroupThm.lean:29) | K | θ, mu, kinds (from the laws) | finitely many, n-independent. The spec `GroupOK` (Nc/Dl/Inst.lean:28) contains value identities, but as a constant that is harmless |
| 5 | symbol code cb | Pieces.lean:672–676 (`Fintype.equivFin (Option Γ)`) | K/S | Γ | constant, any injection |
| 6 | units ub = T/v^{a′}, load, U1, K = v^e, T, ℓ, X, Lc, bd, ev, ιb | Pieces.lean:685–697; Cuts.lean:154–348; Tree.lean:1416 | E | v, τ, s, k | arithmetic |
| 7 | bit strings of T, ub, ℓ | `exists_bits` Cuts.lean:306–308 (`bitsN`, a def) | E | numbers | poly |
| 8 | **tower** `tower h n h2` | Nc/Tower/Tower.lean:24–76 | E given 9–11 | n = least with M ≤ \|G_n\| (`Nat.find`, Tree.lean:1304–1305) | G_n = SL_h(F₂[s]/s^{n+1}) (Nc/Tower/Grp.lean:22); X_j = G_n/Γ_j (Inst.lean:33). The `Fintype.ofFinite` and `Classical.decEq` instances (Inst.lean:36, 38) are computable given Γ_j |
| 9 | subgroup chain `Gam := (exists_chain h n).choose` | Nc/Tower/Inst.lean:22; spec Nc/Tower/Chain.lean:34–35 (existence by Sylow) | S | n | spec: Γ₀ = ⊥, increasing, ⊂ Ker, \|Γ_j\| = b^j. Greedy index-2 extension (normaliser argument, as in the notebook): poly(\|G_n\|) = poly(v). Blind search 2^{O(v^{e+2})}. Both fit |
| 10 | host maps `(exists_host j i).choose` | Tower.lean:75; Inst.lean:429–437 | S | tower | injective, vertex condition; fibres of constant size 2^{ee h}: poly(v) |
| 11 | `idx` (Inst.lean:281), `coQ` (Coord.lean:64), `FQ` (Coord.lean:106), `FU` (Coord.lean:123) | Nc/Tower | S, constant size | h only | on SL_h(F₂) or U h: n-independent, O(1) or a table entry |
| 12 | short words / routes `R` | `exists_routes` Tower.lean:197–203 (`choose w` from `WL`, Words.lean:26); used at Tree.lean:1322 | S | tower, m = (C+1)(n+1)^7 | spec: a word of length ≤ m for each g. BFS in the Cayley graph: poly(v) |
| 13 | flag laws `FL = towFlag VL h2 n` | Nc/Vp/Main.lean:30–33 | E | VL, tower | identity equivalences |
| 14 | embedding `ch : Fin AA ↪ T.X 0` | `Function.Embedding.nonempty_of_card_le` Tree.lean:1413 | S | AA, tower | any injection: poly |
| 15 | place `Pl` | `exists_place` Nc/Tow/PlaceE.lean:29–60 (built with `equivFinOfCardEq`) | S (morally E) | ch, tower | any bijection fixing the base nodes: poly |
| 16 | move order `eE := (exists_mono_equiv …).choose` | Nc/Tow/Net.lean:293–294; proof is `Tuple.sort` (Relay.lean:122–128) | S (morally E) | moves | sort by time: poly |
| 17 | law choice at a vertex: `tmin := sInf {t \| ∃ d, Fits …}`, `Pick` (minimum d in a fixed enumeration of Di) | Nc/Tow/Flow.lean:81–86, 90–93 | E (bounded search) | loads, which are functions of (n, o), plus the law table | Fits is a finite comparison; t ≤ ⌈√NN2/a₁⌉ + 1 by L1 (Load3.lean:62–69, 98–113). This is the only place L1 is used, and only to bound the search |
| 18 | system, plan, parent, dead units, `up`, `isLaw`, `stage`, `cap` of TT | Tree.lean:1468–1512 (`sys R FL Pl`, `Tow.plan R FL Pl N N U1`, `treePar`, `deadU`, `treeUp`, `capN`) | E given 8–17 | the above | noncomputable defs, but recursions over finite data (e.g. `numS`, Flow.lean:94ff); poly(v) per argument (n, o) |
| 19 | **TT** (`thm_tree`, H.2) | `exists_thinTrees` Tree.lean:1397–1609; `thm_tree` Tree.lean:1628–1654; used `obtain ⟨TT⟩ := htree …` Pieces.lean:699 | E given 8–18 + 20 | v, T (via M = 2K, N = load, ℓ = ub) | a structure literal. `value` (l.1511), `node_le`, `copies_le` etc. are theorems valid for all choices in 9–16 |
| 20 | SLP of `TT.computed` (steps, inp, H) | `tree_computed` Tree.lean:1139ff, used at Tree.lean:1464 and 1597; built in stages by `tree_slp` (l.669–700) | S (morally E) | TT's functions | built from small explicit operations (`CY.op`, sums, comparisons). Spec: decidable (`SlpN`, Nc/SlpCalc.lean:22). Explicit version poly(v); blind check over the domain below |
| 21 | SLP table `tab`, indices `ix` | `prop_pieces_program` Pieces.lean:444–563 (`TT.computed` l.449, `SlpN.le` l.531, `choose ix hix` l.536) | S | 20 + `pieceFin` | k with fn k = f is decidable over the finite domain NN K U0 × (sys.N → Fin U1), of size 2^{O(v^{2Cp} log v)} |
| 22 | pieces `pieceFin TT k` | Pieces.lean:237–247 (`Staged.piece`) | E | TT, k | heavy/light rule of the printed proof; poly |
| 23 | **pc** (`prop_pieces`, J.2) | literal Pieces.lean:765–801; used `obtain ⟨pc⟩ := hP T k …` Cuts.lean:224 | E given 5, 6, 19–22 | v, T, k | `value`, `cut_le`, `all_le`, `blocks_le` are theorems (l.802–882) |
| 24 | codes `Cd` | `exists_codes` Cuts.lean:334 (Nc/Dl/Inst.lean:60–74; `exists_code` = `bitsN ∘ equivFin`, Nc/Dl/Code.lean:30–32) | S (morally E) | finite name sets of size ≤ 2^{Lc} = poly(v) | any injective code of length ≤ Lc: poly |
| 25 | tags `tg` | `choose tg htg` Cuts.lean:264–266 | S | pc.sys, kinds | index into a fixed list: poly |
| 26 | instructions of the SLP inside G (`slpStep`) | Nc/Dl/Run.lean:333–341: `if h : ∃ i, tab.fn k = tab.inp i … else if ∃ c … else if ∃ i j φ, ∀ x, …` with `h.choose` | S | tab | decidable over the domain of #21. Blind cost pS²·\|domain\|·poly = 2^{O(v^{2Cp+1})}. Refactored: read the instruction off the explicit SLP of #20, poly(v) |
| 27 | one-cut program G = `dealProg …` | `thm_onecut_program` Nc/Dl/Inst.lean:~120ff; `dealProg` Nc/Dl/Cut.lean:55–57; `dealF` Nc/Dl/DealThm.lean:26; called at Cuts.lean:411 | E given 4, 7, 21, 23–26 | v, τ, s, k | list of DSteps, `instTm`: size ≤ (dealC+3000)(X·Lc)^4 (Cuts.lean:447) |
| 28 | composition / iteration | `compC` Compose.lean:53; `thm_cut_compose` Compose.lean:89; `thm_cut_iterate` NS1/OneCut.lean:45ff (case split `by_cases hbase : τ*Λ < v^H*v^64`, l.147; compose l.227) | E | (τ_i, s_i, k_i) by explicit arithmetic | r + 1 = O(α) one-cuts |

None of these witnesses falls in class (N) in the sense of an ineffective argument about an unbounded or v-dependent
object. The only ineffective existence statements are in rows 1–4, and they are n-independent.

## Notes on specific points

**The value identities.** The referee's worry was that the specs of TT and pc contain identities "for every
network/word". That is true of the *types* `ThinTrees` (Tree.lean:324–330) and `PieceCut` (Pieces.lean:202–212). But
the proofs never obtain an inhabitant by an abstract existence argument: they build the literal and then *prove* the
identity.
- At the bottom, `exists_thinTrees` returns `Nonempty (ThinTrees …)` by `refine ⟨{ … value := fun n hv tab => tree_value
  … }⟩` (Tree.lean:1468, 1511).
- `thm_tree` passes this on unchanged (Tree.lean:1654).
- `prop_pieces` destructs it (`obtain ⟨TT⟩`, Pieces.lean:699). It then returns a new literal whose `value` is proved
  from `TT.value` (via `prop_pieces_identity`, Pieces.lean:86–124) and `lem_runnet`.
- So the `Nonempty` wrapper is pure packaging.

**Why other choices are allowed.** Each `obtain ⟨x, hx⟩ := (h : ∃ x, P x)` inside a proof, and each
`def … := h.choose`, leaves the rest of the development using x only through P x. Lean gives no way to inspect what
`Classical.choose` returns. So the same proof terms prove the statements for any x₀ with P x₀. That is the refactoring
of option (2): mechanical, with no new mathematics. For instance, `card_Gam`, `Gam_le` etc. (Inst.lean:24–31) are the
only interface of `Gam`.

**Budget check.**
- Theorem 1 (notebook §2.2) spends 2^{O(v^H)} anyway.
- All the searches above are bounded by 2^{O(v^{2Cp+1} log v)}, from enumerating functions on the domain
  NN K U0 × (sys.N → Fin U1). The bounds come from `steps_le`, `outcomes_le` (Pieces.lean:192, 201): U0, U1,
  |sys.N|, K+K+A′ are all ≤ v^{Cp}.
- Since H ≥ 288·Cp, these searches cost 2^{o(v^H)}.
- With the explicit constructions (greedy chain, BFS words, staged SLP), the cost is poly(v).
- Either way, v ↦ G_v is computable within budget by a fixed machine. G_v depends only on (v, τ, s, k) and the table of
  rows 1–4.

**What the constant table is.**
- h, θ, and generators for A.
- The laws: Di, the finite combinatorics of each law, its table entries as words in θ, a₁, C₀.
- The universal automaton (S, Γ, Q, mu, i, e′, b0, b1, CU).
- The finitely many evaluator programs GR c cb with κ.
- The integers a, e, Cp, v₁, a₀, C, H, C₀, v₀.
- A fixed enumeration of Di, used by `Pick`.

The evaluation step of Theorem R also needs ψ : A → L into a number field (notebook §2.3). That adds the images ψ(θ) to
the table. It is also n-independent.

**Residual risk.**
- Low. The argument above is a reading of the proof terms, not a compiled check.
- The one place to double-check when refactoring is that no proof uses *definitional* unfolding of a specific
  enumeration, such as `Fintype.equivFin` or `Fintype.ofFinite`, beyond its spec. Sums over `univ` do not depend on the
  enumeration. The order-sensitive uses (`Pick`, `eE`, codes) are stated through their specs.
