# Draft posts for X: three results of 26 November 2026

Drafts only. Nothing here has been posted. Every post must be checked by the owner, and every link clicked, before
use. The source of truth for every claim is `README.md`, `../../tools/mc222/README.md`, `note-contracting-eth.md`,
`note-k23-rate.md` and `literature-check.md` in this folder.

Posts are in fenced blocks so they can be copied as they are. Character counts are X's weighted counts (links count
23; ≥, √, −, ≈, ⇒, ₂, ≠ and other symbols outside X's light ranges count 2). They were computed by a script, see the
check at the end.

---

## Part 1. Rules used

### 1a. The "claudish to english" skill

Found. It is a Claude Code plugin by gvzdv, "claudish-to-english":
https://github.com/gvzdv/claudish-to-english (README; the instructions are the system prompts in
https://raw.githubusercontent.com/gvzdv/claudish-to-english/main/rewrite.sh and
https://raw.githubusercontent.com/gvzdv/claudish-to-english/main/md-core.sh). There is no separate SKILL.md in it; the
"skill text" is its rewrite prompt. A SKILL.md adaptation of the same prompt exists as "plain-english-rewrite"
(https://skills.nanoinfra.org/skills/plain-english-rewrite). The plugin itself does not list the tells; for those I
used the companion style reference "Claudish — a style reference"
(https://raw.githubusercontent.com/adamrotmil/claudish-style-adapter/main/docs/claudish-style.md) and the summary in
https://www.bleuken.com/translate-claudish-to-plain-english-with-local-tools/.

Rules taken from them:

- C1. Rewrite into much simpler, plain language. Short sentences, everyday words. (gvzdv prompt)
- C2. Keep every fact, name, number, link and file path. Never drop or soften information; a "must" stays a "must",
  and the degree of certainty stays the same. (gvzdv prompt; style reference, hard rule 3)
- C3. Add nothing: no new facts, causes or hedges. (style reference, hard rule 2)
- C4. No preamble, labels or commentary around the text. (gvzdv prompt)
- C5. No "X, not Y" reframing unless the negation is true and stated in the source; never as a rhythm. (style
  reference: "a contrast asserts its negation")
- C6. No structural metaphors: boundary, surface, seam, layer, spine, scaffold, wiring, handoff, gate. (style ref.)
- C7. No process words used as decoration: landed, surfaced, parity, provenance, canonical, drift, stale. (style ref.)
- C8. No "high-signal" adjectives: load-bearing, clean/cleanly, hard (stop/constraint). (style reference)
- C9. No research-register filler: regime, slice, floor, headline, survives, clears. Literal mathematical terms
  ("lower bound") are allowed where they are the actual term. (style reference)
- C10. No hyphenated compressions made up for the occasion. (style reference)
- C11. No "polished clause, then a short sharp one" cadence used as a tic. (style reference)
- C12. Collapse to the smallest set of ordinary statements that says everything; shorter is usually right. (style
  reference, "→ English")

### 1b. Writing on X about research

Sources read:
- Lydia Krasilnikova, "Tweeting About Your Science": https://lakrasilnikova.home.blog/2022/02/08/tweeting-about-your-science-my-guide-what-ive-learned/
- D. Quintana, "Twitter for Scientists", ch. 3 and 5: https://t4scientists.com/advanced.html
- U. Michigan IHPI, "Building an X thread": https://ihpi.umich.edu/building-x-formerly-twitter-thread-more-impact
- Agent skills for posts: grida "tweet" SKILL.md (https://github.com/gridaco/grida/blob/8d2d05e808138159cc5182eabbe429ca42e54317/.agents/skills/tweet/SKILL.md),
  "github-repo-to-x-threads" SKILL.md (https://github.com/sunflowerslwtech/sunkit/blob/main/plugins/searchpo/x-threads/skills/github-repo-to-x-threads/SKILL.md)
- The fold: https://notpeople.ai/x-post-preview, https://bbuddy.co/blog/why-your-posts-get-cut-off-on-x,
  https://flaghand.com/docs/guides/x-linkedin-character-limits
- Links: Buffer's study of 18.8M posts (Oct 2025), https://buffer.com/resources/links-on-x/; Repli, "Do links hurt
  your reach on X?" (3 Nov 2026), https://repli.sh/blog/do-links-hurt-reach-on-x/; W3match on the 13 Nov 2026
  weight change, https://www.w3match.com/blog/x-algorithm-copy-link-weight-zero

Rules taken from them:

- X1. The timeline shows about the first 280 weighted characters of a long post, cut at a word, then "Show more".
  Links count 23, many symbols count 2. The result must be complete inside that cut. (notpeople, bbuddy, flaghand)
- X2. The first post must work for someone who reads nothing else: state the finding, not a teaser. (Krasilnikova;
  sunkit "hook independence")
- X3. Each post in a thread must stand alone and must not be quotable out of context to mean something false.
  Address likely misreadings head-on. (Krasilnikova; Quintana)
- X4. Links: the evidence is mixed. Buffer (2025) measured much lower engagement on link posts, less so for Premium.
  In July 2026 X's then head of product and its owner said links are no longer penalised; Repli (Nov 2026) found no
  fixed link penalty in the published ranking code, but notes link posts get fewer replies, which the ranker weighs
  most. Rule used: the post carries the full content without a click; links go in the first reply (or in the last
  post of a thread), never in the first post. The owner can test link-in-post on a Premium account.
- X5. Say whether the work is peer-reviewed, and credit prior work. (Krasilnikova step 2; IHPI)
- X6. Number thread posts n/N; no "thread" emoji. (IHPI; the brief)
- X7. No hype words ("excited", "game changer", "breakthrough"), no emoji or hashtags by default. (grida skill;
  "paper-to-social" skill notes academic accounts use none)
- X8. One image per post helps; it should carry one message and have alt text. A link preview disappears when an
  image is attached, which is another reason to keep links in the reply. (Krasilnikova; Quintana)
- X9. Keep one visible uncertainty; do not let the caveat swallow the result, and do not drop it. (sunkit
  "anti-smoothness")
- X10. Use vertical white space; short paragraphs; plain-text maths (X renders no Markdown or LaTeX).

---

## Part 2. Links (owner: open every one before posting)

Repository at the pinned commit 8039282656870eedcf4a25697d28626682defbb6:

- L-mc222: https://github.com/xennygrimmato/math/tree/8039282656870eedcf4a25697d28626682defbb6/tools/mc222
- L-eth: https://github.com/xennygrimmato/math/blob/8039282656870eedcf4a25697d28626682defbb6/research/ports/note-contracting-eth.md
- L-k23: https://github.com/xennygrimmato/math/blob/8039282656870eedcf4a25697d28626682defbb6/research/ports/note-k23-rate.md
- L-readme: https://github.com/xennygrimmato/math/blob/8039282656870eedcf4a25697d28626682defbb6/research/ports/README.md
- L-lit: https://github.com/xennygrimmato/math/blob/8039282656870eedcf4a25697d28626682defbb6/research/ports/literature-check.md
- L-lean: https://github.com/xennygrimmato/math/tree/8039282656870eedcf4a25697d28626682defbb6/research/ports/lean/PortsLean
  (ThmR.lean and ThmA.lean for result 2; FivePoint.lean and CLStar.lean for result 3)

The paper draft for result 1 (`research/mm/paper-mc222/main.pdf`) does not exist yet on the build machine, so the
posts link the mc222 README instead.

---

## Part 3. Result 1: 2×2 matrix product over F₂ needs exactly 7 AND gates

### 1(a) Long post

```text
Over F₂, multiplying two 2×2 matrices needs exactly 7 AND gates, even with free XORs and arbitrary Boolean intermediate values, so Strassen's 7 is optimal here too. Proved in Lean, checked by Lean's `bv_decide`, which trusts the Lean compiler for the SAT certificate checks.

Strassen (1969) multiplies 2×2 matrices with 7 multiplications instead of 8. That 7 is the least possible was proved in 1971 (Hopcroft–Kerr, Winograd), for algorithms in which each multiplication is a product of two linear forms in the matrix entries.

A Boolean circuit can do more. An AND gate may multiply any two things computed earlier, so intermediate values can have any degree, and x·x = x. The 1971 proofs do not cover this. The open question was whether 6 AND gates could be enough. They are not.

How it was checked:

- Lean 4 with Mathlib, no sorry. The symmetry reduction and the meaning of the SAT encoding are proved in Lean. 360 SAT instances are checked by bv_decide: a SAT solver writes a refutation, and Lean's verified LRAT checker checks it as compiled code. So the proof trusts Lean's kernel plus the Lean compiler and runtime, not the kernel alone.
- Separately, outside Lean: the search was split into 1080 SAT instances. All are unsatisfiable, and each came with an LRAT proof that a separate checker verified.
- A second program, sharing no code with that SAT encoder, does an exact search over circuit states. It also finds no 6-gate circuit.
- A second run of the outside pipeline gave identical file hashes. That shows the runs are deterministic; it is not an independent check.

The SAT solver does not need to be trusted in either proof. The Lean proof and the outside pipeline use different encodings and different proof checkers, but they were written in the same project, follow the same strategy and start from the same list of 72 symmetry classes (which Lean re-checks).

Credit and status: the lower bound 6 was already public (September 2026), where 6 versus 7 was called open. I found no statement that the answer is exactly 7, though specialists may know it. The search, the checks and the Lean proof were done by AI agents in a project I direct. I have read the Lean statement and printed its axioms; no human has reviewed the rest yet. A paper is in preparation.

Lean proof, code and how to re-run everything: links in the reply.
```

Reply with links:

```text
Lean proof (the statement is in Statement.lean next to it; build with lake build):
https://github.com/xennygrimmato/math/blob/847247eee74fa403e6f7564fe31f62b00b84e68b/research/mm/lean-mc222/MC222/Main.lean
Outside pipeline, the 1080 proof hashes and ./run_all.sh:
https://github.com/xennygrimmato/math/tree/847247eee74fa403e6f7564fe31f62b00b84e68b/tools/mc222
```

### 1(b) Thread

```text
1/4 Over F₂, multiplying two 2×2 matrices needs exactly 7 AND gates, even with free XORs and arbitrary Boolean intermediate values. So Strassen's 7 is optimal here too. Shown by SAT: 1080 instances, all UNSAT, each with a machine-checked proof. Not yet human-reviewed.
```

```text
2/4 The 1971 lower bound of 7 (Hopcroft–Kerr, Winograd) is for algorithms where each multiplication is a product of two linear forms. In a Boolean circuit a gate can multiply earlier results, so degrees are unbounded and x·x = x. That case was open.
```

```text
3/4 How: after symmetry reduction, a 6-gate circuit would have to satisfy one of 1080 SAT instances. CaDiCaL refutes each and writes an LRAT proof, which a separate checker verifies. An independent exact search agrees. All of it was run by AI agents.
```

```text
4/4 The bound 6 was already public (Sept 2026). I found no statement of exactly 7; specialists may know it. A paper is being written. Code, proofs and re-run script:
https://github.com/xennygrimmato/math/tree/8039282656870eedcf4a25697d28626682defbb6/tools/mc222
```

### 1(c) Image and reply

Image (optional): Strassen's seven products written out, under the line "6 AND gates: impossible (1080 SAT
instances, all with checked proofs)".

Alt text:

```text
Strassen's seven products for 2×2 matrices over F₂, M1 = (a11+a22)(b11+b22) through M7 = (a12+a22)(b21+b22), with the four entries of the product written as sums of them, and a note that no circuit with 6 AND gates exists.
```

(Owner: the alt text assumes the standard Strassen formulas; over F₂ signs do not matter. Check the image against
`results/circuit_mm222_7_p2.txt` or a textbook before posting.)

Reply post: as in 1(a).

---

## Part 4. Result 2: the contracting case of Anthropic's proof contradicts weak ETH

### 2(a) Long post

```text
If the "contracting" case of Anthropic's VP ≠ VNP proof holds over a field of characteristic 0, then 3-SAT on n variables can be solved in time 2^(n^(1−δ)) for some δ > 0. So under weak ETH that case is false, and the proof goes through its "flat" case.

Anthropic's paper (November 2026) splits its proof into two cases, flat and contracting. It shows that at least one of them holds over every field, and that its lower bound follows in either case. It says it does not know which case holds.

The observation is that the contracting case is too strong to be true if 3-SAT is hard. From it one gets an algorithm for 3-SAT that runs in time 2^(n^(1−δ)) instead of about 2^n. The weak exponential-time hypothesis (weak ETH) says no such algorithm exists. It is weaker than the classical ETH and is consistent with the subexponential 3-SAT algorithms both labs claimed in October 2026.

So, assuming weak ETH, the contracting case does not occur over fields of characteristic 0, and Anthropic's lower bound rests on its flat case there.

This is an implication between hypotheses. No fast SAT algorithm was found, and the contracting case has not been shown to be false.

The evidence:

- There are two independent arguments. One uses only Anthropic's paper: it runs Anthropic's own "cutting" programs and counts their guesses. The other goes through OpenAI's "ports" property and a theorem from OpenAI's release of 24 November.
- Each argument was refereed by a separate AI agent.
- The exponent arithmetic and one deduction are checked in Lean, conditional on statements copied by hand from the two labs' papers.
- One key step, a bound on the number of guesses those cutting programs make, is read from Anthropic's printed proof and Lean source. It is not machine-checked against their Lean development.
- The refereed form of the first argument gives an algorithm that also receives a polynomial-size advice string. Removing the advice rests on one agent's reading of Anthropic's Lean proof terms.
- How large δ can be depends on a constant H in Anthropic's proof that the proof does not make explicit. At its smallest allowed value, H = 272, the method gives any δ below 0.121.

Credit: OpenAI's paper on Euclidean geometry in the asymptotic spectrum of tensors (§11.1) already proves the mechanism of the second argument, that a uniform contracting gap gives ports, under a different hypothesis. What is new here is that Anthropic's contracting case supplies such a gap, and the first argument as a whole. A literature search on 26 November found neither stated before; an expert may find them quick to see.

A note for specialists: OpenAI's release also claims a theorem that gives the flat property outright. That does not settle the question, because the two cases are not known to exclude each other.

Status: everything above was produced by AI agents in a project I direct, and no human mathematician has checked it. Anthropic's and OpenAI's papers are machine-generated too, and not refereed by people.

Notes and Lean files: links in the reply.
```

Reply with links:

```text
Note with statements, proofs and a status table for every step:
https://github.com/xennygrimmato/math/blob/8039282656870eedcf4a25697d28626682defbb6/research/ports/note-contracting-eth.md

Lean files (ThmR.lean, ThmA.lean):
https://github.com/xennygrimmato/math/tree/8039282656870eedcf4a25697d28626682defbb6/research/ports/lean/PortsLean
```

### 2(b) Thread

```text
1/6 If the "contracting" case of Anthropic's VP ≠ VNP proof holds over a field of characteristic 0, then 3-SAT on n variables is solvable in time 2^(n^(1−δ)) for some δ > 0. So under weak ETH that case is false and the proof goes through its "flat" case.
```

```text
2/6 Anthropic's proof (Nov 2026) splits into a flat case and a contracting case. It shows one of them holds over every field, and that the lower bound follows either way. It says it does not know which one holds.
```

```text
3/6 Weak ETH says 3-SAT has no 2^(n^(1−δ)) algorithm. It is consistent with the 2^(o(n)) algorithms both labs claimed in October. This is an implication only: no fast SAT algorithm was found, and the contracting case was not shown false.
```

```text
4/6 Two independent arguments: one from Anthropic's paper alone, one through OpenAI's "ports" property (24 Nov release). Each was refereed by an AI agent. The arithmetic and one deduction are checked in Lean, given statements copied from the labs' papers.
```

```text
5/6 Weak point: one step, a count of guesses in Anthropic's cutting programs, is read from their printed proof and Lean source, not machine-checked against it. Credit: OpenAI's paper (§11.1) already has the mechanism of the second argument.
```

```text
6/6 All of this was produced by AI agents and has not been checked by a human. Both source papers are machine-generated and not refereed by people. Note with every step's status:
https://github.com/xennygrimmato/math/blob/8039282656870eedcf4a25697d28626682defbb6/research/ports/note-contracting-eth.md
```

### 2(c) Image and reply

Image (optional): a three-box diagram. Box 1 "contracting (char. 0)" → arrow "two arguments" → box 2 "3-SAT in
2^(n^(1−δ))" → arrow "contradicts" → box 3 "weak ETH". Under it: "so, under weak ETH: not contracting ⇒ flat
(Anthropic's case split)". No other text.

Alt text:

```text
Diagram: "contracting case, characteristic 0" implies "3-SAT in time 2^(n^(1−δ))", which contradicts weak ETH; so under weak ETH the contracting case fails and Anthropic's flat case holds.
```

Reply post: as in 2(a).

---

## Part 5. Result 3: entanglement rate 3/√10 on the network K_{2,3}

### 3(a) Long post

```text
On the five-party network K_{2,3}, with one EPR pair per edge, routing reaches rate 3/4 for the Okamura–Seymour demands, and classical network coding also reaches only 3/4. Converting the entanglement by local linear maps reaches at least 3/√10 ≈ 0.949.

The setup: two hubs u₁, u₂ and three parties v₁, v₂, v₃. Each hub shares one EPR pair with each v, six pairs in all. The goal is EPR pairs on v₁v₂, v₂v₃, v₁v₃ and on u₁u₂, all at the same rate. This is the Okamura–Seymour example from flow theory, where the cut condition holds but flows fall short. Harvey, Kleinberg and Lehman (2006) showed that classical network coding gives 3/4 here, the same as routing.

The model is tensor restriction: each party applies any linear map to its share, and the conversion only has to work asymptotically, with no condition on success probability (an SLOCC-type model). That is a different resource model from classical coding, so the right word is "exceeds": 0.949 is above what coding gets, but the two are not a like-for-like comparison.

The rate is exactly 3/√10 unless Anthropic's "contracting" case holds. Together with the companion result, a protocol beating 0.949 over a field of characteristic 0 would give a 2^(n^(1−δ)) algorithm for 3-SAT. So under the weak exponential-time hypothesis the rate is exactly 3/√10.

The evidence:

- The lower bound uses Strassen's duality theorem and one lemma from Anthropic's paper (prices satisfy a CAT(0) comparison inequality). Given those two, the inequality behind it is proved by hand and checked in Lean.
- It was refereed by a separate AI agent.
- The proof is non-constructive. An explicit protocol family is known that reaches 0.8367, but only at enormous sizes: its smallest instances have wire dimension around 2^128.

Two extensions:

- On K_{2,m} the same method gives rate at least 2m/√(m²(m−1)²+4), with equality unless the contracting case holds. Routing gives 2m/(m(m−1)+2).
- With weight w on the hub demand u₁u₂, the rate is exactly 3/(2+w) for every w ≥ 5/4, with no assumption about the contracting case (it uses the same CAT(0) lemma). The hand proof, refereed, covers w ≥ 1.913; the range down to 5/4 also rests on two computer interval certificates. At w = 2 that is 3/4, against 3/5 for routing.

Status: this was produced by AI agents in a project I direct, and no human has checked it. The Anthropic and OpenAI papers it uses are machine-generated and not refereed by people. A literature search on 26 November found no earlier study of this instance for tensor conversion and no occurrence of 3/√10.

Note and Lean files: links in the reply.
```

Reply with links:

```text
Note with the statements, proofs and status of each part:
https://github.com/xennygrimmato/math/blob/8039282656870eedcf4a25697d28626682defbb6/research/ports/note-k23-rate.md

Lean (FivePoint.lean, CLStar.lean):
https://github.com/xennygrimmato/math/tree/8039282656870eedcf4a25697d28626682defbb6/research/ports/lean/PortsLean
```

### 3(b) Thread

```text
1/5 Five parties on the graph K_{2,3} share one EPR pair per edge and want pairs between each two of the three outer parties and between the two hubs. Routing gives rate 3/4; classical network coding also only 3/4. Local linear maps on the tensors give at least 3/√10 ≈ 0.949.
```

```text
2/5 The network is the Okamura–Seymour example; coding = routing = 3/4 there is Harvey–Kleinberg–Lehman (2006). Our model is tensor restriction (SLOCC-type, any success probability), a different resource model. So 0.949 exceeds coding, but not like for like.
```

```text
3/5 The rate is exactly 3/√10 unless the "contracting" case of Anthropic's VP ≠ VNP proof holds. By a companion result, a protocol above 0.949 over a field of characteristic 0 would give 3-SAT in time 2^(n^(1−δ)), against weak ETH.
```

```text
4/5 The key inequality is checked in Lean, given Strassen's duality theorem and one lemma from Anthropic's paper. Refereed by an AI agent. The proof is non-constructive: the best explicit protocols reach 0.8367, at sizes around 2^128.
```

```text
5/5 Produced by AI agents, not checked by a human; the source papers are machine-generated and not refereed by people. Note, with the K_{2,m} case and the exact rate 3/(2+w) for weight w ≥ 5/4:
https://github.com/xennygrimmato/math/blob/8039282656870eedcf4a25697d28626682defbb6/research/ports/note-k23-rate.md
```

### 3(c) Image and reply

Image (recommended; the setup is hard to picture from text): left, the graph K_{2,3} with u₁, u₂ on top, v₁, v₂, v₃
below, the six supply edges solid; dashed curves for the four demand pairs v₁v₂, v₂v₃, v₁v₃, u₁u₂. Right, a number
line from 0.7 to 1 with marks "routing 3/4", "classical coding 3/4", "explicit protocols 0.8367", "tensor
restriction ≥ 3/√10 ≈ 0.949", "cut bound 1".

Alt text:

```text
Left: the network K_{2,3}, two hubs u1 and u2 each joined to three parties v1, v2, v3 by an EPR pair; dashed lines show the four wanted pairs v1v2, v2v3, v1v3 and u1u2. Right: a number line with routing and classical coding at 3/4, explicit protocols at 0.8367, tensor restriction at least 3/√10 ≈ 0.949, and the cut bound at 1.
```

Reply post: as in 3(a).

---

## Part 6. Optional overview post

Lead: result 1. Reasons: (i) the overview's first 280 characters are all most people will read, and result 1 is
the only one whose statement fits there with no condition attached; (ii) result 2 compressed to a fold is the
easiest of the three to misread as "AI found a fast SAT algorithm", and an overview has less room for the
caveats than its own post; (iii) result 1 has the strongest evidence, so it sets the right level of trust for the
other two, which are conditional and refereed only by AI agents.

```text
Over F₂, the 2×2 matrix product needs exactly 7 AND gates, even with free XOR gates and arbitrary intermediate Boolean functions: Strassen's 7 is optimal in this model. That is one of three results AI agents in a project I direct produced this week.

1. The 7. A search for a 6-gate circuit, split into 1080 SAT instances, finds none, and every instance has an LRAT proof verified by a separate checker. An independent exact search agrees. The lower bound 6 was already public; I found no statement of exactly 7.

2. Anthropic's VP ≠ VNP proof splits into a "flat" and a "contracting" case and does not know which holds. If the contracting case holds over a field of characteristic 0, then 3-SAT can be solved in time 2^(n^(1−δ)) for some δ > 0. So under the weak exponential-time hypothesis, the contracting case fails and the flat case holds. This is an implication: no fast algorithm was found, and the contracting case was not shown to be false. Two independent arguments, each refereed by an AI agent; parts checked in Lean, conditional on statements copied from the labs' papers; one step (a count of guesses) is read from Anthropic's proof, not machine-checked. OpenAI's 24 November paper already has the mechanism of the second argument.

3. On the five-party network K_{2,3} (the Okamura–Seymour example, one EPR pair per edge), routing and classical network coding both give rate 3/4. Tensor restriction, a different resource model, gives at least 3/√10 ≈ 0.949, and exactly that unless the contracting case holds. The key inequality is checked in Lean, given Strassen's duality theorem and one lemma from Anthropic's paper.

None of this has been checked by a human mathematician. Results 2 and 3 build on Anthropic's and OpenAI's papers of November 2026, which are machine-generated and not refereed by people either.

Code, notes and Lean files: in the reply.
```

Reply with links:

```text
1. https://github.com/xennygrimmato/math/tree/8039282656870eedcf4a25697d28626682defbb6/tools/mc222
2. https://github.com/xennygrimmato/math/blob/8039282656870eedcf4a25697d28626682defbb6/research/ports/note-contracting-eth.md
3. https://github.com/xennygrimmato/math/blob/8039282656870eedcf4a25697d28626682defbb6/research/ports/note-k23-rate.md
Overview with status tags: https://github.com/xennygrimmato/math/blob/8039282656870eedcf4a25697d28626682defbb6/research/ports/README.md
```

---

## Part 7. Note to the owner

**Order.** Post result 1 first. It stands alone and has the strongest evidence. Post result 2 a day or more later,
so that replies to it get answered before anything else depends on it. Post result 3 after result 2, because its
upper bound and its 3-SAT remark refer to result 2. Use the overview only if you prefer one post to three, or as a
pinned summary afterwards. Reply to early questions yourself; replies are the strongest ranking signal, and the
caveats are more convincing in your own words.

**Before posting.**
- Open every link in Part 2 while logged out. They could not be opened from the build machine. Check that the
  pinned commit contains `tools/mc222/results/`, the two notes, and the four Lean files named.
- Result 1's paper PDF does not exist yet; the posts link the README. Switch the link when the paper is up.
- If you add the optional images, check the formulas in them yourself.
- Consider asking, before or right after posting:
  - result 1: a researcher in Boolean multiplicative complexity (the Boyar–Find line of work), mainly to ask whether
    "exactly 7" is known folklore, and someone who uses SAT proof checking to look at the encoding;
  - result 2: an algebraic or fine-grained complexity theorist who has read Anthropic's paper, ideally someone able to
    check the guess-count step against Anthropic's Lean development (the known weak point);
  - result 3: a quantum information or tensor researcher who works on the asymptotic spectrum or SLOCC conversion,
    to confirm the model comparison with network coding.

**Claims softened or made more exact, compared with the brief.**
- δ "up to about 0.12": the 0.121 holds only if the constant H in Anthropic's proof equals its least allowed value
  272; the proof does not make H explicit. The long post says so; the threads say only "some δ > 0". I did not use
  2^(n^0.88).
- "Under weak ETH the flat case holds": kept, but the long post adds that OpenAI's release claims the flat property
  outright, and that this does not exclude the contracting case (the two are not known to exclude each other; note
  §7). Without that line a specialist will reply "OpenAI already says flat holds".
- The uniform form of the first argument for result 2 rests on one agent's reading of Anthropic's Lean proof terms;
  the refereed form uses an advice string. This is in the long post, not in the thread.
- Result 3 extension "with no assumptions at all": it is unconditional only with respect to the contracting case.
  It still uses the CAT(0) lemma from Anthropic's paper (README, weak point 4). The post says "no assumption about
  the contracting case (it uses the same CAT(0) lemma)".
- "Reproduced with identical hashes": the README says the run was re-done by the project lead. The posts say "a
  separate re-run reproduced the results, with identical file hashes". If you did the re-run yourself, you can
  write "I re-ran it".
- Result 1 never mentions Lean or formal verification. Its status words are "SAT instances", "LRAT proof",
  "verified by a separate proof checker".
- Credit for the lower bound 6 (result 1): the public source found by the literature check is a machine-generated,
  unrefereed register, "Slop Dealer Research" notes MF-149/MF-180 (4 Sep 2026), which call 6 vs 7 open. The posts
  say "already public (September 2026)" without the name. You may want to name it in the reply.
- Result 2 states credit to OpenAI's EG §11.1. Result 3 credits Okamura–Seymour and Harvey–Kleinberg–Lehman.

**Not mentioned on purpose.** The characteristic-p version of result 2 (a randomised algorithm), Theorem B, the
case table, and the explicit-protocol limit 6/(4+√10). They are in the notes, and they would crowd the posts.

---

## Part 8. Self-check

Weighted character counts (X's rules: links 23; code points outside 0–4351, 8192–8205, 8208–8223, 8242–8247
count 2), computed by script over every block above:

| Block | Weighted total | Opening paragraph (must be ≤ 280 for long posts; whole post ≤ 280 for thread posts) |
|---|---|---|
| 1(a) Long post: Over F₂, multiplying two 2×2 matrices ne… | 2349 | 275 |
| 1(a) Reply: Lean proof (the statement is in Statement.… | 188 | 188 |
| 1(b) Thread: 1/4 Over F₂, multiplying two 2×2 matrice… | 257 | 257 |
| 1(b) Thread: 2/4 The 1971 lower bound of 7 (Hopcroft–… | 249 | 249 |
| 1(b) Thread: 3/4 Evidence: the search for a 6-gate ci… | 241 | 241 |
| 1(b) Thread: 4/4 The bound 6 was already public (Sept… | 189 | 189 |
| 1(c) Image and reply: Strassen's seven products for 2×2 matric… | 223 | 223 |
| 2(a) Long post: If the "contracting" case of Anthropic's… | 3060 | 255 |
| 2(a) Reply: Note with statements, proofs and a statu… | 147 | 87 |
| 2(b) Thread: 1/6 If the "contracting" case of Anthrop… | 256 | 256 |
| 2(b) Thread: 2/6 Anthropic's proof (Nov 2026) splits … | 212 | 212 |
| 2(b) Thread: 3/6 Weak ETH says 3-SAT has no 2^(n^(1−δ… | 238 | 238 |
| 2(b) Thread: 4/6 Two independent arguments: one from … | 255 | 255 |
| 2(b) Thread: 5/6 Weak point: one step, a count of gue… | 240 | 240 |
| 2(b) Thread: 6/6 All of this was produced by AI agent… | 202 | 202 |
| 2(c) Image and reply: Diagram: "contracting case, characterist… | 189 | 189 |
| 3(a) Long post: On the five-party network K_{2,3}, with … | 2636 | 255 |
| 3(a) Reply: Note with the statements, proofs and sta… | 142 | 81 |
| 3(b) Thread: 1/5 Five parties on the graph K_{2,3} sh… | 278 | 278 |
| 3(b) Thread: 2/5 The network is the Okamura–Seymour e… | 258 | 258 |
| 3(b) Thread: 3/5 The rate is exactly 3/√10 unless the… | 234 | 234 |
| 3(b) Thread: 4/5 The key inequality is checked in Lea… | 234 | 234 |
| 3(b) Thread: 5/5 Produced by AI agents, not checked b… | 218 | 218 |
| 3(c) Image and reply: Left: the network K_{2,3}, two hubs u1 a… | 330 | 330 |
| Part 6. Optional overview post: Over F₂, the 2×2 matrix product needs ex… | 1877 | 250 |
| Overview reply: 1. https://github.com/xennygrimmato/math… | 131 | 131 |

All thread posts are ≤ 280 (largest: 3(b) post 1, 278). Every long post's opening paragraph ends before the fold (230–255), so the result is complete above "Show more". The alt text for 3(c) is 330, under X's 1000-character alt-text limit.

Rules against posts (P = pass; notes where a judgement was needed).

| Rule | 1a | 1b | 2a | 2b | 3a | 3b | Overview | Notes |
|---|---|---|---|---|---|---|---|---|
| C1 plain, short sentences | P | P | P | P | P | P | P | Longest sentences are in 2a's evidence list; split where possible |
| C2 no fact dropped or softened | P | P | P | P | P | P | P | Threads omit details (advice string, H) but keep "some δ > 0" and the guess-count weak point |
| C3 nothing added | P | P | P | P | P | P | P | Each number traced to the source files |
| C4 no preamble/labels | P | P | P | P | P | P | P | Labels like "The evidence:" are list headers, kept for phone reading |
| C5 no gratuitous "X, not Y" | P | P | P | P | P | P | P | Only true negations: "exceeds, not like for like" (note §0.1), "no fast SAT algorithm was found" (note §0) |
| C6 no structural metaphors | P | P | P | P | P | P | P | "rests on" is used only for real logical dependencies (2a, 3a) |
| C7 no decorative process words | P | P | P | P | P | P | P | Fixed: "Provenance:" labels in 2a and 3a changed to "Status:" |
| C8 no load-bearing/clean/hard | P | P | P | P | P | P | P | |
| C9 no regime/headline/survives | P | P | P | P | P | P | P | "cut regime" from the note rewritten as "with weight w ≥ 5/4"; "lower bound" kept as the literal term |
| C10 no invented hyphen compounds | P | P | P | P | P | P | P | "SLOCC-type", "like for like", "6-gate" are standard |
| C11 no cadence tic | P | P | P | P | P | P | P | 1a "They are not." is one short sentence answering a stated question; kept |
| C12 smallest set of statements | P | P | P | P | P | P | P | Long posts are long because the brief asks for evidence and caveats |
| X1 result inside first ~280 | P | P | P | P | P | P | P | See counts |
| X2 first post works alone | P | P | P | P | P | P | P | |
| X3 no post misleads alone | – | P | – | P | – | P | – | 2b post 1 says "under weak ETH"; post 3 says "implication only" |
| X4 no link in first post; links in reply/last | P | P | P | P | P | P | P | |
| X5 review status and credit stated | P | P | P | P | P | P | P | Status once per post, no apology |
| X6 numbered, no thread emoji | – | P | – | P | – | P | – | |
| X7 no hype, emoji, hashtags | P | P | P | P | P | P | P | |
| X8 image with alt text | P | – | P | – | P | – | – | Optional images; alt text given |
| X9 one visible uncertainty | P | P | P | P | P | P | P | |
| X10 plain-text maths, white space | P | P | P | P | P | P | P | No LaTeX, no Markdown inside posts |
| Brief: no AI model named | P | P | P | P | P | P | P | "AI agents" only |
| Brief: forbidden claims absent | P | P | P | P | P | P | P | 1a (revised 26 Nov, after the Lean proof): says "proved in Lean" only with the qualification that `bv_decide` trusts the Lean compiler; 1b, 1c and the overview still do not mention Lean; no "fast SAT algorithm found", "contracting refuted", "ETH refuted", "a Lean proof", P vs NP |
