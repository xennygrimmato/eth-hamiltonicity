# Referee report: circuit-lower-bounds.md (E^NP ⊄ SIZE(ε·n·√log n))

**Verdict: sound, with fixable gaps.** The mathematical claim holds. The Lean plan is feasible, but it understates
two changes and states a target theorem that is too weak (issues 1–3).

## What I re-derived

**Primary sources.**
* **Williams, SICOMP 2013** (improved-algs-lbs2.pdf, fetched).
  * Thm 1.1, Thm 1.2 and Lemma 3.2 are as quoted in the note.
  * Thm 6.1 is a *sketch* in §6 ("Discussion"). It guesses a circuit C of cn gates and calls CircuitSAT on D, which
    has O(cn) wires and 3n+O(1) inputs. The tableau has size O(2^{3n}), each cell's clauses come from an O(n)-size
    circuit computed from the indices (i, j), and Tseitin is applied.
  * There is no PCP and no polylog or n·s blow-up. Only constant factors appear: E^NP inputs have length O(n), so
    s is evaluated at O(n).
* **JMV, arXiv 1311.3171 (ICALP'15)** (fetched).
  * Cor 2(1): CircuitSAT for linear-size circuits in 2^n/n^{ω(1)} implies E^NP ⊄ linear size.
  * Cor 3(1′): ¬ETH suffices, and they note that only this item was previously known [Wil13 Thm 6.1].
  * §6 proof: three copies of C_x plus an NC0 clause map on j ∈ {0,1}^{n+O(log n)}. The SAT time is
    2^{|j|}/|j|^{ω(1)} = o(2^n).
  * Both routes keep the check circuit at 3s + O(n) gates.

**Lean.**
* `StAlg` (Interfaces.lean l.47): ∀c₀ ∃N, …, `C.length ≤ c₀(m+1)` → `Acc N m (2^(m/8))`.
* `no_linear_circuits` (Main l.76) uses `hc` only at chain points `p s ≥ 2^a`.
* `StForm` / `FormOK`: the formula is `(tseitin … ++ [[out]]).dedup` with Nv ≤ 3|C| + a₀(L+1) + g(e). Tseitin
  gives 4 clauses per gate (`gateCl`), so **M ≤ 4Nv + 1**, and the formula is Nodup with 3-literal clauses.
* `exists_threshold` hard-codes δ = 1/(32(3c₀+a₀+1)) and two factors of 2^{m/32}.
* `stAlg_of` takes the δ-form `StEngine`.
* This is the Thm 6.1 route, made self-contained by lazy diagonalisation. It is confirmed.

**Clause bound.**
* Paper Cor 11 / Thm 1 and `MainResults.MainTheorem` give 2^{C·k·m/√log m}, with m = number of clauses. The bound is
  uniform in n.
* The hypotheses are:
  * k ≥ 1;
  * `IsKCNF` (clauses of ≤ k literals, and `φ.Nodup`, i.e. no repeated clause);
  * m ≥ 2 and n ≥ 4;
  * `AllOccur`.
* Tseitin output meets these after the existing dedup and a renaming to the occurring variables.
* The engine form `Tied.TopM` (rates/GeneralPieces/Tied/Defs.lean l.74) is *proved*
  (`thmRunningTime_c_m_tied`, used in maintheorem/MainRoute/EveryMachine.lean). Its rate is
  eM ≤ G·k·m/√log₂(m+2).

**Arithmetic.**
* f(x) = x/√log₂(x+2) is increasing on all of ℕ.
* With s = ε(m+1)√log₂(m+2) and M ≤ 12s + 4a₀(m+1) + 4g + 1, we have log M = log m + O(loglog m).
* So the exponent is ≤ 3C·M/√log M = 36Cε·m(1+o(1)) + O(m/√log m).
* Requiring this to be ≤ m/32 − o(m) holds for ε < 1/(1152C). The note's ε = 1/(1200C) is fine.
* The "√log M vs √log m" distinction is immaterial.
* Hierarchy slack: the Lean route has a constant in the exponent (2^{m/8} vs 2^{bt}, bt ≥ 3m/8), and the JMV route
  has 2^n/n^{ω(1)}. Both are comfortably met.

## Issues

1. **(Major, Lean target) Statement 7 is not the i.o. claim and is close to vacuous.**
   * `¬HasCircuits L (⌊ε(n+1)√log(n+2)⌋)` only says that *one* n fails. For tiny ε, s(n) = 0 for many small n, so
     this can hold for trivial reasons.
   * `ENP.infinitely_often` derives the i.o. form by enlarging c, and that trick is unavailable for a fixed ε.
   * Fix: state `∀ N, ∃ n ≥ N, ¬DecidedAt L (s n) n`. Prove it by assuming circuits only for n ≥ N and passing N into
     the lower bound given to `hCode` in `no_linear_circuits`; `hc` is used only at `p s ≥ 2^a`. Small change.
2. **(Major, Lean plan item 6) State-size bound.**
   * `EngineOK` and `Stepped.Runs` require every state to have size ≤ c(N+2)^c. The δ-form engine (COUNTsplit) meets
     this.
   * The rate engine `TopM` is a PolyT function of (input, pad) with |pad| = 2^{eM}. "Build a pad, call AM" has
     exponential-size states and violates `EngineOK`.
   * Fix, either way:
     * relax the state bound to c(N+2)^c·2^{c·t(N,|ψ|)} through `runs_algo`, `base_le` and `exists_threshold`, and
       check that `PaddedDescent.exists_tm'` / `IsPolyT` tolerate it (the base^q factor becomes 2^{O(q·eM)}, which
       is absorbable); or
     * build a poly-space stepped rate engine.
   * This is the real bottleneck. The note's item 3 lists only the time change.
3. **(Minor, Lean) Count vs. decision.**
   * `EngineOK` demands the output `binary N (cntN N ψ)`, a count over all N variables.
   * `TopM` / `MainTheorem` count over the occurring variables only.
   * Either multiply by 2^{#free} (a shift) or weaken `EngineOK` to a decision spec (`runs_algo` only uses isZ). The
     note says "decision only" but omits this interface change.
4. **(Minor) The constant.**
   * ε is governed by the *effective* engine constant: G, the polynomial exponent of AM in the pad, and, if issue 2
     is fixed by relaxing state sizes, also q from `exists_tm'`.
   * It is not the paper's C. ε is still absolute: it is fixed before the table e, because q is obtained before e in
     `stAlg_of`. State it as ε = 1/(1200·C_eff).
5. **(Minor) JMV parametrisation.**
   * The E^NP language there has input (x, i) of length 2n + O(log n). So the check circuit has 3s(2n+O(log n)) + O(n)
     gates, not "3s(ℓ)+O(ℓ)".
   * This is harmless for s = εn√log n, since the constant is absorbed into ε.
6. **(Minor, attribution) Where "3s + O(n)" comes from.**
   * Williams' Thm 6.1 says only "O(cn) wires". The explicit 3s + O(n) is in JMV §6 and in Lean `StForm`.
   * The note should say Thm 6.1 is a sketch.
7. **(Minor, literature) The near-maximum bounds above E^NP.**
   * CHR24 (STOC'24; ECCC TR23-144) proves S₂E/1 ⊄ SIZE[2^n/n], and the same for Σ₂E and ZPE^NP/1.
   * The almost-everywhere bound S₂E ⊄ i.o.-SIZE[2^n/n] is Li24 (arXiv 2310.17762). The note's attribution of the
     i.o. bound for Σ₂E to CHR is likely swapped: check it.
   * Li–Yang 3.1n − o(n) is for affine dispersers (constructible in P). The ECCC abstract notes that a 10n bound was
     open even for NP; a superlinear bound for E^NP was open.
   * An ECCC listing TR26-260 (Oct 2026) claims 3.5n for P. I could not verify it. It is still linear, so it does not
     affect the claim.
   * "E^NP ⊄ SIZE(n^k) open" is consistent with these sources.
8. **(Minor) Novelty.** "First explicit superlinear rate for E^NP over B₂" is plausible but unverifiable. Keep the
   hedge.

## Lean plan feasibility

* Items 2, 4, 5 and 7 are small to moderate, including the i.o. fix (issue 1).
* Item 5: the new real-analysis lemma is routine, given that x/√log x is monotone.
* Item 6 is the main work and is harder than the note says. It needs:
  * the renaming adapter with AllOccur;
  * the count fix-up or a decision spec (issue 3);
  * a relaxed state-size bound or a poly-space rate engine (issue 2).
* The rest of the module is reused unchanged: tables, chains, L0, E^NP membership, `StForm` (already Nodup), and the
  clause count M ≤ 4Nv+1, which follows directly from `tseitin`.
