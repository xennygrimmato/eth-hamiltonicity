# lab notebook — non-algebraic n² matrix multiplication over F₂

Newest at the bottom. Each entry: idea → ran → result → what it changes.

## 0. Setup (2026-11-26)
pip: python-sat, z3-solver, pycryptosat (CryptoMiniSat, native XOR clauses).
Scripts: `mc_sat.py` (E1 exact MC via SAT + CEGAR on input rows), `e2_wordram.py`, `e3_pack.py`.

## E1a. Matrix–vector 2×2·2×1 Boolean multiplicative complexity
- Idea: smallest case of "function, not formal identity": XOR-AND circuits, XOR free, gates may
  feed gates, x²=x allowed. Bilinear rank of ⟨2,2,1⟩ is 4.
- Ran: `python3 mc_sat.py 2 2 1 3` and `... 4`.
- Result: k=3 UNSAT (certified on 42 of the 64 rows, 39 s), k=4 SAT. **MC = 4 = rank.** (Trivial
  case — two independent inner products of length 2, each needs 2 ANDs by Mirwald–Schnorr's
  "half the rank of the symplectic matrix" for a single quadratic form.)
- Changes: nothing yet; sanity check of the encoder.

## E2. Word-RAM baselines (w = 64)
- Ran `e2_wordram.py`: M4RM (Gray-code tables, k = log n − 1) and Strassen–Winograd over F₂ with
  M4RM base at 256; exact 64-bit word-op counts; checked against numpy product up to n=1024.
- Result (word ops):

  | n | M4RM | Strassen+M4RM |
  |---|---|---|
  | 512 | 4.25e5 | 4.75e5 |
  | 1024 | 2.91e6 | 3.39e6 |
  | 2048 | 2.05e7 | 2.40e7 |
  | 4096 | 1.48e8 | 1.69e8 |

  M4RM local exponent 2.70, 2.77, 2.82, 2.85 (it is ≈ 2n³/(w log n)); Strassen slope ≈ 2.82
  (→ 2.807). Word ops per output bit at n=4096: 8.8 (M4RM) and growing ∝ n/(w log n).
- Changes: word parallelism + tables give exactly a w·log n factor over n³, i.e. polylog. To reach
  n²·polylog the per-output cost must be polylog, so the n-fold "sharing" has to come from a
  genuinely different source than packing bits into words. (This is the Ω-side statement:
  any word-RAM algorithm with w = O(log n) is a Boolean circuit of size ~ ops·w·polylog, so it
  inherits whatever Boolean circuit lower bound holds.)
