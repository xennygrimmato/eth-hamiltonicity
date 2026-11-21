# Team protocol (primes-rh)
Board: `python3 /home/user/eth-hamiltonicity/research/primes-rh/board.py read` (announce, subtasks, notes, landed).
Loop: read board → claim/add subtask (`board.py claim NAME ID`, `board.py add NAME "title" "detail"`) → work in your own folder `/home/user/eth-hamiltonicity/research/primes-rh/NAME/` (notebook.md + scripts) → `board.py land NAME "what" "file" "[R]|[K]|[N]|[C]"`, `board.py note NAME "..."` → re-read board, continue.
Rules:
- Iterate fast: idea → smallest experiment on real data (primes up to 10^7–10^9 with sympy/primesieve/numpy) → verdict → next idea. Time-box each idea (~45–60 min); log every idea with an honest verdict, including dead ends and WHY they die.
- Avoid idea basins: after two failed variants of one idea, switch to a genuinely different angle. Crazy ideas welcome; test them cheaply.
- Re-read the board every ~30 min and build on others' results (cite files). Do not wait for the lead.
- Tags: [R] complete proof, [K] known with citation, [N] computation with script, [C] conjecture/heuristic. Mark statements that use RH as "under RH".
- Write only in your own folder and the board. No git commits. Disk < 50 MB per helper. Prior art: before claiming novelty, search (WebSearch / arXiv API https://export.arxiv.org/api/query / Polymath4 wiki michaelnielsen.org/polymath1 "Finding primes").
- Finish by returning: what you landed, best idea and its status, what you would do next.
Context: our parity result — /home/user/eth-hamiltonicity/parity-note/main.tex (method: chain lemma C_L(n) ≡ [n squarefree] mod 2, one-count identity Σ τ^<(m) C_L(m) ≡ π(I) mod 2, counting engine 2^{O(n/√log n)}), Lean in /home/user/eth-hamiltonicity/lean/EthFollowup/Primes/ and lean-bridge-anthropic/bridge/EthFollowup/Primes/. Prior barrier notes: /home/user/eth-hamiltonicity/research/prime-finding.md, research/iterated-product.md.
