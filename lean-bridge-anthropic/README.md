# lean-bridge-anthropic

Discharges the hypothesis `MainResults.MainTheorem` of `lean/EthFollowup/AnthropicHamiltonian.lean`
with Anthropic's own proof (`anthropics/formal-math`, folder `eth`, Lean v4.33.1).

* `bridge/EthFollowup/AnthropicStatement.lean` is the only file that differs from `lean/`. It does
  `import MainResults` (Anthropic's statement file) in place of our verbatim copy.
* `bridge/EthFollowup/AnthropicUnconditional.lean` defines
  `hamParity_allGraphs_unconditional := hamParity_allGraphs_anthropic MainResults.mainTheorem`.
* `setup.sh WORKDIR` fetches Anthropic's folder at the pinned commit, copies the bridge in and builds
  everything.

**Checked 27 Oct 2026:**
* Anthropic's build: `Build completed successfully (9768 jobs)`.
* `scripts/PrintAxioms.lean`: `MainResults.mainTheorem` and `MainResults.ethIsFalse` depend only on
  `[propext, Classical.choice, Quot.sound]`.
* The bridge builds, and `#print axioms EthFollowup.Anthropic.hamParity_allGraphs_unconditional` gives
  `[propext, Classical.choice, Quot.sound]`.
* Our files compiled unchanged against Anthropic's Mathlib (0df444a).
