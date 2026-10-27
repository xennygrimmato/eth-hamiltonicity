import Lake
open Lake DSL

/-! Bridge workspace: builds openai/math's SubexponentialSAT development (fetched by `setup.sh`
into `OAI/`) and instantiates this repo's conditional theorems with the upstream proof
`exact_count_and_sat`, making them unconditional. -/

package «EthBridge» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib OAI where
  roots := #[`OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final]
  globs := #[.submodules `OAI.Algorithms.SubexponentialSAT]

@[default_target] lean_lib EthFollowup where
  srcDir := "bridge"
  roots := #[`EthFollowup.Unconditional]
  globs := #[.submodules `EthFollowup]
