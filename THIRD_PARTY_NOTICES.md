# Third-party notices

This repository is MIT-licensed (see `LICENSE`), except for the files below. They are copied
verbatim, or nearly so, from Apache-2.0-licensed projects and remain under the Apache License 2.0
(see `LICENSE-APACHE-2.0`).

| File | Source | License |
|---|---|---|
| `lean/EthFollowup/Comparator.lean` | comparator definitions from `openai/math`, `lean/ComparatorChallenges/SubexponentialSAT.lean`, commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`; the `sorry`'d theorem is turned into a proposition | Apache-2.0, © OpenAI |
| `lean/EthFollowup/AnthropicStatement.lean` | `eth/MainResults.lean` from `anthropics/formal-math`, commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5` (verbatim, after a header comment) | Apache-2.0, © 2026 Anthropic, PBC |

`lean-bridge/setup.sh` and `lean-bridge-anthropic/setup.sh` download the upstream projects at the
pinned commits. Those projects are not redistributed here.
