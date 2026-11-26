/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import PortsLean.ANFragment.Machine

/-!
# Verbatim definitions copied from anthropics/formal-math `vp-vnp` (no proofs)

* `app`   : `NS1/Step.lean` l.58
* `listT` : `NS1/Lists.lean` l.21
* `foldB`, `foldF` : `NS1/Lists.lean` l.90, l.95
* `appF`  : `NS1/Lists.lean` l.195
* `pickB`, `pickF` : `NS1/Lists.lean` l.315, l.319
* `stepC`, `compC` : `NS1/Compose.lean` l.50, l.53

`PortsLean/ANFragment/Machine.lean` is `NS1/Machine.lean` copied verbatim (it imports only
Mathlib and typechecks unchanged against Mathlib v4.36.0).
-/

namespace NS1

/-- `NS1/Step.lean` l.58 -/
def app (p : Tree) (e : Fm) : Fm := .run (.quote p) e

/-- `NS1/Lists.lean` l.21 -/
def listT : List Tree → Tree
  | [] => .nil
  | x :: xs => .cons x (listT xs)

/-- `NS1/Lists.lean` l.90 -/
def foldB (step : Fm) : Fm := .ite (.tl (.tl .id))
  (.run (.hd .id) (.cons (.hd .id) (.cons (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
    (.tl (.tl (.tl .id)))))) (.hd (.tl .id))

/-- `NS1/Lists.lean` l.95 -/
def foldF (step s l : Fm) : Fm := app (foldB step).code (.cons (.quote (foldB step).code) (.cons s l))

/-- `NS1/Lists.lean` l.195 -/
def appF (a b : Fm) : Fm := foldF .id b (foldF .id (.quote .nil) a)

/-- `NS1/Lists.lean` l.315 -/
def pickB : Fm := .ite (.tl .id)
  (.ite .guess (.hd (.tl .id)) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) .fail

/-- `NS1/Lists.lean` l.319 -/
def pickF (l : Fm) : Fm := app pickB.code (.cons (.quote pickB.code) l)

/-- `NS1/Compose.lean` l.50 -/
def stepC (G : Tree) : Fm := lett (.cons (app G (.hd .id)) (.tl .id)) (appF (.hd .id) (.tl .id))

/-- `NS1/Compose.lean` l.53 -/
def compC (G G' : Tree) : Fm := lett (app G .id) (foldF (stepC G') (.quote .nil) .id)

end NS1
