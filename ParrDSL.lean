/-
Copyright (c) 2026 Ahmad Ali Parr / Bel Esprit D'Accord Irrevocable Trust (EIN 42-697643).
Released under the GNU Affero General Public License v3.0 or later.
See the file LICENSE for details.
Authors: Ahmad Ali Parr
BOW-Ω-φ-∂-2026
-/

/-!
# ParrDSL — Custom Lean DSL for the Parr Conjecture

A domain-specific language layer over the formal developments in this repository.

## Modules

| Module | Role |
|--------|------|
| `ParrDSL.Syntax` | Notation declarations (`N(·)`, `·♯`, `I₄(·)`, `⟨·,·⟩ₛ`, tactics) |
| `ParrDSL.Elaborators` | `macro_rules` expanding surface syntax to GKN terms |
| `ParrDSL.Tactics` | `parr_homog`, `parr_diag`, `parr_bitflip`, `parr_ring`, `parr_auto` |
| `ParrDSL.Automation` | Named lemma bundles for simp / exact |
| `ParrDSL.Examples` | Worked examples (build-tested) |
| `ParrDSL.AMPL` | AMPL-style mathematical programming models grounded in machine-checked theorems |

## Quick start

```lean
import ParrDSL

open GKN_I4_CommRing ParrDSL

example {R} [CommRing R] (c : R) (s : FTS56 R) :
    I₄(c ·ₚ s) = c ^ 4 * I₄(s) := by
  parr_homog
```

## AMPL models

```lean
import ParrDSL.AMPL
open ParrDSL.AMPL

#eval model_I4_scale |>.toAMPL
#check ampl_grounded_in_master
```
-/

import ParrDSL.Syntax
import ParrDSL.Elaborators
import ParrDSL.Tactics
import ParrDSL.Automation
import ParrDSL.AMPL
