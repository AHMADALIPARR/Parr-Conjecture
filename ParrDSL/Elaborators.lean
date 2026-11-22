/-
Copyright (c) 2026 Ahmad Ali Parr / Bel Esprit D'Accord Irrevocable Trust (EIN 42-697643).
Released under the GNU Affero General Public License v3.0 or later.
See the file LICENSE for details.
Authors: Ahmad Ali Parr
BOW-Ω-φ-∂-2026
-/

/-!
# ParrDSL — Elaborators (macro layer)

Surface syntax → GKN / BitFlip / Riemann terms via `macro_rules`.
Reliable on Lean 4.19 without custom `TermElab` state machines.

| Syntax        | Expands to                     |
|---------------|--------------------------------|
| `N(M)`        | `J3O.cubicNorm M`              |
| `M♯`          | `J3O.adjoint M`                |
| `I₄(s)`       | `FTS56.I4 s`                   |
| `⟨s, t⟩ₛ`     | `FTS56.symp s t`               |
| `c ·ₚ s`      | `c • s`                        |
-/

import ParrDSL.Syntax
import GKN.I4_CommRing

open GKN_I4_CommRing

namespace ParrDSL

/-- `N(M)` → cubic norm. -/
macro_rules
  | `(N($m:term)) => `(J3O.cubicNorm $m)

/-- `M♯` → Freudenthal adjoint. -/
macro_rules
  | `($m:term♯) => `(J3O.adjoint $m)

/-- `I₄(s)` → quartic invariant. -/
macro_rules
  | `(I₄($s:term)) => `(FTS56.I4 $s)

/-- `⟨s, t⟩ₛ` → symplectic pairing. -/
macro_rules
  | `(⟨$s:term, $t:term⟩ₛ) => `(FTS56.symp $s $t)

/-- `c ·ₚ s` → scalar action. -/
macro_rules
  | `($c:term ·ₚ $s:term) => `($c • $s)

end ParrDSL
