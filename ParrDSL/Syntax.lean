/-
Copyright (c) 2026 Ahmad Ali Parr / Bel Esprit D'Accord Irrevocable Trust (EIN 42-697643).
Released under the GNU Affero General Public License v3.0 or later.
See the file LICENSE for details.
Authors: Ahmad Ali Parr
BOW-Ω-φ-∂-2026
-/

/-!
# ParrDSL — Syntax layer

Domain-specific mathematical notation for the Parr Conjecture formalisation:

* Jordan / octonion algebra: cubic norm `N(·)`, adjoint `·♯`
* Freudenthal triple system: quartic invariant `I₄`, symplectic form `⟨·,·⟩ₛ`
* Scalar action sugar: `·ₚ`
* Tactics: `parr_homog`, `parr_diag`, `parr_bitflip`, `parr_ring`, `parr_auto`

Elaborators: `ParrDSL.Elaborators`.
Tactics: `ParrDSL.Tactics`.
Automation: `ParrDSL.Automation`.
-/

import Lean

open Lean

namespace ParrDSL

-- ══════════════════════════════════════════════════════════════
-- 1. Algebraic term notation
-- ══════════════════════════════════════════════════════════════

/-- Cubic norm: `N(M)` elaborates to `J3O.cubicNorm M`. -/
syntax:max (name := parrCubicNorm) "N(" term ")" : term

/-- Freudenthal adjoint: `M♯` elaborates to `J3O.adjoint M`. -/
syntax:max (name := parrAdjoint) term:max "♯" : term

/-- Quartic invariant: `I₄(s)` elaborates to `FTS56.I4 s`. -/
syntax:max (name := parrI4) "I₄(" term ")" : term

/-- Symplectic pairing: `⟨s, t⟩ₛ` elaborates to `FTS56.symp s t`. -/
syntax:max (name := parrSymp) "⟨" term "," term "⟩ₛ" : term

/-- Scalar action sugar: `c ·ₚ s` → `c • s`. -/
syntax:70 (name := parrScale) term:70 " ·ₚ " term:71 : term

-- ══════════════════════════════════════════════════════════════
-- 2. Tactic syntax
-- ══════════════════════════════════════════════════════════════

/-- Close homogeneity goals `I4 (c • s) = c^n * I4 s`. -/
syntax (name := parrHomogTac) "parr_homog" : tactic

/-- Simplify under `IsDiag` hypotheses. -/
syntax (name := parrDiagTac) "parr_diag" : tactic

/-- Exhaustive Bool × Fin 3 case analysis for bit-flip recovery. -/
syntax (name := parrBitflipTac) "parr_bitflip" : tactic

/-- Domain-aware ring: GKN/J3O simps then `ring`. -/
syntax (name := parrRingTac) "parr_ring" : tactic

/-- Try `parr_homog` / `parr_diag` / `parr_bitflip` / `parr_ring` / `decide`. -/
syntax (name := parrAutoTac) "parr_auto" : tactic

/-- Pretty-print option for Parr notation. -/
register_option parr.pp.notation : Bool := {
  defValue := true
  descr := "pretty-print GKN / FTS terms using ParrDSL notation (N(·), ·♯, I₄(·))"
}

end ParrDSL
