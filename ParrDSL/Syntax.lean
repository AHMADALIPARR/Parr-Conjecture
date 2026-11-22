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

* Jordan / octonion algebra: `J₃(𝕆)`, cubic norm `N(·)`, adjoint `·♯`
* Freudenthal triple system: `FTS₅₆`, quartic invariant `I₄`
* Homogeneity assertions: `I₄ is homogeneous of degree 4`
* Quantum: bit-flip recovery, syndrome uniqueness
* Spectral / logit: spectral gap, Gates normalisation

This file only declares **syntax**. Elaborators live in `ParrDSL.Elaborators`;
tactics and automation live in `ParrDSL.Tactics` / `ParrDSL.Automation`.
-/

import Lean

open Lean Meta Elab

namespace ParrDSL

/-- Category for domain-specific term syntax. -/
declare_syntax_cat parr_term

/-- Category for domain-specific command syntax. -/
declare_syntax_cat parr_cmd

-- ══════════════════════════════════════════════════════════════
-- 1. Algebraic term notation
-- ══════════════════════════════════════════════════════════════

/-- Cubic norm: `N(M)` elaborates to `J3O.cubicNorm M`. -/
syntax (name := parrCubicNorm) "N(" term ")" : term

/-- Freudenthal adjoint: `M♯` elaborates to `J3O.adjoint M`. -/
syntax (name := parrAdjoint) term:max "♯" : term

/-- Quartic invariant: `I₄(s)` elaborates to `FTS56.I4 s`. -/
syntax (name := parrI4) "I₄(" term ")" : term

/-- Symplectic pairing: `⟨s, t⟩ₛ` elaborates to `FTS56.symp s t`. -/
syntax (name := parrSymp) "⟨" term "," term "⟩ₛ" : term

/-- Scalar action sugar: `c · s` on FTS56 / J3O (when not already overloaded). -/
syntax (name := parrScale) term:70 " ·ₚ " term:71 : term

-- ══════════════════════════════════════════════════════════════
-- 2. Statement macros (surface syntax for common claims)
-- ══════════════════════════════════════════════════════════════

/--
`assert_homogeneous I₄ degree 4` expands to a theorem skeleton
  `∀ c s, I₄(c · s) = c^4 * I₄(s)`.
-/
syntax (name := parrAssertHomog)
  "assert_homogeneous" ident "degree" num : command

/--
`assert_recovery bitflip` expands to the master recovery theorem form:
  encode → inject X_i → syndrome → correct → decode recovers b.
-/
syntax (name := parrAssertRecovery)
  "assert_recovery" &"bitflip" : command

/--
`assert_gates_norm g` expands to `∑ i, logitSimplex g i = 1`.
-/
syntax (name := parrAssertGates)
  "assert_gates_norm" term : command

-- ══════════════════════════════════════════════════════════════
-- 3. Tactic syntax
-- ══════════════════════════════════════════════════════════════

/--
`parr_homog` — try to close a homogeneity goal of the form
  `I4 (c • s) = c ^ n * I4 s` using the library lemma + `ring`.
-/
syntax (name := parrHomogTac) "parr_homog" : tactic

/--
`parr_diag` — simplify under a diagonal (`IsDiag`) hypothesis:
  rewrite octonion components to 0, then `ring` / `simp`.
-/
syntax (name := parrDiagTac) "parr_diag" : tactic

/--
`parr_bitflip` — discharge finite Bool × Fin 3 case analysis for
  the three-qubit bit-flip code (uses `fin_cases` + `cases` + `simp`).
-/
syntax (name := parrBitflipTac) "parr_bitflip" : tactic

/--
`parr_ring` — domain-aware ring: `simp` the GKN / J3O simp-lemmas, then `ring`.
-/
syntax (name := parrRingTac) "parr_ring" : tactic

/--
`parr_auto` — lightweight automation: try `parr_homog`, `parr_diag`,
  `parr_bitflip`, then `parr_ring`, then `decide` / `trivial`.
-/
syntax (name := parrAutoTac) "parr_auto" : tactic

-- ══════════════════════════════════════════════════════════════
-- 4. Pretty-printing helpers (delaborators registered later)
-- ══════════════════════════════════════════════════════════════

/-- Marker attribute for terms that should pretty-print with Parr notation. -/
register_option parr.pp.notation : Bool := {
  defValue := true
  descr := "pretty-print GKN / FTS terms using ParrDSL notation (N(·), ·♯, I₄(·))"
}

end ParrDSL
