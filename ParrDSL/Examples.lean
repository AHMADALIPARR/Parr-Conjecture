/-
Copyright (c) 2026 Ahmad Ali Parr / Bel Esprit D'Accord Irrevocable Trust (EIN 42-697643).
Released under the GNU Affero General Public License v3.0 or later.
See the file LICENSE for details.
Authors: Ahmad Ali Parr
BOW-Ω-φ-∂-2026
-/

/-!
# ParrDSL — Worked examples

Demonstrates custom notation, elaborators, and tactics against the
live GKN / BitFlip / RiemannMetatron libraries.
-/

import ParrDSL.Syntax
import ParrDSL.Elaborators
import ParrDSL.Tactics
import ParrDSL.Automation
import GKN.I4_CommRing
import BitFlipCode.BitFlipCode
import RiemannMetatron.RiemannMetatron

open GKN_I4_CommRing
open ParrDSL

variable {R : Type*} [CommRing R]

-- ══════════════════════════════════════════════════════════════
-- 1. Notation elaborates correctly
-- ══════════════════════════════════════════════════════════════

/-- `N(M)` is definitionally `J3O.cubicNorm M`. -/
example (M : J3O R) : N(M) = J3O.cubicNorm M := rfl

/-- `M♯` is definitionally `J3O.adjoint M`. -/
example (M : J3O R) : M♯ = J3O.adjoint M := rfl

/-- `I₄(s)` is definitionally `FTS56.I4 s`. -/
example (s : FTS56 R) : I₄(s) = FTS56.I4 s := rfl

/-- `⟨s, t⟩ₛ` is definitionally `FTS56.symp s t`. -/
example (s t : FTS56 R) : ⟨s, t⟩ₛ = FTS56.symp s t := rfl

/-- `c ·ₚ s` is definitionally `c • s`. -/
example (c : R) (s : FTS56 R) : c ·ₚ s = c • s := rfl

-- ══════════════════════════════════════════════════════════════
-- 2. Tactic: parr_homog
-- ══════════════════════════════════════════════════════════════

example (c : R) (s : FTS56 R) : I₄(c ·ₚ s) = c ^ 4 * I₄(s) := by
  parr_homog

example (s : FTS56 R) : I₄((2 : R) ·ₚ s) = 16 * I₄(s) := by
  parr_homog

-- ══════════════════════════════════════════════════════════════
-- 3. Tactic: parr_ring / automation lemmas
-- ══════════════════════════════════════════════════════════════

example (s : FTS56 R) : ⟨s, s⟩ₛ = 0 := by
  exact parr_symp_alt s

example (s t : FTS56 R) : ⟨s, t⟩ₛ = -⟨t, s⟩ₛ := by
  exact parr_symp_antisym s t

example (r : R) (M : J3O R) : N(r ·ₚ M) = r ^ 3 * N(M) := by
  exact parr_cubicNorm_homog r M

-- ══════════════════════════════════════════════════════════════
-- 4. Tactic: parr_bitflip
-- ══════════════════════════════════════════════════════════════

example (b : Bool) (i : Fin 3) :
    BitFlipCode.decode
      (BitFlipCode.correct
        (BitFlipCode.syndrome (BitFlipCode.xError i (BitFlipCode.encode b)))
        (BitFlipCode.xError i (BitFlipCode.encode b))) = b := by
  exact parr_bitflip_recover b i

-- ══════════════════════════════════════════════════════════════
-- 5. Gates normalisation
-- ══════════════════════════════════════════════════════════════

example (g : RiemannMetatron.LogitGate) :
    ∑ i : Fin g.vocab_size, RiemannMetatron.logitSimplex g i = 1 := by
  exact parr_gates_norm g

-- ══════════════════════════════════════════════════════════════
-- 6. Composite: notation + homog in one line
-- ══════════════════════════════════════════════════════════════

/-- The Parr homogeneity statement in surface syntax. -/
theorem parr_I4_surface (c : R) (s : FTS56 R) :
    I₄(c ·ₚ s) = c ^ 4 * I₄(s) := by
  parr_homog

/-- Fourth-difference identity recovered via homogeneity. -/
theorem parr_fourth_diff (s : FTS56 R) :
    I₄((4 : R) ·ₚ s) - 4 * I₄((3 : R) ·ₚ s) + 6 * I₄((2 : R) ·ₚ s)
      - 4 * I₄((1 : R) ·ₚ s) + I₄((0 : R) ·ₚ s) = 24 * I₄(s) := by
  simpa using FTS56.I4_fourth_difference s

end
