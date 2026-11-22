/-
Copyright (c) 2026 Ahmad Ali Parr / Bel Esprit D'Accord Irrevocable Trust (EIN 42-697643).
Released under the GNU Affero General Public License v3.0 or later.
See the file LICENSE for details.
Authors: Ahmad Ali Parr
BOW-Ω-φ-∂-2026
-/

/-!
# ParrDSL — Specialized tactics

Domain-specific proof automation for the Parr Conjecture formalisation.

| Tactic         | Purpose |
|----------------|---------|
| `parr_homog`   | Close `I4 (c • s) = c^n * I4 s` via `I4_homogeneous` + `ring` |
| `parr_diag`    | Simplify under `IsDiag` hypotheses, then `ring` |
| `parr_bitflip` | Exhaustive Bool × Fin 3 case analysis for bit-flip recovery |
| `parr_ring`    | GKN/J3O simp set, then `ring` |
| `parr_auto`    | Try the above in sequence, then `decide` / `trivial` |
-/

import ParrDSL.Syntax
import GKN.I4_CommRing
import BitFlipCode.BitFlipCode
import Mathlib.Tactic

open Lean Meta Elab Tactic
open GKN_I4_CommRing

namespace ParrDSL

/-- Core implementation of `parr_homog`. -/
def evalParrHomog : TacticM Unit := do
  evalTactic (← `(tactic|
    first
    | (rw [FTS56.I4_homogeneous]; try ring)
    | (simp only [FTS56.I4_homogeneous]; try ring)
    | (apply FTS56.I4_homogeneous)))

/-- Core implementation of `parr_diag`. -/
def evalParrDiag : TacticM Unit := do
  evalTactic (← `(tactic|
    try simp only [J3O.IsDiag, J3O.cubicNorm, J3O.adjoint,
                   Octonion.normSq_zero, Octonion.realPart_zero] at *
    try simp_all [Octonion.normSq_zero, Octonion.realPart_zero]
    try ring))

/-- Core implementation of `parr_bitflip`. -/
def evalParrBitflip : TacticM Unit := do
  evalTactic (← `(tactic|
    try (intro i; fin_cases i <;> try (cases ‹Bool›) <;>
      simp [BitFlipCode.encode, BitFlipCode.xError, BitFlipCode.syndrome,
            BitFlipCode.parity, BitFlipCode.correctionIdx, BitFlipCode.correct,
            BitFlipCode.decode])
    try (fin_cases ‹Fin 3› <;> cases ‹Bool› <;>
      simp [BitFlipCode.encode, BitFlipCode.xError, BitFlipCode.syndrome,
            BitFlipCode.parity, BitFlipCode.correctionIdx, BitFlipCode.correct,
            BitFlipCode.decode])
    try (cases ‹Bool› <;>
      simp [BitFlipCode.encode, BitFlipCode.xError, BitFlipCode.syndrome,
            BitFlipCode.parity, BitFlipCode.correctionIdx, BitFlipCode.correct,
            BitFlipCode.decode])))

/-- Core implementation of `parr_ring`. -/
def evalParrRing : TacticM Unit := do
  evalTactic (← `(tactic|
    try simp only [
      J3O.smul_d, J3O.smul_o, J3O.add_d, J3O.add_o,
      J3O.cubicNorm, J3O.adjoint, J3O.trace,
      Octonion.normSq_smul, Octonion.realPart_smul,
      Octonion.normSq_zero, Octonion.realPart_zero,
      FTS56.smul_α, FTS56.smul_β, FTS56.smul_X, FTS56.smul_Y,
      FTS56.I4, FTS56.symp] at *
    try ring))

/-- Core implementation of `parr_auto`. -/
def evalParrAuto : TacticM Unit := do
  evalTactic (← `(tactic|
    first
    | done
    | (parr_homog; done)
    | (parr_diag; done)
    | (parr_bitflip; done)
    | (parr_ring; done)
    | (decide; done)
    | (trivial; done)
    | (simp; done)
    | skip))

@[tactic parrHomogTac]
def evalParrHomogTac : Tactic := fun _ => evalParrHomog

@[tactic parrDiagTac]
def evalParrDiagTac : Tactic := fun _ => evalParrDiag

@[tactic parrBitflipTac]
def evalParrBitflipTac : Tactic := fun _ => evalParrBitflip

@[tactic parrRingTac]
def evalParrRingTac : Tactic := fun _ => evalParrRing

@[tactic parrAutoTac]
def evalParrAutoTac : Tactic := fun _ => evalParrAuto

end ParrDSL
