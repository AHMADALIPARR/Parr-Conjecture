/-
Copyright (c) 2026 Ahmad Ali Parr / Bel Esprit D'Accord Irrevocable Trust (EIN 42-697643).
Released under the GNU Affero General Public License v3.0 or later.
See the file LICENSE for details.
Authors: Ahmad Ali Parr
BOW-Ω-φ-∂-2026
-/

/-!
# ParrDSL — Elaborators

Turn surface syntax from `ParrDSL.Syntax` into kernel terms that
reference `GKN.I4_CommRing` definitions.

| Syntax        | Elaborates to                          |
|---------------|----------------------------------------|
| `N(M)`        | `GKN_I4_CommRing.J3O.cubicNorm M`      |
| `M♯`          | `GKN_I4_CommRing.J3O.adjoint M`        |
| `I₄(s)`       | `GKN_I4_CommRing.FTS56.I4 s`           |
| `⟨s, t⟩ₛ`     | `GKN_I4_CommRing.FTS56.symp s t`       |
| `c ·ₚ s`      | `c • s` (SMul)                         |
-/

import ParrDSL.Syntax
import GKN.I4_CommRing

open Lean Meta Elab Term
open GKN_I4_CommRing

namespace ParrDSL

/-- Elaborate `N(M)` → `J3O.cubicNorm M`. -/
@[term_elab parrCubicNorm]
def elabCubicNorm : TermElab := fun stx _expectedType? => do
  match stx with
  | `(N($m:term)) =>
    let m ← elabTerm m none
    let m ← ensureHasType (← inferType m) m
    -- Build `J3O.cubicNorm m` via expression synthesis
    let cubicNorm := mkConst ``J3O.cubicNorm [← getLevel m]
    -- Prefer typed elaboration through the elaborator
    elabTerm (← `(J3O.cubicNorm $(← Term.exprToSyntax m))) none
  | _ => throwUnsupportedSyntax
where
  getLevel (e : Expr) : MetaM Level := do
    let ty ← inferType e
    match ty with
    | .app (.const ``J3O [u]) _ => pure u
    | _ => pure levelZero

/-- Elaborate `M♯` → `J3O.adjoint M`. -/
@[term_elab parrAdjoint]
def elabAdjoint : TermElab := fun stx _expectedType? => do
  match stx with
  | `($m:term♯) =>
    elabTerm (← `(J3O.adjoint $m)) none
  | _ => throwUnsupportedSyntax

/-- Elaborate `I₄(s)` → `FTS56.I4 s`. -/
@[term_elab parrI4]
def elabI4 : TermElab := fun stx _expectedType? => do
  match stx with
  | `(I₄($s:term)) =>
    elabTerm (← `(FTS56.I4 $s)) none
  | _ => throwUnsupportedSyntax

/-- Elaborate `⟨s, t⟩ₛ` → `FTS56.symp s t`. -/
@[term_elab parrSymp]
def elabSymp : TermElab := fun stx _expectedType? => do
  match stx with
  | `(⟨$s:term, $t:term⟩ₛ) =>
    elabTerm (← `(FTS56.symp $s $t)) none
  | _ => throwUnsupportedSyntax

/-- Elaborate `c ·ₚ s` → `c • s`. -/
@[term_elab parrScale]
def elabScale : TermElab := fun stx _expectedType? => do
  match stx with
  | `($c:term ·ₚ $s:term) =>
    elabTerm (← `($c • $s)) none
  | _ => throwUnsupportedSyntax

-- ── Command elaborators ───────────────────────────────────────────────────────

/-- Expand `assert_homogeneous I₄ degree 4` into a named theorem. -/
@[command_elab parrAssertHomog]
def elabAssertHomog : Command.CommandElab := fun stx => Command.liftTermElabM do
  match stx with
  | `(command| assert_homogeneous $name:ident degree $n:num) => do
    let nVal := n.getNat
    let thmName := name.getId
    -- Generate: theorem name (c : R) (s : FTS56 R) : I4 (c • s) = c^n * I4 s := by parr_homog
    let cmd ← `(command|
      theorem $(mkIdent thmName) {R : Type*} [CommRing R] (c : R) (s : FTS56 R) :
          FTS56.I4 (c • s) = c ^ $(quote nVal) * FTS56.I4 s := by
        simp only [FTS56.I4_homogeneous]
        ring)
    Command.elabCommand cmd
  | _ => throwUnsupportedSyntax

/-- Expand `assert_recovery bitflip` into the master recovery theorem. -/
@[command_elab parrAssertRecovery]
def elabAssertRecovery : Command.CommandElab := fun stx => Command.liftTermElabM do
  match stx with
  | `(command| assert_recovery bitflip) => do
    let cmd ← `(command|
      theorem parr_bitflip_master_recovery (b : Bool) (i : Fin 3) :
          BitFlipCode.decode
            (BitFlipCode.correct
              (BitFlipCode.syndrome (BitFlipCode.xError i (BitFlipCode.encode b)))
              (BitFlipCode.xError i (BitFlipCode.encode b))) = b :=
        BitFlipCode.recover_single_x b i)
    Command.elabCommand cmd
  | _ => throwUnsupportedSyntax

/-- Expand `assert_gates_norm g` into the simplex-sum theorem application. -/
@[command_elab parrAssertGates]
def elabAssertGates : Command.CommandElab := fun stx => Command.liftTermElabM do
  match stx with
  | `(command| assert_gates_norm $g:term) => do
    let cmd ← `(command|
      example : ∑ i : Fin ($g).vocab_size, RiemannMetatron.logitSimplex $g i = 1 :=
        RiemannMetatron.logit_simplex_sums_to_one $g)
    Command.elabCommand cmd
  | _ => throwUnsupportedSyntax

end ParrDSL
