/-
Copyright (c) 2026 Ahmad Ali Parr / Bel Esprit D'Accord Irrevocable Trust (EIN 42-697643).
Released under the GNU Affero General Public License v3.0 or later.
See the file LICENSE for details.
Authors: Ahmad Ali Parr
BOW-Ω-φ-∂-2026
-/

import Lake
open Lake DSL

package «ParrConjecture» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.19.0"

@[default_target]
lean_lib «ParrConjecture» where
  roots := #[
    `S_AUTOCODE.MTheory,
    `S_AUTOCODE.CheckI4_56,
    `S_AUTOCODE.CheckI4,
    `GKN.I4_CommRing,
    `GKN.Axioms_stub,
    `GKN.VerifyE7Bridge,
    `BitFlipCode.BitFlipCode,
    `Quantum.QuantumPartitionBridge,
    `RiemannMetatron.RiemannMetatron,
    `ParrDSL.Syntax,
    `ParrDSL.Elaborators,
    `ParrDSL.Tactics,
    `ParrDSL.Automation,
    `ParrDSL.Examples,
    `ParrDSL.AMPL,
    `ParrDSL
  ]
