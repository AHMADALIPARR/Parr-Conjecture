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
  -- add package configuration options here
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ParrConjecture» where
  -- main library roots
  roots := #[
    `S_AUTOCODE.MTheory,
    `S_AUTOCODE.CheckI4_56,
    `S_AUTOCODE.CheckI4,
    `GKN.I4_CommRing,
    `BitFlipCode.BitFlipCode,
    `Quantum.QuantumPartitionBridge,
    `RiemannMetatron.RiemannMetatron
  ]
