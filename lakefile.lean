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
  -- Basic package configuration
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]
  -- More permissive for a research formalisation
  moreLeanArgs := #["-DwarningAsError=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

/-- Main library: all formal developments under one target.
    Module names follow directory structure:
      S_AUTOCODE/MTheory.lean          → S_AUTOCODE.MTheory
      GKN/I4_CommRing.lean             → GKN.I4_CommRing
      BitFlipCode/BitFlipCode.lean     → BitFlipCode.BitFlipCode
      etc.
-/
@[default_target]
lean_lib «ParrConjecture» where
  roots := #[
    `S_AUTOCODE.MTheory,
    `S_AUTOCODE.CheckI4_56,
    `S_AUTOCODE.CheckI4,
    `GKN.I4_CommRing,
    `GKN.Axioms_stub,
    `BitFlipCode.BitFlipCode,
    `Quantum.QuantumPartitionBridge,
    `RiemannMetatron.RiemannMetatron
  ]
  -- Globs are an alternative if you prefer auto-discovery:
  -- globs := #[.submodules `S_AUTOCODE, .submodules `GKN, ...]

/-- Optional: keep the Float computational witness separate if desired.
    Uncomment and adjust if you want a lighter default target.
-/
-- lean_lib «S_AUTOCODE» where
--   roots := #[`S_AUTOCODE.MTheory, `S_AUTOCODE.CheckI4_56, `S_AUTOCODE.CheckI4]
