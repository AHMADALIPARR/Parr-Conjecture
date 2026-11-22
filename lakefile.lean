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
