<!-- Copyright (c) 2026 Ahmad Ali Parr / Bel Esprit D'Accord Irrevocable Trust (EIN 42-697643).
     Released under the GNU Affero General Public License v3.0 or later.
     See the file LICENSE for details.
     Authors: Ahmad Ali Parr
     BOW-Ω-φ-∂-2026 -->

# Parr Conjecture — GKN–E₇ Bridge


- **Lean 4 and Mathlib** (`GKN/`, `BitFlipCode/`, `Quantum/`, `RiemannMetatron/`, `ParrDSL/`, `S_AUTOCODE/`): algebraic definitions and theorems, a bit-flip code, finite-spectrum thermodynamic results, zeta/logit examples, a Lean DSL, and a separate floating-point implementation.
- **Rocq** (`Rocq/`): an octonion/Jordan/FTS development, with its mathematical specification in `Rocq/SPECIFICATION.md`.
- **Agda** (`Agda/`): a self-contained development using a parameterized analytic-field interface and `--safe --without-K`.
- **Dafny** (`Dafny/`): definitions, executable methods, contracts, and proof obligations.
- **AMPL** (`AMPL/`): a nonlinear optimization model and data/script files for a diagonal real slice.
- **Documentation** (`docs/`): file inventory, theorem index, and diagrams.

## What the formalizations cover

The Lean core in `GKN/I4_CommRing.lean` defines a coefficient-vector octonion type, a `J3O` record, an `FTS56` state, and a quartic function `I4`. It proves homogeneity of that defined `I4` over a commutative ring, along with related scaling and symplectic-form results. It also proves a double-adjoint identity in the diagonal case.

There are important modeling limits to that Lean core: the octonion type has no octonion multiplication, and its adjoint sets the off-diagonal components to zero. Consequently, it is not by itself a full implementation of the exceptional Jordan algebra over octonions. The Lean bridge in `GKN/VerifyE7Bridge.lean` additionally states `I4_shift_invariant` as an axiom; its shift definition omits the Freudenthal cross-product term.

Other components include:

- A constructive Lean proof of exact recovery for a three-bit repetition code under any single-bit error (`BitFlipCode/`).
- A finite-spectrum partition function and a Gibbs-state free-energy identity (`Quantum/`).
- Zeta-related statements and a logit-gate structure (`RiemannMetatron/`). The theorem named `gue_conjecture` has conclusion `True` and is explicitly vacuous; it does not prove a substantive conjecture.
- `ParrDSL/`, a Lean syntax/tactic layer and AMPL-style model-description layer. The Lean AMPL layer is not a solver binding: its certification check tests contract-name strings, not proofs of the model's optimization semantics.
- `S_AUTOCODE/`, a separate `Float`-based implementation with axiomatized claims. Its numeric `#eval` files are examples, not general proofs.

## Definitions and proof status differ across systems

The implementations should not be treated as interchangeable proofs of one identical specification. For example, the Lean and Rocq-family definitions of `I4` use different sign conventions and are not generally equal. The Lean, Rocq, Agda, and Dafny shift definitions and their proof status also differ.

Some specific limitations recorded in the source:

- Lean's bridge shift invariance is an axiom, not a proved theorem.
- Rocq's `I4_shift_invariant` is an axiom.
- Agda's polynomial identities are fields of `E7PolynomialWitness`; this file does not provide an instance proving them.
- Dafny contains axiom declarations and lemmas with empty bodies; this repository does not include a Dafny verification run.
- `S_AUTOCODE/MTheory.lean` contains axioms, including claims about its floating-point and relocation model.

Consult the source files and [`docs/THEOREM_INDEX.md`](docs/THEOREM_INDEX.md) for individual statements and their assumptions. A declaration's presence in a file should not be read as evidence that the full mathematical claim has been proved.

## Build

The Lean toolchain is pinned in [`lean-toolchain`](lean-toolchain) and Mathlib is specified in [`lakefile.lean`](lakefile.lean). With [elan](https://github.com/leanprover/elan) installed, run:

```sh
lake update
lake exe cache get
lake build
```

The GitHub Actions workflow at [`.github/workflows/lean.yml`](.github/workflows/lean.yml) runs `lake update`, attempts to fetch the Mathlib cache (allowing that step to fail), and then runs `lake build`. It does not run Agda, Rocq, Dafny, or AMPL verification. No build result is implied by these instructions.

## License

This project is released under the GNU Affero General Public License v3.0 or later. See [`LICENSE`](LICENSE).
