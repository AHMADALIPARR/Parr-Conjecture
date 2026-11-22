# File Inventory — Parr Conjecture (GKN–E7 Bridge)

Complete inventory of the 37 tracked files in this repository, with measured size in bytes and lines (`wc -c -l`), language, purpose, and subsystem. Implementation files are listed at remote HEAD `d342fb9` (AHMADALIPARR/Parr-Conjecture); the documentation files in this inventory are the README.md and the two files under `docs/` written in the same documentation pass. Total: 9595 lines, 439501 bytes across all 37 files, including this inventory file itself.

Purposes for the implementation files are taken verbatim from the inventory table in the README, Section 12, which was itself written from reading each file. Sizes are measured from the files as committed, not estimated.

| # | File | Bytes / lines | Language | Purpose |
|---|---|---|---|---|
| 1 | `.github/workflows/lean.yml` | 1239 / 47 | YAML | CI: elan install, `lake update`, `lake exe cache get`, `lake build` on push/PR to `main` |
| 2 | `AMPL/GKN_E7_Bridge.dat` | 664 / 19 | AMPL data | Concrete feasible instance: N_E=4, energies, logits, u_grid, error bits, FTS56 diagonal-slice state |
| 3 | `AMPL/GKN_E7_Bridge.mod` | 3409 / 84 | AMPL model | NLP model: sets/params/vars, diagonal J3(R) I4 expressions, Legendre-dual objective, 6 named constraints |
| 4 | `AMPL/GKN_E7_Bridge.nl` | 2992 / 107 | AMPL .nl sketch | Hand-structured .nl-style emission: 7 vars, 9 constraints, 1 objective, bounds, initial point, constraint ranges, verified instance constants in comments |
| 5 | `AMPL/GKN_E7_Bridge.run` | 548 / 13 | AMPL script | Loads .mod+.dat, `option solver ipopt`, `write gGKN_E7_Bridge`, `solve`, displays 7 outputs |
| 6 | `Agda/GKN_E7_Bridge.agda` | 15838 / 437 | Agda | Self-contained Safe Agda bridge: own prelude, `OrderedAnalyticField` record parameter, Oct/J3O/FTS56, bit-flip, partition, logit/Montgomery |
| 7 | `BitFlipCode/BitFlipCode.lean` | 8031 / 159 | Lean 4 + Mathlib | [[3,1,3]] bit-flip code: encode, X-error, syndrome, correction, majority decode, exact-recovery theorems |
| 8 | `Dafny/GKN_E7_Bridge.dfy` | 10492 / 309 | Dafny 4 | Algorithm contracts: Oct/J3O/FTS56 functions, lemmas (mostly empty bodies), methods with requires/ensures, axiomatized Exp/Ln/Sin |
| 9 | `GKN/Axioms_stub.lean` | 3033 / 85 | Lean 4 + Mathlib | Incomplete abstract layer (file header: "Extracted stub from source paste (incomplete abstract layer)"): abstract `OctonionAlgebra` class, `J3O`/`State56` structures, truncated `cubicNorm`, diagonal-only `jordanProduct`, placeholder half-factor in `freudenthalDual` |
| 10 | `GKN/I4_CommRing.lean` | 14415 / 365 | Lean 4 + Mathlib | CommRing formalisation of Octonion (Fin 8 coeffs, no mul), J3O (diagonal-only adjoint), FTS56, I4; homogeneity/symplectic/polarization theorems, all proved by `ring`/`simp` |
| 11 | `GKN/VerifyE7Bridge.lean` | 14203 / 305 | Lean 4 + Mathlib | Lean port of `verify_gkn_e7_bridge.py`: Fano triples, J3 homogeneity/Euler/Springer (diagonal), I4 sigma/scale, bit-flip, partition, logit/Montgomery, master bundle `all_closed_checks`, 1 axiom for full T_C shift |
| 12 | `LICENSE` | 34477 / 661 | Legal text | GNU Affero General Public License, Version 3, 19 November 2007 (FSF text) |
| 13 | `ParrDSL.lean` | 1362 / 52 | Lean 4 | Root DSL module: docstring overview + quick-start; imports Syntax, Elaborators, Tactics, Automation, AMPL (NOT Examples); the `#eval`/`#check` lines are inside the doc comment, not code |
| 14 | `ParrDSL/AMPL.lean` | 14922 / 391 | Lean 4 + Mathlib | AMPL-style modelling layer in Lean: `Sense`/`Var`/`Param`/`Rel`/`Constraint`/`Objective`/`Model`, 5 stock models, `certifiedContracts`, `Model.toAMPL` pretty-printer, `models_certified` (via `native_decide`), `ampl_grounded_in_master` |
| 15 | `ParrDSL/Automation.lean` | 4554 / 104 | Lean 4 + Mathlib | Lemma wrappers (`parr_*`) re-exposing GKN/BitFlip/Riemann results + 3 `List Name` bundles (`homogLemmaNames`, `sympLemmaNames`, `bitflipLemmaNames`) |
| 16 | `ParrDSL/Elaborators.lean` | 1375 / 51 | Lean 4 | `macro_rules` expanding `N(·)`, `·♯`, `I₄(·)`, `⟨·,·⟩ₛ`, `·ₚ` to GKN terms |
| 17 | `ParrDSL/Examples.lean` | 4994 / 105 | Lean 4 + Mathlib | 12 unnamed `example`s + 2 theorems (`parr_I4_surface`, `parr_fourth_diff`) demonstrating notation/tactics; ends with a stray `end` (line 105) with no matching `section`/`namespace` opened in the file |
| 18 | `ParrDSL/Syntax.lean` | 2974 / 74 | Lean 4 | Syntax declarations for the 5 notations + 5 tactics (`parr_homog`, `parr_diag`, `parr_bitflip`, `parr_ring`, `parr_auto`) + `parr.pp.notation` option |
| 19 | `ParrDSL/Tactics.lean` | 3501 / 106 | Lean 4 | Tactic implementations `evalParrHomog/Diag/Bitflip/Ring/Auto` as `TacticM Unit` via quoted-tactic `first`/`try` chains |
| 20 | `Quantum/QuantumPartitionBridge.lean` | 4796 / 115 | Lean 4 + Mathlib | Finite-spectrum partition function over `Fin n`: `partZ`, `gibbs`, `freeE`, `expH`, `SvN`; `entropy_eq` and Legendre duality `free_energy_legendre` |
| 21 | `README.md` | 133512 / 1145 | Markdown | This README |
| 22 | `RiemannMetatron/RiemannMetatron.lean` | 6389 / 133 | Lean 4 + Mathlib | Zeta structural facts (via Mathlib `riemannZeta`), critical strip, von Mangoldt log sum, `LogitGate` structure, softmax/spectral gap, vacuous `gue_conjecture : True` |
| 23 | `Rocq/GKN_E7_Bridge.v` | 14452 / 390 | Rocq/Coq | Full bridge in Coq: Oct (with mul), J3O, FTS56, I4, sigma proved, shift axiomatized, bit-flip, partition, logit/Montgomery |
| 24 | `Rocq/SPECIFICATION.md` | 4552 / 69 | Markdown + LaTeX | Mathematical specification: octonion/J3O/I4 definitions, symmetry contracts, QEC, partition, logit/Montgomery, Rocq proof-status table |
| 25 | `S_AUTOCODE/CheckI4.lean` | 1583 / 43 | Lean 4 | Numeric witness only: sparse `basis0` state, 2 `#eval`s (cubicNorm, I4 ratio 16 vs 64); no theorems |
| 26 | `S_AUTOCODE/CheckI4_56.lean` | 1637 / 39 | Lean 4 | Numeric witnesses only: 3 test states (sparse/diagonal/off-diagonal), 3 `#eval`s of I4_56 ratio at r=2; no theorems |
| 27 | `S_AUTOCODE/MTheory.lean` | 17406 / 385 | Lean 4 (Float, no Mathlib import) | Float autocode: Octonion mul, J3O Jordan product/cubic norm/Freudenthal dual, State56 + `I4_56`, legacy State108 + `I4` (degree 6), Weyl relocation, drum optimizer, compiler pipeline; 5 axioms, 2 theorems |
| 28 | `docs/assets/ampl-pipeline.svg` | 4131 / 36 | SVG | Diagram: .mod → .dat → .run → .nl IR → Ipopt solver target; contract list; residual note |
| 29 | `docs/assets/constraint-bounds.svg` | 3306 / 30 | SVG | Diagram: beta_thermo / p_logit[k] / R2_val·S_entropy bounds + hard contracts |
| 30 | `docs/assets/proof-dependency.svg` | 4973 / 44 | SVG | Diagram: theorem dependency boxes (no drawn edges) |
| 31 | `docs/assets/system-architecture.svg` | 5062 / 42 | SVG | Diagram: Lean/Agda/Rocq/Dafny boxes, shared mathematical core, AMPL NLP layer |
| 32 | `docs/assets/verification-architecture.svg` | 5155 / 45 | SVG | Diagram: Lean CI / Lean theorems / Rocq·Agda / Dafny boxes + evidence classes |
| 33 | `docs/FILE_INVENTORY.md` | 7845 / 46 | Markdown | Complete tracked-file inventory for this repository: every tracked file with measured size, language, purpose, and subsystem; generated from the tracked tree. |
| 34 | `docs/THEOREM_INDEX.md` | 80609 / 3518 | Markdown | Complete registry of every theorem, lemma, axiom, and formal definition in the repository, with source file and line and verbatim formal statement. |
| 35 | `lake-manifest.json` | 116 / 1 | JSON | Package manifest; `packages` list is empty in the clone (Mathlib not yet fetched; CI regenerates it with `lake update`) |
| 36 | `lakefile.lean` | 929 / 39 | Lean (Lake DSL) | Package `ParrConjecture`, `autoImplicit`/`relaxedAutoImplicit` false, `require mathlib @ git "v4.19.0"`, 16 lib roots |
| 37 | `lean-toolchain` | 25 / 1 | Text | `leanprover/lean4:v4.19.0` |

