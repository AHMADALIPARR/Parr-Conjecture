# Repository Architecture, Proof Methodology, and Module Reference

**Repository:** `AHMADALIPARR`  
**Branch described:** `main`  
**Scope:** Formal methods, mathematical modeling, domain-specific languages, and bit-level computation

## Overview

This repository brings together mathematical models, proof-assistant developments, verification contracts, a Lean-based domain-specific language (DSL), and bit-level computation. Its organization follows the mathematical problem and the formal language used to express it, rather than placing every experiment behind one universal compiler or proof engine.

The repository has five broad areas: CI configuration in `.github/workflows/`; mathematical models in `AMPL/`, `Quantum/`, and `RiemannMetatron/`; formal developments in `Agda/`, `Rocq/`, `Dafny/`, `GKN/`, and the Lean-based `ParrDSL/`; bit-level and autocode material in `BitFlipCode/` and `S_AUTOCODE/`; and documentation and licensing in `docs/` and `LICENSE`.

## Repository map

| Path | Category | Responsibility |
| --- | --- | --- |
| `.github/workflows/` | Automation | CI definitions and automated checks |
| `AMPL/` | Optimization | Algebraic models, parameters, objectives, constraints, and data |
| `Agda/` | Formal proof | Constructive definitions and dependent-type proofs |
| `BitFlipCode/` | Bit-level methods | Bit-flip transformations, syndromes, and recovery properties |
| `Dafny/` | Deductive verification | Functions, methods, contracts, invariants, and verification obligations |
| `GKN/` | Mathematical core | Algebraic definitions and theorem developments |
| `ParrDSL/` | Lean DSL | Syntax, elaboration, tactics, automation, and model representation |
| `ParrDSL.lean` | Lean entry point | Top-level module exposing the DSL |
| `Quantum/` | Mathematical modeling | Finite spectra, partition functions, and related quantum models |
| `RiemannMetatron/` | Analytic mathematics | Spectral, zeta-related, and logit-gate constructs |
| `Rocq/` | Formal proof | Rocq/Coq specifications and theorem proofs |
| `S_AUTOCODE/` | Autocode and numerics | Low-level mathematical representations and numerical witnesses |
| `docs/` | Documentation | Specifications, theorem indexes, figures, and reference material |
| `LICENSE` | Governance | Legal terms for reuse and redistribution |

### Architecture diagram

```mermaid
flowchart TB
    A[Mathematical definitions and specifications]
    B[Lean and ParrDSL]
    C[Agda]
    D[Rocq]
    E[Dafny]
    F[AMPL models]
    G[BitFlipCode and S_AUTOCODE]
    H[Documentation and evidence]
    I[CI checks]
    A --> B
    A --> C
    A --> D
    A --> E
    A --> F
    B --> H
    C --> H
    D --> H
    E --> H
    F --> H
    G --> H
    I --> H
```

The arrows express a **documentation and conceptual organization**, not verified automatic translations between languages. Cross-language equivalence is a separate theorem or contract to establish.

## Design principles

### Separate mathematical meaning from verification evidence

A formal repository needs distinct categories for the objects it defines, the properties it claims, and the evidence it supplies.

| Category | Meaning | What establishes confidence |
| --- | --- | --- |
| Definition | Introduces a mathematical or computational object | Inspection of the actual definition and its domain |
| Specification | States expected behavior or invariants | Precise preconditions and postconditions |
| Theorem or lemma | States a proposition with a proof | Successful checking of the proof term in its formal system |
| Axiom or assumption | Introduces an unproved premise | Explicit disclosure and dependency tracing |
| Verification obligation | Property a verifier must discharge | A recorded successful verification result |
| Numerical witness | Demonstrates behavior for particular inputs | Reproducible computation and tolerance criteria |
| Generated artifact | Material produced from another representation | Provenance and validation of its output format |

A test result cannot substitute for a universal theorem. Conversely, a formally valid theorem may establish a weaker proposition than its name suggests. The statement and its assumptions are authoritative.

### Conceptual proof flow

```mermaid
flowchart TD
    S[Write mathematical specification]
    D[Define objects and operations]
    O[State proof obligations]
    L[Prove supporting lemmas]
    P[Construct final theorem]
    V[Check with the relevant proof kernel or verifier]
    A[Audit assumptions and dependencies]
    R[Record evidence and source references]
    S --> D --> O --> L --> P --> V --> A --> R
```

### Why use multiple formal languages?

Agda, Rocq, and Lean support dependent types and machine-checkable proof terms, but they have different libraries, automation, and language ergonomics. Dafny focuses on program contracts and automated deductive verification. AMPL expresses optimization problems for numerical solver backends. None of these roles requires every mathematical claim to be duplicated across every language.

Cross-language work becomes meaningful when its definitions, sign conventions, normalization factors, indexing choices, and assumptions are compared explicitly. A theorem proved over one representation is not automatically a theorem over a differently defined representation.

## Module reference

### 1. `.github/workflows/` — continuous integration

Workflow definitions describe which toolchains are configured and what checks run on repository changes. CI should distinguish successful compilation, theorem checking, test completion, and optional external-solver availability.

| Review item | Expected documentation |
| --- | --- |
| Toolchain setup | Exact versions and reproducible installation instructions |
| Build step | The commands actually used by the workflow |
| Proof checking | The theorem modules included in the build |
| Failure handling | Which failures are fatal and which are optional |
| Artifact retention | Logs or generated evidence available for review |

A build workflow for Lean does not automatically validate the Agda, Rocq, Dafny, or AMPL directories. Describe only the checks that the workflow actually performs.

### 2. `Agda/` — constructive proofs and dependent types

Agda supports proofs-as-programs, inductive families, structural recursion, and dependent pattern matching. Its type checker validates the internal consistency of definitions and proof terms relative to their assumptions.

Key review points include termination and positivity checks, module-name alignment, explicit assumptions, equational reasoning, and the distinction between an inhabited record of proof obligations and an unfilled record type. A field specifying a required proof is not itself a supplied proof.

When documenting Agda code, show the exact proposition type and explain any relevant pattern matches, recursion measures, and premises. Keep holes and postulates visible in an assumption inventory when present.

### 3. `Rocq/` — proof developments in the Calculus of Inductive Constructions

Rocq (formerly Coq) provides inductive types, modules, typeclasses, proof terms, and tactics such as `intros`, `induction`, `rewrite`, `ring`, and `lia`. Its checker validates completed theorem proofs relative to their environment.

A theorem reference should include the statement, supporting lemmas, proof method, and assumptions. `Print Assumptions` is useful when auditing reliance on classical principles or explicitly declared axioms. The presence of `Qed` marks a closed proof script in source, but an actual successful check is the evidence that the file is accepted by a particular toolchain.

### 4. `Dafny/` — contract-driven program verification

Dafny uses `requires`, `ensures`, loop `invariant`, framing clauses, and termination measures to express and check program behavior. Verification normally uses an SMT-backed workflow.

| Construct | Engineering purpose |
| --- | --- |
| `requires` | Defines a valid input domain |
| `ensures` | Specifies the required result |
| `invariant` | Preserves a loop property across iterations |
| `decreases` | Supports termination reasoning |
| `lemma` | Packages reusable logical reasoning |
| Ghost code | Supports verification without becoming ordinary runtime logic |

The presence of a method contract, including a lemma with an empty body, is not evidence of a successful verifier run. Record verifier results separately. For complex proofs, intermediate assertions and small lemmas make proof obligations more understandable and reduce solver instability.

### 5. `GKN/` — mathematical core

The `GKN/` workspace contains the repository's specialized algebraic objects, formal definitions, and theorem developments. Its exact exports must be read from the source, not inferred from the folder name.

For each major algebraic operation, document the ground ring or field, input structure, output type, equation, and assumptions. For example, homogeneity claims should specify both the scalar action and the degree of the polynomial:

$$
F(c \cdot x) = c^d F(x).
$$

If parallel formalizations use different signs, scalar pairings, or restricted subalgebras, document the distinction in a comparison table before discussing their proofs together.

### 6. `ParrDSL/` and `ParrDSL.lean` — Lean DSL

Lean 4 combines functional programming, dependent type theory, macros, elaboration, tactics, and kernel-checked propositions. The root `ParrDSL.lean` serves as the entry-point module for the domain-specific language material.

The DSL may provide surface notation, transformations into core Lean terms, specialized tactics, theorem wrappers, or modeling structures. The important semantic boundary is between **notation expansion**, **proof construction**, and **proof checking**. Convenient syntax does not create a new theorem; a tactic may construct a proof term, which Lean's kernel subsequently checks.

```mermaid
flowchart LR
    N[DSL notation]
    M[Macro or elaborator]
    T[Lean core term]
    P[Tactic or proof term]
    K[Lean kernel]
    N --> M --> T
    T --> P --> K
```

Document a notation with its exact expansion, a tactic with the lemmas it may invoke, and a theorem wrapper with the underlying theorem it references. If the DSL also emits AMPL-style text, distinguish text generation from solver validation.

### 7. `AMPL/` — mathematical programming

AMPL represents constrained optimization using sets, parameters, decision variables, objectives, and relations. Its common file types separate the mathematical model from the numerical instance and solver command sequence.

| Extension | Contents | Role |
| --- | --- | --- |
| `.mod` | Sets, parameters, variables, objectives, and constraints | Model specification |
| `.dat` | Numerical parameters and indexed data | Concrete problem instance |
| `.run` | Load, solve, and report commands | Solver workflow |
| `.nl` | Solver-facing optimization representation | Intermediate exchange format |

```mermaid
flowchart LR
    M[AMPL model .mod]
    D[Instance data .dat]
    T[AMPL translation and presolve]
    N[Solver representation .nl]
    B[Solver backend]
    O[Solution and diagnostics]
    M --> T
    D --> T
    T --> N --> B --> O
```

When auditing a model, verify that summation indices match their declared sets, parameters are defined for the active instance, domains and units are consistent, and the objective has the intended sign. Distinguish the result of solving one numerical instance from a theorem about every admissible instance. A hand-authored `.nl` sketch is not equivalent to translator-generated solver input unless compatibility has been checked.

### 8. `Quantum/` — finite-spectrum and quantum mathematics

Quantum-oriented material should define state conventions, energy spectra, observables, normalization, and the algebraic assumptions behind each equation. Exact symbolic statements and numerical approximations need separate evidence.

For a finite energy spectrum, a common starting point is the partition function

$$
Z(\beta) = \sum_{i=1}^{n} e^{-\beta E_i},
$$

with Gibbs weights

$$
p_i(\beta) = \frac{e^{-\beta E_i}}{Z(\beta)}.
$$

For a nonempty finite spectrum of real energies, the exponential terms are positive, so $Z(\beta) > 0$ and the probabilities sum to one. Actual repository theorems must still be identified by their precise formal statements and dependencies.

### 9. `RiemannMetatron/` — analytic and spectral structures

This directory covers analytic, spectral, and related mathematical constructions. Separate known identities from conjectural relationships and from numerical experiments. For zeta-function or spectral-gap work, clearly state complex domains, normalization conventions, ordering assumptions, and any limiting process.

A name such as `conjecture` does not establish a theorem of the intended conjecture: inspect the formal conclusion. In particular, a proof of `True` is only a proof of `True`, irrespective of the declaration's descriptive name.

### 10. `BitFlipCode/` — bitwise operations and recovery

Bit-level proofs require unambiguous bit positions, syndrome conventions, error models, and recovery procedures.

A single-bit error at position $i$ changes only one coordinate. A recovery claim should specify the index domain and show that applying the correction and decoding returns the original logical bit for each admitted error.

```mermaid
flowchart TD
    A[Logical bit]
    B[Repetition encoding]
    C[At most one bit flip]
    D[Compute syndrome]
    E[Select correction]
    F[Correct word]
    G[Decode logical bit]
    A --> B --> C --> D --> E --> F --> G
```

The syndrome can encode equality or inequality of adjacent bits; these conventions give complementary bit patterns. Document the exact convention before comparing results across languages. A three-qubit bit-flip repetition code protects against the specified bit-flip error class; it is not, by itself, a code correcting arbitrary single-qubit Pauli errors.

### 11. `S_AUTOCODE/` — generated or low-level mathematical artifacts

This workspace contains autocode-oriented mathematical representations, transformations, and computational witnesses. Distinguish structural definitions from algorithms, direct numerical evaluation from assertions, and formal proofs from axiomatized properties.

If computations use machine floating point, ordinary ring laws do not automatically hold without regard to rounding and exceptional values. Document precision, evaluation order, admissible ranges, and comparison tolerances. A printed ratio or diagnostic is useful evidence for one input, but it is not an assertion over all inputs.

### 12. `docs/` and `LICENSE` — evidence, references, and governance

Technical appendices belong under `docs/` when they need more space than the root README: theorem registries, mathematical specifications, source maps, diagrams, and audit records. Prefer exact source paths and symbol names, and update references when source declarations move.

`LICENSE` governs copying, modification, and redistribution. Consult its actual text and retain required attribution when combining third-party material.


## Detailed engineering conventions by subsystem


### Dependent type theory: preserving proof meaning

For Agda, Lean, and Rocq, proof-oriented documentation starts with the proposition's exact type. Informal mathematical notation helps a reader, but it must preserve the formal binding of variables, implicit parameters, typeclass assumptions, and any local hypotheses. A proof of a statement parameterized by a record of algebraic laws depends on that record. It is not automatically a proof that a particular concrete structure satisfies those laws. Likewise, a result restricted to a diagonal subalgebra should not be presented as a universal identity over an entire nonassociative algebra.

Inductive proofs deserve a description of the induction principle and the changing hypothesis. For a list theorem, name the base case and show why the cons case follows from the induction hypothesis. For a finite-index theorem, describe whether the proof uses exhaustive cases, a decidability procedure, or a general invariant. For algebraic normalization, identify the laws required by the tactic: commutativity, associativity, distributivity, or ordered-field properties. The checker validates a proposition in its actual environment, not the broader intuition implied by its theorem name.

### Dafny: contract boundaries and algorithm refinement

A Dafny contract is a formal interface between caller and callee. The precondition identifies the states in which the operation may be invoked; the postcondition identifies the states the operation must produce on normal completion. Frame specifications constrain which locations may change, and loop invariants connect a finite body of code to a general property over all iterations. In a sound review, each invariant should be meaningful before the first iteration, preserved by the body, and strong enough to imply the required postcondition when the loop terminates.

When mathematical definitions are translated into imperative algorithms, document the abstraction relation between the program state and the mathematical object. A program's array of coefficients may represent a polynomial, a matrix, a quantum state, or a set of bounds. The contract should explain the representation and preservation requirements, not just assert a numeric outcome. Termination arguments are equally important: a decreasing integer quantity must be bounded appropriately, while more involved algorithms may use lexicographic measures. A contract with insufficient evidence remains a proof obligation even when its syntax is valid.

### AMPL: model semantics, presolving, and result interpretation

AMPL-style modeling separates abstract structure from particular values. An indexed constraint can expand into many concrete constraints after data is loaded; therefore the number of named declarations in a `.mod` file is not necessarily the number of rows a solver receives. Before interpreting an optimizer's result, confirm the model's effective variables, bounds, objective direction, constraints, and any presolve transformations. Constraints depending only on parameters can act as consistency checks for the selected data instance, rather than restricting decision variables.

For nonlinear optimization, a solver's success status should be reported with its meaning: a local stationary solution, a feasible point, a global optimum under additional guarantees, or another status. Numerical tolerances matter, particularly around equalities, singularities, and functions defined piecewise. If model output is serialized to `.nl`, distinguish an actual translator-produced representation from an illustrative sketch. A readable description of an intermediate format is valuable documentation, but it is not a substitute for a parser-compatible artifact.

### Bit-level reasoning: representation contracts

Bit-level interfaces need precise treatment of ordering and encodings. If three bits are stored as a function on `Fin 3`, the index domain is formal and finite. If they are stored in a machine word, the bit-position convention, shifts, width, and overflow behavior must be stated. The phrase “flip bit one” is not sufficiently precise unless the indexing base and orientation are known. Syndrome conventions must specify what each Boolean signifies: equality of adjacent coordinates and XOR of adjacent coordinates express complementary conditions, even when their correction maps ultimately restore the same codeword.

Exact recovery should be expressed as a composition of encode, corruption, syndrome, correction, and decode operations. The admitted error class must appear in the statement. A proof for at most one bit flip is not a proof for arbitrary corruption or arbitrary quantum errors. The same caution applies to low-level numeric witnesses: observing an expected output for a fixed set of states does not establish a universal equivalence. Those distinctions make bit-oriented work reviewable without overstating its guarantees.

### Autocode: preserving semantics across representations

Autocode can serve as a concrete mathematical implementation, a code generator, or a diagnostic harness; these are different responsibilities. A generator produces artifacts, a checker validates claims, and a witness prints or records observed values. When a mathematical object is moved from exact real or ring reasoning into floating-point arithmetic, associativity and distributivity can fail in ordinary machine computation because of rounding, underflow, overflow, and exceptional values. Any claim of semantic preservation therefore needs an explicit numeric model and stated tolerances, or a representation that retains exact arithmetic.

Generated source should identify its input representation, output format, naming conventions, and deterministic ordering rules. If two backends share a theorem statement, describe the translation of types and operations between them before asserting their equivalence. A successful emission step establishes that a file was produced; it does not establish that the file is accepted by a compiler or that its behavior matches the mathematical source. This is especially important for hardware-oriented or optimizer-facing backends, where interface compatibility and mathematical correctness are separate obligations.


### Evidence-oriented review flow

```mermaid
flowchart TD
    A[Select mathematical claim]
    B[Locate formal definition]
    C[Compare representations and assumptions]
    D[Identify proof or contract]
    E{Evidence available?}
    F[Record checked theorem or validated result]
    G[Record open obligation or unverified claim]
    H[Update theorem index and documentation]
    A --> B --> C --> D --> E
    E -->|Yes| F --> H
    E -->|No| G --> H
```





