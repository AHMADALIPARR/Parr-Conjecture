# Parr-AMPL Toolchain

```
AMPL .mod / .dat
        │
        ▼
Lexer → Parser → Typed AST
        │
        ▼
Model Translator
        │
        ▼
Presolver
  ├── Bound propagation
  ├── Constraint simplification
  ├── Variable elimination
  └── Infeasibility detection
        │
        ▼
Custom MLIR Optimization Dialect
        │
        ├── Linear / quadratic IR
        ├── Nonlinear expression IR
        ├── Constraint transformations
        └── Solver-specific lowering
        │
        ▼
AMPL-compatible .nl serialization
        │
        ▼
MP-compatible Driver Layer
        │
        ├── LP / MILP backend   (HiGHS)
        ├── NLP backend        (SciPy, Ipopt)
        └── CP backend         (fallback)
        │
        ▼
Solution + Status + Diagnostics
```

Lean certification: `ParrDSL/AMPL.lean`, `GKN/VerifyE7Bridge.lean`.

## Package map

| Stage | Module |
|-------|--------|
| Lexer / Parser / Typed AST | `parr_ampl.frontend` |
| Model Translator | `parr_ampl.translator` |
| Presolver | `parr_ampl.presolver` |
| MLIR-style opt dialect | `parr_ampl.mlir_dialect` |
| .nl serialization | `parr_ampl.nl_writer` |
| MP driver / solvers | `parr_ampl.solvers` |
| Orchestrator | `parr_ampl.pipeline` |
| CLI | `parr_ampl.driver` |

## Models

```
ampl/models/i4_scale.mod + .dat
ampl/models/free_energy.mod + .dat
```

## Run

```bash
python ampl/parr_ampl/driver.py ampl/models/i4_scale.mod ampl/models/i4_scale.dat \
  --solver scipy --dump-dialect --json

python ampl/parr_ampl/driver.py ampl/models/free_energy.mod ampl/models/free_energy.dat \
  --nl /tmp/fe.nl --json
```

## Solver selection

Dialect lowering picks a default target:

| Target | Solver hint |
|--------|-------------|
| LP / MILP | `highs` |
| NLP | `scipy` (or `ipopt` if requested) |

Override with `--solver scipy|highs|ipopt|gurobi|cplex`.

## Diagnostics JSON (excerpt)

```json
{
  "stage": ["frontend", "translate", "presolve", "mlir_dialect", "nl", "solve", "diagnostics"],
  "presolve": {"bound_updates": 0, "infeasible": false},
  "dialect_target": "NLP",
  "status": "ok",
  "obj_value": 4375.0,
  "certified": ["I4_scale_invariant", "FTS56.I4_homogeneous"]
}
```
