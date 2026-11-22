# Parr-AMPL Toolchain

**This is a Python modelling pipeline — not MLIR, not LLVM.**

```
.mod / .dat
    → lexer / parser / AST     (frontend.py)
    → model translator         (translator.py)
    → presolver                (presolver.py)
    → .nl text dump            (nl_writer.py)
    → solver backends          (solvers.py)
    → solution + diagnostics   (pipeline.py)
```

Lean-side certification is separate: `ParrDSL/AMPL.lean`, `GKN/VerifyE7Bridge.lean`.

## What exists

| Component | Real? |
|-----------|-------|
| `.mod` / `.dat` sources | yes |
| Lexer / parser / AST | yes (Python) |
| Translator → `NLProblem` | yes |
| Presolver (bounds, simplify, fix, infeas) | yes |
| `.nl`-style text dump | yes (subset, not full ASL binary) |
| SciPy / HiGHS / Ipopt drivers | yes (with fallbacks) |
| **MLIR dialect** | **no — removed** |
| **LLVM/MLIR lowering** | **no** |

## Run

```bash
python ampl/parr_ampl/driver.py ampl/models/i4_scale.mod ampl/models/i4_scale.dat \
  --solver scipy --json

python ampl/parr_ampl/driver.py ampl/models/free_energy.mod ampl/models/free_energy.dat \
  --solver scipy --json
```

Optional: `pip install scipy numpy highspy cyipopt`

## Models

- `ampl/models/i4_scale.mod` + `.dat`
- `ampl/models/free_energy.mod` + `.dat`
