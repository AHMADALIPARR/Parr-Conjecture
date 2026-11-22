# Parr-AMPL Toolchain

Full AMPL-style pipeline for the Parr Conjecture formalisation:

```
.mod + .dat
    → translator / presolver   (parr_ampl.translator)
    → model expansion + constraint processing
    → NLProblem IR            (variables, bounds, linear terms, expr trees)
    → .nl intermediate        (parr_ampl.nl_writer)
    → MP driver / ASL-style API
    → solver backends         (SciPy, HiGHS, Ipopt, Gurobi, CPLEX)
```

Lean-side certification lives in `ParrDSL/AMPL.lean` and `GKN/VerifyE7Bridge.lean`.
Every stock model constraint cites a machine-checked theorem.

## Layout

```
ampl/
  models/
    i4_scale.mod / .dat          # maximise |λ⁴ I₄(s)|
    free_energy.mod / .dat       # minimise βE + ln Z(β)
  parr_ampl/
    ir.py                        # NL IR: Expr trees, Variable, Objective, Constraint
    translator.py                # .mod+.dat → NLProblem
    nl_writer.py                 # NLProblem → .nl text
    solvers.py                   # SciPy / HiGHS / Ipopt / Gurobi / CPLEX
    driver.py                    # CLI
```

## Quick start

```bash
# from repo root
python ampl/parr_ampl/driver.py ampl/models/i4_scale.mod ampl/models/i4_scale.dat --solver scipy --nl /tmp/i4.nl

python ampl/parr_ampl/driver.py ampl/models/free_energy.mod ampl/models/free_energy.dat --solver scipy --json
```

Optional solvers:

| Solver | Package | Notes |
|--------|---------|-------|
| SciPy  | `scipy` | default NLP (SLSQP) |
| HiGHS  | `highspy` | LP/MIP; NLP falls back to SciPy |
| Ipopt  | `cyipopt` | interior-point NLP |
| Gurobi | `gurobipy` | commercial; stub → fallback |
| CPLEX  | `cplex` | commercial; stub → fallback |

```bash
pip install scipy numpy          # required
pip install highspy              # optional
pip install cyipopt              # optional
```

## IR overview

- **Variables**: name, index, lb/ub, init
- **Linear terms**: `(var_index, coeff)`
- **Expr trees**: `CONST | VAR | ADD|SUB|MUL|DIV|POW|NEG|ABS|EXP|LOG|SIN|COS|SUM`
- **Objectives**: sense + linear + nonlinear + constant
- **Constraints**: rel ∈ {EQ,LE,GE} + linear + nonlinear + rhs

## Certification link

`NLProblem.meta["certified"]` lists Lean theorem names. The Lean module
`ParrDSL.AMPL` proves stock models only reference theorems in
`certifiedContracts`, closed by `all_closed_checks`.
