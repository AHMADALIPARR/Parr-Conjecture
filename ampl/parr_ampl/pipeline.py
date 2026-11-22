"""End-to-end Parr-AMPL pipeline.

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
        ├── LP / MILP backend
        ├── NLP backend
        └── Constraint programming backend
        │
        ▼
Solution + Status + Diagnostics
"""
from __future__ import annotations

import json
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional

from .frontend import ModelAST, parse_files
from .translator import translate
from .presolver import presolve, PresolveReport
from .mlir_dialect import dialect_to_solver_hint, lower_to_dialect, Module
from .nl_writer import write_nl
from .solvers import solve, SolveResult
from .ir import NLProblem


@dataclass
class PipelineDiagnostics:
    stage: List[str] = field(default_factory=list)
    ast_params: int = 0
    ast_vars: int = 0
    ast_constraints: int = 0
    presolve: Dict[str, Any] = field(default_factory=dict)
    dialect_target: str = ""
    dialect_dump: str = ""
    nl_path: Optional[str] = None
    solver: str = ""
    status: str = ""
    obj_value: Optional[float] = None
    x: Dict[str, float] = field(default_factory=dict)
    message: str = ""
    certified: List[str] = field(default_factory=list)

    def to_json(self) -> str:
        return json.dumps({
            "stage": self.stage,
            "ast": {
                "params": self.ast_params,
                "vars": self.ast_vars,
                "constraints": self.ast_constraints,
            },
            "presolve": self.presolve,
            "dialect_target": self.dialect_target,
            "nl_path": self.nl_path,
            "solver": self.solver,
            "status": self.status,
            "obj_value": self.obj_value,
            "x": self.x,
            "message": self.message,
            "certified": self.certified,
        }, indent=2)


@dataclass
class PipelineResult:
    problem: NLProblem
    dialect: Module
    solve: SolveResult
    diagnostics: PipelineDiagnostics


def run_pipeline(
    mod_path: str | Path,
    dat_path: Optional[str | Path] = None,
    *,
    solver: Optional[str] = None,
    nl_out: Optional[str | Path] = None,
    dump_dialect: bool = False,
) -> PipelineResult:
    diag = PipelineDiagnostics()

    # 1. Lexer → Parser → Typed AST
    diag.stage.append("frontend")
    ast: ModelAST = parse_files(str(mod_path), str(dat_path) if dat_path else None)
    diag.ast_params = len(ast.params)
    diag.ast_vars = len(ast.vars)
    diag.ast_constraints = len(ast.constraints)

    # 2. Model Translator (.mod+.dat → NLProblem)
    #    Uses domain expanders; AST is available for future generic lowering.
    diag.stage.append("translate")
    problem = translate(mod_path, dat_path)
    diag.certified = list(problem.meta.get("certified", []))

    # 3. Presolver
    diag.stage.append("presolve")
    problem, report = presolve(problem)
    diag.presolve = {
        "bound_updates": report.bound_updates,
        "constraints_removed": report.constraints_removed,
        "variables_fixed": report.variables_fixed,
        "infeasible": report.infeasible,
        "messages": report.messages,
    }
    if report.infeasible:
        diag.status = "infeasible"
        diag.message = "; ".join(report.messages)
        empty = SolveResult("infeasible", None, message=diag.message, solver="presolve")
        dialect = lower_to_dialect(problem)
        return PipelineResult(problem, dialect, empty, diag)

    # 4. Custom MLIR Optimization Dialect
    diag.stage.append("mlir_dialect")
    dialect = lower_to_dialect(problem)
    diag.dialect_target = dialect.target.name
    if dump_dialect:
        diag.dialect_dump = dialect.dump()

    # 5. .nl serialization
    diag.stage.append("nl")
    if nl_out is None:
        nl_out = Path(mod_path).with_suffix(".nl")
    nl_path = write_nl(problem, nl_out)
    diag.nl_path = str(nl_path)

    # 6. MP driver + solver backends
    diag.stage.append("solve")
    chosen = solver or dialect_to_solver_hint(dialect)
    result = solve(problem, solver=chosen)
    diag.solver = result.solver
    diag.status = result.status
    diag.obj_value = result.obj_value
    diag.x = result.x
    diag.message = result.message

    # 7. Solution + diagnostics (already filled)
    diag.stage.append("diagnostics")
    return PipelineResult(problem, dialect, result, diag)
