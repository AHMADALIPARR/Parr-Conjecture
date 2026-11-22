"""Parr-AMPL pipeline (honest stages only).

  .mod / .dat
      → lexer / parser / AST   (frontend)
      → model translator       (translator)
      → presolver              (bounds, simplify, eliminate, infeasibility)
      → .nl write              (nl_writer)
      → solver driver          (solvers)
      → solution + diagnostics

No MLIR. No LLVM. Python IR only.
"""
from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional

from .frontend import ModelAST, parse_files
from .translator import translate
from .presolver import presolve
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
    nl_path: Optional[str] = None
    solver: str = ""
    status: str = ""
    obj_value: Optional[float] = None
    x: Dict[str, float] = field(default_factory=dict)
    message: str = ""
    certified: List[str] = field(default_factory=list)

    def to_json(self) -> str:
        return json.dumps(
            {
                "stage": self.stage,
                "ast": {
                    "params": self.ast_params,
                    "vars": self.ast_vars,
                    "constraints": self.ast_constraints,
                },
                "presolve": self.presolve,
                "nl_path": self.nl_path,
                "solver": self.solver,
                "status": self.status,
                "obj_value": self.obj_value,
                "x": self.x,
                "message": self.message,
                "certified": self.certified,
            },
            indent=2,
        )


@dataclass
class PipelineResult:
    problem: NLProblem
    solve: SolveResult
    diagnostics: PipelineDiagnostics


def run_pipeline(
    mod_path: str | Path,
    dat_path: Optional[str | Path] = None,
    *,
    solver: Optional[str] = None,
    nl_out: Optional[str | Path] = None,
) -> PipelineResult:
    diag = PipelineDiagnostics()

    diag.stage.append("frontend")
    ast: ModelAST = parse_files(str(mod_path), str(dat_path) if dat_path else None)
    diag.ast_params = len(ast.params)
    diag.ast_vars = len(ast.vars)
    diag.ast_constraints = len(ast.constraints)

    diag.stage.append("translate")
    problem = translate(mod_path, dat_path)
    diag.certified = list(problem.meta.get("certified", []))

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
        return PipelineResult(problem, empty, diag)

    diag.stage.append("nl")
    if nl_out is None:
        nl_out = Path(mod_path).with_suffix(".nl")
    diag.nl_path = str(write_nl(problem, nl_out))

    diag.stage.append("solve")
    chosen = solver or "scipy"
    result = solve(problem, solver=chosen)
    diag.solver = result.solver
    diag.status = result.status
    diag.obj_value = result.obj_value
    diag.x = result.x
    diag.message = result.message

    diag.stage.append("diagnostics")
    return PipelineResult(problem, result, diag)
