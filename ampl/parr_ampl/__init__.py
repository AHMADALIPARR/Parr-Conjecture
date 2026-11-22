"""Parr-AMPL: AMPL-style modelling toolchain for the Parr Conjecture."""

from .ir import NLProblem, Sense, Rel, Variable, Objective, Constraint, Expr
from .translator import translate
from .nl_writer import write_nl
from .solvers import solve, SolveResult, SOLVERS
from .pipeline import run_pipeline, PipelineResult, PipelineDiagnostics
from .presolver import presolve
from .mlir_dialect import lower_to_dialect
from .frontend import parse_files, parse_mod, lex

__all__ = [
    "NLProblem",
    "Sense",
    "Rel",
    "Variable",
    "Objective",
    "Constraint",
    "Expr",
    "translate",
    "write_nl",
    "solve",
    "SolveResult",
    "SOLVERS",
    "run_pipeline",
    "PipelineResult",
    "PipelineDiagnostics",
    "presolve",
    "lower_to_dialect",
    "parse_files",
    "parse_mod",
    "lex",
]
