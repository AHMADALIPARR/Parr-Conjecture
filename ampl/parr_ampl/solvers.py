"""AMPL Solver Library / MP driver.

Reformulates NLProblem into solver-specific APIs:
  - SciPy (SLSQP / trust-constr) — always available with scipy
  - HiGHS — via highspy if installed (LP/MIP; NLP falls back)
  - Ipopt — via cyipopt if installed
  - Gurobi / CPLEX — optional commercial stubs

Returns a common SolveResult.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence

from .ir import (
    Constraint,
    Expr,
    NLProblem,
    Objective,
    Op,
    Rel,
    Sense,
    Variable,
)


@dataclass
class SolveResult:
    status: str
    obj_value: Optional[float]
    x: Dict[str, float] = field(default_factory=dict)
    message: str = ""
    solver: str = ""
    raw: Any = None


# ── Expression evaluation (for nonlinear drivers) ────────────────────────────

def eval_expr(e: Expr, x: Sequence[float]) -> float:
    if e.op == Op.CONST:
        return float(e.value)
    if e.op == Op.VAR:
        return float(x[e.var_index])
    if e.op == Op.NEG:
        return -eval_expr(e.children[0], x)
    if e.op == Op.ABS:
        return abs(eval_expr(e.children[0], x))
    if e.op == Op.EXP:
        return math.exp(eval_expr(e.children[0], x))
    if e.op == Op.LOG:
        v = eval_expr(e.children[0], x)
        return math.log(max(v, 1e-300))
    if e.op == Op.SIN:
        return math.sin(eval_expr(e.children[0], x))
    if e.op == Op.COS:
        return math.cos(eval_expr(e.children[0], x))
    if e.op in (Op.ADD, Op.SUM):
        return sum(eval_expr(c, x) for c in e.children)
    if e.op == Op.SUB:
        return eval_expr(e.children[0], x) - eval_expr(e.children[1], x)
    if e.op == Op.MUL:
        return eval_expr(e.children[0], x) * eval_expr(e.children[1], x)
    if e.op == Op.DIV:
        den = eval_expr(e.children[1], x)
        return eval_expr(e.children[0], x) / (den if den != 0 else 1e-300)
    if e.op == Op.POW:
        base = eval_expr(e.children[0], x)
        exp = eval_expr(e.children[1], x)
        if base < 0 and abs(exp - round(exp)) > 1e-12:
            base = abs(base)
        return math.pow(base, exp)
    raise ValueError(f"unknown op {e.op}")


def eval_objective(obj: Objective, x: Sequence[float]) -> float:
    val = obj.constant
    for t in obj.linear:
        val += t.coeff * x[t.var_index]
    if obj.nonlinear is not None:
        val += eval_expr(obj.nonlinear, x)
    return val


def eval_constraint_body(c: Constraint, x: Sequence[float]) -> float:
    val = 0.0
    for t in c.linear:
        val += t.coeff * x[t.var_index]
    if c.nonlinear is not None:
        val += eval_expr(c.nonlinear, x)
    return val


# ── SciPy backend ────────────────────────────────────────────────────────────

def solve_scipy(problem: NLProblem, method: str = "SLSQP") -> SolveResult:
    try:
        import numpy as np
        from scipy.optimize import minimize
    except ImportError:
        return SolveResult("error", None, message="scipy not installed", solver="scipy")

    n = problem.n_var
    if n == 0:
        return SolveResult("ok", 0.0, message="no variables", solver="scipy")

    x0 = []
    bounds = []
    for v in problem.variables:
        lo = None if v.lb == float("-inf") else v.lb
        hi = None if v.ub == float("+inf") else v.ub
        bounds.append((lo, hi))
        if v.init is not None:
            x0.append(v.init)
        else:
            x0.append(0.0 if lo is None else max(lo, 0.0))
    x0 = np.array(x0, dtype=float)

    obj = problem.objectives[0] if problem.objectives else None
    if obj is None:
        return SolveResult("error", None, message="no objective", solver="scipy")

    def f(x):
        val = eval_objective(obj, x)
        return val if obj.sense == Sense.MINIMIZE else -val

    cons = []
    for c in problem.constraints:
        def body_factory(cc):
            def body(x):
                return eval_constraint_body(cc, x) - cc.constant
            return body
        b = body_factory(c)
        if c.rel == Rel.EQ:
            cons.append({"type": "eq", "fun": b})
        elif c.rel == Rel.GE:
            cons.append({"type": "ineq", "fun": b})  # body - const >= 0
        elif c.rel == Rel.LE:
            cons.append({"type": "ineq", "fun": lambda x, b=b: -b(x)})

    res = minimize(f, x0, method=method, bounds=bounds, constraints=cons or None)
    xmap = {v.name: float(res.x[i]) for i, v in enumerate(problem.variables)}
    obj_val = eval_objective(obj, res.x)
    status = "ok" if res.success else "fail"
    return SolveResult(status, obj_val, xmap, message=str(res.message), solver=f"scipy:{method}", raw=res)


# ── HiGHS backend (LP/MIP; NLP → note + scipy fallback) ─────────────────────

def solve_highs(problem: NLProblem) -> SolveResult:
    # Check linearity
    nonlinear = any(
        (o.nonlinear and not o.nonlinear.is_linear()) for o in problem.objectives
    ) or any(
        (c.nonlinear and not c.nonlinear.is_linear()) for c in problem.constraints
    )
    if nonlinear:
        r = solve_scipy(problem)
        r.message = f"HiGHS skipped (nonlinear); fell back to scipy. {r.message}"
        r.solver = "highs->scipy"
        return r
    try:
        import highspy
    except ImportError:
        r = solve_scipy(problem)
        r.message = f"highspy not installed; fell back to scipy. {r.message}"
        r.solver = "highs->scipy"
        return r

    h = highspy.Highs()
    h.setOptionValue("output_flag", False)
    for v in problem.variables:
        lo = -1e20 if v.lb == float("-inf") else v.lb
        hi = 1e20 if v.ub == float("+inf") else v.ub
        h.addVar(lo, hi)
    # single linear objective
    obj = problem.objectives[0]
    sense = highspy.ObjSense.kMinimize if obj.sense == Sense.MINIMIZE else highspy.ObjSense.kMaximize
    h.changeObjectiveSense(sense)
    for t in obj.linear:
        h.changeColCost(t.var_index, t.coeff)
    for c in problem.constraints:
        lo, hi = -1e20, 1e20
        if c.rel == Rel.EQ:
            lo = hi = c.constant
        elif c.rel == Rel.GE:
            lo = c.constant
        elif c.rel == Rel.LE:
            hi = c.constant
        coeffs = [0.0] * problem.n_var
        for t in c.linear:
            coeffs[t.var_index] = t.coeff
        h.addRow(lo, hi, problem.n_var, list(range(problem.n_var)), coeffs)
    h.run()
    sol = h.getSolution()
    xmap = {v.name: float(sol.col_value[i]) for i, v in enumerate(problem.variables)}
    info = h.getInfo()
    return SolveResult(
        "ok" if h.getModelStatus() == highspy.HighsModelStatus.kOptimal else "fail",
        float(info.objective_function_value),
        xmap,
        message=str(h.getModelStatus()),
        solver="highs",
        raw=sol,
    )


# ── Ipopt backend ────────────────────────────────────────────────────────────

def solve_ipopt(problem: NLProblem) -> SolveResult:
    try:
        import numpy as np
        from cyipopt import minimize_ipopt
    except ImportError:
        r = solve_scipy(problem)
        r.message = f"cyipopt not installed; fell back to scipy. {r.message}"
        r.solver = "ipopt->scipy"
        return r

    obj = problem.objectives[0]
    n = problem.n_var
    x0 = np.array([v.init if v.init is not None else 0.0 for v in problem.variables])
    bounds = [
        (
            None if v.lb == float("-inf") else v.lb,
            None if v.ub == float("+inf") else v.ub,
        )
        for v in problem.variables
    ]

    def f(x):
        val = eval_objective(obj, x)
        return val if obj.sense == Sense.MINIMIZE else -val

    cons = []
    for c in problem.constraints:
        def make(cc):
            def body(x):
                return eval_constraint_body(cc, x) - cc.constant
            return body
        b = make(c)
        if c.rel == Rel.EQ:
            cons.append({"type": "eq", "fun": b})
        elif c.rel == Rel.GE:
            cons.append({"type": "ineq", "fun": b})
        else:
            cons.append({"type": "ineq", "fun": lambda x, b=b: -b(x)})

    res = minimize_ipopt(f, x0, bounds=bounds, constraints=cons or ())
    xmap = {v.name: float(res.x[i]) for i, v in enumerate(problem.variables)}
    return SolveResult(
        "ok" if res.success else "fail",
        eval_objective(obj, res.x),
        xmap,
        message=str(res.message),
        solver="ipopt",
        raw=res,
    )


# ── Commercial stubs ─────────────────────────────────────────────────────────

def solve_gurobi(problem: NLProblem) -> SolveResult:
    try:
        import gurobipy as gp  # noqa: F401
    except ImportError:
        r = solve_scipy(problem)
        r.message = f"gurobipy not installed; fell back to scipy. {r.message}"
        r.solver = "gurobi->scipy"
        return r
    # Minimal path: fall through to scipy unless LP
    return solve_highs(problem)


def solve_cplex(problem: NLProblem) -> SolveResult:
    try:
        import cplex  # noqa: F401
    except ImportError:
        r = solve_scipy(problem)
        r.message = f"cplex not installed; fell back to scipy. {r.message}"
        r.solver = "cplex->scipy"
        return r
    return solve_highs(problem)


SOLVERS: Dict[str, Callable[[NLProblem], SolveResult]] = {
    "scipy": solve_scipy,
    "highs": solve_highs,
    "ipopt": solve_ipopt,
    "gurobi": solve_gurobi,
    "cplex": solve_cplex,
}


def solve(problem: NLProblem, solver: str = "scipy") -> SolveResult:
    key = solver.lower().split(":")[0]
    if key not in SOLVERS:
        return SolveResult("error", None, message=f"unknown solver {solver}", solver=solver)
    return SOLVERS[key](problem)
