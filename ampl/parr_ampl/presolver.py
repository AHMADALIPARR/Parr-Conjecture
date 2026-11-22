"""Presolver passes over NLProblem.

  - Bound propagation
  - Constraint simplification
  - Variable elimination (fixed vars)
  - Infeasibility detection
"""
from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from .ir import (
    Constraint,
    Expr,
    LinearTerm,
    NLProblem,
    Objective,
    Op,
    Rel,
    Sense,
    Variable,
)


@dataclass
class PresolveReport:
    bound_updates: int = 0
    constraints_removed: int = 0
    variables_fixed: int = 0
    infeasible: bool = False
    messages: List[str] = field(default_factory=list)

    def log(self, msg: str) -> None:
        self.messages.append(msg)


def _is_fixed(v: Variable) -> bool:
    return v.lb == v.ub and v.lb not in (float("-inf"), float("+inf"))


def bound_propagation(problem: NLProblem, report: PresolveReport) -> NLProblem:
    """Tighten bounds from linear equality/inequality constraints."""
    p = deepcopy(problem)
    changed = True
    rounds = 0
    while changed and rounds < 20:
        changed = False
        rounds += 1
        for c in p.constraints:
            if c.nonlinear is not None:
                continue
            if len(c.linear) != 1:
                continue
            t = c.linear[0]
            v = p.variables[t.var_index]
            if t.coeff == 0:
                continue
            # a*x  rel  constant  →  bound on x
            rhs = c.constant / t.coeff
            if c.rel == Rel.EQ:
                if v.lb < rhs or v.ub > rhs:
                    v.lb = v.ub = rhs
                    report.bound_updates += 1
                    changed = True
            elif c.rel == Rel.GE:
                # a*x >= const
                if t.coeff > 0 and rhs > v.lb:
                    v.lb = rhs
                    report.bound_updates += 1
                    changed = True
                elif t.coeff < 0 and rhs < v.ub:
                    v.ub = rhs
                    report.bound_updates += 1
                    changed = True
            elif c.rel == Rel.LE:
                if t.coeff > 0 and rhs < v.ub:
                    v.ub = rhs
                    report.bound_updates += 1
                    changed = True
                elif t.coeff < 0 and rhs > v.lb:
                    v.lb = rhs
                    report.bound_updates += 1
                    changed = True
    return p


def detect_infeasibility(problem: NLProblem, report: PresolveReport) -> NLProblem:
    for v in problem.variables:
        if v.lb > v.ub + 1e-12:
            report.infeasible = True
            report.log(f"infeasible bounds on {v.name}: lb={v.lb} > ub={v.ub}")
    for c in problem.constraints:
        if c.nonlinear is None and not c.linear:
            # 0  rel  constant
            if c.rel == Rel.EQ and abs(c.constant) > 1e-12:
                report.infeasible = True
                report.log(f"infeasible empty constraint {c.name}: 0 == {c.constant}")
            if c.rel == Rel.GE and c.constant > 1e-12:
                report.infeasible = True
                report.log(f"infeasible empty constraint {c.name}: 0 >= {c.constant}")
            if c.rel == Rel.LE and c.constant < -1e-12:
                report.infeasible = True
                report.log(f"infeasible empty constraint {c.name}: 0 <= {c.constant}")
    return problem


def simplify_constraints(problem: NLProblem, report: PresolveReport) -> NLProblem:
    """Drop tautologies; fold fixed-variable linear terms into constants."""
    p = deepcopy(problem)
    fixed = {v.index: v.lb for v in p.variables if _is_fixed(v)}
    new_cons: List[Constraint] = []
    for c in p.constraints:
        lin: List[LinearTerm] = []
        const = c.constant
        for t in c.linear:
            if t.var_index in fixed:
                # a*x moves to constant side: a*x - const  rel  0
                # body = sum a_i x_i + nl ; compare to constant
                # when x fixed, a*x is known: subtract from constant for EQ form
                const = const - t.coeff * fixed[t.var_index]
            else:
                lin.append(t)
        # tautology: no terms and satisfied
        if not lin and c.nonlinear is None:
            ok = False
            if c.rel == Rel.EQ and abs(const) <= 1e-12:
                ok = True
            if c.rel == Rel.GE and const <= 1e-12:
                ok = True
            if c.rel == Rel.LE and const >= -1e-12:
                ok = True
            if ok:
                report.constraints_removed += 1
                report.log(f"removed tautology {c.name}")
                continue
        new_cons.append(
            Constraint(
                name=c.name,
                rel=c.rel,
                linear=lin,
                nonlinear=c.nonlinear,
                constant=const,
                lb=c.lb,
                ub=c.ub,
            )
        )
    p.constraints = new_cons
    return p


def eliminate_fixed_variables(problem: NLProblem, report: PresolveReport) -> NLProblem:
    """Record fixed vars; substitute into objectives (linear part)."""
    p = deepcopy(problem)
    fixed = {v.index: v.lb for v in p.variables if _is_fixed(v)}
    report.variables_fixed = len(fixed)
    if not fixed:
        return p
    for o in p.objectives:
        new_lin = []
        const = o.constant
        for t in o.linear:
            if t.var_index in fixed:
                const += t.coeff * fixed[t.var_index]
            else:
                new_lin.append(t)
        o.linear = new_lin
        o.constant = const
    report.log(f"fixed {len(fixed)} variables: {sorted(fixed)}")
    return p


def presolve(problem: NLProblem) -> Tuple[NLProblem, PresolveReport]:
    report = PresolveReport()
    p = bound_propagation(problem, report)
    p = detect_infeasibility(p, report)
    if report.infeasible:
        return p, report
    p = simplify_constraints(p, report)
    p = eliminate_fixed_variables(p, report)
    p = detect_infeasibility(p, report)
    p.meta = dict(problem.meta)
    p.meta["presolve"] = {
        "bound_updates": report.bound_updates,
        "constraints_removed": report.constraints_removed,
        "variables_fixed": report.variables_fixed,
        "infeasible": report.infeasible,
        "messages": report.messages,
    }
    return p, report
