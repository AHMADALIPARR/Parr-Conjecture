"""Write NLProblem to AMPL .nl intermediate representation (text subset).

Reference: Gay, "Writing .nl files" / ASL stub format.
We emit a readable, structured .nl-like document sufficient for our MP driver.
"""
from __future__ import annotations

from pathlib import Path
from typing import List

from .ir import Constraint, Expr, NLProblem, Objective, Op, Rel, Sense


def _fmt_expr(e: Expr, vars_names: List[str]) -> str:
    if e.op == Op.CONST:
        return repr(e.value)
    if e.op == Op.VAR:
        assert e.var_index is not None
        return vars_names[e.var_index]
    if e.op == Op.NEG:
        return f"(-{_fmt_expr(e.children[0], vars_names)})"
    if e.op == Op.ABS:
        return f"abs({_fmt_expr(e.children[0], vars_names)})"
    if e.op == Op.EXP:
        return f"exp({_fmt_expr(e.children[0], vars_names)})"
    if e.op == Op.LOG:
        return f"log({_fmt_expr(e.children[0], vars_names)})"
    if e.op == Op.SIN:
        return f"sin({_fmt_expr(e.children[0], vars_names)})"
    if e.op == Op.COS:
        return f"cos({_fmt_expr(e.children[0], vars_names)})"
    if e.op in (Op.ADD, Op.SUM):
        return "(" + " + ".join(_fmt_expr(c, vars_names) for c in e.children) + ")"
    if e.op == Op.SUB:
        return f"({_fmt_expr(e.children[0], vars_names)} - {_fmt_expr(e.children[1], vars_names)})"
    if e.op == Op.MUL:
        return f"({_fmt_expr(e.children[0], vars_names)} * {_fmt_expr(e.children[1], vars_names)})"
    if e.op == Op.DIV:
        return f"({_fmt_expr(e.children[0], vars_names)} / {_fmt_expr(e.children[1], vars_names)})"
    if e.op == Op.POW:
        return f"({_fmt_expr(e.children[0], vars_names)} ^ {_fmt_expr(e.children[1], vars_names)})"
    return f"/* unknown op {e.op} */"


def write_nl(problem: NLProblem, path: str | Path) -> Path:
    path = Path(path)
    names = [v.name for v in problem.variables]
    lines: List[str] = []
    lines.append(f"g3 1 1 0  # Parr-AMPL NL intermediate for {problem.name}")
    lines.append(f"# n_var={problem.n_var} n_con={problem.n_con} n_obj={problem.n_obj}")
    lines.append(f"{problem.n_var} {problem.n_con} {problem.n_obj} 0 0 0  # vars cons objs ranges lcons")
    lines.append("")
    lines.append("# Variables")
    for v in problem.variables:
        lines.append(f"# {v.index}: {v.name}  lb={v.lb}  ub={v.ub}  init={v.init}")
    lines.append("")
    lines.append("# Bounds b")
    for v in problem.variables:
        # 0 = free, 1 = lb only, 2 = ub only, 3 = both, 4 = fixed
        if v.lb == float("-inf") and v.ub == float("+inf"):
            tag = 0
        elif v.ub == float("+inf"):
            tag = 1
        elif v.lb == float("-inf"):
            tag = 2
        elif v.lb == v.ub:
            tag = 4
        else:
            tag = 3
        lines.append(f"{tag} {v.lb} {v.ub}")
    lines.append("")
    lines.append("# Objectives")
    for o in problem.objectives:
        sense = "min" if o.sense == Sense.MINIMIZE else "max"
        lin = " + ".join(f"{t.coeff}*{names[t.var_index]}" for t in o.linear) or "0"
        nl = _fmt_expr(o.nonlinear, names) if o.nonlinear else "0"
        lines.append(f"# {sense} {o.name}: linear=({lin}) + nonlinear=({nl}) + const={o.constant}")
        lines.append(f"O {0 if o.sense == Sense.MINIMIZE else 1}  # 0=min 1=max")
    lines.append("")
    lines.append("# Constraints")
    for c in problem.constraints:
        rel = {Rel.EQ: "==", Rel.LE: "<=", Rel.GE: ">="}[c.rel]
        lin = " + ".join(f"{t.coeff}*{names[t.var_index]}" for t in c.linear) or "0"
        nl = _fmt_expr(c.nonlinear, names) if c.nonlinear else "0"
        lines.append(f"# {c.name}: ({lin}) + ({nl}) {rel} {c.constant}")
        lines.append(f"C  # body follows in driver evaluation")
    lines.append("")
    if problem.meta.get("certified"):
        lines.append("# Certified Lean contracts:")
        for th in problem.meta["certified"]:
            lines.append(f"#   - {th}")
    lines.append("end")
    path.write_text("\n".join(lines) + "\n")
    return path
