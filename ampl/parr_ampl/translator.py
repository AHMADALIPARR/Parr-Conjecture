"""AMPL translator / presolver.

Pipeline:
  .mod + .dat  →  parse  →  expand sets/params  →  constraint processing
               →  NLProblem (variables, bounds, linear terms, expression trees)

This is a focused translator for the Parr Conjecture model family, not a
full AMPL front-end. It handles the constructs used in ampl/models/*.mod.
"""
from __future__ import annotations

import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from .ir import (
    C,
    Constraint,
    Expr,
    LinearTerm,
    NLProblem,
    Objective,
    Op,
    Rel,
    Sense,
    Variable,
    V,
    abs_,
    add,
    exp_,
    log_,
    mul,
    pow_,
    sub,
)


def _strip_comments(text: str) -> str:
    out = []
    for line in text.splitlines():
        if "#" in line:
            line = line[: line.index("#")]
        out.append(line)
    return "\n".join(out)


def parse_dat(text: str) -> Dict[str, float]:
    """Parse a simple AMPL .dat into scalar params (and flat 1-indexed vectors as param[i])."""
    text = _strip_comments(text)
    params: Dict[str, float] = {}
    for m in re.finditer(r"param\s+(\w+)\s*:=\s*([-+eE0-9.]+)\s*;", text):
        params[m.group(1)] = float(m.group(2))
    for m in re.finditer(
        r"param\s+(\w+)\s*:=\s*((?:\d+\s+[-+eE0-9.]+\s*)+)\s*;",
        text,
        re.DOTALL,
    ):
        name = m.group(1)
        pairs = re.findall(r"(\d+)\s+([-+eE0-9.]+)", m.group(2))
        for i, v in pairs:
            params[f"{name}[{i}]"] = float(v)
        params[name + "__n"] = float(len(pairs))
    return params


def parse_mod_header(text: str) -> Tuple[List[str], List[Tuple[str, Optional[float], Optional[float]]]]:
    """Extract param names and var declarations from .mod."""
    text = _strip_comments(text)
    params = re.findall(r"param\s+(\w+)", text)
    vars_: List[Tuple[str, Optional[float], Optional[float]]] = []
    for m in re.finditer(
        r"var\s+(\w+)(?:\s*>=\s*([-+eE0-9.]+))?(?:\s*<=\s*([-+eE0-9.]+))?\s*;",
        text,
    ):
        lb = float(m.group(2)) if m.group(2) else None
        ub = float(m.group(3)) if m.group(3) else None
        vars_.append((m.group(1), lb, ub))
    return params, vars_


def detect_sense(text: str) -> Tuple[Sense, str]:
    text = _strip_comments(text)
    m = re.search(r"(minimize|maximize)\s+(\w+)\s*:", text, re.I)
    if not m:
        return Sense.MINIMIZE, "obj"
    sense = Sense.MINIMIZE if m.group(1).lower() == "minimize" else Sense.MAXIMIZE
    return sense, m.group(2)


def expand_i4_scale(params: Dict[str, float], vars_decl) -> NLProblem:
    I4_s = params.get("I4_s", 1.0)
    problem = NLProblem(name="I4_ScaleHomogeneous", params=dict(params))
    lb = vars_decl[0][1] if vars_decl and vars_decl[0][1] is not None else 0.0
    # Default finite upper bound: maximising lambda^4 is unbounded without one
    ub = vars_decl[0][2] if vars_decl and vars_decl[0][2] is not None else 5.0
    problem.variables.append(
        Variable(
            "lambda",
            0,
            lb=float(lb) if lb is not None else 0.0,
            ub=float(ub) if ub is not None else 5.0,
            init=1.0,
        )
    )
    body = abs_(mul(pow_(V(0), C(4.0)), C(I4_s)))
    problem.objectives.append(
        Objective(name="abs_I4", sense=Sense.MAXIMIZE, nonlinear=body)
    )
    problem.constraints.append(
        Constraint(
            name="homogeneity_doc",
            rel=Rel.GE,
            linear=[LinearTerm(0, 1.0)],
            constant=0.0,
        )
    )
    problem.meta["certified"] = ["I4_scale_invariant", "FTS56.I4_homogeneous"]
    return problem


def expand_free_energy(params: Dict[str, float], vars_decl) -> NLProblem:
    n = int(params.get("n", params.get("E__n", 0)))
    E = [params.get(f"E[{i}]", 0.0) for i in range(1, n + 1)]
    E_target = params.get("E_target", 0.0)
    problem = NLProblem(name="FreeEnergy_Legendre", params=dict(params))
    problem.variables.append(Variable("beta", 0, init=1.0))
    terms = [exp_(mul(C(-E[i]), V(0))) for i in range(n)]
    Z = Expr(Op.SUM, children=terms) if terms else C(1.0)
    body = add(mul(V(0), C(E_target)), log_(Z))
    problem.objectives.append(
        Objective(name="free_energy", sense=Sense.MINIMIZE, nonlinear=body)
    )
    problem.constraints.append(
        Constraint(
            name="Z_positive",
            rel=Rel.GE,
            nonlinear=Z,
            constant=1e-300,
        )
    )
    problem.meta["certified"] = ["partition_Z_pos", "log_sum_exp_lower"]
    problem.meta["E"] = E
    return problem


def translate(mod_path: str | Path, dat_path: Optional[str | Path] = None) -> NLProblem:
    """Translate .mod (+ optional .dat) into an NLProblem."""
    mod_path = Path(mod_path)
    mod_text = mod_path.read_text()
    params: Dict[str, float] = {}
    if dat_path:
        params.update(parse_dat(Path(dat_path).read_text()))
    for m in re.finditer(r"param\s+(\w+)\s+default\s+([-+eE0-9.]+)", mod_text):
        params.setdefault(m.group(1), float(m.group(2)))
    _, vars_decl = parse_mod_header(mod_text)
    sense, obj_name = detect_sense(mod_text)

    name_lower = mod_path.stem.lower()
    if "i4" in name_lower or "scale" in name_lower:
        return expand_i4_scale(params, vars_decl)
    if "free" in name_lower or "energy" in name_lower or "legendre" in name_lower:
        return expand_free_energy(params, vars_decl)

    problem = NLProblem(name=mod_path.stem, params=params)
    for i, (vn, lb, ub) in enumerate(vars_decl):
        problem.variables.append(
            Variable(
                vn,
                i,
                lb=lb if lb is not None else float("-inf"),
                ub=ub if ub is not None else float("+inf"),
            )
        )
    if problem.variables:
        problem.objectives.append(
            Objective(
                name=obj_name,
                sense=sense,
                linear=[LinearTerm(0, 1.0)],
            )
        )
    return problem
