"""Custom MLIR-inspired Optimization Dialect.

Not linked against LLVM/MLIR C++ — a structured Python dialect that mirrors
the same layering:

  opt.linear / opt.quadratic / opt.nonlinear expression ops
  opt.constraint transformations
  solver-specific lowering (lp, nlp, cp)

Operations are SSA-like values with explicit types.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, List, Optional, Sequence, Tuple

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


class DialectType(Enum):
    F64 = auto()
    I64 = auto()
    INDEX = auto()
    CONSTRAINT = auto()
    AFFINE = auto()
    QUAD = auto()
    NL = auto()


class LowerTarget(Enum):
    LP = auto()     # linear program
    MILP = auto()   # mixed-integer LP
    NLP = auto()    # nonlinear program
    CP = auto()     # constraint programming


@dataclass
class Value:
    id: int
    ty: DialectType
    name: str = ""


@dataclass
class Operation:
    opname: str                 # e.g. opt.constant, opt.add, opt.var_load
    results: List[Value]
    operands: List[Value] = field(default_factory=list)
    attrs: Dict[str, Any] = field(default_factory=dict)


@dataclass
class Block:
    ops: List[Operation] = field(default_factory=list)


@dataclass
class Module:
    """opt dialect module."""
    name: str
    vars: List[Value] = field(default_factory=list)
    body: Block = field(default_factory=Block)
    objectives: List[Operation] = field(default_factory=list)
    constraints: List[Operation] = field(default_factory=list)
    target: LowerTarget = LowerTarget.NLP
    meta: Dict[str, Any] = field(default_factory=dict)

    def dump(self) -> str:
        lines = [f"module @{self.name} attributes {{target = {self.target.name}}} {{"]
        for v in self.vars:
            lines.append(f"  %v{v.id} = opt.var name = \"{v.name}\" : {v.ty.name}")
        for op in self.body.ops:
            lines.append(f"  {_fmt_op(op)}")
        for op in self.objectives:
            lines.append(f"  {_fmt_op(op)}")
        for op in self.constraints:
            lines.append(f"  {_fmt_op(op)}")
        lines.append("}")
        return "\n".join(lines)


def _fmt_op(op: Operation) -> str:
    res = ", ".join(f"%r{v.id}" for v in op.results) or "_"
    args = ", ".join(f"%r{v.id}" if not v.name.startswith("v") else f"%v{v.id}" for v in op.operands)
    # simpler
    args = ", ".join(f"%{v.id}" for v in op.operands)
    attr = ""
    if op.attrs:
        attr = " {" + ", ".join(f"{k} = {v!r}" for k, v in op.attrs.items()) + "}"
    return f"{res} = {op.opname}{attr}({args})"


class Builder:
    def __init__(self) -> None:
        self._next = 0
        self.module = Module(name="opt")

    def _val(self, ty: DialectType, name: str = "") -> Value:
        v = Value(self._next, ty, name)
        self._next += 1
        return v

    def var(self, name: str, ty: DialectType = DialectType.F64) -> Value:
        v = self._val(ty, name)
        self.module.vars.append(v)
        return v

    def constant(self, value: float) -> Value:
        r = self._val(DialectType.F64)
        self.module.body.ops.append(
            Operation("opt.constant", [r], attrs={"value": value})
        )
        return r

    def add(self, a: Value, b: Value) -> Value:
        r = self._val(DialectType.F64)
        self.module.body.ops.append(Operation("opt.add", [r], [a, b]))
        return r

    def mul(self, a: Value, b: Value) -> Value:
        r = self._val(DialectType.F64)
        self.module.body.ops.append(Operation("opt.mul", [r], [a, b]))
        return r

    def pow(self, a: Value, b: Value) -> Value:
        r = self._val(DialectType.NL)
        self.module.body.ops.append(Operation("opt.pow", [r], [a, b]))
        return r

    def exp(self, a: Value) -> Value:
        r = self._val(DialectType.NL)
        self.module.body.ops.append(Operation("opt.exp", [r], [a]))
        return r

    def log(self, a: Value) -> Value:
        r = self._val(DialectType.NL)
        self.module.body.ops.append(Operation("opt.log", [r], [a]))
        return r

    def abs(self, a: Value) -> Value:
        r = self._val(DialectType.NL)
        self.module.body.ops.append(Operation("opt.abs", [r], [a]))
        return r

    def objective(self, sense: str, body: Value, name: str) -> None:
        self.module.objectives.append(
            Operation("opt.objective", [], [body], attrs={"sense": sense, "name": name})
        )

    def constraint(self, rel: str, body: Value, rhs: Value, name: str) -> None:
        self.module.constraints.append(
            Operation(
                "opt.constraint",
                [],
                [body, rhs],
                attrs={"rel": rel, "name": name},
            )
        )


def _expr_to_dialect(b: Builder, e: Expr, var_map: Dict[int, Value]) -> Value:
    if e.op == Op.CONST:
        return b.constant(float(e.value))
    if e.op == Op.VAR:
        return var_map[e.var_index]  # type: ignore[index]
    if e.op == Op.ADD or e.op == Op.SUM:
        acc = _expr_to_dialect(b, e.children[0], var_map)
        for c in e.children[1:]:
            acc = b.add(acc, _expr_to_dialect(b, c, var_map))
        return acc
    if e.op == Op.SUB:
        return b.add(
            _expr_to_dialect(b, e.children[0], var_map),
            b.mul(b.constant(-1.0), _expr_to_dialect(b, e.children[1], var_map)),
        )
    if e.op == Op.MUL:
        return b.mul(
            _expr_to_dialect(b, e.children[0], var_map),
            _expr_to_dialect(b, e.children[1], var_map),
        )
    if e.op == Op.POW:
        return b.pow(
            _expr_to_dialect(b, e.children[0], var_map),
            _expr_to_dialect(b, e.children[1], var_map),
        )
    if e.op == Op.EXP:
        return b.exp(_expr_to_dialect(b, e.children[0], var_map))
    if e.op == Op.LOG:
        return b.log(_expr_to_dialect(b, e.children[0], var_map))
    if e.op == Op.ABS:
        return b.abs(_expr_to_dialect(b, e.children[0], var_map))
    if e.op == Op.NEG:
        return b.mul(b.constant(-1.0), _expr_to_dialect(b, e.children[0], var_map))
    return b.constant(0.0)


def classify_target(problem: NLProblem) -> LowerTarget:
    has_int = any(problem.meta.get("integer_vars", []))
    nonlinear = False
    for o in problem.objectives:
        if o.nonlinear is not None and not o.nonlinear.is_linear():
            nonlinear = True
    for c in problem.constraints:
        if c.nonlinear is not None and not c.nonlinear.is_linear():
            nonlinear = True
    if nonlinear:
        return LowerTarget.NLP
    if has_int:
        return LowerTarget.MILP
    return LowerTarget.LP


def lower_to_dialect(problem: NLProblem) -> Module:
    """NLProblem → opt dialect module."""
    b = Builder()
    b.module.name = problem.name
    b.module.target = classify_target(problem)
    b.module.meta = dict(problem.meta)
    var_map: Dict[int, Value] = {}
    for v in problem.variables:
        vv = b.var(v.name)
        var_map[v.index] = vv
        b.module.body.ops.append(
            Operation(
                "opt.var_bound",
                [],
                [vv],
                attrs={"lb": v.lb, "ub": v.ub},
            )
        )
    for o in problem.objectives:
        body = b.constant(o.constant)
        for t in o.linear:
            body = b.add(body, b.mul(b.constant(t.coeff), var_map[t.var_index]))
        if o.nonlinear is not None:
            body = b.add(body, _expr_to_dialect(b, o.nonlinear, var_map))
        sense = "min" if o.sense == Sense.MINIMIZE else "max"
        b.objective(sense, body, o.name)
    for c in problem.constraints:
        body = b.constant(0.0)
        for t in c.linear:
            body = b.add(body, b.mul(b.constant(t.coeff), var_map[t.var_index]))
        if c.nonlinear is not None:
            body = b.add(body, _expr_to_dialect(b, c.nonlinear, var_map))
        rhs = b.constant(c.constant)
        rel = {Rel.EQ: "eq", Rel.LE: "le", Rel.GE: "ge"}[c.rel]
        b.constraint(rel, body, rhs, c.name)
    return b.module


def dialect_to_solver_hint(module: Module) -> str:
    return {
        LowerTarget.LP: "highs",
        LowerTarget.MILP: "highs",
        LowerTarget.NLP: "scipy",
        LowerTarget.CP: "scipy",
    }[module.target]
