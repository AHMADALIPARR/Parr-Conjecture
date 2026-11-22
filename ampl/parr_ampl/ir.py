"""Parr-AMPL intermediate representation.

Mirrors the AMPL .nl / ASL abstract problem:
  - variables with bounds
  - objectives (min/max) with linear + nonlinear parts
  - constraints with linear terms and nonlinear expression trees
  - expression DAG (sums, products, powers, exp, log, abs, sin, ...)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, List, Optional, Sequence, Union


class Sense(Enum):
    MINIMIZE = auto()
    MAXIMIZE = auto()


class Rel(Enum):
    EQ = auto()
    LE = auto()
    GE = auto()


class Op(Enum):
    """Expression-tree operators (ASL-compatible subset)."""
    CONST = auto()
    VAR = auto()
    ADD = auto()
    SUB = auto()
    MUL = auto()
    DIV = auto()
    POW = auto()
    NEG = auto()
    ABS = auto()
    EXP = auto()
    LOG = auto()
    SIN = auto()
    COS = auto()
    SUM = auto()  # n-ary sum


@dataclass
class Expr:
    """Nonlinear expression tree node."""
    op: Op
    children: List["Expr"] = field(default_factory=list)
    value: Optional[float] = None      # CONST
    var_index: Optional[int] = None    # VAR

    def is_const(self) -> bool:
        return self.op == Op.CONST

    def is_var(self) -> bool:
        return self.op == Op.VAR

    def is_linear(self) -> bool:
        if self.op in (Op.CONST, Op.VAR):
            return True
        if self.op == Op.NEG and self.children:
            return self.children[0].is_linear()
        if self.op in (Op.ADD, Op.SUB, Op.SUM):
            return all(c.is_linear() for c in self.children)
        if self.op == Op.MUL:
            # a*b linear if one side constant
            if len(self.children) == 2:
                a, b = self.children
                return (a.is_const() and b.is_linear()) or (b.is_const() and a.is_linear())
        return False


def C(x: float) -> Expr:
    return Expr(Op.CONST, value=float(x))


def V(i: int) -> Expr:
    return Expr(Op.VAR, var_index=i)


def add(*args: Expr) -> Expr:
    return Expr(Op.SUM if len(args) > 2 else Op.ADD, children=list(args))


def sub(a: Expr, b: Expr) -> Expr:
    return Expr(Op.SUB, children=[a, b])


def mul(a: Expr, b: Expr) -> Expr:
    return Expr(Op.MUL, children=[a, b])


def div(a: Expr, b: Expr) -> Expr:
    return Expr(Op.DIV, children=[a, b])


def pow_(a: Expr, b: Expr) -> Expr:
    return Expr(Op.POW, children=[a, b])


def neg(a: Expr) -> Expr:
    return Expr(Op.NEG, children=[a])


def abs_(a: Expr) -> Expr:
    return Expr(Op.ABS, children=[a])


def exp_(a: Expr) -> Expr:
    return Expr(Op.EXP, children=[a])


def log_(a: Expr) -> Expr:
    return Expr(Op.LOG, children=[a])


@dataclass
class Variable:
    name: str
    index: int
    lb: float = float("-inf")
    ub: float = float("+inf")
    init: Optional[float] = None


@dataclass
class LinearTerm:
    """Coefficient of a variable in a linear form."""
    var_index: int
    coeff: float


@dataclass
class Objective:
    name: str
    sense: Sense
    linear: List[LinearTerm] = field(default_factory=list)
    nonlinear: Optional[Expr] = None
    constant: float = 0.0


@dataclass
class Constraint:
    name: str
    rel: Rel
    linear: List[LinearTerm] = field(default_factory=list)
    nonlinear: Optional[Expr] = None
    constant: float = 0.0   # rhs: body  rel  constant   (body = linear + nonlinear)
    lb: float = float("-inf")  # for range constraints
    ub: float = float("+inf")


@dataclass
class NLProblem:
    """AMPL .nl-level problem (ASL abstract model)."""
    name: str
    variables: List[Variable] = field(default_factory=list)
    objectives: List[Objective] = field(default_factory=list)
    constraints: List[Constraint] = field(default_factory=list)
    params: Dict[str, float] = field(default_factory=dict)
    meta: Dict[str, Any] = field(default_factory=dict)

    @property
    def n_var(self) -> int:
        return len(self.variables)

    @property
    def n_con(self) -> int:
        return len(self.constraints)

    @property
    def n_obj(self) -> int:
        return len(self.objectives)

    def var_by_name(self, name: str) -> Variable:
        for v in self.variables:
            if v.name == name:
                return v
        raise KeyError(name)
