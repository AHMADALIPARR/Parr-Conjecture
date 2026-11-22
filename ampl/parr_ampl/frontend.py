"""AMPL frontend: Lexer → Parser → Typed AST.

Covers the surface language used by Parr models (params, vars, bounds,
minimize/maximize, subject to, simple algebraic expressions).
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, Iterator, List, Optional, Tuple, Union


# ══════════════════════════════════════════════════════════════
# Lexer
# ══════════════════════════════════════════════════════════════

class TokKind(Enum):
    ID = auto()
    NUM = auto()
    STRING = auto()
    KW = auto()
    OP = auto()
    LBRACE = auto()
    RBRACE = auto()
    LBRACK = auto()
    RBRACK = auto()
    LPAREN = auto()
    RPAREN = auto()
    SEMI = auto()
    COLON = auto()
    COMMA = auto()
    DOTDOT = auto()
    EOF = auto()


KEYWORDS = {
    "param", "var", "minimize", "maximize", "subject", "to", "s.t.",
    "end", "data", "set", "default", "in", "binary", "integer",
    "abs", "exp", "log", "sin", "cos", "sum",
}


@dataclass
class Token:
    kind: TokKind
    text: str
    line: int
    col: int


def lex(src: str) -> List[Token]:
    tokens: List[Token] = []
    i, line, col = 0, 1, 1
    n = len(src)

    def advance(k: int = 1) -> None:
        nonlocal i, line, col
        for _ in range(k):
            if i < n and src[i] == "\n":
                line += 1
                col = 1
            else:
                col += 1
            i += 1

    while i < n:
        ch = src[i]
        # whitespace
        if ch.isspace():
            advance()
            continue
        # comments
        if ch == "#":
            while i < n and src[i] != "\n":
                advance()
            continue
        start_line, start_col = line, col
        # numbers
        if ch.isdigit() or (ch == "." and i + 1 < n and src[i + 1].isdigit()):
            j = i
            while j < n and (src[j].isdigit() or src[j] in ".eE+-"):
                j += 1
            text = src[i:j]
            tokens.append(Token(TokKind.NUM, text, start_line, start_col))
            advance(j - i)
            continue
        # identifiers / keywords
        if ch.isalpha() or ch == "_":
            j = i
            while j < n and (src[j].isalnum() or src[j] == "_"):
                j += 1
            text = src[i:j]
            # multi-word kw s.t.
            kind = TokKind.KW if text.lower() in KEYWORDS else TokKind.ID
            tokens.append(Token(kind, text, start_line, start_col))
            advance(j - i)
            continue
        # operators / punctuation
        two = src[i : i + 2]
        if two in ("..", "<=", ">=", "==", "**", ":="):
            tokens.append(Token(TokKind.OP, two, start_line, start_col))
            advance(2)
            continue
        if two == "s." and i + 3 < n and src[i : i + 4] == "s.t.":
            tokens.append(Token(TokKind.KW, "s.t.", start_line, start_col))
            advance(4)
            continue
        single = {
            "{": TokKind.LBRACE, "}": TokKind.RBRACE,
            "[": TokKind.LBRACK, "]": TokKind.RBRACK,
            "(": TokKind.LPAREN, ")": TokKind.RPAREN,
            ";": TokKind.SEMI, ":": TokKind.COLON, ",": TokKind.COMMA,
        }
        if ch in single:
            tokens.append(Token(single[ch], ch, start_line, start_col))
            advance()
            continue
        if ch in "+-*/^=<>!":
            tokens.append(Token(TokKind.OP, ch, start_line, start_col))
            advance()
            continue
        # skip unknown
        advance()
    tokens.append(Token(TokKind.EOF, "", line, col))
    return tokens


# ══════════════════════════════════════════════════════════════
# Typed AST
# ══════════════════════════════════════════════════════════════

class Ty(Enum):
    REAL = auto()
    INT = auto()
    BOOL = auto()
    SET = auto()
    UNKNOWN = auto()


@dataclass
class ASTNode:
    line: int = 0
    col: int = 0


@dataclass
class NumLit(ASTNode):
    value: float = 0.0
    ty: Ty = Ty.REAL


@dataclass
class NameRef(ASTNode):
    name: str = ""
    ty: Ty = Ty.UNKNOWN


@dataclass
class BinOp(ASTNode):
    op: str = "+"
    left: ASTNode = field(default_factory=ASTNode)
    right: ASTNode = field(default_factory=ASTNode)
    ty: Ty = Ty.REAL


@dataclass
class UnaryOp(ASTNode):
    op: str = "-"
    arg: ASTNode = field(default_factory=ASTNode)
    ty: Ty = Ty.REAL


@dataclass
class Call(ASTNode):
    func: str = ""
    args: List[ASTNode] = field(default_factory=list)
    ty: Ty = Ty.REAL


@dataclass
class IndexedRef(ASTNode):
    name: str = ""
    index: ASTNode = field(default_factory=ASTNode)
    ty: Ty = Ty.REAL


@dataclass
class SumExpr(ASTNode):
    index: str = ""
    lo: ASTNode = field(default_factory=ASTNode)
    hi: ASTNode = field(default_factory=ASTNode)
    body: ASTNode = field(default_factory=ASTNode)
    ty: Ty = Ty.REAL


@dataclass
class ParamDecl(ASTNode):
    name: str = ""
    default: Optional[float] = None
    indexed: bool = False
    ty: Ty = Ty.REAL


@dataclass
class VarDecl(ASTNode):
    name: str = ""
    lb: Optional[ASTNode] = None
    ub: Optional[ASTNode] = None
    binary: bool = False
    integer: bool = False
    ty: Ty = Ty.REAL


@dataclass
class ObjectiveDecl(ASTNode):
    sense: str = "minimize"  # minimize | maximize
    name: str = "obj"
    expr: ASTNode = field(default_factory=ASTNode)


@dataclass
class ConstraintDecl(ASTNode):
    name: str = ""
    left: ASTNode = field(default_factory=ASTNode)
    rel: str = "="  # = | <= | >=
    right: ASTNode = field(default_factory=ASTNode)


@dataclass
class ModelAST(ASTNode):
    params: List[ParamDecl] = field(default_factory=list)
    vars: List[VarDecl] = field(default_factory=list)
    objectives: List[ObjectiveDecl] = field(default_factory=list)
    constraints: List[ConstraintDecl] = field(default_factory=list)
    data: Dict[str, Any] = field(default_factory=dict)


# ══════════════════════════════════════════════════════════════
# Parser
# ══════════════════════════════════════════════════════════════

class ParseError(Exception):
    pass


class Parser:
    def __init__(self, tokens: List[Token]):
        self.toks = tokens
        self.i = 0

    def cur(self) -> Token:
        return self.toks[self.i]

    def advance(self) -> Token:
        t = self.cur()
        if t.kind != TokKind.EOF:
            self.i += 1
        return t

    def expect(self, *kinds: TokKind, text: Optional[str] = None) -> Token:
        t = self.cur()
        if t.kind not in kinds or (text is not None and t.text.lower() != text.lower()):
            raise ParseError(f"line {t.line}:{t.col}: expected {kinds} got {t.kind} '{t.text}'")
        return self.advance()

    def match_kw(self, *words: str) -> bool:
        t = self.cur()
        return t.kind == TokKind.KW and t.text.lower() in {w.lower() for w in words}

    def match_op(self, *ops: str) -> bool:
        t = self.cur()
        return t.kind == TokKind.OP and t.text in ops

    def parse_model(self) -> ModelAST:
        model = ModelAST()
        while self.cur().kind != TokKind.EOF:
            if self.match_kw("end"):
                self.advance()
                break
            if self.match_kw("data"):
                self.advance()
                if self.cur().kind == TokKind.SEMI:
                    self.advance()
                model.data.update(self.parse_data_section())
                continue
            if self.match_kw("param"):
                model.params.append(self.parse_param())
                continue
            if self.match_kw("var"):
                model.vars.append(self.parse_var())
                continue
            if self.match_kw("minimize", "maximize"):
                model.objectives.append(self.parse_objective())
                continue
            if self.match_kw("subject", "s.t."):
                model.constraints.append(self.parse_constraint())
                continue
            # skip stray tokens
            self.advance()
        return model

    def parse_param(self) -> ParamDecl:
        self.expect(TokKind.KW, text="param")
        name = self.expect(TokKind.ID).text
        default = None
        indexed = False
        if self.cur().kind == TokKind.LBRACE:
            indexed = True
            self.advance()
            # skip index set expression
            depth = 1
            while depth and self.cur().kind != TokKind.EOF:
                if self.cur().kind == TokKind.LBRACE:
                    depth += 1
                elif self.cur().kind == TokKind.RBRACE:
                    depth -= 1
                self.advance()
        if self.match_kw("default"):
            self.advance()
            default = float(self.expect(TokKind.NUM).text)
        if self.match_op(">", ">="):
            self.advance()
            if self.cur().kind == TokKind.NUM:
                self.advance()
        if self.cur().kind == TokKind.SEMI:
            self.advance()
        return ParamDecl(name=name, default=default, indexed=indexed)

    def parse_var(self) -> VarDecl:
        self.expect(TokKind.KW, text="var")
        name = self.expect(TokKind.ID).text
        lb = ub = None
        binary = integer = False
        while self.cur().kind != TokKind.SEMI and self.cur().kind != TokKind.EOF:
            if self.match_kw("binary"):
                binary = True
                self.advance()
            elif self.match_kw("integer"):
                integer = True
                self.advance()
            elif self.match_op(">="):
                self.advance()
                lb = self.parse_expr()
            elif self.match_op("<="):
                self.advance()
                ub = self.parse_expr()
            else:
                self.advance()
        if self.cur().kind == TokKind.SEMI:
            self.advance()
        return VarDecl(name=name, lb=lb, ub=ub, binary=binary, integer=integer)

    def parse_objective(self) -> ObjectiveDecl:
        sense = self.advance().text.lower()
        name = self.expect(TokKind.ID).text
        self.expect(TokKind.COLON)
        expr = self.parse_expr()
        if self.cur().kind == TokKind.SEMI:
            self.advance()
        return ObjectiveDecl(sense=sense, name=name, expr=expr)

    def parse_constraint(self) -> ConstraintDecl:
        if self.match_kw("subject"):
            self.advance()
            if self.match_kw("to"):
                self.advance()
        elif self.match_kw("s.t."):
            self.advance()
        name = "con"
        if self.cur().kind == TokKind.ID:
            name = self.advance().text
            if self.cur().kind == TokKind.COLON:
                self.advance()
        left = self.parse_expr()
        rel = "="
        if self.match_op("<=", ">=", "=", "=="):
            rel = self.advance().text
            if rel == "==":
                rel = "="
        right = self.parse_expr()
        if self.cur().kind == TokKind.SEMI:
            self.advance()
        return ConstraintDecl(name=name, left=left, rel=rel, right=right)

    def parse_data_section(self) -> Dict[str, Any]:
        data: Dict[str, Any] = {}
        while self.cur().kind != TokKind.EOF and not self.match_kw("end"):
            if self.match_kw("param"):
                self.advance()
                name = self.expect(TokKind.ID).text
                if self.match_op(":="):
                    self.advance()
                # scalar or pairs
                if self.cur().kind == TokKind.NUM and self._peek_is_semi_or_id_after_num():
                    # could be list of pairs
                    pairs = []
                    while self.cur().kind == TokKind.NUM:
                        a = float(self.advance().text)
                        if self.cur().kind == TokKind.NUM:
                            b = float(self.advance().text)
                            pairs.append((a, b))
                        else:
                            data[name] = a
                            pairs = None
                            break
                    if pairs is not None:
                        data[name] = {int(i): v for i, v in pairs}
                        data[name + "__n"] = len(pairs)
                if self.cur().kind == TokKind.SEMI:
                    self.advance()
            else:
                self.advance()
        return data

    def _peek_is_semi_or_id_after_num(self) -> bool:
        return True

    # Pratt-style expression parser
    def parse_expr(self, min_bp: int = 0) -> ASTNode:
        t = self.cur()
        if t.kind == TokKind.NUM:
            self.advance()
            left: ASTNode = NumLit(value=float(t.text), line=t.line, col=t.col)
        elif t.kind == TokKind.OP and t.text in ("+", "-"):
            self.advance()
            arg = self.parse_expr(100)
            left = UnaryOp(op=t.text, arg=arg, line=t.line, col=t.col)
        elif t.kind in (TokKind.ID, TokKind.KW) and t.text.lower() in (
            "abs", "exp", "log", "sin", "cos"
        ):
            fn = self.advance().text.lower()
            self.expect(TokKind.LPAREN)
            arg = self.parse_expr()
            self.expect(TokKind.RPAREN)
            left = Call(func=fn, args=[arg], line=t.line, col=t.col)
        elif self.match_kw("sum"):
            left = self.parse_sum()
        elif t.kind == TokKind.ID:
            name = self.advance().text
            if self.cur().kind == TokKind.LBRACK:
                self.advance()
                idx = self.parse_expr()
                self.expect(TokKind.RBRACK)
                left = IndexedRef(name=name, index=idx, line=t.line, col=t.col)
            else:
                left = NameRef(name=name, line=t.line, col=t.col)
        elif t.kind == TokKind.LPAREN:
            self.advance()
            left = self.parse_expr()
            self.expect(TokKind.RPAREN)
        else:
            # recovery
            self.advance()
            left = NumLit(value=0.0, line=t.line, col=t.col)

        while True:
            t = self.cur()
            if t.kind != TokKind.OP or t.text not in ("+", "-", "*", "/", "^", "**"):
                break
            op = t.text
            if op == "**":
                op = "^"
            lbp, rbp = self._bp(op)
            if lbp < min_bp:
                break
            self.advance()
            right = self.parse_expr(rbp)
            left = BinOp(op=op, left=left, right=right, line=t.line, col=t.col)
        return left

    def parse_sum(self) -> SumExpr:
        self.expect(TokKind.KW, text="sum")
        self.expect(TokKind.LBRACE)
        idx = self.expect(TokKind.ID).text
        if self.match_kw("in"):
            self.advance()
        lo: ASTNode = NumLit(value=1.0)
        hi: ASTNode = NumLit(value=1.0)
        # 1..n  or name
        if self.cur().kind == TokKind.NUM:
            lo = NumLit(value=float(self.advance().text))
            if self.match_op(".."):
                self.advance()
                hi = self.parse_expr()
        self.expect(TokKind.RBRACE)
        body = self.parse_expr(50)
        return SumExpr(index=idx, lo=lo, hi=hi, body=body)

    @staticmethod
    def _bp(op: str) -> Tuple[int, int]:
        if op in ("+", "-"):
            return 10, 11
        if op in ("*", "/"):
            return 20, 21
        if op == "^":
            return 30, 30  # right assoc
        return 0, 0


def parse_mod(text: str) -> ModelAST:
    return Parser(lex(text)).parse_model()


def parse_dat(text: str) -> Dict[str, Any]:
    """Standalone .dat parse into a dict."""
    # Reuse existing simple regex path for robustness on data files
    from .translator import parse_dat as _pd

    return _pd(text)


def parse_files(mod_path: str, dat_path: Optional[str] = None) -> ModelAST:
    from pathlib import Path

    model = parse_mod(Path(mod_path).read_text())
    if dat_path:
        model.data.update(parse_dat(Path(dat_path).read_text()))
    # apply defaults
    for p in model.params:
        if p.name not in model.data and p.default is not None:
            model.data[p.name] = p.default
    return model
