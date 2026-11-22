#!/usr/bin/env python3
"""Parr-AMPL driver — Python pipeline only (no MLIR).

  .mod/.dat → parse → translate → presolve → .nl → solve → diagnostics
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from parr_ampl.pipeline import run_pipeline
from parr_ampl.solvers import SOLVERS


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Parr-AMPL pipeline (Python IR, not MLIR)")
    p.add_argument("mod", type=Path)
    p.add_argument("dat", type=Path, nargs="?")
    p.add_argument("--solver", default="scipy", choices=sorted(SOLVERS.keys()))
    p.add_argument("--nl", type=Path, default=None)
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)

    result = run_pipeline(args.mod, args.dat, solver=args.solver, nl_out=args.nl)
    d = result.diagnostics

    if args.json:
        print(d.to_json())
    else:
        print(f"[pipeline] {' → '.join(d.stage)}")
        print(f"[frontend] params={d.ast_params} vars={d.ast_vars} cons={d.ast_constraints}")
        print(f"[presolve] {d.presolve}")
        print(f"[nl]       {d.nl_path}")
        if d.certified:
            print(f"[certified] {', '.join(d.certified)}")
        print(f"[solve]    solver={d.solver} status={d.status} obj={d.obj_value}")
        for k, v in d.x.items():
            print(f"  {k} = {v}")
        if d.message:
            print(f"[msg] {d.message}")
    return 0 if d.status == "ok" else 1


if __name__ == "__main__":
    raise SystemExit(main())
