#!/usr/bin/env python3
"""Parr-AMPL driver: .mod + .dat → translate → .nl → solve.

Usage:
  python -m parr_ampl.driver ampl/models/i4_scale.mod ampl/models/i4_scale.dat --solver scipy
  python -m parr_ampl.driver ampl/models/free_energy.mod ampl/models/free_energy.dat --solver scipy --nl out.nl
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

# Allow running from repo root without install
_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from parr_ampl.translator import translate
from parr_ampl.nl_writer import write_nl
from parr_ampl.solvers import solve, SOLVERS


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Parr-AMPL MP driver")
    p.add_argument("mod", type=Path, help="AMPL .mod file")
    p.add_argument("dat", type=Path, nargs="?", help="AMPL .dat file")
    p.add_argument("--solver", default="scipy", choices=sorted(SOLVERS.keys()))
    p.add_argument("--nl", type=Path, help="Write .nl intermediate to this path")
    p.add_argument("--json", action="store_true", help="Print SolveResult as JSON")
    args = p.parse_args(argv)

    problem = translate(args.mod, args.dat)
    print(f"[translate] {problem.name}: n_var={problem.n_var} n_con={problem.n_con} n_obj={problem.n_obj}")
    if problem.meta.get("certified"):
        print("[certified]", ", ".join(problem.meta["certified"]))

    if args.nl:
        path = write_nl(problem, args.nl)
        print(f"[nl] wrote {path}")

    result = solve(problem, solver=args.solver)
    if args.json:
        print(json.dumps({
            "status": result.status,
            "obj_value": result.obj_value,
            "x": result.x,
            "message": result.message,
            "solver": result.solver,
        }, indent=2))
    else:
        print(f"[solve] solver={result.solver} status={result.status}")
        print(f"[solve] obj={result.obj_value}")
        for k, v in result.x.items():
            print(f"  {k} = {v}")
        if result.message:
            print(f"[solve] msg: {result.message}")
    return 0 if result.status == "ok" else 1


if __name__ == "__main__":
    raise SystemExit(main())
