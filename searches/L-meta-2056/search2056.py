#!/usr/bin/env python3
"""Exact-synthesis / CEGAR search for L-meta-2056: a Monotone2 circuit of size <= K
on 26 inputs meeting the PG(2,3) incidence-pair and |S|<=3 off-set constraints.
"""
from __future__ import annotations

import argparse
import itertools
import os
import sys
import time
from collections import defaultdict

from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical153

D = (0, 1, 3, 9)
N = 13
M = 26  # inputs


def near(p: int, l: int) -> bool:
    return ((p + l) % N) in D


def points_on_line(l: int) -> list[int]:
    return [(d - l) % N for d in D]


def off(S: frozenset[int]) -> frozenset[int]:
    return frozenset(l for l in range(N) if all(not near(p, l) for p in S))


def vec(s: frozenset[int], t: frozenset[int]) -> tuple[bool, ...]:
    bits = []
    for i in range(M):
        if i < N:
            bits.append(i in s)
        else:
            bits.append((i % N) in t)
    return tuple(bits)


def all_constraints() -> list[tuple[tuple[bool, ...], bool]]:
    cons = []
    # true on incident pairs
    for p, l in itertools.product(range(N), repeat=2):
        if near(p, l):
            cons.append((vec(frozenset([p]), frozenset([l])), True))
    # false on (S, off(S)) and (off(S), S) for |S|<=3
    for r in range(0, 4):
        for S in itertools.combinations(range(N), r):
            fs = frozenset(S)
            o = off(fs)
            cons.append((vec(fs, o), False))
            cons.append((vec(o, fs), False))
    # dedup (same vector might appear twice)
    seen = {}
    out = []
    for x, y in cons:
        if x in seen:
            if seen[x] != y:
                raise RuntimeError("contradictory constraints")
            continue
        seen[x] = y
        out.append((x, y))
    return out


def eval_circuit(gates: list[tuple[str, list[int]]], output: int, x: tuple[bool, ...]) -> bool:
    w = list(x)
    for op, ins in gates:
        vals = [w[i] if i < len(w) else False for i in ins]
        if op == "and":
            w.append(all(vals) if vals else True)
        elif op == "or":
            w.append(any(vals) if vals else False)
        else:
            raise ValueError(op)
    return w[output] if output < len(w) else False


def build_64() -> tuple[list[tuple[str, list[int]]], int]:
    """OR_l (y_l AND OR_{p on line l} x_p). Expected size 64."""
    gates: list[tuple[str, list[int]]] = []

    def add(op, *ins):
        gates.append((op, list(ins)))
        return M + len(gates) - 1

    line_ands = []
    for l in range(N):
        pts = points_on_line(l)
        a, b, c, d = pts  # four point wires
        o1 = add("or", a, b)
        o2 = add("or", o1, c)
        o3 = add("or", o2, d)
        yl = N + l
        line_ands.append(add("and", yl, o3))
    acc = line_ands[0]
    for t in line_ands[1:]:
        acc = add("or", acc, t)
    return gates, acc


def check_circuit(gates, output, cons) -> list[tuple[tuple[bool, ...], bool, bool]]:
    bad = []
    for x, y in cons:
        got = eval_circuit(gates, output, x)
        if got != y:
            bad.append((x, y, got))
    return bad


# ----- SAT exact synthesis -----
def synthesize(k: int, cons, timeout=None, assume_first=None):
    """Search a Monotone2 circuit with exactly k gates, output = last wire.
    assume_first: optional (op, a, b) for gate 0, op in {'and','or'}.
    Compact encoding: O(k * nprev * ncons) clauses via per-slot values.
    """
    vpool = IDPool()
    cnf = CNF()

    def var(*key):
        return vpool.id(key)

    for g in range(k):
        nprev = M + g
        for slot in (0, 1):
            sels = [var("sel", g, slot, i) for i in range(nprev)]
            cnf.append(sels)
            for a, b in itertools.combinations(sels, 2):
                cnf.append([-a, -b])

    if assume_first is not None:
        op, a, b = assume_first
        cnf.append([var("and", 0)] if op == "and" else [-var("and", 0)])
        if not (0 <= a < M and 0 <= b < M):
            raise ValueError("bad first-gate wires")
        cnf.append([var("sel", 0, 0, a)])
        cnf.append([var("sel", 0, 1, b)])

    def val(t, w):
        return var("val", t, w)

    for t, (x, y) in enumerate(cons):
        for i in range(M):
            cnf.append([val(t, i)] if x[i] else [-val(t, i)])
        for g in range(k):
            w = M + g
            nprev = M + g
            is_and = var("and", g)
            s0v = var("slot", t, g, 0)
            s1v = var("slot", t, g, 1)
            vw = val(t, w)
            for slot, sv in ((0, s0v), (1, s1v)):
                for i in range(nprev):
                    sel = var("sel", g, slot, i)
                    vi = val(t, i)
                    # sel -> (sv <-> vi)
                    cnf.append([-sel, -sv, vi])
                    cnf.append([-sel, -vi, sv])
            # AND: vw <=> s0v & s1v
            cnf.append([-is_and, -vw, s0v])
            cnf.append([-is_and, -vw, s1v])
            cnf.append([-is_and, -s0v, -s1v, vw])
            # OR: vw <=> s0v | s1v
            cnf.append([is_and, -s0v, vw])
            cnf.append([is_and, -s1v, vw])
            cnf.append([is_and, -vw, s0v, s1v])
        out = val(t, M + k - 1)
        cnf.append([out] if y else [-out])
    print(f"cnf clauses={len(cnf.clauses)} vars={vpool.top}", flush=True)

    solver = Cadical153(bootstrap_with=cnf, use_timer=True)
    # pysat timeout: we'll just solve; caller can wrap
    sat = solver.solve()
    if not sat:
        solver.delete()
        return None
    model = set(solver.get_model())
    solver.delete()

    gates = []
    for g in range(k):
        op = "and" if var("and", g) in model else "or"
        ins = []
        nprev = M + g
        for slot in (0, 1):
            picked = [i for i in range(nprev) if var("sel", g, slot, i) in model]
            if len(picked) != 1:
                raise RuntimeError(f"gate {g} slot {slot} picks {picked}")
            ins.append(picked[0])
        gates.append((op, ins))
    return gates, M + k - 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--k", type=int, default=63)
    ap.add_argument("--verify64", action="store_true")
    ap.add_argument("--first-op", choices=["and", "or"])
    ap.add_argument("--first-a", type=int)
    ap.add_argument("--first-b", type=int)
    ap.add_argument("--shard", type=int, default=int(os.environ.get("SHARD", "0") or 0))
    args = ap.parse_args()
    t0 = time.time()
    cons = all_constraints()
    print(f"constraints={len(cons)} unique", flush=True)
    # counts
    ntrue = sum(1 for _, y in cons if y)
    print(f"true={ntrue} false={len(cons)-ntrue}", flush=True)

    g64, o64 = build_64()
    print(f"64-circuit size={len(g64)} output={o64}", flush=True)
    bad = check_circuit(g64, o64, cons)
    print(f"64-circuit violations={len(bad)}", flush=True)
    if bad:
        print("64 FAILED", bad[:3], flush=True)
        if args.verify64:
            sys.exit(1)
    else:
        print("64 OK", flush=True)
        if args.verify64 and args.k == 64:
            print("RESULT: SAT (constructive 64)", flush=True)
            return

    assume = None
    if args.first_op is not None:
        assume = (args.first_op, args.first_a, args.first_b)
        print(f"assuming first gate {assume}", flush=True)

    print(f"synthesizing k={args.k} ...", flush=True)
    res = synthesize(args.k, cons, assume_first=assume)
    dt = time.time() - t0
    if res is None:
        print(f"RESULT: UNSAT k={args.k} time={dt:.1f}s", flush=True)
        sys.exit(2)
    gates, out = res
    bad = check_circuit(gates, out, cons)
    print(f"model size={len(gates)} output={out} violations={len(bad)} time={dt:.1f}s", flush=True)
    print("GATES", gates, flush=True)
    print("OUTPUT", out, flush=True)
    if bad:
        print("RESULT: ERROR model failed residual checks", flush=True)
        sys.exit(3)
    print("RESULT: SAT", flush=True)


if __name__ == "__main__":
    main()
