#!/usr/bin/env python3
"""L-meta-1342, desk shard FIRSTJ=13 (lowest junk AND at gate 13).

Search for a Monotone2 circuit of size <= 21 computing the edge function of
the 11-vertex C4-free graph with 16 edges (cover 7). A junk AND is an AND
gate that is true on some maximal independent set (hence not below f).
Shard 13 of 19: gate 13 is the lowest junk AND, and a second junk AND sits
above it. Cubes partition the position j of that second-lowest junk AND
(j in 14..20). GHA shard s in 0..3 runs the cubes with (j-14) % 4 == s,
four processes per job.

Any SAT model is re-evaluated on all 2048 inputs. Prints RESULT: SAT / UNSAT / UNKNOWN.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from multiprocessing import Process, Queue

from pysat.card import CardEnc
from pysat.solvers import Solver

E = [
    (0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
    (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9),
]
N, G, FIRSTJ = 11, 21, 13
SECOND_JS = list(range(FIRSTJ + 1, G))  # 14..20


def f(m: int) -> bool:
    return any((m >> u) & 1 and (m >> v) & 1 for u, v in E)


def rows_and_mis():
    ind = [m for m in range(1 << N) if not f(m)]
    indset = set(ind)
    maxind = [
        m for m in ind
        if all((m >> i) & 1 or (m | (1 << i)) not in indset for i in range(N))
    ]
    rows = [((1 << u) | (1 << v), True) for u, v in E] + [(m, False) for m in maxind]
    return rows, maxind


def build():
    rows, maxind = rows_and_mis()
    assert len(maxind) == 24
    mis_rows = [r for r, (_, want) in enumerate(rows) if not want]
    cnt = [0]

    def nv():
        cnt[0] += 1
        return cnt[0]

    cl = []
    # t[i] true = AND, false = OR
    t = [nv() for _ in range(G)]
    sa, sb = {}, {}
    for i in range(G):
        for j in range(N + i):
            sa[i, j] = nv()
            sb[i, j] = nv()
    val = {}
    for r in range(len(rows)):
        for i in range(G):
            val[N + i, r] = nv()
    for i in range(G):
        w = N + i
        for lits in ([sa[i, j] for j in range(w)], [sb[i, j] for j in range(w)]):
            enc = CardEnc.equals(lits=lits, bound=1, top_id=cnt[0], encoding=1)
            cnt[0] = max(cnt[0], enc.nv)
            cl.extend(enc.clauses)
        # a <= b (copies a==b allowed, so size < 21 can pad)
        for j in range(w):
            for k in range(j):
                cl.append([-sa[i, j], -sb[i, k]])

    def lit(j, r):
        if j < N:
            return bool((rows[r][0] >> j) & 1)
        return val[j, r]

    for r in range(len(rows)):
        for i in range(G):
            w = N + i
            v = val[N + i, r]
            a, b = nv(), nv()
            T = t[i]
            for j in range(w):
                L = lit(j, r)
                for sel, y in ((sa[i, j], a), (sb[i, j], b)):
                    if L is True:
                        cl.append([-sel, y])
                    elif L is False:
                        cl.append([-sel, -y])
                    else:
                        cl.append([-sel, -L, y])
                        cl.append([-sel, L, -y])
            # AND (~ wait: T true => AND): v <=> (T ? a&b : a|b)
            cl += [
                [-T, -a, -b, v], [-T, a, -v], [-T, b, -v],
                [T, -a, v], [T, -b, v], [T, a, b, -v],
            ]
        out = val[N + G - 1, r]
        cl.append([out] if rows[r][1] else [-out])

    # every non-output gate is read later; every input is read
    for i in range(G - 1):
        w = N + i
        cl.append([sa[k, w] for k in range(i + 1, G)] + [sb[k, w] for k in range(i + 1, G)])
    for j in range(N):
        cl.append([sa[k, j] for k in range(G)] + [sb[k, j] for k in range(G)])

    # junk_i <=> t[i] AND (OR_r val[n+i, r] for MIS rows)
    junk = []
    for i in range(G):
        orv = nv()
        # orv <=> OR of val on MIS rows
        for r in mis_rows:
            cl.append([-val[N + i, r], orv])
        cl.append([-orv] + [val[N + i, r] for r in mis_rows])
        ji = nv()
        junk.append(ji)
        # ji <=> t[i] & orv
        cl += [[-ji, t[i]], [-ji, orv], [ji, -t[i], -orv]]

    return cl, t, sa, sb, junk, rows, maxind


def check(circ):
    for m in range(1 << N):
        w = [bool((m >> j) & 1) for j in range(N)]
        for op, a, b in circ:
            va = w[a] if a < len(w) else False
            vb = w[b] if b < len(w) else False
            w.append((va and vb) if op == "and" else (va or vb))
        if w[-1] != f(m):
            return False
    return True


def decode(model, sa, sb, t):
    M = set(l for l in model if l > 0)
    circ = []
    for i in range(G):
        a = next(j for j in range(N + i) if sa[i, j] in M)
        b = next(j for j in range(N + i) if sb[i, j] in M)
        circ.append(("and" if t[i] in M else "or", a, b))
    return circ


def make_solver(name, clauses):
    name = (name or "cadical153").lower()
    for cand in (name, "cadical153", "cadical195", "glucose42"):
        try:
            return Solver(name=cand, bootstrap_with=clauses)
        except Exception:
            continue
    return Solver(bootstrap_with=clauses)


def solve_cube(j, solver_name):
    """Lowest junk AND at 13, second-lowest at j (no junk in (13, j))."""
    cl, t, sa, sb, junk, rows, maxind = build()
    # FIRSTJ=13 is junk; gates 0..12 not junk; j is junk; 14..j-1 not junk
    cl.append([junk[FIRSTJ]])
    for i in range(FIRSTJ):
        cl.append([-junk[i]])
    cl.append([junk[j]])
    for i in range(FIRSTJ + 1, j):
        cl.append([-junk[i]])
    t0 = time.time()
    with make_solver(solver_name, cl) as s:
        res = s.solve()
        circ = None
        if res:
            circ = decode(s.get_model(), sa, sb, t)
    return j, bool(res), round(time.time() - t0, 1), circ


def worker(j, solver_name, q: Queue):
    try:
        q.put(("done",) + solve_cube(j, solver_name))
    except Exception as e:
        print(f"cube j={j} ERROR {type(e).__name__}: {e}", flush=True)
        q.put(("done", j, "error", 0.0, None))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--shard", type=int, default=None)
    ap.add_argument("--solver", default=None)
    ap.add_argument("shard_pos", nargs="?", default=None)
    args = ap.parse_args()
    shard = args.shard
    if shard is None:
        env = os.environ.get("SHARD")
        shard = int(env) if env not in (None, "") else int(args.shard_pos or 0)
    solver = args.solver or os.environ.get("SOLVER") or "cadical153"
    outd = os.environ.get("OUT_DIR", ".")
    os.makedirs(outd, exist_ok=True)

    cubes = [j for i, j in enumerate(SECOND_JS) if i % 4 == shard]
    print(f"FIRSTJ={FIRSTJ} shard={shard} second_junk_cubes={cubes} solver={solver}", flush=True)
    if not cubes:
        print("RESULT: UNSAT", flush=True)
        return 0

    q: Queue = Queue()
    procs = [Process(target=worker, args=(j, solver, q), name=f"j{j}") for j in cubes]
    for p in procs:
        p.start()

    results = {}
    sat_circ = None
    sat_j = None
    while len(results) < len(cubes):
        try:
            item = q.get(timeout=5)
        except Exception:
            if all(not p.is_alive() for p in procs) and q.empty():
                break
            continue
        if item[0] != "done":
            continue
        _, j, res, sec, circ = item
        results[j] = res
        print(f"cube j={j} res={res} sec={sec}", flush=True)
        if res is True and circ is not None:
            ok = check(circ)
            print(f"witness check on all 2048 inputs: {ok}", flush=True)
            with open(os.path.join(outd, "model.txt"), "a") as fo:
                fo.write(json.dumps({"second_junk": j, "firstj": FIRSTJ, "circuit": circ, "verified": ok}) + "\n")
            if ok:
                sat_circ, sat_j = circ, j
                for p in procs:
                    if p.is_alive():
                        p.terminate()
                break

    for p in procs:
        p.join(timeout=10)
        if p.is_alive():
            p.terminate()

    if sat_circ is not None:
        with open(os.path.join(outd, "gates.json"), "w") as fo:
            json.dump({"firstj": FIRSTJ, "second_junk": sat_j, "gates": sat_circ, "output": N + len(sat_circ) - 1}, fo, indent=1)
        print("RESULT: SAT", flush=True)
        return 0
    statuses = [results.get(j) for j in cubes]
    if all(s is False for s in statuses) and len(results) == len(cubes):
        print("RESULT: UNSAT", flush=True)
        return 0
    if any(s == "error" for s in statuses):
        print("RESULT: ERROR", flush=True)
        return 1
    print("RESULT: UNKNOWN", flush=True)
    return 2


if __name__ == "__main__":
    sys.exit(main())
