#!/usr/bin/env python3
"""L-meta-650: Monotone2 circuit of size <= 63 for PG(2,3) incidence.

Complete 16-way cube split on gate-0's input pair (a < b, a,b < 26):
cube k forbids every pair whose index is not k (mod 16). Four shards
(0-3) each run four cubes in parallel (cubes 4*shard .. 4*shard+3).

Prints a single RESULT: SAT|UNSAT|TIMEOUT|ERROR line.
A SAT witness is written to $OUT_DIR/gates.json.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from itertools import combinations
from multiprocessing import Process, Queue
from pathlib import Path

EDGES = [
    (0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25),
    (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24),
    (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24),
    (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22),
    (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20),
    (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24),
    (12, 14), (12, 15), (12, 17), (12, 23),
]
N = 26
NPOINTS = 13
SIZE = 63
N_CUBES = 16
CUBES_PER_SHARD = 4


def adj_masks():
    adj = [0] * N
    for u, v in EDGES:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return adj


def maximal_independent_sets(adj):
    def lines_missing(pmask):
        L = 0
        for ell in range(13, 26):
            if (adj[ell] & pmask) == 0:
                L |= 1 << ell
        return L

    def points_missing(lmask):
        P = 0
        for p in range(13):
            if (adj[p] & lmask) == 0:
                P |= 1 << p
        return P

    out = []
    for P in range(1 << 13):
        L = lines_missing(P)
        if points_missing(L) == P:
            out.append(P | L)
    return out


def eval_circuit(gates, output, xmask):
    w = [bool((xmask >> i) & 1) for i in range(N)]
    for op, a, b in gates:
        va = w[a] if a < len(w) else False
        vb = w[b] if b < len(w) else False
        w.append((va and vb) if op == "and" else (va or vb))
    return output < len(w) and w[output]


def failures(gates, output, edges, mis):
    bad = []
    for u, v in edges:
        m = (1 << u) | (1 << v)
        if not eval_circuit(gates, output, m):
            bad.append((m, True))
    for s in mis:
        if eval_circuit(gates, output, s):
            bad.append((s, False))
    return bad


def seed_tests(edges, mis):
    tests = [((1 << u) | (1 << v), True) for u, v in edges]
    mis_sorted = sorted(mis, key=lambda m: (m.bit_count(), m))
    seed = [mis_sorted[0], mis_sorted[-1]] + mis_sorted[1:-1: max(1, len(mis_sorted) // 40)]
    seen = {t[0] for t in tests}
    for m in seed:
        if m not in seen:
            tests.append((m, False))
            seen.add(m)
    return tests


def gate0_pairs():
    return [(a, b) for a in range(N) for b in range(a + 1, N)]


# -------------------- SAT --------------------

class Enc:
    def __init__(self):
        self.nvars = 0
        self.clauses = []

    def var(self):
        self.nvars += 1
        return self.nvars

    def add(self, *lits):
        self.clauses.append(list(lits))

    def exactly_one(self, vs):
        self.add(*vs)
        if len(vs) <= 1:
            return
        prev = vs[0]
        for i in range(1, len(vs) - 1):
            self.add(-vs[i], -prev)
            nxt = self.var()
            self.add(-prev, nxt)
            self.add(-vs[i], nxt)
            self.add(-nxt, prev, vs[i])
            prev = nxt
        self.add(-vs[-1], -prev)


def build_structure(enc, s, cube):
    ops = [enc.var() for _ in range(s)]
    left, right = [], []
    for i in range(s):
        nprev = N + i
        L = [enc.var() for _ in range(nprev)]
        R = [enc.var() for _ in range(nprev)]
        enc.exactly_one(L)
        enc.exactly_one(R)
        for a in range(nprev):
            for b in range(0, a + 1):
                enc.add(-L[a], -R[b])
        left.append(L)
        right.append(R)
    # complete partition: gate 0 pair residue class
    pairs = gate0_pairs()
    for idx, (a, b) in enumerate(pairs):
        if idx % N_CUBES != cube:
            enc.add(-left[0][a], -right[0][b])
    return ops, left, right


def add_test(enc, ops, left, right, s, xmask, want):
    gval = [enc.var() for _ in range(s)]

    def wire(w):
        if w < N:
            return bool((xmask >> w) & 1)
        return gval[w - N]

    def mux(sel, nprev):
        terms = []
        for j in range(nprev):
            w = wire(j)
            if w is False:
                continue
            if w is True:
                terms.append(sel[j])
            else:
                aux = enc.var()
                enc.add(-aux, sel[j])
                enc.add(-aux, w)
                enc.add(-sel[j], -w, aux)
                terms.append(aux)
        if not terms:
            return False
        if len(terms) == 1:
            return terms[0]
        r = enc.var()
        for t in terms:
            enc.add(-t, r)
        enc.add(-r, *terms)
        return r

    for i in range(s):
        nprev = N + i
        L = mux(left[i], nprev)
        R = mux(right[i], nprev)
        gv = gval[i]
        op = ops[i]
        if L is False or R is False:
            enc.add(op, -gv)
        elif L is True and R is True:
            enc.add(op, gv)
        elif L is True:
            enc.add(op, -R, gv)
            enc.add(op, -gv, R)
        elif R is True:
            enc.add(op, -L, gv)
            enc.add(op, -gv, L)
        else:
            enc.add(op, -L, -R, gv)
            enc.add(op, -gv, L)
            enc.add(op, -gv, R)
        if L is True or R is True:
            enc.add(-op, gv)
        elif L is False and R is False:
            enc.add(-op, -gv)
        elif L is False:
            enc.add(-op, -gv, R)
            enc.add(-op, -R, gv)
        elif R is False:
            enc.add(-op, -gv, L)
            enc.add(-op, -L, gv)
        else:
            enc.add(-op, -L, gv)
            enc.add(-op, -R, gv)
            enc.add(-op, -gv, L, R)
    enc.add(gval[-1] if want else -gval[-1])


def decode(model, ops, left, right, s):
    sset = set(l for l in model if l > 0)
    gates = []
    for i in range(s):
        op = "or" if ops[i] in sset else "and"
        a = next(j for j, v in enumerate(left[i]) if v in sset)
        b = next(j for j, v in enumerate(right[i]) if v in sset)
        gates.append((op, a, b))
    return gates


def make_solver(name, clauses):
    from pysat.solvers import Glucose42
    name = (name or "cadical153").lower().replace("-", "")
    tried = []
    if "195" in name:
        tried.append("Cadical195")
    if "153" in name or "cadical" in name:
        tried.append("Cadical153")
    tried += ["Cadical195", "Cadical153", "Cadical", "Glucose42"]
    seen = set()
    last = None
    for cls_name in tried:
        if cls_name in seen:
            continue
        seen.add(cls_name)
        try:
            mod = __import__("pysat.solvers", fromlist=[cls_name])
            cls = getattr(mod, cls_name)
            return cls(bootstrap_with=clauses)
        except Exception as e:
            last = e
            continue
    return Glucose42(bootstrap_with=clauses)


def cegar_cube(cube, solver_name, edges, mis, tests0, deadline, log):
    """Return ('sat', gates) | ('unsat', None) | ('timeout', None)."""
    tests = list(tests0)
    have = set(tests)
    round_no = 0
    while True:
        if time.time() >= deadline:
            log(f"cube {cube}: timeout before encode")
            return "timeout", None
        round_no += 1
        enc = Enc()
        ops, left, right = build_structure(enc, SIZE, cube)
        for xmask, want in tests:
            add_test(enc, ops, left, right, SIZE, xmask, want)
        log(f"cube {cube} round {round_no}: {len(tests)} tests, vars={enc.nvars} clauses={len(enc.clauses)}")
        slv = make_solver(solver_name, enc.clauses)
        # Cadical has no portable time limit; the job wrapper enforces timeout.
        # We still abort between rounds if the deadline passed.
        sat = slv.solve()
        if time.time() >= deadline:
            slv.delete()
            log(f"cube {cube}: timeout after solve")
            return "timeout", None
        if sat is not True:
            slv.delete()
            log(f"cube {cube}: UNSAT at round {round_no}" if sat is False else f"cube {cube}: UNKNOWN")
            return ("unsat" if sat is False else "timeout"), None
        gates = decode(slv.get_model(), ops, left, right, SIZE)
        slv.delete()
        out = N + len(gates) - 1
        bad = failures(gates, out, edges, mis)
        if not bad:
            log(f"cube {cube}: SAT verified")
            return "sat", gates
        added = 0
        for m, want in bad:
            if (m, want) not in have:
                tests.append((m, want))
                have.add((m, want))
                added += 1
                if added >= 30:
                    break
        log(f"cube {cube}: candidate failed {len(bad)}; added {added}")
        if added == 0:
            return "timeout", gates


def cube_worker(cube, solver_name, edges, mis, tests0, deadline, q: Queue):
    def log(msg):
        print(msg, flush=True)
        q.put(("log", cube, msg))

    try:
        status, gates = cegar_cube(cube, solver_name, edges, mis, tests0, deadline, log)
        q.put(("done", cube, status, gates))
    except Exception as e:
        q.put(("done", cube, "error", None))
        print(f"cube {cube}: ERROR {type(e).__name__}: {e}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--shard", type=int, default=None)
    ap.add_argument("--solver", default=None)
    ap.add_argument("--timeout-sec", type=int, default=0,
                    help="soft deadline in seconds (leave a few minutes for cleanup)")
    ap.add_argument("shard_pos", nargs="?", default=None)
    args = ap.parse_args()

    shard = args.shard
    if shard is None:
        env = os.environ.get("SHARD")
        if env not in (None, ""):
            shard = int(env)
        elif args.shard_pos is not None:
            shard = int(args.shard_pos)
        else:
            shard = 0
    solver = args.solver or os.environ.get("SOLVER") or "cadical153"
    out_dir = Path(os.environ.get("OUT_DIR") or ".").resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    tmo = args.timeout_sec
    if tmo <= 0:
        # workflow timeout is in minutes; leave 3 min for flush if TIMEOUT env set
        env_t = os.environ.get("TIMEOUT") or os.environ.get("TIMEOUT_MIN")
        if env_t:
            try:
                tmo = max(60, int(env_t) * 60 - 180)
            except ValueError:
                tmo = 0
    deadline = time.time() + tmo if tmo > 0 else time.time() + 7 * 24 * 3600

    if not (0 <= shard < N_CUBES // CUBES_PER_SHARD):
        print(f"RESULT: ERROR", flush=True)
        print(f"bad shard {shard}", flush=True)
        return 2

    cubes = [CUBES_PER_SHARD * shard + i for i in range(CUBES_PER_SHARD)]
    print(f"shard={shard} cubes={cubes} solver={solver} out={out_dir}", flush=True)

    adj = adj_masks()
    mis = maximal_independent_sets(adj)
    tests0 = seed_tests(EDGES, mis)
    print(f"edges={len(EDGES)} MIS={len(mis)} seed_tests={len(tests0)} pairs={len(gate0_pairs())}",
          flush=True)

    q: Queue = Queue()
    procs = []
    for c in cubes:
        p = Process(target=cube_worker, args=(c, solver, EDGES, mis, tests0, deadline, q),
                    name=f"cube-{c}")
        p.start()
        procs.append(p)

    results = {}
    sat_gates = None
    sat_cube = None
    while len(results) < len(cubes):
        try:
            item = q.get(timeout=5)
        except Exception:
            if time.time() >= deadline:
                break
            # reap finished processes that failed to report
            if all(not p.is_alive() for p in procs) and q.empty():
                break
            continue
        kind = item[0]
        if kind == "log":
            continue
        _, cube, status, gates = item
        results[cube] = status
        print(f"cube {cube} finished: {status}", flush=True)
        if status == "sat" and gates is not None:
            sat_gates = gates
            sat_cube = cube
            for p in procs:
                if p.is_alive():
                    p.terminate()
            break

    for p in procs:
        p.join(timeout=10)
        if p.is_alive():
            p.terminate()

    if sat_gates is not None:
        payload = {
            "gates": sat_gates,
            "output": N + len(sat_gates) - 1,
            "size": len(sat_gates),
            "cube": sat_cube,
            "shard": shard,
        }
        (out_dir / "gates.json").write_text(json.dumps(payload, indent=1))
        (out_dir / "model.txt").write_text(json.dumps(payload))
        print("RESULT: SAT", flush=True)
        return 0

    statuses = [results.get(c, "timeout") for c in cubes]
    if all(st == "unsat" for st in statuses) and len(results) == len(cubes):
        (out_dir / "unsat.txt").write_text("cubes " + ",".join(map(str, cubes)) + " UNSAT\n")
        print("RESULT: UNSAT", flush=True)
        return 0
    if any(st == "error" for st in statuses):
        print("RESULT: ERROR", flush=True)
        return 1
    print("RESULT: TIMEOUT", flush=True)
    (out_dir / "timeout.txt").write_text("results=" + json.dumps(results) + "\n")
    return 124


if __name__ == "__main__":
    sys.exit(main())
