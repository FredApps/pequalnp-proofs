#!/usr/bin/env python3
"""CEGAR exact synthesis for L-meta-2056, size k (default 63).
Prints RESULT: SAT / RESULT: UNSAT. Writes a circuit to $OUT_DIR if set.
Optional --shard 0-5: first gate is AND/OR on a representative pair
[(0,1),(0,13),(0,15)] (same symmetry as R_meta_2056_773).
"""
from __future__ import annotations

import itertools
import os
import sys
import time
import argparse
from importlib.machinery import SourceFileLoader

from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical153

HERE = os.path.dirname(os.path.abspath(__file__))
m = SourceFileLoader("s2056", os.path.join(HERE, "search2056.py")).load_module()
# When offloaded, search2056.py should sit next to this file. Fix import if needed.
M = 26
REPS = [(0, 1), (0, 13), (0, 15)]  # (op_and_bit later)


class Syn:
    def __init__(self, k, assume_first=None):
        self.k = k
        self.vpool = IDPool()
        self.struct = CNF()
        self.assume_first = assume_first
        self._build_struct()
        self.examples = []  # (x_tuple, y)

    def var(self, *key):
        return self.vpool.id(key)

    def _build_struct(self):
        k = self.k
        for g in range(k):
            nprev = M + g
            for slot in (0, 1):
                sels = [self.var("sel", g, slot, i) for i in range(nprev)]
                self.struct.append(sels)
                for a, b in itertools.combinations(sels, 2):
                    self.struct.append([-a, -b])
        if self.assume_first is not None:
            op, a, b = self.assume_first
            self.struct.append([self.var("and", 0)] if op == "and" else [-self.var("and", 0)])
            self.struct.append([self.var("sel", 0, 0, a)])
            self.struct.append([self.var("sel", 0, 1, b)])

    def example_clauses(self, x, y, tid):
        clauses = []
        def val(w):
            return self.var("val", tid, w)
        for i in range(M):
            clauses.append([val(i)] if x[i] else [-val(i)])
        for g in range(self.k):
            w = M + g
            nprev = M + g
            is_and = self.var("and", g)
            s0v = self.var("slot", tid, g, 0)
            s1v = self.var("slot", tid, g, 1)
            vw = val(w)
            for slot, sv in ((0, s0v), (1, s1v)):
                for i in range(nprev):
                    sel = self.var("sel", g, slot, i)
                    vi = val(i)
                    clauses.append([-sel, -sv, vi])
                    clauses.append([-sel, -vi, sv])
            clauses.append([-is_and, -vw, s0v])
            clauses.append([-is_and, -vw, s1v])
            clauses.append([-is_and, -s0v, -s1v, vw])
            clauses.append([is_and, -s0v, vw])
            clauses.append([is_and, -s1v, vw])
            clauses.append([is_and, -vw, s0v, s1v])
        out = val(M + self.k - 1)
        clauses.append([out] if y else [-out])
        return clauses

    def decode(self, model):
        model = set(model)
        gates = []
        for g in range(self.k):
            op = "and" if self.var("and", g) in model else "or"
            ins = []
            nprev = M + g
            for slot in (0, 1):
                picked = [i for i in range(nprev) if self.var("sel", g, slot, i) in model]
                if len(picked) != 1:
                    raise RuntimeError(f"gate {g} slot {slot} = {picked}")
                ins.append(picked[0])
            gates.append((op, ins))
        return gates, M + self.k - 1

    def phases_from_circuit(self, gates, output, examples):
        """Return a list of literals for set_phases. output must be last wire."""
        lits = []
        if output != M + self.k - 1:
            # only phases for a suffix-aligned circuit
            pass
        for g, (op, ins) in enumerate(gates):
            if g >= self.k:
                break
            av = self.var("and", g)
            lits.append(av if op == "and" else -av)
            nprev = M + g
            for slot in (0, 1):
                want = ins[slot] if slot < len(ins) else ins[0]
                if not (0 <= want < nprev):
                    continue
                for i in range(nprev):
                    v = self.var("sel", g, slot, i)
                    lits.append(v if i == want else -v)
        # eval phases per example
        for tid, (x, y) in enumerate(examples):
            wvals = list(x)
            for op, ins in gates:
                a = wvals[ins[0]]
                b = wvals[ins[1]] if len(ins) > 1 else a
                bit = (a and b) if op == "and" else (a or b)
                wvals.append(bit)
            for w, bit in enumerate(wvals[: M + self.k]):
                v = self.var("val", tid, w)
                lits.append(v if bit else -v)
            for g in range(min(self.k, len(gates))):
                op, ins = gates[g]
                for slot in (0, 1):
                    want = ins[slot] if slot < len(ins) else ins[0]
                    if 0 <= want < len(wvals):
                        bit = wvals[want]
                        v = self.var("slot", tid, g, slot)
                        lits.append(v if bit else -v)
        return lits


def almost_circuit():
    """63-gate circuit with exactly 1 violation (delete line0.or1, replace with x0)."""
    # local compact_after_delete
    g0, o0 = m.build_64()
    gdel, repl = 0, 0
    dead = M + gdel
    def mapw(w):
        if w == dead:
            return repl
        if w > dead:
            return w - 1
        return w
    ng = []
    for gi, (op, ins) in enumerate(g0):
        if gi == gdel:
            continue
        ng.append((op, [mapw(i) for i in ins]))
    no = mapw(o0)
    return ng, no


def seed_constraints(cons):
    trues = [(x, y) for x, y in cons if y]
    falses = [(x, y) for x, y in cons if not y]
    # strongest falses first: large |S| or many bits
    def weight(item):
        x, y = item
        return (-sum(x),)
    falses.sort(key=weight)
    # all trues + first 80 "large" falses
    seeds = trues + falses[:80]
    return seeds, cons


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--k", type=int, default=63)
    ap.add_argument("--shard", type=int, default=int(os.environ.get("SHARD", "0") or 0))
    ap.add_argument("--no-shard", action="store_true")
    ap.add_argument("--max-cex", type=int, default=8)
    args = ap.parse_args()
    t0 = time.time()
    cons = m.all_constraints()
    assume = None
    if not args.no_shard:
        # shards 0-5 as described; shard ignored if --no-shard
        # If called with a single job, --no-shard is safer for existence.
        pass
    # default: no first-gate restriction unless SHARD set and --shard-first
    shard = args.shard
    # only apply symmetry restriction if env PNP_SHARD_FIRST=1
    if os.environ.get("PNP_SHARD_FIRST") == "1" or "--use-shard" in sys.argv:
        op = "and" if (shard % 2 == 0) else "or"
        a, b = REPS[shard // 2]
        assume = (op, a, b)
        print(f"shard={shard} assume first {assume}", flush=True)
    else:
        print(f"unsharded k={args.k}", flush=True)

    syn = Syn(args.k, assume_first=assume)
    seeds, allcons = seed_constraints(cons)
    solver = Cadical153(bootstrap_with=syn.struct, use_timer=True)
    added = {}
    tid = 0
    for x, y in seeds:
        if x in added:
            continue
        solver.append_formula(syn.example_clauses(x, y, tid))
        added[x] = (y, tid)
        tid += 1
    print(f"seeded={len(added)} struct={len(syn.struct.clauses)} t={time.time()-t0:.1f}s", flush=True)

    ag, ao = almost_circuit()
    # only use phases if sizes match and output is last wire
    if len(ag) == args.k and ao == M + args.k - 1:
        exs = [(x, y) for x, (y, i) in sorted(added.items(), key=lambda kv: kv[1][1])]
        # rebuild in tid order
        by_tid = [None] * len(added)
        for x, (y, i) in added.items():
            by_tid[i] = (x, y)
        phases = syn.phases_from_circuit(ag, ao, by_tid)
        solver.set_phases(phases)
        v_almost = len(m.check_circuit(ag, ao, cons))
        print(f"phased from almost-circuit viol={v_almost} nphase={len(phases)}", flush=True)
    else:
        print(f"almost-circuit size={len(ag)} out={ao} (no phases)", flush=True)

    niter = 0
    outdir = os.environ.get("OUT_DIR")
    while True:
        niter += 1
        print(f"iter {niter} solving examples={len(added)} t={time.time()-t0:.1f}s ...", flush=True)
        sat = solver.solve()
        if not sat:
            print(f"RESULT: UNSAT k={args.k} iters={niter} examples={len(added)} time={time.time()-t0:.1f}s", flush=True)
            solver.delete()
            sys.exit(2)
        gates, out = syn.decode(solver.get_model())
        bad = m.check_circuit(gates, out, allcons)
        print(f"  model viol={len(bad)} t={time.time()-t0:.1f}s", flush=True)
        if not bad:
            print("GATES", gates, flush=True)
            print("OUTPUT", out, flush=True)
            print(f"RESULT: SAT k={args.k} iters={niter} examples={len(added)} time={time.time()-t0:.1f}s", flush=True)
            if outdir:
                os.makedirs(outdir, exist_ok=True)
                path = os.path.join(outdir, "circuit.txt")
                with open(path, "w") as f:
                    f.write(repr((gates, out)) + "\n")
                print("wrote", path, flush=True)
            solver.delete()
            sys.exit(0)
        # add new cex
        nadd = 0
        for x, y, got in bad:
            if x in added:
                continue
            solver.append_formula(syn.example_clauses(x, y, tid))
            added[x] = (y, tid)
            tid += 1
            nadd += 1
            if nadd >= args.max_cex:
                break
        print(f"  added {nadd} cex (now {len(added)})", flush=True)


if __name__ == "__main__":
    main()
