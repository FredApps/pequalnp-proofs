# L-meta-651 range 2: Petersen edge function, circuits of AND/OR (fan-in 2) and NOT,
# exactly S gates (smaller ones pad), gate 0 fixed = OR(x0, x2) (0,2 non-adjacent; Petersen is
# distance-transitive so every non-adjacent pair is equivalent). Gates 1.. are AND/OR of two
# distinct earlier wires or NOT of one (constants/copies are removable, WLOG).
# Shard = (job shard 0..3) x (4 local processes) = 16 subproblems, split by gate 1's (op, first input).
# CEGAR over truth-table rows; UNSAT on a subset of rows => UNSAT on all.
import sys, os, random, time, json, itertools, argparse
from multiprocessing import Process, Queue
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

ap = argparse.ArgumentParser()
ap.add_argument('--shard', type=int, default=int(os.environ.get('SHARD', 0)))
ap.add_argument('--solver', default=os.environ.get('SOLVER', 'cadical153'))
ap.add_argument('--size', type=int, default=19)
ap.add_argument('--graph', default='petersen')
ap.add_argument('--nshards', type=int, default=4)
ap.add_argument('--procs', type=int, default=4)
ap.add_argument('--g0', default='or,0,2')
args = ap.parse_args()

if args.graph == 'petersen':
    n = 10
    E = [(i, (i+1) % 5) for i in range(5)] + [(i, i+5) for i in range(5)] + [(5+i, 5+(i+2) % 5) for i in range(5)]
elif args.graph == 'c5':
    n = 5; E = [(i, (i+1) % 5) for i in range(5)]
else:
    raise SystemExit('unknown graph')
R = 1 << n
F = [any((r >> u) & 1 and (r >> v) & 1 for u, v in E) for r in range(R)]
S = args.size
g0op, g0j, g0k = args.g0.split(','); g0j = int(g0j); g0k = int(g0k)
OPS = ('and', 'or', 'not')

def combos():
    W = n + 1
    cs = [(op, j) for op in ('and', 'or') for j in range(W - 1)] + [('not', j) for j in range(W)]
    return cs

def build_and_solve(sub, nsub, q):
    pool = IDPool()
    s = Solver(name=args.solver)
    T = pool.id('T'); s.add_clause([T])
    s1 = {}; s2 = {}; op = {}
    for i in range(S):
        W = n + i
        for j in range(W):
            s1[i, j] = pool.id(('s1', i, j)); s2[i, j] = pool.id(('s2', i, j))
        for o in OPS: op[i, o] = pool.id(('op', i, o))
        for cl in CardEnc.equals([s1[i, j] for j in range(W)], 1, vpool=pool, encoding=EncType.seqcounter).clauses: s.add_clause(cl)
        for cl in CardEnc.equals([s2[i, j] for j in range(W)], 1, vpool=pool, encoding=EncType.seqcounter).clauses: s.add_clause(cl)
        for cl in CardEnc.equals([op[i, o] for o in OPS], 1, vpool=pool, encoding=EncType.pairwise).clauses: s.add_clause(cl)
        for j in range(W):
            # NOT: s2 mirrors s1; AND/OR: first < second
            s.add_clause([-op[i, 'not'], -s1[i, j], s2[i, j]])
            for k in range(j + 1):
                s.add_clause([op[i, 'not'], -s1[i, j], -s2[i, k]])
    # gate 0 fixed
    s.add_clause([op[0, g0op]]); s.add_clause([s1[0, g0j]]); s.add_clause([s2[0, g0k]])
    # gate 1 restricted to this subproblem's combos
    if S > 1:
        mine = [c for idx, c in enumerate(combos()) if idx % nsub == sub]
        ts = []
        for (o, j) in mine:
            t = pool.id(('t', o, j)); ts.append(t)
            s.add_clause([-t, op[1, o]]); s.add_clause([-t, s1[1, j]])
        if not ts:
            q.put((sub, 'UNSAT', None)); return
        s.add_clause(ts)
    y = [pool.id(('y', i)) for i in range(S)]
    for cl in CardEnc.equals(y, 1, vpool=pool, encoding=EncType.seqcounter).clauses: s.add_clause(cl)

    def v(w, r):
        if w < n: return T if (r >> w) & 1 else -T
        return pool.id(('v', w - n, r))
    def add_row(r):
        for i in range(S):
            W = n + i
            a = pool.id(('a', i, r)); b = pool.id(('b', i, r)); g = v(n + i, r)
            for j in range(W):
                vj = v(j, r)
                s.add_clause([-s1[i, j], -a, vj]); s.add_clause([-s1[i, j], a, -vj])
                s.add_clause([-s2[i, j], -b, vj]); s.add_clause([-s2[i, j], b, -vj])
            A, O, N = op[i, 'and'], op[i, 'or'], op[i, 'not']
            s.add_clause([-A, -g, a]); s.add_clause([-A, -g, b]); s.add_clause([-A, g, -a, -b])
            s.add_clause([-O, g, -a]); s.add_clause([-O, g, -b]); s.add_clause([-O, -g, a, b])
            s.add_clause([-N, g, a]); s.add_clause([-N, -g, -a])
            s.add_clause([-y[i], g if F[r] else -g])
    rng = random.Random(1000 + sub)
    rows = set()
    # seed rows: weight-2 inputs (edges and non-edges) and some random
    for u, w in itertools.combinations(range(n), 2): rows.add((1 << u) | (1 << w))
    for _ in range(24): rows.add(rng.randrange(R))
    for r in rows: add_row(r)
    it = 0
    while True:
        it += 1
        ok = s.solve()
        if not ok:
            q.put((sub, 'UNSAT', {'rows': len(rows), 'iters': it})); return
        m = set(l for l in s.get_model() if l > 0)
        circ = []
        for i in range(S):
            W = n + i
            o = [o for o in OPS if op[i, o] in m][0]
            j = [j for j in range(W) if s1[i, j] in m][0]
            k = [k for k in range(W) if s2[i, k] in m][0]
            circ.append((o, j, k))
        out = [i for i in range(S) if y[i] in m][0] + n
        bad = []
        for r in range(R):
            w = [(r >> t) & 1 for t in range(n)]
            for (o, j, k) in circ:
                w.append((w[j] & w[k]) if o == 'and' else (w[j] | w[k]) if o == 'or' else 1 - w[j])
            if bool(w[out]) != F[r]: bad.append(r)
        if not bad:
            q.put((sub, 'SAT', {'gates': circ, 'out': out, 'rows': len(rows)})); return
        for r in rng.sample(bad, min(4, len(bad))):
            rows.add(r); add_row(r)

if __name__ == '__main__':
    out_dir = os.environ.get('OUT_DIR', '.')
    nsub = args.nshards * args.procs
    subs = [args.shard * args.procs + p for p in range(args.procs)]
    q = Queue(); ps = []
    t0 = time.time()
    for sb in subs:
        p = Process(target=build_and_solve, args=(sb, nsub, q)); p.start(); ps.append(p)
    results = {}
    while len(results) < len(subs):
        sb, st, info = q.get()
        results[sb] = (st, info)
        print('sub', sb, st, json.dumps(info), 'at %.0fs' % (time.time() - t0), flush=True)
        if st == 'SAT':
            with open(os.path.join(out_dir, 'model.txt'), 'w') as f: f.write(json.dumps(info) + '\n')
            for p in ps: p.terminate()
            print('RESULT: SAT', flush=True); sys.exit(0)
    for p in ps: p.join()
    print('RESULT: UNSAT', flush=True)
