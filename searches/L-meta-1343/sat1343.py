# L-meta-1343 range 21: is there a monotone fan-in<=2 AND/OR circuit with exactly G=21 gates
# computing the edge function of the 11-vertex graph, with some AND gate true at the input
# where exactly {0,1,2,3} is true?  Superset model: each gate reads two operands (repetition
# allowed) among earlier wires and two constants FALSE/TRUE (covers fan-in 0/1 and
# out-of-range reads).  Rows: the 16 edges (output true) and the 24 maximal independent sets
# (output false); by monotonicity these rows determine the edge function.
# Sub-cube by the index g0 of the special AND gate; shard s takes g0 = s, s+K, s+2K, ...
import sys, os, itertools, time
from multiprocessing import Pool
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

N = 11
E = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10),
     (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
G = int(os.environ.get("GATES", "21"))
SPECIAL = frozenset({0, 1, 2, 3})

def mis_list():
    adj = {v: set() for v in range(N)}
    for a, b in E:
        adj[a].add(b); adj[b].add(a)
    res = []
    for m in range(1 << N):
        S = {v for v in range(N) if m >> v & 1}
        if any(b in S for a in S for b in adj[a]):
            continue
        if all((v in S) or (adj[v] & S) for v in range(N)):
            res.append(frozenset(S))
    return res

def build(g0, solver_name):
    MIS = mis_list()
    assert len(MIS) == 24, len(MIS)
    assert SPECIAL in MIS
    rows = [(frozenset(e), 1) for e in E] + [(S, 0) for S in MIS]
    pool = IDPool()
    cl = []
    # wire indices: 0..N-1 inputs, N..N+G-1 gates, FALSE=-1, TRUE=-2 pseudo
    def opts(g):
        return list(range(N + g)) + ['F', 'T']
    s1 = lambda g, a: pool.id(('s1', g, a))
    s2 = lambda g, a: pool.id(('s2', g, a))
    A = lambda g: pool.id(('and', g))
    O = lambda j: pool.id(('out', j))
    V = lambda j, r: pool.id(('v', j, r))
    for g in range(G):
        o = opts(g)
        for sel in (s1, s2):
            enc = CardEnc.equals([sel(g, a) for a in o], 1, vpool=pool, encoding=EncType.seqcounter)
            cl += enc.clauses
        # symmetry (sound): operand order irrelevant for AND/OR; require idx(op1) <= idx(op2)
        for i, a in enumerate(o):
            for j, b in enumerate(o):
                if j < i:
                    cl.append([-s1(g, a), -s2(g, b)])
    enc = CardEnc.equals([O(N + g) for g in range(G)], 1, vpool=pool, encoding=EncType.seqcounter)
    cl += enc.clauses
    for r, (S, t) in enumerate(rows):
        for g in range(G):
            v = V(N + g, r)
            u1 = pool.id(('u1', g, r)); u2 = pool.id(('u2', g, r))
            for sel, u in ((s1, u1), (s2, u2)):
                for a in opts(g):
                    if a == 'F':
                        cl.append([-sel(g, a), -u])
                    elif a == 'T':
                        cl.append([-sel(g, a), u])
                    elif a < N:
                        cl.append([-sel(g, a), u if a in S else -u])
                    else:
                        x = V(a, r)
                        cl.append([-sel(g, a), -u, x]); cl.append([-sel(g, a), u, -x])
            a_ = A(g)
            cl += [[-a_, -v, u1], [-a_, -v, u2], [-a_, v, -u1, -u2],
                   [a_, v, -u1], [a_, v, -u2], [a_, -v, u1, u2]]
            cl.append([-O(N + g), v if t else -v])
    # shard condition: gate g0 is an AND and is true on the row SPECIAL
    rs = [r for r, (S, t) in enumerate(rows) if S == SPECIAL and t == 0][0]
    if g0 >= 0:
        cl.append([A(g0)])
        cl.append([V(N + g0, rs)])
    return cl, pool, rows

def solve_one(args):
    g0, solver_name = args
    t0 = time.time()
    cl, pool, rows = build(g0, solver_name)
    with Solver(name=solver_name, bootstrap_with=cl) as s:
        ok = s.solve()
        model = s.get_model() if ok else None
    return g0, ok, round(time.time() - t0, 1), model, pool.obj2id if ok else None

def main():
    shard = int(os.environ.get('SHARD', sys.argv[1] if len(sys.argv) > 1 else '0'))
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    solver = os.environ.get('SOLVER', 'cadical153')
    procs = int(os.environ.get('PROCS', '4'))
    gs = [g for g in range(G) if g % K == shard]
    out = os.environ.get('OUT_DIR', '.')
    print('shard', shard, 'of', K, 'g0 values', gs, 'solver', solver, flush=True)
    anysat = False
    with Pool(procs) as p:
        for g0, ok, sec, model, o2i in p.imap_unordered(solve_one, [(g, solver) for g in gs]):
            print('g0', g0, 'SAT' if ok else 'UNSAT', sec, 's', flush=True)
            if ok:
                anysat = True
                ms = set(l for l in model if l > 0)
                with open(os.path.join(out, 'model.txt'), 'a') as f:
                    f.write('g0 %d\n' % g0)
                    for k, i in o2i.items():
                        if i in ms and k[0] in ('s1', 's2', 'and', 'out'):
                            f.write(repr(k) + '\n')
                p.terminate()
                break
    print('RESULT: SAT' if anysat else 'RESULT: UNSAT', flush=True)

if __name__ == '__main__':
    main()
