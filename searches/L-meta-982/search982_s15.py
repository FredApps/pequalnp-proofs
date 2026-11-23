# L-meta-982 shard 15: n7-057, edges 0-1 0-2 0-3 0-4 1-2 1-5 3-4 5-6, claimed bound s = 11.
# Question: is there a circuit of AND, OR, NOT gates, fan-in at most two, with at most 10 gates?
# A minimal circuit uses only AND(a,b), OR(a,b) with a != b and NOT(a), on existing wires, every
# gate feeds a later gate or is the output (the last gate), no NOT of a NOT: anything else can be
# removed without growing the circuit. Two adjacent gates where the later one (not the output)
# does not read the earlier can be swapped, so they are taken in increasing choice order.
# For each k = 1..10, a complete SAT solver (CaDiCaL) looks for such a circuit with exactly k
# gates; the truth-table rows are added lazily (a candidate circuit is evaluated on all 128 rows
# and a failing row is added). UNSAT on a subset of rows implies UNSAT on all rows.
# Cubes (all cover every case): k = 1..8 whole; for k = 9 and 10: the output gate is NOT, or it
# is OR or AND and gate k-2 is NOT, or both are AND/OR and gate k-3 is AND, OR or NOT.
# Usage: search982_s15.py <shard 0..3> (or env SHARD). The 4 shards split the cube list; each
# runs its cubes on 4 processes. Prints RESULT: UNSAT if every cube is UNSAT, RESULT: SAT with the
# circuit in $OUT_DIR/model.txt if one is found (it is verified on all 128 rows first).
# Locally checked: k = 11 is SAT (verified circuit), so the encoding finds circuits.
import sys, os, time, multiprocessing
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
N = 7
EDGES = [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(5,6)]
ALL = list(range(1 << N))
def f(r): return any((r >> a) & 1 and (r >> b) & 1 for a, b in EDGES)

def evalc(circ, r):
    w = [bool((r >> i) & 1) for i in range(N)]
    for kind, a, b in circ:
        w.append((not w[a]) if kind == 'not' else (w[a] and w[b]) if kind == 'and' else (w[a] or w[b]))
    return w[-1]

def solve(k, cube=()):
    top = [0]
    def new():
        top[0] += 1; return top[0]
    S = Cadical153()
    choices = []
    for i in range(k):
        w = N + i; ch = []
        for a in range(w):
            ch.append((new(), 'not', a, None))
            for b in range(a + 1, w):
                ch.append((new(), 'and', a, b)); ch.append((new(), 'or', a, b))
        choices.append(ch)
    for i in range(k):
        enc = CardEnc.equals(lits=[c[0] for c in choices[i]], bound=1, top_id=top[0], encoding=EncType.seqcounter)
        top[0] = max(top[0], enc.nv); S.append_formula(enc.clauses)
    # cube: (d, kind) pins gate k-1-d to that kind; the cubes below cover every case
    for d, kind0 in cube:
        S.add_clause([c for (c, kind, a, b) in choices[k - 1 - d] if kind == kind0])
    for i in range(k - 1):
        S.add_clause([c for j in range(i + 1, k) for (c, kind, a, b) in choices[j] if a == N + i or b == N + i])
    for i in range(k):
        for (c, kind, a, b) in choices[i]:
            if kind == 'not' and a >= N:
                for (c2, k2, a2, b2) in choices[a - N]:
                    if k2 == 'not': S.add_clause([-c, -c2])
    for i in range(k - 2):
        idx = {(kind, a, b): n for n, (c, kind, a, b) in enumerate(choices[i + 1])}
        for (c1, k1, a1, b1) in choices[i]:
            n1 = idx[(k1, a1, b1)]
            for (c2, k2, a2, b2) in choices[i + 1]:
                if a2 == N + i or b2 == N + i: continue
                if idx[(k2, a2, b2)] <= n1: S.add_clause([-c1, -c2])
    def add_row(r):
        val = {w: bool((r >> w) & 1) for w in range(N)}
        for i in range(k):
            w = N + i; g = new(); val[w] = g
            for (c, kind, a, b) in choices[i]:
                A = val[a]; B = val[b] if b is not None else None
                if kind == 'not':
                    if isinstance(A, bool): S.add_clause([-c, (g if not A else -g)])
                    else: S.add_clause([-c, -g, -A]); S.add_clause([-c, g, A])
                    continue
                ops = [A, B]
                if kind == 'and':
                    if any(o is False for o in ops): S.add_clause([-c, -g]); continue
                    vs = [o for o in ops if o is not True]
                    for o in vs: S.add_clause([-c, -g, o])
                    S.add_clause([-c, g] + [-o for o in vs])
                else:
                    if any(o is True for o in ops): S.add_clause([-c, g]); continue
                    vs = [o for o in ops if o is not False]
                    for o in vs: S.add_clause([-c, g, -o])
                    S.add_clause([-c, -g] + vs)
        S.add_clause([val[N + k - 1]] if f(r) else [-val[N + k - 1]])
    rows = [r for r in ALL if bin(r).count('1') == 2 and f(r)]
    rows += [r for r in ALL if not f(r) and all(f(r | (1 << i)) for i in range(N) if not (r >> i) & 1)]
    rows += [0, (1 << N) - 1]
    for r in rows: add_row(r)
    used = set(rows)
    while True:
        if not S.solve():
            S.delete(); return False, None, len(used)
        m = set(l for l in S.get_model() if l > 0)
        circ = [next((kind, a, b) for (c, kind, a, b) in choices[i] if c in m) for i in range(k)]
        bad = [r for r in ALL if evalc(circ, r) != f(r)]
        if not bad:
            S.delete(); return True, circ, len(used)
        for r in bad[:4]:
            add_row(r); used.add(r)


KINDS = ['and', 'or', 'not']
def cubes():
    out = [(k, ()) for k in range(1, 9)]
    for k in (9, 10):
        out.append((k, ((0, 'not'),)))
        for o in ('and', 'or'):
            out.append((k, ((0, o), (1, 'not'))))
            for p in ('and', 'or'):
                for q in KINDS:
                    out.append((k, ((0, o), (1, p), (2, q))))
    return out

def work(item):
    k, cube = item
    t = time.time()
    sat, circ, nr = solve(k, cube)
    return k, cube, sat, circ, nr, time.time() - t

if __name__ == '__main__':
    shard = int(sys.argv[1]) if len(sys.argv) > 1 else int(os.environ.get('SHARD', '0'))
    nsh = 4
    mine = [c for i, c in enumerate(cubes()) if i % nsh == shard]
    print('shard', shard, 'cubes', len(mine), 'of', len(cubes()), flush=True)
    found = None
    with multiprocessing.Pool(4) as pool:
        for k, cube, sat, circ, nr, dt in pool.imap_unordered(work, mine):
            print('k', k, 'cube', cube, 'SAT' if sat else 'UNSAT', 'rows', nr, '%.0fs' % dt, circ if sat else '', flush=True)
            if sat and found is None:
                found = (k, circ)
                pool.terminate()
                break
    if found:
        od = os.environ.get('OUT_DIR', '.')
        os.makedirs(od, exist_ok=True)
        with open(os.path.join(od, 'model.txt'), 'w') as fh:
            fh.write('k=%d circuit=%r\n' % found)
        print('RESULT: SAT')
    else:
        print('RESULT: UNSAT')
