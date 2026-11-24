# L-meta-2452: AND/OR/NOT fan-in<=2 circuit, exactly k gates (dead gates allowed), gate 0 = AND of two
# inputs, last gate = output, computing OR over the 11 edges of the theta graph of (x_a AND x_b), 10 inputs.
# argv: k shard   (shard = index 0..15 into REPS (gate 0 input pair up to graph automorphism); 'all' = no split)
# Prints RESULT: SAT / RESULT: UNSAT. On SAT writes circuit to $OUT_DIR/model.txt.
import sys, os, itertools, random
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
N = 10
EDGES = [(0,2),(2,3),(3,1),(0,4),(4,5),(5,6),(6,1),(0,7),(7,8),(8,9),(9,1)]
# orbit representatives of input pairs under the 4 automorphisms of the theta graph
REPS = [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(2,3),(2,4),(2,5),(2,6),(4,5),(4,6),(4,7),(4,8),(4,9),(5,8)]
def f(r): return any((r >> a) & 1 and (r >> b) & 1 for a, b in EDGES)
def evalc(c, r):
    w = [bool((r >> i) & 1) for i in range(N)]
    for kind, a, b in c:
        w.append((w[a] and w[b]) if kind == 'and' else (w[a] or w[b]) if kind == 'or' else (not w[a]))
    return w[-1]
def solve(k, shard):
    top = [0]
    def new(): top[0] += 1; return top[0]
    S = Cadical153(); ch = []
    pairs = list(itertools.combinations(range(N), 2))
    for i in range(k):
        w = N + i; c = []
        if i == 0:
            if shard == 'all': c = [(new(), 'and', a, b) for a, b in pairs]
            else: a, b = REPS[int(shard)]; c = [(new(), 'and', a, b)]
        else:
            for a in range(w):
                for b in range(a + 1, w):
                    c.append((new(), 'and', a, b)); c.append((new(), 'or', a, b))
                c.append((new(), 'not', a, None))
        ch.append(c)
    for i in range(k):
        e = CardEnc.equals(lits=[x[0] for x in ch[i]], bound=1, top_id=top[0], encoding=EncType.seqcounter)
        top[0] = max(top[0], e.nv); S.append_formula(e.clauses)
    def add_row(r):
        val = {w: bool((r >> w) & 1) for w in range(N)}
        for i in range(k):
            g = new(); val[N + i] = g
            for (c, kind, a, b) in ch[i]:
                if kind == 'not':
                    o = val[a]
                    if o is True: S.add_clause([-c, -g])
                    elif o is False: S.add_clause([-c, g])
                    else: S.add_clause([-c, g, o]); S.add_clause([-c, -g, -o])
                    continue
                ops = [val[a], val[b]]
                if kind == 'and':
                    if False in ops: S.add_clause([-c, -g]); continue
                    vs = [o for o in ops if o is not True]
                    for o in vs: S.add_clause([-c, -g, o])
                    S.add_clause([-c, g] + [-o for o in vs])
                else:
                    if True in ops: S.add_clause([-c, g]); continue
                    vs = [o for o in ops if o is not False]
                    for o in vs: S.add_clause([-c, g, -o])
                    S.add_clause([-c, -g] + vs)
        S.add_clause([val[N + k - 1]] if f(r) else [-val[N + k - 1]])
    random.seed(1)
    rows = [r for r in range(1 << N) if bin(r).count('1') <= 2]
    rows += random.sample(range(1 << N), 64)
    used = set(rows)
    for r in rows: add_row(r)
    while True:
        if not S.solve(): return None
        m = set(l for l in S.get_model() if l > 0)
        circ = [next((x[1], x[2], x[3]) for x in ch[i] if x[0] in m) for i in range(k)]
        bad = [r for r in range(1 << N) if evalc(circ, r) != f(r)]
        if not bad: return circ
        for r in random.sample(bad, min(8, len(bad))): add_row(r)
if __name__ == '__main__':
    k, shard = int(sys.argv[1]), sys.argv[2]
    c = solve(k, shard)
    if c:
        od = os.environ.get('OUT_DIR')
        if od:
            os.makedirs(od, exist_ok=True); open(os.path.join(od, 'model.txt'), 'w').write(repr(c))
        print('RESULT: SAT', c)
    else: print('RESULT: UNSAT')
