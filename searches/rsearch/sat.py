# sat.py <problem.json> <shard> <seconds> : SAT search for <=K all-0 rectangles covering the 0-cells.
# Shards impose invariance of the cover under a matrix automorphism (or none).
import json,sys,os,random,time,threading
from pysat.solvers import Solver
here=os.path.dirname(os.path.abspath(__file__))
p=json.load(open(os.path.join(here,sys.argv[1])));R,C,K,M=p['R'],p['C'],p['K'],p['M']
shard=int(sys.argv[2]);secs=float(sys.argv[3]);t0=time.time()
one=[[M[i]>>j&1 for j in range(C)] for i in range(R)]
zeros=[(i,j) for i in range(R) for j in range(C) if not one[i][j]]
def automorphism(rng,limit=200000):
    """random (row perm, col perm) preserving the matrix, by backtracking"""
    rp=[None]*R;cp=[None]*C;ur=set();uc=set();steps=[0]
    order=[('r',i) for i in range(R)]+[('c',j) for j in range(C)]
    rng.shuffle(order)
    def ok(kind,a,b):
        if kind=='r': return all(cp[j] is None or one[a][j]==one[b][cp[j]] for j in range(C)) and sum(one[a])==sum(one[b])
        return all(rp[i] is None or one[i][a]==one[rp[i]][b] for i in range(R)) and sum(one[i][a] for i in range(R))==sum(one[i][b] for i in range(R))
    def go(k):
        steps[0]+=1
        if steps[0]>limit: raise TimeoutError
        if k==len(order): return True
        # most constrained next
        best=None
        for kind,a in order:
            arr=rp if kind=='r' else cp
            if arr[a] is not None: continue
            used=ur if kind=='r' else uc
            opts=[b for b in range(R if kind=='r' else C) if b not in used and ok(kind,a,b)]
            if best is None or len(opts)<len(best[2]): best=(kind,a,opts)
            if len(opts)<=1: break
        kind,a,opts=best;rng.shuffle(opts)
        arr=rp if kind=='r' else cp;used=ur if kind=='r' else uc
        for b in opts:
            arr[a]=b;used.add(b)
            if go(k+1): return True
            arr[a]=None;used.discard(b)
        return False
    try: return (rp,cp) if go(0) else None
    except TimeoutError: return None
def order_of(g):
    rp,cp=g;a,b=list(range(R)),list(range(C))
    for k in range(1,200):
        a=[rp[x] for x in a];b=[cp[x] for x in b]
        if a==list(range(R)) and b==list(range(C)): return k
    return 0
def power(g,e):
    rp,cp=g;a,b=list(range(R)),list(range(C))
    for _ in range(e):
        a=[rp[x] for x in a];b=[cp[x] for x in b]
    return a,b
def element_of_order(k,rng):
    while time.time()-t0<secs/3:
        g=automorphism(rng)
        if g:
            o=order_of(g)
            if o and o%k==0:
                h=power(g,o//k)
                if order_of(h)==k: return h
    return None
def solve(g,k,fixed,orbits,seed,budget):
    rng=random.Random(seed)
    nv=[0]
    def new():
        nv[0]+=1;return nv[0]
    cl=[]
    rects=[]   # (rowlits, collits)
    for _ in range(orbits):
        rows=[new() for i in range(R)];cols=[new() for j in range(C)]
        for e in range(k):
            a,b=power(g,e)
            ia=[0]*R;ib=[0]*C
            for i in range(R): ia[a[i]]=i
            for j in range(C): ib[b[j]]=j
            rects.append(([rows[ia[i]] for i in range(R)],[cols[ib[j]] for j in range(C)]))
        for i in range(R):
            for j in range(C):
                if one[i][j]: cl.append([-rows[i],-cols[j]])
    for _ in range(fixed):
        rows=[new() for i in range(R)];cols=[new() for j in range(C)]
        if k>1:
            for i in range(R): cl.append([-rows[i],rows[g[0][i]]])
            for j in range(C): cl.append([-cols[j],cols[g[1][j]]])
        rects.append((rows,cols))
        for i in range(R):
            for j in range(C):
                if one[i][j]: cl.append([-rows[i],-cols[j]])
    # coverage: for invariant covers it is enough to cover one cell of each orbit
    done=set();aux={}
    for z in zeros:
        if z in done: continue
        if k>1:
            i,j=z
            for e in range(k):
                done.add((i,j));i,j=g[0][i],g[1][j]
        lits=[]
        for t,(rows,cols) in enumerate(rects):
            y=new();lits.append(y);cl.append([-y,rows[z[0]]]);cl.append([-y,cols[z[1]]])
        cl.append(lits)
    if k==1:   # break symmetry: first zero cell goes in rectangle 0
        rows,cols=rects[0];cl.append([rows[zeros[0][0]]]);cl.append([cols[zeros[0][1]]])
    perm=list(range(1,nv[0]+1));rng.shuffle(perm)
    mp=lambda l:perm[abs(l)-1]*(1 if l>0 else -1)
    inv={perm[v-1]:v for v in range(1,nv[0]+1)}
    rng.shuffle(cl)
    s=Solver(name=['cadical153','glucose4','maplechrono'][seed%3],bootstrap_with=[[mp(l) for l in c] for c in cl])
    s.set_phases([v if rng.random()<0.3 else -v for v in range(1,nv[0]+1)]) if seed%3!=2 else None
    timer=threading.Timer(budget,s.interrupt);timer.start()
    r=s.solve_limited(expect_interrupt=True);timer.cancel()
    if r:
        m=set(l for l in s.get_model() if l>0)
        out=[[[i for i in range(R) if perm[rows[i]-1] in m],[j for j in range(C) if perm[cols[j]-1] in m]] for rows,cols in rects]
        cov=set((i,j) for a,b in out for i in a for j in b)
        assert cov==set(zeros) and len(out)<=K
        print('FOUND',json.dumps(out),flush=True)
    s.delete()
    return r
plans=[(3,1,4),(3,4,3),(5,3,2),(2,1,6),(2,3,5),(7,6,1),(3,7,2),(2,5,4),(1,13,0)]
k,f,m=plans[shard%len(plans)]
rng=random.Random(1000+shard)
trial=0;budget=60
while time.time()-t0<secs:
    trial+=1
    if k==1:
        r=solve(None,1,13,0,shard*100+trial,secs-(time.time()-t0))
    else:
        g=element_of_order(k,rng)
        if g is None: print('no element of order',k,flush=True);break
        r=solve(g,k,f,m,shard*100+trial,min(budget,max(1,secs-(time.time()-t0))))
    print('trial',trial,'order',k,'fixed',f,'orbits',m,'result',{True:'SAT',False:'UNSAT',None:'timeout'}[r],'t',int(time.time()-t0),flush=True)
    if r: break
    if trial%6==0: budget*=2
