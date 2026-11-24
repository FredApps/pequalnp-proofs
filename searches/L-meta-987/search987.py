# L-meta-987 search: Boolean sums of linear set systems (pairwise intersection <=1, sets >=2) on n points,
# circuits of fan-in<=2 AND/OR/NOT gates with exactly one NOT whose input wire vanishes whenever x[t0]=0
# (T={t0}, or t0 a fresh degree-0 dummy input), size G = sum(|S|-1). SAT = counterexample.
import itertools, sys, os, time, threading, hashlib, json
from multiprocessing import Pool
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
SOLVER=os.environ.get('SOLVER','cadical153')
def build(n,S,G,t0):
    P=IDPool(); cl=[]; X=range(1<<n); ops=('and','or','not')
    def add(c):
        c2=[]
        for t in c:
            if t is True: return
            if t is False: continue
            c2.append(t)
        cl.append(c2)
    op={}
    for j in range(G):
        w=n+j
        for o in ops: op[j,o]=P.id(('op',j,o))
        cl.append([op[j,o] for o in ops])
        for a,b in itertools.combinations(ops,2): cl.append([-op[j,a],-op[j,b]])
        sel=[]
        for a in range(w):
            for b in range(a,w):
                s=P.id(('s',j,a,b)); sel.append(s)
                for x in X:
                    def L(u,pos):
                        if u<n: bit=bool((x>>u)&1); return bit if pos else (not bit)
                        v=P.id(('v',u,x)); return v if pos else -v
                    v=P.id(('v',w,x))
                    add([-s,-op[j,'and'],-v,L(a,1)]); add([-s,-op[j,'and'],-v,L(b,1)]); add([-s,-op[j,'and'],v,L(a,0),L(b,0)])
                    add([-s,-op[j,'or'],v,L(a,0)]); add([-s,-op[j,'or'],v,L(b,0)]); add([-s,-op[j,'or'],-v,L(a,1),L(b,1)])
                    add([-s,-op[j,'not'],-v,L(a,0)]); add([-s,-op[j,'not'],v,L(a,1)])
                if a>=n:
                    for x in X:
                        if not (x>>t0)&1: cl.append([-s,-op[j,'not'],-P.id(('v',a,x))])
                elif a!=t0: cl.append([-s,-op[j,'not']])
        cl.append(sel); cl.extend(CardEnc.atmost(sel,1,vpool=P,encoding=EncType.seqcounter).clauses)
    nots=[op[j,'not'] for j in range(G)]
    cl.append(nots); cl.extend(CardEnc.atmost(nots,1,vpool=P,encoding=EncType.seqcounter).clauses)
    for o,Sx in enumerate(S):
        outs=[]
        for j in range(G):
            w=n+j; e=P.id(('out',o,w)); outs.append(e)
            for x in X:
                f=any((x>>u)&1 for u in Sx); v=P.id(('v',w,x)); cl.append([-e, v if f else -v])
        cl.append(outs)
    return P,cl,op
def run(job):
    n,S,G,t0,lim=job
    P,cl,op=build(n,S,G,t0)
    s=Solver(name=SOLVER,bootstrap_with=cl)
    tm=threading.Timer(lim,lambda: s.interrupt()); tm.start()
    r=s.solve_limited(expect_interrupt=True); tm.cancel()
    model=None
    if r:
        m=set(l for l in s.get_model() if l>0)
        circ=[]
        for j in range(G):
            o=[k for k in ('and','or','not') if op[j,k] in m][0]
            ins=[(a,b) for a in range(n+j) for b in range(a,n+j) if P.id(('s',j,a,b)) in m][0]
            circ.append((o,ins))
        model=circ
    s.delete()
    return (n,S,G,t0,r,model)
def systems(n,maxm):
    cands=[frozenset(c) for k in range(2,n+1) for c in itertools.combinations(range(n),k)]
    perms=list(itertools.permutations(range(n))); seen=set()
    def canon(F): return min(tuple(sorted(tuple(sorted(p[i] for i in s)) for s in F)) for p in perms)
    def rec(start,F):
        if F:
            tot=sum(len(s)-1 for s in F)
            if tot>=len(F)+1 and set().union(*F)==set(range(n)): seen.add(canon(F))
        if len(F)>=maxm: return
        for i in range(start,len(cands)):
            s=cands[i]
            if all(len(s&f)<=1 for f in F): rec(i+1,F+[s])
    rec(0,[])
    return sorted(seen)
if __name__=='__main__':
    shard=int(sys.argv[1]); nsh=int(sys.argv[2]); n=int(sys.argv[3]); maxm=int(sys.argv[4]); lim=float(sys.argv[5])
    out=os.environ.get('OUT_DIR','.')
    sysl=systems(n,maxm); print('systems',len(sysl),flush=True)
    jobs=[]
    for i,F in enumerate(sysl):
        if i%nsh!=shard: continue
        tot=sum(len(s)-1 for s in F)
        orbit=set()
        for t0 in range(n):  # cheap orbit reduction: only distinct (degree, sizes-of-sets-through) signatures
            sig=tuple(sorted(len(s) for s in F if t0 in s)); 
            if sig in orbit: continue
            orbit.add(sig); jobs.append((n,[list(s) for s in F],tot,t0,lim))
        jobs.append((n+1,[list(s) for s in F],tot,n,lim))  # dummy t0
    jobs.sort(key=lambda j:j[2])
    print('jobs',len(jobs),flush=True)
    found=False; unk=0; uns=0
    with Pool(4) as p:
        for (nn,S,G,t0,r,model) in p.imap_unordered(run,jobs):
            print(nn,S,'G',G,'t0',t0,r,flush=True)
            if r is None: unk+=1
            elif r is False: uns+=1
            else:
                found=True; open(os.path.join(out,'model.txt'),'a').write(json.dumps([nn,S,G,t0,model])+'\n')
    print('unsat',uns,'unknown',unk)
    print('RESULT:', 'SAT' if found else ('UNSAT' if unk==0 else 'UNKNOWN'))
