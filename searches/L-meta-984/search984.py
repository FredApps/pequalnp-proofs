# L-meta-984 range 30: graph n7-072 (edges 0-1 0-2 0-3 1-2 1-4 3-5 3-6 4-5 5-6), s = 12.
# Claim checked: no monotone fan-in-two AND/OR circuit with at most 11 gates computes its edge
# function. For each G in 1..11 the normal-form encoding below must be UNSAT. A minimal circuit
# of size k can always be put in this normal form with exactly k gates (distinct gate functions,
# every gate read, inputs a<b, output last gate, consecutive independent gates in lex order).
# Cubes: for G >= 8, split on the output gate type and its first input wire.
# Shard s (0..3) takes the jobs with index % 4 == s and runs them on 4 processes.
# Prints RESULT: SAT (witness in $OUT_DIR/model.txt) or RESULT: UNSAT.
# Exact monotone fan-in-2 circuit search with sound symmetry breaking.
# Usage: enc2.py G solver "edges" n.  Asks: is there a circuit of AND/OR gates of fan-in two,
# exactly G gates, every gate reading two distinct earlier wires, every gate computing a function
# different from every earlier wire, every non-output gate read later, output = last gate,
# consecutive independent gates in lexicographic order of inputs, computing the edge function.
# A minimal circuit of size k can always be brought into this form, so UNSAT for all G<=s-1
# proves the lower bound s.
import sys, os, itertools, time
from multiprocessing import Pool
from pysat.solvers import Solver
from pysat.card import CardEnc
EDGES=[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5),(5,6)]
NV=7
def build(G,E,n):
  def f(m): return any((m>>u)&1 and (m>>v)&1 for u,v in E)
  rows=list(range(1<<n)); R=len(rows)
  cnt=[0]
  def nv(): cnt[0]+=1; return cnt[0]
  cl=[]
  t=[nv() for _ in range(G)]
  sa={};sb={}
  for i in range(G):
    w=n+i
    for j in range(w): sa[i,j]=nv(); sb[i,j]=nv()
  val={}
  for r in rows:
    for i in range(G): val[n+i,r]=nv()
  def lit(j,r):
    if j<n: return bool((rows[r]>>j)&1)
    return val[j,r]
  for i in range(G):
    w=n+i
    for lits in ([sa[i,j] for j in range(w)],[sb[i,j] for j in range(w)]):
      enc=CardEnc.equals(lits=lits,bound=1,top_id=cnt[0],encoding=1); cnt[0]=max(cnt[0],enc.nv); cl+=enc.clauses
    for j in range(w):
      for k in range(j+1): cl.append([-sa[i,j],-sb[i,k]])   # a < b
  for r in range(R):
    for i in range(G):
      w=n+i; v=val[n+i,r]; a=nv(); b=nv(); T=t[i]
      for j in range(w):
        L=lit(j,r)
        for sel,y in ((sa[i,j],a),(sb[i,j],b)):
          if L is True: cl.append([-sel,y])
          elif L is False: cl.append([-sel,-y])
          else: cl.append([-sel,-L,y]); cl.append([-sel,L,-y])
      cl += [[-T,-a,-b,v],[-T,a,-v],[-T,b,-v],[T,-a,v],[T,-b,v],[T,a,b,-v]]
    out=val[n+G-1,r]
    cl.append([out] if f(rows[r]) else [-out])
  # distinct from every earlier wire
  for i in range(G):
    for j in range(n+i):
      ds=[]
      for r in range(R):
        L=lit(j,r); v=val[n+i,r]
        if L is True: ds.append(-v)
        elif L is False: ds.append(v)
        else:
          d=nv(); ds.append(d)
          cl += [[-d,v,L],[-d,-v,-L]]
      cl.append(ds)
  # used
  for i in range(G-1):
    w=n+i
    cl.append([sa[k,w] for k in range(i+1,G)]+[sb[k,w] for k in range(i+1,G)])
  for j in range(n):
    if any(j in e for e in E):
      cl.append([sa[k,j] for k in range(G)]+[sb[k,j] for k in range(G)])
  # lex order of consecutive independent gates: if gate i+1 does not read wire n+i then
  # (a_i,b_i) <= (a_{i+1},b_{i+1}) lexicographically (pairs as numbers a*W+b), types too if equal pairs
  W=n+G
  for i in range(G-1):
    w=n+i
    indep=nv()  # indep -> gate i+1 does not read n+i
    cl.append([-indep,-sa[i+1,w]]); cl.append([-indep,-sb[i+1,w]])
    cl.append([indep,sa[i+1,w],sb[i+1,w]])
    for a1 in range(w):
      for b1 in range(a1+1,w):
        for a2 in range(w+1):
          for b2 in range(a2+1,w+1):
            if (a2,b2)<(a1,b1):
              cl.append([-indep,-sa[i,a1],-sb[i,b1],-sa[i+1,a2],-sb[i+1,b2]])
  return cl,t,sa,sb

def job(args):
  G,cube,solvername=args
  cl,t,sa,sb=build(G,EDGES,NV)
  n=NV
  assum=[]
  if cube is not None:
    typ,a=cube
    assum=[t[G-1] if typ=='and' else -t[G-1], sa[G-1,a]]
  t0=time.time()
  with Solver(name=solvername,bootstrap_with=cl) as s:
    res=s.solve(assumptions=assum)
    circ=None
    if res:
      M=set(l for l in s.get_model() if l>0)
      circ=[]
      for i in range(G):
        w=n+i
        a=[j for j in range(w) if sa[i,j] in M][0]; b=[j for j in range(w) if sb[i,j] in M][0]
        circ.append(('and' if t[i] in M else 'or',a,b))
  return G,cube,res,round(time.time()-t0,1),circ
def jobs(solvername):
  J=[]
  for G in range(1,12):
    if G<8: J.append((G,None,solvername))
    else:
      for typ in ('and','or'):
        for a in range(NV+G-1): J.append((G,(typ,a),solvername))
  return J
if __name__=='__main__':
  import argparse
  ap=argparse.ArgumentParser(); ap.add_argument('--shard',type=int,default=int(os.environ.get('SHARD','0')))
  ap.add_argument('--solver',default=os.environ.get('SOLVER','cadical195')); ap.add_argument('--shards',type=int,default=4)
  a=ap.parse_args()
  mine=[j for i,j in enumerate(jobs(a.solver)) if i%a.shards==a.shard]
  print('shard',a.shard,'jobs',len(mine),flush=True)
  outd=os.environ.get('OUT_DIR','.')
  sat=False
  with Pool(4) as p:
    for G,cube,res,sec,circ in p.imap_unordered(job,mine):
      print('G',G,'cube',cube,'res',res,'sec',sec,flush=True)
      if res:
        sat=True
        with open(os.path.join(outd,'model.txt'),'a') as f: f.write('G=%d cube=%s circuit=%s\n'%(G,cube,circ))
        p.terminate(); break
  print('RESULT: SAT' if sat else 'RESULT: UNSAT',flush=True)
