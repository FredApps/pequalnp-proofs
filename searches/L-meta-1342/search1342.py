# L-meta-1342 range 22: is there a monotone fan-in-two AND/OR circuit with at most 21 gates for the
# edge function of the 11-vertex graph below, in which some AND gate is true on the input whose
# true set is exactly {0,1,2,6} (one of the 24 maximal independent sets)?
# Rows (monotone, so enough): the 16 edges true, the 24 maximal independent sets false.
# Exactly 21 gates; inputs a <= b per gate (a == b allowed, so smaller circuits pad by copies);
# every non-output gate is read later; every input is read; output = last gate.
# Cubes partition the range: cube k = "gate k is the FIRST AND gate true on {0,1,2,6}".
# Shard s of S takes cubes k with k % S == s and runs them on 4 processes.
# Any model is re-evaluated on all 2048 inputs. Prints RESULT: SAT / UNSAT / UNKNOWN.
import sys, os, time, json
from multiprocessing import Pool
from pysat.solvers import Solver
from pysat.card import CardEnc
E=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
n=11; G=21; SPECIAL=(1<<0)|(1<<1)|(1<<2)|(1<<6)
def f(m): return any((m>>u)&1 and (m>>v)&1 for u,v in E)
def rows_():
  ind=set(m for m in range(1<<n) if not f(m))
  maxind=[m for m in sorted(ind) if all((m>>i)&1 or (m|1<<i) not in ind for i in range(n))]
  return [((1<<u)|(1<<v),True) for u,v in E]+[(m,False) for m in maxind], maxind
def build():
  rows,maxind=rows_()
  assert len(maxind)==24 and SPECIAL in maxind
  cnt=[0]
  def nv(): cnt[0]+=1; return cnt[0]
  cl=[]
  t=[nv() for _ in range(G)]
  sa={};sb={}
  for i in range(G):
    for j in range(n+i): sa[i,j]=nv(); sb[i,j]=nv()
  val={}
  for r in range(len(rows)):
    for i in range(G): val[n+i,r]=nv()
  for i in range(G):
    w=n+i
    for lits in ([sa[i,j] for j in range(w)],[sb[i,j] for j in range(w)]):
      enc=CardEnc.equals(lits=lits,bound=1,top_id=cnt[0],encoding=1); cnt[0]=max(cnt[0],enc.nv); cl.extend(enc.clauses)
    for j in range(w):
      for k in range(j): cl.append([-sa[i,j],-sb[i,k]])
  def lit(j,r):
    if j<n: return bool((rows[r][0]>>j)&1)
    return val[j,r]
  for r in range(len(rows)):
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
    cl.append([out] if rows[r][1] else [-out])
  for i in range(G-1):
    w=n+i
    cl.append([sa[k,w] for k in range(i+1,G)]+[sb[k,w] for k in range(i+1,G)])
  for j in range(n):
    cl.append([sa[k,j] for k in range(G)]+[sb[k,j] for k in range(G)])
  rs=[r for r in range(len(rows)) if rows[r][0]==SPECIAL and not rows[r][1]][0]
  y=[]
  for i in range(G):
    yi=nv(); y.append(yi)
    cl += [[-yi,t[i]],[-yi,val[n+i,rs]],[yi,-t[i],-val[n+i,rs]]]
  cl.append(list(y))
  return cl,t,sa,sb,y
def check(circ):
  for m in range(1<<n):
    w=[bool((m>>j)&1) for j in range(n)]
    for op,a,b in circ: w.append((w[a] and w[b]) if op=='and' else (w[a] or w[b]))
    if w[-1]!=f(m): return False
  wv=[bool((SPECIAL>>j)&1) for j in range(n)]
  for op,a,b in circ: wv.append((wv[a] and wv[b]) if op=='and' else (wv[a] or wv[b]))
  return any(op=='and' and wv[n+i] for i,(op,a,b) in enumerate(circ))
def job(args):
  k,solvername=args
  cl,t,sa,sb,y=build()
  assum=[y[k]]+[-y[j] for j in range(k)]
  t0=time.time()
  with Solver(name=solvername,bootstrap_with=cl) as s:
    res=s.solve(assumptions=assum)
    circ=None
    if res:
      M=set(l for l in s.get_model() if l>0)
      circ=[]
      for i in range(G):
        a=[j for j in range(n+i) if sa[i,j] in M][0]; b=[j for j in range(n+i) if sb[i,j] in M][0]
        circ.append(('and' if t[i] in M else 'or',a,b))
  return k,res,round(time.time()-t0,1),circ
if __name__=='__main__':
  import argparse
  ap=argparse.ArgumentParser()
  ap.add_argument('--shard',type=int,default=int(os.environ.get('SHARD','0')))
  ap.add_argument('--shards',type=int,default=4)
  ap.add_argument('--solver',default=os.environ.get('SOLVER','cadical195'))
  ap.add_argument('--cubes',default='')
  a=ap.parse_args()
  cubes=[int(c) for c in a.cubes.split(',')] if a.cubes else [k for k in range(G) if k%a.shards==a.shard]
  print('shard',a.shard,'cubes',cubes,flush=True)
  outd=os.environ.get('OUT_DIR','.')
  sat=False; done=0
  with Pool(4) as p:
    for k,res,sec,circ in p.imap_unordered(job,[(k,a.solver) for k in cubes]):
      print('cube',k,'res',res,'sec',sec,flush=True); done+=1
      if res:
        ok=check(circ)
        print('witness check on all 2048 inputs:',ok,flush=True)
        with open(os.path.join(outd,'model.txt'),'a') as fo: fo.write(json.dumps({'cube':k,'circuit':circ,'verified':ok})+'\n')
        if ok: sat=True; p.terminate(); break
  print('RESULT: SAT' if sat else ('RESULT: UNSAT' if done==len(cubes) else 'RESULT: UNKNOWN'),flush=True)
