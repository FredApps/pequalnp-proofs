# run.py <problem.json: R,C,K,M> <shard> <seconds>
import json,subprocess,sys,os
here=os.path.dirname(os.path.abspath(__file__))
p=json.load(open(os.path.join(here,sys.argv[1])));R,C,K,M=p['R'],p['C'],p['K'],p['M']
Z=[((1<<C)-1)&~m for m in M]
closed=set([(1<<C)-1])
for z in Z: closed|={c&z for c in closed}
rects=[]
for cols in sorted(closed):
    rows=sum(1<<i for i in range(R) if cols&~Z[i]==0)
    if rows and cols: rects.append((rows,cols))
open('/tmp/rects.txt','w').write('%d %d %d %d\n'%(R,C,K,len(rects))+''.join('%d %d\n'%r for r in rects))
subprocess.check_call(['g++','-O3','-march=native','-std=c++17','-o','/tmp/rect',os.path.join(here,'rect.cpp')])
procs=[subprocess.Popen(['/tmp/rect','/tmp/rects.txt',str(int(sys.argv[2])*4+k),sys.argv[3]]) for k in range(os.cpu_count() or 4)]
rc=[q.wait() for q in procs]
sys.exit(1 if any(rc) else 0)
