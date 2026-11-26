import subprocess,sys,os
here=os.path.dirname(os.path.abspath(__file__))
mask,gates,shard,secs=sys.argv[1:5]
subprocess.check_call(['g++','-O3','-march=native','-o','/tmp/s44',os.path.join(here,'s.cpp')])
sys.exit(subprocess.call(['/tmp/s44',mask,gates,shard,secs]))
