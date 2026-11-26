#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <ctime>
#include <string>
typedef uint64_t u64;
const int NI=11,N=44,W=NI+N;
const u64 IN[NI]={2147418115ULL,663661903884ULL,34144976944ULL,728266375360ULL,21653750532ULL,103293914128ULL,26322415680ULL,344922804352ULL,414195942664ULL,581968119809ULL,1065151898146ULL};
const u64 M=(1ULL<<40)-1,T=65535,Z=M&~T;
struct G{int op,a,b;};struct C{G g[N];int out;};
static u64 st;static inline u64 rnd(){st^=st<<13;st^=st>>7;st^=st<<17;return st;}
static void eval(const C&c,int&err,int&act,int&mix){
  bool use[W]={0};use[c.out]=1;act=0;mix=0;
  for(int i=N-1;i>=0;i--)if(use[NI+i]){act++;use[c.g[i].a]=1;use[c.g[i].b]=1;}
  u64 v[W];for(int i=0;i<NI;i++)v[i]=IN[i];
  for(int i=0;i<N;i++)if(use[NI+i]){const G&g=c.g[i];v[NI+i]=g.op==0?(v[g.a]&v[g.b]):(v[g.a]|v[g.b]);if(g.op==0&&(v[NI+i]&Z))mix++;}
  err=__builtin_popcountll((v[c.out]^T)&M);if(mix>3)mix=3;
}
static G rg(int i){return G{(int)(rnd()&1),(int)(rnd()%(NI+i)),(int)(rnd()%(NI+i))};}
static void mutate(C&c){
  int k=1+rnd()%4;
  while(k--){int r=rnd()%100;
    if(r<3){c.out=NI+rnd()%N;continue;}
    int i=rnd()%N;
    if(r<45){if(rnd()&1)c.g[i].a=rnd()%(NI+i);else c.g[i].b=rnd()%(NI+i);}
    else if(r<58)c.g[i].op^=1;
    else if(r<72)c.g[i]=rg(i);
    else if(r<90){if(i==0)continue;int j=rnd()%i;for(int t=j+1;t<N;t++)if(c.g[t].a==NI+i&&(rnd()&1))c.g[t].a=NI+j;}
    else{int t=rnd()%N;if(t<=i)continue;if(rnd()&1){if(c.g[t].a<NI+i)c.g[i].a=c.g[t].a;c.g[t].a=NI+i;}else{if(c.g[t].b<NI+i)c.g[i].b=c.g[t].b;c.g[t].b=NI+i;}}
  }
}
// star-cover seed of the edge function (rows 0..15 are the one-inputs)
static bool seeded(C&c){
  int adj[NI]={0};
  for(int r=0;r<16;r++){int e[NI],n=0;for(int i=0;i<NI;i++)if(IN[i]>>r&1)e[n++]=i;if(n!=2)return false;adj[e[0]]|=1<<e[1];adj[e[1]]|=1<<e[0];}
  int rem[NI];for(int i=0;i<NI;i++)rem[i]=adj[i];
  G L[128];int n=0,terms[NI],nt=0;
  while(true){int best=-1,bc=0;for(int v=0;v<NI;v++){int k=__builtin_popcount(rem[v])*8+(rnd()%8);if(rem[v]&&k>bc){bc=k;best=v;}}
    if(best<0)break;int s=-1;int nb=rem[best];
    for(int u=0;u<NI;u++)if(nb>>u&1){if(s<0)s=u;else{L[n]=G{1,s,u};s=100+n;n++;}rem[u]&=~(1<<best);}
    rem[best]=0;L[n]=G{0,best,s};terms[nt++]=100+n;n++;}
  int s=terms[0];for(int i=1;i<nt;i++){L[n]=G{1,s,terms[i]};s=100+n;n++;}
  if(n>N)return false;
  int pos[128];for(int i=0;i<N;i++)c.g[i]=rg(i);
  int slot=0;for(int k=0;k<n;k++){int left=n-k,room=N-slot;int skip=rnd()%(room-left+1);if(skip>2)skip=rnd()%3;slot+=skip;pos[k]=slot++;}
  auto w=[&](int x){return x<100?x:NI+pos[x-100];};
  for(int k=0;k<n;k++)c.g[pos[k]]=G{L[k].op,w(L[k].a),w(L[k].b)};
  c.out=NI+pos[n-1];return true;
}
static void dump(const C&c,int act,int mix){
  bool use[W]={0};use[c.out]=1;for(int i=N-1;i>=0;i--)if(use[NI+i]){use[c.g[i].a]=1;use[c.g[i].b]=1;}
  int id[W];for(int i=0;i<NI;i++)id[i]=i;int n=0;std::string s;char buf[64];
  for(int i=0;i<N;i++)if(use[NI+i]){id[NI+i]=NI+n++;const G&g=c.g[i];snprintf(buf,64,"%s %d %d;",g.op?"or":"and",id[g.a],id[g.b]);s+=buf;}
  printf("FOUND size=%d mix=%d out=%d : %s\n",act,mix,id[c.out],s.c_str());fflush(stdout);
}
int main(int argc,char**argv){
  int shard=atoi(argv[1]);double secs=atof(argv[2]);
  st=0x9E3779B97F4A7C15ULL*(shard+1)^(u64)time(0);for(int i=0;i<20;i++)rnd();
  time_t t0=time(0);int found=0,best=99,restarts=0;bool canseed=true;
  while(difftime(time(0),t0)<secs){
    C p;bool seed=(shard%4)!=3;
    if(seed)seed=seeded(p);
    if(!seed){for(int i=0;i<N;i++)p.g[i]=rg(i);p.out=NI+N-1;}
    int pe,pa,pm;eval(p,pe,pa,pm);
    if(restarts==0){printf("start seeded=%d err=%d act=%d mix=%d\n",(int)seed,pe,pa,pm);fflush(stdout);}
    long long budget=20000000LL<<(shard%5);
    for(long long j=0;j<budget;j++){
      C c=p;mutate(c);int e,a,m;eval(c,e,a,m);bool acc;
      if(pe==0){
        if(e)acc=false;else{int score=a+(3-m),ps=pa+(3-pm);acc=score<=ps||rnd()%(shard%2?3000:100000)==0&&score<=ps+1;}
      }else{acc=e<pe||(e==pe&&a<=pa+1);if(!acc&&rnd()%100000==0&&e<=pe+2)acc=true;}
      if(acc){p=c;pe=e;pa=a;pm=m;}
      if(e==0){
        int score=a+(3-m);
        if(score<best){best=score;printf("best score=%d size=%d mix=%d\n",score,a,m);fflush(stdout);if(a<=22)dump(c,a,m);}
        if(a<=21&&m>=3){dump(c,a,m);if(++found>=3)return 0;}
      }
      if((j&0xfffff)==0&&difftime(time(0),t0)>=secs)break;
    }
    restarts++;
  }
  printf("done restarts=%d best=%d\n",restarts,best);
}
