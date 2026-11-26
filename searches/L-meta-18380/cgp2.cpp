#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <ctime>
#include <set>
#include <string>
typedef uint64_t u64;
const int NI=7,N=40,W=NI+N;
struct G{int op,a,b;};            // 0 and, 1 or, 2 not
struct C{G g[N];int out;};
static u64 st;
static inline u64 rnd(){st^=st<<13;st^=st>>7;st^=st<<17;return st;}
u64 IN[NI][2],T[2];
static void eval(const C&c,int&err,int&act,bool&notg){
  bool use[W]={0};use[c.out]=1;act=0;notg=0;bool bad=0;
  for(int i=N-1;i>=0;i--)if(use[NI+i]){act++;const G&g=c.g[i];use[g.a]=1;
    if(g.op!=2)use[g.b]=1; else if(g.a>=NI){ if(c.g[g.a-NI].op==2)bad=1; else notg=1;}}
  u64 v[W][2];
  for(int i=0;i<NI;i++){v[i][0]=IN[i][0];v[i][1]=IN[i][1];}
  for(int i=0;i<N;i++)if(use[NI+i]){const G&g=c.g[i];
    for(int k=0;k<2;k++)v[NI+i][k]= g.op==0?(v[g.a][k]&v[g.b][k]):g.op==1?(v[g.a][k]|v[g.b][k]):~v[g.a][k];}
  err=__builtin_popcountll(v[c.out][0]^T[0])+__builtin_popcountll(v[c.out][1]^T[1]);
  if(bad)err+=1000;
}
static G rg(int i){int o=rnd()%16; o=o<7?0:o<14?1:2; return G{o,(int)(rnd()%(NI+i)),(int)(rnd()%(NI+i))};}
static void mutate(C&c){
  int k=1+rnd()%4;
  while(k--){
    int r=rnd()%100;
    if(r<3){c.out=NI+rnd()%N;continue;}
    int i=rnd()%N;
    if(r<45){ if(rnd()&1)c.g[i].a=rnd()%(NI+i);else c.g[i].b=rnd()%(NI+i);}
    else if(r<60){int o=rnd()%16;c.g[i].op=o<7?0:o<14?1:2;}
    else if(r<75){c.g[i]=rg(i);}
    else if(r<90){ // redirect one use of a wire to another earlier wire
      if(i==0)continue; int j=rnd()%i; int w=NI+j;
      for(int t=j+1;t<N;t++){ if(c.g[t].a==NI+i && w<NI+t && (rnd()&1))c.g[t].a=w; }
    } else { // splice: new node feeding an existing use
      int t=rnd()%N; if(t<=i)continue; if(rnd()&1){c.g[i].a=c.g[t].a<NI+i?c.g[t].a:c.g[i].a;c.g[t].a=NI+i;}else{c.g[i].b=c.g[t].b<NI+i?c.g[t].b:c.g[i].b;c.g[t].b=NI+i;}
    }
  }
}
#include "seeds.h"
static C seeded(){
  const int NS=sizeof(SEEDS)/sizeof(SEEDS[0]);const int(*L)[3]=SEEDS[rnd()%NS];
  C c;int pos[20];for(int i=0;i<N;i++)c.g[i]=rg(i);
  int slot=0;for(int k=0;k<20;k++){int left=20-k,room=N-slot;int skip=rnd()%(room-left+1); if(skip>2)skip=rnd()%3; slot+=skip;pos[k]=slot++;}
  auto w=[&](int x){return x<7?x:NI+pos[x-7];};
  for(int k=0;k<20;k++)c.g[pos[k]]=G{L[k][0],w(L[k][1]),w(L[k][2])};
  c.out=NI+pos[19];return c;
}
static void dump(const C&c,int act,bool notg){
  bool use[W]={0};use[c.out]=1;for(int i=N-1;i>=0;i--)if(use[NI+i]){use[c.g[i].a]=1;if(c.g[i].op!=2)use[c.g[i].b]=1;}
  int id[W];for(int i=0;i<NI;i++)id[i]=i;int n=0;std::string s;char buf[64];
  for(int i=0;i<N;i++)if(use[NI+i]){id[NI+i]=NI+n++;const G&g=c.g[i];
    if(g.op==2)snprintf(buf,64,"not %d;",id[g.a]);else snprintf(buf,64,"%s %d %d;",g.op?"or":"and",id[g.a],id[g.b]);s+=buf;}
  printf("FOUND size=%d notgate=%d out=%d : %s\n",act,(int)notg,id[c.out],s.c_str());fflush(stdout);
}
int main(int argc,char**argv){
  int shard=atoi(argv[1]);double secs=atof(argv[2]);
  st=0x9E3779B97F4A7C15ULL*(shard+1)^(u64)time(0);for(int i=0;i<20;i++)rnd();
  for(int x=0;x<128;x++){for(int i=0;i<NI;i++)if(x>>i&1)IN[i][x/64]|=1ULL<<(x%64);if(__builtin_popcount(x)>=4)T[x/64]|=1ULL<<(x%64);}
  bool seed=true;
  time_t t0=time(0);int found=0,best=99,bestm=99,printed=0;long long it=0,restarts=0;
  while(difftime(time(0),t0)<secs){
    C p=seed?seeded():C(); if(!seed){for(int i=0;i<N;i++)p.g[i]=rg(i);p.out=NI+N-1;}
    int pe,pa;bool pn;eval(p,pe,pa,pn);
    if(seed&&restarts==0)printf("seed err=%d act=%d\n",pe,pa),fflush(stdout);
    long long budget=20000000LL<<(shard%4);
    for(long long j=0;j<budget;j++,it++){
      C c=p;mutate(c);int e,a;bool n;eval(c,e,a,n);
      int cap = shard%3==0 ? 21 : (rnd()%(shard%3==1?100000:2000)==0?22:(pa>21?pa:21));
      bool acc = e==0 && a<=cap;
      if(acc && a>pa && a==21 && rnd()%4) acc=0;
      if(acc && pn && !n && rnd()%50) acc=0;
      if(acc){p=c;pe=e;pa=a;pn=n;}
      if(e==0){
        if(a<best){best=a;printf("best correct=%d notgate=%d it=%lld\n",a,(int)n,it);fflush(stdout);}
        if(a<=21&&n){dump(c,a,n);if(++found>=3)return 0;}
        else if(a<20&&!n&&(a<bestm||printed<3)){bestm=a;printed++;dump(c,a,n);}
      }
      if((j&0xfffff)==0 && difftime(time(0),t0)>=secs)break;
    }
    restarts++;
  }
  printf("done it=%lld restarts=%lld best=%d\n",it,restarts,best);
}
