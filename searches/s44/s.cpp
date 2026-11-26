// s <mask> <gates> <shard> <seconds> : stochastic search (neutral drift) for an AND/OR/NOT circuit
// representing a 4x4 bipartite graph on the 16 one-vertex-per-side inputs.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <ctime>
static uint64_t S;
static inline uint32_t rnd(uint32_t n){S^=S<<13;S^=S>>7;S^=S<<17;return (uint32_t)((S>>11)%n);}
struct G{int op,a,b;};
int main(int argc,char**argv){
  int mask=atoi(argv[1]),N=atoi(argv[2]),shard=atoi(argv[3]),secs=atoi(argv[4]);
  S=0x9E3779B97F4A7C15ULL*(shard+1)^(uint64_t)time(0);
  uint16_t in[8]={0},T=(uint16_t)mask;
  for(int u=0;u<4;u++)for(int v=0;v<4;v++){int r=4*u+v;in[u]|=1<<r;in[4+v]|=1<<r;}
  time_t t0=time(0);long long restarts=0;int best=99;
  while(time(0)-t0<secs){
    restarts++;
    int M=N+(shard%3)*3;              // extra inactive slots help drift; only active gates are limited to N
    G c[32];int out;
    auto rg=[&](int i){int op=rnd(10)==0?2:(int)rnd(2);return G{op,(int)rnd(8+i),(int)rnd(8+i)};};
    for(int i=0;i<M;i++)c[i]=rg(i);
    out=8+rnd(M);
    auto score=[&](G*g,int&o)->int{
      uint16_t w[40];memcpy(w,in,sizeof in);bool use[40]={0};
      for(int i=0;i<M;i++){uint16_t x=w[g[i].a],y=w[g[i].b];w[8+i]=g[i].op==0?(x&y):g[i].op==1?(x|y):(uint16_t)~x;}
      int bs=-1,bo=o;
      for(int k=0;k<8+M;k++){int e=16-__builtin_popcount((uint16_t)(w[k]^T));if(e>bs||(e==bs&&k==o)){bs=e;bo=k;}}
      o=bo;use[o]=1;int act=0;
      for(int i=M-1;i>=0;i--)if(use[8+i]){act++;use[g[i].a]=1;if(g[i].op!=2)use[g[i].b]=1;}
      if(act>N)return -100-act;
      return bs*100-act;
    };
    int cur=score(c,out);
    for(long it=0;it<400000;it++){
      G d[32];memcpy(d,c,sizeof(G)*M);int o=out;
      int nm=1+rnd(3);
      for(int k=0;k<nm;k++){int i=rnd(M);int r=rnd(10);
        if(r<3)d[i]=rg(i);else if(r<6)d[i].a=rnd(8+i);else if(r<9)d[i].b=rnd(8+i);else d[i].op=rnd(10)<2?2:(int)rnd(2);}
      if(rnd(10)==0)o=8+rnd(M);
      int s=score(d,o);
      bool take = s/100>=cur/100 ? (s>-100) : rnd(20000)==0&&s>-100;
      if(take){memcpy(c,d,sizeof(G)*M);out=o;cur=s;}
      if(s>-100&&(s+99)/100>=16&&s>=1500){
        int sc=(s+99)/100;
        if(sc==16){
          uint16_t w[40];memcpy(w,in,sizeof in);
          for(int i=0;i<M;i++){uint16_t x=w[d[i].a],y=w[d[i].b];w[8+i]=d[i].op==0?(x&y):d[i].op==1?(x|y):(uint16_t)~x;}
          if(w[o]!=T)continue;
          bool use[40]={0};use[o]=1;
          for(int i=M-1;i>=0;i--)if(use[8+i]){use[d[i].a]=1;if(d[i].op!=2)use[d[i].b]=1;}
          int id[40];for(int k=0;k<8;k++)id[k]=k;int n=0;
          printf("FOUND restarts=%lld : ",restarts);
          for(int i=0;i<M;i++)if(use[8+i]){id[8+i]=8+n;n++;
            if(d[i].op==2)printf("not %d;",id[d[i].a]);else printf("%s %d %d;",d[i].op?"or":"and",id[d[i].a],id[d[i].b]);}
          printf(" size=%d out=%d\n",n,id[o]);return 0;
        }
      }
      int e=(cur+99)/100; if(16-e<best){best=16-e;printf("wrong %d\n",best);fflush(stdout);}
    }
  }
  printf("done restarts=%lld best_wrong=%d\n",restarts,best);
}
