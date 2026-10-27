// probSAT (break-only, exponential) for k-SAT. usage: probsat cnf seed cb seconds [initfile]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
static unsigned long long rs;
static inline unsigned long long rnd(){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static inline double rndf(){return (rnd()>>11)*(1.0/9007199254740992.0);}
int main(int argc,char**argv){
  if(argc<5){fprintf(stderr,"usage\n");return 2;}
  FILE*f=fopen(argv[1],"r"); int V,M; char buf[256];
  while(fgets(buf,256,f)){ if(buf[0]=='p'){sscanf(buf,"p cnf %d %d",&V,&M);break;} }
  int K=5; int *cl=malloc(sizeof(int)*M*8); int *len=calloc(M,sizeof(int)); int m=0,x,pos=0;
  int *start=malloc(sizeof(int)*(M+1));
  start[0]=0;
  while(m<M && fscanf(f,"%d",&x)==1){ if(x==0){m++;start[m]=pos;} else {cl[pos++]=x;len[m]++;} }
  fclose(f);
  rs=strtoull(argv[2],0,10)*2654435761ULL+12345; double cb=atof(argv[3]); double T=atof(argv[4]);
  // occurrence lists
  int *occn=calloc(2*V+2,sizeof(int));
  for(int c=0;c<M;c++)for(int j=start[c];j<start[c+1];j++){int l=cl[j];occn[l>0?2*l:2*(-l)+1]++;}
  int **occ=malloc(sizeof(int*)*(2*V+2)); int *oc=calloc(2*V+2,sizeof(int));
  for(int i=0;i<2*V+2;i++)occ[i]=malloc(sizeof(int)*(occn[i]+1));
  for(int c=0;c<M;c++)for(int j=start[c];j<start[c+1];j++){int l=cl[j];int id=l>0?2*l:2*(-l)+1;occ[id][oc[id]++]=c;}
  char *a=malloc(V+1);
  if(argc>5){FILE*g=fopen(argv[5],"r"); if(g){ for(int i=0;i<V;i++){int ch=fgetc(g); a[i+1]=(ch=='1');} fclose(g);} else for(int i=1;i<=V;i++)a[i]=rnd()&1;}
  else for(int i=1;i<=V;i++)a[i]=rnd()&1;
  int *nt=calloc(M,sizeof(int)); int *crit=calloc(M,sizeof(int)); int *br=calloc(V+1,sizeof(int));
  int *un=malloc(sizeof(int)*M); int *wh=malloc(sizeof(int)*M); int nu=0;
  double pb[64]; for(int i=0;i<64;i++)pb[i]=pow(cb,-i);
  for(int c=0;c<M;c++){ for(int j=start[c];j<start[c+1];j++){int l=cl[j]; if((l>0)==a[abs(l)]){nt[c]++;crit[c]^=abs(l);} }
    if(nt[c]==0){wh[c]=nu;un[nu++]=c;} else if(nt[c]==1) br[crit[c]]++; }
  clock_t t0=clock(); long long flips=0; int best=nu;
  double prob[16]; int cand[16];
  while(nu>0){
    if((flips&0xFFFF)==0){ double el=(double)(clock()-t0)/CLOCKS_PER_SEC; if(el>T)break; if(nu<best)best=nu; if((flips&0xFFFFFF)==0)fprintf(stderr,"flips=%lld unsat=%d best=%d t=%.0f\n",flips,nu,best,el);}
    int c=un[rnd()%nu]; double s=0; int n=0;
    for(int j=start[c];j<start[c+1];j++){int v=abs(cl[j]); cand[n]=v; int b=br[v]; prob[n]=b<64?pb[b]:0; s+=prob[n]; n++;}
    double r=rndf()*s; int k=0; for(;k<n-1;k++){r-=prob[k]; if(r<=0)break;}
    int v=cand[k]; flips++;
    // flip v: literal that becomes true
    int tl = a[v]? -v : v; a[v]=!a[v];
    int idT = tl>0?2*tl:2*(-tl)+1; int fl=-tl; int idF = fl>0?2*fl:2*(-fl)+1;
    for(int i=0;i<occn[idT];i++){int d=occ[idT][i]; nt[d]++;
      if(nt[d]==1){ int u=wh[d]; un[u]=un[--nu]; wh[un[u]]=u; br[v]++; crit[d]=v; }
      else if(nt[d]==2){ br[crit[d]]--; crit[d]^=v; }
      else crit[d]^=v; }
    for(int i=0;i<occn[idF];i++){int d=occ[idF][i]; nt[d]--;
      if(nt[d]==0){ wh[d]=nu; un[nu++]=d; br[v]--; crit[d]=0; }
      else if(nt[d]==1){ crit[d]^=v; br[crit[d]]++; }
      else crit[d]^=v; }
  }
  if(nu==0){ for(int i=1;i<=V;i++)putchar(a[i]?'1':'0'); putchar('\n'); fprintf(stderr,"SOLVED flips=%lld\n",flips); return 0;}
  fprintf(stderr,"fail best=%d\n",best); return 1;
}
