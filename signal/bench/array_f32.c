// Same algorithm as ica.bend: interleaved key/payload float array, heapsort, enum, two-pass Pearson.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
static uint32_t lcg(uint32_t s){return s*1664525u+1013904223u;}
static float unif(uint32_t s){return (float)(s>>8)/16777216.0f;}
static void swp(float*a,uint32_t i,uint32_t m){float k=a[2*i],p=a[2*i+1];a[2*i]=a[2*m];a[2*i+1]=a[2*m+1];a[2*m]=k;a[2*m+1]=p;}
static void sift(float*a,uint32_t i,uint32_t n){for(;;){uint32_t l=2*i+1,r=l+1,m=i;float k=a[2*i];
  if(l<n&&a[2*l]>k){m=l;k=a[2*l];} if(r<n&&a[2*r]>k)m=r; if(m==i)return; swp(a,i,m); i=m;}}
static void hsort(float*a,uint32_t n){for(int i=n/2-1;i>=0;i--)sift(a,i,n);for(uint32_t e=n-1;e>0;e--){swp(a,0,e);sift(a,0,e);}}
static void en(float*a,uint32_t n){for(uint32_t k=0;k<n;k++){a[2*k]=a[2*k+1];a[2*k+1]=(float)k;}}
static float pearson(float*a,uint32_t n){float sa=0,sb=0;for(uint32_t k=0;k<n;k++){sa+=a[2*k];sb+=a[2*k+1];}
  float ma=sa/n,mb=sb/n,saa=0,sbb=0,sab=0;for(uint32_t k=0;k<n;k++){float da=a[2*k]-ma,db=a[2*k+1]-mb;saa+=da*da;sbb+=db*db;sab+=da*db;}
  return sab/sqrtf(saa*sbb);}
int main(int c,char**v){uint32_t T=atoi(v[1]),N=atoi(v[2]);float*P=malloc(sizeof(float)*2048*T);float*ic=malloc(sizeof(float)*T);
  struct timespec t0,t1;clock_gettime(CLOCK_MONOTONIC,&t0);uint32_t s=12345;
  for(uint32_t t=0;t<T;t++){s=lcg(s*2654435761u+7);uint32_t z=s;float*a=P+2048*t;
    for(uint32_t k=0;k<N;k++){uint32_t s1=lcg(z),s2=lcg(s1);float x=unif(s1)-0.5f,e=unif(s2)-0.5f;a[2*k]=x;a[2*k+1]=0.1f*x+e;z=s2;}}
  for(uint32_t t=0;t<T;t++){float*a=P+2048*t;hsort(a,N);en(a,N);hsort(a,N);en(a,N);ic[t]=pearson(a,N);}
  float m=0;for(uint32_t t=0;t<T;t++)m+=ic[t];m/=T;float ss=0;for(uint32_t t=0;t<T;t++)ss+=(ic[t]-m)*(ic[t]-m);float sd=sqrtf(ss/(T-1));
  clock_gettime(CLOCK_MONOTONIC,&t1);
  printf("ic=%.8f sd=%.8f t=%.5f gen+ic_ms=%.0f\n",m,sd,m/sd*sqrtf(T),(t1.tv_sec-t0.tv_sec)*1e3+(t1.tv_nsec-t0.tv_nsec)/1e6);}
