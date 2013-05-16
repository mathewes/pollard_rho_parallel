#include<stdio.h>
#include<omp.h>
#include<pari/pari.h>
#include<string.h>
#include<stdlib.h>
void init_11(long prec);
void init_configure(long prec);
void thread(int id);

static GEN n;
static GEN E;
static GEN Q;
static GEN L;
static GEN a;
static GEN b;
static GEN R;
static GEN avec;
static GEN p;
static GEN P;
static GEN st;

#define THRDNUM 3
#define LESLEN 2
#define CALEN 30
#define POINTNUM 1000000
#define HSB 5
#define HASHLEN 100000

typedef struct POINT{
  char xP[CALEN];char yP[CALEN];
  char cX[CALEN];char dX[CALEN];
  int next;
}POINT;

POINT points[POINTNUM];
int oldN;
int hash[HASHLEN];

#define input0() gp_read_stream(stdin)
int flag=0;omp_lock_t lock;
void print23(int id,int val)
{
printf("%d---%d\n",id,val);
}
void
init_11(long prec)	  /* void */
{
  pari_sp ltop = avma;
  init_configure(prec);

  omp_set_num_threads(THRDNUM);
  struct pari_thread pth[THRDNUM];
  int i;omp_init_lock(&lock);
  memset(hash,-1,HASHLEN*sizeof(int));
  memset(points,-1,sizeof(POINT)*POINTNUM);
  oldN=0;
  st = stoi(gettime());
  flag=0;
  for (i = 1; i < THRDNUM; i++) 
    pari_thread_alloc(&pth[i],400000,NULL);
#pragma omp parallel
  {
    int this_th = omp_get_thread_num();
    if (this_th)
      pari_thread_start(&pth[this_th]);
    int k;
#pragma omp for
  for(k=0;k<THRDNUM;k++)
	if(this_th)
		thread(this_th);
	else
		while(!flag);  
  if (this_th) 
      pari_thread_close();
  }
  printf("END");
  gerepileall(ltop, 10, &n, &E, &Q, &L, &a, &b, &R, &avec, &p, &P);
  return;	
}


void
init_configure(long prec)	  /* void */
{
  pari_sp ltop = avma;
  GEN p1 = gen_0, p2 = gen_0, p3 = gen_0, p7 = gen_0, p8 = gen_0, p9 = gen_0;
  {
    long l10;
    p1 = cgetg(6, t_VEC);
    for (l10 = 1; l10 <= 5; ++l10)
      gel(p1, l10) = gen_0;
  }
  avec = p1;
  gel(avec, 1) = input0();
  gel(avec, 2) = input0();
  gel(avec, 3) = input0();
  gel(avec, 4) = input0();
  gel(avec, 5) = input0();
  p = input0();
  {
    long l11;
    p2 = cgetg(3, t_VEC);
    for (l11 = 1; l11 <= 2; ++l11)
      gel(p2, l11) = gen_0;
  }
 // n=input0();
  P = p2;
  gel(P, 1) = input0();
  gel(P, 2) = input0();
  {
    long l12;
    p3 = cgetg(3, t_VEC);
    for (l12 = 1; l12 <= 2; ++l12)
      gel(p3, l12) = gen_0;
  }
  Q = p3;
  gel(Q, 1) = input0();
  gel(Q, 2) = input0();
  L = input0();
  E=ellinit(gmul(avec,gmodulsg(1,p)),prec);
  n=ellorder(E,P,NULL);
  pari_printf("1\n");
 {
    long l16;
    p7 = cgetg(gtos(L)+1, t_VEC);
    for (l16 = 1; gcmpsg(l16, L) <= 0; ++l16)
      gel(p7, l16) = gen_0;
  }
  a = p7;
  {
    long l17;
    p8 = cgetg(gtos(L)+1, t_VEC);
    for (l17 = 1; gcmpsg(l17, L) <= 0; ++l17)
      gel(p8, l17) = gen_0;
  }
  b = p8;
  {
    long l18;
    p9 = cgetg(gtos(L)+1, t_VEC);
    for (l18 = 1; gcmpsg(l18, L) <= 0; ++l18)
      gel(p9, l18) = gen_0;
  }
  R = p9;
  {
    pari_sp btop = avma, st_lim = stack_lim(btop, 1);
    GEN i = gen_0;
    for (i = gen_1; gcmp(i, L) <= 0; i = gaddgs(i, 1))
    {
      gel(a, gtos(i)) = lift(gmul(genrand(NULL), gmodulsg(1, n)));
      gel(b, gtos(i)) = lift(gmul(genrand(NULL), gmodulsg(1, n)));
      gel(R, gtos(i)) = addell(E, powell(E, P, gel(a, gtos(i))), powell(E, Q, gel(b, gtos(i))));
      if (low_stack(st_lim, stack_lim(btop, 1)))
        gerepileall(btop, 4, &a, &b, &R, &i);
    }
  }
  gerepileall(ltop, 10, &n, &E, &Q, &L, &a, &b, &R, &avec, &p, &P);
  return;
}


int getVal(char*str)
{
	int len=strlen(str);
	int val=0;
	len=len-LESLEN;
	int mx=len>HSB?HSB:len;
	int i;int st2=len-mx;
	for(i=0;i<mx;i++)
		val=val*10+str[st2+i]-'0';
	return val;
}	

void thread(int id)
{
  GEN X,c,d,j;
  setrand(stoi(id));
  c = lift(gmul(genrand(NULL), gmodulsg(1, n)));
  d = lift(gmul(genrand(NULL), gmodulsg(1, n)));
  X = addell(E,powell(E, P, c), powell(E, Q, d));
  pari_printf("%d--%Ps %Ps %Ps\n",id,X,c,d);
  pari_sp ltop = avma;
  {
    pari_sp btop = avma, st_lim = stack_lim(btop, 1);
    POINT tmp;
    while (!flag)
      {
	char*x11=GENtostr(lift(gel(X,1)));
	char*x22=GENtostr(lift(gel(X,2)));
	char*c11=GENtostr(c);
	char*d11=GENtostr(d);
	strcpy(tmp.xP,x11);
	strcpy(tmp.yP,x22);
	strcpy(tmp.cX,c11);
	strcpy(tmp.dX,d11);
	free(x11);free(x22);free(c11);free(d11);
	int len=strlen(tmp.xP);
	if(len>LESLEN)
	  {
	    int i1;
	    for(i1=1;i1<=LESLEN;i1++)
	      {
		if(tmp.xP[len-i1]!='0')
		  break;
	      }
	    if(i1>LESLEN)
	      {
		omp_set_lock(&lock);
		if(flag==1)
		  break;
		int hav=getVal(tmp.xP);
		if(hash[hav]!=-1)
		{
			int now=hash[hav];
			while(now!=-1)
			{
				if(strcmp(points[now].xP,tmp.xP)==0&&strcmp(points[now].yP,tmp.yP)==0)
                      		{
                        	GEN c1=readseq(points[now].cX);GEN d1=readseq(points[now].dX);
                        	GEN c2=readseq(tmp.cX);GEN d2=readseq(tmp.dX);
                        	if (gequal(d1,d2))
                         		 pari_printf("failure\n");
                        	else
                          		pari_printf("%Ps\n", lift(gmul(gdiv(gsub(c1,c2), gsub(d2, d1)), gmodulsg(1, n))));
                        	flag=1;
                        	pari_printf("%Psms\n", gsubsg(gettime(), st));
                        	break;
                      		}
				else
					now=points[now].next;

			}
			if(now!=-1)
			{
			        omp_unset_lock(&lock);
				break;
			}		
		}
		strcpy(points[oldN].xP,tmp.xP);
                strcpy(points[oldN].yP,tmp.yP);
                strcpy(points[oldN].cX,tmp.cX);
                strcpy(points[oldN].dX,tmp.dX);
               	points[oldN].next=hash[hav];
		hash[hav]=oldN;
		oldN++;
		if(oldN%1000==0)
			printf("%d\n",oldN);
		omp_unset_lock(&lock);
	      }
	  }
	j = gaddgs(lift(gmul(lift(gel(X, 1)), gmodulsg(1, L))), 1);
	X = addell(E,X,gel(R,gtos(j)));     	
	c = lift(gmul(gadd(c, gel(a, gtos(j))), gmodulsg(1, n)));
	d = lift(gmul(gadd(d, gel(b, gtos(j))), gmodulsg(1, n)));
	if (low_stack(st_lim, stack_lim(btop, 1)))
	  gerepileall(btop, 4, &X, &c, &d, &j);
      }
  }
  gerepileall(ltop, 4, &X, &c, &d,&j);
  return;
}

int main()
{
pari_init(1000000,100);
init_11(10);
pari_close();
return 0;
}
