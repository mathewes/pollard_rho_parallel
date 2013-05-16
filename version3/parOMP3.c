#include<stdio.h>
#include<pari/pari.h>
#include<string.h>
#include<stdlib.h>
#include<omp.h>
void init(long prec);
void init_configure(long prec);
void thread(int id);

static GEN n;static GEN E;static GEN Q;static GEN L;
static GEN a;static GEN b;static GEN R;static GEN avec;
static GEN p;static GEN P;static GEN st;

#define LESLEN 4
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
omp_lock_t lock;
#define input0() gp_read_stream(stdin)
 
int flag;
void
init(long prec)	  /* void */
{
  pari_sp ltop = avma;
  init_configure(prec);
  memset(hash,-1,HASHLEN*sizeof(int));
  memset(points,-1,sizeof(POINT)*POINTNUM);
  oldN=0;st = stoi(gettime());flag=0;
  thread(0);printf("END");
  gerepileall(ltop, 0);
  return;	
}

//GEN long*
void
init_configure(long prec)	  /* void */
{
  pari_sp ltop = avma;

  //init the vector
  avec = cgetg(6, t_VEC);
  gel(avec, 1) = input0();gel(avec, 2) = input0();gel(avec, 3) = input0();
  gel(avec, 4) = input0();gel(avec, 5) = input0();
  
  p = input0();n=input0();
  P = cgetg(3, t_VEC);
  gel(P, 1) = input0();
  gel(P, 2) = input0();
  
  Q = cgetg(3, t_VEC);
  gel(Q, 1) = input0();
  gel(Q, 2) = input0();
  
  L = input0();
  E=ellinit(gmul(avec,gmodulsg(1,p)),prec);
  a = cgetg(gtos(L)+1, t_VEC);
   
  b = cgetg(gtos(L)+1, t_VEC);
  R = cgetg(gtos(L)+1, t_VEC);
  pari_sp btop = avma, st_lim = stack_lim(btop, 1);
  GEN i;
  for (i = gen_1; gcmp(i, L) <= 0; i = gaddgs(i, 1))
  {
      gel(a, gtos(i)) = lift(gmul(genrand(NULL), gmodulsg(1, n)));
      gel(b, gtos(i)) = lift(gmul(genrand(NULL), gmodulsg(1, n)));
      gel(R, gtos(i)) = addell(E, powell(E, P, gel(a, gtos(i))), powell(E, Q, gel(b, gtos(i))));
      if (low_stack(st_lim, stack_lim(btop, 1)))
        gerepileall(btop, 4, &a, &b, &R, &i);
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
  c = lift(gmul(genrand(NULL), gmodulsg(1, n)));
  d = lift(gmul(genrand(NULL), gmodulsg(1, n)));
  X = addell(E,powell(E, P, c), powell(E, Q, d));
  pari_printf("%d--%Ps %Ps %Ps\n",id,X,c,d);
  
  pari_sp btop = avma, st_lim = stack_lim(btop, 1);
  POINT tmp;
  while (!flag)
  {
      GEN tmp1=lift(gel(X,1));GEN tmp2=lift(gel(X,2));

    	char*x11=GENtostr(tmp1);char*x22=GENtostr(tmp2);
    	char*c11=GENtostr(c);char*d11=GENtostr(d);
    	
      strcpy(tmp.xP,x11);strcpy(tmp.yP,x22);
    	strcpy(tmp.cX,c11);strcpy(tmp.dX,d11);
    	
      free(x11);free(x22);free(c11);free(d11);
    	
      int len=strlen(tmp.xP);
  	  /*if(len>LESLEN)
  	  {
  	    int i1;
  	    for(i1=1;i1<=LESLEN;i1++)
      		if(tmp.xP[len-i1]!='0')
      		  break;
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
      		strcpy(points[oldN].xP,tmp.xP);strcpy(points[oldN].yP,tmp.yP);
          strcpy(points[oldN].cX,tmp.cX);strcpy(points[oldN].dX,tmp.dX);
          points[oldN].next=hash[hav];
      		hash[hav]=oldN;
      		oldN++;
      		if(oldN%1000==0)
      			printf("%d\n",oldN);
      		omp_unset_lock(&lock);
  	    }
  	  }*/
    	j = gaddgs(lift(gmul(tmp1), gmodulsg(1, L))), 1);
    	X = addell(E,X,gel(R,gtos(j)));     	
    	c = lift(gmul(gadd(c, gel(a, gtos(j))), gmodulsg(1, n)));
    	d = lift(gmul(gadd(d, gel(b, gtos(j))), gmodulsg(1, n)));
    	if (low_stack(st_lim, stack_lim(btop, 1)))
    	  gerepileall(btop, 4, &X, &c, &d, &j);
  }
  gerepileall(btop, 0);
  return;
}

int main()
{
  pari_init(1000000,100);
  init(10);
  pari_close();
  return 0;
}
