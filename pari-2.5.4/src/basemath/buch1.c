/* $Id$

Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */
#include "pari.h"
#include "paripriv.h"

/*******************************************************************/
/*                                                                 */
/*         CLASS GROUP AND REGULATOR (McCURLEY, BUCHMANN)          */
/*                   QUADRATIC FIELDS                              */
/*                                                                 */
/*******************************************************************/
/* For largeprime() hashtable. Note that hashed pseudoprimes are odd (unless
 * 2 | index), hence the low order bit is not useful. So we hash
 * HASHBITS bits starting at bit 1, not bit 0 */
#define HASHBITS 10
static const long HASHT = 1L << HASHBITS;

static long
hash(long q) { return (q & ((1L << (HASHBITS+1)) - 1)) >> 1; }
#undef HASHBITS

/* See buch2.c:
 * B->subFB contains split p such that \prod p > sqrt(B->Disc)
 * B->powsubFB contains powers of forms in B->subFB */
#define RANDOM_BITS 4
static const long CBUCH = (1L<<RANDOM_BITS)-1;

struct buch_quad
{
  ulong limhash;
  long KC, KC2, PRECREG;
  long *primfact, *exprimfact, **hashtab;
  GEN FB, numFB;
  GEN powsubFB, vperm, subFB, badprim;
  struct qfr_data *QFR;
};

/*******************************************************************/
/*                                                                 */
/*  Routines related to binary quadratic forms (for internal use)  */
/*                                                                 */
/*******************************************************************/
/* output canonical representative wrt projection Cl^+ --> Cl (a > 0) */
static GEN
qfr3_canon(GEN x, struct qfr_data *S)
{
  GEN a = gel(x,1), c = gel(x,3);
  if (signe(a) < 0) {
    if (absi_equal(a,c)) return qfr3_rho(x, S);
    setsigne(a, 1);
    setsigne(c,-1);
  }
  return x;
}
static GEN
qfr3_canon_safe(GEN x, struct qfr_data *S)
{
  GEN a = gel(x,1), c = gel(x,3);
  if (signe(a) < 0) {
    if (absi_equal(a,c)) return qfr3_rho(x, S);
    gel(x,1) = negi(a);
    gel(x,3) = negi(c);
  }
  return x;
}
static GEN
qfr5_canon(GEN x, struct qfr_data *S)
{
  GEN a = gel(x,1), c = gel(x,3);
  if (signe(a) < 0) {
    if (absi_equal(a,c)) return qfr5_rho(x, S);
    setsigne(a, 1);
    setsigne(c,-1);
  }
  return x;
}
static GEN
QFR5_comp(GEN x,GEN y, struct qfr_data *S)
{ return qfr5_canon(qfr5_comp(x,y,S), S); }
static GEN
QFR3_comp(GEN x, GEN y, struct qfr_data *S)
{ return qfr3_canon(qfr3_comp(x,y,S), S); }

/* compute rho^n(x) */
static GEN
qfr5_rho_pow(GEN x, long n, struct qfr_data *S)
{
  long i;
  pari_sp av = avma, lim = stack_lim(av, 1);
  for (i=1; i<=n; i++)
  {
    x = qfr5_rho(x,S);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"qfr5_rho_pow");
      x = gerepilecopy(av, x);
    }
  }
  return gerepilecopy(av, x);
}

static GEN
qfr5_pf(struct qfr_data *S, long p, long prec)
{
  GEN y = primeform_u(S->D,p);
  return qfr5_canon(qfr5_red(qfr_to_qfr5(y,prec), S), S);
}

static GEN
qfr3_pf(struct qfr_data *S, long p)
{
  GEN y = primeform_u(S->D,p);
  return qfr3_canon(qfr3_red(y, S), S);
}

#define qfi_pf primeform_u

/* Warning: ex[0] not set in general */
static GEN
init_form(struct buch_quad *B, GEN ex,
          GEN (*comp)(GEN,GEN,struct qfr_data *S))
{
  long i, l = lg(B->powsubFB);
  GEN F = NULL;
  for (i=1; i<l; i++)
    if (ex[i])
    {
      GEN t = gmael(B->powsubFB,i,ex[i]);
      F = F? comp(F, t, B->QFR): t;
    }
  return F;
}
static GEN
qfr5_factorback(struct buch_quad *B, GEN ex) { return init_form(B, ex, &QFR5_comp); }

static GEN
QFI_comp(GEN x, GEN y, struct qfr_data *S) { (void)S; return qficomp(x,y); }

static GEN
qfi_factorback(struct buch_quad *B, GEN ex) { return init_form(B, ex, &QFI_comp); }

static GEN
random_form(struct buch_quad *B, GEN ex,
            GEN (*comp)(GEN,GEN, struct qfr_data *S))
{
  long i, l = lg(ex);
  pari_sp av = avma;
  GEN F;
  for(;;)
  {
    for (i=1; i<l; i++) ex[i] = random_bits(RANDOM_BITS);
    if ((F = init_form(B, ex, comp))) return F;
    avma = av;
  }
}
static GEN
qfr3_random(struct buch_quad *B,GEN ex){ return random_form(B, ex, &QFR3_comp); }
static GEN
qfi_random(struct buch_quad *B,GEN ex) { return random_form(B, ex, &QFI_comp); }

/*******************************************************************/
/*                                                                 */
/*                     Common subroutines                          */
/*                                                                 */
/*******************************************************************/
double
check_bach(double cbach, double B)
{
  if (cbach >= B)
   pari_err(talker,"sorry, couldn't deal with this field. PLEASE REPORT");
  if (cbach <= 0.3)
    cbach *= 2;
  else
    cbach += 0.2;
  if (cbach > B) cbach = B;
  if (DEBUGLEVEL) err_printf("\n*** Bach constant: %f\n", cbach);
  return cbach;
}

/* Is |q| <= p ? */
static int
isless_iu(GEN q, ulong p) {
  long l = lgefint(q);
  return l==2 || (l == 3 && (ulong)q[2] <= p);
}

static long
factorquad(struct buch_quad *B, GEN f, long nFB, ulong limp)
{
  ulong X;
  long i, lo = 0;
  GEN x = gel(f,1), FB = B->FB, P = B->primfact, E = B->exprimfact;

  for (i=1; lgefint(x) > 3; i++)
  {
    ulong p = (ulong)FB[i], r;
    GEN q = diviu_rem(x, p, &r);
    if (!r)
    {
      long k = 0;
      do { k++; x = q; q = diviu_rem(x, p, &r); } while (!r);
      lo++; P[lo] = p; E[lo] = k;
    }
    if (isless_iu(q,p)) {
      if (lgefint(x) == 3) { X = (ulong)x[2]; goto END; }
      return 0;
    }
    if (i == nFB) return 0;
  }
  X = (ulong)x[2];
  if (X == 1) { P[0] = 0; return 1; }
  for (;; i++)
  { /* single precision affair, split for efficiency */
    ulong p = (ulong)FB[i];
    ulong q = X / p, r = X % p; /* gcc makes a single div */
    if (!r)
    {
      long k = 0;
      do { k++; X = q; q = X / p; r = X % p; } while (!r);
      lo++; P[lo] = p; E[lo] = k;
    }
    if (q <= p) break;
    if (i == nFB) return 0;
  }
END:
  if (X > B->limhash) return 0;
  if (X != 1 && X <= limp)
  {
    if (B->badprim && ugcd(X, umodiu(B->badprim,X)) > 1) return 0;
    lo++; P[lo] = X; E[lo] = 1;
    X = 1;
  }
  P[0] = lo; return X;
}

/* Check for a "large prime relation" involving q; q may not be prime */
static long *
largeprime(struct buch_quad *B, long q, GEN ex, long np, long nrho)
{
  const long hashv = hash(q);
  long *pt, i, l = lg(B->subFB);

  for (pt = B->hashtab[hashv]; ; pt = (long*) pt[0])
  {
    if (!pt)
    {
      pt = (long*) pari_malloc((l+3) * sizeof(long));
      *pt++ = nrho; /* nrho = pt[-3] */
      *pt++ = np;   /* np   = pt[-2] */
      *pt++ = q;    /* q    = pt[-1] */
      pt[0] = (long)B->hashtab[hashv];
      for (i=1; i<l; i++) pt[i]=ex[i];
      B->hashtab[hashv]=pt; return NULL;
    }
    if (pt[-1] == q) break;
  }
  for(i=1; i<l; i++)
    if (pt[i] != ex[i]) return pt;
  return (pt[-2]==np)? NULL: pt;
}

static void
clearhash(long **hash)
{
  long *pt;
  long i;
  for (i=0; i<HASHT; i++) {
    for (pt = hash[i]; pt; ) {
      void *z = (void*)(pt - 3);
      pt = (long*) pt[0]; pari_free(z);
    }
    hash[i] = NULL;
  }
}

/* p | conductor of order of disc D ? */
static int
is_bad(GEN D, ulong p)
{
  pari_sp av = avma;
  int r;
  if (p == 2)
  {
    r = mod16(D) >> 1;
    if (r && signe(D) < 0) r = 8-r;
    return (r < 4);
  }
  r = (remii(D, sqru(p)) == gen_0); /* p^2 | D ? */
  avma = av; return r;
}

/* create B->FB, B->numFB; set B->badprim. Return L(kro_D, 1) */
static GEN
FBquad(struct buch_quad *B, long C2, long C1, GRHcheck_t *S)
{
  GEN Res = real_1(DEFAULTPREC), D = B->QFR->D;
  double L = log((double)C2), SA = 0, SB = 0;
  long i, p, s, LIM;
  pari_sp av;
  byteptr d = diffptr;

  B->numFB = cgetg(C2+1, t_VECSMALL);
  B->FB    = cgetg(C2+1, t_VECSMALL);
  av = avma;
  B->KC = 0; i = 0;
  maxprime_check((ulong)C2);
  B->badprim = gen_1;
  for (p = 0;;) /* p <= C2 */
  {
    NEXT_PRIME_VIADIFF(p, d);
    if (!B->KC && p > C1) B->KC = i;
    if (p > C2) break;
    s = krois(D,p);
    if (s) Res = mulur(p, divru(Res, p - s));
    switch (s)
    {
      case -1: break; /* inert */
      case  0: /* ramified */
        if (is_bad(D, (ulong)p)) { B->badprim = muliu(B->badprim, p); break; }
        /* fall through */
      default:  /* split */
        i++; B->numFB[p] = i; B->FB[i] = p; break;
    }
    if (!S->checkok)
    {
      double logp = log((double)p);
      double logNP = s < 0? 2*logp: logp;
      double q = s < 0? 1/(double)p: 1/sqrt((double)p);
      double A = logNP * q, B = logNP * A;
      long M = (long)(L/logNP);
      if (M > 1)
      {
        double inv1_q = 1 / (1-q);
        A *= (1 - pow(q, M)) * inv1_q;
        B *= (1 - pow(q, M)*(M+1 - M*q)) * inv1_q * inv1_q;
      }
      if (s > 0) { SA += 2 * A; SB += 2 * B; } else { SA += A; SB += B; }
    }
  }
  if (!B->KC) return NULL;
  if (!GRHok(S, L, SA, SB)) return NULL;
  B->KC2 = i;
  setlg(B->FB, B->KC2+1);
  LIM = (expi(D) < 16)? 100: 1000;
  while (p < LIM)
  {
    s = krois(D,p);
    Res = mulur(p, divru(Res, p - s));
    NEXT_PRIME_VIADIFF(p, d);
  }
  if (B->badprim != gen_1)
    gerepileall(av, 2, &Res, &B->badprim);
  else
  {
    B->badprim = NULL;
    Res = gerepileuptoleaf(av, Res);
  }
  S->checkok = 1; return Res;
}

/* create B->vperm, return B->subFB */
static GEN
subFBquad(struct buch_quad *B, GEN D, double PROD)
{
  long i, j, minSFB, lgsub = 1, ino = 1, lv = B->KC+1;
  double prod = 1.;
  pari_sp av;
  GEN no;

  minSFB = (expi(D) > 15)? 3: 2;
  B->vperm = cgetg(lv, t_VECSMALL);
  av = avma;
  no    = cgetg(lv, t_VECSMALL);
  for (j = 1; j < lv; j++)
  {
    ulong p = B->FB[j];
    if (!umodiu(D, p)) no[ino++] = j; /* ramified */
    else
    {
      B->vperm[lgsub++] = j;
      prod *= p;
      if (lgsub > minSFB && prod > PROD) break;
    }
  }
  if (j == lv) return NULL;
  i = lgsub;
  for (j = 1; j < ino;i++,j++) B->vperm[i] = no[j];
  for (     ; i < lv; i++)     B->vperm[i] = i;
  no = gclone(vecslice(B->vperm, 1, lgsub-1));
  avma = av; return no;
}

/* assume n >= 1, x[i][j] = B->subFB[i]^j, for j = 1..n */
static GEN
powsubFBquad(struct buch_quad *B, long n)
{
  pari_sp av = avma;
  long i,j, l = lg(B->subFB);
  GEN F, y, x = cgetg(l, t_VEC), D = B->QFR->D;

  if (B->PRECREG) /* real */
  {
    for (i=1; i<l; i++)
    {
      F = qfr5_pf(B->QFR, B->FB[B->subFB[i]], B->PRECREG);
      y = cgetg(n+1, t_VEC); gel(x,i) = y;
      gel(y,1) = F;
      for (j=2; j<=n; j++) gel(y,j) = QFR5_comp(gel(y,j-1), F, B->QFR);
    }
  }
  else /* imaginary */
  {
    for (i=1; i<l; i++)
    {
      F = qfi_pf(D, B->FB[B->subFB[i]]);
      y = cgetg(n+1, t_VEC); gel(x,i) = y;
      gel(y,1) = F;
      for (j=2; j<=n; j++) gel(y,j) = qficomp(gel(y,j-1), F);
    }
  }
  x = gclone(x); avma = av; return x;
}

static void
sub_fact(struct buch_quad *B, GEN col, GEN F)
{
  GEN b = gel(F,2);
  long i;
  for (i=1; i<=B->primfact[0]; i++)
  {
    ulong p = B->primfact[i], k = B->numFB[p];
    long e = B->exprimfact[i];
    if (umodiu(b, p<<1) > p) e = -e;
    col[k] -= e;
  }
}
static void
add_fact(struct buch_quad *B, GEN col, GEN F)
{
  GEN b = gel(F,2);
  long i;
  for (i=1; i<=B->primfact[0]; i++)
  {
    ulong p = B->primfact[i], k = B->numFB[p];
    long e = B->exprimfact[i];
    if (umodiu(b, p<<1) > p) e = -e;
    col[k] += e;
  }
}

static GEN
get_clgp(struct buch_quad *B, GEN W, GEN *ptD, long prec)
{
  GEN res, init, u1, D = ZM_snf_group(W,NULL,&u1), Z = prec? real_0(prec): NULL;
  long i, j, l = lg(W), c = lg(D);

  res=cgetg(c,t_VEC); init = cgetg(l,t_VEC);
  for (i=1; i<l; i++) gel(init,i) = primeform_u(B->QFR->D, B->FB[B->vperm[i]]);
  for (j=1; j<c; j++)
  {
    GEN g = NULL;
    if (prec)
    {
      for (i=1; i<l; i++)
      {
        GEN t, u = gcoeff(u1,i,j);
        if (!signe(u)) continue;
        t = qfr3_pow(gel(init,i), u, B->QFR);
        g = g? qfr3_comp(g, t, B->QFR): t;
      }
      g = qfr3_to_qfr(qfr3_canon_safe(qfr3_red(g, B->QFR), B->QFR), Z);
    }
    else
    {
      for (i=1; i<l; i++)
      {
        GEN t, u = gcoeff(u1,i,j);
        if (!signe(u)) continue;
        t = powgi(gel(init,i), u);
        g = g? qficomp(g, t): t;
      }
    }
    gel(res,j) = g;
  }
  *ptD = D; return res;
}

static long
trivial_relations(struct buch_quad *B, GEN mat, GEN C)
{
  long i, j = 0;
  GEN col, D = B->QFR->D;
  for (i = 1; i <= B->KC; i++)
  { /* ramified prime ==> trivial relation */
    if (umodiu(D, B->FB[i])) continue;
    col = const_vecsmall(B->KC, 0);
    col[i] = 2; j++;
    gel(mat,j) = col;
    gel(C,j) = gen_0;
  }
  return j;
}

static void
dbg_all(pari_timer *T, const char *phase, long s, long n)
{
  err_printf("\n");
  timer_printf(T, "%s rel [#rel/#test = %ld/%ld]", phase,s,n);
}

/* Imaginary Quadratic fields */

static void
imag_relations(struct buch_quad *B, long need, long *pc, ulong LIMC, GEN mat)
{
  pari_timer T;
  long lgsub = lg(B->subFB), current = *pc, nbtest = 0, s = 0;
  long i, fpc;
  pari_sp av;
  GEN col, form, ex = cgetg(lgsub, t_VECSMALL);

  if (!current) current = 1;
  if (DEBUGLEVEL) timer_start(&T);
  av = avma;
  for(;;)
  {
    if (s >= need) break;
    avma = av;
    form = qfi_random(B,ex);
    form = qficomp(form, qfi_pf(B->QFR->D, B->FB[current]));
    nbtest++; fpc = factorquad(B,form,B->KC,LIMC);
    if (!fpc)
    {
      if (DEBUGLEVEL>1) err_printf(".");
      if ((nbtest & 0xff) == 0 && ++current > B->KC) current = 1;
      continue;
    }
    if (fpc > 1)
    {
      long *fpd = largeprime(B,fpc,ex,current,0);
      ulong b1, b2, p;
      GEN form2;
      if (!fpd)
      {
        if (DEBUGLEVEL>1) err_printf(".");
        continue;
      }
      form2 = qficomp(qfi_factorback(B,fpd), qfi_pf(B->QFR->D, B->FB[fpd[-2]]));
      p = fpc << 1;
      b1 = umodiu(gel(form2,2), p);
      b2 = umodiu(gel(form,2),  p);
      if (b1 != b2 && b1+b2 != p) continue;

      col = gel(mat,++s);
      add_fact(B,col, form);
      (void)factorquad(B,form2,B->KC,LIMC);
      if (b1==b2)
      {
        for (i=1; i<lgsub; i++) col[B->subFB[i]] += fpd[i]-ex[i];
        sub_fact(B, col, form2); col[fpd[-2]]++;
      }
      else
      {
        for (i=1; i<lgsub; i++) col[B->subFB[i]] += -fpd[i]-ex[i];
        add_fact(B, col, form2); col[fpd[-2]]--;
      }
    }
    else
    {
      col = gel(mat,++s);
      for (i=1; i<lgsub; i++) col[B->subFB[i]] = -ex[i];
      add_fact(B, col, form);
    }
    col[current]--;
    if (++current > B->KC) current = 1;
  }
  if (DEBUGLEVEL) dbg_all(&T, "random", s, nbtest);
  *pc = current;
}

static int
imag_be_honest(struct buch_quad *B)
{
  long p, fpc, s = B->KC, nbtest = 0;
  GEN F, ex = cgetg(lg(B->subFB), t_VECSMALL);
  pari_sp av = avma;

  while (s<B->KC2)
  {
    p = B->FB[s+1]; if (DEBUGLEVEL) err_printf(" %ld",p);
    F = qficomp(qfi_pf(B->QFR->D, p), qfi_random(B, ex));
    fpc = factorquad(B,F,s,p-1);
    if (fpc == 1) { nbtest=0; s++; }
    else
      if (++nbtest > 40) return 0;
    avma = av;
  }
  return 1;
}

/* Real Quadratic fields */

static void
real_relations(struct buch_quad *B, long need, long *pc, long lim, ulong LIMC, GEN mat, GEN C)
{
  pari_timer T;
  long lgsub = lg(B->subFB), prec = B->PRECREG, current = *pc, nbtest=0, s=0;
  long i, fpc, endcycle, rhoacc, rho;
  /* in a 2nd phase, don't include FB[current] but run along the cyle
   * ==> get more units */
  int first = (current == 0);
  pari_sp av, av1, limstack;
  GEN d, col, form, form0, form1, ex = cgetg(lgsub, t_VECSMALL);

  if (DEBUGLEVEL) timer_start(&T);
  if (!current) current = 1;
  if (lim > need) lim = need;
  av = avma; limstack = stack_lim(av,1);
  for(;;)
  {
    if (s >= need) break;
    if (first && s >= lim) {
      first = 0;
      if (DEBUGLEVEL) dbg_all(&T, "initial", s, nbtest);
    }
    avma = av; form = qfr3_random(B, ex);
    if (!first)
      form = QFR3_comp(form, qfr3_pf(B->QFR, B->FB[current]), B->QFR);
    av1 = avma;
    form0 = form; form1 = NULL;
    endcycle = rhoacc = 0;
    rho = -1;

CYCLE:
    if (endcycle || rho > 5000)
    {
      if (++current > B->KC) current = 1;
      continue;
    }
    if (low_stack(limstack, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"real_relations");
      gerepileall(av1, form1? 2: 1, &form, &form1);
    }
    if (rho < 0) rho = 0; /* first time in */
    else
    {
      form = qfr3_rho(form, B->QFR); rho++;
      rhoacc++;
      if (first)
        endcycle = (absi_equal(gel(form,1),gel(form0,1))
             && equalii(gel(form,2),gel(form0,2)));
      else
      {
        if (absi_equal(gel(form,1), gel(form,3))) /* a = -c */
        {
          if (absi_equal(gel(form,1),gel(form0,1)) &&
                  equalii(gel(form,2),gel(form0,2))) continue;
          form = qfr3_rho(form, B->QFR); rho++;
          rhoacc++;
        }
        else
          { setsigne(form[1],1); setsigne(form[3],-1); }
        if (equalii(gel(form,1),gel(form0,1)) &&
            equalii(gel(form,2),gel(form0,2))) continue;
      }
    }
    nbtest++; fpc = factorquad(B,form,B->KC,LIMC);
    if (!fpc)
    {
      if (DEBUGLEVEL>1) err_printf(".");
      goto CYCLE;
    }
    if (fpc > 1)
    { /* look for Large Prime relation */
      long *fpd = largeprime(B,fpc,ex,first? 0: current,rhoacc);
      ulong b1, b2, p;
      GEN form2;
      if (!fpd)
      {
        if (DEBUGLEVEL>1) err_printf(".");
        goto CYCLE;
      }
      if (!form1)
      {
        form1 = qfr5_factorback(B,ex);
        if (!first)
          form1 = QFR5_comp(form1, qfr5_pf(B->QFR, B->FB[current], prec), B->QFR);
      }
      form1 = qfr5_rho_pow(form1, rho, B->QFR);
      rho = 0;

      form2 = qfr5_factorback(B,fpd);
      if (fpd[-2])
        form2 = QFR5_comp(form2, qfr5_pf(B->QFR, B->FB[fpd[-2]], prec), B->QFR);
      form2 = qfr5_rho_pow(form2, fpd[-3], B->QFR);
      if (!absi_equal(gel(form2,1),gel(form2,3)))
      {
        setsigne(form2[1], 1);
        setsigne(form2[3],-1);
      }
      p = fpc << 1;
      b1 = umodiu(gel(form2,2), p);
      b2 = umodiu(gel(form1,2), p);
      if (b1 != b2 && b1+b2 != p) goto CYCLE;

      col = gel(mat,++s);
      add_fact(B, col, form1);
      (void)factorquad(B,form2,B->KC,LIMC);
      if (b1==b2)
      {
        for (i=1; i<lgsub; i++) col[B->subFB[i]] += fpd[i]-ex[i];
        sub_fact(B,col, form2);
        if (fpd[-2]) col[fpd[-2]]++;
        d = qfr5_dist(subii(gel(form1,4),gel(form2,4)),
                      divrr(gel(form1,5),gel(form2,5)), prec);
      }
      else
      {
        for (i=1; i<lgsub; i++) col[B->subFB[i]] += -fpd[i]-ex[i];
        add_fact(B, col, form2);
        if (fpd[-2]) col[fpd[-2]]--;
        d = qfr5_dist(addii(gel(form1,4),gel(form2,4)),
                      mulrr(gel(form1,5),gel(form2,5)), prec);
      }
      if (DEBUGLEVEL) err_printf(" %ldP",s);
    }
    else
    { /* standard relation */
      if (!form1)
      {
        form1 = qfr5_factorback(B, ex);
        if (!first)
          form1 = QFR5_comp(form1, qfr5_pf(B->QFR, B->FB[current], prec), B->QFR);
      }
      form1 = qfr5_rho_pow(form1, rho, B->QFR);
      rho = 0;

      col = gel(mat,++s);
      for (i=1; i<lgsub; i++) col[B->subFB[i]] = -ex[i];
      add_fact(B, col, form1);
      d = qfr5_dist(gel(form1,4), gel(form1,5), prec);
      if (DEBUGLEVEL) err_printf(" %ld",s);
    }
    affrr(d, gel(C,s));
    if (first)
    {
      if (s >= lim) continue;
      goto CYCLE;
    }
    else
    {
      col[current]--;
      if (++current > B->KC) current = 1;
    }
  }
  if (DEBUGLEVEL) dbg_all(&T, "random", s, nbtest);
  *pc = current;
}

static int
real_be_honest(struct buch_quad *B)
{
  long p, fpc, s = B->KC, nbtest = 0;
  GEN F,F0, ex = cgetg(lg(B->subFB), t_VECSMALL);
  pari_sp av = avma;

  while (s<B->KC2)
  {
    p = B->FB[s+1]; if (DEBUGLEVEL) err_printf(" %ld",p);
    F = QFR3_comp(qfr3_random(B, ex), qfr3_pf(B->QFR, p), B->QFR);
    for (F0 = F;;)
    {
      fpc = factorquad(B,F,s,p-1);
      if (fpc == 1) { nbtest=0; s++; break; }
      if (++nbtest > 40) return 0;
      F = qfr3_canon(qfr3_rho(F, B->QFR), B->QFR);
      if (equalii(gel(F,1),gel(F0,1))
       && equalii(gel(F,2),gel(F0,2))) break;
    }
    avma = av;
  }
  return 1;
}

static GEN
gcdreal(GEN a,GEN b)
{
  if (!signe(a)) return mpabs(b);
  if (!signe(b)) return mpabs(a);
  if (typ(a)==t_INT)
  {
    if (typ(b)==t_INT) return gcdii(a,b);
    a = itor(a, lg(b));
  }
  else if (typ(b)==t_INT)
    b = itor(b, lg(a));
  if (expo(a)<-5) return absr(b);
  if (expo(b)<-5) return absr(a);
  a = absr(a); b = absr(b);
  while (expo(b) >= -5  && signe(b))
  {
    long e;
    GEN r, q = gcvtoi(divrr(a,b),&e);
    if (e > 0) return NULL;
    r = subrr(a, mulir(q,b)); a = b; b = r;
  }
  return absr(a);
}

static int
get_R(struct buch_quad *B, GEN C, long sreg, GEN z, GEN *ptR)
{
  GEN R = gen_1;
  double c;
  long i;

  if (B->PRECREG)
  {
    R = mpabs(gel(C,1));
    for (i=2; i<=sreg; i++)
    {
      R = gcdreal(gel(C,i), R);
      if (!R) return fupb_PRECI;
    }
    if (gexpo(R) <= -3)
    {
      if (DEBUGLEVEL) err_printf("regulator is zero.\n");
      return fupb_RELAT;
    }
    if (DEBUGLEVEL) err_printf("#### Tentative regulator: %Ps\n",R);
  }
  c = gtodouble(gmul(z, R));
  if (c < 0.8 || c > 1.3) return fupb_RELAT;
  *ptR = R; return fupb_NONE;
}

static int
quad_be_honest(struct buch_quad *B)
{
  int r;
  if (B->KC2 <= B->KC) return 1;
  if (DEBUGLEVEL)
    err_printf("be honest for primes from %ld to %ld\n", B->FB[B->KC+1],B->FB[B->KC2]);
  r = B->PRECREG? real_be_honest(B): imag_be_honest(B);
  if (DEBUGLEVEL) err_printf("\n");
  return r;
}


GEN
Buchquad(GEN D, double cbach, double cbach2, long prec)
{
  const long MAXRELSUP = 7, SFB_MAX = 3;
  pari_timer T;
  pari_sp av0 = avma, av, av2;
  const long RELSUP = 5;
  long i, s, current, triv, sfb_trials, nrelsup, nreldep, need, nsubFB;
  ulong LIMC, LIMC2, cp;
  GEN W, cyc, res, gen, dep, mat, C, extraC, B, R, resc, Res, z, h = NULL; /*-Wall*/
  double drc, lim, LOGD, LOGD2;
  GRHcheck_t G, *GRHcheck = &G;
  struct qfr_data QFR;
  struct buch_quad BQ;
  int FIRST = 1;

  check_quaddisc(D, &s, /*junk*/&i, "Buchquad");
  R = NULL; /* -Wall */
  BQ.QFR = &QFR;
  QFR.D = D;
  if (s < 0)
  {
    if (cmpiu(QFR.D,4) <= 0)
    {
      GEN z = cgetg(5,t_VEC);
      gel(z,1) = gel(z,4) = gen_1; gel(z,2) = gel(z,3) = cgetg(1,t_VEC);
      return z;
    }
    BQ.PRECREG = 0;
  } else {
    BQ.PRECREG = maxss(prec+1, MEDDEFAULTPREC + 2*(expi(QFR.D)/BITS_IN_LONG));
  }
  if (DEBUGLEVEL) timer_start(&T);
  BQ.primfact   = new_chunk(100);
  BQ.exprimfact = new_chunk(100);
  BQ.hashtab = (long**) new_chunk(HASHT);
  for (i=0; i<HASHT; i++) BQ.hashtab[i] = NULL;

  drc = fabs(gtodouble(QFR.D));
  LOGD = log(drc);
  LOGD2 = LOGD * LOGD;

  lim = sqrt(drc);
  /* resc = sqrt(D) w / 2^r1 (2pi)^r2 ~ hR / L(chi,1) */
  if (BQ.PRECREG) resc = dbltor(lim / 2.);
  else         resc = dbltor(lim / PI);
  if (!BQ.PRECREG) lim /= sqrt(3.);
  cp = (ulong)exp(sqrt(LOGD*log(LOGD)/8.0));
  if (cp < 20) cp = 20;
  if (cbach > 6.) {
    if (cbach2 < cbach) cbach2 = cbach;
    cbach = 6.;
  }
  if (cbach <= 0.) pari_err(talker,"Bach constant <= 0 in Buchquad");
  av = avma;
  BQ.powsubFB = BQ.subFB = NULL;
  init_GRHcheck(GRHcheck, 2, BQ.PRECREG? 2: 0, LOGD);

/* LIMC = Max(cbach*(log D)^2, exp(sqrt(log D loglog D) / 8)) */
START:
  do
  {
    if (!FIRST) cbach = check_bach(cbach,6.);
    FIRST = 0; avma = av;
    if (BQ.subFB) gunclone(BQ.subFB);
    if (BQ.powsubFB) gunclone(BQ.powsubFB);
    clearhash(BQ.hashtab);
    LIMC = (ulong)(cbach*LOGD2);
    if (LIMC < cp) { LIMC = cp; cbach = (double)LIMC / LOGD2; }
    LIMC2 = (ulong)(maxdd(cbach,cbach2)*LOGD2);
    if (LIMC2 < LIMC) LIMC2 = LIMC;
    if (BQ.PRECREG) qfr_data_init(QFR.D, BQ.PRECREG, &QFR);

    Res = FBquad(&BQ, LIMC2, LIMC, GRHcheck);
    if (DEBUGLEVEL) timer_printf(&T, "factor base");
  }
  while (!Res || !(BQ.subFB = subFBquad(&BQ, QFR.D, lim + 0.5)));
  if (DEBUGLEVEL) timer_printf(&T, "subFBquad = %Ps",
                               vecpermute(BQ.FB, BQ.subFB));
  nsubFB = lg(BQ.subFB) - 1;
  BQ.powsubFB = powsubFBquad(&BQ,CBUCH+1);
  if (DEBUGLEVEL) timer_printf(&T, "powsubFBquad");
  BQ.limhash = (LIMC & HIGHMASK)? (HIGHBIT>>1): LIMC*LIMC;

  need = BQ.KC + RELSUP - 2;
  current = 0;
  W = NULL;
  sfb_trials = nreldep = nrelsup = 0;
  s = nsubFB + RELSUP;
  av2 = avma;

  do
  {
    if ((nreldep & 3) == 1 || (nrelsup & 7) == 1) {
      if (DEBUGLEVEL) err_printf("*** Changing sub factor base\n");
      gunclone(BQ.subFB);
      gunclone(BQ.powsubFB);
      BQ.subFB = gclone(vecslice(BQ.vperm, 1, nsubFB));
      BQ.powsubFB = powsubFBquad(&BQ,CBUCH+1);
      if (DEBUGLEVEL) timer_printf(&T, "powsubFBquad");
      clearhash(BQ.hashtab);
    }
    need += 2;
    mat    = cgetg(need+1, t_MAT);
    extraC = cgetg(need+1, t_VEC);
    if (!W) { /* first time */
      C = extraC;
      triv = trivial_relations(&BQ, mat, C);
      if (DEBUGLEVEL) err_printf("KC = %ld, need %ld relations\n", BQ.KC, need);
    } else {
      triv = 0;
      if (DEBUGLEVEL) err_printf("...need %ld more relations\n", need);
    }
    if (BQ.PRECREG) {
      for (i = triv+1; i<=need; i++) {
        gel(mat,i) = const_vecsmall(BQ.KC, 0);
        gel(extraC,i) = cgetr(BQ.PRECREG);
      }
      real_relations(&BQ, need - triv, &current, s,LIMC,mat + triv,extraC + triv);
    } else {
      for (i = triv+1; i<=need; i++) {
        gel(mat,i) = const_vecsmall(BQ.KC, 0);
        gel(extraC,i) = gen_0;
      }
      imag_relations(&BQ, need - triv, &current, LIMC,mat + triv);
    }

    if (!W)
      W = hnfspec_i(mat,BQ.vperm,&dep,&B,&C,nsubFB);
    else
      W = hnfadd_i(W,BQ.vperm,&dep,&B,&C, mat,extraC);
    gerepileall(av2, 4, &W,&C,&B,&dep);
    need = lg(dep)>1? lg(dep[1])-1: lg(B[1])-1;
    if (need)
    {
      if (++nreldep > 15 && cbach < 1) goto START;
      continue;
    }

    h = ZM_det_triangular(W);
    if (DEBUGLEVEL) err_printf("\n#### Tentative class number: %Ps\n", h);

    z = mulrr(Res, resc); /* ~ hR if enough relations, a multiple otherwise */
    switch(get_R(&BQ, C, (lg(C)-1) - (lg(B)-1) - (lg(W)-1), divir(h,z), &R))
    {
      case fupb_PRECI:
        BQ.PRECREG = (BQ.PRECREG<<1)-2;
        FIRST = 1; goto START;

      case fupb_RELAT:
        if (++nrelsup > MAXRELSUP)
        {
          if (++sfb_trials > SFB_MAX && cbach <= 1) goto START;
          if (nsubFB < minss(10,BQ.KC)) nsubFB++;
        }
        need = minss(BQ.KC, nrelsup);
    }
  }
  while (need);
  /* DONE */
  if (!quad_be_honest(&BQ)) goto START;
  if (DEBUGLEVEL) timer_printf(&T, "be honest");
  clearhash(BQ.hashtab);

  gen = get_clgp(&BQ,W,&cyc,BQ.PRECREG);
  gunclone(BQ.subFB);
  gunclone(BQ.powsubFB);
  res = cgetg(5,t_VEC);
  gel(res,1) = h;
  gel(res,2) = cyc;
  gel(res,3) = gen;
  gel(res,4) = R; return gerepilecopy(av0,res);
}

GEN
buchimag(GEN D, GEN c, GEN c2, GEN REL)
{ (void)REL; return Buchquad(D,gtodouble(c),gtodouble(c2),0); }

GEN
buchreal(GEN D, GEN flag, GEN c, GEN c2, GEN REL, long prec) {
  if (signe(flag)) pari_err(impl,"narrow class group");
  (void)REL; return Buchquad(D,gtodouble(c),gtodouble(c2),prec);
}

GEN
quadclassunit0(GEN x, long flag, GEN data, long prec)
{
  long lx;
  double c1 = 0.2, c2 = 0.2;

  if (!data) lx=1;
  else
  {
    lx = lg(data);
    if (typ(data)!=t_VEC || lx > 7)
      pari_err(talker,"incorrect parameters in quadclassunit");
    if (lx > 3) lx = 3;
  }
  switch(lx)
  {
    case 3: c2 = gtodouble(gel(data,2));
    case 2: c1 = gtodouble(gel(data,1));
  }
  if (flag) pari_err(impl,"narrow class group");
  return Buchquad(x,c1,c2,prec);
}