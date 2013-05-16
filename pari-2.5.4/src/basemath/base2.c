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

/*******************************************************************/
/*                                                                 */
/*                       MAXIMAL ORDERS                            */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

/* FIXME: backward compatibility. Should use the proper nf_* equivalents */
#define compat_PARTIAL 1
#define compat_ROUND2  2

static void
nfmaxord_check_args(nfmaxord_t *S, GEN T, long flag, GEN fa)
{
  GEN dT, P;
  long l;

  if (typ(T)!=t_POL) pari_err(notpoler,"nfmaxord");
  if (degpol(T) <= 0) pari_err(constpoler,"nfmaxord");

  if (fa) {
    if (typ(fa) != t_MAT) pari_err(typeer,"nfmaxord");
    dT = factorback(fa);
    if (!signe(dT)) pari_err(talker,"reducible polynomial in nfmaxord");
  } else {
    dT = ZX_disc(T);
    if (flag & nf_PARTIALFACT)
      fa = Z_factor_limit(absi(dT), 0);
    else
      fa = Z_factor(absi(dT));
  }
  S->dT = dT;
  P = gel(fa,1); l = lg(P);
  if (l > 1 && is_pm1(gel(P,1))) P = vecslice(P, 2, --l);
  S->dTP = P;
  S->dTE = vec_to_vecsmall(gel(fa,2));
}

static int
fnz(GEN x,long j)
{
  long i;
  for (i=1; i<j; i++)
    if (signe(x[i])) return 0;
  return 1;
}
/* return list u[i], 2 by 2 coprime with the same prime divisors as ab */
static GEN
get_coprimes(GEN a, GEN b)
{
  long i, k = 1;
  GEN u = cgetg(3, t_COL);
  gel(u,1) = a;
  gel(u,2) = b;
  /* u1,..., uk 2 by 2 coprime */
  while (k+1 < lg(u))
  {
    GEN d, c = gel(u,k+1);
    if (is_pm1(c)) { k++; continue; }
    for (i=1; i<=k; i++)
    {
      GEN ui = gel(u,i);
      if (is_pm1(ui)) continue;
      d = gcdii(c, ui);
      if (d == gen_1) continue;
      c = diviiexact(c, d);
      gel(u,i) = diviiexact(ui, d);
      u = shallowconcat(u, d);
    }
    gel(u,++k) = c;
  }
  for (i = k = 1; i < lg(u); i++)
    if (!is_pm1(gel(u,i))) gel(u,k++) = gel(u,i);
  setlg(u, k); return u;
}
/* allow p = -1 from factorizations */
static long
safe_Z_pvalrem(GEN x, GEN p, GEN *z)
{
  if (signe(p) < 0) { *z = absi(x); return 1; }
  return Z_pvalrem(x, p, z);
}
/* denominator of diagonal. All denominators are powers of a given integer */
static GEN
diag_denom(GEN M)
{
  GEN d = gen_1;
  long j, l = lg(M);
  for (j=1; j<l; j++)
  {
    GEN t = gcoeff(M,j,j);
    if (typ(t) == t_INT) continue;
    t = gel(t,2);
    if (absi_cmp(t,d) > 0) d = t;
  }
  return d;
}
static void
allbase_from_ordmax(nfmaxord_t *S, GEN ordmax, GEN P, GEN f)
{
  GEN a = NULL, da = NULL, index, P2, E2, D;
  long n = degpol(f), lP = lg(P), i, j, k;
  int centered = 0;
  for (i=1; i<lP; i++)
  {
    GEN M, db, b = gel(ordmax,i);
    if (b == gen_1) continue;
    db = diag_denom(b);
    if (db == gen_1) continue;

    /* db = denom(b), (da,db) = 1. Compute da Im(b) + db Im(a) */
    b = Q_muli_to_int(b,db);
    if (!da) { da = db; a = b; }
    else
    { /* optimization: easy as long as both matrix are diagonal */
      j=2; while (j<=n && fnz(gel(a,j),j) && fnz(gel(b,j),j)) j++;
      k = j-1; M = cgetg(2*n-k+1,t_MAT);
      for (j=1; j<=k; j++)
      {
        gel(M,j) = gel(a,j);
        gcoeff(M,j,j) = mulii(gcoeff(a,j,j),gcoeff(b,j,j));
      }
      /* could reduce mod M(j,j) but not worth it: usually close to da*db */
      for (  ; j<=n;     j++) gel(M,j) = ZC_Z_mul(gel(a,j), db);
      for (  ; j<=2*n-k; j++) gel(M,j) = ZC_Z_mul(gel(b,j+k-n), da);
      da = mulii(da,db);
      a = ZM_hnfmodall(M, da, hnf_MODID|hnf_CENTER);
      centered = 1;
    }
    if (DEBUGLEVEL>5) err_printf("Result for prime %Ps is:\n%Ps\n",P[i],b);
  }
  if (da)
  {
    index = diviiexact(da, gcoeff(a,1,1));
    for (j=2; j<=n; j++) index = mulii(index, diviiexact(da, gcoeff(a,j,j)));
    if (!centered) a = ZM_hnfcenter(a);
    a = RgM_Rg_div(a, da);
  }
  else
  {
    index = gen_1;
    a = matid(n);
  }
  S->dK = diviiexact(S->dT, sqri(index));
  S->index = index;

  D = S->dK;
  P2 = cgetg(lP, t_COL);
  E2 = cgetg(lP, t_VECSMALL);
  for (k = j = 1; j < lP; j++)
  {
    long v = Z_pvalrem(D, gel(P,j), &D);
    if (v) { gel(P2,k) = gel(P,j); E2[k] = v; k++; }
  }
  setlg(P2, k); S->dKP = P2;
  setlg(E2, k); S->dKE = P2;
  S->basis = RgM_to_RgXV(a, varn(f));
}

/*******************************************************************/
/*                                                                 */
/*                            ROUND 2                              */
/*                                                                 */
/*******************************************************************/
/* transpose of companion matrix of unitary polynomial x, cf matcompanion */
static GEN
companion(GEN x)
{
  long j, l = degpol(x);
  GEN c, y = cgetg(l+1,t_MAT);

  c = zerocol(l); gel(c,l) = gneg(gel(x,2));
  gel(y,1) = c;
  for (j=2; j<=l; j++)
  {
    c = col_ei(l, j-1); gel(c,l) = gneg(gel(x,j+1));
    gel(y,j) = c;
  }
  return y;
}

/* return (v - qw) mod m (only compute entries k0,..,n)
 * v and w are expected to have entries smaller than m */
static GEN
mtran(GEN v, GEN w, GEN q, GEN m, GEN mo2, long k0)
{
  long k;
  GEN p1;

  if (signe(q))
    for (k=lg(v)-1; k >= k0; k--)
    {
      pari_sp av = avma;
      p1 = subii(gel(v,k), mulii(q,gel(w,k)));
      p1 = centermodii(p1, m, mo2);
      gel(v,k) = gerepileuptoint(av, p1);
    }
  return v;
}

/* entries of v and w are C small integers */
static GEN
mtran_long(GEN v, GEN w, long q, long m, long k0)
{
  long k, p1;

  if (q)
  {
    for (k=lg(v)-1; k>= k0; k--)
    {
      p1 = v[k] - q * w[k];
      v[k] = p1 % m;
    }
  }
  return v;
}

/* coeffs of a are C-long integers */
static void
rowred_long(GEN a, long rmod)
{
  long q,j,k,pro, c = lg(a), r = lg(a[1]);

  for (j=1; j<r; j++)
  {
    for (k=j+1; k<c; k++)
      while (coeff(a,j,k))
      {
        q = coeff(a,j,j) / coeff(a,j,k);
        pro=(long)mtran_long(gel(a,j),gel(a,k),q,rmod, j);
        a[j]=a[k]; a[k]=pro;
      }
    if (coeff(a,j,j) < 0)
      for (k=j; k<r; k++) coeff(a,k,j)=-coeff(a,k,j);
    for (k=1; k<j; k++)
    {
      q = coeff(a,j,k) / coeff(a,j,j);
      gel(a,k) = mtran_long(gel(a,k),gel(a,j),q,rmod, k);
    }
  }
  /* don't update the 0s in the last columns */
  for (j=1; j<r; j++)
    for (k=1; k<r; k++) gcoeff(a,j,k) = stoi(coeff(a,j,k));
}

static void
rowred(GEN a, GEN rmod)
{
  long j,k,pro, c = lg(a), r = lg(a[1]);
  pari_sp av=avma, lim=stack_lim(av,1);
  GEN q, rmodo2 = shifti(rmod,-1);

  for (j=1; j<r; j++)
  {
    for (k=j+1; k<c; k++)
      while (signe(gcoeff(a,j,k)))
      {
        q=diviiround(gcoeff(a,j,j),gcoeff(a,j,k));
        pro=(long)mtran(gel(a,j),gel(a,k),q,rmod,rmodo2, j);
        a[j]=a[k]; a[k]=pro;
      }
    if (signe(gcoeff(a,j,j)) < 0)
      for (k=j; k<r; k++) gcoeff(a,k,j) = negi(gcoeff(a,k,j));
    for (k=1; k<j; k++)
    {
      q=diviiround(gcoeff(a,j,k),gcoeff(a,j,j));
      gel(a,k) = mtran(gel(a,k),gel(a,j),q,rmod,rmodo2, k);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      long j1,k1;
      GEN p1;
      if(DEBUGMEM>1) pari_warn(warnmem,"rowred j=%ld", j);
      p1 = gerepilecopy(av,a);
      for (j1=1; j1<r; j1++)
        for (k1=1; k1<c; k1++) gcoeff(a,j1,k1) = gcoeff(p1,j1,k1);
    }
  }
}

/* Compute d/x where d is t_INT, x lower triangular t_MAT with t_INT coeffs
 * whose diagonal coeffs divide d (lower triangular ZM result). */
static GEN
matinv(GEN x, GEN d)
{
  pari_sp av,av1;
  long i,j,k, n = lg(x);
  GEN y,h;

  y = matid(n-1);
  for (i=1; i<n; i++)
    gcoeff(y,i,i) = diviiexact(d,gcoeff(x,i,i));
  av=avma;
  for (i=2; i<n; i++)
    for (j=i-1; j; j--)
    {
      for (h=gen_0,k=j+1; k<=i; k++)
      {
        GEN p1 = mulii(gcoeff(y,i,k),gcoeff(x,k,j));
        if (p1 != gen_0) h=addii(h,p1);
      }
      togglesign(h); av1=avma;
      gcoeff(y,i,j) = gerepile(av,av1,diviiexact(h,gcoeff(x,j,j)));
      av = avma;
    }
  return y;
}

/* epsilon > 1 */
static GEN
maxord2(GEN cf, GEN p, long epsilon)
{
  long sp,i,n=lg(cf)-1;
  pari_sp av=avma, av2,limit;
  GEN T,T2,Tn,m,v,delta,hard_case_exponent, *w;
  const GEN pp = sqri(p);
  const GEN ppo2 = shifti(pp,-1);
  const long pps = (2*expi(pp)+2 < (long)BITS_IN_LONG)? pp[2]: 0;

  if (cmpiu(p,n) > 0)
  {
    hard_case_exponent = NULL;
    sp = 0; /* gcc -Wall */
  }
  else
  {
    long k;
    k = sp = itos(p);
    i=1; while (k < n) { k *= sp; i++; }
    hard_case_exponent = utoipos(i);
  }
  T=cgetg(n+1,t_MAT); for (i=1; i<=n; i++) gel(T,i) = cgetg(n+1,t_COL);
  T2=cgetg(2*n+1,t_MAT); for (i=1; i<=2*n; i++) gel(T2,i) = cgetg(n+1,t_COL);
  Tn=cgetg(n*n+1,t_MAT); for (i=1; i<=n*n; i++) gel(Tn,i) = cgetg(n+1,t_COL);
  v = new_chunk(n+1);
  w = (GEN*)new_chunk(n+1);

  av2 = avma; limit = stack_lim(av2,1);
  delta=gen_1; m=matid(n);

  for(;;)
  {
    long j, k, h;
    pari_sp av0 = avma;
    GEN t,b,jp,hh,index,p1, dd = sqri(delta), ppdd = mulii(dd,pp);
    GEN ppddo2 = shifti(ppdd,-1);

    if (DEBUGLEVEL > 3)
      err_printf("ROUND2: epsilon = %ld\tavma = %ld\n",epsilon,avma);

    b=matinv(m,delta);
    for (i=1; i<=n; i++)
    {
      for (j=1; j<=n; j++)
        for (k=1; k<=n; k++)
        {
          p1 = j==k? gcoeff(m,i,1): gen_0;
          for (h=2; h<=n; h++)
          {
            GEN p2 = mulii(gcoeff(m,i,h),gcoeff(gel(cf,h),j,k));
            if (p2!=gen_0) p1 = addii(p1,p2);
          }
          gcoeff(T,j,k) = centermodii(p1, ppdd, ppddo2);
        }
      p1 = ZM_mul(m, ZM_mul(T,b));
      for (j=1; j<=n; j++)
        for (k=1; k<=n; k++)
          gcoeff(p1,j,k) = centermodii(diviiexact(gcoeff(p1,j,k),dd),pp,ppo2);
      w[i] = p1;
    }

    if (hard_case_exponent)
    {
      for (j=1; j<=n; j++)
      {
        for (i=1; i<=n; i++) gcoeff(T,i,j) = gcoeff(w[j],1,i);
        /* ici la boucle en k calcule la puissance p mod p de w[j] */
        for (k=1; k<sp; k++)
        {
          for (i=1; i<=n; i++)
          {
            p1 = gen_0;
            for (h=1; h<=n; h++)
            {
              GEN p2=mulii(gcoeff(T,h,j),gcoeff(w[j],h,i));
              if (p2!=gen_0) p1 = addii(p1,p2);
            }
            gel(v,i) = modii(p1, p);
          }
          for (i=1; i<=n; i++) gcoeff(T,i,j) = gel(v,i);
        }
      }
      t = ZM_pow(T, hard_case_exponent);
    }
    else
    {
      for (i=1; i<=n; i++)
        for (j=1; j<=n; j++)
        {
          pari_sp av1 = avma;
          p1 = gen_0;
          for (k=1; k<=n; k++)
            for (h=1; h<=n; h++)
            {
              const GEN r=modii(gcoeff(w[i],k,h),p);
              const GEN s=modii(gcoeff(w[j],h,k),p);
              const GEN p2 = mulii(r,s);
              if (p2!=gen_0) p1 = addii(p1,p2);
            }
          gcoeff(T,i,j) = gerepileupto(av1,p1);
        }
      t = T;
    }

    setlg(T2, 2*n+1);
    if (pps)
    {
      long ps = p[2];
      for (i=1; i<=n; i++)
        for (j=1; j<=n; j++)
        {
          coeff(T2,j,i)=(i==j)? ps: 0;
          coeff(T2,j,n+i)=smodis(gcoeff(t,i,j),ps);
        }
      rowred_long(T2,pps);
    }
    else
    {
      for (i=1; i<=n; i++)
        for (j=1; j<=n; j++)
        {
          gcoeff(T2,j,i)=(i==j)? p: gen_0;
          gcoeff(T2,j,n+i) = modii(gcoeff(t,i,j),p);
        }
      rowred(T2,pp);
    }
    setlg(T2, n+1);
    jp=matinv(T2,p);
    setlg(Tn, n*n+1);
    if (pps)
    {
      for (k=1; k<=n; k++)
      {
        pari_sp av1=avma;
        t = ZM_mul(ZM_mul(jp,w[k]), T2);
        for (h=i=1; i<=n; i++)
          for (j=1; j<=n; j++,h++)
            coeff(Tn,k,h) = itos(diviiexact(gcoeff(t,i,j), p)) % pps;
        avma=av1;
      }
      avma = av0;
      rowred_long(Tn,pps);
    }
    else
    {
      for (k=1; k<=n; k++)
      {
        t = ZM_mul(ZM_mul(jp,w[k]), T2);
        for (h=i=1; i<=n; i++)
          for (j=1; j<=n; j++,h++)
            gcoeff(Tn,k,h) = diviiexact(gcoeff(t,i,j), p);
      }
      rowred(Tn,pp);
    }
    setlg(Tn, n+1);
    index = ZM_det_triangular(Tn);
    if (is_pm1(index)) break;

    m = ZM_mul(matinv(Tn,index), m);
    m = Q_primitive_part(m, &hh);
    delta = mulii(index,delta);
    if (hh) delta = diviiexact(delta,hh);
    epsilon -= 2 * Z_pval(index,p);
    if (epsilon < 2) break;
    if (low_stack(limit,stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"maxord2");
      gerepileall(av2, 2, &m, &delta);
    }
  }
  m = shallowtrans(m);
  return gerepileupto(av, RgM_Rg_div(ZM_hnfmodid(m, delta), delta));
}

/* Input:
 *  x normalized integral polynomial of degree n, defining K=Q(theta).
 *
 *  code 0, 1 or (long)p if we want base, smallbase ou factoredbase (resp.).
 *  y is GEN *, which will receive the discriminant of K.
 *
 * Output
 *  1) A t_COL whose n components are rationnal polynomials (with degree
 *     0,1...n-1) : integral basis for K (putting x=theta).
 *     Rem: common denominator is in da.
 *
 *  2) discriminant of K (in *y).
 */
static void
allbase2(nfmaxord_t *S, GEN f)
{
  GEN cf, ordmax, P = S->dTP, E = S->dTE;
  long i, lP = lg(P), n = degpol(f);

  cf = cgetg(n+1,t_VEC); gel(cf,2) = companion(f);
  for (i=3; i<=n; i++) gel(cf,i) = ZM_mul(gel(cf,2), gel(cf,i-1));
  ordmax = cgetg(lP, t_VEC);
  for (i=1; i<lP; i++)
  {
    GEN p = gel(P, i);
    long e = E[i];
    if (DEBUGLEVEL) err_printf("Treating p^k = %Ps^%ld\n", p, e);
    gel(ordmax,i) = e == 1? gen_1: maxord2(cf, p, e);
  }
  allbase_from_ordmax(S, ordmax, P, f);
}

/*******************************************************************/
/*                                                                 */
/*                            ROUND 4                              */
/*                                                                 */
/*******************************************************************/
GEN maxord_i(GEN p, GEN f, long mf, GEN w, long flag);
static GEN dbasis(GEN p, GEN f, long mf, GEN alpha, GEN U);
static GEN maxord(GEN p,GEN f,long mf);

/* return integer basis. If fa not NULL, taken to be the factorization
 * of disc(T) [no consistency check] */
void
nfmaxord(nfmaxord_t *S, GEN T, long flag, GEN fa)
{
  VOLATILE GEN P, E, ordmax;
  VOLATILE long lP, i, k;

  {
    pari_timer t;
    if (DEBUGLEVEL) timer_start(&t);
    nfmaxord_check_args(S, T, flag, fa);
    if (DEBUGLEVEL) timer_printf(&t, "disc. factorisation");
  }
  if (flag & nf_ROUND2) { allbase2(S, T); return; }
  P = S->dTP; lP = lg(P);
  E = S->dTE;
  ordmax = cgetg(1, t_VEC);
  for (i=1; i<lP; i++)
  {
    VOLATILE pari_sp av;
    /* includes the silly case where P[i] = -1 */
    if (E[i] == 1) { ordmax = shallowconcat(ordmax, gen_1); continue; }
    av = avma;
    CATCH(invmoder) { /* caught false prime, update factorization */
      GEN x = (GEN)global_err_data;
      GEN N, p = gcdii(gel(x,1), gel(x,2)), u = diviiexact(gel(x,1),p);
      long l;
      if (DEBUGLEVEL) pari_warn(warner,"impossible inverse: %Ps", x);
      gerepileall(av, 2, &p, &u);

      u = get_coprimes(p, u); l = lg(u);
      /* no small factors, but often a prime power */
      for (k = 1; k < l; k++) (void)Z_isanypower(gel(u,k), &gel(u,k));
      gel(P,i) = gel(u,1);
      P = shallowconcat(P, vecslice(u, 2, l-1));
      av = avma;
      N = S->dT; E[i] = Z_pvalrem(N, gel(P,i), &N);
      for (k=lP, lP=lg(P); k < lP; k++) E[k] = Z_pvalrem(N, gel(P,k), &N);
    } RETRY {
      if (DEBUGLEVEL) err_printf("Treating p^k = %Ps^%ld\n",P[i],E[i]);
      ordmax = shallowconcat(ordmax, mkvec( maxord(gel(P,i),T,E[i]) ));
    } ENDCATCH;
  }
  allbase_from_ordmax(S, ordmax, P, T);
}

/* d a t_INT, f a t_MAT factorisation sharing some prime divisors with d */
static GEN
update_fact(GEN d, GEN f)
{
  GEN fa, E, Q, P = gel(f,1);
  long iq, i, k, l;
  if (typ(f)!=t_MAT || lg(f)!=3)
    pari_err(talker,"not a factorisation in nfbasis");
  l = lg(P);
  if (l > 1 && is_pm1(gel(P,1))) P = vecslice(P, 2, --l);
  Q = cgetg(l,t_COL);
  E = cgetg(l,t_COL); iq = 1;
  for (i=1; i<l; i++)
  {
    k = safe_Z_pvalrem(d, gel(P,i), &d);
    if (k) { Q[iq] = P[i]; gel(E,iq) = utoipos(k); iq++; }
  }
  setlg(Q,iq);
  setlg(E,iq); fa = mkmat2(Q,E);
  if (signe(d) < 0) d = negi(d);
  if (is_pm1(d)) return fa;
  d = BPSW_psp(gel(P,l-1))? Z_factor(d): to_famat_shallow(d, gen_1);
  return merge_factor_i(d, fa);
}

/* FIXME: have to deal with compatibility flags */
static void
_nfbasis(GEN x0, long flag, GEN fa, GEN *pbas, GEN *pdK)
{
  GEN x, lead;
  nfmaxord_t S;
  long fl = 0;

  if (typ(x0)!=t_POL) pari_err(typeer,"nfbasis");
  if (degpol(x0) <= 0) pari_err(zeropoler,"nfbasis");
  RgX_check_ZX(x0, "nfbasis");

  x = ZX_Q_normalize(x0, &lead);
  if (fa && !isint1(lead)) fa = update_fact(ZX_disc(x), fa);
  if (flag & compat_PARTIAL) fl |= nf_PARTIALFACT;
  if (flag & compat_ROUND2)  fl |= nf_ROUND2;
  nfmaxord(&S, x, fl, fa);
  if (pbas) *pbas = RgXV_unscale(S.basis, lead);
  if (pdK)  *pdK = S.dK;
}

GEN
nfbasis(GEN x, GEN *pdK, long flag, GEN fa)
{
  pari_sp av = avma;
  GEN bas; _nfbasis(x, flag, fa, &bas, pdK);
  gerepileall(av, pdK? 2: 1, &bas, pdK); return bas;
}
GEN
nfbasis0(GEN x, long flag, GEN fa)
{
  pari_sp av = avma;
  GEN bas; _nfbasis(x, flag, fa, &bas, NULL);
  return gerepilecopy(av, bas);
}
GEN
nfdisc0(GEN x, long flag, GEN fa)
{
  pari_sp av = avma;
  GEN dK; _nfbasis(x, flag, fa, NULL, &dK);
  return gerepilecopy(av, dK);
}
GEN
nfdisc(GEN x) { return nfdisc0(x, 0, NULL); }

/* return U if Z[alpha] is not maximal or 2*dU < m-1; else return NULL */
static GEN
dedek(GEN f, long mf, GEN p,GEN g)
{
  GEN k,h;
  long dk;

  h = FpX_div(f,g,p);
  k = ZX_Z_divexact(ZX_sub(f, ZX_mul(g,h)), p);
  k = FpX_gcd(k, FpX_gcd(g,h, p), p);

  dk = degpol(k);
  if (DEBUGLEVEL>2)
  {
    err_printf("  dedek: gcd has degree %ld\n", dk);
    if (DEBUGLEVEL>5) err_printf("initial parameters p=%Ps,\n  f=%Ps\n",p,f);
  }
  if (2*dk >= mf-1) return FpX_div(f,k,p);
  return dk? NULL: f;
}

/* p-maximal order of Af; mf = v_p(Disc(f)) */
static GEN
maxord(GEN p,GEN f,long mf)
{
  const pari_sp av = avma;
  GEN w = NULL, g, res, fp = FpX_red(f, p);

  if (cmpui(degpol(f),p) < 0)
    g = FpX_div(fp, FpX_gcd(fp,ZX_deriv(fp), p), p);
  else
  {
    w = gel(FpX_factor(fp,p),1);
    g = FpXV_prod(w, p);
  }
  res = dedek(f, mf, p, g);
  if (res)
    res = dbasis(p, f, mf, pol_x(varn(f)), res);
  else
  {
    if (!w) w = gel(FpX_factor(fp,p),1);
    res = maxord_i(p, f, mf, w, 0);
  }
  return gerepileupto(av,res);
}

/* Sylvester's matrix, mod p^m (assumes f1 monic) */
static GEN
ZpX_sylvester_hnf(GEN f1, GEN f2, GEN pm)
{
  long j, n = degpol(f1);
  GEN h, a = cgetg(n+1,t_MAT);
  h = FpXQ_red(f2,f1,pm);
  for (j=1;; j++)
  {
    gel(a,j) = RgX_to_RgV(h, n);
    if (j == n) break;
    h = FpX_rem(RgX_shift_shallow(h, 1), f1, pm);
  }
  return ZM_hnfmodall(a, pm, hnf_MODID|hnf_PART);
}

/* polynomial gcd mod p^m (assumes f1 monic) */
GEN
ZpX_gcd(GEN f1, GEN f2, GEN pm)
{
  pari_sp av = avma;
  GEN a = ZpX_sylvester_hnf(f1,f2,pm);
  long c, l = lg(a), v = varn(f1);
  for (c = 1; c < l; c++)
  {
    GEN t = gcoeff(a,c,c);
    if (!equalii(t, pm))
      return gerepileupto(av, RgX_Rg_div(RgV_to_RgX(gel(a,c), v), t));
  }
  avma = av; return pol_0(v);
}

/* Return m > 0, such that p^m ~ 2^32 for initial value of m; p > 1 */
static long
init_m(GEN p)
{
  if (lgefint(p) > 3) return 1;
  return (long)(32 / log2(p[2]));
}

/* reduced resultant mod p^m (assumes x monic) */
GEN
ZpX_reduced_resultant(GEN x, GEN y, GEN pm)
{
  pari_sp av = avma;
  GEN z = ZpX_sylvester_hnf(x,y,pm);
  z = gcoeff(z,1,1);
  if (equalii(z,pm)) { avma = av; return gen_0; }
  return gerepileuptoint(av, icopy(z));
}
/* Assume Res(f,g) divides p^M. Return Res(f, g), using dynamic p-adic
 * precision (until result is non-zero or p^M). */
GEN
ZpX_reduced_resultant_fast(GEN f, GEN g, GEN p, long M)
{
  GEN R, q = NULL;
  long m;
  m = init_m(p); if (m < 1) m = 1;
  for(;; m <<= 1) {
    if (M < 2*m) break;
    q = q? sqri(q): powiu(p, m); /* p^m */
    R = ZpX_reduced_resultant(f,g, q); if (signe(R)) return R;
  }
  q = powiu(p, M);
  R = ZpX_reduced_resultant(f,g, q); return signe(R)? R: q;
}

/* discriminant valuation mod p^m (assumes x monic, dx = x') */
static long
ZpX_disc_val_i(GEN x, GEN dx, GEN p, GEN pm)
{
  pari_sp av = avma;
  GEN z = ZpX_sylvester_hnf(x,dx,pm);
  long i, v = 0, l = lg(z);
  for (i = 1; i < l; i++)
  {
    GEN c = gcoeff(z,i,i);
    if (equalii(c, pm)) { avma = av; return -1; } /* failure */
    v += Z_pval(c, p);
  }
  return v;
}
/* assume f monic */
long
ZpX_disc_val(GEN f, GEN p)
{
  pari_sp av = avma;
  GEN q = NULL, df;
  long v, m;

  if (degpol(f) == 1) return 0;
  df = ZX_deriv(f);
  m = init_m(p); if (m < 2) m = 2;
  for(;; m <<= 1) {
    q = q? sqri(q): powiu(p, m); /* p^m */
    v = ZpX_disc_val_i(f,df, p, q); if (v >= 0) break;
  }
  avma = av; return v;
}

/* *e a ZX, *d, *z in Z, *d = p^(*vd). Simplify e / d by cancelling a
 * common factor p^v; if z!=NULL, update it by cancelling the same power of p */
static void
update_den(GEN p, GEN *e, GEN *d, long *vd, GEN *z)
{
  GEN newe;
  long ve = ZX_pvalrem(*e, p, &newe);
  if (ve) {
    GEN newd;
    long v = minss(*vd, ve);
    if (v) {
      if (v == *vd)
      { /* rare, denominator cancelled */
        if (ve != v) newe = ZX_Z_mul(newe, powiu(p, ve - v));
        newd = gen_1;
        *vd = 0;
        if (z) *z =diviiexact(*z, powiu(p, v));
      }
      else
      { /* v = ve < vd, generic case */
        GEN q = powiu(p, v);
        newd = diviiexact(*d, q);
        *vd -= v;
        if (z) *z = diviiexact(*z, q);
      }
      *e = newe;
      *d = newd;
    }
  }
}

/* return denominator, a power of p */
static GEN
QpX_denom(GEN x)
{
  long i, l = lg(x);
  GEN maxd = gen_1;
  for (i=2; i<l; i++)
  {
    GEN d = gel(x,i);
    if (typ(d) == t_FRAC && cmpii(gel(d,2), maxd) > 0) maxd = gel(d,2);
  }
  return maxd;
}
static GEN
QpXV_denom(GEN x)
{
  long l = lg(x), i;
  GEN maxd = gen_1;
  for (i = 1; i < l; i++)
  {
    GEN d = QpX_denom(gel(x,i));
    if (cmpii(d, maxd) > 0) maxd = d;
  }
  return maxd;
}

static GEN
QpX_remove_denom(GEN x, GEN p, GEN *pdx, long *pv)
{
  *pdx = QpX_denom(x);
  if (*pdx == gen_1) { *pv = 0; *pdx = NULL; }
  else {
    x = Q_muli_to_int(x,*pdx);
    *pv = Z_pval(*pdx, p);
  }
  return x;
}

/* p^v * f o g mod (T,q). q = p^vq  */
static GEN
compmod(GEN p, GEN f, GEN g, GEN T, GEN q, long v)
{
  GEN D = NULL, z, df, dg, qD;
  long vD = 0, vdf, vdg;

  f = QpX_remove_denom(f, p, &df, &vdf);
  if (typ(g) == t_VEC) /* [num,den,v_p(den)] */
  { vdg = itos(gel(g,3)); dg = gel(g,2); g = gel(g,1); }
  else
    g = QpX_remove_denom(g, p, &dg, &vdg);
  if (df) { D = df; vD = vdf; }
  if (dg) {
    long degf = degpol(f);
    D = mul_content(D, powiu(dg, degf));
    vD += degf * vdg;
  }
  qD = D ? mulii(q, D): q;
  if (dg) f = FpX_rescale(f, dg, qD);
  z = FpX_FpXQ_eval(f, g, T, qD);
  if (!D) {
    if (v) {
      if (v > 0)
        z = ZX_Z_mul(z, powiu(p, v));
      else
        z = RgX_Rg_div(z, powiu(p, -v));
    }
    return z;
  }
  update_den(p, &z, &D, &vD, NULL);
  qD = mulii(D,q);
  if (v) vD -= v;
  D = gpowgs(p, vD);
  z = FpX_center(z, qD, shifti(qD,-1));
  if (vD > 0)
    z = RgX_Rg_div(z, powiu(p, vD));
  else if (vD < 0)
    z = ZX_Z_mul(z, powiu(p, -vD));
  return z;
}

static GEN
dbasis(GEN p, GEN f, long mf, GEN a, GEN U)
{
  long n = degpol(f), dU, i, vda;
  GEN D, da, b, ha, pd, pdp;

  if (n == 1) return scalarmat(gen_1, 1);
  if (DEBUGLEVEL>5)
  {
    err_printf("  entering Dedekind Basis with parameters p=%Ps\n",p);
    err_printf("  f = %Ps,\n  a = %Ps\n",f,a);
  }
  pd = powiu(p, mf >> 1); pdp = mulii(pd,p);
  dU = U ? degpol(U): 0;
  b = cgetg(n, t_MAT); /* Z[a] + U/p Z[a] is maximal */
  ha = scalarpol(pd, varn(f));
  a = QpX_remove_denom(a, p, &da, &vda);
  D = da? mulii(pdp, da): pdp;
  /* skip first column = [pd, 0,...,0] */
  for (i=1; i<n; i++)
  {
    if (i == dU)
      ha = compmod(p, U, mkvec3(a,da,stoi(vda)), f, pdp, (mf>>1) - 1);
    else
    {
      ha = FpXQ_mul(ha, a, f, D);
      if (da) ha = ZX_Z_divexact(ha, da);
    }
    gel(b,i) = RgX_to_RgV(ha,n);
  }
  b = ZM_hnfmodid(b,pd);
  if (DEBUGLEVEL>5) err_printf("  new order: %Ps\n",b);
  return RgM_Rg_div(b, pd);
}

static GEN
get_partial_order_as_pols(GEN p, GEN f)
{
  long v = ZpX_disc_val(f, p);
  return RgM_to_RgXV(maxord(p,f, v), varn(f));
}

typedef struct __decomp {
  /* constants */
  GEN p, f; /* goal: factor f p-adically */
  long df; /* p^df = reduced discriminant of f */
  GEN psf, pmf; /* stability precision for f, wanted precision for f */
  long vpsf; /* v_p(p_f) */
  /* these are updated along the way */
  GEN phi; /* a p-integer, in Q[X] */
  GEN phi0; /* a p-integer, in Q[X] from testb2 / testc2, to be composed with
             * phi when correct precision is known */
  GEN chi; /* characteristic polynomial of phi (mod psc) in Z[X] */
  GEN nu; /* irreducible divisor of chi mod p, in Z[X] */
  GEN invnu; /* numerator ( 1/ Mod(nu, chi) mod pmr ) */
  GEN Dinvnu;/* denominator ( ... ) */
  long vDinvnu; /* v_p(Dinvnu) */
  GEN prc, psc; /* reduced discriminant of chi, stability precision for chi */
  long vpsc; /* v_p(p_c) */
  GEN ns, precns; /* cached Newton sums and their precision */
} decomp_t;

/* if flag = 0, maximal order, else factorization to precision r = flag */
static GEN
Decomp(decomp_t *S, long flag)
{
  pari_sp av = avma;
  GEN fred, res, pr, pk, ph, b1, b2, a, e, de, f1, f2, dt, th;
  GEN p = S->p;
  long k, r = flag? flag: 2*S->df + 1;
  long vde, vdt;

  if (DEBUGLEVEL>2)
  {
    err_printf("  entering Decomp");
    if (DEBUGLEVEL>5) err_printf(", parameters: %Ps^%ld\n  f = %Ps",p, r, S->f);
    err_printf("\n");
  }
  if (!FpX_valrem(S->chi, S->nu, p, &b1))
    pari_err(talker, "bug in Decomp (not a factor), is p = %Ps a prime?", p);
  b2 = FpX_div(S->chi, b1, p);
  a = FpX_mul(FpXQ_inv(b2, b1, p), b2, p);
  /* E = e / de, e in Z[X], de in Z,  E = a(phi) mod (f, p) */
  th = QpX_remove_denom(S->phi, p, &dt, &vdt);
  if (dt)
  {
    long dega = degpol(a);
    vde = dega * vdt;
    de = powiu(dt, dega);
    pr = mulii(p, de);
    a = FpX_rescale(a, dt, pr);
  }
  else
  {
    vde = 0;
    de = gen_1;
    pr = p;
  }
  e = FpX_FpXQ_eval(a, th, S->f, pr);
  update_den(p, &e, &de, &vde, NULL);

  pk = p; k = 1;
  /* E, (1 - E) tend to orthogonal idempotents in Zp[X]/(f) */
  while (k < r + vde)
  { /* E <-- E^2(3-2E) mod p^2k, with E = e/de */
    GEN D;
    pk = sqri(pk); k <<= 1;
    e = ZX_mul(ZX_sqr(e), Z_ZX_sub(mului(3,de), gmul2n(e,1)));
    de= mulii(de, sqri(de));
    vde *= 3;
    D = mulii(pk, de);
    e = FpX_rem(e, centermod(S->f, D), D); /* e/de defined mod pk */
    update_den(p, &e, &de, &vde, NULL);
  }
  pr = powiu(p, r); /* required precision of the factors */
  ph = mulii(de, pr);
  fred = centermod(S->f, ph);
  e    = centermod(e, ph);

  f1 = ZpX_gcd(fred, Z_ZX_sub(de, e), ph); /* p-adic gcd(f, 1-e) */
  fred = centermod(fred, pr);
  f1   = centermod(f1,   pr);
  f2 = FpX_div(fred,f1, pr);
  f2 = FpX_center(f2, pr, shifti(pr,-1));

  if (DEBUGLEVEL>5)
    err_printf("  leaving Decomp: f1 = %Ps\nf2 = %Ps\ne = %Ps\nde= %Ps\n", f1,f2,e,de);

  if (flag) {
    gerepileall(av, 2, &f1, &f2);
    return famat_mul_shallow(ZX_monic_factorpadic(f1, p, flag),
                             ZX_monic_factorpadic(f2, p, flag));
  } else {
    GEN D, Dov2, d1, d2, ib1, ib2;
    long n, n1, n2, i;
    gerepileall(av, 4, &f1, &f2, &e, &de);
    D = de;
    ib1 = get_partial_order_as_pols(p,f1); n1 = lg(ib1)-1;
    ib2 = get_partial_order_as_pols(p,f2); n2 = lg(ib2)-1; n = n1+n2;
    d1 = QpXV_denom(ib1);
    d2 = QpXV_denom(ib2); if (cmpii(d1, d2) < 0) d1 = d2;
    if (d1 != gen_1) {
      ib1 = Q_muli_to_int(ib1, d1);
      ib2 = Q_muli_to_int(ib2, d1);
      D = mulii(d1, D);
    }
    Dov2 = shifti(D,-1);
    fred = centermod_i(S->f, D, Dov2);
    res = cgetg(n+1, t_VEC);
    for (i=1; i<=n1; i++)
      gel(res,i) = FpX_center(FpX_rem(FpX_mul(gel(ib1,i),e,D), fred, D), D, Dov2);
    e = Z_ZX_sub(de, e); ib2 -= n1;
    for (   ; i<=n; i++)
      gel(res,i) = FpX_center(FpX_rem(FpX_mul(gel(ib2,i),e,D), fred, D), D, Dov2);
    res = RgXV_to_RgM(res, n);
    return RgM_Rg_div(ZM_hnfmodid(res,D), D); /* normalized integral basis */
  }
}

/* minimum extension valuation: L/E */
static void
vstar(GEN p,GEN h, long *L, long *E)
{
  long first, j, k, v, w, m = degpol(h);

  first = 1; k = 1; v = 0;
  for (j=1; j<=m; j++)
  {
    GEN c = gel(h, m-j+2);
    if (signe(c))
    {
      w = Z_pval(c,p);
      if (first || w*k < v*j) { v = w; k = j; }
      first = 0;
    }
  }
  w = (long)ugcd(v,k);
  *L = v/w;
  *E = k/w;
}

static GEN
redelt_i(GEN a, GEN N, GEN p, GEN *pda, long *pvda)
{
  GEN z;
  a = Q_remove_denom(a, pda);
  *pvda = 0;
  if (*pda)
  {
    long v = Z_pvalrem(*pda, p, &z);
    if (v) {
      *pda = powiu(p, v);
      *pvda = v;
      N  = mulii(*pda, N);
    }
    else
      *pda = NULL;
    if (!is_pm1(z)) a = ZX_Z_mul(a, Fp_inv(z, N));
  }
  return centermod(a, N);
}
/* reduce the element a modulo N [ a power of p ], taking first care of the
 * denominators */
static GEN
redelt(GEN a, GEN N, GEN p)
{
  GEN da;
  long vda;
  a = redelt_i(a, N, p, &da, &vda);
  if (da) a = RgX_Rg_div(a, da);
  return a;
}

/* compute the Newton sums of g(x) mod p, assume deg g > 0 */
GEN
polsymmodp(GEN g, GEN p)
{
  pari_sp av;
  long d = degpol(g), i, k;
  GEN s, y, po2;

  y = cgetg(d + 1, t_COL);
  gel(y,1) = utoipos(d);
  if (d == 1) return y;
  /* k = 1, split off for efficiency */
  po2 = shifti(p,-1); /* to be left on stack */
  av = avma;
  s = gel(g,d-1+2);
  gel(y,2) = gerepileuptoint(av, centermodii(negi(s), p, po2));
  for (k = 2; k < d; k++)
  {
    av = avma;
    s = mului(k, remii(gel(g,d-k+2), p));
    for (i = 1; i < k; i++) s = addii(s, mulii(gel(y,k-i+1), gel(g,d-i+2)));
    togglesign_safe(&s);
    gel(y,k+1) = gerepileuptoint(av, centermodii(s, p, po2));
  }
  return y;
}

/* compute the c first Newton sums modulo pp of the
   characteristic polynomial of a/d mod chi, d > 0 power of p (NULL = gen_1),
   a, chi in Zp[X], vda = v_p(da)
   ns = Newton sums of chi */
static GEN
newtonsums(GEN p, GEN a, GEN da, long vda, GEN chi, long c, GEN pp, GEN ns)
{
  GEN va, pa, dpa, s;
  long j, k, vdpa;
  pari_sp av, lim;

  a = centermod(a, pp); av = avma; lim = stack_lim(av, 1);
  dpa = pa = NULL; /* -Wall */
  vdpa = 0;
  va = zerovec(c);
  for (j = 1; j <= c; j++)
  { /* pa/dpa = (a/d)^(j-1) mod (chi, pp), dpa = p^vdpa */
    long degpa;
    pa = j == 1? a: FpXQ_mul(pa, a, chi, pp);
    degpa = degpol(pa);
    if (degpa < 0) {
      for (; j <= c; j++) gel(va,j) = gen_0;
      return va;
    }

    if (da) {
      dpa = j == 1? da: mulii(dpa, da);
      vdpa += vda;
      update_den(p, &pa, &dpa, &vdpa, &pp);
    }
    s = mulii(gel(pa,2), gel(ns,1)); /* k = 0 */
    for (k=1; k<=degpa; k++) s = addii(s, mulii(gel(pa,k+2), gel(ns,k+1)));
    if (da) {
      GEN r;
      s = dvmdii(s, dpa, &r);
      if (r != gen_0) return NULL;
    }
    gel(va,j) = centermodii(s, pp, shifti(pp,-1));

    if (low_stack(lim, stack_lim(av, 1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem, "newtonsums");
      gerepileall(av, dpa?4:3, &pa, &va, &pp, &dpa);
    }
  }
  return va;
}

/* compute the characteristic polynomial of a/da mod chi (a in Z[X]), given
 * by its Newton sums to a precision of pp using Newton sums */
static GEN
newtoncharpoly(GEN pp, GEN p, GEN NS)
{
  long n = lg(NS)-1, j, k;
  GEN c = cgetg(n + 2, t_VEC);

  gel(c,1) = (n & 1 ? gen_m1: gen_1);
  for (k = 2; k <= n+1; k++)
  {
    pari_sp av2 = avma;
    GEN s = gen_0;
    ulong z;
    long v = u_pvalrem(k - 1, p, &z);
    for (j = 1; j < k; j++)
    {
      GEN t = mulii(gel(NS,j), gel(c,k-j));
      if (!odd(j)) t = negi(t);
      s = addii(s, t);
    }
    if (v) {
      s = gdiv(s, powiu(p, v));
      if (typ(s) != t_INT) return NULL;
    }
    s = mulii(s, Fp_inv(utoipos(z), pp));
    gel(c,k) = gerepileuptoint(av2, centermod(s, pp));
  }
  for (k = odd(n)? 1: 2; k <= n+1; k += 2) gel(c,k) = negi(gel(c,k));
  return gtopoly(c, 0);
}

static void
manage_cache(decomp_t *S, GEN f, GEN pp)
{
  GEN t = S->precns;

  if (!t) t = mulii(S->pmf, powiu(S->p, S->df));
  t = gmax(t, pp);

  if (! S->precns || cmpii(S->precns, t) < 0)
  {
    if (DEBUGLEVEL>4)
      err_printf("  Precision for cached Newton sums: %Ps -> %Ps\n",
                 S->precns? S->precns: gen_0, t);
    S->ns = polsymmodp(f, t);
    S->precns = t;
  }
}

/* return NULL if a mod f is not an integer
 * The denominator of any integer in Zp[X]/(f) divides pdr */
static GEN
mycaract(decomp_t *S, GEN f, GEN a, GEN pp, GEN pdr)
{
  pari_sp av;
  GEN d, chi, prec1, prec2, prec3, ns;
  long vd, n = degpol(f);

  if (gequal0(a)) return pol_0(varn(f));

  a = QpX_remove_denom(a, S->p, &d, &vd);
  prec1 = pp;
  if (lgefint(S->p) == 3)
    prec1 = mulii(prec1, powiu(S->p, factorial_lval(n, itou(S->p))));
  if (d)
  {
    GEN p1 = powiu(d, n-1);
    prec2 = mulii(prec1, p1);
    prec3 = mulii(prec1, gmin(mulii(p1, d), pdr));
  }
  else
    prec2 = prec3 = prec1;
  manage_cache(S, f, prec3);

  av = avma;
  ns = newtonsums(S->p, a, d, vd, f, n, prec2, S->ns);
  if (!ns) return NULL;
  chi = newtoncharpoly(prec1, S->p, ns);
  if (!chi) return NULL;
  setvarn(chi, varn(f));
  return gerepileupto(av, centermod(chi, pp));
}

static GEN
get_nu(GEN chi, GEN p, long *ptl)
{
  GEN P = gel(FpX_factor(chi, p),1);
  *ptl = lg(P) - 1;
  return gel(P,*ptl);
}

/* Factor characteristic polynomial of S->phi mod (p, S->chi) */
static long
factcp(decomp_t *S)
{
  GEN chi = mycaract(S, S->chi, S->phi, S->psf, S->prc);
  long l;
  S->chi = chi;
  S->nu  = get_nu(chi, S->p, &l); return l;
}

/* Return the prime element in Zp[phi], a t_INT (iff *Ep = 1) or QX;
 * nup, chip are ZX.
 * If *Ep < oE or Ep divides Ediv (!=0) return NULL (uninteresting) */
static GEN
getprime(decomp_t *S, GEN phi, GEN chip, GEN nup, long *Lp, long *Ep,
         long oE, long Ediv)
{
  GEN chin, q, qp;
  long r, s;

  if (degpol(nup) == 1)
  {
    GEN c = gel(nup,2); /* nup = X + c */
    chin = signe(c)? RgX_translate(chip, negi(c)): chip;
  }
  else
    chin = ZXQ_charpoly(nup, chip, varn(chip));

  vstar(S->p, chin, Lp, Ep);
  if (*Ep < oE || (Ediv && Ediv % *Ep == 0)) return NULL;

  if (*Ep == 1) return S->p;
  (void)cbezout(*Lp, -*Ep, &r, &s); /* = 1 */
  if (r <= 0)
  {
    long t = 1 + ((-r) / *Ep);
    r += t * *Ep;
    s += t * *Lp;
  }
  /* r > 0 minimal such that r L/E - s = 1/E
   * pi = nu^r / p^s is an element of valuation 1/E,
   * so is pi + O(p) since 1/E < 1. May compute nu^r mod p^(s+1) */
  q = powiu(S->p, s); qp = mulii(q, S->p);
  nup = FpXQ_pow(nup, utoipos(r), S->chi, qp);
  if (!phi) return RgX_Rg_div(nup, q); /* phi = X : no composition */
  return compmod(S->p, nup, phi, S->chi, qp, -s);
}

static void
kill_cache(decomp_t *S) { S->precns = NULL; }

/* S->phi := T o T0 mod (p, f) */
static void
composemod(decomp_t *S, GEN T, GEN T0) {
  S->phi = compmod(S->p, T, T0, S->f, S->p, 0);
}

static int
update_phi(decomp_t *S, long *ptl, long flag)
{
  GEN PHI = NULL, prc, psc = S->psc, X = pol_x(varn(S->f));
  GEN pdf = powiu(S->p, S->df);
  long k;

  if (!S->chi)
  {
    kill_cache(S);
    S->chi = mycaract(S, S->f, S->phi, S->psf, pdf);
    S->nu = get_nu(S->chi, S->p, ptl);
    if (*ptl > 1) return 0; /* we can get a decomposition */
  }

  for (k = 1;; k++)
  {
    kill_cache(S);
    prc = ZpX_reduced_resultant_fast(S->chi, ZX_deriv(S->chi), S->p, S->vpsc);
    if (!equalii(prc, S->psc)) break;

    /* increase precision */
    S->vpsc = maxss(S->vpsf, S->vpsc + 1);
    S->psc = (S->vpsc == S->vpsf)? S->psf: mulii(S->psc, S->p);

    PHI = S->phi0? compmod(S->p, S->phi, S->phi0, S->f, S->psc, 0)
                 : S->phi;
    PHI = gadd(PHI, ZX_Z_mul(X, mului(k, S->p)));
    S->chi = mycaract(S, S->f, PHI, S->psc, pdf);
  }
  psc = mulii(sqri(prc), S->p);
  S->chi = FpX_red(S->chi, psc);
  if (!PHI) /* ok above for k = 1 */
    PHI = S->phi0? compmod(S->p, S->phi, S->phi0, S->f, psc, 0)
                 : S->phi;
  S->phi = PHI;

  if (is_pm1(prc))
  { /* may happen if p is unramified */
    if (!flag) { *ptl = 1; return 0; }
    S->nu = get_nu(S->chi, S->p, ptl);
    return 0;
  }
  S->psc = psc;
  S->vpsc = 2*Z_pval(prc, S->p) + 1;
  S->prc = mulii(prc, S->p); return 1;
}

/* return 1 if at least 2 factors mod p ==> chi can be split
 * Replace S->phi such that F increases (to D) */
static int
testb2(decomp_t *S, long D, GEN theta)
{
  long v = varn(S->chi), dlim = degpol(S->chi)-1;
  GEN T0 = S->phi, chi0 = S->chi;

  if (DEBUGLEVEL>4) err_printf("  Increasing Fa\n");
  for (;;)
  {
    S->phi = gadd(theta, random_FpX(dlim, v, S->p));
    /* phi non-primary ? */
    if (factcp(S) > 1) { composemod(S, S->phi, T0); return 1; }
    if (degpol(S->nu) == D) break;
    S->chi = chi0;
  }
  S->phi0 = T0; return 0; /* F_phi=lcm(F_alpha, F_theta)=D and E_phi=E_alpha */
}

/* return 1 if at least 2 factors mod p ==> chi can be split.
 * compute a new S->phi such that E = lcm(Ea, Et);
 * A a ZX, T a t_INT (iff Et = 1, probably impossible ?) or QX */
static int
testc2(decomp_t *S, GEN A, long Ea, GEN T, long Et)
{
  GEN c, T0 = S->phi;

  if (DEBUGLEVEL>4) err_printf("  Increasing Ea\n");
  if (Et == 1) /* same as other branch, split for efficiency */
    c = A; /* Et = 1 => s = 1, r = 0, t = 0 */
  else
  {
    long r, s, t;
    (void)cbezout(Ea, Et, &r, &s); t = 0;
    while (r < 0) { r = r + Et; t++; }
    while (s < 0) { s = s + Ea; t++; }

    /* A^s T^r / p^t */
    c = RgXQ_mul(RgXQ_powu(A, s, S->chi), RgXQ_powu(T, r, S->chi), S->chi);
    c = RgX_Rg_div(c, powiu(S->p, t));
    c = redelt(c, S->psc, S->p);
  }
  S->phi = RgX_add(c,  pol_x(varn(S->chi)));
  if (factcp(S) > 1) { composemod(S, S->phi, T0); return 1; }
  S->phi0 = T0; return 0; /* E_phi = lcm(E_alpha,E_theta) */
}

static GEN
ch_var(GEN x, long v)
{
  if (typ(x) == t_POL) { x = leafcopy(x); setvarn(x, v); }
  return x;
}

/* x p^-eq nu^-er mod p */
static GEN
get_gamma(decomp_t *S, GEN x, long eq, long er)
{
  GEN q, g = x, Dg = powiu(S->p, eq);
  long vDg = eq;
  if (er)
  {
    if (!S->invnu)
    {
      while (gdvd(S->chi, S->nu)) S->nu = gadd(S->nu, S->p);
      S->invnu = QXQ_inv(S->nu, S->chi);
      S->invnu = redelt_i(S->invnu, S->psc, S->p, &S->Dinvnu, &S->vDinvnu);
    }
    if (S->Dinvnu) {
      Dg = mulii(Dg, powiu(S->Dinvnu, er));
      vDg += er * S->vDinvnu;
    }
    q = mulii(S->p, Dg);
    g = ZX_mul(g, FpXQ_pow(S->invnu, stoi(er), S->chi, q));
    g = FpX_rem(g, S->chi, q);
    update_den(S->p, &g, &Dg, &vDg, NULL);
    g = centermod(g, mulii(S->p, Dg));
  }
  if (!is_pm1(Dg)) g = RgX_Rg_div(g, Dg);
  return g;
}

/* return 1 if at least 2 factors mod p ==> chi can be split */
static int
loop(decomp_t *S, long nv, long Ea, long Fa)
{
  pari_sp av2 = avma, limit = stack_lim(av2, 1);
  GEN R, w, chib, beta, gamm, chig, nug, delt = NULL;
  long L, E, i, l, Fg, eq = 0, er = 0, N = degpol(S->f), v = varn(S->f);

  beta  = FpXQ_pow(S->nu, stoi(Ea), S->chi, S->p);
  S->invnu = NULL;
  chib = chig = NULL; /* -Wall */
  for (;;)
  { /* beta tends to a factor of chi */
    if (DEBUGLEVEL>4) err_printf("  beta = %Ps\n", beta);

    R = modii(ZX_resultant(beta, S->chi), S->pmf);
    if (signe(R))
    {
      chib = NULL;
      L = Z_pval(R, S->p);
      E = N;
    }
    else
    { /* pmf | norm(beta) ==> useless */
      chib = ZXQ_charpoly(beta, S->chi, v);
      vstar(S->p, chib, &L, &E);
    }
    eq = (long)(L / E);
    er = (long)(L*Ea / E - eq*Ea);
    if (DEBUGLEVEL>4) err_printf("  (eq,er) = (%ld,%ld)\n", eq,er);
    if (er || !chib)
    { /* gamm might not be an integer ==> chig = NULL */
      gamm = get_gamma(S, beta, eq, er); /* = beta p^-eq  nu^-er (a unit) */
      chig = mycaract(S, S->chi, gamm, S->psc, S->prc);
    }
    else
    { /* gamm = beta/p^eq, special case of the above */
      GEN h = powiu(S->p, eq);
      gamm = RgX_Rg_div(beta, h);
      chig = RgX_Rg_div(RgX_unscale(chib, h), powiu(h, N));
      chig = gequal1(Q_denom(chig))? FpX_red(chig, S->pmf): NULL;
    }

    if (!chig)
    { /* Valuation of beta was wrong ==> gamma fails the v*-test */
      chib = ZXQ_charpoly(beta, S->chi, v);
      vstar(S->p, chib, &L, &E);
      eq = (long)(L / E);
      er = (long)(L*Ea / E - eq*Ea);

      gamm = get_gamma(S, beta, eq, er); /* an integer */
      chig = mycaract(S, S->chi, gamm, S->psc, S->prc);
    }

    nug = get_nu(chig, S->p, &l);
    if (l > 1)
    {
      S->chi = chig;
      S->nu  = nug; composemod(S, gamm, S->phi); return 1;
    }

    Fg = degpol(nug);
    if (Fa % Fg) return testb2(S, clcm(Fa,Fg), gamm);

    /* nug irreducible mod p */
    w = FpX_factorff_irred(nug, ch_var(S->nu, nv), S->p);
    if (degpol(gel(w,1)) != 1)
      pari_err(talker, "no root in nilord. Is p = %Ps a prime?", S->p);

    for (i = 1; i < lg(w); i++)
    { /* Look for a root delt of nug in Fp[phi] such that vp(gamma - delta) > 0
         Can be used to improve beta */
      GEN eta, chie, nue, W = gel(w,i); /* monic linear polynomial */
      delt = gneg_i( ch_var(gel(W,2), v) );
      eta  = gsub(gamm, delt);

      if (typ(delt) == t_INT)
        chie = RgX_translate(chig, delt); /* frequent special case */
      else
      {
        if (!dvdii(QXQ_intnorm(eta, S->chi), S->p)) continue;
        chie = mycaract(S, S->chi, eta, S->psc, S->prc);
      }
      nue = get_nu(chie, S->p, &l);
      if (l > 1) {
        S->nu = nue;
        S->chi= chie; composemod(S, eta, S->phi); return 1;
      }

      if (RgX_is_monomial(nue))
      { /* vp(eta) = vp(gamma - delta) > 0 */
        long Le, Ee;
        GEN pie;

        if (dvdii(constant_term(chie), S->psc))
        {
          chie = mycaract(S, S->chi, eta, S->pmf, S->prc);
          if (dvdii(constant_term(chie), S->pmf))
            chie = ZXQ_charpoly(eta, S->chi, v);
        }

        pie = getprime(S, eta, chie, nue, &Le, &Ee,  0,Ea);
        if (pie) return testc2(S, S->nu, Ea, pie, Ee);
        break;
      }
    }
    if (i == lg(w))
      pari_err(talker, "no root in nilord. Is p = %Ps a prime?", S->p);

    if (eq) delt = gmul(delt, powiu(S->p,  eq));
    if (er) delt = gmul(delt, gpowgs(S->nu, er));
    beta = gsub(beta, delt);

    if (low_stack(limit,stack_lim(av2,1)))
    {
      if (DEBUGMEM > 1) pari_warn(warnmem, "nilord");
      gerepileall(av2, S->invnu? 5: 3, &beta, &(S->precns), &(S->ns), &(S->invnu), &(S->Dinvnu));
    }
  }
}

/* flag != 0 iff we're looking for the p-adic factorization,
   in which case it is the p-adic precision we want */
static GEN
nilord(decomp_t *S, GEN dred, long mf, long flag)
{
  GEN p = S->p;
  long Fa, oE, l, N  = degpol(S->f), v = varn(S->f), nv = fetch_var();
  GEN opa; /* t_INT or QX */

  if (DEBUGLEVEL>2)
  {
    err_printf("  entering Nilord");
    if (DEBUGLEVEL>4)
    {
      err_printf(" with parameters: %Ps^%ld\n", p, S->df);
      err_printf("  fx = %Ps, gx = %Ps", S->f, S->nu);
    }
    err_printf("\n");
  }

  S->psc = mulii(sqri(dred), p);
  S->vpsc= 2*S->df + 1;
  S->prc = mulii(dred, p);
  S->psf = S->psc;
  S->vpsf = S->vpsc;
  S->chi = FpX_red(S->f, S->psc);
  S->phi = pol_x(v);
  S->pmf = powiu(p, mf+1);
  S->precns = NULL;
  oE = 0;
  opa = NULL; /* -Wall */
  l = 2; /* Decomp by default */

  for(;;)
  {
    S->phi0 = NULL; /* no delayed composition */
    Fa = degpol(S->nu);
    for(;;)
    {
      long La, Ea;
      /* N.B If oE = 0, getprime cannot return NULL */
      GEN pia  = getprime(S, NULL, S->chi, S->nu, &La, &Ea, oE,0);
      if (pia) { /* success, we break out in THIS loop */
        opa = (Ea > 1)? RgX_RgXQ_eval(pia, S->phi, S->f): pia;
        oE = Ea;
        if (La == 1) break; /* no need to change phi so that nu = pia */
      }
      /* phi += prime elt */
      S->phi = typ(opa) == t_INT? RgX_Rg_add_shallow(S->phi, opa)
                                : RgX_add(S->phi, opa);
      S->chi = NULL;
      if (!update_phi(S, &l, flag)) goto DONE;
      if (pia) break;
    }

    if (DEBUGLEVEL>4) err_printf("  (Fa, oE) = (%ld,%ld)\n", Fa, oE);
    if (oE*Fa == N)
    { /* O = Zp[phi] */
      if (!flag) S->phi = redelt(S->phi, sqri(p), p);
      S->chi = NULL; l = 1; goto DONE;
    }
    l = 2;
    if (loop(S, nv, oE, Fa)) goto DONE;
    if (!update_phi(S, &l, flag)) goto DONE;
  }
DONE:
  (void)delete_var();
  if (l == 1) return flag? NULL: dbasis(p, S->f, mf, S->phi, S->chi);
  return Decomp(S, flag);
}

GEN
maxord_i(GEN p, GEN f, long mf, GEN w, long flag)
{
  long l = lg(w)-1;
  GEN h = gel(w,l); /* largest factor */
  GEN D = ZpX_reduced_resultant_fast(f, ZX_deriv(f), p, mf);
  decomp_t S;

  S.f = f;
  S.p = p;
  S.nu = h;
  S.df = Z_pval(D, p);
  if (l == 1) return nilord(&S, D, mf, flag);
  if (flag && flag <= mf) flag = mf + 1;
  S.phi = pol_x(varn(f));
  S.chi = f; return Decomp(&S, flag);
}

/* DT = multiple of disc(T) or NULL
 * Return a multiple of the denominator of an algebraic integer (in Q[X]/(T))
 * when expressed in terms of the power basis */
GEN
indexpartial(GEN T, GEN DT)
{
  pari_sp av = avma;
  long i, nb;
  GEN fa, E, P, res = gen_1, dT = ZX_deriv(T);

  if (!DT) DT = ZX_disc(T);
  DT = absi(DT);
  fa = Z_factor_limit(DT, 0);
  P = gel(fa,1);
  E = gel(fa,2); nb = lg(P)-1;
  for (i = 1; i <= nb; i++)
  {
    long e = itou(gel(E,i)), e2 = e >> 1;
    GEN p = gel(P,i), q = p;
    if (i == nb)
      q = powiu(p, (odd(e) && !BPSW_psp(p))? e2+1: e2);
    else if (e2 >= 2)
      q = ZpX_reduced_resultant_fast(T, dT, p, e2);
    res = mulii(res, q);
  }
  return gerepileuptoint(av,res);
}

/*******************************************************************/
/*                                                                 */
/*    2-ELT REPRESENTATION FOR PRIME IDEALS (dividing index)       */
/*                                                                 */
/*******************************************************************/
/* to compute norm of elt in basis form */
typedef struct {
  long r1;
  GEN M;  /* via norm_by_embed */

  GEN D, w, T; /* via resultant if M = NULL */
} norm_S;

static GEN
get_norm(norm_S *S, GEN a)
{
  if (S->M)
  {
    long e;
    GEN N = grndtoi( norm_by_embed(S->r1, RgM_RgC_mul(S->M, a)), &e );
    if (e > -5) pari_err(precer, "get_norm");
    return N;
  }
  if (S->w) a = RgV_RgC_mul(S->w, a);
  return ZX_resultant_all(S->T, a, S->D, 0);
}
static void
init_norm(norm_S *S, GEN nf, GEN p)
{
  GEN T = nf_get_pol(nf);
  long N = degpol(T);

  S->M = NULL; /* -Wall */
  S->r1 = 0;   /* -Wall */
  S->D = NULL; /* -Wall */
  S->w = NULL; /* -Wall */
  S->T = NULL; /* -Wall */
  if (typ(nf[5]) == t_VEC) /* beware dummy nf from padicff */
  {
    GEN M = nf_get_M(nf);
    long ex = gexpo(M) + gexpo(mului(8 * N, p));
    if (N * ex <= bit_accuracy(gprecision(M)))
    { /* enough prec to use norm_by_embed */
      S->M = M;
      S->r1 = nf_get_r1(nf);
    }
  }
  if (!S->M)
  {
    GEN D, w = Q_remove_denom(nf_get_zk(nf), &D), Dp = sqri(p);
    long i;
    if (!D) w = leafcopy(w);
    else {
      GEN w1 = D;
      long v = Z_pval(D, p);
      D = powiu(p, v);
      Dp = mulii(D, Dp);
      gel(w, 1) = remii(w1, Dp);
    }
    for (i=2; i<=N; i++) gel(w,i) = FpX_red(gel(w,i), Dp);
    S->D = D;
    S->w = w;
    S->T = T;
  }
}
/* f = f(pr/p), q = p^(f+1), a in pr.
 * Return 1 if v_pr(a) = 1, and 0 otherwise */
static int
is_uniformizer(GEN a, GEN q, norm_S *S)
{ return (remii(get_norm(S,a), q) != gen_0); }

/* Return x * y, x, y are t_MAT (Fp-basis of in O_K/p), assume (x,y)=1.
 * Either x or y may be NULL (= O_K), not both */
static GEN
mul_intersect(GEN x, GEN y, GEN p)
{
  if (!x) return y;
  if (!y) return x;
  return FpM_intersect(x, y, p);
}
/* Fp-basis of (ZK/pr): applied to the primes found in primedec_aux() */
static GEN
Fp_basis(GEN nf, GEN pr)
{
  long i, j, l;
  GEN x, y;
  /* already in basis form (from Buchman-Lenstra) ? */
  if (typ(pr) == t_MAT) return pr;
  /* ordinary prid (from Kummer) */
  x = idealhnf_two(nf, pr);
  l = lg(x);
  y = cgetg(l, t_MAT);
  for (i=j=1; i<l; i++)
    if (gequal1(gcoeff(x,i,i))) y[j++] = x[i];
  setlg(y, j); return y;
}
/* Let Ip = prod_{ P | p } P be the p-radical. The list L contains the
 * P (mod Ip) seen as sub-Fp-vector spaces of ZK/Ip.
 * Return the list of (Ip / P) (mod Ip).
 * N.B: All ideal multiplications are computed as intersections of Fp-vector
 * spaces. */
static GEN
get_LV(GEN nf, GEN L, GEN p, long N)
{
  long i, l = lg(L)-1;
  GEN LV, LW, A, B;

  LV = cgetg(l+1, t_VEC);
  if (l == 1) { gel(LV,1) = matid(N); return LV; }
  LW = cgetg(l+1, t_VEC);
  for (i=1; i<=l; i++) gel(LW,i) = Fp_basis(nf, gel(L,i));

  /* A[i] = L[1]...L[i-1], i = 2..l */
  A = cgetg(l+1, t_VEC); gel(A,1) = NULL;
  for (i=1; i < l; i++) gel(A,i+1) = mul_intersect(gel(A,i), gel(LW,i), p);
  /* B[i] = L[i+1]...L[l], i = 1..(l-1) */
  B = cgetg(l+1, t_VEC); gel(B,l) = NULL;
  for (i=l; i>=2; i--) gel(B,i-1) = mul_intersect(gel(B,i), gel(LW,i), p);
  for (i=1; i<=l; i++) gel(LV,i) = mul_intersect(gel(A,i), gel(B,i), p);
  return LV;
}

static void
errprime(GEN p) { pari_err(talker, "idealprimedec: %Ps is not prime", p); }

/* P = Fp-basis (over O_K/p) for pr.
 * V = Z-basis for I_p/pr. ramif != 0 iff some pr|p is ramified.
 * Return a p-uniformizer for pr. Assume pr not inert, i.e. m > 0 */
static GEN
uniformizer(GEN nf, norm_S *S, GEN P, GEN V, GEN p, int ramif)
{
  long i, l, f, m = lg(P)-1, N = nf_get_degree(nf);
  GEN u, Mv, x, q;

  f = N - m; /* we want v_p(Norm(x)) = p^f */
  q = powiu(p,f+1);

  u = FpM_invimage(shallowconcat(P, V), col_ei(N,1), p);
  setlg(u, lg(P));
  u = centermod(ZM_ZC_mul(P, u), p);
  if (is_uniformizer(u, q, S)) return u;
  if (signe(u[1]) <= 0) /* make sure u[1] in ]-p,p] */
    gel(u,1) = addii(gel(u,1), p); /* try u + p */
  else
    gel(u,1) = subii(gel(u,1), p); /* try u - p */
  if (!ramif || is_uniformizer(u, q, S)) return u;

  /* P/p ramified, u in P^2, not in Q for all other Q|p */
  Mv = zk_multable(nf, unnf_minus_x(u));
  l = lg(P);
  for (i=1; i<l; i++)
  {
    x = centermod(ZC_add(u, ZM_ZC_mul(Mv, gel(P,i))), p);
    if (is_uniformizer(x, q, S)) return x;
  }
  errprime(p);
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                   BUCHMANN-LENSTRA ALGORITHM                    */
/*                                                                 */
/*******************************************************************/
static GEN
mk_pr(GEN p, GEN u, long e, long f, GEN t)
{ return mkvec5(p, u, utoipos(e), utoipos(f), t); }

/* pr = (p,u) of ramification index e */
GEN
primedec_apply_kummer(GEN nf,GEN u,long e,GEN p)
{
  GEN t, T = nf_get_pol(nf);
  long f = degpol(u), N = degpol(T);

  if (f == N) /* inert */
  {
    u = scalarcol_shallow(p,N);
    t = gen_1;
  }
  else
  { /* make sure v_pr(u) = 1 (automatic if e>1) */
    t = poltobasis(nf, FpX_div(T,u,p));
    t = centermod(t, p);
    u = FpX_center(u, p, shifti(p,-1));
    if (e == 1)
    {
      norm_S S;
      S.D = S.w = S.M = NULL; S.T = T;
      if (!is_uniformizer(u, powiu(p,f+1), &S)) gel(u,2) = addii(gel(u,2), p);
    }
    u = poltobasis(nf,u);
  }
  return mk_pr(p,u,e,f,t);
}

/* return a Z basis of Z_K's p-radical, phi = x--> x^p-x */
static GEN
pradical(GEN nf, GEN p, GEN *phi)
{
  long i, N = nf_get_degree(nf);
  GEN q,m,frob,rad;

  /* matrix of Frob: x->x^p over Z_K/p */
  frob = cgetg(N+1,t_MAT);
  for (i=1; i<=N; i++)
    gel(frob,i) = pow_ei_mod_p(nf,i,p, p);

  m = frob; q = p;
  while (cmpiu(q,N) < 0) { q = mulii(q,p); m = FpM_mul(m, frob, p); }
  rad = FpM_ker(m, p); /* m = Frob^k, s.t p^k >= N */
  for (i=1; i<=N; i++)
    gcoeff(frob,i,i) = subis(gcoeff(frob,i,i), 1);
  *phi = frob; return rad;
}

/* return powers of a: a^0, ... , a^d,  d = dim A */
static GEN
get_powers(GEN mul, GEN p)
{
  long i, d = lg(mul[1]);
  GEN z, pow = cgetg(d+2,t_MAT), P = pow+1;

  gel(P,0) = scalarcol_shallow(gen_1, d-1);
  z = gel(mul,1);
  for (i=1; i<=d; i++)
  {
    gel(P,i) = z; /* a^i */
    if (i!=d) z = FpM_FpC_mul(mul, z, p);
  }
  return pow;
}

/* minimal polynomial of a in A (dim A = d).
 * mul = multiplication table by a in A */
static GEN
pol_min(GEN mul, GEN p)
{
  pari_sp av = avma;
  GEN z = FpM_deplin(get_powers(mul, p), p);
  return gerepilecopy(av, RgV_to_RgX(z,0));
}

static GEN
get_pr(GEN nf, norm_S *S, GEN p, GEN P, GEN V, int ramif)
{
  GEN u, t;
  long e, f, N;

  if (typ(P) == t_VEC) return P; /* already done (Kummer) */
  N = nf_get_degree(nf);
  f = N - (lg(P)-1);
  if (f == N)
    return mk_pr(p,scalarcol_shallow(p,N),1,f,gen_1);

  u = uniformizer(nf, S, P, V, p, ramif);
  /* P = (p,u) prime. t is an anti-uniformizer: Z_K + t/p Z_K = P^(-1) */
  t = FpM_deplin(zk_multable(nf, u), p);
  e = ramif? 1 + int_elt_val(nf,t,p,t,NULL): 1;
  return mk_pr(p,u,e,f,t);
}

/* prime ideal decomposition of p */
static GEN
primedec_aux(GEN nf, GEN p)
{
  GEN E, F, L, Ip, H, phi, mat1, f, g, h, p1, UN, T = nf_get_pol(nf);
  long i, k, c, iL, N;

  F = FpX_factor(T, p);
  E = gel(F,2);
  F = gel(F,1);

  k = lg(F); if (k == 1) errprime(p);
  if ( !dvdii(nf_get_index(nf),p) ) /* p doesn't divide index */
  {
    L = cgetg(k,t_VEC);
    for (i=1; i<k; i++)
      gel(L,i) = primedec_apply_kummer(nf,gel(F,i), E[i],p);
    return L;
  }

  g = FpXV_prod(F, p);
  h = FpX_div(T,g,p);
  f = FpX_red(ZX_Z_divexact(ZX_sub(ZX_mul(g,h), T), p), p);

  N = degpol(T);
  L = cgetg(N+1,t_VEC); iL = 1;
  for (i=1; i<k; i++)
    if (E[i] == 1 || signe(FpX_rem(f,gel(F,i),p)))
      gel(L,iL++) = primedec_apply_kummer(nf,gel(F,i), E[i],p);
    else /* F[i] | (f,g,h), happens at least once by Dedekind criterion */
      E[i] = 0;

  /* phi matrix of x -> x^p - x in algebra Z_K/p */
  Ip = pradical(nf,p,&phi);

  /* split etale algebra Z_K / (p,Ip) */
  h = cgetg(N+1,t_VEC);
  if (iL > 1)
  { /* split off Kummer factors */
    GEN mulbeta, beta = NULL;
    for (i=1; i<k; i++)
      if (!E[i]) beta = beta? FpX_mul(beta, gel(F,i), p): gel(F,i);
    if (!beta) errprime(p);
    beta = FpC_red(poltobasis(nf,beta), p);

    mulbeta = FpM_red(zk_multable(nf, beta), p);
    p1 = shallowconcat(mulbeta, Ip);
    /* Fp-base of ideal (Ip, beta) in ZK/p */
    gel(h,1) = FpM_image(p1, p);
  }
  else
    gel(h,1) = Ip;

  UN = col_ei(N, 1);
  for (c=1; c; c--)
  { /* Let A:= (Z_K/p) / Ip; try to split A2 := A / Im H ~ Im M2
       H * ? + M2 * Mi2 = Id_N ==> M2 * Mi2 projector A --> A2 */
    GEN M, Mi, M2, Mi2, phi2;
    long dim;

    H = gel(h,c); k = lg(H)-1;
    M   = FpM_suppl(shallowconcat(H,UN), p);
    Mi  = FpM_inv(M, p);
    M2  = vecslice(M, k+1,N); /* M = (H|M2) invertible */
    Mi2 = rowslice(Mi,k+1,N);
    /* FIXME: FpM_mul(,M2) could be done with vecpermute */
    phi2 = FpM_mul(Mi2, FpM_mul(phi,M2, p), p);
    mat1 = FpM_ker(phi2, p);
    dim = lg(mat1)-1; /* A2 product of 'dim' fields */
    if (dim > 1)
    { /* phi2 v = 0 <==> a = M2 v in Ker phi */
      GEN R, a, mula, mul2, v = gel(mat1,2);
      long n;

      a = FpM_FpC_mul(M2,v, p);
      mula = zk_scalar_or_multable(nf, a); /* not a scalar */
      mula = FpM_red(mula, p);
      mul2 = FpM_mul(Mi2, FpM_mul(mula,M2, p), p);
      R = FpX_roots(pol_min(mul2,p), p); /* totally split mod p */

      n = lg(R)-1;
      for (i=1; i<=n; i++)
      {
        GEN r = gel(R,i), I = RgM_Rg_add_shallow(mula, negi(r));
        gel(h,c++) = FpM_image(shallowconcat(H, I), p);
      }
      if (n == dim)
        for (i=1; i<=n; i++) { H = gel(h,--c); gel(L,iL++) = H; }
    }
    else /* A2 field ==> H maximal, f = N-k = dim(A2) */
      gel(L,iL++) = H;
  }
  setlg(L, iL);
{
  GEN Lpr = cgetg(iL, t_VEC);
  GEN LV = get_LV(nf, L,p,N);
  int ramif = dvdii(nf_get_disc(nf), p);
  norm_S S; init_norm(&S, nf, p);
  for (i=1; i<iL; i++)
    gel(Lpr,i) = get_pr(nf, &S, p, gel(L,i), gel(LV,i), ramif);
  return Lpr;
}
}

GEN
idealprimedec(GEN nf, GEN p)
{
  pari_sp av = avma;
  if (typ(p) != t_INT) pari_err(typeer, "idealprimedec");
  return gerepileupto(av, gen_sort(primedec_aux(checknf(nf),p),
                                   (void*)&cmp_prime_over_p, &cmp_nodata));
}

/* return [Fp[x]: Fp] */
static long
ffdegree(GEN x, GEN frob, GEN p)
{
  pari_sp av = avma;
  long d, f = lg(frob)-1;
  GEN y = x;

  for (d=1; d < f; d++)
  {
    y = FpM_FpC_mul(frob, y, p);
    if (ZV_equal(y, x)) break;
  }
  avma = av; return d;
}

static GEN
lift_to_zk(GEN v, GEN c, long N)
{
  GEN w = zerocol(N);
  long i, l = lg(c);
  for (i=1; i<l; i++) w[c[i]] = v[i];
  return w;
}

/* return integral x = 0 mod p/pr^e, (x,pr) = 1.
 * Don't reduce mod p here: caller may need result mod pr^k */
GEN
special_anti_uniformizer(GEN nf, GEN pr)
{
  GEN b = pr_get_tau(pr);
  long e = pr_get_e(pr);
  if (e == 1) return b;
  return ZC_Z_divexact(nfpow_u(nf, b, e), powiu(pr_get_p(pr), e-1));
}

/* return t = 1 mod pr, t = 0 mod p / pr^e(pr/p) */
static GEN
anti_uniformizer2(GEN nf, GEN pr)
{
  GEN p = pr_get_p(pr), z;
  long N = nf_get_degree(nf), e = pr_get_e(pr), f = pr_get_f(pr);
  if (e*f == N) return col_ei(N, 1);

  z = FpC_red(special_anti_uniformizer(nf, pr), p);
  z = zk_scalar_or_multable(nf, z); /* not a scalar */
  z = ZM_hnfmodid(z, p);
  z = idealaddtoone_i(nf, pr, z);
  return unnf_minus_x(z);
}

#define mpr_TAU 1
#define mpr_FFP 2
#define mpr_PR  3
#define mpr_T   4
#define mpr_NFP 5
#define SMALLMODPR 4
#define LARGEMODPR 6
static GEN
modpr_TAU(GEN modpr)
{
  GEN tau = gel(modpr,mpr_TAU);
  return isintzero(tau)? NULL: tau;
}

/* prh = HNF matrix, which is identity but for the first line. Return a
 * projector to ZK / prh ~ Z/prh[1,1] */
GEN
dim1proj(GEN prh)
{
  long i, N = lg(prh)-1;
  GEN ffproj = cgetg(N+1, t_VEC);
  GEN x, q = gcoeff(prh,1,1);
  gel(ffproj,1) = gen_1;
  for (i=2; i<=N; i++)
  {
    x = gcoeff(prh,1,i);
    if (signe(x)) x = subii(q,x);
    gel(ffproj,i) = x;
  }
  return ffproj;
}

/* p not necessarily prime, but coprime to denom(basis) */
GEN
get_proj_modT(GEN basis, GEN T, GEN p)
{
  long i, l = lg(basis), f = degpol(T);
  GEN z = cgetg(l, t_MAT);
  for (i = 1; i < l; i++)
  {
    GEN cx, w = gel(basis,i);
    if (typ(w) != t_INT)
    {
      w = Q_primitive_part(w, &cx);
      w = FpXQ_red(w, T, p);
      if (cx) w = FpX_Fp_mul(w, Rg_to_Fp(cx, p), p);
    }
    gel(z,i) = RgX_to_RgV(w, f); /* w_i mod (T,p) */
  }
  return z;
}

/* initialize reduction mod pr; if zk = 1, will only init data required to
 * reduce *integral* element.  Realize (O_K/pr) as Fp[X] / (T), for a
 * *monic* T */
static GEN
modprinit(GEN nf, GEN pr, int zk)
{
  pari_sp av = avma;
  GEN res, tau, mul, x, p, T, pow, ffproj, nfproj, prh, c;
  long N, i, k, f;

  nf = checknf(nf); checkprid(pr);
  f = pr_get_f(pr);
  N = nf_get_degree(nf);
  prh = idealhnf_two(nf, pr);
  tau = zk? gen_0: anti_uniformizer2(nf, pr);
  p = pr_get_p(pr);

  if (f == 1)
  {
    res = cgetg(SMALLMODPR, t_COL);
    gel(res,mpr_TAU) = tau;
    gel(res,mpr_FFP) = dim1proj(prh);
    gel(res,mpr_PR) = pr; return gerepilecopy(av, res);
  }

  c = cgetg(f+1, t_VECSMALL);
  ffproj = cgetg(N+1, t_MAT);
  for (k=i=1; i<=N; i++)
  {
    x = gcoeff(prh, i,i);
    if (!is_pm1(x)) { c[k] = i; gel(ffproj,i) = col_ei(N, i); k++; }
    else
      gel(ffproj,i) = ZC_neg(gel(prh,i));
  }
  ffproj = rowpermute(ffproj, c);
  if (! dvdii(nf_get_index(nf), p))
  {
    GEN basis = nf_get_zk(nf);
    if (N == f) T = nf_get_pol(nf); /* pr inert */
    else
    {
      T = RgV_RgC_mul(Q_primpart(basis), pr_get_gen(pr));
      T = FpX_normalize(T,p);
      basis = vecpermute(basis, c);
    }
    T = FpX_red(T, p);
    ffproj = FpM_mul(get_proj_modT(basis, T, p), ffproj, p);

    res = cgetg(SMALLMODPR+1, t_COL);
    gel(res,mpr_TAU) = tau;
    gel(res,mpr_FFP) = ffproj;
    gel(res,mpr_PR) = pr;
    gel(res,mpr_T) = T; return gerepilecopy(av, res);
  }

  if (uisprime(f))
  {
    mul = ei_multable(nf, c[2]);
    mul = vecpermute(mul, c);
  }
  else
  {
    GEN v, u, u2, frob;
    long deg,deg1,deg2;

    /* matrix of Frob: x->x^p over Z_K/pr = < w[c1], ..., w[cf] > over Fp */
    frob = cgetg(f+1, t_MAT);
    for (i=1; i<=f; i++)
    {
      x = pow_ei_mod_p(nf,c[i],p, p);
      gel(frob,i) = FpM_FpC_mul(ffproj, x, p);
    }
    u = col_ei(f,2); k = 2;
    deg1 = ffdegree(u, frob, p);
    while (deg1 < f)
    {
      k++; u2 = col_ei(f, k);
      deg2 = ffdegree(u2, frob, p);
      deg = clcm(deg1,deg2);
      if (deg == deg1) continue;
      if (deg == deg2) { deg1 = deg2; u = u2; continue; }
      u = ZC_add(u, u2);
      while (ffdegree(u, frob, p) < deg) u = ZC_add(u, u2);
      deg1 = deg;
    }
    v = lift_to_zk(u,c,N);

    mul = cgetg(f+1,t_MAT);
    gel(mul,1) = v; /* assume w_1 = 1 */
    for (i=2; i<=f; i++) gel(mul,i) = zk_ei_mul(nf,v,c[i]);
  }

  /* Z_K/pr = Fp(v), mul = mul by v */
  mul = FpM_red(mul, p);
  mul = FpM_mul(ffproj, mul, p);

  pow = get_powers(mul, p);
  T = RgV_to_RgX(FpM_deplin(pow, p), nf_get_varn(nf));
  nfproj = cgetg(f+1, t_MAT);
  for (i=1; i<=f; i++) gel(nfproj,i) = lift_to_zk(gel(pow,i), c, N);
  nfproj = coltoliftalg(nf, nfproj);

  setlg(pow, f+1);
  ffproj = FpM_mul(FpM_inv(pow, p), ffproj, p);

  res = cgetg(LARGEMODPR, t_COL);
  gel(res,mpr_TAU) = tau;
  gel(res,mpr_FFP) = ffproj;
  gel(res,mpr_PR) = pr;
  gel(res,mpr_T) = T;
  gel(res,mpr_NFP) = nfproj; return gerepilecopy(av, res);
}

GEN
nfmodprinit(GEN nf, GEN pr) { return modprinit(nf, pr, 0); }
GEN
zkmodprinit(GEN nf, GEN pr) { return modprinit(nf, pr, 1); }

void
checkmodpr(GEN modpr)
{
  if (typ(modpr) != t_COL || lg(modpr) < SMALLMODPR)
    pari_err(talker,"incorrect modpr format");
  checkprid(gel(modpr,mpr_PR));
}


static GEN
to_ff_init(GEN nf, GEN *pr, GEN *T, GEN *p, int zk)
{
  GEN modpr = (typ(*pr) == t_COL)? *pr: modprinit(nf, *pr, zk);
  *T = lg(modpr)==SMALLMODPR? NULL: gel(modpr,mpr_T);
  *pr = gel(modpr,mpr_PR);
  *p = gel(*pr,1); return modpr;
}

/* Return an element of O_K which is set to x Mod T */
GEN
modpr_genFq(GEN modpr)
{
  switch(lg(modpr))
  {
    case SMALLMODPR: /* Fp */
      return gen_1;
    case LARGEMODPR:  /* painful case, p \mid index */
      return gmael(modpr,mpr_NFP, 2);
    default: /* trivial case : p \nmid index */
    {
      long v = varn( gel(modpr, mpr_T) );
      return pol_x(v);
    }
  }
}

GEN
nf_to_Fq_init(GEN nf, GEN *pr, GEN *T, GEN *p) {
  GEN modpr = to_ff_init(nf,pr,T,p,0);
  GEN tau = modpr_TAU(modpr);
  if (!tau) gel(modpr,mpr_TAU) = anti_uniformizer2(nf, *pr);
  return modpr;
}
GEN
zk_to_Fq_init(GEN nf, GEN *pr, GEN *T, GEN *p) {
  return to_ff_init(nf,pr,T,p,1);
}

/* assume x in 'basis' form (t_COL) */
GEN
zk_to_Fq(GEN x, GEN modpr)
{
  GEN pr = gel(modpr,mpr_PR), p = pr_get_p(pr);
  GEN ffproj = gel(modpr,mpr_FFP);
  if (lg(modpr) == SMALLMODPR) return FpV_dotproduct(ffproj,x, p);
  return FpM_FpC_mul_FpX(ffproj,x, p, varn(modpr[mpr_T]));
}

/* REDUCTION Modulo a prime ideal */

/* x integral, reduce mod prh in HNF */
GEN
nfreducemodpr_i(GEN x, GEN prh)
{
  GEN p = gcoeff(prh,1,1);
  long i,j;

  x = leafcopy(x);
  for (i=lg(x)-1; i>=2; i--)
  {
    GEN t = gel(prh,i), p1 = remii(gel(x,i), p);
    gel(x,i) = p1;
    if (signe(p1) && is_pm1(gel(t,i)))
    {
      for (j=1; j<i; j++)
        gel(x,j) = subii(gel(x,j), mulii(p1, gel(t,j)));
      gel(x,i) = gen_0;
    }
  }
  gel(x,1) = remii(gel(x,1), p); return x;
}

/* nf a true nf */
static GEN
Rg_to_ff(GEN nf, GEN x, GEN modpr)
{
  GEN den, pr = gel(modpr,mpr_PR), p = pr_get_p(pr);
  long tx = typ(x);

  if (tx == t_POLMOD) { x = gel(x,2); tx = typ(x); }
  switch(tx)
  {
    case t_INT: return modii(x, p);
    case t_FRAC: return Rg_to_Fp(x, p);
    case t_POL:
      if (lg(x) == 3) return Rg_to_Fp(gel(x,2), p);
      x = Q_remove_denom(x, &den);
      x = poltobasis(nf, x);
      break;
    case t_COL:
      x = Q_remove_denom(x, &den);
      if (lg(x) == lg(nf_get_zk(nf))) break;
    default: pari_err(typeer,"Rg_to_ff");
  }
  if (den)
  {
    long v = Z_pvalrem(den, p, &den);
    if (v)
    {
      GEN tau = modpr_TAU(modpr);
      if (!tau) pari_err(talker,"modpr initialized for integers only!");
      x = nfmuli(nf,x, nfpow_u(nf, tau, v));
      x = ZC_Z_divexact(x, powiu(p, v));
    }
    if (!is_pm1(den)) x = ZC_Z_mul(x, Fp_inv(den, p));
    x = FpC_red(x, p);
  }
  return zk_to_Fq(x, modpr);
}

GEN
nfreducemodpr(GEN nf, GEN x, GEN modpr)
{
  pari_sp av = avma;
  nf = checknf(nf); checkmodpr(modpr);
  return gerepileupto(av, algtobasis(nf, Fq_to_nf(Rg_to_ff(nf,x,modpr),modpr)));
}

/* lift A from residue field to nf */
GEN
Fq_to_nf(GEN A, GEN modpr)
{
  long dA;
  if (typ(A) == t_INT || lg(modpr) < LARGEMODPR) return A;
  dA = degpol(A);
  if (dA <= 0) return dA ? gen_0: gel(A,2);
  return mulmat_pol(gel(modpr,mpr_NFP), A);
}
GEN
FqV_to_nfV(GEN A, GEN modpr)
{
  long i,l = lg(A);
  GEN B = cgetg(l,typ(A));
  for (i=1; i<l; i++) gel(B,i) = Fq_to_nf(gel(A,i), modpr);
  return B;
}
GEN
FqM_to_nfM(GEN A, GEN modpr)
{
  long i,j,h,l = lg(A);
  GEN B = cgetg(l, t_MAT);

  if (l == 1) return B;
  h = lg(A[1]);
  for (j=1; j<l; j++)
  {
    GEN Aj = gel(A,j), Bj = cgetg(h,t_COL); gel(B,j) = Bj;
    for (i=1; i<h; i++) gel(Bj,i) = Fq_to_nf(gel(Aj,i), modpr);
  }
  return B;
}
GEN
FqX_to_nfX(GEN A, GEN modpr)
{
  long i, l;
  GEN B;

  if (typ(A)!=t_POL) return icopy(A); /* scalar */
  B = cgetg_copy(A, &l); B[1] = A[1];
  for (i=2; i<l; i++) gel(B,i) = Fq_to_nf(gel(A,i), modpr);
  return B;
}

/* reduce A to residue field */
GEN
nf_to_Fq(GEN nf, GEN A, GEN modpr)
{
  pari_sp av = avma;
  return gerepileupto(av, Rg_to_ff(checknf(nf), A, modpr));
}
/* A t_VEC/t_COL */
GEN
nfV_to_FqV(GEN A, GEN nf,GEN modpr)
{
  long i,l = lg(A);
  GEN B = cgetg(l,typ(A));
  for (i=1; i<l; i++) gel(B,i) = nf_to_Fq(nf,gel(A,i), modpr);
  return B;
}
/* A  t_MAT */
GEN
nfM_to_FqM(GEN A, GEN nf,GEN modpr)
{
  long i,j,h,l = lg(A);
  GEN B = cgetg(l,t_MAT);

  if (l == 1) return B;
  h = lg(A[1]);
  for (j=1; j<l; j++)
  {
    GEN Aj = gel(A,j), Bj = cgetg(h,t_COL); gel(B,j) = Bj;
    for (i=1; i<h; i++) gel(Bj,i) = nf_to_Fq(nf, gel(Aj,i), modpr);
  }
  return B;
}
/* A t_POL */
GEN
nfX_to_FqX(GEN A, GEN nf,GEN modpr)
{
  long i,l = lg(A);
  GEN B = cgetg(l,t_POL); B[1] = A[1];
  for (i=2; i<l; i++) gel(B,i) = nf_to_Fq(nf,gel(A,i),modpr);
  return normalizepol_lg(B, l);
}

/*******************************************************************/
/*                                                                 */
/*                       RELATIVE ROUND 2                          */
/*                                                                 */
/*******************************************************************/

static void
fill(long l, GEN H, GEN Hx, GEN I, GEN Ix)
{
  long i;
  if (typ(Ix) == t_VEC) /* standard */
    for (i=1; i<l; i++) { gel(H,i) = gel(Hx,i); gel(I,i) = gel(Ix,i); }
  else /* constant ideal */
    for (i=1; i<l; i++) { gel(H,i) = gel(Hx,i); gel(I,i) = Ix; }
}

/* given MODULES x and y by their pseudo-bases, returns a pseudo-basis of the
 * module generated by x and y. */
static GEN
rnfjoinmodules_i(GEN nf, GEN Hx, GEN Ix, GEN Hy, GEN Iy)
{
  long lx = lg(Hx), ly = lg(Hy), l = lx+ly-1;
  GEN H = cgetg(l, t_MAT), I = cgetg(l, t_VEC);
  fill(lx, H     , Hx, I     , Ix);
  fill(ly, H+lx-1, Hy, I+lx-1, Iy); return nfhnf(nf, mkvec2(H, I));
}
static GEN
rnfjoinmodules(GEN nf, GEN x, GEN y)
{
  if (!x) return y;
  if (!y) return x;
  return rnfjoinmodules_i(nf, gel(x,1), gel(x,2), gel(y,1), gel(y,2));
}

typedef struct {
  GEN multab, T,p;
  long h;
} rnfeltmod_muldata;

static GEN
_sqr(void *data, GEN x)
{
  rnfeltmod_muldata *D = (rnfeltmod_muldata *) data;
  GEN z = x? tablesqr(D->multab,x)
           : tablemul_ei_ej(D->multab,D->h,D->h);
  return FqV_red(z,D->T,D->p);
}
static GEN
_msqr(void *data, GEN x)
{
  GEN x2 = _sqr(data, x), z;
  rnfeltmod_muldata *D = (rnfeltmod_muldata *) data;
  z = tablemul_ei(D->multab, x2, D->h);
  return FqV_red(z,D->T,D->p);
}

/* Compute W[h]^n mod (T,p) in the extension, assume n >= 0. T a ZX */
static GEN
rnfelementid_powmod(GEN multab, long h, GEN n, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN y;
  rnfeltmod_muldata D;

  if (!signe(n)) return gen_1;

  D.multab = multab;
  D.h = h;
  D.T = T;
  D.p = p;
  y = leftright_pow_fold(NULL, n, (void*)&D, &_sqr, &_msqr);
  return gerepilecopy(av, y);
}

/* P != 0 has at most degpol(P) roots. Look for an element in Fq which is not
 * a root, cf repres() */
static GEN
FqX_non_root(GEN P, GEN T, GEN p)
{
  long dP = degpol(P), f, vT;
  long i, j, k, pi, pp;
  GEN v;

  if (dP == 0) return gen_1;
  pp = is_bigint(p) ? dP+1: itos(p);
  v = cgetg(dP + 2, t_VEC);
  gel(v,1) = gen_0;
  if (T)
  { f = degpol(T); vT = varn(T); }
  else
  { f = 1; vT = 0; }
  for (i=pi=1; i<=f; i++,pi*=pp)
  {
    GEN gi = i == 1? gen_1: monomial(gen_1, i-1, vT), jgi = gi;
    for (j=1; j<pp; j++)
    {
      for (k=1; k<=pi; k++)
      {
        GEN z = Fq_add(gel(v,k), jgi, T,p);
        if (!gequal0(FqX_eval(P, z, T,p))) return z;
        gel(v, j*pi+k) = z;
      }
      if (j < pp-1) jgi = Fq_add(jgi, gi, T,p); /* j*g[i] */
    }
  }
  return NULL;
}

/* Relative Dedekind criterion over (true) nf, applied to the order defined by a
 * root of monic irreducible polynomial P, modulo the prime ideal pr. Assume
 * vdisc = v_pr( disc(P) ).
 * Return NULL if nf[X]/P is pr-maximal. Otherwise, return [flag, O, v]:
 *   O = enlarged order, given by a pseudo-basis
 *   flag = 1 if O is proven pr-maximal (may be 0 and O nevertheless pr-maximal)
 *   v = v_pr(disc(O)). */
static GEN
rnfdedekind_i(GEN nf, GEN P, GEN pr, long vdisc, long only_maximal)
{
  GEN Ppr, A, I, p, tau, g, h, k, base, T, gzk, hzk, prinvp, pal, nfT, modpr;
  long m, vt, r, d, i, j, mpr;

  if (vdisc < 0)
    pari_err(talker,"relative polynomial with non-integral coefficients");
  if (vdisc == 1) return NULL; /* pr-maximal */
  if (!only_maximal && !gequal1(leading_term(P)))
    pari_err(impl, "the full Dedekind criterion in the non-monic case");
  /* either monic OR only_maximal = 1 */
  m = degpol(P);
  nfT = nf_get_pol(nf);
  modpr = nf_to_Fq_init(nf,&pr, &T, &p);
  Ppr = nfX_to_FqX(P, nf, modpr);
  mpr = degpol(Ppr);
  if (mpr < m) /* non-monic => only_maximal = 1 */
  {
    if (mpr < 0) return NULL;
    if (! RgX_valrem(Ppr, &Ppr))
    { /* non-zero constant coefficient */
      Ppr = RgX_shift_shallow(RgX_recip_shallow(Ppr), m - mpr);
      P = RgX_recip_shallow(P);
    }
    else
    {
      GEN z = FqX_non_root(Ppr, T, p);
      if (!z) pari_err(impl, "Dedekind in the difficult case");
      z = Fq_to_nf(z, modpr);
      if (typ(z) == t_INT)
        P = RgX_translate(P, z);
      else
        P = RgXQX_translate(P, z, T);
      P = RgX_recip_shallow(P);
      Ppr = nfX_to_FqX(P, nf, modpr); /* degpol(P) = degpol(Ppr) = m */
    }
  }
  A = gel(FqX_factor(Ppr,T,p),1);
  r = lg(A); /* > 1 */
  g = gel(A,1);
  for (i=2; i<r; i++) g = FqX_mul(g, gel(A,i), T, p);
  h = FqX_div(Ppr,g, T, p);
  gzk = FqX_to_nfX(g, modpr);
  hzk = FqX_to_nfX(h, modpr);

  k = gsub(P, RgXQX_mul(gzk,hzk, nfT));
  tau = pr_get_tau(pr);
  if (typ(tau) == t_INT)
    k = gdiv(k, p);
  else
  {
    tau = coltoliftalg(nf, tau);
    k = gdiv(RgXQX_RgXQ_mul(k, tau, nfT), p);
  }
  k = nfX_to_FqX(k, nf, modpr);
  k  = FqX_normalize(FqX_gcd(FqX_gcd(g,h,  T,p), k, T,p), T,p);
  d = degpol(k);  /* <= m */
  if (!d) return NULL; /* pr-maximal */
  if (only_maximal) return gen_0; /* not maximal */

  A = cgetg(m+d+1,t_MAT);
  I = cgetg(m+d+1,t_VEC); base = mkvec2(A, I);
 /* base[2] temporarily multiplied by p, for the final nfhnfmod,
  * which requires integral ideals */
  prinvp = pidealprimeinv(nf,pr); /* again multiplied by p */
  for (j=1; j<=m; j++)
  {
    gel(A,j) = col_ei(m, j);
    gel(I,j) = p;
  }
  pal = FqX_to_nfX(FqX_div(Ppr,k, T,p), modpr);
  for (   ; j<=m+d; j++)
  {
    gel(A,j) = RgX_to_RgV(pal,m);
    gel(I,j) = prinvp;
    if (j < m+d) pal = RgXQX_rem(RgX_shift(pal,1),P,nfT);
  }
  /* the modulus is integral */
  base = nfhnfmod(nf,base, ZM_Z_mul(idealpows(nf, prinvp, d), powiu(p, m-d)));
  gel(base,2) = gdiv(gel(base,2), p); /* cancel the factor p */
  vt = vdisc - 2*d;
  return mkvec3(vt < 2? gen_1: gen_0, base, stoi(vt));
}

/* [L:K] = n */
static GEN
triv_order(long n)
{
  GEN z = cgetg(3, t_VEC);
  gel(z,1) = matid(n);
  gel(z,2) = const_vec(n, gen_1); return z;
}

/* if flag is set, return gen_1 (resp. gen_0) if the order K[X]/(P)
 * is pr-maximal (resp. not pr-maximal). */
GEN
rnfdedekind(GEN nf, GEN P, GEN pr, long flag)
{
  pari_sp av = avma;
  long v;
  GEN z, dP;

  nf = checknf(nf);
  P = rnf_fix_pol(nf_get_pol(nf), P, 0);
  dP = RgX_disc(P); P = lift_intern(P);
  if (!pr) {
    GEN fa = idealfactor(nf, dP);
    GEN Q = gel(fa,1), E = gel(fa,2);
    pari_sp av2 = avma;
    long i, l = lg(Q);
    for (i=1; i < l; i++)
    {
      v = itos(gel(E,i));
      if (rnfdedekind_i(nf,P,gel(Q,i),v,1)) { avma=av; return gen_0; }
      avma = av2;
    }
    avma = av; return gen_1;
  } else if (typ(pr) == t_VEC) {
    if (lg(pr) == 1) { avma = av; return gen_1; } /* flag = 1 is implicit */
    if (typ(gel(pr,1)) == t_VEC) {
      GEN Q = pr;
      pari_sp av2 = avma;
      long i, l = lg(Q);
      for (i=1; i < l; i++)
      {
        v = nfval(nf, dP, gel(Q,i));
        if (rnfdedekind_i(nf,P,gel(Q,i),v,1)) { avma=av; return gen_0; }
        avma = av2;
      }
      avma = av; return gen_1;
    }
  }

  v = nfval(nf, dP, pr);
  z = rnfdedekind_i(nf, P, pr, v, flag);
  if (z)
  {
    if (flag) { avma = av; return gen_0; }
    z = gerepilecopy(av, z);
  }
  else {
    long d;
    avma = av; if (flag) return gen_1;
    d = degpol(P);
    z = cgetg(4, t_VEC);
    gel(z,1) = gen_1;
    gel(z,2) = triv_order(d);
    gel(z,3) = stoi(v);
  }
  return z;
}

static int
ideal_is1(GEN x) {
  switch(typ(x))
  {
    case t_INT: return is_pm1(x);
    case t_MAT: return RgM_isidentity(x);
  }
  return 0;
}

/* nf a true nf. Return NULL if power order if pr-maximal */
static GEN
rnfordmax(GEN nf, GEN pol, GEN pr, long vdisc)
{
  pari_sp av = avma, av1, lim;
  long i, j, k, n, vpol, cmpt, sep;
  GEN q, q1, p, T, modpr, W, I, MW, C, p1;
  GEN Tauinv, Tau, prhinv, pip, nfT, rnfId;

  if (DEBUGLEVEL>1) err_printf(" treating %Ps^%ld\n", pr, vdisc);
  modpr = nf_to_Fq_init(nf,&pr,&T,&p);
  av1 = avma;
  p1 = rnfdedekind_i(nf, pol, modpr, vdisc, 0);
  if (!p1) { avma = av; return NULL; }
  if (is_pm1(gel(p1,1))) return gerepilecopy(av,gel(p1,2));
  sep = itos(gel(p1,3));
  W = gmael(p1,2,1);
  I = gmael(p1,2,2);
  gerepileall(av1, 2, &W, &I);

  pip = coltoalg(nf, pr_get_gen(pr));
  nfT = nf_get_pol(nf);
  n = degpol(pol); vpol = varn(pol);
  q = T? powiu(p,degpol(T)): p;
  q1 = q; while (cmpiu(q1,n) < 0) q1 = mulii(q1,q);
  rnfId = matid(n);

  prhinv = idealinv(nf, pr);
  C = cgetg(n+1, t_MAT);
  for (j=1; j<=n; j++) gel(C,j) = cgetg(n*n+1, t_COL);
  MW = cgetg(n*n+1, t_MAT);
  for (j=1; j<=n*n; j++) gel(MW,j) = cgetg(n+1, t_COL);
  Tauinv = cgetg(n+1, t_VEC);
  Tau    = cgetg(n+1, t_VEC);
  av1 = avma; lim = stack_lim(av1,1);
  for(cmpt=1; ; cmpt++)
  {
    GEN I0 = leafcopy(I), W0 = leafcopy(W);
    GEN Wa, Wainv, Waa, Ip, A, Ainv, MWmod, F, pseudo, G;

    if (DEBUGLEVEL>1) err_printf("    pass no %ld\n",cmpt);
    for (j=1; j<=n; j++)
    {
      GEN tau, tauinv;
      long v1, v2;
      if (ideal_is1(gel(I,j))) { gel(Tau,j) = gel(Tauinv,j) = gen_1; continue; }

      p1 = idealtwoelt(nf,gel(I,j));
      v1 = nfval(nf,gel(p1,1),pr);
      v2 = nfval(nf,gel(p1,2),pr);
      tau = (v1 > v2)? gel(p1,2): gel(p1,1);
      tauinv = nfinv(nf, tau);
      gel(Tau,j) = tau;
      gel(Tauinv,j) = tauinv;
      gel(W,j) = nfC_nf_mul(nf, gel(W,j), tau);
      gel(I,j) = idealmul(nf,    tauinv, gel(I,j));
    }
    /* W = (Z_K/pr)-basis of O/pr. O = (W0,I0) ~ (W, I) */
    Wa = matbasistoalg(nf,W);

   /* compute MW: W_i*W_j = sum MW_k,(i,j) W_k */
    Waa = lift_intern(RgM_to_RgXV(Wa,vpol));
    Wainv = lift_intern(ginv(Wa));
    for (i=1; i<=n; i++)
      for (j=i; j<=n; j++)
      {
        GEN z = RgXQX_rem(gmul(gel(Waa,i),gel(Waa,j)), pol, nfT);
        long tz = typ(z);
        if (is_scalar_t(tz) || (tz == t_POL && varncmp(varn(z), vpol) > 0))
          z = gmul(z, gel(Wainv,1));
        else
          z = mulmat_pol(Wainv, z);
        for (k=1; k<=n; k++)
        {
          GEN c = grem(gel(z,k), nfT);
          gcoeff(MW, k, (i-1)*n+j) = c;
          gcoeff(MW, k, (j-1)*n+i) = c;
        }
      }

    /* compute Ip =  pr-radical [ could use Ker(trace) if q large ] */
    MWmod = nfM_to_FqM(MW,nf,modpr);
    F = cgetg(n+1, t_MAT); F[1] = rnfId[1];
    for (j=2; j<=n; j++) gel(F,j) = rnfelementid_powmod(MWmod, j, q1, T,p);
    Ip = FqM_ker(F,T,p);
    if (lg(Ip) == 1) { W = W0; I = I0; break; }

    /* Fill C: W_k A_j = sum_i C_(i,j),k A_i */
    A = FqM_to_nfM(FqM_suppl(Ip,T,p), modpr);
    for (j=1; j<lg(Ip); j++)
    {
      p1 = gel(A,j);
      for (i=1; i<=n; i++) gel(p1,i) = mkpolmod(gel(p1,i), nfT);
    }
    for (   ; j<=n; j++)
    {
      p1 = gel(A,j);
      for (i=1; i<=n; i++) gel(p1,i) = gmul(pip, gel(p1,i));
    }
    Ainv = lift_intern(RgM_inv(A));
    A    = lift_intern(A);
    for (k=1; k<=n; k++)
      for (j=1; j<=n; j++)
      {
        GEN z = RgM_RgC_mul(Ainv, gmod(tablemul_ei(MW, gel(A,j),k), nfT));
        for (i=1; i<=n; i++)
        {
          GEN c = grem(gel(z,i), nfT);
          gcoeff(C, (j-1)*n+i, k) = nf_to_Fq(nf,c,modpr);
        }
      }
    G = FqM_to_nfM(FqM_ker(C,T,p), modpr);

    pseudo = rnfjoinmodules_i(nf, G,prhinv, rnfId,I);
    /* express W in terms of the power basis */
    W = RgM_mul(Wa, matbasistoalg(nf,gel(pseudo,1)));
    W = RgM_to_nfM(nf, W);
    I = gel(pseudo,2);
    /* restore the HNF property W[i,i] = 1. NB: Wa upper triangular, with
     * Wa[i,i] = Tau[i] */
    for (j=1; j<=n; j++)
      if (gel(Tau,j) != gen_1)
      {
        gel(W,j) = nfC_nf_mul(nf, gel(W,j), gel(Tauinv,j));
        gel(I,j) = idealmul(nf, gel(Tau,j), gel(I,j));
      }
    if (DEBUGLEVEL>3) err_printf(" new order:\n%Ps\n%Ps\n", W, I);
    if (sep <= 3 || gequal(I,I0)) break;

    if (low_stack(lim, stack_lim(av1,1)) || (cmpt & 3) == 0)
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"rnfordmax");
      gerepileall(av1,2, &W,&I);
    }
  }
  return gerepilecopy(av, mkvec2(W, I));
}

static void
check_pol(GEN *px)
{
  GEN x = *px;
  long i, lx = lg(x);
  for (i=2; i<lx; i++)
  {
    long tx = typ(x[i]);
    if (!is_rational_t(tx)) pari_err(talker,"incorrect coeff in rnf function");
  }
  if (lx == 2) *px = gen_0;
  if (lx == 3) *px = gel(x,2);
}

/* check whether P is a polynomials with coeffs in the number field defined
 * by the absolute equation T(y) = 0 */
GEN
rnf_fix_pol(GEN T, GEN P, int lift)
{
  long i, vT = varn(T), lP = lg(P);
  GEN Q = cgetg(lP, t_POL);
  if (typ(P) != t_POL || varncmp(varn(P), vT) >= 0)
    pari_err(talker,"incorrect polynomial in rnf function");
  Q[1] = P[1];
  for (i=2; i<lP; i++)
  {
    GEN c = gel(P,i);
    switch(typ(c))
    {
      case t_INT: case t_FRAC: break;
      case t_POL:
        if (varn(c) != vT)
          pari_err(talker,"incorrect variable in rnf function");
        if (lg(c) >= lg(T)) c = RgX_rem(c,T);
        check_pol(&c);
        if (!lift && typ(c) == t_POL) c = mkpolmod(c, T);
        break;
      case t_POLMOD:
        if (!RgX_equal_var(gel(c,1), T)) pari_err(consister,"rnf function");
        if (lift) c = gel(c,2);
        break;
      default: pari_err(typeer, "rnf function");
    }
    gel(Q,i) = c;
  }
  return normalizepol_lg(Q, lP);
}

/* determinant of the trace pairing */
static GEN
get_d(GEN nf, GEN pol, GEN A)
{
  long i, j, n = degpol(pol);
  GEN W = RgM_to_RgXV(lift_intern(matbasistoalg(nf,A)), varn(pol));
  GEN T, nfT = nf_get_pol(nf), sym = polsym_gen(pol, NULL, n-1, nfT, NULL);
  T = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++) gel(T,j) = cgetg(n+1,t_COL);
  for (j=1; j<=n; j++)
    for (i=j; i<=n; i++)
    {
      GEN c = RgXQX_mul(gel(W,i),gel(W,j), nfT);
      c = RgXQX_rem(c, pol, nfT);
      c = simplify_shallow(quicktrace(c,sym));
      gcoeff(T,j,i) = gcoeff(T,i,j) = c;
    }
  return nf_to_scalar_or_basis(nf, det(T));
}

/* nf = base field K
 * pol= monic polynomial, coefficients in Z_K, defining a relative
 *   extension L = K[X]/(pol). One MUST have varn(pol) << nf_get_varn(nf).
 * Returns a pseudo-basis [A,I] of Z_L, set (D,d) to the relative
 * discriminant, and f to the index-ideal */
GEN
rnfallbase(GEN nf, GEN *ppol, GEN *pD, GEN *pd, GEN *pf)
{
  long i, n, l;
  GEN A, nfT, fa, E, P, I, z, d, D, disc, pol = *ppol;

  nf = checknf(nf); nfT = nf_get_pol(nf);
  pol = rnf_fix_pol(nfT,pol,0);
  if (!gequal1(leading_term(pol)))
    pari_err(impl,"non-monic relative polynomials");

  n = degpol(pol);
  disc = RgX_disc(pol); pol = lift_intern(pol);
  fa = idealfactor(nf, disc);
  P = gel(fa,1); l = lg(P);
  E = gel(fa,2);
  z = NULL;
  for (i=1; i < l; i++)
  {
    long e = itos(gel(E,i));
    if (e > 1) z = rnfjoinmodules(nf, z, rnfordmax(nf, pol, gel(P,i), e));
  }
  if (!z) z = triv_order(n);
  A = gel(z,1); d = get_d(nf, pol, A);
  I = gel(z,2);

  i=1; while (i<=n && ideal_is1(gel(I,i))) { gel(I,i) = gen_1; i++; }
  if (i > n) { D = gen_1; if (pf) *pf = gen_1; }
  else
  {
    D = gel(I,i);
    for (i++; i<=n; i++) D = idealmul(nf,D,gel(I,i));
    if (pf) *pf = idealinv(nf, D);
    D = idealpow(nf,D,gen_2);
  }
  if (pd)
  {
    GEN f = core2partial(Q_content(d), 0);
    *pd = gdiv(d, sqri(gel(f,2)));
  }
  *pD = idealmul(nf,D,d);
  *ppol = pol; return z;
}

GEN
rnfpseudobasis(GEN nf, GEN pol)
{
  pari_sp av = avma;
  GEN D, d, z = rnfallbase(nf,&pol, &D, &d, NULL);
  return gerepilecopy(av, mkvec4(gel(z,1), gel(z,2), D, d));
}

GEN
rnfdiscf(GEN nf, GEN pol)
{
  pari_sp av = avma;
  GEN D, d; (void)rnfallbase(nf,&pol, &D, &d, NULL);
  return gerepilecopy(av, mkvec2(D,d));
}

GEN
gen_if_principal(GEN bnf, GEN x)
{
  pari_sp av = avma;
  GEN z = bnfisprincipal0(bnf,x, nf_GEN_IF_PRINCIPAL | nf_FORCE);
  if (z == gen_0) { avma = av; return NULL; }
  return z;
}

/* given bnf and a pseudo-basis of an order in HNF [A,I], tries to simplify
 * the HNF as much as possible. The resulting matrix will be upper triangular
 * but the diagonal coefficients will not be equal to 1. The ideals are
 * guaranteed to be integral and primitive. */
GEN
rnfsimplifybasis(GEN bnf, GEN x)
{
  pari_sp av = avma;
  long i, l;
  GEN y, Az, Iz, nf, A, I;

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  if (typ(x) != t_VEC || lg(x) < 3)
    pari_err(talker,"not a pseudo-basis in nfsimplifybasis");
  A = gel(x,1);
  I = gel(x,2); l = lg(I);
  y = cgetg(3, t_VEC);
  Az = cgetg(l, t_MAT); gel(y,1) = Az;
  Iz = cgetg(l, t_VEC); gel(y,2) = Iz;
  for (i = 1; i < l; i++)
  {
    GEN c, d;
    if (ideal_is1(gel(I,i))) {
      gel(Iz,i) = gen_1;
      gel(Az,i) = gel(A,i);
      continue;
    }

    gel(Iz,i) = Q_primitive_part(gel(I,i), &c);
    gel(Az,i) = c? RgC_Rg_mul(gel(A,i),c): gel(A,i);
    if (c && ideal_is1(gel(Iz,i))) continue;

    d = gen_if_principal(bnf, gel(Iz,i));
    if (d)
    {
      gel(Iz,i) = gen_1;
      gel(Az,i) = nfC_nf_mul(nf, gel(Az,i), d);
    }
  }
  return gerepilecopy(av, y);
}

static GEN
get_order(GEN nf, GEN O, const char *s)
{
  if (typ(O) == t_POL)
    return rnfpseudobasis(nf, O);
  if (typ(O)!=t_VEC || lg(O) < 3 || typ(O[1]) != t_MAT || typ(O[2]) != t_VEC
      || lg(O[1]) != lg(O[2]))
    pari_err(talker,"not a pseudo-matrix in %s", s);
  return O;
}

GEN
rnfdet(GEN nf, GEN order)
{
  pari_sp av = avma;
  GEN A, I, D;
  nf = checknf(nf);
  order = get_order(nf, order, "rnfdet");
  A = gel(order,1);
  I = gel(order,2);
  D = idealmul(nf, det(matbasistoalg(nf, A)), prodid(nf, I));
  return gerepileupto(av, D);
}

/* Given two fractional ideals a and b, gives x in a, y in b, z in b^-1,
   t in a^-1 such that xt-yz=1. In the present version, z is in Z. */
static void
nfidealdet1(GEN nf, GEN a, GEN b, GEN *px, GEN *py, GEN *pz, GEN *pt)
{
  GEN x, uv, y, da, db;

  a = idealinv(nf,a);
  a = Q_remove_denom(a, &da);
  b = Q_remove_denom(b, &db);
  x = idealcoprime(nf,a,b);
  uv = idealaddtoone(nf, idealmul(nf,x,a), b);
  y = gel(uv,2);
  if (da) x = RgC_Rg_mul(x,da);
  if (db) y = RgC_Rg_div(y,db);
  *px = x;
  *py = y;
  *pz = db ? negi(db): gen_m1;
  *pt = nfdiv(nf, gel(uv,1), x);
}

/* given a pseudo-basis of an order in HNF [A,I] (or [A,I,D,d]), gives an
 * n x n matrix (not in HNF) of a pseudo-basis and an ideal vector
 * [1,1,...,1,I] such that order = Z_K^(n-1) x I.
 * Uses the approximation theorem ==> slow. */
GEN
rnfsteinitz(GEN nf, GEN order)
{
  pari_sp av = avma;
  long i, n, l;
  GEN A, I, p1;

  nf = checknf(nf);
  order = get_order(nf, order, "rnfsteinitz");
  A = RgM_to_nfM(nf, gel(order,1));
  I = leafcopy(gel(order,2)); n=lg(A)-1;
  for (i=1; i<n; i++)
  {
    GEN c1, c2, b, a = gel(I,i);
    gel(I,i) = gen_1;
    if (ideal_is1(a)) continue;

    c1 = gel(A,i);
    c2 = gel(A,i+1);
    b = gel(I,i+1);
    if (ideal_is1(b))
    {
      gel(A,i) = c2;
      gel(A,i+1) = gneg(c1);
      gel(I,i+1) = a;
    }
    else
    {
      pari_sp av2 = avma;
      GEN x, y, z, t;
      nfidealdet1(nf,a,b, &x,&y,&z,&t);
      x = RgC_add(nfC_nf_mul(nf, c1, x), nfC_nf_mul(nf, c2, y));
      y = RgC_add(nfC_nf_mul(nf, c1, z), nfC_nf_mul(nf, c2, t));
      gerepileall(av2, 2, &x,&y);
      gel(A,i) = x;
      gel(A,i+1) = y;
      gel(I,i+1) = Q_primitive_part(idealmul(nf,a,b), &p1);
      if (p1) gel(A,i+1) = nfC_nf_mul(nf, gel(A,i+1), p1);
    }
  }
  l = lg(order);
  p1 = cgetg(l,t_VEC);
  gel(p1,1) = A;
  gel(p1,2) = I; for (i=3; i<l; i++) gel(p1,i) = gel(order,i);
  return gerepilecopy(av, p1);
}

/* Given bnf and either an order as output by rnfpseudobasis or a polynomial,
 * and outputs a basis if it is free, an n+1-generating set if it is not */
GEN
rnfbasis(GEN bnf, GEN order)
{
  pari_sp av = avma;
  long j, n;
  GEN nf, A, I, cl, col, a;

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  order = get_order(nf, order, "rnfbasis");
  I = gel(order,2); n = lg(I)-1;
  j=1; while (j<n && ideal_is1(gel(I,j))) j++;
  if (j<n)
  {
    order = rnfsteinitz(nf,order);
    I = gel(order,2);
  }
  A = gel(order,1);
  col= gel(A,n); A = vecslice(A, 1, n-1);
  cl = gel(I,n);
  a = gen_if_principal(bnf, cl);
  if (!a)
  {
    GEN v = idealtwoelt(nf, cl);
    A = shallowconcat(A, gmul(gel(v,1), col));
    a = gel(v,2);
  }
  A = shallowconcat(A, nfC_nf_mul(nf, col, a));
  return gerepilecopy(av, A);
}

/* Given bnf and either an order as output by rnfpseudobasis or a polynomial,
 * and outputs a basis (not pseudo) in Hermite Normal Form if it exists, zero
 * if not
 */
GEN
rnfhnfbasis(GEN bnf, GEN order)
{
  pari_sp av = avma;
  long j, n;
  GEN nf, A, I, a;

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  order = get_order(nf, order, "rnfbasis");
  A = gel(order,1); A = RgM_shallowcopy(A);
  I = gel(order,2); n = lg(A)-1;
  for (j=1; j<=n; j++)
  {
    if (ideal_is1(gel(I,j))) continue;
    a = gen_if_principal(bnf, gel(I,j));
    if (!a) { avma = av; return gen_0; }
    gel(A,j) = nfC_nf_mul(nf, gel(A,j), a);
  }
  return gerepilecopy(av,A);
}

static long
rnfisfree_aux(GEN bnf, GEN order)
{
  long n, j;
  GEN nf, P, I;

  bnf = checkbnf(bnf);
  if (is_pm1( bnf_get_no(bnf) )) return 1;
  nf = bnf_get_nf(bnf);
  order = get_order(nf, order, "rnfisfree");
  I = gel(order,2); n = lg(I)-1;
  j=1; while (j<=n && ideal_is1(gel(I,j))) j++;
  if (j>n) return 1;

  P = gel(I,j);
  for (j++; j<=n; j++)
    if (!ideal_is1(gel(I,j))) P = idealmul(nf,P,gel(I,j));
  return gequal0( isprincipal(bnf,P) );
}

long
rnfisfree(GEN bnf, GEN order)
{
  pari_sp av = avma;
  long n = rnfisfree_aux(bnf, order);
  avma = av; return n;
}

/**********************************************************************/
/**                                                                  **/
/**                   COMPOSITUM OF TWO NUMBER FIELDS                **/
/**                                                                  **/
/**********************************************************************/
/* modular version */
GEN
polcompositum0(GEN A, GEN B, long flall)
{
  pari_sp av = avma;
  int same;
  long v, k;
  GEN C, D, LPRS;

  if (typ(A)!=t_POL || typ(B)!=t_POL) pari_err(typeer,"polcompositum0");
  if (degpol(A)<=0 || degpol(B)<=0) pari_err(constpoler,"compositum");
  v = varn(A);
  if (varn(B) != v) pari_err(talker,"not the same variable in compositum");
  same = (A == B || RgX_equal(A,B));
  A = Q_primpart(A); RgX_check_ZX(A,"compositum");
  if (!ZX_is_squarefree(A)) pari_err(talker,"compositum: %Ps inseparable", A);
  if (!same) {
    B = Q_primpart(B); RgX_check_ZX(B,"compositum");
    if (!ZX_is_squarefree(B)) pari_err(talker,"compositum: %Ps inseparable", B);
  }

  D = NULL; /* -Wall */
  k = same? -1: 1;
  C = ZX_ZXY_resultant_all(A, B, &k, flall? &LPRS: NULL);
  if (same)
  {
    D = RgX_rescale(A, stoi(1 - k));
    C = RgX_div(C, D);
    if (degpol(C) <= 0) C = mkvec(D); else C = shallowconcat(ZX_DDF(C), D);
  }
  else
    C = ZX_DDF(C); /* C = Res_Y (A(Y), B(X + kY)) guaranteed squarefree */
  gen_sort_inplace(C, (void*)&cmpii, &gen_cmp_RgX, NULL);
  if (flall)
  { /* a,b,c root of A,B,C = compositum, c = b - k a */
    long i, l = lg(C);
    GEN a, b, mH0 = RgX_neg(gel(LPRS,1)), H1 = gel(LPRS,2);
    for (i=1; i<l; i++)
    {
      GEN D = gel(C,i);
      a = RgXQ_mul(mH0, QXQ_inv(H1, D), D);
      b = gadd(pol_x(v), gmulsg(k,a));
      gel(C,i) = mkvec4(D, mkpolmod(a,D), mkpolmod(b,D), stoi(-k));
    }
  }
  settyp(C, t_VEC); return gerepilecopy(av, C);
}
GEN
compositum(GEN pol1,GEN pol2) { return polcompositum0(pol1,pol2,0); }
GEN
compositum2(GEN pol1,GEN pol2) { return polcompositum0(pol1,pol2,1); }

/* Assume A,B irreducible (in particular squarefree) and define linearly
 * disjoint extensions: no factorisation needed */
GEN
ZX_compositum_disjoint(GEN A, GEN B)
{
  long k = 1;
  return ZX_ZXY_resultant_all(A, B, &k, NULL);
}
