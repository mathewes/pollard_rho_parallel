/* $Id$

Copyright (C) 2000-2003  The PARI group.

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
/*************************************************************************/
/**                                                                     **/
/**                           GALOIS CONJUGATES                         **/
/**                                                                     **/
/*************************************************************************/

static int is2sparse(GEN x)
{
  long i, l = lg(x);
  if (odd(l-3)) return 0;
  for(i=3; i<l; i+=2)
    if (signe(gel(x,i)))
      return 0;
  return 1;
}

static GEN
galoisconj1(GEN nf)
{
  GEN x = get_nfpol(nf, &nf), y, z;
  long i, lz, v = varn(x), nbmax;
  pari_sp av = avma;
  RgX_check_ZX(x, "nfgaloisconj");
  nbmax = numberofconjugates(x, 2);
  if (nbmax==1)
  {
    GEN res = cgetg(2,t_COL);
    gel(res,1) = pol_x(v);
    return res;
  }
  if (nbmax==2 && is2sparse(x))
  {
    GEN res = cgetg(3,t_COL);
    gel(res,1) = deg1pol_shallow(gen_m1, gen_0, v);
    gel(res,2) = pol_x(v);
    return res;
  }
  if (v == 0)
  {
    long w = fetch_user_var("y");
    if (nf) y = gsubst(nf, 0, pol_x(w));
    else { y = leafcopy(x); setvarn(y, w); }
  }
  else
  {
    y = x;
    x = leafcopy(x); setvarn(x, 0);
  }
  z = nfroots(y, x); lz = lg(z);
  y = cgetg(lz, t_COL);
  for (i = 1; i < lz; i++)
  {
    GEN t = lift(gel(z,i));
    if (typ(t) == t_POL) setvarn(t, v);
    gel(y,i) = t;
  }
  return gerepileupto(av, y);
}

/* nbmax: bound for the number of conjugates */
static GEN
galoisconj2pol(GEN x, long prec)
{
  long i, n, v, nbauto, nbmax;
  pari_sp av = avma;
  GEN y, w, polr, p1, p2;
  n = degpol(x);
  if (n <= 0) return cgetg(1, t_VEC);
  RgX_check_ZX(x, "galoisconj2pol");
  if (!ZX_is_irred(x)) pari_err(redpoler, "galoisconj2pol");

  nbmax = numberofconjugates(x, 2);
  polr = cleanroots(x, prec);
  p1 = gel(polr,1);
  /* accuracy in decimal digits */
  prec = (long)bit_accuracy_mul(prec, LOG10_2 * 0.75);
  nbauto = 1;
  w = cgetg(n + 2, t_VEC);
  gel(w,1) = gen_1;
  for (i = 2; i <= n; i++) gel(w,i) = gmul(p1, gel(w,i-1));
  v = varn(x);
  y = cgetg(nbmax + 1, t_COL);
  gel(y,1) = pol_x(v);
  for (i = 2; i <= n && nbauto < nbmax; i++)
  {
    gel(w,n+1) = gel(polr,i);
    p1 = lindep2(w, prec);
    if (signe(p1[n+1]))
    {
      p1[0] = evallg(n+1) | evaltyp(t_COL);
      p2 = gdiv(RgV_to_RgX(p1, v), negi(gel(p1,n+1)));
      if (gdvd(poleval(x, p2), x))
      {
        gel(y,++nbauto) = p2;
        if (DEBUGLEVEL > 1) err_printf("conjugate %ld: %Ps\n", i, y[nbauto]);
      }
    }
  }
  if (nbauto < nbmax)
    pari_warn(warner, "conjugates list may be incomplete in nfgaloisconj");
  setlg(y, 1 + nbauto);
  return gerepileupto(av, gen_sort(y, (void*)&gcmp, &gen_cmp_RgX));
}

static GEN
galoisconj2(GEN nf, long prec)
{
  long i, n, nbauto, nbmax;
  pari_sp av = avma;
  GEN T = get_nfpol(nf,&nf), y, w, polr, p1, p2;

  if (!nf) return galoisconj2pol(T, prec);
  n = degpol(T);
  if (n <= 0) return cgetg(1, t_VEC);
  nbmax = numberofconjugates(T, 2);
  y = cgetg(nbmax + 1, t_COL);
  gel(y,1) = pol_x(varn(T));
  /* accuracy in decimal digits */
  prec = (long)bit_accuracy_mul(nf_get_prec(nf), LOG10_2 * 0.75);
  nbauto = 1;
  polr = nf_get_allroots(nf);
  p2 = nf_get_M(nf);
  w = cgetg(n + 2, t_VEC);
  for (i = 1; i <= n; i++) gel(w,i) = gcoeff(p2, 1, i);
  for (i = 2; i <= n && nbauto < nbmax; i++)
  {
    gel(w,n+1) = gel(polr,i);
    p1 = lindep2(w, prec);
    if (signe(p1[n+1]))
    {
      p1[0] = evallg(n+1) | evaltyp(t_COL);
      p2 = gdiv(coltoliftalg(nf, p1), negi(gel(p1, n+1)));
      if (gdvd(poleval(T, p2), T))
      {
        gel(y,++nbauto) = p2;
        if (DEBUGLEVEL > 1) err_printf("conjugate %ld: %Ps\n", i, y[nbauto]);
      }
    }
  }
  if (nbauto < nbmax)
    pari_warn(warner, "conjugates list may be incomplete in nfgaloisconj");
  setlg(y, 1 + nbauto);
  return gerepileupto(av, gen_sort(y, (void*)&gcmp, &gen_cmp_RgX));
}
/*************************************************************************/
/**                                                                     **/
/**                           GALOISCONJ4                               **/
/**                                                                     **/
/*************************************************************************/
/*DEBUGLEVEL:
  1: timing
  2: outline
  4: complete outline
  6: detail
  7: memory
  9: complete detail
*/
struct galois_borne {
  GEN  l;
  long valsol;
  long valabs;
  GEN  bornesol;
  GEN  ladicsol;
  GEN  ladicabs;
};
struct galois_lift {
  GEN  T;
  GEN  den;
  GEN  p;
  GEN  L;
  GEN  Lden;
  long e;
  GEN  Q;
  GEN  TQ;
  struct galois_borne *gb;
};
struct galois_testlift {
  long n;
  long f;
  long g;
  GEN  bezoutcoeff;
  GEN  pauto;
  GEN  C;
  GEN  Cd;
};
struct galois_test { /* data for permutation test */
  GEN order; /* order of tests pour galois_test_perm */
  GEN borne, lborne; /* coefficient bounds */
  GEN ladic;
  GEN PV; /* NULL or vector of test matrices (Vmatrix) */
  GEN TM; /* transpose of M */
  GEN L; /* p-adic roots, known mod ladic */
  GEN M; /* vandermonde inverse */
};
/* result of the study of Frobenius degrees */
enum ga_code {ga_all_normal=1,ga_ext_2=2,ga_non_wss=4};
struct galois_analysis {
  long p; /* prime to be lifted */
  long deg; /* degree of the lift */
  long ord;
  long l; /* l: prime number such that T is totally split mod l */
  long p4;
  enum ga_code group;
  byteptr primepointer; /* allow computing the primes following p */
};
struct galois_frobenius {
  long p;
  long fp;
  long deg;
  GEN Tmod;
  GEN psi;
};

GEN
vandermondeinverseprep(GEN L)
{
  long i, j, n = lg(L);
  GEN V;
  V = cgetg(n, t_VEC);
  for (i = 1; i < n; i++)
  {
    pari_sp ltop = avma;
    GEN W = cgetg(n-1,t_VEC);
    long k = 1;
    for (j = 1; j < n; j++)
      if (i != j) gel(W, k++) = gsub(gel(L,i),gel(L,j));
    gel(V,i) = gerepileupto(ltop,divide_conquer_prod(W,&gmul));
  }
  return V;
}

/* Compute the inverse of the van der Monde matrix of T multiplied by den */
GEN
vandermondeinverse(GEN L, GEN T, GEN den, GEN prep)
{
  pari_sp ltop = avma;
  long i, n = lg(L)-1;
  GEN M, P;
  if (!prep) prep = vandermondeinverseprep(L);
  M = cgetg(n+1, t_MAT);
  for (i = 1; i <= n; i++)
  {
    P = gdiv(RgX_div_by_X_x(T, gel(L,i), NULL), gel(prep,i));
    gel(M,i) = RgX_to_RgV(P,n);
  }
  return gerepileupto(ltop, gmul(den, M));
}

/* Compute bound for the coefficients of automorphisms.
 * T a ZX, dn a t_INT denominator or NULL */
GEN
initgaloisborne(GEN T, GEN dn, long prec, GEN *ptL, GEN *ptprep, GEN *ptdis)
{
  GEN L, prep, den, nf, r;
  pari_timer ti;

  if (DEBUGLEVEL>=4) timer_start(&ti);
  T = get_nfpol(T, &nf);
  r = nf ? nf_get_roots(nf) : NULL;
  if (nf &&  precision(gel(r, 1)) >= prec)
  {
    long r1,r2;
    nf_get_sign(nf, &r1, &r2);
    if (!r2) L = r;
    else
    {
      long i,j, N = r1+2*r2;
      L = cgetg(N + 1, t_VEC);
      for (i = 1; i <= r1; i++) gel(L,i) = gel(r,i);
      for (j = i; j <= N; i++)
      {
        gel(L,j++) = gel(r,i);
        gel(L,j++) = gconj(gel(r,i));
      }
    }
  }
  else
    L = cleanroots(T, prec);
  if (DEBUGLEVEL>=4) timer_printf(&ti,"roots");
  prep = vandermondeinverseprep(L);
  if (!dn)
  {
    GEN dis, res = divide_conquer_prod(gabs(prep,prec), mpmul);
    dbg_block();
    dis = ZX_disc_all(T, 1+logint(res,gen_2,NULL));
    dbg_release();
    den = indexpartial(T,dis);
    if (ptdis) *ptdis = dis;
  }
  else
  {
    if (typ(dn) != t_INT || signe(dn) <= 0)
      pari_err(talker, "incorrect denominator in initgaloisborne: %Ps", dn);
    den = dn;
  }
  if (ptprep) *ptprep = prep;
  *ptL = L; return den;
}

/* ||| M ||| with respect to || x ||_oo. Assume M square t_MAT */
GEN
matrixnorm(GEN M, long prec)
{
  long i,j, n = lg(M);
  GEN B = real_0(prec);

  for (i = 1; i < n; i++)
  {
    GEN z = gabs(gcoeff(M,i,1), prec);
    for (j = 2; j < n; j++) z = gadd(z, gabs(gcoeff(M,i,j), prec));
    if (gcmp(z, B) > 0) B = z;
  }
  return B;
}

static GEN
galoisborne(GEN T, GEN dn, struct galois_borne *gb, long d)
{
  pari_sp ltop = avma, av2;
  GEN borne, borneroots, borneabs;
  long prec;
  GEN L, M, prep, den;
  pari_timer ti;

  prec = ZX_max_lg(T);
  den = initgaloisborne(T,dn,prec, &L,&prep,NULL);
  if (!dn) den = gclone(den);
  if (DEBUGLEVEL>=4) timer_start(&ti);
  M = vandermondeinverse(L, RgX_gtofp(T, prec), den, prep);
  if (DEBUGLEVEL>=4) timer_printf(&ti,"vandermondeinverse");
  borne = matrixnorm(M, prec);
  borneroots = gsupnorm(L, prec); /*t_REAL*/
  borneabs = addsr(1, gmul(borne,gmulsg(d, powru(borneroots, d))));
  borneroots = addsr(1, gmul(borne, borneroots));
  av2 = avma;
  /*We use d-1 test, so we must overlift to 2^BITS_IN_LONG*/
  gb->valsol = logint(gmul2n(borneroots,2+BITS_IN_LONG), gb->l,NULL);
  gb->valabs = logint(gmul2n(borneabs,2), gb->l,NULL);
  gb->valabs = maxss(gb->valsol, gb->valabs);
  if (DEBUGLEVEL >= 4)
    err_printf("GaloisConj:val1=%ld val2=%ld\n", gb->valsol, gb->valabs);
  avma = av2;
  gb->bornesol = gerepileuptoint(ltop, ceil_safe(shiftr(borneroots,1)));
  if (DEBUGLEVEL >= 9)
    err_printf("GaloisConj: Bound %Ps\n",borneroots);
  gb->ladicsol = powiu(gb->l, gb->valsol);
  gb->ladicabs = powiu(gb->l, gb->valabs);
  if (!dn) { dn = icopy(den); gunclone(den); }
  return dn;
}

static GEN
makeLden(GEN L,GEN den, struct galois_borne *gb)
{ return FpC_Fp_mul(L, den, gb->ladicsol); }

/* Initialize the galois_lift structure */
static void
initlift(GEN T, GEN den, GEN p, GEN L, GEN Lden, struct galois_borne *gb, struct galois_lift *gl)
{
  pari_sp av = avma;
  long e;
  gl->gb = gb;
  gl->T = T;
  gl->den = is_pm1(den)? gen_1: den;
  gl->p = p;
  gl->L = L;
  gl->Lden = Lden;
  e = logint(gmul2n(gb->bornesol, 2+BITS_IN_LONG),p,NULL);
  avma = av;
  if (e < 2) e = 2;
  gl->e = e;
  gl->Q = powiu(p, e);
  gl->TQ = FpX_red(T,gl->Q);
}

/* Check whether f is (with high probability) a solution and compute its
 * permutation */
static int
poltopermtest(GEN f, struct galois_lift *gl, GEN pf)
{
  pari_sp av;
  GEN fx, fp, B = gl->gb->bornesol;
  long i, j, ll;
  for (i = 2; i < lg(f); i++)
    if (absi_cmp(gel(f,i),B) > 0)
    {
      if (DEBUGLEVEL>=4) err_printf("GaloisConj: Solution too large.\n");
      if (DEBUGLEVEL>=8) err_printf("f=%Ps\n borne=%Ps\n",f,B);
      return 0;
    }
  ll = lg(gl->L);
  fp = const_vecsmall(ll-1, 1); /* left on stack */
  av = avma;
  for (i = 1; i < ll; i++, avma = av)
  {
    fx = FpX_eval(f, gel(gl->L,i), gl->gb->ladicsol);
    for (j = 1; j < ll; j++)
      if (fp[j] && equalii(fx, gel(gl->Lden,j))) { pf[i]=j; fp[j]=0; break; }
    if (j == ll) return 0;
  }
  return 1;
}

static long
monoratlift(GEN S, GEN q, GEN qm1old,struct galois_lift *gl, GEN frob)
{
  GEN tlift = FpX_ratlift(S,q,qm1old,qm1old,gl->den);
  if (tlift)
  {
    pari_sp ltop = avma;
    if(DEBUGLEVEL>=4)
      err_printf("MonomorphismLift: trying early solution %Ps\n",tlift);
    if (gl->den != gen_1) {
      GEN N = gl->gb->ladicsol, N2 = shifti(N,-1);
      tlift = FpX_center(FpX_red(Q_muli_to_int(tlift, gl->den), N), N,N2);
    }
    if (poltopermtest(tlift, gl, frob))
    {
      if(DEBUGLEVEL>=4) err_printf("MonomorphismLift: true early solution.\n");
      avma = ltop; return 1;
    }
    avma = ltop;
    if(DEBUGLEVEL>=4) err_printf("MonomorphismLift: false early solution.\n");
  }
  return 0;
}

static GEN
monomorphismratlift(GEN P, GEN S, struct galois_lift *gl, GEN frob)
{
  pari_sp ltop, lbot;
  GEN Q = gl->T, p = gl->p, qold = NULL, q = p;
  GEN Sr, Spow, Wr = NULL, W, Prold = NULL, Pr, Qrold = NULL, Qr;
  long e = gl->e, level = 1, rt;
  ulong mask;
  GEN *gptr[2];
  pari_timer ti;

  if (DEBUGLEVEL == 1) timer_start(&ti);
  rt = brent_kung_optpow(degpol(Q),1);
  mask = quadratic_prec_mask(e);
  Pr = FpX_red(P,q);
  Qr = (P==Q)? Pr: FpX_red(Q, q);/*A little speed up for automorphismlift*/
  W = FpXQ_inv(FpX_FpXQ_eval(ZX_deriv(Pr),S, Qr,q), Qr,q);
  gptr[0] = &S;
  gptr[1] = &Wr;
  for (;;)
  {
    if (DEBUGLEVEL>=2) { level = (level<<1) - (mask & 1); timer_start(&ti); }
    q = sqri(q);
    if (mask & 1) q = diviiexact(q, p);
    mask >>= 1;
    Pr = FpX_red(P, q);
    Qr = (P==Q)? Pr: FpX_red(Q, q);/*A little speed up for automorphismlift*/
    ltop = avma;
    Sr = S;
    Spow = FpXQ_powers(Sr, rt, Qr, q);
    if (Wr)
    {
      W = FpXQ_mul(Wr, FpX_FpXQV_eval(ZX_deriv(Prold),FpXV_red(Spow,qold),Qrold,qold),
                   Qrold,qold);
      W = FpXQ_mul(Wr, Fp_FpX_sub(gen_2, W, qold), Qrold,qold);
    }
    Wr = W;
    S = FpXQ_mul(Wr, FpX_FpXQV_eval(Pr, Spow, Qr, q),Qr,q);
    lbot = avma;
    S = FpX_sub(Sr, S, q);
    if (DEBUGLEVEL >= 4) timer_printf(&ti, "MonomorphismLift: lift to prec %d",level);
    if (mask == 1) break;
    Wr = ZX_copy(Wr);
    gerepilemanysp(ltop, lbot, gptr, 2);
    if (qold && frob && monoratlift(S,q,diviiexact(qold,p),gl,frob)) return NULL;
    qold = q; Prold = Pr; Qrold = Qr;
  }
  if (DEBUGLEVEL == 1) timer_printf(&ti, "monomorphismlift()");
  return S;
}

/* Let T be a polynomial in Z[X] , p a prime number, S in Fp[X]/(T) so
 * that T(S)=0 [p,T]. Lift S in S_0 so that T(S_0)=0 [T,p^e]
 * Unclean stack */
static GEN
automorphismlift(GEN S, struct galois_lift *gl, GEN frob)
{
  return monomorphismratlift(gl->T, S, gl, frob);
}

/* Let P be a polynomial in Z[X] , p a prime number, S in Fp[X]/(Q) so
 * that T(S)=0 [p,T]. Lift S in S_0 so that T(S_0)=0 [Q,p^e]
 * Unclean stack */

GEN
monomorphismlift(GEN P, GEN S, GEN Q, GEN p, long e)
{
  struct galois_lift gl;
  gl.T = Q;
  gl.p = p;
  gl.e = e;
  return monomorphismratlift(P,S,&gl,NULL);
}

static GEN
galoisdolift(struct galois_lift *gl, GEN frob)
{
  pari_sp av = avma;
  GEN Tp = FpX_red(gl->T, gl->p);
  GEN S = FpXQ_pow(pol_x(varn(Tp)), gl->p, Tp, gl->p);
  return gerepileupto(av, automorphismlift(S, gl, frob));
}

static void
inittestlift(GEN plift, GEN Tmod, struct galois_lift *gl,
             struct galois_testlift *gt)
{
  long v = varn(gl->T);
  gt->n = lg(gl->L) - 1;
  gt->g = lg(Tmod) - 1;
  gt->f = gt->n / gt->g;
  gt->bezoutcoeff = bezout_lift_fact(gl->T, Tmod, gl->p, gl->e);
  gt->pauto = cgetg(gt->f + 1, t_VEC);
  gel(gt->pauto,1) = pol_x(v);
  gel(gt->pauto,2) = gcopy(plift);
  if (gt->f > 2)
  {
    pari_sp av = avma, ltop;
    long i, nautpow = brent_kung_optpow(gt->n-1,gt->f-2);
    GEN autpow;
    pari_timer ti;
    if (DEBUGLEVEL >= 1) timer_start(&ti);
    autpow = FpXQ_powers(plift,nautpow,gl->TQ,gl->Q);
    ltop = avma;
    for (i = 3; i <= gt->f; i++)
      gel(gt->pauto,i) = FpX_FpXQV_eval(gel(gt->pauto,i-1),autpow,gl->TQ,gl->Q);
    /*Somewhat paranoid with memory, but this function use a lot of stack.*/
    gerepilecoeffssp(av, ltop, gt->pauto + 3, gt->f-2);
    if (DEBUGLEVEL >= 1) timer_printf(&ti, "Frobenius power");
  }
}

/* Explanation of the intheadlong technique:
 * Let C be a bound, B = BITS_IN_LONG, M > C*2^B a modulus and 0 <= a_i < M for
 * i=1,...,n where n < 2^B. We want to test if there exist k,l, |k| < C < M/2^B,
 * such that sum a_i = k + l*M
 * We write a_i*2^B/M = b_i+c_i with b_i integer and 0<=c_i<1, so that
 *   sum b_i - l*2^B = k*2^B/M - sum c_i
 * Since -1 < k*2^B/M < 1 and 0<=c_i<1, it follows that
 *   -n-1 < sum b_i - l*2^B < 1  i.e.  -n <= sum b_i -l*2^B <= 0
 * So we compute z = - sum b_i [mod 2^B] and check if 0 <= z <= n. */

/* Assume 0 <= x < mod. */
long
intheadlong(GEN x, GEN mod)
{
  pari_sp av = avma;
  long res = (long) itou(divii(shifti(x,BITS_IN_LONG),mod));
  avma = av; return res;
}
static GEN
vecheadlong(GEN W, GEN mod)
{
  long i, l = lg(W);
  GEN V = cgetg(l, t_VECSMALL);
  for(i=1; i<l; i++) V[i] = intheadlong(gel(W,i), mod);
  return V;
}
GEN
matheadlong(GEN W, GEN mod)
{
  long i, l = lg(W);
  GEN V = cgetg(l,t_MAT);
  for(i=1; i<l; i++) gel(V,i) = vecheadlong(gel(W,i), mod);
  return V;
}
long
polheadlong(GEN P, long n, GEN mod)
{
  return (lg(P)>n+2)? intheadlong(gel(P,n+2),mod): 0;
}

#define headlongisint(Z,N) (-(ulong)(Z)<=(ulong)(N))

static long
frobeniusliftall(GEN sg, long el, GEN *psi, struct galois_lift *gl,
                 struct galois_testlift *gt, GEN frob)
{
  pari_sp av, ltop2, ltop = avma;
  long i,j,k, c = lg(sg)-1, n = lg(gl->L)-1, m = gt->g, d = m / c;
  GEN pf, u, v, C, Cd, SG, cache;
  long N1, N2, R1, Ni, Z, ord = gt->f, c_idx = gt->g-1;
  long hop = 0;
  GEN NN, NQ;
  pari_timer ti;

  *psi = pf = cgetg(m, t_VECSMALL);
  ltop2 = avma;
  NN = diviiexact(mpfact(m), mului(c, powiu(mpfact(d), c)));
  if (DEBUGLEVEL >= 4)
    err_printf("GaloisConj:I will try %Ps permutations\n", NN);
  N1=10000000;
  NQ=divis_rem(NN,N1,&R1);
  if (cmpiu(NQ,1000000000)>0)
  {
    pari_warn(warner,"Combinatorics too hard : would need %Ps tests!\n"
        "I will skip it, but it may induce an infinite loop",NN);
    avma = ltop; *psi = NULL; return 0;
  }
  N2=itos(NQ); if(!N2) N1=R1;
  if (DEBUGLEVEL>=4) timer_start(&ti);
  avma = ltop2;
  C = gt->C;
  Cd= gt->Cd;
  v = FpXQ_mul(gel(gt->pauto, 1+el%ord), gel(gt->bezoutcoeff, m),gl->TQ,gl->Q);
  if (gl->den != gen_1) v = FpX_Fp_mul(v, gl->den, gl->Q);
  SG = cgetg(lg(sg),t_VECSMALL);
  for(i=1; i<lg(SG); i++) SG[i] = (el*sg[i])%ord + 1;
  cache = cgetg(m+1,t_VECSMALL); cache[m] = polheadlong(v,1,gl->Q);
  Z = polheadlong(v,2,gl->Q);
  for (i = 1; i < m; i++) pf[i] = 1 + i/d;
  av = avma;
  for (Ni = 0, i = 0; ;i++)
  {
    for (j = c_idx ; j > 0; j--)
    {
      long h = SG[pf[j]];
      if (!mael(C,h,j))
      {
        pari_sp av3 = avma;
        GEN r = FpXQ_mul(gel(gt->pauto,h), gel(gt->bezoutcoeff,j),gl->TQ,gl->Q);
        if (gl->den != gen_1) r = FpX_Fp_mul(r, gl->den, gl->Q);
        gmael(C,h,j) = gclone(r);
        mael(Cd,h,j) = polheadlong(r,1,gl->Q);
        avma = av3;
      }
      cache[j] = cache[j+1]+mael(Cd,h,j);
    }
    if (headlongisint(cache[1],n))
    {
      long ZZ = Z;
      for (j = 1; j < m; j++) ZZ += polheadlong(gmael(C,SG[pf[j]],j),2,gl->Q);
      if (headlongisint(ZZ,n))
      {
        u = v;
        for (j = 1; j < m; j++) u = ZX_add(u, gmael(C,SG[pf[j]],j));
        u = FpX_center(FpX_red(u, gl->Q), gl->Q, shifti(gl->Q,-1));
        if (poltopermtest(u, gl, frob))
        {
          if (DEBUGLEVEL >= 4)
          {
            timer_printf(&ti, "");
            err_printf("GaloisConj: %d hops on %Ps tests\n",hop,addis(mulss(Ni,N1),i));
          }
          avma = ltop2; return 1;
        }
        if (DEBUGLEVEL >= 4) err_printf("M");
      }
      else hop++;
    }
    if (DEBUGLEVEL >= 4 && i % maxss(N1/20, 1) == 0)
      timer_printf(&ti, "GaloisConj:Testing %Ps", addis(mulss(Ni,N1),i));
    avma = av;
    if (i == N1-1)
    {
      if (Ni==N2-1) N1 = R1;
      if (Ni==N2) break;
      Ni++; i = 0;
      if (DEBUGLEVEL>=4) timer_start(&ti);
    }
    for (j = 2; j < m && pf[j-1] >= pf[j]; j++)
      /*empty*/; /* to kill clang Warning */
    for (k = 1; k < j-k && pf[k] != pf[j-k]; k++) { lswap(pf[k], pf[j-k]); }
    for (k = j - 1; pf[k] >= pf[j]; k--)
      /*empty*/;
    lswap(pf[j], pf[k]); c_idx = j;
  }
  if (DEBUGLEVEL>=4) err_printf("GaloisConj: not found, %d hops \n",hop);
  *psi = NULL; avma = ltop; return 0;
}

/* Compute the test matrix for the i-th line of V. Clone. */
static GEN
Vmatrix(long i, struct galois_test *td)
{
  pari_sp av = avma;
  GEN m = gclone( matheadlong(FpC_FpV_mul(td->L, row(td->M,i), td->ladic), td->ladic));
  avma = av; return m;
}

/* Initialize galois_test */
static void
inittest(GEN L, GEN M, GEN borne, GEN ladic, struct galois_test *td)
{
  long i, n = lg(L)-1;
  GEN p = cgetg(n+1, t_VECSMALL);
  if (DEBUGLEVEL >= 8) err_printf("GaloisConj:Init Test\n");
  td->order = p;
  for (i = 1; i <= n-2; i++) p[i] = i+2;
  p[n-1] = 1; p[n] = 2;
  td->borne = borne;
  td->lborne = subii(ladic, borne);
  td->ladic = ladic;
  td->L = L;
  td->M = M;
  td->TM = shallowtrans(M);
  td->PV = const_vecsmall(n, 0);
  gel(td->PV, 2) = Vmatrix(2, td);
}

/* Free clones stored inside galois_test */
static void
freetest(struct galois_test *td)
{
  long i;
  for (i = 1; i < lg(td->PV); i++)
    if (td->PV[i]) { gunclone(gel(td->PV,i)); td->PV[i] = 0; }
}

/* Check if the integer P seen as a p-adic number is close to an integer less
 * than td->borne in absolute value */
static long
padicisint(GEN P, struct galois_test *td)
{
  pari_sp ltop = avma;
  GEN U  = modii(P, td->ladic);
  long r = cmpii(U, td->borne) <= 0 || cmpii(U, td->lborne) >= 0;
  avma = ltop; return r;
}

/* Check if the permutation pf is valid according to td.
 * If not, update td to make subsequent test faster (hopefully) */
static long
galois_test_perm(struct galois_test *td, GEN pf)
{
  pari_sp av = avma;
  long i, j, n = lg(td->L)-1;
  GEN V, P = NULL;
  for (i = 1; i < n; i++)
  {
    long ord = td->order[i];
    GEN PW = gel(td->PV, ord);
    if (PW)
    {
      long Z = mael(PW,1,pf[1]);
      for (j = 2; j <= n; j++) Z += mael(PW,j,pf[j]);
      if (!headlongisint(Z,n)) break;
    } else
    {
      if (!P) P = vecpermute(td->L, pf);
      V = FpV_dotproduct(gel(td->TM,ord), P, td->ladic);
      if (!padicisint(V, td)) {
        gel(td->PV, ord) = Vmatrix(ord, td);
        if (DEBUGLEVEL >= 4) err_printf("M");
        break;
      }
    }
  }
  if (i == n) { avma = av; return 1; }
  if (DEBUGLEVEL >= 4) err_printf("%d.", i);
  if (i > 1)
  {
    long z = td->order[i];
    for (j = i; j > 1; j--) td->order[j] = td->order[j-1];
    td->order[1] = z;
    if (DEBUGLEVEL >= 8) err_printf("%Ps", td->order);
  }
  avma = av; return 0;
}
/*Compute a*b/c when a*b will overflow*/
static long
muldiv(long a,long b,long c)
{
  return (long)((double)a*(double)b/c);
}

/* F = cycle decomposition of sigma,
 * B = cycle decomposition of cl(tau).
 * Check all permutations pf who can possibly correspond to tau, such that
 * tau*sigma*tau^-1 = sigma^s and tau^d = sigma^t, where d = ord cl(tau)
 * x: vector of choices,
 * G: vector allowing linear access to elts of F.
 * Choices multiple of e are not changed. */
static GEN
testpermutation(GEN F, GEN B, GEN x, long s, long e, long cut,
                struct galois_test *td)
{
  pari_sp av, avm = avma;
  long a, b, c, d, n, p1, p2, p3, p4, p5, p6, l1, l2, N1, N2, R1;
  long V, i, j, cx, hop = 0, start = 0;
  GEN pf, ar, G, W, NN, NQ;
  pari_timer ti;
  if (DEBUGLEVEL >= 1) timer_start(&ti);
  a = lg(F)-1; b = lg(F[1])-1;
  c = lg(B)-1; d = lg(B[1])-1;
  n = a*b;
  s = (b+s) % b;
  pf = cgetg(n+1, t_VECSMALL);
  av = avma;
  ar = cgetg(a+2, t_VECSMALL); ar[a+1]=0;
  G  = cgetg(a+1, t_VECSMALL);
  W  = gel(td->PV, td->order[n]);
  for (cx=1, i=1, j=1; cx <= a; cx++, i++)
  {
    gel(G,cx) = gel(F, coeff(B,i,j));
    if (i == d) { i = 0; j++; }
  }
  NN = divis(powuu(b, c * (d - d/e)), cut);
  if (DEBUGLEVEL>=4) err_printf("GaloisConj:I will try %Ps permutations\n", NN);
  N1 = 1000000;
  NQ = divis_rem(NN,N1,&R1);
  if (cmpiu(NQ,100000000)>0)
  {
    avma = avm;
    pari_warn(warner,"Combinatorics too hard : would need %Ps tests!\n I'll skip it but you will get a partial result...",NN);
    return identity_perm(n);
  }
  N2 = itos(NQ);
  for (l2 = 0; l2 <= N2; l2++)
  {
    long nbiter = (l2<N2) ? N1: R1;
    if (DEBUGLEVEL >= 2 && N2) err_printf("%d%% ", muldiv(l2,100,N2));
    for (l1 = 0; l1 < nbiter; l1++)
    {
      if (start)
      {
        for (i=1, j=e; i < a;)
        {
          if ((++(x[i])) != b) break;
          x[i++] = 0;
          if (i == j) { i++; j += e; }
        }
      }
      else { start=1; i = a-1; }
      /* intheadlong test: overflow in + is OK, we compute mod 2^BIL */
      for (p1 = i+1, p5 = p1%d - 1 ; p1 >= 1; p1--, p5--) /* p5 = (p1%d) - 1 */
      {
        if (p5 == - 1) { p5 = d - 1; p6 = p1 + 1 - d; } else p6 = p1 + 1;
        p4 = p5 ? x[p1-1] : 0;
        V = 0;
        for (p2 = 1+p4, p3 = 1 + x[p1]; p2 <= b; p2++)
        {
          V += mael(W,mael(G,p6,p3),mael(G,p1,p2));
          p3 += s; if (p3 > b) p3 -= b;
        }
        p3 = 1 + x[p1] - s; if (p3 <= 0) p3 += b;
        for (p2 = p4; p2 >= 1; p2--)
        {
          V += mael(W,mael(G,p6,p3),mael(G,p1,p2));
          p3 -= s; if (p3 <= 0) p3 += b;
        }
        ar[p1] = ar[p1+1] + V;
      }
      if (!headlongisint(ar[1],n)) continue;

      /* intheadlong succeeds. Full computation */
      for (p1=1, p5=d; p1 <= a; p1++, p5++)
      {
        if (p5 == d) { p5 = 0; p4 = 0; } else p4 = x[p1-1];
        if (p5 == d-1) p6 = p1+1-d; else p6 = p1+1;
        for (p2 = 1+p4, p3 = 1 + x[p1]; p2 <= b; p2++)
        {
          pf[mael(G,p1,p2)] = mael(G,p6,p3);
          p3 += s; if (p3 > b) p3 -= b;
        }
        p3 = 1 + x[p1] - s; if (p3 <= 0) p3 += b;
        for (p2 = p4; p2 >= 1; p2--)
        {
          pf[mael(G,p1,p2)] = mael(G,p6,p3);
          p3 -= s; if (p3 <= 0) p3 += b;
        }
      }
      if (galois_test_perm(td, pf))
      {
        if (DEBUGLEVEL >= 1)
        {
          GEN nb = addis(mulss(l2,N1),l1);
          timer_printf(&ti, "testpermutation(%Ps)", nb);
          if (DEBUGLEVEL >= 2 && hop)
            err_printf("GaloisConj:%d hop over %Ps iterations\n", hop, nb);
        }
        avma = av; return pf;
      }
      hop++;
    }
  }
  if (DEBUGLEVEL >= 1)
  {
    timer_printf(&ti, "testpermutation(%Ps)", NN);
    if (DEBUGLEVEL >= 2 && hop)
      err_printf("GaloisConj:%d hop over %Ps iterations\n", hop, NN);
  }
  avma = avm; return NULL;
}

/* List of subgroups of (Z/mZ)^* whose order divide o, and return the list
 * of their elements, sorted by increasing order */
GEN
listznstarelts(long m, long o)
{
  pari_sp av = avma;
  GEN L, zn, zns, res;
  long i, phi, ind, l;
  if (m == 2)
  {
    res = cgetg(2, t_VEC);
    gel(res,1) = mkvecsmall(1);
    return res;
  }
  zn = znstar(stoi(m));
  phi = itos(gel(zn,1));
  o = ugcd(o, phi); /* do we impose this on input ? */
  zns = znstar_small(zn);
  L = cgetg(o+1, t_VEC);
  for (i=1,ind = phi; ind; ind -= phi/o, i++) /* by *decreasing* exact index */
    gel(L,i) = subgrouplist(gel(zn,2), mkvec(utoipos(ind)));
  L = shallowconcat1(L); l = lg(L);
  for (i = 1; i < l; i++) gel(L,i) = znstar_hnf_elts(zns, gel(L,i));
  return gerepilecopy(av, L);
}

/* A sympol is a symmetric polynomial
 *
 * Currently sympol are couple of t_VECSMALL [v,w]
 * v[1]...v[k], w[1]...w[k]  represent the polynomial sum(i=1,k,v[i]*s_w[i])
 * where s_i(X_1,...,X_n) = sum(j=1,n,X_j^i) */

/*Return s_e*/
static GEN
sympol_eval_newtonsum(long e, GEN O, GEN mod)
{
  long f = lg(O), g = lg(O[1]), i, j;
  GEN PL = cgetg(f, t_COL);
  for(i=1; i<f; i++)
  {
    pari_sp av = avma;
    GEN s = gen_0;
    for(j=1; j<g; j++) s = addii(s, Fp_powu(gmael(O,i,j), (ulong)e, mod));
    gel(PL,i) = gerepileuptoint(av, remii(s,mod));
  }
  return PL;
}

static GEN
sympol_eval(GEN v, GEN NS)
{
  pari_sp av = avma;
  long i;
  GEN S = gen_0;
  for (i=1; i<lg(v); i++)
    if (v[i]) S = gadd(S, gmulsg(v[i], gel(NS,i)));
  return gerepileupto(av, S);
}

/* Let sigma be an automorphism of L (as a polynomial with rational coefs)
 * Let 'sym' be a symmetric polynomial defining alpha in L.
 * We have alpha = sym(x,sigma(x),,,sigma^(g-1)(x)). Compute alpha mod p */
static GEN
sympol_aut_evalmod(GEN sym, long g, GEN sigma, GEN Tp, GEN p)
{
  pari_sp ltop=avma;
  long i, j, npows = brent_kung_optpow(degpol(Tp)-1, g-1);
  GEN s, f, pows, v = zv_to_ZV(gel(sym,1)), w = zv_to_ZV(gel(sym,2));
  sigma = RgX_to_FpX(sigma, p);
  pows  = FpXQ_powers(sigma,npows,Tp,p);
  f = pol_x(varn(sigma));
  s = pol_0(varn(sigma));
  for(i=1; i<=g;i++)
  {
    if (i > 1) f = FpX_FpXQV_eval(f,pows,Tp,p);
    for(j=1; j<lg(v); j++)
      s = FpX_add(s, FpX_Fp_mul(FpXQ_pow(f,gel(w,j),Tp,p),gel(v,j),p),p);
  }
  return gerepileupto(ltop, s);
}

/* Let Sp be as computed with sympol_aut_evalmod
 * Let Tmod be the factorisation of T mod p.
 * Return the factorisation of the minimal polynomial of S mod p w.r.t. Tmod */
static GEN
fixedfieldfactmod(GEN Sp, GEN p, GEN Tmod)
{
  long i, l = lg(Tmod);
  GEN F = cgetg(l,t_VEC);
  for(i=1; i<l; i++)
  {
    GEN Ti = gel(Tmod,i);
    gel(F,i) = FpXQ_minpoly(FpX_rem(Sp,Ti,p), Ti,p);
  }
  return F;
}

static GEN
fixedfieldsurmer(GEN mod, GEN l, GEN p, long v, GEN NS, GEN W)
{
  const long step=3;
  long i, j, n = lg(W)-1, m = 1L<<((n-1)<<1);
  GEN sym = cgetg(n+1,t_VECSMALL), mod2 = shifti(mod,-1);
  for (j=1;j<n;j++) sym[j] = step;
  sym[n] = 0;
  if (DEBUGLEVEL>=4) err_printf("FixedField: Weight: %Ps\n",W);
  for (i=0; i<m; i++)
  {
    pari_sp av = avma;
    GEN L, P;
    for (j=1; sym[j]==step; j++) sym[j]=0;
    sym[j]++;
    if (DEBUGLEVEL>=6) err_printf("FixedField: Sym: %Ps\n",sym);
    L = sympol_eval(sym,NS);
    if (!vec_is1to1(FpC_red(L,l))) continue;
    P = FpX_center(FpV_roots_to_pol(L,mod,v),mod,mod2);
    if (!p || FpX_is_squarefree(P,p)) return mkvec3(mkvec2(sym,W),L,P);
    avma = av;
  }
  return NULL;
}

/*Check whether the line of NS are pair-wise distinct.*/
static long
sympol_is1to1_lg(GEN NS, long n)
{
  long i, j, k, l = lg(NS[1]);
  for (i=1; i<l; i++)
    for(j=i+1; j<l; j++)
    {
      for(k=1; k<n; k++)
        if (!equalii(gmael(NS,k,j),gmael(NS,k,i))) break;
      if (k>=n) return 0;
    }
  return 1;
}

/* Let O a set of orbits of roots (see fixedfieldorbits) modulo mod,
 * l | mod and p two prime numbers. Return a vector [sym,s,P] where:
 * sym is a sympol, s is the set of images of sym on O and
 * P is the polynomial with roots s. */
static GEN
fixedfieldsympol(GEN O, GEN mod, GEN l, GEN p, long v)
{
  pari_sp ltop=avma;
  const long n=(BITS_IN_LONG>>1)-1;
  GEN NS = cgetg(n+1,t_MAT), sym = NULL, W = cgetg(n+1,t_VECSMALL);
  long i, e=1;
  if (DEBUGLEVEL>=4)
    err_printf("FixedField: Size: %ldx%ld\n",lg(O)-1,lg(O[1])-1);
  for (i=1; !sym && i<=n; i++)
  {
    GEN L = sympol_eval_newtonsum(e++, O, mod);
    if (lg(O)>2)
      while (vec_isconst(L)) L = sympol_eval_newtonsum(e++, O, mod);
    W[i] = e-1; gel(NS,i) = L;
    if (sympol_is1to1_lg(NS,i+1))
      sym = fixedfieldsurmer(mod,l,p,v,NS,vecsmall_shorten(W,i));
  }
  if (!sym) pari_err(talker,"p too small in fixedfieldsympol");
  if (DEBUGLEVEL>=2) err_printf("FixedField: Found: %Ps\n",gel(sym,1));
  return gerepilecopy(ltop,sym);
}

/* Let O a set of orbits as indices and L the corresponding roots.
 * Return the set of orbits as roots. */
static GEN
fixedfieldorbits(GEN O, GEN L)
{
  GEN S = cgetg(lg(O), t_MAT);
  long i;
  for (i = 1; i < lg(O); i++) gel(S,i) = vecpermute(L, gel(O,i));
  return S;
}

static GEN
fixedfieldinclusion(GEN O, GEN PL)
{
  long i, j, f = lg(O)-1, g = lg(O[1])-1;
  GEN S = cgetg(f*g + 1, t_COL);
  for (i = 1; i <= f; i++)
  {
    GEN Oi = gel(O,i);
    for (j = 1; j <= g; j++) S[ Oi[j] ] = PL[i];
  }
  return S;
}

/*Usually mod > den so there is no need to reduce it.*/
GEN
vandermondeinversemod(GEN L, GEN T, GEN den, GEN mod)
{
  pari_sp av;
  long i, n = lg(L);
  GEN P, Tp, M = cgetg(n, t_MAT);
  av = avma;
  Tp = gclone(FpX_deriv(T,mod)); /*clone*/
  avma = av;
  for (i = 1; i < n; i++)
  {
    GEN z;
    av = avma;
    z = Fp_inv(FpX_eval(Tp, gel(L,i),mod),mod);
    z = Fp_mul(den,z,mod);
    P = FpX_Fp_mul(FpX_div_by_X_x(T, gel(L,i), mod, NULL), z, mod);
    gel(M,i) = gerepilecopy(av, RgX_to_RgV(P, n-1));
  }
  gunclone(Tp); /*unclone*/
  return M;
}

/* Polynomial associated to a vector of conjugates. Not stack clean */
static GEN
vectopol(GEN v, GEN M, GEN den , GEN mod, GEN mod2, long x)
{
  long l = lg(v)+1, i;
  GEN z = cgetg(l,t_POL);
  z[1] = evalsigne(1)|evalvarn(x);
  for (i=2; i<l; i++)
    gel(z,i) = gdiv(centermodii(ZMrow_ZC_mul(M,v,i-1), mod, mod2), den);
  return normalizepol_lg(z, l);
}

/* Polynomial associate to a permutation of the roots. Not stack clean */
static GEN
permtopol(GEN p, GEN L, GEN M, GEN den, GEN mod, GEN mod2, long x)
{
  if (lg(p) != lg(L)) pari_err(talker,"incorrect permutation in permtopol");
  return vectopol(vecpermute(L,p), M, den, mod, mod2, x);
}

static GEN
galoisgrouptopol(GEN res, GEN L, GEN M, GEN den, GEN mod, long v)
{
  long i, l = lg(res);
  GEN mod2 = shifti(mod,-1), aut = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
  {
    if (DEBUGLEVEL>=6) err_printf("%d ",i);
    gel(aut,i) = permtopol(gel(res,i), L, M, den, mod, mod2, v);
  }
  return aut;
}

static void
notgalois(long p, struct galois_analysis *ga)
{
  if (DEBUGLEVEL >= 2) err_printf("GaloisAnalysis:non Galois for p=%ld\n", p);
  ga->p = p;
  ga->deg = 0;
}

#define numberof(x) (long)(sizeof(x) / sizeof((x)[0]))

/*Gather information about the group*/
static long
init_group(long n, long np, GEN Fp, GEN Fe, long *porder)
{
  /*TODO: complete the table to at least 200*/
  const long prim_nonss_orders[] = { 36,48,56,60,72,75,80,96,108,120,132 };
  long i, phi_order = 1, order = 1, group = 0;

 /* non-WSS groups of this order? */
  for (i=0; i < numberof(prim_nonss_orders); i++)
    if (n % prim_nonss_orders[i] == 0) { group |= ga_non_wss; break; }
  if (np == 2 && Fp[2] == 3 && Fe[2] == 1 && Fe[1] > 2) group |= ga_ext_2;

  for (i = np; i > 0; i--)
  {
    long p = Fp[i];
    if (phi_order % p == 0) { group |= ga_all_normal; break; }
    order *= p; phi_order *= p-1;
    if (Fe[i] > 1) break;
  }
  *porder = order; return group;
}

/*is a "better" than b ? (if so, update karma) */
static int
improves(long a, long b, long plift, long p, long n, long *karma)
{
  if (!plift || a > b) { *karma = ugcd(p-1,n); return 1; }
  if (a == b) {
    long k = ugcd(p-1,n);
    if (k > *karma) { *karma = k; return 1; }
  }
  return 0; /* worse */
}

/* return 0 if not galois or not wss */
static int
galoisanalysis(GEN T, struct galois_analysis *ga, long calcul_l)
{
  pari_sp ltop = avma, av;
  long group, linf, n, p, i, karma = 0;
  GEN F, Fp, Fe, Fpe, O;
  long np, order, plift, nbmax, nbtest, deg;
  byteptr primepointer, pp;
  pari_timer ti;
  if (DEBUGLEVEL >= 1) timer_start(&ti);
  n = degpol(T);
  O = const_vecsmall(n, 0);
  F = factoru_pow(n);
  Fp = gel(F,1); np = lg(Fp)-1;
  Fe = gel(F,2);
  Fpe= gel(F,3);
  group = init_group(n, np, Fp, Fe, &order);

  /*Now we study the orders of the Frobenius elements*/
  deg = Fp[np]; /* largest prime | n */
  plift = 0;
  nbtest = 0;
  nbmax = 8+(n>>1);
  pp = primepointer = diffptr;
  p = init_primepointer(n*maxss(expu(n)-3, 2), 0, &primepointer);
  av = avma;
  while (!plift || (nbtest < nbmax && (nbtest <=8 || order < (n>>1)))
                || (n == 24 && O[6] == 0 && O[4] == 0)
                || ((group&ga_non_wss) && order == Fp[np]))
  {
    long d, o, norm_o = 1;
    GEN D, Tp;

    if ((group&ga_non_wss) && nbtest >= 3*nbmax) break; /* in all cases */

    if (nbtest++) { avma = av; NEXT_PRIME_VIADIFF_CHECK(p,primepointer); }
    Tp = ZX_to_Flx(T,p);
    if (!Flx_is_squarefree(Tp,p)) { if (!--nbtest) nbtest = 1; continue; }

    D = Flx_nbfact_by_degree(Tp, &d, p);
    o = n / d; /* d factors, all should have degree o */
    if (D[o] != d) { notgalois(p, ga); avma = ltop; return 0; }

    if (!O[o]) O[o] = p;
    if (o % deg) goto ga_end; /* NB: deg > 1 */
    if ((group&ga_all_normal) && o < order) goto ga_end;

    /*Frob_p has order o > 1, find a power which generates a normal subgroup*/
    if (o * Fp[1] >= n)
      norm_o = o; /*subgroups of smallest index are normal*/
    else
    {
      for (i = np; i > 0; i--)
      {
        if (o % Fpe[i]) break;
        norm_o *= Fpe[i];
      }
    }
    /* Frob_p^(o/norm_o) generates a normal subgroup of order norm_o */
    if (norm_o != 1)
    {
      if (!(group&ga_all_normal) || o > order)
        karma = ugcd(p-1,n);
      else if (!improves(norm_o, deg, plift,p,n, &karma)) goto ga_end;
      /* karma0=0, deg0<=norm_o -> the first improves() returns 1 */
      deg = norm_o; group |= ga_all_normal; /* STORE */
    }
    else if (group&ga_all_normal) goto ga_end;
    else if (!improves(o, order, plift,p,n, &karma)) goto ga_end;

    order = o; plift = p; pp = primepointer; /* STORE */
    ga_end:
    if (DEBUGLEVEL >= 5)
      err_printf("GaloisAnalysis:Nbtest=%ld,p=%ld,o=%ld,n_o=%d,best p=%ld,ord=%ld,k=%ld\n", nbtest, p, o, norm_o, plift, order,karma);
  }
  /* To avoid looping on non-wss group.
   * TODO: check for large groups. Would it be better to disable this check if
   * we are in a good case (ga_all_normal && !(ga_ext_2) (e.g. 60)) ?*/
  ga->p = plift;
  if (!plift || ((group&ga_non_wss) && order == Fp[np]))
  {
    pari_warn(warner,"Galois group almost certainly not weakly super solvable");
    return 0;
  }
  /*linf=(n*(n-1))>>2;*/
  linf = n;
  if (calcul_l && O[1] <= linf)
  {
    pari_sp av2 = avma;
    p = init_primepointer(linf+1, p, &primepointer);
    for(;; avma = av2) /*find a totally split prime l*/
    {
      GEN Tp = ZX_to_Flx(T, p);
      long nb = Flx_nbroots(Tp, p);
      if (nb == n) { O[1] = p; break; }
      if (nb && Flx_is_squarefree(Tp,p)) {
        notgalois(p,ga); avma = ltop; return 0;
      }
      NEXT_PRIME_VIADIFF_CHECK(p,primepointer);
    }
  }
  ga->group = (enum ga_code)group;
  ga->deg = deg;
  ga->ord = order;
  ga->primepointer = pp;
  ga->l  = O[1];
  ga->p4 = n >= 4 ? O[4] : 0;
  if (DEBUGLEVEL >= 4)
    err_printf("GaloisAnalysis:p=%ld l=%ld group=%ld deg=%ld ord=%ld\n",
               plift, O[1], group, deg, order);
  if (DEBUGLEVEL >= 1) timer_printf(&ti, "galoisanalysis()");
  avma = ltop; return 1;
}

static GEN
a4galoisgen(struct galois_test *td)
{
  const long n = 12;
  pari_sp ltop = avma, av, av2;
  long i, j, k, N, hop = 0;
  GEN MT, O,O1,O2,O3, ar, mt, t, u, res, orb, pft, pfu, pfv;

  res = cgetg(3, t_VEC);
  pft = cgetg(n+1, t_VECSMALL);
  pfu = cgetg(n+1, t_VECSMALL);
  pfv = cgetg(n+1, t_VECSMALL);
  gel(res,1) = mkvec3(pft,pfu,pfv);
  gel(res,2) = mkvecsmall3(2,2,3);
  av = avma;
  ar = cgetg(5, t_VECSMALL);
  mt = gel(td->PV, td->order[n]);
  t = identity_perm(n) + 1; /* Sorry for this hack */
  u = cgetg(n+1, t_VECSMALL) + 1; /* too lazy to correct */
  MT = cgetg(n+1, t_MAT);
  for (j = 1; j <= n; j++) gel(MT,j) = cgetg(n+1, t_VECSMALL);
  for (j = 1; j <= n; j++)
    for (i = 1; i < j; i++)
      coeff(MT,i,j) = coeff(MT,j,i) = coeff(mt,i,j)+coeff(mt,j,i);
  /* MT(i,i) unused */

  av2 = avma;
  /* N = itos(gdiv(mpfact(n), mpfact(n >> 1))) >> (n >> 1); */
  /* n = 2k = 12; N = (2k)! / (k! * 2^k) = 10395 */
  N = 10395;
  if (DEBUGLEVEL>=4) err_printf("A4GaloisConj:will test %ld permutations\n", N);
  ar[4] = mael(MT,11,12);
  ar[3] = ar[4] + mael(MT,9,10);
  ar[2] = ar[3] + mael(MT,7,8);
  ar[1] = ar[2] + mael(MT,5,6);
  for (i = 0; i < N; i++)
  {
    long g;
    if (i)
    {
      long a, x = i, y = 1;
      do { y += 2; a = x%y; x = x/y; } while (!a);
      switch (y)
      {
      case 3:
        lswap(t[2], t[2-a]);
        break;
      case 5:
        x = t[0]; t[0] = t[2]; t[2] = t[1]; t[1] = x;
        lswap(t[4], t[4-a]);
        ar[1] = ar[2] + mael(MT,t[4],t[5]);
        break;
      case 7:
        x = t[0]; t[0] = t[4]; t[4] = t[3]; t[3] = t[1]; t[1] = t[2]; t[2] = x;
        lswap(t[6], t[6-a]);
        ar[2] = ar[3] + mael(MT,t[6],t[7]);
        ar[1] = ar[2] + mael(MT,t[4],t[5]);
        break;
      case 9:
        x = t[0]; t[0] = t[6]; t[6] = t[5]; t[5] = t[3]; t[3] = x;
        lswap(t[1], t[4]);
        lswap(t[8], t[8-a]);
        ar[3] = ar[4] + mael(MT,t[8],t[9]);
        ar[2] = ar[3] + mael(MT,t[6],t[7]);
        ar[1] = ar[2] + mael(MT,t[4],t[5]);
        break;
      case 11:
        x = t[0]; t[0] = t[8]; t[8] = t[7]; t[7] = t[5]; t[5] = t[1];
        t[1] = t[6]; t[6] = t[3]; t[3] = t[2]; t[2] = t[4]; t[4] = x;
        lswap(t[10], t[10-a]);
        ar[4] = mael(MT,t[10],t[11]);
        ar[3] = ar[4] + mael(MT,t[8],t[9]);
        ar[2] = ar[3] + mael(MT,t[6],t[7]);
        ar[1] = ar[2] + mael(MT,t[4],t[5]);
      }
    }
    g = ar[1]+mael(MT,t[0],t[1])+mael(MT,t[2],t[3]);
    if (headlongisint(g,n))
    {
      for (k = 0; k < n; k += 2)
      {
        pft[t[k]] = t[k+1];
        pft[t[k+1]] = t[k];
      }
      if (galois_test_perm(td, pft)) break;
      hop++;
    }
    avma = av2;
  }
  if (DEBUGLEVEL >= 1 && hop)
    err_printf("A4GaloisConj: %ld hop over %ld iterations\n", hop, N);
  if (i == N) { avma = ltop; return gen_0; }
  /* N = itos(gdiv(mpfact(n >> 1), mpfact(n >> 2))) >> 1; */
  N = 60;
  if (DEBUGLEVEL >= 4) err_printf("A4GaloisConj:sigma=%Ps \n", pft);
  for (k = 0; k < n; k += 4)
  {
    u[k+3] = t[k+3];
    u[k+2] = t[k+1];
    u[k+1] = t[k+2];
    u[k]   = t[k];
  }
  for (i = 0; i < N; i++)
  {
    long g = 0;
    if (i)
    {
      long a, x = i, y = -2;
      do { y += 4; a = x%y; x = x/y; } while (!a);
      lswap(u[0],u[2]);
      switch (y)
      {
      case 2:
        break;
      case 6:
        lswap(u[4],u[6]);
        if (!(a & 1))
        {
          a = 4 - (a>>1);
          lswap(u[6], u[a]);
          lswap(u[4], u[a-2]);
        }
        break;
      case 10:
        x = u[6];
        u[6] = u[3];
        u[3] = u[2];
        u[2] = u[4];
        u[4] = u[1];
        u[1] = u[0];
        u[0] = x;
        if (a >= 3) a += 2;
        a = 8 - a;
        lswap(u[10],u[a]);
        lswap(u[8], u[a-2]);
        break;
      }
    }
    for (k = 0; k < n; k += 2) g += mael(MT,u[k],u[k+1]);
    if (headlongisint(g,n))
    {
      for (k = 0; k < n; k += 2)
      {
        pfu[u[k]] = u[k+1];
        pfu[u[k+1]] = u[k];
      }
      if (galois_test_perm(td, pfu)) break;
      hop++;
    }
    avma = av2;
  }
  if (i == N) { avma = ltop; return gen_0; }
  if (DEBUGLEVEL >= 1 && hop)
    err_printf("A4GaloisConj: %ld hop over %ld iterations\n", hop, N);
  if (DEBUGLEVEL >= 4) err_printf("A4GaloisConj:tau=%Ps \n", pfu);
  avma = av2;
  orb = mkvec2(pft,pfu);
  O = vecperm_orbits(orb, 12);
  if (DEBUGLEVEL >= 4) {
    err_printf("A4GaloisConj:orb=%Ps\n", orb);
    err_printf("A4GaloisConj:O=%Ps \n", O);
  }
  av2 = avma;
  O1 = gel(O,1); O2 = gel(O,2); O3 = gel(O,3);
  for (j = 0; j < 2; j++)
  {
    pfv[O1[1]] = O2[1];
    pfv[O1[2]] = O2[3+j];
    pfv[O1[3]] = O2[4 - (j << 1)];
    pfv[O1[4]] = O2[2+j];
    for (i = 0; i < 4; i++)
    {
      long g = 0;
      switch (i)
      {
      case 0: break;
      case 1: lswap(O3[1], O3[2]); lswap(O3[3], O3[4]); break;
      case 2: lswap(O3[1], O3[4]); lswap(O3[2], O3[3]); break;
      case 3: lswap(O3[1], O3[2]); lswap(O3[3], O3[4]); break;
      }
      pfv[O2[1]]          = O3[1];
      pfv[O2[3+j]]        = O3[4-j];
      pfv[O2[4 - (j<<1)]] = O3[2 + (j<<1)];
      pfv[O2[2+j]]        = O3[3-j];
      pfv[O3[1]]          = O1[1];
      pfv[O3[4-j]]        = O1[2];
      pfv[O3[2 + (j<<1)]] = O1[3];
      pfv[O3[3-j]]        = O1[4];
      for (k = 1; k <= n; k++) g += mael(mt,k,pfv[k]);
      if (headlongisint(g,n) && galois_test_perm(td, pfv))
      {
        avma = av;
        if (DEBUGLEVEL >= 1)
          err_printf("A4GaloisConj:%ld hop over %d iterations max\n",
                     hop, 10395 + 68);
        return res;
      }
      hop++; avma = av2;
    }
  }
  avma = ltop; return gen_0; /* Fail */
}

/* S4 */
static void
s4makelift(GEN u, struct galois_lift *gl, GEN liftpow)
{
  GEN s = automorphismlift(u, gl, NULL);
  long i;
  gel(liftpow,1) = s;
  for (i = 2; i < lg(liftpow); i++)
    gel(liftpow,i) = FpXQ_mul(gel(liftpow,i-1), s, gl->TQ, gl->Q);
}
static long
s4test(GEN u, GEN liftpow, struct galois_lift *gl, GEN phi)
{
  pari_sp av = avma;
  GEN res, Q, Q2;
  long bl, i, d = lg(u)-2;
  pari_timer ti;
  if (DEBUGLEVEL >= 6) timer_start(&ti);
  if (!d) return 0;
  Q = gl->Q; Q2 = shifti(Q,-1);
  res = gel(u,2);
  for (i = 1; i < d; i++)
    if (lg(liftpow[i])>2)
      res = addii(res, mulii(gmael(liftpow,i,2), gel(u,i+2)));
  res = remii(res,Q);
  if (gl->den != gen_1) res = mulii(res, gl->den);
  res = centermodii(res, Q,Q2);
  if (absi_cmp(res, gl->gb->bornesol) > 0) { avma = av; return 0; }
  res = scalar_ZX_shallow(gel(u,2),varn(u));
  for (i = 1; i < d ; i++)
    if (lg(liftpow[i])>2)
      res = ZX_add(res, ZX_Z_mul(gel(liftpow,i), gel(u,i+2)));
  res = FpX_red(res, Q);
  if (gl->den != gen_1) res = FpX_Fp_mul(res, gl->den, Q);
  res = FpX_center(res, Q, shifti(Q,-1));
  bl = poltopermtest(res, gl, phi);
  if (DEBUGLEVEL >= 6) timer_printf(&ti, "s4test()");
  avma = av; return bl;
}

static GEN
aux(long a, long b, GEN T, GEN M, GEN p, GEN *pu)
{
  *pu = FpX_mul(gel(T,b), gel(T,a),p);
  return FpX_chinese_coprime(gmael(M,a,b), gmael(M,b,a),
                             gel(T,b), gel(T,a), *pu, p);
}

static GEN
s4releveauto(GEN misom,GEN Tmod,GEN Tp,GEN p,long a1,long a2,long a3,long a4,long a5,long a6)
{
  pari_sp av = avma;
  GEN u4,u5;
  GEN pu1, pu2, pu3, pu4;
  GEN u1 = aux(a1, a2, Tmod, misom, p, &pu1);
  GEN u2 = aux(a3, a4, Tmod, misom, p, &pu2);
  GEN u3 = aux(a5, a6, Tmod, misom, p, &pu3);
  pu4 = FpX_mul(pu1,pu2,p);
  u4 = FpX_chinese_coprime(u1,u2,pu1,pu2,pu4,p);
  u5 = FpX_chinese_coprime(u4,u3,pu4,pu3,Tp,p);
  return gerepileupto(av, u5);
}
static GEN
lincomb(GEN A, GEN B, GEN pauto, long j)
{
  long k = (-j) & 3;
  if (j == k) return ZX_mul(ZX_add(A,B), gel(pauto, j+1));
  return ZX_add(ZX_mul(A, gel(pauto, j+1)), ZX_mul(B, gel(pauto, k+1)));
}
/* FIXME: could use the intheadlong technique */
static GEN
s4galoisgen(struct galois_lift *gl)
{
  const long n = 24;
  struct galois_testlift gt;
  pari_sp av, ltop2, ltop = avma;
  long i, j;
  GEN sigma, tau, phi, res, r1,r2,r3,r4, pj, p = gl->p, Q = gl->Q, TQ = gl->TQ;
  GEN sg, Tp, Tmod, isom, isominv, misom, Bcoeff, pauto, liftpow, aut;

  res = cgetg(3, t_VEC);
  r1 = cgetg(n+1, t_VECSMALL);
  r2 = cgetg(n+1, t_VECSMALL);
  r3 = cgetg(n+1, t_VECSMALL);
  r4 = cgetg(n+1, t_VECSMALL);
  gel(res,1)= mkvec4(r1,r2,r3,r4);
  gel(res,2) = mkvecsmall4(2,2,3,2);
  ltop2 = avma;
  sg = identity_perm(6);
  pj = const_vecsmall(6, 0);
  sigma = cgetg(n+1, t_VECSMALL);
  tau = cgetg(n+1, t_VECSMALL);
  phi = cgetg(n+1, t_VECSMALL);
  Tp = FpX_red(gl->T,p);
  Tmod = gel(FpX_factor(Tp,p), 1);
  isom    = cgetg(lg(Tmod), t_VEC);
  isominv = cgetg(lg(Tmod), t_VEC);
  misom   = cgetg(lg(Tmod), t_MAT);
  aut = galoisdolift(gl, NULL);
  inittestlift(aut, Tmod, gl, &gt);
  Bcoeff = gt.bezoutcoeff;
  pauto = gt.pauto;
  for (i = 1; i < lg(isom); i++)
  {
    gel(misom,i) = cgetg(lg(Tmod), t_COL);
    gel(isom,i) = FpX_ffisom(gel(Tmod,1), gel(Tmod,i), p);
    if (DEBUGLEVEL >= 6)
      err_printf("S4GaloisConj:Computing isomorphisms %d:%Ps\n", i,
                 gel(isom,i));
    gel(isominv,i) = FpXQ_ffisom_inv(gel(isom,i), gel(Tmod,i),p);
  }
  for (i = 1; i < lg(isom); i++)
    for (j = 1; j < lg(isom); j++)
      gmael(misom,i,j) = FpX_FpXQ_eval(gel(isominv,i),gel(isom,j),
                                         gel(Tmod,j),p);
  liftpow = cgetg(24, t_VEC);
  av = avma;
  for (i = 0; i < 3; i++, avma = av)
  {
    pari_sp av1, av2, av3;
    GEN u, u1, u2, u3;
    long j1, j2, j3;
    if (i)
    {
      if (i == 1) { lswap(sg[2],sg[3]); }
      else        { lswap(sg[1],sg[3]); }
    }
    u = s4releveauto(misom,Tmod,Tp,p,sg[1],sg[2],sg[3],sg[4],sg[5],sg[6]);
    s4makelift(u, gl, liftpow);
    av1 = avma;
    for (j1 = 0; j1 < 4; j1++, avma = av1)
    {
      u1 = lincomb(gel(Bcoeff,sg[5]),gel(Bcoeff,sg[6]), pauto,j1);
      u1 = FpX_rem(u1, TQ, Q); av2 = avma;
      for (j2 = 0; j2 < 4; j2++, avma = av2)
      {
        u2 = lincomb(gel(Bcoeff,sg[3]),gel(Bcoeff,sg[4]), pauto,j2);
        u2 = FpX_rem(FpX_add(u1, u2, Q), TQ,Q); av3 = avma;
        for (j3 = 0; j3 < 4; j3++, avma = av3)
        {
          u3 = lincomb(gel(Bcoeff,sg[1]),gel(Bcoeff,sg[2]), pauto,j3);
          u3 = FpX_rem(FpX_add(u2, u3, Q), TQ,Q);
          if (DEBUGLEVEL >= 4)
            err_printf("S4GaloisConj:Testing %d/3:%d/4:%d/4:%d/4:%Ps\n",
                       i,j1,j2,j3, sg);
          if (s4test(u3, liftpow, gl, sigma))
          {
            pj[1] = j3;
            pj[2] = j2;
            pj[3] = j1; goto suites4;
          }
        }
      }
    }
  }
  avma = ltop; return gen_0;
suites4:
  if (DEBUGLEVEL >= 4) err_printf("S4GaloisConj:sigma=%Ps\n", sigma);
  if (DEBUGLEVEL >= 4) err_printf("S4GaloisConj:pj=%Ps\n", pj);
  avma = av;
  for (j = 1; j <= 3; j++)
  {
    pari_sp av2, av3;
    GEN u;
    long w, l, z;
    z = sg[1]; sg[1] = sg[3]; sg[3] = sg[5]; sg[5] = z;
    z = sg[2]; sg[2] = sg[4]; sg[4] = sg[6]; sg[6] = z;
    z = pj[1]; pj[1] = pj[2]; pj[2] = pj[3]; pj[3] = z;
    for (l = 0; l < 2; l++, avma = av)
    {
      u = s4releveauto(misom,Tmod,Tp,p,sg[1],sg[3],sg[2],sg[4],sg[5],sg[6]);
      s4makelift(u, gl, liftpow);
      av2 = avma;
      for (w = 0; w < 4; w += 2, avma = av2)
      {
        GEN uu;
        pj[6] = (w + pj[3]) & 3;
        uu = lincomb(gel(Bcoeff,sg[5]),gel(Bcoeff,sg[6]), pauto, pj[6]);
        uu = FpX_rem(FpX_red(uu,Q), TQ, Q);
        av3 = avma;
        for (i = 0; i < 4; i++, avma = av3)
        {
          GEN u;
          pj[4] = i;
          pj[5] = (i + pj[2] - pj[1]) & 3;
          if (DEBUGLEVEL >= 4)
            err_printf("S4GaloisConj:Testing %d/3:%d/2:%d/2:%d/4:%Ps:%Ps\n",
                       j-1, w >> 1, l, i, sg, pj);
          u = ZX_add(lincomb(gel(Bcoeff,sg[1]),gel(Bcoeff,sg[3]), pauto,pj[4]),
                     lincomb(gel(Bcoeff,sg[2]),gel(Bcoeff,sg[4]), pauto,pj[5]));
          u = FpX_rem(FpX_add(uu,u,Q), TQ, Q);
          if (s4test(u, liftpow, gl, tau)) goto suites4_2;
        }
      }
      lswap(sg[3], sg[4]);
      pj[2] = (-pj[2]) & 3;
    }
  }
  avma = ltop; return gen_0;
suites4_2:
  avma = av;
  {
    long abc = (pj[1] + pj[2] + pj[3]) & 3;
    long abcdef = ((abc + pj[4] + pj[5] - pj[6]) & 3) >> 1;
    GEN u;
    pari_sp av2;
    u = s4releveauto(misom,Tmod,Tp,p,sg[1],sg[4],sg[2],sg[5],sg[3],sg[6]);
    s4makelift(u, gl, liftpow);
    av2 = avma;
    for (j = 0; j < 8; j++)
    {
      long h, g, i;
      h = j & 3;
      g = (abcdef + ((j & 4) >> 1)) & 3;
      i = (h + abc - g) & 3;
      u = ZX_add(   lincomb(gel(Bcoeff,sg[1]), gel(Bcoeff,sg[4]), pauto, g),
                    lincomb(gel(Bcoeff,sg[2]), gel(Bcoeff,sg[5]), pauto, h));
      u = FpX_add(u, lincomb(gel(Bcoeff,sg[3]), gel(Bcoeff,sg[6]), pauto, i),Q);
      u = FpX_rem(u, TQ, Q);
      if (DEBUGLEVEL >= 4)
        err_printf("S4GaloisConj:Testing %d/8 %d:%d:%d\n", j,g,h,i);
      if (s4test(u, liftpow, gl, phi)) break;
      avma = av2;
    }
  }
  if (j == 8) { avma = ltop; return gen_0; }
  for (i = 1; i <= n; i++)
  {
    r1[i] = sigma[tau[i]];
    r2[i] = phi[sigma[tau[phi[i]]]];
    r3[i] = phi[sigma[i]];
    r4[i] = sigma[i];
  }
  avma = ltop2; return res;
}

static GEN
galoisfindgroups(GEN lo, GEN sg, long f)
{
  pari_sp ltop = avma;
  long i, j, k;
  GEN V = cgetg(lg(lo), t_VEC);
  for(j=1,i=1; i<lg(lo); i++)
  {
    pari_sp av = avma;
    GEN loi = gel(lo,i), W = cgetg(lg(loi),t_VECSMALL);
    for (k=1; k<lg(loi); k++) W[k] = loi[k] % f;
    W = vecsmall_uniq(W);
    if (zv_equal(W, sg)) gel(V,j++) = loi;
    avma = av;
  }
  setlg(V,j); return gerepilecopy(ltop,V);
}

static long
galoisfrobeniustest(GEN aut, struct galois_lift *gl, GEN frob)
{
  pari_sp av = avma;
  GEN tlift = aut;
  long res;
  if (gl->den != gen_1) tlift = FpX_Fp_mul(tlift, gl->den, gl->Q);
  tlift = FpX_center(tlift, gl->Q, shifti(gl->Q,-1));
  res = poltopermtest(tlift, gl, frob);
  avma = av; return res;
}

static GEN
galoismakepsi(long g, GEN sg, GEN pf)
{
  GEN psi=cgetg(g+1,t_VECSMALL);
  long i;
  for (i = 1; i < g; i++) psi[i] = sg[pf[i]];
  psi[g] = sg[1]; return psi;
}

static GEN
galoisfrobeniuslift(GEN T, GEN den, GEN L,  GEN Lden,
    struct galois_frobenius *gf,  struct galois_borne *gb)
{
  pari_sp ltop=avma, av2;
  struct galois_testlift gt;
  struct galois_lift gl;
  long i, j, k, n = lg(L)-1, deg = 1, g = lg(gf->Tmod)-1;
  GEN F,Fp,Fe, aut, frob, ip = utoipos(gf->p), res = cgetg(lg(L), t_VECSMALL);
  if (DEBUGLEVEL >= 4)
    err_printf("GaloisConj:p=%ld deg=%ld fp=%ld\n", gf->p, deg, gf->fp);
  gf->psi = const_vecsmall(g,1);
  av2 = avma;
  initlift(T, den, ip, L, Lden, gb, &gl);
  aut = galoisdolift(&gl, res);
  if (!aut || galoisfrobeniustest(aut,&gl,res))
  {
    avma = av2; gf->deg = gf->fp; return res;
  }
  inittestlift(aut,gf->Tmod, &gl, &gt);
  gt.C = cgetg(gf->fp+1,t_VEC);
  gt.Cd= cgetg(gf->fp+1,t_VEC);
  for (i = 1; i <= gf->fp; i++) {
    gel(gt.C,i)  = const_vecsmall(gt.g, 0);
    gel(gt.Cd,i) = const_vecsmall(gt.g, 0);
  }

  F =factoru(gf->fp);
  Fp = gel(F,1);
  Fe = gel(F,2);
  frob = cgetg(lg(L), t_VECSMALL);
  for(k=lg(Fp)-1;k>=1;k--)
  {
    pari_sp btop=avma;
    GEN psi=NULL, fres=NULL, sg = identity_perm(1);
    long el=gf->fp, dg=1, dgf=1, e, pr;
    for(e=1; e<=Fe[k]; e++)
    {
      GEN lo, pf;
      long l;
      dg *= Fp[k]; el /= Fp[k];
      if (DEBUGLEVEL>=4) err_printf("Trying degre %d.\n",dg);
      if (galoisfrobeniustest(gel(gt.pauto,el+1),&gl,frob))
      {
        psi = const_vecsmall(g,1);
        dgf = dg; fres = gcopy(frob); continue;
      }
      dbg_block();
      lo = listznstarelts(dg, n / gf->fp);
      dbg_release();
      if (e!=1) lo = galoisfindgroups(lo, sg, dgf);
      if (DEBUGLEVEL>=4) err_printf("Galoisconj:Subgroups list:%Ps\n", lo);
      for (l = 1; l < lg(lo); l++)
        if (lg(lo[l])>2 && frobeniusliftall(gel(lo,l), el, &pf,&gl,&gt, frob))
        {
          sg  = gcopy(gel(lo,l));
          psi = galoismakepsi(g,sg,pf);
          dgf = dg; fres = gcopy(frob); break;
        }
      if (l == lg(lo)) break;
    }
    if (dgf == 1) { avma = btop; continue; }
    pr = deg*dgf;
    if (deg == 1)
    {
      for(i=1;i<lg(res);i++) res[i]=fres[i];
      for(i=1;i<lg(psi);i++) gf->psi[i]=psi[i];
    }
    else
    {
      GEN cp = perm_mul(res,fres);
      for(i=1;i<lg(res);i++) res[i] = cp[i];
      for(i=1;i<lg(psi);i++) gf->psi[i] = (dgf*gf->psi[i] + deg*psi[i]) % pr;
    }
    deg = pr; avma = btop;
  }
  for (i = 1; i <= gf->fp; i++)
    for (j = 1; j <= gt.g; j++)
      if (mael(gt.C,i,j)) gunclone(gmael(gt.C,i,j));
  if (DEBUGLEVEL>=4 && res) err_printf("Best lift: %d\n",deg);
  if (deg==1) { avma = ltop; return NULL; }
  else
  {
    /* Normalize result so that psi[g]=1 */
    long im = Fl_inv(gf->psi[g], deg);
    GEN cp = perm_pow(res, im);
    for(i=1;i<lg(res);i++) res[i] = cp[i];
    for(i=1;i<lg(gf->psi);i++) gf->psi[i] = Fl_mul(im, gf->psi[i], deg);
    avma = av2; gf->deg = deg; return res;
  }
}

/* return NULL if not Galois */
static GEN
galoisfindfrobenius(GEN T, GEN L, GEN den, struct galois_frobenius *gf,
    struct galois_borne *gb, const struct galois_analysis *ga)
{
  pari_sp ltop = avma;
  long Try = 0, n = degpol(T), deg, gmask = (ga->group&ga_ext_2)? 3: 1;
  byteptr primepointer = ga->primepointer;
  GEN frob, Lden = makeLden(L,den,gb);
  deg = gf->deg = ga->deg; gf->p = ga->p;
  for (;;)
  {
    pari_sp lbot, av = avma;
    GEN Ti, Tp = ZX_to_Flx(T, gf->p);
    long nb, d;
    if (!Flx_is_squarefree(Tp, gf->p)) goto nextp;
    Ti = gel(FpX_factor(Flx_to_ZX(Tp), utoipos(gf->p)), 1);
    nb = lg(Ti)-1; d = degpol(gel(Ti,1));
    if (nb > 1 && degpol(gel(Ti,nb)) != d) { avma = ltop; return NULL; }
    if (((gmask&1)==0 || d % deg) && ((gmask&2)==0 || odd(d))) goto nextp;
    if (DEBUGLEVEL >= 1) err_printf("GaloisConj: Trying p=%ld\n", gf->p);
    gf->fp = d;
    gf->Tmod = Ti; lbot = avma;
    frob = galoisfrobeniuslift(T, den, L, Lden, gf, gb);
    if (frob)
    {
      GEN *gptr[3];
      gf->Tmod = gcopy(Ti);
      gptr[0]=&gf->Tmod; gptr[1]=&gf->psi; gptr[2]=&frob;
      gerepilemanysp(ltop,lbot,gptr,3); return frob;
    }
    if ((ga->group&ga_all_normal) && d % deg == 0) gmask &= ~1;
    /* The first prime degree is always divisible by deg, so we don't
     * have to worry about ext_2 being used before regular supersolvable*/
    if (!gmask) { avma = ltop; return NULL; }
    if ((ga->group&ga_non_wss) && ++Try > ((3*n)>>1))
    {
      pari_warn(warner,"Galois group almost certainly not weakly super solvable");
      return NULL;
    }
nextp:
    NEXT_PRIME_VIADIFF_CHECK(gf->p, primepointer);
    avma = av;
  }
}

static GEN
galoisgen(GEN T, GEN L, GEN M, GEN den, struct galois_borne *gb,
          const struct galois_analysis *ga);
static GEN
galoisgenfixedfield(GEN Tp, GEN Pmod, GEN V, GEN ip, struct galois_borne *gb, GEN Pg)
{
  pari_sp ltop=avma;
  GEN     P, PL, Pden, PM, Pp;
  GEN     tau, PG;
  long    g,gp;
  long    x=varn(Tp);
  P=gel(V,3);
  PL=gel(V,2);
  gp=lg(Pmod)-1;
  Pp = FpX_red(P,ip);
  if (DEBUGLEVEL>=6)
    err_printf("GaloisConj: Fixed field %Ps\n",P);
  if (degpol(P)==2)
  {
    PG=cgetg(3,t_VEC);
    gel(PG,1) = mkvec( mkvecsmall2(2,1) );
    gel(PG,2) = mkvecsmall(2);
    tau = deg1pol_shallow(gen_m1, negi(gel(P,3)), x);
    tau = RgX_to_FpX(tau, ip);
    tau = FpX_FpXQ_eval(gel(Pmod,gp), tau,Pp,ip);
    tau = FpX_gcd(Pp, tau,ip);
    tau = FpX_normalize(tau, ip);
    for (g = 1; g <= gp; g++)
      if (ZX_equal(tau, gel(Pmod,g))) break;
    if (g == lg(Pmod)) return NULL;
    Pg[1]=g;
  }
  else
  {
    struct galois_analysis Pga;
    struct galois_borne Pgb;
    GEN mod, mod2;
    long j;
    if (!galoisanalysis(P, &Pga, 0)) return NULL;
    Pgb.l = gb->l;
    Pden = galoisborne(P, NULL, &Pgb, degpol(P));

    if (Pgb.valabs > gb->valabs)
    {
      if (DEBUGLEVEL>=4)
        err_printf("GaloisConj:increase prec of p-adic roots of %ld.\n"
            ,Pgb.valabs-gb->valabs);
      PL = ZpX_liftroots(P,PL,gb->l,Pgb.valabs);
    }
    else if (Pgb.valabs < gb->valabs)
      PL = FpC_red(PL, Pgb.ladicabs);
    PM = vandermondeinversemod(PL, P, Pden, Pgb.ladicabs);
    PG = galoisgen(P, PL, PM, Pden, &Pgb, &Pga);
    mod = Pgb.ladicabs; mod2 = shifti(mod, -1);
    if (PG == gen_0) return NULL;
    for (j = 1; j < lg(PG[1]); j++)
    {
      pari_sp btop=avma;
      tau = permtopol(gmael(PG,1,j), PL, PM, Pden, mod, mod2, x);
      tau = RgX_to_FpX(tau, ip);
      tau = FpX_FpXQ_eval(gel(Pmod,gp), tau,Pp,ip);
      tau = FpX_gcd(Pp, tau,ip);
      tau = FpX_normalize(tau, ip);
      for (g = 1; g < lg(Pmod); g++)
        if (ZX_equal(tau, gel(Pmod,g))) break;
      if (g == lg(Pmod)) return NULL;
      avma=btop;
      Pg[j]=g;
    }
  }
  return gerepilecopy(ltop,PG);
}

/* Let sigma^m=1,  tau*sigma*tau^-1=sigma^s.
 * Compute n so that (sigma*tau)^e = sigma^n*tau^e
 * We have n = sum_{k=0}^{e-1} s^k mod m.
 * so n*(1-s) = 1-s^e mod m
 * Unfortunately (1-s) might not invertible mod m.
 */

static long
stpow(long s, long e, long m)
{
  long i;
  long n = 1;
  for (i = 1; i < e; i++)
    n = (1 + n * s) % m;
  return n;
}

static GEN
wpow(long s, long m, long e, long n)
{
  GEN   w = cgetg(n+1,t_VECSMALL);
  long si = s;
  long i;
  w[1] = 1;
  for(i=2; i<=n; i++) w[i] = w[i-1]*e;
  for(i=n; i>=1; i--)
  {
    si = Fl_powu(si,e,m);
    w[i] = Fl_mul(s-1, stpow(si, w[i], m), m);
  }
  return w;
}

static GEN
galoisgen(GEN T, GEN L, GEN M, GEN den, struct galois_borne *gb,
          const struct galois_analysis *ga)
{
  struct galois_test td;
  struct galois_frobenius gf;
  pari_sp lbot, ltop2, ltop = avma;
  long p, deg, x, i, j, n = degpol(T);
  GEN sigma, Tmod, res, res1, res2, pf, ip, frob, O, PG, PG1, PG2, Pg;

  if (!ga->deg) return gen_0;
  x = varn(T);
  if (DEBUGLEVEL >= 9) err_printf("GaloisConj:denominator:%Ps\n", den);
  if (n == 12 && ga->ord==3 && !ga->p4)
  { /* A4 is very probable: test it first */
    pari_sp av = avma;
    if (DEBUGLEVEL >= 4) err_printf("GaloisConj:Testing A4 first\n");
    inittest(L, M, gb->bornesol, gb->ladicsol, &td);
    lbot = avma;
    PG = a4galoisgen(&td);
    freetest(&td);
    if (PG != gen_0) return gerepile(ltop, lbot, PG);
    avma = av;
  }
  if (n == 24 && ga->ord==3)
  { /* S4 is very probable: test it first */
    pari_sp av = avma;
    struct galois_lift gl;
    if (DEBUGLEVEL >= 4) err_printf("GaloisConj:Testing S4 first\n");
    lbot = avma;
    initlift(T, den, stoi(ga->p4), L, makeLden(L,den,gb), gb, &gl);
    PG = s4galoisgen(&gl);
    if (PG != gen_0) return gerepile(ltop, lbot, PG);
    avma = av;
  }
  frob = galoisfindfrobenius(T, L, den, &gf, gb, ga);
  if (!frob) { avma=ltop; return gen_0; }
  p = gf.p; ip = utoipos(p);
  Tmod = gf.Tmod;
  O = perm_cycles(frob);
  deg = lg(O[1])-1;
  sigma = permtopol(frob, L, M, den, gb->ladicabs, shifti(gb->ladicabs,-1), x);
  if (DEBUGLEVEL >= 9) err_printf("GaloisConj:Orbite:%Ps\n", O);
  if (deg == n)        /* cyclic */
  {
    lbot = avma;
    res = cgetg(3, t_VEC);
    gel(res,1) = mkvec( cyc_pow_perm(O,1) );
    gel(res,2) = mkvecsmall(deg);
    return gerepile(ltop, lbot, res);
  }
  if (DEBUGLEVEL >= 9) err_printf("GaloisConj:Frobenius:%Ps\n", sigma);
  Pg=cgetg(lg(O),t_VECSMALL);
  {
    pari_sp btop=avma;
    GEN     V, Tp, Sp, Pmod;
    GEN OL = fixedfieldorbits(O,L);
    V  = fixedfieldsympol(OL, gb->ladicabs, gb->l, ip, x);
    Tp = FpX_red(T,ip);
    Sp = sympol_aut_evalmod(gel(V,1),deg,sigma,Tp,ip);
    Pmod = fixedfieldfactmod(Sp,ip,Tmod);
    PG = galoisgenfixedfield(Tp, Pmod, V, ip, gb, Pg);
    if (PG == NULL) { avma = ltop; return gen_0; }
    if (DEBUGLEVEL >= 4) err_printf("GaloisConj:Back to Earth:%Ps\n", PG);
    PG=gerepileupto(btop, PG);
  }
  inittest(L, M, gb->bornesol, gb->ladicsol, &td);
  PG1 = gel(PG, 1);
  PG2 = gel(PG, 2);
  lbot = avma;
  res = cgetg(3, t_VEC);
  gel(res,1) = res1 = cgetg(lg(PG1) + 1, t_VEC);
  gel(res,2) = res2 = cgetg(lg(PG1) + 1, t_VECSMALL);
  gel(res1, 1) = cyc_pow_perm(O,1);
  res2[1] = deg;
  for (i = 2; i < lg(res1); i++) gel(res1,i) = cgetg(n+1, t_VECSMALL);
  ltop2 = avma;
  for (j = 1; j < lg(PG1); j++)
  {
    long sr, k;
    GEN  X  = cgetg(lg(O), t_VECSMALL);
    GEN  oX = cgetg(lg(O), t_VECSMALL);
    GEN  gj = gel(PG1, j);
    long s  = gf.psi[Pg[j]];
    GEN  B  = perm_cycles(gj);
    long oj = lg(B[1]) - 1;
    GEN  F  = factoru(oj);
    GEN  Fp = gel(F,1);
    GEN  Fe = gel(F,2);
    if (DEBUGLEVEL >= 6)
      err_printf("GaloisConj: G[%d]=%Ps of relative order %d\n", j, gj, oj);
    B = perm_cycles(gel(PG1,j));
    pf = identity_perm(n);
    for (k=lg(Fp)-1; k>=1; k--)
    {
      long f, dg = 1, el = oj, osel = 1, a = 0;
      long p  = Fp[k], e  = Fe[k], op = oj / upowuu(p,e);
      GEN  pf1 = NULL, w, wg, Be = cgetg(e+1,t_VEC);
      gel(Be,e) = cyc_pow(B, op);
      for(i=e-1; i>=1; i--) gel(Be,i) = cyc_pow(gel(Be,i+1), p);
      w = wpow(Fl_powu(s,op,deg),deg,p,e);
      wg = cgetg(e+2,t_VECSMALL);
      wg[e+1] = deg;
      for (i=e; i>=1; i--) wg[i] = ugcd(wg[i+1], w[i]);
      for (i=1; i<lg(O); i++) oX[i] = 0;
      for (f=1; f<=e; f++)
      {
        long sel, t;
        GEN Bel = gel(Be,f);
        dg *= p; el /= p;
        sel = Fl_powu(s,el,deg);
        if (DEBUGLEVEL >= 6) err_printf("GaloisConj: B=%Ps\n", Bel);
        sr  = cgcd(stpow(sel,p,deg),deg);
        if (DEBUGLEVEL >= 6)
          err_printf("GaloisConj: exp %d: s=%ld [%ld] a=%ld w=%ld wg=%ld sr=%ld\n",
              dg, sel, deg, a, w[f], wg[f+1], sr);
        for (t = 0; t < sr; t++)
          if ((a+t*w[f])%wg[f+1]==0)
          {
            long i, j, k, st;
            for (i = 1; i < lg(X); i++) X[i] = 0;
            for (i = 0; i < lg(X); i+=dg)
              for (j = 1, k = p, st = t; k <= dg; j++, k += p)
              {
                X[k+i] = (oX[j+i] + st)%deg;
                st = (t + st*osel)%deg;
              }
            pf1 = testpermutation(O, Bel, X, sel, p, sr, &td);
            if (pf1) break;
          }
        if (!pf1) { freetest(&td); avma = ltop; return gen_0; }
        for (i=1; i<lg(O); i++) oX[i] = X[i];
        osel = sel; a = (a+t*w[f])%deg;
      }
      pf = perm_mul(pf, perm_pow(pf1, el));
    }
    for (k = 1; k <= n; k++) gmael(res1, j+1,k) = gel(pf,k);
    res2[j+1] = PG2[j];
    avma = ltop2;
  }
  if (DEBUGLEVEL >= 4) err_printf("GaloisConj:Fini!\n");
  freetest(&td);
  return gerepile(ltop, lbot, res);
}

/* T: polynomial or nf, den multiple of common denominator of solutions or
 * NULL (unknown). If T is nf, and den unknown, use den = denom(nf.zk) */
static GEN
galoisconj4_main(GEN T, GEN den, long flag)
{
  pari_sp ltop = avma;
  GEN nf, G, L, M, aut;
  struct galois_analysis ga;
  struct galois_borne gb;
  long n;
  pari_timer ti;

  T = get_nfpol(T, &nf); n = degpol(T);
  if (nf)
  { if (!den) den = Q_denom(nf_get_zk(nf)); }
  else
  {
    if (n <= 0) pari_err(constpoler, "galoisinit");
    RgX_check_ZX(T, "galoisinit");
    if (!ZX_is_squarefree(T))
      pari_err(talker, "Polynomial not squarefree in galoisinit");
    if (!gequal1(gel(T,n+2)))
      pari_err(talker, "non-monic polynomial in galoisinit");
  }
  if (n == 1)
  {
    if (!flag) { G = cgetg(2, t_COL); gel(G,1) = pol_x(varn(T)); return G;}
    ga.l = 3;
    ga.deg = 1;
    den = gen_1;
  }
  else if (!galoisanalysis(T, &ga, 1)) { avma = ltop; return utoipos(ga.p); }

  if (den)
  {
    if (typ(den) != t_INT)
      pari_err(talker, "Second arg. must be integer in galoisconj4");
    den = absi(den);
  }
  gb.l = utoipos(ga.l);
  if (DEBUGLEVEL >= 1) timer_start(&ti);
  den = galoisborne(T, den, &gb, degpol(T));
  if (DEBUGLEVEL >= 1) timer_printf(&ti, "galoisborne()");
  L = rootpadicfast(T, gb.l, gb.valabs);
  if (DEBUGLEVEL >= 1) timer_printf(&ti, "rootpadicfast()");
  M = vandermondeinversemod(L, T, den, gb.ladicabs);
  if (DEBUGLEVEL >= 1) timer_printf(&ti, "vandermondeinversemod()");
  if (n == 1)
  {
    G = cgetg(3, t_VEC);
    gel(G,1) = cgetg(1, t_VEC);
    gel(G,2) = cgetg(1, t_VECSMALL);
  }
  else
    G = galoisgen(T, L, M, den, &gb, &ga);
  if (DEBUGLEVEL >= 6) err_printf("GaloisConj:%Ps\n", G);
  if (G == gen_0) { avma = ltop; return gen_0; }
  if (DEBUGLEVEL >= 1) timer_start(&ti);
  if (flag)
  {
    GEN grp = cgetg(9, t_VEC);
    gel(grp,1) = ZX_copy(T);
    gel(grp,2) = mkvec3(utoipos(ga.l), utoipos(gb.valabs), icopy(gb.ladicabs));
    gel(grp,3) = ZC_copy(L);
    gel(grp,4) = ZM_copy(M);
    gel(grp,5) = icopy(den);
    gel(grp,6) = group_elts(G,n);
    gel(grp,7) = gcopy(gel(G,1));
    gel(grp,8) = gcopy(gel(G,2)); return gerepileupto(ltop, grp);
  }
  aut = galoisgrouptopol(group_elts(G, n),L,M,den,gb.ladicsol, varn(T));
  if (DEBUGLEVEL >= 1) timer_printf(&ti, "Computation of polynomials");
  return gerepileupto(ltop, gen_sort(aut, (void*)&gcmp, &gen_cmp_RgX));
}

/* Heuristic computation of #Aut(T), pinit = first prime to be tested */
long
numberofconjugates(GEN T, long pinit)
{
  pari_sp av = avma;
  long p, c, nbtest = 0, n = degpol(T), nbmax = (n < 10)? 20: (n<<1) + 1;
  byteptr diff = diffptr;

#if 0
  c = sturm(T); c = ugcd(c, n - c); /* too costly: finite primes are cheaper */
#else
  c = n;
#endif
  p = init_primepointer(pinit, 0, &diff);
  for (; nbtest < nbmax && c > 1; avma = av)
  {
    GEN L, Tp = ZX_to_Flx(T,p);
    long i, nb;
    if (Flx_is_squarefree(Tp, p))
    { /* unramified */
      nbtest++;
      L = Flx_nbfact_by_degree(Tp, &nb, p); /* L[i] = #factors of degree i */
      if (L[n/nb] == nb) {
        if (c == n && nbtest > 10) break; /* probably Galois */
      }
      else
      {
        c = ugcd(c, L[1]);
        for (i = 2; i <= n; i++)
          if (L[i]) { c = ugcd(c, L[i]*i); if (c == 1) break; }
      }
      if (DEBUGLEVEL >= 6)
        err_printf("NumberOfConjugates [%ld]:c=%ld,p=%ld\n", nbtest,c,p);
    }
    NEXT_PRIME_VIADIFF_CHECK(p,diff);
  }
  if (DEBUGLEVEL >= 2) err_printf("NumberOfConjugates:c=%ld,p=%ld\n", c, p);
  avma = av; return c;
}
static GEN
galoisconj4(GEN nf, GEN d)
{
  pari_sp av = avma;
  GEN G, T;
  G = galoisconj4_main(nf, d, 0);
  if (typ(G) != t_INT) return G; /* Success */
  avma = av; T = get_nfpol(nf, &nf);
  G = cgetg(2, t_COL); gel(G,1) = pol_x(varn(T)); return G; /* Fail */

}

/* d multipllicative bound for the automorphism's denominators */
GEN
galoisconj(GEN nf, GEN d)
{
  pari_sp av = avma;
  GEN G = galoisconj4_main(nf, d, 0);
  if (typ(G) != t_INT) return G; /* Success */
  avma = av; return galoisconj1(nf);
}

GEN
galoisconj0(GEN nf, long flag, GEN d, long prec)
{
  switch(flag) {
    case 0: return galoisconj(nf, d);
    case 1: return galoisconj1(nf);
    case 2: return galoisconj2(nf, prec);
    case 4: return galoisconj4(nf, d);
  }
  pari_err(flagerr, "nfgaloisconj");
  return NULL; /*not reached*/
}

/******************************************************************************/
/* Isomorphism between number fields                                          */
/******************************************************************************/
long
isomborne(GEN P, GEN den, GEN p)
{
  pari_sp av = avma;
  struct galois_borne gb;
  gb.l = p; (void)galoisborne(P,den,&gb,degpol(P));
  avma = av; return gb.valsol;
}

/******************************************************************************/
/* Galois theory related algorithms                                           */
/******************************************************************************/
GEN
checkgal(GEN gal)
{
  if (typ(gal) == t_POL) pari_err(talker, "please apply galoisinit first");
  if (typ(gal) != t_VEC || lg(gal) != 9)
    pari_err(talker, "Not a Galois group in a Galois related function");
  return gal;
}

GEN
galoisinit(GEN nf, GEN den)
{
  GEN G = galoisconj4_main(nf, den, 1);
  return (typ(G) == t_INT)? gen_0: G;
}

static GEN
galoispermtopol_i(GEN gal, GEN perm, GEN mod, GEN mod2)
{
  long t = typ(perm), i;
  GEN v;
  switch (t)
  {
  case t_VECSMALL:
  {
    long v = varn(gel(gal,1));
    return permtopol(perm, gal_get_roots(gal), gal_get_invvdm(gal),
                           gal_get_den(gal), mod, mod2, v);
  }
  case t_VEC: case t_COL: case t_MAT:
    v = cgetg(lg(perm), t);
    if (DEBUGLEVEL>=4) err_printf("GaloisPermToPol:");
    for (i = 1; i < lg(v); i++)
    {
      gel(v,i) = galoispermtopol_i(gal, gel(perm,i), mod, mod2);
      if (DEBUGLEVEL>=4) err_printf("%ld ",i);
    }
    if (DEBUGLEVEL>=4) err_printf("\n");
    return v;
  }
  pari_err(typeer, "galoispermtopol");
  return NULL; /* not reached */
}

GEN
galoispermtopol(GEN gal, GEN perm)
{
  pari_sp av = avma;
  GEN mod, mod2;
  gal = checkgal(gal);
  mod = gal_get_mod(gal);
  mod2 = shifti(mod,-1);
  return gerepilecopy(av, galoispermtopol_i(gal, perm, mod, mod2));
}

GEN
galoiscosets(GEN O, GEN perm)
{
  long i, j, k, u, f, l = lg(O);
  GEN RC, C = cgetg(l,t_VECSMALL), o = gel(O,1);
  pari_sp av = avma;
  f = lg(o); u = o[1]; RC = const_vecsmall(lg(perm)-1, 0);
  for(i=1,j=1; j<l; i++)
  {
    GEN p = gel(perm,i);
    if (RC[ p[u] ]) continue;
    for(k=1; k<f; k++) RC[ p[ o[k] ] ] = 1;
    C[j++] = i;
  }
  avma = av; return C;
}

static GEN
fixedfieldfactor(GEN L, GEN O, GEN perm, GEN M, GEN den, GEN mod, GEN mod2,
                 long x,long y)
{
  pari_sp ltop = avma;
  long i, j, k, l = lg(O), lo = lg(O[1]);
  GEN V, res, cosets = galoiscosets(O,perm), F = cgetg(lo+1,t_COL);

  gel(F, lo) = gen_1;
  if (DEBUGLEVEL>=4) err_printf("GaloisFixedField:cosets=%Ps \n",cosets);
  if (DEBUGLEVEL>=6) err_printf("GaloisFixedField:den=%Ps mod=%Ps \n",den,mod);
  V = cgetg(l,t_COL); res = cgetg(l,t_VEC);
  for (i = 1; i < l; i++)
  {
    pari_sp av = avma;
    GEN G = cgetg(l,t_VEC), Lp = vecpermute(L, gel(perm, cosets[i]));
    for (k = 1; k < l; k++)
      gel(G,k) = FpV_roots_to_pol(vecpermute(Lp, gel(O,k)), mod, x);
    for (j = 1; j < lo; j++)
    {
      for(k = 1; k < l; k++) V[k] = mael(G,k,j+1);
      gel(F,j) = vectopol(V, M, den, mod, mod2, y);
    }
    gel(res,i) = gerepileupto(av,gtopolyrev(F,x));
  }
  return gerepileupto(ltop,res);
}

static void
chk_perm(GEN perm, long n)
{
  if (typ(perm) != t_VECSMALL || lg(perm)!=n+1)
    pari_err(typeer, "galoisfixedfield");
}

static int
is_group(GEN g)
{
  return typ(g)==t_VEC && lg(g)==3 && typ(g[1])==t_VEC
      && typ(g[2])==t_VECSMALL;
}

GEN
galoisfixedfield(GEN gal, GEN perm, long flag, long y)
{
  pari_sp lbot, ltop = avma;
  GEN T, L, P, S, PL, O, res, mod, mod2;
  long x, n, i;
  if (flag<0 || flag>2) pari_err(flagerr, "galoisfixedfield");
  gal = checkgal(gal); T = gal_get_pol(gal);
  x = varn(T);
  L = gal_get_roots(gal); n = lg(L)-1;
  mod = gal_get_mod(gal);
  if (typ(perm) == t_VEC)
  {
    if (is_group(perm)) perm = gel(perm, 1);
    for (i = 1; i < lg(perm); i++) chk_perm(gel(perm,i), n);
    O = vecperm_orbits(perm, n);
  }
  else
  {
    chk_perm(perm, n);
    O = perm_cycles(perm);
  }

  {
    GEN OL= fixedfieldorbits(O,L);
    GEN V = fixedfieldsympol(OL, mod, gal_get_p(gal), NULL, x);
    PL= gel(V,2);
    P = gel(V,3);
  }
  if (flag==1) return gerepileupto(ltop,P);
  mod2 = shifti(mod,-1);
  S = fixedfieldinclusion(O, PL);
  S = vectopol(S, gal_get_invvdm(gal), gal_get_den(gal), mod, mod2, x);
  if (flag==0)
  { lbot = avma; res = cgetg(3, t_VEC); }
  else
  {
    GEN PM, Pden;
    struct galois_borne Pgb;
    long val = itos(gal_get_e(gal));
    Pgb.l = gal_get_p(gal);
    Pden = galoisborne(P, NULL, &Pgb, degpol(T)/degpol(P));
    if (Pgb.valabs > val)
    {
      if (DEBUGLEVEL>=4)
        err_printf("GaloisConj:increase p-adic prec by %ld.\n", Pgb.valabs-val);
      PL = ZpX_liftroots(P, PL, Pgb.l, Pgb.valabs);
      L  = ZpX_liftroots(T, L, Pgb.l, Pgb.valabs);
      mod = Pgb.ladicabs; mod2 = shifti(mod,-1);
    }
    PM = vandermondeinversemod(PL, P, Pden, mod);
    if (y < 0) y = fetch_user_var("y");
    if (y <= x)
      pari_err(talker,"variable priority too high in galoisfixedfield");
    lbot = avma; res = cgetg(4, t_VEC);
    gel(res,3) = fixedfieldfactor(L,O,gal_get_group(gal), PM,Pden,mod,mod2,x,y);
  }
  gel(res,1) = gcopy(P);
  gel(res,2) = gmodulo(S, T);
  return gerepile(ltop, lbot, res);
}

/* gal a galois group output the underlying wss group */
GEN
galois_group(GEN gal) { return mkvec2(gal_get_gen(gal), gal_get_orders(gal)); }

GEN
checkgroup(GEN g, GEN *S)
{
  if (is_group(g)) { *S = NULL; return g; }
  g  = checkgal(g);
  *S = gal_get_group(g); return galois_group(g);
}

GEN
galoisisabelian(GEN gal, long flag)
{
  pari_sp av = avma;
  GEN S, G = checkgroup(gal,&S);
  if (!group_isabelian(G)) { avma=av; return gen_0; }
  switch(flag)
  {
    case 0: return gerepileupto(av, group_abelianHNF(G,S));
    case 1: avma=av; return gen_1;
    case 2: return gerepileupto(av, group_abelianSNF(G,S));
    default: pari_err(flagerr,"galoisisabelian");
  }
  return NULL; /* not reached */
}

long
galoisisnormal(GEN gal, GEN sub)
{
  pari_sp av = avma;
  GEN S, G = checkgroup(gal, &S), H = checkgroup(sub, &S);
  long res = group_subgroup_isnormal(G, H);
  avma = av;
  return res;
}

GEN
galoissubgroups(GEN gal)
{
  pari_sp av = avma;
  GEN S, G = checkgroup(gal,&S);
  return gerepileupto(av, group_subgroups(G));
}

GEN
galoissubfields(GEN G, long flag, long v)
{
  pari_sp av = avma;
  GEN L = galoissubgroups(G);
  long i, l = lg(L);
  GEN S = cgetg(l, t_VEC);
  for (i = 1; i < l; ++i) gel(S,i) = galoisfixedfield(G, gmael(L,i,1), flag, v);
  return gerepileupto(av, S);
}

GEN
galoisexport(GEN gal, long format)
{
  pari_sp av = avma;
  GEN S, G = checkgroup(gal,&S);
  return gerepileupto(av, group_export(G,format));
}

GEN
galoisidentify(GEN gal)
{
  pari_sp av = avma;
  GEN S, G = checkgroup(gal,&S);
  long idx = group_ident(G,S), card = group_order(G);
  avma = av; return mkvec2s(card, idx);
}