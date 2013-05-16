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
/*                       BASIC NF OPERATIONS                       */
/*                          (continued 2)                          */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

static GEN
_checkrnfeq(GEN x)
{
  if (typ(x) == t_VEC)
    switch(lg(x))
    {
      case 13: /* checkrnf(x); */ return gel(x,11);
      case  4: return x;
    }
  return NULL;
}

GEN
checkrnfeq(GEN x)
{
  x = _checkrnfeq(x);
  if (!x) pari_err(talker,"please apply rnfequation(,,1)");
  return x;
}

GEN
eltreltoabs(GEN rnfeq, GEN x)
{
  long i, k, va;
  pari_sp av = avma;
  GEN polabs, teta, alpha, s;

  rnfeq = checkrnfeq(rnfeq);
  polabs= gel(rnfeq,1);
  alpha = lift_intern(gel(rnfeq,2));
  k     = itos(gel(rnfeq,3));

  va = varn(polabs);
  if (varncmp(gvar(x), va) > 0) x = scalarpol(x,va);
  /* Mod(X - k alpha, polabs(X)), alpha root of the polynomial defining base */
  teta = gadd(pol_x(va), gmulsg(-k,alpha));
  s = gen_0;
  for (i=lg(x)-1; i>1; i--)
  {
    GEN c = gel(x,i);
    long tc = typ(c);
    switch(tc)
    {
      case t_POLMOD: c = gel(c,2);
        if (typ(c) != t_POL) break;
        c = RgX_RgXQ_eval(c, alpha, polabs); break;
      case t_POL:
        c = RgX_RgXQ_eval(c, alpha, polabs); break;
      default:
        if (!is_const_t(tc)) pari_err(talker, "incorrect data in eltreltoabs");
    }
    s = RgX_rem(gadd(c, gmul(teta,s)), polabs);
  }
  return gerepileupto(av, s);
}

/* x a t_VEC of rnf elements in 'alg' form */
static GEN
modulereltoabs(GEN rnf, GEN x)
{
  GEN W = gel(x,1), I = gel(x,2), nf = gel(rnf,10), rnfeq = gel(rnf,11);
  GEN M, basnf, cobasnf, T = nf_get_pol(nf), polabs = gel(rnfeq,1);
  long i, j, k, n = lg(W)-1, m = degpol(T);

  M = cgetg(n*m+1, t_VEC);
  basnf = lift_intern( gsubst(nf_get_zk(nf), varn(T), gel(rnfeq,2)) );
  basnf = Q_primitive_part(basnf, &cobasnf); /* remove denom. --> faster */
  for (k=i=1; i<=n; i++)
  {
    GEN c0, cid, w = gel(W,i), id = gel(I,i);

    if (lg(id) == 1) continue; /* must be a t_MAT */
    id = Q_primitive_part(id, &cid);
    w = Q_primitive_part(eltreltoabs(rnfeq,w), &c0);
    c0 = mul_content(c0, mul_content(cid,cobasnf));
    if (typ(id) == t_INT)
      for (j=1; j<=m; j++)
      {
        GEN z = RgX_rem(gmul(w, gel(basnf,j)), polabs);
        if (c0) z = RgX_Rg_mul(z, c0);
        gel(M,k++) = z;
      }
    else
      for (j=1; j<=m; j++)
      {
        GEN c, z = Q_primitive_part(gmul(basnf,gel(id,j)), &c);
        z = RgX_rem(gmul(w, z), polabs);
        c = mul_content(c, c0); if (c) z = RgX_Rg_mul(z, c);
        gel(M,k++) = z;
      }
  }
  setlg(M, k); return M;
}

static GEN
makenfabs(GEN rnf)
{
  GEN M, d, rnfeq, pol, nf, NF = zerovec(9);
  long n;

  rnfeq = gel(rnf,11); pol = gel(rnfeq,1);
  nf = gel(rnf,10);

  M = modulereltoabs(rnf, gel(rnf,7));
  n = degpol(pol);
  M = RgXV_to_RgM(Q_remove_denom(M, &d), n);
  if (d) M = RgM_Rg_div(ZM_hnfmodall(M, d, hnf_MODID|hnf_CENTER), d);
  else   M = matid(n);

  gel(NF,1) = pol;
  gel(NF,3) = mulii(powiu(nf_get_disc(nf), rnf_get_degree(rnf)),
                    idealnorm(nf, gel(rnf,3)));
  nf_set_multable(NF, M, NULL);
  /* possibly wrong, but correct prime divisors [for idealprimedec] */
  gel(NF,4) = Q_denom(gel(NF,7));
  return NF;
}

static GEN
makenorms(GEN rnf)
{
  GEN f = gel(rnf,4);
  return typ(f) == t_INT? gen_1: RgM_det_triangular(f);
}

#define NFABS 1
#define NORMS 2
GEN
check_and_build_nfabs(GEN rnf) {
  return check_and_build_obj(rnf, NFABS, &makenfabs);
}
GEN
check_and_build_norms(GEN rnf) {
  return check_and_build_obj(rnf, NORMS, &makenorms);
}

GEN
rnfinit(GEN nf, GEN pol)
{
  pari_sp av = avma;
  GEN rnf, bas, D,d,f, B;

  nf = checknf(nf);
  bas = rnfallbase(nf,&pol, &D,&d, &f);
  B = matbasistoalg(nf,gel(bas,1));
  gel(bas,1) = lift_if_rational( RgM_to_RgXV(B,varn(pol)) );

  rnf = cgetg(13, t_VEC);
  gel(rnf,1) = pol;
  gel(rnf,2) = cgetg(1, t_VEC); /* dummy */
  gel(rnf,3) = mkvec2(D, d);
  gel(rnf,4) = f;
  gel(rnf,5) = cgetg(1, t_VEC); /* dummy */
  gel(rnf,6) = cgetg(1, t_VEC); /* dummy */
  gel(rnf,7) = bas;
  gel(rnf,8) = lift_if_rational( RgM_inv(B) );
  gel(rnf,9) = cgetg(1,t_VEC); /* dummy */
  gel(rnf,10) = nf;
  gel(rnf,11) = rnfequation2(nf,pol);
  gel(rnf,12) = gen_0;
  return gerepilecopy(av, rnf);
}

GEN
rnfelementreltoabs(GEN rnf,GEN x)
{
  long i, lx;
  GEN z;

  switch(typ(x))
  {
    case t_VEC: case t_COL: case t_MAT:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(z,i) = rnfelementreltoabs(rnf, gel(x,i));
      return z;

    case t_POLMOD: x = gel(x,2); /* fall through */
    case t_POL: return eltreltoabs(rnf, x);
    default: return gcopy(x);
  }
}

/* Let T,pol t_POL. T(y) defines base field, pol(x) defines rnf over T
 * Return Mod(x + k y, pol) */
GEN
get_theta_abstorel(GEN T, GEN pol, GEN k)
{
  GEN u, ky = signe(k)? deg1pol_shallow(k, gen_0, varn(T)): gen_0;
  u = deg1pol_shallow(mkpolmod(gen_1, T), mkpolmod(ky, T), varn(pol));
  if (degpol(pol) == 1) u = RgX_rem(u,pol);
  return mkpolmod(u, pol);
}
GEN
eltabstorel(GEN x, GEN T, GEN pol, GEN k)
{
  return poleval(x, get_theta_abstorel(T,pol,k));
}

GEN
rnfelementabstorel(GEN rnf,GEN x)
{
  pari_sp av = avma;
  long i, lx;
  GEN z;

  checkrnf(rnf);
  switch(typ(x))
  {
    case t_VEC: case t_COL: case t_MAT:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(z,i) = rnfelementabstorel(rnf,gel(x,i));
      return z;

    case t_POLMOD:
      x = gel(x,2);
      if (typ(x) != t_POL) return gcopy(x);
      /* fall through */
    case t_POL:
    {
      GEN k, T, pol, rnfeq = gel(rnf,11), nf = gel(rnf,10);
      k = gel(rnfeq,3);
      T = nf_get_pol(nf);
      pol = gel(rnf,1);
      return gerepileupto(av, eltabstorel(x, T, pol, k));
    }

    default: return gcopy(x);
  }
}

/* x t_POLMOD or t_POL or vector of such objects */
GEN
rnfelementup(GEN rnf,GEN x)
{
  long i, lx;
  GEN z;

  checkrnf(rnf);
  switch(typ(x))
  {
    case t_VEC: case t_COL: case t_MAT:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(z,i) = rnfelementup(rnf,gel(x,i));
      return z;

    case t_POLMOD: x = gel(x,2); /* fall through */
    case t_POL:
      return poleval(x, gmael(rnf,11,2));

    default: return gcopy(x);
  }
}

/* x t_POLMOD or t_POL or vector of such objects */
GEN
rnfelementdown(GEN rnf,GEN x)
{
  pari_sp av;
  long i, lx;
  GEN z;

  checkrnf(rnf);
  switch(typ(x))
  {
    case t_VEC: case t_COL: case t_MAT:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(z,i) = rnfelementdown(rnf,gel(x,i));
      return z;

    case t_POLMOD: x = gel(x,2); /* fall through */
    case t_POL:
      if (gequal0(x)) return gen_0;
      av = avma; z = rnfelementabstorel(rnf,x);
      if (typ(z)==t_POLMOD && varn(z[1])==varn(rnf[1])) z = gel(z,2);
      if (varncmp(gvar(z), varn(rnf[1])) <= 0)
      {
        lx = lg(z);
        if (lx == 2) { avma = av; return gen_0; }
        if (lx > 3)
          pari_err(talker,"element is not in the base field in rnfelementdown");
        z = gel(z,2);
      }
      return gerepilecopy(av, z);

    default: return gcopy(x);
  }
}

/* x est exprime sur la base relative */
static GEN
rnfprincipaltohermite(GEN rnf,GEN x)
{
  pari_sp av = avma;
  GEN bas = gel(rnf,7), nf = gel(rnf,10);

  x = rnfbasistoalg(rnf,x);
  x = rnfalgtobasis(rnf, gmul(x, gmodulo(gel(bas,1), gel(rnf,1))));
  settyp(x, t_MAT);
  return gerepileupto(av, nfhnf(nf, mkvec2(x, gel(bas,2))));
}

GEN
rnfidealhermite(GEN rnf, GEN x)
{
  GEN z, nf, bas;

  checkrnf(rnf); nf = gel(rnf,10);
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      bas = gel(rnf,7); z = cgetg(3,t_VEC);
      gel(z,1) = matid(rnf_get_degree(rnf));
      gel(z,2) = gmul(x, gel(bas,2)); return z;

    case t_VEC:
      if (lg(x) == 3 && typ(x[1]) == t_MAT) return nfhnf(nf, x);
      return rnfidealabstorel(rnf, x);

    case t_POLMOD: case t_POL: case t_COL:
      return rnfprincipaltohermite(rnf,x);
  }
  pari_err(typeer,"rnfidealhermite");
  return NULL; /* not reached */
}

GEN
prodid(GEN nf, GEN I)
{
  long i, l = lg(I);
  GEN z;
  if (l == 1) return matid(nf_get_degree(nf));
  z = gel(I,1);
  for (i=2; i<l; i++) z = idealmul(nf, z, gel(I,i));
  return z;
}

static GEN
prodidnorm(GEN nf, GEN I)
{
  long i, l = lg(I);
  GEN z;
  if (l == 1) return gen_1;
  z = idealnorm(nf, gel(I,1));
  for (i=2; i<l; i++) z = gmul(z, idealnorm(nf, gel(I,i)));
  return z;
}

GEN
rnfidealnormrel(GEN rnf, GEN id)
{
  pari_sp av = avma;
  GEN z, nf;
  checkrnf(rnf); nf = gel(rnf,10);
  if (rnf_get_degree(rnf) == 1) return matid(nf_get_degree(nf));

  z = prodid(nf, gel(rnfidealhermite(rnf,id),2));
  return gerepileupto(av, idealmul(nf,z, gel(rnf,4)));
}

GEN
rnfidealnormabs(GEN rnf, GEN id)
{
  pari_sp av = avma;
  GEN z, nf;

  checkrnf(rnf);
  if (rnf_get_degree(rnf) == 1) return gen_1;
  nf = gel(rnf,10);
  z = prodidnorm(nf, gel(rnfidealhermite(rnf,id),2));
  return gerepileupto(av, gmul(z, check_and_build_norms(rnf)));
}

GEN
rnfidealreltoabs(GEN rnf,GEN x)
{
  pari_sp av = avma;
  long i, l;
  GEN w;

  x = rnfidealhermite(rnf,x);
  w = gel(x,1); l = lg(w); settyp(w, t_VEC);
  for (i=1; i<l; i++) gel(w,i) = lift_intern( rnfbasistoalg(rnf, gel(w,i)) );
  return gerepilecopy(av, modulereltoabs(rnf, x));
}

GEN
rnfidealabstorel(GEN rnf, GEN x)
{
  long N, m, j;
  pari_sp av = avma;
  GEN nf, A, I, z, invbas;

  checkrnf(rnf); nf = gel(rnf,10); invbas = gel(rnf,8);
  m = nf_get_degree(nf);
  N = m * rnf_get_degree(rnf);
  if (lg(x)-1 != N) pari_err(typeer, "rnfidealabstorel");
  if (typ(x) != t_VEC) pari_err(typeer,"rnfidealabstorel");
  A = cgetg(N+1,t_MAT);
  I = cgetg(N+1,t_VEC); z = mkvec2(A,I);
  for (j=1; j<=N; j++)
  {
    GEN t = lift_intern( rnfelementabstorel(rnf, gel(x,j)) );
    gel(A,j) = mulmat_pol(invbas, t);
    gel(I,j) = gen_1;
  }
  return gerepileupto(av, nfhnf(nf,z));
}

GEN
rnfidealdown(GEN rnf,GEN x)
{
  pari_sp av = avma; x = rnfidealhermite(rnf,x);
  return gerepilecopy(av, gmael(x,2,1));
}

/* lift ideal x to the relative extension, returns a Z-basis */
GEN
rnfidealup(GEN rnf,GEN x)
{
  pari_sp av = avma;
  long i, n;
  GEN nf, bas, bas2, I;

  checkrnf(rnf); nf = gel(rnf,10);
  n = rnf_get_degree(rnf);
  bas = gel(rnf,7); bas2 = gel(bas,2);

  (void)idealtyp(&x, &I); /* I is junk */
  I = cgetg(n+1,t_VEC);
  for (i=1; i<=n; i++) gel(I,i) = idealmul(nf,x,gel(bas2,i));
  return gerepilecopy(av, modulereltoabs(rnf, mkvec2(gel(bas,1), I)));
}

/* x a relative HNF ---> vector of 2 generators (relative polymods) */
GEN
rnfidealtwoelement(GEN rnf, GEN x)
{
  pari_sp av = avma;
  GEN y, z, NF;

  checkrnf(rnf);
  NF = check_and_build_nfabs(rnf);
  y = rnfidealreltoabs(rnf,x);
  y = matalgtobasis(NF, y); settyp(y, t_MAT);
  y = idealtwoelt(NF, ZM_hnf(y));
  z = rnfelementabstorel(rnf, gmul(gel(NF,7), gel(y,2)));
  return gerepilecopy(av, mkvec2(gel(y,1), z));
}

GEN
rnfidealmul(GEN rnf,GEN x,GEN y) /* x et y sous HNF relative uniquement */
{
  pari_sp av = avma;
  GEN z, nf, x1, x2, p1, p2;

  z = rnfidealtwoelement(rnf,y);
  nf = gel(rnf,10);
  x = rnfidealhermite(rnf,x);
  x1 = gmodulo(gmul(gmael(rnf,7,1), matbasistoalg(nf,gel(x,1))),gel(rnf,1));
  x2 = gel(x,2);
  p1 = gmul(gel(z,1), gel(x,1));
  p2 = rnfalgtobasis(rnf, gmul(gel(z,2), x1)); settyp(p2, t_MAT);
  z = mkvec2(shallowconcat(p1, p2), shallowconcat(x2, x2));
  return gerepileupto(av, nfhnf(nf,z));
}

int
nfissquarefree(GEN nf, GEN x)
{
  pari_sp av = avma;
  GEN g, y = RgX_deriv(x);
  if (RgX_is_rational(x))
    g = QX_gcd(x, y);
  else
    g = nfgcd(x, y, nf, NULL);
  avma = av; return (degpol(g) == 0);
}

GEN
rnfequationall(GEN A, GEN B, long *pk, GEN *pLPRS)
{
  long lA, lB;
  GEN nf, C;

  A = get_nfpol(A, &nf); lA = lg(A);
  if (!nf) {
    if (lA<=3) pari_err(constpoler,"rnfequation");
    RgX_check_ZX(A,"rnfequation");
  }
  B = rnf_fix_pol(A,B,1); lB = lg(B);
  if (lB<=3) pari_err(constpoler,"rnfequation");
  B = Q_primpart(B);
  RgX_check_ZXY(B,"rnfequation");

  if (!nfissquarefree(A,B))
    pari_err(talker,"inseparable relative equation in rnfequation");

  *pk = 0; C = ZX_ZXY_resultant_all(A, B, pk, pLPRS);
  if (gsigne(leading_term(C)) < 0) C = RgX_neg(C);
  *pk = -*pk; return Q_primpart(C);
}

GEN
rnfequation0(GEN A, GEN B, long flall)
{
  pari_sp av = avma;
  GEN LPRS, C;
  long k;

  C = rnfequationall(A, B, &k, flall? &LPRS: NULL);
  if (flall)
  { /* a,b,c root of A,B,C = compositum, c = b + k a */
    GEN a, mH0 = RgX_neg(gel(LPRS,1)), H1 = gel(LPRS,2);
    a = RgXQ_mul(mH0, QXQ_inv(H1, C), C);
    C = mkvec3(C, mkpolmod(a, C), stoi(k));
  }
  return gerepilecopy(av, C);
}
GEN
rnfequation(GEN nf, GEN pol) { return rnfequation0(nf,pol,0); }
GEN
rnfequation2(GEN nf, GEN pol) { return rnfequation0(nf,pol,1); }

static GEN
nftau(long r1, GEN x)
{
  long i, l = lg(x);
  GEN s = r1? gel(x,1): gmul2n(real_i(gel(x,1)),1);
  for (i=2; i<=r1; i++) s = gadd(s, gel(x,i));
  for (   ; i < l; i++) s = gadd(s, gmul2n(real_i(gel(x,i)),1));
  return s;
}

static GEN
initmat(long l)
{
  GEN x = cgetg(l, t_MAT);
  long i;
  for (i = 1; i < l; i++) gel(x,i) = cgetg(l, t_COL);
  return x;
}

static GEN
nftocomplex(GEN nf, GEN x)
{
  GEN M = nf_get_M(nf);
  x = nf_to_scalar_or_basis(nf,x);
  if (typ(x) != t_COL) return const_col(lg(M[1])-1, x);
  return RgM_RgC_mul(M, x);
}
/* assume x a square t_MAT, return a t_VEC of embeddings of its columns */
static GEN
mattocomplex(GEN nf, GEN x)
{
  long i,j, l = lg(x);
  GEN v = cgetg(l, t_VEC);
  for (j=1; j<l; j++)
  {
    GEN c = gel(x,j), b = cgetg(l, t_MAT);
    for (i=1; i<l; i++) gel(b,i) = nftocomplex(nf, gel(c,i));
    b = shallowtrans(b); settyp(b, t_COL);
    gel(v,j) = b;
  }
  return v;
}

static GEN
nf_all_roots(GEN nf, GEN x, long prec)
{
  long i, j, l = lg(x), ru = lg(nf[6]);
  GEN y = cgetg(l, t_POL), v, z;

  x = RgX_to_nfX(nf, x);
  y[1] = x[1];
  for (i=2; i<l; i++) gel(y,i) = nftocomplex(nf, gel(x,i));
  i = gprecision(y); if (i && i <= 3) return NULL;

  v = cgetg(ru, t_VEC);
  z = cgetg(l, t_POL); z[1] = x[1];
  for (i=1; i<ru; i++)
  {
    for (j = 2; j < l; j++) gel(z,j) = gmael(y,j,i);
    gel(v,i) = cleanroots(z, prec);
  }
  return v;
}

static GEN
rnfscal(GEN m, GEN x, GEN y)
{
  long i, l = lg(m);
  GEN z = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
    gel(z,i) = gmul(gconj(shallowtrans(gel(x,i))), gmul(gel(m,i), gel(y,i)));
  return z;
}

/* x ideal in HNF */
static GEN
findmin(GEN nf, GEN x, GEN muf)
{
  pari_sp av = avma;
  long e;
  GEN cx, y, m, M = nf_get_M(nf);

  x = Q_primitive_part(x, &cx);
  if (gequal1(gcoeff(x,1,1))) y = M;
  else
  {
    GEN G = nf_get_G(nf);
    m = lllfp(RgM_mul(G,x), 0.75, 0);
    if (typ(m) != t_MAT)
    {
      x = ZM_lll(x, 0.75, LLL_INPLACE);
      m = lllfp(RgM_mul(G,x), 0.75, 0);
      if (typ(m) != t_MAT) pari_err(precer,"rnflllgram");
    }
    x = ZM_mul(x, m);
    y = RgM_mul(M, x);
  }
  m = RgM_solve_realimag(y, muf);
  if (!m) return NULL; /* precision problem */
  if (cx) m = RgC_Rg_div(m, cx);
  m = grndtoi(m, &e);
  if (e >= 0) return NULL; /* precision problem */
  m = ZM_ZC_mul(x, m);
  if (cx) m = RgC_Rg_mul(m, cx);
  return gerepileupto(av, m);
}

static int
RED(long k, long l, GEN U, GEN mu, GEN MC, GEN nf, GEN I, GEN *Ik_inv)
{
  GEN x, xc, ideal;
  long i;

  if (!*Ik_inv) *Ik_inv = idealinv(nf, gel(I,k));
  ideal = idealmul(nf,gel(I,l), *Ik_inv);
  x = findmin(nf, ideal, gcoeff(mu,k,l));
  if (!x) return 0;
  if (gequal0(x)) return 1;

  xc = nftocomplex(nf,x);
  gel(MC,k) = gsub(gel(MC,k), vecmul(xc,gel(MC,l)));
  gel(U,k) = gsub(gel(U,k), gmul(coltoalg(nf,x), gel(U,l)));
  gcoeff(mu,k,l) = gsub(gcoeff(mu,k,l), xc);
  for (i=1; i<l; i++)
    gcoeff(mu,k,i) = gsub(gcoeff(mu,k,i), vecmul(xc,gcoeff(mu,l,i)));
  return 1;
}

static int
check_0(GEN B)
{
  long i, l = lg(B);
  for (i = 1; i < l; i++)
    if (gsigne(gel(B,i)) <= 0) return 1;
  return 0;
}

static int
do_SWAP(GEN I, GEN MC, GEN MCS, GEN h, GEN mu, GEN B, long kmax, long k,
        const long alpha, long r1)
{
  GEN p1, p2, muf, mufc, Bf, temp;
  long i, j;

  p1 = nftau(r1, gadd(gel(B,k),
                      gmul(gnorml2(gcoeff(mu,k,k-1)), gel(B,k-1))));
  p2 = nftau(r1, gel(B,k-1));
  if (gcmp(gmulsg(alpha,p1), gmulsg(alpha-1,p2)) > 0) return 0;

  swap(gel(MC,k-1),gel(MC,k));
  swap(gel(h,k-1), gel(h,k));
  swap(gel(I,k-1), gel(I,k));
  for (j=1; j<=k-2; j++) swap(gcoeff(mu,k-1,j),gcoeff(mu,k,j));
  muf = gcoeff(mu,k,k-1);
  mufc = gconj(muf);
  Bf = gadd(gel(B,k), vecmul(real_i(vecmul(muf,mufc)), gel(B,k-1)));
  if (check_0(Bf)) return 1; /* precision problem */

  p1 = vecdiv(gel(B,k-1),Bf);
  gcoeff(mu,k,k-1) = vecmul(mufc,p1);
  temp = gel(MCS,k-1);
  gel(MCS,k-1) = gadd(gel(MCS,k), vecmul(muf,gel(MCS,k-1)));
  gel(MCS,k) = gsub(vecmul(vecdiv(gel(B,k),Bf), temp),
                    vecmul(gcoeff(mu,k,k-1), gel(MCS,k)));
  gel(B,k) = vecmul(gel(B,k),p1);
  gel(B,k-1) = Bf;
  for (i=k+1; i<=kmax; i++)
  {
    temp = gcoeff(mu,i,k);
    gcoeff(mu,i,k) = gsub(gcoeff(mu,i,k-1), vecmul(muf, gcoeff(mu,i,k)));
    gcoeff(mu,i,k-1) = gadd(temp, vecmul(gcoeff(mu,k,k-1),gcoeff(mu,i,k)));
  }
  return 1;
}

static GEN
rel_T2(GEN nf, GEN pol, long lx, long prec)
{
  long ru, i, j, k, l;
  GEN T2, s, unro, roorder, powreorder;

  roorder = nf_all_roots(nf, pol, prec);
  if (!roorder) return NULL;
  ru = lg(roorder);
  unro = cgetg(lx,t_COL); for (i=1; i<lx; i++) gel(unro,i) = gen_1;
  powreorder = cgetg(lx,t_MAT); gel(powreorder,1) = unro;
  T2 = cgetg(ru, t_VEC);
  for (i = 1; i < ru; i++)
  {
    GEN ro = gel(roorder,i);
    GEN m = initmat(lx);
    for (k=2; k<lx; k++)
    {
      GEN c = cgetg(lx, t_COL); gel(powreorder,k) = c;
      for (j=1; j < lx; j++)
        gel(c,j) = gmul(gel(ro,j), gmael(powreorder,k-1,j));
    }
    for (l = 1; l < lx; l++)
      for (k = 1; k <= l; k++)
      {
        s = gen_0;
        for (j = 1; j < lx; j++)
          s = gadd(s, gmul(gconj(gmael(powreorder,k,j)),
                                 gmael(powreorder,l,j)));
        if (l == k)
          gcoeff(m, l, l) = real_i(s);
        else
        {
          gcoeff(m, k, l) = s;
          gcoeff(m, l, k) = gconj(s);
        }
      }
    gel(T2,i) = m;
  }
  return T2;
}

/* given a base field nf (e.g main variable y), a polynomial pol with
 * coefficients in nf    (e.g main variable x), and an order as output
 * by rnfpseudobasis, outputs a reduced order. */
GEN
rnflllgram(GEN nf, GEN pol, GEN order,long prec)
{
  pari_sp av = avma, lim = stack_lim(av,2);
  long j, k, l, kmax, r1, lx, count = 0;
  GEN M, I, h, H, mth, MC, MPOL, MCS, B, mu;
  const long alpha = 10, MAX_COUNT = 4;

  nf = checknf(nf); r1 = nf_get_r1(nf);
  check_ZKmodule(order, "rnflllgram");
  M = gel(order,1);
  I = gel(order,2); lx = lg(I);
  if (lx < 3) return gcopy(order);
  if (lx-1 != degpol(pol)) pari_err(consister,"rnflllgram");
  I = leafcopy(I);
  H = NULL;
  MPOL = matbasistoalg(nf, M);
  MCS = matid(lx-1); /* dummy for gerepile */
PRECNF:
  if (count == MAX_COUNT)
  {
    prec = (prec<<1)-2; count = 0;
    if (DEBUGLEVEL) pari_warn(warnprec,"rnflllgram",prec);
    nf = nfnewprec_shallow(nf,prec);
  }
  mth = rel_T2(nf, pol, lx, prec);
  if (!mth) { count = MAX_COUNT; goto PRECNF; }
  h = NULL;
PRECPB:
  if (h)
  { /* precision problem, recompute. If no progress, increase nf precision */
    if (++count == MAX_COUNT || RgM_isidentity(h)) {count = MAX_COUNT; goto PRECNF;}
    H = H? gmul(H, h): h;
    MPOL = gmul(MPOL, h);
  }
  h = matid(lx-1);
  MC = mattocomplex(nf, MPOL);
  mu = cgetg(lx,t_MAT);
  B  = cgetg(lx,t_COL);
  for (j=1; j<lx; j++)
  {
    gel(mu,j) = zerocol(lx - 1);
    gel(B,j) = gen_0;
  }
  if (DEBUGLEVEL) err_printf("k = ");
  gel(B,1) = real_i(rnfscal(mth,gel(MC,1),gel(MC,1)));
  MCS[1] = MC[1];
  kmax = 1; k = 2;
  do
  {
    GEN Ik_inv = NULL;
    if (DEBUGLEVEL) err_printf("%ld ",k);
    if (k > kmax)
    { /* Incremental Gram-Schmidt */
      kmax = k; MCS[k] = MC[k];
      for (j=1; j<k; j++)
      {
        gcoeff(mu,k,j) = vecdiv(rnfscal(mth,gel(MCS,j),gel(MC,k)),
                                gel(B,j));
        gel(MCS,k) = gsub(gel(MCS,k), vecmul(gcoeff(mu,k,j),gel(MCS,j)));
      }
      gel(B,k) = real_i(rnfscal(mth,gel(MCS,k),gel(MCS,k)));
      if (check_0(gel(B,k))) goto PRECPB;
    }
    if (!RED(k, k-1, h, mu, MC, nf, I, &Ik_inv)) goto PRECPB;
    if (do_SWAP(I,MC,MCS,h,mu,B,kmax,k,alpha, r1))
    {
      if (!B[k]) goto PRECPB;
      if (k > 2) k--;
    }
    else
    {
      for (l=k-2; l; l--)
        if (!RED(k, l, h, mu, MC, nf, I, &Ik_inv)) goto PRECPB;
      k++;
    }
    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"rnflllgram");
      gerepileall(av, H?10:9, &nf,&mth,&h,&MPOL,&B,&MC,&MCS,&mu,&I,&H);
    }
  }
  while (k < lx);
  MPOL = gmul(MPOL,h);
  if (H) h = gmul(H, h);
  if (DEBUGLEVEL) err_printf("\n");
  MPOL = RgM_to_nfM(nf,MPOL);
  h = RgM_to_nfM(nf,h);
  return gerepilecopy(av, mkvec2(mkvec2(MPOL,I), h));
}

GEN
rnfpolred(GEN nf, GEN pol, long prec)
{
  pari_sp av = avma;
  long i, j, n, v = varn(pol);
  GEN id, w, I, O, bnf, nfpol;

  if (typ(pol)!=t_POL) pari_err(typeer,"rnfpolred");
  bnf = nf; nf = checknf(bnf);
  bnf = (nf == bnf)? NULL: checkbnf(bnf);
  if (degpol(pol) <= 1) { w = cgetg(2, t_VEC); gel(w,1) = pol_x(v); return w; }
  nfpol = nf_get_pol(nf);

  id = rnfpseudobasis(nf,pol);
  if (bnf && is_pm1( bnf_get_no(bnf) )) /* if bnf is principal */
  {
    GEN newI, newO;
    O = gel(id,1);
    I = gel(id,2); n = lg(I)-1;
    newI = cgetg(n+1,t_VEC);
    newO = cgetg(n+1,t_MAT);
    for (j=1; j<=n; j++)
    {
      GEN al = gen_if_principal(bnf,gel(I,j));
      gel(newI,j) = gen_1;
      gel(newO,j) = nfC_nf_mul(nf, gel(O,j), al);
    }
    id = mkvec2(newO, newI);
  }

  id = gel(rnflllgram(nf,pol,id,prec),1);
  O = gel(id,1);
  I = gel(id,2); n = lg(I)-1;
  w = cgetg(n+1,t_VEC);
  pol = lift(pol);
  for (j=1; j<=n; j++)
  {
    GEN newpol, L, a, Ij = gel(I,j);
    a = RgC_Rg_mul(gel(O,j), (typ(Ij) == t_MAT)? gcoeff(Ij,1,1): Ij);
    for (i=n; i; i--)
    {
      GEN c = gel(a,i);
      if (typ(c) == t_COL) gel(a,i) = coltoliftalg(nf, c);
    }
    a = RgV_to_RgX(a, v);
    newpol = RgXQX_red(RgXQ_charpoly(a, pol, v), nfpol);
    newpol = Q_primpart(newpol);

    (void)nfgcd_all(newpol, RgX_deriv(newpol), nfpol, nf_get_index(nf), &newpol);
    L = leading_term(newpol);
    gel(w,j) = (typ(L) == t_POL)? RgXQX_div(newpol, L, nfpol)
                                : RgX_Rg_div(newpol, L);
  }
  return gerepilecopy(av,w);
}

/* Let K = Q[X]/T = nf. Given a relative polynomial pol in K[X], L = K[X]/(pol),
 * compute a pseudo-basis for Z_L, then an absolute basis */
static GEN
makebasis(GEN nf, GEN pol, GEN rnfeq)
{
  GEN T = nf_get_pol(nf), TAB = gel(nf,9), W, I, polabs, a, B, ZK, p1, den, A;
  pari_sp av = avma;
  long i, j, k, N = degpol(pol), n = degpol(T), nN = n*N;

  polabs= gel(rnfeq,1); /* in Z[X], L = Q[X] / polabs, and pol | polabs */
  a     = gel(rnfeq,2); a = lift_intern(a); /* root of T in Q[X]/polabs */
  p1 = rnfpseudobasis(nf,pol);
  W = gel(p1,1);
  I = gel(p1,2);
  if (DEBUGLEVEL>1) err_printf("relative basis computed\n");

  A = QXQ_powers(a, n-1, polabs);
  /* ZK = integer basis of K, as elements of L */
  ZK = RgV_RgM_mul(A, RgXV_to_RgM(nf_get_zk(nf),n));

  W = RgV_RgM_mul(pol_x_powers(N, varn(pol)), W); /* vector of nfX */
  B = cgetg(nN+1, t_MAT);
  for(i=k=1; i<=N; i++)
  {
    GEN w = gel(W,i), id = gel(I,i);
    if (typ(id) == t_MAT)
    {
      w = typ(w) == t_COL? tablemulvec(TAB, w, id): RgM_Rg_mul(id,w);
      for(j=1; j<=n; j++)
      {
        p1 = grem(RgV_dotproduct(ZK, gel(w,j)), polabs);
        gel(B,k++) = RgX_to_RgV(p1, nN);
      }
    }
    else
    { /* scalar */
      if (typ(id) != t_INT || !is_pm1(id)) w = gmul(w, id);
      for(j=1; j<=n; j++)
      {
        p1 = grem(gmul(gel(ZK,j), w), polabs);
        gel(B,k++) = RgX_to_RgV(p1, nN);
      }
    }
  }
  B = Q_remove_denom(B, &den);
  if (den) { B = ZM_hnfmodid(B, den); B = RgM_Rg_div(B, den); }
  else B = matid(nN);
  return gerepilecopy(av, mkvec2(polabs, B));
}

/* relative polredabs. Returns relative polynomial by default (flag = 0)
 * flag & nf_ORIG: + element (base change)
 * flag & nf_ADDZK: + integer basis
 * flag & nf_ABSOLUTE: absolute polynomial */
GEN
rnfpolredabs(GEN nf, GEN relpol, long flag)
{
  pari_timer ti;
  GEN red, bas, elt, pol, T, a;
  long fl = (flag & nf_ADDZK)? nf_ADDZK: nf_RAW;
  pari_sp av = avma;

  if (typ(relpol)!=t_POL) pari_err(typeer,"rnfpolredabs");
  nf = checknf(nf);
  if (DEBUGLEVEL>1) timer_start(&ti);
  T = nf_get_pol(nf);
  relpol = rnf_fix_pol(T, relpol, 0);
  if ((flag & nf_ADDZK) && !(flag & nf_ABSOLUTE))
    pari_err(impl,"this combination of flags in rnfpolredabs");
  if (flag & nf_PARTIALFACT)
  {
    long sa;
    fl |= nf_PARTIALFACT;
    bas = rnfequationall(nf, relpol, &sa, NULL);
    a = stoi(sa);
  }
  else
  {
    GEN eq = rnfequation2(nf,relpol), rel;
    a = gel(eq,3);
    /* relpol( X + Mod(-a y, T(y)) )*/
    rel = RgXQX_translate(relpol, deg1pol_shallow(negi(a),gen_0,varn(T)), T);
    bas = makebasis(nf, rel, eq);
    if (DEBUGLEVEL>1)
    {
      timer_printf(&ti, "absolute basis");
      err_printf("original absolute generator: %Ps\n", gel(eq,1));
    }
  }
  red = polredabs0(bas, fl);
  pol = gel(red,1);
  if (DEBUGLEVEL>1) err_printf("reduced absolute generator: %Ps\n",pol);
  if (flag & nf_ABSOLUTE)
    return gerepilecopy(av, (flag & nf_ADDZK)? red: pol);

  elt = RgXQX_translate(gel(red,2), deg1pol_shallow(a,gen_0,varn(T)), T);
  elt = rnf_fix_pol(T, elt, 0);
  pol = RgXQ_charpoly(elt, relpol, varn(relpol));
  pol = lift_if_rational(pol);
  if (flag & nf_ORIG) pol = mkvec2(pol, mkpolmod(RgXQ_reverse(elt,relpol),pol));
  return gerepilecopy(av, pol);
}
