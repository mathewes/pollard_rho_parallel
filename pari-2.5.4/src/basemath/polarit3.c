/* $Id$

Copyright (C) 2000-2005  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/***********************************************************************/
/**                                                                   **/
/**               ARITHMETIC OPERATIONS ON POLYNOMIALS                **/
/**                         (third part)                              **/
/**                                                                   **/
/***********************************************************************/
#include "pari.h"
#include "paripriv.h"

/************************************************************************
 **                                                                    **
 **                      Ring membership                               **
 **                                                                    **
 ************************************************************************/

int
Rg_is_Fp(GEN x, GEN *pp)
{
  GEN mod;
  switch(typ(x))
  {
  case t_INTMOD:
    mod = gel(x,1);
    if (!*pp) *pp = mod;
    else if (mod != *pp && !equalii(mod, *pp))
    {
      if (DEBUGMEM) pari_warn(warner,"different moduli in Rg_is_Fp");
      return 0;
    }
    return 1;
  case t_INT:
    return 1;
  default: return 0;
  }
}

int
RgX_is_FpX(GEN x, GEN *pp)
{
  long i, lx = lg(x);
  for (i=2; i<lx; i++)
    if (!Rg_is_Fp(gel(x, i), pp))
      return 0;
  return 1;
}

int
RgV_is_FpV(GEN x, GEN *pp)
{
  long i, lx = lg(x);
  for (i=1; i<lx; i++)
    if (!Rg_is_Fp(gel(x,i), pp)) return 0;
  return 1;
}

int
RgM_is_FpM(GEN x, GEN *pp)
{
  long i, lx = lg(x);
  for (i=1; i<lx; i++)
    if (!RgV_is_FpV(gel(x, i), pp)) return 0;
  return 1;
}

int
Rg_is_FpXQ(GEN x, GEN *pT, GEN *pp)
{
  GEN pol, mod;
  switch(typ(x))
  {
  case t_INTMOD:
    return Rg_is_Fp(x, pp);
  case t_INT:
    return 1;
  case t_POL:
    return RgX_is_FpX(x, pp);
  case t_POLMOD:
    mod = gel(x,1); pol = gel(x, 2);
    if (!RgX_is_FpX(mod, pp)) return 0;
    if (typ(pol)==t_POL)
    {
      if (!RgX_is_FpX(pol, pp)) return 0;
    }
    else if (!Rg_is_Fp(pol, pp)) return 0;
    if (!*pT) *pT = mod;
    else if (mod != *pT && !gequal(mod, *pT))
    {
      if (DEBUGMEM) pari_warn(warner,"different moduli in Rg_is_FpXQ");
      return 0;
    }
    return 1;

  default: return 0;
  }
}

int
RgX_is_FpXQX(GEN x, GEN *pT, GEN *pp)
{
  long i, lx = lg(x);
  for (i = 2; i < lx; i++)
    if (!Rg_is_FpXQ(gel(x,i), pT, pp)) return 0;
  return 1;
}

/************************************************************************
 **                                                                    **
 **                      Ring conversion                               **
 **                                                                    **
 ************************************************************************/

/* p > 0 a t_INT, return lift(x * Mod(1,p)).
 * If x is an INTMOD, assume modulus is a multiple of p. */
GEN
Rg_to_Fp(GEN x, GEN p)
{
  if (lgefint(p) == 3) return utoi(Rg_to_Fl(x, (ulong)p[2]));
  switch(typ(x))
  {
    case t_INT: return modii(x, p);
    case t_FRAC: {
      pari_sp av = avma;
      GEN z = modii(gel(x,1), p);
      if (z == gen_0) return gen_0;
      return gerepileuptoint(av, remii(mulii(z, Fp_inv(gel(x,2), p)), p));
    }
    case t_PADIC: return padic_to_Fp(x, p);
    case t_INTMOD: {
      GEN q = gel(x,1), a = gel(x,2);
      if (equalii(q, p)) return icopy(a);
      if (!dvdii(q,p))
        pari_err(talker,"inconsistent moduli in Rg_to_Fp: %Ps, %Ps", q, p);
      return remii(a, p);
    }
    default: pari_err(typeer, "Rg_to_Fp");
      return NULL; /* not reached */
  }
}
ulong
Rg_to_Fl(GEN x, ulong p)
{
  switch(typ(x))
  {
    case t_INT: return umodiu(x, p);
    case t_FRAC: {
      ulong z = umodiu(gel(x,1), p);
      if (!z) return 0;
      return Fl_div(z, umodiu(gel(x,2), p), p);
    }
    case t_PADIC: return padic_to_Fl(x, p);
    case t_INTMOD: {
      GEN q = gel(x,1), a = gel(x,2);
      if (equaliu(q, p)) return itou(a);
      if (!dvdiu(q,p))
        pari_err(talker,"inconsistent moduli in Rg_to_Fp: %Ps, %lu", q, p);
      return umodiu(a, p);
    }
    default: pari_err(typeer, "Rg_to_Fl");
      return 0; /* not reached */
  }
}
/* If x is a POLMOD, assume modulus is a multiple of T. */
GEN
Rg_to_FpXQ(GEN x, GEN T, GEN p)
{
  long ta, tx = typ(x), v = varn(T);
  GEN a, b;
  if (is_const_t(tx))
  {
    if (tx == t_FFELT) return FF_to_FpXQ(x);
    return scalar_ZX(Rg_to_Fp(x, p), v);
  }
  switch(tx)
  {
    case t_POLMOD:
      b = gel(x,1);
      a = gel(x,2); ta = typ(a);
      if (is_const_t(ta)) return Rg_to_Fp(a, p);
      b = RgX_to_FpX(b, p); if (varn(b) != v) break;
      a = RgX_to_FpX(a, p); if (ZX_equal(b,T)) return a;
      return FpX_rem(a, T, p);
    case t_POL:
      if (varn(x) != v) break;
      return FpX_rem(RgX_to_FpX(x,p), T, p);
    case t_RFRAC:
      a = Rg_to_FpXQ(gel(x,1), T,p);
      b = Rg_to_FpXQ(gel(x,2), T,p);
      return FpXQ_div(a,b, T,p);
  }
  pari_err(typeer,"Rg_to_FpXQ");
  return NULL; /* not reached */
}
GEN
RgX_to_FpX(GEN x, GEN p)
{
  long i, l;
  GEN z = cgetg_copy(x, &l); z[1] = x[1];
  for (i = 2; i < l; i++) gel(z,i) = Rg_to_Fp(gel(x,i), p);
  return normalizepol_lg(z, l);
}

GEN
RgV_to_FpV(GEN x, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(z,i) = Rg_to_Fp(gel(x,i), p);
  return z;
}

GEN
RgC_to_FpC(GEN x, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_COL);
  for (i = 1; i < l; i++) gel(z,i) = Rg_to_Fp(gel(x,i), p);
  return z;
}

GEN
RgM_to_FpM(GEN x, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_MAT);
  for (i = 1; i < l; i++) gel(z,i) = RgC_to_FpC(gel(x,i), p);
  return z;
}

GEN
RgX_to_FpXQX(GEN x, GEN T, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_POL); z[1] = x[1];
  for (i = 2; i < l; i++) gel(z,i) = Rg_to_FpXQ(gel(x,i), T,p);
  return normalizepol_lg(z, l);
}
GEN
RgX_to_FqX(GEN x, GEN T, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_POL); z[1] = x[1];
  for (i = 2; i < l; i++) gel(z,i) = simplify_shallow(Rg_to_FpXQ(gel(x,i), T,p));
  return normalizepol_lg(z, l);
}

/* lg(V) > 1 */
GEN
FpXV_FpC_mul(GEN V, GEN W, GEN p)
{
  pari_sp av = avma;
  long i, l = lg(V);
  GEN z = ZX_Z_mul(gel(V,1),gel(W,1));
  for(i=2; i<l; i++) z = ZX_add(z, ZX_Z_mul(gel(V,i),gel(W,i)));
  return gerepileupto(av, FpX_red(z,p));
}

#if 0
static long brent_kung_nbmul(long d, long n, long p)
{
  return p+n*((d+p-1)/p);
}
  TODO: This the the optimal parameter for the purpose of reducing
  multiplications, but profiling need to be done to ensure it is not slower
  than the other option in practice
/*Return optimal parameter l for the evaluation of n polynomials of degree d*/
long brent_kung_optpow(long d, long n)
{
  double r;
  long f,c,pr;
  if (n>=d ) return d;
  pr=n*d;
  if (pr<=1) return 1;
  r=d/sqrt(pr);
  c=(long)ceil(d/ceil(r));
  f=(long)floor(d/floor(r));
  return (brent_kung_nbmul(d, n, c) <= brent_kung_nbmul(d, n, f))?c:f;
}
#endif
/*Return optimal parameter l for the evaluation of n polynomials of degree d*/
long
brent_kung_optpow(long d, long n)
{
  long l, pr;
  if (n >= d) return d;
  pr = n*d; if (pr <= 1) return 1;
  l = (long) ((double)d / sqrt(pr));
  return (d+l-1) / l;
}

/*Close to FpXV_FpC_mul*/
static GEN
FpXQ_eval_powers(GEN P, GEN V, long a, long n, GEN p)
{
  GEN z = scalar_ZX_shallow(gel(P,2+a), varn(P)); /* V[1] = 1 */
  long i;
  for (i=1; i<=n; i++) z = ZX_add(z, ZX_Z_mul(gel(V,i+1),gel(P,2+a+i)));
  return FpX_red(z, p);
}

/* Brent & Kung
 * (Fast algorithms for manipulating formal power series, JACM 25:581-595, 1978)
 *
 * V as output by FpXQ_powers(x,l,T,p). For optimal performance, l is as given
 * by brent_kung_optpow */
GEN
FpX_FpXQV_eval(GEN P, GEN V, GEN T, GEN p)
{
  pari_sp av = avma, btop;
  long l = lg(V)-1, d = degpol(P);
  GEN z, u;

  if (d < 0) return pol_0(varn(T));
  if (d < l)
  {
    z = FpXQ_eval_powers(P,V,0,d,p);
    return gerepileupto(av, z);
  }
  if (l<=1) pari_err(talker,"powers is only [] or [1] in FpX_FpXQV_eval");
  d -= l;
  btop = avma;
  z = FpXQ_eval_powers(P,V,d+1,l-1,p);
  while (d >= l-1)
  {
    d -= l-1;
    u = FpXQ_eval_powers(P,V,d+1,l-2,p);
    z = FpX_add(u, FpXQ_mul(z,gel(V,l),T,p), p);
    z = gerepileupto(btop, z);
  }
  u = FpXQ_eval_powers(P,V,0,d,p);
  z = FpX_add(u, FpXQ_mul(z,gel(V,d+2),T,p), p);
  if (DEBUGLEVEL>=8)
  {
    long cnt = 1 + (degpol(P) - l) / (l-1);
    err_printf("FpX_FpXQV_eval: %ld FpXQ_mul [%ld]\n", cnt, l-1);
  }
  return gerepileupto(av, z);
}

/* Q in Z[X] and x in Fp[X]/(T). Return a lift of Q(x) */
GEN
FpX_FpXQ_eval(GEN Q, GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z;
  long d = degpol(Q), rtd;
  if (d < 0) return pol_0(varn(Q));
  rtd = (long) sqrt((double)d);
  z = FpX_FpXQV_eval(Q, FpXQ_powers(x,rtd,T,p), T,p);
  return gerepileupto(av, z);
}

GEN
FqX_eval(GEN x, GEN y, GEN T, GEN p)
{
  pari_sp av;
  GEN p1, r;
  long j, i=lg(x)-1;
  if (i<=2)
    return (i==2)? Fq_red(gel(x,2), T, p): gen_0;
  av=avma; p1=gel(x,i);
  /* specific attention to sparse polynomials (see poleval)*/
  /*You've guessed it! It's a copy-paste(tm)*/
  for (i--; i>=2; i=j-1)
  {
    for (j=i; !signe(gel(x,j)); j--)
      if (j==2)
      {
        if (i!=j) y = Fq_pow(y,utoipos(i-j+1), T, p);
        return gerepileupto(av, gmul(p1,y));
      }
    r = (i==j)? y: Fq_pow(y, utoipos(i-j+1), T, p);
    p1 = Fq_red(gadd(gmul(p1,r), gel(x,j)), T, p);
  }
  return gerepileupto(av, p1);
}

/*******************************************************************/
/*                                                                 */
/*                             FpXX                                */
/*                                                                 */
/*******************************************************************/
/*Polynomials whose coefficients are either polynomials or integers*/
GEN
FpXX_red(GEN z, GEN p)
{
  GEN res;
  long i, l = lg(z);
  res = cgetg(l,t_POL); res[1] = z[1];
  for (i=2; i<l; i++)
  {
    GEN zi = gel(z,i), c;
    if (typ(zi)==t_INT)
      c = modii(zi,p);
    else
    {
      pari_sp av = avma;
      c = FpX_red(zi,p);
      switch(lg(c)) {
        case 2: avma = av; c = gen_0; break;
        case 3: c = gerepilecopy(av, gel(c,2)); break;
      }
    }
    gel(res,i) = c;
  }
  return FpXX_renormalize(res,lg(res));
}
GEN
FpXX_add(GEN x, GEN y, GEN p)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx; z = cgetg(lz, t_POL); z[1]=x[1];
  for (i=2; i<ly; i++) gel(z,i) = Fq_add(gel(x,i), gel(y,i), NULL, p);
  for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
  return FpXX_renormalize(z, lz);
}
GEN
FpXX_sub(GEN x, GEN y, GEN p)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly <= lx)
  {
    lz = lx; z = cgetg(lz, t_POL); z[1]=x[1];
    for (i=2; i<ly; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
  }
  else
  {
    lz = ly; z = cgetg(lz, t_POL); z[1]=x[1];
    for (i=2; i<lx; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<ly; i++) gel(z,i) = Fq_neg(gel(y,i), NULL, p);
  }
  return FpXX_renormalize(z, lz);
}

GEN
FpXX_Fp_mul(GEN P, GEN u, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN x = gel(P,i);
    gel(res,i) = typ(x)==t_INT? Fp_mul(x,u,p): FpX_Fp_mul(x,u,p);
  }
  return FpXX_renormalize(res,lP);
}

/*******************************************************************/
/*                                                                 */
/*                             (Fp[X]/(Q))[Y]                      */
/*                                                                 */
/*******************************************************************/
/*Not malloc nor warn-clean.*/
GEN
Kronecker_to_FpXQX(GEN Z, GEN T, GEN p)
{
  long i,j,lx,l, N = (degpol(T)<<1) + 1;
  GEN x, t = cgetg(N,t_POL), z = FpX_red(Z, p);
  t[1] = T[1];
  l = lg(z); lx = (l-2) / (N-2);
  x = cgetg(lx+3,t_POL);
  x[1] = z[1];
  for (i=2; i<lx+2; i++)
  {
    for (j=2; j<N; j++) t[j] = z[j];
    z += (N-2);
    gel(x,i) = FpX_rem(FpX_renormalize(t,N), T,p);
  }
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) t[j] = z[j];
  gel(x,i) = FpX_rem(FpX_renormalize(t,N), T,p);
  return FpXQX_renormalize(x, i+1);
}

GEN
FpXQX_red(GEN z, GEN T, GEN p)
{
  long i, l = lg(z);
  GEN res = cgetg(l,t_POL); res[1] = z[1];
  for(i=2;i<l;i++)
    if (typ(z[i]) == t_INT)
      gel(res,i) = modii(gel(z,i),p);
    else
      gel(res,i) = FpXQ_red(gel(z,i),T,p);
  return FpXQX_renormalize(res,lg(res));
}

GEN
FpXQX_mul(GEN x, GEN y, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z, kx, ky;
  kx = mod_to_Kronecker(x,T);
  ky = mod_to_Kronecker(y,T);
  z = Kronecker_to_FpXQX(ZX_mul(ky,kx), T, p);
  return gerepileupto(av, z);
}
GEN
FpXQX_sqr(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z, kx;
  kx= mod_to_Kronecker(x,T);
  z = Kronecker_to_FpXQX(ZX_sqr(kx), T, p);
  return gerepileupto(av, z);
}

GEN
FpXQX_FpXQ_mul(GEN P, GEN U, GEN T, GEN p)
{
  long i, lP;
  GEN res;
  res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = typ(gel(P,i))==t_INT? FpX_Fp_mul(U, gel(P,i), p):
                                       FpXQ_mul(U, gel(P,i), T,p);
  return FpXQX_renormalize(res,lP);
}

GEN
FqX_Fq_mul_to_monic(GEN P, GEN U, GEN T, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP-1; i++) gel(res,i) = Fq_mul(U,gel(P,i), T,p);
  gel(res,lP-1) = gen_1; return res;
}

GEN
FqX_normalize(GEN z, GEN T, GEN p)
{
  GEN p1;
  if (!T) return FpX_normalize(z,p);
  p1 = leading_term(z);
  if (lg(z) == 2 || gequal1(p1)) return z;
  return FqX_Fq_mul_to_monic(z, Fq_inv(p1,T,p), T,p);
}

/* a X^d */
GEN
monomial(GEN a, long d, long v)
{
  long i, lP = d+3;
  GEN P;
  if (d < 0) {
    P = cgetg(3, t_RFRAC);
    gel(P,1) = a;
    gel(P,2) = monomial(gen_1, -d, v);
  } else {
    P = cgetg(lP, t_POL);
    if (gequal0(a)) P[1] = evalsigne(0) | evalvarn(v);
    else          P[1] = evalsigne(1) | evalvarn(v);
    lP--; gel(P,lP) = a;
    for (i=2; i<lP; i++) gel(P,i) = gen_0;
  }
  return P;
}
GEN
monomialcopy(GEN a, long d, long v)
{
  long i, lP = d+3;
  GEN P;
  if (d < 0) {
    P = cgetg(3, t_RFRAC);
    gel(P,1) = gcopy(a);
    gel(P,2) = monomial(gen_1, -d, v);
  } else {
    P = cgetg(lP, t_POL);
    if (gequal0(a)) P[1] = evalsigne(0) | evalvarn(v);
    else          P[1] = evalsigne(1) | evalvarn(v);
    lP--; gel(P,lP) = gcopy(a);
    for (i=2; i<lP; i++) gel(P,i) = gen_0;
  }
  return P;
}
GEN
pol_x_powers(long N, long v)
{
  GEN L = cgetg(N+1,t_VEC);
  long i;
  for (i=1; i<=N; i++) gel(L,i) = monomial(gen_1, i-1, v);
  return L;
}

/* x and y in Z[Y][X]. Assume T irreducible mod p */
GEN
FpXQX_divrem(GEN x, GEN y, GEN T, GEN p, GEN *pr)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av, tetpil;
  GEN z,p1,rem,lead;

  if (!T) return FpX_divrem(x,y,p,pr);
  if (!signe(y)) pari_err(gdiver);
  vx=varn(x); dy=degpol(y); dx=degpol(x);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = FpXQX_red(x, T, p);
      if (pr == ONLY_DIVIDES) { avma=av0; return signe(x)? NULL: pol_0(vx); }
      if (pr == ONLY_REM) return x;
      *pr = x;
    }
    return pol_0(vx);
  }
  lead = leading_term(y);
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return pol_0(vx);
      *pr = pol_0(vx);
    }
    if (gequal1(lead)) return FpXQX_red(x,T,p);
    av0 = avma; x = FqX_Fq_mul(x, Fq_inv(lead, T,p), T,p);
    return gerepileupto(av0,x);
  }
  av0 = avma; dz = dx-dy;
  if (lgefint(p) == 3)
  { /* assume ab != 0 mod p */
    {
      GEN *gptr[2];
      ulong pp = (ulong)p[2];
      long v = varn(T);
      GEN a = ZXX_to_FlxX(x, pp, v);
      GEN b = ZXX_to_FlxX(y, pp, v);
      GEN t = ZX_to_Flx(T, pp);
      z = FlxqX_divrem(a,b,t,pp,pr);
      tetpil=avma;
      z = FlxX_to_ZXX(z);
      if (pr && pr != ONLY_DIVIDES && pr != ONLY_REM)
        *pr = FlxX_to_ZXX(*pr);
      else return gerepile(av0,tetpil,z);
      gptr[0]=pr; gptr[1]=&z;
      gerepilemanysp(av0,tetpil,gptr,2);
      return z;
    }
  }
  lead = gequal1(lead)? NULL: gclone(Fq_inv(lead,T,p));
  avma = av0;
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = lead? gerepileupto(av, Fq_mul(p1,lead, T, p)): gcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j),NULL,p),NULL,p);
    if (lead) p1 = Fq_mul(p1, lead, NULL,p);
    tetpil=avma; gel(z,i-dy) = gerepile(av,tetpil,Fq_red(p1,T,p));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j),NULL,p),NULL,p);
    tetpil=avma; p1 = Fq_red(p1, T, p); if (signe(p1)) { sx = 1; break; }
    if (!i) break;
    avma=av;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (lead) gunclone(lead);
    if (sx) { avma=av0; return NULL; }
    avma = (pari_sp)rem; return z-2;
  }
  lr=i+3; rem -= lr;
  rem[0] = evaltyp(t_POL) | evallg(lr);
  rem[1] = z[-1];
  p1 = gerepile((pari_sp)rem,tetpil,p1);
  rem += 2; gel(rem,i) = p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j), NULL,p), NULL,p);
    tetpil=avma; gel(rem,i) = gerepile(av,tetpil, Fq_red(p1, T, p));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)FpXQX_renormalize(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

GEN
FpXQX_gcd(GEN P, GEN Q, GEN T, GEN p)
{
  pari_sp av=avma, av0;
  GEN R;
  if (lgefint(p) == 3)
  {
    ulong pp = (ulong)p[2];
    GEN Pl, Ql, Tl, U;
    Pl = ZXX_to_FlxX(P, pp, varn(T));
    Ql = ZXX_to_FlxX(Q, pp, varn(T));
    Tl = ZX_to_Flx(T, pp);
    U  = FlxqX_gcd(Pl, Ql, Tl, pp);
    return gerepileupto(av, FlxX_to_ZXX(U));
  }
  P = FpXX_red(P, p); av0 = avma;
  Q = FpXX_red(Q, p);
  while (signe(Q))
  {
    av0 = avma; R = FpXQX_rem(P,Q,T,p); P=Q; Q=R;
  }
  avma = av0; return gerepileupto(av, P);
}

/* x and y in Z[Y][X], return lift(gcd(x mod T,p, y mod T,p)). Set u and v st
 * ux + vy = gcd (mod T,p) */
GEN
FpXQX_extgcd(GEN x, GEN y, GEN T, GEN p, GEN *ptu, GEN *ptv)
{
  GEN a, b, q, r, u, v, d, d1, v1;
  long vx = varn(x);
  pari_sp ltop=avma;
  if (lgefint(p) == 3)
  {
    ulong pp = (ulong)p[2];
    GEN Pl, Ql, Tl, Dl;
    Pl = ZXX_to_FlxX(x, pp, varn(T));
    Ql = ZXX_to_FlxX(y, pp, varn(T));
    Tl = ZX_to_Flx(T, pp);
    Dl = FlxqX_extgcd(Pl, Ql, Tl, pp, ptu, ptv);
    if (ptu) *ptu = FlxX_to_ZXX(*ptu);
    *ptv = FlxX_to_ZXX(*ptv);
    d = FlxX_to_ZXX(Dl);
  }
  else
  {
    a = FpXQX_red(x, T, p);
    b = FpXQX_red(y, T, p);
    d = a; d1 = b; v = pol_0(vx); v1 = pol_1(vx);
    while (signe(d1))
    {
      q = FqX_divrem(d,d1,T,p, &r);
      v = FqX_sub(v, FqX_mul(q,v1, T,p), T,p);
      u=v; v=v1; v1=u;
      u=r; d=d1; d1=u;
    }
    if (ptu) *ptu = FqX_div(FqX_sub(d, FqX_mul(b,v, T,p), T,p),a, T,p);
    *ptv = v;
  }
  gerepileall(ltop,ptu?3:2,&d,ptv,ptu);
  return d;
}

/* Inverse of x in Z/pZ[X]/(pol) or NULL if inverse doesn't exist
 * return lift(1 / (x mod (p,pol))) */
GEN
FpXQXQ_invsafe(GEN x, GEN S, GEN T, GEN p)
{
  GEN V, z = FpXQX_extgcd(S, x, T, p, NULL, &V);
  if (degpol(z)) return NULL;
  z = gel(z,2);
  z = typ(z)==t_INT ? Fp_invsafe(z,p) : FpXQ_invsafe(z,T,p);
  if (!z) return NULL;
  return typ(z)==t_INT ? FpXX_Fp_mul(V, z, p): FpXQX_FpXQ_mul(V, z, T, p);
}

GEN
FpXQXQ_inv(GEN x, GEN S, GEN T,GEN p)
{
  pari_sp av = avma;
  GEN U = FpXQXQ_invsafe(x, S, T, p);
  if (!U) pari_err(gdiver);
  return gerepileupto(av, U);
}

GEN
FpXQXQ_div(GEN x,GEN y,GEN S, GEN T,GEN p)
{
  pari_sp av = avma;
  return gerepileupto(av, FpXQXQ_mul(x, FpXQXQ_inv(y,S,T,p),S,T,p));
}

/*******************************************************************/
/*                                                                 */
/*                       (Fp[X]/T(X))[Y] / S(Y)                    */
/*                                                                 */
/*******************************************************************/

/*Preliminary implementation to speed up FpX_ffisom*/
typedef struct {
  GEN S, T, p;
} FpXYQQ_muldata;

/* reduce x in Fp[X, Y] in the algebra Fp[X, Y]/ (P(X),Q(Y)) */
static GEN
FpXYQQ_redswap(GEN x, GEN S, GEN T, GEN p)
{
  pari_sp ltop=avma;
  long n=degpol(S);
  long m=degpol(T);
  long v=varn(T),w=varn(S);
  GEN V = RgXY_swap(x,n,w);
  setvarn(T,w);
  V = FpXQX_red(V,T,p);
  setvarn(T,v);
  V = RgXY_swap(V,m,w);
  return gerepilecopy(ltop,V);
}
static GEN
FpXYQQ_sqr(void *data, GEN x)
{
  FpXYQQ_muldata *D = (FpXYQQ_muldata*)data;
  return FpXYQQ_redswap(FpXQX_sqr(x, D->S, D->p),D->S,D->T,D->p);

}
static GEN
FpXYQQ_mul(void *data, GEN x, GEN y)
{
  FpXYQQ_muldata *D = (FpXYQQ_muldata*)data;
  return FpXYQQ_redswap(FpXQX_mul(x,y, D->S, D->p),D->S,D->T,D->p);
}

/* x in Z[X,Y], S in Z[X] over Fq = Z[Y]/(p,T); compute lift(x^n mod (S,T,p)) */
GEN
FpXYQQ_pow(GEN x, GEN n, GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  FpXYQQ_muldata D;
  GEN y;
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    x = ZXX_to_FlxX(x, pp, varn(T));
    S = ZX_to_Flx(S, pp);
    T = ZX_to_Flx(T, pp);
    y = FlxX_to_ZXX( FlxYqQ_pow(x, n, S, T, pp) );
  }
  else
  {
    D.S = S;
    D.T = T;
    D.p = p;
    y = gen_pow(x, n, (void*)&D, &FpXYQQ_sqr, &FpXYQQ_mul);
  }
  return gerepileupto(av, y);
}

GEN
FpXQXQ_mul(GEN x, GEN y, GEN S, GEN T, GEN p) {
  GEN kx = mod_to_Kronecker(x, T);
  GEN ky = mod_to_Kronecker(y, T);
  GEN t = Kronecker_to_FpXQX(ZX_mul(kx, ky), T, p);
  return FpXQX_rem(t, S, T, p);
}

GEN
FpXQXQ_sqr(GEN x, GEN S, GEN T, GEN p) {
  GEN kx = mod_to_Kronecker(x, T);
  GEN t = Kronecker_to_FpXQX(ZX_sqr(kx), T, p);
  return FpXQX_rem(t, S, T, p);
}

typedef struct {
  GEN T, p, S;
} kronecker_muldata;

static GEN
_FpXQXQ_red(void *data, GEN x)
{
  kronecker_muldata *D = (kronecker_muldata*)data;
  GEN t = Kronecker_to_FpXQX(x, D->T, D->p);
  t = FpXQX_rem(t, D->S, D->T, D->p);
  return mod_to_Kronecker(t, D->T);
}
static GEN
_FpXQXQ_mul(void *data, GEN x, GEN y) {
  return _FpXQXQ_red(data, ZX_mul(x,y));
}
static GEN
_FpXQXQ_sqr(void *data, GEN x) {
  return _FpXQXQ_red(data, ZX_sqr(x));
}

/* x over Fq, return lift(x^n) mod S */
GEN
FpXQXQ_pow(GEN x, GEN n, GEN S, GEN T, GEN p)
{
  pari_sp ltop = avma;
  GEN y;
  kronecker_muldata D;
  long s = signe(n);
  if (!s) return pol_1(varn(x));
  if (is_pm1(n)) /* +/- 1 */
    return (s < 0)? FpXQXQ_inv(x,S,T,p): gcopy(x);
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    GEN z;
    long v = varn(T);
    T = ZX_to_Flx(T, pp);
    x = ZXX_to_FlxX(x, pp, v);
    S = ZXX_to_FlxX(S, pp, v);
    z = FlxqXQ_pow(x, n, S, T, pp);
    y = FlxX_to_ZXX(z);
  }
  else
  {
    D.S = S;
    D.T = T;
    D.p = p;
    if (s < 0) x = FpXQXQ_inv(x,S,T,p);
    y = gen_pow(mod_to_Kronecker(x,T), n, (void*)&D,&_FpXQXQ_sqr,&_FpXQXQ_mul);
    y = Kronecker_to_FpXQX(y, T,p);
  }
  return gerepileupto(ltop, y);
}
/*******************************************************************/
/*                                                                 */
/*                             Fq                                  */
/*                                                                 */
/*******************************************************************/

GEN
Fq_add(GEN x, GEN y, GEN T/*unused*/, GEN p)
{
  (void)T;
  switch((typ(x)==t_POL)|((typ(y)==t_POL)<<1))
  {
    case 0: return Fp_add(x,y,p);
    case 1: return FpX_Fp_add(x,y,p);
    case 2: return FpX_Fp_add(y,x,p);
    case 3: return FpX_add(x,y,p);
  }
  return NULL;
}

GEN
Fq_sub(GEN x, GEN y, GEN T/*unused*/, GEN p)
{
  (void)T;
  switch((typ(x)==t_POL)|((typ(y)==t_POL)<<1))
  {
    case 0: return Fp_sub(x,y,p);
    case 1: return FpX_Fp_sub(x,y,p);
    case 2: return Fp_FpX_sub(x,y,p);
    case 3: return FpX_sub(x,y,p);
  }
  return NULL;
}

GEN
Fq_neg(GEN x, GEN T/*unused*/, GEN p)
{
  (void)T;
  return (typ(x)==t_POL)? FpX_neg(x,p)
                        : Fp_neg(x,p);
}

/* If T==NULL do not reduce*/
GEN
Fq_mul(GEN x, GEN y, GEN T, GEN p)
{
  switch((typ(x)==t_POL)|((typ(y)==t_POL)<<1))
  {
    case 0: return Fp_mul(x,y,p);
    case 1: return FpX_Fp_mul(x,y,p);
    case 2: return FpX_Fp_mul(y,x,p);
    case 3: if (T) return FpXQ_mul(x,y,T,p);
            else return FpX_mul(x,y,p);
  }
  return NULL;
}
/* y t_INT */
GEN
Fq_Fp_mul(GEN x, GEN y, GEN T/*unused*/, GEN p)
{
  (void)T;
  return (typ(x) == t_POL)? FpX_Fp_mul(x,y,p)
                          : Fp_mul(x,y,p);
}
/* If T==NULL do not reduce*/
GEN
Fq_sqr(GEN x, GEN T, GEN p)
{
  if (typ(x) == t_POL)
  {
    if (T) return FpXQ_sqr(x,T,p);
    else return FpX_sqr(x,p);
  }
  else
    return Fp_sqr(x,p);
  return NULL;
}

GEN
Fq_neg_inv(GEN x, GEN T, GEN p)
{
  if (typ(x) == t_INT) return Fp_inv(Fp_neg(x,p),p);
  return FpXQ_inv(FpX_neg(x,p),T,p);
}

GEN
Fq_invsafe(GEN x, GEN pol, GEN p)
{
  if (typ(x) == t_INT) return Fp_invsafe(x,p);
  return FpXQ_invsafe(x,pol,p);
}

GEN
Fq_inv(GEN x, GEN pol, GEN p)
{
  if (typ(x) == t_INT) return Fp_inv(x,p);
  return FpXQ_inv(x,pol,p);
}

GEN
Fq_pow(GEN x, GEN n, GEN pol, GEN p)
{
  if (typ(x) == t_INT) return Fp_pow(x,n,p);
  return FpXQ_pow(x,n,pol,p);
}

GEN
Fq_sqrt(GEN x, GEN T, GEN p)
{
  if (typ(x) == t_POL)
    return FpXQ_sqrtn(x,gen_2,T,p,NULL);
  else
    return Fp_sqrt(x,p);
  return NULL;
}

/*******************************************************************/
/*                                                                 */
/*                             Fq[X]                               */
/*                                                                 */
/*******************************************************************/
/* P(X + c), c an Fq */
GEN
FqX_translate(GEN P, GEN c, GEN T, GEN p)
{
  pari_sp av = avma, lim;
  GEN Q, *R;
  long i, k, n;

  if (!signe(P) || !signe(c)) return gcopy(P); /* signe works for t_(INT|POL) */
  Q = leafcopy(P);
  R = (GEN*)(Q+2); n = degpol(P);
  lim = stack_lim(av, 2);
  for (i=1; i<=n; i++)
  {
    for (k=n-i; k<n; k++)
      R[k] = Fq_add(R[k], Fq_mul(c, R[k+1], T, p), T, p);

    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"FqX_translate, i = %ld/%ld", i,n);
      Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
    }
  }
  return gerepilecopy(av, normalizepol(Q));
}


struct _FpXQX { GEN T,p; };
static GEN _FpXQX_mul(void *data, GEN a,GEN b)
{
  struct _FpXQX *d=(struct _FpXQX*)data;
  return FpXQX_mul(a,b,d->T,d->p);
}
GEN
FpXQXV_prod(GEN V, GEN T, GEN p)
{
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    ulong pp = p[2];
    GEN Tl = ZX_to_Flx(T, pp);
    GEN Vl = ZXXV_to_FlxXV(V, pp, varn(T));
    Tl = FlxqXV_prod(Vl, Tl, pp);
    return gerepileupto(av, FlxX_to_ZXX(Tl));
  }
  else
  {
    struct _FpXQX d;
    d.p=p;
    d.T=T;
    return divide_conquer_assoc(V, (void*)&d, &_FpXQX_mul);
  }
}

GEN
FqV_roots_to_pol(GEN V, GEN T, GEN p, long v)
{
  pari_sp ltop = avma;
  long k;
  GEN W;
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    GEN Tl = ZX_to_Flx(T, pp);
    GEN Vl = FqV_to_FlxV(V, T, p);
    Tl = FlxqV_roots_to_pol(Vl, Tl, pp, v);
    return gerepileupto(ltop, FlxX_to_ZXX(Tl));
  }
  W = cgetg(lg(V),t_VEC);
  for(k=1; k < lg(V); k++)
    gel(W,k) = deg1pol_shallow(gen_1,Fq_neg(gel(V,k),T,p),v);
  return gerepileupto(ltop, FpXQXV_prod(W, T, p));
}

GEN
FqV_red(GEN z, GEN T, GEN p)
{
  long i, l = lg(z);
  GEN res = cgetg(l, typ(z));
  for(i=1;i<l;i++) gel(res,i) = Fq_red(gel(z,i),T,p);
  return res;
}

GEN
FqV_to_FlxV(GEN v, GEN T, GEN pp)
{
  long j, N = lg(v);
  long vT = varn(T);
  ulong p = pp[2];
  GEN y = cgetg(N, t_VEC);
  for (j=1; j<N; j++)
    gel(y,j) = (typ(v[j])==t_INT?  Z_to_Flx(gel(v,j), p, vT)
                                  : ZX_to_Flx(gel(v,j), p));
  return y;
}

GEN
FqC_to_FlxC(GEN v, GEN T, GEN pp)
{
  long j, N = lg(v);
  long vT = varn(T);
  ulong p = pp[2];
  GEN y = cgetg(N, t_COL);
  for (j=1; j<N; j++)
    gel(y,j) = (typ(v[j])==t_INT?  Z_to_Flx(gel(v,j), p, vT)
                                  : ZX_to_Flx(gel(v,j), p));
  return y;
}

GEN
FqM_to_FlxM(GEN x, GEN T, GEN pp)
{
  long j, n = lg(x);
  GEN y = cgetg(n,t_MAT);
  if (n == 1) return y;
  for (j=1; j<n; j++)
    gel(y,j) = FqC_to_FlxC(gel(x,j), T, pp);
  return y;
}


/*******************************************************************/
/*  Isomorphisms between finite fields                             */
/*******************************************************************/

/* compute the reciprocical isomorphism of S mod T,p, i.e. V such that
   V(S)=X  mod T,p*/
GEN
FpXQ_ffisom_inv(GEN S,GEN T, GEN p)
{
  pari_sp ltop = avma;
  long n = degpol(T);
  GEN V, M = FpXQ_matrix_pow(S,n,n,T,p);
  V = FpM_invimage(M, col_ei(n, 2), p);
  return gerepileupto(ltop, gtopolyrev(V, varn(T)));
}

/* Let M the matrix of the x^p Frobenius automorphism.
 * Compute x^(p^i) for i=0..r */
static GEN
FpM_Frobenius(GEN M, long r, GEN p, long v)
{
  GEN W, V = cgetg(r+2,t_VEC);
  long i;
  gel(V,1) = pol_x(v); if (!r) return V;
  gel(V,2) = RgV_to_RgX(gel(M,2),v);
  W = gel(M,2);
  for (i = 3; i <= r+1; ++i)
  {
    W = FpM_FpC_mul(M,W,p);
    gel(V,i) = RgV_to_RgX(W,v);
  }
  return V;
}

/* Let M the matrix of the x^p Frobenius automorphism.
 * Compute x^(p^i) for i=0..r */
static GEN
Flm_Frobenius(GEN M, long r, ulong p, long v)
{
  GEN W, V = cgetg(r+2,t_VEC);
  long i;
  gel(V,1) = polx_Flx(v); if (!r) return V;
  gel(V,2) = Flv_to_Flx(gel(M,2),v);
  W = gel(M,2);
  for (i = 3; i <= r+1; ++i)
  {
    W = Flm_Flc_mul(M,W,p);
    gel(V,i) = Flv_to_Flx(W,v);
  }
  return V;
}

/* Let P a polynomial != 0 and M the matrix of the x^p Frobenius automorphism in
 * FFp[X]/T. Compute P(M)
 * V=FpM_Frobenius(M, p, degpol(P), v)
 * not stack clean
 */

static GEN
FpXQV_FpX_Frobenius(GEN V, GEN P, GEN T, GEN p)
{
  pari_sp btop;
  long i;
  long l=degpol(T);
  long v=varn(T);
  GEN M,W,Mi;
  GEN *gptr[2];
  long lV=lg(V);
  GEN  PV=RgX_to_RgV(P, lgpol(P));
  M=cgetg(l+1,t_VEC);
  gel(M,1) = scalar_ZX_shallow(FpX_eval(P,gen_1,p),v);
  gel(M,2) = FpXV_FpC_mul(V,PV,p);
  btop=avma;
  gptr[0]=&Mi;
  gptr[1]=&W;
  W = leafcopy(V);
  for(i=3;i<=l;i++)
  {
    long j;
    pari_sp bbot;
    GEN W2=cgetg(lV,t_VEC);
    for(j=1;j<lV;j++)
      gel(W2,j) = FpXQ_mul(gel(W,j),gel(V,j),T,p);
    bbot=avma;
    Mi=FpXV_FpC_mul(W2,PV,p);
    W=gcopy(W2);
    gerepilemanysp(btop,bbot,gptr,2);
    btop=(pari_sp)W;
    gel(M,i) = Mi;
  }
  return RgXV_to_RgM(M,l);
}

static GEN
FlxqV_Flx_Frobenius(GEN V, GEN P, GEN T, ulong p)
{
  pari_sp btop;
  long i;
  long l=degpol(T);
  long v=varn(T);
  GEN M,W,Mi;
  GEN PV=Flx_to_Flv(P, lgpol(P));
  GEN *gptr[2];
  long lV=lg(V);
  M=cgetg(l+1,t_VEC);
  gel(M,1) = Fl_to_Flx(Flx_eval(P,1,p),v);
  gel(M,2) = FlxV_Flc_mul(V,PV,p);
  btop=avma;
  gptr[0]=&Mi;
  gptr[1]=&W;
  W=gcopy(V);
  for(i=3;i<=l;i++)
  {
    long j;
    pari_sp bbot;
    GEN W2=cgetg(lV,t_VEC);
    for(j=1;j<lV;j++)
      gel(W2,j) = Flxq_mul(gel(W,j),gel(V,j),T,p);
    bbot=avma;
    Mi=FlxV_Flc_mul(W2,PV,p);
    W=gcopy(W2);
    gerepilemanysp(btop,bbot,gptr,2);
    btop=(pari_sp)W;
    gel(M,i) = Mi;
  }
  return FlxV_to_Flm(M,l);
}

/* Let M the matrix of the Frobenius automorphism of Fp[X]/(T).
 * Compute M^d
 * TODO: use left-right binary (tricky!)
 */
GEN
Flm_Frobenius_pow(GEN M, long d, GEN T, ulong p)
{
  pari_sp ltop=avma;
  long i,l=degpol(T);
  GEN R, W = gel(M,2);
  for (i = 2; i <= d; ++i) W = Flm_Flc_mul(M,W,p);
  R=Flxq_matrix_pow(Flv_to_Flx(W,T[2]),l,l,T,p);
  return gerepileupto(ltop,R);
}

GEN
FpM_Frobenius_pow(GEN M, long d, GEN T, GEN p)
{
  pari_sp ltop=avma;
  long i,l=degpol(T);
  GEN R, W = gel(M,2);
  for (i = 2; i <= d; ++i) W = FpM_FpC_mul(M,W,p);
  R=FpXQ_matrix_pow(RgV_to_RgX(W,varn(T)),l,l,T,p);
  return gerepilecopy(ltop,R);
}

/* Essentially we want to compute
 * FqM_ker(MA-pol_x(MAXVARN),U,l)
 * To avoid use of matrix in Fq we procede as follows:
 * We compute FpM_ker(U(MA),l) and then we recover
 * the eigen value by Galois action, see formula.
 */
static GEN
intersect_ker(GEN P, GEN MA, GEN U, GEN l)
{
  pari_sp ltop = avma;
  long i, vp = varn(P), vu = varn(U), r = degpol(U);
  GEN A, R, ib0;
  pari_timer T;
  if (DEBUGLEVEL>=4) timer_start(&T);
  if (lgefint(l)==3)
  {
    ulong p = l[2];
    GEN M, V = Flm_Frobenius(ZM_to_Flm(MA, p), r, p, evalvarn(vu));
    if (DEBUGLEVEL>=4) timer_printf(&T,"pol[Frobenius]");
    M = FlxqV_Flx_Frobenius(V, ZX_to_Flx(U, p), ZX_to_Flx(P, p), p);
    if (DEBUGLEVEL>=4) timer_printf(&T,"U[Frobenius]");
    if (p==2)
      A = F2m_to_ZM(F2m_ker(Flm_to_F2m(M)));
    else
      A = Flm_to_ZM(Flm_ker(M,p));
  }
  else
  {
    GEN V = FpM_Frobenius(MA,r,l,vu);
    if (DEBUGLEVEL>=4) timer_printf(&T,"pol[Frobenius]");
    A = FpM_ker(FpXQV_FpX_Frobenius(V, U, P, l), l);
  }
  if (DEBUGLEVEL>=4) timer_printf(&T,"matrix polcyclo");
  if (lg(A)!=r+1)
    pari_err(talker,"ZZ_%Ps[%Ps]/(%Ps) is not a field in FpX_ffintersect"
        ,l,pol_x(vp),P);
  A = gerepileupto(ltop,A);
  /*The formula is
   * a_{r-1} = -\phi(a_0)/b_0
   * a_{i-1} = \phi(a_i)+b_ia_{r-1}  i=r-1 to 1
   * Where a_0=A[1] and b_i=U[i+2] */
  ib0 = Fp_inv(negi(gel(U,2)),l);
  R = cgetg(r+1,t_MAT);
  gel(R,1) = gel(A,1);
  gel(R,r) = FpM_FpC_mul(MA, FpC_Fp_mul(gel(A,1),ib0,l), l);
  for(i=r-1;i>1;i--)
    gel(R,i) = FpC_add(FpM_FpC_mul(MA,gel(R,i+1),l),
                       FpC_Fp_mul(gel(R,r), gel(U,i+2), l),l);
  R = shallowtrans(R);
  for(i=1;i<lg(R);i++) gel(R,i) = RgV_to_RgX(gel(R,i),vu);
  A = gtopolyrev(R,vp);
  return gerepileupto(ltop,A);
}

/* n must divide both the degree of P and Q.  Compute SP and SQ such
  that the subfield of FF_l[X]/(P) generated by SP and the subfield of
  FF_l[X]/(Q) generated by SQ are isomorphic of degree n.  P and Q do
  not need to be of the same variable.  if MA (resp. MB) is not NULL,
  must be the matrix of the Frobenius map in FF_l[X]/(P) (resp.
  FF_l[X]/(Q) ).  */
/* Note on the implementation choice:
 * We assume the prime p is very large
 * so we handle Frobenius as matrices.
 */
void
FpX_ffintersect(GEN P, GEN Q, long n, GEN l,GEN *SP, GEN *SQ, GEN MA, GEN MB)
{
  pari_sp lbot, ltop = avma;
  long vp, vq, np, nq, e;
  ulong pg;
  GEN A, B, Ap, Bp;
  GEN *gptr[2];
  vp = varn(P); np = degpol(P);
  vq = varn(Q); nq = degpol(Q);
  if (np<=0 || nq<=0 || n<=0 || np%n!=0 || nq%n!=0)
    pari_err(talker,"bad degrees in FpX_ffintersect: %d,%d,%d",n,np,nq);
  e = u_pvalrem(n, l, &pg);
  if(!MA) MA = FpXQ_matrix_pow(FpXQ_pow(pol_x(vp),l,P,l),np,np,P,l);
  if(!MB) MB = FpXQ_matrix_pow(FpXQ_pow(pol_x(vq),l,Q,l),nq,nq,Q,l);
  A = Ap = pol_0(vp);
  B = Bp = pol_0(vq);
  if (pg > 1)
  {
    GEN ipg = utoipos(pg);
    pari_timer T;
    if (umodiu(l,pg) == 1)
    /* No need to use relative extension, so don't. (Well, now we don't
     * in the other case either, but this special case is more efficient) */
    {
      GEN L, An, Bn, z;
      ulong t; (void)u_lvalrem(pg, 2, &t); /* 2 implicit in pgener_Fp_local */
      z = pgener_Fp_local(l, gel(Z_factor(utoipos(t)), 1));
      z = Fp_pow(z, diviuexact(subis(l,1), pg), l); /* prim. pg-th root of 1 */
      z = negi(z);
      if (DEBUGLEVEL>=4) timer_start(&T);
      A = FpM_ker(RgM_Rg_add_shallow(MA, z),l);
      if (lg(A)!=2)
        pari_err(talker,"ZZ_%Ps[%Ps]/(%Ps) is not a field in FpX_ffintersect"
            ,l,pol_x(vp),P);
      A = RgV_to_RgX(gel(A,1),vp);

      B = FpM_ker(RgM_Rg_add_shallow(MB, z),l);
      if (lg(B)!=2)
        pari_err(talker,"ZZ_%Ps[%Ps]/(%Ps) is not a field in FpX_ffintersect"
            ,l,pol_x(vq),Q);
      B = RgV_to_RgX(gel(B,1),vq);

      if (DEBUGLEVEL>=4) timer_printf(&T, "FpM_ker");
      An = gel(FpXQ_pow(A,ipg,P,l),2);
      Bn = gel(FpXQ_pow(B,ipg,Q,l),2);
      if (!invmod(Bn,l,&z))
        pari_err(talker,"Polynomials not irreducible in FpX_ffintersect");
      z = Fp_mul(An,z,l);
      L = Fp_sqrtn(z,ipg,l,NULL);
      if ( !L )
        pari_err(talker,"Polynomials not irreducible in FpX_ffintersect");
      if (DEBUGLEVEL>=4) timer_printf(&T, "Fp_sqrtn");
      B = FpX_Fp_mul(B,L,l);
    }
    else
    {
      GEN L, An, Bn, z, U;
      U = gmael(FpX_factor(polcyclo(pg,MAXVARN),l),1,1);
      A = intersect_ker(P, MA, U, l);
      B = intersect_ker(Q, MB, U, l);
      if (DEBUGLEVEL>=4) timer_start(&T);
      An = gel(FpXYQQ_pow(A,ipg,U,P,l),2);
      Bn = gel(FpXYQQ_pow(B,ipg,U,Q,l),2);
      if (DEBUGLEVEL>=4) timer_printf(&T,"pows [P,Q]");
      z = Fq_inv(Bn,U,l);
      z = Fq_mul(An,z,U,l);
      if (typ(z)==t_INT) z = scalarpol(z,MAXVARN);
      L = FpXQ_sqrtn(z,ipg,U,l,NULL);
      if (DEBUGLEVEL>=4) timer_printf(&T,"FpXQ_sqrtn");
      if (!L) pari_err(talker,"Polynomials not irreducible in FpX_ffintersect");
      B = FqX_Fq_mul(B,L,U,l);
      B = gsubst(B,MAXVARN,gen_0);
      A = gsubst(A,MAXVARN,gen_0);
    }
  }
  if (e)
  {
    GEN VP, VQ, Ay, By, lmun = addis(l,-1);
    long i, j;
    MA = RgM_Rg_add_shallow(MA,gen_m1);
    MB = RgM_Rg_add_shallow(MB,gen_m1);
    Ay = pol_1(vp);
    By = pol_1(vq);
    VP = col_ei(np, 1);
    VQ = np == nq? VP: col_ei(nq, 1); /* save memory */
    for(j=0;j<e;j++)
    {
      if (j)
      {
        Ay = FpXQ_mul(Ay,FpXQ_pow(Ap,lmun,P,l),P,l);
        for(i=1;i<lg(Ay)-1;i++) VP[i] = Ay[i+1];
        for(;i<=np;i++) gel(VP,i) = gen_0;
      }
      Ap = FpM_invimage(MA,VP,l);
      Ap = RgV_to_RgX(Ap,vp);

      if (j)
      {
        By = FpXQ_mul(By,FpXQ_pow(Bp,lmun,Q,l),Q,l);
        for(i=1;i<lg(By)-1;i++) VQ[i] = By[i+1];
        for(;i<=nq;i++) gel(VQ,i) = gen_0;
      }
      Bp = FpM_invimage(MB,VQ,l);
      Bp = RgV_to_RgX(Bp,vq);
    }
  }
  A = ZX_add(A,Ap);
  B = ZX_add(B,Bp);
  lbot = avma;
  *SP = FpX_red(A,l);
  *SQ = FpX_red(B,l);
  gptr[0] = SP;
  gptr[1] = SQ; gerepilemanysp(ltop,lbot,gptr,2);
}
/* Let l be a prime number, P, Q in ZZ[X].  P and Q are both
 * irreducible modulo l and degree(P) divides degree(Q).  Output a
 * monomorphism between FF_l[X]/(P) and FF_l[X]/(Q) as a polynomial R such
 * that Q | P(R) mod l.  If P and Q have the same degree, it is of course an
 * isomorphism.  */
GEN
FpX_ffisom(GEN P,GEN Q,GEN l)
{
  pari_sp av = avma;
  GEN SP, SQ, R;
  FpX_ffintersect(P,Q,degpol(P),l,&SP,&SQ,NULL,NULL);
  R = FpXQ_ffisom_inv(SP,P,l);
  return gerepileupto(av, FpX_FpXQ_eval(R,SQ,Q,l));
}

/* Let l be a prime number, P a ZX irreducible modulo l, MP the matrix of the
 * Frobenius automorphism of F_l[X]/(P).
 * Factor P over the subfield of F_l[X]/(P) of index d. */
static GEN
FpX_factorgalois(GEN P, GEN l, long d, long w, GEN MP)
{
  pari_sp ltop = avma;
  GEN R, V, Tl, z, M;
  long k, n = degpol(P), m = n/d;
  long v = varn(P);

  /* x - y */
  if (m == 1) return deg1pol_shallow(gen_1, deg1pol_shallow(subis(l,1), gen_0, w), v);
  M = FpM_Frobenius_pow(MP,d,P,l);

  Tl = leafcopy(P); setvarn(Tl,w);
  V = cgetg(m+1,t_VEC);
  gel(V,1) = pol_x(w);
  z = gel(M,2);
  gel(V,2) = RgV_to_RgX(z,w);
  for(k=3;k<=m;k++)
  {
    z = FpM_FpC_mul(M,z,l);
    gel(V,k) = RgV_to_RgX(z,w);
  }
  R = FqV_roots_to_pol(V,Tl,l,v);
  return gerepileupto(ltop,R);
}
/* same: P is an Flx, MP an Flm */
static GEN
Flx_factorgalois(GEN P, ulong l, long d, long w, GEN MP)
{
  pari_sp ltop = avma;
  GEN R, V, Tl, z, M;
  long k, n = degpol(P), m = n/d;
  long v = varn(P);

  if (m == 1) {
    R = polx_Flx(v);
    gel(R,2) = z = polx_Flx(w); z[3] = l - 1; /* - y */
    gel(R,3) = pol1_Flx(w);
    return R; /* x - y */
  }
  M = Flm_Frobenius_pow(MP,d,P,l);

  Tl = leafcopy(P); setvarn(Tl,w);
  V = cgetg(m+1,t_VEC);
  gel(V,1) = polx_Flx(w);
  z = gel(M,2);
  gel(V,2) = Flv_to_Flx(z,w);
  for(k=3;k<=m;k++)
  {
    z = Flm_Flc_mul(M,z,l);
    gel(V,k) = Flv_to_Flx(z,w);
  }
  R = FlxqV_roots_to_pol(V,Tl,l,v);
  return gerepileupto(ltop,R);
}

/* P,Q irreducible over F_l. Factor P over FF_l[X] / Q  [factors are ordered as
 * a Frobenius cycle] */
GEN
FpX_factorff_irred(GEN P, GEN Q, GEN l)
{
  pari_sp ltop = avma, av;
  GEN SP, SQ, MP, MQ, M, FP, FQ, E, V, IR, res;
  long np = degpol(P), nq = degpol(Q), d = cgcd(np,nq);
  long i, vp = varn(P), vq = varn(Q);

  if (d==1) return mkcolcopy(P);
  if (lgefint(l)==3)
  {
    ulong p = l[2];
    GEN Px = ZX_to_Flx(P,p), Qx = ZX_to_Flx(Q,p);
    FQ = Flxq_matrix_pow(Flxq_pow(polx_Flx(vq),l,Qx,p),nq,nq,Qx,p);
    av = avma;
    FP = Flxq_matrix_pow(Flxq_pow(polx_Flx(vp),l,Px,p),np,np,Px,p);
    FpX_ffintersect(P,Q,d,l,&SP,&SQ, Flm_to_ZM(FP), Flm_to_ZM(FQ));

    E = Flx_factorgalois(Px,p,d,vq, FP);
    E = FlxX_to_Flm(E,np);
    MP= Flxq_matrix_pow(ZX_to_Flx(SP,p),np,d,Px,p);
    IR= gel(Flm_indexrank(MP,p),1);
    E = rowpermute(E, IR);
    M = rowpermute(MP,IR);
    M = Flm_inv(M,p);
    MQ= Flxq_matrix_pow(ZX_to_Flx(SQ,p),nq,d,Qx,p);
    M = Flm_mul(MQ,M,p);
    M = Flm_mul(M,E,p);
    M = gerepileupto(av,M);
    V = cgetg(d+1,t_VEC);
    gel(V,1) = M;
    for(i=2;i<=d;i++)
      gel(V,i) = Flm_mul(FQ,gel(V,i-1),p);
    res=cgetg(d+1,t_COL);
    for(i=1;i<=d;i++)
      gel(res,i) = FlxX_to_ZXX(Flm_to_FlxX(gel(V,i),evalvarn(vp),evalvarn(vq)));
  }
  else
  {
    FQ = FpXQ_matrix_pow(FpXQ_pow(pol_x(vq),l,Q,l),nq,nq,Q,l);
    av = avma;
    FP = FpXQ_matrix_pow(FpXQ_pow(pol_x(vp),l,P,l),np,np,P,l);
    FpX_ffintersect(P,Q,d,l,&SP,&SQ,FP,FQ);

    E = FpX_factorgalois(P,l,d,vq,FP);
    E = RgXX_to_RgM(E,np);
    MP= FpXQ_matrix_pow(SP,np,d,P,l);
    IR= gel(FpM_indexrank(MP,l),1);
    E = rowpermute(E, IR);
    M = rowpermute(MP,IR);
    M = FpM_inv(M,l);
    MQ= FpXQ_matrix_pow(SQ,nq,d,Q,l);
    M = FpM_mul(MQ,M,l);
    M = FpM_mul(M,E,l);
    M = gerepileupto(av,M);
    V = cgetg(d+1,t_VEC);
    gel(V,1) = M;
    for(i=2;i<=d;i++)
      gel(V,i) = FpM_mul(FQ,gel(V,i-1),l);
    res = cgetg(d+1,t_COL);
    for(i=1;i<=d;i++)
      gel(res,i) = RgM_to_RgXX(gel(V,i),vp,vq);
  }
  return gerepilecopy(ltop,res);
}

/* z in R[Y] representing an elt in R[X,Y] mod T(Y) in Kronecker form,
 * i.e subst(lift(z), x, y^(2deg(z)-1)). Recover the "real" z, with
 * normalized coefficients */
GEN
Kronecker_to_mod(GEN z, GEN T)
{
  long i,j,lx,l = lg(z), N = (degpol(T)<<1) + 1;
  GEN x, t = cgetg(N,t_POL);
  t[1] = T[1];
  lx = (l-2) / (N-2); x = cgetg(lx+3,t_POL);
  x[1] = z[1];
  T = gcopy(T);
  for (i=2; i<lx+2; i++, z+= N-2)
  {
    for (j=2; j<N; j++) gel(t,j) = gel(z,j);
    gel(x,i) = mkpolmod(RgX_rem(normalizepol_lg(t,N), T), T);
  }
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) t[j] = z[j];
  gel(x,i) = mkpolmod(RgX_rem(normalizepol_lg(t,N), T), T);
  return normalizepol_lg(x, i+1);
}

/* Kronecker substitution, RgYX -> RgY :
 * Q a RgY of degree n, P(X) = sum P_i * X^i, where the deg P_i are t_POLMOD
 * mod Q or RgY of degree < n.
 * Lift the P_i which are t_POLMOD, then return subst(P( Y^(2n-1) ), Y,X) */
GEN
mod_to_Kronecker(GEN P, GEN Q)
{
  long i, k, lx = lg(P), N = (degpol(Q)<<1) + 1, vQ = varn(Q);
  GEN y = cgetg((N-2)*(lx-2) + 2, t_POL);

  for (k=i=2; i<lx; i++)
  {
    GEN c = gel(P,i);
    long j, tc = typ(c);
    if (tc == t_POLMOD) { c = gel(c,2); tc = typ(c); }
    if (is_scalar_t(tc) || varncmp(varn(c), vQ) > 0)
    {
      gel(y,k++) = c; j = 3;
    }
    else
    {
      long l = lg(c);
      for (j=2; j < l; j++) gel(y,k++) = gel(c,j);
    }
    if (i == lx-1) break;
    for (   ; j < N; j++) gel(y,k++) = gen_0;
  }
  y[1] = P[1]; setlg(y, k); return y;
}

/*******************************************************************/
/*                                                                 */
/*                          MODULAR GCD                            */
/*                                                                 */
/*******************************************************************/
/* return z = a mod q, b mod p (p,q) = 1. qinv = 1/q mod p */
static GEN
Fl_chinese_coprime(GEN a, ulong b, GEN q, ulong p, ulong qinv, GEN pq)
{
  ulong d, amod = umodiu(a, p);
  pari_sp av = avma;
  GEN ax;

  if (b == amod) return NULL;
  d = (b > amod)? b - amod: p - (amod - b); /* (b - a) mod p */
  (void)new_chunk(lgefint(pq)<<1); /* HACK */
  ax = mului(Fl_mul(d,qinv,p), q); /* d mod p, 0 mod q */
  avma = av; return addii(a, ax); /* in ]-q, pq[ assuming a in -]-q,q[ */
}
GEN
Z_init_CRT(ulong Hp, ulong p) { return stoi(Fl_center(Hp, p, p>>1)); }
GEN
ZX_init_CRT(GEN Hp, ulong p, long v)
{
  long i, l = lg(Hp), lim = (long)(p>>1);
  GEN H = cgetg(l, t_POL);
  H[1] = evalsigne(1) | evalvarn(v);
  for (i=2; i<l; i++)
    gel(H,i) = stoi(Fl_center(Hp[i], p, lim));
  return H;
}

/* assume lg(Hp) > 1 */
GEN
ZM_init_CRT(GEN Hp, ulong p)
{
  long i,j, m = lg(Hp[1]), l = lg(Hp), lim = (long)(p>>1);
  GEN c,cp,H = cgetg(l, t_MAT);
  for (j=1; j<l; j++)
  {
    cp = gel(Hp,j);
    c = cgetg(m, t_COL);
    gel(H,j) = c;
    for (i=1; i<l; i++) gel(c,i) = stoi(Fl_center(cp[i],p, lim));
  }
  return H;
}

int
Z_incremental_CRT(GEN *H, ulong Hp, GEN q, GEN qp, ulong p)
{
  GEN h, lim = shifti(qp,-1);
  ulong qinv = Fl_inv(umodiu(q,p), p);
  int stable = 1;
  h = Fl_chinese_coprime(*H,Hp,q,p,qinv,qp);
  if (h)
  {
    if (cmpii(h,lim) > 0) h = subii(h,qp);
    *H = h; stable = 0;
  }
  return stable;
}

int
ZX_incremental_CRT(GEN *ptH, GEN Hp, GEN q, GEN qp, ulong p)
{
  GEN H = *ptH, h, lim = shifti(qp,-1);
  ulong qinv = Fl_inv(umodiu(q,p), p);
  long i, l = lg(H), lp = lg(Hp);
  int stable = 1;

  if (l < lp)
  { /* degree increases */
    GEN x = cgetg(lp, t_POL);
    for (i=1; i<l; i++)  x[i] = H[i];
    for (   ; i<lp; i++) gel(x,i) = gen_0;
    *ptH = H = x;
    stable = 0;
  } else if (l > lp)
  { /* degree decreases */
    GEN x = cgetg(l, t_VECSMALL);
    for (i=1; i<lp; i++)  x[i] = Hp[i];
    for (   ; i<l; i++) x[i] = 0;
    Hp = x; lp = l;
  }
  for (i=2; i<lp; i++)
  {
    h = Fl_chinese_coprime(gel(H,i),Hp[i],q,p,qinv,qp);
    if (h)
    {
      if (cmpii(h,lim) > 0) h = subii(h,qp);
      gel(H,i) = h; stable = 0;
    }
  }
  return stable;
}

int
ZM_incremental_CRT(GEN *pH, GEN Hp, GEN q, GEN qp, ulong p)
{
  GEN h, H = *pH, lim = shifti(qp,-1);
  ulong qinv = Fl_inv(umodiu(q,p), p);
  long i,j, l = lg(H), m = lg(H[1]);
  int stable = 1;
  for (j=1; j<l; j++)
    for (i=1; i<m; i++)
    {
      h = Fl_chinese_coprime(gcoeff(H,i,j), coeff(Hp,i,j),q,p,qinv,qp);
      if (h)
      {
        if (cmpii(h,lim) > 0) h = subii(h,qp);
        gcoeff(H,i,j) = h; stable = 0;
      }
    }
  return stable;
}

/* record the degrees of Euclidean remainders (make them as large as
 * possible : smaller values correspond to a degenerate sequence) */
static void
Flx_resultant_set_dglist(GEN a, GEN b, GEN dglist, ulong p)
{
  long da,db,dc, ind;
  pari_sp av = avma, lim = stack_lim(av, 2);

  if (lgpol(a)==0 || lgpol(b)==0) return;
  da = degpol(a);
  db = degpol(b);
  if (db > da)
  { swapspec(a,b, da,db); }
  else if (!da) return;
  ind = 0;
  while (db)
  {
    GEN c = Flx_rem(a,b, p);
    a = b; b = c; dc = degpol(c);
    if (dc < 0) break;

    ind++;
    if (dc > dglist[ind]) dglist[ind] = dc;
    if (low_stack(lim,stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"Flx_resultant_all");
      gerepileall(av, 2, &a,&b);
    }
    da = db; /* = degpol(a) */
    db = dc; /* = degpol(b) */
  }
  if (ind+1 > lg(dglist)) setlg(dglist,ind+1);
  avma = av; return;
}
/* assuming the PRS finishes on a degree 1 polynomial C0 + C1X, with
 * "generic" degree sequence as given by dglist, set *Ci and return
 * resultant(a,b). Modular version of Collins's subresultant */
static ulong
Flx_resultant_all(GEN a, GEN b, long *C0, long *C1, GEN dglist, ulong p)
{
  long da,db,dc, ind;
  ulong lb, res, g = 1UL, h = 1UL, ca = 1UL, cb = 1UL;
  int s = 1;
  pari_sp av = avma, lim = stack_lim(av,2);

  *C0 = 1; *C1 = 0;
  if (lgpol(a)==0 || lgpol(b)==0) return 0;
  da = degpol(a);
  db = degpol(b);
  if (db > da)
  {
    swapspec(a,b, da,db);
    if (both_odd(da,db)) s = -s;
  }
  else if (!da) return 1; /* = a[2] ^ db, since 0 <= db <= da = 0 */
  ind = 0;
  while (db)
  { /* sub-resultant algo., applied to ca * a and cb * b, ca,cb scalars,
     * da = deg a, db = deg b */
    GEN c = Flx_rem(a,b, p);
    long delta = da - db;

    if (both_odd(da,db)) s = -s;
    lb = Fl_mul(b[db+2], cb, p);
    a = b; b = c; dc = degpol(c);
    ind++;
    if (dc != dglist[ind]) { avma = av; return 0; } /* degenerates */
    if (g == h)
    { /* frequent */
      ulong cc = Fl_mul(ca, Fl_powu(Fl_div(lb,g,p), delta+1, p), p);
      ca = cb;
      cb = cc;
    }
    else
    {
      ulong cc = Fl_mul(ca, Fl_powu(lb, delta+1, p), p);
      ulong ghdelta = Fl_mul(g, Fl_powu(h, delta, p), p);
      ca = cb;
      cb = Fl_div(cc, ghdelta, p);
    }
    da = db; /* = degpol(a) */
    db = dc; /* = degpol(b) */

    g = lb;
    if (delta == 1)
      h = g; /* frequent */
    else
      h = Fl_mul(h, Fl_powu(Fl_div(g,h,p), delta, p), p);

    if (low_stack(lim,stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"Flx_resultant_all");
      gerepileall(av, 2, &a,&b);
    }
  }
  if (da > 1) return 0; /* Failure */
  /* last non-constant polynomial has degree 1 */
  *C0 = Fl_mul(ca, a[2], p);
  *C1 = Fl_mul(ca, a[3], p);
  res = Fl_mul(cb, b[2], p);
  if (s == -1) res = p - res;
  avma = av; return res;
}

/* u P(X) + v P(-X) */
static GEN
pol_comp(GEN P, GEN u, GEN v)
{
  long i, l = lg(P);
  GEN y = cgetg(l, t_POL);
  for (i=2; i<l; i++)
  {
    GEN t = gel(P,i);
    gel(y,i) = gequal0(t)? gen_0:
                         (i&1)? gmul(t, gsub(u,v)) /*  odd degree */
                              : gmul(t, gadd(u,v));/* even degree */
  }
  y[1] = P[1]; return normalizepol_lg(y,l);
}

GEN
polint_triv(GEN xa, GEN ya)
{
  GEN P = NULL, Q = roots_to_pol(xa,0);
  long i, n = lg(xa);
  pari_sp av = avma, lim = stack_lim(av, 2);
  for (i=1; i<n; i++)
  {
    GEN T, dP, r;
    if (gequal0(gel(ya,i))) continue;
    T = RgX_div_by_X_x(Q, gel(xa,i), NULL);
    r = poleval(T, gel(xa,i));
    if (i < n-1 && absi_equal(gel(xa,i), gel(xa,i+1)))
    { /* x_i = -x_{i+1} */
      dP = pol_comp(gdiv(T, r), gel(ya,i), gel(ya,i+1));
      i++;
    }
    else
      dP = gdiv(gmul(gel(ya,i), T), r);
    P = P? gadd(P, dP): dP;
    if (low_stack(lim,stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"polint_triv2 (i = %ld)",i);
      P = gerepileupto(av, P);
    }
  }
  return P? P: pol_0(0);
}

GEN
FpV_polint(GEN xa, GEN ya, GEN p, long v)
{
  GEN inv,T,dP, P = NULL, Q = FpV_roots_to_pol(xa, p, v);
  long i, n = lg(xa);
  pari_sp av, lim;
  av = avma; lim = stack_lim(av,2);
  for (i=1; i<n; i++)
  {
    if (!signe(ya[i])) continue;
    T = FpX_div_by_X_x(Q, gel(xa,i), p, NULL);
    inv = Fp_inv(FpX_eval(T,gel(xa,i), p), p);
    if (i < n-1 && equalii(addii(gel(xa,i), gel(xa,i+1)), p))
    {
      dP = pol_comp(T, Fp_mul(gel(ya,i),  inv,p),
                       Fp_mul(gel(ya,i+1),inv,p));
      i++; /* x_i = -x_{i+1} */
    }
    else
      dP = FpX_Fp_mul(T, Fp_mul(gel(ya,i),inv,p), p);
    P = P? FpX_add(P, dP, p): dP;
    if (low_stack(lim, stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpV_polint");
      if (!P) avma = av; else P = gerepileupto(av, P);
    }
  }
  return P? P: pol_0(v);
}

static void
Flv_polint_all(GEN xa, GEN ya, GEN C0, GEN C1, ulong p,
               GEN *pHp, GEN *pH0p, GEN *pH1p)
{
  GEN T,Q = Flv_roots_to_pol(xa, p, 0);
  GEN dP  = NULL,  P = NULL;
  GEN dP0 = NULL, P0= NULL;
  GEN dP1 = NULL, P1= NULL;
  long i, n = lg(xa);
  ulong inv;
  for (i=1; i<n; i++)
  {
    T = Flx_div_by_X_x(Q, xa[i], p, NULL);
    inv = Fl_inv(Flx_eval(T,xa[i], p), p);

    if (ya[i])
    {
      dP = Flx_Fl_mul(T, Fl_mul(ya[i],inv,p), p);
      P = P ? Flx_add(P , dP , p): dP;
    }
    if (C0[i])
    {
      dP0= Flx_Fl_mul(T, Fl_mul(C0[i],inv,p), p);
      P0= P0? Flx_add(P0, dP0, p): dP0;
    }
    if (C1[i])
    {
      dP1= Flx_Fl_mul(T, Fl_mul(C1[i],inv,p), p);
      P1= P1? Flx_add(P1, dP1, p): dP1;
    }
  }
  *pHp  = (P ? P : zero_Flx(0));
  *pH0p = (P0? P0: zero_Flx(0));
  *pH1p = (P1? P1: zero_Flx(0));
}

/* Q a vector of polynomials representing B in Fp[X][Y], evaluate at X = x,
 * Return 0 in case of degree drop. */
static GEN
FlxY_evalx_drop(GEN Q, ulong x, ulong p)
{
  GEN z;
  long i, lb = lg(Q);
  ulong leadz = Flx_eval(leading_term(Q), x, p);
  long vs=mael(Q,2,1);
  if (!leadz) return zero_Flx(vs);

  z = cgetg(lb, t_VECSMALL); z[1] = vs;
  for (i=2; i<lb-1; i++) z[i] = Flx_eval(gel(Q,i), x, p);
  z[i] = leadz; return z;
}

/* as above, but don't care about degree drop */
static GEN
FlxY_evalx(GEN Q, ulong x, ulong p)
{
  GEN z;
  long i, lb = lg(Q);
  z = cgetg(lb,t_VECSMALL); z[1]=mael(Q,2,1);
  for (i=2; i<lb; i++) z[i] = Flx_eval(gel(Q,i), x, p);
  return Flx_renormalize(z, lb);
}

/* Q an FpXY (t_POL with FpX coeffs), evaluate at X = x */
GEN
FpXY_evalx(GEN Q, GEN x, GEN p)
{
  long i, lb = lg(Q);
  GEN z;
  z = cgetg(lb, t_POL); z[1] = Q[1];
  for (i=2; i<lb; i++)
  {
    GEN q = gel(Q,i);
    gel(z,i) = typ(q) == t_INT? modii(q,p): FpX_eval(q, x, p);
  }
  return FpX_renormalize(z, lb);
}
/* Q an FpXY, evaluate at Y = y */
GEN
FpXY_evaly(GEN Q, GEN y, GEN p, long vx)
{
  pari_sp av = avma;
  long i, lb = lg(Q);
  GEN z;
  if (lb == 2) return pol_0(vx);
  z = gel(Q, lb-1);
  if (lb == 3 || !signe(y)) return typ(z)==t_INT? scalar_ZX(z, vx): ZX_copy(z);

  if (typ(z) == t_INT) z = scalar_ZX_shallow(z, vx);
  for (i=lb-2; i>=2; i--) z = Fq_add(gel(Q,i), FpX_Fp_mul(z, y, p), NULL, p);
  return gerepileupto(av, z);
}
/* Q an FpXY, evaluate at (X,Y) = (x,y) */
GEN
FpXY_eval(GEN Q, GEN y, GEN x, GEN p)
{
  pari_sp av = avma;
  return gerepileuptoint(av, FpX_eval(FpXY_evalx(Q, x, p), y, p));
}

static GEN
ZX_norml1(GEN x)
{
  long i, l = lg(x);
  GEN s;

  if (l == 2) return gen_0;
  s = gel(x, l-1); /* != 0 */
  for (i = l-2; i > 1; i--) {
    GEN xi = gel(x,i);
    if (!signe(x)) continue;
    s = addii_sign(s,1, xi,1);
  }
  return s;
}

/* Interpolate at roots of 1 and use Hadamard bound for univariate resultant:
 *   bound = N_2(A)^degpol B N_2(B)^degpol(A),  where
 *     N_2(A) = sqrt(sum (N_1(Ai))^2)
 * Return e such that Res(A, B) < 2^e */
ulong
ZX_ZXY_ResBound(GEN A, GEN B, GEN dB)
{
  pari_sp av = avma;
  GEN a = gen_0, b = gen_0;
  long i , lA = lg(A), lB = lg(B);
  double loga, logb;
  for (i=2; i<lA; i++) a = addii(a, sqri(gel(A,i)));
  for (i=2; i<lB; i++)
  {
    GEN t = gel(B,i);
    if (typ(t) == t_POL) t = ZX_norml1(t);
    b = addii(b, sqri(t));
  }
  loga = dbllog2(a);
  logb = dbllog2(b); if (dB) logb -= 2 * dbllog2(dB);
  i = (long)((degpol(B) * loga + degpol(A) * logb) / 2);
  avma = av; return (i <= 0)? 1: 1 + (ulong)i;
}

/* return Res(a(Y), b(n,Y)) over Fp. la = leading_term(a) [for efficiency] */
static ulong
Flx_FlxY_eval_resultant(GEN a, GEN b, ulong n, ulong p, ulong la)
{
  GEN ev = FlxY_evalx(b, n, p);
  long drop = lg(b) - lg(ev);
  ulong r = Flx_resultant(a, ev, p);
  if (drop && la != 1) r = Fl_mul(r, Fl_powu(la, drop,p),p);
  return r;
}
static GEN
FpX_FpXY_eval_resultant(GEN a, GEN b, GEN n, GEN p, GEN la)
{
  GEN ev = FpXY_evalx(b, n, p);
  long drop=lg(b)-lg(ev);
  GEN r = FpX_resultant(a, ev, p);
  if (drop && !gequal1(la)) r = Fp_mul(r, Fp_powu(la, drop,p),p);
  return r;
}

/* assume dres := deg(Res_X(a,b), Y) <= deg(a,X) * deg(b,Y) < p */
/* Return a Fly */
static GEN
Flx_FlyX_resultant_polint(GEN a, GEN b, ulong p, ulong dres, long sx)
{
  ulong i, n, la = (ulong)leading_term(a);
  GEN  x = cgetg(dres+2, t_VECSMALL);
  GEN  y = cgetg(dres+2, t_VECSMALL);
 /* Evaluate at dres+ 1 points: 0 (if dres even) and +/- n, so that P_n(X) =
  * P_{-n}(-X), where P_i is Lagrange polynomial: P_i(j) = delta_{i,j} */
  for (i=0,n = 1; i < dres; n++)
  {
    x[++i] = n;   y[i] = Flx_FlxY_eval_resultant(a,b, x[i], p,la);
    x[++i] = p-n; y[i] = Flx_FlxY_eval_resultant(a,b, x[i], p,la);
  }
  if (i == dres)
  {
    x[++i] = 0;   y[i] = Flx_FlxY_eval_resultant(a,b, x[i], p,la);
  }
  return Flv_polint(x,y, p, sx);
}

static GEN
FlxX_pseudorem(GEN x, GEN y, ulong p)
{
  long vx = varn(x), dx, dy, dz, i, lx, dp;
  pari_sp av = avma, av2, lim;

  if (!signe(y)) pari_err(gdiver);
  (void)new_chunk(2);
  dx=degpol(x); x = RgX_recip_shallow(x)+2;
  dy=degpol(y); y = RgX_recip_shallow(y)+2; dz=dx-dy; dp = dz+1;
  av2 = avma; lim = stack_lim(av2,1);
  for (;;)
  {
    gel(x,0) = Flx_neg(gel(x,0), p); dp--;
    for (i=1; i<=dy; i++)
      gel(x,i) = Flx_add( Flx_mul(gel(y,0), gel(x,i), p),
                              Flx_mul(gel(x,0), gel(y,i), p), p );
    for (   ; i<=dx; i++)
      gel(x,i) = Flx_mul(gel(y,0), gel(x,i), p);
    do { x++; dx--; } while (dx >= 0 && lg(gel(x,0))==2);
    if (dx < dy) break;
    if (low_stack(lim,stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"FlxX_pseudorem dx = %ld >= %ld",dx,dy);
      gerepilecoeffs(av2,x,dx+1);
    }
  }
  if (dx < 0) return zero_Flx(0);
  lx = dx+3; x -= 2;
  x[0]=evaltyp(t_POL) | evallg(lx);
  x[1]=evalsigne(1) | evalvarn(vx);
  x = RgX_recip_shallow(x);
  if (dp)
  { /* multiply by y[0]^dp   [beware dummy vars from FpX_FpXY_resultant] */
    GEN t = Flx_pow(gel(y,0), dp, p);
    for (i=2; i<lx; i++)
      gel(x,i) = Flx_mul(gel(x,i), t, p);
  }
  return gerepilecopy(av, x);
}

/* return a Flx */
GEN
FlxX_resultant(GEN u, GEN v, ulong p, long sx)
{
  pari_sp av = avma, av2, lim;
  long degq,dx,dy,du,dv,dr,signh;
  GEN z,g,h,r,p1;

  dx=degpol(u); dy=degpol(v); signh=1;
  if (dx < dy)
  {
    swap(u,v); lswap(dx,dy);
    if (both_odd(dx, dy)) signh = -signh;
  }
  if (dy < 0) return zero_Flx(sx);
  if (dy==0) return gerepileupto(av, Flx_pow(gel(v,2),dx,p));

  g = h = pol1_Flx(sx); av2 = avma; lim = stack_lim(av2,1);
  for(;;)
  {
    r = FlxX_pseudorem(u,v,p); dr = lg(r);
    if (dr == 2) { avma = av; return zero_Flx(sx); }
    du = degpol(u); dv = degpol(v); degq = du-dv;
    u = v; p1 = g; g = leading_term(u);
    switch(degq)
    {
      case 0: break;
      case 1:
        p1 = Flx_mul(h,p1, p); h = g; break;
      default:
        p1 = Flx_mul(Flx_pow(h,degq,p), p1, p);
        h = Flx_div(Flx_pow(g,degq,p), Flx_pow(h,degq-1,p), p);
    }
    if (both_odd(du,dv)) signh = -signh;
    v = FlxY_Flx_div(r, p1, p);
    if (dr==3) break;
    if (low_stack(lim,stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"resultant_all, dr = %ld",dr);
      gerepileall(av2,4, &u, &v, &g, &h);
    }
  }
  z = gel(v,2);
  if (dv > 1) z = Flx_div(Flx_pow(z,dv,p), Flx_pow(h,dv-1,p), p);
  if (signh < 0) z = Flx_neg(z,p);
  return gerepileupto(av, z);
}

/* Warning:
 * This function switches between valid and invalid variable ordering*/

static GEN
FlxY_to_FlyX(GEN b, long sv)
{
  long i, n=-1;
  long sw = b[1]&VARNBITS;
  for(i=2;i<lg(b);i++) n = maxss(n,lgpol(gel(b,i)));
  return Flm_to_FlxX(Flm_transpose(FlxX_to_Flm(b,n)),sv,sw);
}

/* Return a Fly*/
GEN
Flx_FlxY_resultant(GEN a, GEN b, ulong pp)
{
  pari_sp ltop=avma;
  long dres = degpol(a)*degpol(b);
  long sx=a[1], sy=b[1]&VARNBITS;
  GEN z;
  b = FlxY_to_FlyX(b,sx);
  if ((ulong)dres >= pp)
    z = FlxX_resultant(Fly_to_FlxY(a, sy), b, pp, sx);
  else
    z = Flx_FlyX_resultant_polint(a, b, pp, (ulong)dres, sy);
  return gerepileupto(ltop,z);
}

/* return a t_POL (in variable v) whose coeffs are the coeffs of b,
 * in variable v. This is an incorrect PARI object if initially varn(b) << v.
 * We could return a vector of coeffs, but it is convenient to have degpol()
 * and friends available. Even in that case, it will behave nicely with all
 * functions treating a polynomial as a vector of coeffs (eg poleval).
 * FOR INTERNAL USE! */
GEN
swap_vars(GEN b0, long v)
{
  long i, n = poldegree(b0, v);
  GEN b, x;
  if (n < 0) return pol_0(v);
  b = cgetg(n+3, t_POL); x = b + 2;
  b[1] = evalsigne(1) | evalvarn(v);
  for (i=0; i<=n; i++) gel(x,i) = polcoeff_i(b0, i, v);
  return b;
}

/* assume varn(b) << varn(a) */
/* return a FpY*/
GEN
FpX_FpXY_resultant(GEN a, GEN b, GEN p)
{
  long i,n,dres, vX = varn(b), vY = varn(a);
  GEN la,x,y;

  if (lgefint(p) == 3)
  {
    ulong pp = (ulong)p[2];
    b = ZXX_to_FlxX(b, pp, vY);
    a = ZX_to_Flx(a, pp);
    x = Flx_FlxY_resultant(a, b, pp);
    return Flx_to_ZX(x);
  }
  dres = degpol(a)*degpol(b);
  b = swap_vars(b, vY);
  la = leading_term(a);
  x = cgetg(dres+2, t_VEC);
  y = cgetg(dres+2, t_VEC);
 /* Evaluate at dres+ 1 points: 0 (if dres even) and +/- n, so that P_n(X) =
  * P_{-n}(-X), where P_i is Lagrange polynomial: P_i(j) = delta_{i,j} */
  for (i=0,n = 1; i < dres; n++)
  {
    gel(x,++i) = utoipos(n);
    gel(y,i) = FpX_FpXY_eval_resultant(a,b,gel(x,i),p,la);
    gel(x,++i) = subis(p,n);
    gel(y,i) = FpX_FpXY_eval_resultant(a,b,gel(x,i),p,la);
  }
  if (i == dres)
  {
    gel(x,++i) = gen_0;
    gel(y,i) = FpX_FpXY_eval_resultant(a,b, gel(x,i), p,la);
  }
  return FpV_polint(x,y, p, vX);
}

GEN
FpX_direct_compositum(GEN A, GEN B, GEN p)
{
  GEN a, b, x;
  a = leafcopy(A); setvarn(a, MAXVARN);
  b = leafcopy(B); setvarn(b, MAXVARN);
  x = deg1pol_shallow(gen_1, pol_x(MAXVARN), 0); /* x + y */
  return FpX_FpXY_resultant(a, poleval(b,x),p);
}

/* 0, 1, -1, 2, -2, ... */
#define next_lambda(a) (a>0 ? -a : 1-a)
GEN
FpX_compositum(GEN A, GEN B, GEN p)
{
  GEN a, b;
  long k;
  a = leafcopy(A); setvarn(a, MAXVARN);
  b = leafcopy(B); setvarn(b, MAXVARN);
  for (k = 1;; k = next_lambda(k))
  {
    GEN x = deg1pol_shallow(gen_1, gmulsg(k, pol_x(MAXVARN)), 0); /* x + k y */
    GEN C = FpX_FpXY_resultant(a, poleval(b,x),p);
    if (FpX_is_squarefree(C, p)) return C;
  }
}

/* check that theta(maxprime) - theta(27448) >= 2^bound */
/* NB: theta(27449) ~ 27225.387, theta(x) > 0.98 x for x>7481
 * (Schoenfeld, 1976 for x > 1155901 + direct calculations) */
static void
check_theta(ulong bound) {
  maxprime_check( (ulong)ceil((bound * LOG2 + 27225.388) / 0.98) );
}
/* 27449 = prime(3000) */
byteptr
init_modular(ulong *p) { *p = 27449; return diffptr + 3000; }

/* Assume A in Z[Y], B in Q[Y][X], and Res_Y(A, B) in Z[X].
 * If lambda = NULL, return Res_Y(A,B).
 * Otherwise, find a small lambda (start from *lambda, use the sequence above)
 * such that R(X) = Res_Y(A(Y), B(X + lambda Y)) is squarefree, reset *lambda
 * to the chosen value and return R
 *
 * If LERS is non-NULL, set it to the Last non-constant polynomial in the
 * Euclidean Remainder Sequence */
GEN
ZX_ZXY_resultant_all(GEN A, GEN B0, long *plambda, GEN *LERS)
{
  int checksqfree = plambda? 1: 0, delvar = 0, stable;
  long lambda = plambda? *plambda: 0;
  ulong bound, p, dp;
  pari_sp av = avma, av2 = 0, lim;
  long i,n, lb, degA = degpol(A), dres = degA*degpol(B0);
  long vX = varn(B0), vY = varn(A); /* assume vX << vY */
  long sX = evalvarn(vX);
  GEN x, y, dglist, dB, B, q, a, b, ev, H, H0, H1, Hp, H0p, H1p, C0, C1, L;
  byteptr d = init_modular(&p);

  dglist = Hp = H0p = H1p = C0 = C1 = NULL; /* gcc -Wall */
  if (LERS)
  {
    if (!checksqfree)
      pari_err(talker,"ZX_ZXY_resultant_all: LERS != NULL needs lambda");
    C0 = cgetg(dres+2, t_VECSMALL);
    C1 = cgetg(dres+2, t_VECSMALL);
    dglist = cgetg(dres+1, t_VECSMALL);
  }
  x = cgetg(dres+2, t_VECSMALL);
  y = cgetg(dres+2, t_VECSMALL);
  if (vY == MAXVARN)
  {
    vY = fetch_var(); delvar = 1;
    B0 = gsubst(B0, MAXVARN, pol_x(vY));
    A = leafcopy(A); setvarn(A, vY);
  }
  L = pol_x(MAXVARN);
  B0 = Q_remove_denom(B0, &dB);
  lim = stack_lim(av,2);

  /* make sure p large enough */
  while (p < (ulong)(dres<<1)) NEXT_PRIME_VIADIFF(p,d);

INIT:
  /* allways except the first time */
  if (av2) { avma = av2; lambda = next_lambda(lambda); }
  if (checksqfree)
  {
    /* # + lambda */
    L = deg1pol_shallow(stoi(lambda), pol_x(MAXVARN), vY);
    if (DEBUGLEVEL>4) err_printf("Trying lambda = %ld\n", lambda);
  }
  B = poleval(B0, L); av2 = avma;

  if (degA <= 3)
  { /* sub-resultant faster for small degrees */
    if (LERS)
    { /* implies checksqfree */
      H = resultant_all(A,B,&q);
      if (typ(q) != t_POL || degpol(q)!=1) goto INIT;
      H0 = gel(q,2);
      if (typ(H0) == t_POL) setvarn(H0,vX); else H0 = scalarpol(H0,vX);
      H1 = gel(q,3);
      if (typ(H1) == t_POL) setvarn(H1,vX); else H1 = scalarpol(H1,vX);
    }
    else
      H = resultant(A,B);
    if (checksqfree && !ZX_is_squarefree(H)) goto INIT;
    goto END;
  }

  H = H0 = H1 = NULL;
  lb = lg(B);
  bound = ZX_ZXY_ResBound(A, B, dB);
  if (DEBUGLEVEL>4) err_printf("bound for resultant coeffs: 2^%ld\n",bound);
  check_theta(bound);

  dp = 1;
  for(;;)
  {
    NEXT_PRIME_VIADIFF_CHECK(p,d);
    if (dB) { dp = smodis(dB, p); if (!dp) continue; }

    a = ZX_to_Flx(A, p);
    b = ZXX_to_FlxX(B, p, varn(A));
    if (LERS)
    {
      if (degpol(a) < degA || lg(b) < lb) continue; /* p | lc(A)lc(B) */
      if (checksqfree)
      { /* find degree list for generic Euclidean Remainder Sequence */
        long goal = minss(degpol(a), degpol(b)); /* longest possible */
        for (n=1; n <= goal; n++) dglist[n] = 0;
        setlg(dglist, 1);
        for (n=0; n <= dres; n++)
        {
          ev = FlxY_evalx_drop(b, n, p);
          Flx_resultant_set_dglist(a, ev, dglist, p);
          if (lg(dglist)-1 == goal) break;
        }
        /* last pol in ERS has degree > 1 ? */
        goal = lg(dglist)-1;
        if (degpol(B) == 1) { if (!goal) goto INIT; }
        else
        {
          if (goal <= 1) goto INIT;
          if (dglist[goal] != 0 || dglist[goal-1] != 1) goto INIT;
        }
        if (DEBUGLEVEL>4)
          err_printf("Degree list for ERS (trials: %ld) = %Ps\n",n+1,dglist);
      }

      for (i=0,n = 0; i <= dres; n++)
      {
        ev = FlxY_evalx_drop(b, n, p);
        x[++i] = n; y[i] = Flx_resultant_all(a, ev, C0+i, C1+i, dglist, p);
        if (!C1[i]) i--; /* C1(i) = 0. No way to recover C0(i) */
      }
      Flv_polint_all(x,y,C0,C1, p, &Hp, &H0p, &H1p);
    }
    else
    {
      long dropa = degA - degpol(a), dropb = lb - lg(b);
      Hp = Flx_FlyX_resultant_polint(a, b, p, (ulong)dres, sX);
      if (dropa && dropb)
        Hp = zero_Flx(sX);
      else {
        if (dropa)
        { /* multiply by ((-1)^deg B lc(B))^(deg A - deg a) */
          GEN c = gel(b,lb-1); /* lc(B) */
          if (!odd(lb)) c = Flx_neg(c, p); /* deg B = lb - 3 */
          if (!Flx_equal1(c)) {
            c = Flx_pow(c, dropa, p);
            if (!Flx_equal1(c)) Hp = Flx_mul(Hp, c, p);
          }
        }
        else if (dropb)
        { /* multiply by lc(A)^(deg B - deg b) */
          ulong c = a[degA+2]; /* lc(A) */
          c = Fl_powu(c, dropb, p);
          if (c != 1) Hp = Flx_Fl_mul(Hp, c, p);
        }
      }
    }
    if (!H && degpol(Hp) != dres) continue;
    if (dp != 1) Hp = Flx_Fl_mul(Hp, Fl_powu(Fl_inv(dp,p), degA, p), p);
    if (checksqfree) {
      if (!Flx_is_squarefree(Hp, p)) goto INIT;
      if (DEBUGLEVEL>4) err_printf("Final lambda = %ld\n", lambda);
      checksqfree = 0;
    }

    if (!H)
    { /* initialize */
      q = utoipos(p); stable = 0;
      H = ZX_init_CRT(Hp, p,vX);
      if (LERS) {
        H0= ZX_init_CRT(H0p, p,vX);
        H1= ZX_init_CRT(H1p, p,vX);
      }
    }
    else
    {
      GEN qp = muliu(q,p);
      stable = ZX_incremental_CRT(&H, Hp, q,qp, p);
      if (LERS) {
        stable &= ZX_incremental_CRT(&H0,H0p, q,qp, p);
        stable &= ZX_incremental_CRT(&H1,H1p, q,qp, p);
      }
      q = qp;
    }
    /* could make it probabilistic for H ? [e.g if stable twice, etc]
     * Probabilistic anyway for H0, H1 */
    if (DEBUGLEVEL>5)
      err_printf("resultant mod %ld (bound 2^%ld, stable=%ld)", p,expi(q),stable);
    if (stable && (ulong)expi(q) >= bound) break; /* DONE */
    if (low_stack(lim, stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ZX_ZXY_rnfequation");
      gerepileall(av2, LERS? 4: 2, &H, &q, &H0, &H1);
    }
  }
END:
  setvarn(H, vX); if (delvar) (void)delete_var();
  if (plambda) *plambda = lambda;
  if (LERS)
  {
    *LERS = mkvec2(H0,H1);
    gerepileall(av, 2, &H, LERS);
    return H;
  }
  return gerepilecopy(av, H);
}

GEN
ZX_ZXY_rnfequation(GEN A, GEN B, long *lambda)
{
  return ZX_ZXY_resultant_all(A, B, lambda, NULL);
}

/* If lambda = NULL, return caract(Mod(A, T)), T,A in Z[X].
 * Otherwise find a small lambda such that caract (Mod(A + lambda X, T)) is
 * squarefree */
GEN
ZXQ_charpoly_sqf(GEN A, GEN T, long *lambda, long v)
{
  pari_sp av = avma;
  GEN R, a;
  long dA;
  int delvar;

  if (v < 0) v = 0;
  switch (typ(A))
  {
    case t_POL: dA = degpol(A); if (dA > 0) break;
      A = dA? gel(A,2): gen_0; /* fall through */
    default:
      if (lambda) { A = scalar_ZX_shallow(A,varn(T)); dA = 0; break;}
      return gerepileupto(av, gpowgs(gsub(pol_x(v), A), degpol(T)));
  }
  delvar = 0;
  if (varn(T) == 0)
  {
    long v0 = fetch_var(); delvar = 1;
    T = leafcopy(T); setvarn(T,v0);
    A = leafcopy(A); setvarn(A,v0);
  }
  R = ZX_ZXY_rnfequation(T, deg1pol_shallow(gen_1, gneg_i(A), 0), lambda);
  if (delvar) (void)delete_var();
  setvarn(R, v); a = leading_term(T);
  if (!gequal1(a)) R = gdiv(R, powiu(a, dA));
  return gerepileupto(av, R);
}


/* charpoly(Mod(A,T)), A may be in Q[X], but assume T and result are integral */
GEN
ZXQ_charpoly(GEN A, GEN T, long v)
{
  return (degpol(T) < 16) ? RgXQ_charpoly(A,T,v): ZXQ_charpoly_sqf(A,T, NULL, v);
}

static GEN
trivial_case(GEN A, GEN B)
{
  long d;
  if (typ(A) == t_INT) return powiu(A, degpol(B));
  d = degpol(A);
  if (d == 0) return trivial_case(gel(A,2),B);
  if (d < 0) return gen_0;
  return NULL;
}

/* floating point resultant */
static GEN
fp_resultant(GEN a, GEN b)
{
  long da, db, dc;
  GEN res = gen_1;
  pari_sp av, lim;

  if (lgpol(a)==0 || lgpol(b)==0) return gen_0;
  da = degpol(a);
  db = degpol(b);
  if (db > da)
  {
    swapspec(a,b, da,db);
    if (both_odd(da,db)) res = gneg(res);
  }
  else if (!da) return gen_1; /* = res * a[2] ^ db, since 0 <= db <= da = 0 */
  av = avma; lim = stack_lim(av, 1);
  while (db)
  {
    GEN lb = gel(b,db+2), c = RgX_rem(a,b);
    c = normalizepol_approx(c, lg(c)); /* kill leading zeroes without warning */
    a = b; b = c; dc = degpol(c);
    if (dc < 0) { avma = av; return gen_0; }

    if (both_odd(da,db)) res = gneg(res);
    res = gmul(res, gpowgs(lb, da - dc));
    if (low_stack(lim, stack_lim(av,1))) {
      if (DEBUGMEM>1) pari_warn(warnmem,"fp_resultant");
      gerepileall(av, 3, &a,&b,&res);
    }
    da = db; /* = degpol(a) */
    db = dc; /* = degpol(b) */
  }
  return gerepileupto(av, gmul(res, gpowgs(gel(b,2), da)));
}

/* Res(A, B/dB), assuming the A,B in Z[X] and result is integer */
GEN
ZX_resultant_all(GEN A, GEN B, GEN dB, ulong bound)
{
  ulong Hp, dp, p;
  pari_sp av = avma, av2, lim;
  long degA, degB;
  int stable;
  GEN q, a, b, H;
  byteptr d;

  if ((H = trivial_case(A,B)) || (H = trivial_case(B,A))) return H;
  q = H = NULL;
  av2 = avma; lim = stack_lim(av,2);
  degA = degpol(A);
  degB = degpol(B);
  if (!bound)
  {
    bound = ZX_ZXY_ResBound(A, B, dB);
    if (bound > 10000)
    {
      const long CNTMAX = 5; /* to avoid oo loops if R = 0 */
      long bnd = 0, cnt;
      long prec = nbits2prec( maxss(gexpo(A), gexpo(B)) + 1 );
      for(cnt = 1; cnt < CNTMAX; cnt++, prec = (prec-1)<<1)
      {
        GEN R = fp_resultant(RgX_gtofp(A, prec), RgX_gtofp(B, prec));
        bnd = gexpo(R) + 1;
        if (bnd >= 0 && bnd <= (long)bound && !gequal0(R)) break;
      }
      if (cnt < CNTMAX) bound = bnd;
      if (dB) bound -= (long)(dbllog2(dB)*degA);
    }
  }
  if (DEBUGLEVEL>4) err_printf("bound for resultant: 2^%ld\n",bound);
  d = init_modular(&p);
  check_theta(bound);

  dp = 1; /* denominator mod p */
  for(;;)
  {
    long dropa, dropb;
    NEXT_PRIME_VIADIFF_CHECK(p,d);
    if (dB) { dp = smodis(dB, p); if (!dp) continue; }

    a = ZX_to_Flx(A, p); dropa = degA - degpol(a);
    b = ZX_to_Flx(B, p); dropb = degB - degpol(b);
    if (dropa && dropb) /* p | lc(A), p | lc(B) */
      Hp = 0;
    else
    {
      Hp = Flx_resultant(a, b, p);
      if (dropa)
      { /* multiply by ((-1)^deg B lc(B))^(deg A - deg a) */
        ulong c = b[degB+2]; /* lc(B) */
        if (odd(degB)) c = p - c;
        c = Fl_powu(c, dropa, p);
        if (c != 1) Hp = Fl_mul(Hp, c, p);
      }
      else if (dropb)
      { /* multiply by lc(A)^(deg B - deg b) */
        ulong c = a[degA+2]; /* lc(A) */
        c = Fl_powu(c, dropb, p);
        if (c != 1) Hp = Fl_mul(Hp, c, p);
      }
      if (dp != 1) Hp = Fl_mul(Hp, Fl_powu(Fl_inv(dp,p), degA, p), p);
    }

    if (!H)
    {
      stable = 0; q = utoipos(p);
      H = Z_init_CRT(Hp, p);
    }
    else /* could make it probabilistic ??? [e.g if stable twice, etc] */
    {
      GEN qp = muliu(q,p);
      stable = Z_incremental_CRT(&H, Hp, q,qp, p);
      q = qp;
    }
    if (DEBUGLEVEL>5)
      err_printf("resultant mod %ld (bound 2^%ld, stable = %d)",p,expi(q),stable);
    if (stable && (ulong)expi(q) >= bound) break; /* DONE */
    if (low_stack(lim, stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ZX_resultant");
      gerepileall(av2, 2, &H,&q);
    }
  }
  return gerepileuptoint(av, icopy(H));
}

/* A0 and B0 in Q[X] */
GEN
QX_resultant(GEN A0, GEN B0)
{
  GEN s, a, b, A, B;
  pari_sp av = avma;

  A = Q_primitive_part(A0, &a);
  B = Q_primitive_part(B0, &b);
  s = ZX_resultant(A, B);
  if (!signe(s)) { avma = av; return gen_0; }
  if (a) s = gmul(s, gpowgs(a,degpol(B)));
  if (b) s = gmul(s, gpowgs(b,degpol(A)));
  return gerepileupto(av, s);
}

GEN
ZX_resultant(GEN A, GEN B) { return ZX_resultant_all(A,B,NULL,0); }

GEN
QXQ_intnorm(GEN A, GEN B)
{
  GEN c, n, R, lB;
  long dA = degpol(A), dB = degpol(B);
  pari_sp av = avma;
  if (dA < 0) return gen_0;
  A = Q_primitive_part(A, &c);
  if (!c || typ(c) == t_INT) {
    n = c;
    R = ZX_resultant(B, A);
  } else {
    n = gel(c,1);
    R = ZX_resultant_all(B, A, gel(c,2), 0);
  }
  if (n && !equali1(n)) R = mulii(R, powiu(n, dB));
  lB = leading_term(B);
  if (!equali1(lB)) R = diviiexact(R, powiu(lB, dA));
  return gerepileuptoint(av, R);
}

GEN
QXQ_norm(GEN A, GEN B)
{
  GEN c, R, lB;
  long dA = degpol(A), dB = degpol(B);
  pari_sp av = avma;
  if (dA < 0) return gen_0;
  A = Q_primitive_part(A, &c);
  R = ZX_resultant(B, A);
  if (c) R = gmul(R, gpowgs(c, dB));
  lB = leading_term(B);
  if (!equali1(lB)) R = gdiv(R, gpowgs(lB, dA));
  return gerepileupto(av, R);
}

/* assume x has integral coefficients */
GEN
ZX_disc_all(GEN x, ulong bound)
{
  pari_sp av = avma;
  GEN l, R;
  long s, d = degpol(x);
  if (d <= 1) return d ? gen_1: gen_0;
  s = (d & 2) ? -1: 1;
  l = leading_term(x);
  R = ZX_resultant_all(x, ZX_deriv(x), NULL, bound);
  if (is_pm1(l))
  { if (signe(l) < 0) s = -s; }
  else
    R = diviiexact(R,l);
  if (s == -1) togglesign_safe(&R);
  return gerepileuptoint(av,R);
}
GEN ZX_disc(GEN x) { return ZX_disc_all(x,0); }

GEN
QX_disc(GEN x)
{
  pari_sp av = avma;
  GEN c, d = ZX_disc( Q_primitive_part(x, &c) );
  if (c) d = gmul(d, gpowgs(c, 2*degpol(x) - 2));
  return gerepileupto(av, d);
}

/* lift(1 / Mod(A,B)). B a ZX, A a scalar or a QX */
GEN
QXQ_inv(GEN A, GEN B)
{
  GEN D, cU, q, U, V;
  ulong p;
  pari_sp av2, av = avma, avlim = stack_lim(av, 1);
  byteptr d;

  if (is_scalar_t(typ(A))) return scalarpol(ginv(A), varn(B));
  /* A a QX, B a ZX */
  if (degpol(A) < 15) return RgXQ_inv(A,B);
  A = Q_primitive_part(A, &D);
  /* A, B in Z[X] */
  av2 = avma; U = NULL;
  d = init_modular(&p);
  for(;;)
  {
    GEN a, b, qp, Up, Vp;
    int stable;

    NEXT_PRIME_VIADIFF_CHECK(p,d);
    a = ZX_to_Flx(A, p);
    b = ZX_to_Flx(B, p);
    /* if p | Res(A/G, B/G), discard */
    if (!Flx_extresultant(b,a,p, &Vp,&Up)) continue;

    if (!U)
    { /* First time */
      U = ZX_init_CRT(Up,p,varn(A));
      V = ZX_init_CRT(Vp,p,varn(A));
      q = utoipos(p); continue;
    }
    if (DEBUGLEVEL>5) err_printf("QXQ_inv: mod %ld (bound 2^%ld)", p,expi(q));
    qp = muliu(q,p);
    stable = ZX_incremental_CRT(&U, Up, q,qp, p);
    stable&= ZX_incremental_CRT(&V, Vp, q,qp, p);
    if (stable)
    { /* all stable: check divisibility */
      GEN res = ZX_add(ZX_mul(A,U), ZX_mul(B,V));
      if (degpol(res) == 0) {
        res = gel(res,2);
        D = D? gmul(D, res): res;
        break;
      } /* DONE */
      if (DEBUGLEVEL) err_printf("QXQ_inv: char 0 check failed");
    }
    q = qp;
    if (low_stack(avlim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"QXQ_inv");
      gerepileall(av2, 3, &q,&U,&V);
    }
  }
  cU = ZX_content(U);
  if (!is_pm1(cU)) { U = Q_div_to_int(U, cU); D = gdiv(D, cU); }
  return gerepileupto(av, RgX_Rg_div(U, D));
}

/************************************************************************
 *                                                                      *
 *                   IRREDUCIBLE POLYNOMIAL / Fp                        *
 *                                                                      *
 ************************************************************************/

/* irreducible (unitary) polynomial of degree n over Fp */
GEN
ffinit_rand(GEN p,long n)
{
  for(;;) {
    pari_sp av = avma;
    GEN pol = ZX_add(monomial(gen_1, n, 0), random_FpX(n-1,0, p));
    if (FpX_is_irred(pol, p)) return pol;
    avma = av;
  }
}

/* return an extension of degree 2^l of F_2, assume l > 0
 * Not stack clean. */
static GEN
f2init(long l)
{
  long i;
  GEN Q, T, S;

  if (l == 1) return polcyclo(3, MAXVARN);

  S = mkpoln(4, gen_1,gen_1,gen_0,gen_0); /* y(y^2 + y) */
  setvarn(S, MAXVARN);
  Q = mkpoln(3, gen_1,gen_1, S); /* x^2 + x + y(y^2+y) */

  /* x^4+x+1, irred over F_2, minimal polynomial of a root of Q */
  T = mkpoln(5, gen_1,gen_0,gen_0,gen_1,gen_1);
  for (i=2; i<l; i++)
  { /* Q = x^2 + x + a(y) irred. over K = F2[y] / (T(y))
     * ==> x^2 + x + a(y) b irred. over K for any root b of Q
     * ==> x^2 + x + (b^2+b)b */
    setvarn(T,MAXVARN);
    T = FpX_FpXY_resultant(T, Q, gen_2); /* = minpoly of b over F2 */
  }
  return T;
}

/* return an extension of degree p^l of F_p, assume l > 0
 * Not stack clean. */
GEN
ffinit_Artin_Shreier(GEN ip, long l)
{
  long i, p = itos(ip);
  GEN T, Q, xp = monomial(gen_1,p,0); /* x^p */
  T = ZX_sub(xp, deg1pol_shallow(gen_1,gen_1,0)); /* x^p - x - 1 */
  if (l == 1) return T;

  Q = ZX_sub(monomial(gen_1,2*p-1,MAXVARN), monomial(gen_1,p,MAXVARN));
  Q = gsub(xp, deg1pol_shallow(gen_1, Q, 0)); /* x^p - x - (y^(2p-1)-y^p) */
  for (i = 2; i <= l; ++i)
  {
    setvarn(T,MAXVARN);
    T = FpX_FpXY_resultant(T, Q, ip);
  }
  return T;
}

/* check if polsubcyclo(n,l,0) is irreducible modulo p */
static long
fpinit_check(GEN p, long n, long l)
{
  ulong q;
  if (!uisprime(n)) return 0;
  q = umodiu(p,n); if (!q) return 0;
  return cgcd((n-1)/Fl_order(q, n-1, n), l) == 1;
}

/* let k=2 if p%4==1, and k=4 else and assume k*p does not divide l.
 * Return an irreducible polynomial of degree l over F_p.
 * Variant of Adleman and Lenstra "Finding irreducible polynomials over
 * finite fields", ACM, 1986 (5) 350--355.
 * Not stack clean */
static GEN
fpinit(GEN p, long l)
{
  ulong n = 1+l;
  while (!fpinit_check(p,n,l)) n += l;
  if (DEBUGLEVEL>=4) err_printf("FFInit: using polsubcyclo(%ld, %ld)\n",n,l);
  return FpX_red(polsubcyclo(n,l,0),p);
}

static GEN
ffinit_fact(GEN p, long n)
{
  GEN P, F = gel(factoru_pow(n),3);
  long i;
  if (!odd(n) && equaliu(p, 2))
    P = f2init(vals(n)); /* if n is even, F[1] = 2^vals(n)*/
  else
    P = fpinit(p, F[1]);
  for (i = 2; i < lg(F); ++i)
    P = FpX_direct_compositum(fpinit(p, F[i]), P, p);
  return P;
}

static GEN
ffinit_nofact(GEN p, long n)
{
  GEN P, Q = NULL;
  if (lgefint(p)==3)
  {
    ulong pp = p[2], q;
    long v = u_lvalrem(n,pp,&q);
    if (v>0)
    {
      Q = (pp == 2)? f2init(v): fpinit(p,n/q);
      n = q;
    }
  }
  /* n coprime to p */
  if (n==1) P = Q;
  else
  {
    P = fpinit(p, n);
    if (Q) P = FpX_direct_compositum(P, Q, p);
  }
  return P;
}

static GEN
init_Fq_i(GEN p, long n, long v)
{
  GEN P;
  if (n <= 0) pari_err(talker,"non positive degree in ffinit");
  if (typ(p) != t_INT) pari_err(typeer, "ffinit");
  if (signe(p) <= 0) pari_err(talker,"%Ps is not a prime", p);
  if (v < 0) v = 0;
  if (n == 1) return pol_x(v);
  if (fpinit_check(p, n+1, n)) return polcyclo(n+1, v);
  if (lgefint(p)-2 <= expu(n))
    P = ffinit_fact(p,n);
  else
    P = ffinit_nofact(p,n);
  setvarn(P, v); return P;
}
GEN
init_Fq(GEN p, long n, long v)
{
  pari_sp av = avma;
  return gerepileupto(av, init_Fq_i(p, n, v));
}
GEN
ffinit(GEN p, long n, long v)
{
  pari_sp av = avma;
  return gerepileupto(av, FpX_to_mod(init_Fq_i(p, n, v), p));
}
