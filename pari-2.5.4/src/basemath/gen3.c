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

/********************************************************************/
/**                                                                **/
/**                      GENERIC OPERATIONS                        **/
/**                         (third part)                           **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/********************************************************************/
/**                                                                **/
/**                 PRINCIPAL VARIABLE NUMBER                      **/
/**                                                                **/
/********************************************************************/
long
gvar(GEN x)
{
  long i, v, w;
  switch(typ(x))
  {
    case t_POL: case t_SER: return varn(x);
    case t_POLMOD: return varn(gel(x,1));
    case t_RFRAC:  return varn(gel(x,2));
    case t_VEC: case t_COL: case t_MAT:
      v = NO_VARIABLE;
      for (i=1; i < lg(x); i++) { w=gvar(gel(x,i)); if (varncmp(w,v) < 0) v=w; }
      return v;
    case t_VECSMALL:
    case t_STR:
    case t_LIST:
      pari_err(typeer, "gvar");
  }
  return NO_VARIABLE;
}
/* T main polynomial in R[X], A auxiliary in R[X] (possibly degree 0).
 * Guess and return the main variable of R */
static long
var2_aux(GEN T, GEN A)
{
  long a = gvar2(T);
  long b = (typ(A) == t_POL && varn(A) == varn(T))? gvar2(A): gvar(A);
  if (varncmp(a, b) > 0) a = b;
  return a;
}
static long
var2_rfrac(GEN x)  { return var2_aux(gel(x,2), gel(x,1)); }
static long
var2_polmod(GEN x) { return var2_aux(gel(x,1), gel(x,2)); }

/* main variable of x, with the convention that the "natural" main
 * variable of a POLMOD is mute, so we want the next one. */
static long
gvar9(GEN x)
{ return (typ(x) == t_POLMOD)? var2_polmod(x): gvar(x); }

/* main variable of the ring over wich x is defined */
long
gvar2(GEN x)
{
  long i, v, w;
  switch(typ(x))
  {
    case t_POLMOD:
      return var2_polmod(x);
    case t_POL: case t_SER:
      v = NO_VARIABLE;
      for (i=2; i < lg(x); i++) {
        w = gvar9(gel(x,i));
        if (varncmp(w,v) < 0) v=w;
      }
      return v;
    case t_RFRAC:
      return var2_rfrac(x);
    case t_VEC: case t_COL: case t_MAT:
      v = NO_VARIABLE;
      for (i=1; i < lg(x); i++) {
        w = gvar2(gel(x,i));
        if (varncmp(w,v)<0) v=w;
      }
      return v;
  }
  return NO_VARIABLE;
}

/*******************************************************************/
/*                                                                 */
/*                    PRECISION OF SCALAR OBJECTS                  */
/*                                                                 */
/*******************************************************************/
static long
prec0(long e) { return (e < 0)? nbits2prec(-e): 2; }
static long
precREAL(GEN x) { return signe(x) ? lg(x): prec0(expo(x)); }
/* t t_REAL, s an exact non-complex type. Return precision(|t| + |s|) */
static long
precrealexact(GEN t, GEN s) {
  long l, e = gexpo(s);
  if (e == -(long)HIGHEXPOBIT) return precREAL(t);
  if (e < 0) e = 0;
  e -= expo(t);
  if (!signe(t)) return prec0(-e);
  l = lg(t);
  return (e > 0)? l + divsBIL(e): l;
}
static long
precCOMPLEX(GEN z)
{ /* ~ precision(|x| + |y|) */
  GEN x = gel(z,1), y = gel(z,2);
  long e, ex, ey, lz, lx, ly;
  if (typ(x) != t_REAL) {
    if (typ(y) != t_REAL) return 0;
    return precrealexact(y, x);
  }
  if (typ(y) != t_REAL) return precrealexact(x, y);
  /* x, y are t_REALs, cf addrr_sign */
  ex = expo(x);
  ey = expo(y);
  e = ey - ex;
  if (!signe(x)) {
    if (!signe(y)) return prec0( minss(ex,ey) );
    if (e <= 0) return prec0(ex);
    lz = nbits2prec(e);
    ly = lg(y); if (lz > ly) lz = ly;
    return lz;
  }
  if (!signe(y)) {
    if (e >= 0) return prec0(ey);
    lz = nbits2prec(-e);
    lx = lg(x); if (lz > lx) lz = lx;
    return lz;
  }
  if (e < 0) { swap(x, y); e = -e; }
  lx = lg(x);
  ly = lg(y);
  if (e) {
    long d = divsBIL(e), l = ly-d;
    return (l > lx)? lx + d: ly;
  }
  return minss(lx, ly);
}
long
precision(GEN z)
{
  switch(typ(z))
  {
    case t_REAL: return precREAL(z);
    case t_COMPLEX: return precCOMPLEX(z);
  }
  return 0;
}

long
gprecision(GEN x)
{
  long i, k, l;

  switch(typ(x))
  {
    case t_REAL: return precREAL(x);
    case t_COMPLEX: return precCOMPLEX(x);
    case t_INT: case t_INTMOD: case t_FRAC: case t_FFELT:
    case t_PADIC: case t_QUAD: case t_POLMOD:
      return 0;

    case t_POL:
      k = LONG_MAX;
      for (i=lg(x)-1; i>1; i--)
      {
        l = gprecision(gel(x,i));
        if (l && l<k) k = l;
      }
      return (k==LONG_MAX)? 0: k;
    case t_VEC: case t_COL: case t_MAT:
      k = LONG_MAX;
      for (i=lg(x)-1; i>0; i--)
      {
        l = gprecision(gel(x,i));
        if (l && l<k) k = l;
      }
      return (k==LONG_MAX)? 0: k;

    case t_RFRAC:
    {
      k=gprecision(gel(x,1));
      l=gprecision(gel(x,2)); if (l && (!k || l<k)) k=l;
      return k;
    }
    case t_QFR:
      return gprecision(gel(x,4));
  }
  return 0;
}

GEN
precision0(GEN x, long n)
{
  long a;
  if (n) return gprec(x,n);
  a = gprecision(x);
  return utoi(a ? prec2ndec(a): LONG_MAX);
}

/* ABSOLUTE padic precision */
long
padicprec(GEN x, GEN p)
{
  long i, s, t;

  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      return LONG_MAX;

    case t_INTMOD:
      return Z_pval(gel(x,1),p);

    case t_PADIC:
      if (!equalii(gel(x,2),p))
        pari_err(talker,"not the same prime in padicprec");
      return precp(x)+valp(x);

    case t_POL: case t_SER:
      for (s=LONG_MAX, i=lg(x)-1; i>1; i--)
      {
        t = padicprec(gel(x,i),p); if (t<s) s = t;
      }
      return s;

    case t_COMPLEX: case t_QUAD: case t_POLMOD: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT:
      for (s=LONG_MAX, i=lg(x)-1; i>0; i--)
      {
        t = padicprec(gel(x,i),p); if (t<s) s = t;
      }
      return s;
  }
  pari_err(typeer,"padicprec");
  return 0; /* not reached */
}

#define DEGREE0 -LONG_MAX
/* Degree of x (scalar, t_POL, t_RFRAC) wrt variable v if v >= 0,
 * wrt to main variable if v < 0.
 */
long
poldegree(GEN x, long v)
{
  long tx = typ(x), lx,w,i,d;

  if (is_scalar_t(tx)) return gequal0(x)? DEGREE0: 0;
  switch(tx)
  {
    case t_POL:
      if (!signe(x)) return DEGREE0;
      w = varn(x);
      if (v < 0 || v == w) return degpol(x);
      if (v < w) return 0;
      lx = lg(x); d = DEGREE0;
      for (i=2; i<lx; i++)
      {
        long e = poldegree(gel(x,i), v);
        if (e > d) d = e;
      }
      return d;

    case t_RFRAC:
      if (gequal0(gel(x,1))) return DEGREE0;
      return poldegree(gel(x,1),v) - poldegree(gel(x,2),v);
  }
  pari_err(typeer,"degree");
  return 0; /* not reached  */
}

long
degree(GEN x)
{
  return poldegree(x,-1);
}

/* If v<0, leading coeff with respect to the main variable, otherwise wrt v. */
GEN
pollead(GEN x, long v)
{
  long l, tx = typ(x), w;
  pari_sp av;
  GEN xinit;

  if (is_scalar_t(tx)) return gcopy(x);
  w = varn(x);
  switch(tx)
  {
    case t_POL:
      if (v < 0 || v == w)
      {
        l=lg(x);
        return (l==2)? gen_0: gcopy(gel(x,l-1));
      }
      break;

    case t_SER:
      if (v < 0 || v == w) return signe(x)? gcopy(gel(x,2)): gen_0;
      break;

    default:
      pari_err(typeer,"pollead");
      return NULL; /* not reached */
  }
  if (v < w) return gcopy(x);
  av = avma; xinit = x;
  x = gsubst(gsubst(x,w,pol_x(MAXVARN)),v,pol_x(0));
  if (gvar(x)) { avma = av; return gcopy(xinit);}
  tx = typ(x);
  if (tx == t_POL) {
    l = lg(x); if (l == 2) { avma = av; return gen_0; }
    x = gel(x,l-1);
  }
  else if (tx == t_SER) {
    if (!signe(x)) { avma = av; return gen_0;}
    x = gel(x,2);
  } else pari_err(typeer,"pollead");
  return gerepileupto(av, gsubst(x,MAXVARN,pol_x(w)));
}

/* returns 1 if there's a real component in the structure, 0 otherwise */
int
isinexactreal(GEN x)
{
  long i;
  switch(typ(x))
  {
    case t_REAL: return 1;
    case t_COMPLEX: return (typ(x[1])==t_REAL || typ(x[2])==t_REAL);

    case t_INT: case t_INTMOD: case t_FRAC:
    case t_FFELT: case t_PADIC: case t_QUAD:
    case t_QFR: case t_QFI: return 0;

    case t_RFRAC: case t_POLMOD:
      return isinexactreal(gel(x,1)) || isinexactreal(gel(x,2));

    case t_POL: case t_SER:
      for (i=lg(x)-1; i>1; i--)
        if (isinexactreal(gel(x,i))) return 1;
      return 0;

    case t_VEC: case t_COL: case t_MAT:
      for (i=lg(x)-1; i>0; i--)
        if (isinexactreal(gel(x,i))) return 1;
      return 0;
    default: return 0;
  }
}
/* Check if x is approximately real with precision e */
int
isrealappr(GEN x, long e)
{
  long i;
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return 1;
    case t_COMPLEX:
      return (gexpo(gel(x,2)) < e);

    case t_POL: case t_SER:
      for (i=lg(x)-1; i>1; i--)
        if (! isrealappr(gel(x,i),e)) return 0;
      return 1;

    case t_RFRAC: case t_POLMOD:
      return isrealappr(gel(x,1),e) && isrealappr(gel(x,2),e);

    case t_VEC: case t_COL: case t_MAT:
      for (i=lg(x)-1; i>0; i--)
        if (! isrealappr(gel(x,i),e)) return 0;
      return 1;
    default: pari_err(typeer,"isrealappr"); return 0;
  }
}

/* returns 1 if there's an inexact component in the structure, and
 * 0 otherwise. */
int
isinexact(GEN x)
{
  long lx, i;

  switch(typ(x))
  {
    case t_REAL: case t_PADIC: case t_SER:
      return 1;
    case t_INT: case t_INTMOD: case t_FFELT: case t_FRAC:
    case t_QFR: case t_QFI:
      return 0;
    case t_COMPLEX: case t_QUAD: case t_RFRAC: case t_POLMOD:
      return isinexact(gel(x,1)) || isinexact(gel(x,2));
    case t_POL:
      for (i=lg(x)-1; i>1; i--)
        if (isinexact(gel(x,i))) return 1;
      return 0;
    case t_VEC: case t_COL: case t_MAT:
      for (i=lg(x)-1; i>0; i--)
        if (isinexact(gel(x,i))) return 1;
      return 0;
    case t_LIST:
      x = list_data(x); lx = x? lg(x): 1;
      for (i=1; i<lx; i++)
        if (isinexact(gel(x,i))) return 1;
      return 0;
  }
  return 0;
}

int
isrationalzeroscalar(GEN g)
{
  switch (typ(g))
  {
    case t_INT:     return !signe(g);
    case t_COMPLEX: return isintzero(gel(g,1)) && isintzero(gel(g,2));
    case t_QUAD:    return isintzero(gel(g,2)) && isintzero(gel(g,3));
  }
  return 0;
}

int
iscomplex(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return 0;
    case t_COMPLEX:
      return !gequal0(gel(x,2));
    case t_QUAD:
      return signe(gmael(x,1,2)) > 0;
  }
  pari_err(typeer,"iscomplex");
  return 0; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                    GENERIC REMAINDER                            */
/*                                                                 */
/*******************************************************************/
/* euclidean quotient for scalars of admissible types */
static GEN
_quot(GEN x, GEN y)
{
  GEN q = gdiv(x,y), f = gfloor(q);
  if (gsigne(y) < 0 && !gequal(f,q)) f = gaddgs(f, 1);
  return f;
}
static GEN
_quotsg(long x, GEN y)
{
  GEN q = gdivsg(x,y), f = gfloor(q);
  if (gsigne(y) < 0 && !gequal(f,q)) f = gaddgs(f, 1);
  return f;
}
static GEN
_quotgs(GEN x, long y)
{
  GEN q = gdivgs(x,y), f = gfloor(q);
  if (y < 0 && !gequal(f,q)) f = gaddgs(f, 1);
  return f;
}
static GEN
quot(GEN x, GEN y)
{
  pari_sp av = avma;
  return gerepileupto(av, _quot(x, y));
}
static GEN
quotgs(GEN x, long y)
{
  pari_sp av = avma;
  return gerepileupto(av, _quotgs(x, y));
}
static GEN
quotsg(long x, GEN y)
{
  pari_sp av = avma;
  return gerepileupto(av, _quotsg(x, y));
}

/* assume y a t_REAL, x a t_INT, t_FRAC or t_REAL.
 * Return x mod y or NULL if accuracy error */
GEN
modr_safe(GEN x, GEN y)
{
  GEN q, f;
  long e;
  if (typ(x) == t_INT && !signe(x)) return gen_0;
  q = gdiv(x,y); /* t_REAL */

  e = expo(q);
  if (e >= 0 && nbits2prec(e) > lg(q)) return NULL;
  f = floorr(q);
  if (gsigne(y) < 0 && signe(subri(q,f))) f = addis(f, 1);
  return signe(f)? gsub(x, mulir(f,y)): x;
}

/* x t_POLMOD, y t_POL in the same variable as x[1], return x % y */
static GEN
polmod_mod(GEN x, GEN y)
{
  GEN z, T = gel(x,1);
  if (RgX_equal_var(T, y)) return gcopy(x);
  z = cgetg(3,t_POLMOD); T = RgX_gcd(T,y);
  gel(z,1) = T;
  gel(z,2) = grem(gel(x,2), T);
  return z;
}
GEN
gmod(GEN x, GEN y)
{
  pari_sp av, tetpil;
  long i,lx,ty, tx = typ(x);
  GEN z,p1;

  if (is_matvec_t(tx))
  {
    z = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(z,i) = gmod(gel(x,i),y);
    return z;
  }
  ty = typ(y);
  switch(ty)
  {
    case t_INT:
      switch(tx)
      {
        case t_INT:
          return modii(x,y);

        case t_INTMOD: z=cgetg(3, t_INTMOD);
          gel(z,1) = gcdii(gel(x,1),y);
          gel(z,2) = modii(gel(x,2),gel(z,1)); return z;

        case t_FRAC:
          av=avma;
          p1=mulii(gel(x,1),Fp_inv(gel(x,2),y));
          tetpil=avma; return gerepile(av,tetpil,modii(p1,y));

        case t_QUAD: z=cgetg(4,t_QUAD);
          gel(z,1) = ZX_copy(gel(x,1));
          gel(z,2) = gmod(gel(x,2),y);
          gel(z,3) = gmod(gel(x,3),y); return z;

        case t_PADIC: return padic_to_Fp(x, y);
        case t_POLMOD: case t_POL:
          return gen_0;
        case t_REAL: /* NB: conflicting semantic with lift(x * Mod(1,y)). */
          av = avma;
          return gerepileuptoleaf(av, mpsub(x, mpmul(_quot(x,y),y)));

        default: pari_err(operf,"%",x,y);
      }

    case t_REAL: case t_FRAC:
      switch(tx)
      {
        case t_INT: case t_REAL: case t_FRAC:
          av = avma;
          return gerepileupto(av, gadd(x, gneg(gmul(_quot(x,y),y))));

        case t_POLMOD: case t_POL:
          return gen_0;

        default: pari_err(operf,"%",x,y);
      }

    case t_POL:
      if (is_scalar_t(tx))
      {
        if (tx!=t_POLMOD || varncmp(varn(x[1]), varn(y)) > 0)
          return degpol(y)? gcopy(x): gen_0;
        if (varn(x[1])!=varn(y)) return gen_0;
        return polmod_mod(x, y);
      }
      switch(tx)
      {
        case t_POL:
          return grem(x,y);

        case t_RFRAC:
          av=avma;
          p1=gmul(gel(x,1),ginvmod(gel(x,2),y)); tetpil=avma;
          return gerepile(av,tetpil,grem(p1,y));

        case t_SER:
          if (RgX_is_monomial(y) && varn(x) == varn(y))
          {
            long d = degpol(y);
            if (lg(x)-2 + valp(x) < d) pari_err(operi,"%",x,y);
            av = avma;
            return gerepileupto(av, gmod(ser2rfrac_i(x), y));
          }
        default: pari_err(operf,"%",x,y);
      }
  }
  pari_err(operf,"%",x,y);
  return NULL; /* not reached */
}
/* divisibility: return 1 if y | x, 0 otherwise */
int
gdvd(GEN x, GEN y)
{
  pari_sp av = avma;
  x = gmod(x,y); avma = av; return gequal0(x);
}

GEN
gmodgs(GEN x, long y)
{
  ulong u;
  long i, lx, tx = typ(x);
  GEN z;
  if (is_matvec_t(tx))
  {
    z = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(z,i) = gmodgs(gel(x,i),y);
    return z;
  }
  switch(tx)
  {
    case t_INT:
      return modis(x,y);

    case t_INTMOD: z=cgetg(3, t_INTMOD);
      i = cgcd(smodis(gel(x,1), y), y);
      gel(z,1) = utoi(i);
      gel(z,2) = modis(gel(x,2), i); return z;

    case t_FRAC:
      u = (ulong)labs(y);
      return utoi( Fl_div(umodiu(gel(x,1), u),
                          umodiu(gel(x,2), u), u) );

    case t_QUAD: z=cgetg(4,t_QUAD);
      gel(z,1) = ZX_copy(gel(x,1));
      gel(z,2) = gmodgs(gel(x,2),y);
      gel(z,3) = gmodgs(gel(x,3),y); return z;

    case t_PADIC: return padic_to_Fp(x, stoi(y));
    case t_POLMOD: case t_POL:
      return gen_0;
  }
  pari_err(operf,"%",x,stoi(y));
  return NULL; /* not reached */
}
GEN
gmodsg(long x, GEN y)
{
  switch(typ(y))
  {
    case t_INT:
      return modsi(x,y);
    case t_REAL: case t_FRAC: {
      pari_sp av = avma;
      return gerepileupto(av, gaddsg(x, gneg(gmul(_quotsg(x,y),y))));
    }

    case t_POL:
      return degpol(y)? stoi(x): gen_0;
  }
  pari_err(operf,"%",stoi(x),y);
  return NULL; /* not reached */
}

GEN
gmodulsg(long x, GEN y)
{
  GEN z;

  switch(typ(y))
  {
    case t_INT: z = cgetg(3,t_INTMOD);
      gel(z,1) = absi(y);
      gel(z,2) = modsi(x,y); return z;

    case t_POL: z = cgetg(3,t_POLMOD);
      gel(z,1) = gcopy(y);
      gel(z,2) = stoi(x); return z;
  }
  pari_err(operf,"%",stoi(x),y); return NULL; /* not reached */
}

GEN
gmodulss(long x, long y)
{
  GEN z = cgetg(3,t_INTMOD);
  y = labs(y);
  gel(z,1) = stoi(y);
  gel(z,2) = modss(x, y); return z;
}

static GEN
specialmod(GEN x, GEN y)
{
  GEN z = gmod(x,y);
  if (varncmp(gvar(z), varn(y)) < 0) z = gen_0;
  return z;
}

GEN
gmodulo(GEN x,GEN y)
{
  long tx = typ(x), l, i;
  GEN z;

  if (is_matvec_t(tx))
  {
    z = cgetg_copy(x, &l);
    for (i=1; i<l; i++) gel(z,i) = gmodulo(gel(x,i),y);
    return z;
  }
  switch(typ(y))
  {
    case t_INT: z = cgetg(3,t_INTMOD);
      gel(z,1) = absi(y);
      gel(z,2) = Rg_to_Fp(x,y); return z;

    case t_POL: z = cgetg(3,t_POLMOD);
      if (tx == t_POLMOD)
      {
        long vx = varn(gel(x,1)), vy = varn(y);
        if (vx == vy) return polmod_mod(x,y);
        if (varncmp(vx, vy) < 0)
          gel(z,2) = gen_0;
        else if (vx > vy)
          gel(z,2) = (lg(y) > 3)? gcopy(x): gen_0;
        gel(z,1) = gcopy(y);
        return z;
      }

      gel(z,1) = gcopy(y);
      if (is_const_t(tx))
      {
        gel(z,2) = (lg(y) > 3)? gcopy(x): gmod(x,y);
        return z;
      }
      switch(tx)
      {
        case t_POL: case t_RFRAC: case t_SER:
          gel(z,2) = specialmod(x,y); return z;
      }
  }
  pari_err(operf,"%",x,y);
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                 GENERIC EUCLIDEAN DIVISION                      */
/*                                                                 */
/*******************************************************************/

GEN
gdivent(GEN x, GEN y)
{
  long tx = typ(x);

  if (is_matvec_t(tx))
  {
    long i, lx;
    GEN z = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(z,i) = gdivent(gel(x,i),y);
    return z;
  }
  switch(typ(y))
  {
    case t_INT:
      switch(tx)
      { /* equal to, but more efficient than, quot(x,y) */
        case t_INT: return truedivii(x,y);
        case t_REAL: case t_FRAC: return quot(x,y);
        case t_POL: return gdiv(x,y);
      }
      break;
    case t_REAL: case t_FRAC: return quot(x,y);
    case t_POL:
      if (is_scalar_t(tx))
      {
        if (tx == t_POLMOD) break;
        return degpol(y)? gen_0: gdiv(x,y);
      }
      if (tx == t_POL) return gdeuc(x,y);
  }
  pari_err(operf,"\\",x,y);
  return NULL; /* not reached */
}

GEN
gdiventgs(GEN x, long y)
{
  long i, lx;
  GEN z;
  switch(typ(x))
  {
    case t_INT: return truedivis(x,y); /* = quotgs(x,y) */
    case t_REAL: case t_FRAC: return quotgs(x,y);
    case t_POL: return gdivgs(x,y);
    case t_VEC: case t_COL: case t_MAT:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(z,i) = gdiventgs(gel(x,i),y);
      return z;
  }
  pari_err(operf,"\\",x,stoi(y));
  return NULL; /* not reached */
}
GEN
gdiventsg(long x, GEN y)
{
  switch(typ(y))
  {
    case t_INT: return truedivsi(x,y); /* = quotsg(x,y) */
    case t_REAL: case t_FRAC: return quotsg(x,y);
    case t_POL: return degpol(y)? gen_0: gdivsg(x,y);
  }
  pari_err(operf,"\\",stoi(x),y);
  return NULL; /* not reached */
}

/* with remainder */
static GEN
quotrem(GEN x, GEN y, GEN *r)
{
  pari_sp av;
  GEN q = quot(x,y);
  av = avma;
  *r = gerepileupto(av, gsub(x, gmul(q,y)));
  return q;
}

GEN
gdiventres(GEN x, GEN y)
{
  long tx = typ(x);
  GEN z,q,r;

  if (is_matvec_t(tx))
  {
    long i, lx;
    z = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(z,i) = gdiventres(gel(x,i),y);
    return z;
  }
  z = cgetg(3,t_COL);
  switch(typ(y))
  {
    case t_INT:
      switch(tx)
      { /* equal to, but more efficient than next case */
        case t_INT:
          gel(z,1) = truedvmdii(x,y,(GEN*)(z+2));
          return z;
        case t_REAL: case t_FRAC:
          q = quotrem(x,y,&r);
          gel(z,1) = q;
          gel(z,2) = r; return z;
        case t_POL:
          gel(z,1) = gdiv(x,y);
          gel(z,2) = gen_0; return z;
      }
      break;
    case t_REAL: case t_FRAC:
          q = quotrem(x,y,&r);
          gel(z,1) = q;
          gel(z,2) = r; return z;
    case t_POL:
      if (is_scalar_t(tx))
      {
        if (tx == t_POLMOD) break;
        if (degpol(y))
        {
          q = gen_0;
          r = gcopy(x);
        }
        else
        {
          q = gdiv(x,y);
          r = gen_0;
        }
        gel(z,1) = q;
        gel(z,2) = r; return z;
      }
      if (tx == t_POL)
      {
        gel(z,1) = poldivrem(x,y,(GEN *)(z+2));
        return z;
      }
  }
  pari_err(operf,"\\",x,y);
  return NULL; /* not reached */
}

GEN
divrem(GEN x, GEN y, long v)
{
  pari_sp av = avma;
  long vx, vy;
  GEN q, r;
  if (v < 0 || typ(y) != t_POL || typ(x) != t_POL) return gdiventres(x,y);
  vx = varn(x); if (vx != v) x = swap_vars(x,v);
  vy = varn(y); if (vy != v) y = swap_vars(y,v);
  q = poldivrem(x,y, &r);
  if (v && (vx != v || vy != v))
  {
    GEN X = pol_x(v);
    q = gsubst(q, v, X); /* poleval broken for t_RFRAC, subst is safe */
    r = gsubst(r, v, X);
  }
  return gerepilecopy(av, mkcol2(q, r));
}

GEN
diviiround(GEN x, GEN y)
{
  pari_sp av1, av = avma;
  GEN q,r;
  int fl;

  q = dvmdii(x,y,&r); /* q = x/y rounded towards 0, sgn(r)=sgn(x) */
  if (r==gen_0) return q;
  av1 = avma;
  fl = absi_cmp(shifti(r,1),y);
  avma = av1; cgiv(r);
  if (fl >= 0) /* If 2*|r| >= |y| */
  {
    long sz = signe(x)*signe(y);
    if (fl || sz > 0) q = gerepileuptoint(av, addis(q,sz));
  }
  return q;
}

/* If x and y are not both scalars, same as gdivent.
 * Otherwise, compute the quotient x/y, rounded to the nearest integer
 * (towards +oo in case of tie). */
GEN
gdivround(GEN x, GEN y)
{
  pari_sp av1, av;
  long tx=typ(x),ty=typ(y);
  GEN q,r;
  int fl;

  if (tx==t_INT && ty==t_INT) return diviiround(x,y);
  av = avma;
  if (is_rational_t(tx) && is_rational_t(ty))
  { /* same as diviiround but less efficient */
    q = quotrem(x,y,&r);
    av1 = avma;
    fl = gcmp(gmul2n(Q_abs(r),1), Q_abs(y));
    avma = av1; cgiv(r);
    if (fl >= 0) /* If 2*|r| >= |y| */
    {
      long sz = gsigne(y);
      if (fl || sz > 0) q = gerepileupto(av, gaddgs(q, sz));
    }
    return q;
  }
  if (is_matvec_t(tx))
  {
    long i, lx;
    GEN z = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(z,i) = gdivround(gel(x,i),y);
    return z;
  }
  return gdivent(x,y);
}

GEN
gdivmod(GEN x, GEN y, GEN *pr)
{
  long ty,tx=typ(x);

  if (tx==t_INT)
  {
    ty=typ(y);
    if (ty==t_INT) return dvmdii(x,y,pr);
    if (ty==t_POL) { *pr=gcopy(x); return gen_0; }
    pari_err(typeer,"gdivmod");
  }
  if (tx!=t_POL) pari_err(typeer,"gdivmod");
  return poldivrem(x,y,pr);
}

/*******************************************************************/
/*                                                                 */
/*                               SHIFT                             */
/*                                                                 */
/*******************************************************************/

/* Shift tronque si n<0 (multiplication tronquee par 2^n)  */

GEN
gshift(GEN x, long n)
{
  long i, lx;
  GEN y;

  switch(typ(x))
  {
    case t_INT: return shifti(x,n);
    case t_REAL:return shiftr(x,n);

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gshift(gel(x,i),n);
      return y;
  }
  return gmul2n(x,n);
}

/*******************************************************************/
/*                                                                 */
/*           SUBSTITUTION DANS UN POLYNOME OU UNE SERIE            */
/*                                                                 */
/*******************************************************************/

/* Convert t_SER --> t_POL, ignoring valp. INTERNAL ! */
GEN
ser2pol_i(GEN x, long lx)
{
  long i = lx-1;
  GEN y;
  while (i > 1 && isexactzero(gel(x,i))) i--;
  y = cgetg(i+1, t_POL); y[1] = x[1] & ~VALPBITS;
  for ( ; i > 1; i--) y[i] = x[i];
  return y;
}

/* T t_POL in var v, mod out by T components of x which are
 * t_POL/t_RFRAC in v. Recursively */
static GEN
mod_r(GEN x, long v, GEN T)
{
  long i, w, lx, tx = typ(x);
  GEN y;

  if (is_const_t(tx)) return x;
  switch(tx)
  {
    case t_POLMOD:
      w = varn(gel(x,1));
      if (w == v) pari_err(talker, "subst: unexpected variable precedence");
      if (varncmp(v, w) < 0) return x;
      return gmodulo(mod_r(gel(x,2),v,T), mod_r(gel(x,1),v,T));
    case t_POL:
      w = varn(x);
      if (w == v) return RgX_rem(x, T);
      if (varncmp(v, w) < 0) return x;
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i = 2; i < lx; i++) gel(y,i) = mod_r(gel(x,i),v,T);
      return normalizepol_lg(y, lx);
    case t_RFRAC:
      return gdiv(mod_r(gel(x,1),v,T), mod_r(gel(x,2),v,T));
    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i = 1; i < lx; i++) gel(y,i) = mod_r(gel(x,i),v,T);
      return y;
    case t_LIST:
      y = listcreate();
      list_data(y) = list_data(x)? mod_r(list_data(x),v,T): NULL;
      return y;
  }
  pari_err(typeer,"substpol");
  return NULL;/*not reached*/
}
GEN
gsubst_expr(GEN expr, GEN from, GEN to)
{
  pari_sp av = avma;
  long w, v = fetch_var(); /* FIXME: Need fetch_var_low_priority() */
  GEN y;

  from = simplify_shallow(from);
  switch (typ(from)) {
    case t_RFRAC: /* M= numerator(from) - t * denominator(from) */
      y = gsub(gel(from,1), gmul(pol_x(v), gel(from,2)));
      break;
    default:
      y = gsub(from, pol_x(v));        /* M = from - t */
  }
  w = gvar(from);
  if (varncmp(v,w) <= 0)
    pari_err(talker, "subst: unexpected variable precedence");
  y = gsubst(mod_r(expr, w, y), v, to);
  (void)delete_var(); return gerepileupto(av, y);
}

GEN
gsubstpol(GEN x, GEN T, GEN y)
{
  if (typ(T) == t_POL && RgX_is_monomial(T) && gequal1(leading_term(T)))
  { /* T = t^d */
    long d = degpol(T), v = varn(T);
    pari_sp av = avma;
    GEN deflated = d == 1? x: gdeflate(x, v, d);
    if (deflated) return gerepileupto(av, gsubst(deflated, v, y));
    avma = av;
  }
  return gsubst_expr(x,T,y);
}

static long
checkdeflate(GEN x)
{
  ulong d = 0, i, lx = (ulong)lg(x);
  for (i=3; i<lx; i++)
    if (!gequal0(gel(x,i))) { d = ugcd(d,i-2); if (d == 1) break; }
  return (long)d;
}

/* return NULL if substitution fails */
GEN
gdeflate(GEN x, long v, long d)
{
  long i, lx, tx = typ(x);
  GEN z;
  if (is_scalar_t(tx)) return gcopy(x);
  if (d <= 0) pari_err(talker,"need positive degree in gdeflate");
  if (tx == t_POL || tx == t_SER)
  {
    long vx = varn(x);
    pari_sp av;
    if (varncmp(vx, v) < 0)
    {
      z = cgetg_copy(x, &lx); z[1] = x[1];
      for (i=2; i<lx; i++)
      {
        gel(z,i) = gdeflate(gel(x,i),v,d);
        if (!z[i]) return NULL;
      }
      return z;
    }
    if (varncmp(vx, v) > 0) return gcopy(x);
    av = avma;
    if (tx == t_SER)
    {
      long V = valp(x);
      GEN y;

      lx = lg(x);
      if (lx == 2) return zeroser(v, V / d);
      y = ser2pol_i(x, lx);
      if (V % d != 0 || checkdeflate(y) % d != 0)
        pari_err(talker, "can't deflate this power series (d = %ld): %Ps", d, x);
      y = poltoser(RgX_deflate(y, d), v, 1 + (lx-3)/d);
      setvalp(y, V/d); return gerepilecopy(av, y);
    }
    /* t_POL */
    if (checkdeflate(x) % d != 0) return NULL;
    return gerepilecopy(av, RgX_deflate(x,d));
  }
  if (tx == t_RFRAC)
  {
    z = cgetg(3, t_RFRAC);
    gel(z,1) = gdeflate(gel(x,1),v,d); if (!z[1]) return NULL;
    gel(z,2) = gdeflate(gel(x,2),v,d); if (!z[2]) return NULL;
    return z;
  }
  if (is_matvec_t(tx))
  {
    z = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++)
    {
      gel(z,i) = gdeflate(gel(x,i),v,d);
      if (!z[i]) return NULL;
    }
    return z;
  }
  if (tx == t_LIST)
  {
    z = listcreate();
    if (list_data(x))
    {
      GEN y = gdeflate(list_data(x),v,d);
      if (!y) return NULL;
      list_data(z) = y;
    }
    else
      list_data(z) = NULL;
    return z;
  }
  pari_err(typeer,"gdeflate");
  return NULL; /* not reached */
}

/* set *m to the largest d such that x0 = A(X^d); return A */
GEN
RgX_deflate_max(GEN x, long *m)
{
  *m = checkdeflate(x);
  return RgX_deflate(x, *m);
}

static GEN
RgM_eval_powers(GEN P, GEN V, long a, long n)
{
  GEN z = scalarmat_shallow(gel(P,2+a), lg(V[1])-1); /* V[1] = 1 */
  long i;
  for (i=1; i<=n; i++) z = RgM_add(z, RgM_Rg_mul(gel(V,i+1),gel(P,2+a+i)));
  return z;
}

GEN
RgX_RgMV_eval(GEN P, GEN V)
{
  pari_sp av = avma;
  long l = lg(V)-1, d = degpol(P), n = lg(V[1])-1;
  GEN z;

  if (d < 0) return zeromat(n, n);
  if (d < l)
  {
    z = RgM_eval_powers(P,V,0,d);
    return gerepileupto(av, z);
  }
  if (l<=1) pari_err(talker,"powers is only [] or [1] in RgX_RgMV_eval");
  d -= l;
  z = RgM_eval_powers(P,V,d+1,l-1);
  while (d >= l-1)
  {
    d -= l-1;
    z = RgM_add(RgM_eval_powers(P,V,d+1,l-2), RgM_mul(z,gel(V,l)));
    z = gerepileupto(av, z);
  }
  z = RgM_add(RgM_eval_powers(P,V,0,d), RgM_mul(z,gel(V,d+2)));
  if (DEBUGLEVEL>=8)
  {
    long cnt = 1 + (degpol(P) - l) / (l-1);
    err_printf("RgX_RgMV_eval: %ld RgM_mul [%ld]\n", cnt, l-1);
  }
  return gerepileupto(av, z);
}

GEN
RgX_RgM_eval(GEN Q, GEN x)
{
  pari_sp av = avma;
  GEN z;
  long d = degpol(Q), rtd, n = lg(x)-1;
  if (d < 0) return zeromat(n, n);
  rtd = (long) sqrt((double)d);
  z = RgX_RgMV_eval(Q, RgM_powers(x, rtd));
  return gerepileupto(av, z);
}

GEN
RgX_RgM_eval_col(GEN x, GEN M, long c)
{
  long i, n = lg(M)-1, lc = lg(x)-1;
  GEN z;
  if (signe(x)==0) return zerocol(n);
  z = Rg_col_ei(gel(x, lc), n, c);
  for (i=lc-1; i>=2; i--)
  {
    z = RgM_RgC_mul(M, z);
    gel(z,c) = gadd(gel(z,c), gel(x, i));
  }
  return z;
}

GEN
gsubst(GEN x, long v, GEN y)
{
  long tx = typ(x), ty = typ(y), lx = lg(x), ly = lg(y);
  long l, vx, vy, e, ex, ey, i, j, k, jb;
  pari_sp av, av2, lim;
  GEN X, t, p1, p2, modp1, z;

  switch(ty)
  {
    case t_MAT:
      if (ly==1) return cgetg(1,t_MAT);
      if (ly != lg(y[1]))
        pari_err(talker,"forbidden substitution by a non square matrix");
      break;
    case t_QFR: case t_QFI: case t_VEC: case t_COL:
      pari_err(talker,"forbidden substitution by a vector");
      break; /* not reached */
  }

  if (is_scalar_t(tx))
  {
    if (tx!=t_POLMOD || varncmp(v, varn(x[1])) <= 0)
    {
      if (ty==t_MAT) return scalarmat(x,ly-1);
      return gcopy(x);
    }
    av=avma;
    p1=gsubst(gel(x,1),v,y); vx=varn(p1);
    p2=gsubst(gel(x,2),v,y); vy=gvar(p2);
    if (typ(p1)!=t_POL)
      pari_err(talker,"forbidden substitution in a scalar type");
    if (varncmp(vy, vx) >= 0) return gerepileupto(av, gmodulo(p2,p1));
    modp1 = mkpolmod(gen_1,p1);
    lx = lg(p2);
    z = cgetg(lx,t_POL); z[1] = p2[1];
    for (i=2; i<lx; i++)
    {
      GEN c = gel(p2,i);
      if (varncmp(vx, gvar(c)) <= 0)
        c = gmodulo(c,p1);
      else
        c = gmul(c, modp1);
      gel(z,i) = c;
    }
    return gerepileupto(av, normalizepol_lg(z,lx));
  }

  switch(tx)
  {
    case t_POL:
      if (lx==2)
        return (ty==t_MAT)? scalarmat(gen_0,ly-1): gen_0;

      vx = varn(x);
      if (varncmp(vx, v) > 0) return ty == t_MAT? scalarmat(x,ly-1): gcopy(x);
      if (varncmp(vx, v) < 0)
      {
        av = avma; z = cgetg(lx, t_POL); z[1] = x[1];
        for (i=2; i<lx; i++) gel(z,i) = gsubst(gel(x,i),v,y);
        return gerepileupto(av, poleval(z, pol_x(vx)));
      }
      return ty == t_MAT? RgX_RgM_eval(x, y): poleval(x,y);

    case t_SER:
      vx = varn(x);
      if (varncmp(vx, v) > 0) return (ty==t_MAT)? scalarmat(x,ly-1): gcopy(x);
      ex = valp(x);
      if (varncmp(vx, v) < 0)
      {
        if (lx == 2) return (ty==t_MAT)? scalarmat(x,ly-1): gcopy(x);
        av = avma; X = pol_x(vx);
        av2 = avma; lim = stack_lim(av2,1);
        z = gadd(gsubst(gel(x,lx-1),v,y), zeroser(vx,1));
        for (i = lx-2; i>=2; i--)
        {
          z = gadd(gmul(z,X), gsubst(gel(x,i),v,y));
          if (low_stack(lim, stack_lim(av2,1)))
          {
            if(DEBUGMEM>1) pari_warn(warnmem,"gsubst (i = %ld)", i);
            z = gerepileupto(av2, z);
          }
        }
        if (ex) z = gmul(z, monomial(gen_1,ex,vx));
        return gerepileupto(av, z);
      }
      switch(ty) /* here vx == v */
      {
        case t_SER:
          ey = valp(y);
          vy = varn(y);
          if (ey < 1) return zeroser(vy, ey*(ex+lx-2));
          if (lx == 2) return zeroser(vy, ey*ex);
          if (vy != vx)
          {
            av = avma; lim = stack_lim(av,1); z = gel(x,lx-1);

            for (i=lx-2; i>=2; i--)
            {
              z = gadd(gmul(y,z), gel(x,i));
              if (low_stack(lim, stack_lim(av,1)))
              {
                if(DEBUGMEM>1) pari_warn(warnmem,"gsubst (i = %ld)", i);
                z = gerepileupto(av, z);
              }
            }
            if (ex) z = gmul(z, gpowgs(y,ex));
            return gerepileupto(av,z);
          }
          l = (lx-2)*ey+2;
          if (ex) { if (l>ly) l = ly; }
          else if (lx != 3)
          {
            long l2;
            for (i = 3; i < lx; i++)
              if (!isexactzero(gel(x,i))) break;
            l2 = (i-2)*ey + (gequal0(y)? 2 : ly);
            if (l > l2) l = l2;
          }
          p2 = ex? gpowgs(y, ex): NULL;

          av = avma; lim=stack_lim(av,1);
          t = leafcopy(y);
          if (l < ly) setlg(t, l);
          z = scalarser(gel(x,2),varn(y),l-2);
          for (i=3,jb=ey; jb<=l-2; i++,jb+=ey)
          {
            if (i < lx) {
              for (j=jb+2; j<minss(l, jb+ly); j++)
                gel(z,j) = gadd(gel(z,j), gmul(gel(x,i),gel(t,j-jb)));
            }
            for (j=l-1-jb-ey; j>1; j--)
            {
              p1 = gen_0;
              for (k=2; k<j; k++)
                p1 = gadd(p1, gmul(gel(t,j-k+2),gel(y,k)));
              gel(t,j) = gadd(p1, gmul(gel(t,2),gel(y,j)));
            }
            if (low_stack(lim, stack_lim(av,1)))
            {
              if(DEBUGMEM>1) pari_warn(warnmem,"gsubst");
              gerepileall(av,2, &z,&t);
            }
          }
          if (!p2) return gerepilecopy(av,z);
          return gerepileupto(av, gmul(z,p2));

        case t_POL:
          if (lg(y) == 2) return scalarser(gel(x,2),v,lx-2);
        case t_RFRAC:
          vy = gvar(y); e = gval(y,vy);
          if (e <= 0)
            pari_err(talker,"non positive valuation in a series substitution");
          av = avma; p1 = poleval(ser2pol_i(x, lg(x)), y);
          z = gmul(gpowgs(y,ex), gadd(p1, zeroser(vy, e*(lx-2))));
          return gerepileupto(av, z);

        default:
          pari_err(talker,"non polynomial or series type substituted in a series");
      }
      break;

    case t_RFRAC: av=avma;
      p1=gsubst(gel(x,1),v,y);
      p2=gsubst(gel(x,2),v,y); return gerepileupto(av, gdiv(p1,p2));

    case t_VEC: case t_COL: case t_MAT:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(z,i) = gsubst(gel(x,i),v,y);
      return z;
    case t_LIST:
      z = listcreate();
      list_data(z) = list_data(x)? gsubst(list_data(x),v,y): NULL;
      return z;
  }
  return gcopy(x);
}

GEN
gsubstvec(GEN e, GEN v, GEN r)
{
  pari_sp ltop=avma;
  long i, j, l = lg(v);
  GEN w, z, R;
  if ( !is_vec_t(typ(v)) || !is_vec_t(typ(r)) ) pari_err(typeer,"substvec");
  if (lg(r)!=l)
    pari_err(talker,"different number of variables and values in substvec");
  w = cgetg(l,t_VECSMALL);
  z = cgetg(l,t_VECSMALL);
  R = cgetg(l,t_VEC);
  for(i=j=1;i<l;i++)
  {
    GEN T = gel(v,i), ri = gel(r,i);
    if (!gcmpX(T)) pari_err(talker,"not a variable in substvec (%Ps)", T);
    if (gvar(ri) == NO_VARIABLE) /* no need to take precautions */
      e = gsubst(e, varn(T), ri);
    else
    {
      w[j] = varn(T);
      z[j] = fetch_var();
      gel(R,j) = ri;
      j++;
    }
  }
  for(i=1;i<j;i++) e = gsubst(e,w[i],pol_x(z[i]));
  for(i=1;i<j;i++) e = gsubst(e,z[i],gel(R,i));
  for(i=1;i<j;i++) (void)delete_var();
  return gerepileupto(ltop,e);
}

/*******************************************************************/
/*                                                                 */
/*                SERIE RECIPROQUE D'UNE SERIE                     */
/*                                                                 */
/*******************************************************************/

GEN
recip(GEN x)
{
  long v=varn(x), lx = lg(x);
  pari_sp tetpil, av=avma;
  GEN p1,p2,a,y,u;

  if (typ(x)!=t_SER) pari_err(talker,"not a series in serreverse");
  if (valp(x)!=1 || lx < 3)
    pari_err(talker,"valuation not equal to 1 in serreverse");

  a=gel(x,2);
  if (gequal1(a))
  {
    long i, j, k, mi;
    pari_sp lim=stack_lim(av, 2);

    mi = lx-1; while (mi>=3 && gequal0(gel(x,mi))) mi--;
    u = cgetg(lx,t_SER);
    y = cgetg(lx,t_SER);
    u[1] = y[1] = evalsigne(1) | _evalvalp(1) | evalvarn(v);
    gel(u,2) = gel(y,2) = gen_1;
    if (lx > 3)
    {
      gel(u,3) = gmulsg(-2,gel(x,3));
      gel(y,3) = gneg(gel(x,3));
    }
    for (i=3; i<lx-1; )
    {
      pari_sp av2;
      for (j=3; j<i+1; j++)
      {
        av2 = avma; p1 = gel(x,j);
        for (k = maxss(3,j+2-mi); k < j; k++)
          p1 = gadd(p1, gmul(gel(u,k),gel(x,j-k+2)));
        p1 = gneg(p1);
        gel(u,j) = gerepileupto(av2, gadd(gel(u,j), p1));
      }
      av2 = avma;
      p1 = gmulsg(i,gel(x,i+1));
      for (k = 2; k < minss(i,mi); k++)
      {
        p2 = gmul(gel(x,k+1),gel(u,i-k+2));
        p1 = gadd(p1, gmulsg(k,p2));
      }
      i++;
      gel(u,i) = gerepileupto(av2, gneg(p1));
      gel(y,i) = gdivgs(gel(u,i), i-1);
      if (low_stack(lim, stack_lim(av,2)))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"recip");
        for(k=i+1; k<lx; k++) gel(u,k) = gel(y,k) = gen_0; /* dummy */
        gerepileall(av,2, &u,&y);
      }
    }
    return gerepilecopy(av,y);
  }
  y = gdiv(x,a); gel(y,2) = gen_1; y = recip(y);
  a = gdiv(pol_x(v),a); tetpil = avma;
  return gerepile(av,tetpil, gsubst(y,v,a));
}

/*******************************************************************/
/*                                                                 */
/*                    DERIVATION ET INTEGRATION                    */
/*                                                                 */
/*******************************************************************/
GEN
derivser(GEN x)
{
  long i, vx = varn(x), e = valp(x), lx = lg(x);
  GEN y;
  if (lx == 2) return zeroser(vx,e? e-1: 0);
  if (e)
  {
    y = cgetg(lx,t_SER); y[1] = evalvalp(e-1) | evalvarn(vx);
    for (i=2; i<lx; i++) gel(y,i) = gmulsg(i+e-2,gel(x,i));
  } else {
    if (lx == 3) return zeroser(vx, 0);
    lx--;
    y = cgetg(lx,t_SER); y[1] = _evalvalp(0) | evalvarn(vx);
    for (i=2; i<lx; i++) gel(y,i) = gmulsg(i-1,gel(x,i+1));
  }
  return normalize(y);
}

GEN
deriv(GEN x, long v)
{
  long lx, vx, tx, i, j;
  pari_sp av;
  GEN y;

  tx = typ(x); if (is_const_t(tx)) return gen_0;
  if (v < 0 && tx!=t_CLOSURE) v = gvar9(x);
  switch(tx)
  {
    case t_POLMOD:
      if (varncmp(v, varn(x[1]))) return gen_0;
      y = cgetg(3,t_POLMOD);
      gel(y,1) = gcopy(gel(x,1));
      gel(y,2) = deriv(gel(x,2),v); return y;

    case t_POL:
      vx = varn(x);
      if (varncmp(vx, v) > 0) return gen_0;
      if (varncmp(vx, v) == 0) return RgX_deriv(x);
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = deriv(gel(x,i),v);
      return normalizepol_lg(y,i);

    case t_SER:
      vx = varn(x);
      if (varncmp(vx, v) > 0) return gen_0;
      if (varncmp(vx, v) == 0) return derivser(x);
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (j=2; j<lx; j++) gel(y,j) = deriv(gel(x,j),v);
      return normalize(y);

    case t_RFRAC: {
      GEN a = gel(x,1), b = gel(x,2), bp, b0, d, t;
      y = cgetg(3,t_RFRAC); av = avma;

      bp = deriv(b, v);
      d = RgX_gcd(bp, b);
      if (gequal1(d)) {
        d = gsub(gmul(b, deriv(a,v)), gmul(a, bp));
        if (isexactzero(d)) return gerepileupto((pari_sp)(y+3), d);
        gel(y,1) = gerepileupto(av, d);
        gel(y,2) = gsqr(b); return y;
      }
      b0 = gdivexact(b, d);
      bp = gdivexact(bp,d);
      a = gsub(gmul(b0, deriv(a,v)), gmul(a, bp));
      if (isexactzero(a)) return gerepileupto((pari_sp)(y+3), a);
      t = ggcd(a, d);
      if (!gequal1(t)) { a = gdivexact(a, t); d = gdivexact(d, t); }
      gel(y,1) = a;
      gel(y,2) = gmul(d, gsqr(b0));
      return gerepilecopy((pari_sp)(y+3), y);
    }

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = deriv(gel(x,i),v);
      return y;

    case t_CLOSURE:
      if (v==-1) return closure_deriv(x);
  }
  pari_err(typeer,"deriv");
  return NULL; /* not reached */
}

static long
lookup(GEN v, long vx)
{
  long i ,l = lg(v);
  for(i=1; i<l; i++)
    if (varn(gel(v,i)) == vx) return i;
  return 0;
}

GEN
diffop(GEN x, GEN v, GEN dv)
{
  pari_sp av;
  long i, idx, lx, tx = typ(x), vx;
  GEN y;
  if (!is_vec_t(typ(v)) || !is_vec_t(typ(dv)))
    pari_err(typeer,"diffop");
  if (lg(v)!=lg(dv))
    pari_err(talker,"different number of variables and values");
  if (is_const_t(tx)) return gen_0;
  switch(tx)
  {
    case t_POLMOD:
      av = avma;
      vx  = varn(gel(x,1)); idx = lookup(v,vx);
      if (idx) /*Assume the users now what they are doing */
        y = gmodulo(diffop(gel(x,2),v,dv), gel(x,1));
      else
      {
        GEN m = gel(x,1), pol=gel(x,2);
        GEN u = gneg(gdiv(diffop(m,v,dv),RgX_deriv(m)));
        y = diffop(pol,v,dv);
        if (typ(pol)==t_POL && varn(pol)==varn(m))
          y = gadd(y, gmul(u,RgX_deriv(pol)));
        y = gmodulo(y, gel(x,1));
      }
      return gerepileupto(av, y);
    case t_POL:
      if (signe(x)==0) return gen_0;
      vx  = varn(x); idx = lookup(v,vx);
      av = avma; lx = lg(x);
      y = diffop(gel(x,lx-1),v,dv);
      for (i=lx-2; i>=2; i--) y = gadd(gmul(y,pol_x(vx)),diffop(gel(x,i),v,dv));
      if (idx) y = gadd(y, gmul(gel(dv,idx),RgX_deriv(x)));
      return gerepileupto(av, y);

    case t_SER:
      if (signe(x)==0) return gen_0;
      vx  = varn(x); idx = lookup(v,vx);
      if (!idx) return gen_0;
      av = avma;
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = diffop(gel(x,i),v,dv);
      y = normalize(y); /* y is probably invalid */
      y = gsubst(y, vx, pol_x(vx)); /* Fix that */
      y = gadd(y, gmul(gel(dv,idx),derivser(x)));
      return gerepileupto(av, y);

    case t_RFRAC: {
      GEN a = gel(x,1), b = gel(x,2), ap, bp;
      av = avma;
      ap = diffop(a, v, dv); bp = diffop(b, v, dv);
      y = gsub(gdiv(ap,b),gdiv(gmul(a,bp),gsqr(b)));
      return gerepileupto(av, y);
    }

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = diffop(gel(x,i),v,dv);
      return y;

  }
  pari_err(typeer,"diffop");
  return NULL; /* not reached */
}

GEN
diffop0(GEN x, GEN v, GEN dv, long n)
{
  pari_sp av=avma;
  long i;
  for(i=1; i<=n; i++)
    x = gerepileupto(av, diffop(x,v,dv));
  return x;
}

/********************************************************************/
/**                                                                **/
/**                         TAYLOR SERIES                          **/
/**                                                                **/
/********************************************************************/
/* swap vars (vx,v) in x (assume vx < v, vx main variable in x), then call
 * act(data, v, x). FIXME: use in other places */
static GEN
swapvar_act(GEN x, long vx, long v, GEN (*act)(void*, long, GEN), void *data)
{
  GEN y;
  if (v != MAXVARN) { /* (vx,v) -> (MAXVARN, v) */
    y = act(data, v, gsubst(x,vx,pol_x(MAXVARN)));
    y = gsubst(y,MAXVARN,pol_x(vx));
  } else if (vx != 0) { /* (vx,v) -> (vx, 0) */
    y = act(data, 0, gsubst(x,v,pol_x(0)));
    y = gsubst(y,0,pol_x(v));
  } else { /* (0,MAXVARN) -> (w, 0) */
    long w = fetch_var();
    y = act(data, 0, gsubst(gsubst(x,0,pol_x(w)), MAXVARN,pol_x(0)));
    y = gsubst(gsubst(y,0,pol_x(MAXVARN)), w,pol_x(0));
    (void)delete_var();
  }
  return y;
}
/* x + O(v^data) */
static GEN
tayl_act(void *data, long v, GEN x) { return gadd(zeroser(v, (long)data), x); }
static  GEN
integ_act(void *data, long v, GEN x) { (void)data; return integ(x,v); }

GEN
tayl(GEN x, long v, long precS)
{
  long vx = gvar9(x);
  pari_sp av;

  if (varncmp(v, vx) <= 0) return gadd(zeroser(v,precS), x);
  av = avma;
  return gerepileupto(av, swapvar_act(x, vx, v, tayl_act, (void*)precS));
}

GEN
ggrando(GEN x, long n)
{
  long m, v;

  switch(typ(x))
  {
  case t_INT:/* bug 3 + O(1). We suppose x is a truc() */
    if (signe(x) <= 0) pari_err(talker,"non-positive argument in O()");
    if (!is_pm1(x)) return zeropadic(x,n);
    /* +/-1 = x^0 */
    v = m = 0; break;
  case t_POL:
    if (!signe(x)) pari_err(talker,"zero argument in O()");
    v = varn(x); if ((ulong)v > MAXVARN) pari_err(talker,"incorrect object in O()");
    m = n * RgX_val(x); break;
  case t_RFRAC:
    if (!gequal0(gel(x,1))) pari_err(talker,"zero argument in O()");
    v = gvar(x); if ((ulong)v > MAXVARN) pari_err(talker,"incorrect object in O()");
    m = n * gval(x,v); break;
    default: pari_err(talker,"incorrect argument in O()");
      v = m = 0; /* not reached */
  }
  return zeroser(v,m);
}

/*******************************************************************/
/*                                                                 */
/*                    FORMAL INTEGRATION                           */
/*                                                                 */
/*******************************************************************/

static GEN
triv_integ(GEN x, long v)
{
  long i, lx;
  GEN y = cgetg_copy(x, &lx); y[1] = x[1];
  for (i=2; i<lx; i++) gel(y,i) = integ(gel(x,i),v);
  return y;
}

GEN
integ(GEN x, long v)
{
  long lx, tx, e, i, vx, n;
  pari_sp av = avma;
  GEN y,p1;

  tx = typ(x);
  if (v < 0) { v = gvar(x); if (v == NO_VARIABLE) v = 0; }
  if (is_scalar_t(tx))
  {
    if (tx == t_POLMOD && varncmp(v, varn(x[1])) > 0)
    {
      y = cgetg(3,t_POLMOD);
      gel(y,1) = gcopy(gel(x,1));
      gel(y,2) = integ(gel(x,2),v); return y;
    }
    if (gequal0(x)) return gen_0;
    return deg1pol(x, gen_0, v);
  }

  switch(tx)
  {
    case t_POL:
      vx = varn(x); lx = lg(x);
      if (lx == 2) {
        if (varncmp(vx, v) < 0) v = vx;
        return zeropol(v);
      }
      if (varncmp(vx, v) > 0) return deg1pol(x, gen_0, v);
      if (varncmp(vx, v) < 0) return triv_integ(x,v);
      y = cgetg(lx+1, t_POL); y[1] = x[1]; gel(y,2) = gen_0;
      for (i=3; i<=lx; i++) gel(y,i) = gdivgs(gel(x,i-1),i-2);
      return y;

    case t_SER:
      lx = lg(x); vx = varn(x); e = valp(x);
      if (lx == 2)
      {
        if (vx == v) e++; else if (varncmp(vx, v) < 0) v = vx;
        return zeroser(v, e);
      }
      if (varncmp(vx, v) > 0)
      {
        y = cgetg(4,t_POL);
        y[1] = evalvarn(v) | evalsigne(1);
        gel(y,2) = gen_0;
        gel(y,3) = gcopy(x); return y;
      }
      if (varncmp(vx, v) < 0) return triv_integ(x,v);
      y = cgetg(lx, t_SER);
      for (i=2; i<lx; i++)
      {
        long j = i+e-1;
        if (!j)
        { /* should be isexactzero, but try to avoid error */
          if (gequal0(gel(x,i))) { gel(y,i) = gen_0; continue; }
          pari_err(talker, "a log appears in intformal");
        }
        else gel(y,i) = gdivgs(gel(x,i),j);
      }
      y[1] = evalsigne(1) | evalvarn(vx) | evalvalp(e+1); return y;

    case t_RFRAC:
      vx = gvar(x);
      if (varncmp(vx, v) > 0)
      {
        y=cgetg(4,t_POL);
        y[1] = signe(x[1])? evalvarn(v) | evalsigne(1)
                          : evalvarn(v);
        gel(y,2) = gen_0;
        gel(y,3) = gcopy(x); return y;
      }
      if (varncmp(vx, v) < 0)
        return gerepileupto(av, swapvar_act(x, vx, v, integ_act, NULL));

      tx = typ(x[1]); i = is_scalar_t(tx)? 0: degpol(gel(x,1));
      tx = typ(x[2]); n = is_scalar_t(tx)? 0: degpol(gel(x,2));
      y = integ(gadd(x, zeroser(v,i+n + 2)), v);
      y = gdiv(gtrunc(gmul(gel(x,2), y)), gel(x,2));
      if (!gequal(deriv(y,v),x)) pari_err(talker,"a log/atan appears in intformal");
      if (typ(y)==t_RFRAC && lg(y[1]) == lg(y[2]))
      {
        GEN p2;
        tx=typ(y[1]); p1=is_scalar_t(tx)? gel(y,1): leading_term(gel(y,1));
        tx=typ(y[2]); p2=is_scalar_t(tx)? gel(y,2): leading_term(gel(y,2));
        y = gsub(y, gdiv(p1,p2));
      }
      return gerepileupto(av,y);

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lg(x); i++) gel(y,i) = integ(gel(x,i),v);
      return y;
  }
  pari_err(typeer,"integ");
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                    PARTIES ENTIERES                             */
/*                                                                 */
/*******************************************************************/

GEN
gfloor(GEN x)
{
  GEN y;
  long i, lx;

  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_POL: return gcopy(x);
    case t_REAL: return floorr(x);
    case t_FRAC: return truedivii(gel(x,1),gel(x,2));
    case t_RFRAC: return gdeuc(gel(x,1),gel(x,2));
    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gfloor(gel(x,i));
      return y;
  }
  pari_err(typeer,"gfloor");
  return NULL; /* not reached */
}

GEN
gfrac(GEN x)
{
  pari_sp av = avma, tetpil;
  GEN p1 = gneg_i(gfloor(x));
  tetpil = avma; return gerepile(av,tetpil,gadd(x,p1));
}

/* assume x t_REAL */
GEN
ceilr(GEN x) {
  pari_sp av = avma;
  GEN y = floorr(x);
  if (cmpri(x, y)) return gerepileuptoint(av, addsi(1,y));
  return y;
}

GEN
gceil(GEN x)
{
  GEN y, p1;
  long i, lx;
  pari_sp av;

  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_POL: return gcopy(x);
    case t_REAL: return ceilr(x);
    case t_FRAC:
      av = avma; y = dvmdii(gel(x,1),gel(x,2),&p1);
      if (p1 != gen_0 && signe(gel(x,1)) > 0)
      {
        cgiv(p1);
        return gerepileuptoint(av, addsi(1,y));
      }
      return y;

    case t_RFRAC:
      return gdeuc(gel(x,1),gel(x,2));

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gceil(gel(x,i));
      return y;
  }
  pari_err(typeer,"gceil");
  return NULL; /* not reached */
}

GEN
round0(GEN x, GEN *pte)
{
  if (pte) { long e; x = grndtoi(x,&e); *pte = stoi(e); }
  return ground(x);
}

/* assume x a t_REAL */
GEN
roundr(GEN x)
{
  long ex, s = signe(x);
  pari_sp av;
  GEN t;
  if (!s || (ex=expo(x)) < -1) return gen_0;
  if (ex == -1) return s>0? gen_1:
                            absrnz_equal2n(x)? gen_0: gen_m1;
  av = avma;
  t = addrr(real2n(-1, nbits2prec(ex+1)), x); /* x + 0.5 */
  return gerepileuptoint(av, floorr(t));
}
GEN
roundr_safe(GEN x)
{
  long e1, ex, lx, s = signe(x);
  pari_sp av;
  GEN t, y;

  if (!s || (ex = expo(x)) < -1) return gen_0;
  if (ex == -1) return s>0? gen_1:
                            absrnz_equal2n(x)? gen_0: gen_m1;
  av = avma;
  t = addrr(real2n(-1,nbits2prec(ex+1)), x); /* x + 0.5 */

  lx = lg(x);
  e1 = expo(t) - bit_accuracy(lx) + 1;
  y = trunc2nr_lg(t, lx, e1);
  if (signe(x) < 0) y = addsi(-1,y);
  return gerepileuptoint(av,y);
}

GEN
ground(GEN x)
{
  GEN y;
  long i, lx;
  pari_sp av;

  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_INTMOD: case t_QUAD: return gcopy(x);
    case t_REAL: return roundr(x);
    case t_FRAC: return diviiround(gel(x,1), gel(x,2));
    case t_POLMOD: y=cgetg(3,t_POLMOD);
      gel(y,1) = gcopy(gel(x,1));
      gel(y,2) = ground(gel(x,2)); return y;

    case t_COMPLEX:
      av = avma; y = cgetg(3, t_COMPLEX);
      gel(y,2) = ground(gel(x,2));
      if (!signe(y[2])) { avma = av; return ground(gel(x,1)); }
      gel(y,1) = ground(gel(x,1)); return y;

    case t_POL:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = ground(gel(x,i));
      return normalizepol_lg(y, lx);
    case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = ground(gel(x,i));
      return normalize(y);
    case t_RFRAC:
      y = cgetg(3, t_RFRAC);
      gel(y,1) = ground(gel(x,1));
      gel(y,2) = ground(gel(x,2)); return y;
    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = ground(gel(x,i));
      return y;
  }
  pari_err(typeer,"ground");
  return NULL; /* not reached */
}

/* e = number of error bits on integral part */
GEN
grndtoi(GEN x, long *e)
{
  GEN y;
  long i, lx, e1;
  pari_sp av;

  *e = -(long)HIGHEXPOBIT;
  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_REAL: {
      long ex = expo(x);
      GEN t;
      if (!signe(x) || ex < -1) { *e = ex; return gen_0; }
      av = avma;
      /* ex+2 since we may have ex = -1 */
      t = addrr(real2n(-1,nbits2prec(ex+2)), x); e1 = expo(t);
      if (e1 < 0)
      {
        if (signe(t) >= 0) { *e = ex; avma = av; return gen_0; }
        *e = expo(addsr(1,x)); avma = av; return gen_m1;
      }
      lx = lg(x);
      e1 = e1 - bit_accuracy(lx) + 1;
      y = trunc2nr_lg(t, lx, e1);
      if (signe(x) < 0) y = addsi(-1,y);
      y = gerepileuptoint(av,y);

      if (e1 <= 0) { av = avma; e1 = expo(subri(x,y)); avma = av; }
      *e = e1; return y;
    }
    case t_FRAC: return diviiround(gel(x,1), gel(x,2));
    case t_INTMOD: case t_QUAD: return gcopy(x);
    case t_COMPLEX:
      av = avma; y = cgetg(3, t_COMPLEX);
      gel(y,2) = grndtoi(gel(x,2), e);
      if (!signe(y[2])) {
        avma = av;
        y = grndtoi(gel(x,1), &e1);
      }
      else
        gel(y,1) = grndtoi(gel(x,1), &e1);
      if (e1 > *e) *e = e1;
      return y;

    case t_POLMOD: y = cgetg(3,t_POLMOD);
      gel(y,1) = gcopy(gel(x,1));
      gel(y,2) = grndtoi(gel(x,2), e); return y;

    case t_POL:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++)
      {
        gel(y,i) = grndtoi(gel(x,i),&e1);
        if (e1 > *e) *e = e1;
      }
      return normalizepol_lg(y, lx);
    case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++)
      {
        gel(y,i) = grndtoi(gel(x,i),&e1);
        if (e1 > *e) *e = e1;
      }
      return normalize(y);
    case t_RFRAC:
      y = cgetg(3,t_RFRAC);
      gel(y,1) = grndtoi(gel(x,1),&e1); if (e1 > *e) *e = e1;
      gel(y,2) = grndtoi(gel(x,2),&e1); if (e1 > *e) *e = e1;
      return y;
    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++)
      {
        gel(y,i) = grndtoi(gel(x,i),&e1);
        if (e1 > *e) *e = e1;
      }
      return y;
  }
  pari_err(typeer,"grndtoi");
  return NULL; /* not reached */
}

/* trunc(x * 2^s). lindep() sanity checks rely on this function to return a
 * t_INT or fail when fed a non-t_COMPLEX input; so do not make this one
 * recursive [ or change the lindep call ] */
GEN
gtrunc2n(GEN x, long s)
{
  GEN z;
  switch(typ(x))
  {
    case t_INT:  return shifti(x, s);
    case t_REAL: return trunc2nr(x, s);
    case t_FRAC: {
      pari_sp av;
      GEN a = gel(x,1), b = gel(x,2), q;
      if (s == 0) return divii(a, b);
      av = avma;
      if (s < 0) q = divii(shifti(a, s), b);
      else {
        GEN r;
        q = dvmdii(a, b, &r);
        q = addii(shifti(q,s), divii(shifti(r,s), b));
      }
      return gerepileuptoint(av, q);
    }
    case t_COMPLEX:
      z = cgetg(3, t_COMPLEX);
      gel(z,2) = gtrunc2n(gel(x,2), s);
      if (!signe(gel(z,2))) {
        avma = (pari_sp)(z + 3);
        return gtrunc2n(gel(x,1), s);
      }
      gel(z,1) = gtrunc2n(gel(x,1), s);
      return z;
    default: pari_err(typeer,"gtrunc2n");
      return NULL; /* not reached */
  }
}

/* e = number of error bits on integral part */
GEN
gcvtoi(GEN x, long *e)
{
  long tx = typ(x), lx, i, ex, e1;
  GEN y;

  if (tx == t_REAL)
  {
    ex = expo(x); if (ex < 0) { *e = ex; return gen_0; }
    lx = lg(x); e1 = ex - bit_accuracy(lx) + 1;
    y = trunc2nr_lg(x, lx, e1);
    if (e1 <= 0) { pari_sp av = avma; e1 = expo(subri(x,y)); avma = av; }
    *e = e1; return y;
  }
  *e = -(long)HIGHEXPOBIT;
  if (is_matvec_t(tx))
  {
    y = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++)
    {
      gel(y,i) = gcvtoi(gel(x,i),&e1);
      if (e1 > *e) *e = e1;
    }
    return y;
  }
  return gtrunc(x);
}

int
isint(GEN n, GEN *ptk)
{
  switch(typ(n))
  {
    case t_INT: *ptk = n; return 1;
    case t_REAL: {
      pari_sp av0 = avma;
      GEN z = floorr(n);
      pari_sp av = avma;
      long s = signe(subri(n, z));
      if (s) { avma = av0; return 0; }
      *ptk = z; avma = av; return 1;
    }
    case t_FRAC:    return 0;
    case t_COMPLEX: return gequal0(gel(n,2)) && isint(gel(n,1),ptk);
    case t_QUAD:    return gequal0(gel(n,3)) && isint(gel(n,2),ptk);
    default: pari_err(typeer,"isint"); return 0; /* not reached */
  }
}

int
issmall(GEN n, long *ptk)
{
  pari_sp av = avma;
  GEN z;
  long k;
  if (!isint(n, &z)) return 0;
  k = itos_or_0(z); avma = av;
  if (k || lgefint(z) == 2) { *ptk = k; return 1; }
  return 0;
}

/* smallest integer greater than any incarnations of the real x
 * Avoid "precision loss in truncation" */
GEN
ceil_safe(GEN x)
{
  pari_sp av = avma;
  long e, tx = typ(x);
  GEN y;

  if (is_rational_t(tx)) return gceil(x);
  y = gcvtoi(x,&e);
  if (gsigne(x) >= 0)
  {
    if (e < 0) e = 0;
    y = addii(y, int2n(e));
  }
  return gerepileuptoint(av, y);
}
/* largest integer smaller than any incarnations of the real x
 * Avoid "precision loss in truncation" */
GEN
floor_safe(GEN x)
{
  pari_sp av = avma;
  long e, tx = typ(x);
  GEN y;

  if (is_rational_t(tx)) return gfloor(x);
  y = gcvtoi(x,&e);
  if (gsigne(x) <= 0)
  {
    if (e < 0) e = 0;
    y = subii(y, int2n(e));
  }
  return gerepileuptoint(av, y);
}

GEN
ser2rfrac_i(GEN x)
{
  long e = valp(x);
  GEN a = ser2pol_i(x, lg(x));
  if (e) {
    if (e > 0) a = RgX_shift_shallow(a, e);
    else a = gred_rfrac_simple(a, monomial(gen_1, -e, varn(a)));
  }
  return a;
}

static GEN
ser2rfrac(GEN x)
{
  pari_sp av = avma;
  return gerepilecopy(av, ser2rfrac_i(x));
}

GEN
gtrunc(GEN x)
{
  long i, v;
  pari_sp av;
  GEN y;

  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_REAL: return truncr(x);
    case t_FRAC: return divii(gel(x,1),gel(x,2));

    case t_PADIC:
      if (!signe(x[4])) return gen_0;
      v = valp(x);
      if (!v) return icopy(gel(x,4));
      if (v>0)
      { /* here p^v is an integer */
        av = avma; y = powiu(gel(x,2),v);
        return gerepileuptoint(av, mulii(y,gel(x,4)));
      }
      y = cgetg(3,t_FRAC);
      gel(y,1) = icopy(gel(x,4));
      gel(y,2) = powiu(gel(x,2),-v);
      return y;

    case t_POL: return gcopy(x);
    case t_RFRAC:
      return gdeuc(gel(x,1),gel(x,2));

    case t_SER:
      return ser2rfrac(x);

    case t_VEC: case t_COL: case t_MAT:
    {
      long lx;
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gtrunc(gel(x,i));
      return y;
    }
  }
  pari_err(typeer,"gtrunc");
  return NULL; /* not reached */
}

GEN
trunc0(GEN x, GEN *pte)
{
  if (pte) { long e; x = gcvtoi(x,&e); *pte = stoi(e); }
  return gtrunc(x);
}
/*******************************************************************/
/*                                                                 */
/*                  CONVERSIONS -->  INT, POL & SER                */
/*                                                                 */
/*******************************************************************/

/* return a_(n-1) B^(n-1) + ... + a_0, where B = 2^32.
 * The a_i are 32bits integers */
GEN
mkintn(long n, ...)
{
  va_list ap;
  GEN x, y;
  long i;
#ifdef LONG_IS_64BIT
  long e = (n&1);
  n = (n+1) >> 1;
#endif
  va_start(ap,n);
  x = cgetipos(n+2);
  y = int_MSW(x);
  for (i=0; i <n; i++)
  {
#ifdef LONG_IS_64BIT
    ulong a = (e && !i)? 0: va_arg(ap, long);
    ulong b = va_arg(ap, long);
    *y = (a << 32) | b;
#else
    *y = va_arg(ap, long);
#endif
    y = int_precW(y);
  }
  va_end(ap);
  return int_normalize(x, 0);
}

/* 2^32 a + b */
GEN
uu32toi(ulong a, ulong b)
{
#ifdef LONG_IS_64BIT
  return utoi((a<<32) | b);
#else
  return uutoi(a, b);
#endif
}

/* return a_(n-1) x^(n-1) + ... + a_0 */
GEN
mkpoln(long n, ...)
{
  va_list ap;
  GEN x, y;
  long i, l = n+2;
  va_start(ap,n);
  x = cgetg(l, t_POL); y = x + 2;
  x[1] = evalvarn(0);
  for (i=n-1; i >= 0; i--) gel(y,i) = va_arg(ap, GEN);
  va_end(ap); return normalizepol_lg(x, l);
}

/* return [a_1, ..., a_n] */
GEN
mkvecn(long n, ...)
{
  va_list ap;
  GEN x;
  long i;
  va_start(ap,n);
  x = cgetg(n+1, t_VEC);
  for (i=1; i <= n; i++) gel(x,i) = va_arg(ap, GEN);
  va_end(ap); return x;
}

GEN
mkcoln(long n, ...)
{
  va_list ap;
  GEN x;
  long i;
  va_start(ap,n);
  x = cgetg(n+1, t_COL);
  for (i=1; i <= n; i++) gel(x,i) = va_arg(ap, GEN);
  va_end(ap); return x;
}

GEN
mkvecsmalln(long n, ...)
{
  va_list ap;
  GEN x;
  long i;
  va_start(ap,n);
  x = cgetg(n+1, t_VECSMALL);
  for (i=1; i <= n; i++) gel(x,i) = va_arg(ap, GEN);
  va_end(ap); return x;
}

GEN
scalarpol(GEN x, long v)
{
  GEN y;
  if (isrationalzero(x)) return zeropol(v);
  y = cgetg(3,t_POL);
  y[1] = gequal0(x)? evalvarn(v)
                 : evalvarn(v) | evalsigne(1);
  gel(y,2) = gcopy(x); return y;
}

/* x0 + x1*T, do not assume x1 != 0 */
GEN
deg1pol(GEN x1, GEN x0,long v)
{
  GEN x = cgetg(4,t_POL);
  x[1] = evalsigne(1) | evalvarn(v);
  gel(x,2) = x0 == gen_0? x0: gcopy(x0); /* gen_0 frequent */
  gel(x,3) = gcopy(x1); return normalizepol_lg(x,4);
}

/* same, no copy */
GEN
deg1pol_shallow(GEN x1, GEN x0,long v)
{
  GEN x = cgetg(4,t_POL);
  x[1] = evalsigne(1) | evalvarn(v);
  gel(x,2) = x0;
  gel(x,3) = x1; return normalizepol_lg(x,4);
}

static GEN
_gtopoly(GEN x, long v, int reverse)
{
  long tx = typ(x), lx, i, j;
  GEN y;

  if (v<0) v = 0;
  if (is_scalar_t(tx)) return scalarpol(x,v);
  switch(tx)
  {
    case t_POL:
      if (varncmp(varn(x), v) < 0)
        pari_err(talker,"variable must have higher priority in gtopoly");
      y=gcopy(x); break;
    case t_SER:
      if (varncmp(varn(x), v) < 0)
        pari_err(talker,"variable must have higher priority in gtopoly");
      y = ser2rfrac(x);
      if (typ(y) != t_POL)
        pari_err(talker,"t_SER with negative valuation in gtopoly");
      break;
    case t_RFRAC:
      if (varncmp(varn(gel(x,2)), v) < 0)
        pari_err(talker,"variable must have higher priority in gtopoly");
      y=gdeuc(gel(x,1),gel(x,2)); break;
    case t_QFR: case t_QFI: case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); if (tx == t_QFR) lx--;
      if (varncmp(gvar(x), v) <= 0)
        pari_err(talker,"variable must have higher priority in gtopoly");
      if (reverse)
      { /* cf normalizepol_lg */
        for (i = lx-1; i>0; i--)
          if (! isrationalzero(gel(x,i))) break;
        if (i == 0) return zeropol(v);
        /* not a rational 0, to be kept iff all other coeffs are exact 0s */
        y = gel(x,i);
        for (; i>0; i--)
          if (! isexactzero(gel(x,i))) break;
        if (i == 0) return scalarpol(y, v);

        for (j = i; j>0; j--)
          if (! gequal0(gel(x,j))) break;
        i += 2;
        y = cgetg(i,t_POL);
        y[1] = evalvarn(v) | evalsigne((j == 0)? 0: 1);
        for (j=2; j<i; j++) gel(y,j) = gcopy(gel(x,j-1));
        return y;
      }
      else
      {
        for (i = 1; i<lx; i++)
          if (! isrationalzero(gel(x,i))) break;
        if (i == lx) return zeropol(v);
        /* not a rational 0, to be kept iff all other coeffs are exact 0s */
        y = gel(x,i);
        for (; i<lx; i++)
          if (! isexactzero(gel(x,i))) break;
        if (i == lx) return scalarpol(y, v);

        for (j = i; j<lx; j++)
          if (! gequal0(gel(x,j))) break;
        i = lx-i+2;
        y = cgetg(i, t_POL);
        y[1] = evalvarn(v) | evalsigne((j == lx)? 0: 1);
        for (j=2; j<i; j++) gel(y,j) = gcopy(gel(x,--lx));
        return y;
      }
      break;
    default: pari_err(typeer,"gtopoly");
      return NULL; /* not reached */
  }
  setvarn(y,v); return y;
}

GEN
gtopolyrev(GEN x, long v) { return _gtopoly(x,v,1); }

GEN
gtopoly(GEN x, long v) { return _gtopoly(x,v,0); }

GEN
scalarser(GEN x, long v, long prec)
{
  long i, l;
  GEN y;

  if (isrationalzero(x)) return zeroser(v,0);
  if (isexactzero(x))
  {
    y = cgetg(3, t_SER);
    y[1] = evalsigne(0) | _evalvalp(0) | evalvarn(v);
    gel(y,2) = gcopy(x); return y;
  }
  l = prec + 2; y = cgetg(l, t_SER);
  y[1] = evalsigne(gequal0(x)? 0: 1) | _evalvalp(0) | evalvarn(v);
  gel(y,2) = gcopy(x); for (i=3; i<l; i++) gel(y,i) = gen_0;
  return y;
}

/* assume x a t_[SER|POL], apply gtoser to all coeffs */
static GEN
coefstoser(GEN x, long v, long prec)
{
  long i, lx;
  GEN y = cgetg_copy(x, &lx); y[1] = x[1];
  for (i=2; i<lx; i++) gel(y,i) = gtoser(gel(x,i), v, prec);
  return y;
}

/* x a t_POL. Not stack-clean */
GEN
poltoser(GEN x, long v, long prec)
{
  long vx = varn(x);
  GEN y;

  if (varncmp(vx, v) > 0) return scalarser(x, v, prec);
  if (varncmp(vx, v) < 0) return coefstoser(x, v, prec);
  if (!lgpol(x)) return zeroser(v, prec);
  y = RgX_to_ser(x, prec+2);
  setvarn(y, v); return y;
}

/* x a t_RFRAC. Not stack-clean */
GEN
rfractoser(GEN x, long v, long prec)
{
  GEN n = gel(x,1);
  if (is_scalar_t(typ(n)))
    n = scalarser(n, v, prec);
  else
    n = poltoser(n, v, prec);
  return gdiv(n, poltoser(gel(x,2), v, prec));
}

GEN
toser_i(GEN x)
{
  switch(typ(x))
  {
    case t_SER: return x;
    case t_POL: return poltoser(x, varn(x), precdl);
    case t_RFRAC: return rfractoser(x, gvar(x), precdl);
  }
  return NULL;
}

GEN
gtoser(GEN x, long v, long prec)
{
  long tx=typ(x), lx, i, j, l;
  pari_sp av;
  GEN y;

  if (v < 0) v = 0;
  if (tx == t_SER)
  {
    long vx = varn(x);
    if      (varncmp(vx, v) < 0) y = coefstoser(x, v, prec);
    else if (varncmp(vx, v) > 0) y = scalarser(x, v, prec);
    else y = gcopy(x);
    return y;
  }
  if (is_scalar_t(tx)) return scalarser(x,v,prec);
  switch(tx)
  {
    case t_POL:
      if (varncmp(varn(x), v) < 0)
        pari_err(talker,"main variable must have higher priority in gtoser");
      y = poltoser(x, v, prec); l = lg(y);
      for (i=2; i<l; i++)
        if (gel(y,i) != gen_0) gel(y,i) = gcopy(gel(y,i));
      break;

    case t_RFRAC:
      if (varncmp(varn(gel(x,2)), v) < 0)
        pari_err(talker,"main variable must have higher priority in gtoser");
      av = avma;
      return gerepileupto(av, rfractoser(x, v, prec));

    case t_QFR: case t_QFI: case t_VEC: case t_COL:
      if (varncmp(gvar(x), v) <= 0)
        pari_err(talker,"main variable must have higher priority in gtoser");
      lx = lg(x); if (tx == t_QFR) lx--;
      for (i=1; i < lx; i++)
        if (!isrationalzero(gel(x,i))) break;
      if (i == lx) return zeroser(v, lx-1);
      y = gel(x,i);
      for (; i<lx; i++)
        if (!isexactzero(gel(x,i))) break;
      if (i == lx)
      {
        GEN z = cgetg(3, t_SER);
        z[1] = evalsigne(0) | evalvalp(i-2) | evalvarn(v);
        gel(z,2) = gcopy(y); return z;
      }

      lx -= i-2; x += i-2;
      y = cgetg(lx,t_SER);
      y[1] = evalsigne(1) | evalvalp(i-1) | evalvarn(v);
      for (j=2; j<lx; j++) gel(y,j) = gcopy(gel(x,j));
      break;

    default: pari_err(typeer,"gtoser");
      return NULL; /* not reached */
  }
  return y;
}

GEN
gtovec(GEN x)
{
  long tx, lx, i;
  GEN y;

  if (!x) return cgetg(1,t_VEC);
  tx = typ(x);
  if (is_scalar_t(tx)) return mkveccopy(x);
  switch(tx)
  {
    case t_POL:
      lx=lg(x); y=cgetg(lx-1,t_VEC);
      for (i=1; i<=lx-2; i++) gel(y,i) = gcopy(gel(x,lx-i));
      return y;
    case t_SER:
      lx=lg(x); y=cgetg(lx-1,t_VEC); x++;
      for (i=1; i<=lx-2; i++) gel(y,i) = gcopy(gel(x,i));
      return y;
    case t_RFRAC: return mkveccopy(x);
    case t_QFR: case t_QFI: case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,t_VEC);
      for (i=1; i<lx; i++) gel(y,i) = gcopy(gel(x,i));
      return y;
    case t_LIST:
      x = list_data(x); lx = x? lg(x): 1;
      y = cgetg(lx, t_VEC);
      for (i=1; i<lx; i++) gel(y,i) = gcopy(gel(x,i));
      return y;
    case t_STR:
    {
      char *s = GSTR(x);
      lx = strlen(s)+1; y = cgetg(lx, t_VEC);
      s--;
      for (i=1; i<lx; i++) gel(y,i) = chartoGENstr(s[i]);
      return y;
    }
    case t_VECSMALL:
      return vecsmall_to_vec(x);
    default: pari_err(typeer,"gtovec");
      return NULL; /*notreached*/
  }
}

GEN
gtovecrev(GEN x)
{
  GEN y = gtovec(x);
  long ly = lg(y), lim = ly>>1, i;
  for (i = 1; i <= lim; i++) swap(gel(y,i), gel(y,ly-i));
  return y;
}

GEN
gtocol(GEN x)
{
  long lx, tx, i, j, h;
  GEN y;
  if (!x) return cgetg(1,t_COL);
  tx = typ(x);
  if (tx != t_MAT) { y = gtovec(x); settyp(y, t_COL); return y; }
  lx = lg(x); if (lx == 1) return cgetg(1, t_COL);
  h = lg(x[1]); y = cgetg(h, t_COL);
  for (i = 1 ; i < h; i++) {
    gel(y,i) = cgetg(lx, t_VEC);
    for (j = 1; j < lx; j++) gmael(y,i,j) = gcopy(gcoeff(x,i,j));
  }
  return y;
}

GEN
gtovecsmall(GEN x)
{
  GEN V;
  long tx, l,i;

  if (!x) return cgetg(1,t_VECSMALL);
  tx = typ(x);
  if (tx == t_VECSMALL) return gcopy(x);
  if (tx == t_INT) return mkvecsmall(itos(x));
  if (tx == t_STR)
  {
    char *s = GSTR(x);
    l = strlen(s);
    V = cgetg(l+1, t_VECSMALL);
    s--;
    for (i=1; i<=l; i++) V[i] = (long)s[i];
    return V;
  }
  if (!is_vec_t(tx)) pari_err(typeer,"vectosmall");
  l = lg(x);
  V = cgetg(l,t_VECSMALL);
  for(i=1; i<l; i++) {
    GEN y = gel(x,i);
    if (typ(y) != t_INT) pari_err(typeer,"vectosmall");
    V[i] = itos(y);
  }
  return V;
}

GEN
compo(GEN x, long n)
{
  long tx = typ(x);
  ulong l, lx = (ulong)lg(x);

  if (!is_recursive_t(tx))
  {
    if (tx == t_VECSMALL)
    {
      if (n < 1 || (ulong)n >= lx) pari_err(talker,"nonexistent component");
      return stoi(x[n]);
    }
    pari_err(talker, "this object is a leaf. It has no components");
  }
  if (n < 1) pari_err(talker,"nonexistent component");
  if (tx == t_POL && (ulong)n+1 >= lx) return gen_0;
  if (tx == t_LIST) {
    long llx;
    x = list_data(x); llx = x? lg(x): 1;
    lx = (ulong)llx; tx = t_VEC;
  }
  l = (ulong)lontyp[tx] + (ulong)n-1; /* beware overflow */
  if (l >= lx) pari_err(talker,"nonexistent component");
  return gcopy(gel(x,l));
}

/* assume v > varn(x), extract coeff of pol_x(v)^n */
static GEN
multi_coeff(GEN x, long n, long v, long dx)
{
  long i, lx = dx+3;
  GEN z = cgetg(lx, t_POL); z[1] = x[1];
  for (i = 2; i < lx; i++) gel(z,i) = polcoeff_i(gel(x,i), n, v);
  return normalizepol_lg(z, lx);
}

/* assume x a t_POL */
static GEN
_polcoeff(GEN x, long n, long v)
{
  long w, dx;
  dx = degpol(x);
  if (dx < 0) return gen_0;
  if (v < 0 || v == (w=varn(x)))
    return (n < 0 || n > dx)? gen_0: gel(x,n+2);
  if (w > v) return n? gen_0: x;
  /* w < v */
  return multi_coeff(x, n, v, dx);
}

/* assume x a t_SER */
static GEN
_sercoeff(GEN x, long n, long v)
{
  long w, dx = degpol(x), ex = valp(x), N = n - ex;
  GEN z;
  if (dx < 0)
  {
    if (N >= 0) pari_err(talker,"non existent component in truecoeff");
    return gen_0;
  }
  if (v < 0 || v == (w=varn(x)))
  {
    if (N > dx) pari_err(talker,"non existent component in truecoeff");
    return (N < 0)? gen_0: gel(x,N+2);
  }
  if (w > v) return N? gen_0: x;
  /* w < v */
  z = multi_coeff(x, n, v, dx);
  if (ex) z = gmul(z, monomial(gen_1,ex, w));
  return z;
}

/* assume x a t_RFRAC(n) */
static GEN
_rfraccoeff(GEN x, long n, long v)
{
  GEN P,Q, p = gel(x,1), q = gel(x,2);
  long vp = gvar(p), vq = gvar(q);
  if (v < 0) v = minss(vp, vq);
  P = (vp == v)? p: swap_vars(p, v);
  Q = (vq == v)? q: swap_vars(q, v);
  if (!RgX_is_monomial(Q)) pari_err(typeer, "polcoeff");
  n += degpol(Q);
  return gdiv(_polcoeff(P, n, v), leading_term(Q));
}

GEN
polcoeff_i(GEN x, long n, long v)
{
  switch(typ(x))
  {
    case t_POL: return _polcoeff(x,n,v);
    case t_SER: return _sercoeff(x,n,v);
    case t_RFRAC: return _rfraccoeff(x,n,v);
    default: return n? gen_0: x;
  }
}

/* with respect to the main variable if v<0, with respect to the variable v
   otherwise. v ignored if x is not a polynomial/series. */
GEN
polcoeff0(GEN x, long n, long v)
{
  long tx=typ(x);
  pari_sp av;

  if (is_scalar_t(tx)) return n? gen_0: gcopy(x);

  av = avma;
  switch(tx)
  {
    case t_POL: x = _polcoeff(x,n,v); break;
    case t_SER: x = _sercoeff(x,n,v); break;
    case t_RFRAC: x = _rfraccoeff(x,n,v); break;

    case t_QFR: case t_QFI: case t_VEC: case t_COL: case t_MAT:
      if (n>=1 && n<lg(x)) return gcopy(gel(x,n));
    /* fall through */

    default: pari_err(talker,"nonexistent component in truecoeff");
  }
  if (x == gen_0) return x;
  if (avma == av) return gcopy(x);
  return gerepilecopy(av, x);
}

GEN
denom(GEN x)
{
  long lx, i;
  pari_sp av, tetpil;
  GEN s,t;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD: case t_FFELT:
    case t_PADIC: case t_SER:
      return gen_1;

    case t_FRAC:
      return icopy(gel(x,2));

    case t_COMPLEX:
      av=avma; t=denom(gel(x,1)); s=denom(gel(x,2)); tetpil=avma;
      return gerepile(av,tetpil,glcm(s,t));

    case t_QUAD:
      av=avma; t=denom(gel(x,2)); s=denom(gel(x,3)); tetpil=avma;
      return gerepile(av,tetpil,glcm(s,t));

    case t_POLMOD:
      return denom(gel(x,2));

    case t_RFRAC:
      return gcopy(gel(x,2));

    case t_POL:
      return pol_1(varn(x));

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); if (lx==1) return gen_1;
      av = tetpil = avma; s = denom(gel(x,1));
      for (i=2; i<lx; i++)
      {
        t = denom(gel(x,i));
        if (t != gen_1) { tetpil=avma; s=glcm(s,t); }
      }
      return gerepile(av,tetpil,s);
  }
  pari_err(typeer,"denom");
  return NULL; /* not reached */
}

GEN
numer(GEN x)
{
  pari_sp av, tetpil;
  GEN s;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD: case t_FFELT:
    case t_PADIC: case t_POL: case t_SER:
      return gcopy(x);

    case t_FRAC:
      return (signe(x[2])>0)? icopy(gel(x,1)): negi(gel(x,1));

    case t_POLMOD:
      av=avma; s=numer(gel(x,2)); tetpil=avma;
      return gerepile(av,tetpil,gmodulo(s,gel(x,1)));

    case t_RFRAC:
      return gcopy(gel(x,1));

    case t_COMPLEX: case t_QUAD: case t_VEC: case t_COL: case t_MAT:
      av=avma; s=denom(x); tetpil=avma;
      return gerepile(av,tetpil,gmul(s,x));
  }
  pari_err(typeer,"numer");
  return NULL; /* not reached */
}

/* Lift only intmods if v does not occur in x, lift with respect to main
 * variable of x if v < 0, with respect to variable v otherwise.
 */
GEN
lift0(GEN x, long v)
{
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_INT:
      return icopy(x);
    case t_REAL:
      return leafcopy(x);

    case t_INTMOD:
      return icopy(gel(x,2));

    case t_POLMOD:
      if (v < 0 || v == varn(gel(x,1))) return gcopy(gel(x,2));
      y = cgetg(3, t_POLMOD);
      gel(y,1) = lift0(gel(x,1),v);
      gel(y,2) = lift0(gel(x,2),v); return y;

    case t_FRAC: case t_FFELT:
      return gcopy(x);

    case t_PADIC:
      return gtrunc(x);

    case t_POL:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = lift0(gel(x,i), v);
      return normalizepol_lg(y,lx);
    case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = lift0(gel(x,i), v);
      return normalize(y);
    case t_COMPLEX: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = lift0(gel(x,i), v);
      return y;

    case t_QUAD:
      y=cgetg(4,t_QUAD); gel(y,1) = ZX_copy(gel(x,1));
      gel(y,2) = lift0(gel(x,2),v);
      gel(y,3) = lift0(gel(x,3),v); return y;
  }
  pari_err(typeer,"lift");
  return NULL; /* not reached */
}

GEN
lift(GEN x)
{
  return lift0(x,-1);
}

/* same as lift, without copy. May DESTROY x. For internal use only.
   Conventions on v as for lift. */
GEN
lift_intern0(GEN x, long v)
{
  long i;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return x;

    case t_INTMOD:
      return gel(x,2);

    case t_POLMOD:
      if (v < 0 || v == varn(gel(x,1))) return gel(x,2);
      gel(x,1) = lift_intern0(gel(x,1),v);
      gel(x,2) = lift_intern0(gel(x,2),v);
      return x;

    case t_SER: case t_POL:
      for (i = lg(x)-1; i>=2; i--)
        gel(x,i) = lift_intern0(gel(x,i),v);
      return x;
    case t_COMPLEX: case t_QUAD:
    case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      for (i = lg(x)-1; i>=1; i--)
        gel(x,i) = lift_intern0(gel(x,i),v);
      return x;
  }
  pari_err(typeer,"lift_intern");
  return NULL; /* not reached */
}

static GEN
centerliftii(GEN x, GEN y)
{
  pari_sp av = avma;
  long i = cmpii(shifti(x,1), y);
  avma = av; return (i > 0)? subii(x,y): icopy(x);
}

/* see lift0 */
GEN
centerlift0(GEN x, long v)
{
  long i, lx;
  GEN y;

  switch(typ(x))
  {
    case t_INT:
      return icopy(x);
    case t_INTMOD:
      return centerliftii(gel(x,2), gel(x,1));

    case t_POLMOD:
      if (v < 0 || v == varn(gel(x,1))) return gcopy(gel(x,2));
      y = cgetg(3, t_POLMOD);
      gel(y,1) = centerlift0(gel(x,1),v);
      gel(y,2) = centerlift0(gel(x,2),v); return y;
    case t_FRAC:
      return gcopy(x);
   case t_POL: case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = centerlift0(gel(x,i),v);
      return y;
   case t_COMPLEX: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = centerlift0(gel(x,i),v);
      return y;

    case t_QUAD:
      y=cgetg(4,t_QUAD); gel(y,1) = ZX_copy(gel(x,1));
      gel(y,2) = centerlift0(gel(x,2),v);
      gel(y,3) = centerlift0(gel(x,3),v); return y;

    case t_PADIC:
      if (!signe(x[4])) return gen_0;
      v = valp(x);
      if (v>=0)
      { /* here p^v is an integer */
        GEN z =  centerliftii(gel(x,4), gel(x,3));
        pari_sp av;
        if (!v) return z;
        av = avma; y = powiu(gel(x,2),v);
        return gerepileuptoint(av, mulii(y,z));
      }
      y = cgetg(3,t_FRAC);
      gel(y,1) = centerliftii(gel(x,4), gel(x,3));
      gel(y,2) = powiu(gel(x,2),-v);
      return y;
  }
  pari_err(typeer,"centerlift");
  return NULL; /* not reached */
}

GEN
centerlift(GEN x)
{
  return centerlift0(x,-1);
}

/*******************************************************************/
/*                                                                 */
/*                      REAL & IMAGINARY PARTS                     */
/*                                                                 */
/*******************************************************************/

static GEN
op_ReIm(GEN f(GEN), GEN x)
{
  long lx, i, j;
  pari_sp av;
  GEN z;

  switch(typ(x))
  {
    case t_POL:
      z = cgetg_copy(x, &lx); z[1] = x[1];
      for (j=2; j<lx; j++) gel(z,j) = f(gel(x,j));
      return normalizepol_lg(z, lx);

    case t_SER:
      z = cgetg_copy(x, &lx); z[1] = x[1];
      for (j=2; j<lx; j++) gel(z,j) = f(gel(x,j));
      return normalize(z);

    case t_RFRAC: {
      GEN dxb, n, d;
      av = avma; dxb = gconj(gel(x,2));
      n = gmul(gel(x,1), dxb);
      d = gmul(gel(x,2), dxb);
      return gerepileupto(av, gdiv(f(n), d));
    }

    case t_VEC: case t_COL: case t_MAT:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(z,i) = f(gel(x,i));
      return z;
  }
  pari_err(typeer,"greal/gimag");
  return NULL; /* not reached */
}

GEN
real_i(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return x;
    case t_COMPLEX:
      return gel(x,1);
    case t_QUAD:
      return gel(x,2);
  }
  return op_ReIm(real_i,x);
}
GEN
imag_i(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return gen_0;
    case t_COMPLEX:
      return gel(x,2);
    case t_QUAD:
      return gel(x,3);
  }
  return op_ReIm(imag_i,x);
}
GEN
greal(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return gcopy(x);

    case t_COMPLEX:
      return gcopy(gel(x,1));

    case t_QUAD:
      return gcopy(gel(x,2));
  }
  return op_ReIm(greal,x);
}
GEN
gimag(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return gen_0;

    case t_COMPLEX:
      return gcopy(gel(x,2));

    case t_QUAD:
      return gcopy(gel(x,3));
  }
  return op_ReIm(gimag,x);
}

/* return Re(x * y), x and y scalars */
GEN
mulreal(GEN x, GEN y)
{
  if (typ(x) == t_COMPLEX)
  {
    if (typ(y) == t_COMPLEX)
    {
      pari_sp av = avma;
      GEN a = gmul(gel(x,1), gel(y,1));
      GEN b = gmul(gel(x,2), gel(y,2));
      return gerepileupto(av, gsub(a, b));
    }
    x = gel(x,1);
  }
  else
    if (typ(y) == t_COMPLEX) y = gel(y,1);
  return gmul(x,y);
}
/* Compute Re(x * y), x and y matrices of compatible dimensions
 * assume scalar entries */
GEN
RgM_mulreal(GEN x, GEN y)
{
  long i, j, k, l, lx = lg(x), ly = lg(y);
  GEN z = cgetg(ly,t_MAT);
  l = (lx == 1)? 1: lg(x[1]);
  for (j=1; j<ly; j++)
  {
    GEN zj = cgetg(l,t_COL), yj = gel(y,j);
    gel(z,j) = zj;
    for (i=1; i<l; i++)
    {
      pari_sp av = avma;
      GEN c = mulreal(gcoeff(x,i,1),gel(yj,1));
      for (k=2; k<lx; k++) c = gadd(c, mulreal(gcoeff(x,i,k),gel(yj,k)));
      gel(zj, i) = gerepileupto(av, c);
    }
  }
  return z;
}

/*******************************************************************/
/*                                                                 */
/*                     LOGICAL OPERATIONS                          */
/*                                                                 */
/*******************************************************************/
static long
_egal(GEN x, GEN y)
{
  pari_sp av = avma;
  long r = gequal(simplify_shallow(x), simplify_shallow(y));
  avma = av; return r;
}

GEN
glt(GEN x, GEN y) { return gcmp(x,y)<0? gen_1: gen_0; }

GEN
gle(GEN x, GEN y) { return gcmp(x,y)<=0? gen_1: gen_0; }

GEN
gge(GEN x, GEN y) { return gcmp(x,y)>=0? gen_1: gen_0; }

GEN
ggt(GEN x, GEN y) { return gcmp(x,y)>0? gen_1: gen_0; }

GEN
geq(GEN x, GEN y) { return _egal(x,y)? gen_1: gen_0; }

GEN
gne(GEN x, GEN y) { return _egal(x,y)? gen_0: gen_1; }

GEN
gand(GEN x, GEN y) { return gequal0(x)? gen_0: (gequal0(y)? gen_0: gen_1); }

GEN
gor(GEN x, GEN y) { return gequal0(x)? (gequal0(y)? gen_0: gen_1): gen_1; }

GEN
gnot(GEN x) { return gequal0(x)? gen_1: gen_0; }

/*******************************************************************/
/*                                                                 */
/*                      FORMAL SIMPLIFICATIONS                     */
/*                                                                 */
/*******************************************************************/

GEN
geval_gp(GEN x, GEN t)
{
  long lx, i, tx = typ(x);
  pari_sp av;
  GEN y, z;

  if (is_const_t(tx)) return gcopy(x);
  switch(tx)
  {
    case t_STR:
      return localvars_read_str(GSTR(x),t);

    case t_POLMOD:
      av = avma;
      return gerepileupto(av, gmodulo(geval_gp(gel(x,2),t),
                                      geval_gp(gel(x,1),t)));

    case t_POL:
      lx=lg(x); if (lx==2) return gen_0;
      z = fetch_var_value(varn(x),t);
      if (!z) return gcopy(x);
      av = avma; y = geval_gp(gel(x,lx-1),t);
      for (i=lx-2; i>1; i--)
        y = gadd(geval_gp(gel(x,i),t), gmul(z,y));
      return gerepileupto(av, y);

    case t_SER:
      pari_err(impl, "evaluation of a power series");

    case t_RFRAC:
      av = avma;
      return gerepileupto(av, gdiv(geval_gp(gel(x,1),t), geval_gp(gel(x,2),t)));

    case t_QFR: case t_QFI: case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = geval_gp(gel(x,i),t);
      return y;

    case t_CLOSURE:
      if (x[1]) pari_err(impl,"eval on functions with parameters");
      return closure_evalres(x);
  }
  pari_err(typeer,"geval");
  return NULL; /* not reached */
}
GEN
geval(GEN x) { return geval_gp(x,NULL); }

GEN
simplify_shallow(GEN x)
{
  long i, lx;
  GEN y, z;
  if (!x) pari_err(bugparier, "simplify, NULL input");

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD: case t_FRAC: case t_FFELT:
    case t_PADIC: case t_QFR: case t_QFI: case t_LIST: case t_STR: case t_VECSMALL:
    case t_CLOSURE:
      return x;
    case t_COMPLEX: return isintzero(gel(x,2))? gel(x,1): x;
    case t_QUAD:    return isintzero(gel(x,3))? gel(x,2): x;

    case t_POLMOD: y = cgetg(3,t_POLMOD);
      z = simplify_shallow(gel(x,1));
      if (typ(z) != t_POL) z = scalarpol(z, varn(gel(x,1)));
      gel(y,1) = z; /* z must be a t_POL: invalid object otherwise */
      gel(y,2) = simplify_shallow(gel(x,2)); return y;

    case t_POL:
      lx = lg(x);
      if (lx==2) return gen_0;
      if (lx==3) return simplify_shallow(gel(x,2));
      y = cgetg(lx,t_POL); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = simplify_shallow(gel(x,i));
      return y;

    case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = simplify_shallow(gel(x,i));
      return y;

    case t_RFRAC: y = cgetg(3,t_RFRAC);
      gel(y,1) = simplify_shallow(gel(x,1));
      z = simplify_shallow(gel(x,2));
      if (typ(z) != t_POL) return gdiv(gel(y,1), z);
      gel(y,2) = z; return y;

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = simplify_shallow(gel(x,i));
      return y;
  }
  pari_err(bugparier,"simplify_shallow, type unknown");
  return NULL; /* not reached */
}

GEN
simplify(GEN x)
{
  pari_sp av = avma;
  GEN y = simplify_shallow(x);
  return av == avma ? gcopy(y): gerepilecopy(av, y);
}

/*******************************************************************/
/*                                                                 */
/*                EVALUATION OF SOME SIMPLE OBJECTS                */
/*                                                                 */
/*******************************************************************/
/* l = lg(x) = lg(q) > 1. x a ZV, don't use Horner */
static GEN
qfeval0_Z(GEN q, GEN x, long l)
{
  long i, j;
  pari_sp av = avma;
  GEN res;
  if (l == 2) return gerepileupto(av, gmul(gcoeff(q,1,1), sqri(gel(x,1))));

  res = gmul(gcoeff(q,2,1), mulii(gel(x,2),gel(x,1))); /* i = 2 */
  for (i=3;i<l;i++)
    for (j=1;j<i;j++)
      res = gadd(res, gmul(gcoeff(q,i,j), mulii(gel(x,i),gel(x,j))) );
  res = gshift(res,1);
  for (i=1;i<l;i++) res = gadd(res, gmul(gcoeff(q,i,i), sqri(gel(x,i))) );
  return gerepileupto(av,res);
}
/* l = lg(x) = lg(q) > 1. x a RgV, Horner-type evaluation */
static GEN
qfeval0(GEN q, GEN x, long l)
{
  long i, j;
  pari_sp av = avma;
  GEN res = gmul(gcoeff(q,1,1), gsqr(gel(x,1)));
  for (i=2; i<l; i++)
  {
    GEN c = gel(q,i), sx = gmul(gel(c,1), gel(x,1));
    for (j=2; j<i; j++) sx = gadd(sx, gmul(gel(c,j),gel(x,j)));
    sx = gadd(gshift(sx,1), gmul(gel(c,i),gel(x,i)));
    res = gadd(res, gmul(gel(x,i), sx));
  }
  return gerepileupto(av,res);
}
/* assume q is a real symetric matrix */
GEN
qfeval(GEN q, GEN x)
{
  long l = lg(q);
  if (lg(x) != l) pari_err(consister,"qfeval");
  if (l == 1) return gen_0;
  return qfeval0(q,x,l);
}

/* l = lg(x) = lg(q) > 1. x a RgV */
static GEN
hqfeval0(GEN q, GEN x, long l)
{
  long i, j;
  pari_sp av = avma;
  GEN res, xc;
  if (l == 2) return gerepileupto(av, gmul(gcoeff(q,1,1), gnorm(gel(x,1))));

  xc = gconj(x);
  res = mulreal(gcoeff(q,2,1), gmul(gel(x,2),gel(xc,1)));
  for (i=3;i<l;i++)
    for (j=1;j<i;j++)
      res = gadd(res, mulreal(gcoeff(q,i,j), gmul(gel(x,i),gel(xc,j))));
  res = gshift(res,1);
  for (i=1;i<l;i++) res = gadd(res, gmul(gcoeff(q,i,i), gnorm(gel(x,i))));
  return gerepileupto(av,res);
}
/* We assume q is a hermitian complex matrix */
GEN
hqfeval(GEN q, GEN x)
{
  long l = lg(q);

  if (lg(x) != l) pari_err(consister,"hqfeval");
  if (l==1) return gen_0;
  if (lg(q[1]) != l) pari_err(talker,"invalid quadratic form in hqfeval");
  return hqfeval0(q,x,l);
}

/* Horner-type evaluation (mul x 2/3) would force us to use gmul and not
 * mulii (more than 4 x slower for small entries). Not worth it. */
static GEN
qfevalb0_Z(GEN q, GEN x, GEN y, long l)
{
  long i, j;
  pari_sp av=avma;
  GEN res = gmul(gcoeff(q,1,1), mulii(gel(x,1),gel(y,1)));
  for (i=2;i<l;i++)
  {
    if (!signe(x[i]))
    {
      if (!signe(y[i])) continue;
      for (j=1;j<i;j++)
        res = gadd(res, gmul(gcoeff(q,i,j), mulii(gel(x,j),gel(y,i))));
    }
    else if (!signe(y[i]))
    {
      for (j=1;j<i;j++)
        res = gadd(res, gmul(gcoeff(q,i,j), mulii(gel(x,i),gel(y,j))));
    }
    else
    {
      for (j=1;j<i;j++)
      {
        GEN p1 = addii(mulii(gel(x,i),gel(y,j)), mulii(gel(x,j),gel(y,i)));
        res = gadd(res, gmul(gcoeff(q,i,j),p1));
      }
      res = gadd(res, gmul(gcoeff(q,i,i), mulii(gel(x,i),gel(y,i))));
    }
  }
  return gerepileupto(av,res);
}

static GEN
qfevalb0(GEN q, GEN x, GEN y, long l)
{
  long i, j;
  pari_sp av=avma;
  GEN res = gmul(gcoeff(q,1,1), gmul(gel(x,1), gel(y,1)));

  for (i=2; i<l; i++)
  {
    GEN c = gel(q,i);
    GEN sx = gmul(gel(c,1), gel(y,1));
    GEN sy = gmul(gel(c,1), gel(x,1));
    for (j=2; j<i; j++)
    {
      sx = gadd(sx, gmul(gel(c,j),gel(y,j)));
      sy = gadd(sy, gmul(gel(c,j),gel(x,j)));
    }
    sx = gadd(sx, gmul(gel(c,i),gel(y,i)));
    res = gadd(res, gadd(gmul(gel(x,i), sx), gmul(gel(y,i), sy)));
  }
  return gerepileupto(av,res);
}
/* assume q is a real symetric matrix */
GEN
qfevalb(GEN q, GEN x, GEN y)
{
  long l = lg(q);
  if (lg(x) != l || lg(y) != l) pari_err(consister,"qfevalb");
  if (l==1) return gen_0;
  return qfevalb0(q,x,y,l);
}

static void
init_qf_apply(GEN q, GEN M, long *k, long *l)
{
  *l = lg(q); *k = lg(M);
  if (*l == 1) { if (*k == 1) return; }
  else         { if (*k != 1 && lg(M[1]) == *l) return; }
  pari_err(consister,"qf_apply_RgM");
}
/* Return X = M'.q.M, assuming q is a symetric matrix and M is a
 * matrix of compatible dimensions. X_ij are X_ji identical, not copies */
GEN
qf_apply_RgM(GEN q, GEN M)
{
  long i, j, k, l;
  GEN res;

  init_qf_apply(q, M, &k, &l); if (l == 1) return cgetg(1, t_MAT);
  res = cgetg(k,t_MAT);
  for (i=1; i<k; i++) {
    gel(res,i) = cgetg(k,t_COL);
    gcoeff(res,i,i) = qfeval0(q,gel(M,i),l);
  }
  for (i=2;i<k;i++)
    for (j=1;j<i;j++)
      gcoeff(res,i,j) = gcoeff(res,j,i) = qfevalb0(q,gel(M,i),gel(M,j),l);
  return res;
}
GEN
qf_apply_ZM(GEN q, GEN M)
{
  long i, j, k, l;
  GEN res;

  init_qf_apply(q, M, &k, &l); if (l == 1) return cgetg(1, t_MAT);
  res = cgetg(k,t_MAT);
  for (i=1; i<k; i++) {
    gel(res,i) = cgetg(k,t_COL);
    gcoeff(res,i,i) = qfeval0_Z(q,gel(M,i),l);
  }
  for (i=2;i<k;i++)
    for (j=1;j<i;j++)
      gcoeff(res,i,j) = gcoeff(res,j,i) = qfevalb0_Z(q,gel(M,i),gel(M,j),l);
  return res;
}

GEN
poleval(GEN x, GEN y)
{
  long i, j, imin, tx = typ(x);
  pari_sp av0 = avma, av, lim;
  GEN p1, p2, r, s;

  if (is_scalar_t(tx)) return gcopy(x);
  switch(tx)
  {
    case t_POL:
      i = lg(x)-1; imin = 2; break;

    case t_RFRAC:
      p1 = poleval(gel(x,1),y);
      p2 = poleval(gel(x,2),y);
      return gerepileupto(av0, gdiv(p1,p2));

    case t_VEC: case t_COL:
      i = lg(x)-1; imin = 1; break;
    default: pari_err(typeer,"poleval");
      return NULL; /* not reached */
  }
  if (i<=imin)
    return (i==imin)? gcopy(gel(x,imin)): gen_0;

  lim = stack_lim(av0,2);
  p1 = gel(x,i); i--;
  if (typ(y)!=t_COMPLEX)
  {
#if 0 /* standard Horner's rule */
    for ( ; i>=imin; i--)
      p1 = gadd(gmul(p1,y),gel(x,i));
#endif
    /* specific attention to sparse polynomials */
    for ( ; i>=imin; i=j-1)
    {
      for (j=i; isexactzero(gel(x,j)); j--)
        if (j==imin)
        {
          if (i!=j) y = gpowgs(y, i-j+1);
          return gerepileupto(av0, gmul(p1,y));
        }
      r = (i==j)? y: gpowgs(y, i-j+1);
      p1 = gadd(gmul(p1,r), gel(x,j));
      if (low_stack(lim, stack_lim(av0,2)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"poleval: i = %ld",i);
        p1 = gerepileupto(av0, p1);
      }
    }
    return gerepileupto(av0,p1);
  }

  p2 = gel(x,i); i--; r = gtrace(y); s = gneg_i(gnorm(y));
  av = avma;
  for ( ; i>=imin; i--)
  {
    GEN p3 = gadd(p2, gmul(r, p1));
    p2 = gadd(gel(x,i), gmul(s, p1)); p1 = p3;
    if (low_stack(lim, stack_lim(av0,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"poleval: i = %ld",i);
      gerepileall(av, 2, &p1, &p2);
    }
  }
  return gerepileupto(av0, gadd(p2, gmul(y,p1)));
}
