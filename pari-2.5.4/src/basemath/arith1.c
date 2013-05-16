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

/*********************************************************************/
/**                                                                 **/
/**                     ARITHMETIC FUNCTIONS                        **/
/**                         (first part)                            **/
/**                                                                 **/
/*********************************************************************/
#include "pari.h"
#include "paripriv.h"

/******************************************************************/
/*                                                                */
/*                 GENERATOR of (Z/mZ)*                           */
/*                                                                */
/******************************************************************/

GEN
znprimroot0(GEN m)
{
  return map_proto_G(znprimroot,m);
}

int
is_gener_Fl(ulong x, ulong p, ulong p_1, GEN L)
{
  long i;
  if (krouu(x, p) >= 0) return 0;
  for (i=lg(L)-1; i; i--)
  {
    ulong t = Fl_powu(x, (ulong)L[i], p);
    if (t == p_1 || t == 1) return 0;
  }
  return 1;
}
/* assume p prime */
ulong
pgener_Fl_local(ulong p, GEN L0)
{
  const pari_sp av = avma;
  const ulong p_1 = p - 1;
  const ulong q = p_1 >>1;
  long i, x, l ;
  GEN L;
  if (p <= 19)
  { /* quick trivial cases */
    switch(p)
    {
      case 2:  return 1;
      case 7:
      case 17: return 3;
      default: return 2;
    }
  }

  if (!L0) {
    ulong t;
    (void)u_lvalrem(q, 2, &t);
    L0 = L = gel(factoru(t), 1);
    l = lg(L);
  } else {
    l = lg(L0);
    L = cgetg(l, t_VECSMALL);
  }

  for (i=1; i<l; i++) L[i] = q / (ulong)L0[i];
  for (x=2;;x++) { if (is_gener_Fl(x,p,p_1,L)) break; }
  avma = av; return x;
}
ulong
pgener_Fl(ulong p) { return pgener_Fl_local(p, NULL); }

/* L[i] = set of (p-1)/2l, l ODD prime divisor of p-1 (l=2 can be included,
 * but wasteful) */
int
is_gener_Fp(GEN x, GEN p, GEN p_1, GEN L)
{
  long i, t = lgefint(x)==3? krosi(x[2], p): kronecker(x, p);
  if (t >= 0) return 0;
  for (i = lg(L)-1; i; i--) {
    GEN t = Fp_pow(x, gel(L,i), p);
    if (equalii(t, p_1) || is_pm1(t)) return 0;
  }
  return 1;
}

/* assume p prime, return a generator of all L[i]-Sylows in F_p^*. */
GEN
pgener_Fp_local(GEN p, GEN L0)
{
  pari_sp av0 = avma;
  long l, i;
  GEN x, q, p_1, L;
  if (lgefint(p) == 3)
  {
    ulong z;
    if (p[2] == 2) return gen_1;
    if (L0) L0 = ZV_to_nv(L0);
    z = pgener_Fl_local((ulong)p[2], L0);
    avma = av0; return utoipos(z);
  }
  p_1 = subis(p,1);
  q = shifti(p_1, -1);
  if (!L0) {
    GEN t;
    (void)Z_lvalrem(q, 2, &t);
    L0 = L = gel(Z_factor(t), 1);
    l = lg(L);
  } else {
    l = lg(L0);
    L = cgetg(l, t_VEC);
  }

  for (i=1; i<l; i++) gel(L,i) = diviiexact(q, gel(L0,i));
  x = utoipos(2);
  for (;; x[2]++) { if (is_gener_Fp(x, p, p_1, L)) break; }
  avma = av0; return utoipos((ulong)x[2]);
}

GEN
pgener_Fp(GEN p) { return pgener_Fp_local(p, NULL); }

/* Can fail if 2p > 2^BIL */
ulong
pgener_Zl(ulong p)
{
  ulong x;
  if (p == 2) pari_err(talker,"primitive root mod 2^3 does not exist");
  /* only p < 2^32 such that znprimroot(p) != znprimroot(p^2) */
  if (p == 40487) return 40492;
  x = pgener_Fl(p);
#ifdef LONG_IS_64BIT
{
  pari_sp av = avma;
  GEN q = sqru(p);
  GEN y = Fp_powu(utoipos(x), p-1, q);
  if (is_pm1(y)) {
    x += p;
    if (x < p) pari_err(talker, "p too large in pgener_Zl");
  }
  avma = av;
}
#endif
  return x;
}

/* p prime. Return a primitive root modulo p^e, e > 1 */
GEN
pgener_Zp(GEN p)
{
  GEN x, y;

  if (lgefint(p) == 3 && !(p[2] & HIGHBIT)) return utoipos( pgener_Zl(p[2]) );
  x = pgener_Fp(p);
  y = Fp_pow(x, subis(p,1), sqri(p));
  if (is_pm1(y)) x = addii(x,p); else avma = (pari_sp)x;
  return x;
}

static GEN
gener_Zp(GEN q)
{
  GEN p;
  long e = Z_isanypower(q, &p);
  return e > 1? pgener_Zp(p): pgener_Fp(q);
}

GEN
znprimroot(GEN m)
{
  pari_sp av;
  GEN x, z;

  if (typ(m) != t_INT) pari_err(arither1);
  if (!signe(m)) pari_err(talker,"zero modulus in znprimroot");
  if (is_pm1(m)) return mkintmodu(0,1);
  z = cgetg(3, t_INTMOD);
  m = absi(m);
  gel(z,1) = m; av = avma;

  switch(mod4(m))
  {
    case 0: /* m = 0 mod 4 */
      if (!equaliu(m,4)) /* m != 4, non cyclic */
        pari_err(talker,"primitive root mod %Ps does not exist", m);
      x = utoipos(3);
      break;
    case 2: /* m = 2 mod 4 */
      m = shifti(m,-1); /* becomes odd */
      if (is_pm1(m)) { x = gen_1; break; }
      x = gener_Zp(m); if (!mod2(x)) x = addii(x,m);
      break;
    default: /* m odd */
      x = gener_Zp(m);
      break;
  }
  gel(z,2) = gerepileuptoint(av, x); return z;
}

GEN
znstar(GEN N)
{
  GEN res = cgetg(4,t_VEC), z, P, E, cyc, gen, mod;
  long i, j, nbp, sizeh;
  pari_sp av;

  if (typ(N) != t_INT) pari_err(arither1);
  if (!signe(N))
  {
    gel(res,1) = gen_2;
    gel(res,2) = mkvec(gen_2);
    gel(res,3) = mkvec(gen_m1); return res;
  }
  if (cmpiu(N,2) <= 0)
  {
    gel(res,1) = gen_1;
    gel(res,2) = cgetg(1,t_VEC);
    gel(res,3) = cgetg(1,t_VEC); return res;
  }
  N = absi(N); /* copy needed: will be part of res (mkintmod) */
  av = avma;
  z = Z_factor(N);
  P = gel(z,1);
  E = gel(z,2); nbp = lg(P)-1;
  cyc = cgetg(nbp+2,t_VEC);
  gen = cgetg(nbp+2,t_VEC);
  mod = cgetg(nbp+2,t_VEC);
  switch(mod8(N))
  {
    case 0: {
      long v2 = itos(gel(E,1));
      gel(cyc,1) = int2n(v2-2);
      gel(cyc,2) = gen_2;
      gel(gen,1) = utoipos(5);
      gel(gen,2) = addis(int2n(v2-1), -1);
      gel(mod,1) = gel(mod,2) = int2n(v2);
      sizeh = nbp+1; i = 3; j = 2; break;
    }
    case 4:
      gel(cyc,1) = gen_2;
      gel(gen,1) = utoipos(3);
      gel(mod,1) = utoipos(4);
      sizeh = nbp; i = j = 2; break;
    case 2: case 6:
      sizeh = nbp-1; i=1; j=2; break;
    default: /* 1, 3, 5, 7 */
      sizeh = nbp; i = j = 1;
  }
  for ( ; j<=nbp; i++,j++)
  {
    long e = itos(gel(E,j));
    GEN p = gel(P,j), q = powiu(p, e-1), Q = mulii(p, q);
    gel(cyc,i) = subii(Q, q); /* phi(p^e) */
    gel(gen,i) = e > 1? pgener_Zp(p): pgener_Fp(p);
    gel(mod,i) = Q;
  }
  setlg(gen, sizeh+1);
  setlg(cyc, sizeh+1);
  if (nbp > 1)
    for (i=1; i<=sizeh; i++)
    {
      GEN Q = gel(mod,i), g = gel(gen,i), qinv = Fp_inv(Q, diviiexact(N,Q));
      g = addii(g, mulii(mulii(subsi(1,g),qinv),Q));
      gel(gen,i) = modii(g, N);
    }

  /*The cyc[i] are > 1. They remain so in the loop*/
  for (i=sizeh; i>=2; i--)
  {
    GEN ci = gel(cyc,i), gi = gel(gen,i);
    for (j=i-1; j>=1; j--) /* we want cyc[i] | cyc[j] */
    {
      GEN cj = gel(cyc,j), gj, qj, v, d;

      d = bezout(ci,cj,NULL,&v); /* > 1 */
      if (absi_equal(ci, d)) continue; /* ci | cj */
      if (absi_equal(cj, d)) { /* cj | ci */
        swap(gel(gen,j),gel(gen,i)); gi = gel(gen,i);
        swap(gel(cyc,j),gel(cyc,i)); ci = gel(cyc,i); continue;
      }

      gj = gel(gen,j);
      qj = diviiexact(cj,d);
      gel(cyc,j) = mulii(ci,qj);
      gel(cyc,i) = d;
      /* [1,v*cj/d; 0,1]*[1,0;-1,1]*diag(cj,ci)*[ci/d,-v; cj/d,u]
       * = diag(lcm,gcd), with u ci + v cj = d */

      /* (gj, gi) *= [1,0; -1,1]^-1 */
      gj = Fp_mul(gj, gi, N); /* order ci*qj = lcm(ci,cj) */
      /* (gj,gi) *= [1,v*qj; 0,1]^-1 */
      togglesign_safe(&v);
      if (signe(v) < 0) v = modii(v,ci); /* >= 0 to avoid inversions */
      gi = Fp_mul(gi, Fp_pow(gj, mulii(qj, v), N), N);
      gel(gen,i) = gi;
      gel(gen,j) = gj;
      ci = d; if (equaliu(ci, 2)) break;
    }
  }
  gerepileall(av, 2, &cyc, &gen);
  gel(res,1) = ZV_prod(cyc);
  gel(res,2) = cyc;
  for (i = 1; i <= sizeh; i++) gel(gen,i) = mkintmod(gel(gen,i), N);
  gel(res,3) = gen; return res;
}

/*********************************************************************/
/**                                                                 **/
/**                     INTEGRAL SQUARE ROOT                        **/
/**                                                                 **/
/*********************************************************************/
GEN
sqrtint(GEN a)
{
  if (typ(a) != t_INT) pari_err(arither1);
  switch (signe(a))
  {
    case 1: return sqrti(a);
    case 0: return gen_0;
    default: pari_err(talker, "negative integer in sqrtint");
  }
  return NULL; /* not reached */
}

/*********************************************************************/
/**                                                                 **/
/**                      PERFECT SQUARE                             **/
/**                                                                 **/
/*********************************************************************/
static int
carremod(ulong A)
{
  const int carresmod64[]={
    1,1,0,0,1,0,0,0,0,1, 0,0,0,0,0,0,1,1,0,0, 0,0,0,0,0,1,0,0,0,0,
    0,0,0,1,0,0,1,0,0,0, 0,1,0,0,0,0,0,0,0,1, 0,0,0,0,0,0,0,1,0,0, 0,0,0,0};
  const int carresmod63[]={
    1,1,0,0,1,0,0,1,0,1, 0,0,0,0,0,0,1,0,1,0, 0,0,1,0,0,1,0,0,1,0,
    0,0,0,0,0,0,1,1,0,0, 0,0,0,1,0,0,1,0,0,1, 0,0,0,0,0,0,0,0,1,0, 0,0,0};
  const int carresmod65[]={
    1,1,0,0,1,0,0,0,0,1, 1,0,0,0,1,0,1,0,0,0, 0,0,0,0,0,1,1,0,0,1,
    1,0,0,0,0,1,1,0,0,1, 1,0,0,0,0,0,0,0,0,1, 0,1,0,0,0,1,1,0,0,0, 0,1,0,0,1};
  const int carresmod11[]={1,1,0,1,1,1,0,0,0,1, 0};
  return (carresmod64[A & 0x3fUL]
    && carresmod63[A % 63UL]
    && carresmod65[A % 65UL]
    && carresmod11[A % 11UL]);
}

/* emulate Z_issquareall on single-word integers */
long
uissquareall(ulong A, ulong *sqrtA)
{
  if (!A) { *sqrtA = 0; return 1; }
  if (carremod(A))
  {
    ulong a = usqrtsafe(A);
    if (a * a == A) { *sqrtA = a; return 1; }
  }
  return 0;
}

long
Z_issquareall(GEN x, GEN *pt)
{
  pari_sp av;
  GEN y, r;

  switch(signe(x))
  {
    case -1: return 0;
    case 0: if (pt) *pt=gen_0; return 1;
  }
  if (lgefint(x) == 3)
  {
    ulong a;
    if (!uissquareall((ulong)x[2], &a)) return 0;
    if (pt) *pt = utoipos(a);
    return 1;
  }
  if (!carremod(umodiu(x, 64*63*65*11))) return 0;
  av = avma; y = sqrtremi(x, &r);
  if (r != gen_0) { avma = av; return 0; }
  if (pt) { *pt = y; avma = (pari_sp)y; } else avma = av;
  return 1;
}

/* a t_INT, p prime */
long
Zp_issquare(GEN a, GEN p)
{
  long v;
  GEN ap;

  if (!signe(a) || gequal1(a)) return 1;
  v = Z_pvalrem(a, p, &ap);
  if (v&1) return 0;
  return equaliu(p, 2)? umodiu(ap, 8) == 1
                      : kronecker(ap,p) == 1;
}

static int
is_char_2(GEN a)
{
  long j;
  GEN b;
  switch(typ(a))
  {
  case t_INTMOD:
    b = gel(a,1);
    if (!mod2(b))
    {
      if (!equaliu(b, 2)) pari_err(impl, "issquare for this input");
      return 1;
    }
    return 0;
  case t_FFELT:
    if (equaliu(FF_p_i(a), 2)) return 1;
    return 0;
  case t_POLMOD:
    if (is_char_2(gel(a,1)) || is_char_2(gel(a,2))) return 1;
    return 0;
  case t_POL:
    for (j = 2; j < lg(a); j++)
      if (is_char_2(gel(a,j))) return 1;
    return 0;
  }
  return 0;
}

static long
polissquareall(GEN x, GEN *pt)
{
  pari_sp av;
  long v, l = degpol(x);
  GEN y, a, b;

  if (!signe(x))
  {
    if (pt) *pt = gcopy(x);
    return 1;
  }
  if (pt) *pt = gen_0;
  if (l&1) return 0; /* odd degree */
  av = avma;
  v = RgX_valrem(x, &x);
  if (v) {
    l = degpol(x);
    if (l&1) return 0;
  }
  a = gel(x,2);
  switch (typ(a))
  {
    case t_INT: y =  Z_issquareall(a,&b)? gen_1: gen_0; break;
    case t_POL: y = polissquareall(a,&b)? gen_1: gen_0; break;
    default: y = gissquare(a); b = NULL; break;
  }
  if (y == gen_0) { avma = av; return 0; }
  if (!l) {
    if (!pt) { avma = av; return 1; }
    if (!b) b = gsqrt(a,DEFAULTPREC);
    y = scalarpol(b, varn(x)); goto END;
  }
  if (is_char_2(x))
  {
    long i, lx;
    x = gmul(x, mkintmod(gen_1, gen_2));
    lx = lg(x);
    if ((lx-3) & 1) { avma = av; return 0; }
    for (i = 3; i < lx; i+=2)
      if (!gequal0(gel(x,i))) { avma = av; return 0; }
    if (pt) {
      y = cgetg((lx+3) / 2, t_POL);
      for (i = 2; i < lx; i+=2)
        if (!gissquareall(gel(x,i), &gel(y, (i+2)>>1))) { avma = av; return 0; }
      y[1] = evalsigne(1) | evalvarn(varn(x));
      goto END;
    } else {
      for (i = 2; i < lx; i+=2)
        if (!gissquare(gel(x,i))) { avma = av; return 0; }
      avma = av; return 1;
    }
  }
  else
  {
    x = RgX_Rg_div(x,a);
    y = gtrunc(gsqrt(RgX_to_ser(x,2+l),0));
    if (!RgX_equal(gsqr(y), x)) { avma = av; return 0; }
    if (!pt) { avma = av; return 1; }
    if (!gequal1(a))
    {
      if (!b) b = gsqrt(a,DEFAULTPREC);
      y = gmul(b, y);
    }
  }
END:
  *pt = v? gerepilecopy(av, RgX_shift_shallow(y, v >> 1)): gerepileupto(av, y);
  return 1;
}

GEN
gissquareall(GEN x, GEN *pt)
{
  long l, tx = typ(x);
  GEN F;
  pari_sp av;

  if (!pt) return gissquare(x);
  if (is_matvec_t(tx))
  {
    GEN t, y, z;
    long i;
    l = lg(x);
    y = cgetg(l,tx);
    z = cgetg(l,tx);
    for (i=1; i<l; i++)
    {
      GEN p = gen_0;
      t = gissquareall(gel(x,i),&p);
      gel(y,i) = t;
      gel(z,i) = p;
    }
    *pt = z; return y;
  }
  switch(tx)
  {
    case t_INT: l = Z_issquareall(x, pt); break;
    case t_FRAC: av = avma;
      F = cgetg(3, t_FRAC);
      l = Z_issquareall(gel(x,1), &gel(F,1));
      if (l) l = Z_issquareall(gel(x,2), &gel(F,2));
      if (!l) { avma = av; break; }
      *pt = F; break;

    case t_POL: l = polissquareall(x,pt); break;
    case t_RFRAC: av = avma;
      F = cgetg(3, t_RFRAC);
      l = (gissquareall(gel(x,1), &gel(F,1)) != gen_0);
      if (l) l = polissquareall(gel(x,2), &gel(F,2));
      if (!l) { avma = av; break; }
      *pt = F; break;

    case t_REAL: case t_COMPLEX: case t_PADIC: case t_SER:
      F = gissquare(x);
      if (F == gen_1) *pt = gsqrt(x, DEFAULTPREC);
      return F;

    case t_INTMOD:
    {
      GEN L, P, E, q = gel(x,1), a = gel(x,2);
      long i;
      if (!signe(a)) { *pt = gcopy(x); return gen_1; }
      av = avma;
      L = Z_factor(q);
      P = gel(L,1); l = lg(P);
      E = gel(L,2);
      L = cgetg(l, t_VEC);
      for (i = 1; i < l; i++)
      {
        GEN p = gel(P,i), t, b;
        long e = itos(gel(E,i)), v = Z_pvalrem(a, p, &b);
        if (v >= e) { gel(L, i) = mkintmod(gen_0, powiu(p, e)); continue; }
        if (odd(v)) { avma = av; return gen_0; }
        t = cvtop(b, gel(P,i), e - v);
        if (gissquare(t) != gen_1) { avma = av; return gen_0; }
        t = gtrunc(Qp_sqrt(t));
        if (v) t = mulii(t, powiu(p, v>>1));
        gel(L,i) = mkintmod(t, powiu(p, e));
      }
      *pt = gerepileupto(av, chinese1_coprime_Z(L));
      return gen_1;
    }

    case t_FFELT: return FF_issquareall(x, pt)? gen_1: gen_0;

    default: pari_err(typeer, "gissquareall");
      return NULL; /* not reached */
  }
  return l? gen_1: gen_0;
}

GEN
gissquare(GEN x)
{
  pari_sp av;
  GEN p1,a,p;
  long l, i, v;

  switch(typ(x))
  {
    case t_INT:
      return Z_issquare(x)? gen_1: gen_0;

    case t_REAL:
      return (signe(x)>=0)? gen_1: gen_0;

    case t_INTMOD:
    {
      GEN b, q;
      long w;
      a = gel(x,2); if (!signe(a)) return gen_1;
      av = avma;
      q = gel(x,1); v = vali(q);
      if (v) /* > 0 */
      {
        long dv;
        w = vali(a); dv = v - w;
        if (dv > 0)
        {
          if (w & 1) { avma = av; return gen_0; }
          if (dv >= 2)
          {
            b = w? shifti(a,-w): a;
            if ((dv>=3 && mod8(b) != 1) ||
                (dv==2 && mod4(b) != 1)) { avma = av; return gen_0; }
          }
        }
        q = shifti(q, -v);
      }
      /* q is now odd */
      i = kronecker(a,q);
      if (i < 0) { avma = av; return gen_0; }
      if (i==0)
      {
        GEN d = gcdii(a,q);
        p = gel(Z_factor(d),1); l = lg(p);
        for (i=1; i<l; i++)
        {
          v = Z_pvalrem(a,gel(p,i),&p1);
          w = Z_pvalrem(q,gel(p,i), &q);
          if (v < w && (v&1 || kronecker(p1,gel(p,i)) == -1))
            { avma = av; return gen_0; }
        }
        a = modii(a, q);
        if (kronecker(a,q) == -1) { avma = av; return gen_0; }
      }
      /* kro(a,q) = 1, q odd: need to factor q and check all p|q
       * (can't use product formula in case v_p(q) is even for some p) */
      p = gel(Z_factor(q),1); l = lg(p);
      for (i=1; i<l; i++)
        if (kronecker(a,gel(p,i)) == -1) { avma = av; return gen_0; }
      return gen_1;
    }

    case t_FRAC:
      av=avma; l=Z_issquare(mulii(gel(x,1),gel(x,2)));
      avma=av; return l? gen_1: gen_0;

    case t_FFELT: return FF_issquareall(x, NULL)? gen_1: gen_0;

    case t_COMPLEX:
      return gen_1;

    case t_PADIC:
      a = gel(x,4); if (!signe(a)) return gen_1;
      if (valp(x)&1) return gen_0;
      p = gel(x,2);
      if (!equaliu(p, 2))
        return (kronecker(a,p)== -1)? gen_0: gen_1;

      v = precp(x); /* here p=2, a is odd */
      if ((v>=3 && mod8(a) != 1 ) ||
          (v==2 && mod4(a) != 1)) return gen_0;
      return gen_1;

    case t_POL:
      return polissquareall(x,NULL)? gen_1: gen_0;

    case t_SER:
      if (!signe(x)) return gen_1;
      if (valp(x)&1) return gen_0;
      return gissquare(gel(x,2));

    case t_RFRAC:
      av = avma; a = gissquare(gmul(gel(x,1),gel(x,2)));
      avma = av; return a;

    case t_VEC: case t_COL: case t_MAT:
      p1 = cgetg_copy(x, &l);
      for (i=1; i<l; i++) gel(p1,i) = gissquare(gel(x,i));
      return p1;
  }
  pari_err(typeer,"gissquare");
  return NULL; /* not reached */
}

/*********************************************************************/
/**                                                                 **/
/**                        PERFECT POWER                            **/
/**                                                                 **/
/*********************************************************************/
static int
pow_check(ulong p, GEN *x, GEN *logx, long *k)
{
  GEN u, y;
  long e;
  setlg(*logx, DEFAULTPREC + (lg(*x)-2) / p);
  u = divru(*logx, p); y = grndtoi(mpexp(u), &e);
  if (e >= -10 || !equalii(powiu(y, p), *x)) return 0;
  *k *= p; *x = y; *logx = u; return 1;
}

static long
polispower(GEN x, GEN K, GEN *pt)
{
  pari_sp av;
  long v, l = degpol(x), k = itos(K);
  GEN y, a, b;

  if (!signe(x)) return 1;
  if (l % k) return 0; /* degree not multiple of k */
  v = RgX_valrem(x, &x);
  if (v % k) return 0;
  av = avma; a = gel(x,2); b = NULL;
  if (!ispower(a, K, &b)) { avma = av; return 0; }
  av = avma;
  if (degpol(x))
  {
    x = RgX_Rg_div(x,a);
    y = gtrunc(gsqrtn(RgX_to_ser(x,lg(x)), K, NULL, 0));
    if (!RgX_equal(powgi(y, K), x)) { avma = av; return 0; }
  }
  else y = pol_1(varn(x));
  if (pt)
  {
    if (!gequal1(a))
    {
      if (!b) b = gsqrtn(a, K, NULL, DEFAULTPREC);
      y = gmul(b,y);
    }
    *pt = v? gerepilecopy(av, RgX_shift_shallow(y, v/k)): gerepileupto(av, y);
  }
  else avma = av;
  return 1;
}

long
Z_ispowerall(GEN x, ulong k, GEN *pt)
{
  long s = signe(x);
  ulong mask;
  if (!s) { if (pt) *pt = gen_0; return 1; }
  if (s > 0) {
    if (k == 2) return Z_issquareall(x, pt);
    if (k == 3) { mask = 1; return !!is_357_power(x, pt, &mask); }
    if (k == 5) { mask = 2; return !!is_357_power(x, pt, &mask); }
    if (k == 7) { mask = 4; return !!is_357_power(x, pt, &mask); }
    return is_kth_power(x, k, pt, NULL);
  }
  if (!odd(k)) return 0;
  if (Z_ispowerall(absi(x), k, pt))
  {
    if (pt) *pt = negi(*pt);
    return 1;
  };
  return 0;
}

/* is x a K-th power mod p ? Assume p prime. */
static int
Fp_ispower(GEN x, GEN K, GEN p)
{
  pari_sp av = avma;
  GEN p_1;
  long r;
  x = modii(x, p);
  if (!signe(x) || equali1(x)) { avma = av; return 1; }
  p_1 = subis(p,1);
  K = gcdii(K, p_1);
  if (equaliu(K, 2)) { r = kronecker(x,p); avma = av; return r; }
  x = Fp_pow(x, diviiexact(p_1,K), p);
  avma = av; return equali1(x);
}

long
ispower(GEN x, GEN K, GEN *pt)
{
  GEN z;

  if (!K) return gisanypower(x, pt);
  if (typ(K) != t_INT) pari_err(typeer, "ispower");
  if (signe(K) <= 0) pari_err(talker, "non-positive exponent %Ps in ispower",K);
  if (is_pm1(K)) { if (pt) *pt = gcopy(x); return 1; }
  switch(typ(x)) {
    case t_INT:
      return Z_ispowerall(x, itou(K), pt);
    case t_FRAC:
    {
      GEN a = gel(x,1), b = gel(x,2);
      ulong k = itou(K);
      if (pt) {
        z = cgetg(3, t_FRAC);
        if (Z_ispowerall(a, k, &a) && Z_ispowerall(b, k, &b)) {
          *pt = z; gel(z,1) = a; gel(z,2) = b; return 1;
        }
        avma = (pari_sp)(z + 3); return 0;
      }
      return Z_ispower(a, k) && Z_ispower(b, k);
    }
    case t_INTMOD:
    {
      GEN L, P, E, q = gel(x,1), a = gel(x,2);
      pari_sp av;
      long i, l;
      if (!signe(a)) {
        if (pt) *pt = gcopy(x);
        return 1;
      }
      /* a != 0 */
      av = avma;
      L = Z_factor(q);
      P = gel(L,1); l = lg(P);
      E = gel(L,2);
      L = cgetg(l, t_VEC);
      for (i = 1; i < l; i++)
      {
        GEN p = gel(P,i), t, b;
        long w, e = itos(gel(E,i)), v = Z_pvalrem(a, p, &b);
        ulong r;
        if (v >= e) { gel(L, i) = mkintmod(gen_0, powiu(p, e)); continue; }
        w = udivui_rem(v, K, &r);
        if (r) { avma = av; return 0; }
        /* b unit mod p */
        if (e - v == 1)
        { /* mod p: faster */
          if (!Fp_ispower(b, K, p)) { avma = av; return 0; }
          if (pt) t = Fp_sqrtn(b, K, p, NULL);
        }
        else
        {
          /* mod p^{2 +} */
          t = cvtop(b, gel(P,i), e - v);
          if (!ispower(t, K, &t)) { avma = av; return 0; }
          t = gtrunc(t);
        }
        if (pt)
        {
          if (w) t = mulii(t, powiu(p, w));
          gel(L,i) = mkintmod(t, powiu(p, e));
        }
      }
      if (pt) *pt = gerepileupto(av, chinese1_coprime_Z(L));
      return 1;
    }
    case t_FFELT:
      return FF_ispower(x, K, pt);

    case t_PADIC:
      z = Qp_sqrtn(x, K, NULL);
      if (!z) return 0;
      if (pt) *pt = z;
      return 1;

    case t_POL:
      return polispower(x, K, pt);
    case t_RFRAC: {
      GEN a = gel(x,1), b = gel(x,2);
      if (pt) {
        z = cgetg(3, t_RFRAC);
        if (ispower(a, K, &a) && polispower(b, K, &b)) {
          *pt = z; gel(z,1) = a; gel(z,2) = b; return 1;
        }
        avma = (pari_sp)(z + 3); return 0;
      }
      return (ispower(a, K, NULL) && polispower(b, K, NULL));
    }
    case t_REAL:
      if (signe(x) < 0 && !mpodd(K)) return 0;
    case t_COMPLEX:
      if (pt) *pt = gsqrtn(x, K, NULL, DEFAULTPREC);
      return 1;

    case t_SER:
      if (signe(x) && (!dvdsi(valp(x), K) || !ispower(gel(x,2), K, NULL)))
        return 0;
      if (pt) *pt = gsqrtn(x, K, NULL, DEFAULTPREC);
      return 1;

    default: pari_err(typeer, "ispower");
    return 0; /* not reached */
  }
}

long
gisanypower(GEN x, GEN *pty)
{
  long tx = typ(x);
  ulong k, h;
  if (tx == t_INT) return Z_isanypower(x, pty);
  if (tx == t_FRAC)
  {
    pari_sp av = avma;
    GEN fa, P, E, a = gel(x,1), b = gel(x,2);
    long i, j, p, e;
    int sw = (absi_cmp(a, b) > 0);

    if (sw) swap(a, b);
    k = Z_isanypower(a, pty? &a: NULL);
    if (!k)
    { /* a = -1,1 or not a pure power */
      if (!is_pm1(a)) { avma = av; return 0; }
      if (signe(a) < 0) b = negi(b);
      k = Z_isanypower(b, pty? &b: NULL);
      if (!k || !pty) { avma = av; return k; }
      *pty = gerepileupto(av, ginv(b));
      return k;
    }
    fa = factoru(k);
    P = gel(fa,1);
    E = gel(fa,2); h = k;
    for (i = lg(P) - 1; i > 0; i--)
    {
      p = P[i];
      e = E[i];
      for (j = 0; j < e; j++)
        if (!is_kth_power(b, p, &b, NULL)) break;
      if (j < e) k /= upowuu(p, e - j);
    }
    if (k == 1) { avma = av; return 0; }
    if (!pty) { avma = av; return k; }
    if (k != h) a = powiu(a, h/k);
    *pty = gerepilecopy(av, mkfrac(a, b));
    return k;
  }
  pari_err(talker, "missing exponent");
  return 0; /* not reached */
}

/* disregard the sign of x, caller will take care of x < 0 */
static long
Z_isanypower_aux(GEN x, GEN *pty)
{
  long ex, v, i, j, l, k;
  GEN logx, y, fa, P, E, Pe, Ee;
  byteptr d = diffptr;
  ulong mask, p = 0, ex0 = 11, e = 0, e2;

  if (absi_cmp(x, gen_2) < 0) return 0; /* -1,0,1 */

  x = absi(x); /* Z_lvalrem_stop assigns to x */
  k = 1;
  P = cgetg(26 + 1, t_VECSMALL);
  E = cgetg(26 + 1, t_VECSMALL);
  /* trial division */
  for(l = 1;;)
  {
    int stop;
    NEXT_PRIME_VIADIFF(p,d);
    if (p > 102) break;

    v = Z_lvalrem_stop(x, p, &stop);
    if (v)
    {
      P[l] = p;
      E[l] = v; l++;
      e = cgcd(e, v); if (e == 1) goto END;
    }
    if (stop) {
      if (is_pm1(x)) k = e;
      goto END;
    }
  }

  if (e)
  { /* Bingo. Result divides e */
    long v3, v5, v7, le;
    ulong e2 = e;
    v = u_lvalrem(e2, 2, &e2);
    if (v)
    {
      for (i = 0; i < v; i++)
      {
        if (!Z_issquareall(x, &y)) break;
        k <<= 1; x = y;
      }
    }
    mask = 0;
    v3 = u_lvalrem(e2, 3, &e2); if (v3) mask = 1;
    v5 = u_lvalrem(e2, 5, &e2); if (v5) mask |= 2;
    v7 = u_lvalrem(e2, 7, &e2); if (v7) mask |= 4;
    while ( (ex = is_357_power(x, &y, &mask)) ) {
      x = y;
      switch(ex)
      {
        case 3: k *= 3; if (--v3 == 0) mask &= ~1; break;
        case 5: k *= 5; if (--v5 == 0) mask &= ~2; break;
        case 7: k *= 7; if (--v7 == 0) mask &= ~4; break;
      }
    }

    if (e2 == 1) goto END;
    fa = factoru(e2);
    Pe = gel(fa,1); le = lg(Pe);
    Ee = gel(fa,2);
    for (i = 1; i < le; i++)
    {
      p = Pe[i];
      for (j = 0; j < Ee[i]; j++)
      {
        if (!is_kth_power(x, p, &y, NULL)) break;
        k *= p; x = y;
      }
    }
  }
  else
  { /* any prime divisor of x is > 102 */
    const double LOG2_103 = 6.6865; /* lower bound for log_2(103) */

    while (Z_issquareall(x, &y)) { k <<= 1; x = y; }
    mask = 7;
    while ( (ex = is_357_power(x, &y, &mask)) ) { k *= ex; x = y; }
    /* cut off at 4 bits which seems to be about optimum;  for primes
     * >> 10^3 the modular checks are no longer competitively fast */
    while ( (ex = is_pth_power(x, &y, &ex0, 4)) ) { k *= ex; x = y; }
    if (DEBUGLEVEL>4) err_printf("Z_isanypower: now k=%ld, x=%Ps\n", k, x);
    do {
      if (!*d) { p = unextprime(ex0); break; }
      NEXT_PRIME_VIADIFF(p,d);
    } while (p < ex0);

    /* upper bound for log(x) / log(103) */
    e2 = (long)((expi(x) + 1) / LOG2_103);
    logx = logr_abs( itor(x, DEFAULTPREC + (lg(x)-2) / p) );
    while (p < e2)
    {
      if (pow_check(p, &x, &logx, &k)) {
        e2 = (long)((expi(x) + 1) / LOG2_103);
        continue; /* if success, retry same p */
      }
      if (*d) NEXT_PRIME_VIADIFF(p, d); else p = unextprime(p+1);
    }
  }
END:
  if (pty && k != 1)
  {
    if (e)
    { /* add missing small factors */
      y = powuu(P[1], E[1] / k);
      for (i = 2; i < l; i++) y = mulii(y, powuu(P[i], E[i] / k));
      x = is_pm1(x)? y: mulii(x,y);
    }
    *pty = x;
  }
  return k == 1? 0: k;
}
long
Z_isanypower(GEN x, GEN *pty)
{
  pari_sp av = avma;
  long k = Z_isanypower_aux(x, pty);
  if (!k) { avma = av; return 0; }
  if (signe(x) < 0)
  {
    long v = vals(k);
    if (v)
    {
      GEN y;
      k >>= v;
      if (k == 1) { avma = av; return 0; }
      if (!pty) { avma = av; return k; }
      y = *pty;
      y = powiu(y, 1<<v);
      togglesign(y);
      *pty = gerepileuptoint(av, y);
      return k;
    }
    if (pty) togglesign_safe(pty);
  }
  if (pty) *pty = gerepilecopy(av, *pty); else avma = av;
  return k;
}

/*********************************************************************/
/**                                                                 **/
/**                        KRONECKER SYMBOL                         **/
/**                                                                 **/
/*********************************************************************/
/* u = 3,5 mod 8 ?  (= 2 not a square mod u) */
#define  ome(t) (labs(((t)&7)-4) == 1)
#define gome(t) (ome(mod2BIL(t)))

/* assume y odd, return kronecker(x,y) * s */
static long
krouu_s(ulong x, ulong y, long s)
{
  ulong x1 = x, y1 = y, z;
  while (x1)
  {
    long r = vals(x1);
    if (r)
    {
      if (odd(r) && ome(y1)) s = -s;
      x1 >>= r;
    }
    if (x1 & y1 & 2) s = -s;
    z = y1 % x1; y1 = x1; x1 = z;
  }
  return (y1 == 1)? s: 0;
}

GEN
gkronecker(GEN x, GEN y) { return map_proto_lGG(kronecker,x,y); }

long
kronecker(GEN x, GEN y)
{
  pari_sp av = avma, lim;
  long s = 1, r;
  ulong xu, yu;

  if (typ(x) != t_INT || typ(y) != t_INT) pari_err(arither1);

  switch (signe(y))
  {
    case -1: y = negi(y); if (signe(x) < 0) s = -1; break;
    case 0: return is_pm1(x);
  }
  r = vali(y);
  if (r)
  {
    if (!mpodd(x)) { avma = av; return 0; }
    if (odd(r) && gome(x)) s = -s;
    y = shifti(y,-r);
  }
  lim = stack_lim(av,2);
  x = modii(x,y);
  while (lgefint(x) > 3) /* x < y */
  {
    GEN z;
    r = vali(x);
    if (r)
    {
      if (odd(r) && gome(y)) s = -s;
      x = shifti(x,-r);
    }
    /* x=3 mod 4 && y=3 mod 4 ? (both are odd here) */
    if (mod2BIL(x) & mod2BIL(y) & 2) s = -s;
    z = remii(y,x); y = x; x = z;
    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"kronecker");
      gerepileall(av, 2, &x, &y);
    }
  }
  xu = itou(x);
  if (!xu) return is_pm1(y)? s: 0;
  r = vals(xu);
  if (r)
  {
    if (odd(r) && gome(y)) s = -s;
    xu >>= r;
  }
  /* x=3 mod 4 && y=3 mod 4 ? (both are odd here) */
  if (xu & mod2BIL(y) & 2) s = -s;
  yu = umodiu(y, xu);
  avma = av; return krouu_s(yu, xu, s);
}

long
krois(GEN x, long y)
{
  ulong yu;
  long s = 1, r;

  if (y <= 0)
  {
    if (y == 0) return is_pm1(x);
    yu = (ulong)-y; if (signe(x) < 0) s = -1;
  }
  else
    yu = (ulong)y;
  r = vals(yu);
  if (r)
  {
    if (!mpodd(x)) return 0;
    if (odd(r) && gome(x)) s = -s;
    yu >>= r;
  }
  return krouu_s(umodiu(x, yu), yu, s);
}

long
krosi(long x, GEN y)
{
  const pari_sp av = avma;
  long s = 1, r;
  ulong u, xu;

  switch (signe(y))
  {
    case -1: y = negi(y); if (x < 0) s = -1; break;
    case 0: return (x==1 || x==-1);
  }
  r = vali(y);
  if (r)
  {
    if (!odd(x)) { avma = av; return 0; }
    if (odd(r) && ome(x)) s = -s;
    y = shifti(y,-r);
  }
  if (x < 0) { x = -x; if (mod4(y) == 3) s = -s; }
  xu = (ulong)x;
  if (lgefint(y) == 3)
    return krouu_s(xu, itou(y), s);
  if (!xu) return 0; /* y != 1 */
  r = vals(xu);
  if (r)
  {
    if (odd(r) && gome(y)) s = -s;
    xu >>= r;
  }
  /* xu=3 mod 4 && y=3 mod 4 ? (both are odd here) */
  if (xu & mod2BIL(y) & 2) s = -s;
  u = umodiu(y, xu);
  avma = av; return krouu_s(u, xu, s);
}

long
kross(long x, long y)
{
  ulong yu;
  long s = 1, r;

  if (y <= 0)
  {
    if (y == 0) return (labs(x)==1);
    yu = (ulong)-y; if (x < 0) s = -1;
  }
  else
    yu = (ulong)y;
  r = vals(yu);
  if (r)
  {
    if (!odd(x)) return 0;
    if (odd(r) && ome(x)) s = -s;
    yu >>= r;
  }
  x %= (long)yu; if (x < 0) x += yu;
  return krouu_s((ulong)x, yu, s);
}

long
krouu(ulong x, ulong y)
{
  long r;
  if (y & 1) return krouu_s(x, y, 1);
  if (!odd(x)) return 0;
  r = vals(y);
  return krouu_s(x, y >> r, (odd(r) && ome(x))? -1: 1);
}

/*********************************************************************/
/**                                                                 **/
/**                          HILBERT SYMBOL                         **/
/**                                                                 **/
/*********************************************************************/
#define eps(t) (((signe(t)*(mod2BIL(t)))&3)==3)
long
hilbertii(GEN x, GEN y, GEN p)
{
  pari_sp av;
  long a, b, z;
  GEN u, v;

  if (!p) return (signe(x)<0 && signe(y)<0)? -1: 1;
  if (is_pm1(p)) pari_err(talker,"p = 1 in hilbert()");
  av = avma;
  a = odd(Z_pvalrem(x,p,&u));
  b = odd(Z_pvalrem(y,p,&v));
  if (equaliu(p, 2))
  {
    z = (eps(u) && eps(v))? -1: 1;
    if (a && gome(v)) z = -z;
    if (b && gome(u)) z = -z;
  }
  else
  {
    z = (a && b && eps(p))? -1: 1;
    if (a && kronecker(v,p)<0) z = -z;
    if (b && kronecker(u,p)<0) z = -z;
  }
  avma = av; return z;
}

static void
err_at2(void) {pari_err(talker, "insufficient precision for p = 2 in hilbert");}

long
hilbert(GEN x, GEN y, GEN p)
{
  pari_sp av;
  long tx, ty, z;
  GEN p1, p2;

  if (gequal0(x) || gequal0(y)) return 0;
  av = avma; tx = typ(x); ty = typ(y);
  if (tx > ty) swapspec(x,y, tx,ty);
  if (p)
  {
    if (typ(p) != t_INT) pari_err(typeer,"hilbert");
    if (signe(p) <= 0) p = NULL;
  }

  switch(tx) /* <= ty */
  {
    case t_INT:
      switch(ty)
      {
        case t_INT: return hilbertii(x,y,p);
        case t_REAL:
          return (signe(x)<0 && signe(y)<0)? -1: 1;
        case t_INTMOD:
          p = gel(y,1); if (equaliu(p,2)) err_at2();
          return hilbertii(x, gel(y,2), p);
        case t_FRAC:
          z = hilbertii(x, mulii(gel(y,1),gel(y,2)), p);
          avma = av; return z;
        case t_PADIC:
          p = gel(y,2);
          if (equaliu(p,2) && precp(y) <= 1) err_at2();
          p1 = odd(valp(y))? mulii(p,gel(y,4)): gel(y,4);
          z = hilbertii(x, p1, p); avma = av; return z;
      }
      break;

    case t_REAL:
      if (ty != t_FRAC) break;
      if (signe(x) > 0) return 1;
      return signe(y[1])*signe(y[2]);

    case t_INTMOD:
      p = gel(x,1); if (equaliu(p,2)) err_at2();
      switch(ty)
      {
        case t_INTMOD:
          if (!equalii(p, gel(y,1))) break;
          return hilbertii(gel(x,2),gel(y,2),p);
        case t_FRAC:
          return hilbert(gel(x,2),y,p);
        case t_PADIC:
          if (!equalii(p, gel(y,2))) break;
          return hilbert(gel(x,2),y,p);
      }
      break;

    case t_FRAC:
      p1 = mulii(gel(x,1),gel(x,2));
      switch(ty)
      {
        case t_FRAC:
          p2 = mulii(gel(y,1),gel(y,2));
          z = hilbertii(p1,p2,p); avma = av; return z;
        case t_PADIC:
          z = hilbert(p1,y,NULL); avma = av; return z;
      }
      break;

    case t_PADIC:
      p = gel(x,2);
      if (ty != t_PADIC || !equalii(p,gel(y,2))) break;
      if (equaliu(p,2) && (precp(x) <= 1 || precp(y) <= 1)) err_at2();
      p1 = odd(valp(x))? mulii(p,gel(x,4)): gel(x,4);
      p2 = odd(valp(y))? mulii(p,gel(y,4)): gel(y,4);
      z = hilbertii(p1,p2,p); avma = av; return z;
  }
  pari_err(talker,"forbidden or incompatible types in hilbert");
  return 0; /* not reached */
}
#undef eps
#undef ome
#undef gome

/*******************************************************************/
/*                                                                 */
/*                       SQUARE ROOT MODULO p                      */
/*                                                                 */
/*******************************************************************/

/* Tonelli-Shanks. Assume p is prime and (a,p) != -1. */
ulong
Fl_sqrt(ulong a, ulong p)
{
  long i, e, k;
  ulong p1, q, v, y, w, m;

  if (!a) return 0;
  p1 = p - 1; e = vals(p1);
  if (e == 0) /* p = 2 */
  {
    if (p != 2) pari_err(talker,"composite modulus in Fl_sqrt: %lu",p);
    return ((a & 1) == 0)? 0: 1;
  }
  q = p1 >> e; /* q = (p-1)/2^oo is odd */
  if (e == 1) y = p1;
  else /* look for an odd power of a primitive root */
    for (k=2; ; k++)
    { /* loop terminates for k < p (even if p composite) */
      i = krouu(k, p);
      if (i >= 0)
      {
        if (i) continue;
        pari_err(talker,"composite modulus in Fl_sqrt: %lu",p);
      }
      y = m = Fl_powu(k, q, p);
      for (i=1; i<e; i++)
        if ((m = Fl_sqr(m,p)) == 1) break;
      if (i == e) break; /* success */
    }

  p1 = Fl_powu(a, q >> 1, p); /* a ^ [(q-1)/2] */
  if (!p1) return 0;
  v = Fl_mul(a, p1, p);
  w = Fl_mul(v, p1, p);
  while (w != 1)
  { /* a*w = v^2, y primitive 2^e-th root of 1
       a square --> w even power of y, hence w^(2^(e-1)) = 1 */
    p1 = Fl_sqr(w,p);
    for (k=1; p1 != 1 && k < e; k++) p1 = Fl_sqr(p1,p);
    if (k == e) return ~0UL;
    /* w ^ (2^k) = 1 --> w = y ^ (u * 2^(e-k)), u odd */
    p1 = y;
    for (i=1; i < e-k; i++) p1 = Fl_sqr(p1,p);
    y = Fl_sqr(p1, p); e = k;
    w = Fl_mul(y, w, p);
    v = Fl_mul(v, p1, p);
  }
  p1 = p - v; if (v > p1) v = p1;
  return v;
}

/* Cipolla is better than Tonelli-Shanks when e = v_2(p-1) is "too big".
 * Otherwise, is a constant times worse; for p = 3 (mod 4), is about 3 times worse,
 * and in average is about 2 or 2.5 times worse. But try both algorithms for
 * S(n) = (2^n+3)^2-8 with n = 750, 771, 779, 790, 874, 1176, 1728, 2604, etc.
 *
 * If X^2 := t^2 - a  is not a square in F_p (so X is in F_p^2), then
 *   (t+X)^(p+1) = (t-X)(t+X) = a,   hence  sqrt(a) = (t+X)^((p+1)/2)  in F_p^2.
 * If (a|p)=1, then sqrt(a) is in F_p.
 * cf: LNCS 2286, pp 430-434 (2002)  [Gonzalo Tornaria] */

/* compute y^2, y = y[1] + y[2] X */
static GEN
sqrt_Cipolla_sqr(void *data, GEN y)
{
  GEN u = gel(y,1), v = gel(y,2), p = gel(data,2), n = gel(data,3);
  GEN z, u2 = sqri(u), v2 = sqri(v);
  v = subii(sqri(addii(v,u)), addii(u2,v2));
  u = addii(u2, mulii(v2,n));
  z = cgetg(3, t_VEC); /* NOT mkvec2: must be gerepileupto-able */
  gel(z,1) = modii(u,p);
  gel(z,2) = modii(v,p); return z;
}
/* compute (t+X) y^2 */
static GEN
sqrt_Cipolla_msqr(void *data, GEN y)
{
  GEN u = gel(y,1), v = gel(y,2), a = gel(data,1), p = gel(data,2), gt = gel(data,4);
  ulong t = gt[2];
  GEN d = addii(u, mului(t,v)), d2= sqri(d);
  GEN z, b = remii(mulii(a,v), p);
  u = subii(mului(t,d2), mulii(b,addii(u,d)));
  v = subii(d2, mulii(b,v));
  z = cgetg(3, t_VEC); /* NOT mkvec2: must be gerepileupto-able */
  gel(z,1) = modii(u,p);
  gel(z,2) = modii(v,p); return z;
}
/* assume a reduced mod p [ otherwise correct but inefficient ] */
static GEN
sqrt_Cipolla(GEN a, GEN p)
{
  pari_sp av1;
  GEN u, v, n, y, pov2;
  ulong t;

  if (kronecker(a, p) < 0) return NULL;
  pov2 = shifti(p,-1);
  if (cmpii(a,pov2) > 0) a = subii(a,p); /* center: avoid multiplying by huge base*/

  av1 = avma;
  for(t=1; ; t++)
  {
    n = subsi((long)(t*t), a);
    if (kronecker(n, p) < 0) break;
    avma = av1;
  }

  /* compute (t+X)^((p-1)/2) =: u+vX */
  u = utoipos(t);
  y = leftright_pow_fold(mkvec2(u, gen_1), pov2, mkvec4(a,p,n,u),
                         sqrt_Cipolla_sqr, sqrt_Cipolla_msqr);
  u = gel(y,1);
  v = gel(y,2);
  /* Now u+vX = (t+X)^((p-1)/2); thus
   *   (u+vX)(t+X) = sqrt(a) + 0 X
   * Whence,
   *   sqrt(a) = (u+vt)t - v*a
   *   0       = (u+vt)
   * Thus a square root is v*a */

  v = Fp_mul(v,a, p);
  if (cmpii(v,pov2) > 0) v = subii(p,v);
  return v;
}

#define sqrmod(x,p) (remii(sqri(x),p))

/* Tonelli-Shanks. Assume p is prime and return NULL if (a,p) = -1. */
GEN
Fp_sqrt(GEN a, GEN p)
{
  pari_sp av = avma, av1,lim;
  long i, k, e;
  GEN p1, q, v, y, w, m;

  if (typ(a) != t_INT || typ(p) != t_INT) pari_err(arither1);
  if (signe(p) <= 0 || is_pm1(p)) pari_err(talker,"not a prime in Fp_sqrt");
  if (lgefint(p) == 3)
  {
    ulong u = (ulong)p[2]; u = Fl_sqrt(umodiu(a, u), u);
    if (u == ~0UL) return NULL;
    return utoi(u);
  }

  p1 = addsi(-1,p); e = vali(p1);
  a = modii(a, p);

  /* On average, the algorithm of Cipolla is better than the algorithm of
   * Tonelli and Shanks if and only if e(e-1)>8*log2(n)+20
   * see LNCS 2286 pp 430 [GTL] */
  if (e*(e-1) > 20 + 8 * bit_accuracy(lgefint(p)))
  {
    v = sqrt_Cipolla(a,p);
    if (!v) { avma = av; return NULL; }
    return gerepileuptoint(av,v);
  }

  if (e == 0) /* p = 2 */
  {
    avma = av;
    if (!equaliu(p,2)) pari_err(talker,"composite modulus in Fp_sqrt: %Ps",p);
    if (!signe(a) || !mod2(a)) return gen_0;
    return gen_1;
  }
  q = shifti(p1,-e); /* q = (p-1)/2^oo is odd */
  if (e == 1) y = p1;
  else /* look for an odd power of a primitive root */
    for (k=2; ; k++)
    { /* loop terminates for k < p (even if p composite) */

      i = krosi(k,p);
      if (i >= 0)
      {
        if (i) continue;
        pari_err(talker,"composite modulus in Fp_sqrt: %Ps",p);
      }
      av1 = avma;
      y = m = Fp_pow(utoipos((ulong)k),q,p);
      for (i=1; i<e; i++)
        if (gequal1(m = sqrmod(m,p))) break;
      if (i == e) break; /* success */
      avma = av1;
    }

  p1 = Fp_pow(a, shifti(q,-1), p); /* a ^ [(q-1)/2] */
  if (!signe(p1)) { avma=av; return gen_0; }
  v = Fp_mul(a, p1, p);
  w = Fp_mul(v, p1, p);
  lim = stack_lim(av,1);
  while (!is_pm1(w))
  { /* a*w = v^2, y primitive 2^e-th root of 1
       a square --> w even power of y, hence w^(2^(e-1)) = 1 */
    p1 = sqrmod(w,p);
    for (k=1; !is_pm1(p1) && k < e; k++) p1 = sqrmod(p1,p);
    if (k == e) { avma=av; return NULL; } /* p composite or (a/p) != 1 */
    /* w ^ (2^k) = 1 --> w = y ^ (u * 2^(e-k)), u odd */
    p1 = y;
    for (i=1; i < e-k; i++) p1 = sqrmod(p1,p);
    y = sqrmod(p1, p); e = k;
    w = Fp_mul(y, w, p);
    v = Fp_mul(v, p1, p);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"Fp_sqrt");
      gerepileall(av,3, &y,&w,&v);
    }
  }
  av1 = avma;
  p1 = subii(p,v); if (cmpii(v,p1) > 0) v = p1; else avma = av1;
  return gerepileuptoint(av, v);
}

/*********************************************************************/
/**                                                                 **/
/**                        GCD & BEZOUT                             **/
/**                                                                 **/
/*********************************************************************/

GEN
lcmii(GEN x, GEN y)
{
  pari_sp av;
  GEN a, b;
  if (!signe(x) || !signe(y)) return gen_0;
  av = avma;
  a = gcdii(x,y); if (!is_pm1(a)) y = diviiexact(y,a);
  b = mulii(x,y); setabssign(b); return gerepileuptoint(av, b);
}

/*********************************************************************/
/**                                                                 **/
/**                      CHINESE REMAINDERS                         **/
/**                                                                 **/
/*********************************************************************/

/*  P.M. & M.H.
 *
 *  Chinese Remainder Theorem.  x and y must have the same type (integermod,
 *  polymod, or polynomial/vector/matrix recursively constructed with these
 *  as coefficients). Creates (with the same type) a z in the same residue
 *  class as x and the same residue class as y, if it is possible.
 *
 *  We also allow (during recursion) two identical objects even if they are
 *  not integermod or polymod. For example, if
 *
 *    x = [1. mod(5, 11), mod(X + mod(2, 7), X^2 + 1)]
 *    y = [1, mod(7, 17), mod(X + mod(0, 3), X^2 + 1)],
 *
 *  then chinese(x, y) returns
 *
 *    [1, mod(16, 187), mod(X + mod(9, 21), X^2 + 1)]
 *
 *  Someone else may want to allow power series, complex numbers, and
 *  quadratic numbers.
 */

GEN
chinese1(GEN x) { return gassoc_proto(chinese,x,NULL); }

GEN
chinese(GEN x, GEN y)
{
  pari_sp av,tetpil;
  long i,lx, tx = typ(x);
  GEN z,p1,p2,d,u,v;

  if (!y) return chinese1(x);
  if (gequal(x,y)) return gcopy(x);
  if (tx == typ(y)) switch(tx)
  {
    case t_POLMOD:
      z = cgetg(3, t_POLMOD);
      if (varn(gel(x,1))!=varn(gel(y,1)))
         pari_err(talker,"incompatible variables in chinese");
      if (RgX_equal(gel(x,1),gel(y,1)))  /* same modulus */
      {
        gel(z,1) = gcopy(gel(x,1));
        gel(z,2) = chinese(gel(x,2),gel(y,2));
        return z;
      }
      av = avma;
      d = RgX_extgcd(gel(x,1),gel(y,1),&u,&v);
      p2 = gsub(gel(y,2), gel(x,2));
      if (!gequal0(gmod(p2, d))) break;
      p1 = gdiv(gel(x,1),d);
      p2 = gadd(gel(x,2), gmul(gmul(u,p1), p2));

      tetpil=avma; gel(z,1) = gmul(p1,gel(y,1)); gel(z,2) = gmod(p2,gel(z,1));
      gerepilecoeffssp(av,tetpil,z+1,2); return z;
    case t_INTMOD:
    {
      GEN A = gel(x,1), B = gel(y,1);
      GEN a = gel(x,2), b = gel(y,2), c, d, C, U;
      z = cgetg(3,t_INTMOD);
      Z_chinese_pre(A, B, &C, &U, &d);
      c = Z_chinese_post(a, b, C, U, d);
      if (!c) pari_err(consister,"Z_chinese");
      gel(z,1) = icopy_avma(C, (pari_sp)z);
      gel(z,2) = icopy_avma(c, (pari_sp)gel(z,1));
      avma = (pari_sp)gel(z,2); return z;
    }
    case t_POL:
      z = cgetg_copy(x, &lx); z[1] = x[1];
      if (lx != lg(y) || varn(x) != varn(y)) break;
      for (i=2; i<lx; i++) gel(z,i) = chinese(gel(x,i),gel(y,i));
      return z;

    case t_VEC: case t_COL: case t_MAT:
      z = cgetg_copy(x, &lx); if (lx!=lg(y)) break;
      for (i=1; i<lx; i++) gel(z,i) = chinese(gel(x,i),gel(y,i));
      return z;
  }
  pari_err(typeer,"chinese");
  return NULL; /* not reached */
}

/* init chinese(Mod(.,A), Mod(.,B)) */
void
Z_chinese_pre(GEN A, GEN B, GEN *pC, GEN *pU, GEN *pd)
{
  GEN u, d = bezout(A,B,&u,NULL); /* U = u(A/d), u(A/d) + v(B/d) = 1 */
  GEN t = diviiexact(A,d);
  *pU = mulii(u, t);
  *pC = mulii(t, B);
  if (pd) *pd = d;
}
/* Assume C = lcm(A, B), U = 0 mod (A/d), U = 1 mod (B/d), a = b mod d,
 * where d = gcd(A,B) or NULL, return x = a (mod A), b (mod B).
 * If d not NULL, check wether a = b mod d. */
GEN
Z_chinese_post(GEN a, GEN b, GEN C, GEN U, GEN d)
{
  GEN b_a;
  if (!signe(a))
  {
    if (d && remii(b, d) != gen_0) return NULL;
    return Fp_mul(b, U, C);
  }
  b_a = subii(b,a);
  if (d && remii(b_a, d) != gen_0) return NULL;
  return modii(addii(a, mulii(U, b_a)), C);
}
GEN
Z_chinese(GEN a, GEN b, GEN A, GEN B)
{
  pari_sp av = avma;
  GEN C, U; Z_chinese_pre(A, B, &C, &U, NULL);
  return gerepileuptoint(av, Z_chinese_post(a,b, C, U, NULL));
}
GEN
Z_chinese_all(GEN a, GEN b, GEN A, GEN B, GEN *pC)
{
  GEN U; Z_chinese_pre(A, B, pC, &U, NULL);
  return Z_chinese_post(a,b, *pC, U, NULL);
}

/* return lift(chinese(a mod A, b mod B))
 * assume(A,B)=1, a,b,A,B integers and C = A*B */
GEN
Z_chinese_coprime(GEN a, GEN b, GEN A, GEN B, GEN C)
{
  pari_sp av = avma;
  GEN U = mulii(Fp_inv(A,B), A);
  return gerepileuptoint(av, Z_chinese_post(a,b,C,U, NULL));
}

/* chinese1 for coprime moduli in Z */
static GEN
chinese1_coprime_Z_aux(GEN x, GEN y)
{
  GEN z = cgetg(3, t_INTMOD);
  GEN A = gel(x,1), a = gel(x, 2);
  GEN B = gel(y,1), b = gel(y, 2), C = mulii(A,B);
  pari_sp av = avma;
  GEN U = mulii(Fp_inv(A,B), A);
  gel(z,2) = gerepileuptoint(av, Z_chinese_post(a,b,C,U, NULL));
  gel(z,1) = C; return z;
}
GEN
chinese1_coprime_Z(GEN x) {return gassoc_proto(chinese1_coprime_Z_aux,x,NULL);}

/*********************************************************************/
/**                                                                 **/
/**                    MODULAR EXPONENTIATION                       **/
/**                                                                 **/
/*********************************************************************/

/* modified Barrett reduction with one fold */
/* See Fast Modular Reduction, W. Hasenplaugh, G. Gaubatz, V. Gopal, ARITH 18 */

static GEN
Fp_invmBarrett(GEN p, long s)
{
  GEN R, Q = dvmdii(int2n(3*s),p,&R);
  return mkvec2(Q,R);
}

static GEN
Fp_rem_mBarrett(GEN a, GEN B, long s, GEN p)
{
  pari_sp av = avma;
  GEN Q = gel(B, 1), R = gel(B, 2);
  long sQ = expi(Q);
  GEN A = addii(remi2n(a, 3*s), mulii(R,shifti(a, -3*s)));
  GEN q = shifti(mulii(shifti(A, sQ-3*s), Q), -sQ);
  GEN r = subii(A, mulii(q, p));
  GEN sr= subii(r,p);     /* Now 0 <= r < 4*p */
  if (signe(sr)<0) return gerepileuptoint(av, r);
  r=sr; sr = subii(r,p);  /* Now 0 <= r < 3*p */
  if (signe(sr)<0) return gerepileuptoint(av, r);
  r=sr; sr = subii(r,p);  /* Now 0 <= r < 2*p */
  return gerepileuptoint(av, signe(sr)>=0 ? sr:r);
}

/* Montgomery reduction */

INLINE ulong
init_montdata(GEN N) { return (ulong) -invmod2BIL(mod2BIL(N)); }

typedef struct muldata {
  GEN N;
  GEN iM;
  ulong inv, s;
  GEN (*res)(struct muldata *,GEN);
  GEN (*mul2)(struct muldata *,GEN);
} muldata;

/* Montgomery reduction */
static GEN
_montred(muldata *D, GEN x)
{
  return red_montgomery(x, D->N, D->inv);
}

static GEN
_remii(muldata *D, GEN x) { return remii(x, D->N); }

static GEN
_remiibar(muldata *D, GEN x) { return Fp_rem_mBarrett(x, D->iM, D->s, D->N); }

/* 2x mod N */
static GEN
_muli2red(muldata *D, GEN x)
{
  GEN z = shifti(x,1);
  return (cmpii(z,D->N) >= 0)? subii(z,D->N): z;
}
static GEN
_muli2montred(muldata *D, GEN x)
{
  GEN z = _muli2red(D,x);
  long l = lgefint(D->N);
  while (lgefint(z) > l) z = subii(z,D->N);
  return z;
}
static GEN
_mul(void *data, GEN x, GEN y)
{
  muldata *D = (muldata *)data;
  return D->res(D, mulii(x,y));
}
static GEN
_sqr(void *data, GEN x)
{
  muldata *D = (muldata *)data;
  return D->res(D, sqri(x));
}
static GEN
_m2sqr(void *data, GEN x)
{
  muldata *D = (muldata *)data;
  return D->mul2(D, D->res(D, sqri(x)));
}
ulong
Fl_powu(ulong x, ulong n0, ulong p)
{
  ulong y, z, n;
  if (n0 <= 2)
  { /* frequent special cases */
    if (n0 == 2) return Fl_sqr(x,p);
    if (n0 == 1) return x;
    if (n0 == 0) return 1;
  }
  if (x <= 1) return x; /* 0 or 1 */
  y = 1; z = x; n = n0;
  for(;;)
  {
    if (n&1) y = Fl_mul(y,z,p);
    n>>=1; if (!n) return y;
    z = Fl_sqr(z,p);
  }
}

static long
Fp_select_red(GEN *y, ulong k, GEN N, long lN, muldata *D)
{
  D->N = N;
  if (lN >= Fp_POW_BARRETT_LIMIT && (k==0 || ((double)k)*expi(*y) > 2 + expi(N)))
  {
    D->mul2 = &_muli2red;
    D->res = &_remiibar;
    D->s = 1+(expi(N)>>1);
    D->iM = Fp_invmBarrett(N, D->s);
    return 0;
  }
  else if (mod2(N) && lN < Fp_POW_REDC_LIMIT)
  {
    *y = remii(shifti(*y, bit_accuracy(lN)), N);
    D->mul2 = &_muli2montred;
    D->res = &_montred;
    D->inv = init_montdata(N);
    return 1;
  }
  else
  {
    D->mul2 = &_muli2red;
    D->res = &_remii;
    return 0;
  }
}

GEN
Fp_powu(GEN A, ulong k, GEN N)
{
  long lN = lgefint(N);
  int base_is_2, use_montgomery;
  muldata  D;

  if (lN == 3) {
    ulong n = (ulong)N[2];
    return utoi( Fl_powu(umodiu(A, n), k, n) );
  }
  if (k <= 2)
  { /* frequent special cases */
    if (k == 2) return Fp_sqr(A,N);
    if (k == 1) return A;
    if (k == 0) return gen_1;
  }

  base_is_2 = 0;
  if (lgefint(A) == 3) switch(A[2])
  {
    case 1: return gen_1;
    case 2:  base_is_2 = 1; break;
  }

  /* TODO: Move this out of here and use for general modular computations */
  use_montgomery = Fp_select_red(&A, k, N, lN, &D);
  if (base_is_2)
    A = leftright_pow_u_fold(A, k, (void*)&D, &_sqr, &_m2sqr);
  else
    A = gen_powu(A, k, (void*)&D, &_sqr, &_mul);
  if (use_montgomery)
  {
    A = _montred(&D, A);
    if (cmpii(A,N) >= 0) A = subii(A,N);
  }
  return A;
}
GEN
Fp_pows(GEN A, long k, GEN N)
{
  if (lgefint(N) == 3) {
    ulong n = N[2];
    ulong a = umodiu(A, n);
    if (k < 0) {
      a = Fl_inv(a, n);
      k = -k;
    }
    return utoi( Fl_powu(a, (ulong)k, n) );
  }
  if (k < 0) { A = Fp_inv(A, N); k = -k; };
  return Fp_powu(A, (ulong)k, N);
}

/* A^K mod N */
GEN
Fp_pow(GEN A, GEN K, GEN N)
{
  pari_sp av = avma;
  long t,s, lN = lgefint(N);
  int base_is_2, use_montgomery;
  GEN y;
  muldata  D;

  s = signe(K);
  if (!s)
  {
    t = signe(remii(A,N)); avma = av;
    return t? gen_1: gen_0;
  }
  if (lN == 3)
  {
    ulong k, n = N[2], a = umodiu(A, n);
    if (s < 0) a = Fl_inv(a, n);
    if (a <= 1) return utoi(a); /* 0 or 1 */
    if (lgefint(K) > 3)
    { /* silly case : huge exponent, small modulus */
      pari_warn(warner, "Mod(a,b)^n with n >> b : wasteful");
      if (s > 0)
      {
        ulong d = ugcd(a, n);
        if (d != 1)
        { /* write n = n1 n2, with n2 maximal such that (n1,a) = 1 */
          ulong n1 = ucoprime_part(n, d), n2 = n/n1;

          k = umodiu(K, eulerphiu(n1));
          /* CRT: = a^K (mod n1), = 0 (mod n2)*/
          return utoi( Fl_mul(Fl_powu(a, k, n1), n2 * Fl_inv(n2,n1), n) );
        }
      }
      /* gcd(a,n) = 1 */
      k = umodiu(K, eulerphiu(n));
    }
    else
      k = (ulong)K[2];
    return utoi(Fl_powu(a, k, n));
  }

  if (s < 0) y = Fp_inv(A,N);
  else
  {
    y = modii(A,N);
    if (!signe(y)) { avma = av; return gen_0; }
  }
  if (lgefint(K) == 3) return gerepileuptoint(av, Fp_powu(y, K[2], N));

  base_is_2 = 0;
  if (lgefint(y) == 3) switch(y[2])
  {
    case 1: avma = av; return gen_1;
    case 2:  base_is_2 = 1; break;
  }

  /* TODO: Move this out of here and use for general modular computations */
  use_montgomery = Fp_select_red(&y, 0UL, N, lN, &D);
  if (base_is_2)
    y = leftright_pow_fold(y, K, (void*)&D, &_sqr, &_m2sqr);
  else
    y = gen_pow(y, K, (void*)&D, &_sqr, &_mul);
  if (use_montgomery)
  {
    y = _montred(&D,y);
    if (cmpii(y,N) >= 0) y = subii(y,N);
  }
  return gerepileuptoint(av,y);
}

static GEN
_Fp_mul(void *E, GEN x, GEN y) { return Fp_mul(x,y,(GEN)E); }

static GEN
_Fp_pow(void *E, GEN x, GEN n) { return Fp_pow(x,n,(GEN)E); }

static GEN
_Fp_rand(void *E) { return addis(randomi(subis((GEN)E,1)),1); }

static const struct bb_group Fp_star={_Fp_mul,_Fp_pow,_Fp_rand,mod2BIL,
                                      cmpii,gequal1};

/*********************************************************************/
/**                                                                 **/
/**               ORDER of INTEGERMOD x  in  (Z/nZ)*                **/
/**                                                                 **/
/*********************************************************************/
ulong
Fl_order(ulong a, ulong o, ulong p)
{
  pari_sp av = avma;
  GEN m, P, E;
  long i;
  if (!o) o = p-1;
  m = factoru(o);
  P = gel(m,1);
  E = gel(m,2);
  for (i = lg(P)-1; i; i--)
  {
    ulong j, l=P[i], e=E[i], t = o / upowuu(l,e), y = Fl_powu(a, t, p);
    if (y == 1) o = t;
    else {
      for (j = 1; j < e; j++) { y = Fl_powu(y, l, p); if (y == 1) break; }
      o = t *  upowuu(l, j);
    }
  }
  avma = av; return o;
}

/*Find the exact order of a assuming a^o==1*/
GEN
Fp_order(GEN a, GEN o, GEN p) {
  if (lgefint(p) == 3 && typ(o) == t_INT && lgefint(o)==3)
  {
    ulong pp = p[2], oo = o[2];
    return utoi( Fl_order(umodiu(a, pp), oo, pp) );
  }
  return gen_eltorder(a, o, (void*)p, &Fp_star);
}

/* return order of a mod p^e, e > 0, pe = p^e */
static GEN
Zp_order(GEN a, GEN p, long e, GEN pe)
{
  GEN ap, op;
  if (equalii(p, gen_2))
  {
    if (e == 1) return gen_1;
    if (e == 2) return mod4(a) == 1? gen_1: gen_2;
    if (mod4(a) == 1)
      op = gen_1;
    else {
      op = gen_2;
      a = Fp_sqr(a, pe);
    }
  } else {
    ap = (e == 1)? a: remii(a,p);
    op = Fp_order(ap, subis(p,1), p);
    if (e == 1) return op;
    a = Fp_pow(a, op, pe); /* 1 mod p */
  }
  if (is_pm1(a)) return op;
  return mulii(op, powiu(p, e - Z_pval(subis(a,1), p)));
}

GEN
znorder(GEN x, GEN o)
{
  pari_sp av = avma;
  GEN b, a;

  if (typ(x) != t_INTMOD)
    pari_err(talker,"not an element of (Z/nZ)* in order");
  b = gel(x,1); a = gel(x,2);
  if (!gequal1(gcdii(a,b)))
    pari_err(talker,"not an element of (Z/nZ)* in order");
  if (!o)
  {
    GEN fa = Z_factor(b), P = gel(fa,1), E = gel(fa,2);
    long i, l = lg(P);
    o = gen_1;
    for (i = 1; i < l; i++)
    {
      GEN p = gel(P,i);
      long e = itos(gel(E,i));

      if (l == 2)
        o = Zp_order(a, p, e, b);
      else {
        GEN pe = powiu(p,e);
        o = lcmii(o, Zp_order(remii(a,pe), p, e, pe));
      }
    }
    return gerepileuptoint(av, o);
  }
  return Fp_order(a, o, b);
}
GEN
order(GEN x) { return znorder(x, NULL); }

/*********************************************************************/
/**                                                                 **/
/**               DISCRETE LOGARITHM  in  (Z/nZ)*  i                **/
/**                                                                 **/
/*********************************************************************/
static GEN
_Fp_easylog(void *E, GEN x, GEN g, GEN ord)
{
  pari_sp av = avma;
  GEN p1, p = (GEN)E;
  (void)g;
  if (is_pm1(x)) return gen_0;
  /* p > 2 */
  p1 = addsi(-1, p);
  if (equalii(p1,x))  /* -1 */
  {
    ord = dlog_get_ord(ord);
    if (!ord) ord = p1;
    return gerepileupto(av, shifti(ord,-1));
  }
  avma = av; return NULL;
}

GEN
Fp_log(GEN a, GEN g, GEN ord, GEN p)
{
  return gen_PH_log(a,g,ord,(void*)p,&Fp_star,_Fp_easylog);
}

/* find a s.t. g^a = x (mod p^k), p prime, k > 0, (x,p) = 1, g primitive root
 * mod p^2 [ hence mod p^k ] */
#if 0
/* direct Pohlig-Helmann: O(k log p) mul*/
static GEN
Zplog2(GEN x, GEN g, GEN p, ulong k, GEN pk)
{
  ulong l;
  GEN b, c, ct, t, pl, pl_1, q, Q;
  if (k == 1) return Fp_log(x, g, subis(p,1), p);
  l = (k+1) >> 1;
  pl_1 = powiu(p, l-1);
  pl = mulii(pl_1, p);
  q = odd(k)? pl_1: pl;
  Q = subii(pl, pl_1);
  /* write a = b + Q c, Q = (p-1)p^(l-1), c defined mod q */
  b = Zplog2(remii(x, pl), remii(g, pl), p, l, pl); /* g^b = x (mod p^l) */
  /* G := g^Q = 1 + t p^l (mod p^k), (t,p) = 1 */
  t = diviiexact(subis(Fp_pow(g, Q, pk), 1), pl);
  /* G^c = 1 + c p^l t (mod p^k) = x g^-b */
  ct = diviiexact(subis(Fp_mul(x, Fp_pow(g, negi(b), pk), pk), 1), pl);
  c = Fp_mul(ct, Fp_inv(t, q), q);
  return addii(b, mulii(c, Q));
}
#else
/* use p-adic log: O(log p + k) mul*/
static GEN
Zplog(GEN x, GEN g, GEN p, ulong k, GEN pk, GEN o)
{
  GEN b, n = subis(p,1), a = Fp_log(x, g, o?o:n, p);
  if (k == 1) return a;
  x = Fp_mul(x, Fp_pow(g, negi(a), pk), pk);
  b = gdiv(Qp_log(cvtop(x, p, k)), Qp_log(cvtop(Fp_pow(g,n,pk), p, k)));
  return addii(a, mulii(n, gtrunc(b)));
}
#endif

GEN
znlog(GEN x, GEN g, GEN o)
{
  pari_sp av = avma;
  long k;
  GEN p, pk;
  switch (typ(g))
  {
    case t_PADIC: {
      pk = gel(g,3); k = precp(g);
      p = gel(g,2); x = Rg_to_Fp(x, pk);
      if (equaliu(p, 2))
      {
        if (k > 2) pari_err(talker, "not a primitive root in znlog");
        avma = av; return is_pm1(x)? gen_0: gen_1;
      }
      g = gel(g,4);
      break;
    }
    case t_INTMOD: {
      long e;
      pk = gel(g,1);
      e = mod4(pk);
      if (e == 0)
      {
        if (!equaliu(pk, 4)) pari_err(talker, "not a primitive root in znlog");
        x = Rg_to_Fp(x, pk);
        avma = av; return is_pm1(x)? gen_0: gen_1;
      }
      g = gel(g,2);
      if (e == 2) {
        if (equaliu(pk, 2)) return gen_0;
        pk = shifti(pk, -1);
        if (cmpii(g, pk) >= 0) g = subii(g, pk);
      }
      x = Rg_to_Fp(x, pk);
      k = Z_isanypower(pk, &p);
      if (!k) { p = pk; k = 1; }
      break;
    }
    default: pari_err(talker,"not an element of (Z/pZ)* in znlog");
      return NULL; /* not reached */
  }
  return gerepileuptoint(av, Zplog(x, g, p, k, pk, o));
}

GEN
Fp_sqrtn(GEN a, GEN n, GEN p, GEN *zeta)
{
  a = modii(a,p);
  if (!signe(a))
  {
    if (zeta) *zeta = gen_1;
    return gen_0;
  }
  return gen_Shanks_sqrtn(a,n,addis(p,-1),zeta,(void*)p,&Fp_star);
}

/*********************************************************************/
/**                                                                 **/
/**                    FUNDAMENTAL DISCRIMINANTS                    **/
/**                                                                 **/
/*********************************************************************/
static long
isfund(GEN x) {
  if (typ(x) != t_INT) pari_err(arither1);
  return Z_isfundamental(x);
}
GEN
gisfundamental(GEN x) { return map_proto_lG(isfund,x); }

long
Z_isfundamental(GEN x)
{
  long r;
  if (!signe(x)) return 0;
  r = mod16(x);
  if (!r) return 0;
  if ((r & 3) == 0)
  {
    pari_sp av;
    r >>= 2; /* |x|/4 mod 4 */
    if (signe(x) < 0) r = 4-r;
    if (r == 1) return 0;
    av = avma;
    r = Z_issquarefree( shifti(x,-2) );
    avma = av; return r;
  }
  r &= 3; /* |x| mod 4 */
  if (signe(x) < 0) r = 4-r;
  return (r==1) ? Z_issquarefree(x) : 0;
}

GEN
quaddisc(GEN x)
{
  const pari_sp av = avma;
  long i,r,tx=typ(x);
  GEN P,E,f,s;

  if (!is_rational_t(tx)) pari_err(arither1);
  f = factor(x);
  P = gel(f,1);
  E = gel(f,2); s = gen_1;
  for (i=1; i<lg(P); i++)
    if (odd(mael(E,i,2))) s = mulii(s,gel(P,i));
  r = mod4(s); if (gsigne(x) < 0) r = 4-r;
  if (r>1) s = shifti(s,2);
  return gerepileuptoint(av, s);
}

/*********************************************************************/
/**                                                                 **/
/**                              FACTORIAL                          **/
/**                                                                 **/
/*********************************************************************/
/* return a * (a+1) * ... * b. Assume a <= b  [ note: factoring out powers of 2
 * first is slower ... ] */
GEN
mulu_interval(ulong a, ulong b)
{
  pari_sp av = avma;
  ulong k, l, N, n = b - a + 1;
  long lx;
  GEN x;

  if (n < 61)
  {
    x = utoi(a);
    for (k=a+1; k<=b; k++) x = mului(k,x);
    return gerepileuptoint(av, x);
  }
  lx = 1; x = cgetg(2 + n/2, t_VEC);
  N = b + a;
  for (k = a;; k++)
  {
    l = N - k; if (l <= k) break;
    gel(x,lx++) = muluu(k,l);
  }
  if (l == k) gel(x,lx++) = utoipos(k);
  setlg(x, lx);
  return gerepileuptoint(av, divide_conquer_prod(x, mulii));
}

GEN
mpfact(long n)
{
  if (n < 2)
  {
    if (n < 0) pari_err(talker,"negative argument in factorial function");
    return gen_1;
  }
  return mulu_interval(2UL, (ulong)n);
}

/*******************************************************************/
/**                                                               **/
/**                      LUCAS & FIBONACCI                        **/
/**                                                               **/
/*******************************************************************/
static void
lucas(ulong n, GEN *a, GEN *b)
{
  GEN z, t, zt;
  if (!n) { *a = gen_2; *b = gen_1; return; }
  lucas(n >> 1, &z, &t); zt = mulii(z, t);
  switch(n & 3) {
    case  0: *a = addsi(-2,sqri(z)); *b = addsi(-1,zt); break;
    case  1: *a = addsi(-1,zt);      *b = addsi(2,sqri(t)); break;
    case  2: *a = addsi(2,sqri(z));  *b = addsi(1,zt); break;
    case  3: *a = addsi(1,zt);       *b = addsi(-2,sqri(t));
  }
}

GEN
fibo(long n)
{
  pari_sp av = avma;
  GEN a, b;
  if (!n) return gen_0;
  lucas((ulong)(labs(n)-1), &a, &b);
  a = diviuexact(addii(shifti(a,1),b), 5);
  if (n < 0 && !odd(n)) setsigne(a, -1);
  return gerepileuptoint(av, a);
}

/*******************************************************************/
/*                                                                 */
/*                      CONTINUED FRACTIONS                        */
/*                                                                 */
/*******************************************************************/
static GEN
icopy_lg(GEN x, long l)
{
  long lx = lgefint(x);
  GEN y;

  if (lx >= l) return icopy(x);
  y = cgeti(l); affii(x, y); return y;
}

/* continued fraction of a/b. If y != NULL, stop when partial quotients
 * differ from y */
static GEN
Qsfcont(GEN a, GEN b, GEN y, ulong k)
{
  GEN  z, c;
  ulong i, l, ly = lgefint(b);

  /* times log(2) / log2( (1+sqrt(5)) / 2 )  */
  l = (ulong)(3 + bit_accuracy_mul(ly, 1.44042009041256));
  if (k > 0 && k+1 > 0 && l > k+1) l = k+1; /* beware overflow */
  if (l > LGBITS) l = LGBITS;

  z = cgetg(l,t_VEC);
  l--;
  if (y) {
    pari_sp av = avma;
    if (l >= (ulong)lg(y)) l = lg(y)-1;
    for (i = 1; i <= l; i++)
    {
      GEN q = gel(y,i);
      gel(z,i) = q;
      c = b; if (!gequal1(q)) c = mulii(q, b);
      c = subii(a, c);
      if (signe(c) < 0)
      { /* partial quotient too large */
        c = addii(c, b);
        if (signe(c) >= 0) i++; /* by 1 */
        break;
      }
      if (cmpii(c, b) >= 0)
      { /* partial quotient too small */
        c = subii(c, b);
        if (cmpii(c, b) < 0) {
          /* by 1. If next quotient is 1 in y, add 1 */
          if (i < l && is_pm1(gel(y,i+1))) gel(z,i) = addis(q,1);
          i++;
        }
        break;
      }
      if ((i & 0xff) == 0) gerepileall(av, 2, &b, &c);
      a = b; b = c;
    }
  } else {
    a = icopy_lg(a, ly);
    b = icopy(b);
    for (i = 1; i <= l; i++)
    {
      gel(z,i) = truedvmdii(a,b,&c);
      if (c == gen_0) { i++; break; }
      affii(c, a); cgiv(c); c = a;
      a = b; b = c;
    }
  }
  i--;
  if (i > 1 && gequal1(gel(z,i)))
  {
    cgiv(gel(z,i)); --i;
    gel(z,i) = addsi(1, gel(z,i)); /* unclean: leave old z[i] on stack */
  }
  setlg(z,i+1); return z;
}

static GEN
sersfcont(GEN a, GEN b, long k)
{
  long i, l = typ(a) == t_POL? lg(a): 3;
  GEN y, c;
  if (lg(b) > l) l = lg(b);
  if (k > 0 && l > k+1) l = k+1;
  y = cgetg(l,t_VEC);
  for (i=1; i<l; i++)
  {
    gel(y,i) = poldivrem(a,b,&c);
    if (gequal0(c)) { i++; break; }
    a = b; b = c;
  }
  setlg(y, i); return y;
}

GEN
gboundcf(GEN x, long k)
{
  pari_sp av;
  long lx, tx = typ(x), e;
  GEN y, a, b, c;

  if (k < 0) pari_err(talker, "negative nmax in gboundcf");
  if (is_scalar_t(tx))
  {
    if (gequal0(x)) return mkvec(gen_0);
    switch(tx)
    {
      case t_INT: return mkveccopy(x);
      case t_REAL:
        av = avma; lx = lg(x);
        e = bit_accuracy(lx)-1-expo(x);
        if (e < 0) pari_err(talker,"integral part not significant in gboundcf");
        c = trunc2nr_lg(x,lx,0);
        y = int2n(e);
        a = Qsfcont(c,y, NULL, k);
        b = addsi(signe(x), c);
        return gerepilecopy(av, Qsfcont(b,y, a, k));

      case t_FRAC:
        av = avma;
        return gerepileupto(av, Qsfcont(gel(x,1),gel(x,2), NULL, k));
    }
    pari_err(typeer,"gboundcf");
  }

  switch(tx)
  {
    case t_POL: return mkveccopy(x);
    case t_SER:
      av = avma;
      return gerepileupto(av, gboundcf(ser2rfrac_i(x), k));
    case t_RFRAC:
      av = avma;
      return gerepilecopy(av, sersfcont(gel(x,1), gel(x,2), k));
  }
  pari_err(typeer,"gboundcf");
  return NULL; /* not reached */
}

static GEN
sfcont2(GEN b, GEN x, long k)
{
  pari_sp av = avma;
  long lb = lg(b), tx = typ(x), i;
  GEN y,p1;

  if (k)
  {
    if (k >= lb) pari_err(talker,"list of numerators too short in sfcontf2");
    lb = k+1;
  }
  y = cgetg(lb,t_VEC);
  if (lb==1) return y;
  if (is_scalar_t(tx))
  {
    if (!is_intreal_t(tx) && tx != t_FRAC) pari_err(typeer,"sfcont2");
  }
  else if (tx == t_SER) x = ser2rfrac_i(x);

  if (!gequal1(gel(b,1))) x = gmul(gel(b,1),x);
  for (i = 1;;)
  {
    if (tx == t_REAL)
    {
      long e = expo(x);
      if (e > 0 && nbits2prec(e+1) > lg(x)) break;
      gel(y,i) = floorr(x);
      p1 = subri(x, gel(y,i));
    }
    else
    {
      gel(y,i) = gfloor(x);
      p1 = gsub(x, gel(y,i));
    }
    if (++i >= lb) break;
    if (gequal0(p1)) break;
    x = gdiv(gel(b,i),p1);
  }
  setlg(y,i);
  return gerepilecopy(av,y);
}


GEN
gcf(GEN x)
{
  return gboundcf(x,0);
}

GEN
gcf2(GEN b, GEN x)
{
  return contfrac0(x,b,0);
}

GEN
contfrac0(GEN x, GEN b, long nmax)
{
  long tb;

  if (!b) return gboundcf(x,nmax);
  tb = typ(b);
  if (tb == t_INT) return gboundcf(x,itos(b));
  if (! is_vec_t(tb)) pari_err(typeer,"contfrac0");
  if (nmax < 0) pari_err(talker, "negative nmax in contfrac0");
  return sfcont2(b,x,nmax);
}

GEN
pnqn(GEN x)
{
  pari_sp av = avma;
  long i, lx, tx = typ(x);
  GEN p0, p1, q0, q1, a, p2, q2;

  if (! is_matvec_t(tx)) pari_err(typeer,"pnqn");
  lx = lg(x); if (lx == 1) return matid(2);
  p0 = gen_1; q0 = gen_0;
  if (tx != t_MAT)
  {
    p1 = gel(x,1); q1 = gen_1;
    for (i=2; i<lx; i++)
    {
      a = gel(x,i);
      p2 = gadd(gmul(a,p1),p0); p0=p1; p1=p2;
      q2 = gadd(gmul(a,q1),q0); q0=q1; q1=q2;
    }
  }
  else
  {
    long ly = lg(x[1]);
    if (ly==2)
    {
      p1 = gcoeff(x,1,1); q1 = gen_1;
      for (i=2; i<lx; i++)
      {
        a = gcoeff(x,1,i);
        p2 = gadd(gmul(a,p1),p0); p0=p1; p1=p2;
        q2 = gadd(gmul(a,q1),q0); q0=q1; q1=q2;
      }
    }
    else
    {
      if (ly != 3) pari_err(talker,"incorrect size in pnqn");
      p1 = gcoeff(x,2,1); q1 = gcoeff(x,1,1);
      for (i=2; i<lx; i++)
      {
        GEN b = gcoeff(x,1,i);
        a = gcoeff(x,2,i);
        p2 = gadd(gmul(a,p1),gmul(b,p0)); p0=p1; p1=p2;
        q2 = gadd(gmul(a,q1),gmul(b,q0)); q0=q1; q1=q2;
      }
    }
  }
  return gerepilecopy(av, mkmat2(mkcol2(p1,q1), mkcol2(p0,q0)));
}

/* x t_INTMOD. Look for coprime integers a<=A and b<=B, such that a/b = x */
GEN
bestappr_mod(GEN x, GEN A, GEN B)
{
  long i, lx;
  GEN y;
  switch(typ(x))
  {
    case t_INTMOD:
    {
      pari_sp av = avma;
      GEN a,b,d, t = cgetg(3, t_FRAC);
      if (! ratlift(gel(x,2), gel(x,1), A,B, &a,&b)) return NULL;
      if (is_pm1(b)) return icopy_avma(a, av);
      d = gcdii(a,b);
      if (!is_pm1(d)) { avma = av; return NULL; }
      cgiv(d);
      gel(t,1) = a;
      gel(t,2) = b; return t;
    }
    case t_POLMOD:
    {
      pari_sp av = avma;
      GEN a,b,d;
      if (! RgXQ_ratlift(gel(x,2), gel(x,1), itos(A), itos(B), &a,&b))
        return NULL;
      d = RgX_gcd(a,b);
      if (degpol(d)>0) { avma = av; return NULL; }
      return gerepileupto(av, gdiv(a,b));
    }
    case t_COMPLEX: {
        GEN t;
        y = cgetg(3, t_COMPLEX);
        t = bestappr_mod(gel(x,1),A,B); if (!t) return NULL;
        gel(y,1) = t;
        t = bestappr_mod(gel(x,2),A,B); if (!t) return NULL;
        gel(y,2) = t; return y;
      }
    case t_POL: case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++)
      {
        GEN t = bestappr_mod(gel(x,i),A,B);
        if (!t) return NULL;
        gel(y,i) = t;
      }
      return y;
    case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++)
      {
        GEN t = bestappr_mod(gel(x,i),A,B);
        if (!t) return NULL;
        gel(y,i) = t;
      }
      return y;
  }
  pari_err(typeer,"bestappr0");
  return NULL; /* not reached */
}

/* bestappr(t_REAL != 0), to maximal accuracy */
static GEN
bestappr_max(GEN x)
{
  pari_sp av = avma;
  GEN p0, p1, p, q0, q1, q, a;
  long e;
  p1 = gen_1; a = p0 = floorr(x); q1 = gen_0; q0 = gen_1;
  x = subri(x,a); /* 0 <= x < 1 */
  e = bit_accuracy(lg(x)) - expo(x);
  for(;;)
  {
    long d;
    if (!signe(x) || expi(q0) > e) { p1 = p0; q1 = q0; break; }
    x = invr(x); /* > 1 */
    d = nbits2prec(expo(x) + 1);
    if (d > lg(x)) { p1 = p0; q1 = q0; break; } /* original x was ~ 0 */

    a = truncr(x); /* truncr(x) will NOT raise precer */
    p = addii(mulii(a,p0), p1); p1=p0; p0=p;
    q = addii(mulii(a,q0), q1); q1=q0; q0=q;
    x = subri(x,a); /* 0 <= x < 1 */
  }
  return gerepileupto(av, gdiv(p1,q1));
}

/* allow k = NULL: maximal accuracy */
GEN
bestappr(GEN x, GEN k)
{
  pari_sp av = avma;
  long lx, i;
  GEN p0, p1, p, q0, q1, q, a, y;

  if (k) {
    switch(typ(k))
    {
      case t_INT: break;
      case t_REAL: case t_FRAC: k = gcvtoi(k,&i); break;
      default:
        pari_err(talker,"incorrect bound type in bestappr");
    }
    if (signe(k) <= 0) k = gen_1;
  }
  switch(typ(x))
  {
    case t_INT:
      avma = av; return icopy(x);

    case t_FRAC:
      if (!k || cmpii(gel(x,2),k) <= 0) { avma = av; return gcopy(x); }
      y = x;
      p1 = gen_1; p0 = truedvmdii(gel(x,1), gel(x,2), &a); /* = floor(x) */
      q1 = gen_0; q0 = gen_1;
      x = mkfrac(a, gel(x,2)); /* = frac(x); now 0<= x < 1 */
      for(;;)
      {
        x = ginv(x); /* > 1 */
        a = typ(x)==t_INT? x: divii(gel(x,1), gel(x,2));
        if (cmpii(a,k) > 0)
        { /* next partial quotient will overflow limits */
          GEN n, d;
          a = divii(subii(k, q1), q0);
          p = addii(mulii(a,p0), p1); p1=p0; p0=p;
          q = addii(mulii(a,q0), q1); q1=q0; q0=q;
          /* compare |y-p0/q0|, |y-p1/q1| */
          n = gel(y,1);
          d = gel(y,2);
          if (absi_cmp(mulii(q1, subii(mulii(q0,n), mulii(d,p0))),
                       mulii(q0, subii(mulii(q1,n), mulii(d,p1)))) < 0)
                       { p1 = p0; q1 = q0; }
          break;
        }
        p = addii(mulii(a,p0), p1); p1=p0; p0=p;
        q = addii(mulii(a,q0), q1); q1=q0; q0=q;

        if (cmpii(q0,k) > 0) break;
        x = gsub(x,a); /* 0 <= x < 1 */
        if (typ(x) == t_INT) { p1 = p0; q1 = q0; break; } /* x = 0 */

      }
      return gerepileupto(av, gdiv(p1,q1));

    case t_REAL: {
      long lx;
      GEN kr;

      if (!signe(x)) return gen_0;
      if (!k) return bestappr_max(x);
      y = x;
      p1 = gen_1; a = p0 = floorr(x);
      q1 = gen_0; q0 = gen_1;
      x = subri(x,a); /* 0 <= x < 1 */
      lx = lg(x);
      if (lx == 2) { cgiv(x); return a; }
      kr = itor(k, lx);
      for(;;)
      {
        x = invr(x); /* > 1 */
        if (cmprr(x,kr) > 0)
        { /* next partial quotient will overflow limits */
          a = divii(subii(k, q1), q0);
          p = addii(mulii(a,p0), p1); p1=p0; p0=p;
          q = addii(mulii(a,q0), q1); q1=q0; q0=q;
          /* compare |y-p0/q0|, |y-p1/q1| */
          if (absr_cmp(mulir(q1, subri(mulir(q0,y), p0)),
                       mulir(q0, subri(mulir(q1,y), p1))) < 0)
                       { p1 = p0; q1 = q0; }
          break;
        }
        a = truncr(x); /* truncr(x) may raise precer */
        p = addii(mulii(a,p0), p1); p1=p0; p0=p;
        q = addii(mulii(a,q0), q1); q1=q0; q0=q;

        if (cmpii(q0,k) > 0) break;
        x = subri(x,a); /* 0 <= x < 1 */
        if (!signe(x)) { p1 = p0; q1 = q0; break; }
      }
      return gerepileupto(av, gdiv(p1,q1));
   }
   case t_COMPLEX:
      y = cgetg(3, t_COMPLEX);
      gel(y,1) = bestappr(gel(x,1),k);
      gel(y,2) = bestappr(gel(x,2),k);
      return y;
   case t_POL: case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = bestappr(gel(x,i),k);
      return y;
   case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = bestappr(gel(x,i),k);
      return y;
  }
  pari_err(typeer,"bestappr");
  return NULL; /* not reached */
}

GEN
bestappr0(GEN x, GEN a, GEN b)
{
  pari_sp av;
  GEN t;
  if (!b) return bestappr(x,a);
  av = avma;
  t = bestappr_mod(x,a,b);
  if (!t) { avma = av; return gen_m1; }
  return t;
}

/***********************************************************************/
/**                                                                   **/
/**         FUNDAMENTAL UNIT AND REGULATOR (QUADRATIC FIELDS)         **/
/**                                                                   **/
/***********************************************************************/

static GEN
get_quad(GEN f, GEN pol, long r)
{
  GEN p1 = gcoeff(f,1,2), q1 = gcoeff(f,2,2);
  return mkquad(pol, r? subii(p1,q1): p1, q1);
}

/* replace f by f * [a,1; 1,0] */
static void
update_f(GEN f, GEN a)
{
  GEN p1;
  p1 = gcoeff(f,1,1);
  gcoeff(f,1,1) = addii(mulii(a,p1), gcoeff(f,1,2));
  gcoeff(f,1,2) = p1;

  p1 = gcoeff(f,2,1);
  gcoeff(f,2,1) = addii(mulii(a,p1), gcoeff(f,2,2));
  gcoeff(f,2,2) = p1;
}

GEN
quadunit(GEN x)
{
  pari_sp av = avma, av2, lim;
  GEN pol, y, a, u, v, sqd, f;
  long r;

  check_quaddisc_real(x, &r, "quadunit");
  pol = quadpoly(x);
  sqd = sqrti(x); av2 = avma; lim = stack_lim(av2,2);
  a = shifti(addsi(r,sqd),-1);
  f = mkmat2(mkcol2(a, gen_1), mkcol2(gen_1, gen_0)); /* [a,0; 1,0] */
  u = stoi(r); v = gen_2;
  for(;;)
  {
    GEN u1, v1;
    u1 = subii(mulii(a,v),u);
    v1 = divii(subii(x,sqri(u1)),v);
    if ( equalii(v,v1) ) {
      y = get_quad(f,pol,r);
      update_f(f,a);
      y = gdiv(get_quad(f,pol,r), gconj(y));
      break;
    }
    a = divii(addii(sqd,u1), v1);
    if ( equalii(u,u1) ) {
      y = get_quad(f,pol,r);
      y = gdiv(y, gconj(y));
      break;
    }
    update_f(f,a);
    u = u1; v = v1;
    if (low_stack(lim, stack_lim(av2,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"quadunit");
      gerepileall(av2,4, &a,&f,&u,&v);
    }
  }
  if (signe(y[3]) < 0) y = gneg(y);
  return gerepileupto(av, y);
}

GEN
quadregulator(GEN x, long prec)
{
  pari_sp av = avma, av2, lim;
  GEN R, rsqd, u, v, sqd;
  long r, Rexpo;

  check_quaddisc_real(x, &r, "quadregulator");
  sqd = sqrti(x);
  rsqd = gsqrt(x,prec);
  Rexpo = 0; R = real2n(1, prec); /* = 2 */
  av2 = avma; lim = stack_lim(av2,2);
  u = stoi(r); v = gen_2;
  for(;;)
  {
    GEN u1 = subii(mulii(divii(addii(u,sqd),v), v), u);
    GEN v1 = divii(subii(x,sqri(u1)),v);
    if (equalii(v,v1))
    {
      R = sqrr(R); setexpo(R,expo(R)-1);
      R = mulrr(R, divri(addir(u1,rsqd),v));
      break;
    }
    if (equalii(u,u1))
    {
      R = sqrr(R); setexpo(R,expo(R)-1);
      break;
    }
    R = mulrr(R, divri(addir(u1,rsqd),v));
    Rexpo += expo(R); setexpo(R,0);
    u = u1; v = v1;
    if (Rexpo & ~EXPOBITS) pari_err(talker,"exponent overflow in quadregulator");
    if (low_stack(lim, stack_lim(av2,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"quadregulator");
      gerepileall(av2,3, &R,&u,&v);
    }
  }
  R = logr_abs(divri(R,v));
  if (Rexpo)
  {
    GEN t = mulsr(Rexpo, mplog2(prec));
    setexpo(t, expo(t)+1);
    R = addrr(R,t);
  }
  return gerepileuptoleaf(av, R);
}

/*************************************************************************/
/**                                                                     **/
/**                            CLASS NUMBER                             **/
/**                                                                     **/
/*************************************************************************/

GEN
qfbclassno0(GEN x,long flag)
{
  switch(flag)
  {
    case 0: return map_proto_G(classno,x);
    case 1: return map_proto_G(classno2,x);
    default: pari_err(flagerr,"qfbclassno");
  }
  return NULL; /* not reached */
}

/* f^h = 1, return order(f) */
static GEN
find_order(GEN f, GEN h)
{
  GEN fh, p,e;
  long i,j,lim;

  p = Z_factor(h);
  e =gel(p,2);
  p =gel(p,1);
  for (i=1; i<lg(p); i++)
  {
    lim = itos(gel(e,i));
    for (j=1; j<=lim; j++)
    {
      GEN q = diviiexact(h,gel(p,i));
      fh = powgi(f, q);
      if (!is_pm1(gel(fh,1))) break;
      h = q;
    }
  }
  return h;
}

static GEN
end_classno(GEN h, GEN hin, GEN forms, long lform)
{
  long i,com;
  GEN a,b,p1,q,fh,fg, f = gel(forms,0);

  h = find_order(f,h); /* H = <f> */
  q = diviiround(hin, h); /* approximate order of G/H */
  for (i=1; i < lform; i++)
  {
    pari_sp av = avma;
    fg = powgi(gel(forms,i), h);
    fh = powgi(fg, q);
    a = gel(fh,1);
    if (is_pm1(a)) continue;
    b = gel(fh,2); p1 = fg;
    for (com=1; ; com++, p1 = gmul(p1,fg))
      if (equalii(gel(p1,1), a) && absi_equal(gel(p1,2), b)) break;
    if (signe(p1[2]) == signe(b)) com = -com;
    /* f_i ^ h(q+com) = 1 */
    q = addsi(com,q);
    if (gequal0(q))
    { /* f^(ih) != 1 for all 0 < i <= oldq. Happen if the original upper bound
         for h was wrong */
      long c;
      p1 = fh;
      for (c=1; ; c++, p1 = gmul(p1,fh))
        if (gequal1(gel(p1,1))) break;
      q = mulsi(-com, find_order(fh, utoipos((ulong)c)));
    }
    q = gerepileuptoint(av, q);
  }
  return mulii(q,h);
}

/* Write x = Df^2, where D = fundamental discriminant,
 * P^E = factorisation of conductor f, with E[i] >= 0 */
static void
corediscfact(GEN x, long xmod4, GEN *ptD, GEN *ptP, GEN *ptE)
{
  long s = signe(x), l, i;
  GEN fa = Z_factor(s < 0? absi(x): x);
  GEN d, P = gel(fa,1), E = gtovecsmall(gel(fa,2));

  l = lg(P); d = gen_1;
  for (i=1; i<l; i++)
  {
    if (E[i] & 1) d = mulii(d, gel(P,i));
    E[i] >>= 1;
  }
  if (!xmod4 && mod4(d) != ((s < 0)? 3: 1)) { d = shifti(d,2); E[1]--; }
  *ptD = (s < 0)? negi(d): d;
  *ptP = P;
  *ptE = E;
}

static GEN
conductor_part(GEN x, long xmod4, GEN *ptD, GEN *ptreg)
{
  long l, i, s = signe(x);
  GEN E, H, D, P, reg;

  corediscfact(x, xmod4, &D, &P, &E);
  H = gen_1; l = lg(P);
  /* f \prod_{p|f}  [ 1 - (D/p) p^-1 ] = \prod_{p^e||f} p^(e-1) [ p - (D/p) ] */
  for (i=1; i<l; i++)
  {
    long e = E[i];
    if (e)
    {
      GEN p = gel(P,i);
      H = mulii(H, subis(p, kronecker(D,p)));
      if (e >= 2) H = mulii(H, powiu(p,e-1));
    }
  }

  /* divide by [ O_K^* : O^* ] */
  if (s < 0)
  {
    reg = NULL;
    switch(itou_or_0(D))
    {
      case 4: H = shifti(H,-1); break;
      case 3: H = divis(H,3); break;
    }
  } else {
    reg = quadregulator(D,DEFAULTPREC);
    if (!equalii(x,D))
      H = divii(H, roundr(divrr(quadregulator(x,DEFAULTPREC), reg)));
  }
  if (ptreg) *ptreg = reg;
  *ptD = D; return H;
}

static long
two_rank(GEN x)
{
  GEN p = gel(Z_factor(absi(x)),1);
  long l = lg(p)-1;
#if 0 /* positive disc not needed */
  if (signe(x) > 0)
  {
    long i;
    for (i=1; i<=l; i++)
      if (mod4(gel(p,i)) == 3) { l--; break; }
  }
#endif
  return l-1;
}

static GEN
sqr_primeform(GEN x, long f) { return redimag(qfisqr(primeform_u(x, f))); }

#define MAXFORM 11
#define _low(to, x) { GEN __x = (GEN)(x); to = signe(__x)?mod2BIL(__x):0; }

/* h(x) for x<0 using Baby Step/Giant Step.
 * Assumes G is not too far from being cyclic.
 *
 * Compute G^2 instead of G so as to kill most of the non-cyclicity */
GEN
classno(GEN x)
{
  pari_sp av = avma, av2, lim;
  long r2,c,lforms,k,l,i,j,com,s, forms[MAXFORM];
  GEN count,index,tabla,tablb,hash,p1,p2,hin,h,f,fh,fg,ftest;
  GEN Hf, D;
  byteptr p = diffptr;

  if (signe(x) >= 0) return classno2(x);

  check_quaddisc(x, &s, &k, "classno");
  if (cmpiu(x,12) <= 0) return gen_1;

  Hf = conductor_part(x, k, &D, NULL);
  if (cmpiu(D,12) <= 0) return gerepilecopy(av, Hf);

  p2 = gsqrt(absi(D),DEFAULTPREC);
  p1 = mulrr(divrr(p2,mppi(DEFAULTPREC)), dbltor(1.005)); /*overshoot by 0.5%*/
  s = itos_or_0( truncr(shiftr(sqrtr(p2), 1)) );
  if (!s) pari_err(talker,"discriminant too big in classno");
  if (s < 10) s = 200;
  else if (s < 20) s = 1000;
  else if (s < 5000) s = 5000;

  c = lforms = 0; maxprime_check(s);
  while (c <= s)
  {
    long d;
    NEXT_PRIME_VIADIFF(c,p);

    k = krois(D,c); if (!k) continue;
    if (k > 0)
    {
      if (lforms < MAXFORM) forms[lforms++] = c;
      d = c - 1;
    }
    else
      d = c + 1;
    av2 = avma;
    affrr(divru(mulur(c,p1),d), p1);
    avma = av2;
  }
  r2 = two_rank(D);
  h = hin = roundr(shiftr(p1, -r2));
  s = 2*itos(gceil(sqrtnr(p1, 4)));
  if (s > 10000) s = 10000;

  count = new_chunk(256); for (i=0; i<=255; i++) count[i]=0;
  index = new_chunk(257);
  tabla = new_chunk(10000);
  tablb = new_chunk(10000);
  hash  = new_chunk(10000);
  f = sqr_primeform(D, forms[0]);
  p1 = fh = powgi(f, h);
  for (i=0; i<s; i++, p1 = qficomp(p1,f))
  {
    _low(tabla[i], p1[1]);
    _low(tablb[i], p1[2]); count[tabla[i]&255]++;
  }
  /* follow the idea of counting sort to avoid maintaining linked lists in
   * hashtable */
  index[0]=0; for (i=0; i< 255; i++) index[i+1] = index[i]+count[i];
  /* index[i] = # of forms hashing to <= i */
  for (i=0; i<s; i++) hash[ index[tabla[i]&255]++ ] = i;
  index[0]=0; for (i=0; i<=255; i++) index[i+1] = index[i]+count[i];
  /* hash[index[i-1]..index[i]-1] = forms hashing to i */

  fg = gpowgs(f,s); av2 = avma; lim = stack_lim(av2,2);
  ftest = gpowgs(p1,0);
  for (com=0; ; com++)
  {
    long j1, j2;
    GEN a, b;
    a = gel(ftest,1); _low(k, a);
    b = gel(ftest,2); _low(l, b); j = k&255;
    for (j1=index[j]; j1 < index[j+1]; j1++)
    {
      j2 = hash[j1];
      if (tabla[j2] == k && tablb[j2] == l)
      {
        p1 = gmul(gpowgs(f,j2),fh);
        if (equalii(gel(p1,1), a) && absi_equal(gel(p1,2), b))
        { /* p1 = ftest or ftest^(-1), we are done */
          if (signe(p1[2]) == signe(b)) com = -com;
          h = addii(addis(h,j2), mulss(s,com));
          gel(forms,0) = f;
          for (i=1; i<lforms; i++)
            gel(forms,i) = sqr_primeform(D, forms[i]);
          h = end_classno(h,hin,forms,lforms);
          h = mulii(h,Hf);
          return gerepileuptoint(av, shifti(h, r2));
        }
      }
    }
    ftest = gmul(ftest,fg);
    if (is_pm1(gel(ftest,1))) pari_err(impl,"classno with too small order");
    if (low_stack(lim, stack_lim(av2,2))) ftest = gerepileupto(av2,ftest);
  }
}

/* use Euler products */
GEN
classno2(GEN x)
{
  pari_sp av = avma;
  const long prec = DEFAULTPREC;
  long n, i, k, r, s;
  GEN p1, p2, S, p4, p5, p7, Hf, Pi, reg, logd, d, dr, D, half;

  check_quaddisc(x, &s, &r, "classno2");
  if (s < 0 && cmpiu(x,12) <= 0) return gen_1;

  Hf = conductor_part(x, r, &D, &reg);
  if (s < 0 && cmpiu(D,12) <= 0) return gerepilecopy(av, Hf); /* |D| < 12*/

  Pi = mppi(prec);
  d = absi(D); dr = itor(d, prec);
  logd = logr_abs(dr);
  p1 = sqrtr(divrr(mulir(d,logd), gmul2n(Pi,1)));
  if (s > 0)
  {
    GEN invlogd = invr(logd);
    p2 = subsr(1, shiftr(mulrr(logr_abs(reg),invlogd),1));
    if (cmprr(sqrr(p2), shiftr(invlogd,1)) >= 0) p1 = mulrr(p2,p1);
  }
  n = itos_or_0( mptrunc(p1) );
  if (!n) pari_err(talker,"discriminant too large in classno");

  p4 = divri(Pi,d);
  p7 = invr(sqrtr_abs(Pi));
  p1 = sqrtr_abs(dr);
  S = gen_0;
  half = real2n(-1, prec);
  if (s > 0)
  {
    for (i=1; i<=n; i++)
    {
      k = krois(D,i); if (!k) continue;
      p2 = mulir(sqru(i), p4);
      p5 = subsr(1, mulrr(p7,incgamc(half,p2,prec)));
      p5 = addrr(divru(mulrr(p1,p5),i), eint1(p2,prec));
      S = (k>0)? addrr(S,p5): subrr(S,p5);
    }
    S = shiftr(divrr(S,reg),-1);
  }
  else
  {
    p1 = gdiv(p1,Pi);
    for (i=1; i<=n; i++)
    {
      k = krois(D,i); if (!k) continue;
      p2 = mulir(sqru(i), p4);
      p5 = subsr(1, mulrr(p7,incgamc(half,p2,prec)));
      p5 = addrr(p5, divrr(divru(p1,i), mpexp(p2)));
      S = (k>0)? addrr(S,p5): subrr(S,p5);
    }
  }
  return gerepileuptoint(av, mulii(Hf, roundr(S)));
}

static GEN
hclassno2(GEN x)
{
  long i, l, s, xmod4;
  GEN Q, H, D, P, E;

  x = negi(x);
  check_quaddisc(x, &s, &xmod4, "hclassno");
  corediscfact(x, xmod4, &D, &P, &E);

  Q = quadclassunit0(D, 0, NULL, 0);
  H = gel(Q,1); l = lg(P);

  /* H \prod_{p^e||f}  (1 + (p^e-1)/(p-1))[ p - (D/p) ] */
  for (i=1; i<l; i++)
  {
    long e = E[i];
    if (e)
    {
      GEN p = gel(P,i), t = subis(p, kronecker(D,p));
      if (e > 1) t = mulii(t, diviiexact(subis(powiu(p,e), 1), subis(p,1)));
      H = mulii(H, addsi(1, t));
    }
  }
  switch( itou_or_0(D) )
  {
    case 3: H = gdivgs(H, 3); break;
    case 4: H = gdivgs(H, 2); break;
  }
  return H;
}

GEN
hclassno(GEN x)
{
  ulong a, b, b2, d, h;
  long s;
  int f;

  if (typ(x) != t_INT) pari_err(typeer,"hclassno");
  s = signe(x);
  if (s < 0) return gen_0;
  if (!s) return gdivgs(gen_1, -12);

  a = mod4(x); if (a == 1 || a == 2) return gen_0;

  d = itou_or_0(x);
  if (!d || d > 500000) return hclassno2(x);

  h = 0; b = d&1; b2 = (1+d)>>2; f=0;
  if (!b)
  {
    for (a=1; a*a<b2; a++)
      if (b2%a == 0) h++;
    f = (a*a==b2); b=2; b2=(4+d)>>2;
  }
  while (b2*3 < d)
  {
    if (b2%b == 0) h++;
    for (a=b+1; a*a < b2; a++)
      if (b2%a == 0) h += 2;
    if (a*a == b2) h++;
    b += 2; b2 = (b*b+d)>>2;
  }
  if (b2*3 == d)
  {
    GEN y = cgetg(3,t_FRAC);
    gel(y,1) = utoipos(3*h+1);
    gel(y,2) = utoipos(3); return y;
  }
  if (f)
  {
    GEN y = cgetg(3,t_FRAC);
    gel(y,1) = utoipos(2*h+1);
    gel(y,2) = gen_2; return y;
  }
  return utoipos(h);
}

