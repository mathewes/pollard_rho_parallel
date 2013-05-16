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
/**                   TRANSCENDENTAL FONCTIONS                     **/
/**                          (part 3)                              **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/***********************************************************************/
/**                                                                   **/
/**                       BESSEL FUNCTIONS                            **/
/**                                                                   **/
/***********************************************************************/

/* n! sum_{k=0}^m Z^k / (k!*(k+n)!), with Z := (-1)^flag*z^2/4 */
static GEN
_jbessel(GEN n, GEN z, long flag, long m)
{
  pari_sp av, lim;
  GEN Z,s;
  long k;

  Z = gmul2n(gsqr(z),-2); if (flag & 1) Z = gneg(Z);
  if (typ(z) == t_SER)
  {
    long v = valp(z);
    k = lg(Z)-2 - v;
    if (v < 0) pari_err(negexper,"jbessel");
    if (v == 0) pari_err(impl,"jbessel around a!=0");
    if (k <= 0) return scalarser(gen_1, varn(z), 2*v);
    setlg(Z, k+2);
  }
  s = gen_1;
  av = avma; lim = stack_lim(av,1);
  for (k=m; k>=1; k--)
  {
    s = gaddsg(1, gdiv(gmul(Z,s), gmulgs(gaddgs(n,k),k)));
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"jbessel");
      s = gerepileupto(av, s);
    }
  }
  return s;
}

/* return L * approximate solution to x log x = B */
static long
bessel_get_lim(double B, double L)
{
  long lim;
  double x = 1 + B; /* 3 iterations are enough except in pathological cases */
  x = (x + B)/(log(x)+1);
  x = (x + B)/(log(x)+1);
  x = (x + B)/(log(x)+1); x = L*x;
  lim = (long)x; if (lim < 2) lim = 2;
  return lim;
}

static GEN
jbesselintern(GEN n, GEN z, long flag, long prec)
{
  long i, lz, ki;
  pari_sp av = avma;
  GEN y;

  switch(typ(z))
  {
    case t_INT: case t_FRAC: case t_QUAD:
    case t_REAL: case t_COMPLEX:
    {
      int flz0 = gequal0(z);
      long lim, k, precnew;
      GEN p1, p2;
      double B, L;

      i = precision(z); if (i) prec = i;
      if (flz0 && gequal0(n)) return real_1(prec);
      p2 = gdiv(gpow(gmul2n(z,-1),n,prec), ggamma(gaddgs(n,1),prec));
      if (flz0) return gerepileupto(av, p2);
      L = 1.3591409 * gtodouble(gabs(gtofp(z,3),prec));
      precnew = prec;
      if (L >= 1.0) precnew += 1 + (long)(L/(1.3591409*LOG2*BITS_IN_LONG));
      if (issmall(n,&ki))
      {
        k = labs(ki);
        n = utoi(k);
      } else {
        i = precision(n);
        if (i && i < precnew) n = gtofp(n,precnew);
      }
      z = gtofp(z,precnew);
      B = bit_accuracy_mul(prec, LOG2/2) / L;
      lim = bessel_get_lim(B, L);
      p1 = gprec_wtrunc(_jbessel(n,z,flag,lim), prec);
      return gerepileupto(av, gmul(p2,p1));
    }

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(z, &lz);
      for (i=1; i<lz; i++)
        gel(y,i) = jbesselintern(n,gel(z,i),flag,prec);
      return y;

    case t_POLMOD:
      y = cleanroots(gel(z,1), prec); lz = lg(y);
      for (i=1; i<lz; i++) {
        GEN t = poleval(gel(z,2), gel(y,i));
        gel(y,i) = jbesselintern(n,t,flag,prec);
      }
      return gerepilecopy(av,y);

    case t_PADIC: pari_err(impl,"p-adic jbessel function");
    default:
      if (!(y = toser_i(z))) break;
      if (issmall(n,&ki)) n = utoi(labs(ki));
      return gerepileupto(av, _jbessel(n,y,flag,lg(y)-2));
  }
  pari_err(typeer,"jbessel");
  return NULL; /* not reached */
}
GEN
jbessel(GEN n, GEN z, long prec) { return jbesselintern(n,z,1,prec); }
GEN
ibessel(GEN n, GEN z, long prec) { return jbesselintern(n,z,0,prec); }

static GEN
_jbesselh(long k, GEN z, long prec)
{
  GEN s,c,p0,p1,p2, zinv = ginv(z);
  long i;

  gsincos(z,&s,&c,prec);
  p1 = gmul(zinv,s);
  if (k)
  {
    p0 = p1; p1 = gmul(zinv,gsub(p0,c));
    for (i=2; i<=k; i++)
    {
      p2 = gsub(gmul(gmulsg(2*i-1,zinv),p1), p0);
      p0 = p1; p1 = p2;
    }
  }
  return p1;
}

GEN
jbesselh(GEN n, GEN z, long prec)
{
  long gz, k, l, linit, i, lz;
  pari_sp av;
  GEN res, y, p1;

  if (typ(n)!=t_INT) pari_err(talker,"not an integer index in jbesselh");
  k = itos(n);
  if (k < 0) return jbessel(gadd(ghalf,n), z, prec);

  switch(typ(z))
  {
    case t_INT: case t_FRAC: case t_QUAD:
    case t_REAL: case t_COMPLEX:
      if (gequal0(z))
      {
        av = avma;
        p1 = gmul(gsqrt(gdiv(z,mppi(prec)),prec),gpowgs(z,k));
        p1 = gdiv(p1, mulu_interval(k+1, 2*k+1)); /* x k! / (2k+1)! */
        return gerepileupto(av, gmul2n(p1,2*k));
      }
      gz = gexpo(z);
      linit = precision(z); if (!linit) linit = prec;
      res = cgetc(linit);
      av = avma;
      if (gz>=0) l = linit;
      else l = linit - 1 + divsBIL(-2*k*gz);
      if (l>prec) prec = l;
      prec += divsBIL(-gz);
      if (prec < 3) prec = 3;
      z = gadd(z, real_0(prec));
      if (typ(z) == t_COMPLEX) gel(z,2) = gadd(gel(z,2), real_0(prec));
      p1 = gmul(_jbesselh(k,z,prec), gsqrt(gdiv(z,Pi2n(-1,prec)),prec));
      avma = av; return affc_fixlg(p1, res);

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(z, &lz);
      for (i=1; i<lz; i++) gel(y,i) = jbesselh(n,gel(z,i),prec);
      return y;

    case t_POLMOD:
      av = avma;
      y = cleanroots(gel(z,1), prec); lz = lg(y);
      for (i=1; i<lz; i++) {
        GEN t = poleval(gel(z,2), gel(y,i));
        gel(y,i) = jbesselh(n,t,prec);
      }
      return gerepilecopy(av, y);

    case t_PADIC: pari_err(impl,"p-adic jbesselh function");
    default:
      av = avma; if (!(y = toser_i(z))) break;
      if (gequal0(y)) return gerepileupto(av, gpowgs(y,k));
      if (valp(y) < 0) pari_err(negexper,"jbesselh");
      y = gprec(y, lg(y)-2 + (2*k+1)*valp(y));
      p1 = gdiv(_jbesselh(k,y,prec),gpowgs(y,k));
      for (i=1; i<=k; i++) p1 = gmulgs(p1,2*i+1);
      return gerepilecopy(av,p1);
  }
  pari_err(typeer,"jbesselh");
  return NULL; /* not reached */
}

static GEN
kbessel2(GEN nu, GEN x, long prec)
{
  pari_sp av = avma;
  GEN p1, x2, a;

  if (typ(x)==t_REAL) prec = lg(x);
  x2 = gshift(x,1);
  a = gtofp(gaddgs(gshift(nu,1), 1), prec);
  p1 = hyperu(gshift(a,-1),a,x2,prec);
  p1 = gmul(gmul(p1,gpow(x2,nu,prec)), sqrtr(mppi(prec)));
  return gerepileupto(av, gmul(p1,gexp(gneg(x),prec)));
}

static GEN
kbessel1(GEN nu, GEN gx, long prec)
{
  GEN x, y, p1, zf, zz, r, s, t, u, ak, pitemp, nu2;
  long l, lnew, k, k2, l1, n2, n, ex;
  pari_sp av;

  if (typ(nu)==t_COMPLEX) return kbessel2(nu,gx,prec);
  l = (typ(gx)==t_REAL)? lg(gx): prec;
  ex = gexpo(gx);
  if (ex < 0)
  {
    long rab = nbits2nlong(-ex);
    lnew = l + rab; prec += rab;
  }
  else lnew = l;
  y = cgetr(l); l1=lnew+1;
  av = avma; x = gtofp(gx, lnew); nu = gtofp(nu, lnew);
  nu2 = gmul2n(sqrr(nu), 2); togglesign(nu2);
  n = (long) (bit_accuracy_mul(l,LOG2) + PI*sqrt(gtodouble(gnorm(nu)))) / 2;
  n2 = n<<1; pitemp=mppi(l1);
  r = gmul2n(x,1);
  if (cmprs(x, n) < 0)
  {
    GEN q = stor(n2, l1), v, c, e, f;
    pari_sp av1, av2;
    u=cgetr(l1); v=cgetr(l1); e=cgetr(l1); f=cgetr(l1);
    av1 = avma;
    zf = sqrtr(divru(pitemp,n2));
    zz = invr(stor(n2<<2, prec));
    s = real_1(prec); t = real_0(prec);
    for (k=n2,k2=2*n2-1; k > 0; k--,k2-=2)
    {
      p1 = addri(nu2, sqrs(k2));
      ak = divrs(mulrr(p1,zz),-k);
      s = addsr(1, mulrr(ak,s));
      t = addsr(k2,mulrr(ak,t));
    }
    mulrrz(zf, s, u); setexpo(t, expo(t)-1);
    divrsz(addrr(mulrr(t,zf),mulrr(u,nu)),-n2,v);
    for(;; avma = av1)
    {
      GEN d = real_1(l1);
      c = divur(5,q); if (expo(c) >= -1) c = real2n(-1,l1);
      p1 = subsr(1,divrr(r,q)); if (cmprr(c,p1)>0) c = p1;
      togglesign(c);
      affrr(u,e);
      affrr(v,f); av2 = avma;
      for (k=1;; k++, avma=av2)
      {
        GEN w = addrr(gmul2n(mulur(2*k-1,u), -1), mulrr(subrs(q,k),v));
        w = addrr(w, mulrr(nu, subrr(u,gmul2n(v,1))));
        divrsz(mulrr(q,v),k,u);
        divrsz(w,k,v);
        mulrrz(d,c,d);
        addrrz(e,mulrr(d,u),e); p1=mulrr(d,v);
        addrrz(f,p1,f);
        if (gexpo(p1) - gexpo(f) <= 1-bit_accuracy(precision(p1))) break;

      }
      swap(e, u);
      swap(f, v);
      affrr(mulrr(q,addrs(c,1)), q);
      if (expo(subrr(q,r)) - expo(r) <= 1-bit_accuracy(lnew)) break;
    }
    u = mulrr(u, gpow(divru(x,n),nu,prec));
  }
  else
  {
    zf = sqrtr(divrr(pitemp,r));
    zz = ginv(gmul2n(r,2)); s = real_1(prec);
    for (k=n2,k2=2*n2-1; k > 0; k--,k2-=2)
    {
      p1 = addri(nu2, sqrs(k2));
      ak = divru(mulrr(p1,zz), k);
      s = subsr(1, mulrr(ak,s));
    }
    u = mulrr(s, zf);
  }
  affrr(mulrr(u, mpexp(mpneg(x))), y);
  avma = av; return y;
}

/*   sum_{k=0}^m Z^k (H(k)+H(k+n)) / (k! (k+n)!)
 * + sum_{k=0}^{n-1} (-Z)^(k-n) (n-k-1)!/k!   with Z := (-1)^flag*z^2/4.
 * Warning: contrary to _jbessel, no n! in front.
 * When flag > 1, compute exactly the H(k) and factorials (slow) */
static GEN
_kbessel1(long n, GEN z, long flag, long m, long prec)
{
  GEN Z, p1, p2, s, H;
  pari_sp av, lim;
  long k;

  Z = gmul2n(gsqr(z),-2); if (flag & 1) Z = gneg(Z);
  if (typ(z) == t_SER)
  {
    long v = valp(z);
    k = lg(Z)-2 - v;
    if (v < 0) pari_err(negexper,"_kbessel1");
    if (v == 0) pari_err(impl,"Bessel K around a!=0");
    if (k <= 0) return gadd(gen_1, zeroser(varn(z), 2*v));
    setlg(Z, k+2);
  }
  H = cgetg(m+n+2,t_VEC); gel(H,1) = gen_0;
  if (flag <= 1)
  {
    gel(H,2) = s = real_1(prec);
    for (k=2; k<=m+n; k++) gel(H,k+1) = s = divru(addsr(1,mulur(k,s)),k);
  }
  else
  {
    gel(H,2) = s = gen_1;
    for (k=2; k<=m+n; k++) gel(H,k+1) = s = gdivgs(gaddsg(1,gmulsg(k,s)),k);
  }
  s = gadd(gel(H,m+1), gel(H,m+n+1));
  av = avma; lim = stack_lim(av,1);
  for (k=m; k>0; k--)
  {
    s = gadd(gadd(gel(H,k),gel(H,k+n)),gdiv(gmul(Z,s),mulss(k,k+n)));
    if (low_stack(lim,stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"_kbessel1");
      s = gerepileupto(av, s);
    }
  }
  p1 = (flag <= 1) ? mpfactr(n,prec) : mpfact(n);
  s = gdiv(s,p1);
  if (n)
  {
    Z = gneg(ginv(Z));
    p2 = gmulsg(n, gdiv(Z,p1));
    s = gadd(s,p2);
    for (k=n-1; k>0; k--)
    {
      p2 = gmul(p2, gmul(mulss(k,n-k),Z));
      s = gadd(s,p2);
    }
  }
  return s;
}

static GEN
kbesselintern(GEN n, GEN z, long flag, long prec)
{
  long i, k, ki, lz, lim, precnew, fl, fl2, ex;
  pari_sp av = avma;
  GEN p1, p2, y, p3, pp, pm, s, c;
  double B, L;

  fl = (flag & 1) == 0;
  switch(typ(z))
  {
    case t_INT: case t_FRAC: case t_QUAD:
    case t_REAL: case t_COMPLEX:
      if (gequal0(z)) pari_err(talker,"zero argument in a k/n bessel function");
      i = precision(z); if (i) prec = i;
      i = precision(n); if (i && prec > i) prec = i;
      ex = gexpo(z);
      /* experimental */
      if (!flag && !gequal0(n) && ex > bit_accuracy(prec)/16 + gexpo(n))
        return kbessel1(n,z,prec);
      L = 1.3591409 * gtodouble(gabs(z,prec));
      precnew = prec;
      if (L >= 1.3591409) {
        long rab = (long)(L/(1.3591409*LOG2*BITS_IN_LONG));
        if (fl) rab *= 2;
         precnew += 1 + rab;
      }
      z = gtofp(z, precnew);
      if (issmall(n,&ki))
      {
        GEN z2 = gmul2n(z, -1);
        k = labs(ki);
        B = bit_accuracy_mul(prec,LOG2/2) / L;
        if (fl) B += 0.367879;
        lim = bessel_get_lim(B, L);
        p1 = gmul(gpowgs(z2,k), _kbessel1(k,z,flag,lim,precnew));
        p2 = gadd(mpeuler(precnew), glog(z2,precnew));
        p3 = jbesselintern(stoi(k),z,flag,precnew);
        p2 = gsub(gmul2n(p1,-1),gmul(p2,p3));
        p2 = gprec_wtrunc(p2, prec);
        if (fl) {
          if (k & 1) p2 = gneg(p2);
        }
        else
        {
          p2 = gdiv(p2, Pi2n(-1,prec));
          if (ki >= 0 || (k&1)==0) p2 = gneg(p2);
        }
        return gerepilecopy(av, p2);
      }

      n = gtofp(n, precnew);
      gsincos(gmul(n,mppi(precnew)), &s,&c,precnew);
      ex = gexpo(s);
      if (ex < 0)
      {
        long rab = nbits2nlong(-ex);
        if (fl) rab *= 2;
        precnew += rab;
      }
      if (i && i < precnew) {
        n = gtofp(n,precnew);
        z = gtofp(z,precnew);
        gsincos(gmul(n,mppi(precnew)), &s,&c,precnew);
      }

      pp = jbesselintern(n,      z,flag,precnew);
      pm = jbesselintern(gneg(n),z,flag,precnew);
      if (fl)
        p1 = gmul(gsub(pm,pp), Pi2n(-1,precnew));
      else
        p1 = gsub(gmul(c,pp),pm);
      p1 = gdiv(p1, s);
      return gerepilecopy(av, gprec_wtrunc(p1,prec));

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(z, &lz);
      for (i=1; i<lz; i++) gel(y,i) = kbesselintern(n,gel(z,i),flag,prec);
      return y;

    case t_POLMOD:
      y = cleanroots(gel(z,1), prec); lz = lg(y);
      for (i=1; i<lz; i++) {
        GEN t = poleval(gel(z,2), gel(y,i));
        gel(y,i) = kbesselintern(n,t,flag,prec);
      }
      return gerepilecopy(av, y);

    case t_PADIC: pari_err(impl,"p-adic Bessel K function");
    default:
      if (!(y = toser_i(z))) break;
      if (issmall(n,&ki))
      {
        k = labs(ki);
        return gerepilecopy(av, _kbessel1(k,y,flag+2,lg(y)-2,prec));
      }
      if (!issmall(gmul2n(n,1),&ki))
        pari_err(talker,"cannot give a power series result in k/n bessel function");
      k = labs(ki); n = gmul2n(stoi(k),-1);
      fl2 = (k&3)==1;
      pm = jbesselintern(gneg(n),y,flag,prec);
      if (fl)
      {
        pp = jbesselintern(n,y,flag,prec);
        p2 = gpowgs(y,-k); if (fl2 == 0) p2 = gneg(p2);
        p3 = gmul2n(diviiexact(mpfact(k + 1),mpfact((k + 1) >> 1)),-(k + 1));
        p3 = gdivgs(gmul2n(gsqr(p3),1),k);
        p2 = gmul(p2,p3);
        p1 = gsub(pp,gmul(p2,pm));
      }
      else p1 = pm;
      return gerepileupto(av, fl2? gneg(p1): gcopy(p1));
  }
  pari_err(typeer,"kbesselintern");
  return NULL; /* not reached */
}

GEN
kbessel(GEN n, GEN z, long prec) { return kbesselintern(n,z,0,prec); }
GEN
nbessel(GEN n, GEN z, long prec) { return kbesselintern(n,z,1,prec); }
/* J + iN */
GEN
hbessel1(GEN n, GEN z, long prec)
{
  pari_sp av = avma;
  return gerepileupto(av, gadd(jbessel(n,z,prec), mulcxI(nbessel(n,z,prec))));
}
/* J - iN */
GEN
hbessel2(GEN n, GEN z, long prec)
{
  pari_sp av = avma;
  return gerepileupto(av, gadd(jbessel(n,z,prec), mulcxmI(nbessel(n,z,prec))));
}

/***********************************************************************/
/*                                                                    **/
/**                    FONCTION U(a,b,z) GENERALE                     **/
/**                         ET CAS PARTICULIERS                       **/
/**                                                                   **/
/***********************************************************************/
/* Assume gx > 0 and a,b complex */
/* This might one day be extended to handle complex gx */
/* see Temme, N. M. "The numerical computation of the confluent        */
/* hypergeometric function U(a,b,z)" in Numer. Math. 41 (1983),        */
/* no. 1, 63--82.                                                      */
GEN
hyperu(GEN a, GEN b, GEN gx, long prec)
{
  GEN S, P, T, x, p1, zf, u, a1, mb = gneg(b);
  const int ex = iscomplex(a) || iscomplex(b);
  long k, n, l = (typ(gx)==t_REAL)? lg(gx): prec, l1 = l+1;
  GEN y = ex? cgetc(l): cgetr(l);
  pari_sp av = avma;

  if(gsigne(gx) <= 0)
    pari_err(talker,"hyperu's third argument must be positive");
  x = gtofp(gx, l);
  a1 = gaddsg(1, gadd(a,mb)); P = gmul(a1, a);
  p1 = gabs(gtofp(P,3), 3);
  n = (long)(bit_accuracy_mul(l, LOG2) + PI*sqrt(gtodouble(p1)));
  S = gadd(a1, a);
  if (cmprs(x,n) < 0)
  {
    GEN q = stor(n, l1), s = gen_1, t = gen_0, v, c, e, f;
    pari_sp av1, av2;

    if (ex) { u=cgetc(l1); v=cgetc(l1); e=cgetc(l1); f=cgetc(l1); }
    else    { u=cgetr(l1); v=cgetr(l1); e=cgetr(l1); f=cgetr(l1); }
    av1 = avma;
    zf = gpow(stoi(n),gneg_i(a),l1);
    T = gadd(gadd(P, gmulsg(n-1, S)), sqrs(n-1));
    for (k=n-1; k>=0; k--)
    {
      /* T = (a+k)*(a1+k) = a*a1 + k(a+a1) + k^2 = previous(T) - S - 2k + 1 */
      p1 = gdiv(T, mulss(-n, k+1));
      s = gaddgs(gmul(p1,s), 1);
      t = gadd(  gmul(p1,t), gaddgs(a,k));
      if (!k) break;
      T = gsubgs(gsub(T, S), 2*k-1);
    }
    gmulz(zf, s, u);
    gmulz(zf, gdivgs(t,-n), v);
    for(;; avma = av1)
    {
      GEN d = real_1(l1), p3 = gadd(q,mb);
      c = divur(5,q); if (expo(c)>= -1) c = real2n(-1, l1);
      p1 = subsr(1,divrr(x,q)); if (cmprr(c,p1)>0) c = p1;
      togglesign(c);
      gaffect(u,e);
      gaffect(v,f); av2 = avma;
      for(k=1;;k++, avma = av2)
      {
        GEN w = gadd(gmul(gaddgs(a,k-1),u), gmul(gaddgs(p3,1-k),v));
        gmulz(divru(q,k),v, u);
        gaffect(gdivgs(w,k), v);
        mulrrz(d,c,d);
        gaddz(e,gmul(d,u),e); p1=gmul(d,v);
        gaddz(f,p1,f);
        if (gequal0(p1) || gexpo(p1) - gexpo(f) <= 1-bit_accuracy(precision(p1)))
          break;
      }
      swap(e, u);
      swap(f, v);
      affrr(mulrr(q, addrs(c,1)), q);
      if (expo(subrr(q,x)) - expo(x) <= 1-bit_accuracy(l)) break;
    }
  }
  else
  {
    GEN zz = invr(x), s = gen_1;
    togglesign(zz); /* -1/x */
    zf = gpow(x,gneg_i(a),l1);
    T = gadd(gadd(P, gmulsg(n-1, S)), sqrs(n-1));
    for (k=n-1; k>=0; k--)
    {
      p1 = gmul(T,divru(zz,k+1));
      s = gaddsg(1, gmul(p1,s));
      if (!k) break;
      T = gsubgs(gsub(T, S), 2*k-1);
    }
    u = gmul(s,zf);
  }
  gaffect(u,y); avma = av; return y;
}

/* = incgam2(0, x, prec). typ(x) = t_REAL. Optimized for eint1 */
static GEN
incgam2_0(GEN x, GEN expx)
{
  long l = lg(x), n, i;
  GEN z;

  if (expo(x) >= 4)
  {
    double mx = rtodbl(x), m = (bit_accuracy_mul(l,LOG2) + mx)/4;
    n = (long)(1+m*m/mx);
    z = divsr(-n, addsr(n<<1,x));
    for (i=n-1; i >= 1; i--)
      z = divsr(-i, addrr(addsr(i<<1,x), mulur(i,z))); /* -1 / (2 + z + x/i) */
    return divrr(addrr(real_1(l),z), mulrr(expx, x));
  }
  else
  {
    GEN S, t, H, run = real_1(l+1);
    n = -bit_accuracy(l)-1;
    x = rtor(x, l+1);
    S = z = t = H = run;
    for (i = 2; expo(t) - expo(S) >= n; i++)
    {
      H = addrr(H, divru(run,i)); /* H = sum_{k<=i} 1/k */
      z = divru(mulrr(x,z), i);   /* z = x^(i-1)/i! */
      t = mulrr(z, H); S = addrr(S, t);
    }
    return subrr(mulrr(x, divrr(S,expx)), addrr(mplog(x), mpeuler(l)));
  }
}

/* assume x != 0 */
static GEN
incgam2(GEN s, GEN x, long prec)
{
  GEN b, x_s, S, y;
  long l, n, i;
  pari_sp av = avma, av2, avlim;
  double m,mx;

  if (typ(x) != t_REAL) x = gtofp(x, prec);
  if (gequal0(s) && typ(x) == t_REAL && signe(x) > 0)
    return gerepileuptoleaf(av, incgam2_0(x, mpexp(x)));
  if (typ(x) == t_COMPLEX)
  {
    double a = rtodbl(gel(x,1));
    double b = rtodbl(gel(x,2));
    l = precision(x);
    mx = sqrt(a*a + b*b);
  }
  else
  {
    l = lg(x);
    mx = fabs(rtodbl(x));
  }
  m = (bit_accuracy_mul(l,LOG2) + mx)/4;
  n = (long)(1+m*m/mx);
  i = typ(s);
  if (i == t_REAL) b = addsr(-1,s);
  else
  { /* keep b integral : final powering more efficient */
    GEN z = gtofp(s, prec);
    b = (i == t_INT)? addsi(-1,s): gaddsg(-1,z);
    s = z;
  }
  y = gmul(gexp(gneg(x), prec), gpow(x,b,prec));
  x_s = gsub(x, s);
  av2 = avma; avlim = stack_lim(av2,3);
  S = gdiv(gaddsg(-n,s), gaddgs(x_s,n<<1));
  for (i=n-1; i>=1; i--)
  {
    S = gdiv(gaddsg(-i,s), gadd(gaddgs(x_s,i<<1),gmulsg(i,S)));
    if (low_stack(avlim,stack_lim(av2,3)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"incgam2");
      S = gerepileupto(av2, S);
    }
  }
  return gerepileupto(av, gmul(y, gaddsg(1,S)));
}

/* use exp(-x) * (x^s/s) * sum_{k >= 0} x^k / prod(i=1,k, s+i) */
GEN
incgamc(GEN s, GEN x, long prec)
{
  GEN b, S, t, y;
  long l, n, i;
  pari_sp av = avma, av2, avlim;

  if (typ(x) != t_REAL) x = gtofp(x, prec);
  if (gequal0(x)) return gcopy(x);

  l = precision(x); n = -bit_accuracy(l)-1;
  i = typ(s); b = s;
  if (i != t_REAL)
  {
    s = gtofp(s, prec);
    if (i != t_INT) b = s;
  }
  av2 = avma; avlim = stack_lim(av2,3);
  S = t = real_1(l);
  for (i=1; gexpo(S) >= n; i++)
  {
    S = gdiv(gmul(x,S), gaddsg(i,s)); /* x^i / ((s+1)...(s+i)) */
    t = gadd(S,t);
    if (low_stack(avlim,stack_lim(av2,3)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"incgamc");
      gerepileall(av2, 2, &S, &t);
    }
  }
  y = gdiv(gmul(gexp(gneg(x),prec), gpow(x,b,prec)), s);
  return gerepileupto(av, gmul(y,t));
}

/* If g != NULL, assume that g=gamma(s,prec). */
GEN
incgam0(GEN s, GEN x, GEN g, long prec)
{
  pari_sp av;
  long es, e;
  GEN z;

  if (gequal0(x)) return g? gcopy(g): ggamma(s,prec);
  av = avma;
  es = gexpo(s); e = maxss(es, 0);
  if (gsigne(real_i(s)) <= 0 || gexpo(x) > e)
    z = incgam2(s,x,prec);
  else
  {
    if (es < 0) {
      long l = precision(s);
      if (!l) l = prec;
      prec = l + nbits2nlong(-es) + 1;
      s = gtofp(s, prec);
      x = gtofp(x, prec);
    }
    if (!g) g = ggamma(s,prec);
    z = gsub(g, incgamc(s,x,prec));
  }
  return gerepileupto(av, z);
}

GEN
incgam(GEN s, GEN x, long prec) { return incgam0(s, x, NULL, prec); }

/* x >= 0 a t_REAL */
GEN
mpeint1(GEN x, GEN expx)
{
  pari_sp av = avma;
  return gerepileuptoleaf(av, incgam2_0(x, expx));
}

GEN
eint1(GEN x, long prec)
{
  long l, n, i;
  pari_sp av = avma;
  GEN p1, t, S, y;

  if (typ(x) != t_REAL) {
    x = gtofp(x, prec);
    if (typ(x) != t_REAL) pari_err(impl,"non-real argument in eint1");
  }
  if (signe(x) >= 0) return gerepileuptoleaf(av, incgam2_0(x, mpexp(x)));
  /* rewritten from code contributed by Manfred Radimersky */
  l  = lg(x);
  n  = bit_accuracy(l);
  y  = negr(x);
  if (cmprs(y, (3*n)/4) < 0) {
    p1 = t = S = y;
    for (i = 2; expo(t) - expo(S) >= -n; i++) {
      p1 = mulrr(y, divru(p1, i));
      t = divru(p1, i); S = addrr(S, t);
    }
    y  = addrr(S, addrr(mplog(y), mpeuler(l)));
  } else {
    p1 = invr(y);
    t = S = real_1(l);
    for (i = 1; expo(t) - expo(S) >= -n; i++) {
      t = mulrr(p1, mulru(t, i)); S = addrr(S, t);
    }
    y  = mulrr(S, mulrr(p1, mpexp(y)));
  }
  return gerepileuptoleaf(av, negr(y));
}

GEN
veceint1(GEN C, GEN nmax, long prec)
{
  if (!nmax) return eint1(C,prec);
  if (typ(nmax) != t_INT) pari_err(typeer,"veceint1");
  if (typ(C) != t_REAL) {
    C = gtofp(C, prec);
    if (typ(C) != t_REAL) pari_err(typeer,"veceint1");
  }
  if (signe(C) <= 0) pari_err(talker,"negative or zero constant in veceint1");
  return mpveceint1(C, NULL, itos(nmax));
}

/* C > 0 a t_REAL */
GEN
mpveceint1(GEN C, GEN eC, long n)
{
  long i, nstop, nmin, G, chkpoint, prec = lg(C);
  pari_sp av, av1;
  GEN y, e1, e2, F0, unr;

  if (n <= 0) return cgetg(1,t_VEC);
  y = cgetg(n+1,t_VEC);
  for(i=1; i<=n; i++) gel(y,i) = cgetr(prec);
  av = avma; G = expo(C);
  if (G >= 0) nstop = n;
  else
  {
    nstop = itos(ceilr(divur(4,C))); /* >= 4 ~ 4 / C */
    if (nstop > n) nstop = n;
  }
  /* 1 <= nstop <= n */

  if (!eC) eC = mpexp(C);
  if (DEBUGLEVEL>1) err_printf("veceint1: (n, nstop) = (%ld, %ld)\n",n, nstop);
  e1 = rcopy(eC); av1 = avma;
  affrr(incgam2_0(C, e1), gel(y,1));
  for(i=2; i <= nstop; i++, avma = av1)
  {
    affrr(mulrr(e1, eC), e1); /* e1 = exp(iC) */
    affrr(incgam2_0(mulur(i,C), e1), gel(y,i));
  }
  if (nstop == n) { avma = av; return y; }

  e1 = powrs(eC, -n);
  e2 = powru(eC, 10);
  unr = real_1(prec);
  av1 = avma;
  G = -bit_accuracy(prec);
  F0 = gel(y,n); chkpoint = n;
  affrr(eint1(mulur(n,C),prec), F0);
  nmin = n;
  for(;;)
  {
    GEN minvn = divrs(unr,-n), My = subrr(minvn,C);
    GEN mcn   = divrs(C,  -n), Mx = mcn;
    GEN t = divrs(e1,-n), D = mkvec2( t, mulrr(My,t) );
    long a, k, cD = 2; /* cD = #D */

    /* D = [ e1/-n, (-1/n-C) * (e1/-n) ] */
    nmin -= 10; if (nmin < nstop) nmin = nstop;
    My = addrr(My, minvn);
    if (DEBUGLEVEL>1 && n < chkpoint)
      { err_printf("%ld ",n) ; chkpoint -= nstop/20; }
    for (a=1,n--; n>=nmin; n--,a++)
    {
      GEN F = F0, den = stor(-a, prec);
      for (k=1;;)
      {
        GEN add;
        if (k > cD)
        {
          GEN z = addrr(mulrr(My, gel(D,cD)), mulrr(Mx,gel(D,cD-1)));
          Mx = addrr(Mx,mcn);
          My = addrr(My,minvn);
          D = shallowconcat(D, z); cD = k;
          /* My = -C - k/n,  Mx = -C k/n */
        }
        add = mulrr(den, gel(D,k));
        if (expo(add) < G) { affrr(F,gel(y,n)); break; }
        F = addrr(F,add); k++;
        den = mulrs(divru(den, k), -a);
        /* den = prod(i=1,k, -a/i)*/
      }
    }
    avma = av1; F0 = gel(y, ++n);
    if (n <= nstop) break;
    affrr(mulrr(e1,e2), e1);
  }
  if (DEBUGLEVEL>1) err_printf("\n");
  avma = av; return y;
}

/* e t_REAL, vector of e^i, 1 <= i <= n */
GEN
mpvecpow(GEN e, long n)
{
  GEN G = cgetg(n+1, t_VEC);
  long j;
  gel(G, 1) = e;
  for (j = 2; j <= n; j++) gel(G,j) = mulrr(gel(G,j-1), e);
  return G;
}

/* erfc via numerical integration : assume real(x)>=1 */
static GEN
cxerfc_r1(GEN x, long prec)
{
  GEN h, h2, eh2, denom, res, lambda;
  long u, v;
  const double D = bit_accuracy_mul(prec, LOG2);
  const long npoints = (long)ceil(D/PI)+1;
  pari_sp av = avma;
  {
    double t = exp(-2*PI*PI/D); /* ~exp(-2*h^2) */
    v = 30; /* bits that fit in both long and double mantissa */
    u = (long)floor(t*(1L<<v));
    /* define exp(-2*h^2) to be u*2^(-v) */
  }
  prec++;
  x = gtofp(x,prec);
  eh2 = sqrtr_abs(rtor(shiftr(dbltor(u),-v),prec));
  h2 = negr(logr_abs(eh2));
  h = sqrtr_abs(h2);
  lambda = gdiv(x,h);
  denom = gsqr(lambda);
  { /* res = h/x + 2*x*h*sum(k=1,npoints,exp(-(k*h)^2)/(lambda^2+k^2)); */
    GEN Uk; /* = exp(-(kh)^2) */
    GEN Vk = eh2;/* = exp(-(2k+1)h^2) */
    pari_sp av2 = avma;
    long k;
    /* k = 0 moved out for efficiency */
    denom = gaddsg(1,denom);
    Uk = Vk;
    Vk = mulur(u,Vk); setexpo(Vk, expo(Vk)-v);
    res = gdiv(Uk, denom);
    for (k = 1; k < npoints; k++)
    {
      if ((k & 255) == 0) gerepileall(av2,4,&denom,&Uk,&Vk,&res);
      denom = gaddsg(2*k+1,denom);
      Uk = mpmul(Uk,Vk);
      Vk = mulur(u,Vk); setexpo(Vk, expo(Vk)-v);
      res = gadd(res, gdiv(Uk, denom));
    }
  }
  res = gmul(res, gshift(lambda,1));
  /* 0 term : */
  res = gadd(res, ginv(lambda));
  res = gmul(res, gdiv(gexp(gneg(gsqr(x)), prec), mppi(prec)));
  if (rtodbl(real_i(x)) < sqrt(D))
  {
    GEN t = gmul(divrr(Pi2n(1,prec),h), x);
    if (typ(x) == t_REAL)
      t = mpexp1(t); /* stabler */
    else
      t = gsubgs(gexp(t, prec), 1);
    res = gsub(res, gdivsg(2, t));
  }
  return gerepileupto(av,res);
}

GEN
gerfc(GEN x, long prec)
{
  GEN z, xr, res;
  pari_sp av;

  x = trans_fix_arg(&prec,&x,&xr,&av,&res);
  if (signe(xr) >= 0) {
    if (cmprs(xr, 1) > 0) /* use numerical integration */
      z = cxerfc_r1(x, prec);
    else
    { /* erfc(x) = incgam(1/2,x^2)/sqrt(Pi) */
      GEN sqrtpi = sqrtr(mppi(prec));
      z = incgam0(ghalf, gsqr(x), sqrtpi, prec);
      z = gdiv(z, sqrtpi);
    }
  }
  else
  { /* erfc(-x)=2-erfc(x) */
    /* FIXME could decrease prec
    long size = ceil((pow(rtodbl(gimag(x)),2)-pow(rtodbl(greal(x)),2))/(LOG2*BITS_IN_LONG));
    prec = size > 0 ? prec : prec + size;
    */
    /* NOT gsubsg(2, ...) : would create a result of
     * huge accuracy if re(x)>>1, rounded to 2 by subsequent affc_fixlg... */
    z = gsub(real2n(1,prec+1), gerfc(gneg(x), prec));
  }
  avma = av; return affc_fixlg(z, res);
}

/***********************************************************************/
/**                                                                   **/
/**                     FONCTION ZETA DE RIEMANN                      **/
/**                                                                   **/
/***********************************************************************/
static const double log2PI = 1.83787706641;

static double
get_xinf(double beta)
{
  const double maxbeta = 0.06415003; /* 3^(-2.5) */
  double x0, y0, x1;

  if (beta < maxbeta) return beta + pow(3*beta, 1.0/3.0);
  x0 = beta + PI/2.0;
  for(;;)
  {
    y0 = x0*x0;
    x1 = (beta+atan(x0)) * (1+y0) / y0 - 1/x0;
    if (0.99*x0 < x1) return x1;
    x0 = x1;
  }
}
/* optimize for zeta( s + it, prec ) */
static void
optim_zeta(GEN S, long prec, long *pp, long *pn)
{
  double s, t, alpha, beta, n, B;
  long p;
  if (typ(S) == t_REAL) {
    s = rtodbl(S);
    t = 0.;
  } else {
    s = rtodbl(gel(S,1));
    t = fabs( rtodbl(gel(S,2)) );
  }

  B = bit_accuracy_mul(prec, LOG2);
  if (s <= 0) /* may occur if S ~ 0, and we don't use the func. eq. */
  { /* TODO: the crude bounds below are generally valid. Optimize ? */
    double l,l2, la = 1.; /* heuristic */
    if (dnorm(s-1,t) < 0.1) /* |S - 1|^2 < 0.1 */
      l2 = -(s - 0.5);
    else
    {
      double rlog, ilog; dcxlog(s-1,t, &rlog,&ilog);
      l2 = (s - 0.5)*rlog - t*ilog; /* = Re( (S - 1/2) log (S-1) ) */
    }
    l = (B - l2 + s*log2PI) / (2. * (1.+ log((double)la)));
    l2 = dabs(s, t)/2;
    if (l < l2) l = l2;
    p = (long) ceil(l); if (p < 2) p = 2;
    l2 = (p + s/2. - .25);
    n = 1 + dabs(l2, t/2) * la / PI;
  }
  else if (t != 0)
  {
    double sn = dabs(s, t), L = log(sn/s);
    alpha = B - 0.39 + L + s*(log2PI - log(sn));
    beta = (alpha+s)/t - atan(s/t);
    if (beta <= 0)
    {
      if (s >= 1.0)
      {
        p = 0;
        n = exp((B - LOG2 + L) / s);
      }
      else
      {
        p = 1;
        n = dabs(s + 1, t) / (2*PI);
      }
    }
    else
    {
      beta = 1.0 - s + t * get_xinf(beta);
      if (beta > 0)
      {
        p = (long)ceil(beta / 2.0);
        n = dabs(s + 2*p-1, t) / (2*PI);
      }
      else
      {
        p = 0;
        n = exp((B - LOG2 + L) / s);
      }
    }
  }
  else
  {
    double sn = fabs(s);
    beta = B + 0.61 + s*(log2PI - log(s));
    if (beta > 0)
    {
      p = (long)ceil(beta / 2.0);
      n = fabs(s + 2*p-1)/(2*PI);
    }
    else
    {
      p = 0;
      n = exp((B - LOG2 + log(sn/s)) / s);
    }
  }
  *pp = p;
  *pn = (long)ceil(n);
  if (DEBUGLEVEL) err_printf("lim, nn: [%ld, %ld]\n", *pp, *pn);
}

/* 1/zeta(n) using Euler product. Assume n > 0.
 * if (lba != 0) it is log(bit_accuracy) we _really_ require */
GEN
inv_szeta_euler(long n, double lba, long prec)
{
  GEN z, res = cgetr(prec);
  pari_sp av = avma, avlim = stack_lim(av, 1);
  byteptr d =  diffptr + 2;
  double A = n / (LOG2*BITS_IN_LONG), D;
  ulong p, lim;

  if (n > bit_accuracy(prec)) return real_1(prec);
  if (!lba) lba = bit_accuracy_mul(prec, LOG2);
  D = exp((lba - log(n-1)) / (n-1));
  lim = 1 + (ulong)ceil(D);
  maxprime_check(lim);

  prec++;
  z = subir(gen_1, real2n(-n, prec));
  for (p = 3; p <= lim;)
  {
    long l = prec + 1 - (long)floor(A * log(p));
    GEN h;

    if (l < 3)         l = 3;
    else if (l > prec) l = prec;
    h = divrr(z, rpowuu(p, (ulong)n, l));
    z = subrr(z, h);
    if (low_stack(avlim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"inv_szeta_euler, p = %lu/%lu", p,lim);
      affrr(z, res); avma = av;
    }
    NEXT_PRIME_VIADIFF(p,d);
  }
  affrr(z, res); avma = av; return res;
}

/* assume n even > 0, if iz != NULL, assume iz = 1/zeta(n) */
GEN
bernreal_using_zeta(long n, GEN iz, long prec)
{
  long l = prec + 1;
  GEN z;

  if (!iz) iz = inv_szeta_euler(n, 0., l);
  z = divrr(mpfactr(n, l), mulrr(powru(Pi2n(1, l), n), iz));
  setexpo(z, expo(z) + 1); /* 2 * n! * zeta(n) / (2Pi)^n */
  if ((n & 3) == 0) setsigne(z, -1);
  return z;
}

/* assume n even > 0. Faster than standard bernfrac for n >= 6 */
GEN
bernfrac_using_zeta(long n)
{
  pari_sp av = avma;
  GEN iz, a, d, D = divisors(utoipos( n/2 ));
  long i, prec, l = lg(D);
  double t, u;

  d = utoipos(6); /* 2 * 3 */
  for (i = 2; i < l; i++) /* skip 1 */
  { /* Clausen - von Staudt */
    ulong p = 2*itou(gel(D,i)) + 1;
    if (uisprime(p)) d = muliu(d, p);
  }
  /* 1.712086 = ??? */
  t = log( gtodouble(d) ) + (n + 0.5) * log(n) - n*(1+log2PI) + 1.712086;
  u = t / (LOG2*BITS_IN_LONG); prec = (long)ceil(u);
  prec += 3;
  iz = inv_szeta_euler(n, t, prec);
  a = roundr( mulir(d, bernreal_using_zeta(n, iz, prec)) );
  return gerepilecopy(av, mkfrac(a, d));
}

/* y = binomial(n,k-2). Return binomial(n,k) */
static GEN
next_bin(GEN y, long n, long k)
{
  y = divru(mulru(y, n-k+2), k-1);
  return divru(mulru(y, n-k+1), k);
}

/* assume k > 1 odd */
static GEN
szeta_odd(long k, long prec)
{
  long kk, n, li = -(1+bit_accuracy(prec));
  pari_sp av = avma, av2, limit;
  GEN y, p1, qn, z, q, pi2 = Pi2n(1, prec), binom= real_1(prec+1);

  q = mpexp(pi2); kk = k+1; /* >= 4 */
  y = NULL; /* gcc -Wall */
  if ((k&3)==3)
  {
    for (n=0; n <= kk>>1; n+=2)
    {
      p1 = mulrr(bernreal(kk-n,prec),bernreal(n,prec));
      if (n) { binom = next_bin(binom,kk,n); setlg(binom,prec+1); }
      p1 = mulrr(binom,p1);
      if (n == kk>>1) setexpo(p1, expo(p1)-1);
      if ((n>>1)&1) togglesign(p1);
      y = n? addrr(y,p1): p1;
    }
    y = mulrr(divrr(powru(pi2,k),mpfactr(kk,prec)),y);

    av2 = avma; limit = stack_lim(av2,1);
    qn = sqrr(q); z = invr( addrs(q,-1) );
    for (n=2; ; n++)
    {
      long ep1, l;
      p1 = invr( mulir(powuu(n,k),addrs(qn,-1)) );

      z = addrr(z,p1); if ((ep1 = expo(p1)) < li) break;
      l = (ep1 < 0) ? prec+1 : prec+1 + nbits2nlong(ep1);
      if (l < lg(qn)) setlg(qn, l);
      qn = mulrr(qn,q);
      if (low_stack(limit,stack_lim(av2,1)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"szeta, delta = %ld", expo(p1)-li);
        gerepileall(av2,2, &z, &qn);
      }
    }
    setexpo(z, expo(z)+1);
    y = addrr(y,z); togglesign(y);
  }
  else
  {
    GEN p2 = divru(pi2, k-1);
    for (n=0; n <= k>>1; n+=2)
    {
      p1 = mulrr(bernreal(kk-n,prec),bernreal(n,prec));
      if (n) binom = next_bin(binom,kk,n);
      p1 = mulrr(binom,p1);
      p1 = mulur(kk-(n<<1),p1);
      if ((n>>1)&1) togglesign(p1);
      y = n? addrr(y,p1): p1;
    }
    y = mulrr(divrr(powru(pi2,k),mpfactr(kk,prec)),y);
    y = divru(y,k-1);
    av2 = avma; limit = stack_lim(av2,1);
    qn = q; z=gen_0;
    for (n=1; ; n++)
    {
      long ep1, l;
      p1 = mulir(powuu(n,k),sqrr(addrs(qn,-1)));
      p1 = divrr(addrs(mulrr(qn,addsr(1,mulur(n<<1,p2))),-1),p1);

      z = addrr(z,p1); if ((ep1 = expo(p1)) < li) break;
      l = (ep1 < 0)? prec+1 : prec+1 + nbits2nlong(ep1);
      if (l < lg(qn)) setlg(qn, l);
      qn = mulrr(qn,q);
      if (low_stack(limit,stack_lim(av2,1)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"szeta, delta = %ld", ep1-li);
        gerepileall(av2,2, &z, &qn);
      }
    }
    setexpo(z, expo(z)+1);
    y = subrr(y,z);
  }
  return gerepileuptoleaf(av, y);
}

/* assume k > 0 even. Return B_k */
static GEN
single_bern(long k, long prec)
{
  GEN B;
  if (OK_bern(k >> 1, prec)) B = bernreal(k, prec);
  else if (k * (log(k) - 2.83) > bit_accuracy_mul(prec, LOG2))
    B = bernreal_using_zeta(k, NULL, prec);
  else
    B = fractor(bernfrac(k), prec);
  return B;
}

/* assume k != 1 */
GEN
szeta(long k, long prec)
{
  pari_sp av = avma;
  GEN y;

  /* treat trivial cases */
  if (!k) { y = real2n(-1, prec); setsigne(y,-1); return y; }
  if (k < 0)
  {
    if ((k&1) == 0) return gen_0;
    /* the one value such that k < 0 and 1 - k < 0, due to overflow */
    if ((ulong)k == (HIGHBIT | 1))
      pari_err(talker, "too large negative arg %ld in zeta", k);
    k = 1-k;
    y = single_bern(k, prec); togglesign(y);
    return gerepileuptoleaf(av, divru(y, k));
  }
  if (k > bit_accuracy(prec)+1) return real_1(prec);
  if ((k&1) == 0)
  {
    if (!OK_bern(k >> 1, prec)
        && (k * (log(k) - 2.83) > bit_accuracy_mul(prec, LOG2)))
      y = invr( inv_szeta_euler(k, 0, prec) ); /* would use zeta above */
    else
    {
      y = mulrr(powru(Pi2n(1, prec), k), single_bern(k, prec));
      y = divrr(y, mpfactr(k,prec));
      y[1] = evalsigne(1) | evalexpo(expo(y)-1);
    }
    return gerepileuptoleaf(av, y);
  }
  /* k > 1 odd */
  if (k * log(k) > bit_accuracy_mul(prec, LOG2)) /* heuristic */
    return gerepileuptoleaf(av, invr( inv_szeta_euler(k, 0, prec) ));
  return szeta_odd(k, prec);
}

/* return x^n, assume n > 0 */
static long
pows(long x, long n)
{
  long i, y = x;
  for (i=1; i<n; i++) y *= x;
  return y;
}

/* return n^-s, n > 1 odd. tab[q] := q^-s, q prime power */
static GEN
n_s(ulong n, GEN *tab)
{
  byteptr d =  diffptr + 2;
  GEN x = NULL;
  long p, e;

  for (p = 3; n > 1; )
  {
    e = u_lvalrem(n, p, &n);
    if (e)
    {
      GEN y = tab[pows(p,e)];
      if (!x) x = y; else x = gmul(x,y);
    }
    NEXT_PRIME_VIADIFF_CHECK(p,d);
  }
  return x;
}

/* s0 a t_INT, t_REAL or t_COMPLEX.
 * If a t_INT, assume it's not a trivial case (i.e we have s0 > 1, odd)
 * */
GEN
czeta(GEN s0, long prec)
{
  GEN s, u, a, y, res, tes, sig, invn2, unr;
  GEN sim, *tab, tabn, funeq_factor = NULL;
  ulong p, sqn;
  long i, nn, lim, lim2, ct;
  pari_sp av0 = avma, av, av2, avlim;
  byteptr d;
  pari_timer T;

  if (DEBUGLEVEL>2) timer_start(&T);
  s = trans_fix_arg(&prec,&s0,&sig,&av,&res);
  if (typ(s0) == t_INT) return gerepileupto(av, gzeta(s0, prec));
  u = gsubgs(s, 1); /* temp */
  if (gexpo(u) < -5 || (gexpo(s) > -5 && (signe(sig) <= 0 || expo(sig) < -1)))
  { /* s <--> 1-s */
    GEN t;
    s = gneg(u); sig = real_i(s);
    /* Gamma(s) (2Pi)^-s 2 cos(Pi s/2) */
    t = gmul(ggamma(gprec_w(s,prec),prec), gpow(Pi2n(1,prec), gneg(s), prec));
    funeq_factor = gmul2n(gmul(t, gcos(gmul(Pi2n(-1,prec),s), prec)), 1);
  }
  if (gcmpgs(sig, bit_accuracy(prec) + 1) > 0) { /* zeta(s) = 1 */
    if (!funeq_factor) { avma = av0; return real_1(prec); }
    return gerepileupto(av0, funeq_factor);
  }
  optim_zeta(s, prec, &lim, &nn);
  maxprime_check((ulong)nn);
  prec++; unr = real_1(prec); /* one extra word of precision */

  tab = (GEN*)cgetg(nn, t_VEC); /* table of q^(-s), q = p^e */
  { /* general case */
    GEN ms = gneg(s), rp = cgetr(prec);
    d = diffptr + 1;
    for (p=2; p < (ulong)nn;)
    {
      affur(p, rp);
      tab[p] = gexp(gmul(ms, mplog(rp)), prec);
      NEXT_PRIME_VIADIFF(p,d);
    }
    affsr(nn, rp);
    a = gexp(gmul(ms, mplog(rp)), prec);
  }
  sqn = (ulong)sqrt(nn-1.);
  d = diffptr + 2; /* fill in odd prime powers */
  for (p=3; p <= sqn; )
  {
    ulong oldq = p, q = p*p;
    while (q<(ulong)nn) { tab[q] = gmul(tab[p], tab[oldq]); oldq = q; q *= p; }
    NEXT_PRIME_VIADIFF(p,d);
  }
  if (DEBUGLEVEL>2) timer_printf(&T,"tab[q^-s] from 1 to N-1");

  tabn = cgetg(nn, t_VECSMALL); ct = 0;
  for (i = nn-1; i; i>>=1) tabn[++ct] = (i-1)>>1;
  sim = y = unr;
  /* compute 1 + 2^-s + ... + n^-s = P(2^-s) using Horner's scheme */
  for (i=ct; i > 1; i--)
  {
    long j;
    av2 = avma;
    for (j=tabn[i]+1; j<=tabn[i-1]; j++)
      sim = gadd(sim, n_s(2*j+1, tab));
    sim = gerepileupto(av2, sim);
    y = gadd(sim, gmul(tab[2],y));
  }
  y = gadd(y, gmul2n(a,-1));
  if (DEBUGLEVEL>2) timer_printf(&T,"sum from 1 to N-1");

  invn2 = divri(unr, mulss(nn,nn)); lim2 = lim<<1;
  tes = bernreal(lim2, prec);
  {
    GEN s1, s2, s3, s4, s5;
    s1 = gsub(gmul2n(s,1), unr);
    s2 = gmul(s, gsub(s,unr));
    s3 = gmul2n(invn2,3);
    av2 = avma; avlim = stack_lim(av2,3);
    s4 = gmul(invn2, gmul2n(gaddsg(4*lim-2,s1),1));
    s5 = gmul(invn2, gadd(s2, gmulsg(lim2, gaddgs(s1, lim2))));
    for (i = lim2-2; i>=2; i -= 2)
    {
      s5 = gsub(s5, s4);
      s4 = gsub(s4, s3);
      tes = gadd(bernreal(i,prec), divgunu(gmul(s5,tes), i+1));
      if (low_stack(avlim,stack_lim(av2,3)))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"czeta");
        gerepileall(av2,3, &tes,&s5,&s4);
      }
    }
    u = gmul(gmul(tes,invn2), gmul2n(s2, -1));
    tes = gmulsg(nn, gaddsg(1, u));
  }
  if (DEBUGLEVEL>2) timer_printf(&T,"Bernoulli sum");
  /* y += tes n^(-s) / (s-1) */
  y = gadd(y, gmul(tes, gdiv(a, gsub(s, unr))));
  if (funeq_factor) y = gmul(y, funeq_factor);
  avma = av; return affc_fixlg(y,res);
}

/* return P mod x^n where P is polynomial in x */
static GEN
pol_mod_xn(GEN P, long n)
{
  long j, l = lg(P), N = n+2;
  GEN R;
  if (l > N) l = N;
  R = cgetg(N, t_POL); R[1] = evalvarn(0);
  for (j = 2; j < l; j++) gel(R,j) = gel(P,j);
  return normalizepol_lg(R, n+2);
}

/* compute the values of the twisted partial
   zeta function Z_f(a, c, s) for a in va */
GEN
twistpartialzeta(GEN q, long f, long c, GEN va, GEN cff)
{
  long j, k, lva = lg(va)-1, N = lg(cff)-1;
  pari_sp av, av2, lim;
  GEN Ax, Cx, Bx, Dx, x = pol_x(0), y = pol_x(fetch_user_var("y"));
  GEN cyc, psm, rep, eta, etaf;

  cyc = gdiv(gsubgs(gpowgs(y, c), 1), gsubgs(y, 1));
  psm = polsym(cyc, degpol(cyc) - 1);
  eta = mkpolmod(y, cyc);
  etaf = gpowgs(eta,f);
  av = avma;
  Ax  = gsubgs(gpowgs(gaddgs(x, 1), f), 1);
  Ax  = gdiv(gmul(Ax, etaf), gsubsg(1, etaf));
  Ax  = gerepileupto(av, RgX_to_FqX(Ax, cyc, q));
  Cx  = Ax;
  Bx  = gen_1;
  av  = avma; lim = stack_lim(av, 1);
  for (j = 2; j <= N; j++)
  {
    Bx = gadd(Bx, Cx);
    Bx = FpXQX_red(Bx, cyc, q);
    Cx = FpXQX_mul(Cx, Ax, cyc, q);
    Cx = pol_mod_xn(Cx, N);
    if (gequal0(Cx)) break;
    if (low_stack(lim, stack_lim(av, 1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem, "twistpartialzeta (1), j = %ld/%ld", j, N);
      gerepileall(av, 2, &Cx, &Bx);
    }
  }
  Bx  = lift(gmul(ginv(gsubsg(1, etaf)), Bx));
  Bx  = gerepileupto(av, RgX_to_FqX(Bx, cyc, q));
  Cx = lift(gmul(eta, gaddsg(1, x)));
  Dx = pol_1(varn(x));
  av2 = avma; lim = stack_lim(av2, 1);
  for (j = lva; j > 1; j--)
  {
    GEN Ex;
    long e = va[j] - va[j-1];
    if (e == 1)
      Ex = Cx;
    else
      /* e is very small in general and actually very rarely different
         to 1, it is always 1 for zetap (so it should be OK not to store
         them or to compute them in a smart way) */
      Ex = gpowgs(Cx, e);
    Dx = gaddsg(1, FpXQX_mul(Dx, Ex, cyc, q));
    if (low_stack(lim, stack_lim(av2, 1)))
    {
      if(DEBUGMEM>1)
        pari_warn(warnmem, "twistpartialzeta (2), j = %ld/%ld", lva-j, lva);
      Dx = gerepileupto(av2, FpXQX_red(Dx, cyc, q));
    }
  }
  Dx = FpXQX_mul(Dx, Cx, cyc, q); /* va[1] = 1 */
  Bx = gerepileupto(av, FpXQX_mul(Dx, Bx, cyc, q));
  rep = gen_0;
  av2 = avma; lim = stack_lim(av2, 1);
  for (k = 1; k <= N; k++)
  {
    GEN p2, ak = polcoeff_i(Bx, k, 0);
    p2  = quicktrace(ak, psm);
    rep = modii(addii(rep, mulii(gel(cff, k), p2)), q);
    if (low_stack(lim, stack_lim(av2, 1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem, "twistpartialzeta (3), j = %ld/%ld", k, N);
      rep = gerepileupto(av2, rep);
    }
  }
  return rep;
}

#if 0
/* initialize the roots of unity for the computation
   of the Teichmuller character (also the values of f and c) */
GEN
init_teich(ulong p, GEN q, long prec)
{
  GEN vz, gp = utoipos(p);
  pari_sp av = avma;
  long j;

  if (p == 2UL)
    return NULL;
  else
  { /* primitive (p-1)-th root of 1 */
    GEN z, z0 = Zp_sqrtnlift(gen_1, utoipos(p-1), pgener_Fp(gp), gp, prec);
    z = z0;
    vz = cgetg(p, t_VEC);
    for (j = 1; j < (long)p-2; j++)
    {
      gel(vz, umodiu(z, p)) = z; /* z = z0^i */
      z = modii(mulii(z, z0), q);
    }
    gel(vz, umodiu(z, p)) = z; /* z = z0^(p-2) */
    gel(vz,1) = gen_1; /* z0^(p-1) */
  }
  return gerepileupto(av, gcopy(vz));
}

/* compute phi^(m)_s(x); s must be an integer */
GEN
phi_ms(ulong p, GEN q, long m, GEN s, long x, GEN vz)
{
  long xp = x % p;
  GEN p1, p2;

  if (!xp) return gen_0;
  if (vz)
    p1 =gel(vz,xp); /* vz[x] = Teichmuller(x) */
  else
    p1 = (x & 2)? gen_m1: gen_1;
  p1 = Fp_pow(p1, addis(s, m), q);
  p2 = Fp_pow(stoi(x), negi(s), q);
  return modii(mulii(p1,p2), q);
}

/* compute the first N coefficients of the Mahler expansion
   of phi^m_s skipping the first one (which is zero) */
GEN
coeff_of_phi_ms(ulong p, GEN q, long m, GEN s, long N, GEN vz)
{
  GEN qs2 = shifti(q, -1), cff = zerovec(N);
  pari_sp av, lim;
  long k, j;

  av = avma; lim = stack_lim(av, 2);
  for (k = 1; k <= N; k++)
  {
    gel(cff, k) = phi_ms(p, q, m, s, k, vz);
    if (low_stack(lim, stack_lim(av, 2)))
    {
      if(DEBUGMEM>1)
        pari_warn(warnmem, "coeff_of_phi_ms (1), k = %ld/%ld", N-k, N);
      cff = gerepileupto(av, gcopy(cff));
    }
  }
  for (j = N; j > 1; j--)
  {
    GEN b = subii(gel(cff, j), gel(cff, j-1));
    gel(cff, j) = centermodii(b, q, qs2);
    if (low_stack(lim, stack_lim(av, 2)))
    {
      if(DEBUGMEM>1)
        pari_warn(warnmem, "coeff_of_phi_ms (2), j = %ld/%ld", N-j, N);
      cff = gerepileupto(av, gcopy(cff));
    }
  }
  for (k = 1; k < N; k++)
    for (j = N; j > k; j--)
    {
      GEN b = subii(gel(cff, j), gel(cff, j-1));
      gel(cff, j) = centermodii(b, q, qs2);
      if (low_stack(lim, stack_lim(av, 2)))
      {
        if(DEBUGMEM>1)
          pari_warn(warnmem, "coeff_of_phi_ms (3), (k,j) = (%ld,%ld)/%ld",
              k, N-j, N);
        cff = gerepileupto(av, gcopy(cff));
      }
    }
  k = N; while(gequal0(gel(cff, k))) k--;
  setlg(cff, k+1);
  if (DEBUGLEVEL > 2)
    err_printf("  coeff_of_phi_ms: %ld coefficients kept out of %ld\n",
               k, N);
  return gerepileupto(av, cff);
}

static long
valfact(long N, ulong p)
{
  long f = 0;
  while (N > 1)
  {
    N /= p;
    f += N;
  }
  return f;
}

static long
number_of_terms(ulong p, long prec)
{
  long N, f;

  if (prec == 0) return p;
  N = (long)((p-1)*prec + (p>>1)*(log2(prec)/log2(p)));
  N = p*(N/p);
  f = valfact(N, p);
  while (f > prec)
  {
    N = p*(N/p) - 1;
    f -= u_lval(N+1, p);
  }
  while (f < prec)
  {
    N = p*(N/p+1);
    f += u_lval(N, p);
  }
  return N;
}

static GEN
zetap(GEN s)
{
  ulong p;
  long N, f, c, prec = precp(s);
  pari_sp av = avma;
  GEN gp, q, vz, is, cff, val, va, cft;

  if (valp(s) < 0)
    pari_err(talker, "argument must be a p-adic integer");
  if (!prec) prec = 1;

  gp = gel(s,2); p = itou(gp);
  is = gtrunc(s);  /* make s an integer */

  N  = number_of_terms(p, prec);
  q  = powiu(gp, prec);

  /* initialize the roots of unity for the computation
     of the Teichmuller character (also the values of f and c) */
  if (DEBUGLEVEL > 1) err_printf("zetap: computing (p-1)th roots of 1\n");
  vz = init_teich(p, q, prec);
  if (p == 2UL) {  f = 4; c = 3; } else { f = (long)p; c = 2; }

  /* compute the first N coefficients of the Mahler expansion
     of phi^(-1)_s skipping the first one (which is zero) */
  if (DEBUGLEVEL > 1)
    err_printf("zetap: computing Mahler expansion of phi^(-1)_s\n");
  cff = coeff_of_phi_ms(p, q, -1, is, N, vz);

  /* compute the coefficients of the power series corresponding
     to the twisted partial zeta function Z_f(a, c, s) for a in va */
  /* The line below looks a bit stupid but it is to keep the
     possibility of later adding p-adic Dirichlet L-functions */
  va = identity_perm(f - 1);
  if (DEBUGLEVEL > 1)
    err_printf("zetap: computing values of twisted partial zeta functions\n");
  val = twistpartialzeta(q, f, c, va, cff);

  /* sum over all a's the coefficients of the twisted
     partial zeta functions and integrate */
  if (DEBUGLEVEL > 1)
    err_printf("zetap: multiplying by correcting factor\n");

  /* multiply by the corrective factor */
  cft = gsubgs(gmulsg(c, phi_ms(p, q, -1, is, c, vz)), 1);
  val = gdiv(val, cft);

  /* adjust the precision and return */
  return gerepileupto(av, cvtop(val, gp, prec));
}
#else
static GEN
hurwitz_p(GEN cache, GEN s, GEN x, GEN p, long prec)
{
  GEN S, x2, x2j, s_1 = gsubgs(s,1);
  long j, J = lg(cache)-2;
  x = ginv(gadd(x, zeropadic(p, prec)));
  x2 = gsqr(x);
  S = gmul2n(gmul(s_1, x), -1);
  x2j = gen_1;
  for (j = 0;; j++)
  {
    S = gadd(S, gmul(gel(cache, j+1), x2j));
    if (j == J) break;
    x2j = gmul(x2, x2j);
  }
  return gmul(gdiv(S, s_1), Qp_exp(gmul(s_1, Qp_log(x))));
}

static GEN
init_cache(long J, GEN s)
{
  GEN C = gen_1, cache = bernvec(J);
  long j;

  for (j = 1; j <= J; j++)
  { /* B_{2j} * binomial(1-s, 2j) */
    GEN t = gmul(gaddgs(s, 2*j-3), gaddgs(s, 2*j-2));
    C = gdiv(gmul(C, t), mulss(2*j, 2*j-1));
    gel(cache, j+1) = gmul(gel(cache, j+1), C);
  }
  return cache;
}

static GEN
zetap(GEN s)
{
  pari_sp av = avma;
  GEN cache, S, gp = gel(s,2);
  ulong a, p = itou(gp);
  long J, prec = valp(s) + precp(s);

  if (prec <= 0) prec = 1;
  if (p == 2) {
    J = ((long)(1+ceil((prec+1.)/2))) >> 1;
    cache = init_cache(J, s);
    S = gmul2n(hurwitz_p(cache, s, gmul2n(gen_1, -2), gen_2, prec), -1);
  } else {
    J = (prec+2) >> 1;
    cache = init_cache(J, s);
    S = gen_0;
    for (a = 1; a <= (p-1)>>1; a++)
      S = gadd(S, hurwitz_p(cache, s, gdivsg(a, gp), gp, prec));
    S = gdiv(gmul2n(S, 1), gp);
  }
  return gerepileupto(av, S);
}
#endif

GEN
gzeta(GEN x, long prec)
{
  if (gequal1(x)) pari_err(talker, "argument equal to one in zeta");
  switch(typ(x))
  {
    case t_INT:
      if (is_bigint(x))
      {
        if (signe(x) > 0) return real_1(prec);
        if (signe(x) < 0 && mod2(x) == 0) return real_0(prec);
      }
      return szeta(itos(x),prec);

    case t_REAL: case t_COMPLEX:
      return czeta(x,prec);

    case t_INTMOD: pari_err(typeer,"gzeta");

    case t_PADIC:
      return zetap(x);

    case t_SER: pari_err(impl,"zeta of power series");
  }
  return transc(gzeta,x,prec);
}

/***********************************************************************/
/**                                                                   **/
/**                    FONCTIONS POLYLOGARITHME                       **/
/**                                                                   **/
/***********************************************************************/

/* returns H_n = 1 + 1/2 + ... + 1/n, as a rational number (n "small") */
static GEN
Harmonic(long n)
{
  GEN h = gen_1;
  long i;
  for (i=2; i<=n; i++) h = gadd(h, mkfrac(gen_1, utoipos(i)));
  return h;
}

/* m >= 2. Validity domain contains | log |x| | < 5, best for |x| ~ 1.
 * Li_m(x = e^z) = sum_{n >= 0} zeta(m-n) z^n / n!
 *    with zeta(1) := H_m - log(-z) */
static GEN
cxpolylog(long m, GEN x, long prec)
{
  long li, n;
  GEN z, h, q, s;
  int real;

  if (gequal1(x)) return szeta(m,prec);
  /* x real <= 1 ==> Li_m(x) real */
  real = (typ(x) == t_REAL && (expo(x) < 0 || signe(x) <= 0));

  z = glog(x,prec);
  /* n = 0 */
  q = gen_1;
  s = szeta(m,prec);
  for (n=1; n < m-1; n++)
  {
    q = gdivgs(gmul(q,z),n);
    s = gadd(s, gmul(szeta(m-n,prec), real? real_i(q): q));
  }
  /* n = m-1 */
    q = gdivgs(gmul(q,z),n); /* multiply by "zeta(1)" */
    h = gmul(q, gsub(Harmonic(m-1), glog(gneg_i(z),prec)));
    s = gadd(s, real? real_i(h): h);
  /* n = m */
    q = gdivgs(gmul(q,z),m);
    s = gadd(s, gmul(szeta(0,prec), real? real_i(q): q));
  /* n = m+1 */
    q = gdivgs(gmul(q,z),m+1);
    s = gadd(s, gmul(szeta(-1,prec), real? real_i(q): q));

  z = gsqr(z); li = -(bit_accuracy(prec)+1);
  /* n = m+3, m+5, ...; note that zeta(- even integer) = 0 */
  for(n = m+3;; n += 2)
  {
    GEN zet = szeta(m-n,prec);
    q = divgunu(gmul(q,z), n-1);
    s = gadd(s, gmul(zet, real? real_i(q): q));
    if (gexpo(q) + expo(zet) < li) break;
  }
  return s;
}

static GEN
polylog(long m, GEN x, long prec)
{
  long l, e, i, G, sx;
  pari_sp av, av1, limpile;
  GEN X, Xn, z, p1, p2, y, res;

  if (m < 0) pari_err(talker,"negative index in polylog");
  if (!m) return mkfrac(gen_m1,gen_2);
  if (gequal0(x)) return gcopy(x);
  if (m==1)
  {
    av = avma;
    return gerepileupto(av, gneg(glog(gsub(gen_1,x), prec)));
  }

  l = precision(x); if (!l) l = prec;
  res = cgetc(l); av = avma;
  x = gtofp(x, l+1);
  e = gexpo(gnorm(x));
  if (!e || e == -1) {
    y = cxpolylog(m,x,prec);
    avma = av; return affc_fixlg(y, res);
  }
  X = (e > 0)? ginv(x): x;
  G = -bit_accuracy(l);
  av1 = avma; limpile = stack_lim(av1,1);
  y = Xn = X;
  for (i=2; ; i++)
  {
    Xn = gmul(X,Xn); p2 = gdiv(Xn,powuu(i,m));
    y = gadd(y,p2);
    if (gexpo(p2) <= G) break;

    if (low_stack(limpile, stack_lim(av1,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"polylog");
      gerepileall(av1,2, &y, &Xn);
    }
  }
  if (e < 0) { avma = av; return affc_fixlg(y, res); }

  sx = gsigne(imag_i(x));
  if (!sx)
  {
    if (m&1) sx = gsigne(gsub(gen_1, real_i(x)));
    else     sx = - gsigne(real_i(x));
  }
  z = divri(mppi(l), mpfact(m-1)); setsigne(z, sx);
  z = mkcomplex(gen_0, z);

  if (m == 2)
  { /* same formula as below, written more efficiently */
    y = gneg_i(y);
    if (typ(x) == t_REAL && signe(x) < 0)
      p1 = logr_abs(x);
    else
      p1 = gsub(glog(x,l), z);
    p1 = gmul2n(gsqr(p1), -1); /* = (log(-x))^2 / 2 */

    p1 = gadd(p1, divru(sqrr(mppi(l)), 6));
    p1 = gneg_i(p1);
  }
  else
  {
    GEN logx = glog(x,l), logx2 = gsqr(logx);
    p1 = mkfrac(gen_m1,gen_2);
    for (i=m-2; i>=0; i-=2)
      p1 = gadd(szeta(m-i,l), gmul(p1,gdivgs(logx2,(i+1)*(i+2))));
    if (m&1) p1 = gmul(logx,p1); else y = gneg_i(y);
    p1 = gadd(gmul2n(p1,1), gmul(z,gpowgs(logx,m-1)));
    if (typ(x) == t_REAL && signe(x) < 0) p1 = real_i(p1);
  }
  y = gadd(y,p1);
  avma = av; return affc_fixlg(y, res);
}

GEN
dilog(GEN x, long prec)
{
  return gpolylog(2, x, prec);
}

/* x a floating point number, t_REAL or t_COMPLEX of t_REAL */
static GEN
logabs(GEN x)
{
  GEN y;
  if (typ(x) == t_COMPLEX)
  {
    y = logr_abs( cxnorm(x) );
    setexpo(y, expo(y)-1);
  } else
    y = logr_abs(x);
  return y;
}

static GEN
polylogD(long m, GEN x, long flag, long prec)
{
  long k, l, fl, m2;
  pari_sp av;
  GEN p1, p2, y;

  if (gequal0(x)) return gcopy(x);
  m2 = m&1;
  if (gequal1(x) && m>=2) return m2? szeta(m,prec): gen_0;
  av = avma; l = precision(x);
  if (!l) { l = prec; x = gtofp(x,l); }
  p1 = logabs(x);
  k = signe(p1);
  if (k > 0) { x = ginv(x); fl = !m2; } else { setabssign(p1); fl = 0; }
  /* |x| <= 1, p1 = - log|x| >= 0 */
  p2 = gen_1;
  y = polylog(m,x,l);
  y = m2? real_i(y): imag_i(y);
  for (k=1; k<m; k++)
  {
    GEN t = polylog(m-k,x,l);
    p2 = gdivgs(gmul(p2,p1), k); /* (-log|x|)^k / k! */
    y = gadd(y, gmul(p2, m2? real_i(t): imag_i(t)));
  }
  if (m2)
  {
    if (!flag) p1 = negr( logabs(gsubsg(1,x)) ); else p1 = shiftr(p1,-1);
    p2 = gdivgs(gmul(p2,p1), -m);
    y = gadd(y, p2);
  }
  if (fl) y = gneg(y);
  return gerepileupto(av, y);
}

static GEN
polylogP(long m, GEN x, long prec)
{
  long k, l, fl, m2;
  pari_sp av;
  GEN p1,y;

  if (gequal0(x)) return gcopy(x);
  m2 = m&1;
  if (gequal1(x) && m>=2) return m2? szeta(m,prec): gen_0;
  av = avma; l = precision(x);
  if (!l) { l = prec; x = gtofp(x,l); }
  mpbern(m>>1, l);
  p1 = logabs(x);
  k = signe(p1);
  if (k > 0) { x = ginv(x); fl = !m2; } else fl = 0;
  /* |x| <= 1 */
  if (k > 0) setsigne(p1, -1);
  setexpo(p1, expo(p1)+1); /* 2log|x| <= 0 */

  y = polylog(m,x,l);
  y = m2? real_i(y): imag_i(y);

  if (m==1)
    y = gadd(y, gmul2n(p1,-2));
  else
  {
    GEN p2 = gen_1;
    for (k=1; k<m; k++)
    {
      p2 = gdivgs(gmul(p2,p1),k);
      if (!(k&1) || k==1)
      {
        GEN u, t = polylog(m-k,x,l);
        if (k!=1) u = gmul(p2, bern(k>>1));
        else      u = gneg_i(gmul2n(p2,-1));
        /* u = p2*B_k */
        y = gadd(y, gmul(u, m2?real_i(t):imag_i(t)));
      }
    }
  }
  if (fl) y = gneg(y);
  return gerepileupto(av, y);
}

GEN
gpolylog(long m, GEN x, long prec)
{
  long i, lx, n, v;
  pari_sp av = avma;
  GEN a, y, p1;

  if (m <= 0)
  {
    GEN t = mkpoln(2, gen_m1, gen_1); /* 1 - X */
    p1 = pol_x(0);
    for (i=2; i <= -m; i++)
      p1 = RgX_shift_shallow(gadd(gmul(t,ZX_deriv(p1)), gmulsg(i,p1)), 1);
    p1 = gdiv(p1, gpowgs(t,1-m));
    return gerepileupto(av, poleval(p1,x));
  }

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_COMPLEX: case t_QUAD:
      return polylog(m,x,prec);

    case t_POLMOD:
      p1=cleanroots(gel(x,1),prec); lx=lg(p1);
      for (i=1; i<lx; i++) gel(p1,i) = poleval(gel(x,2),gel(p1,i));
      y=cgetg(lx,t_COL);
      for (i=1; i<lx; i++) gel(y,i) = polylog(m,gel(p1,i),prec);
      return gerepileupto(av, y);

    case t_INTMOD: case t_PADIC: pari_err(impl, "padic polylogarithm");
    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (!m) { avma = av; return mkfrac(gen_m1,gen_2); }
      if (m==1) return gerepileupto(av, gneg( glog(gsub(gen_1,y),prec) ));
      if (gequal0(y)) return gerepilecopy(av, y);
      v = valp(y);
      if (v <= 0) pari_err(impl,"polylog around a!=0");
      n = (lg(y)-3 + v) / v;
      a = zeroser(varn(y), lg(y)-2);
      for (i=n; i>=1; i--)
        a = gmul(y, gadd(a, powis(utoipos(i),-m)));
      return gerepileupto(av, a);

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gpolylog(m,gel(x,i),prec);
      return y;
  }
  pari_err(typeer,"gpolylog");
  return NULL; /* not reached */
}

GEN
polylog0(long m, GEN x, long flag, long prec)
{
  switch(flag)
  {
    case 0: return gpolylog(m,x,prec);
    case 1: return polylogD(m,x,0,prec);
    case 2: return polylogD(m,x,1,prec);
    case 3: return polylogP(m,x,prec);
    default: pari_err(flagerr,"polylog");
  }
  return NULL; /* not reached */
}

static GEN
upper_half(GEN x, long *prec)
{
  long tx = typ(x), l;
  if (tx == t_QUAD) { x = quadtofp(x, *prec); tx = typ(x); }
  if (tx != t_COMPLEX || gsigne(gel(x,2)) <= 0)
    pari_err(talker,"argument '%Ps' does not belong to upper half-plane", x);
  l = precision(x); if (l) *prec = l;
  return x;
}

/* sqrt(3)/2 */
static GEN
sqrt32(long prec) { GEN z = sqrtr_abs(stor(3,prec)); setexpo(z, -1); return z; }
/* exp(i x), x = k pi/12 */
static GEN
e12(ulong k, long prec)
{
  int s, sPi, sPiov2;
  GEN z, t;
  k %= 24;
  if (!k) return gen_1;
  if (k == 12) return gen_m1;
  if (k >12) { s = 1; k = 24 - k; } else s = 0; /* x -> 2pi - x */
  if (k > 6) { sPi = 1; k = 12 - k; } else sPi = 0; /* x -> pi  - x */
  if (k > 3) { sPiov2 = 1; k = 6 - k; } else sPiov2 = 0; /* x -> pi/2 - x */
  z = cgetg(3, t_COMPLEX);
  switch(k)
  {
    case 0: gel(z,1) = icopy(gen_1); gel(z,2) = gen_0; break;
    case 1: t = gmul2n(addrs(sqrt32(prec), 1), -1);
      gel(z,1) = sqrtr(t);
      gel(z,2) = gmul2n(invr(gel(z,1)), -2); break;

    case 2: gel(z,1) = sqrt32(prec);
            gel(z,2) = real2n(-1, prec); break;

    case 3: gel(z,1) = sqrtr_abs(real2n(-1,prec));
            gel(z,2) = rcopy(gel(z,1)); break;
  }
  if (sPiov2) swap(gel(z,1), gel(z,2));
  if (sPi) togglesign(gel(z,1));
  if (s)   togglesign(gel(z,2));
  return z;
}
/* z a t_FRAC */
static GEN
eiPi_frac(GEN z, long prec)
{
  GEN n, d;
  ulong q, r;
  n = gel(z,1);
  d = gel(z,2);
  q = udivui_rem(12, d, &r);
  if (!r) /* relatively frequent case */
    return e12(q * umodiu(n, 24), prec);
  n = centermodii(n, shifti(d,1), d);
  return exp_Ir(divri(mulri(mppi(prec), n), d));
}
/* exp(i Pi z), z a t_INT or t_FRAC */
static GEN
exp_IPiQ(GEN z, long prec)
{
  if (typ(z) == t_INT) return mpodd(z)? gen_m1: gen_1;
  return eiPi_frac(z, prec);
}
/* z a t_COMPLEX */
static GEN
exp_IPiC(GEN z, long prec)
{
  GEN r, x = gel(z,1), y = gel(z,2);
  GEN pi, mpi = mppi(prec);
  togglesign(mpi); /* mpi = -Pi */
  r = gexp(gmul(mpi, y), prec);
  switch(typ(x))
  {
    case t_INT:
      if (mpodd(x)) togglesign(r);
      return r;
    case t_FRAC:
      return gmul(r, eiPi_frac(x, prec));
    default:
      pi = mpi; togglesign(mpi); /* pi = Pi */
      return gmul(r, exp_Ir(gmul(pi, x)));
  }
}

static GEN
qq(GEN x, long prec)
{
  long tx = typ(x);

  if (is_scalar_t(tx))
  {
    if (tx == t_PADIC) return x;
    x = upper_half(x, &prec);
    return exp_IPiC(gmul2n(x,1), prec); /* e(x) */
  }
  if (! ( x = toser_i(x)) ) pari_err(talker,"bad argument for modular function");
  return x;
}

/* return (y * X^d) + x. Assume d > 0, x != 0, valp(x) = 0 */
static GEN
ser_addmulXn(GEN y, GEN x, long d)
{
  long i, lx, ly, l = valp(y) + d; /* > 0 */
  GEN z;

  lx = lg(x);
  ly = lg(y) + l; if (lx < ly) ly = lx;
  if (l > lx-2) return gcopy(x);
  z = cgetg(ly,t_SER);
  for (i=2; i<=l+1; i++) gel(z,i) = gel(x,i);
  for (   ; i < ly; i++) gel(z,i) = gadd(gel(x,i),gel(y,i-l));
  z[1] = x[1]; return z;
}

/* q a t_POL */
static GEN
inteta_pol(GEN q, long v, long l)
{
  pari_sp av = avma, lim = stack_lim(av, 1);
  GEN qn, ps, y;
  ulong vps, vqn, n;

  y = qn = ps = pol_1(0);
  vps = vqn = 0;
  for(n = 0;; n++)
  { /* qn = q^n,  ps = (-1)^n q^(n(3n+1)/2),
     * vps, vqn valuation of ps, qn HERE */
    pari_sp av2 = avma;
    ulong vt = vps + 2*vqn + v; /* valuation of t at END of loop body */
    long k1, k2;
    GEN t;
    vqn += v; vps = vt + vqn; /* valuation of qn, ps at END of body */
    k1 = l-2 + v - vt + 1;
    k2 = k1 - vqn; /* = l-2 + v - vps + 1 */
    if (k1 <= 0) break;
    t = RgX_mul(q, RgX_sqr(qn));
    t = RgX_modXn_shallow(t, k1);
    t = RgX_mul(ps,t);
    t = RgX_modXn_shallow(t, k1);
    t = RgX_neg(t); /* t = (-1)^(n+1) q^(n(3n+1)/2 + 2n+1) */
    t = gerepileupto(av2, t);
    y = addmulXn(t, y, vt);
    if (k2 <= 0) break;

    qn = RgX_mul(qn,q);
    ps = RgX_mul(t,qn);
    ps = RgX_modXn_shallow(ps, k2);
    y = addmulXn(ps, y, vps);

    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"eta, n = %ld", n);
      gerepileall(av, 3, &y, &qn, &ps);
    }
  }
  setvarn(y, varn(q)); return RgX_to_ser(y, l+v);
}

static GEN
inteta(GEN q)
{
  long tx = typ(q);
  GEN ps, qn, y;

  y = gen_1; qn = gen_1; ps = gen_1;
  if (tx==t_PADIC)
  {
    if (valp(q) <= 0) pari_err(talker,"non-positive valuation in eta");
    for(;;)
    {
      GEN t = gneg_i(gmul(ps,gmul(q,gsqr(qn))));
      y = gadd(y,t); qn = gmul(qn,q); ps = gmul(t,qn);
      t = y;
      y = gadd(y,ps); if (gequal(t,y)) return y;
    }
  }

  if (tx == t_SER)
  {
    ulong vps, vqn;
    long l = lg(q), v, n;
    pari_sp av, lim;

    v = valp(q); /* handle valuation separately to avoid overflow */
    if (v <= 0) pari_err(talker,"non-positive valuation in eta");
    y = ser2pol_i(q, l); /* t_SER inefficient when input has low degree */
    n = degpol(y);
    if (n == 1 || n < (l>>2)) return inteta_pol(y, v, l);

    q = leafcopy(q); av = avma; lim = stack_lim(av, 3);
    setvalp(q, 0);
    y = scalarser(gen_1, varn(q), l+v);
    vps = vqn = 0;
    for(n = 0;; n++)
    { /* qn = q^n,  ps = (-1)^n q^(n(3n+1)/2) */
      ulong vt = vps + 2*vqn + v;
      long k;
      GEN t;
      t = gneg_i(gmul(ps,gmul(q,gsqr(qn))));
      /* t = (-1)^(n+1) q^(n(3n+1)/2 + 2n+1) */
      y = ser_addmulXn(t, y, vt);
      qn = gmul(qn,q); ps = gmul(t,qn);
      vqn += v; vps = vt + vqn;
      k = l+v - vps; if (k <= 2) return y;

      y = ser_addmulXn(ps, y, vps);
      setlg(q, k);
      setlg(qn, k);
      setlg(ps, k);
      if (low_stack(lim, stack_lim(av,3)))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"eta");
        gerepileall(av, 3, &y, &qn, &ps);
      }
    }
  }
  {
    long l; /* gcc -Wall */
    pari_sp av = avma, lim = stack_lim(av, 3);

    if (is_scalar_t(tx)) l = -bit_accuracy(precision(q));
    else
    {
      l = lg(q)-2; tx = 0;
      if (valp(q) <= 0) pari_err(talker,"non-positive valuation in eta");
    }
    for(;;)
    {
      GEN t = gneg_i(gmul(ps,gmul(q,gsqr(qn))));
      /* qn = q^n
       * ps = (-1)^n q^(n(3n+1)/2)
       * t = (-1)^(n+1) q^(n(3n+1)/2 + 2n+1) */
      y = gadd(y,t); qn = gmul(qn,q); ps = gmul(t,qn);
      y = gadd(y,ps);
      if (tx)
        { if (gexpo(ps)-gexpo(y) < l) return y; }
      else
        { if (valp(ps) >= l) return y; }
      if (low_stack(lim, stack_lim(av,3)))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"eta");
        gerepileall(av, 3, &y, &qn, &ps);
      }
    }
  }
}

GEN
eta(GEN x, long prec)
{
  pari_sp av = avma;
  GEN z = inteta( qq(x,prec) );
  if (typ(z) == t_SER) return gerepilecopy(av, z);
  return gerepileupto(av, z);
}

/* s(h,k) = sum(n = 1, k-1, (n/k)*(frac(h*n/k) - 1/2))
 * Knuth's algorithm. h integer, k integer > 0, (h,k) = 1 */
GEN
sumdedekind_coprime(GEN h, GEN k)
{
  pari_sp av = avma;
  GEN s2, s1 = gen_0, p = gen_1, pp = gen_0, s = gen_1;
  s2 = h = modii(h, k);
  while (signe(h)) {
    GEN r, nexth, a = dvmdii(k, h, &nexth);
    if (is_pm1(h)) s2 = addii(s2, mulii(p, s));
    s1 = addii(s1, mulii(a, s));
    togglesign_safe(&s);
    k = h; h = nexth;
    r = addii(mulii(a,p), pp); pp = p; p = r;
  }
  if (signe(s) < 0) s1 = subis(s1, 3);
  return gerepileupto(av, gdiv(addii(mulii(p,s1), s2), muliu(p,12)));
}
GEN
sumdedekind(GEN h, GEN k)
{
  pari_sp av = avma;
  GEN d;
  if (typ(h) != t_INT || typ(k) != t_INT) pari_err(typeer, "sumdedekind");
  d = gcdii(h,k);
  if (!is_pm1(d))
    avma = av;
  else {
    h = diviiexact(h, d);
    k = diviiexact(k, d);
  }
  return gerepileupto(av, sumdedekind_coprime(h,k));
}

/* eta(x); assume Im x >> 0 (e.g. x in SL2's standard fundamental domain) */
static GEN
eta_reduced(GEN x, long prec)
{
  GEN z = exp_IPiC(gdivgs(x, 12), prec); /* e(x/24) */
  if (24 * gexpo(z) >= -bit_accuracy(prec))
    z = gmul(z, inteta( gpowgs(z,24) ));
  return z;
}

/* x = U.z (flag = 1), or x = U^(-1).z (flag = 0)
 * Return [s,t] such that eta(z) = eta(x) * sqrt(s) * exp(I Pi t) */
static GEN
eta_correction(GEN x, GEN U, long flag)
{
  GEN a,b,c,d, s,t;
  long sc;
  a = gcoeff(U,1,1);
  b = gcoeff(U,1,2);
  c = gcoeff(U,2,1);
  d = gcoeff(U,2,2);
  /* replace U by U^(-1) */
  if (flag) {
    swap(a,d);
    togglesign_safe(&b);
    togglesign_safe(&c);
  }
  sc = signe(c);
  if (!sc) {
    if (signe(d) < 0) togglesign_safe(&b);
    s = gen_1;
    t = gdivgs(utoi(umodiu(b, 24)), 12);
  } else {
    if (sc < 0) {
      togglesign_safe(&a);
      togglesign_safe(&b);
      togglesign_safe(&c);
      togglesign_safe(&d);
    } /* now c > 0 */
    s = mulcxmI(gadd(gmul(c,x), d));
    t = gadd(gdiv(addii(a,d),muliu(c,12)), sumdedekind_coprime(negi(d),c));
    /* correction : exp(I Pi (((a+d)/12c) + s(-d,c)) ) sqrt(-i(cx+d))  */
  }
  return mkvec2(s, t);
}

/* returns the true value of eta(x) for Im(x) > 0, using reduction to
 * standard fundamental domain */
GEN
trueeta(GEN x, long prec)
{
  pari_sp av = avma;
  GEN U, st, s, t;

  if (!is_scalar_t(typ(x))) pari_err(typeer,"trueeta");
  x = upper_half(x, &prec);
  x = redtausl2(x, &U);
  st = eta_correction(x, U, 1);
  x = eta_reduced(x, prec);
  s = gel(st, 1);
  t = gel(st, 2);
  x = gmul(x, exp_IPiQ(t, prec));
  if (s != gen_1) x = gmul(x, gsqrt(s, prec));
  return gerepileupto(av, x);
}

GEN
eta0(GEN x, long flag,long prec)
{ return flag? trueeta(x,prec): eta(x,prec); }

#if 0
/* U = [a,b;c,d], return c*z +d */
static GEN
aut_factor(GEN U, GEN z)
{
  GEN c = gcoeff(U,2,1), d = gcoeff(U,2,2);
  return signe(c)? gadd(gmul(c,z), d): d;
}
#endif

GEN
jell(GEN x, long prec)
{
  long tx = typ(x);
  pari_sp av = avma;
  GEN q, h, U;

  if (!is_scalar_t(tx) || tx == t_PADIC)
  {
    GEN p1, p2;
    q = qq(x,prec);
    p1 = gdiv(inteta(gsqr(q)), inteta(q));
    p1 = gmul2n(gsqr(p1),1);
    p1 = gmul(q,gpowgs(p1,12));
    p2 = gaddsg(768,gadd(gsqr(p1),gdivsg(4096,p1)));
    p1 = gmulsg(48,p1);
    return gerepileupto(av, gadd(p2,p1));
  }
  /* Let h = Delta(2x) / Delta(x), then j(x) = (1 + 256h)^3 / h */
  x = upper_half(x, &prec);
  x = redtausl2(x, &U); /* forget about Ua : j has weight 0 */
  { /* cf eta_reduced, raiѕed to power 24
     * Compute
     *   t = (inteta(q(2x)) / inteta(q(x))) ^ 24;
     * then
     *   h = t * (q(2x) / q(x) = t * q(x);
     * but inteta(q) costly and useless if expo(q) << 1  => inteta(q) = 1.
     * log_2 ( exp(-2Pi Im tau) ) < -bit_accuracy(prec)
     * <=> Im tau > bit_accuracy(prec) * log(2) / 2Pi */
    long C = (long)bit_accuracy_mul(prec, LOG2/(2*PI));
    q = exp_IPiC(gmul2n(x,1), prec); /* e(x) */
    if (gcmpgs(gel(x,2), C) > 0) /* eta(q(x)) = 1 : no need to compute q(2x) */
      h = q;
    else
    {
      GEN t = gdiv(inteta(gsqr(q)), inteta(q));
      h = gmul(q, gpowgs(t, 24));
    }
  }
  /* real_1 important ! gaddgs(, 1) could increase the accuracy ! */
  return gerepileupto(av, gdiv(gpowgs(gadd(gmul2n(h,8), real_1(prec)), 3), h));
}

static GEN
to_form(GEN a, GEN w, GEN C)
{ return mkvec3(a, w, diviiexact(C, a)); }
static GEN
form_to_quad(GEN f, GEN sqrtD)
{
  long a = itos(gel(f,1)), a2 = a << 1;
  GEN b = gel(f,2);
  return mkcomplex(gdivgs(b, -a2), gdivgs(sqrtD, a2));
}
static GEN
eta_form(GEN f, GEN sqrtD, GEN *s_t, long prec)
{
  GEN U, t = form_to_quad(redimagsl2(f, &U), sqrtD);
  *s_t = eta_correction(t, U, 0);
  return eta_reduced(t, prec);
}

/* eta(t/p)eta(t/q) / (eta(t)eta(t/pq)), t = (-w + sqrt(D)) / 2a */
GEN
double_eta_quotient(GEN a, GEN w, GEN D, long p, long q, GEN pq, GEN sqrtD)
{
  GEN C = shifti(subii(sqri(w), D), -2);
  GEN d, t, z, zp, zq, zpq, s_t, s_tp, s_tpq, s, sp, spq;
  long prec = lg(sqrtD);

  z = eta_form(to_form(a, w, C), sqrtD, &s_t, prec);
  s = gel(s_t, 1);
  zp = eta_form(to_form(mului(p, a), w, C), sqrtD, &s_tp, prec);
  sp = gel(s_tp, 1);
  zpq = eta_form(to_form(mulii(pq, a), w, C), sqrtD, &s_tpq, prec);
  spq = gel(s_tpq, 1);
  if (p == q) {
    z = gdiv(gsqr(zp), gmul(z, zpq));
    t = gsub(gmul2n(gel(s_tp,2), 1),
             gadd(gel(s_t,2), gel(s_tpq,2)));
    if (sp != gen_1) z = gmul(z, sp);
  } else {
    GEN s_tq, sq;
    zq = eta_form(to_form(mului(q, a), w, C), sqrtD, &s_tq, prec);
    sq = gel(s_tq, 1);
    z = gdiv(gmul(zp, zq), gmul(z, zpq));
    t = gsub(gadd(gel(s_tp,2), gel(s_tq,2)),
             gadd(gel(s_t,2), gel(s_tpq,2)));
    if (sp != gen_1) z = gmul(z, gsqrt(sp, prec));
    if (sq != gen_1) z = gmul(z, gsqrt(sq, prec));
  }
  d = NULL;
  if (s != gen_1) d = gsqrt(s, prec);
  if (spq != gen_1) {
    GEN x = gsqrt(spq, prec);
    d = d? gmul(d, x): x;
  }
  if (d) z = gdiv(z, d);
  return gmul(z, exp_IPiQ(t, prec));
}

/* sqrt(2) eta(2x) / eta(x) */
GEN
weberf2(GEN x, long prec)
{
  pari_sp av = avma;
  GEN z, t, a,b, Ua,Ub, s_a, s_b, st_a,st_b;
  x = upper_half(x, &prec);
  a = redtausl2(x, &Ua);
  b = redtausl2(gmul2n(x,1), &Ub);
  if (gequal(a,b)) /* not infrequent */
    z = gen_1;
  else
    z = gdiv(eta_reduced(b,prec), eta_reduced(a,prec));
  st_a = eta_correction(a, Ua, 1); s_a = gel(st_a, 1);
  st_b = eta_correction(b, Ub, 1); s_b = gel(st_b, 1);
  t = gsub(gel(st_b,2), gel(st_a,2));
  z = gmul(z, exp_IPiQ(t, prec));
  if (s_b != gen_1) z = gmul(z, gsqrt(s_b, prec));
  if (s_a != gen_1) z = gdiv(z, gsqrt(s_a, prec));
  return gerepileupto(av, gmul(z, sqrtr(real2n(1, prec))));
}

/* eta(x/2) / eta(x) */
GEN
weberf1(GEN x, long prec)
{
  pari_sp av = avma;
  GEN z, t, a,b, Ua,Ub, s_a, s_b, st_a,st_b;
  x = upper_half(x, &prec);
  a = redtausl2(x, &Ua);
  b = redtausl2(gmul2n(x,-1), &Ub);
  if (gequal(a,b)) /* not infrequent */
    z = gen_1;
  else
    z = gdiv(eta_reduced(b,prec), eta_reduced(a,prec));
  st_a = eta_correction(a, Ua, 1); s_a = gel(st_a, 1);
  st_b = eta_correction(b, Ub, 1); s_b = gel(st_b, 1);
  t = gsub(gel(st_b,2), gel(st_a,2));
  z = gmul(z, exp_IPiQ(t, prec));
  if (s_b != gen_1) z = gmul(z, gsqrt(s_b, prec));
  if (s_a != gen_1) z = gdiv(z, gsqrt(s_a, prec));
  return gerepileupto(av, z);
}
/* e(-1/24) * eta((x+1)/2) / eta(x) */
GEN
weberf(GEN x, long prec)
{
  pari_sp av = avma;
  GEN z, t, a,b, Ua,Ub, s_a, s_b, st_a,st_b;
  x = upper_half(x, &prec);
  a = redtausl2(x, &Ua);
  b = redtausl2(gmul2n(gaddgs(x,1),-1), &Ub);
  if (gequal(a,b)) /* not infrequent */
    z = gen_1;
  else
    z = gdiv(eta_reduced(b,prec), eta_reduced(a,prec));
  st_a = eta_correction(a, Ua, 1); s_a = gel(st_a, 1);
  st_b = eta_correction(b, Ub, 1); s_b = gel(st_b, 1);
  t = gsub(gsub(gel(st_b,2), gel(st_a,2)), mkfrac(gen_1, utoipos(24)));
  z = gmul(z, exp_IPiQ(t, prec));
  if (s_b != gen_1) z = gmul(z, gsqrt(s_b, prec));
  if (s_a != gen_1) z = gdiv(z, gsqrt(s_a, prec));
  return gerepileupto(av, z);
}
GEN
weber0(GEN x, long flag,long prec)
{
  switch(flag)
  {
    case 0: return weberf(x,prec);
    case 1: return weberf1(x,prec);
    case 2: return weberf2(x,prec);
    default: pari_err(flagerr,"weber");
  }
  return NULL; /* not reached */
}

GEN
theta(GEN q, GEN z, long prec)
{
  long l, n;
  pari_sp av = avma, av2, lim;
  GEN s, c, snz, cnz, s2z, c2z, ps, qn, y, zy, ps2, k, zold;

  l = precision(q);
  n = precision(z); if (n && n < l) l = n;
  if (l) prec = l;
  z = gtofp(z, prec);
  q = gtofp(q, prec); if (gexpo(q) >= 0) pari_err(talker,"q >= 1 in theta");
  zold = NULL; /* gcc -Wall */
  zy = imag_i(z);
  if (gequal0(zy)) k = gen_0;
  else
  {
    GEN lq = glog(q,prec); k = roundr(divrr(zy, real_i(lq)));
    if (signe(k)) { zold = z; z = gadd(z, mulcxmI(gmul(lq,k))); }
  }
  qn = gen_1;
  ps2 = gsqr(q);
  ps = gneg_i(ps2);
  gsincos(z, &s, &c, prec);
  s2z = gmul2n(gmul(s,c),1); /* sin 2z */
  c2z = gsubgs(gmul2n(gsqr(c),1), 1); /* cos 2z */
  snz = s;
  cnz = c; y = s;
  av2 = avma; lim = stack_lim(av2,2);
  for (n = 3;; n += 2)
  {
    long e;
    s = gadd(gmul(snz, c2z), gmul(cnz,s2z));
    qn = gmul(qn,ps);
    y = gadd(y, gmul(qn, s));
    e = gexpo(s); if (e < 0) e = 0;
    if (gexpo(qn) + e < -bit_accuracy(prec)) break;

    ps = gmul(ps,ps2);
    c = gsub(gmul(cnz, c2z), gmul(snz,s2z));
    snz = s; /* sin nz */
    cnz = c; /* cos nz */
    if (low_stack(lim, stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"theta (n = %ld)", n);
      gerepileall(av2, 5, &snz, &cnz, &ps, &qn, &y);
    }
  }
  if (signe(k))
  {
    y = gmul(y, gmul(powgi(q,sqri(k)),
                     gexp(gmul(mulcxI(zold),shifti(k,1)), prec)));
    if (mod2(k)) y = gneg_i(y);
  }
  return gerepileupto(av, gmul(y, gmul2n(gsqrt(gsqrt(q,prec),prec),1)));
}

GEN
thetanullk(GEN q, long k, long prec)
{
  long l, n;
  pari_sp av = avma;
  GEN p1, ps, qn, y, ps2;

  if (k < 0) pari_err(talker,"k < 0 in thetanullk");
  l = precision(q);
  if (l) prec = l;
  q = gtofp(q, prec); if (gexpo(q) >= 0) pari_err(talker,"q >= 1 in theta");

  if (!(k&1)) { avma = av; return gen_0; }
  qn = gen_1;
  ps2 = gsqr(q);
  ps = gneg_i(ps2);
  y = gen_1;
  for (n = 3;; n += 2)
  {
    GEN t;
    qn = gmul(qn,ps);
    ps = gmul(ps,ps2);
    t = gmul(qn, powuu(n, k)); y = gadd(y, t);
    if (gexpo(t) < -bit_accuracy(prec)) break;
  }
  p1 = gmul2n(gsqrt(gsqrt(q,prec),prec),1);
  if (k&2) y = gneg_i(y);
  return gerepileupto(av, gmul(p1, y));
}

/* [d^i theta/dz^i(q, 0), i = 1, 3, .., 2*k - 1] */
GEN
vecthetanullk(GEN q, long k, long prec)
{
  long i, l, n;
  pari_sp av = avma;
  GEN p1, ps, qn, y, ps2;

  l = precision(q); if (l) prec = l;
  q = gtofp(q, prec); if (gexpo(q) >= 0) pari_err(talker,"q >= 1 in theta");

  qn = gen_1;
  ps2 = gsqr(q);
  ps = gneg_i(ps2);
  y = const_vec(k, gen_1);
  for (n = 3;; n += 2)
  {
    GEN t = NULL/*-Wall*/, P = utoipos(n), N2 = sqru(n);
    qn = gmul(qn,ps);
    ps = gmul(ps,ps2);
    for (i = 1; i <= k; i++)
    {
      t = gmul(qn, P); gel(y,i) = gadd(gel(y,i), t);
      P = mulii(P, N2);
    }
    if (gexpo(t) < -bit_accuracy(prec)) break;
  }
  p1 = gmul2n(gsqrt(gsqrt(q,prec),prec),1);
  for (i = 2; i <= k; i+=2) gel(y,i) = gneg_i(gel(y,i));
  return gerepileupto(av, gmul(p1, y));
}
