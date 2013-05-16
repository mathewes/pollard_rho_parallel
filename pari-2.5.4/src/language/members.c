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

/********************************************************************/
/**                                                                **/
/**                          MEMBER FUNCTIONS                      **/
/**                                                                **/
/********************************************************************/
INLINE int is_ell5(GEN x) {
  long lx = lg(x);
  return (typ(x) == t_VEC && (lx == 6 || lx == 14 || lx == 20));
}
INLINE int is_smallell(GEN x) {
  long lx = lg(x);
  return (typ(x) == t_VEC && (lx == 14 || lx == 20));
}
INLINE int is_ell(GEN x) {
  long lx = lg(x);
  return (typ(x) == t_VEC && lx == 20);
}

static void
member_err(const char *s) { pari_err(typeer,s); }

GEN
member_e(GEN x)
{
  x = get_prid(x);
  if (!x) member_err("e");
  return gel(x,3);
}

GEN
member_f(GEN x)
{
  x = get_prid(x);
  if (!x) member_err("f");
  return gel(x,4);
}

GEN
member_p(GEN x)
{
  long t; (void)get_nf(x,&t);
  if (t == typ_GAL) return gal_get_p(x);
  switch(typ(x)) {
    case t_VEC:
      x = get_prid(x); if (!x) member_err("p");
      return pr_get_p(x);
    case t_PADIC:
      return gel(x,2);
    case t_FFELT:
      return FF_p_i(x);
  }
  member_err("p");
  return NULL;
}

GEN
member_bid(GEN x)
{
  long t; (void)get_nf(x,&t);
  switch(t) {
    case typ_BNR: return bnr_get_bid(x);
    case typ_BID: return x;
  }
  member_err("bid");
  return NULL;
}

GEN
member_bnf(GEN x)
{
  long t; x = get_bnf(x,&t);
  if (!x) member_err("bnf");
  return x;
}

GEN
member_nf(GEN x)
{
  long t; GEN y = get_nf(x,&t);
  if (!y) {
    if (t == typ_RNF) return gel(x,10);
    member_err("nf");
  }
  return y;
}

/* integral basis */
GEN
member_zk(GEN x)
{
  long t; GEN y = get_nf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_Q:
        y = cgetg(3,t_VEC);
        gel(y,1) = gen_1;
        gel(y,2) = pol_x(varn(x[1])); return y;
      case typ_RNF:
        return gel(x,7);
    }
    member_err("zk");
  }
  return nf_get_zk(y);
}

GEN
member_disc(GEN x) /* discriminant */
{
  long t; GEN y = get_nf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_Q  : return quad_disc(x);
      case typ_ELL: return ell_get_disc(x);
    }
    member_err("disc");
  }
  return nf_get_disc(y);
}

GEN
member_pol(GEN x) /* polynomial */
{
  long t; GEN y = get_nf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_POL: return x;
      case typ_Q  : return gel(x,1);
      case typ_GAL: return gal_get_pol(x);
      case typ_RNF: return gmael(x,11,1);
    }
    if (typ(x)==t_POLMOD) return gel(x,2);
    if (typ(x)==t_FFELT) return FF_to_FpXQ(x);
    member_err("pol");
  }
  return nf_get_pol(y);
}

GEN
member_mod(GEN x) /* modulus */
{
  long t; (void)get_nf(x,&t);
  switch(t) {
    case typ_GAL: return gal_get_mod(x);
    case typ_BNR: return bnr_get_mod(x);
    case typ_BID: return gel(x,1);
  }
  switch(typ(x))
  {
    case t_INTMOD: case t_POLMOD: case t_QUAD: break;
    case t_PADIC: return gel(x,3);
    case t_FFELT: return FF_mod(x);
    default: member_err("mod");
  }
  return gel(x,1);
}

GEN
member_sign(GEN x) /* signature */
{
  long t; GEN y = get_nf(x,&t);
  if (!y) member_err("sign");
  return gel(y,2);
}
GEN
member_r1(GEN x) { return gel(member_sign(x), 1); }
GEN
member_r2(GEN x) { return gel(member_sign(x), 2); }

GEN
member_index(GEN x)
{
  long t; GEN y = get_nf(x,&t);
  if (!y) member_err("index");
  return nf_get_index(y);
}

/* x assumed to be output by get_nf: ie a t_VEC with length 11 */
static GEN
nfmats(GEN x)
{
  GEN y;
  if (!x) return NULL;
  y = gel(x,5);
  if (typ(y) == t_VEC && lg(y) != 8) return NULL;
  return y;
}

GEN
member_t2(GEN x) /* T2 matrix */
{
  long t; x = nfmats(get_nf(x,&t));
  if (!x) member_err("t2");
  return gram_matrix(gel(x,2));
}

GEN
member_diff(GEN x) /* different */
{
  long t; x = nfmats(get_nf(x,&t));
  if (!x) member_err("diff");
  return gel(x,5);
}

GEN
member_codiff(GEN x) /* codifferent */
{
  long t; GEN T, D, DinvT, nf = get_nf(x,&t), y = nfmats(nf);
  if (!y) member_err("codiff");
  T = gel(y,4);
  D = absi(nf_get_disc(nf));
  DinvT = ZM_inv(T,D);
  return gdiv(ZM_hnfmod(DinvT, D), D);
}

GEN
member_roots(GEN x) /* roots */
{
  long t; GEN y = get_nf(x,&t);
  if (!y)
  {
    if (t == typ_ELL && is_ell(x)) return ell_get_roots(x);
    if (t == typ_GAL) return gal_get_roots(x);
    member_err("roots");
  }
  return nf_get_roots(y);
}

/* assume x output by get_bnf: ie a t_VEC with length 10 */
static GEN
check_RES(GEN x, const char *s)
{
  GEN y = gel(x,8);
  if (typ(y) != t_VEC || lg(y) < 4) member_err(s);
  return y;
}

GEN
member_clgp(GEN x) /* class group (3-component row vector) */
{
  long t; GEN y = get_bnf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_QUA: return mkvec3(gel(x,1), gel(x,2), gel(x,3));
      case typ_BID: return gel(x,2);
    }
    if (typ(x)==t_VEC)
      switch(lg(x))
      {
        case 3: /* no gen */
        case 4: return x;
      }
    member_err("clgp");
  }
  if (t==typ_BNR) return gel(x,5);
  y = check_RES(y, "clgp");
  return gel(y,1);
}

GEN
member_reg(GEN x) /* regulator */
{
  long t; GEN y = get_bnf(x,&t);
  if (!y)
  {
    if (t == typ_QUA) return gel(x,4);
    member_err("reg");
  }
  if (t == typ_BNR) pari_err(impl,"ray regulator");
  y = check_RES(y, "reg");
  return gel(y,2);
}

GEN
member_fu(GEN x) /* fundamental units */
{
  long t; GEN y = get_bnf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_Q:
        x = quad_disc(x);
        return (signe(x)<0)? cgetg(1,t_VEC): quadunit(x);
    }
    member_err("fu");
  }
  if (t == typ_BNR) pari_err(impl,"ray units");
  return matbasistoalg(y, bnf_get_fu(y));
}

/* torsion units. return [w,e] where w is the number of roots of 1, and e a
 * polymod generator */
GEN
member_tu(GEN x)
{
  long t; GEN bnf = get_bnf(x,&t), res = cgetg(3,t_VEC);
  if (!bnf)
  {
    GEN y;
    if (t != typ_Q) member_err("tu");
    y = quad_disc(x);
    if (signe(y) > 0 || cmpiu(y,4) > 0) return mkvec2(gen_m1, gen_2);

    gel(res,1) = utoipos((itos(y) == -4)? 4: 6);
    gel(res,2) = gcopy(x);
  }
  else
  {
    if (t == typ_BNR) pari_err(impl,"ray torsion units");
    gel(res,1) = utoipos( bnf_get_tuN(bnf) );
    gel(res,2) = basistoalg(bnf, bnf_get_tuU(bnf));
  }
  return res;
}

GEN
member_futu(GEN x) /*  concatenation of fu and tu, w is lost */
{
  return shallowconcat(member_fu(x), gel(member_tu(x),2));
}

GEN
member_tufu(GEN x) /*  concatenation of tu and fu, w is lost */
{
  return shallowconcat(gel(member_tu(x),2), member_fu(x));
}

/* structure of (Z_K/m)^*, where x is an idealstarinit (with or without gen)
 * or a bnrinit (with or without gen) */
GEN
member_zkst(GEN x)
{
  long t; (void)get_nf(x,&t);
  switch(t)
  {
    case typ_BID: return gel(x,2);
    case typ_BNR: {
      GEN bid = bnr_get_bid(x);
      if (typ(bid) == t_VEC && lg(bid) > 2) return gel(bid,2);
    }
  }
  member_err("zkst");
  return NULL; /* not reached */
}

GEN
member_no(GEN clg) /* number of elements of a group (of type clgp) */
{
  pari_sp av = avma;
  clg = member_clgp(clg);
  if (typ(clg)!=t_VEC || (lg(clg)!=3 && lg(clg)!=4)) member_err("no");
  avma = av; return gel(clg,1);
}

GEN
member_cyc(GEN clg) /* cyclic decomposition (SNF) of a group (of type clgp) */
{
  pari_sp av = avma;
  clg = member_clgp(clg);
  if (typ(clg)!=t_VEC || (lg(clg)!=3 && lg(clg)!=4)) member_err("cyc");
  avma = av; return gel(clg,2);
}

/* SNF generators of a group (of type clgp), or generators of a prime
 * ideal */
GEN
member_gen(GEN x)
{
  pari_sp av;
  long t;
  GEN y = get_prid(x);
  if (y) return mkvec2(gel(y,1), gel(y,2));
  (void)get_nf(x,&t);
  if (t == typ_GAL) return gal_get_gen(x);
  av = avma;
  x = member_clgp(x);
  if (typ(x)!=t_VEC || lg(x)!=4) member_err("gen");
  avma = av;
  if (typ(x[1]) == t_COL) return gel(x,2); /* from bnfisprincipal */
  return gel(x,3);
}
GEN
member_group(GEN x)
{
  long t; (void)get_nf(x,&t);
  if (t == typ_GAL) return gal_get_group(x);
  member_err("group");
  return NULL; /* not reached */
}
GEN
member_orders(GEN x)
{
  long t; (void)get_nf(x,&t);
  if (t == typ_GAL) return gal_get_orders(x);
  member_err("orders");
  return NULL; /* not reached */
}

GEN
member_a1(GEN x)
{
  if (!is_ell5(x)) member_err("a1");
  return ell_get_a1(x);
}

GEN
member_a2(GEN x)
{
  if (!is_ell5(x)) member_err("a2");
  return ell_get_a2(x);
}

GEN
member_a3(GEN x)
{
  if (!is_ell5(x)) member_err("a3");
  return ell_get_a3(x);
}

GEN
member_a4(GEN x)
{
  if (!is_ell5(x)) member_err("a4");
  return ell_get_a4(x);
}

GEN
member_a6(GEN x)
{
  if (!is_ell5(x)) member_err("a6");
  return ell_get_a6(x);
}

GEN
member_b2(GEN x)
{
  if (!is_smallell(x)) member_err("b2");
  return ell_get_b2(x);
}

GEN
member_b4(GEN x)
{
  if (!is_smallell(x)) member_err("b4");
  return ell_get_b4(x);
}

GEN
member_b6(GEN x)
{
  if (!is_smallell(x)) member_err("b6");
  return ell_get_b6(x);
}

GEN
member_b8(GEN x)
{
  if (!is_smallell(x)) member_err("b8");
  return ell_get_b8(x);
}

GEN
member_c4(GEN x)
{
  if (!is_smallell(x)) member_err("c4");
  return ell_get_c4(x);
}

GEN
member_c6(GEN x)
{
  if (!is_smallell(x)) member_err("c6");
  return ell_get_c6(x);
}

GEN
member_j(GEN x)
{
  if (!is_smallell(x)) member_err("j");
  return ell_get_j(x);
}

GEN
member_omega(GEN x)
{
  if (!is_ell(x)) member_err("omega");
  if (!ell_is_real(x)) pari_err(talker,"curve not defined over R");
  return mkvec2(gel(x,15), gel(x,16));
}

GEN
member_eta(GEN x)
{
  if (!is_ell(x)) member_err("eta");
  if (!ell_is_real(x)) pari_err(talker,"curve not defined over R");
  return mkvec2(gel(x,17), gel(x,18));
}

GEN
member_area(GEN x)
{
  if (!is_ell(x)) member_err("area");
  if (!ell_is_real(x)) pari_err(talker,"curve not defined over R");
  return gel(x,19);
}

GEN
member_tate(GEN x)
{
  if (!is_ell(x)) member_err("tate");
  if (!ell_is_padic(x))
    pari_err(talker,"curve not defined over a p-adic field");
  return mkvec3(gel(x,15), gel(x,16), gel(x,17));
}

GEN
member_w(GEN x)
{
  if (!is_ell(x)) member_err("w");
  if (!ell_is_padic(x))
    pari_err(talker,"curve not defined over a p-adic field");
  return gel(x,18);
}
