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
/*                          CONCATENATION                          */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

/* assume A or B is a t_LIST */
static GEN
listconcat(GEN A, GEN B)
{
  long i, l1, lx;
  GEN L, z, L1, L2;

  if (typ(A) != t_LIST) {
    L2 = list_data(B);
    if (!L2) return mklistcopy(A);
    lx = lg(L2) + 1;
    z = listcreate();
    list_data(z) = L = cgetg(lx, t_VEC);
    for (i = 2; i < lx; i++) gel(L,i) = gcopy(gel(L2,i-1));
    gel(L,1) = gcopy(A); return z;
  } else if (typ(B) != t_LIST) {
    L1 = list_data(A);
    if (!L1) return mklistcopy(B);
    lx = lg(L1) + 1;
    z = listcreate();
    list_data(z) = L = cgetg(lx, t_VEC);
    for (i = 1; i < lx-1; i++) gel(L,i) = gcopy(gel(L1,i));
    gel(L,i) = gcopy(B); return z;
  }
  /* A, B both t_LISTs */
  L1 = list_data(A); if (!L1) return listcopy(B);
  L2 = list_data(B); if (!L2) return listcopy(A);

  l1 = lg(L1);
  lx = l1-1 + lg(L2);
  z = cgetg(3, t_LIST);
  list_nmax(z) = 0;
  list_data(z) = L = cgetg(lx, t_VEC);
  L2 -= l1-1;
  for (i=1; i<l1; i++) gel(L,i) = gclone(gel(L1,i));
  for (   ; i<lx; i++) gel(L,i) = gclone(gel(L2,i));
  return z;
}

/* assume A or B is a t_STR */
static GEN
strconcat(GEN x, GEN y)
{
  int flx = 0, fly = 0;
  size_t l, lx;
  char *sx,*sy,*str;

  if (typ(x)==t_STR) sx = GSTR(x); else { flx=1; sx = GENtostr(x); }
  if (typ(y)==t_STR) sy = GSTR(y); else { fly=1; sy = GENtostr(y); }
  lx = strlen(sx);
  l = nchar2nlong(lx + strlen(sy) + 1);
  x = cgetg(l + 1, t_STR); str = GSTR(x);
  strcpy(str,   sx);
  strcpy(str+lx,sy);
  if (flx) pari_free(sx);
  if (fly) pari_free(sy);
  return x;
}

/* concat A and B vertically. Internal */
GEN
vconcat(GEN A, GEN B)
{
  long la, ha, hb, hc, i, j, T;
  GEN M, a, b, c;

  if (!A) return B;
  if (!B) return A;
  la = lg(A); if (la==1) return A;
  T = typ(A[1]); /* t_COL or t_VECSMALL */
  ha = lg(A[1]); M = cgetg(la,t_MAT);
  hb = lg(B[1]); hc = ha+hb-1;
  for (j=1; j<la; j++)
  {
    c = cgetg(hc, T); gel(M, j) = c;
    a = gel(A,j);
    b = gel(B,j);
    for (i=1; i<ha; i++) *++c = *++a;
    for (i=1; i<hb; i++) *++c = *++b;
  }
  return M;
}

static void
err_cat(GEN x, GEN y)
{
  pari_err(talker,"impossible concatenation: %s %Ps . %s %Ps",
      type_name(typ(x)), matsize(x), type_name(typ(y)), matsize(y));
}

GEN
shallowconcat(GEN x, GEN y)
{
  long tx=typ(x),ty=typ(y),lx=lg(x),ly=lg(y),i;
  GEN z,p1;

  if (tx==t_STR  || ty==t_STR)  return strconcat(x,y);
  if (tx==t_LIST || ty==t_LIST) return listconcat(x,y);

  if (tx==t_MAT && lx==1)
  {
    if (ty!=t_VEC) return gtomat(y);
    if (ly==1) return cgetg(1, t_MAT);
    err_cat(x,y);
  }
  if (ty==t_MAT && ly==1)
  {
    if (tx!=t_VEC) return gtomat(x);
    if (lx==1) return cgetg(1, t_MAT);
    err_cat(x,y);
  }

  if (tx == ty)
  {
    if (tx == t_MAT)
    { if (lg(x[1]) != lg(y[1])) err_cat(x,y); }
    else
      if (!is_matvec_t(tx) && tx != t_VECSMALL) return mkvec2(x, y);
    z=cgetg(lx+ly-1,tx);
    for (i=1; i<lx; i++) z[i]     = x[i];
    for (i=1; i<ly; i++) z[lx+i-1]= y[i];
    return z;
  }

  if (! is_matvec_t(tx))
  {
    if (! is_matvec_t(ty)) return mkvec2(x, y);
    z=cgetg(ly+1,ty);
    if (ty != t_MAT) p1 = x;
    else
    {
      if (lg(y[1])!=2) err_cat(x,y);
      p1 = mkcol(x);
    }
    for (i=2; i<=ly; i++) z[i] = y[i-1];
    gel(z, 1) = p1; return z;
  }
  if (! is_matvec_t(ty))
  {
    z=cgetg(lx+1,tx);
    if (tx != t_MAT) p1 = y;
    else
    {
      if (lg(x[1])!=2) err_cat(x,y);
      p1 = mkcol(y);
    }
    for (i=1; i<lx; i++) z[i]=x[i];
    gel(z, lx) = p1; return z;
  }

  switch(tx)
  {
    case t_VEC:
      switch(ty)
      {
        case t_COL:
          if (lx<=2) return (lx==1)? y: shallowconcat(gel(x,1),y);
          if (ly>=3) break;
          return (ly==1)? x: shallowconcat(x,gel(y,1));
        case t_MAT:
          z=cgetg(ly,t_MAT); if (lx != ly) break;
          for (i=1; i<ly; i++) gel(z,i) = shallowconcat(gel(x,i),gel(y,i));
          return z;
      }
      break;

    case t_COL:
      switch(ty)
      {
        case t_VEC:
          if (lx<=2) return (lx==1)? y: shallowconcat(gel(x,1), y);
          if (ly>=3) break;
          return (ly==1)? x: shallowconcat(x, gel(y,1));
        case t_MAT:
          if (lx != lg(y[1])) break;
          z=cgetg(ly+1,t_MAT); gel(z,1) = x;
          for (i=2; i<=ly; i++) z[i]=y[i-1];
          return z;
      }
      break;

    case t_MAT:
      switch(ty)
      {
        case t_VEC:
          z=cgetg(lx, t_MAT); if (ly != lx) break;
          for (i=1; i<lx; i++) gel(z,i) = shallowconcat(gel(x,i), gel(y,i));
          return z;
        case t_COL:
          if (ly != lg(x[1])) break;
          z=cgetg(lx+1,t_MAT); gel(z,lx) = y;
          for (i=1; i<lx; i++) z[i]=x[i];
          return z;
      }
      break;
  }
  err_cat(x,y);
  return NULL; /* not reached */
}

/* see catmany() */
static GEN
catmanyMAT(GEN y1, GEN y2)
{
  long i, h = 0, L = 1;
  GEN z, y;
  for (y = y2; y >= y1; y--)
  {
    GEN c = gel(y,0);
    long nc = lg(c)-1;
    if (nc == 0) continue;
    if (h != lg(c[1]))
    {
      if (h) err_cat(gel(y2,0), c);
      h = lg(c[1]);
    }
    L += nc;
    z = new_chunk(nc) - 1;
    for (i=1; i<=nc; i++) z[i] = c[i];
  }
  z = new_chunk(1);
  *z = evaltyp(t_MAT) | evallg(L);
  return z;
}
/* see catmany() */
static GEN
catmanySTR(GEN y1, GEN y2)
{
  long i, L = 1;
  GEN z, y;
  char *s, *S = (char*)avma;
  pari_sp av = avma;
  (void)new_chunk(1); *--S = 0;
  for (y = y2; y >= y1; y--)
  {
    char *c = GSTR( gel(y,0) );
    long nc = strlen(c);
    if (nc == 0) continue;
    L += nc; c += nc;
    (void)new_chunk(nchar2nlong(nc));
    for (i=1; i<=nc; i++) *--S = *--c;
  }
  avma = av;
  z = cgetg(nchar2nlong(L) + 1, t_STR);
  s = GSTR(z);
  if (S != s) { for (i = 0; i <= L; i++) *s++ = *S++; }
  return z;
}

/* all entries in y have the same type t = t_VEC, COL, MAT or VECSMALL
 * concatenate y[k1..k2], with yi = y + ki, k1 <= k2 */
static GEN
catmany(GEN y1, GEN y2, long t)
{
  long i, L;
  GEN z, y;
  if (y1 == y2) return gel(y1,0);
  if (t == t_MAT) return catmanyMAT(y1, y2);
  if (t == t_STR) return catmanySTR(y1, y2);
  L = 1;
  for (y = y2; y >= y1; y--)
  {
    GEN c = gel(y,0);
    long nc = lg(c)-1;
    if (nc == 0) continue;
    L += nc;
    z = new_chunk(nc) - 1;
    for (i=1; i<=nc; i++) z[i] = c[i];
  }
  z = new_chunk(1);
  *z = evaltyp(t) | evallg(L);
  return z;
}

GEN
shallowconcat1(GEN x)
{
  pari_sp av = avma, lim = stack_lim(av, 3);
  long tx = typ(x), lx, t, i;
  GEN z;

  if      (tx == t_VEC) lx = lg(x);
  else if (tx == t_LIST)
  { x = list_data(x); lx = x ? lg(x): 1; }
  else
  { pari_err(typeer,"concat"); return NULL; /* not reached */ }
  if (lx==1) pari_err(talker,"trying to concat elements of an empty vector");
  if (lx==2) return gel(x,1);

  z = gel(x,1);
  t = typ(z);
  i = 2;
  if (is_matvec_t(t) || t == t_VECSMALL || t == t_STR)
  { /* detect a "homogeneous" object: catmany is faster */
    for (; i<lx; i++)
      if (typ(gel(x,i)) != t) break;
    z = catmany(x + 1, x + i-1, t);
  }
  for (; i<lx; i++) {
    z = shallowconcat(z, gel(x,i));
    if (low_stack(lim, stack_lim(av,3)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"concat: i = %ld", i);
      z = gerepilecopy(av, z);
    }
  }
  return z;
}

GEN
concat1(GEN x)
{
  pari_sp av = avma;
  return gerepilecopy(av, shallowconcat1(x));
}

GEN
concat(GEN x, GEN y)
{
  long tx, lx,ty,ly,i;
  GEN z,p1;

  if (!y) return concat1(x);
  tx = typ(x);
  ty = typ(y);
  if (tx==t_STR  || ty==t_STR)  return strconcat(x,y);
  if (tx==t_LIST || ty==t_LIST) return listconcat(x,y);
  lx=lg(x); ly=lg(y);

  if (tx==t_MAT && lx==1)
  {
    if (ty!=t_VEC) return gtomat(y);
    if (ly==1) return cgetg(1, t_MAT);
    err_cat(x,y);
  }
  if (ty==t_MAT && ly==1)
  {
    if (tx!=t_VEC) return gtomat(x);
    if (lx==1) return cgetg(1, t_MAT);
    err_cat(x,y);
  }

  if (tx == ty)
  {
    if (tx == t_MAT && lg(x[1]) != lg(y[1])) err_cat(x,y);
    if (!is_matvec_t(tx))
    {
      if (tx != t_VECSMALL) return mkvec2copy(x, y);
      z = cgetg(lx+ly-1,t_VECSMALL);
      for (i=1; i<lx; i++) z[i]     = x[i];
      for (i=1; i<ly; i++) z[lx+i-1]= y[i];
      return z;
    }
    z=cgetg(lx+ly-1,tx);
    for (i=1; i<lx; i++) gel(z,i)     = gcopy(gel(x,i));
    for (i=1; i<ly; i++) gel(z,lx+i-1)= gcopy(gel(y,i));
    return z;
  }

  if (! is_matvec_t(tx))
  {
    if (! is_matvec_t(ty)) return mkvec2copy(x, y);
    z=cgetg(ly+1,ty);
    if (ty != t_MAT) p1 = gcopy(x);
    else
    {
      if (lg(y[1])!=2) err_cat(x,y);
      p1 = mkcolcopy(x);
    }
    for (i=2; i<=ly; i++) gel(z,i) = gcopy(gel(y,i-1));
    gel(z,1) = p1; return z;
  }
  if (! is_matvec_t(ty))
  {
    z=cgetg(lx+1,tx);
    if (tx != t_MAT) p1 = gcopy(y);
    else
    {
      if (lg(x[1])!=2) err_cat(x,y);
      p1 = mkcolcopy(y);
    }
    for (i=1; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
    gel(z,lx) = p1; return z;
  }

  switch(tx)
  {
    case t_VEC:
      switch(ty)
      {
        case t_COL:
          if (lx<=2) return (lx==1)? gcopy(y): concat(gel(x,1),y);
          if (ly>=3) break;
          return (ly==1)? gcopy(x): concat(x,gel(y,1));
        case t_MAT:
          z=cgetg(ly,t_MAT); if (lx != ly) break;
          for (i=1; i<ly; i++) gel(z,i) = concat(gel(x,i),gel(y,i));
          return z;
      }
      break;

    case t_COL:
      switch(ty)
      {
        case t_VEC:
          if (lx<=2) return (lx==1)? gcopy(y): concat(gel(x,1),y);
          if (ly>=3) break;
          return (ly==1)? gcopy(x): concat(x,gel(y,1));
        case t_MAT:
          if (lx != lg(y[1])) break;
          z=cgetg(ly+1,t_MAT); gel(z,1) = gcopy(x);
          for (i=2; i<=ly; i++) gel(z,i) = gcopy(gel(y,i-1));
          return z;
      }
      break;

    case t_MAT:
      switch(ty)
      {
        case t_VEC:
          z=cgetg(lx,t_MAT); if (ly != lx) break;
          for (i=1; i<lx; i++) gel(z,i) = concat(gel(x,i),gel(y,i));
          return z;
        case t_COL:
          if (ly != lg(x[1])) break;
          z=cgetg(lx+1,t_MAT); gel(z,lx) = gcopy(y);
          for (i=1; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
          return z;
      }
      break;
  }
  err_cat(x,y);
  return NULL; /* not reached */
}
