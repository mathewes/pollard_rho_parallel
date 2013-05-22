/* > ecdlp-89.c
 * Purpose: Some tools for arithmetic on elliptic curves.
 * Copyright: Robert J. Harley, 03-Feb-1997
 * Contact: Robert.Harley@inria.fr
 * Legalese: You can do what you want with this code as long as this
 *           comment stays attached in a prominent position in
 *           human-readable form, any distribution of this or
 *           derived products is made without profit and includes
 *           full source and is subject to the same conditions.
 */

/* Compile with something like:
 *   gcc -O4 ecdlp-89.c -o ecdl -DFROM=somebody@somewhere
 * or:
 *   cc -O5 -tune host -std1 ecdlp-89.c -o ecdl -DFROM=somebody@somewhere
 *
 * Replace "somebody@somewhere" with your email address, unless you prefer
 * to remain anonymous.
 *
 * Append one of the following flags:
 *
 *   If your machine is permanently connected to the Net:
 *     -DTO=ecdl@pauillac.inria.fr
 *
 *   If it is connected but email to INRIA bounces, try this instead:
 *     -DTO=robert@vlsi.cs.caltech.edu
 *
 *   If it is not connected, or email won't get through, use batch mode:
 *     -DBATCH
 *
 *   In batch mode, you should send the output "by hand" via email to one
 *   of the addresses, ideally from a machine with ptr and mx DNS records.
 *
 * (NB: if you compile on Digital Unix with -non_shared and run on Linux
 *      then use batch mode, since otherwise the compiled program will
 *      look for /sbin/sh whereas Linux has /bin/sh instead.)
 */

/*#ifndef __alpha
#error Use an Alpha!
#endif*/


/*== #includes =============================================================*/

/** Ansi includes. **/
#include <stdio.h>
#include <stdlib.h>

/** Unix includes. **/
/* For getpid(). */
#include <unistd.h>
/* For pclose() status. */
#include <sysexits.h>
/* Timing. */
#include <sys/time.h>
#include <sys/resource.h>
#include <time.h>
/** System-specific includes. **/
#ifdef __DECC
#include <c_asm.h>
#endif


/*== Types =================================================================*/

typedef unsigned u32;
typedef unsigned long u64;
typedef struct { u64 hi, lo; } u128;


/*== #defines ==============================================================*/



/* Version 1.02: December 31th 1997
 * - Replaced u128 consts with u64 consts in squareMod() and productMod().
 * - Does 386K/sec with "gcc -O4" on Alpha Linux on 500Mhz PWS
 *
 * Version 1.01: December 30th 1997
 * - Replaced some parameters that are always the same with constants.
 * - Reordered functions to reduce I-cache conflicts.
 * - Does 360K/sec with "gcc -O4" on Alpha Linux on 500Mhz PWS
 *
 * Version 1.00: December 18th 1997
 * - Does 344K/sec with "gcc -O4" on Alpha Linux on 500Mhz PWS
 */
#define CLIENT "RobsECDL"
#define VERSION "102"


#ifdef __GNUC__

#define INLINE inline
/*static inline u64 HiMul(u64 m0, u64 m1) {
  unsigned long tmp;

  asm("umulh %r1,%2,%0" : "=r" (tmp) : "%rJ" (m0), "rI" (m1));

  return tmp;
}*/ /* end HiMul */
static inline u64 HiMul(u64 mo,u64 ml){
  return (int64_t)((__int128_t)mo*ml >> 64);
}
#else

#ifdef __DECC

/* Digital's cc. */
#define INLINE
#define HiMul(m0, m1) asm("umulh %a0, %a1, %v0", m0, m1)

#else

#error Weird compiler, dude!  Write code here.

#endif

#endif


#define STR(x) #x
#define STRINGIFY(x) STR(x)



/** Curve from Certicom ECCp-89. **/
/* mod = 416363315556156604917983573
 * a   = 134463312896805761244606051 (3881733152902215205506458208 % mod)
 * b   = 121489936031066440060440631
 * x1  = 232349146313044524685417226
 * y1  =   8425515734129553132973322
 * x2  = 268507436745473388067569197
 * y2  =  51099634945595802171100073
 * ord = 416363315556124458285894983 (prime)
 */

/* The prime. */
#define MOD_HI (22571100UL)
#define MOD_LO (10394050944438085973UL)
#define MOD { MOD_HI, MOD_LO }

/* 1/mod modulo 2^96. */
#define INV_HI (410366702UL)
#define INV_LO (13789780428223613949UL)
#define INV { INV_HI, INV_LO }

/* 2^96 modulo mod = encoded 1. */
#define ONE  {  6458188UL, 17378680517395239658UL }

/* 2^192 modulo mod. */
#define CODE {  6753051UL, 15968640992227210721UL }

/* Group order */
#define ORD  { 22571100UL, 10394018797805997383UL }

/* These get encoded. */
#define A    {  7289270UL, 14722636937936645731UL }
#define B    {  6585982UL, 11603008659889393719UL }
#define X1   { 12595672UL,  8492655189263211274UL }
#define Y1   {   456748UL,  2271950862851468554UL }
#define X2   { 14555817UL,  5762722643593018925UL }
#define Y2   {  2770116UL, 14039107793886792617UL }


/*== Function declarations =================================================*/

static INLINE u64 equal(u128 x, u128 y);
static INLINE u128 sumMod(u128 x, u128 y, u128 mod);
static INLINE u128 diffMod(u128 x, u128 y, u128 mod);
static INLINE u128 doubleMod(u128 x, u128 mod);

static INLINE u128 encode(u128 x);
static u128 decode(u128 x);
static u128 inverseMod(u128 y);
static INLINE u128 quotientMod(u128 x, u128 y);
static u128 squareMod(u128 x);
static u128 productMod(u128 x, u128 y);

static int ellipticSum
  ( u128 x1, u128 y1, u128 x2, u128 y2, u128 a
  , u128 *px3, u128 *py3
  );
static int ellipticDouble
  ( u128 x, u128 y, u128 a, u128 *px2, u128 *py2
  );
static int ellipticProduct
  ( u128 x, u128 y, u128 fac, u128 a, u128 *px2, u128 *py2
  );

static int ellipticProductSum
  ( u128 x1, u128 y1, u128 fac1, u128 x2, u128 y2, u128 fac2, u128 a, u128 *px2, u128 *py2
  );


/*== Function definitions ==================================================*/

/*== Some simple modular arithmetic ========================================*/

/*-- equal -----------------------------------------------------------------*/

/* Check equality: x == y, 0 <= x, y < some modulus < 2^96. */
static INLINE u64 equal(u128 x, u128 y) {
  u64 xh,xl, yh,yl;

  xh = x.hi; xl = x.lo;
  yh = y.hi; yl = y.lo;

  return ((xh ^ yh) | (xl ^ yl)) == 0UL;
} /* end equal */


/*-- sumMod ----------------------------------------------------------------*/

/* Add: x + y modulo modulus, 0 <= x, y < modulus < 2^96. */
static INLINE u128 sumMod(u128 x, u128 y, u128 mod) {
  u64 c, mh,ml, xh,xl, yh,yl;
  u128 z;

  xh = x.hi; xl = x.lo;
  yh = y.hi; yl = y.lo;
  xh += yh; xl += yl; xh += xl < yl;

  mh = mod.hi; ml = mod.lo;
  if (xh > mh || (xh == mh && xl >= ml)) {
    xh -= mh; c = xl < ml; xl -= ml; xh -= c;
  } /* end if */

  z.hi = xh; z.lo = xl;
  return z;
} /* end sumMod */


/*-- diffMod ---------------------------------------------------------------*/

/* Subtract: x - y modulo modulus, 0 <= x, y < modulus < 2^96. */
static INLINE u128 diffMod(u128 x, u128 y, u128 mod) {
  u64 c, mh,ml, xh,xl, yh,yl;
  u128 z;

  xh = x.hi; xl = x.lo;
  yh = y.hi; yl = y.lo;
  if (xh < yh || (xh == yh && xl < yl)) {
    mh = mod.hi; ml = mod.lo;
    xh += mh; xl += ml; xh += xl < ml;
  } /* end if */
  xh -= yh; c = xl < yl; xl -= yl; xh -= c;

  z.hi = xh; z.lo = xl;
  return z;
} /* end diffMod */


/*-- doubleMod -------------------------------------------------------------*/

/* Double x modulo odd modulus, 0 <= x < modulus < 2^96. */
static INLINE u128 doubleMod(u128 x, u128 mod) {
  u64 c, mh,ml, xh,xl;
  u128 y;

  xh = x.hi; xl = x.lo;
  mh = mod.hi; ml = mod.lo;

  xh <<= 1; xh |= xl>>63; xl <<= 1;
  if (xh > mh || (xh == mh && xl >= ml)) {
    xh -= mh; c = xl < ml; xl -= ml; xh -= c;
  } /* end if */

  y.hi = xh; y.lo = xl;
  return y;
} /* end doubleMod */


/*== Arithmetic for field Z/pZ, p odd, using 2-adic inverse ================*/

/*-- encode ----------------------------------------------------------------*/

/* Encode x modulo odd modulus, 0 <= x < modulus < 2^96.
 * Point coordinates are encoded by multiplying by 2^96 modulo the prime
 * so that we can multiply modulo the prime quickly using a precomputed
 * 2-adic inverse (as described by Peter Montgomery).
 */
static INLINE u128 encode(u128 x) {
  const u128 code = CODE;

  return productMod(x, code);
} /* end encode */


/*-- decode ----------------------------------------------------------------*/

/* Decode x modulo odd modulus, 0 <= x < modulus < 2^96. */
static u128 decode(u128 x) {
  u64 ih,il, mh,ml, ph,pm, qh,ql, t, uh,ul, vh,vl, xh,xl;
  u128 z;
  const u128 mod = MOD, inv = INV;

  xh = x.hi; xl = x.lo;
  ih = inv.hi; il = inv.lo;

  qh = HiMul(il, xl)+il*xh+ih*xl; qh &= 0xffffffffUL;
  ql = il*xl;

  mh = mod.hi; ml = mod.lo;
  pm = HiMul(ql, ml);
  ph = qh*mh+HiMul(qh, ml)+HiMul(ql, mh);
  t = qh*ml; pm += t; ph += pm < t;
  t = ql*mh; pm += t; ph += pm < t;

  ul = pm>>32 | ph<<32; uh = ph>>32;

  vh = vl = 0UL;
  if (uh | ul) { vh = mh-uh; vl = ml-ul; vh -= ml < ul;}

  z.hi = vh; z.lo = vl;
  return z;
} /* end decode */


/*-- inverseMod ------------------------------------------------------------*/

/* Divide 1 by y modulo odd modulus, 0 <= y < modulus < 2^96, y != 0.
 * Input must be encoded and output is too.
 */

#define TAB_SIZE (64UL)
#define TAB_MASK (TAB_SIZE-1UL)

static u128 inverseMod(u128 y) {
  u64 ah,al, bh,bl, c, sh,th, t, uh,ul, vh,vl;
  static const int tab[TAB_SIZE] =
  { 6,0,1,0,2,0,1,0,3,0,1,0,2,0,1,0,4,0,1,0,2,0,1,0,3,0,1,0,2,0,1,0
  , 5,0,1,0,2,0,1,0,3,0,1,0,2,0,1,0,4,0,1,0,2,0,1,0,3,0,1,0,2,0,1,0
  };
  const u128 mod = MOD;

  y = decode(y);

  /* Maintain: u.y = a<<t and v.y = -b<<t. */

  ah = y.hi; al = y.lo;
  t = 0UL;
  while (!(al & 1UL)) {
    al >>= 1; al |= ah<<63; ah >>= 1;
    ++t;
  } /* end while */
  bh = mod.hi; bl = mod.lo;
  uh = 0UL; ul = 1UL;
  vh = 0UL; vl = 0UL;

  do {
    do {
      bh -= ah; c = bl < al; bl -= al; bh -= c;
      vh += uh; vl += ul; vh += vl < ul;

      sh = (u64)(long)tab[bl & TAB_MASK]; th = 64UL-sh;
      bl >>= sh; bl |= bh<<th; bh >>= sh;
      t += sh;
      uh <<= sh; uh |= ul>>th; ul <<= sh;
      while (!(bl & 1UL)) {
        bl >>= 1; bl |= bh<<63; bh >>= 1;
        ++t;
        uh <<= 1; uh |= ul>>63; ul <<= 1;
      } /* end while */
    } while (ah < bh || (ah == bh && al < bl));
    if (ah == bh && al == bl) break;
    do {
      ah -= bh; c = al < bl; al -= bl; ah -= c;
      uh += vh; ul += vl; uh += ul < vl;

      sh = (u64)(long)tab[al & TAB_MASK]; th = 64UL-sh;
      al >>= sh; al |= ah<<th; ah >>= sh;
      t += sh;
      vh <<= sh; vh |= vl>>th; vl <<= sh;
      while (!(al & 1UL)) {
        al >>= 1; al |= ah<<63; ah >>= 1;
        ++t;
        vh <<= 1; vh |= vl>>63; vl <<= 1;
      } /* end while */
    } while (ah > bh || (ah == bh && al > bl));
  } while (ah != bh || al != bl);

  /* TO DO: consider multiplying by constants from a table here. */
  if (t > 96UL) {
    u64 fh,fl;

    t -= 96UL;
    fl = mod.lo>>1 | mod.hi<<63; fh = mod.hi>>1;
    ++fl; fh += fl == 0UL;
    do {
      u64 o;

      o = ul & 1UL;
      ul >>= 1; ul |= uh<<63; uh >>= 1;
      if (o) { uh += fh; ul += fl; uh += ul < fl; }
      --t;
    } while (t);
  } else if (t < 96UL) {
    u64 mh,ml;

    t = 96UL-t;
    mh = mod.hi, ml = mod.lo;
    do {
      u64 c;

      uh <<= 1; uh |= ul>>63; ul <<= 1;
      if (uh > mh || (uh == mh && ul >= ml)) {
        uh -= mh; c = ul < ml; ul -= ml; uh -= c;
      } /* end if */
      --t;
    } while (t);
  } /* end if/else */

  { u128 u;
    u.hi = uh; u.lo = ul;
    return u;
  } /* end block */
} /* end inverseMod */


/*-- quotientMod -----------------------------------------------------------*/

/* Divide x by y modulo odd modulus, 0 <= x,y < modulus < 2^96, y != 0. */

static INLINE u128 quotientMod(u128 x, u128 y) {
  u128 z;

  z = inverseMod(y);

  return productMod(x, z);
} /* end quotientMod */


/*-- squareMod -------------------------------------------------------------*/

/* Square of x modulo odd modulus, 0 <= x < modulus < 2^96.
 * Input must be encoded and output is too.
 */
static u128 squareMod(u128 x) {
  u64 c, mh,ml, ph,pm,pl, rh,rl, t, uh,ul, vh,vl, xh,xl;
  u128 z;

  xh = x.hi; xl = x.lo;

  pl = xl*xl;
  pm = HiMul(xl, xl);
  ph = HiMul(xh, xl); t = xh*xl;
  ph = ph<<1 | t>>63; t <<= 1;
  pm += t; ph += pm < t;
  ph += xh*xh;

  ul = pl; uh = pm & 0xffffffffUL;
  vl = pm>>32 | ph<<32; vh = ph>>32;

  { u64 ih, il;

    ih = INV_HI; il = INV_LO;
    rh = HiMul(il, ul)+il*uh+ih*ul; rh &= 0xffffffffUL;
    rl = il*ul;
  } /* end block */

  mh = MOD_HI; ml = MOD_LO;

  /* Karatsuba. */
  { u64 c, qh,ql, sign, t, mm, rm;

    pl = ml*rl;
    pm = HiMul(ml, rl);
    ph = mh*rh;

    sign = ml < mh;
    mm = ml-mh; if (sign) mm = mh-ml;
    t = rl < rh; sign ^= t;
    rm = rl-rh; if (t) rm = rh-rl;

    ql = mm*rm; 
    qh = HiMul(mm, rm);
 
    if (sign) { ql += pl; c = ql < pl; qh += pm; qh += c; }
    else { c = pl < ql; ql = pl-ql; qh = pm-qh; qh -= c; }

    ql += ph; c = ql < ph; qh += c;

    pm += ql; c = pm < ql; ph += qh; ph += c;
  } /* end block */
  
  ul = pm>>32 | ph<<32; uh = ph>>32;

  if (vh < uh || (vh == uh && vl < ul)) { vh += mh; vl += ml; vh += vl < ml; }

  vh -= uh; c = vl < ul; vl -= ul; vh -= c;

  z.hi = vh; z.lo = vl;
  return z;
} /* end squareMod */


/*-- productMod ------------------------------------------------------------*/

/* Product of x and y modulo odd modulus, 0 <= x, y < modulus < 2^96.
 * Input must be encoded and output is too.
 */
static u128 productMod(u128 x, u128 y) {
  u64 c, mh,ml, ph,pm,pl, rh,rl, uh,ul, vh,vl, xh,xl, yh,yl;
  u128 z;

  xh = x.hi; xl = x.lo;
  yh = y.hi; yl = y.lo;

  /* Karatsuba. */
  { u64 c, qh,ql, sign, t, xm, ym;

    pl = xl*yl;
    pm = HiMul(xl, yl);
    ph = xh*yh;

    sign = xl < xh;
    xm = xl-xh; if (sign) xm = xh-xl;
    t = yl < yh; sign ^= t;
    ym = yl-yh; if (t) ym = yh-yl;

    ql = xm*ym; 
    qh = HiMul(xm, ym);
 
    if (sign) { ql += pl; c = ql < pl; qh += pm; qh += c; }
    else { c = pl < ql; ql = pl-ql; qh = pm-qh; qh -= c; }

    ql += ph; c = ql < ph; qh += c;

    pm += ql; c = pm < ql; ph += qh; ph += c;
  } /* end block */

  ul = pl; uh = pm & 0xffffffffUL;
  vl = pm>>32 | ph<<32; vh = ph>>32;

  { u64 ih, il;

    ih = INV_HI; il = INV_LO;
    rh = HiMul(il, ul)+il*uh+ih*ul; rh &= 0xffffffffUL;
    rl = il*ul;
  } /* end block */

  mh = MOD_HI; ml = MOD_LO;

  /* Karatsuba. */
  { u64 c, qh,ql, sign, t, mm, rm;

    pl = ml*rl;
    pm = HiMul(ml, rl);
    ph = mh*rh;

    sign = ml < mh;
    mm = ml-mh; if (sign) mm = mh-ml;
    t = rl < rh; sign ^= t;
    rm = rl-rh; if (t) rm = rh-rl;

    ql = mm*rm; 
    qh = HiMul(mm, rm);
 
    if (sign) { ql += pl; c = ql < pl; qh += pm; qh += c; }
    else { c = pl < ql; ql = pl-ql; qh = pm-qh; qh -= c; }

    ql += ph; c = ql < ph; qh += c;

    pm += ql; c = pm < ql; ph += qh; ph += c;
  } /* end block */

  ul = pm>>32 | ph<<32; uh = ph>>32;

  if (vh < uh || (vh == uh && vl < ul)) { vh += mh; vl += ml; vh += vl < ml; }

  vh -= uh; c = vl < ul; vl -= ul; vh -= c;

  z.hi = vh; z.lo = vl;
  return z;
} /* end productMod */


/*== Driver ================================================================*/

/*-- main ------------------------------------------------------------------*/

/* Number of iterations to run "in parallel".  This is done so that
 * PARAL inversions can be replaced by one inversion and 3*PARAL-3 mults.
 */
#define PARAL (32UL)

/* Do not change these. */
#define ADD_MASK (15UL)
#define ADDERS (15UL)
#ifdef TEST
#define POW_WRITE (20UL)
#else
#define POW_WRITE (30UL)
#endif

u128 getRandU128()
{
  u64 t1=rand(),t2=rand(),t3=rand(),t4=rand();
  u128 startv;
  startv.lo=(t1<<32 | t2);
  startv.hi=(t3<<32 | t4);
  return startv;
}
int main(int argc, char *argv[]) {
  const u128 mod = MOD, one = ONE, ord = ORD;
  u128 a = A, b = B, x1 = X1, y1 = Y1, x2 = X2, y2 = Y2;

  u64 i, sent, itersT[PARAL];

  u128 aR[ADDERS], bR[ADDERS], xR[ADDERS], yR[ADDERS];
  u128 cP, dP, xP, yP;

  puts("Getting curve...");

  puts("Getting initial points...");

  /** Choose PARAL random starting points. **/
  { u64 seed;
    FILE *handle;

    /* Get a fairly random seed. */
    handle = fopen("/dev/urandom", "r");
    if (handle != NULL) {
      fread((void *)&seed, sizeof(u64), 1UL, handle);
      fclose(handle);
    } /* end if */
    seed ^= (u64)getpid()<<32;
    seed ^= (u64)time(NULL);
    srand(seed);
    for (i = 0UL; i < PARAL; ++i) {
      aR[i]=getRandU128();bR[i]=getRandU128();
      ellipticProductSum(x1,y1,aR[i],x2,y2,bR[i],a,&xR[i],&yR[i]);
    } /* end for (i) */
    cP=getRandU128();dP=getRandU128();
    ellipticProductSum(x1,y1,cP,x2,y2,dP,a,&xP,&yP);
  } /* end block */


  puts("Computing iterations...");
  fflush(stdout);
  int num=1;int num2=0;
  /** Main loop. **/
  const clock_t begin_time = clock();
  for (; ; ) {
    if (xP.lo>>(64UL-POW_WRITE) == 0UL) {
    } /* end if */
    fflush(stdout);
    int flag= (xP.lo & ADDERS);
    ellipticSum(xP,yP,xR[flag],yR[flag],a,&xP,&yP);
    cP=sumMod(cP, aR[flag], mod);
    dP=sumMod(dP, bR[flag], mod);
    if(num%10000000==0)
      { 
        num=1;
        printf("%d %d s\n",num2,(int)(clock()-begin_time/CLOCKS_PER_SEC)/1000000);
        num2++;
      }
      else
        num++;
  } /* end forever */

  return 0;
} /* end main */

/*== Stuff for elliptic curve y^2 = x^3 + a*x + b ==========================*/

/*-- ellipticSum -----------------------------------------------------------*/

/* Given pts (x1:y1:z1) and (x2:y2:z2) on y^2 = x^3+a*x+b modulo odd modulus,
 * computes their sum by the group law.  Doesn't actually need b.
 * The point at infinity is represented by (0:1:0), with encoded 1.
 * Finite points are represented by (x:y:1), with encoded coordinates x and y.
 */
static int ellipticSum
  ( u128 x1, u128 y1, u128 x2, u128 y2
  , u128 a, u128 *px3, u128 *py3
  ) {
  u128 den, lam, num, s, x3, y3;
  const u128 mod = MOD;

  if (equal(x1, x2)) {
    const u128 one = ONE;

    if (equal(y1, y2)) return ellipticDouble(x1, y1, a, px3, py3);
    px3->hi = px3->lo = 0UL; *py3 = one; return 0;
  } /* end if */

  num = diffMod(y2, y1, mod);
  den = diffMod(x2, x1, mod);
  lam = quotientMod(num, den);

  x3 = squareMod(lam);
  x3 = diffMod(x3, x1, mod);
  x3 = diffMod(x3, x2, mod);

  s = diffMod(x1, x3, mod);
  y3 = productMod(lam, s);
  y3 = diffMod(y3, y1, mod);

  *px3 = x3; *py3 = y3; return 1;
} /* end ellipticSum */


/*-- ellipticDouble --------------------------------------------------------*/

/* Given point (x, y) on y^2 = x^3+a*x+b modulo odd modulus, this
 * computes its double by the group law.  Doesn't actually need b.
 * The point at infinity is represented by (0:1:0), with encoded 1.
 * Finite points are represented by (x:y:1), with encoded coordinates x and y.
 */
static int ellipticDouble
  ( u128 x, u128 y, u128 a, u128 *px2, u128 *py2
  ) {
  u128 den, lam, num, s, t, x2, y2;
  const u128 mod = MOD;

  if ((y.hi | y.lo) == 0UL) {
    const u128 one = ONE;

    px2->hi = px2->lo = 0UL; *py2 = one; return 0;
  } /* end if */

  num = squareMod(x);
  s = doubleMod(num, mod);
  num = sumMod(num, s, mod);
  num = sumMod(num, a, mod);

  den = doubleMod(y, mod);
  lam = quotientMod(num, den);

  x2 = squareMod(lam);
  t = doubleMod(x, mod);
  x2 = diffMod(x2, t, mod);

  s = diffMod(x, x2, mod);
  y2 = productMod(lam, s);
  y2 = diffMod(y2, y, mod);

  *px2 = x2; *py2 = y2; return 1;
} /* end ellipticDouble */


/*-- ellipticProduct -------------------------------------------------------*/

static int ellipticProduct
  ( u128 x, u128 y, u128 fac, u128 a, u128 *px2, u128 *py2
  ) {
  int z2;
  u64 fh, fl, m;
  u128 x2, y2;
  const u128 one = ONE;

  fh = fac.hi; fl = fac.lo;
  if ((fh | fl) == 0UL) { px2->hi = px2->lo = 0UL; *py2 = one; return 0; }

  if (fh) {
    x2 = x; y2 = y;
    m = fh;
    m |= m>>1; m |= m>>2; m |= m>>4; m |= m>>8; m |= m>>16; m |= m>>32;
    m ^= m>>1;
    while (m >>= 1) {
      /* Double */
      ellipticDouble(x2, y2, a, &x2, &y2);
      /* Increment */
      if (fh & m) ellipticSum(x, y, x2, y2, a, &x2, &y2);
    } /* end while */
  } else { x2.hi = x2.lo = 0UL; y2 = one;}

  m = 1UL<<63;
  do {
    /* Double */
    z2 = ellipticDouble(x2, y2, a, &x2, &y2);
    /* Increment */
    if (fl & m) z2 = ellipticSum(x, y, x2, y2, a, &x2, &y2);
    m >>= 1;
  } while (m);

  *px2 = x2; *py2 = y2; return z2;
} /* end ellipticProduct */

static int ellipticProductSum( u128 x1, u128 y1, u128 fac1, u128 x2, u128 y2, u128 fac2, u128 a, u128 *px2, u128 *py2
  ) 
{
  u128 tmp1,tmp2;
  ellipticProduct(x1,y1,fac1,a,&tmp1,&tmp2);
  u128 tmp3,tmp4;
  ellipticProduct(x2,y2,fac2,a,&tmp3,&tmp4);
  ellipticSum(tmp1,tmp2,tmp3,tmp4,a,&tmp1,&tmp2);
  return 1;
}
/*== end of file ecdlp-89.c ================================================*/
