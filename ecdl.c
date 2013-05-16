/* > ecdl.c
 * Purpose: Some tools for arithmetic on elliptic curves.
 * Copyright: Robert J. Harley, 03-Feb-1997
 * Contact: Robert.Harley@inria.fr
 * Legalese: You can do what you want with this code as long as this
 *           comment stays attached in a prominent position in
 *           human-readable form, any distribution of this or
 *           derived products is made without profit and includes
 *           full source and is subject to the same conditions.
 */

/* Compile with one of:

gcc -O4 ecdl.c f2Mul.s -o ecdl
cc -O5 -tune host -std1 ecdl.c f2Mul.s -o ecdl

 * or some similar incantation.  Add the flag -DBATCH for batch mode.
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
/* For timing. */
#include <sys/time.h>
#include <sys/resource.h>

/** System-specific includes. **/
#ifdef __DECC
#include <c_asm.h>
#endif


/*== Types =================================================================*/

typedef unsigned  u32;
typedef unsigned long u64;
typedef struct { u64 hi, lo; } u128;


/*== #defines ==============================================================*/

#ifdef __GNUC__
#define INLINE inline
#else
#ifdef __DECC
#define INLINE
#else
#error Weird compiler, dude!  Write code here.
#endif
#endif


/*== Function declarations =================================================*/

/* From f2Mul.s */
/* About 203 cycles. */
extern u64 f2Mul(u64 *ph, u64 a, u64 b);

/* From this file. */
static INLINE u64 equal(u128 x, u128 y);
static INLINE u128 sum(u128 x, u128 y);
static u64 f2MulLo(u64 a, u64 b);
static u128 product(u128 x, u128 y);
static u128 square(u128 x);
static u128 inverse(u128 y);
static u128 quotient(u128 x, u128 y);

static u64 ellipticDouble
  ( u128 x, u128 y, u64 z, u128 a
  , u128 *px2, u128 *py2
  );
static u64 ellipticSum
  ( u128 x1, u128 y1, u64 z1, u128 x2, u128 y2, u64 z2, u128 a
  , u128 *px3, u128 *py3
  );
static u64 ellipticProduct
  ( u128 x, u128 y, u64 z, u128 fac, u128 a
  , u128 *px2, u128 *py2
  );

static INLINE u128 incMod(u128 x, u128 mod);
static INLINE u128 doubleMod(u128 x, u128 mod);


/*== Function definitions ==================================================*/

/*== Stuff for field (Z/2Z)[u] / (Z/2Z)[1+u^9+u^79] ========================*/

/*-- equal -----------------------------------------------------------------*/

/* Check equality: x == y, where degree x, y < 128. */
static INLINE u64 equal(u128 x, u128 y) {

  return ((x.hi ^ y.hi) | (x.lo ^ y.lo)) == 0UL;
} /* end equal */


/*-- sum -------------------------------------------------------------------*/

/* Add: x + y, where degree x, y < 128. */
static INLINE u128 sum(u128 x, u128 y) {
  u128 z;

  z.hi = x.hi ^ y.hi; z.lo = x.lo ^ y.lo;

  return z;
} /* end sum */


/*-- f2MulLo ---------------------------------------------------------------*/

/* About 101 cycles (gcc), 101 (cc). */
static u64 f2MulLo(u64 a, u64 b) {
  u64 a0,a1,a2,a3,a01,a23,a02,a13,a0123
    , b0,b1,b2,b3,b01,b23,b02,b13,b0123
    , c0l,c1l,c2l,c3l,c01l,c23l,c02l,c13l,c0123l
    ;
  const u64 mask = 0x1111111111111111UL;

  a0 = a&mask; a1 = (a>>1)&mask; a2 = (a>>2)&mask; a3 = (a>>3)&mask;
  a01 = a0^a1; a23 = a2^a3; a02 = a0^a2; a13 = a1^a3; a0123 = a02^a13;

  b0 = b&mask; b1 = (b>>1)&mask; b2 = (b>>2)&mask; b3 = (b>>3)&mask;
  b01 = b0^b1; b23 = b2^b3; b02 = b0^b2; b13 = b1^b3; b0123 = b02^b13;

  c01l = a01*b01 & mask;
  c0l = a0*b0 & mask; c01l ^= c0l;
  c1l = a1*b1 & mask; c01l ^= c1l;

  c23l = a23*b23 & mask;
  c2l = a2*b2 & mask; c23l ^= c2l;
  c3l = a3*b3 & mask; c23l ^= c3l;

  c0123l = a0123*b0123 & mask;
  c02l = a02*b02 & mask; c0123l ^= c02l;
  c13l = a13*b13 & mask; c0123l ^= c13l;

  c01l = c0l^c01l<<1^c1l<<2;
  c23l = c2l^c23l<<1^c3l<<2;
  c0123l = c02l^c0123l<<1^c13l<<2;

  c0123l ^= c01l; c0123l ^= c23l;

  return (c0123l^c23l<<2)<<2^c01l;
} /* end f2MulLo */


/*-- product ---------------------------------------------------------------*/

/* Product of x and y modulo 1+u^9+u^79, degree x, y < 79.
 * About 541 cycles (gcc), 548 cycles (cc).
 */
static u128 product(u128 x, u128 y) {
  u64 ah,al, bh,bl, c, tmp, tmp2, t0,t1,t2;
  u128 z;

  al = f2Mul(&ah, x.lo, y.lo);
  bl = f2Mul(&bh, x.lo^x.hi, y.lo^y.hi);
  c = f2MulLo(x.hi, y.hi);

  t0 = al; tmp = ah^c; t1 = al^bl^tmp; t2 = bh^tmp;

  t0 ^= t2<<49; t1 ^= t2>>15;
  t0 ^= t2<<58; t1 ^= t2>>6;

  tmp2 = t1>>15; t1 ^= tmp2<<15; t0 ^= tmp2; t0 ^= tmp2<<9;

  z.hi = t1; z.lo = t0;
  return z;
} /* end product */


/*-- square ----------------------------------------------------------------*/

/* Square of x modulo 1+u^9+u^79, degree x < 79.
 * About 57 cycles (gcc), 56 cycles (cc).
 */
static u128 square(u128 x) {
  /* TO DO: smaller tab??? */
  static const int tab[256] =
  { 0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 256, 257
  , 260, 261, 272, 273, 276, 277, 320, 321, 324, 325, 336, 337, 340, 341
  , 1024, 1025, 1028, 1029, 1040, 1041, 1044, 1045, 1088, 1089, 1092
  , 1093, 1104, 1105, 1108, 1109, 1280, 1281, 1284, 1285, 1296, 1297
  , 1300, 1301, 1344, 1345, 1348, 1349, 1360, 1361, 1364, 1365, 4096
  , 4097, 4100, 4101, 4112, 4113, 4116, 4117, 4160, 4161, 4164, 4165
  , 4176, 4177, 4180, 4181, 4352, 4353, 4356, 4357, 4368, 4369, 4372
  , 4373, 4416, 4417, 4420, 4421, 4432, 4433, 4436, 4437, 5120, 5121
  , 5124, 5125, 5136, 5137, 5140, 5141, 5184, 5185, 5188, 5189, 5200
  , 5201, 5204, 5205, 5376, 5377, 5380, 5381, 5392, 5393, 5396, 5397
  , 5440, 5441, 5444, 5445, 5456, 5457, 5460, 5461, 16384, 16385, 16388
  , 16389, 16400, 16401, 16404, 16405, 16448, 16449, 16452, 16453, 16464
  , 16465, 16468, 16469, 16640, 16641, 16644, 16645, 16656, 16657, 16660
  , 16661, 16704, 16705, 16708, 16709, 16720, 16721, 16724, 16725, 17408
  , 17409, 17412, 17413, 17424, 17425, 17428, 17429, 17472, 17473, 17476
  , 17477, 17488, 17489, 17492, 17493, 17664, 17665, 17668, 17669, 17680
  , 17681, 17684, 17685, 17728, 17729, 17732, 17733, 17744, 17745, 17748
  , 17749, 20480, 20481, 20484, 20485, 20496, 20497, 20500, 20501, 20544
  , 20545, 20548, 20549, 20560, 20561, 20564, 20565, 20736, 20737, 20740
  , 20741, 20752, 20753, 20756, 20757, 20800, 20801, 20804, 20805, 20816
  , 20817, 20820, 20821, 21504, 21505, 21508, 21509, 21520, 21521, 21524
  , 21525, 21568, 21569, 21572, 21573, 21584, 21585, 21588, 21589, 21760
  , 21761, 21764, 21765, 21776, 21777, 21780, 21781, 21824, 21825, 21828
  , 21829, 21840, 21841, 21844, 21845
  };

  u64 t0,t1,t2, tmp, xh,xl;
  u128 z;

  xh = x.hi; xl = x.lo;

  t0 = (u64)(long)tab[xl & 255]
      | (u64)(long)tab[xl>>8 & 255]<<16
      | (u64)(long)tab[xl>>16 & 255]<<32
      | (u64)(long)tab[xl>>24 & 255]<<48
      ;
  t1 = (u64)(long)tab[xl>>32 & 255]
      | (u64)(long)tab[xl>>40 & 255]<<16
      | (u64)(long)tab[xl>>48 & 255]<<32
      | (u64)(long)tab[xl>>56 & 255]<<48
      ;
  t2 = (u64)(long)tab[xh & 255]
      | (u64)(long)tab[xh>>8 & 255]<<16
      | (u64)(long)tab[xh>>16 & 255]<<32
      | (u64)(long)tab[xh>>24 & 255]<<48
      ;

  t0 ^= t2<<49; t1 ^= t2>>15;
  t0 ^= t2<<58; t1 ^= t2>>6;

  tmp = t1>>15; t1 ^= tmp<<15; t0 ^= tmp; t0 ^= tmp<<9;

  z.hi = t1; z.lo = t0;
  return z;
} /* end square */


/*-- inverse --------------------------------------------------------------*/

/* Invert y modulo 1+u^9+u^79, degree y < 79, y != 0.
 * About 1641 cycles (gcc), 1353 (cc) for 79-bit inputs.
 */

#define TAB_SIZE (64UL)
#define TAB_MASK (TAB_SIZE-1UL)

static u128 inverse(u128 y) {
  u64 ah,al, bh,bl, sh, th, t, uh,ul, vh,vl;
  u128 u;
  static const int tab[TAB_SIZE] =
  { 6,0,1,0,2,0,1,0,3,0,1,0,2,0,1,0,4,0,1,0,2,0,1,0,3,0,1,0,2,0,1,0
  , 5,0,1,0,2,0,1,0,3,0,1,0,2,0,1,0,4,0,1,0,2,0,1,0,3,0,1,0,2,0,1,0
  };
  const u64 mh = 1UL<<15, ml = 1UL | 1UL<<9;

  /* Maintain: u.y = a<<t and v.y = b<<t. */

  ah = y.hi; al = y.lo;
  t = 0UL;
  while (!(al & 1UL)) {
    al >>= 1; al |= ah<<63; ah >>= 1;
    ++t;
  } /* end while */
  bh = mh; bl = ml;
  uh = 0UL; ul = 1UL; vh = 0UL; vl = 0UL;

  do {
    do {
      bh ^= ah; bl ^= al;
      vh ^= uh; vl ^= ul;

#ifdef __GNUC__
      sh = (u64)(long)tab[bl & TAB_MASK]; th = 64UL-sh;
      bl >>= sh; bl |= bh<<th; bh >>= sh;
      t += sh;
      uh <<= sh; uh |= ul>>th; ul <<= sh;
      while (!(bl & 1UL)) {
        bl >>= 1; bl |= bh<<63; bh >>= 1;
        ++t;
        uh <<= 1; uh |= ul>>63; ul <<= 1;
      } /* end while */
#else
      do {
        sh = (u64)(long)tab[bl & TAB_MASK]; th = 64UL-sh;
        bl >>= sh; bl |= bh<<th; bh >>= sh;
        t += sh;
        uh <<= sh; uh |= ul>>th; ul <<= sh;
      } while (!(bl & 1UL));
#endif

    } while (ah < bh || (ah == bh && al < bl));
    if (ah == bh && al == bl) break;
    do {
      ah ^= bh; al ^= bl;
      uh ^= vh; ul ^= vl;

#ifdef __GNUC__
      sh = (u64)(long)tab[al & TAB_MASK]; th = 64UL-sh;
      al >>= sh; al |= ah<<th; ah >>= sh;
      t += sh;
      vh <<= sh; vh |= vl>>th; vl <<= sh;
      while (!(al & 1UL)) {
        al >>= 1; al |= ah<<63; ah >>= 1;
        ++t;
        vh <<= 1; vh |= vl>>63; vl <<= 1;
      } /* end while */
#else
      do {
        sh = (u64)(long)tab[al & TAB_MASK]; th = 64UL-sh;
        al >>= sh; al |= ah<<th; ah >>= sh;
        t += sh;
        vh <<= sh; vh |= vl>>th; vl <<= sh;
      } while (!(al & 1UL));
#endif

    } while (ah > bh || (ah == bh && al > bl));
  } while (ah != bh || al != bl);

  /* Divide u by 2^t modulo the modulus. */
  while (t >= 36UL) {
    u64 w;

    w = ul & 511UL; ul >>= 9;
    ul ^= w; uh ^= w<<15;
    w = ul & 511UL; ul >>= 9;
    ul ^= w; uh ^= w<<24;
    w = ul & 511UL; ul >>= 9;
    ul ^= w; uh ^= w<<33;
    w = ul & 511UL; ul >>= 9;
    ul ^= w; uh ^= w<<42;
    ul |= uh<<28; uh >>= 36;
    t -= 36UL;
  } /* end while */
  if (t >= 18UL) {
    u64 w;

    w = ul & 511UL; ul >>= 9;
    ul ^= w; uh ^= w<<15;
    w = ul & 511UL; ul >>= 9;
    ul ^= w; uh ^= w<<24;
    ul |= uh<<46; uh >>= 18;
    t -= 18UL;
  } /* end if */
  if (t >= 9UL) {
    u64 w;

    w = ul & 511UL;
    ul >>= 9; ul |= uh<<55; uh >>= 9;
    ul ^= w; uh ^= w<<6;
    t -= 9UL;
  } /* end if */
  if (t) {
    u64 w;

    w = ul^ul>>t<<t;
    ul ^= w<<9UL; uh ^= w<<15UL;
    ul >>= t; ul |= uh<<(64UL-t); uh >>= t;
  } /* end if */

  u.hi = uh; u.lo = ul;
  return u;
} /* end inverse */


/*-- quotient --------------------------------------------------------------*/

/* Divide x by y modulo 1+u^9+u^79, degree x, y < 79, y != 0.
 * About 2173 cycles (gcc), 1909 (cc).
 */
static u128 quotient(u128 x, u128 y) {
  u128 z;

  z = inverse(y);

  return product(x, z);
} /* end quotient */


/*== Stuff for elliptic curves over the field ==============================*/

/*-- ellipticDouble --------------------------------------------------------*/

/* Given point (x:y:z) on y^2 + x*y = x^3 + a*x^2 + b, this computes
 * its double (x2:y2:z2) by the group law.  Doesn't actually need b.
 * Puts x2 at *px2 and y2 at *py2, and returns z2.
 * The point at infinity is represented by (0:1:0).
 * Finite points are represented by (x:y:1).
 */
static u64 ellipticDouble
  ( u128 x, u128 y, u64 z, u128 a
  , u128 *px2, u128 *py2
  ) {
  u128 lam, x2, y2;
  const u128 zero = { 0UL, 0UL }, one = { 0UL, 1UL };

#if 0
  /* Short and sweet. */
  if (z == 0UL || equal(x, zero)) { *px2 = zero; *py2 = one; return 0UL; }

  lam = sum(x, quotient(y, x));
  x2 = sum(sum(square(lam), lam), a);
  y2 = sum(square(x), sum(product(lam, x2), x2));
#else
  /* Same thing but a bit faster with explicit xors. */
  u128 t;

  if (z == 0UL || (x.hi | x.lo) == 0UL) {
    *px2 = zero; *py2 = one; return 0UL;
  } /* end if */

  lam = quotient(y, x);
  lam.hi ^= x.hi; lam.lo ^= x.lo;

  x2 = square(lam);
  x2.hi ^= lam.hi; x2.lo ^= lam.lo;
  x2.hi ^= a.hi; x2.lo ^= a.lo;

  y2 = product(lam, x2);
  t = square(x);
  y2.hi ^= x2.hi; y2.lo ^= x2.lo;
  y2.hi ^= t.hi; y2.lo ^= t.lo;
#endif

  *px2 = x2; *py2 = y2;
  return 1UL;
} /* end ellipticDouble */


/*-- ellipticSum -----------------------------------------------------------*/

/* Given pts (x1:y1:z1) and (x2:y2:z2) on y^2 + x*y = x^3 + a*x^2 + b,
 * computes their sum (x3:y3:z3) by the group law.  Doesn't actually need b.
 * Puts x3 at *px3 and y3 at *py3, and returns z3.
 * The point at infinity is represented by (0:1:0).
 * Finite points are represented by (x:y:1).
 */
static u64 ellipticSum
  ( u128 x1, u128 y1, u64 z1, u128 x2, u128 y2, u64 z2, u128 a
  , u128 *px3, u128 *py3
  ) {
  u128 lam, x3, y3;

#if 0
  /* Short and sweet. */
  if (z1 == 0UL) { *px3 = x2; *py3 = y2; return z2; }
  if (z2 == 0UL) { *px3 = x1; *py3 = y1; return z1; }

  if (equal(x1, x2)) {
    const u128 zero = { 0UL, 0UL }, one = { 0UL, 1UL };

    if (equal(y1, y2)) return ellipticDouble(x1, y1, z1, a, px3, py3);
    *px3 = zero; *py3 = one; return 0UL;
  } /* end if */

  lam = quotient(sum(y1, y2), sum(x1, x2));
  x3 = sum(sum(sum(sum(square(lam), lam), x1), x2), a);
  y3 = sum(sum(product(lam, sum(x1, x3)), x3), y1);
#else
  /* Same thing but a bit faster with explicit xors. */
  u128 t, x, y;

  if (z1 == 0UL) { *px3 = x2; *py3 = y2; return z2; }
  if (z2 == 0UL) { *px3 = x1; *py3 = y1; return z1; }

  if (((x1.hi ^ x2.hi) | (x1.lo ^ x2.lo)) == 0UL) {
    const u128 zero = { 0UL, 0UL }, one = { 0UL, 1UL };

    if (((y1.hi ^ y2.hi) | (y1.lo ^ y2.lo)) == 0UL) {
      return ellipticDouble(x1, y1, z1, a, px3, py3);
    } /* end if */
    *px3 = zero; *py3 = one; return 0UL;
  } /* end if */

  x.hi = x1.hi^x2.hi; x.lo = x1.lo^x2.lo;
  y.hi = y1.hi^y2.hi; y.lo = y1.lo^y2.lo;
  lam = quotient(y, x);

  x3 = square(lam);
  x3.hi ^= lam.hi; x3.lo ^= lam.lo;
  x3.hi ^= x1.hi; x3.lo ^= x1.lo;
  x3.hi ^= x2.hi; x3.lo ^= x2.lo;
  x3.hi ^= a.hi; x3.lo ^= a.lo;

  t.hi = x1.hi^x3.hi; t.lo = x1.lo^x3.lo;
  y3 = product(lam, t);
  y3.hi ^= y1.hi; y3.lo ^= y1.lo;
  y3.hi ^= x3.hi; y3.lo ^= x3.lo;
#endif

  *px3 = x3; *py3 = y3; return 1UL;
} /* end ellipticSum */


/*-- ellipticProduct -------------------------------------------------------*/

/* Given point (x, y) on y^2 + x*y = x^3 + a*x^2 + b, this computes its
 * fac-th multiple (x2:y2:z2) by the group law.  Doesn't actually need b.
 * Puts x2 at *px2 and y2 at *py2, and returns z2.
 * The point at infinity is represented by (0:1:0).
 * Finite points are represented by (x:y:1).
 */
static u64 ellipticProduct
  ( u128 x, u128 y, u64 z, u128 fac, u128 a
  , u128 *px2, u128 *py2
  ) {
  u64 fh, fl, m, z2;
  u128 x2, y2;
  const u128 zero = { 0UL, 0UL }, one = { 0UL, 1UL };

  if (equal(fac, zero)) { *px2 = zero; *py2 = one; return 0UL; }

  fh = fac.hi;
  if (fh) {
    x2 = x; y2 = y; z2 = z;
    m = fh;
    m |= m>>1; m |= m>>2; m |= m>>4; m |= m>>8; m |= m>>16; m |= m>>32;
    m ^= m>>1;
    while (m >>= 1) {
      z2 = ellipticDouble(x2, y2, z2, a, &x2, &y2);
      if (fh & m) z2 = ellipticSum(x, y, z, x2, y2, z2, a, &x2, &y2);
    } /* end while */
  } else { x2 = zero; y2 = one; z2 = 0UL; }

  m = 1UL<<63;
  fl = fac.lo;
  do {
    z2 = ellipticDouble(x2, y2, z2, a, &x2, &y2);
    if (fl & m) z2 = ellipticSum(x, y, z, x2, y2, z2, a, &x2, &y2);
    m >>= 1;
  } while (m);

  *px2 = x2; *py2 = y2; return z2;
} /* end ellipticProduct */


/*== Driver ================================================================*/

/*-- incMod ----------------------------------------------------------------*/

/* x+1 modulo mod, where x < mod. */
static INLINE u128 incMod(u128 x, u128 mod) {
  const u128 zero = { 0UL, 0UL };

  ++x.lo; x.hi += x.lo == 0UL;

  return equal(x, mod) ? zero : x;
} /* end incMod */


/*-- doubleMod -------------------------------------------------------------*/

/* x<<1 modulo mod, where x < mod. */
static INLINE u128 doubleMod(u128 x, u128 mod) {

  x.hi <<= 1; x.hi |= x.lo>>63; x.lo <<= 1;
  if (x.hi > mod.hi || (x.hi == mod.hi && x.lo >= mod.lo)) {
    u64 c;

    c = x.lo < mod.lo; x.hi -= mod.hi; x.lo -= mod.lo; x.hi -= c;
  } /* end if */

  return x;
} /* end doubleMod */


/*-- main ------------------------------------------------------------------*/

#define GET_TIME \
  do { getrusage(RUSAGE_SELF, &ru); } while (0)
#define STORE_TIME \
  do { tvUT = ru.ru_utime; tvST = ru.ru_stime; } while (0)
#define REPORT_TIME_DIFF \
  do {                                                                  \
    dUT = (double)(ru.ru_utime.tv_sec-tvUT.tv_sec)                      \
          +(double)(ru.ru_utime.tv_usec-tvUT.tv_usec)/1000000.0;        \
    printf("time = %.8fu secs.\n", dUT);                                \
    fflush(stdout);                                                     \
  } while (0)

int main(int argc, char *argv[]) {

  /** Curve from Certicom. **/
  /* mod = 1+u^9+u^79
   * size = 2^79
   * subSize = 2^78
   * a = 350307752743756744112223
   * b = 207999945740371913173159
   * x1 = 230419611992652394983695
   * y1 = 398950942939094935630139
   * x2 = 593366987472068244261
   * y2 = 384681936094096304619817
   * ord = 302231454903954479142443
   */
  const u128
    mod = { 32768UL, 513UL }       /* The irreducible polynomial. */
  , a = { 18990UL, 4082784012358924383UL }
  , b = { 11275UL, 12906309296718702759UL }
  , ord = { 16384UL, 297185465899UL }
  ;
  u128
    x1 = { 12491UL, 1331767946385748239UL }
  , y1 = { 21627UL, 3208856978462830907UL }
  , x2 = { 32UL, 3071177113362592549UL }
  , y2 = { 20853UL, 11981925031024771369UL }
  ;
  u64 z1 = 1UL, z2 = 1UL;

/* 2^POW_WRITE ~= sqrt(ord)/100 or 1000 or so.  Take 30 here. */
#define POW_WRITE (30UL)

  u64 k, startu, z3;
  u128 u3,v3,x3,y3;

  double dUT;
  struct rusage ru;
  struct timeval tvUT, tvST;


  GET_TIME; STORE_TIME;

  /** Work in subgroup of index 2. **/
  puts("Computing points...");
  fflush(stdout);

  z1 = ellipticDouble(x1, y1, z1, a, &x1, &y1);
  printf("Base: %lu|%lu:%lu|%lu:%lu\n", x1.hi, x1.lo, y1.hi, y1.lo, z1);
  fflush(stdout);

  z2 = ellipticDouble(x2, y2, z2, a, &x2, &y2);
  printf("Target: %lu|%lu:%lu|%lu:%lu\n", x2.hi, x2.lo, y2.hi, y2.lo, z2);
  fflush(stdout);

  GET_TIME; REPORT_TIME_DIFF; STORE_TIME;


  /** Get a fairly random initial value. **/
  { long seed;
    FILE *handle;

    handle = fopen("/dev/urandom", "r");
    if (handle != NULL) {
      fread((void *)&seed, sizeof(long), 1UL, handle);
      fclose(handle);
    } /* end if */
    seed ^= (long)getpid();
    seed ^= (long)time(NULL); /* Random enough for you?  =:-) */
    srand48(seed);
    startu = (u64)(u32)mrand48() ^ (u64)(u32)mrand48()<<16
             ^ (u64)(u32)mrand48()<<32 ^ (u64)(u32)mrand48()<<48
             ;
  } /* end block */


  /** Initialisations. **/
  u3.hi = 0UL; u3.lo = startu;
  v3.hi = v3.lo = 0UL;
  z3 = ellipticProduct(x1, y1, z1, u3, a, &x3, &y3);
 
  /** Main loop does about 170K steps/sec with gcc+Linux on 500Mhz Alpha. **/
  puts("Computing iterations...");
  fflush(stdout);

  for (k = 0UL; ; ) {
    u64 t;

    if (x3.lo>>(64UL-POW_WRITE) == 0UL) {
#ifndef BATCH
      FILE *handle;

      handle = popen("/usr/sbin/sendmail -t", "w");
      if (handle == NULL) {
        puts("Warning: couldn't pipe to sendmail, send by hand!");
      } else {
        int status;

        fprintf( handle
               , "To: ecdl@pauillac.inria.fr\n"
         "ECC2-79 s %lu i %lu x %lu %lu y %lu %lu z %lu u %lu %lu v %lu %lu\n"
               , startu, k, x3.hi, x3.lo, y3.hi, y3.lo, z3
               , u3.hi, u3.lo, v3.hi, v3.lo
               );
        fflush(handle);
        status = pclose(handle);
        if (status != EX_OK) {
          printf("Warning: sendmail returned status %d\n", status);
          fflush(stdout);
        } /* end if */
      } /* end if/else */
#endif
      printf( "ECC2-79 s %lu i %lu x %lu %lu y %lu %lu z %lu u %lu %lu v "
                "%lu %lu\n"
            , startu, k, x3.hi, x3.lo, y3.hi, y3.lo, z3
            , u3.hi, u3.lo, v3.hi, v3.lo
            );
      fflush(stdout);
      GET_TIME; REPORT_TIME_DIFF;
    } /* end if (write) */

    t = x3.lo & 31UL;
#if 0
    /* Short and sweet. */
    if (t < 15UL) {
      u3 = incMod(u3, ord);
      z3 = ellipticSum(x1, y1, z1, x3, y3, z3, a, &x3, &y3);
    } else if (t < 30UL) {
      v3 = incMod(v3, ord);
      z3 = ellipticSum(x2, y2, z2, x3, y3, z3, a, &x3, &y3);
    } else {
      /* Reduced number of doublings to 1 in 8. */
      u3 = doubleMod(u3, ord);
      v3 = doubleMod(v3, ord);
      z3 = ellipticDouble(x3, y3, z3, a, &x3, &y3);
    } /* end if/else if/else */
#else
    /* Same thing but a bit faster with explicit adds etc. */
    if (t < 15UL) {
      ++u3.lo; u3.hi += u3.lo == 0UL;
      if (((u3.lo ^ ord.lo) | (u3.hi ^ ord.hi)) == 0UL) u3.hi = u3.lo = 0UL;
      z3 = ellipticSum(x1, y1, z1, x3, y3, z3, a, &x3, &y3);
    } else if (t < 30UL) {
      ++v3.lo; v3.hi += v3.lo == 0UL;
      if (((v3.lo ^ ord.lo) | (v3.hi ^ ord.hi)) == 0UL) v3.hi = v3.lo = 0UL;
      z3 = ellipticSum(x2, y2, z2, x3, y3, z3, a, &x3, &y3);
    } else { /* Reduced number of doublings to 1 in 8. */
      u64 c;

      u3.hi <<= 1; u3.hi |= u3.lo>>63; u3.lo <<= 1;
      if (u3.hi > ord.hi || (u3.hi == ord.hi && u3.lo >= ord.lo)) {
        c = u3.lo < ord.lo; u3.hi -= ord.hi; u3.lo -= ord.lo; u3.hi -= c;
      } /* end if */
      v3.hi <<= 1; v3.hi |= v3.lo>>63; v3.lo <<= 1;
      if (v3.hi > ord.hi || (v3.hi == ord.hi && v3.lo >= ord.lo)) {
        c = v3.lo < ord.lo; v3.hi -= ord.hi; v3.lo -= ord.lo; v3.hi -= c;
      } /* end if */
      z3 = ellipticDouble(x3, y3, z3, a, &x3, &y3);
    } /* end if/else if/else */
#endif

    ++k;

  } /* end for (k) main loop */

  return 0;
} /* end main */


/*== end of file ecdl.c ====================================================*/
