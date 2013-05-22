/* > eccp97b.c
 * Source for a client to generate distinguished points as part of a
 * solution to the problem of determining the private key to a known
 * public key in an elliptic curve cryptosystem of prime order ~2^97.
 *
 * This is code for 64-bit architectures. See eccp97a.c for 32-bit stuff.
 * Modified from Robert Harley's ecdlp-89.c by John Sager, BT Labs.
 */

/* Copyright: parts Robert Harley 1997 (Robert.Harley@inria.fr)
 * Copyright: parts British Telecommunications plc 1997, 1998
 *              (john.sager@bt-sys.bt.co.uk)
 *
 * Usage rights statements below. Where usage restrictions differ in the two
 * statements the more restrictive applies.
 */

/*
 * Purpose: Some tools for arithmetic on elliptic curves.
 * Copyright: Robert J. Harley, 03-Feb-1997
 * Contact: Robert.Harley@inria.fr
 * Legalese: You can do what you want with this code as long as this
 *           comment stays attached in a prominent position in
 *           human-readable form, any distribution of this or
 *           derived products is made without profit and includes
 *           full source and is subject to the same conditions.
 */

/*
 * Copyright (c) 1997,1998 by British Telecommunications plc.
 *
 * Permission to use, copy, modify, and distribute this software for
 * any purpose without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND BRITISH TELECOMMUNICATIONS PLC
 * DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT
 * SHALL BRITISH TELECOMMUNICATIONS PLC BE LIABLE FOR ANY SPECIAL,
 * DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN
 * AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING
 * OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS
 * SOFTWARE.
 */

#ifndef __alpha
#error Use an Alpha!
#endif

/* Compile with something like:
 *   gcc -O4 eccp97b.c -o eccp97b
 * or:
 *   cc -O5 -tune host -std1 eccp97b.c -o eccp97b
 */


/*== #includes =============================================================*/

/** Ansi includes. **/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/** Unix includes. **/
#include <sys/types.h>
#include <unistd.h>
#include <signal.h>
/* Timing. */
#include <sys/time.h>
#include <time.h>

/** I/O. **/
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>

/** System-specific includes. **/
#ifdef VMS
#include <ints.h>
#include <unixio.h>
#include <inet.h>
#include <builtins.h>
#include <sys/times.h>
#else
#include <sys/resource.h>
#endif

#ifdef __DECC
#include <c_asm.h>
#endif


/*== Types =================================================================*/

#ifdef VMS
typedef uint32 u32;
typedef uint64 u64;
#else
typedef unsigned int u32;
typedef unsigned long u64;
#endif

typedef struct { u64 hi, lo; } u128;


/*== #defines ==============================================================*/

#ifndef CLIENT
#define CLIENT "BTRH64CC"
#endif

/* Version 1.01: February 17th 1998
 * - Arithmetic munged around a little bit by Rob, for extra speed.
 * Version 1.00: February 13th 1998
 * - Some cosmetic changes, B.T.'s external proxy set up.
 * Version 0.91: 
 * - Preliminary release by John Sager, based on Rob's ECCp-89 code with
 *   saved state, ini file and TCP communication added.
 */
#define VERSION "101"

#ifdef VMS
#define SAV_FILE "eccp97b.sav;1"
#define INI_FILE "eccp97b.ini;0"
#define BUF_FILE "eccp97b.buf;1"
#else
#define SAV_FILE "eccp97b.sav"
#define INI_FILE "eccp97b.ini"
#define BUF_FILE "eccp97b.buf"
#endif

#define BUFLEN  1024

#define MSGLEN  399

#define PROXYPORT  8797

/* 193.113.60.37 - eccproxy.labs.bt.com. */
#define OPROXYADDR (0xc1713c25)

/* 132.146.196.89 - raman.alien.bt.co.uk. */
#define IPROXYADDR (0x8492c459)

/* 132.146.196.54 - klingon.alien.bt.co.uk. */
#define SVRADDR    (0x8492c436)

#define MAILADDR   "eccp97@zoo.bt.co.uk"


#ifdef VMS

#define INLINE
#define HiMul(_x, _y) __UMULH(_x, _y)

#elif defined(__GNUC__)

#define INLINE inline
static inline u64 HiMul(u64 m0, u64 m1) {
  unsigned long tmp;

  asm("umulh %r1,%2,%0" : "=r" (tmp) : "%rJ" (m0), "rI" (m1));

  return tmp;
} /* end HiMul */

#elif defined(__DECC)

/* Digital's cc. */
#define INLINE __inline
#define HiMul(m0, m1) asm("umulh %a0, %a1, %v0", m0, m1)

#else

#error Weird compiler, dude!  Write code here.

#endif


/** Data from Certicom ECCp-97. **/

/* The field prime, mod = 113466572691320833494871051829. */
#define MOD_HI (0x16ea1595eUL)
#define MOD_LO (0xd21ae4d8d8420e35UL)
#define MOD { MOD_HI, MOD_LO }

/* Group order (prime). */
#define ORD  { 0x16ea1595eUL, 0xd21ae98fb6cca20dUL }

/* These get encoded. */
/* Curve y^2 = x^3 + A*x + B. */
#define A    { 0x047370916UL, 0xa603b07657c305c4UL }
#define B    { 0x1124df86dUL, 0x04064f503d9925afUL }
/* Point (X1:Y1:1) is base of logarithm. */
#define X1   { 0x0d5d9e9dfUL, 0xf58a9232a2749ebcUL }
#define Y1   { 0x11b34ae5aUL, 0xab7c7ae55d6abdb5UL }
/* Point (X2:Y2:1) whose log is to be found. */
#define X2   { 0x0df7e84c4UL, 0x2fef50c5316c508aUL }
#define Y2   { 0x0f259bc58UL, 0x3729da0fe8b97336UL }


/** More useful constants. **/
/* 1/mod modulo 2^97. */
#define INV_HI (0x0606bb011UL)
#define INV_LO (0x0bc46a65dbcf541dUL)
#define INV { INV_HI, INV_LO }

/* 2^97 modulo mod = encoded 1. */
#define ONE  { 0x0915ea6a1UL, 0x2de51b2727bdf1cbUL }

/* 2^194 modulo mod. */
#define CODE { 0x15c8e199aUL, 0x19353f4f1bf8cec1UL }

/* (mod+1)/2. */
#define FIX  { 0x0b750acafUL, 0x690d726c6c21071bUL }


/*== Function declarations =================================================*/

static INLINE int equal(u128 x, u128 y);
static INLINE u128 sumMod(u128 x, u128 y, const u128 mod);
static INLINE u128 diffMod(u128 x, u128 y, const u128 mod);
static INLINE u128 doubleMod(u128 x, const u128 mod);

void termSig(int sigNum);
int main(int argc, char *argv[]);

static INLINE u128 encode(u128 x);
static u128 decode(u128 x);
static u128 inverseMod(u128 y);
static INLINE u128 quotientMod(u128 x, u128 y);
static u128 squareMod(u128 x);
static u128 productMod(u128 x, u128 y);

static int ellipticSum
  ( u128 x1, u128 y1, int z1, u128 x2, u128 y2, int z2, u128 a
  , u128 *px3, u128 *py3
  );
static int ellipticDouble
  ( u128 x, u128 y, int z, u128 a, u128 *px2, u128 *py2
  );
static int ellipticProduct
  ( u128 x, u128 y, int z, u128 fac, u128 a, u128 *px2, u128 *py2
  );

static int loadIni(void);
static void sendIt(char *, int);
static double getTime(void);


/*== Global variables ======================================================*/

/* Copyright messages. */
const char
  copyright1[] = "Copyright: parts Robert Harley 1997"
                   " (Robert.Harley@inria.fr)"
, copyright2[] = "Copyright: parts British Telecommunications plc 1997, 1998 "
                   "(john.sager@bt-sys.bt.co.uk)"
;

/* Format strings - 'cos VMS is different! */
const char
#ifdef VMS
  savr[] = "%09llx%016llx %012llx %09llx%016llx %09llx%016llx %lf\n"
, savw[] = "%09llx%016llx %012llx %09llx%016llx %09llx%016llx %12.4f\n"
, outw[] = "ECCp-97 s %09llx%016llx i %012llx "
             "x %09llx%016llx y %09llx%016llx z %01x "
             "u %09llx%016llx v %09llx%016llx t %08lx %s%02d %s "
#else
  savr[] = "%09lx%016lx %012lx %09lx%016lx %09lx%016lx %lf\n"
, savw[] = "%09lx%016lx %012lx %09lx%016lx %09lx%016lx %12.4f\n"
, outw[] = "ECCp-97 s %09lx%016lx i %012lx "
             "x %09lx%016lx y %09lx%016lx z %01x "
             "u %09lx%016lx v %09lx%016lx t %08lx %s%02d %s "
#endif
;

/* Global variables set from the ini file. */
#define PROTO_NONE      0
#define PROTO_TCP       1
#define PROTO_MAIL      2
int protocol = PROTO_TCP; /* 0 = log only, 1 = TCP, 2 = mail. */
int proxyport = PROXYPORT;
u32 proxy1addr = SVRADDR;
u32 proxy2addr = IPROXYADDR;
char frombuf[128] = "";
char freeform[256] = "";

/* Set to 0 by a term signal. */
int running;


/*== Function definitions ==================================================*/

/*== Some simple modular arithmetic ========================================*/

/*-- equal -----------------------------------------------------------------*/

/* Check equality: x == y, 0 <= x, y < 2^128. */
static INLINE int equal(u128 x, u128 y) {

  return ((x.hi ^ y.hi) | (x.lo ^ y.lo)) == 0UL;
} /* end equal */


/*-- sumMod ----------------------------------------------------------------*/

/* Add: x + y modulo modulus, 0 <= x, y < modulus <= 2^127. */
static INLINE u128 sumMod(u128 x, u128 y, const u128 mod) {
  x.hi += y.hi; x.lo += y.lo; x.hi += x.lo < y.lo;

  if (x.hi > mod.hi || (x.hi == mod.hi && x.lo >= mod.lo)) {
    x.hi -= mod.hi; x.hi -= x.lo < mod.lo; x.lo -= mod.lo;
  } /* end if */

  return x;
} /* end sumMod */


/*-- diffMod ---------------------------------------------------------------*/

/* Subtract: x - y modulo modulus, 0 <= x, y < modulus < 2^128. */
static INLINE u128 diffMod(u128 x, u128 y, const u128 mod) {
  u64 xh,xl;

  xh = x.hi; xl = x.lo;

  if (xh < y.hi || (xh == y.hi && xl < y.lo)) {
    xh += mod.hi; xl += mod.lo; xh += xl < mod.lo;
  } /* end if */

  xh -= y.hi; xh -= xl < y.lo; xl -= y.lo;

  x.hi = xh; x.lo = xl;
  return x;

} /* end diffMod */


/*-- doubleMod -------------------------------------------------------------*/

/* Double x modulo odd modulus, 0 <= x < modulus < 2^127. */
static INLINE u128 doubleMod(u128 x, const u128 mod) {
  u64 xh,xl;

  xh = x.hi; xl = x.lo;

  xh <<= 1; xh |= xl>>63; xl <<= 1;
  if (xh > mod.hi || (xh == mod.hi && xl >= mod.lo)) {
    xh -= mod.hi; xh -= xl < mod.lo; xl -= mod.lo;
  } /* end if */

  x.hi = xh; x.lo = xl;

  return x;
} /* end doubleMod */


/*== Driver ================================================================*/

/*-- termSig ---------------------------------------------------------------*/

/* Signal catcher for SIGTERM. */
void termSig(int sigNum) {

  running = 0;

} /* end termSig */


/*-- main ------------------------------------------------------------------*/

/* Number of iterations to run "in parallel".  This is done so that
 * PARAL inversions can be replaced by one inversion and 3*PARAL-3 mults.
 */
#define PARAL (32UL)

/* Do not change these. */
#define ADD_MASK (15UL)
#define ADDERS (15UL)
#define POW_WRITE (30UL)

int main(int argc, char *argv[]) {
  const u128 mod = MOD, one = ONE, ord = ORD;
  u128 a = A, b = B, x1 = X1, y1 = Y1, x2 = X2, y2 = Y2;
  int z1 = 1, z2 = 1;

  u64 i, itersT[PARAL];
  int zA[ADDERS], z3T[PARAL], zT[PARAL];
  u128 uA[ADDERS], xA[ADDERS], yA[ADDERS]
  , u3T[PARAL], v3T[PARAL], x3T[PARAL], y3T[PARAL]
  , xT[PARAL], yT[PARAL]
  , denT[PARAL], numT[PARAL]
  , startvT[PARAL]
  ;
  char outbuf[BUFLEN];


  /* Timing. */
  double startTime, saveTime, timeT[PARAL];

  /* Save state. */
  FILE *savHandle;


  if (!loadIni()) {
    puts(
#ifdef VMS
          "No ini file!  'run timerp97b' to create one."
#else
          "No ini file!  Run 'timerp97b -i' to create one."
#endif
        );
    exit(1);
  } /* end if */

  puts("Getting curve...");
  a = encode(a);
  b = encode(b);

  puts("Getting initial points...");
  x1 = encode(x1);
  y1 = encode(y1);
  x2 = encode(x2);
  y2 = encode(y2);

  /** Pseudo-random values to add.  Do not change. */
  { u32 startu;

    startu = 1U;
    for (i = 0UL; i < ADDERS; ++i) {
      u128 fac;
      const u32 pi = 3141592653U; /* Pi times 1e9. */

      startu *= pi;
      fac.hi = 0UL; fac.lo = (u64)startu | (((u64)startu)<<32);
      uA[i] = fac;
      zA[i] = ellipticProduct(x1, y1, z1, fac, a, xA+i, yA+i);
    } /* end for */
  } /* end block */

  /* Reload sav file, if it exists, then initialise any shortfall with
   * random start points.
   */

  i = 0;
  { u128 xu, yu, xv, yv;
    u32 zu, zv;

    if ((savHandle = fopen(SAV_FILE, "r")) != NULL) {
      while (!feof(savHandle)) {
        fscanf( savHandle, savr, &startvT[i].hi, &startvT[i].lo, &itersT[i],
                &u3T[i].hi, &u3T[i].lo, &v3T[i].hi, &v3T[i].lo, &timeT[i]
              );
        zu = ellipticProduct(x1, y1, z1, u3T[i], a, &xu, &yu);
        zv = ellipticProduct(x2, y2, z2, v3T[i], a, &xv, &yv);
        z3T[i] = ellipticSum(xu, yu, zu, xv, yv, zv, a, x3T+i, y3T+i);
        if (++i >= PARAL) break;
      } /* end while */
      fclose(savHandle);
      remove(SAV_FILE);
      printf("Loaded %lu saved points\n", i);
    } /* end if */
  } /* end block */


  /** Choose PARAL random starting points. **/
  { u64 seed;

    seed = ((u64)getpid()<<32) | (u64)time(NULL);

    for (; i < PARAL; ++i) {
      u128 startv;
      const u64 eulerGamma = 10647749645774669733UL; /* Gamma times 2^64. */

      u3T[i].hi = 0UL; u3T[i].lo = 0UL;
      startv.hi = 0UL; startv.lo = seed;
      seed += eulerGamma;
      startvT[i] = startv;
      v3T[i] = startv;
      itersT[i] = 0UL;
      timeT[i] = 0.0;
      z3T[i] = ellipticProduct(x2, y2, z2, startv, a, x3T+i, y3T+i);
    } /* end for (i) */
  } /* end block */


  /** Main loop. **/
  puts("Computing iterations...");
  fflush(stdout);
  startTime = getTime();

  /* Adjust point times. */
  for (i = 0; i < PARAL; ++i) timeT[i] = startTime-timeT[i];

  /* Catch TERM signal. */
  signal(SIGTERM, termSig);

  running = 1;
  while (running) {

    /* Look for distinguished points. */
    for (i = 0UL; i < PARAL; ++i) {
      if (x3T[i].lo>>(64UL-POW_WRITE) == 0UL) {
        u64 pointTime;
        u128 x3,y3;
        double dTime;
        long len1, len2;

        dTime = getTime()-timeT[i];
        pointTime = (u64)(dTime+0.5);

        x3 = decode(x3T[i]);
        y3 = decode(y3T[i]);

        /* Output distinguished point. */
        sprintf( outbuf, outw, startvT[i].hi, startvT[i].lo, itersT[i]
               , x3.hi, x3.lo, y3.hi, y3.lo, z3T[i]
               , u3T[i].hi, u3T[i].lo, v3T[i].hi, v3T[i].lo, pointTime
               , CLIENT, PARAL, VERSION
               );
        len1 = strlen(outbuf);
        len2 = strlen(frombuf);
        if ((len1+len2) > MSGLEN) {
          len2 = MSGLEN-len1;
          frombuf[len2] = '\0'; /* Truncate it. */
        } /* end if */
        strcpy(outbuf+len1, frombuf);
        len1 += len2;
        if (len1+2 < MSGLEN) {
          len2 = strlen(freeform);
          if ((len1+len2+2) > MSGLEN) {
            len2 = MSGLEN-2-len1;
            freeform[len2] = '\0'; /* Truncate it. */
          } /* end if */
          strcpy(outbuf+len1, " ;");
          len1 += 2;
          strcpy(outbuf+len1, freeform);
          len1 += len2;
          strcpy(outbuf+len1++, "\n");
        } /* end if */
        sendIt(outbuf, len1);

        if (dTime) {
          printf( "%lu*%lu iters in %g secs = %g iters/sec.\n"
                , itersT[i], PARAL, dTime
                , (double)(itersT[i]*PARAL)/dTime
                );
          fflush(stdout);
        } /* end if */

        /* Restart this one by setting u to 0... */
        u3T[i].hi = 0UL; u3T[i].lo = 0UL;
        startvT[i] = v3T[i];
        itersT[i] = 0UL;
        z3T[i] = ellipticProduct(x2, y2, z2, startvT[i], a, x3T+i, y3T+i);
        timeT[i] = getTime();
      } /* end if (distinguished point) */
    } /* end for (i) */


    /* Get numT[] & denT[], update u3T[] & v3T[]. */
    for (i = 0UL; i < PARAL; ++i) {
      int z, z3;
      u64 m;
      u128 den, num, x,y, x3,y3;
      const u128 zero = { 0UL, 0UL };

      x3 = x3T[i]; y3 = y3T[i]; z3 = z3T[i];

      /* Pseudo-random function.  Same on all machines. **/
      m = x3.lo & ADD_MASK;
      if (m < ADDERS) {
        u3T[i] = sumMod(u3T[i], uA[m], ord);
        x = xA[m]; y = yA[m]; z = zA[m];
      } else {
        u3T[i] = doubleMod(u3T[i], ord);
        v3T[i] = doubleMod(v3T[i], ord);
        x = x3; y = y3; z = z3;
      } /* end if/else */
      xT[i] = x; yT[i] = y; zT[i] = z;

      if (z == 0 || z3 == 0) { num = zero; den = one; } /* Dummy, den != 0. */
      else if (equal(x, x3)) {
        if (equal(y, y3)) { /* Doubling. */
          if ((y.hi | y.lo) == 0UL) { num = zero; den = one; } /* Dummies. */
          else {
            u128 s;

            s = squareMod(x);
            num = doubleMod(s, mod);
            num = sumMod(num, s, mod);
            num = sumMod(num, a, mod);

            den = doubleMod(y, mod);
          } /* end if/else */
        } else { num = zero; den = one; } /* Dummies. */
      } else { /* General case. */
        num = diffMod(y, y3, mod);
        den = diffMod(x, x3, mod);
      } /* end if/else if/else... */

      numT[i] = num; denT[i] = den;

    } /* end for (i) */


    /* Divide numT[] by denT[] with one inversion and 4*PARAL-3 mults. */
    { u128 ix, prod, q, prodT[PARAL];

      prod = denT[0];
      for (i = 1UL; i < PARAL; ++i) {
        prodT[i] = prod;
        prod = productMod(prod, denT[i]);
      } /* end for */
      q = inverseMod(prod);
      for (i = PARAL; --i; ) {
        ix = productMod(q, prodT[i]);
        numT[i] = productMod(numT[i], ix);
        q = productMod(q, denT[i]);
      } /* end for */
      numT[0] = productMod(numT[0], q);
    } /* end block */


    /* Get new points. */
    for (i = 0UL; i < PARAL; ++i) {
      int nz, z, z3;
      u128 nx,ny, x,y, x3,y3;

      x = xT[i]; y = yT[i]; z = zT[i];
      x3 = x3T[i]; y3 = y3T[i]; z3 = z3T[i];

      if (z == 0) { nx = x3; ny = y3; nz = z3; }
      else if (z3 == 0) { nx = x; ny = y; nz = z; }
      else if (equal(x, x3)) {
        const u128 zero = { 0UL, 0UL };

        if (equal(y, y3)) { /* Doubling. */
          if ((y.hi | y.lo) == 0UL) { nx = zero; ny = one; nz = 0; }
          else {
            u128 lam, s, t;

            lam = numT[i];

            nx = squareMod(lam);
            s = doubleMod(x, mod);
            nx = diffMod(nx, s, mod);

            t = diffMod(x, nx, mod);
            ny = productMod(lam, t);
            ny = diffMod(ny, y, mod);

            nz = 1;
          } /* end if/else */
        } else { nx = zero; ny = one; nz = 0; }
      } else { /* General case. */
        u128 lam, s;

        lam = numT[i];

        nx = squareMod(lam);
        nx = diffMod(nx, x, mod);
        nx = diffMod(nx, x3, mod);

        s = diffMod(x, nx, mod);
        ny = productMod(lam, s);
        ny = diffMod(ny, y, mod);

        nz = 1;
      } /* end if/else/else... */

      x3T[i] = nx; y3T[i] = ny; z3T[i] = nz;
      ++itersT[i];
    } /* end for (i) */

  } /* end while */

  saveTime = getTime();
  if ((savHandle = fopen(SAV_FILE, "w")) != NULL) {
    for (i = 0UL; i < PARAL; i++) {
      fprintf( savHandle, savw, startvT[i].hi, startvT[i].lo, itersT[i],
               u3T[i].hi, u3T[i].lo, v3T[i].hi, v3T[i].lo,
               saveTime-timeT[i]
             );
    } /* end for */
    fclose(savHandle);
  } /* end if */

  return 0;
} /* end main */


/*== Arithmetic for field Z/pZ, p odd, using 2-adic inverse ================*/

/*-- encode ----------------------------------------------------------------*/

/* Encode x modulo odd modulus, 0 <= x < modulus < 2^97.
 * Point coordinates are encoded by multiplying by 2^97 modulo the prime
 * so that we can multiply modulo the prime quickly using a precomputed
 * 2-adic inverse (as described by Peter Montgomery).
 */
static INLINE u128 encode(u128 x) {
  const u128 code = CODE;

  return productMod(x, code);
} /* end encode */


/*-- decode ----------------------------------------------------------------*/

/* Decode x modulo odd modulus, 0 <= x < modulus < 2^97. */
static u128 decode(u128 x) {
  u64 mh,ml, px,ph,pm,pl, rh,rl, uh,ul, vh,vl, xh,xl;
  u128 z;

  xh = x.hi; xl = x.lo;
  { u64 ih, il;

    ih = INV_HI; il = INV_LO;
    rh = HiMul(il, xl)+il*xh+ih*xl; rh &= 0x1ffffffffUL;
    rl = il*xl;
  } /* end block */


  /* Karatsuba. */
  mh = MOD_HI; ml = MOD_LO;
  { u64 c, d, qx,qh,ql, sign, mm, rm;

    pl = ml*rl;
    ph = (mh & 0xffffffffUL)*rh;

    mm = ml-mh;
    sign = rl < rh;
    rm = rl-rh; if (sign) rm = rh-rl;

    ql = mm*rm;

    px = rh>>32;

    pm = HiMul(ml, rl);

    if (px) { u64 um = mh<<32; px += ph < um; }

    qh = HiMul(mm, rm);

    { u64 ur = rh<<32; ph += ur; px += ph < ur; }

    if (sign) {
      ql += pl; c = ql < pl; qh += pm; qx = qh < pm; qh += c; qx += qh < c;
    } else {
      c = pl < ql; ql = pl-ql; qx = -(pm < qh); qh = pm-qh;
      qx -= qh < c; qh -= c;
    } /* end if/else */

    ql += ph; c = ql < ph; qh += c; qx += qh < c; qh += px; qx += qh < px;
    pm += ql; d = pm < ql; ph += d; px += ph < d; ph += qh; px += ph < qh;
    px += qx;
  } /* end block */


  ul = pm>>33 | ph<<31; uh = ph>>33 | px<<31;

  vh = vl = 0UL;
  if (uh | ul) { vh = mh-uh; vl = ml-ul; vh -= ml < ul; }

  z.hi = vh; z.lo = vl;
  return z;
} /* end decode */


/*-- inverseMod ------------------------------------------------------------*/

/* Divide 1 by y modulo odd modulus, 0 < y < modulus < 2^128.
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
  if (t > 97UL) {
    u64 fh,fl;
    const u128 fix = FIX;

    t -= 97UL;
    fh = fix.hi; fl = fix.lo;
    do {
      u64 o;

      o = ul & 1UL;
      ul >>= 1; ul |= uh<<63; uh >>= 1;
      if (o) { uh += fh; ul += fl; uh += ul < fl; }
      --t;
    } while (t);
  } else if (t < 97UL) {
    u64 mh,ml;

    t = 97UL-t;
    mh = mod.hi; ml = mod.lo;
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

/* Divide x by y modulo odd modulus, 0 <= x,y < modulus < 2^97, y != 0. */

static INLINE u128 quotientMod(u128 x, u128 y) {
  u128 z;

  z = inverseMod(y);

  return productMod(x, z);
} /* end quotientMod */


/*-- squareMod -------------------------------------------------------------*/

/* Square of x modulo odd modulus, 0 <= x < modulus < 2^97.
 * Input must be encoded and output is too.
 */
static u128 squareMod(u128 x) {
  u64 c, mh,ml, px,ph,pm,pl, rh,rl, t, uh,ul, vh,vl, xh,xl;
  u128 z;

  xh = x.hi; xl = x.lo;

  t = xh*xl;
  ph = HiMul(xh, xl);
  pm = HiMul(xl, xl);
  ph = ph<<1 | t>>63; t <<= 1;
  pm += t; ph += pm < t;
  t = xh & 0xffffffffUL; t = t*t;
  px = xh>>32;
  pl = xl*xl;
  if (px) { u64 tx = xh<<32; px += tx>>63; tx <<= 1; t += tx; px += t < tx; }
  ph += t; px += ph < t;

  ul = pl; uh = pm & 0x1ffffffffUL;
  vl = pm>>33 | ph<<31; vh = ph>>33 | px<<31;

  { u64 ih, il;

    ih = INV_HI; il = INV_LO;
    rh = HiMul(il, ul)+il*uh+ih*ul; rh &= 0x1ffffffffUL;
    rl = il*ul;
  } /* end block */


  /* Karatsuba. */
  mh = MOD_HI; ml = MOD_LO;
  { u64 c, d, qx,qh,ql, sign, mm, rm;

    pl = ml*rl;
    ph = (mh & 0xffffffffUL)*rh;

    mm = ml-mh;
    sign = rl < rh;
    rm = rl-rh; if (sign) rm = rh-rl;

    ql = mm*rm;

    px = rh>>32;

    pm = HiMul(ml, rl);

    if (px) { u64 um = mh<<32; px += ph < um; }

    qh = HiMul(mm, rm);

    { u64 ur = rh<<32; ph += ur; px += ph < ur; }

    if (sign) {
      ql += pl; c = ql < pl; qh += pm; qx = qh < pm; qh += c; qx += qh < c;
    } else {
      c = pl < ql; ql = pl-ql; qx = -(pm < qh); qh = pm-qh;
      qx -= qh < c; qh -= c;
    } /* end if/else */

    ql += ph; c = ql < ph; qh += c; qx += qh < c; qh += px; qx += qh < px;
    pm += ql; d = pm < ql; ph += d; px += ph < d; ph += qh; px += ph < qh;
    px += qx;
  } /* end block */


  ul = pm>>33 | ph<<31; uh = ph>>33 | px<<31;

  if (vh < uh || (vh == uh && vl < ul)) { vh += mh; vl += ml; vh += vl < ml; }

  vh -= uh; c = vl < ul; vl -= ul; vh -= c;

  z.hi = vh; z.lo = vl;
  return z;
} /* end squareMod */


/*-- productMod ------------------------------------------------------------*/

/* Product of x and y modulo odd modulus, 0 <= x, y < modulus < 2^97.
 * Input must be encoded and output is too.
 */
static u128 productMod(u128 x, u128 y) {
  u64 mh,ml, px,ph,pm,pl, rh,rl, uh,ul, vh,vl, xh,xl, yh,yl;
  u128 z;

  xh = x.hi; xl = x.lo;
  yh = y.hi; yl = y.lo;

  /* Karatsuba. */
  { u64 c, d, qx,qh,ql, sign, t,tx,ty, xm, ym;

    pl = xl*yl;
    ph = (xh & 0xffffffffUL)*yh;

    sign = xl < xh;
    xm = xl-xh; if (sign) xm = xh-xl;
    t = yl < yh; sign ^= t;
    ym = yl-yh; if (t) ym = yh-yl;

    ql = xm*ym;

    tx = xh>>32; ty = yh>>32;
    px = tx & ty;

    pm = HiMul(xl, yl);

    if (ty) { u64 ux = xh<<32; px += ph < ux;  }

    qh = HiMul(xm, ym);

    if (tx) { u64 uy = yh<<32; ph += uy; px += ph < uy; }

    if (sign) {
      ql += pl; c = ql < pl; qh += pm; qx = qh < pm; qh += c; qx += qh < c;
    } else {
      c = pl < ql; ql = pl-ql; qx = -(pm < qh); qh = pm-qh;
      qx -= qh < c; qh -= c;
    } /* end if/else */

    ql += ph; c = ql < ph; qh += c; qx += qh < c; qh += px; qx += qh < px;
    pm += ql; d = pm < ql; ph += d; px += ph < d; ph += qh; px += ph < qh;
    px += qx;
  } /* end block */

  ul = pl; uh = pm;
  vl = pm>>33 | ph<<31; vh = ph>>33 | px<<31;

  { u64 ih, il;

    ih = INV_HI; il = INV_LO;
    rh = HiMul(il, ul)+ih*ul+il*uh; rh &= 0x1ffffffffUL;
    rl = il*ul;
  } /* end block */

  /* Karatsuba. */
  mh = MOD_HI; ml = MOD_LO;
  { u64 c, d, qx,qh,ql, sign, mm, rm;

    pl = ml*rl;
    ph = (mh & 0xffffffffUL)*rh;

    mm = ml-mh;
    sign = rl < rh;
    rm = rl-rh; if (sign) rm = rh-rl;

    ql = mm*rm;

    px = rh>>32;

    pm = HiMul(ml, rl);

    if (px) { u64 um = mh<<32; px += ph < um; }

    qh = HiMul(mm, rm);

    { u64 ur = rh<<32; ph += ur; px += ph < ur; }

    if (sign) {
      ql += pl; c = ql < pl; qh += pm; qx = qh < pm; qh += c; qx += qh < c;
    } else {
      c = pl < ql; ql = pl-ql; qx = -(pm < qh); qh = pm-qh;
      qx -= qh < c; qh -= c;
    } /* end if/else */

    ql += ph; c = ql < ph; qh += c; qx += qh < c; qh += px; qx += qh < px;
    pm += ql; d = pm < ql; ph += d; px += ph < d; ph += qh; px += ph < qh;
    px += qx;
  } /* end block */


  ul = pm>>33 | ph<<31; uh = ph>>33 | px<<31;

  if (vh < uh || (vh == uh && vl < ul)) { vh += mh; vl += ml; vh += vl < ml; }

  { u64 c; vh -= uh; c = vl < ul; vl -= ul; vh -= c; }

  z.hi = vh; z.lo = vl;
  return z;
} /* end productMod */


/*== Stuff for elliptic curve y^2 = x^3 + a*x + b ==========================*/

/*-- ellipticSum -----------------------------------------------------------*/

/* Given pts (x1:y1:z1) and (x2:y2:z2) on y^2 = x^3+a*x+b,
 * computes their sum (x3:y3:z3) by the group law.  Doesn't actually need b.
 * Puts x3 at *px3 and y3 at *py3, and returns z3.
 * The point at infinity is represented by (0:1:0), with encoded 1.
 * Finite points are represented by (x:y:1), with encoded coordinates x and y.
 */
static int ellipticSum
  ( u128 x1, u128 y1, int z1, u128 x2, u128 y2, int z2
  , u128 a, u128 *px3, u128 *py3
  ) {
  u128 den, lam, num, s, x3, y3;
  const u128 mod = MOD;

  if (z1 == 0) { *px3 = x2; *py3 = y2; return z2; }
  if (z2 == 0) { *px3 = x1; *py3 = y1; return z1; }

  if (equal(x1, x2)) {
    const u128 one = ONE;

    if (equal(y1, y2)) return ellipticDouble(x1, y1, z1, a, px3, py3);
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

/* Given point (x, y) on y^2 = x^3+a*x+b, this computes its double
 * (x2:y2:z2) by the group law.  Doesn't actually need b.
 * Puts x2 at *px2 and y2 at *py2, and returns z2.
 * The point at infinity is represented by (0:1:0), with encoded 1.
 * Finite points are represented by (x:y:1), with encoded coordinates x and y.
 */
static int ellipticDouble
  ( u128 x, u128 y, int z, u128 a, u128 *px2, u128 *py2
  ) {
  u128 den, lam, num, s, t, x2, y2;
  const u128 mod = MOD;

  if (z == 0 || (y.hi | y.lo) == 0UL) {
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

/* Given point (x:y:z) on y^2 + x*y = x^3 + a*x^2 + b, this computes its
 * fac-th multiple (x2:y2:z2) by the group law.  Doesn't actually need b.
 * Puts x2 at *px2 and y2 at *py2, and returns z2.
 * The point at infinity is represented by (0:1:0), with encoded 1.
 * Finite points are represented by (x:y:1), with encoded coordinates x and y.
 */
static int ellipticProduct
  ( u128 x, u128 y, int z, u128 fac, u128 a
  , u128 *px2, u128 *py2
  ) {
  int z2;
  u64 fh, fl, m;
  u128 x2, y2;
  const u128 zero = { 0UL, 0UL }, one = ONE;

  if (equal(fac, zero)) { *px2 = zero; *py2 = one; return 0; }

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
  } else { x2 = zero; y2 = one; z2 = 0; }

  m = (u64)1UL<<63;
  fl = fac.lo;
  do {
    z2 = ellipticDouble(x2, y2, z2, a, &x2, &y2);
    if (fl & m) z2 = ellipticSum(x, y, z, x2, y2, z2, a, &x2, &y2);
    m >>= 1;
  } while (m);

  *px2 = x2; *py2 = y2; return z2;
} /* end ellipticProduct */


/*== Utility stuff. ========================================================*/

/*-- loadIni ---------------------------------------------------------------*/

/* Get the setup data in the ini file. */
static int loadIni(void) {
  FILE *iniHandle;
  struct hostent *hp;
  u32 addr;
  char buf[BUFLEN];

  if ((iniHandle = fopen(INI_FILE, "r")) == NULL) return 0; /* No ini file. */

  if (fgets(buf, BUFLEN, iniHandle) == NULL) { /* First choice dest. */
    fclose(iniHandle);
    return 0; /* Fault. */
  }
  if ((addr = inet_addr(buf)) == -1) {
    if ((hp = gethostbyname(buf)) == NULL) addr = -1;
    else addr = *(u32 *)hp->h_addr_list[0];
  } /* end if */
  if (addr != -1)
    proxy1addr = ntohl(addr); /* Proxyaddr is kept in host byte order. */

  if (fgets(buf, BUFLEN, iniHandle) == NULL) { /* Second choice dest. */
    fclose(iniHandle);
    return 0; /* Fault. */
  } /* end if */
  if ((addr = inet_addr(buf)) == -1) {
    if ((hp = gethostbyname(buf)) == NULL) addr = -1;
    else addr = *(u32 *)hp->h_addr_list[0];
  } /* end if */
  if (addr != -1)
    proxy2addr = ntohl(addr); /* Proxyaddr is kept in host byte order. */

  if (fgets(buf, BUFLEN, iniHandle) == NULL) { /* Port. */
    fclose(iniHandle);
    return 0; /* Fault. */
  } /* end if */
  proxyport = atoi(buf) & 0xffff;
  if (fgets(buf, BUFLEN, iniHandle) == NULL) { /* Mail flag. */
    fclose(iniHandle);
    return 0; /* Fault. */
  } /* end if */
  protocol = atoi(buf) & 0xffff;

  if (fgets(buf, BUFLEN, iniHandle) == NULL) { /* Sender id. */
    fclose(iniHandle);
    return 0; /* Fault. */
  } /* end if */
  buf[strlen(buf)-1] = '\0';
  strncpy(frombuf, buf, 128);
  if (fgets(buf, BUFLEN, iniHandle) != NULL) { /* Freeform - optional. */
    buf[strlen(buf)-1] = '\0';
    strncpy(freeform, buf, 256);
  } /* end if */

  fclose(iniHandle);
  return 1;
} /* end loadIni */


/*-- sendIt ----------------------------------------------------------------*/

/* Send information by mail or TCP, or just log it. */
static void sendIt(char *buf, int len) {
  FILE *pipeHandle, *bufHandle;
  int status;
  int fd, fault;
  struct sockaddr_in addr;
  char lbuf[MSGLEN+3];

  fault = 0;
  switch (protocol) {
  case PROTO_MAIL:

#ifndef VMS
    /* Don't use mail on VMS. */
    pipeHandle = popen("/usr/lib/sendmail " MAILADDR, "w");
    if (pipeHandle == NULL) {
      puts("Warning: couldn't pipe to sendmail\n");
      fflush(stdout);
    } else {
      fputs(buf, pipeHandle);
      fflush(pipeHandle);
      status = pclose(pipeHandle);
      if (status != 0) {
        printf("Warning: sendmail returned status %d\n", status);
        fflush(stdout);
      } /* end if */
    } /* end if/else */
#endif
    break;

  case PROTO_TCP:
    fault = 0;
    fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd > 0) {
      addr.sin_family = AF_INET;
      addr.sin_port = htons(proxyport);
      addr.sin_addr.s_addr = htonl(proxy1addr);
      if (connect(fd, (struct sockaddr *)&addr, sizeof(addr)) >= 0) {
        if ((bufHandle = fopen(BUF_FILE, "r")) != NULL) {
          while(fgets(lbuf, MSGLEN+3, bufHandle) != NULL) {
            if (send(fd, lbuf, strlen(lbuf), 0) < 0) {
              fault = 1;
              break;
            } /* end if */
          } /* end while */
          fclose(bufHandle);
          if (!fault) remove(BUF_FILE);
        } /* end if */
        if (send(fd, buf, len, 0) < 0) fault = 1;
      } else fault = 1;
      close(fd);
    } else fault = 1;

    if (!fault) break;

    fault = 0;
    fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd > 0) {
      addr.sin_family = AF_INET;
      addr.sin_port = htons(proxyport);
      addr.sin_addr.s_addr = htonl(proxy2addr);
      if (connect(fd, (struct sockaddr *)&addr, sizeof(addr)) >= 0) {
        if ((bufHandle=fopen(BUF_FILE, "r")) != NULL) {
          while(fgets(lbuf, MSGLEN+3, bufHandle) != NULL) {
            if (send(fd, lbuf, strlen(lbuf), 0) < 0) {
              fault = 1;
              break;
            } /* end if */
          } /* end while */
          fclose(bufHandle);
          if (!fault) remove(BUF_FILE);
        } /* end if */
        if (send(fd, buf, len, 0) < 0) fault = 1;
      } else fault = 1;
      close(fd);
    } else fault = 1;
    break;

  default:
    break;

  } /* end switch */

  if (fault && ((bufHandle=fopen(BUF_FILE, "a")) != NULL)) {
    fputs(buf, bufHandle);
    fclose(bufHandle);
  } /* end if */

  fputs(buf, stdout); /* Log it. */
  fflush(stdout);
} /* end sendIt */


/*-- getTime ---------------------------------------------------------------*/

/* Get current process usage time. */
static double getTime(void) {

#ifdef VMS
  struct tms tm;

  times(&tm);

  return (double)( tm.tms_utime
#ifdef SYS_TIME
                   + tm.tms_stime
#endif
                 )/CLOCKS_PER_SEC;
#else
  struct rusage ru;

  getrusage(RUSAGE_SELF, &ru);

  return (double)( ru.ru_utime.tv_sec
#ifdef SYS_TIME
                   + ru.ru_stime.tv_sec
#endif
                 )
         + (double)( ru.ru_utime.tv_usec
#ifdef SYS_TIME
                     + ru.ru_stime.tv_usec
#endif
                   )/1000000.0
  ;
#endif

} /* end getTime */


/*== end of file eccp97b.c =================================================*/
