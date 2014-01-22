#include <stdio.h>

#define TRUE 1
#define FALSE 0

typedef unsigned char uchar;
typedef unsigned int  bool;

#ifdef _MSC_VER
#define CALLEXTERNALASMCODE
#endif
#ifdef OS2
#define CALLEXTERNALASMCODE
#endif
#ifdef __GNUC__
#if #cpu(i386) && (TRUE)
#define CALLEXTERNALASMCODE
#endif
#endif

#ifdef __GNUC__
#if #cpu(i386) && (TRUE)

#define LOAD(regcode, regvar, memvar) \
asm volatile(""                 \
        : regcode (regvar) ,"=b" (ksp) \
        : "0"  (memvar) , "1" (ksp))

#define STORE(regcode, memvar, regvar) \
asm volatile(""                 \
        : regcode (memvar) , "=b" (ksp) \
        : "0"  (regvar) , "1" (ksp))

#define XOR(regcode, regvar, bitmask) \
asm volatile(""                 \
        : regcode (regvar)      \
        : "0"  ((unsigned char)(regvar ^ (bitmask))) )

#define GKST15(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9, n10,r10, n11,r11, n12,r12, n13,r13, n14,r14, n15,r15) \
  { \
  unsigned char ta, tb, tc, *ksp=(unsigned char *)&ks[0]; \
  GKSTA2(n1 ,r1 ,n2 ,r2 ); \
  GKSTA2(n3 ,r3 ,n4 ,r4 ); \
  GKSTA2(n5 ,r5 ,n6 ,r6 ); \
  GKSTA2(n7 ,r7 ,n8 ,r8 ); \
  GKSTA2(n9 ,r9 ,n10,r10); \
  GKSTA2(n11,r11,n12,r12); \
  GKSTA3(n13,r13,n14,r14,n15,r15); \
  }

#define GKST14(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9, n10,r10, n11,r11, n12,r12, n13,r13, n14,r14) \
  { \
  unsigned char ta, tb, *ksp=(unsigned char *)&ks[0]; \
  GKSTA2(n1 ,r1 ,n2 ,r2 ); \
  GKSTA2(n3 ,r3 ,n4 ,r4 ); \
  GKSTA2(n5 ,r5 ,n6 ,r6 ); \
  GKSTA2(n7 ,r7 ,n8 ,r8 ); \
  GKSTA2(n9 ,r9 ,n10,r10); \
  GKSTA2(n11,r11,n12,r12); \
  GKSTA2(n13,r13,n14,r14); \
  }

#define GKST13(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9, n10,r10, n11,r11, n12,r12, n13,r13) \
  { \
  unsigned char ta, tb, tc, *ksp=(unsigned char *)&ks[0]; \
  GKSTA2(n1 ,r1 ,n2 ,r2 ); \
  GKSTA2(n3 ,r3 ,n4 ,r4 ); \
  GKSTA2(n5 ,r5 ,n6 ,r6 ); \
  GKSTA2(n7 ,r7 ,n8 ,r8 ); \
  GKSTA2(n9 ,r9 ,n10,r10); \
  GKSTA3(n11,r11,n12,r12,n13,r13); \
  }

#define GKST12(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9, n10,r10, n11,r11, n12,r12) \
  { \
  unsigned char ta, tb, *ksp=(unsigned char *)&ks[0]; \
  GKSTA2(n1 ,r1 ,n2 ,r2 ); \
  GKSTA2(n3 ,r3 ,n4 ,r4 ); \
  GKSTA2(n5 ,r5 ,n6 ,r6 ); \
  GKSTA2(n7 ,r7 ,n8 ,r8 ); \
  GKSTA2(n9 ,r9 ,n10,r10); \
  GKSTA2(n11,r11,n12,r12); \
  }

#define GKST11(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9, n10,r10, n11,r11) \
  { \
  unsigned char ta, tb, tc, *ksp=(unsigned char *)&ks[0]; \
  GKSTA2(n1 ,r1 ,n2 ,r2 ); \
  GKSTA2(n3 ,r3 ,n4 ,r4 ); \
  GKSTA2(n5 ,r5 ,n6 ,r6 ); \
  GKSTA2(n7 ,r7 ,n8 ,r8 ); \
  GKSTA3(n9 ,r9 ,n10,r10,n11,r11); \
  }

#define GKST10(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9, n10,r10) \
  { \
  unsigned char ta, tb, *ksp=(unsigned char *)&ks[0]; \
  GKSTA2(n1 ,r1 ,n2 ,r2 ); \
  GKSTA2(n3 ,r3 ,n4 ,r4 ); \
  GKSTA2(n5 ,r5 ,n6 ,r6 ); \
  GKSTA2(n7 ,r7 ,n8 ,r8 ); \
  GKSTA2(n9 ,r9 ,n10,r10); \
  }

#define GKST9(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9) \
  { \
  unsigned char ta, tb, tc, *ksp=(unsigned char *)&ks[0]; \
  GKSTA2(n1 ,r1 ,n2 ,r2 ); \
  GKSTA2(n3 ,r3 ,n4 ,r4 ); \
  GKSTA2(n5 ,r5 ,n6 ,r6 ); \
  GKSTA3(n7 ,r7 ,n8 ,r8 ,n9 ,r9); \
  }

#define GKST8(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8) \
  { \
  unsigned char ta, tb, *ksp=(unsigned char *)&ks[0]; \
  GKSTA2(n1 ,r1 ,n2 ,r2 ); \
  GKSTA2(n3 ,r3 ,n4 ,r4 ); \
  GKSTA2(n5 ,r5 ,n6 ,r6 ); \
  GKSTA2(n7 ,r7 ,n8 ,r8 ); \
  }

#define GKST7(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7) \
  { \
  unsigned char ta, tb, tc, *ksp=(unsigned char *)&ks[0]; \
  GKSTA2(n1 ,r1 ,n2 ,r2 ); \
  GKSTA2(n3 ,r3 ,n4 ,r4 ); \
  GKSTA3(n5 ,r5 ,n6 ,r6 ,n7, r7); \
  }

#define GKST3(n1,r1,n2,r2,n3,r3) \
  { \
  unsigned char ta, tb, tc, *ksp=(unsigned char *)&ks[0]; \
  GKSTA3(n1 ,r1 ,n2 ,r2 ,n3 , r3); \
  }

#define GKST2(n1,r1,n2,r2) \
  { \
  unsigned char ta, tb, *ksp=(unsigned char *)&ks[0]; \
  GKSTA2(n1 ,r1 ,n2 ,r2 ); \
  }

#define GKST1(n1,r1) \
  { \
  unsigned char ta, *ksp=(unsigned char *)&ks[0]; \
  GKSTA1(n1 ,r1); \
  }


#define GKSBYTE(round,bit3,bit54) (*(ksp+8*round+((bit3)<<2)+(3-(bit54))))
#define GKSTA1(around,abit) \
    GKSTS1(around,((abit-1)/12),(((abit-1)/6)&1),((abit-1)%6),(abit!=0))
#define GKSTS1(around,abit54,abit3,abits210,abitnz) \
    GKSTB1(around,3&(abit54+abit3*abits210/4),abit3,7&(abits210+abit3*4),abitnz)
#define GKSTA2(around,abit,bround,bbit) \
    GKSTS2(around,((abit-1)/12),(((abit-1)/6)&1),((abit-1)%6),(abit!=0), \
          bround,((bbit-1)/12),(((bbit-1)/6)&1),((bbit-1)%6),(bbit!=0))
#define GKSTS2(around,abit54,abit3,abits210,abitnz, \
               bround,bbit54,bbit3,bbits210,bbitnz) \
    GKSTB2(around,3&(abit54+abit3*abits210/4),abit3,7&(abits210+abit3*4),abitnz, \
           bround,3&(bbit54+bbit3*bbits210/4),bbit3,7&(bbits210+bbit3*4),bbitnz)
#define GKSTA3(around,abit,bround,bbit,cround,cbit) \
    GKSTS3(around,((abit-1)/12),(((abit-1)/6)&1),((abit-1)%6),(abit!=0), \
           bround,((bbit-1)/12),(((bbit-1)/6)&1),((bbit-1)%6),(bbit!=0), \
           cround,((cbit-1)/12),(((cbit-1)/6)&1),((cbit-1)%6),(cbit!=0))
#define GKSTS3(around,abit54,abit3,abits210,abitnz, \
               bround,bbit54,bbit3,bbits210,bbitnz, \
               cround,cbit54,cbit3,cbits210,cbitnz) \
    GKSTB3(around,3&(abit54+abit3*abits210/4),abit3,7&(abits210+abit3*4),abitnz, \
           bround,3&(bbit54+bbit3*bbits210/4),bbit3,7&(bbits210+bbit3*4),bbitnz, \
           cround,3&(cbit54+cbit3*cbits210/4),cbit3,7&(cbits210+cbit3*4),cbitnz)
#define GKSTB1(around,abit54,abit3,abits210,abitnz) \
  { \
  LOAD ("=a", ta, GKSBYTE(around,abit3,abit54) ); \
  XOR  ("=a", ta, ((abitnz*0x80)>>(abitnz*abits210)) ); \
  STORE("=a", GKSBYTE(around,abit3,abit54), ta ); \
  }
#define GKSTB2(around,abit54,abit3,abits210,abitnz,bround,bbit54,bbit3,bbits210,bbitnz) \
  { \
  LOAD ("=a", ta, GKSBYTE(around,abit3,abit54) ); \
  XOR  ("=a", ta, ((abitnz*0x80)>>(abitnz*abits210)) ); \
  LOAD ("=d", tb, GKSBYTE(bround,bbit3,bbit54) ); \
  STORE("=a", GKSBYTE(around,abit3,abit54), ta ); \
  XOR  ("=d", tb, ((bbitnz*0x80)>>(bbitnz*bbits210)) ); \
  STORE("=d", GKSBYTE(bround,bbit3,bbit54), tb ); \
  }
#define GKSTB3(around,abit54,abit3,abits210,abitnz, \
              bround,bbit54,bbit3,bbits210,bbitnz, \
              cround,cbit54,cbit3,cbits210,cbitnz) \
  { \
  LOAD ("=a", ta, GKSBYTE(around,abit3,abit54) ); \
  LOAD ("=d", tb, GKSBYTE(bround,bbit3,bbit54) ); \
  XOR  ("=a", ta, ((abitnz*0x80)>>(abitnz*abits210)) ); \
  LOAD ("=c", tc, GKSBYTE(cround,cbit3,cbit54) );  \
  XOR  ("=d", tb, ((bbitnz*0x80)>>(bbitnz*bbits210)) ); \
  STORE("=a", GKSBYTE(around,abit3,abit54), ta ); \
  XOR  ("=c", tc, ((cbitnz*0x80)>>(cbitnz*cbits210)) ); \
  STORE("=d", GKSBYTE(bround,bbit3,bbit54), tb ); \
  STORE("=c", GKSBYTE(cround,cbit3,cbit54), tc ); \
  }

#endif /* i386 */
#endif /* __GNUC__ */

#define CKST15(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9, n10,r10, n11,r11, n12,r12, n13,r13, n14,r14, n15,r15) \
  { \
  CKSTA(n1 ,r1 ); \
  CKSTA(n2 ,r2 ); \
  CKSTA(n3 ,r3 ); \
  CKSTA(n4 ,r4 ); \
  CKSTA(n5 ,r5 ); \
  CKSTA(n6 ,r6 ); \
  CKSTA(n7 ,r7 ); \
  CKSTA(n8 ,r8 ); \
  CKSTA(n9 ,r9 ); \
  CKSTA(n10,r10); \
  CKSTA(n11,r11); \
  CKSTA(n12,r12); \
  CKSTA(n13,r13); \
  CKSTA(n14,r14); \
  CKSTA(n15,r15); \
  }

#define CKST14(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9, n10,r10, n11,r11, n12,r12, n13,r13, n14,r14) \
  { \
  CKSTA(n1 ,r1 ); \
  CKSTA(n2 ,r2 ); \
  CKSTA(n3 ,r3 ); \
  CKSTA(n4 ,r4 ); \
  CKSTA(n5 ,r5 ); \
  CKSTA(n6 ,r6 ); \
  CKSTA(n7 ,r7 ); \
  CKSTA(n8 ,r8 ); \
  CKSTA(n9 ,r9 ); \
  CKSTA(n10,r10); \
  CKSTA(n11,r11); \
  CKSTA(n12,r12); \
  CKSTA(n13,r13); \
  CKSTA(n14,r14); \
  }

#define CKST13(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9, n10,r10, n11,r11, n12,r12, n13,r13) \
  { \
  CKSTA(n1 ,r1 ); \
  CKSTA(n2 ,r2 ); \
  CKSTA(n3 ,r3 ); \
  CKSTA(n4 ,r4 ); \
  CKSTA(n5 ,r5 ); \
  CKSTA(n6 ,r6 ); \
  CKSTA(n7 ,r7 ); \
  CKSTA(n8 ,r8 ); \
  CKSTA(n9 ,r9 ); \
  CKSTA(n10,r10); \
  CKSTA(n11,r11); \
  CKSTA(n12,r12); \
  CKSTA(n13,r13); \
  }

#define CKST12(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9, n10,r10, n11,r11, n12,r12) \
  { \
  CKSTA(n1 ,r1 ); \
  CKSTA(n2 ,r2 ); \
  CKSTA(n3 ,r3 ); \
  CKSTA(n4 ,r4 ); \
  CKSTA(n5 ,r5 ); \
  CKSTA(n6 ,r6 ); \
  CKSTA(n7 ,r7 ); \
  CKSTA(n8 ,r8 ); \
  CKSTA(n9 ,r9 ); \
  CKSTA(n10,r10); \
  CKSTA(n11,r11); \
  CKSTA(n12,r12); \
  }

#define CKST11(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9, n10,r10, n11,r11) \
  { \
  CKSTA(n1 ,r1 ); \
  CKSTA(n2 ,r2 ); \
  CKSTA(n3 ,r3 ); \
  CKSTA(n4 ,r4 ); \
  CKSTA(n5 ,r5 ); \
  CKSTA(n6 ,r6 ); \
  CKSTA(n7 ,r7 ); \
  CKSTA(n8 ,r8 ); \
  CKSTA(n9 ,r9 ); \
  CKSTA(n10,r10); \
  CKSTA(n11,r11); \
  }

#define CKST10(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9, n10,r10) \
  { \
  CKSTA(n1 ,r1 ); \
  CKSTA(n2 ,r2 ); \
  CKSTA(n3 ,r3 ); \
  CKSTA(n4 ,r4 ); \
  CKSTA(n5 ,r5 ); \
  CKSTA(n6 ,r6 ); \
  CKSTA(n7 ,r7 ); \
  CKSTA(n8 ,r8 ); \
  CKSTA(n9 ,r9 ); \
  CKSTA(n10,r10); \
  }

#define CKST9(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8, \
         n9,r9) \
  { \
  CKSTA(n1 ,r1 ); \
  CKSTA(n2 ,r2 ); \
  CKSTA(n3 ,r3 ); \
  CKSTA(n4 ,r4 ); \
  CKSTA(n5 ,r5 ); \
  CKSTA(n6 ,r6 ); \
  CKSTA(n7 ,r7 ); \
  CKSTA(n8 ,r8 ); \
  CKSTA(n9 ,r9 ); \
  }

#define CKST8(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7, n8,r8) \
  { \
  CKSTA(n1 ,r1 ); \
  CKSTA(n2 ,r2 ); \
  CKSTA(n3 ,r3 ); \
  CKSTA(n4 ,r4 ); \
  CKSTA(n5 ,r5 ); \
  CKSTA(n6 ,r6 ); \
  CKSTA(n7 ,r7 ); \
  CKSTA(n8 ,r8 ); \
  }

#define CKST7(n1,r1, n2,r2, n3,r3, n4,r4, n5,r5, n6,r6, n7,r7) \
  { \
  CKSTA(n1 ,r1 ); \
  CKSTA(n2 ,r2 ); \
  CKSTA(n3 ,r3 ); \
  CKSTA(n4 ,r4 ); \
  CKSTA(n5 ,r5 ); \
  CKSTA(n6 ,r6 ); \
  CKSTA(n7 ,r7 ); \
  }

#define CKST3(n1,r1,n2,r2,n3,r3) \
  { \
  CKSTA(n1 ,r1 ); \
  CKSTA(n2 ,r2 ); \
  CKSTA(n3 ,r3 ); \
  }

#define CKST2(n1,r1,n2,r2) \
  { \
  CKSTA(n1 ,r1 ); \
  CKSTA(n2 ,r2 ); \
  }

#define CKST1(n1,r1) \
  { \
  CKSTA(n1 ,r1 ); \
  }

#define CKSTA(round,bit) \
    CKSTS(round,((bit-1)/12),(((bit-1)/6)&1),((bit-1)%6),(bit!=0))
#define CKSTS(round,bit54,bit3,bits210,bitnz) \
    CKSTB(round,3&(bit54+bit3*bits210/4),bit3,7&(bits210+bit3*4),bitnz)
#ifdef LITTLEENDIAN
#define CKSTB(round,bit54,bit3,bits210,bitnz) \
  ks[round][((bit3)<<2)+(3-(bit54))] ^= (bitnz*0x80)>>(bitnz*bits210);
#endif /* LITTLEENDIAN */
#ifdef BIGENDIAN
#define CKSTB(round,bit54,bit3,bits210,bitnz) \
  ks[round][((bit3)<<2)+(bit54)] ^= (bitnz*0x80)>>(bitnz*bits210);
#endif /* BIGENDIAN */

#define KSTO01 {KST14 (0,20,1,10,2,16,3,24,4, 8,5,17,6, 4,     8,11,9,14,10, 2,11, 9,12,23,13, 3,      15,18)}
#define KSTO02 {KST15 (0, 9,1, 1,2,15,3,12,4,18,5,10,6,16,7,24,8, 5,9,21,      11,13,12,11,13,14,14, 2,15,19)}
#define KSTO03 {KST13 (0,13,     2,22,     4,19,5, 1,6,15,7,12,     9,20,10, 6,11, 7,12, 5,13,21,14, 0,15, 4)}
#define KSTO04 {KST14 (0,30,     2,26,3,45,4,36,5,43,6,37,7,44,8,25,9,39,10,28,      12,35,13,27,14,47,15,40)}
#define KSTO05 {KST14 (0,33,1,45,2,36,3,43,4,37,5,44,6,32,     8,28,     10,35,11,27,12,47,13,30,14,42,15,26)}
#define KSTO06 {KST14 (     1,44,2,32,     4,46,5,41,6,48,7,31,8,47,9,30,10,42,11,33,12,38,13,29,14,34,15,37)}
#define KSTO09 {KST14 (0,10,1, 6,2, 7,3, 5,4,21,     6,13,7,11,8,22,     10,19,11, 1,12,15,13,12,14,18,15,20)}
#define KSTO10 {KST13 (0, 1,1,23,2, 3,     4,20,5, 6,6, 7,7, 5,8, 8,9,17,10, 4,      12,22,      14,19,15, 9)}
#define KSTO11 {KST14 (     1,11,2,14,3, 2,4, 9,5,23,6, 3,     8,18,9,10,10,16,11,24,12, 8,13,17,14, 4,15,13)}
#define KSTO13 {KST14 (0,45,1,38,2,29,3,34,     5,25,6,39,7,28,8,46,9,41,10,48,11,31,12,40,      14,26,15,33)}
#define KSTO14 {KST13 (0,44,1,25,2,39,3,28,     5,35,6,27,7,47,8,40,     10,26,11,45,12,36,13,43,14,37      )}
#define KSTO15 {KST14 (0,41,1,35,2,27,3,47,4,30,5,42,6,33,7,38,8,36,9,43,10,37,11,44,12,32,      14,46      )}
#define KSTO17 {KST14 (0, 6,1,16,2,24,3, 8,4,17,5, 4,     7,22,8,14,9, 2,10, 9,11,23,12, 3,      14,20,15,10)}
#define KSTO18 {KST15 (0,23,1,15,2,12,3,18,4,10,5,16,6,24,7, 8,8,21,     10,13,11,11,12,14,13, 2,14, 9,15, 1)}
#define KSTO19 {KST13 (0,11,1,22,     3,19,4, 1,5,15,6,12,7,18,8,20,9, 6,10, 7,11, 5,12,21,      14,13      )}
#define KSTO20 {KST14 (0,42,1,26,2,45,3,36,4,43,5,37,6,44,7,32,8,39,9,28,      11,35,12,27,13,47,14,30      )}
#define KSTO21 {KST14 (0,38,1,36,2,43,3,37,4,44,5,32,     7,46,     9,35,10,27,11,47,12,30,13,42,14,33,15,45)}
#define KSTO22 {KST14 (0,25,1,32,     3,46,4,41,5,48,6,31,7,40,8,30,9,42,10,33,11,38,12,29,13,34,      15,44)}
#define KSTO23 {KST14 (0,35,1,48,2,31,3,40,     5,26,6,45,7,36,8,29,9,34,      11,25,12,39,13,28,14, 0,15,41)}
#define KSTO25 {KST14 (0,16,1, 7,2, 5,3,21,     5,13,6,11,7,14,     9,19,10, 1,11,15,12,12,13,18,14,10,15, 6)}
#define KSTO26 {KST13 (0,15,1, 3,     3,20,4, 6,5, 7,6, 5,7,21,8,17,9, 4,      11,22,      13,19,14, 1,15,23)}
#define KSTO27 {KST14 (0,22,1,14,2, 2,3, 9,4,23,5, 3,     7,20,8,10,9,16,10,24,11, 8,12,17,13, 4,      15,11)}
#define KSTO28 {KST14 (0,26,1,33,2,38,3,29,4,34,     6,25,7,39,     9,46,10,41,11,48,12,31,13,40,14, 0,15,42)}
#define KSTO29 {KST13 (0,36,1,29,2,34,     4,25,5,39,6,28,     8,41,9,48,10,31,11,40,      13,26,14,45,15,38)}
#define KSTO30 {KST14 (0,32,1,39,2,28,     4,35,5,27,6,47,7,30,     9,26,10,45,11,36,12,43,13,37,14,44,15,25)}
#define KSTO31 {KST15 (0,48,1,27,2,47,3,30,4,42,5,33,6,38,7,29,8,43,9,37,10,44,11,32,      13,46,14,41,15,35)}
#define KSTO33 {KST13 (0, 7,1,24,2, 8,3,17,4, 4,     6,22,     8, 2,9, 9,10,23,11, 3,      13,20,14, 6,15,16)}
#define KSTO34 {KST15 (0, 3,1,12,2,18,3,10,4,16,5,24,6, 8,7,17,     9,13,10,11,11,14,12, 2,13, 9,14,23,15,15)}
#define KSTO35 {KST14 (0,14,     2,19,3, 1,4,15,5,12,6,18,7,10,8, 6,9, 7,10, 5,11,21,      13,13,14,11,15,22)}
#define KSTO36 {KST13 (0,21,1,17,2, 4,     4,22,     6,19,7, 1,8,23,9, 3,      11,20,12, 6,13, 7,14, 5,15, 8)}
#define KSTO37 {KST15 (0,29,1,43,2,37,3,44,4,32,     6,46,7,41,8,35,9,27,10,47,11,30,12,42,13,33,14,38,15,36)}
#define KSTO38 {KST13 (0,39,     2,46,3,41,4,48,5,31,6,40,     8,42,9,33,10,38,11,29,12,34,      14,25,15,32)}
#define KSTO39 {KST13 (0,27,1,31,2,40,     4,26,5,45,6,36,7,43,8,34,     10,25,11,39,12,28,      14,35,15,48)}
#define KSTO41 {KST15 (0,24,1, 5,2,21,     4,13,5,11,6,14,7, 2,8,19,9, 1,10,15,11,12,12,18,13,10,14,16,15, 7)}
#define KSTO42 {KST12 (0,12,     2,20,3, 6,4, 7,5, 5,6,21,     8, 4,     10,22,      12,19,13, 1,14,15,15, 3)}
#define KSTO44 {KST15 (0,17,     2,13,3,11,4,14,5, 2,6, 9,7,23,8,15,9,12,10,18,11,10,12,16,13,24,14, 8,15,21)}
#define KSTO45 {KST13 (0,43,1,34,     3,25,4,39,5,28,     7,35,8,48,9,31,10,40,      12,26,13,45,14,36,15,29)}
#define KSTO46 {KST14 (     1,28,     3,35,4,27,5,47,6,30,7,42,8,26,9,45,10,36,11,43,12,37,13,44,14,32,15,39)}
#define KSTO47 {KST15 (0,31,1,47,2,30,3,42,4,33,5,38,6,29,7,34,8,37,9,44,10,32,      12,46,13,41,14,48,15,27)}
#define KSTO49 {KST13 (0, 5,1, 8,2,17,3, 4,     5,22,     7,19,8, 9,9,23,10, 3,      12,20,13, 6,14, 7,15,24)}
#define KSTO50 {KST15 (     1,18,2,10,3,16,4,24,5, 8,6,17,7, 4,8,13,9,11,10,14,11, 2,12, 9,13,23,14, 3,15,12)}
#define KSTO53 {KST15 (0,34,1,37,2,44,3,32,     5,46,6,41,7,48,8,27,9,47,10,30,11,42,12,33,13,38,14,29,15,43)}
#define KSTO55 {KST13 (0,47,1,40,     3,26,4,45,5,36,6,43,7,37,     9,25,10,39,11,28,      13,35,14,27,15,31)}
#define KSTO57 {KST15 (0, 8,1,21,     3,13,4,11,5,14,6, 2,7, 9,8, 1,9,15,10,12,11,18,12,10,13,16,14,24,15, 5)}

#define KSTO58 {KST9  (0,18,1,20,               5,21,     7,13,     9,22,      11,19,12, 1,13,15,14,12      )}    /* 1,20,2, 6,3, 7,4, 5, */
#define KSTO54 {KST11 (0,28,1,46,2,41,          5,40,     7,26,8,33,9,38,10,29,11,34,      13,25,14,39      )}    /* 1,46,2,41,3,48,4,31, */
#define KSTO51 {KST11 (0, 2,1,19,               5,18,6,10,7,16,8, 7,9, 5,10,21,      12,13,13,11,14,14      )}    /* 1,19,2, 1,3,15,4,12, */
#define KSTO60 {KST12 (0, 4,1,13,               5, 9,6,23,7, 3,8,12,9,18,10,10,11,16,12,24,13, 8,14,17      )}    /* 1,13,2,11,3,14,4, 2, */

#define KSTO52 {KST11 (     1, 4,               5,19,6, 1,7,15,8, 3,     10,20,11, 6,12, 7,13, 5,14,21,15,17)}    /* 1, 4,     3,22,      */
#define KSTO43 {KST10 (     1, 2,                    6,20,7, 6,8,16,9,24,10, 8,11,17,12, 4,      14,22,15,14)}    /* 1, 2,2, 9,3,23,4, 3, */
#define KSTO07 {KST11 (     1,41,          4,40,     6,26,7,45,8,38,9,29,10,34,      12,25,13,39,14,28,15,46)}    /* 1,41,2,48,3,31,4,40, */
#define KSTO12 {KST10 (     1,42,               5,34,     7,25,8,32,     10,46,11,41,12,48,13,31,14,40,15,30)}    /* 1,42,2,33,3,38,4,29, */

#define KSTO59 {KST12 (0,19,1, 9,2,23,          5,20,6, 6,7, 7,8,24,9, 8,10,17,11, 4,      13,22,      15, 2)}    /* 1, 9,2,23,3, 3,      */
#define KSTO61 {KST10 (0,37,                         6,35,7,27,8,31,9,40,      11,26,12,45,13,36,14,43,15,34)}    /*      2,25,3,39,4,28, */
#define KSTO62 {KST11 (0,46,                    5,30,6,42,7,33,8,45,9,36,10,43,11,37,12,44,13,32,      15,28)}    /*      2,35,3,27,4,47, */
#define KSTO63 {KST13 (0,40,1,30,2,42,     4,38,5,29,6,34,     8,44,9,32,      11,46,12,41,13,48,14,31,15,47)}    /* 1,30,2,42,3,33,4,38, */

#define KSTO58R1P2 {KST2 (0,18,1,20)}
#define KSTO58N1234 {KST7  (                       5,21,     7,13,     9,22,      11,19,12, 1,13,15,14,12      )}    /* 1,20,2, 6,3, 7,4, 5, */
#define KSTO54R1P23 {KST3 (0,28,1,46,2,41)}
#define KSTO54N1234 {KST8  (                       5,40,     7,26,8,33,9,38,10,29,11,34,      13,25,14,39      )}    /* 1,46,2,41,3,48,4,31, */
#define KSTO51R1P2 {KST2 (0, 2,1,19)}
#define KSTO51N1234 {KST9  (                       5,18,6,10,7,16,8, 7,9, 5,10,21,      12,13,13,11,14,14      )}    /* 1,19,2, 1,3,15,4,12, */
#define KSTO60R1P2 {KST2 (0, 4,1,13)}
#define KSTO60N1234 {KST10 (                       5, 9,6,23,7, 3,8,12,9,18,10,10,11,16,12,24,13, 8,14,17      )}    /* 1,13,2,11,3,14,4, 2, */

#ifdef GKST15           /* If GNUC/Pentium macros generated, use them */
#define KST15 GKST15
#define KST14 GKST14
#define KST13 GKST13
#define KST12 GKST12
#define KST11 GKST11
#define KST10 GKST10
#define KST9  GKST9
#define KST8  GKST8
#define KST7  GKST7
#define KST3  GKST3
#define KST2  GKST2
#define KST1  GKST1
#else
#define KST15 CKST15
#define KST14 CKST14
#define KST13 CKST13
#define KST12 CKST12
#define KST11 CKST11
#define KST10 CKST10
#define KST9  CKST9
#define KST8  CKST8
#define KST7  CKST7
#define KST3  CKST3
#define KST2  CKST2
#define KST1  CKST1
#endif /* GKST15 */

#define cswap(x) { \
    { \
    *(unsigned long *)(&x[0]) = \
        (((((x[0] << 8) + x[1]) << 8) + x[2]) << 8) + x[3]; \
    *(unsigned long *)(&x[4]) = \
        (((((x[4] << 8) + x[5]) << 8) + x[6]) << 8) + x[7]; \
      } \
    }

#ifdef _MSC_VER          /* MS VC++ Version 4 */
#ifdef RCV486
#define ROUND(dummy1,dummy2,dummy3,d6,d7,kseix,dummy4,dummy5,ll,rr) \
{                                                                             \
  /* On entry, the following must be true:                                    \
      EAX = 0x000000??                                                        \
      EBX = 0x000000??                                                        \
      rr = ESI (or EDI)                                                       \
      ll = EDI (or ESI)   */                                                  \
  __asm mov  ecx,dword ptr ks+8*kseix                                         \
  __asm xor  ecx,rr                                                           \
  __asm mov  edx,rr                                                           \
  __asm rol  edx,4                                                            \
  __asm xor  edx,dword ptr ks+8*kseix+4                                       \
  __asm and  ecx,0xfcfcfcfc                                                   \
  __asm mov  al,ch                                                            \
  __asm mov  bl,cl                                                            \
  __asm shr  ecx,16                                                           \
  __asm and  edx,0xfcfcfcfc                                                   \
  __asm xor  ll,s7p[ebx]                                                      \
  __asm mov  bl,ch                                                            \
  __asm xor  ll,s5p[eax]                                                      \
  __asm xor  ch,ch                                                            \
  __asm mov  al,dh                                                            \
  __asm xor  ll,s1p[ebx]                                                      \
  __asm mov  bl,dl                                                            \
  __asm shr  edx,16                                                           \
  __asm xor  ll,s3p[ecx]                                                      \
  __asm xor  ll,s6p[eax]                                                      \
  __asm mov  al,dh                                                            \
  __asm xor  dh,dh                                                            \
  __asm xor  ll,s8p[ebx]                                                      \
  __asm xor  ll,s2p[eax]                                                      \
  __asm xor  ll,s4p[edx]                                                      \
  }
#else
#define ROUND(dummy1,dummy2,dummy3,d6,d7,kseix,dummy4,dummy5,ll,rr) \
{                                                                             \
  /* On entry, the following must be true:                                    \
      EAX = 0x000000??                                                        \
      EBX = 0x000000??                                                        \
      rr = ESI (or EDI)                                                       \
      ll = EDI (or ESI)   */                                                  \
  __asm mov  ecx,dword ptr ks+8*kseix                                         \
  __asm xor  ecx,rr                                                           \
  __asm mov  edx,rr                                                           \
  __asm rol  edx,4                                                            \
  __asm mov  ebp,dword ptr ks+8*kseix+4                                       \
  __asm and  ecx,0xfcfcfcfc                                                   \
  __asm xor  edx,ebp                                                          \
  __asm mov  al,ch                                                            \
  __asm mov  bl,cl                                                            \
  __asm shr  ecx,16                                                           \
  __asm and  edx,0xfcfcfcfc                                                   \
  __asm mov  ebp,s7p[ebx]                                                     \
  __asm mov  bl,ch                                                            \
  __asm xor  ll,ebp                                                           \
  __asm mov  ebp,s5p[eax]                                                     \
  __asm xor  ch,ch                                                            \
  __asm mov  al,dh                                                            \
  __asm xor  ll,ebp                                                           \
  __asm mov  ebp,s1p[ebx]                                                     \
  __asm xor  ll,ebp                                                           \
  __asm mov  bl,dl                                                            \
  __asm shr  edx,16                                                           \
  __asm mov  ebp,s3p[ecx]                                                     \
  __asm xor  ll,ebp                                                           \
  __asm mov  ebp,s6p[eax]                                                     \
  __asm mov  al,dh                                                            \
  __asm xor  dh,dh                                                            \
  __asm xor  ll,ebp                                                           \
  __asm mov  ebp,s8p[ebx]                                                     \
  __asm xor  ll,ebp                                                           \
  __asm mov  ebp,s2p[eax]                                                     \
  __asm xor  ll,ebp                                                           \
  __asm mov  ebp,s4p[edx]                                                     \
  __asm xor  ll,ebp                                                           \
  }
#endif /* RCV486 */
#endif /* _MSC_VER */

#ifdef __GNUC__
#if #cpu(i386) && (TRUE)

#ifdef __linux__
#define ebpsave _ebpsave       /* FreeBSD automatically prepends "_" */
#define ks _ks
#define s1p _s1p
#define s2p _s2p
#define s3p _s3p
#define s4p _s4p
#define s5p _s5p
#define s6p _s6p
#define s7p _s7p
#define s8p _s8p
#endif

#define PREROUND(dummy1,dummy2) \
asm volatile("mov %%ebp,_ebpsave" : : )

#define POSTROUND(dummy1,dummy2) \
asm volatile("mov _ebpsave,%%ebp" : : )

#ifndef RCV686
#define ROUND(dummy1,dummy2,kse,ll,rr,kseix,llreg,rrreg,d3,d4) \
asm volatile("                \n\
      # pushl %%ebp           \n\
        movl _ks+8*" #kseix ",%%ecx\n\
                              \n\
        xorl %1,%%ecx         \n\
        movl %1,%%edx         \n\
                              \n\
        roll $4,%%edx         \n\
        movl _ks+4+8*" #kseix ",%%ebp\n\
                              \n\
        andl $-50529028,%%ecx \n\
        xorl %%ebp,%%edx      \n\
                              \n\
        movb %%ch,%%al        \n\
        movb %%cl,%%bl        \n\
                              \n\
        shrl $16,%%ecx        \n\
        andl $-50529028,%%edx \n\
                              \n\
        movl _s7p(%%ebx),%%ebp\n\
        movb %%ch,%%bl        \n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s5p(%%eax),%%ebp\n\
                              \n\
        xorb %%ch,%%ch        \n\
        movb %%dh,%%al        \n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s1p(%%ebx),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
        movb %%dl,%%bl        \n\
                              \n\
        shrl $16,%%edx        \n\
        movl _s3p(%%ecx),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s6p(%%eax),%%ebp\n\
                              \n\
        movb %%dh,%%al        \n\
        xorb %%dh,%%dh        \n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s8p(%%ebx),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s2p(%%eax),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s4p(%%edx),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
      # popl %%ebp"             \
                                \
        : llreg (ll), rrreg (rr)              \
        : "0"  (ll),  "1"  (rr),  "a" (0), "b"(0) \
        : "ecx", "edx", "cc")
#endif /* RCV686 */
#ifdef RCV686
#define ROUND(dummy1,dummy2,kse,ll,rr,kseix,llreg,rrreg,d3,d4) \
asm volatile("                       \n\
      # pushl %%ebp                  \n\
        movl _ks+8*" #kseix ",%%ecx  \n\
                                     \n\
        xorl %1,%%ecx                \n\
        movl %1,%%edx                \n\
                                     \n\
        roll $4,%%edx                \n\
        andl $-50529028,%%ecx        \n\
        movl _ks+4+8*" #kseix ",%%ebp\n\
                                     \n\
        xorl %%ebp,%%edx             \n\
        movzbl %%cl,%%eax            \n\
                                     \n\
        shrl $8,%%ecx                \n\
        andl $-50529028,%%edx        \n\
        movl _s7p(%%eax),%%ebp       \n\
                                     \n\
        xorl %%ebp,%0                \n\
        movzbl %%dl,%%ebx            \n\
                                     \n\
        shrl $8,%%edx                \n\
        movzbl %%cl,%%eax            \n\
        movl _s8p(%%ebx),%%ebp       \n\
                                     \n\
        xorl %%ebp,%0                \n\
        movzbl %%dl,%%ebx            \n\
        movl _s5p(%%eax),%%ebp       \n\
                                     \n\
        shrl $8,%%ecx                \n\
        xorl %%ebp,%0                \n\
        movl _s6p(%%ebx),%%ebp       \n\
                                     \n\
        shrl $8,%%edx                \n\
        movzbl %%cl,%%eax            \n\
                                     \n\
        xorl %%ebp,%0                \n\
        movzbl %%dl,%%ebx            \n\
        movl _s3p(%%eax),%%ebp       \n\
                                     \n\
        shrl $8,%%ecx                \n\
        xorl %%ebp,%0                \n\
        movl _s4p(%%ebx),%%ebp       \n\
                                     \n\
        shrl $8,%%edx                \n\
        xorl %%ebp,%0                \n\
        movl _s1p(%%ecx),%%ebp       \n\
                                     \n\
        xorl %%ebp,%0                \n\
        movl _s2p(%%edx),%%ebp       \n\
                                     \n\
        xorl %%ebp,%0                \n\
      # popl %%ebp"             \
                                \
        : llreg (ll), rrreg (rr)              \
        : "0"  (ll),  "1"  (rr),  "a" (0), "b"(0) \
        : "ecx", "edx", "cc")
#endif /* RCV686 */

#define ROUND14568(dummy1,dummy2,kse,ll,rr,kseix,llreg,rrreg,d3,d4) \
asm volatile("                \n\
      # pushl %%ebp           \n\
        movl _ks+8*" #kseix ",%%ecx\n\
                              \n\
        xorl %1,%%ecx         \n\
        movl %1,%%edx         \n\
                              \n\
        roll $4,%%edx         \n\
        movl _ks+4+8*" #kseix ",%%ebp\n\
                              \n\
        andl $-50529028,%%ecx \n\
        xorl %%ebp,%%edx      \n\
                              \n\
        movb %%ch,%%al        \n\
        andl $16579836,%%edx  \n\
                              \n\
        shrl $16,%%ecx        \n\
        movb %%ch,%%bl        \n\
                              \n\
        movl _s5p(%%eax),%%ebp\n\
        movb %%dh,%%al        \n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s1p(%%ebx),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
        movb %%dl,%%bl        \n\
                              \n\
        shrl $16,%%edx        \n\
        movl _s6p(%%eax),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s8p(%%ebx),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s4p(%%edx),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
      # popl %%ebp"             \
                                \
        : llreg (ll), rrreg (rr)              \
        : "0"  (ll),  "1"  (rr),  "a" (0), "b"(0) \
        : "ecx", "edx", "cc")

#define ROUND237(dummy1,dummy2,kse,ll,rr,kseix,llreg,rrreg,d3,d4) \
asm volatile("                \n\
      # pushl %%ebp           \n\
        movl _ks+8*" #kseix ",%%ecx\n\
                              \n\
        xorl %1,%%ecx         \n\
        movl %1,%%edx         \n\
                              \n\
        shrl $20,%%edx        \n\
        andl $16515324,%%ecx  \n\
                              \n\
        movb %%cl,%%bl        \n\
        movb _ks+7+8*" #kseix ",%%al\n\
                              \n\
        shrl $16,%%ecx        \n\
        andl $252,%%edx       \n\
                              \n\
        xorl %%edx,%%eax      \n\
        movl _s7p(%%ebx),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s3p(%%ecx),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s2p(%%eax),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
      # popl %%ebp"             \
                                \
        : llreg (ll), rrreg (rr)              \
        : "0"  (ll),  "1"  (rr),  "a" (0), "b"(0) \
        : "ecx", "edx", "cc")

#define ROUND678(dummy1,dummy2,kse,ll,rr,kseix,llreg,rrreg,d3,d4) \
asm volatile("                \n\
      # pushl %%ebp           \n\
        movl %1,%%edx         \n\
                              \n\
        roll $4,%%edx         \n\
        movl _ks+4+8*" #kseix ",%%ebp\n\
                              \n\
        xorl %%ebp,%%edx      \n\
        movl _ks+8*" #kseix ",%%ecx\n\
                              \n\
        xorl %1,%%ecx         \n\
        andl $64764,%%edx     \n\
                              \n\
        andl $252,%%ecx       \n\
        movb %%dl,%%al        \n\
                              \n\
        shrl $8,%%edx         \n\
        movl _s7p(%%ecx),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s8p(%%eax),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
        movl _s6p(%%edx),%%ebp\n\
                              \n\
        xorl %%ebp,%0         \n\
      # popl %%ebp"             \
                                \
        : llreg (ll), rrreg (rr)              \
        : "0"  (ll),  "1"  (rr),  "a" (0), "b"(0) \
        : "ecx", "edx", "cc")
#endif /* #cpu */
#endif /* __GNUC__ */

#ifndef ROUND           /* If still not defined, resort to C-language code */
#define ROUND(rcx,rdx,kse,ll,rr,dummy1,dummy2,dummy3,dummy4,dummy5)           \
{                                                                             \
  rcx = *(unsigned long *)(&kse[0]); /* bytes 1, 3, 5, 7 */                   \
                /*  1  2  3  4  5  6 -- -- 13 14 15 16 17 18 -- --            \
                   25 26 27 28 29 30 -- -- 37 38 39 40 41 42 -- -- */         \
  rdx = *(unsigned long *)(&kse[4]); /* bytes 2, 4, 6, 8 */                   \
                /* 47 48 -- --  7  8  9 10 11 12 -- -- 19 20 21 22            \
                   23 24 -- -- 31 32 33 34 35 36 -- -- 43 44 45 46 */         \
                                                                              \
  rcx ^= rr;    /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15            \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
  rdx ^= rr;    /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15            \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
                                                                              \
  rdx = (rdx << 4) + (rdx >> 28);                                             \
                /*  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19            \
                   20 21 22 23 24 25 26 27 28 29 30 31 32  1  2  3 */         \
                                                                              \
  rcx &= 0xfcfcfcfc;                                                          \
                /* 32  1  2  3  4  5 -- --  8  9 10 11 12 13 -- --            \
                   16 17 18 19 20 21 -- -- 24 25 26 27 28 29 -- -- */         \
  rdx &= 0xfcfcfcfc;                                                          \
                /*  4  5  6  7  8  9 -- -- 12 13 14 15 16 17 -- --            \
                   20 21 22 23 24 25 -- -- 28 29 30 31 32  1 -- -- */         \
                                                                              \
  /* ll =       /*  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16            \
                   17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 */         \
                                                                              \
  ll  ^= *(unsigned long *)((char *)s7p + (rcx & 0xff));                      \
  ll  ^= *(unsigned long *)((char *)s5p + ((rcx & 0xffff) >> 8));             \
  rcx >>= 16;                                                                 \
  ll  ^= *(unsigned long *)((char *)s8p + (rdx & 0xff));                      \
  ll  ^= *(unsigned long *)((char *)s6p + ((rdx & 0xffff) >> 8));             \
  rdx >>= 16;                                                                 \
  ll  ^= *(unsigned long *)((char *)s3p + (rcx & 0xff));                      \
  ll  ^= *(unsigned long *)((char *)s1p + ((rcx         ) >> 8));             \
  ll  ^= *(unsigned long *)((char *)s4p + (rdx & 0xff));                      \
  ll  ^= *(unsigned long *)((char *)s2p + ((rdx         ) >> 8));             \
  }
#endif

#ifndef PREROUND
#define PREROUND(dummy1,dummy2) do {} while(0)
#endif

#ifndef POSTROUND
#define POSTROUND(dummy1,dummy2) do {} while(0)
#endif

#ifndef ROUND14568
#define ROUND14568(rcx,rdx,kse,ll,rr,dummy1,dummy2,dummy3,dummy4,dummy5)      \
{                                                                             \
  rcx = *(unsigned long *)(&kse[0]); /* bytes 1, 3, 5, 7 */                   \
                /*  1  2  3  4  5  6 -- -- 13 14 15 16 17 18 -- --            \
                   25 26 27 28 29 30 -- -- 37 38 39 40 41 42 -- -- */         \
  rdx = *(unsigned long *)(&kse[4]); /* bytes 2, 4, 6, 8 */                   \
                /* 47 48 -- --  7  8  9 10 11 12 -- -- 19 20 21 22            \
                   23 24 -- -- 31 32 33 34 35 36 -- -- 43 44 45 46  */        \
                                                                              \
  rcx ^= rr;    /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15            \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
  rdx ^= rr;    /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15            \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
                                                                              \
  rdx = (rdx << 4) + (rdx >> 28);                                             \
                /*  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19            \
                   20 21 22 23 24 25 26 27 28 29 30 31 32  1  2  3 */         \
                                                                              \
  rcx &= 0xfc00fc00;                                                          \
                /* 32  1  2  3  4  5 -- -- -- -- -- -- -- -- -- --            \
                   16 17 18 19 20 21 -- -- -- -- -- -- -- -- -- -- */         \
  rdx &= 0x00fcfcfc;                                                          \
                /* -- -- -- -- -- -- -- -- 12 13 14 15 16 17 -- --            \
                   20 21 22 23 24 25 -- -- 28 29 30 31 32  1 -- -- */         \
                                                                              \
  /* ll =       /*  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16            \
                   17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 */         \
                                                                              \
  ll  ^= *(unsigned long *)((char *)s5p + ((rcx & 0xffff) >> 8));             \
  ll  ^= *(unsigned long *)((char *)s8p + (rdx & 0xff));                      \
  ll  ^= *(unsigned long *)((char *)s6p + ((rdx & 0xffff) >> 8));             \
  ll  ^= *(unsigned long *)((char *)s1p + (rcx >> 24));                       \
  ll  ^= *(unsigned long *)((char *)s4p + (rdx >> 16));                       \
  }
#endif /* ROUND14568 */

#ifndef ROUND237
#define ROUND237(rcx,rdx,kse,ll,rr,dummy1,dummy2,dummy3,dummy4,dummy5)        \
{                                                                             \
  rcx = *(unsigned long *)(&kse[0]); /* bytes 1, 3, 5, 7 */                   \
                /*  1  2  3  4  5  6 -- -- 13 14 15 16 17 18 -- --            \
                   25 26 27 28 29 30 -- -- 37 38 39 40 41 42 -- -- */         \
  rdx = *(unsigned long *)(&kse[4]); /* bytes 2, 4, 6, 8 */                   \
                /* 47 48 -- --  7  8  9 10 11 12 -- -- 19 20 21 22            \
                   23 24 -- -- 31 32 33 34 35 36 -- -- 43 44 45 46 */         \
                                                                              \
  rcx ^= rr;    /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15            \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
  rdx ^= rr;    /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15            \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
                                                                              \
  rdx = rdx >> 20;                    /* Don't need to rotate! */             \
                /* -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            \
                   -- -- -- -- -- -- 32  1  2  3  4  5  6  7  8  9 */         \
                                                                              \
  rcx &= 0x00fc00fc;                                                          \
                /* -- -- -- -- -- -- -- --  8  9 10 11 12 13 -- --            \
                   -- -- -- -- -- -- -- -- 24 25 26 27 28 29 -- -- */         \
  rdx &= 0x000000fc;                                                          \
                /* -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            \
                   -- -- -- -- -- -- -- --  4  5  6  7  8  9 -- -- */         \
                                                                              \
  /* ll =       /*  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16            \
                   17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 */         \
                                                                              \
  ll  ^= *(unsigned long *)((char *)s7p + (rcx & 0xff));                      \
  ll  ^= *(unsigned long *)((char *)s2p + (rdx      ));                       \
  ll  ^= *(unsigned long *)((char *)s3p + (rcx >> 16));                       \
  }
#endif /* ROUND237 */

#ifndef ROUND7
#define ROUND7(rcx,rdx,kse,ll,rr,dummy1,dummy2,dummy3,dummy4,dummy5)          \
{                                                                             \
  rcx = *(unsigned long *)(&kse[0]); /* bytes 1, 3, 5, 7 */                   \
                /*  1  2  3  4  5  6 -- -- 13 14 15 16 17 18 -- --            \
                   25 26 27 28 29 30 -- -- 37 38 39 40 41 42 -- -- */         \
                                                                              \
  rcx ^= rr;     /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15           \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
                                                                              \
  rcx &= 0x000000fc;                                                          \
                /* -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            \
                   -- -- -- -- -- -- -- -- 24 25 26 27 28 29 -- -- */         \
                                                                              \
  /* ll =       /*  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16            \
                   17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 */         \
                                                                              \
  ll  ^= *(unsigned long *)((char *)s7p + (rcx       ));                      \
  }
#endif /* ROUND7 */

#ifndef ROUND34
#define ROUND34(rcx,rdx,kse,ll,rr,dummy1,dummy2,dummy3,dummy4,dummy5)         \
{                                                                             \
  rcx = *(unsigned long *)(&kse[0]); /* bytes 1, 3, 5, 7 */                   \
                /*  1  2  3  4  5  6 -- -- 13 14 15 16 17 18 -- --            \
                   25 26 27 28 29 30 -- -- 37 38 39 40 41 42 -- -- */         \
  rdx = *(unsigned long *)(&kse[4]); /* bytes 2, 4, 6, 8 */                   \
                /* 47 48 -- --  7  8  9 10 11 12 -- -- 19 20 21 22            \
                   23 24 -- -- 31 32 33 34 35 36 -- -- 43 44 45 46 */         \
                                                                              \
  rcx ^= rr;    /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15            \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
  rdx ^= rr;    /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15            \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
                                                                              \
  rdx = rdx >> 12;                                                            \
                /* -- -- -- -- -- -- -- -- -- -- -- -- 32  1  2  3            \
                    4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 */         \
                                                                              \
  rcx &= 0x00fc0000;                                                          \
                /* -- -- -- -- -- -- -- --  8  9 10 11 12 13 -- --            \
                   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- */         \
                                                                              \
  rdx &= 0x000000fc;                                                          \
                /* -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            \
                   -- -- -- -- -- -- -- -- 12 13 14 15 16 17 -- -- */         \
                                                                              \
  /* ll =       /*  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16            \
                   17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 */         \
                                                                              \
  rcx >>= 16;                                                                 \
  ll  ^= *(unsigned long *)((char *)s3p + (rcx       ));                      \
  ll  ^= *(unsigned long *)((char *)s4p + (rdx       ));                      \
  }
#endif /* ROUND34 */

#ifndef ROUND12568
#define ROUND12568(rcx,rdx,kse,ll,rr,dummy1,dummy2,dummy3,dummy4,dummy5)      \
{                                                                             \
  rcx = *(unsigned long *)(&kse[0]); /* bytes 1, 3, 5, 7 */                   \
                /*  1  2  3  4  5  6 -- -- 13 14 15 16 17 18 -- --            \
                   25 26 27 28 29 30 -- -- 37 38 39 40 41 42 -- -- */         \
  rdx = *(unsigned long *)(&kse[4]); /* bytes 2, 4, 6, 8 */                   \
                /* 47 48 -- --  7  8  9 10 11 12 -- -- 19 20 21 22            \
                   23 24 -- -- 31 32 33 34 35 36 -- -- 43 44 45 46  */        \
                                                                              \
  rcx ^= rr;    /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15            \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
  rdx ^= rr;    /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15            \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
                                                                              \
  rdx = (rdx << 4) + (rdx >> 28);                                             \
                /*  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19            \
                   20 21 22 23 24 25 26 27 28 29 30 31 32  1  2  3 */         \
                                                                              \
  rcx &= 0xfc00fc00;                                                          \
                /* 32  1  2  3  4  5 -- -- -- -- -- -- -- -- -- --            \
                   16 17 18 19 20 21 -- -- -- -- -- -- -- -- -- -- */         \
  rdx &= 0xfc00fcfc;                                                          \
                /*  4  5  6  7  8  9 -- -- -- -- -- -- -- -- -- --            \
                   20 21 22 23 24 25 -- -- 28 29 30 31 32  1 -- -- */         \
                                                                              \
  /* ll =       /*  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16            \
                   17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 */         \
                                                                              \
  ll  ^= *(unsigned long *)((char *)s5p + ((rcx & 0xffff) >> 8));             \
  rcx >>= 24;                                                                 \
  ll  ^= *(unsigned long *)((char *)s8p + (rdx & 0xff));                      \
  ll  ^= *(unsigned long *)((char *)s6p + ((rdx & 0xffff) >> 8));             \
  rdx >>= 24;                                                                 \
  ll  ^= *(unsigned long *)((char *)s1p + ((rcx         )     ));             \
  ll  ^= *(unsigned long *)((char *)s2p + ((rdx         )     ));             \
  }
#endif /* ROUND12568 */

#ifndef ROUND234568
#define ROUND234568(rcx,rdx,kse,ll,rr,dummy1,dummy2,dummy3,dummy4,dummy5)     \
{                                                                             \
  rcx = *(unsigned long *)(&kse[0]); /* bytes 1, 3, 5, 7 */                   \
                /*  1  2  3  4  5  6 -- -- 13 14 15 16 17 18 -- --            \
                   25 26 27 28 29 30 -- -- 37 38 39 40 41 42 -- -- */         \
  rdx = *(unsigned long *)(&kse[4]); /* bytes 2, 4, 6, 8 */                   \
                /* 47 48 -- --  7  8  9 10 11 12 -- -- 19 20 21 22            \
                   23 24 -- -- 31 32 33 34 35 36 -- -- 43 44 45 46  */        \
                                                                              \
  rcx ^= rr;     /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15           \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
  rdx ^= rr;     /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15           \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
                                                                              \
  rdx = (rdx << 4) + (rdx >> 28);                                             \
                /*  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19            \
                   20 21 22 23 24 25 26 27 28 29 30 31 32  1  2  3 */         \
                                                                              \
  rcx &= 0x00fcfc00;                                                          \
                /* -- -- -- -- -- -- -- --  8  9 10 11 12 13 -- --            \
                   16 17 18 19 20 21 -- -- -- -- -- -- -- -- -- -- */         \
  rdx &= 0xfcfcfcfc;                                                          \
                /*  4  5  6  7  8  9 -- -- 12 13 14 15 16 17 -- --            \
                   20 21 22 23 24 25 -- -- 28 29 30 31 32  1 -- -- */         \
                                                                              \
  /* ll =       /*  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16            \
                   17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 */         \
                                                                              \
  ll  ^= *(unsigned long *)((char *)s5p + ((rcx & 0xffff) >> 8));             \
  rcx >>= 16;                                                                 \
  ll  ^= *(unsigned long *)((char *)s8p + (rdx & 0xff));                      \
  ll  ^= *(unsigned long *)((char *)s6p + ((rdx & 0xffff) >> 8));             \
  rdx >>= 16;                                                                 \
  ll  ^= *(unsigned long *)((char *)s3p + (rcx       ));                      \
  ll  ^= *(unsigned long *)((char *)s4p + (rdx & 0xff));                      \
  ll  ^= *(unsigned long *)((char *)s2p + ((rdx         ) >> 8));             \
  }
#endif /* ROUND234568 */

#ifndef ROUND17
#define ROUND17(rcx,rdx,kse,ll,rr,dummy1,dummy2,dummy3,dummy4,dummy5)         \
{                                                                             \
  rcx = *(unsigned long *)(&kse[0]); /* bytes 1, 3, 5, 7 */                   \
                /*  1  2  3  4  5  6 -- -- 13 14 15 16 17 18 -- --            \
                   25 26 27 28 29 30 -- -- 37 38 39 40 41 42 -- -- */         \
                                                                              \
  rcx ^= rr;    /* 32  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15            \
                   16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 */         \
                                                                              \
  rcx &= 0xfc0000fc;                                                          \
                /* 32  1  2  3  4  5 -- -- -- -- -- -- -- -- -- --            \
                   -- -- -- -- -- -- -- -- 24 25 26 27 28 29 -- -- */         \
                                                                              \
  /* ll =       /*  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16            \
                   17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 */         \
                                                                              \
  ll  ^= *(unsigned long *)((char *)s7p + (rcx & 0xff));                      \
  ll  ^= *(unsigned long *)((char *)s1p + ((rcx         ) >> 24));            \
  }
#endif /* ROUND17 */

#ifdef _MSC_VER
#undef PREROUND
#undef POSTROUND
static int esisave, edisave, ebpsave;
#define PREROUND(esisource,edisource) {                  \
    __asm mov esisave,esi                                      \
    __asm xor ebx,ebx                                          \
    __asm mov edisave,edi                                      \
    __asm mov esi,esisource                                    \
    __asm xor eax,eax                                          \
    __asm mov edi,edisource                                    \
    __asm mov ebpsave,ebp                                      \
    }
#define POSTROUND(esidest,edidest) {       \
    __asm mov ebp,ebpsave                                      \
    __asm mov edidest,edi                                      \
    __asm mov esidest,esi                                      \
    __asm mov edi,edisave                                      \
    __asm mov esi,esisave                                      \
    }
#endif /* _MSC_VER */


#ifdef CALLEXTERNALASMCODE
extern unsigned long s1p[64];
extern unsigned long s2p[64];
extern unsigned long s3p[64];
extern unsigned long s4p[64];
extern unsigned long s5p[64];
extern unsigned long s6p[64];
extern unsigned long s7p[64];
extern unsigned long s8p[64];
#else
/* Note:  The output of these s-boxes are rotated right one bit */
       unsigned long s1p[64] =
              {0x00404100,0x00000000,0x00004000,0x00404101,
               0x00404001,0x00004101,0x00000001,0x00004000,
               0x00000100,0x00404100,0x00404101,0x00000100,
               0x00400101,0x00404001,0x00400000,0x00000001,
               0x00000101,0x00400100,0x00400100,0x00004100,
               0x00004100,0x00404000,0x00404000,0x00400101,
               0x00004001,0x00400001,0x00400001,0x00004001,
               0x00000000,0x00000101,0x00004101,0x00400000,
               0x00004000,0x00404101,0x00000001,0x00404000,
               0x00404100,0x00400000,0x00400000,0x00000100,
               0x00404001,0x00004000,0x00004100,0x00400001,
               0x00000100,0x00000001,0x00400101,0x00004101,
               0x00404101,0x00004001,0x00404000,0x00400101,
               0x00400001,0x00000101,0x00004101,0x00404100,
               0x00000101,0x00400100,0x00400100,0x00000000,
               0x00004001,0x00004100,0x00000000,0x00404001};

       unsigned long s2p[64] =
              {0x20042008,0x20002000,0x00002000,0x00042008,
               0x00040000,0x00000008,0x20040008,0x20002008,
               0x20000008,0x20042008,0x20042000,0x20000000,
               0x20002000,0x00040000,0x00000008,0x20040008,
               0x00042000,0x00040008,0x20002008,0x00000000,
               0x20000000,0x00002000,0x00042008,0x20040000,
               0x00040008,0x20000008,0x00000000,0x00042000,
               0x00002008,0x20042000,0x20040000,0x00002008,
               0x00000000,0x00042008,0x20040008,0x00040000,
               0x20002008,0x20040000,0x20042000,0x00002000,
               0x20040000,0x20002000,0x00000008,0x20042008,
               0x00042008,0x00000008,0x00002000,0x20000000,
               0x00002008,0x20042000,0x00040000,0x20000008,
               0x00040008,0x20002008,0x20000008,0x00040008,
               0x00042000,0x00000000,0x20002000,0x00002008,
               0x20000000,0x20040008,0x20042008,0x00042000};

       unsigned long s3p[64] =
              {0x00000082,0x02008080,0x00000000,0x02008002,
               0x02000080,0x00000000,0x00008082,0x02000080,
               0x00008002,0x02000002,0x02000002,0x00008000,
               0x02008082,0x00008002,0x02008000,0x00000082,
               0x02000000,0x00000002,0x02008080,0x00000080,
               0x00008080,0x02008000,0x02008002,0x00008082,
               0x02000082,0x00008080,0x00008000,0x02000082,
               0x00000002,0x02008082,0x00000080,0x02000000,
               0x02008080,0x02000000,0x00008002,0x00000082,
               0x00008000,0x02008080,0x02000080,0x00000000,
               0x00000080,0x00008002,0x02008082,0x02000080,
               0x02000002,0x00000080,0x00000000,0x02008002,
               0x02000082,0x00008000,0x02000000,0x02008082,
               0x00000002,0x00008082,0x00008080,0x02000002,
               0x02008000,0x02000082,0x00000082,0x02008000,
               0x00008082,0x00000002,0x02008002,0x00008080};

       unsigned long s4p[64] =
              {0x40200800,0x40000820,0x40000820,0x00000020,
               0x00200820,0x40200020,0x40200000,0x40000800,
               0x00000000,0x00200800,0x00200800,0x40200820,
               0x40000020,0x00000000,0x00200020,0x40200000,
               0x40000000,0x00000800,0x00200000,0x40200800,
               0x00000020,0x00200000,0x40000800,0x00000820,
               0x40200020,0x40000000,0x00000820,0x00200020,
               0x00000800,0x00200820,0x40200820,0x40000020,
               0x00200020,0x40200000,0x00200800,0x40200820,
               0x40000020,0x00000000,0x00000000,0x00200800,
               0x00000820,0x00200020,0x40200020,0x40000000,
               0x40200800,0x40000820,0x40000820,0x00000020,
               0x40200820,0x40000020,0x40000000,0x00000800,
               0x40200000,0x40000800,0x00200820,0x40200020,
               0x40000800,0x00000820,0x00200000,0x40200800,
               0x00000020,0x00200000,0x00000800,0x00200820};

       unsigned long s5p[64] =
              {0x00000040,0x00820040,0x00820000,0x10800040,
               0x00020000,0x00000040,0x10000000,0x00820000,
               0x10020040,0x00020000,0x00800040,0x10020040,
               0x10800040,0x10820000,0x00020040,0x10000000,
               0x00800000,0x10020000,0x10020000,0x00000000,
               0x10000040,0x10820040,0x10820040,0x00800040,
               0x10820000,0x10000040,0x00000000,0x10800000,
               0x00820040,0x00800000,0x10800000,0x00020040,
               0x00020000,0x10800040,0x00000040,0x00800000,
               0x10000000,0x00820000,0x10800040,0x10020040,
               0x00800040,0x10000000,0x10820000,0x00820040,
               0x10020040,0x00000040,0x00800000,0x10820000,
               0x10820040,0x00020040,0x10800000,0x10820040,
               0x00820000,0x00000000,0x10020000,0x10800000,
               0x00020040,0x00800040,0x10000040,0x00020000,
               0x00000000,0x10020000,0x00820040,0x10000040};

       unsigned long s6p[64] =
              {0x08000004,0x08100000,0x00001000,0x08101004,
               0x08100000,0x00000004,0x08101004,0x00100000,
               0x08001000,0x00101004,0x00100000,0x08000004,
               0x00100004,0x08001000,0x08000000,0x00001004,
               0x00000000,0x00100004,0x08001004,0x00001000,
               0x00101000,0x08001004,0x00000004,0x08100004,
               0x08100004,0x00000000,0x00101004,0x08101000,
               0x00001004,0x00101000,0x08101000,0x08000000,
               0x08001000,0x00000004,0x08100004,0x00101000,
               0x08101004,0x00100000,0x00001004,0x08000004,
               0x00100000,0x08001000,0x08000000,0x00001004,
               0x08000004,0x08101004,0x00101000,0x08100000,
               0x00101004,0x08101000,0x00000000,0x08100004,
               0x00000004,0x00001000,0x08100000,0x00101004,
               0x00001000,0x00100004,0x08001004,0x00000000,
               0x08101000,0x08000000,0x00100004,0x08001004};

       unsigned long s7p[64] =
              {0x00080000,0x81080000,0x81000200,0x00000000,
               0x00000200,0x81000200,0x80080200,0x01080200,
               0x81080200,0x00080000,0x00000000,0x81000000,
               0x80000000,0x01000000,0x81080000,0x80000200,
               0x01000200,0x80080200,0x80080000,0x01000200,
               0x81000000,0x01080000,0x01080200,0x80080000,
               0x01080000,0x00000200,0x80000200,0x81080200,
               0x00080200,0x80000000,0x01000000,0x00080200,
               0x01000000,0x00080200,0x00080000,0x81000200,
               0x81000200,0x81080000,0x81080000,0x80000000,
               0x80080000,0x01000000,0x01000200,0x00080000,
               0x01080200,0x80000200,0x80080200,0x01080200,
               0x80000200,0x81000000,0x81080200,0x01080000,
               0x00080200,0x00000000,0x80000000,0x81080200,
               0x00000000,0x80080200,0x01080000,0x00000200,
               0x81000000,0x01000200,0x00000200,0x80080000};

       unsigned long s8p[64] =
              {0x04000410,0x00000400,0x00010000,0x04010410,
               0x04000000,0x04000410,0x00000010,0x04000000,
               0x00010010,0x04010000,0x04010410,0x00010400,
               0x04010400,0x00010410,0x00000400,0x00000010,
               0x04010000,0x04000010,0x04000400,0x00000410,
               0x00010400,0x00010010,0x04010010,0x04010400,
               0x00000410,0x00000000,0x00000000,0x04010010,
               0x04000010,0x04000400,0x00010410,0x00010000,
               0x00010410,0x00010000,0x04010400,0x00000400,
               0x00000010,0x04010010,0x00000400,0x00010410,
               0x04000400,0x00000010,0x04000010,0x04010000,
               0x04010010,0x04000000,0x00010000,0x04000410,
               0x00000000,0x04010410,0x00010010,0x04000010,
               0x04010000,0x04000400,0x04000410,0x00000000,
               0x04010410,0x00010400,0x00010400,0x00000410,
               0x00000410,0x00010010,0x04000000,0x04010400};
#endif /* CALLEXTERNALASMCODE */

/* Space for Round 1 outputs.  (6 key bits; 2 complementary pairs; 2 halves) */
#ifdef CALLEXTERNALASMCODE
extern unsigned long round1L[2];  /* Left half is invariant for given input */
extern unsigned long round1R[32];
extern unsigned long round3pR[32];
#else
static unsigned long round1L[2];  /* Left half is invariant for given input */
static unsigned long round1R[32];
static unsigned long round2pR[32];
static unsigned long round3pR[32];
static unsigned long round5pL[1], round5pR[1];
static unsigned long round3x7R[1], round2R[1];
#endif

static unsigned long round16L1, round16R1;
static unsigned long round16L2, round16R2;
static unsigned long            round15pR1;
static unsigned long            round15pR2;

#ifdef PRACTICE

/* static uchar k1[8]      = {0x5E,0xD9,0x20,0x4F,0xEF,0x1F,0x46,0x98}; /* 22 bits away */
   static uchar k1[8]      = {0x5E,0xD9,0x20,0x4F,0xEC,0xE0,0xB9,0x67}; /* 0 bits away */
static uchar iv[8]      = {0xA2,0x18,0x5A,0xBF,0x45,0x96,0x60,0xBF};
static uchar plain[8]   = { 'T', 'h', 'e', ' ', 'u', 'n', 'k', 'n'};
static uchar cipher1[8] = {0x3E,0xA7,0x86,0xF9,0x1D,0x76,0xBB,0xD3};

#else

static uchar k1[8]      = {0x52,0xA7,0xC8,0xC1,0x01,0x01,0x01,0x01}; /* 31 bits */
static uchar iv[8]      = {0x99,0xe9,0x7c,0xbf,0x4f,0x7a,0x6e,0x8f};
static uchar plain[8]   = { 'T', 'h', 'e', ' ', 'u', 'n', 'k', 'n'};
static uchar cipher1[8] = {0x79,0x45,0x81,0xc0,0xa0,0x6e,0x40,0xa2};

#endif


#ifdef CALLEXTERNALASMCODE      /* Assembly code is better at cache mgmt */
extern uchar         cprime1[8];
extern uchar         pprime1[8];
extern uchar         ks[16][8];
extern unsigned long ks2save[2];
extern unsigned long bitmask;
extern unsigned long hash3[2];
extern unsigned long specflag;
extern unsigned long speccode;
extern unsigned long counter;
extern bool          gotkey;
#else          /* Cluster all data in global initialized data segment */
       uchar         cprime1[8] = {0};
       uchar         pprime1[8] = {0};
       uchar         ks[16][8] = {{0}};
       unsigned long ks2save[2];
       unsigned long bitmask = 0x00000001;   /* Give up after  1 bit  */
       unsigned long hash3[2] = {0,0};
       unsigned long specflag = 0;
       unsigned long speccode = 0;
       unsigned long counter = {0};
       bool          gotkey = {0};
#endif CALLEXTERNALASMCODE

#ifdef __GNUC__
#if #cpu(i386) && (TRUE)
       unsigned long ebpsave = 0;
#endif
#endif

void kstogg63();
void kstogg62();
void kstogg61();
void kstogg60();
void kstogg59();
void kstogg58();
void kstogg57();
void kstogg55();
void kstogg54();
void kstogg53();
void kstogg52();
void kstogg51();
void kstogg50();
void kstogg49();
void kstogg47();
void kstogg46();
void kstogg45();
void kstogg44();
void kstogg43();
void kstogg42();
void kstogg41();
void kstogg39();
void kstogg38();
void kstogg37();
void kstogg36();
void kstogg35();
void kstogg34();
void kstogg33();
void kstogg31();
void kstogg30();
void kstogg29();
void kstogg28();
void kstogg27();
void kstogg26();
void kstogg25();
void kstogg23();
void kstogg22();
void kstogg21();
void kstogg20();
void kstogg19();
void kstogg18();
void kstogg17();
void kstogg15();
void kstogg14();
void kstogg13();
void kstogg12();
void kstogg11();
void kstogg10();
void kstogg09();
void kstogg07();
void kstogg06();
void kstogg05();
void kstogg04();
void kstogg03();
void kstogg02();
void kstogg01();


static void (* kstogtab[56]) () = {
    kstogg58,           /* Warning -- make sure inline code is changed, too! */
    kstogg52,           /* Warning -- make sure inline code is changed, too! */
    kstogg42,
    kstogg61,
    kstogg59,
    kstogg55,
    kstogg54,
    kstogg49,
    kstogg45,
    kstogg43,
    kstogg63,
    kstogg62,
    kstogg51,
    kstogg46,
    kstogg60,
    kstogg57,
    kstogg53,
    kstogg50,
    kstogg47,
    kstogg44,
    kstogg41,

    kstogg39,
    kstogg38,
    kstogg37,
    kstogg36,
    kstogg35,
    kstogg34,
    kstogg33,

    kstogg31,
    kstogg30,
    kstogg29,
    kstogg28,
    kstogg27,
    kstogg26,
    kstogg25,

    kstogg23,
    kstogg22,
    kstogg21,
    kstogg20,
    kstogg19,
    kstogg18,
    kstogg17,

    kstogg15,
    kstogg14,
    kstogg13,
    kstogg12,
    kstogg11,
    kstogg10,
    kstogg09,

    kstogg07,
    kstogg06,
    kstogg05,
    kstogg04,
    kstogg03,
    kstogg02,
    kstogg01};

#ifdef CALLEXTERNALASMCODE
extern void crunch();
#endif
/* void buildks2(); */
void ksupd53();
void ksupd4();
void ip(uchar input[8], uchar output[8]);
void buildks(uchar key[8], uchar ks[16][8]);
void pc1(uchar key[8], unsigned char c[28], unsigned char d[28]);
void shiftcd(unsigned char c[28], unsigned char d[28]);
void pc2(unsigned char c[28], unsigned char d[28], uchar kse[8]);
char *to8x(uchar input[8], char s[17]);
void genRound1LR();
void genRound16LR();

void init(uchar p[8], uchar c[8], uchar v[8], uchar k[8], int bits)
{
  int i;
  for (i=0; i<8; i++) {
    plain[i]   = p[i];
    cipher1[i] = c[i];
    iv[i]      = v[i];
    k1[i]      = k[i];
    }
  bitmask = (1<<(bits+1)) - 1;
  }

void gethash(unsigned long *hash1p, unsigned long *hash2p)
{
  unsigned long hash[2];   /* Hash for key and complementary key */

  hash[0] = hash3[0];           /* Start with Round 3 output */
  hash[1] = hash3[1];

  /* The outputs produced by GenRound1LR cannot be mixed in  */
  /* at each iteration, because they nullify each other.     */
  /* In fact, the contribution of toggling 4 bits in         */
  /* Round 1 yield relatively minor differences in the       */
  /* Round 1 output.  A basic sanity check is all we can     */
  /* hope to achieve, here.                                  */

  /* Compute hash of current key */
  hash[0] ^= round1L[0];        /* Invariant round 1 output */
  hash[0] ^= round1R[2*10];     /* Bits 58, 54, 51, and 60 toggled */

  /* Compute hash of complementary key */
  hash[1] ^= round1L[1];        /* Invariant round 1 output */
  hash[1] ^= round1R[2*10+1];   /* Bits 58, 54, 51, and 60 toggled */

  if (specflag != 0) {
    hash[0] = specflag;         /* Alert keymaster to debug the client */
    hash[1] = speccode;
    }

  *hash1p = hash[0];            /* Return hash of key */
  *hash2p = hash[1];            /* Return hash of complementary key */

#ifdef DEBUGPRINT
  fprintf(stdout, "Hash values:\n");
  fprintf(stdout, "%8.8X %8.8X\n", round1L[0], round1L[1]);
  fprintf(stdout, "%8.8X %8.8X\n", round1R[2*10], round1R[2*10+1]);
  fprintf(stdout, "%8.8X %8.8X\n", hash3[0], hash3[1]);
  fprintf(stdout, "-------- --------\n");
  fprintf(stdout, "%8.8X %8.8X\n", hash[0], hash[1]);
#endif
  }


#ifndef CALLEXTERNALASMCODE
int tailcomp32(int regsi, int regdi)
  {
        specflag -= 1;          /* Remember highly unusual situation */
        speccode = counter;

        /* If we get here, half of the result matched.  Perform Round #4. */
        /* First, we need to generate the key schedule for Round 4, since
           it has not been fully maintained. */
        ksupd4();       /* Go update key schedule.  R4 */
        {
          unsigned long regcx, regdx;
          PREROUND(regsi,regdi);
          ROUND(regcx,regdx,ks[ 3],regsi,regdi, 1,"=S","=D",esi,edi);
          POSTROUND(regsi,regdi);
          }

        return (regsi != round2R[0]);
  }
#endif /* CALLEXTERNALASMCODE */


#ifndef CALLEXTERNALASMCODE
void genRound1LR() {
{
  static unsigned long plainL, plainR; /* Don't waste registers */
  unsigned long counter;               /* Don't waste registers */
  unsigned long regsi, regdi;          /* Input / Output to Round macro */

    regsi = *(unsigned long*)(&pprime1[0]);
    regdi = *(unsigned long*)(&pprime1[4]);

    regsi = (regsi>>1) + (regsi<<31);
    regdi = (regdi>>1) + (regdi<<31);

    plainL = regsi;             /* Save plaintext */
    plainR = regdi;

#ifdef DEADCODE
    *(unsigned long *)(&ks[ 2][0]) =
     ((*(unsigned long *)(&ks[ 1][4]) & 0x00000001) <<  3) + /* 54 46 41 0x00000008 */
     ((*(unsigned long *)(&ks[ 2][0]) & 0xFFFFFFF4));
#endif

    counter = 0;

    while (TRUE) {
      {
        unsigned long regcx, regdx;     /* Temporary vars to ROUND macro */

        /* regsi = plainL; */           /* regsi/regdi already loaded */
        /* regdi = plainR; */
        PREROUND(regsi, regdi);
        ROUND(regcx,regdx,ks[ 0],regsi,regdi, 0,"=S","=D",esi,edi);
        POSTROUND(regsi, regdi);
        }
#ifdef DEBUGPRINT
      fprintf(stdout,"G1:  After R1:  regsi=%8.8X   regdi=%8.8X\n",
          regsi, regdi);
#endif
      {
        register unsigned long tc;
        tc = counter;           /* Pick up counter */
        round1R[tc] = regsi;            /* After swap at end of round */
        round1L[tc & 0x01] = regdi;
        }
#ifdef DEBUGPRINT
      { char s[17];
        fprintf(stdout, "ks[ 0] = %s\n", to8x(ks[0], s));
        fprintf(stdout, "ks[ 1] = %s\n", to8x(ks[1], s));
        fprintf(stdout, "ks[ 2] = %s\n", to8x(ks[2], s));
        }
#endif
      {
        unsigned long regcx, regdx;     /* Temporary vars to ROUND macro */
                                        /* regsi/regdi already loaded */
        PREROUND(regsi,regdi);
        ROUND234568(regcx,regdx,ks[ 1],regdi,regsi, 1,"=D","=S",edi,esi);
        ROUND7(regcx,regdx,ks[ 2],regsi,regdi, 2,"=S","=D",esi,edi);
        POSTROUND(regsi,regdi);
        }
#ifdef DEBUGPRINT
      fprintf(stdout,"G1:  After R3:  regsi=%8.8X   regdi=%8.8X\n",
          regsi,regdi);
#endif
      {
        register unsigned long tc;
        tc = counter;           /* Pick up counter */
        round2pR[tc] = regdi;   /* After applying S-box 234568 to Round 2 */
        round3pR[tc] = regsi;   /* After applying S-Box 7 to Round 3 */

        tc += 1;
        regsi = plainL;         /* Pick up plaintext for next key */
        regdi = plainR;
        counter= tc;            /* Save updated counter */
        if (0 != (0x00000001 & tc)) {
          regsi = ~regsi;         /* Use complemented plaintext for next key */
          regdi = ~regdi;
          continue;
          }
        if (0 != (0x00000002 & tc))
          {KSTO58R1P2; continue; }
        if (0 != (0x00000004 & tc))
          {KSTO54R1P23; continue; }
        if (0 != (0x00000008 & tc))
          {KSTO51R1P2; continue; }
        KSTO60R1P2;            /* Restore key schedule to original condition */
        if (0 != (0x00000010 & tc))
          continue;
        break;
        }
      }
#ifdef DEBUGPRINT
    for (counter=0; counter<32; counter++) {
      fprintf(stdout, "%8.8X %8.8X %8.8X   ",
            round1L[counter&1], round1R[counter], round3pR[counter]);
      if (1 == (counter&1)) fprintf(stdout, "\n");
      }
#endif
    }
  } /* genRound1LR() */
#endif /* CALLEXTERNALASMCODE */


#ifndef CALLEXTERNALASMCODE
void genRound16LR()
{
  /********************************************************
   * Here we perform a pair of complementary Round 16
   * decipher operations, saving the pair of results.
   ********************************************************/

  {
    static unsigned long cipher2L, cipher2R;    /* Don't waste registers */
    unsigned long regsi, regdi;

    regsi = *(unsigned long*)(&cprime1[0]);
    regdi = *(unsigned long*)(&cprime1[4]);

    regsi = (regsi>>1) + (regsi<<31);
    regdi = (regdi>>1) + (regdi<<31);

    cipher2L = regsi;           /* Save ciphertext */
    cipher2R = regdi;

    {
      unsigned long regcx, regdx;

      PREROUND(regsi, regdi);
      ROUND(regcx,regdx,ks[15],regsi,regdi,15,"=S","=D",esi,edi);
      POSTROUND(regsi, regdi);
      round16L1 = regdi;        /* After swap at end of round */
      round16R1 = regsi;
      PREROUND(regsi, regdi);
      ROUND14568(regcx,regdx,ks[14],regdi,regsi,14,"=D","=S",edi,esi);
      POSTROUND(regsi, regdi);
      round15pR1 = regdi;       /* Save output with 5 S-boxes preapplied */
                     /* (0x00404101 | 0x00000000 | 0x00000000 | 0x40200820 |
                         0x10820040 | 0x08101004 | 0x00000000 | 0x04010410 ) */
                                /* Keep bits from S-Box 1,4,5,6,8 */

      regsi = cipher2L;         /* Get complemented ciphertext */
      regdi = cipher2R;
      regsi = ~regsi;
      regdi = ~regdi;
      PREROUND(regsi, regdi);
      ROUND(regcx,regdx,ks[15],regsi,regdi,15,"=S","=D",esi,edi);
      POSTROUND(regsi, regdi);
      round16L2 = regdi;        /* After swap at end of round */
      round16R2 = regsi;
      PREROUND(regsi, regdi);
      ROUND14568(regcx,regdx,ks[14],regdi,regsi,14,"=D","=S",edi,esi);
      POSTROUND(regsi, regdi);
      round15pR2 = regdi;       /* Save output with 5 S-boxes preapplied */
                     /* (0x00404101 | 0x00000000 | 0x00000000 | 0x40200820 |
                         0x10820040 | 0x08101004 | 0x00000000 | 0x04010410 ) */
                                /* Keep bits from S-Box 1,4,5,6,8 */
      }
#ifdef DEBUGPRINT
    fprintf(stdout, "16:  %8.8X %8.8X   %8.8X %8.8X\n",
        round15pR1, round16R1, round15pR2, round16R2);
#endif
    }
  }
#endif /* CALLEXTERNALASMCODE */


int doit()
{
  unsigned int i;
  unsigned int t, tc;

#ifdef EPPRINT
  fprintf(stdout, "doit() entered\n");
#endif

  /* fprintf(stderr, "RSA DES challenge in process...\n"); */
  /* setpriority(PRIO_PROCESS, 0, 10); */

  /* COMPUTE PPRIME1 = IV XOR PLAIN   ; (EXPECTED RESULT OF DECIPHER) */
  /* COMPUTE PPRIME2 = NOT(PPRIME1)   ; (COMPLEMENTARY RESULT)        */
  /* COMPUTE CIPHER2 = NOT(CIPHER1)   ; (COMPLEMENTARY INPUT)         */

  for (i=0; i<8; i++) {
    pprime1[i] = iv[i] ^ plain[i];
    }

  ip(cipher1, cprime1);         /* Perform Initial Permutation on ciphertext */
  ip(pprime1, pprime1);         /* Initial Permutation on expected plaintext */

  buildks(k1, ks);              /* Build key schedule for 1st key */

#ifdef PRINTDEBUG
  {
    char s[17];
    int i;
    fprintf(stdout, "  plain = %s\n", to8x(plain  , s));
    fprintf(stdout, "     iv = %s\n", to8x(iv     , s));
    fprintf(stdout, "cipher1 = %s\n", to8x(cipher1, s));
    fprintf(stdout, "    key = %s\n", to8x(k1     , s));
    fprintf(stdout,"\n");
    fprintf(stdout, "pprime1 = %s\n", to8x(pprime1, s));
    fprintf(stdout, "cprime1 = %s\n", to8x(cprime1, s));
    fprintf(stdout,"\n");
    for (i=0; i<16; i++) {
      fprintf(stdout, " ks[%2d] = %s\n", i, to8x(ks[i], s));
      }
    }
#endif /* PRINTDEBUG */

  hash3[0]=0;
  hash3[1]=0;

  counter = 0;
  specflag = 0;                 /* Nothing unusual */
  gotkey = TRUE;                /* Let's be optimistic */

#ifdef CALLEXTERNALASMCODE
  crunch();
#else
  while (TRUE) 
  {   /* LoopA */
    genRound1LR();              

    while (TRUE) 
    {   /* LoopB */
      register unsigned long regsi, regdi;

      genRound16LR();           /* Round 16 result is invariant for a while */

      regdi = round15pR1;            /* ll with part of Round 15 preapplied */
      regsi = round16R1;                          /* rr */

      while (TRUE) 
      {   /* LoopC */
        {   /* Local vars */
          unsigned long regcx, regdx;

          #ifdef XDEBUGPRINT
            { char s[17];
              fprintf(stdout, "ks[14] = %s\n", to8x(ks[14], s));
            }
          #endif

          PREROUND(regsi,regdi);
          ROUND237(regcx,regdx,ks[14],regdi,regsi,14,"=D","=S",edi,esi);

          #ifdef XDEBUGPRINT
            POSTROUND(regsi,regdi);
            fprintf(stdout, "15:  %8.8X %8.8X\n", regsi, regdi);
            PREROUND(regsi,regdi);
          #endif
          ROUND(regcx,regdx,ks[13],regsi,regdi,13,"=S","=D",esi,edi);
          ROUND(regcx,regdx,ks[12],regdi,regsi,12,"=D","=S",edi,esi);
          ROUND(regcx,regdx,ks[11],regsi,regdi,11,"=S","=D",esi,edi);
          ROUND(regcx,regdx,ks[10],regdi,regsi,10,"=D","=S",edi,esi);
          ROUND(regcx,regdx,ks[ 9],regsi,regdi, 9,"=S","=D",esi,edi);
          ROUND(regcx,regdx,ks[ 8],regdi,regsi, 8,"=D","=S",edi,esi);
          ROUND(regcx,regdx,ks[ 7],regsi,regdi, 7,"=S","=D",esi,edi);
          ROUND(regcx,regdx,ks[ 6],regdi,regsi, 6,"=D","=S",edi,esi);
          ROUND(regcx,regdx,ks[ 5],regsi,regdi, 5,"=S","=D",esi,edi);
          ROUND7(regcx,regdx,ks[ 4],regdi,regsi, 4,"=D","=S",edi,esi);
          POSTROUND(regsi,regdi);
        } /* Local vars */
        #define CODEBLOCK1 \
          if (0 != (0x00000001 & ++counter)) {                                \
            hash3[0] ^= regsi;    /* regsi contains lots of randomness */     \
            regdi = round15pR2;                 /* complementary ll */        \
            regsi = round16R2;                  /* complementary rr */        \
            continue;           /* Back to top for complementary key */       \
            }                                                                 \
          else {                                                              \
            hash3[1] ^= regsi;    /* regsi contains lots of randomness */     \
            regdi = round15pR1;                         /* ll */              \
            regsi = round16R1;                          /* rr */              \
                                                                              \
            /* These key bits are not used in the Round 16 Subkey.  We        \
               can toggle them before we have to recompute Round 16. */       \
            if (0 != (0x00000002 & counter))                                  \
              {KSTO58N1234 ; continue; }                                      \
            if (0 != (0x00000004 & counter))                                  \
              {KSTO54N1234 ; continue; }                                      \
            if (0 != (0x00000008 & counter))                                  \
              {KSTO51N1234 ; continue; }                                      \
            KSTO60N1234;        /* Keep in phase with stored Round 1 table */ \
            if (0 != (0x00000010 & counter))                                  \
              continue;                                                       \
            break;      /* Break to toggle additional key bits */             \
            }
        /* End of CODEBLOCK1 */

        if (0 != ((regdi ^ round3pR[counter&0x1f]) & 0x81080200)) 
        {
          cb1:
          CODEBLOCK1;
          }

        {   /* Local vars */
          unsigned long regcx, regdx;
          PREROUND(regsi,regdi);
          ROUND34(regcx,regdx,ks[ 4],regdi,regsi, 4,"=D","=S",edi,esi);
          POSTROUND(regsi,regdi);
          round5pR[0] = regdi;       /* Save partial output */
          round5pL[0] = regsi;
        }
        
        {   /* Local vars */
          unsigned long regcx, regdx;
          regdi = round2pR[counter&0x1f];
          regsi = round1R[counter&0x1f];
          PREROUND(regsi,regdi);
          ROUND17(regcx,regdx,ks[ 1],regdi,regsi, 1,"=D","=S",edi,esi);
          ROUND34(regcx,regdx,ks[ 2],regsi,regdi, 2,"=S","=D",esi,edi);
          POSTROUND(regsi,regdi);
        }
        
        if (0 != ((regsi ^ round5pR[0]) & 0x422088A2)) 
        {
          regsi = round5pL[0];  /* Predictable hash */
          goto cb1;
        }

        ksupd53();      /* Go update key schedule, R3/R5-S12568 */

        #ifdef DEBUGPRINT
                { char s[17];
                  fprintf(stdout, "After ROUND34(ks[4]):\n");
                  fprintf(stdout, "regsi=%8.8X     regdi=%8.8X     counter = %d\n",
                         round5pL[0], round5pR[0], counter);
                  fprintf(stdout, "After ROUND34(ks[2]):\n");
                  fprintf(stdout, "regsi=%8.8X     regdi=%8.8X     counter = %d\n",
                         regsi, regdi, counter);
                  fprintf(stdout, "ks[ 4] = %s\n", to8x(ks[4], s));
                  fprintf(stdout, "ks[ 2] = %s\n", to8x(ks[2], s));
                  }
        #endif
        {   /* Local vars */
          unsigned long regcx, regdx;
          PREROUND(regsi,regdi);
          ROUND12568(regcx,regdx,ks[ 2],regsi,regdi, 2,"=S","=D",esi,edi);
          POSTROUND(regsi,regdi);
        } /* Local vars */
        
        round3x7R[0] = regsi;      /* Save partial output */
        round2R[0] = regdi;
        regdi = round5pR[0];      /* Restore partial output */
        regsi = round5pL[0];
        
        {   /* Local vars */
          unsigned long regcx, regdx;
          PREROUND(regsi,regdi);
          ROUND12568(regcx,regdx,ks[ 4],regdi,regsi, 4,"=D","=S",edi,esi);
          POSTROUND(regsi,regdi);
        } /* Local vars */

        #ifdef DEBUGPRINT
                fprintf(stdout, "After ROUND12568(ks[4]):\n");
                fprintf(stdout, "regsi=%8.8X     regdi=%8.8X     counter = %d\n",
                        regsi, regdi, counter);
                fprintf(stdout, "After ROUND12568(ks[2]:\n");
                fprintf(stdout, "regsi=%8.8X     regdi=%8.8X     counter = %d\n",
                        round3x7R[0], round2R[0], counter);
        #endif

        /* Half of the result is known.  Perform early comparison */
        if (0 != ((regdi ^ round3x7R[0]) & 0x3CD7755D)) 
        {
          regsi = round5pL[0];  /* Predictable hash */
          goto cb1;
        }

        /* Start using space-saving, non-Pentium key toggle code */
        #undef KST15
        #undef KST14
        #undef KST13
        #undef KST12
        #undef KST11
        #undef KST10
        #undef KST9
        #undef KST8
        #undef KST7
        #undef KST3
        #undef KST2
        #undef KST1
        #define KST15 CKST15
        #define KST14 CKST14
        #define KST13 CKST13
        #define KST12 CKST12
        #define KST11 CKST11
        #define KST10 CKST10
        #define KST9  CKST9
        #define KST8  CKST8
        #define KST7  CKST7
        #define KST3  CKST3
        #define KST2  CKST2
        #define KST1  CKST1

        if (tailcomp32(regsi,regdi))    /* Go compare 32 more bits */
          goto cb1;
        goto loopexit;          /* Eureka! */

      } /* LoopC */

      #ifdef GKST15           /* If GNUC/Pentium macros generated, use them */
      #undef KST15
      #undef KST14
      #undef KST13
      #undef KST12
      #undef KST11
      #undef KST10
      #undef KST9
      #undef KST8
      #undef KST7
      #undef KST3
      #undef KST2
      #undef KST1
      #define KST15 GKST15
      #define KST14 GKST14
      #define KST13 GKST13
      #define KST12 GKST12
      #define KST11 GKST11
      #define KST10 GKST10
      #define KST9  GKST9
      #define KST8  GKST8
      #define KST7  GKST7
      #define KST3  GKST3
      #define KST2  GKST2
      #define KST1  GKST1
      #endif /* GKST15 */

      /* These 8 bits can toggle before we must recompute Round 1 table */
      if (0 != (0x00000020 & counter))
        { KSTO52 ; continue; }
      if (0 != (0x00000040 & counter))
        { KSTO43 ; continue; }
      if (0 != (0x00000080 & counter))
        { KSTO07 ; continue; }
      if (0 != (0x00000100 & counter))
        { KSTO12 ; continue; }
      break;
    } /* LoopB */


    if (0 == (bitmask & 0x003fffff & counter)) 
    {

      if (0 == (0x003fffff & counter))
        fprintf(stdout, ".");           /* BLIP every 2^21 key pairs */

      if (0 == (bitmask & counter)) {
        gotkey = FALSE;                 /* Announce we failed to find key */
        break;
        }

      if (0 == (0x0fffffff & counter))
        fprintf(stdout, "\n");          /* NL after 64 BLIPs */

      fflush(stdout);
    }

    /* Start using space-saving, non-Pentium key toggle code */
    #undef KST15
    #undef KST14
    #undef KST13
    #undef KST12
    #undef KST11
    #undef KST10
    #undef KST9
    #undef KST8
    #undef KST7
    #undef KST3
    #undef KST2
    #undef KST1
    #define KST15 CKST15
    #define KST14 CKST14
    #define KST13 CKST13
    #define KST12 CKST12
    #define KST11 CKST11
    #define KST10 CKST10
    #define KST9  CKST9
    #define KST8  CKST8
    #define KST7  CKST7
    #define KST3  CKST3
    #define KST2  CKST2
    #define KST1  CKST1

    /* Toggle one bit of key throughout entire key schedule */
    if (0 != (0x00000200 & counter)) { KSTO63 ; continue; }
    if (0 != (0x00000400 & counter)) { KSTO62 ; continue; }
    if (0 != (0x00000800 & counter)) { KSTO61 ; continue; }
    if (0 != (0x00001000 & counter)) { KSTO59 ; continue; }
    if (0 != (0x00002000 & counter)) { KSTO57 ; continue; }
    if (0 != (0x00004000 & counter)) { KSTO55 ; continue; }
    if (0 != (0x00008000 & counter)) { KSTO53 ; continue; }
    if (0 != (0x00010000 & counter)) { KSTO50 ; continue; }
    if (0 != (0x00020000 & counter)) { KSTO49 ; continue; }
    if (0 != (0x00040000 & counter)) { KSTO47 ; continue; }
    if (0 != (0x00080000 & counter)) { KSTO46 ; continue; }
    if (0 != (0x00100000 & counter)) { KSTO45 ; continue; }
    if (0 != (0x00200000 & counter)) { KSTO44 ; continue; }
    if (0 != (0x00400000 & counter)) { KSTO42 ; continue; }
    if (0 != (0x00800000 & counter)) { KSTO41 ; continue; }
    if (0 != (0x01000000 & counter)) { KSTO39 ; continue; }
    if (0 != (0x02000000 & counter)) { KSTO38 ; continue; }
    if (0 != (0x04000000 & counter)) { KSTO37 ; continue; }
    if (0 != (0x08000000 & counter)) { KSTO36 ; continue; }
    if (0 != (0x10000000 & counter)) { KSTO35 ; continue; }
    if (0 != (0x20000000 & counter)) { KSTO34 ; continue; }
    if (0 != (0x40000000 & counter)) { KSTO33 ; continue; }
    if (0 != (0x80000000 & counter)) { KSTO31 ; continue; }
      gotkey = FALSE;
      break;
  }  /* LoopA */
#endif /* OS2 */

loopexit:

  if (gotkey) 
  {
      /* fprintf(stdout, "KEY FOUND!!!!!\n"); */
      if (counter == 0) return(1);
      return(counter);
  }
  else 
  {
    /* fprintf(stdout, "KEY NOT FOUND\n"); */
    return(0);
  }

} /* doit() */


#define QKST1(round,bit) \
    QKSTB(round,((bit-1)/12),(((bit-1)/6)&1),((bit-1)%6),(bit!=0))
#ifdef LITTLEENDIAN
#define QKSTB(round,bit54,bit3,bits210,bitnz) \
  (ks[round][((bit3)<<2)+(3-(bit54))] & ((bitnz*0x80)>>(bitnz*bits210)))
#endif /* LITTLEENDIAN */
#ifdef BIGENDIAN
#define QKSTB(round,bit54,bit3,bits210,bitnz) \
  (ks[round][((bit3)<<2)+(bit54)] & ((bitnz*0x80)>>(bitnz*bits210)))
#endif /* BIGENDIAN */



void ksupd53() {
  /* Here we recover bits:   12 43 51 54 58 60 61 62 */
  *(unsigned long *)(&ks[ 4][0]) =                        /* K  KS KD   11335577 */
   ((*(unsigned long *)(&ks[13][4]) & 0x00000800)      ) +/* 12 31 29 0x00000800 */
   ((*(unsigned long *)(&ks[12][0]) & 0x10000000) <<  1) +/* 43  4  3 0x20000000 */
   ((*(unsigned long *)(&ks[11][4]) & 0x00080000) <<  8) +/* 58 19  5 0x08000000 */
   ((*(unsigned long *)(&ks[ 8][4]) & 0x00400000) <<  8) +/* 60 24  2 0x40000000 */
   ((*(unsigned long *)(&ks[ 9][0]) & 0x00000010) <<  8) +/* 61 40 28 0x00001000 */
   ((*(unsigned long *)(&ks[ 4][0]) & 0x94FCE4FC));
  *(unsigned long *)(&ks[ 4][4]) =                        /* K  KS KD   22446688 */
   ((*(unsigned long *)(&ks[ 7][0]) & 0x00100000) <<  2) +/* 51 16 12 0x00400000 */
   ((*(unsigned long *)(&ks[10][0]) & 0x00000800)      ) +/* 54 29 31 0x00000800 */
   ((*(unsigned long *)(&ks[11][0]) & 0x00000080) << 24) +/* 62 37 47 0x80000000 */
   ((*(unsigned long *)(&ks[ 4][4]) & 0x4F8FC7CF));

  /* Here we recover bits:   7 12 43 51 58 60 61 62 */
  *(unsigned long *)(&ks[ 2][0]) =
   ((*(unsigned long *)(&ks[ 5][4]) & 0x00020000) <<  9) +             /* 58 21  6 0x04000000 */
   ((*(unsigned long *)(&ks[12][0]) & 0x00800000) <<  8) +             /* 51 13  1 0x80000000 */
   ((*(unsigned long *)(&ks[ 6][4]) & 0x00000080) <<  8) +             /* 61 47 25 0x00008000 */
   ((*(unsigned long *)(&ks[ 2][0]) & 0x78FC7CFC));
  *(unsigned long *)(&ks[ 2][4]) =
   ((*(unsigned long *)(&ks[ 6][0]) & 0x00004000) << 16) +             /*  7 26 48 0x40000000 */
   ((*(unsigned long *)(&ks[ 5][4]) & 0x00000100) <<  1) +             /* 12 34 33 0x00000200 */
   ((*(unsigned long *)(&ks[ 9][4]) & 0x00004000) << 11) +             /* 43 36  9 0x02000000 */
   ((*(unsigned long *)(&ks[ 6][4]) & 0x00008000) <<  8) +             /* 60 35 11 0x00800000 */
   ((*(unsigned long *)(&ks[11][0]) & 0x00000080)      ) +             /* 62 37 35 0x00000080 */
   ((*(unsigned long *)(&ks[ 2][4]) & 0x8D4FCD4F));
  }


void ksupd4() {
  /* Here we recover bits:   7 12 43 51 52 54 58 59 60 61 62 63 */
  *(unsigned long *)(&ks[ 3][0]) =
   ((*(unsigned long *)(&ks[12][4]) & 0x40000000) >> 24) +             /* 12 12 38 0x00000040 */
   ((*(unsigned long *)(&ks[ 7][0]) & 0x00100000) <<  1) +             /* 51 16 15 0x00200000 */
   ((*(unsigned long *)(&ks[11][0]) & 0x10000000) <<  1) +             /* 59  4  3 0x20000000 */
   ((*(unsigned long *)(&ks[ 7][0]) & 0x00002000) >>  8) +             /* 61 27 39 0x00000020 */
   ((*(unsigned long *)(&ks[10][4]) & 0x00000008) << 10) +             /* 62 43 27 0x00002000 */
   ((*(unsigned long *)(&ks[ 8][4]) & 0x00400000)      ) +             /* 60 24 14 0x00400000 */
   ((*(unsigned long *)(&ks[ 3][0]) & 0xDC9CDC9C));
  *(unsigned long *)(&ks[ 3][4]) =
   ((*(unsigned long *)(&ks[ 9][4]) & 0x00004000) <<  1) +             /* 43 36 23 0x00008000 */
   ((*(unsigned long *)(&ks[ 6][4]) & 0x00000100) <<  1) +             /* 63 34 33 0x00000200 */
   ((*(unsigned long *)(&ks[ 6][0]) & 0x80000000) >> 15) +             /* 52  1 22 0x00010000 */
   ((*(unsigned long *)(&ks[ 7][0]) & 0x00004000) << 16) +             /* 54 26 48 0x40000000 */
   ((*(unsigned long *)(&ks[11][4]) & 0x00080000) <<  8) +             /* 58 19  7 0x08000000 */
   ((*(unsigned long *)(&ks[ 9][0]) & 0x00000800)      ) +             /*  7 29 31 0x00000800 */
   ((*(unsigned long *)(&ks[ 3][4]) & 0x87CE45CF));
  }


void ip(uchar input[8], uchar output[8])
{
  uchar temp[8];
  signed int i;
  uchar t;

  for (i=7; i>=0; i--) {
    t = input[i];
    temp[3] = (temp[3] << 1) + (t&1);
    t >>= 1;
    temp[7] = (temp[7] << 1) + (t&1);
    t >>= 1;
    temp[2] = (temp[2] << 1) + (t&1);
    t >>= 1;
    temp[6] = (temp[6] << 1) + (t&1);
    t >>= 1;
    temp[1] = (temp[1] << 1) + (t&1);
    t >>= 1;
    temp[5] = (temp[5] << 1) + (t&1);
    t >>= 1;
    temp[0] = (temp[0] << 1) + (t&1);
    t >>= 1;
    temp[4] = (temp[4] << 1) + (t&1);
    }

  *(unsigned long *)(&output[0]) =
      (((((temp[0] << 8) + temp[1]) << 8) + temp[2]) << 8) + temp[3];
  *(unsigned long *)(&output[4]) =
      (((((temp[4] << 8) + temp[5]) << 8) + temp[6]) << 8) + temp[7];
  }


void buildks(uchar key[8], uchar ks[16][8])
{
  static int nshift[16] = {1,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1};
  unsigned char c[28], d[28];
  int i;

  pc1(key, c, d);               /* Perform Permuted-Choice-1 on key */

  for (i=0; i<16; i++) {
    shiftcd(c, d);              /* Perform left-shift on C and D */
    if (nshift[i] == 2)
      shiftcd(c, d);            /* Perform left-shift on C and D */

    pc2(c, d, ks[i]);           /* Generate one key-schedule entry */
    }

  /* Swap key-schedule entries so the in-memory key-schedule bytes
     are arranged as follows:  (odd bytes in first 4-byte word;
     even bytes in second 4-byte word)                         */
  for (i=0; i<16; i++) {
    unsigned long kscx, ksdx;
    kscx = (((((ks[i][0] << 8) + ks[i][2]) << 8) + ks[i][4]) << 8) + ks[i][6];
    ksdx = (((((ks[i][1] << 8) + ks[i][3]) << 8) + ks[i][5]) << 8) + ks[i][7];
    *(unsigned long *)(&ks[i][0]) = kscx;       /* bytes 1, 3, 5, 7 */
    ksdx = (ksdx >> 4) + (ksdx << 28);  /* Rotate even key bytes 4 bits */
    *(unsigned long *)(&ks[i][4]) = ksdx;       /* bytes 2, 4, 6, 8 */
    }

  }


void pc1(uchar key[8], unsigned char c[28], unsigned char d[28])
{
  static int pc1cx[] = {57,49,41,33,25,17, 9, 1,58,50,42,34,26,18,10, 2,
                        59,51,43,35,27,19,11, 3,60,52,44,36};
  static int pc1dx[] = {63,55,47,39,31,23,15, 7,62,54,46,38,30,22,14, 6,
                        61,53,45,37,29,21,13, 5,28,20,12, 4};
  unsigned int i;
  unsigned int t, tbyte, tbit;
  uchar tmask;

  for (i=0; i<28; i++) {
    t = pc1cx[i]-1;
    tbyte = t >> 3;
    tbit  = t & 7;
    tmask = 0x80 >> tbit;
    c[i] = 0 != (key[tbyte] & tmask);
    }

  for (i=0; i<28; i++) {
    t = pc1dx[i]-1;
    tbyte = t >> 3;
    tbit  = t & 7;
    tmask = 0x80 >> tbit;
    d[i] = 0 != (key[tbyte] & tmask);
    }
  }


void shiftcd(unsigned char c[28], unsigned char d[28])
{
  int i;
  unsigned char tc, td;

  tc = c[0];
  td = d[0];
  for (i=0; i<27; i++) {
    c[i] = c[i+1];
    d[i] = d[i+1];
    }
  c[27] = tc;
  d[27] = td;
  }


void pc2(unsigned char c[28], unsigned char d[28], uchar kse[8])
{
  static int pc2x[8][6] = {{14,17,11,24, 1, 5},
                           { 3,28,15, 6,21,10},
                           {23,19,12, 4,26, 8},
                           {16, 7,27,20,13, 2},
                           {41,52,31,37,47,55},
                           {30,40,51,45,33,48},
                           {44,49,39,56,34,53},
                           {46,42,50,36,29,32}};
  int i, j;
  int t;
  unsigned char tbit;

  for (i=0; i<8; i++) {
    for (j=0; j<6; j++) {
      t = pc2x[i][j] - 1;
      if (t < 28)
        tbit = c[t];
      else
        tbit = d[t-28];
      kse[i] = (kse[i] << 1) + tbit;
      }
    kse[i] <<= 2;
    }
  }


#ifdef CALLEXTERNALASMCODE        /* Helper routines for assembly code */
void blippo()
{
  fprintf(stdout, ".");           /* BLIP every 2^21 key pairs */
  fflush(stdout);
  }

void nlo()
{
  fprintf(stdout, "\n");           /* NL every 64 BLIPs */
  fflush(stdout);
  }
#endif /* OS2 */


char *to8x(uchar input[8], char s[17])
{
  sprintf(s, "%8.8X%8.8X", *(unsigned long *)(&input[0]),
      *(unsigned long *)(&input[4]));
  return(s);
   }



void kstogg01() {KSTO01}
void kstogg02() {KSTO02}
void kstogg03() {KSTO03}
void kstogg04() {KSTO04}
void kstogg05() {KSTO05}
void kstogg06() {KSTO06}
void kstogg07() {KSTO07}
void kstogg09() {KSTO09}
void kstogg10() {KSTO10}
void kstogg11() {KSTO11}
void kstogg12() {KSTO12}
void kstogg13() {KSTO13}
void kstogg14() {KSTO14}
void kstogg15() {KSTO15}
void kstogg17() {KSTO17}
void kstogg18() {KSTO18}
void kstogg19() {KSTO19}
void kstogg20() {KSTO20}
void kstogg21() {KSTO21}
void kstogg22() {KSTO22}
void kstogg23() {KSTO23}
void kstogg25() {KSTO25}
void kstogg26() {KSTO26}
void kstogg27() {KSTO27}
void kstogg28() {KSTO28}
void kstogg29() {KSTO29}
void kstogg30() {KSTO30}
void kstogg31() {KSTO31}
void kstogg33() {KSTO33}
void kstogg34() {KSTO34}
void kstogg35() {KSTO35}
void kstogg36() {KSTO36}
void kstogg37() {KSTO37}
void kstogg38() {KSTO38}
void kstogg39() {KSTO39}
void kstogg41() {KSTO41}
void kstogg42() {KSTO42}
void kstogg43() {KSTO43}
void kstogg44() {KSTO44}
void kstogg45() {KSTO45}
void kstogg46() {KSTO46}
void kstogg47() {KSTO47}
void kstogg49() {KSTO49}
void kstogg50() {KSTO50}
void kstogg51() {KSTO51}
void kstogg52() {KSTO52}
void kstogg53() {KSTO53}
void kstogg54() {KSTO54}
void kstogg55() {KSTO55}
void kstogg57() {KSTO57}
void kstogg58() {KSTO58}
void kstogg59() {KSTO59}
void kstogg60() {KSTO60}
void kstogg61() {KSTO61}
void kstogg62() {KSTO62}
void kstogg63() {KSTO63}


int selftest()
{
  unsigned int i, j, k;
  unsigned long hash1, hash2;

  uchar stkt[8];

  /* Following are a correct set of plaintext/ciphertext/iv/key */
  uchar stk1[8]    = {0x5E,0xD9,0x20,0x4F,0xEC,0xE0,0xB9,0x67}; /* correct key */
  uchar stk2[8]    = {0xA1,0x26,0xDF,0xB0,0x13,0x1F,0x46,0x98}; /* complementary key */
  uchar stk3[8]    = {0x5E,0xD9,0x20,0x4F,0xEF,0x1F,0x46,0x98}; /* incorrect key with known hash values */
  uchar stiv[8]    = {0xA2,0x18,0x5A,0xBF,0x45,0x96,0x60,0xBF};
  uchar stp[8]     = { 'T', 'h', 'e', ' ', 'u', 'n', 'k', 'n'};
  uchar stc[8]     = {0x3E,0xA7,0x86,0xF9,0x1D,0x76,0xBB,0xD3};

  uchar stpv[8], stcv[8], stivv[8], stkv[8], stpv1[8], stpv2[8];
  uchar stzzzv[8]  = {0xD9,0x24,0x69,0xEE,0xC8,0x0E,0x1F,0xB2};

  /* Following are the bit-positions of each kstogtab entry */
  short int kstogbit[] = {
    58,
    52,
    42,
    61,
    59,
    55,
    54,
    49,
    45,
    43,
    63,
    62,
    51,
    46,
    60,
    57,
    53,
    50,
    47,
    44,
    41,

    39,38,37,36,35,34,33,
    31,30,29,28,27,26,25,
    23,22,21,20,19,18,17,
    15,14,13,12,11,10, 9,
     7, 6, 5, 4, 3, 2, 1};

  /* Check known plaintext/ciphertext/iv/key */
  init(stp, stc, stiv, stk1, 0);
  if (doit() != 1) {
    fprintf (stderr, "Selftest A failed\n");
    return(1);
    }

  /* Check complementary key for known plaintext/ciphertext/iv/key */
  init(stp, stc, stiv, stk2, 0);
  if (doit() != 1) {
    fprintf (stderr, "Selftest B failed\n");
    return(1);
    }

  /* Check key toggle functions */
  /* Note -- this doesn't work very well for Round 2 keys */
  for (k=0; k<(sizeof(kstogtab)/sizeof(kstogtab[0])); k++) {
    int bytenumber, bitnumber;

    for (i=0; i<8; i++)
      stkt[i] = 0x00;           /* Initialize key to zeros */
    bytenumber = (kstogbit[k]-1) >> 3;  /* get byte number */
    bitnumber  = (kstogbit[k]-1) & 7;   /* get bit number */

    stkt[bytenumber] ^= 0x80>>bitnumber;        /* Set a single bit in key */
    buildks(stkt, ks);          /* Build key schedule for this key */

    (kstogtab[k])();            /* Toggle the same bit */
    ksupd53();                  /* Toggles don't maintain key */
    ksupd4();                   /* Toggles don't maintain key */

    for (i=0; i<16; i++)        /* Check that each key schedule entry is 0 */
      for (j=0; j<8; j++)       /* Check that each byte is 0 */
        if(ks[i][j] != 0x00) {
          fprintf (stderr, "Selftest C failed -- i,j,k = %d %d %d\n",i,j,kstogbit[k]);
          return(1);
          }
    }

  /* Perform a validation test of (almost) the whole shebang */
  init(stp, stc, stiv, stk3, 14);       /* Test 2^14 key pairs */
  if (doit() != 0) {
    fprintf (stderr, "Selftest D failed\n");
    return(1);
    }

  gethash(&hash1, &hash2);     /* Get hash results */
                               /* 2^21 pairs - [B82A9121:FF7C6F6A] */
                               /* 2^14 pairs - [10BEC72B:C88D989D] */
                               /* 2^14 pairs - [AF06B949.81C34CDC] */
                               /* 2^14 pairs - [8747E82A-D2153C36] */
                               /* 2^14 pairs - [1C7BC8D1+D7243D66] T2 */
                               /* 2^14 pairs - [5EC47F4D,04B9A20F] T2 */
                               /* 2^14 pairs - [A71C2FE3/E335B072] T2 */
  if ((0xA71C2FE3 != hash1) || (0xE335B072 != hash2)) {
    fprintf (stderr, "Selftest E failed [%8.8X:%8.8X]\n", hash1, hash2);
    return(1);
    }

  return(0);

  } /* selftest() */
