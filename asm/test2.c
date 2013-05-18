
#include "stdio.h"

typedef unsigned long long u64;
typedef unsigned int u32;

inline u64 mod_mul(u64 a, u64 b, u64 p)
{
	u64 ret;
	/*__asm__(
	"movq %0, %%rax;\n"
	"mulq %1;\n"
	"divq %2;\n"
	"movq %%rdx, %3;"
	:
	:"g"(a), "g"(b), "g"(p), "g"(ret)
	:"%rax", "rdx"
	);*/
	/*__asm__(
	"movq %0, %%rax;\n"
	"mulq %1;\n"
	"movq %%rdx, %2;"
	:
	:"g"(a), "g"(b), "g"(ret)
	:"%rax", "rdx"
	);*/
	__asm__(
	"mul %0, %1, %2;\n"
	:
	:"g"(a), "g"(b), "g"(ret)
	);
	return ret;
}

u64 mod_test(u64 a, u64 n, u64 p)

{
u64 ret = 1;
//u64 b = mod_mul(a, a, p);
//ret = mod_mul(ret, b, p);
ret=mod_mul(a,n,p);
return ret;
}

int main()
{
u64 ret = mod_test(2, 4, 10);
printf("%llu\n", ret);
return 0;
}