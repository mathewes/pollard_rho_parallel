#include<stdio.h>
typedef unsigned long long u64;
typedef unsigned long long int64_t;
int64_t mulHi(int64_t x, int64_t y) {
    return (int64_t)((__int128_t)x*y >> 64);
}

int main()
{
//18446744073709551616
//1075426899686243820
u64 t1=31231230000;
u64 t2=34434343434;
u64 result=t1*t2;
printf("%lld\n",result);
printf("%lld\n",mulHi(t1,t2));
return 0;
}


#if !defined(BATCH) && !defined(TEST)
        { FILE *handle;

          handle = popen("/usr/sbin/sendmail -t", "w");
          if (handle == NULL) {
            puts("Warning: couldn't pipe to sendmail, send by hand!");
            fflush(stdout);
          } else {
            int status;

            fprintf( handle
                   , "To: " STRINGIFY(TO) "\n"
                     "ECCp-89 s %07lx%016lx i %012lx "
                     "x %07lx%016lx y %07lx%016lx z %x "
                     "u %07lx%016lx v %07lx%016lx "
                     CLIENT " " VERSION " " STRINGIFY(FROM) " ;\n"
                   , startv.hi, startv.lo, iters, x3.hi, x3.lo, y3.hi, y3.lo
                   , z3, u3.hi, u3.lo, v3.hi, v3.lo
                   );
            /* Timing. */
            if (dUT) {
              fprintf( handle
                     , "Total iterations = %lu at %g/sec\n"
                     , total, dRate
                     );
            } /* end if */
            fflush(handle);
            status = pclose(handle);
            if (status != EX_OK) {
              printf("Warning: sendmail returned status %d\n", status);
              fflush(stdout);
            } /* end if */
          } /* end if/else */
        } 
#endif