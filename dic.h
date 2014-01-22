/* Written by Germano Caronni and Werner Almesberger */
/* (c) by G. Caronni in '94 */
/* This program is under the GNU Public License Version 2 */

/* dic.h */

#define MAXLEN 16 /* maximal range-width, pw-length */

#define INIT_FILE "state.init"
#define CURR_FILE "state.curr"
#define DUMP_INTERVALL 20

#ifndef DIC_PORT
#define DIC_PORT 8668
#endif
#define MAX_MSG  10000
#define IDLE_TMO 5
#define PDIE(x) { perror(x); exit(1); }

#define SECONDS 1200 /* per run */
#define MAX_DELAY 24*60 /* min (before death) */
#define RETRY_DELAY 10 /* sec */
#define MAX_RETRY_DELAY 600 /* delay gets longer until max reached (sec) */

/* #define UFC_PROBE 3000 -- should now be adaptive */

/*as ktikX remove dot-files in /tmp (sigh) */
#define LOCK "/usr/tmp/.dic-client-lock"
#define NICE_VAL 10

/* define this if flock() does not exist like under std solaris 2.3 */
#undef    USE_LOCKF

#define JOB_TIMEOUT (60*55) /* jobbers are marked with timeout after 55'*/

typedef unsigned char uchar;
