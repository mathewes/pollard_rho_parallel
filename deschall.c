#ifdef OS2
#ifndef BSD_SELECT
#define BSD_SELECT
#endif /* BSD_SELECT */
#define NOT_UNIX
#define time_t long
#include <stdlib.h>
#include <stdio.h>
#include <types.h>
#include <sys/socket.h>
#include <sys/select.h>
#include <sys/time.h>
#include <netinet/in.h>
#include <netdb.h>
#define INCL_DOSPROCESS         /* DosSetPriority */
#include <os2.h>                /* DosSetPriority */

#else

#include <stdio.h>
#include <assert.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#ifdef _MSC_VER
#include <time.h>
#include <winsock.h>
#include <winbase.h>            /* This is for SetPriorityClass */
#else
#include <unistd.h>
#include <sys/time.h>
#include <sys/file.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#endif /* _MSC_VER */
#endif /* OS2 */

#ifdef __FreeBSD__
#include <sys/param.h>
#include <sys/sysctl.h>
#endif

#define FORKABLE
#ifdef OS2
#undef FORKABLE
#endif
#ifdef _MSC_VER
#undef FORKABLE
#endif

#include "dic.h"
#include "keyclnt.h"

#define RECV s
#define SEND s

#define RECVFROM(a,b,c,d,e,f) recvfrom(a,b,c,d,e,f)
#define SENDTO(a,b,c,d,e,f) sendto(a,b,c,d,e,f)

#ifdef _MSC_VER
static SOCKET s;
#else
static int s;
#endif

#ifdef _MSC_VER
#define SOCKERR(x) ((x) == SOCKET_ERROR)
#else
#define SOCKERR(x) ((x) < 0)
#endif

static struct sockaddr_in addr;

static char buf[MAX_MSG] = {0};
static int debug = 0;

#ifdef HELLFREEZESOVER
static char *bitmask[]={
                           "02100000003EFEFE",  /* 21 variable bits */
                           "02100000007EFEFE",  /* 22 */
                           "0210000000FEFEFE",  /* 23 */
                           "0210000002FEFEFE",  /* 24 */
                           "0210000006FEFEFE",  /* 25 */
                           "021000000EFEFEFE",  /* 26 */
                           "021000001EFEFEFE",  /* 27 */
                           "021000003EFEFEFE",  /* 28 */
                           "021000007EFEFEFE",  /* 29 */
                           "02100000FEFEFEFE",  /* 30 */
                           "02100002FEFEFEFE",  /* 31 */
                           "02100006FEFEFEFE"}; /* 32 */
#endif


int cvthex8(char s[17], char hex[8]);
void getsysinfo(char *s, int slen, char *ds);
void catmibinfo(char *s, int mibmajor, int mibminor, int maxlen);
void catmibint(char *s, int mibmajor, int mibminor, int maxlen);

static void measure(void)
{
    time_t tstart;

    time(&tstart);      /* Save start time */

    /* Perform a bogus set of decryptions */
    init("5555555555555555", "AAAAAAAAAAAAAAAA", "0000000000000000",
            "0123456789ABCDEF", 21);
    doit();

    printf("2^21 complementary pairs of keys tested: %ld seconds\n",(long)(time((time_t *)0)-tstart));
}


static void send_rep(char *m)
{
    fd_set fdset;
    struct timeval to;

    struct sockaddr_in from;
    int len,fromlen,fds,msglen;

    time_t retry_delay=RETRY_DELAY;
    time_t timeout;

    while (1) {
        FD_ZERO(&fdset);
        FD_SET(RECV,&fdset);
        to.tv_sec = 0;
        to.tv_usec = 0;
        if ((fds = select(RECV+1,&fdset,NULL,NULL,&to)) < 0) PDIE("select");
        if (!fds) break;
        fromlen = sizeof(from);
        (void) RECVFROM(RECV,buf,MAX_MSG,0,(struct sockaddr *)&from,&fromlen);
    }
    len = strlen(m);

    timeout=time((time_t *)0)+MAX_DELAY*60;     /* compute time some minutes away */
    while(time((time_t *)0)<timeout) {
        if (SOCKERR(SENDTO(SEND,m,len,0,(struct sockaddr *)&addr,sizeof(addr))))
            perror("sendto");
        FD_ZERO(&fdset);
        FD_SET(RECV,&fdset);
        to.tv_sec = retry_delay>MAX_RETRY_DELAY?
                        MAX_RETRY_DELAY:
                        (retry_delay=retry_delay+RETRY_DELAY);
        to.tv_usec = 0;
        if ((fds = select(RECV+1,&fdset,NULL,NULL,&to)) < 0) PDIE("select");
        if (!fds) continue;

        fromlen = sizeof(from);
        if (SOCKERR(msglen = RECVFROM(RECV,buf,MAX_MSG,0,(struct sockaddr *)&from,
                                                        &fromlen))) {
            perror("recvfrom");
            continue;
        }
        if (from.sin_addr.s_addr != addr.sin_addr.s_addr) {
            printf("Received packet from host %lX\n",from.sin_addr.s_addr);
            continue;
        }
        buf[msglen] = 0;
        if (buf[0]=='M') {
            printf("%s\n",buf);
            continue;
        }
        return;
    }
    if (m[0]=='F') {
      printf("\nKey was found, but network notification failed.\n");
      printf("Please send e-mail or telephone!!!!!\n");
      }
    else
      printf("Unable to contact server for more work.\n");
    exit(2);
}


void main(int argc, char *argv[])
{
#ifndef _MSC_VER
    unsigned long id;
    int pid;
#endif
    int bits,number,pass;

    time_t tstart,tstop;
    long tdelta;

    struct hostent *temp;

    char msg[MAX_MSG];
    char *prog=argv[0];
    char sysinfos[161], dateinfos[40];
#ifdef LOCKSWORK
    int lockfd;
#endif

    printf("DES Challenge Solver\n");
    printf("Copyright (c) Rocke Verser, 1986, 1997\n");
    printf("All Rights Reserved.\n\n");
    printf("***** FOR USE IN THE USA AND CANADA ONLY *****\n");
    printf("*************** NOT FOR EXPORT ***************\n");

    if (argc == 2 && !strcmp(argv[1],"-m")) {
        measure();
        exit(0);
        }

    if ((debug = (argc > 1 && !strcmp(argv[1],"-d")))) {
        argv++;
        argc--;
        }

#ifdef LOCKSWORK
    if (argc > 1 && !strcmp(argv[1],"-e")) {
        argv++;
        argc--;
        if (fork()) exit(0);
        lockfd=open(LOCK, O_RDWR | O_CREAT, 0644);
        if (lockfd<0) exit(1);
        if (flock(lockfd, LOCK_EX|LOCK_NB) < 0) exit(1);
        if (lockfd) close(0);
        close(1);
        close(2);
    }
#endif

#ifndef FORKABLE
    if (argc != 2) {
        fprintf(stderr,"usage: %s server   OR\n"
#else
    if (argc != 2 && argc != 3) {
        fprintf(stderr,"usage: %s [-d] [-e] server [ #multiprocessors ]   OR\n"
#endif
                       "       %s -m           (for measurements)\n",
                       prog, prog);
        exit(0);
    }
#ifndef FORKABLE
    number = 1;
#else
    if (argc <= 2) number = 1;
    else for (number = 1; number < atoi(argv[2]); number++) {
            if ((pid = fork()) < 0) PDIE("fork");
            if (!pid) break;
            }

    nice(NICE_VAL);
#endif /* FORKABLE */
#ifdef OS2
    if (0 != DosSetPriority(PRTYS_THREAD,PRTYC_IDLETIME,+31,0))
      fprintf(stderr, "DosSetPriority failed\n");
#endif /* OS2 */
#ifdef _MSC_VER
    /* We'd like to be faster than screensavers, but lower than "real" work */
    if (!SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_HIGHEST))
      fprintf(stderr, "SetThreadPriority failed\n");
    if (!SetPriorityClass(GetCurrentProcess(), IDLE_PRIORITY_CLASS))
      fprintf(stderr, "SetPriorityClass failed\n");
#endif

    if (selftest())
      exit(1);
    else
      fprintf(stderr, "Selftest passed\n");

    getsysinfo(sysinfos, sizeof(sysinfos), dateinfos);

    bits = 22; pass=1;
#ifdef OS2
    if (0 != sock_init()) {
      fprintf(stderr, "INET.SYS probably is not running\n");
      }
#endif
#ifdef _MSC_VER
    {
        WORD wVersionRequested;
        WSADATA wsaData;
        int err;
        wVersionRequested = MAKEWORD(1, 1);

        err = WSAStartup(wVersionRequested, &wsaData);

        if (err != 0) {
            printf("Usable winsock DLL not found\n");
            exit(1);
            }

        /* Confirm that the Windows Sockets DLL supports 1.1.*/
        /* Note that if the DLL supports versions greater */
        /* than 1.1 in addition to 1.1, it will still return */
        /* 1.1 in wVersion since that is the version we */
        /* requested. */

        if ( LOBYTE( wsaData.wVersion ) != 1 ||
                HIBYTE( wsaData.wVersion ) != 1 ) {
            printf("Usable winsock DLL not found\n");
            WSACleanup();
            exit(2);
            }
        /* The Windows Sockets DLL is acceptable. Proceed. */
        }
#endif


    s = socket(PF_INET, SOCK_DGRAM, 0);
    if (SOCKERR(s)) PDIE("socket");
    memset(&addr,0,sizeof (addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons(0);
    addr.sin_addr.s_addr = htonl(INADDR_ANY);
    if (SOCKERR(bind(SEND,(struct sockaddr *) &addr,sizeof(addr)))) PDIE("bind");

    {
      char *t;
      unsigned short serverportn;
      unsigned int n1;

      serverportn = DIC_PORT;

      t = strstr(argv[1],":");
      if (t != NULL) {
        *t = 0;
        if (sscanf(t+1, "%d", &n1) == 1)
          serverportn = n1;
        else
          *t = ':';
        }

      addr.sin_port = htons(serverportn);
      if ((temp = gethostbyname(argv[1]))) {
        addr.sin_family = temp->h_addrtype;
        memcpy(&addr.sin_addr,temp->h_addr,temp->h_length);
        }
      else {
        addr.sin_family = AF_INET;
        if ((addr.sin_addr.s_addr = inet_addr(argv[1])) == -1) PDIE(argv[1]);
        }
      }

    sprintf(msg,"I2 %d %s %s",bits,sysinfos,dateinfos);
                                        /* Send "Initial" request */
                                        /* "2" signal says we vary bits 7,12 */
    send_rep(msg);
    printf("Processor #%d: Working\n",number);
    fflush(stdout);

    while (1) {
        char s1[17], s2[17], s3[17], s4[17], s5[17];
        int kbits;
        char t;
        char plain[8], cipher[8], iv[8], startkey[8], checksum[8];
        int i;
        int t2;
        int kiter;
        unsigned long hash1, hash2;

#ifdef DEBUGPRINT
        printf("Buffer:  %s\n", buf);
        fflush(stdout);
#endif

        if (buf[0]=='Z') {
            printf("Client stopped by server (%s)\n",buf);
            exit(2);
        }
        /* Expect message like: */
        /*    A plaintext ciphertext iv key checksum nbits */
        if (sscanf(buf, "A2 %s %s %s %s %s %lu", s1, s2, s3, s4, s5, &kbits)!= 6) {
            printf("Invalid msg: '%s'\n",buf);
            exit(1);
        }

#ifdef DEBUGPRINT
        printf("Packet received:  %s\n", buf);
        fflush(stdout);
#endif

        if (strcmp(s1, "-") == 0)
          strcpy(s1, "54686520756E6B6E");   /* RSA contest plaintext */

        if (strcmp(s2, "-") == 0)
          strcpy(s2, "794581C0A06E40A2");   /* RSA contest ciphertext */

        if (strcmp(s3, "-") == 0)
          strcpy(s3, "99E97CBF4F7A6E8F");   /* RSA contest IV */

        t  = cvthex8(s1, plain);          /* t = return code */
        t |= cvthex8(s2, cipher);
        t |= cvthex8(s3, iv);
        t |= cvthex8(s4, startkey);
        t |= cvthex8(s5, checksum);

        if (t != 0) {
                printf("Invalid msg: '%s'\n", buf);
                exit(1);
        }

        t = 0;
        for (i=0; i<8; i++) {
          t2  = plain[i];
          t2 ^= cipher[i];
          t2 ^= iv[i];
          t2 ^= startkey[i];
          t2 ^= checksum[i];
          t  |= t2;
          }

        if (t != 0) {
                printf("Invalid checksum: '%s'\n", buf);
                exit(1);
        }


        t = 1;
        for (i=0; i<8; i++) {
          t2  = 0 != (startkey[i] & 0x80);
          t2 ^= 0 != (startkey[i] & 0x40);
          t2 ^= 0 != (startkey[i] & 0x20);
          t2 ^= 0 != (startkey[i] & 0x10);
          t2 ^= 0 != (startkey[i] & 0x08);
          t2 ^= 0 != (startkey[i] & 0x04);
          t2 ^= 0 != (startkey[i] & 0x02);
          t2 ^= 0 != (startkey[i] & 0x01);
          t  &= t2;
          }

        if (t != 1) {
                printf("Invalid key-parity: '%s'\n", buf);
                exit(1);
        }

        printf("Processor %d -- 2^%u complementary pairs of keys starting with %s\n",
                number, kbits, s4);
        fflush(stdout);

        init(plain,cipher,iv,startkey,kbits);

        time(&tstart);          /* Save time when we started */

        kiter = doit();
        if (kiter!=0) {
            sprintf(msg,"F2 %u %s", kiter, buf); /* Eureka, I found it! */
            send_rep(msg);
            printf("\nProcessor %d -- Key found after %d iterations\n",
                    number, kiter);
            exit(1);
        }
        fflush(stdout);

        time(&tstop);           /* Save time when we stopped */

        gethash(&hash1, &hash2);     /* Get hash results */

        bits = kbits;

        tdelta = (long)(tstop - tstart);

        if (kbits >= 27) printf("\n");
        printf("Processor %d -- Elapsed time: %ld seconds\n", number, tdelta);

        if (selftest()) {
          printf("Selftest failed\n");
          exit(3);
          }

        if (pass==1)
          pass=2;
        else {
          if (tdelta*3 < 2*SECONDS*2) bits += 1;
          if (tdelta*2 > 2*SECONDS*3) bits -= 1;
          if (bits < 22) bits = 22;
          if (bits > 31) bits = 31;
          }

        sprintf(msg,"N2[%8.8X/%8.8X] %d %s", hash1, hash2, bits, buf);
                                        /* Not found -- request more work */
        send_rep(msg);
        printf("Processor %d -- Key not found\n", number);
    }
}


int cvthex8(char s[17], char hex[8])
{
  int t1, t2;
  if (sscanf(s, "%8x%8x", &t1, &t2) != 2) {
      printf("Invalid hexdata: '%s'\n",s);
      return(1);
      }
  hex[3] =  t1      & 0xff;
  hex[2] = (t1>> 8) & 0xff;
  hex[1] = (t1>>16) & 0xff;
  hex[0] = (t1>>24) & 0xff;
  hex[7] =  t2      & 0xff;
  hex[6] = (t2>> 8) & 0xff;
  hex[5] = (t2>>16) & 0xff;
  hex[4] = (t2>>24) & 0xff;
  return(0);
  }

void getsysinfo(char *s, int slen, char *ds)
{
  int mib[4];

  s[0] = 0;

#ifdef __FreeBSD__
  /* Each of the following appends a sysctl string of restricted length to s */
  catmibinfo(s, CTL_HW, HW_MACHINE, (slen-strlen(s))/5);
  catmibinfo(s, CTL_HW, HW_MODEL, (slen-strlen(s))/4);
  catmibint(s, CTL_HW, HW_NCPU, 4);
  catmibint(s, CTL_HW, HW_PHYSMEM, 12);
  catmibinfo(s, CTL_KERN, KERN_OSTYPE , (slen-strlen(s))/2);
  catmibinfo(s, CTL_KERN, KERN_OSRELEASE , (slen-strlen(s))/1);
#else
#ifdef OS2
  strcat(s, "OS/2");
#else
#ifdef _MSC_VER
  strcat(s, "Windows");
#else
#ifdef __linux__
  strcat(s, "Linux");
#else
  strcat(s, "?");
#endif /* __linux__ */
#endif /* _MSC_VER */
#endif /* OS2 */
#endif /* __FreeBSD__ */

  sprintf(ds, "V0.214 %s %s", __DATE__, __TIME__);
  fprintf(stdout, "Program version:  %s\n", ds);
  }

#ifdef __FreeBSD__
void catmibinfo(char *s, int mibmajor, int mibminor, int maxlen)
{
  int mib[2];
  size_t tlen;
  char t[129];
  int i;

  mib[0] = mibmajor;
  mib[1] = mibminor;
  tlen = maxlen-1;
  sysctl(mib, 2, t, &tlen, NULL, 0);
  if (tlen > maxlen-1) tlen = maxlen-1;
  for (i=0; i<tlen; i++) {
    if (t[i] == 0) break;
    if (isspace(t[i])) t[i] = '.';
    if (!isprint(t[i])) t[i] = '?';
    if (t[i] == '/') t[i] = '|';
    }
  strncat(s, t, 16);
  strcat(s, "/");
  }

void catmibint(char *s, int mibmajor, int mibminor, int maxlen)
{
  int mib[2];
  size_t tlen;
  int t; char ts[16];

  do {
    mib[0] = mibmajor;
    mib[1] = mibminor;
    tlen = sizeof(t);
    sysctl(mib, 2, &t, &tlen, NULL, 0);
    if (tlen != sizeof(t)) break;
    sprintf(ts, "%d", t);
    if (strlen(ts) > maxlen-1) break;
    strncat(s, ts, 16);
    } while (0);
  strcat(s, "/");
  }
#endif /* __FreeBSD__ */
