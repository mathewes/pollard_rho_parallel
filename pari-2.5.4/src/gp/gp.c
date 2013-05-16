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
/**                                                               **/
/**                        PARI CALCULATOR                        **/
/**                                                               **/
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"
#include "gp.h"

#ifdef _WIN32
#  include <windows.h>
#  ifndef WINCE
#    include <process.h>
#  endif
#endif

#ifdef READLINE
BEGINEXTERN
#  include <readline/readline.h>
ENDEXTERN
#endif

/********************************************************************/
/**                                                                **/
/**                            STRINGS                             **/
/**                                                                **/
/********************************************************************/

#define skip_space(s) while (isspace((int)*s)) s++
#define skip_alpha(s) while (isalpha((int)*s)) s++

static char *
translate(char **src, char *s)
{
  char *t = *src;
  while (*t)
  {
    while (*t == '\\')
    {
      switch(*++t)
      {
        case 'e':  *s='\033'; break; /* escape */
        case 'n':  *s='\n'; break;
        case 't':  *s='\t'; break;
        default:   *s=*t; if (!*t) pari_err(talker,"unfinished string");
      }
      t++; s++;
    }
    if (*t == '"')
    {
      if (t[1] != '"') break;
      t += 2; continue;
    }
    *s++ = *t++;
  }
  *s=0; *src=t; return s;
}

#define match2(s,c) if (*s != c) \
                      pari_err(talker,"expected character: '%c' instead of",c);

/*  Read a "string" from src. Format then copy it, starting at s. Return
 *  pointer to char following the end of the input string */
static char *
readstring(char *src, char *s)
{
  match2(src, '"'); src++; s = translate(&src, s);
  match2(src, '"'); return src+1;
}
/*******************************************************************/
/**                                                               **/
/**                    TEXMACS-SPECIFIC STUFF                     **/
/**                                                               **/
/*******************************************************************/
static int tm_is_waiting = 0, tm_did_complete = 0;

/* tell TeXmacs GP will start outputing data */
static void
tm_start_output(void)
{
  if (!tm_is_waiting) { printf("%cverbatim:",DATA_BEGIN); fflush(stdout); }
  tm_is_waiting = 1;
}
/* tell TeXmacs GP is done and is waiting for new data */
static void
tm_end_output(void)
{
  if (tm_is_waiting) { printf("%c", DATA_END); fflush(stdout); }
  tm_is_waiting = 0;
}
static char *
fgets_texmacs(char *s, int n, FILE *f)
{
  if (!tm_did_complete)
  {
    tm_start_output(); tm_end_output(); /* tell TeXmacs we need input */
  }
  return fgets(s,n,f);
}

#ifdef READLINE
typedef struct {
  char *cmd;
  long n; /* number of args */
  char **v; /* args */
} tm_cmd;

static void
parse_texmacs_command(tm_cmd *c, const char *ch)
{
  long l = strlen(ch);
  char *t, *s = (char*)ch, *send = s+l-1;
  char **A;
  pari_stack s_A;

  if (*s != DATA_BEGIN || *send-- != DATA_END)
    pari_err(talker, "missing DATA_[BEGIN | END] in TeXmacs command");
  s++;
  if (strncmp(s, "special:", 8)) pari_err(talker, "unrecognized TeXmacs command");
  s += 8;
  if (*s != '(' || *send-- != ')')
    pari_err(talker, "missing enclosing parentheses for TeXmacs command");
  s++; t = s;
  skip_alpha(s);
  c->cmd = pari_strndup(t, s - t);
  stack_init(&s_A,sizeof(*A),(void**)&A);
  for (c->n = 0; s <= send; c->n++)
  {
    char *u = (char*)pari_malloc(strlen(s) + 1);
    skip_space(s);
    if (*s == '"') s = readstring(s, u);
    else
    { /* read integer */
      t = s;
      while (isdigit((int)*s)) s++;
      strncpy(u, t, s - t); u[s-t] = 0;
    }
    stack_pushp(&s_A, u);
  }
  c->v = A;
}

static void
free_cmd(tm_cmd *c)
{
  while (c->n--) pari_free((void*)c->v[c->n]);
  pari_free((void*)c->v);
}

static void
handle_texmacs_command(const char *s)
{
  tm_cmd c;
  parse_texmacs_command(&c, s);
  if (strcmp(c.cmd, "complete"))
    pari_err(talker,"Texmacs_stdin command %s not implemented", c.cmd);
  if (c.n != 2)
    pari_err(talker,"was expecting 2 arguments for Texmacs_stdin command");
  texmacs_completion(c.v[0], atol(c.v[1]));
  free_cmd(&c);
  tm_did_complete = 1;
}
#else
static void
handle_texmacs_command(const char *s)
{ (void)s;pari_err(talker, "readline not available"); }
#endif

/*******************************************************************/
/**                                                               **/
/**                          BUFFERS                              **/
/**                                                               **/
/*******************************************************************/
static Buffer **bufstack;
static pari_stack s_bufstack;

static void
pop_buffer(void)
{
  if (s_bufstack.n)
    delete_buffer( bufstack[ --s_bufstack.n ] );
}

/* kill all buffers until B is met or nothing is left */
static void
kill_buffers_upto(Buffer *B)
{
  while (s_bufstack.n) {
    if (bufstack[ s_bufstack.n-1 ] == B) break;
    pop_buffer();
  }
}
static void
kill_buffers_upto_including(Buffer *B)
{
  while (s_bufstack.n) {
    if (bufstack[ s_bufstack.n-1 ] == B) { pop_buffer(); break; }
    pop_buffer();
  }
}

/********************************************************************/
/**                                                                **/
/**                             HELP                               **/
/**                                                                **/
/********************************************************************/
static int disable_exception_handler = 0;
static char *Help;

static char *
init_help(void)
{
  char *h = os_getenv("GPHELP");
# ifdef GPHELP
  if (!h) h = (char*)GPHELP;
# endif
  if (h) h = pari_strdup(h);
  return h;
}

static void
hit_return(void)
{
  int c;
  if (GP_DATA->flags & (gpd_EMACS|gpd_TEXMACS)) return;
  disable_exception_handler = 1;
  pari_puts("---- (type RETURN to continue) ----");
  /* if called from a readline callback, may be in a funny TTY mode */
  do c = fgetc(stdin); while (c >= 0 && c != '\n' && c != '\r');
  pari_putc('\n');
  disable_exception_handler = 0;
}
static void
gp_ask_confirm(const char *s)
{
  err_printf(s);
  err_printf(". OK ? (^C if not)\n");
  hit_return();
}

static int
has_ext_help(void) { return (Help && *Help); }

static int
compare_str(char **s1, char **s2) { return strcmp(*s1, *s2); }

/* Print all elements of list in columns, pausing every nbli lines
 * if nbli is non-zero.
 * list is a NULL terminated list of function names
 */
void
print_fun_list(char **list, long nbli)
{
  long i=0, j=0, maxlen=0, nbcol,len, w = term_width();
  char **l;

  while (list[i]) i++;
  qsort (list, i, sizeof(char *), (QSCOMP)compare_str);

  for (l=list; *l; l++)
  {
    len = strlen(*l);
    if (len > maxlen) maxlen=len;
  }
  maxlen++; nbcol= w / maxlen;
  if (nbcol * maxlen == w) nbcol--;
  if (!nbcol) nbcol = 1;

  pari_putc('\n'); i=0;
  for (l=list; *l; l++)
  {
    pari_puts(*l); i++;
    if (i >= nbcol)
    {
      i=0; pari_putc('\n');
      if (nbli && j++ > nbli) { j = 0; hit_return(); }
      continue;
    }
    len = maxlen - strlen(*l);
    while (len--) pari_putc(' ');
  }
  if (i) pari_putc('\n');
}

static void
commands(long n)
{
  long i;
  entree *ep;
  char **t_L;
  pari_stack s_L;

  stack_init(&s_L, sizeof(*t_L), (void**)&t_L);
  for (i = 0; i < functions_tblsz; i++)
    for (ep = functions_hash[i]; ep; ep = ep->next)
    {
      long m;
      switch (EpVALENCE(ep))
      {
        case EpVAR:
          if (typ(ep->value) == t_CLOSURE) break;
          /* fall through */
        case EpNEW: continue;
      }
      m = ep->menu;
      if ((n < 0 && m && m < 13) || m == n) stack_pushp(&s_L, (void*)ep->name);
    }
  stack_pushp(&s_L, NULL);
  print_fun_list(t_L, term_height()-4);
  stack_delete(&s_L);
}

static void
center(const char *s)
{
  long i, l = strlen(s), pad = term_width() - l;
  char *buf, *u;

  if (pad<0) pad=0; else pad >>= 1;
  u = buf = (char*)pari_malloc(l + pad + 2);
  for (i=0; i<pad; i++) *u++ = ' ';
  while (*s) *u++ = *s++;
  *u++ = '\n'; *u = 0;
  pari_puts(buf); pari_free(buf);
}

static void
usage(char *s)
{
  printf("### Usage: %s [options] [GP files]\n", s);
  printf("Options are:\n");
  printf("\t[-f,--fast]\tFaststart: do not read .gprc\n");
  printf("\t[-q,--quiet]\tQuiet mode: do not print banner and history numbers\n");
  printf("\t[-p,--primelimit limit]\n\t\t\tPrecalculate primes up to 'limit'\n");
  printf("\t[-s,--stacksize stacksize]\n\t\t\tStart with the PARI stack of given size (in bytes)\n");
  printf("\t[--emacs]\tRun as if in Emacs shell\n");
  printf("\t[--help]\tPrint this message\n");
  printf("\t[--test]\tTest mode. No history, wrap long lines (bench only)\n");
  printf("\t[--texmacs]\tRun as if using TeXmacs frontend\n");
  printf("\t[--version]\tOutput version info and exit\n");
  printf("\t[--version-short]\tOutput version number and exit\n\n");
  exit(0);
}

static void
community(void)
{
  pari_sp av = avma;
  char *s = stackmalloc(strlen(pari_datadir) + 1024);

  (void)sprintf(s, "The standard distribution of GP/PARI includes a \
reference manual, a tutorial, a reference card and quite a few examples. They \
should have been installed in the directory '%s'. If not, ask the person \
who installed PARI on your system where they can be found. You can also \
download them from the PARI WWW site 'http://pari.math.u-bordeaux.fr/'."
                 , pari_datadir);
  print_text(s); avma = av;

  pari_puts("\nThree mailing lists are devoted to PARI:\n\
  - pari-announce (moderated) to announce major version changes.\n\
  - pari-dev for everything related to the development of PARI, including\n\
    suggestions, technical questions, bug reports and patch submissions.\n\
  - pari-users for everything else!\n");
  print_text("\
To subscribe, send an empty message to <listname>-request@pari.math.u-bordeaux.fr, \
with a Subject: field containing the word \"subscribe\".  \
An archive is kept at the WWW site mentioned above. You can also reach the \
authors directly by email: pari@math.u-bordeaux.fr (answer not guaranteed)."); }

static void
gentypes(void)
{
  pari_puts("List of the PARI types:\n\
  t_INT    : long integers     [ cod1 ] [ cod2 ] [ man_1 ] ... [ man_k ]\n\
  t_REAL   : long real numbers [ cod1 ] [ cod2 ] [ man_1 ] ... [ man_k ]\n\
  t_INTMOD : integermods       [ code ] [ mod  ] [ integer ]\n\
  t_FRAC   : irred. rationals  [ code ] [ num. ] [ den. ]\n\
  t_FFELT  : finite field elt. [ code ] [ cod2 ] [ elt ] [ mod ] [ p ]\n\
  t_COMPLEX: complex numbers   [ code ] [ real ] [ imag ]\n\
  t_PADIC  : p-adic numbers    [ cod1 ] [ cod2 ] [ p ] [ p^r ] [ int ]\n\
  t_QUAD   : quadratic numbers [ cod1 ] [ mod  ] [ real ] [ imag ]\n\
  t_POLMOD : poly mod          [ code ] [ mod  ] [ polynomial ]\n\
  -------------------------------------------------------------\n\
  t_POL    : polynomials       [ cod1 ] [ cod2 ] [ man_1 ] ... [ man_k ]\n\
  t_SER    : power series      [ cod1 ] [ cod2 ] [ man_1 ] ... [ man_k ]\n\
  t_RFRAC  : irred. rat. func. [ code ] [ num. ] [ den. ]\n\
  t_QFR    : real qfb          [ code ] [ a ] [ b ] [ c ] [ del ]\n\
  t_QFI    : imaginary qfb     [ code ] [ a ] [ b ] [ c ]\n\
  t_VEC    : row vector        [ code ] [  x_1  ] ... [  x_k  ]\n\
  t_COL    : column vector     [ code ] [  x_1  ] ... [  x_k  ]\n\
  t_MAT    : matrix            [ code ] [ col_1 ] ... [ col_k ]\n\
  t_LIST   : list              [ code ] [ n ] [ nmax ][ vec ]\n\
  t_STR    : string            [ code ] [ man_1 ] ... [ man_k ]\n\
  t_VECSMALL: vec. small ints  [ code ] [ x_1 ] ... [ x_k ]\n\
  t_CLOSURE: functions [ code ] [ arity ] [ code ] [ operand ] [ data ] [ text ]\n\
\n");
}

static void
menu_commands(void)
{
  pari_puts("Help topics: for a list of relevant subtopics, type ?n for n in\n\
  0: user-defined functions (aliases, installed and user functions)\n\
  1: Standard monadic or dyadic OPERATORS\n\
  2: CONVERSIONS and similar elementary functions\n\
  3: TRANSCENDENTAL functions\n\
  4: NUMBER THEORETICAL functions\n\
  5: Functions related to ELLIPTIC CURVES\n\
  6: Functions related to general NUMBER FIELDS\n\
  7: POLYNOMIALS and power series\n\
  8: Vectors, matrices, LINEAR ALGEBRA and sets\n\
  9: SUMS, products, integrals and similar functions\n\
 10: GRAPHIC functions\n\
 11: PROGRAMMING under GP\n\
 12: The PARI community\n\
\n\
Also:\n\
  ? functionname (short on-line help)\n\
  ?\\             (keyboard shortcuts)\n\
  ?.             (member functions)\n");
  if (has_ext_help()) pari_puts("\
Extended help (if available):\n\
  ??             (opens the full user's manual in a dvi previewer)\n\
  ??  tutorial / refcard / libpari (tutorial/reference card/libpari manual)\n\
  ??  keyword    (long help text about \"keyword\" from the user's manual)\n\
  ??? keyword    (a propos: list of related functions).");
}

static void
slash_commands(void)
{
  pari_puts("#       : enable/disable timer\n\
##      : print time for last result\n\
\\\\      : comment up to end of line\n\
\\a {n}  : print result in raw format (readable by PARI)\n\
\\B {n}  : print result in beautified format\n\
\\c      : list all commands (same effect as ?*)\n\
\\d      : print all defaults\n\
\\e {n}  : enable/disable echo (set echo=n)\n\
\\g {n}  : set debugging level\n\
\\gf{n}  : set file debugging level\n\
\\gm{n}  : set memory debugging level\n\
\\h {m-n}: hashtable information\n\
\\l {f}  : enable/disable logfile (set logfile=f)\n\
\\m {n}  : print result in prettymatrix format\n\
\\o {n}  : change output method (0=raw, 1=prettymatrix, 2=prettyprint, 3=2-dim)\n\
\\p {n}  : change real precision\n\
\\ps{n}  : change series precision\n\
\\q      : quit completely this GP session\n\
\\r {f}  : read in a file\n\
\\s {n}  : print stack information\n\
\\t      : print the list of PARI types\n\
\\u      : print the list of user-defined functions\n\
\\v      : print current version of GP\n\
\\w {nf} : write to a file\n\
\\x {n}  : print complete inner structure of result\n\
\\y {n}  : disable/enable automatic simplification (set simplify=n)\n\
\n\
{f}=optional filename. {n}=optional integer\n");
}

static void
member_commands(void)
{
  pari_puts("\
Member functions, followed by relevant objects\n\n\
a1-a6, b2-b8, c4-c6 : coeff. of the curve.            ell\n\
area : area                                           ell\n\
bid  : big ideal                     bid,                           bnr\n\
bnf  : big number field                                        bnf, bnr\n\
clgp : class group                   bid,                      bnf, bnr\n\
cyc  : cyclic decomposition (SNF)    bid,       clgp,          bnf, bnr\n\
diff, codiff: different and codifferent                    nf, bnf, bnr\n\
disc : discriminant                                   ell, nf, bnf, bnr\n\
e, f : inertia/residue  degree            prid\n\
fu   : fundamental units                                       bnf, bnr\n\
gen  : generators                    bid, prid, clgp,          bnf, bnr\n\
index: index                                               nf, bnf, bnr\n\
j    : j-invariant                                    ell\n");
/* split: some compilers can't handle long constant strings */
  pari_puts("\
mod  : modulus                       bid,                           bnr\n\
nf   : number field                                        nf, bnf, bnr\n\
no   : number of elements            bid,       clgp,          bnf, bnr\n\
omega, eta: [w1,w2] and [eta1, eta2]                  ell\n\
p    : rational prime below prid          prid\n\
pol  : defining polynomial                                 nf, bnf, bnr\n\
reg  : regulator                                               bnf, bnr\n\
roots: roots                                          ell, nf, bnf, bnr\n\
sign,r1,r2 : signature                                     nf, bnf, bnr\n\
t2   : t2 matrix                                           nf, bnf, bnr\n\
tate : Tate's [u^2, u, q]                             ell\n\
tu   : torsion unit and its order                              bnf, bnr\n\
w    : Mestre's w                                     ell\n\
zk   : integral basis                                      nf, bnf, bnr\n\
zkst : structure of (Z_K/m)*         bid,                           bnr\n");
}

#define QUOTE "_QUOTE"
#define DOUBQUOTE "_DOUBQUOTE"
#define BACKQUOTE "_BACKQUOTE"

static char *
_cat(char *s, const char *t)
{
  *s = 0; strcat(s,t); return s + strlen(t);
}

static char *
filter_quotes(const char *s)
{
  int i, l = strlen(s);
  int quote = 0;
  int backquote = 0;
  int doubquote = 0;
  char *str, *t;

  for (i=0; i < l; i++)
    switch(s[i])
    {
      case '\'': quote++; break;
      case '`' : backquote++; break;
      case '"' : doubquote++;
    }
  str = (char*)pari_malloc(l + quote * (strlen(QUOTE)-1)
                          + doubquote * (strlen(DOUBQUOTE)-1)
                          + backquote * (strlen(BACKQUOTE)-1) + 1);
  t = str;
  for (i=0; i < l; i++)
    switch(s[i])
    {
      case '\'': t = _cat(t, QUOTE); break;
      case '`' : t = _cat(t, BACKQUOTE); break;
      case '"' : t = _cat(t, DOUBQUOTE); break;
      default: *t++ = s[i];
    }
  *t = 0; return str;
}

static int
nl_read(char *s) { size_t l = strlen(s); return s[l-1] == '\n'; }

#define nbof(a) sizeof(a) / sizeof(a[0])
/* query external help program for s. num < 0 [keyword] or chapter number */
static void
external_help(const char *s, int num)
{
  long nbli = term_height()-3, li = 0;
  char buf[256], ar[32], *str;
  const char *opt = "";
  char *t;
  pariFILE *z;
  FILE *f;

  if (!has_ext_help()) pari_err(talker,"no external help program");
  t = filter_quotes(s);
  str = (char*)pari_malloc(strlen(Help) + strlen(t) + 64);
  *ar = 0;
  if (num < 0)
    opt = "-k";
  else if (t[strlen(t)-1] != '@')
    sprintf(ar,"@%d",num);
  sprintf(str,"%s -fromgp %s %c%s%s%c",Help,opt, SHELL_Q,t,ar,SHELL_Q);
  z = try_pipe(str,0); f = z->file;
  pari_free(str);
  pari_free(t);
  while (fgets(buf, nbof(buf), f))
  {
    if (!strncmp("ugly_kludge_done",buf,16)) break;
    pari_puts(buf);
    if (nl_read(buf) && ++li > nbli) { hit_return(); li = 0; }
  }
  pari_fclose(z);
}

const char *keyword_list[]={
  "operator",
  "libpari",
  "member",
  "integer",
  "real",
  "readline",
  "refcard",
  "tutorial",
  "nf",
  "bnf",
  "bnr",
  "ell",
  "rnf",
  "bid",
  "modulus",
  NULL
};

static int
ok_external_help(char **s)
{
  long n;
  if (!**s) return 1;
  if (!isalpha((int)**s)) return 3; /* operator or section number */
  if (!strncmp(*s,"t_",2)) { *s += 2; return 2; } /* type name */

  for (n=0; keyword_list[n]; n++)
    if (!strcmp(*s,keyword_list[n])) return 3;
  return 0;
}

static void
cut_trailing_garbage(char *s)
{
  char c;
  while ( (c = *s++) )
  {
    if (c == '\\' && ! *s++) return; /* gobble next char, return if none. */
    else
      if (!is_keyword_char(c) && c != '@') { s[-1] = 0; return; }
  }
}

/* don't mess readline display */
static void
aide_print(const char *s1, const char *s2) { pari_printf("%s: %s\n", s1, s2); }

static void
aide0(const char *s0, int flag)
{
  long n, long_help = flag & h_LONG;
  entree *ep,*ep1;
  char *s;

  s = get_sep(s0);
  if (isdigit((int)*s))
  {
    n = atoi(s);
    if (n < 0 || n > 15) pari_err(syntaxer,"no such section in help: ?",s,s);
    if (n == 12)
      community();
    else if (long_help)
      external_help(s,3);
    else
      commands(n);
    return;
  }
  /* Get meaningful answer on '\ps 5' (e.g. from <F1>) */
  if (*s == '\\') { char *t = s+1; skip_alpha(t); *t = '\0'; }
  if (isalpha((int)*s)) cut_trailing_garbage(s);

  if (flag & h_APROPOS) { external_help(s,-1); return; }
  if (long_help && (n = ok_external_help(&s))) { external_help(s,n); return; }
  switch (*s)
  {
    case '*' : commands(-1); return;
    case '\0': menu_commands(); return;
    case '\\': slash_commands(); return;
    case '.' : member_commands(); return;
  }
  ep = is_entry(s);
  if (ep && long_help)
  {
    if (!strcmp(ep->name, "default"))
    {
      char *t = s+7, *e;
      skip_space(t);
      if (*t == '(') {
        t++; skip_space(t);
        e = t; skip_alpha(e); *e = '\0'; /* safe: get_sep() made it a copy */
        if (pari_is_default(t)) { external_help(t, 2); return; }
      }
    }
  }
  if (!ep)
  {
    if (long_help)
      external_help(s,3);
    else
    {
      if (pari_is_default(s))
        aide_print(s,"default");
      else if (!cb_pari_whatnow(pariOut, s,1))
        aide_print(s,"unknown identifier");
    }
    return;
  }

  ep1 = ep;  ep = do_alias(ep); s0 = s;
  if (ep1 != ep) { pari_printf("%s is aliased to:\n\n",s0); s0 = ep->name; }

  switch(EpVALENCE(ep))
  {
    case EpVAR:
      if (typ(ep->value)==t_CLOSURE && typ(gel(ep->value,6))==t_VEC)
      {
        GEN str=gel(ep->value,6);
        if (!ep->help || long_help)
          pari_printf("%s(%s)=%s",ep->name,GSTR(gel(str,1)),GSTR(gel(str,2)));
        if (!ep->help) return;
        if (long_help) { pari_puts("\n\n"); long_help=0; }
      }
      else if (!ep->help) { aide_print(s, "user defined variable"); return; }
      long_help=0; break;

    case EpINSTALL:
      if (!ep->help) { aide_print(s, "installed function"); return; }
      long_help=0; break;

    case EpNEW:
      if (!ep->help) {
        aide_print(s, "new identifier (no valence assigned)"); return;
      };
      long_help=0; break;
  }
  if (long_help) { external_help(ep->name,3); return; }
  if (ep->help) { print_text(ep->help); return; }

  pari_err(bugparier,"aide (no help found)");
}

void
aide(const char *s, long flag)
{
  if ((flag & h_RL) == 0)
  {
    if (*s == '?') { flag |= h_LONG; s++; }
    if (*s == '?') { flag |= h_APROPOS; s++; }
  }
  term_color(c_HELP); aide0(s,flag); term_color(c_NONE);
  if ((flag & h_RL) == 0) pari_putc('\n');
}

/********************************************************************/
/**                                                                **/
/**                         GP HEADER                              **/
/**                                                                **/
/********************************************************************/
static char *
what_readline(void)
{
  char *s;
#ifdef READLINE
  const char *ver;
  char *extra = stackmalloc(strlen(READLINE) + 32);
#  if defined(HAS_RL_LIBRARY_VERSION) || defined(FAKE_RL_LIBRARY_VERSION)
#    ifdef FAKE_RL_LIBRARY_VERSION
  extern char *rl_library_version;
#    endif

  if (strcmp(READLINE, rl_library_version))
  {
    ver = (char*)rl_library_version;
    (void)sprintf(extra, " [was v%s in Configure]", READLINE);
  }
  else
#  endif
  {
    ver = READLINE;
    extra[0] = 0;
  }
  s = stackmalloc(3 + strlen(ver) + 8 + strlen(extra));
  (void)sprintf(s, "v%s %s%s", ver,
            (GP_DATA->use_readline)? "enabled": "disabled",
            extra);
#else
  s = (char*)"not compiled in";
#endif
  return s;
}

static void
print_shortversion(void)
{
  const ulong mask = (1UL<<PARI_VERSION_SHIFT) - 1;
  ulong n = paricfg_version_code, major, minor, patch;

  patch = n & mask; n >>= PARI_VERSION_SHIFT;
  minor = n & mask; n >>= PARI_VERSION_SHIFT;
  major = n;
  printf("%lu.%lu.%lu\n", major,minor,patch); exit(0);
}

static char *
what_cc(void)
{
  char *s;
#ifdef GCC_VERSION
#  ifdef __cplusplus
#    define Format "g++-%s"
#  else
#    define Format "gcc-%s"
#  endif
  s = stackmalloc(4 + strlen(GCC_VERSION) + 1);
  (void)sprintf(s, Format, GCC_VERSION);
#else
#  ifdef _MSC_VER
  s = stackmalloc(32);
  (void)sprintf(s, "MSVC-%i", _MSC_VER);
#  else
  s = NULL;
#  endif
#endif
  return s;
}

static void
print_version(void)
{
  pari_sp av = avma;
  char *buf, *ver = what_cc();

  center(paricfg_version);
  center(paricfg_buildinfo);
  buf = stackmalloc(strlen(__DATE__) +  32 + (ver? strlen(ver): 0));
  if (ver) (void)sprintf(buf, "compiled: %s, %s", __DATE__, ver);
  else     (void)sprintf(buf, "compiled: %s", __DATE__);
  center(buf);
  ver = what_readline();
  buf = stackmalloc(strlen(ver) + 64);
  (void)sprintf(buf, "(readline %s, extended help%s enabled)", ver,
                has_ext_help()? "": " not");
  center(buf); avma = av;
}

static void
gp_head(void)
{
#ifdef READLINE
  if (GP_DATA->flags & gpd_TEXMACS)
    printf("%ccommand:(cas-supports-completions-set! \"pari\")%c\n",
           DATA_BEGIN, DATA_END);
#endif
  print_version();
  pari_putc('\n');
  center("Copyright (C) 2000-2013 The PARI Group");
  pari_putc('\n');
  print_text("PARI/GP is free software, covered by the GNU General Public \
License, and comes WITHOUT ANY WARRANTY WHATSOEVER.");
  pari_puts("\nType ? for help, \\q to quit.\n");
  print_text("Type ?12 for how to get moral (and possibly technical) support.");
  pari_printf("\nparisize = %lu, primelimit = %lu\n", top - bot, maxprime());
}

/********************************************************************/
/**                                                                **/
/**                         METACOMMANDS                           **/
/**                                                                **/
/********************************************************************/
#define pariputs_opt(s) if (!(GP_DATA->flags & gpd_QUIET)) pari_puts(s)

void
gp_quit(long exitcode)
{
  if (Help) free((void*)Help);
  free_graph();
  pari_close();
  kill_buffers_upto(NULL);
  term_color(c_NONE);
  pariputs_opt("Goodbye!\n");
  if (GP_DATA->flags & gpd_TEXMACS) tm_end_output();
  exit(exitcode);
}

static GEN
gpreadbin(const char *s, int *vector)
{
  GEN x = readbin(s,pari_infile, vector);
  popinfile();
  if (!x) pari_err(openfiler,"input",s);
  return x;
}

static void
escape(char *tch, int ismain)
{
  const char *s;
  char c;

  if (compatible != NONE)
  {
    s = tch;
    while (*s)
      if (*s++ == '=')
      {
        GEN (*f)(const char *v, long flag) = NULL;
        long len = (s-tch) - 1;
        if      (!strncmp(tch,"precision",len))    f = sd_realprecision;
        else if (!strncmp(tch,"serieslength",len)) f = sd_seriesprecision;
        else if (!strncmp(tch,"format",len))       f = sd_format;
        else if (!strncmp(tch,"prompt",len))       f = sd_prompt;
        if (f) { (void)f(s, d_ACKNOWLEDGE); return; }
        break;
      }
  }
  s = tch;
  switch ((c = *s++))
  {
    case 'w': case 'x': case 'a': case 'b': case 'B': case 'm':
    { /* history things */
      long d;
      GEN x;
      if (c != 'w' && c != 'x') d = get_int(s,0);
      else
      {
        d = atol(s); if (*s == '-') s++;
        while (isdigit((int)*s)) s++;
      }
      x = gp_history(GP_DATA->hist, d, tch+1,tch-1);
      switch (c)
      {
        case 'B':
        { /* prettyprinter */
          gp_data G = *GP_DATA; /* copy */
          gp_hist   h = *(G.hist); /* copy */
          pariout_t f = *(G.fmt);  /* copy */

          G.hist = &h; h.total = 0; /* no hist number */
          G.fmt  = &f; f.prettyp = f_PRETTY;
          G.flags &= ~(gpd_TEST|gpd_TEXMACS);
          G.lim_lines = 0;
          gp_output(x, &G); break;
        }
        case 'a': brute   (x, GP_DATA->fmt->format, -1); break;
        case 'b': /* fall through */
        case 'm': matbrute(x, GP_DATA->fmt->format, -1); break;
        case 'x': dbgGEN(x, get_int(s, -1)); break;
        case 'w':
          s = get_sep(s); if (!*s) s = current_logfile;
          write0(s, mkvec(x)); return;
      }
      pari_putc('\n'); return;
    }

    case 'c': commands(-1); break;
    case 'd': (void)setdefault(NULL,NULL,d_SILENT); break;
    case 'e':
      s = get_sep(s);
      if (!*s) s = (GP_DATA->echo)? "0": "1";
      (void)sd_echo(s,d_ACKNOWLEDGE); break;
    case 'g':
      switch (*s)
      {
        case 'm': s++; (void)sd_debugmem(*s? s: NULL,d_ACKNOWLEDGE); break;
        case 'f': s++; (void)sd_debugfiles(*s? s: NULL,d_ACKNOWLEDGE); break;
        default : (void)sd_debug(*s? s: NULL,d_ACKNOWLEDGE); break;
      }
      break;
    case 'h': print_functions_hash(s); break;
    case 'l':
      s = get_sep(s);
      if (*s)
      {
        (void)sd_logfile(s,d_ACKNOWLEDGE);
        if (pari_logfile) break;
      }
      (void)sd_log(pari_logfile?"0":"1",d_ACKNOWLEDGE);
      break;
    case 'o': (void)sd_output(*s? s: NULL,d_ACKNOWLEDGE); break;
    case 'p':
      switch (*s)
      {
        case 's': s++;
          (void)sd_seriesprecision(*s? s: NULL,d_ACKNOWLEDGE); break;
        default :
          (void)sd_realprecision(*s? s: NULL,d_ACKNOWLEDGE); break;
      }
      break;
    case 'q': gp_quit(0); break;
    case 'r':
      s = get_sep(s);
      if (!ismain) { read0(s); break; }
      switchin(s);
      if (file_is_binary(pari_infile))
      {
        int vector;
        GEN x = gpreadbin(s, &vector);
        if (vector) /* many BIN_GEN */
        {
          long i, l = lg(x);
          pari_warn(warner,"setting %ld history entries", l-1);
          for (i=1; i<l; i++) (void)pari_add_hist(gel(x,i));
        }
      }
      break;
    case 's': dbg_pari_heap(); break;
    case 't': gentypes(); break;
    case 'u':
      print_all_user_fun((*s == 'm')? 1: 0);
      break;
    case 'v': print_version(); break;
    case 'y':
      s = get_sep(s);
      if (!*s) s = (GP_DATA->simplify)? "0": "1";
      (void)sd_simplify(s,d_ACKNOWLEDGE); break;
    default: pari_err(syntaxer,"unexpected character", tch,tch-1);
  }
}

/* Format a time of 'delay' ms */
static char *
gp_format_time(long delay)
{
  static char buf[64];
  char *s = buf;

  term_get_color(s, c_TIME); s+=strlen(s);
  if (delay >= 3600000)
  {
    sprintf(s, "%ldh, ", delay / 3600000); s+=strlen(s);
    delay %= 3600000;
  }
  if (delay >= 60000)
  {
    sprintf(s, "%ldmin, ", delay / 60000); s+=strlen(s);
    delay %= 60000;
  }
  if (delay >= 1000)
  {
    sprintf(s, "%ld,", delay / 1000); s+=strlen(s);
    delay %= 1000;
    if (delay < 100)
    {
      sprintf(s, "%s", (delay<10)? "00": "0");
      s+=strlen(s);
    }
  }
  sprintf(s, "%ld ms", delay); s+=strlen(s);
  term_get_color(s, c_NONE); s+=strlen(s);
  *s++ = '.'; *s++ = '\n'; *s = 0; return buf;
}

static int
chron(char *s)
{
  if (*s)
  { /* if "#" or "##" timer metacommand. Otherwise let the parser get it */
    if (*s == '#') s++;
    if (*s) return 0;
    pari_puts( "  ***   last result computed in " );
    pari_puts( gp_format_time(GP_DATA->last_time) );
  }
  else { GP_DATA->chrono ^= 1; (void)sd_timer(NULL,d_ACKNOWLEDGE); }
  return 1;
}

/* return 0: can't interpret *buf as a metacommand
 *        1: did interpret *buf as a metacommand or empty command */
static int
check_meta(char *buf, int ismain)
{
  switch(*buf++)
  {
    case '?': aide(buf, h_REGULAR); break;
    case '#': return chron(buf);
    case '\\': escape(buf, ismain); break;
    case '\0': break;
    default: return 0;
  }
  return 1;
}

/********************************************************************/
/*                                                                  */
/*                              GPRC                                */
/*                                                                  */
/********************************************************************/
/* LOCATE GPRC */

static int get_line_from_file(const char *prompt, filtre_t *F, FILE *file);
#define err_gprc(s,t,u) { err_printf("\n"); pari_err(syntaxer,s,t,u); }

/* return $HOME or the closest we can find */
static const char *
get_home(int *free_it)
{
  char *drv, *pth = os_getenv("HOME");
  if (pth) return pth;
  if ((drv = os_getenv("HOMEDRIVE"))
   && (pth = os_getenv("HOMEPATH")))
  { /* looks like WinNT */
    char *buf = (char*)pari_malloc(strlen(pth) + strlen(drv) + 1);
    sprintf(buf, "%s%s",drv,pth);
    *free_it = 1; return buf;
  }
  pth = pari_get_homedir("");
  return pth? pth: ".";
}

static FILE *
gprc_chk(const char *s)
{
  FILE *f = fopen(s, "r");
  if (f && !(GP_DATA->flags & gpd_QUIET)) err_printf("Reading GPRC: %s ...", s);
  return f;
}

/* Look for [._]gprc: $GPRC, then in $HOME, ., /etc, path [ to gp binary ] */
static FILE *
gprc_get(char *path)
{
  FILE *f = NULL;
  const char *gprc = os_getenv("GPRC");
  if (gprc) f = gprc_chk(gprc);
  if (!f)
  {
    int free_it = 0;
    const char *home = get_home(&free_it);
    char *str, *s, c;
    long l;
    l = strlen(home); c = home[l-1];
    str = strcpy((char*)pari_malloc(l+7), home);
    if (free_it) pari_free((void*)home);
    s = str + l;
    if (c != '/' && c != '\\') *s++ = '/';
#ifdef UNIX
    *s = '.'; /* .gprc */
#else
    *s = '_'; /* _gprc */
#endif
    strcpy(s+1, "gprc");
    f = gprc_chk(str); /* in $HOME */
    if (!f) f = gprc_chk(s); /* in . */
    if (!f) f = gprc_chk("/etc/gprc");
    if (!f) f = gprc_chk("C:/_gprc");
    if (!f)
    { /* in 'gp' directory */
      char *t = path + strlen(path);
      while (t > path && *t != '/') t--;
      if (*t == '/')
      {
        long l = t - path + 1;
        t = (char*)pari_malloc(l + 6);
        strncpy(t, path, l);
        strcpy(t+l, s); f = gprc_chk(t);
        pari_free(t);
      }
    }
    pari_free(str);
  }
  return f;
}

/* PREPROCESSOR */

static ulong
read_uint(char **s)
{
  long v = atol(*s);
  if (!isdigit((int)**s)) err_gprc("not an integer", *s, *s);
  while (isdigit((int)**s)) (*s)++;
  return v;
}
static ulong
read_dot_uint(char **s)
{
  if (**s != '.') return 0;
  (*s)++; return read_uint(s);
}
/* read a.b.c */
static long
read_version(char **s)
{
  long a, b, c;
  a = read_uint(s);
  b = read_dot_uint(s);
  c = read_dot_uint(s);
  return PARI_VERSION(a,b,c);
}

static int
get_preproc_value(char **s)
{
  if (!strncmp(*s,"EMACS",5)) {
    *s += 5;
    return GP_DATA->flags & (gpd_EMACS|gpd_TEXMACS);
  }
  if (!strncmp(*s,"READL",5)) {
    *s += 5;
    return GP_DATA->use_readline;
  }
  if (!strncmp(*s,"VERSION",7)) {
    int less = 0, orequal = 0;
    long d;
    *s += 7;
    switch(**s)
    {
      case '<': (*s)++; less = 1; break;
      case '>': (*s)++; less = 0; break;
      default: return -1;
    }
    if (**s == '=') { (*s)++; orequal = 1; }
    d = paricfg_version_code - read_version(s);
    if (!d) return orequal;
    return less? (d < 0): (d > 0);
  }
  return -1;
}

/* PARSE GPRC */

/* 1) replace next separator by '\0' (t must be writeable)
 * 2) return the next expression ("" if none)
 * see get_sep() */
static char *
next_expr(char *t)
{
  int outer = 1;
  char *s = t;

  for(;;)
  {
    char c;
    switch ((c = *s++))
    {
      case '"':
        if (outer || (s >= t+2 && s[-2] != '\\')) outer = !outer;
        break;
      case '\0':
        return (char*)"";
      default:
        if (outer && c == ';') { s[-1] = 0; return s; }
    }
  }
}

static Buffer *
filtered_buffer(filtre_t *F)
{
  Buffer *b = new_buffer();
  init_filtre(F, b);
  stack_pushp(&s_bufstack, (void*)b);
  return b;
}

static jmp_buf *env;
static pari_stack s_env;

static void
gp_initrc(pari_stack *p_A, char *path)
{
  char *nexts,*s,*t;
  FILE *file = gprc_get(path);
  Buffer *b;
  filtre_t F;
  VOLATILE long c = 0;

  if (!file) return;
  b = filtered_buffer(&F);
  (void)stack_new(&s_env);
  for(;;)
  {
    if (setjmp(env[s_env.n-1])) err_printf("...skipping line %ld.\n", c);
    c++;
    if (!get_line_from_file(NULL,&F,file)) break;
    s = b->buf;
    if (*s == '#')
    { /* preprocessor directive */
      int z, NOT = 0;
      s++;
      if (strncmp(s,"if",2)) err_gprc("unknown directive",s,b->buf);
      s += 2;
      if (!strncmp(s,"not",3)) { NOT = !NOT; s += 3; }
      if (*s == '!')           { NOT = !NOT; s++; }
      t = s;
      z = get_preproc_value(&s);
      if (z < 0) err_gprc("unknown preprocessor variable",t,b->buf);
      if (NOT) z = !z;
      if (!*s)
      { /* make sure at least an expr follows the directive */
        if (!get_line_from_file(NULL,&F,file)) break;
        s = b->buf;
      }
      if (!z) continue; /* dump current line */
    }
    /* parse line */
    for ( ; *s; s = nexts)
    {
      nexts = next_expr(s);
      if (!strncmp(s,"read",4) && (s[4] == ' ' || s[4] == '\t' || s[4] == '"'))
      { /* read file */
        s += 4;
        t = (char*)pari_malloc(strlen(s) + 1);
        if (*s == '"') (void)readstring(s, t); else strcpy(t,s);
        stack_pushp(p_A,t);
      }
      else
      { /* set default */
        t = s; while (*t && *t != '=') t++;
        if (*t != '=') err_gprc("missing '='",t,b->buf);
        *t++ = 0;
        if (*t == '"') (void)readstring(t, t);
        (void)setdefault(s,t,d_INITRC);
      }
    }
  }
  s_env.n--;
  pop_buffer();
  if (!(GP_DATA->flags & gpd_QUIET)) err_printf("Done.\n\n");
  fclose(file);
}

/********************************************************************/
/*                                                                  */
/*                             PROMPTS                              */
/*                                                                  */
/********************************************************************/
static int gp_is_interactive = 0;
static const char *DFT_PROMPT = "? ";
static const char *CONTPROMPT = "";
static const char *COMMENTPROMPT = "comment> ";
static const char *DFT_INPROMPT = "";

static char Prompt[MAX_PROMPT_LEN], Prompt_cont[MAX_PROMPT_LEN];

/* if prompt is coloured, we must tell readline to ignore the
 * corresponding ANSI escape sequences */
static void
brace_color(char *s, int c, int force)
{
  if (disable_color || (gp_colors[c] == c_NONE && !force)) return;
#ifdef RL_PROMPT_START_IGNORE
  if (GP_DATA->use_readline)
    *s++ = RL_PROMPT_START_IGNORE;
#endif
  term_get_color(s, c);
#ifdef RL_PROMPT_START_IGNORE
  if (GP_DATA->use_readline)
  {
    s+=strlen(s);
    *s++ = RL_PROMPT_END_IGNORE;
    *s = 0;
  }
#endif
}

static void
color_prompt(char *buf, const char *prompt)
{
  char *s = buf;
  *s = 0;
  /* escape sequences bug readline, so use special bracing (if available) */
  brace_color(s, c_PROMPT, 0);
  s += strlen(s); strcpy(s, prompt);
  s += strlen(s);
  brace_color(s, c_INPUT, 1);
}

static const char *
expand_prompt(char *buf, const char *prompt, filtre_t *F)
{
  if (F && F->in_comment) return COMMENTPROMPT;
  strftime_expand(prompt, buf, MAX_PROMPT_LEN-1);
  return buf;
}

const char *
do_prompt(char *buf, const char *prompt, filtre_t *F)
{
  if (GP_DATA->flags & gpd_TEST)
    strcpy(buf, prompt);
  else
  {
    char b[MAX_PROMPT_LEN];
    const char *s = expand_prompt(b, prompt, F);
    color_prompt(buf, s);
  }
  return buf;
}

/********************************************************************/
/*                                                                  */
/*                           GP MAIN LOOP                           */
/*                                                                  */
/********************************************************************/
static void
update_logfile(const char *prompt, const char *s)
{
  if (!pari_logfile) return;
  switch (logstyle) {
    case logstyle_TeX:
      fprintf(pari_logfile,
              "\\PARIpromptSTART|%s\\PARIpromptEND|%s\\PARIinputEND|%%\n",
              prompt,s);
    break;
    case logstyle_plain:
      fprintf(pari_logfile,"%s%s\n",prompt,s);
    break;
    case logstyle_color: {
      pari_sp av = avma;
      fprintf(pari_logfile,"%s%s%s%s%s\n",term_get_color(NULL,c_PROMPT), prompt,
                                          term_get_color(NULL,c_INPUT), s,
                                          term_get_color(NULL,c_NONE));
      avma = av; break;
    }
  }
}

void
echo_and_log(const char *prompt, const char *s)
{
  if (GP_DATA->echo) { pari_puts(prompt); pari_puts(s); pari_putc('\n'); }
  else update_logfile(prompt, s);
  pari_flush();
}

/* prompt = NULL --> from gprc. Return 1 if new input, and 0 if EOF */
static int
get_line_from_file(const char *prompt, filtre_t *F, FILE *file)
{
  const int Texmacs_stdin = ((GP_DATA->flags & gpd_TEXMACS) && file == stdin);
  char *s;
  input_method IM;

  IM.file = file;
  IM.fgets= Texmacs_stdin? &fgets_texmacs: &fgets;
  IM.getline = &file_input;
  IM.free = 0;
  if (! input_loop(F,&IM))
  {
    if (Texmacs_stdin) tm_start_output();
    return 0;
  }

  s = ((Buffer*)F->buf)->buf;
  /* don't log if from gprc or empty input */
  if (*s && prompt) echo_and_log(prompt, s);
  if (GP_DATA->flags & gpd_TEXMACS)
  {
    tm_did_complete = 0;
    if (Texmacs_stdin && *s == DATA_BEGIN)
    { handle_texmacs_command(s); *s = 0; }
    else
      tm_start_output();
  }
  return 1;
}

static int
is_interactive(void)
{
  ulong f = GP_DATA->flags&(gpd_TEXMACS|gpd_TEST);
  return pari_infile == stdin && !f && gp_is_interactive;
}

/* return 0 if no line could be read (EOF). If PROMPT = NULL, expand and
 * color default prompt; otherwise, use PROMPT as-is. */
static int
gp_read_line(filtre_t *F, const char *PROMPT)
{
  Buffer *b = (Buffer*)F->buf;
  char buf[MAX_PROMPT_LEN + 24];
  const char *p;
  int res, interactive;
  disable_exception_handler = 1;
  F->downcase = (compatible == OLDALL);
  if (b->len > 100000) fix_buffer(b, 100000);
  interactive = is_interactive();
  if (interactive || pari_logfile || GP_DATA->echo)
    p = PROMPT? PROMPT: do_prompt(buf, Prompt, F);
  else
    p = DFT_PROMPT;

  if (interactive)
  {
#ifdef READLINE
    if (GP_DATA->use_readline)
    {
      res = get_line_from_readline(p, Prompt_cont, F);
      goto END;
    }
#endif
    pari_puts(p); pari_flush();
  }
  res = get_line_from_file(p, F, pari_infile);

#ifdef READLINE
END:
#endif
  if (!disable_color) { term_color(c_NONE); pari_flush(); }
  disable_exception_handler = 0;
  return res;
}

/* kill all history entries since loc */
static void
prune_history(gp_hist *H, long loc)
{
  long i, j;
  i = (H->total-1) % H->size;
  j = H->total - loc;
  for ( ; j > 0; i--,j--)
  {
    if (H->res[i])
    {
      gunclone(H->res[i]);
      H->res[i] = NULL;
    }
    if (!i) i = H->size;
  }
  H->total = loc;
}

static int
is_silent(char *s) { return s[strlen(s) - 1] == ';'; }

enum { gp_ISMAIN = 1, gp_RECOVER = 2 };

static GEN
gp_main_loop(long flag)
{
  VOLATILE const long dorecover = flag & gp_RECOVER;
  VOLATILE const long ismain    = flag & gp_ISMAIN;
  VOLATILE GEN z = gnil;
  VOLATILE pari_sp av = avma;
  filtre_t F;
  Buffer *b = filtered_buffer(&F);
  struct gp_context rec;
  for(;;)
  {
    if (dorecover)
    { /* set a recovery point */
      static long tloc, outtyp;
      long er;
      outtyp = GP_DATA->fmt->prettyp;
      tloc = pari_nb_hist(); gp_context_save(&rec);
      /* recover: jump from error [ > 0 ] or allocatemem [ -1 ] */
      if ((er = setjmp(env[s_env.n-1])))
      {
        if (er > 0) { /* true error */
          if (!(GP_DATA->recover)) exit(1);
          gp_context_restore(&rec);
          /* true error not from main instance, let caller sort it out */
          if (!ismain) { kill_buffers_upto_including(b); return NULL; }
          GP_DATA->fmt->prettyp = outtyp;
          prune_history(GP_DATA->hist, tloc);
        } else { /* allocatemem */
          filestate_restore(rec.file);
          gp_context_save(&rec);
        }
        avma = av = top;
        kill_buffers_upto(b);
      }
    }

    if (! gp_read_line(&F, NULL))
    {
      if (popinfile()) gp_quit(0);
      if (ismain) continue;
      pop_buffer(); return z;
    }
    if (check_meta(b->buf, ismain)) continue;

    avma = av;
    if (ismain)
    {
#if defined(_WIN32) || defined(__CYGWIN32__)
      win32ctrlc = 0;
#endif
      timer_start(GP_DATA->T);
      pari_set_last_newline(1);
    }
    z = closure_evalres(pari_compile_str(b->buf, GP_DATA->strictmatch));
    if (! ismain) continue;
    alarm0(0);

    if (!pari_last_was_newline()) pari_putc('\n');

    GP_DATA->last_time = timer_delay(GP_DATA->T);
    if (GP_DATA->chrono)
    {
      pari_puts( "time = " );
      pari_puts( gp_format_time(GP_DATA->last_time) );
    }
    if (z == gnil) continue;

    if (GP_DATA->simplify) z = simplify_shallow(z);
    z = pari_add_hist(z);
    if (! is_silent(b->buf) ) gp_output(z, GP_DATA);
  }
}

/********************************************************************/
/*                                                                  */
/*                      EXCEPTION HANDLER                           */
/*                                                                  */
/********************************************************************/
static void
gp_sigint_fun(void) {
  if (GP_DATA->flags & gpd_TEXMACS) tm_start_output();
  pari_sigint( gp_format_time(timer_get(GP_DATA->T)) );
}

#ifdef SIGALRM
static void
gp_alarm_fun(void) {
  if (GP_DATA->flags & gpd_TEXMACS) tm_start_output();
  pari_err(alarmer, gp_format_time(timer_get(GP_DATA->T)));
}
#endif /* SIGALRM */

static const char *
break_loop_prompt(char *buf, long n)
{
  char s[128];
  if (n == 1)
    strcpy(s, "break> ");
  else
    sprintf(s, "break[%ld]> ", n);
  return do_prompt(buf, s, NULL);
}

static long frame_level=0;

static int
break_loop(int numerr)
{
  filtre_t F;
  Buffer *b;
  int sigint = numerr<0, go_on = sigint;
  struct gp_context rec;
  const char *prompt;
  char promptbuf[MAX_PROMPT_LEN + 24];
  long nenv, oldframe_level = frame_level;
  pari_sp av;

  if (numerr == syntaxer) return 0;
  if (numerr == errpile) { evalstate_clone(); avma = top; }

  b = filtered_buffer(&F);
  nenv=stack_new(&s_env);
  gp_context_save(&rec);
  frame_level = closure_context(oldframe_level);
  pari_infile = newfile(stdin, "stdin", mf_IN)->file;
  term_color(c_ERR); pari_putc('\n');
  if (sigint)
    print_errcontext(pariOut, "Break loop: type <Return> to continue; 'break' to go back to GP", NULL, NULL);
  else
    print_errcontext(pariOut, "Break loop: type 'break' to go back to GP", NULL, NULL);
  term_color(c_NONE);
  prompt = break_loop_prompt(promptbuf, s_env.n-1);
  av = avma;
  for(;;)
  {
    GEN x;
    long er, br_status;
    avma = av;
    if ((er=setjmp(env[nenv])))
    {
      if (er<0) { s_env.n=1; longjmp(env[s_env.n-1], er); }
      gp_context_restore(&rec);
      closure_err();
      frame_level = closure_context(oldframe_level);
      pari_infile = newfile(stdin, "stdin", mf_IN)->file;
    }
    term_color(c_NONE);
    if (gp_read_line(&F, prompt))
    {
      /* Empty input --> continue computation if break loop initiated
       * by ^C (will continue) */
      if (! *(b->buf) && sigint) break;
#if defined(_WIN32) || defined(__CYGWIN32__)
      win32ctrlc = 0;
#endif
      if (check_meta(b->buf, 0)) continue;
      x = closure_evalbrk(pari_compile_str(b->buf,0), &br_status);
      if (br_status) goto GP_EOF;

      if (x == gnil || is_silent(b->buf)) continue;

      term_color(c_OUTPUT);
      gen_output(x, GP_DATA->fmt);
      pari_putc('\n'); continue;
    }

    /* EOF or break/next/return */
GP_EOF:
    if (pari_infile != stdin)
    { /* were reading a file from the break loop, and are done : close it */
      if (popinfile()) { go_on = 0; break; /* should not happen */ }
    }
    else
    { /* user typed <C-D> in break loop : exit the debuger */
      go_on = 0; break;
    }
  }
  s_env.n=nenv;
  frame_level = oldframe_level;
  gp_context_restore(&rec);
  pop_buffer(); return go_on;
}

/* numerr < 0: from SIGINT */
static void
gp_err_recover(long numerr)
{
  longjmp(env[s_env.n-1], numerr);
}

/* numerr < 0: from SIGINT */
static int
gp_handle_exception(long numerr)
{
  if (disable_exception_handler) disable_exception_handler = 0;
  else if ((GP_DATA->breakloop) && break_loop(numerr)) return 1;
  if (s_env.n>=1) {
    err_printf("\n"); err_flush();
    gp_err_recover(numerr>=0? numerr: talker);
  }
  return 0;
}

#ifdef SIGALRM
static void
gp_alarm_handler(int sig)
{
#ifndef HAS_SIGACTION
  /*SYSV reset the signal handler in the handler*/
  (void)os_signal(sig,gp_alarm_handler);
#endif
  if (PARI_SIGINT_block) PARI_SIGINT_pending=sig;
  else gp_alarm_fun();
  return;
}
#endif /* SIGALRM */

/********************************************************************/
/*                                                                  */
/*                      GP-SPECIFIC ROUTINES                        */
/*                                                                  */
/********************************************************************/
static void
check_secure(const char *s)
{
  if (GP_DATA->secure)
    pari_err(talker, "[secure mode]: system commands not allowed\nTried to run '%s'",s);
}

GEN
read0(const char *s)
{
  switchin(s);
  if (file_is_binary(pari_infile)) return gpreadbin(s, NULL);
  return gp_main_loop(0);
}
/* as read0 but without a main instance of gp running */
static void
read_main(const char *s)
{
  GEN z;
  if (setjmp(env[s_env.n-1]))
    z = NULL;
  else {
    switchin(s);
    if (file_is_binary(pari_infile)) {
      z = readbin(s,pari_infile, NULL);
      popinfile();
    }
    else z = gp_main_loop(gp_RECOVER);
  }
  if (!z) err_printf("... skipping file '%s'\n", s);
  avma = top;
}

GEN
externstr(const char *s)
{
  pari_sp av = avma;
  long i, nz = 16;
  GEN z = cgetg(nz + 1, t_VEC);
  pariFILE *F;
  Buffer *b;
  input_method IM;

  check_secure(s);
  F = try_pipe(s, mf_IN);
  b = new_buffer();
  IM.fgets = &fgets;
  IM.file = F->file;
  for(i = 1;;)
  {
    char *s = b->buf, *e;
    if (!file_getline(b, &s, &IM)) break;
    if (i > nz) { nz <<= 1; z = vec_lengthen(z, nz); }
    e = s + strlen(s)-1;
    if (*e == '\n') *e = 0;
    gel(z,i++) = strtoGENstr(s);
  }
  delete_buffer(b);
  pari_fclose(F);
  setlg(z, i); return gerepilecopy(av, z);
}

GEN
extern0(const char *s)
{
  check_secure(s);
  pari_infile = try_pipe(s, mf_IN)->file;
  return gp_main_loop(0);
}

GEN
input0(void)
{
  filtre_t F;
  Buffer *b = filtered_buffer(&F);
  GEN x;

  while (! get_line_from_file(DFT_INPROMPT,&F,pari_infile))
    if (popinfile()) { err_printf("no input ???"); gp_quit(1); }
  x = readseq(b->buf);
  pop_buffer(); return x;
}

void
system0(const char *s)
{
/*FIXME: HAS_SYSTEM */
#if defined(UNIX) || defined(__EMX__) || defined(_WIN32)
  check_secure(s);
  if (system(s) < 0)
    pari_err(talker, "system(\"%s\") failed", s);
#else
  pari_err(archer);
#endif
}

void
alarm0(long s)
{
  if (s < 0) pari_err(talker,"delay must be non-negative");
#ifdef HAS_ALARM
  alarm(s);
#else
  if (s) pari_err(archer,"alarm");
#endif
}

/*******************************************************************/
/**                                                               **/
/**                        INITIALIZATION                         **/
/**                                                               **/
/*******************************************************************/
static char *
read_arg(long *nread, char *t, long argc, char **argv)
{
  long i = *nread;
  if (isdigit((int)*t)) return t;
  if (*t || i==argc) usage(argv[0]);
  *nread = i+1; return argv[i];
}

static char *
read_arg_equal(long *nread, char *t, long argc, char **argv)
{
  long i = *nread;
  if (*t=='=' && isdigit((int)t[1])) return t+1;
  if (*t || i==argc) usage(argv[0]);
  *nread = i+1; return argv[i];
}

static void
init_trivial_stack(void)
{
  const size_t s = 2048;
  bot = (pari_sp)pari_malloc(s);
  avma = top = bot + s;
}

static void
read_opt(pari_stack *p_A, long argc, char **argv)
{
  char *b = NULL, *p = NULL, *s = NULL;
  ulong f = GP_DATA->flags;
  long i = 1, initrc = 1;

  (void)&p; (void)&b; (void)&s; /* -Wall gcc-2.95 */

  pari_outfile = stderr;
  while (i < argc)
  {
    char *t = argv[i];

    if (*t++ != '-') break;
    i++;
    switch(*t++)
    {
      case 'b': b = read_arg(&i,t,argc,argv);
        pari_warn(warner, "buffersize is no longer used. -b ignored");
        break;
      case 'p': p = read_arg(&i,t,argc,argv); break;
      case 's': s = read_arg(&i,t,argc,argv); break;

      case 'e':
        if (strncmp(t,"macs",4)) usage(argv[0]); /* obsolete */
        f |= gpd_EMACS; break;
      case 'q':
        f |= gpd_QUIET; break;
      case 't':
        if (strncmp(t,"est",3)) usage(argv[0]); /* obsolete */
        f |= gpd_TEST; break;
      case 'f':
        initrc = 0; break;
      case '-':
        if (strcmp(t, "version-short") == 0) { print_shortversion(); exit(0); }
        if (strcmp(t, "version") == 0) {
          init_trivial_stack(); print_version();
          pari_free((void*)bot); exit(0);
        }
        if (strcmp(t, "texmacs") == 0) { f |= gpd_TEXMACS; break; }
        if (strcmp(t, "emacs") == 0) { f |= gpd_EMACS; break; }
        if (strcmp(t, "test") == 0) { f |= gpd_TEST; break; }
        if (strcmp(t, "quiet") == 0) { f |= gpd_QUIET; break; }
        if (strcmp(t, "fast") == 0) { initrc = 0; break; }
        if (strncmp(t, "primelimit",10) == 0) {p = read_arg_equal(&i,t+10,argc,argv); break; }
        if (strncmp(t, "stacksize",9) == 0) {s = read_arg_equal(&i,t+9,argc,argv); break; }
       /* fall through */
      default:
        usage(argv[0]);
    }
  }
#ifdef READLINE
  GP_DATA->use_readline = gp_is_interactive;
#else
  GP_DATA->use_readline = 0;
#endif
  if (!gp_is_interactive && !(GP_DATA->flags & gpd_EMACS))
    GP_DATA->breakloop = 0;
  if (f & gpd_TEXMACS) tm_start_output();
  GP_DATA->flags = f;
  if (f & gpd_TEST) {
    GP_DATA->breakloop = 0;
    init80col();
  } else if (initrc)
    gp_initrc(p_A, argv[0]);
  for ( ; i < argc; i++) stack_pushp(p_A, pari_strdup(argv[i]));

  /* override the values from gprc */
  if (p) (void)sd_primelimit(p, d_INITRC);
  if (s) (void)sd_parisize(s, d_INITRC);

  if (GP_DATA->flags & (gpd_EMACS|gpd_TEXMACS|gpd_TEST)) disable_color = 1;
  pari_outfile = stdout;
}

#ifdef WINCE
int
WinMain(HINSTANCE hInstance, HINSTANCE hPrevInstance,
        LPWSTR lpCmdLine, int nShowCmd)
{
  char **argv = NULL;
  int argc = 1;
#else
int
main(int argc, char **argv)
{
#endif
  void **A;
  pari_stack s_A;

  GP_DATA = default_gp_data();
  stack_init(&s_env, sizeof(*env), (void**)&env);
  (void)stack_new(&s_env);

  if (setjmp(env[s_env.n-1]))
  {
    puts("### Errors on startup, exiting...\n\n");
    exit(1);
  }
  gp_is_interactive = pari_stdin_isatty();
  pari_init_defaults();
  stack_init(&s_A,sizeof(*A),(void**)&A);
  stack_init(&s_bufstack, sizeof(Buffer*), (void**)&bufstack);
  cb_pari_err_recover = gp_err_recover;
  pari_init_opts(1000000 * sizeof(long), 500000, INIT_SIGm);
  pari_add_defaults_module(functions_gp_default);
  (void)sd_graphcolormap("[\"white\",\"black\",\"blue\",\"violetred\",\"red\",\"green\",\"grey\",\"gainsboro\"]", d_SILENT);
  (void)sd_graphcolors("[4, 5]", d_SILENT);
  strcpy(Prompt,      DFT_PROMPT);
  strcpy(Prompt_cont, CONTPROMPT);
  Help = init_help();

  read_opt(&s_A, argc,argv);
#ifdef SIGALRM
  (void)os_signal(SIGALRM,gp_alarm_handler);
#endif
  pari_add_module(functions_gp);
  pari_add_module(functions_highlevel);
  pari_add_oldmodule(functions_oldgp);

  init_graph();
#ifdef READLINE
  init_readline();
#endif
  cb_pari_whatnow = whatnow;
  cb_pari_sigint = gp_sigint_fun;
  cb_pari_handle_exception = gp_handle_exception;
  cb_pari_ask_confirm = gp_ask_confirm;
  gp_expand_path(GP_DATA->path);

  timer_start(GP_DATA->T);
  if (!(GP_DATA->flags & gpd_QUIET)) gp_head();
  if (s_A.n)
  {
    FILE *l = pari_logfile;
    long i;
    pari_logfile = NULL;
    for (i = 0; i < s_A.n; pari_free(A[i]),i++) read_main((char*)A[i]);
    /* Reading one of the input files above can set pari_logfile.
     * Don't restore in that case. */
    if (!pari_logfile) pari_logfile = l;
  }
  stack_delete(&s_A);
  (void)gp_main_loop(gp_RECOVER|gp_ISMAIN);
  gp_quit(0); return 0; /* not reached */
}

/*******************************************************************/
/**                                                               **/
/**                          GP OUTPUT                            **/
/**                                                               **/
/*******************************************************************/
    /* EXTERNAL PRETTYPRINTER */
/* Wait for prettinprinter to finish, to prevent new prompt from overwriting
 * the output.  Fill the output buffer, wait until it is read.
 * Better than sleep(2): give possibility to print */
static void
prettyp_wait(void)
{
  const char *s = "                                                     \n";
  long i = 2000;

  pari_puts("\n\n"); pari_flush(); /* start translation */
  while (--i) pari_puts(s);
  pari_puts("\n"); pari_flush();
}

/* initialise external prettyprinter (tex2mail) */
static int
prettyp_init(void)
{
  gp_pp *pp = GP_DATA->pp;
  if (!pp->cmd) return 0;
  if (pp->file || (pp->file = try_pipe(pp->cmd, mf_OUT))) return 1;

  pari_warn(warner,"broken prettyprinter: '%s'",pp->cmd);
  pari_free(pp->cmd); pp->cmd = NULL; return 0;
}

/* n = history number. if n = 0 no history */
static int
tex2mail_output(GEN z, long n)
{
  pariout_t T = *(GP_DATA->fmt); /* copy */
  FILE *o_out, *o_logfile = pari_logfile;

  if (!prettyp_init()) return 0;
  o_out = pari_outfile; /* save state */

  /* Emit first: there may be lines before the prompt */
  if (n) term_color(c_OUTPUT);
  pari_flush();
  pari_outfile = GP_DATA->pp->file->file;
  T.prettyp = f_TEX;
  pari_logfile = NULL;

  /* history number */
  if (n)
  {
    pari_sp av = avma;
    const char *c_hist = term_get_color(NULL, c_HIST);
    const char *c_out = term_get_color(NULL, c_OUTPUT);
    if (!(GP_DATA->flags & gpd_QUIET))
    {
      char s[128];
      if (*c_hist || *c_out)
        sprintf(s, "\\LITERALnoLENGTH{%s}\\%%%ld =\\LITERALnoLENGTH{%s} ",
                c_hist, n, c_out);
      else
        sprintf(s, "\\%%%ld = ", n);
      pari_puts(s);
    }
    if (o_logfile) {
      switch (logstyle) {
      case logstyle_plain:
        fprintf(o_logfile, "%%%ld = ", n);
        break;
      case logstyle_color:
        fprintf(o_logfile, "%s%%%ld = %s", c_hist, n, c_out);
        break;
      case logstyle_TeX:
        fprintf(o_logfile, "\\PARIout{%ld}", n);
        break;
      }
    }
    avma = av;
  }
  /* output */
  gen_output(z, &T);

  /* flush and restore, output to logfile */
  prettyp_wait();
  if (o_logfile) {
    pari_outfile = o_logfile;
    if (logstyle == logstyle_TeX) {
      T.TeXstyle |= TEXSTYLE_BREAK;
      gen_output(z, &T);
      pari_putc('%');
    } else {
      T.prettyp = f_RAW;
      gen_output(z, &T);
    }
    pari_putc('\n'); pari_flush();
  }
  pari_logfile = o_logfile;
  pari_outfile = o_out;
  if (n) term_color(c_NONE);
  return 1;
}

    /* TEXMACS */
static void
texmacs_output(GEN z, long n)
{
  char *sz = GENtoTeXstr(z);
  printf("%clatex:", DATA_BEGIN);
  if (n) printf("\\magenta\\%%%ld = ", n);
  printf("$\\blue %s$%c", sz,DATA_END);
  pari_free(sz); fflush(stdout);
}

    /* REGULAR */
static void
normal_output(GEN z, long n)
{
  long l = 0;
  char *s;
  /* history number */
  if (n)
  {
    char buf[64];
    if (!(GP_DATA->flags & gpd_QUIET))
    {
      term_color(c_HIST);
      sprintf(buf, "%%%ld = ", n);
      pari_puts(buf);
      l = strlen(buf);
    }
  }
  /* output */
  term_color(c_OUTPUT);
  s = GENtostr(z);
  if (GP_DATA->lim_lines)
    lim_lines_output(s, l, GP_DATA->lim_lines);
  else
    pari_puts(s);
  free(s);
  term_color(c_NONE); pari_putc('\n');
}

void
gp_output(GEN z, gp_data *G)
{
  if (G->flags & gpd_TEST) {
    init80col();
    gen_output(z, G->fmt); pari_putc('\n');
  }
  else if (G->flags & gpd_TEXMACS)
    texmacs_output(z, G->hist->total);
  else if (G->fmt->prettyp != f_PRETTY || !tex2mail_output(z, G->hist->total))
    normal_output(z, G->hist->total);
  pari_flush();
}

/*******************************************************************/
/**                                                               **/
/**                     GP-SPECIFIC DEFAULTS                      **/
/**                                                               **/
/*******************************************************************/

static long
atocolor(const char *s)
{
  long l = atol(s);
  if (l <   0) l =   0;
  if (l > 255) l = 255;
  return l;
}

GEN
sd_graphcolormap(const char *v, long flag)
{
  char *p, *q;
  long i, j, l, a, s, *lp;

  if (v)
  {
    char *t = filtre(v, 0);
    if (*t != '[' || t[strlen(t)-1] != ']')
      pari_err(syntaxer, "incorrect value for graphcolormap", t, t);
    for (s = 0, p = t+1, l = 2, a=0; *p; p++)
      if (*p == '[')
      {
        a++;
        while (*++p != ']')
          if (!*p || *p == '[')
            pari_err(syntaxer, "incorrect value for graphcolormap", p, t);
      }
      else if (*p == '"')
      {
        s += sizeof(long)+1;
        while (*p && *++p != '"') s++;
        if (!*p) pari_err(syntaxer, "incorrect value for graphcolormap", p, t);
        s = (s+sizeof(long)-1) & ~(sizeof(long)-1);
      }
      else if (*p == ',')
        l++;
    if (l < 4)
      pari_err(talker, "too few colors (< 4) in graphcolormap");
    if (pari_colormap) pari_free(pari_colormap);
    pari_colormap = (GEN)pari_malloc((l+4*a)*sizeof(long) + s);
    pari_colormap[0] = evaltyp(t_VEC)|evallg(l);
    for (p = t+1, i = 1, lp = pari_colormap+l; i < l; p++)
      switch(*p)
      {
      case '"':
        gel(pari_colormap, i) = lp;
        q = ++p; while (*q != '"') q++;
        *q = 0;
        j = 1 + nchar2nlong(q-p+1);
        lp[0] = evaltyp(t_STR)|evallg(j);
        strncpy(GSTR(lp), p, q-p+1);
        lp += j; p = q;
        break;
      case '[': {
        const char *ap[3];
        gel(pari_colormap, i) = lp;
        lp[0] = evaltyp(t_VECSMALL)|_evallg(4);
        for (ap[0] = ++p, j=0; *p && *p != ']'; p++)
          if (*p == ',' && j<2) { *p++ = 0; ap[++j] = p; }
        while (j<2) ap[++j] = "0";
        if (j>2 || *p != ']')
        {
          char buf[100];
          sprintf(buf, "incorrect value for graphcolormap[%ld]: ", i);
          pari_err(syntaxer, buf, p, t);
        }
        *p = '\0';
        lp[1] = atocolor(ap[0]);
        lp[2] = atocolor(ap[1]);
        lp[3] = atocolor(ap[2]);
        lp += 4;
        break;
      }
      case ',':
      case ']':
        i++;
        break;
      default:
        pari_err(syntaxer, "incorrect value for graphcolormap", p, t);
      }
    free(t);
  }
  if (flag == d_RETURN || flag == d_ACKNOWLEDGE)
  {
    GEN cols = cgetg(lg(pari_colormap), t_VEC);
    long i;

    for (i = 1; i < lg(cols); i++)
    {
      GEN c = gel(pari_colormap, i);
      if (typ(c) == t_STR)
        gel(cols, i) = gcopy(c);
      else
        gel(cols, i) = vecsmall_to_vec(c);
    }
    if (flag == d_RETURN) return cols;
    pari_printf("   graphcolormap = %Ps\n", cols);
  }
  return gnil;
}

GEN
sd_graphcolors(const char *v, long flag)
{
  long i, l;
  char *p;

  if (v) {
    char *t = filtre(v, 0);
    for (p = t+1, l=2; *p != ']'; p++)
      if (*p == ',') l++;
      else if (*p < '0' || *p > '9')
        pari_err(syntaxer, "incorrect value for graphcolors", p, t);
    if (*++p) pari_err(syntaxer, "incorrect value for graphcolors", p, t);
    if (pari_graphcolors) pari_free(pari_graphcolors);
    pari_graphcolors = cgetalloc(t_VECSMALL, l);
    for (p = t+1, i=0; *p; p++)
    {
      long n = 0;
      while (*p >= '0' && *p <= '9')
      {
        n *= 10;
        n += *p-'0';
        p++;
      }
      pari_graphcolors[++i] = n;
    }
    free(t);
  }
  switch(flag)
  {
  case d_RETURN:
    return vecsmall_to_vec(pari_graphcolors);
  case d_ACKNOWLEDGE:
    pari_printf("   graphcolors = %Ps\n", vecsmall_to_vec(pari_graphcolors));
  }
  return gnil;
}

GEN
sd_help(const char *v, long flag)
{
  const char *str;
  if (v)
  {
    if (GP_DATA->secure)
      pari_err(talker,"[secure mode]: can't modify 'help' default (to %s)",v);
    if (Help) pari_free((void*)Help);
    Help = path_expand(v);
  }
  str = Help? Help: "none";
  if (flag == d_RETURN) return strtoGENstr(str);
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   help = \"%s\"\n", str);
  return gnil;
}

static GEN
sd_prompt_set(const char *v, long flag, const char *how, char *p)
{
  if (v) strncpy(p,v,MAX_PROMPT_LEN);
  if (flag == d_RETURN) return strtoGENstr(p);
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   prompt%s = \"%s\"\n", how, p);
  return gnil;
}
GEN
sd_prompt(const char *v, long flag)
{ return sd_prompt_set(v, flag, "", Prompt); }
GEN
sd_prompt_cont(const char *v, long flag)
{ return sd_prompt_set(v, flag, "_cont", Prompt_cont); }

GEN
sd_breakloop(const char *v, long flag)
{ return sd_toggle(v,flag,"breakloop", &(GP_DATA->breakloop)); }
GEN
sd_echo(const char *v, long flag)
{ return sd_toggle(v,flag,"echo", &(GP_DATA->echo)); }
GEN
sd_timer(const char *v, long flag)
{ return sd_toggle(v,flag,"timer", &(GP_DATA->chrono)); }
GEN
sd_recover(const char *v, long flag)
{ return sd_toggle(v,flag,"recover", &(GP_DATA->recover)); }

#ifndef READLINE /* default not implemented */
GEN
sd_readline(const char *v, long flag)
{ (void)v; (void)flag; return gnil; }
GEN
sd_histfile(const char *v, long flag)
{ (void)v; (void)flag; return gnil; }
#endif

GEN
sd_psfile(const char *v, long flag)
{ return sd_string(v, flag, "psfile", &current_psfile); }


GEN
sd_lines(const char *v, long flag)
{ return sd_ulong(v,flag,"lines",&(GP_DATA->lim_lines), 0,LONG_MAX,NULL); }
