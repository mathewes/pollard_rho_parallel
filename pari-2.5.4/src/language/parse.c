
/* A Bison parser, made by GNU Bison 2.4.1.  */

/* Skeleton implementation for Bison's Yacc-like parsers in C
   
      Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002, 2003, 2004, 2005, 2006
   Free Software Foundation, Inc.
   
   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.
   
   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "2.4.1"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 1

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1

/* Using locations.  */
#define YYLSP_NEEDED 1

/* Substitute the variable and function names.  */
#define yyparse         pari_parse
#define yylex           pari_lex
#define yyerror         pari_error
#define yylval          pari_lval
#define yychar          pari_char
#define yydebug         pari_debug
#define yynerrs         pari_nerrs
#define yylloc          pari_lloc

/* Copy the first part of user declarations.  */

/* Line 189 of yacc.c  */
#line 1 "../src/language/parse.y"

/* $Id$

Copyright (C) 2006  The PARI group.

This file is part of the PARI package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#define YYSIZE_T size_t
#define YYSTYPE union token_value
#define YYLTYPE struct node_loc
#define YYLLOC_DEFAULT(Current, Rhs, N)     \
        ((Current).start  = ((N)?(Rhs)[1].start:(Rhs)[0].end),  \
         (Current).end    = (Rhs)[N].end)
#include "parsec.h"



/* Line 189 of yacc.c  */
#line 108 "../src/language/parse.c"

/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif

/* Enabling the token table.  */
#ifndef YYTOKEN_TABLE
# define YYTOKEN_TABLE 0
#endif


/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     KPARROW = 258,
     KARROW = 259,
     KPE = 260,
     KSE = 261,
     KME = 262,
     KDE = 263,
     KDRE = 264,
     KEUCE = 265,
     KMODE = 266,
     KAND = 267,
     KOR = 268,
     KID = 269,
     KEQ = 270,
     KNE = 271,
     KGE = 272,
     KLE = 273,
     KSRE = 274,
     KSLE = 275,
     KSR = 276,
     KSL = 277,
     KDR = 278,
     KPP = 279,
     KSS = 280,
     KINTEGER = 281,
     KREAL = 282,
     KENTRY = 283,
     KSTRING = 284,
     DEFFUNC = 285,
     SEQ = 286,
     LVAL = 287,
     INT = 288,
     SIGN = 289,
     MAT = 290
   };
#endif



#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED

# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
#endif

#if ! defined YYLTYPE && ! defined YYLTYPE_IS_DECLARED
typedef struct YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
} YYLTYPE;
# define yyltype YYLTYPE /* obsolescent; will be withdrawn */
# define YYLTYPE_IS_DECLARED 1
# define YYLTYPE_IS_TRIVIAL 1
#endif


/* Copy the second part of user declarations.  */


/* Line 264 of yacc.c  */
#line 197 "../src/language/parse.c"

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#elif (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
typedef signed char yytype_int8;
#else
typedef short int yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(e) ((void) (e))
#else
# define YYUSE(e) /* empty */
#endif

/* Identity function, used to suppress warnings about constant conditions.  */
#ifndef lint
# define YYID(n) (n)
#else
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static int
YYID (int yyi)
#else
static int
YYID (yyi)
    int yyi;
#endif
{
  return yyi;
}
#endif

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#     ifndef _STDLIB_H
#      define _STDLIB_H 1
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (YYID (0))
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined _STDLIB_H \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef _STDLIB_H
#    define _STDLIB_H 1
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
	 || (defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL \
	     && defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
  YYLTYPE yyls_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE) + sizeof (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  YYSIZE_T yyi;				\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];		\
	}					\
      while (YYID (0))
#  endif
# endif

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)				\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack_alloc, Stack, yysize);			\
	Stack = &yyptr->Stack_alloc;					\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  44
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   589

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  61
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  17
/* YYNRULES -- Number of rules.  */
#define YYNRULES  96
/* YYNRULES -- Number of states.  */
#define YYNSTATES  166

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   290

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    50,     2,    49,     2,    43,    37,    53,
      56,    60,    46,    41,    35,    42,    54,    45,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    57,    34,
      40,    36,    39,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    52,    44,    58,    48,     2,    59,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,    38,     2,    51,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    47,
      55
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     5,     8,     9,    11,    14,    18,    24,
      28,    33,    38,    40,    43,    45,    48,    51,    53,    55,
      57,    61,    63,    66,    68,    73,    75,    77,    79,    81,
      85,    88,    91,    95,    99,   103,   107,   111,   115,   119,
     123,   127,   130,   133,   137,   141,   145,   149,   153,   157,
     161,   165,   169,   173,   177,   181,   185,   189,   193,   197,
     201,   205,   209,   213,   216,   219,   223,   226,   229,   232,
     235,   237,   241,   245,   247,   250,   254,   256,   260,   264,
     268,   271,   275,   279,   283,   287,   289,   292,   293,   298,
     300,   304,   309,   313,   320,   326,   330
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int8 yyrhs[] =
{
      62,     0,    -1,    63,    -1,    63,     1,    -1,    -1,    67,
      -1,    63,    34,    -1,    63,    34,    67,    -1,    52,    67,
      35,    67,    58,    -1,    52,    67,    58,    -1,    52,    67,
      35,    58,    -1,    52,    35,    67,    58,    -1,    59,    -1,
      65,    59,    -1,    43,    -1,    43,    26,    -1,    43,    65,
      -1,    26,    -1,    27,    -1,    54,    -1,    26,    54,    28,
      -1,    29,    -1,    53,    28,    -1,    66,    -1,    67,    56,
      74,    60,    -1,    75,    -1,    68,    -1,    71,    -1,    77,
      -1,    68,    36,    67,    -1,    68,    24,    -1,    68,    25,
      -1,    68,     7,    67,    -1,    68,     8,    67,    -1,    68,
       9,    67,    -1,    68,    10,    67,    -1,    68,    11,    67,
      -1,    68,    20,    67,    -1,    68,    19,    67,    -1,    68,
       5,    67,    -1,    68,     6,    67,    -1,    50,    67,    -1,
      49,    67,    -1,    67,    13,    67,    -1,    67,    38,    67,
      -1,    67,    12,    67,    -1,    67,    37,    67,    -1,    67,
      14,    67,    -1,    67,    15,    67,    -1,    67,    16,    67,
      -1,    67,    17,    67,    -1,    67,    39,    67,    -1,    67,
      18,    67,    -1,    67,    40,    67,    -1,    67,    42,    67,
      -1,    67,    41,    67,    -1,    67,    22,    67,    -1,    67,
      21,    67,    -1,    67,    43,    67,    -1,    67,    23,    67,
      -1,    67,    44,    67,    -1,    67,    45,    67,    -1,    67,
      46,    67,    -1,    41,    67,    -1,    42,    67,    -1,    67,
      48,    67,    -1,    67,    51,    -1,    67,    53,    -1,    67,
      50,    -1,    67,    64,    -1,    76,    -1,    67,    57,    28,
      -1,    56,    67,    60,    -1,    28,    -1,    68,    64,    -1,
      68,    57,    28,    -1,    67,    -1,    69,    35,    67,    -1,
      69,    34,    69,    -1,    70,    34,    69,    -1,    52,    58,
      -1,    52,    34,    58,    -1,    52,    69,    58,    -1,    52,
      70,    58,    -1,    52,     1,    58,    -1,    63,    -1,    37,
      68,    -1,    -1,    72,     1,    73,    67,    -1,    72,    -1,
      74,    35,    72,    -1,    28,    56,    74,    60,    -1,    67,
      54,    28,    -1,    28,    56,    74,    60,    36,    63,    -1,
      67,    54,    28,    36,    63,    -1,    68,     4,    63,    -1,
      56,    74,     3,    63,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint8 yyrline[] =
{
       0,    84,    84,    85,    88,    89,    90,    91,    94,    95,
      96,    97,   100,   101,   104,   105,   106,   109,   110,   111,
     112,   114,   115,   116,   117,   118,   119,   120,   121,   122,
     123,   124,   125,   126,   127,   128,   129,   130,   131,   132,
     133,   134,   135,   136,   137,   138,   139,   140,   141,   142,
     143,   144,   145,   146,   147,   148,   149,   150,   151,   152,
     153,   154,   155,   156,   157,   158,   159,   160,   161,   162,
     163,   164,   165,   168,   169,   170,   173,   174,   177,   178,
     181,   182,   183,   184,   185,   188,   189,   190,   190,   194,
     195,   198,   201,   204,   206,   208,   209
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "\")->\"", "\"->\"", "\"+=\"", "\"-=\"",
  "\"*=\"", "\"/=\"", "\"\\\\/=\"", "\"\\\\=\"", "\"%=\"", "\"&&\"",
  "\"||\"", "\"===\"", "\"==\"", "\"!=\"", "\">=\"", "\"<=\"", "\">>=\"",
  "\"<<=\"", "\">>\"", "\"<<\"", "\"\\\\/\"", "\"++\"", "\"--\"",
  "\"integer\"", "\"real number\"", "\"variable name\"",
  "\"character string\"", "DEFFUNC", "SEQ", "LVAL", "INT", "';'", "','",
  "'='", "'&'", "'|'", "'>'", "'<'", "'+'", "'-'", "'%'", "'\\\\'", "'/'",
  "'*'", "SIGN", "'^'", "'#'", "'!'", "'~'", "'['", "'\\''", "'.'", "MAT",
  "'('", "':'", "']'", "'`'", "')'", "$accept", "sequnused", "seq",
  "matrix_index", "backticks", "history", "expr", "lvalue", "matrixelts",
  "matrixlines", "matrix", "arg", "$@1", "listarg", "funcid", "memberid",
  "definition", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,    59,    44,    61,    38,   124,    62,
      60,    43,    45,    37,    92,    47,    42,   289,    94,    35,
      33,   126,    91,    39,    46,   290,    40,    58,    93,    96,
      41
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    61,    62,    62,    63,    63,    63,    63,    64,    64,
      64,    64,    65,    65,    66,    66,    66,    67,    67,    67,
      67,    67,    67,    67,    67,    67,    67,    67,    67,    67,
      67,    67,    67,    67,    67,    67,    67,    67,    67,    67,
      67,    67,    67,    67,    67,    67,    67,    67,    67,    67,
      67,    67,    67,    67,    67,    67,    67,    67,    67,    67,
      67,    67,    67,    67,    67,    67,    67,    67,    67,    67,
      67,    67,    67,    68,    68,    68,    69,    69,    70,    70,
      71,    71,    71,    71,    71,    72,    72,    73,    72,    74,
      74,    75,    76,    77,    77,    77,    77
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     2,     0,     1,     2,     3,     5,     3,
       4,     4,     1,     2,     1,     2,     2,     1,     1,     1,
       3,     1,     2,     1,     4,     1,     1,     1,     1,     3,
       2,     2,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     2,     2,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     2,     2,     3,     2,     2,     2,     2,
       1,     3,     3,     1,     2,     3,     1,     3,     3,     3,
       2,     3,     3,     3,     3,     1,     2,     0,     4,     1,
       3,     4,     3,     6,     5,     3,     4
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       4,    17,    18,    73,    21,     0,     0,    14,     0,     0,
       0,     0,    19,     4,     0,     0,    23,     5,    26,    27,
      25,    70,    28,     0,     4,    63,    64,    15,    12,    16,
      42,    41,     0,     0,    80,    76,     0,     0,    22,     0,
      85,     5,     0,     0,     1,     3,     6,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    68,    66,
       0,    67,     0,     4,     0,    69,     4,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    30,    31,     0,     0,
      74,    20,     0,    13,    84,    81,     0,     0,    82,     0,
      83,    73,    86,    72,    87,     4,     4,     7,    45,    43,
      47,    48,    49,    50,    52,    57,    56,    59,    46,    44,
      51,    53,    55,    54,    58,    60,    61,    62,    65,     0,
       0,    92,     0,    71,    95,    39,    40,    32,    33,    34,
      35,    36,    38,    37,    29,    75,    91,    78,    77,    79,
       0,    96,     0,     0,     0,     9,     4,    24,     4,    88,
      11,    10,     0,    94,    93,     8
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,    14,    40,    75,    29,    16,    17,    18,    36,    37,
      19,    42,   150,    43,    20,    21,    22
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -55
static const yytype_int16 yypact[] =
{
     533,   -49,   -55,   -28,   -55,   533,   533,   -25,   533,   533,
      90,    15,   -55,   484,    44,    12,   -55,   338,   102,   -55,
     -55,   -55,   -55,    45,   484,   124,   124,   -55,   -55,    16,
     -32,   -24,    19,    30,   -55,   338,   -19,   -17,   -55,    46,
      56,   148,    34,     5,   -55,   -55,   533,   533,   533,   533,
     533,   533,   533,   533,   533,   533,   533,   533,   533,   533,
     533,   533,   533,   533,   533,   533,   533,   533,   -55,   -55,
     515,   -55,    64,   484,    65,   -55,   533,   533,   533,   533,
     533,   533,   533,   533,   533,   533,   -55,   -55,   533,    68,
     -55,   -55,   -33,   -55,   -55,   -55,   533,   533,   -55,   533,
     -55,   -55,   -26,   -55,   -55,   533,   484,   338,   382,   382,
     419,   419,   419,   419,   419,   124,   124,   124,   382,   382,
     419,   419,   434,   434,   124,   124,   124,   124,   124,   533,
     197,    63,   -31,   -55,    56,   338,   338,   338,   338,   338,
     338,   338,   338,   338,   338,   -55,    66,    69,   338,    69,
     533,    56,    35,   244,   466,   -55,   533,   -55,   533,   338,
     -55,   -55,   291,    56,    56,   -55
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int8 yypgoto[] =
{
     -55,   -55,     0,   -15,   -55,   -55,     1,    62,   -54,   -55,
     -55,    -3,   -55,    -1,   -55,   -55,   -55
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -91
static const yytype_int16 yytable[] =
{
      15,    27,   106,    90,   106,    23,    25,    26,   105,    30,
      31,    35,    -2,    45,    41,    96,    97,    99,    68,    69,
      70,    71,    72,    92,    73,    74,    70,   146,    24,   157,
      72,    89,    73,    74,    28,   104,   104,   -89,   -90,    98,
     106,   100,   147,    38,    44,   149,    46,   107,   108,   109,
     110,   111,   112,   113,   114,   115,   116,   117,   118,   119,
     120,   121,   122,   123,   124,   125,   126,   127,   128,   -89,
     -90,   130,   132,    91,   101,    93,   134,    94,   135,   136,
     137,   138,   139,   140,   141,   142,   143,    90,    95,   144,
      46,    32,   131,   133,   -89,   -90,   145,    35,   148,   156,
      35,   102,   158,   152,    97,   151,    76,    77,    78,    79,
      80,    81,    82,    83,     0,     0,     1,     2,     3,     4,
       0,    84,    85,     0,    33,     0,    86,    87,     0,     0,
     153,     5,     6,     7,     0,     0,     0,     0,    88,     8,
       9,     0,    10,    11,    12,     0,    13,     0,    34,     0,
       0,   159,     0,     0,    70,   162,   163,     0,   164,    89,
      47,    48,    49,    50,    51,    52,    53,     0,     0,    54,
      55,    56,    67,     0,    68,    69,    70,    71,    72,     0,
      73,    74,     0,     0,     0,    57,    58,    59,    60,    61,
      62,    63,    64,    65,    66,     0,    67,     0,    68,    69,
      70,    71,    72,     0,    73,    74,     0,     0,   103,    47,
      48,    49,    50,    51,    52,    53,     0,     0,    54,    55,
      56,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   154,     0,    57,    58,    59,    60,    61,    62,
      63,    64,    65,    66,     0,    67,     0,    68,    69,    70,
      71,    72,     0,    73,    74,   155,    47,    48,    49,    50,
      51,    52,    53,     0,     0,    54,    55,    56,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    57,    58,    59,    60,    61,    62,    63,    64,    65,
      66,     0,    67,     0,    68,    69,    70,    71,    72,     0,
      73,    74,   160,    47,    48,    49,    50,    51,    52,    53,
       0,     0,    54,    55,    56,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    57,    58,
      59,    60,    61,    62,    63,    64,    65,    66,     0,    67,
       0,    68,    69,    70,    71,    72,     0,    73,    74,   165,
      47,    48,    49,    50,    51,    52,    53,     0,     0,    54,
      55,    56,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    57,    58,    59,    60,    61,
      62,    63,    64,    65,    66,     0,    67,     0,    68,    69,
      70,    71,    72,     0,    73,    74,    49,    50,    51,    52,
      53,     0,     0,    54,    55,    56,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    59,    60,    61,    62,    63,    64,    65,    66,     0,
      67,     0,    68,    69,    70,    71,    72,     0,    73,    74,
      54,    55,    56,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    54,    55,    56,     0,     0,
      61,    62,    63,    64,    65,    66,     0,    67,     0,    68,
      69,    70,    71,    72,     0,    73,    74,    63,    64,    65,
      66,     0,    67,     0,    68,    69,    70,    71,    72,     0,
      73,    74,     1,     2,     3,     4,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     5,     6,     7,
       1,     2,     3,     4,     0,     8,     9,     0,    10,    11,
      12,    39,    13,     0,   161,     5,     6,     7,     0,     0,
       0,     0,     0,     8,     9,     0,    10,    11,    12,     0,
      13,     1,     2,     3,     4,     0,     0,     0,     0,     0,
     129,     0,     0,     0,     0,     0,     5,     6,     7,     1,
       2,     3,     4,     0,     8,     9,     0,    10,    11,    12,
       0,    13,     0,     0,     5,     6,     7,     0,     0,     0,
       0,     0,     8,     9,     0,    10,    11,    12,     0,    13
};

static const yytype_int16 yycheck[] =
{
       0,    26,    35,    18,    35,    54,     5,     6,     3,     8,
       9,    10,     0,     1,    13,    34,    35,    34,    50,    51,
      52,    53,    54,    24,    56,    57,    52,    60,    56,    60,
      54,    57,    56,    57,    59,     1,     1,     3,     3,    58,
      35,    58,    96,    28,     0,    99,    34,    46,    47,    48,
      49,    50,    51,    52,    53,    54,    55,    56,    57,    58,
      59,    60,    61,    62,    63,    64,    65,    66,    67,    35,
      35,    70,    73,    28,    28,    59,    76,    58,    77,    78,
      79,    80,    81,    82,    83,    84,    85,   102,    58,    88,
      34,     1,    28,    28,    60,    60,    28,    96,    97,    36,
      99,    39,    36,   106,    35,   105,     4,     5,     6,     7,
       8,     9,    10,    11,    -1,    -1,    26,    27,    28,    29,
      -1,    19,    20,    -1,    34,    -1,    24,    25,    -1,    -1,
     129,    41,    42,    43,    -1,    -1,    -1,    -1,    36,    49,
      50,    -1,    52,    53,    54,    -1,    56,    -1,    58,    -1,
      -1,   150,    -1,    -1,    52,   154,   156,    -1,   158,    57,
      12,    13,    14,    15,    16,    17,    18,    -1,    -1,    21,
      22,    23,    48,    -1,    50,    51,    52,    53,    54,    -1,
      56,    57,    -1,    -1,    -1,    37,    38,    39,    40,    41,
      42,    43,    44,    45,    46,    -1,    48,    -1,    50,    51,
      52,    53,    54,    -1,    56,    57,    -1,    -1,    60,    12,
      13,    14,    15,    16,    17,    18,    -1,    -1,    21,    22,
      23,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    35,    -1,    37,    38,    39,    40,    41,    42,
      43,    44,    45,    46,    -1,    48,    -1,    50,    51,    52,
      53,    54,    -1,    56,    57,    58,    12,    13,    14,    15,
      16,    17,    18,    -1,    -1,    21,    22,    23,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    37,    38,    39,    40,    41,    42,    43,    44,    45,
      46,    -1,    48,    -1,    50,    51,    52,    53,    54,    -1,
      56,    57,    58,    12,    13,    14,    15,    16,    17,    18,
      -1,    -1,    21,    22,    23,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    37,    38,
      39,    40,    41,    42,    43,    44,    45,    46,    -1,    48,
      -1,    50,    51,    52,    53,    54,    -1,    56,    57,    58,
      12,    13,    14,    15,    16,    17,    18,    -1,    -1,    21,
      22,    23,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    37,    38,    39,    40,    41,
      42,    43,    44,    45,    46,    -1,    48,    -1,    50,    51,
      52,    53,    54,    -1,    56,    57,    14,    15,    16,    17,
      18,    -1,    -1,    21,    22,    23,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    39,    40,    41,    42,    43,    44,    45,    46,    -1,
      48,    -1,    50,    51,    52,    53,    54,    -1,    56,    57,
      21,    22,    23,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    21,    22,    23,    -1,    -1,
      41,    42,    43,    44,    45,    46,    -1,    48,    -1,    50,
      51,    52,    53,    54,    -1,    56,    57,    43,    44,    45,
      46,    -1,    48,    -1,    50,    51,    52,    53,    54,    -1,
      56,    57,    26,    27,    28,    29,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    41,    42,    43,
      26,    27,    28,    29,    -1,    49,    50,    -1,    52,    53,
      54,    37,    56,    -1,    58,    41,    42,    43,    -1,    -1,
      -1,    -1,    -1,    49,    50,    -1,    52,    53,    54,    -1,
      56,    26,    27,    28,    29,    -1,    -1,    -1,    -1,    -1,
      35,    -1,    -1,    -1,    -1,    -1,    41,    42,    43,    26,
      27,    28,    29,    -1,    49,    50,    -1,    52,    53,    54,
      -1,    56,    -1,    -1,    41,    42,    43,    -1,    -1,    -1,
      -1,    -1,    49,    50,    -1,    52,    53,    54,    -1,    56
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    26,    27,    28,    29,    41,    42,    43,    49,    50,
      52,    53,    54,    56,    62,    63,    66,    67,    68,    71,
      75,    76,    77,    54,    56,    67,    67,    26,    59,    65,
      67,    67,     1,    34,    58,    67,    69,    70,    28,    37,
      63,    67,    72,    74,     0,     1,    34,    12,    13,    14,
      15,    16,    17,    18,    21,    22,    23,    37,    38,    39,
      40,    41,    42,    43,    44,    45,    46,    48,    50,    51,
      52,    53,    54,    56,    57,    64,     4,     5,     6,     7,
       8,     9,    10,    11,    19,    20,    24,    25,    36,    57,
      64,    28,    74,    59,    58,    58,    34,    35,    58,    34,
      58,    28,    68,    60,     1,     3,    35,    67,    67,    67,
      67,    67,    67,    67,    67,    67,    67,    67,    67,    67,
      67,    67,    67,    67,    67,    67,    67,    67,    67,    35,
      67,    28,    74,    28,    63,    67,    67,    67,    67,    67,
      67,    67,    67,    67,    67,    28,    60,    69,    67,    69,
      73,    63,    72,    67,    35,    58,    36,    60,    36,    67,
      58,    58,    67,    63,    63,    58
};

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab


/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  */

#define YYFAIL		goto yyerrlab

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
      yytoken = YYTRANSLATE (yychar);				\
      YYPOPSTACK (1);						\
      goto yybackup;						\
    }								\
  else								\
    {								\
      yyerror (&yylloc, lex, YY_("syntax error: cannot back up")); \
      YYERROR;							\
    }								\
while (YYID (0))


#define YYTERROR	1
#define YYERRCODE	256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)				\
    do									\
      if (YYID (N))                                                    \
	{								\
	  (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;	\
	  (Current).first_column = YYRHSLOC (Rhs, 1).first_column;	\
	  (Current).last_line    = YYRHSLOC (Rhs, N).last_line;		\
	  (Current).last_column  = YYRHSLOC (Rhs, N).last_column;	\
	}								\
      else								\
	{								\
	  (Current).first_line   = (Current).last_line   =		\
	    YYRHSLOC (Rhs, 0).last_line;				\
	  (Current).first_column = (Current).last_column =		\
	    YYRHSLOC (Rhs, 0).last_column;				\
	}								\
    while (YYID (0))
#endif


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if YYLTYPE_IS_TRIVIAL
#  define YY_LOCATION_PRINT(File, Loc)			\
     fprintf (File, "%d.%d-%d.%d",			\
	      (Loc).first_line, (Loc).first_column,	\
	      (Loc).last_line,  (Loc).last_column)
# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


/* YYLEX -- calling `yylex' with the right arguments.  */

#ifdef YYLEX_PARAM
# define YYLEX yylex (&yylval, &yylloc, YYLEX_PARAM)
#else
# define YYLEX yylex (&yylval, &yylloc, lex)
#endif

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (YYID (0))

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)			  \
do {									  \
  if (yydebug)								  \
    {									  \
      YYFPRINTF (stderr, "%s ", Title);					  \
      yy_symbol_print (stderr,						  \
		  Type, Value, Location, lex); \
      YYFPRINTF (stderr, "\n");						  \
    }									  \
} while (YYID (0))


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, char **lex)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, lex)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
    YYLTYPE const * const yylocationp;
    char **lex;
#endif
{
  if (!yyvaluep)
    return;
  YYUSE (yylocationp);
  YYUSE (lex);
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# else
  YYUSE (yyoutput);
# endif
  switch (yytype)
    {
      default:
	break;
    }
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, char **lex)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep, yylocationp, lex)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
    YYLTYPE const * const yylocationp;
    char **lex;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  YY_LOCATION_PRINT (yyoutput, *yylocationp);
  YYFPRINTF (yyoutput, ": ");
  yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, lex);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
#else
static void
yy_stack_print (yybottom, yytop)
    yytype_int16 *yybottom;
    yytype_int16 *yytop;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (yydebug)							\
    yy_stack_print ((Bottom), (Top));				\
} while (YYID (0))


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_reduce_print (YYSTYPE *yyvsp, YYLTYPE *yylsp, int yyrule, char **lex)
#else
static void
yy_reduce_print (yyvsp, yylsp, yyrule, lex)
    YYSTYPE *yyvsp;
    YYLTYPE *yylsp;
    int yyrule;
    char **lex;
#endif
{
  int yynrhs = yyr2[yyrule];
  int yyi;
  unsigned long int yylno = yyrline[yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
	     yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       , &(yylsp[(yyi + 1) - (yynrhs)])		       , lex);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, yylsp, Rule, lex); \
} while (YYID (0))

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif



#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static YYSIZE_T
yystrlen (const char *yystr)
#else
static YYSIZE_T
yystrlen (yystr)
    const char *yystr;
#endif
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static char *
yystpcpy (char *yydest, const char *yysrc)
#else
static char *
yystpcpy (yydest, yysrc)
    char *yydest;
    const char *yysrc;
#endif
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
	switch (*++yyp)
	  {
	  case '\'':
	  case ',':
	    goto do_not_strip_quotes;

	  case '\\':
	    if (*++yyp != '\\')
	      goto do_not_strip_quotes;
	    /* Fall through.  */
	  default:
	    if (yyres)
	      yyres[yyn] = *yyp;
	    yyn++;
	    break;

	  case '"':
	    if (yyres)
	      yyres[yyn] = '\0';
	    return yyn;
	  }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into YYRESULT an error message about the unexpected token
   YYCHAR while in state YYSTATE.  Return the number of bytes copied,
   including the terminating null byte.  If YYRESULT is null, do not
   copy anything; just return the number of bytes that would be
   copied.  As a special case, return 0 if an ordinary "syntax error"
   message will do.  Return YYSIZE_MAXIMUM if overflow occurs during
   size calculation.  */
static YYSIZE_T
yysyntax_error (char *yyresult, int yystate, int yychar)
{
  int yyn = yypact[yystate];

  if (! (YYPACT_NINF < yyn && yyn <= YYLAST))
    return 0;
  else
    {
      int yytype = YYTRANSLATE (yychar);
      YYSIZE_T yysize0 = yytnamerr (0, yytname[yytype]);
      YYSIZE_T yysize = yysize0;
      YYSIZE_T yysize1;
      int yysize_overflow = 0;
      enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
      char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
      int yyx;

# if 0
      /* This is so xgettext sees the translatable formats that are
	 constructed on the fly.  */
      YY_("syntax error, unexpected %s");
      YY_("syntax error, unexpected %s, expecting %s");
      YY_("syntax error, unexpected %s, expecting %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s");
# endif
      char *yyfmt;
      char const *yyf;
      static char const yyunexpected[] = "syntax error, unexpected %s";
      static char const yyexpecting[] = ", expecting %s";
      static char const yyor[] = " or %s";
      char yyformat[sizeof yyunexpected
		    + sizeof yyexpecting - 1
		    + ((YYERROR_VERBOSE_ARGS_MAXIMUM - 2)
		       * (sizeof yyor - 1))];
      char const *yyprefix = yyexpecting;

      /* Start YYX at -YYN if negative to avoid negative indexes in
	 YYCHECK.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;

      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yycount = 1;

      yyarg[0] = yytname[yytype];
      yyfmt = yystpcpy (yyformat, yyunexpected);

      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
	if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
	  {
	    if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
	      {
		yycount = 1;
		yysize = yysize0;
		yyformat[sizeof yyunexpected - 1] = '\0';
		break;
	      }
	    yyarg[yycount++] = yytname[yyx];
	    yysize1 = yysize + yytnamerr (0, yytname[yyx]);
	    yysize_overflow |= (yysize1 < yysize);
	    yysize = yysize1;
	    yyfmt = yystpcpy (yyfmt, yyprefix);
	    yyprefix = yyor;
	  }

      yyf = YY_(yyformat);
      yysize1 = yysize + yystrlen (yyf);
      yysize_overflow |= (yysize1 < yysize);
      yysize = yysize1;

      if (yysize_overflow)
	return YYSIZE_MAXIMUM;

      if (yyresult)
	{
	  /* Avoid sprintf, as that infringes on the user's name space.
	     Don't have undefined behavior even if the translation
	     produced a string with the wrong number of "%s"s.  */
	  char *yyp = yyresult;
	  int yyi = 0;
	  while ((*yyp = *yyf) != '\0')
	    {
	      if (*yyp == '%' && yyf[1] == 's' && yyi < yycount)
		{
		  yyp += yytnamerr (yyp, yyarg[yyi++]);
		  yyf += 2;
		}
	      else
		{
		  yyp++;
		  yyf++;
		}
	    }
	}
      return yysize;
    }
}
#endif /* YYERROR_VERBOSE */


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, char **lex)
#else
static void
yydestruct (yymsg, yytype, yyvaluep, yylocationp, lex)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
    YYLTYPE *yylocationp;
    char **lex;
#endif
{
  YYUSE (yyvaluep);
  YYUSE (yylocationp);
  YYUSE (lex);

  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  switch (yytype)
    {
      case 63: /* "seq" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1349 "../src/language/parse.c"
	break;
      case 64: /* "matrix_index" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1358 "../src/language/parse.c"
	break;
      case 65: /* "backticks" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1367 "../src/language/parse.c"
	break;
      case 66: /* "history" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1376 "../src/language/parse.c"
	break;
      case 67: /* "expr" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1385 "../src/language/parse.c"
	break;
      case 68: /* "lvalue" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1394 "../src/language/parse.c"
	break;
      case 69: /* "matrixelts" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1403 "../src/language/parse.c"
	break;
      case 70: /* "matrixlines" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1412 "../src/language/parse.c"
	break;
      case 71: /* "matrix" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1421 "../src/language/parse.c"
	break;
      case 72: /* "arg" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1430 "../src/language/parse.c"
	break;
      case 74: /* "listarg" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1439 "../src/language/parse.c"
	break;
      case 75: /* "funcid" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1448 "../src/language/parse.c"
	break;
      case 76: /* "memberid" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1457 "../src/language/parse.c"
	break;
      case 77: /* "definition" */

/* Line 1000 of yacc.c  */
#line 81 "../src/language/parse.y"
	{ pari_discarded++; };

/* Line 1000 of yacc.c  */
#line 1466 "../src/language/parse.c"
	break;

      default:
	break;
    }
}

/* Prevent warnings from -Wmissing-prototypes.  */
#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int yyparse (void *YYPARSE_PARAM);
#else
int yyparse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int yyparse (char **lex);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */





/*-------------------------.
| yyparse or yypush_parse.  |
`-------------------------*/

#ifdef YYPARSE_PARAM
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void *YYPARSE_PARAM)
#else
int
yyparse (YYPARSE_PARAM)
    void *YYPARSE_PARAM;
#endif
#else /* ! YYPARSE_PARAM */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (char **lex)
#else
int
yyparse (lex)
    char **lex;
#endif
#endif
{
/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;

/* Location data for the lookahead symbol.  */
YYLTYPE yylloc;

    /* Number of syntax errors so far.  */
    int yynerrs;

    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       `yyss': related to states.
       `yyvs': related to semantic values.
       `yyls': related to locations.

       Refer to the stacks thru separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    /* The location stack.  */
    YYLTYPE yylsa[YYINITDEPTH];
    YYLTYPE *yyls;
    YYLTYPE *yylsp;

    /* The locations where the error started and ended.  */
    YYLTYPE yyerror_range[2];

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;
  YYLTYPE yyloc;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yytoken = 0;
  yyss = yyssa;
  yyvs = yyvsa;
  yyls = yylsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */
  yyssp = yyss;
  yyvsp = yyvs;
  yylsp = yyls;

#if YYLTYPE_IS_TRIVIAL
  /* Initialize the default location before parsing starts.  */
  yylloc.first_line   = yylloc.last_line   = 1;
  yylloc.first_column = yylloc.last_column = 1;
#endif

/* User initialization code.  */

/* Line 1242 of yacc.c  */
#line 31 "../src/language/parse.y"
{ yylloc.start=yylloc.end=*lex; }

/* Line 1242 of yacc.c  */
#line 1619 "../src/language/parse.c"
  yylsp[0] = yylloc;

  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack.  Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	yytype_int16 *yyss1 = yyss;
	YYLTYPE *yyls1 = yyls;

	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),
		    &yyls1, yysize * sizeof (*yylsp),
		    &yystacksize);

	yyls = yyls1;
	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
	goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
	yystacksize = YYMAXDEPTH;

      {
	yytype_int16 *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyexhaustedlab;
	YYSTACK_RELOCATE (yyss_alloc, yyss);
	YYSTACK_RELOCATE (yyvs_alloc, yyvs);
	YYSTACK_RELOCATE (yyls_alloc, yyls);
#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;
      yylsp = yyls + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yyn == YYPACT_NINF)
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yyn == 0 || yyn == YYTABLE_NINF)
	goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  *++yyvsp = yylval;
  *++yylsp = yylloc;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];

  /* Default location.  */
  YYLLOC_DEFAULT (yyloc, (yylsp - yylen), yylen);
  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:

/* Line 1455 of yacc.c  */
#line 84 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);;}
    break;

  case 3:

/* Line 1455 of yacc.c  */
#line 85 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (2)].val); pari_unused_chars=(yylsp[(1) - (2)]).end;YYABORT;;}
    break;

  case 4:

/* Line 1455 of yacc.c  */
#line 88 "../src/language/parse.y"
    {(yyval.val)=newnode(Fnoarg,-1,-1,&(yyloc));;}
    break;

  case 5:

/* Line 1455 of yacc.c  */
#line 89 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);;}
    break;

  case 6:

/* Line 1455 of yacc.c  */
#line 90 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (2)].val); (yyloc)=(yylsp[(1) - (2)]);;}
    break;

  case 7:

/* Line 1455 of yacc.c  */
#line 91 "../src/language/parse.y"
    {(yyval.val)=newnode(Fseq,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 8:

/* Line 1455 of yacc.c  */
#line 94 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmatrix,(yyvsp[(2) - (5)].val),(yyvsp[(4) - (5)].val),&(yyloc));;}
    break;

  case 9:

/* Line 1455 of yacc.c  */
#line 95 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmatrix,(yyvsp[(2) - (3)].val),-1,&(yyloc));;}
    break;

  case 10:

/* Line 1455 of yacc.c  */
#line 96 "../src/language/parse.y"
    {(yyval.val)=newnode(FmatrixL,(yyvsp[(2) - (4)].val),-1,&(yyloc));;}
    break;

  case 11:

/* Line 1455 of yacc.c  */
#line 97 "../src/language/parse.y"
    {(yyval.val)=newnode(FmatrixR,(yyvsp[(3) - (4)].val),-1,&(yyloc));;}
    break;

  case 12:

/* Line 1455 of yacc.c  */
#line 100 "../src/language/parse.y"
    {(yyval.val)=1;;}
    break;

  case 13:

/* Line 1455 of yacc.c  */
#line 101 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (2)].val)+1;;}
    break;

  case 14:

/* Line 1455 of yacc.c  */
#line 104 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPhist,-1,-1,&(yyloc));;}
    break;

  case 15:

/* Line 1455 of yacc.c  */
#line 105 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPhist,newintnode(&(yylsp[(2) - (2)])),-1,&(yyloc));;}
    break;

  case 16:

/* Line 1455 of yacc.c  */
#line 106 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPhist,newnode(Fsmall,-(yyvsp[(2) - (2)].val),-1,&(yyloc)),-1,&(yyloc));;}
    break;

  case 17:

/* Line 1455 of yacc.c  */
#line 109 "../src/language/parse.y"
    {(yyval.val)=newintnode(&(yylsp[(1) - (1)]));;}
    break;

  case 18:

/* Line 1455 of yacc.c  */
#line 110 "../src/language/parse.y"
    {(yyval.val)=newconst(CSTreal,&(yyloc));;}
    break;

  case 19:

/* Line 1455 of yacc.c  */
#line 111 "../src/language/parse.y"
    {(yyval.val)=newconst(CSTreal,&(yyloc));;}
    break;

  case 20:

/* Line 1455 of yacc.c  */
#line 112 "../src/language/parse.y"
    {(yyval.val)=newnode(Ffunction,newconst(CSTmember,&(yylsp[(3) - (3)])),
                                                newintnode(&(yylsp[(1) - (3)])),&(yyloc));;}
    break;

  case 21:

/* Line 1455 of yacc.c  */
#line 114 "../src/language/parse.y"
    {(yyval.val)=newconst(CSTstr,&(yyloc));;}
    break;

  case 22:

/* Line 1455 of yacc.c  */
#line 115 "../src/language/parse.y"
    {(yyval.val)=newconst(CSTquote,&(yyloc));;}
    break;

  case 23:

/* Line 1455 of yacc.c  */
#line 116 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);;}
    break;

  case 24:

/* Line 1455 of yacc.c  */
#line 117 "../src/language/parse.y"
    {(yyval.val)=newnode(Fcall,(yyvsp[(1) - (4)].val),(yyvsp[(3) - (4)].val),&(yyloc));;}
    break;

  case 25:

/* Line 1455 of yacc.c  */
#line 118 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);;}
    break;

  case 26:

/* Line 1455 of yacc.c  */
#line 119 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);;}
    break;

  case 27:

/* Line 1455 of yacc.c  */
#line 120 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);;}
    break;

  case 28:

/* Line 1455 of yacc.c  */
#line 121 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);;}
    break;

  case 29:

/* Line 1455 of yacc.c  */
#line 122 "../src/language/parse.y"
    {(yyval.val)=newnode(Faffect,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 30:

/* Line 1455 of yacc.c  */
#line 123 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPpp,(yyvsp[(1) - (2)].val),-1,&(yyloc));;}
    break;

  case 31:

/* Line 1455 of yacc.c  */
#line 124 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPss,(yyvsp[(1) - (2)].val),-1,&(yyloc));;}
    break;

  case 32:

/* Line 1455 of yacc.c  */
#line 125 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPme,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 33:

/* Line 1455 of yacc.c  */
#line 126 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPde,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 34:

/* Line 1455 of yacc.c  */
#line 127 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPdre,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 35:

/* Line 1455 of yacc.c  */
#line 128 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPeuce,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 36:

/* Line 1455 of yacc.c  */
#line 129 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPmode,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 37:

/* Line 1455 of yacc.c  */
#line 130 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPsle,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 38:

/* Line 1455 of yacc.c  */
#line 131 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPsre,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 39:

/* Line 1455 of yacc.c  */
#line 132 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPpe,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 40:

/* Line 1455 of yacc.c  */
#line 133 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPse,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 41:

/* Line 1455 of yacc.c  */
#line 134 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPnb,(yyvsp[(2) - (2)].val),-1,&(yyloc));;}
    break;

  case 42:

/* Line 1455 of yacc.c  */
#line 135 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPlength,(yyvsp[(2) - (2)].val),-1,&(yyloc));;}
    break;

  case 43:

/* Line 1455 of yacc.c  */
#line 136 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPor,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 44:

/* Line 1455 of yacc.c  */
#line 137 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPor,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 45:

/* Line 1455 of yacc.c  */
#line 138 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPand,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 46:

/* Line 1455 of yacc.c  */
#line 139 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPand,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 47:

/* Line 1455 of yacc.c  */
#line 140 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPid,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 48:

/* Line 1455 of yacc.c  */
#line 141 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPeq,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 49:

/* Line 1455 of yacc.c  */
#line 142 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPne,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 50:

/* Line 1455 of yacc.c  */
#line 143 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPge,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 51:

/* Line 1455 of yacc.c  */
#line 144 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPg,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 52:

/* Line 1455 of yacc.c  */
#line 145 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPle,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 53:

/* Line 1455 of yacc.c  */
#line 146 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPl,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 54:

/* Line 1455 of yacc.c  */
#line 147 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPs,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 55:

/* Line 1455 of yacc.c  */
#line 148 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPp,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 56:

/* Line 1455 of yacc.c  */
#line 149 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPsl,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 57:

/* Line 1455 of yacc.c  */
#line 150 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPsr,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 58:

/* Line 1455 of yacc.c  */
#line 151 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPmod,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 59:

/* Line 1455 of yacc.c  */
#line 152 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPdr,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 60:

/* Line 1455 of yacc.c  */
#line 153 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPeuc,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 61:

/* Line 1455 of yacc.c  */
#line 154 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPd,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 62:

/* Line 1455 of yacc.c  */
#line 155 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPm,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 63:

/* Line 1455 of yacc.c  */
#line 156 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(2) - (2)].val);;}
    break;

  case 64:

/* Line 1455 of yacc.c  */
#line 157 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPn,(yyvsp[(2) - (2)].val),-1,&(yyloc));;}
    break;

  case 65:

/* Line 1455 of yacc.c  */
#line 158 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPpow,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 66:

/* Line 1455 of yacc.c  */
#line 159 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPtrans,(yyvsp[(1) - (2)].val),-1,&(yyloc));;}
    break;

  case 67:

/* Line 1455 of yacc.c  */
#line 160 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPderiv,(yyvsp[(1) - (2)].val),-1,&(yyloc));;}
    break;

  case 68:

/* Line 1455 of yacc.c  */
#line 161 "../src/language/parse.y"
    {(yyval.val)=newopcall(OPfact,(yyvsp[(1) - (2)].val),-1,&(yyloc));;}
    break;

  case 69:

/* Line 1455 of yacc.c  */
#line 162 "../src/language/parse.y"
    {(yyval.val)=newnode(Ffacteurmat,(yyvsp[(1) - (2)].val),(yyvsp[(2) - (2)].val),&(yyloc));;}
    break;

  case 70:

/* Line 1455 of yacc.c  */
#line 163 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);;}
    break;

  case 71:

/* Line 1455 of yacc.c  */
#line 164 "../src/language/parse.y"
    {(yyval.val)=newnode(Ftag,(yyvsp[(1) - (3)].val),0,&(yyloc));;}
    break;

  case 72:

/* Line 1455 of yacc.c  */
#line 165 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(2) - (3)].val);;}
    break;

  case 73:

/* Line 1455 of yacc.c  */
#line 168 "../src/language/parse.y"
    {(yyval.val)=newnode(Fentry,newconst(CSTentry,&(yylsp[(1) - (1)])),-1,&(yyloc));;}
    break;

  case 74:

/* Line 1455 of yacc.c  */
#line 169 "../src/language/parse.y"
    {(yyval.val)=newnode(Ffacteurmat,(yyvsp[(1) - (2)].val),(yyvsp[(2) - (2)].val),&(yyloc));;}
    break;

  case 75:

/* Line 1455 of yacc.c  */
#line 170 "../src/language/parse.y"
    {(yyval.val)=newnode(Ftag,(yyvsp[(1) - (3)].val),newconst(CSTentry,&(yylsp[(2) - (3)])),&(yyloc));;}
    break;

  case 76:

/* Line 1455 of yacc.c  */
#line 173 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);;}
    break;

  case 77:

/* Line 1455 of yacc.c  */
#line 174 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmatrixelts,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 78:

/* Line 1455 of yacc.c  */
#line 177 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmatrixlines,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 79:

/* Line 1455 of yacc.c  */
#line 178 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmatrixlines,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 80:

/* Line 1455 of yacc.c  */
#line 181 "../src/language/parse.y"
    {(yyval.val)=newnode(Fvec,-1,-1,&(yyloc));;}
    break;

  case 81:

/* Line 1455 of yacc.c  */
#line 182 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmat,-1,-1,&(yyloc));;}
    break;

  case 82:

/* Line 1455 of yacc.c  */
#line 183 "../src/language/parse.y"
    {(yyval.val)=newnode(Fvec,(yyvsp[(2) - (3)].val),-1,&(yyloc));;}
    break;

  case 83:

/* Line 1455 of yacc.c  */
#line 184 "../src/language/parse.y"
    {(yyval.val)=newnode(Fmat,(yyvsp[(2) - (3)].val),-1,&(yyloc));;}
    break;

  case 84:

/* Line 1455 of yacc.c  */
#line 185 "../src/language/parse.y"
    {(yyval.val)=-1; YYABORT;;}
    break;

  case 85:

/* Line 1455 of yacc.c  */
#line 188 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);;}
    break;

  case 86:

/* Line 1455 of yacc.c  */
#line 189 "../src/language/parse.y"
    {(yyval.val)=newnode(Frefarg,(yyvsp[(2) - (2)].val),-1,&(yyloc));;}
    break;

  case 87:

/* Line 1455 of yacc.c  */
#line 190 "../src/language/parse.y"
    {if (!pari_once) { yyerrok; } pari_once=1;;}
    break;

  case 88:

/* Line 1455 of yacc.c  */
#line 191 "../src/language/parse.y"
    {pari_once=0; (yyval.val)=newopcall(OPcat,(yyvsp[(1) - (4)].val),(yyvsp[(4) - (4)].val),&(yyloc));;}
    break;

  case 89:

/* Line 1455 of yacc.c  */
#line 194 "../src/language/parse.y"
    {(yyval.val)=(yyvsp[(1) - (1)].val);;}
    break;

  case 90:

/* Line 1455 of yacc.c  */
#line 195 "../src/language/parse.y"
    {(yyval.val)=newnode(Flistarg,(yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 91:

/* Line 1455 of yacc.c  */
#line 198 "../src/language/parse.y"
    {(yyval.val)=newnode(Ffunction,newconst(CSTentry,&(yylsp[(1) - (4)])),(yyvsp[(3) - (4)].val),&(yyloc));;}
    break;

  case 92:

/* Line 1455 of yacc.c  */
#line 201 "../src/language/parse.y"
    {(yyval.val)=newnode(Ffunction,newconst(CSTmember,&(yylsp[(3) - (3)])),(yyvsp[(1) - (3)].val),&(yyloc));;}
    break;

  case 93:

/* Line 1455 of yacc.c  */
#line 205 "../src/language/parse.y"
    {(yyval.val)=newfunc(CSTentry,&(yylsp[(1) - (6)]),(yyvsp[(3) - (6)].val),(yyvsp[(6) - (6)].val),&(yyloc));;}
    break;

  case 94:

/* Line 1455 of yacc.c  */
#line 207 "../src/language/parse.y"
    {(yyval.val)=newfunc(CSTmember,&(yylsp[(3) - (5)]),(yyvsp[(1) - (5)].val),(yyvsp[(5) - (5)].val),&(yyloc));;}
    break;

  case 95:

/* Line 1455 of yacc.c  */
#line 208 "../src/language/parse.y"
    {(yyval.val)=newnode(Flambda, (yyvsp[(1) - (3)].val),(yyvsp[(3) - (3)].val),&(yyloc));;}
    break;

  case 96:

/* Line 1455 of yacc.c  */
#line 209 "../src/language/parse.y"
    {(yyval.val)=newnode(Flambda, (yyvsp[(2) - (4)].val),(yyvsp[(4) - (4)].val),&(yyloc));;}
    break;



/* Line 1455 of yacc.c  */
#line 2473 "../src/language/parse.c"
      default: break;
    }
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;
  *++yylsp = yyloc;

  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (&yylloc, lex, YY_("syntax error"));
#else
      {
	YYSIZE_T yysize = yysyntax_error (0, yystate, yychar);
	if (yymsg_alloc < yysize && yymsg_alloc < YYSTACK_ALLOC_MAXIMUM)
	  {
	    YYSIZE_T yyalloc = 2 * yysize;
	    if (! (yysize <= yyalloc && yyalloc <= YYSTACK_ALLOC_MAXIMUM))
	      yyalloc = YYSTACK_ALLOC_MAXIMUM;
	    if (yymsg != yymsgbuf)
	      YYSTACK_FREE (yymsg);
	    yymsg = (char *) YYSTACK_ALLOC (yyalloc);
	    if (yymsg)
	      yymsg_alloc = yyalloc;
	    else
	      {
		yymsg = yymsgbuf;
		yymsg_alloc = sizeof yymsgbuf;
	      }
	  }

	if (0 < yysize && yysize <= yymsg_alloc)
	  {
	    (void) yysyntax_error (yymsg, yystate, yychar);
	    yyerror (&yylloc, lex, yymsg);
	  }
	else
	  {
	    yyerror (&yylloc, lex, YY_("syntax error"));
	    if (yysize != 0)
	      goto yyexhaustedlab;
	  }
      }
#endif
    }

  yyerror_range[0] = yylloc;

  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

      if (yychar <= YYEOF)
	{
	  /* Return failure if at end of input.  */
	  if (yychar == YYEOF)
	    YYABORT;
	}
      else
	{
	  yydestruct ("Error: discarding",
		      yytoken, &yylval, &yylloc, lex);
	  yychar = YYEMPTY;
	}
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  yyerror_range[0] = yylsp[1-yylen];
  /* Do not reclaim the symbols of the rule which action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (yyn != YYPACT_NINF)
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;

      yyerror_range[0] = *yylsp;
      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp, yylsp, lex);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  *++yyvsp = yylval;

  yyerror_range[1] = yylloc;
  /* Using YYLLOC is tempting, but would change the location of
     the lookahead.  YYLOC is available though.  */
  YYLLOC_DEFAULT (yyloc, (yyerror_range - 1), 2);
  *++yylsp = yyloc;

  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined(yyoverflow) || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (&yylloc, lex, YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
     yydestruct ("Cleanup: discarding lookahead",
		 yytoken, &yylval, &yylloc, lex);
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp, yylsp, lex);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  /* Make sure YYID is used.  */
  return YYID (yyresult);
}



/* Line 1675 of yacc.c  */
#line 212 "../src/language/parse.y"


