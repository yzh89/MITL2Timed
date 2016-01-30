/***** ltl2ba : ltl2ba.h *****/

/* Written by Denis Oddoux, LIAFA, France                                 */
/* Copyright (c) 2001  Denis Oddoux                                       */
/* Modified by Paul Gastin, LSV, France                                   */
/* Copyright (c) 2007  Paul Gastin                                        */
/* Modified by Yuchen Zhou, College Park, USA                             */
/* Copyright (c) 2015  Yuchen Zhou                                        */
/*                                                                        */
/* This program is free software; you can redistribute it and/or modify   */
/* it under the terms of the GNU General Public License as published by   */
/* the Free Software Foundation; either version 2 of the License, or      */
/* (at your option) any later version.                                    */
/*                                                                        */
/* This program is distributed in the hope that it will be useful,        */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of         */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          */
/* GNU General Public License for more details.                           */
/*                                                                        */
/* You should have received a copy of the GNU General Public License      */
/* along with this program; if not, write to the Free Software            */
/* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA*/
/*                                                                        */
/* Based on the translation algorithm by Gastin and Oddoux,               */
/* presented at the 13th International Conference on Computer Aided       */
/* Verification, CAV 2001, Paris, France.                                 */
/* Proceedings - LNCS 2102, pp. 53-65                                     */
/*                                                                        */
/* Some of the code in this file was taken from the Spin software         */
/* Written by Gerard J. Holzmann, Bell Laboratories, U.S.A.               */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
#include <math.h>

typedef struct Symbol {
char		*name;
	struct Symbol	*next;	/* linked list, symbol table */
} Symbol;

typedef struct Node {
	short		ntyp;	/* node type */
  float intvl[2]; /*interval*/
	struct Symbol	*sym;
	struct Node	*lft;	/* tree */
	struct Node	*rgt;	/* tree */
	struct Node	*nxt;	/* if linked list */
} Node;

typedef struct Graph {
	Symbol		*name;
	Symbol		*incoming;
	Symbol		*outgoing;
	Symbol		*oldstring;
	Symbol		*nxtstring;
	Node		*New;
	Node		*Old;
	Node		*Other;
	Node		*Next;
	unsigned char	isred[64], isgrn[64];
	unsigned char	redcnt, grncnt;
	unsigned char	reachable;
	struct Graph	*nxt;
} Graph;

typedef struct Mapping {
	char	*from;
	Graph	*to;
	struct Mapping	*nxt;
} Mapping;

typedef struct ATrans {
  int *to;
  int *pos;
  int *neg;
  struct ATrans *nxt;
} ATrans;

typedef struct AProd {
  int astate;
  struct ATrans *prod;
  struct ATrans *trans;
  struct AProd *nxt;
  struct AProd *prv;
} AProd;

typedef struct GTrans {
  int *pos;
  int *neg;
  struct GState *to;
  int *final;
  struct GTrans *nxt;
} GTrans;

typedef struct GState {
  int id;
  int incoming;
  int *nodes_set;
  struct GTrans *trans;
  struct GState *nxt;
  struct GState *prv;
} GState;

typedef struct BTrans {
  struct BState *to;
  int *pos;
  int *neg;
  struct BTrans *nxt;
} BTrans;

typedef struct BState {
  struct GState *gstate;
  int id;
  int incoming;
  int final;
  struct BTrans *trans;
  struct BState *nxt;
  struct BState *prv;
} BState;

typedef struct GScc {
  struct GState *gstate;
  int rank;
  int theta;
  struct GScc *nxt;
} GScc;

typedef struct BScc {
  struct BState *bstate;
  int rank;
  int theta;
  struct BScc *nxt;
} BScc;

enum {
	ALWAYS=257,
	AND,		/* 258 */
	EQUIV,		/* 259 */
	EVENTUALLY,	/* 260 */
	FALSE,		/* 261 */
	IMPLIES,	/* 262 */
	NOT,		/* 263 */
	OR,		/* 264 */
	PREDICATE,	/* 265 */
	TRUE,		/* 266 */
	U_OPER,		/* 267 */
	V_OPER		/* 268 */
// #ifdef TIMED
  , U_I,    /*269*/
  V_I,    // 270
  EVENTUALLY_I, /*271*/
  ALWAYS_I /*272 */
// #endif
#ifdef NXT
	, NEXT		/* 273 */
#endif
};

Node	*Canonical(Node *);
Node	*canonical(Node *);
Node	*cached(Node *);
Node	*dupnode(Node *);
Node	*getnode(Node *);
Node	*in_cache(Node *);
Node	*push_negation(Node *);
Node	*right_linked(Node *);
Node	*tl_nn(int, Node *, Node *);

Symbol	*tl_lookup(char *);
Symbol	*getsym(Symbol *);
Symbol	*DoDump(Node *);

char	*emalloc(int);	

int	anywhere(int, Node *, Node *);
int	dump_cond(Node *, Node *, int);
int	isequal(Node *, Node *);
int	tl_Getchar(void);

void	*tl_emalloc(int);
ATrans  *emalloc_atrans();
void    free_atrans(ATrans *, int);
void    free_all_atrans();
GTrans  *emalloc_gtrans();
void    free_gtrans(GTrans *, GTrans *, int);
BTrans  *emalloc_btrans();
void    free_btrans(BTrans *, BTrans *, int);
void	a_stats(void);
void	addtrans(Graph *, char *, Node *, char *);
void	cache_stats(void);
void	dump(Node *);
void	exit(int);
void	Fatal(char *, char *);
void	fatal(char *, char *);
void	fsm_print(void);
void	releasenode(int, Node *);
void	tfree(void *);
void	tl_explain(int);
void	tl_UnGetchar(void);
void	tl_parse(void);
void	tl_yyerror(char *);
void	trans(Node *);

void    mk_alternating(Node *);
void    mk_generalized();
void    mk_buchi();

ATrans *dup_trans(ATrans *);
ATrans *merge_trans(ATrans *, ATrans *);
void do_merge_trans(ATrans **, ATrans *, ATrans *);

int  *new_set(int);
int  *clear_set(int *, int);
int  *make_set(int , int);
void copy_set(int *, int *, int);
int  *dup_set(int *, int);
void merge_sets(int *, int *, int);
void do_merge_sets(int *, int *, int *, int);
int  *intersect_sets(int *, int *, int);
void add_set(int *, int);
void rem_set(int *, int);
void spin_print_set(int *, int*);
void print_set(int *, int);
void set_to_xml(int *, char *);
int  empty_set(int *, int);
int  get_set(int *,int );
int  count_set(int *, int );
int  empty_intersect_sets(int *, int *, int);
int  same_sets(int *, int *, int);
int  included_set(int *, int *, int);
int  in_set(int *, int);
int  *list_set(int *, int);

void put_uform(void);

int timeval_subtract (struct timeval *, struct timeval *, struct timeval *);

#define ZN	(Node *)0
#define ZS	(Symbol *)0
#define Nhash	255    	
#define True	tl_nn(TRUE,  ZN, ZN)
#define False	tl_nn(FALSE, ZN, ZN)
#define Not(a)	push_negation(tl_nn(NOT, a, ZN))
#define rewrite(n)	canonical(right_linked(n))

typedef Node	*Nodeptr;
#define YYSTYPE	 Nodeptr

#define Debug(x)	{ if (0) printf(x); }
#define Debug2(x,y)	{ if (tl_verbose) printf(x,y); }
#define Dump(x)		{ if (0) dump(x); }
#define Explain(x)	{ if (tl_verbose) tl_explain(x); }

#define Assert(x, y)	{ if (!(x)) { tl_explain(y); \
			  Fatal(": assertion failed\n",(char *)0); } }
#define min(x,y)        ((x<y)?x:y)

#define OUT_TYPE_SPIN 0
#define OUT_TYPE_DOT 1
#define OUT_TYPE_GEXF 2

typedef unsigned char byte;

//MITL functions
// #ifdef TIMED
// NULLOUT is the output of prediction checker of the timed automata of <>_I and Gen Input if it is zero
#define NULLOUT 0xffff
typedef struct CCstr{  //clock constraint for invariant and transition
  int cIdx; //clock index associated with the constraint
  unsigned short gType; //type of inequality
  int bndry; //constraint boundary
} CCstr;

typedef struct CGuard{
  int nType; //guard logic tree AND = 258, OR = 264, PREDICATE = 265
  CCstr *cCstr;
  struct CGuard *lft; 
  struct CGuard *rgt;
} CGuard;

typedef struct TState { //Timed automata state
  char *tstateId;   // state id
  int *sym;    //all the node predicates involves
  CGuard *inv;    // invariant condition on the clock
  unsigned short buchi;   //1 or 0 representing if it is buchi state
  unsigned short *input;    // input array for different bool
  unsigned short inputNum;   //number of input
  unsigned short output;   // output
  // struct TState *next; 
} TState;

typedef struct TTrans{  //time automata transitions
  CGuard *cguard;  //guard condition on the clock variables
  int *cIdx; //clocks to be reset
  struct TState *to; 
  struct TState *from;
  struct TTrans *nxt; //linked list for TTrans
} TTrans;

enum {
  LESSEQUAL=5,
  LESS,    /* 6 */
  GREATER,    /* 7 */
  GREATEREQUAL, /* 8 */
  STOP,
  START,
};

typedef struct TAutomata{
  TTrans* tTrans;
  TState* tStates;
  int stateNum;
  int eventNum;
  TTrans* tEvents; //start of the tEvents transitions
} TAutomata;

  float *tl_GetIntvl(float *);
  Node  *tl_nn_t(int, Node *, Node *,float *);
  TTrans* emalloc_ttrans(int);
  void free_ttrans(TTrans *, int );
  void free_all_ttrans();
  void mk_timed(Node *);
  int calculate_sym_size(Node *);
  void print_CGuard(CGuard *);
  void free_CGuard(CGuard *);

  void free_ttrans_until(TTrans *, TTrans *);
  void free_tstate(TState *, int);

// #endif
