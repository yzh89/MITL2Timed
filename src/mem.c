/***** ltl2ba : mem.c *****/

/* Written by Denis Oddoux, LIAFA, France                                 */
/* Copyright (c) 2001  Denis Oddoux                                       */
/* Modified by Paul Gastin, LSV, France                                   */
/* Copyright (c) 2007  Paul Gastin                                        */
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
/* Send bug-reports and/or questions to Paul Gastin                       */
/* http://www.lsv.ens-cachan.fr/~gastin                                   */
/*                                                                        */
/* Some of the code in this file was taken from the Spin software         */
/* Written by Gerard J. Holzmann, Bell Laboratories, U.S.A.               */

#include "ltl2ba.h"

#if 1
#define log(e, u, d)	event[e][(int) u] += (long) d;
#else
#define log(e, u, d)
#endif

#define A_LARGE		80
#define A_USER		0x55000000
#define NOTOOBIG	32768

#define POOL		0
#define ALLOC		1
#define FREE		2
#define NREVENT		3

extern	unsigned long All_Mem;
extern	int tl_verbose;

ATrans *atrans_list = (ATrans *)0;
GTrans *gtrans_list = (GTrans *)0;
BTrans *btrans_list = (BTrans *)0;

int aallocs = 0, afrees = 0, apool = 0;
int gallocs = 0, gfrees = 0, gpool = 0;
int ballocs = 0, bfrees = 0, bpool = 0;

// #ifdef TIMED
  TTrans *ttrans_list = (TTrans *)0; //Transition list after been freed. 
  int tallocs = 0, tfrees = 0, tpool = 0, tleft = 0;
// #endif

union M {
	long size;
	union M *link;
};

static union M *freelist[A_LARGE];
static long	req[A_LARGE];
static long	event[NREVENT][A_LARGE];

void *
tl_emalloc(int U)
{	union M *m;
  	long r, u;
	void *rp;

	u = (long) ((U-1)/sizeof(union M) + 2);

	if (u >= A_LARGE)
	{	log(ALLOC, 0, 1);
		if (tl_verbose)
		printf("tl_spin: memalloc %ld bytes\n", u);
		m = (union M *) emalloc((int) u*sizeof(union M));
		All_Mem += (unsigned long) u*sizeof(union M);
	} else
	{	if (!freelist[u])
		{	r = req[u] += req[u] ? req[u] : 1;
			if (r >= NOTOOBIG)
				r = req[u] = NOTOOBIG;
			log(POOL, u, r);
			freelist[u] = (union M *)
				emalloc((int) r*u*sizeof(union M));

			All_Mem += (unsigned long) r*u*sizeof(union M);
			m = freelist[u] + (r-2)*u;

			for ( ; m >= freelist[u]; m -= u)
				m->link = m+u;
		}
		log(ALLOC, u, 1);
		m = freelist[u];
		freelist[u] = m->link;
	}
	m->size = (u|A_USER);

  // printf("ALLOC %d : %x - %x \n", u, m, (&m->size)+u);

	for (r = 1; r < u; )
		(&m->size)[r++] = 0;

	rp = (void *) (m+1);
	memset(rp, 0, U);
	return rp;
}

void
tfree(void *v)
{	union M *m = (union M *) v;
	long u;

	--m;
	if ((m->size&0xFF000000) != A_USER){
    // printf("CORRUPT %x \n", m);
		Fatal("releasing a free block", (char *)0);
  }
  
	u = (m->size &= 0xFFFFFF);
  // printf("FREE %d, %x \n", u, m);
	if (u >= A_LARGE)
	{	log(FREE, 0, 1);
		/* free(m); */
	} else
	{	log(FREE, u, 1);
		m->link = freelist[u];
		freelist[u] = m;
	}
}

ATrans* emalloc_atrans() {
  ATrans *result;
  if(!atrans_list) {
    result = (ATrans *)tl_emalloc(sizeof(GTrans));
    result->pos = new_set(1);
    result->neg = new_set(1);
    result->to  = new_set(0);
    apool++;
  }
  else {
    result = atrans_list;
    atrans_list = atrans_list->nxt;
    result->nxt = (ATrans *)0;
  }
  aallocs++;
  return result;
}

void free_atrans(ATrans *t, int rec) {
  if(!t) return;
  if(rec) free_atrans(t->nxt, rec);
  t->nxt = atrans_list;
  atrans_list = t;
  afrees++;
}

// free every state of unuseful automata
void free_tstate(TState *t, int numOfState){
  for (int i=0; i<numOfState ; i++){
    // printf("Free state:%s\n", t[i].tstateId);
    free(t[i].input);
    free_CGuard(t[i].inv);
    // if (t[i].inv){
    //   printf("Free inv:");
    //   print_CGuard(t[i].inv);
    //   free_CGuard(t[i].inv);
    //   printf("\n");
    // }
    // printf("Free sym ...\n");
    if (t[i].sym!=NULL){
      // print_set(t[i].sym, 3);
      clear_set(t[i].sym, 3);
      tfree(t[i].sym);
      // printf("\n");
    }
    
    free(t[i].tstateId);
  }
  tfree(t);
}


void free_all_atrans() {
  ATrans *t;
  while(atrans_list) {
    t = atrans_list;
    atrans_list = t->nxt;
    tfree(t->to);
    tfree(t->pos);
    tfree(t->neg);
    tfree(t);
  }
}

// #ifdef TIMED
// Allocate ttrans , transNum = the num of the transitions, cNum is the maximum
// clocks on the guards
TTrans* emalloc_ttrans(int transNum) { 
  TTrans *result;
  if(!ttrans_list && transNum!=0) {

    result = (TTrans *)tl_emalloc(sizeof(TTrans));
    TTrans *tmp=result;
    tmp->cIdx = (int *) 0;
    tmp->to = (TState *)0;
    tmp->from = (TState *)0;
    tmp->cguard = (CGuard *)0;
    tpool++;

    tallocs++;

    for (int i=1; i<transNum; i++){
      tmp->nxt = (TTrans *)tl_emalloc(sizeof(TTrans));
      tmp = tmp->nxt;
      tmp->cIdx = (int *) 0;
      tmp->to = (TState *)0;
      tmp->from = (TState *)0;
      tmp->cguard = (CGuard *)0;
      tpool++;
      tallocs++;
    }
    
 }
  else {
    result = ttrans_list;
    result->cIdx = (int *) 0;
    result->to = (TState *)0;
    result->from = (TState *)0;
    result->cguard = (CGuard *)0;
    ttrans_list = ttrans_list->nxt;
    result->nxt = (TTrans *)0;

    // printf("Reusing..%d\n",transNum);
    if (transNum>1) result->nxt = emalloc_ttrans(transNum -1);
    tleft++;

    tallocs++;

  }
  return result;
} 

void free_CGuard(CGuard * cg){
  if (!cg){
    return;
  }else{
    switch (cg->nType){
      case AND:
        free_CGuard(cg->lft);
        free_CGuard(cg->rgt);
        free(cg);
        break;

      case OR:
        free_CGuard(cg->lft);
        free_CGuard(cg->rgt);
        free(cg);
        break;

      case START:
        free(cg->lft->cCstr);
        free(cg->lft);
        free(cg);
        break;

      case STOP:
      {
        free(cg->lft->cCstr);
        free(cg->lft);
        free(cg->rgt->cCstr);
        free(cg->rgt);
        free(cg);
        break;
      }

      case PREDICATE:
        free(cg->cCstr);
        free(cg);
        break;
    }
  }
}

void free_ttrans(TTrans *t, int rec) {
  if(!t) return;
  if(rec>0) free_ttrans(t->nxt, rec);
  // if (t->from!=NULL && t->to!=NULL)
    // printf("Free ttrans: %s, %s\n", t->from->tstateId, t->to->tstateId);
  // else
    // printf("Free header\n");

  if (t->cguard!=NULL && rec==2){
    // printf("Freeing guards:");
    // print_CGuard(t->cguard);
    free_CGuard(t->cguard);
    // printf("\n");
  }
  if (t->cIdx!=NULL){
    // printf("Free clock set:");
    // print_set(t->cIdx,4);
    tfree(t->cIdx);
    // printf("\n");
  }
  // printf("Done..\n");
  t->cIdx = NULL;
  t->cguard = (CGuard *)0;  
  t->to = (TState *)0;
  t->from = (TState *)0;  

  t->nxt = ttrans_list;
  ttrans_list = t;
  tfrees++;
}

void free_ttrans_until(TTrans *t, TTrans *tend){
  if (!t) return;
  if (t==tend){
    return;
  }else{
    free_ttrans_until(t->nxt,tend);
  }
  // if (t->from!=NULL && t->to!=NULL)
    // printf("Free ttrans: %s, %s\n", t->from->tstateId, t->to->tstateId);
  // else
    // printf("Free header\n");
  if (t->cguard!=NULL){
    // printf("Freeing guards:");
    // print_CGuard(t->cguard);
    free_CGuard(t->cguard);
    // printf("\n");
  }
  if (t->cIdx!=NULL){
    // printf("Free clock set:");
    // print_set(t->cIdx,4);
    tfree(t->cIdx);
    // printf("\n");
  }
  // printf("Done..\n");

  t->cguard = (CGuard *)0;
  t->cIdx = NULL;
  t->to = (TState *)0;
  t->from = (TState *)0;  

  t->nxt = ttrans_list;
  ttrans_list = t;
  tfrees++;
}

void free_all_ttrans() {
  TTrans *t;
  while(ttrans_list) {
    t = ttrans_list;
    ttrans_list = t->nxt;
    if (t->cguard!=NULL){
      // printf("Freeing guards:");
      // print_CGuard(t->cguard);
      free_CGuard(t->cguard);
      // printf("\n");
    }
    if (t->cIdx!=NULL){
      tfree(t->cIdx);
    }
    tfree(t);
  }
}

// #endif

GTrans* emalloc_gtrans() {
  GTrans *result;
  if(!gtrans_list) {
    result = (GTrans *)tl_emalloc(sizeof(GTrans));
    result->pos   = new_set(1);
    result->neg   = new_set(1);
    result->final = new_set(0);
    gpool++;
  }
  else {
    result = gtrans_list;
    gtrans_list = gtrans_list->nxt;
  }
  gallocs++;
  return result;
}

void free_gtrans(GTrans *t, GTrans *sentinel, int fly) {
  gfrees++;
  if(sentinel && (t != sentinel)) {
    free_gtrans(t->nxt, sentinel, fly);
    if(fly) t->to->incoming--;
  }
  t->nxt = gtrans_list;
  gtrans_list = t;
}

BTrans* emalloc_btrans() {
  BTrans *result;
  if(!btrans_list) {
    result = (BTrans *)tl_emalloc(sizeof(BTrans));
    result->pos = new_set(1);
    result->neg = new_set(1);
    bpool++;
  }
  else {
    result = btrans_list;
    btrans_list = btrans_list->nxt;
  }
  ballocs++;
  return result;
}

void free_btrans(BTrans *t, BTrans *sentinel, int fly) {
  bfrees++;
  if(sentinel && (t != sentinel)) {
    free_btrans(t->nxt, sentinel, fly);
    if(fly) t->to->incoming--;
  }
  t->nxt = btrans_list;
  btrans_list = t;
}

void
a_stats(void)
{	long	p, a, f;
	int	i;

	printf(" size\t  pool\tallocs\t frees\t reuse\n");

	for (i = 0; i < A_LARGE; i++)
	{	p = event[POOL][i];
		a = event[ALLOC][i];
		f = event[FREE][i];

		if(p|a|f)
		printf("%5d\t%6ld\t%6ld\t%6ld\n",
			i, p, a, f);
	}

	printf("atrans\t%6d\t%6d\t%6d\n", 
	       apool, aallocs, afrees);
	printf("gtrans\t%6d\t%6d\t%6d\n", 
	       gpool, gallocs, gfrees);
	printf("btrans\t%6d\t%6d\t%6d\n", 
	       bpool, ballocs, bfrees);
  printf("ttrans\t%6d\t%6d\t%6d\t%6d\n", 
         tpool, tallocs, tfrees, tleft);
}
