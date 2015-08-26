/***** MITL2Timed : timed.c *****/
/* Written by Yuchen Zhou, College Park, USA                              */
/* Copyright (c) 2015  Yuchen Zhou                                        */
/* Based on alternative.c from ltl2ba written by Paul Gastin and Denis    */
/* Oddoux, France                                                         */
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
// #ifdef TIMED
#include "ltl2ba.h"

/********************************************************************\
|*              Structures and shared variables                     *|
\********************************************************************/

extern FILE *tl_out;
extern int tl_verbose, tl_stats, tl_simp_diff;

// Node **t_label;
char **t_sym_table;
TAutomata *tAutomata;
// TTrans **t_transition; //array of timed automata transitions
int cCount; //clock count
// int ttrans_count = 0;
int t_sym_size, t_sym_id = 0, t_node_size, t_clock_size;
// struct rusage tr_debut, tr_fin;
// struct timeval t_diff;
// int *final_set, node_id = 1, sym_id = 0, node_size, sym_size;
// int astate_count = 0, atrans_count = 0; 

// ATrans *build_alternating(Node *p);
void merge_bin_timed(TAutomata *t1, TAutomata *t2, TAutomata *t, TAutomata *out);
void merge_timed(TAutomata *t1,TAutomata *t, TAutomata *out);
void merge_event_timed(TAutomata *, TAutomata *, TAutomata *, TAutomata *);
void print_timed(TAutomata *t);
void print_sub_formula(Node *n, char* subform);
/********************************************************************\
|*              Generation of the timed automata                    *|
\********************************************************************/

// int t_calculate_node_size(Node *p) /* returns the number of temporal nodes */
// {
//   switch(p->ntyp) {
//   case AND:
//   case OR:
//     return(t_calculate_node_size(p->lft) + t_calculate_node_size(p->rgt)+ 1);
//   case U_OPER:
//   case V_OPER:
//     return(t_calculate_node_size(p->lft) + t_calculate_node_size(p->rgt) + 4);
// #ifdef NXT
//   case NEXT:
//     return(t_calculate_node_size(p->lft) + 2);
// #endif
//   default:
//     return 1;
//     break;
//   }
// }


int t_calculate_clock_size(Node *p) /* returns the number of clocks needed */
{
  switch(p->ntyp) {
  case AND:
  case OR:
    return(t_calculate_clock_size(p->lft) + t_calculate_clock_size(p->rgt)+ 1);
  case NOT:
    return(t_calculate_clock_size(p->lft) + 1);
  case PREDICATE:
    return 1;
  case U_OPER:
  case V_OPER:
    return(t_calculate_clock_size(p->lft) + t_calculate_clock_size(p->rgt) + 1);
#ifdef NXT
  case NEXT:
    return(t_calculate_clock_size(p->lft) + 1);
#endif
  case EVENTUALLY_I:{
    float d = p->intvl[1] - p->intvl[0];
    short m = ceil(p->intvl[1]/d) + 1;
    return(t_calculate_clock_size(p->lft) + 2*m + 1);
  }
  default:
    return 0;
    break;
  }
}

int t_calculate_sym_size(Node *p) /* returns the number of predicates */
{
  switch(p->ntyp) {
  case AND:
  case OR:
  case U_OPER:
  case V_OPER:
    return(calculate_sym_size(p->lft) + calculate_sym_size(p->rgt));
#ifdef NXT
  case NEXT:
    return(calculate_sym_size(p->lft));
#endif
  case EVENTUALLY_I:
    return(calculate_sym_size(p->lft) + 1);
  case NOT:
  case PREDICATE:
    return 1;
  default:
    return 0;
  }
}

// During the input output merge duplicate a ttrans (1)
// TTrans *dup_ttrans(TTrans *trans)   
// {
//   TTrans *result;
//   if(!trans) return trans;
//   result = emalloc_ttrans(1,1);
//   return result;
// }

// void do_merge_trans(ATrans **result, ATrans *trans1, ATrans *trans2) 
// { /* merges two transitions */
//   if(!trans1 || !trans2) {
//     free_atrans(*result, 0);
//     *result = (ATrans *)0;
//     return;
//   }
//   if(!*result)
//     *result = emalloc_atrans();
//   do_merge_sets((*result)->to, trans1->to,  trans2->to,  0);
//   do_merge_sets((*result)->pos, trans1->pos, trans2->pos, 1);
//   do_merge_sets((*result)->neg, trans1->neg, trans2->neg, 1);
//   if(!empty_intersect_sets((*result)->pos, (*result)->neg, 1)) {
//     free_atrans(*result, 0);
//     *result = (ATrans *)0;
//   }
// }

// ATrans *merge_trans(ATrans *trans1, ATrans *trans2) /* merges two transitions */
// {
//   ATrans *result = emalloc_atrans();
//   do_merge_trans(&result, trans1, trans2);
//   return result;
// }

// int already_done(Node *p) /* finds the id of the node, if already explored */
// {
//   int i;
//   for(i = 1; i<node_id; i++) 
//     if (isequal(p, label[i])) 
//       return i;
//   return -1;
// }

int t_get_sym_id(char *s) /* finds the id of a predicate, or attributes one */
{
  int i;
  for(i=0; i<t_sym_id; i++) 
    if (!strcmp(s, t_sym_table[i])) 
      return i;
  t_sym_table[t_sym_id] = (char *) malloc(sizeof(char)*(strlen(s)+1));
  strcpy(t_sym_table[t_sym_id], s);
  return t_sym_id++;
}

// ATrans *boolean(Node *p) /* computes the transitions to boolean nodes -> next & init */
// {
//   ATrans *t1, *t2, *lft, *rgt, *result = (ATrans *)0;
//   int id;
//   switch(p->ntyp) {
//   case TRUE:
//     result = emalloc_atrans();
//     clear_set(result->to,  0);
//     clear_set(result->pos, 1);
//     clear_set(result->neg, 1);
//   case FALSE:
//     break;
//   case AND:
//     lft = boolean(p->lft);
//     rgt = boolean(p->rgt);
//     for(t1 = lft; t1; t1 = t1->nxt) {
//       for(t2 = rgt; t2; t2 = t2->nxt) {
// 	ATrans *tmp = merge_trans(t1, t2);
// 	if(tmp) {
// 	  tmp->nxt = result;
// 	  result = tmp;
// 	}
//       }
//     }
//     free_atrans(lft, 1);
//     free_atrans(rgt, 1);
//     break;
//   case OR:
//     lft = boolean(p->lft);
//     for(t1 = lft; t1; t1 = t1->nxt) {
//       ATrans *tmp = dup_trans(t1);
//       tmp->nxt = result;
//       result = tmp;
//     }
//     free_atrans(lft, 1);
//     rgt = boolean(p->rgt);
//     for(t1 = rgt; t1; t1 = t1->nxt) {
//       ATrans *tmp = dup_trans(t1);
//       tmp->nxt = result;
//       result = tmp;
//     }
//     free_atrans(rgt, 1);
//     break;
//   default:
//     build_alternating(p);
//     result = emalloc_atrans();
//     clear_set(result->to,  0);
//     clear_set(result->pos, 1);
//     clear_set(result->neg, 1);
//     add_set(result->to, already_done(p));
//   }
//   return result;
// }

void create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p){
  s->tstateId = tstateId;
  s->inv = inv;

  s->buchi = buchi;
  
  s->input = input;
  s->inputNum = inputNum;
  s->output = output;  //output true
  if (p){
    if (p->lft){
      char buff[40];
      buff[0] = '\0';
      print_sub_formula(p, buff);
      s->tstateId = (char *) realloc(s->tstateId, sizeof(char)*(strlen(s->tstateId) +strlen(buff)+3));
      strcat(s->tstateId, ": ");
      strcat(s->tstateId, buff);
      s->sym = new_set(3);
      clear_set(s->sym, 3);
      add_set(s->sym, t_get_sym_id(buff));
      if (output ==1) s->input[0] = 1 << t_get_sym_id(buff);
    }else{
      s->sym = new_set(3); //3 is symolic set. sym_set_size is used to determine the allocation size
      clear_set(s->sym, 3);
      add_set(s->sym, t_get_sym_id(p->sym->name));
    }
  }
}

void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to){
  t->cguard=cguard;
  t->cIdx = new_set(4);
  clear_set(t->cIdx, 4);
  for (int i=0; i<clockNum ; i++){
    add_set(t->cIdx, cIdxs[i]);
  }
  t->cguard = cguard;
  t->from = from;
  t->to = to;
}

TAutomata *build_timed(Node *p) /* builds an timed automaton for p */
{

   TAutomata *t1, *t2;
  
   TTrans *t = (TTrans *)0, *tmp, *tC = (TTrans *)0, *tG = (TTrans *)0;
   TState *s, *sC, *sG;
   TAutomata *tA, *tB;
   TAutomata *tOut;
//   int node = already_done(p);
//   if(node >= 0) return transition[node];


  switch (p->ntyp) {

    char *stateName;
    unsigned short *input;
    CGuard *cguard;
    int *clockId;

    case TRUE:
      s = (TState *) tl_emalloc(sizeof(TState)*1);
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(s, "T", (CGuard *) 0, (unsigned short*) 0, 0, 1, 1, NULL); //output true

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = (TTrans *)0;
      tA->tStates = s;
      tA->stateNum = 1;
      tA->eventNum = 0;
      tA->tEvents = NULL;
      break;

    case FALSE:
      s = (TState *) tl_emalloc(sizeof(TState)*1);
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(s, "F", (CGuard *) 0, (unsigned short*) 0, 0, 0, 1, NULL); //output true

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = (TTrans *)0;
      tA->tStates = s;
      tA->stateNum = 1;
      tA->eventNum = 0;
      tA->tEvents = NULL;
      break;

    case PREDICATE:
      t = emalloc_ttrans(2,1);  //2 states and 1 clock
      s = (TState *) tl_emalloc(sizeof(TState)*2);

      stateName= (char *) malloc (sizeof(char)*(strlen(p->sym->name))+4);
      sprintf(stateName, "p(%s)", p->sym->name);
      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 1 << t_get_sym_id(p->sym->name);
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(s, stateName, (CGuard *) 0, input, 1, 1, 1, p); //output true when p is true

      stateName= (char *) malloc (sizeof(char)*(strlen(p->sym->name))+5);
      sprintf(stateName, "!p(%s)", p->sym->name);
      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[1], stateName, (CGuard *) 0, input, 1, 0, 1, p); //output false when p is false
      
      tmp=t;
      // (0 -> 1) : z > 0 | z := 0
      cguard = (CGuard *) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr *)(CCstr * )  malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[0],  &s[1]);

      tmp = tmp->nxt;

      // (1 -> 0) : z > 0 | z := 0
      cguard = (CGuard *) (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr *)(CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[1],  &s[0]);

      cCount++;

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = t;
      tA->tStates = s;
      tA->stateNum = 2;
      tA->eventNum = 0;
      tA->tEvents = NULL;
      break;

    case NOT:
      t1 = build_timed(p->lft);

      t = emalloc_ttrans(2,1);  //2 states 2 transitions and 1 clock
      s = (TState *) tl_emalloc(sizeof(TState)*2);

      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b1;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(s, "p", (CGuard *) 0, input, 1, 0, 1, NULL); //output false when p is true

      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b0;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[1], "!p", (CGuard *) 0, input, 1, 1, 1, NULL); //output true when p is false
      
      tmp=t;
      // (0 -> 1) : z > 0 | z := 0
      cguard = (CGuard *) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr *)(CCstr * )  malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[0],  &s[1]);

      tmp = tmp->nxt;

      // (1 -> 0) : z > 0 | z := 0
      cguard = (CGuard *) (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr *)(CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[1],  &s[0]);

      cCount++;

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = t;
      tA->tStates = s;
      tA->stateNum = 2;
      tOut = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      merge_timed(t1,tA,tOut);

      // TOOD: free t1 tA
      tA = tOut;
      break;

  // #ifdef NXT
  //   case NEXT:                                            
  //     t = boolean(p->lft);
  //     break;
  // #endif
    case V_OPER:  // NOT ((NOT p) U (NOT q))
      t1= build_timed(p->lft);
      t2= build_timed(p->rgt);

      //create timed automata with 8 transition and 1 clock;
      t = emalloc_ttrans(8,1); 
      s = (TState *) tl_emalloc(sizeof(TState)*4);

      input = (unsigned short *) malloc(sizeof(unsigned short)*2);
      input[0] = 0b10;
      input[1] = 0b11;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[0], "p", (CGuard *) 0, input, 2, 1, 1, NULL); //output 1 in p state

      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b01;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[1], "!(!pq)", (CGuard *) 0, input, 1, 1, 1, NULL); //output 1 in !(!pq) state

      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b01;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[2], "!pq", (CGuard *) 0, input, 1, 0, 0, NULL); //output 0 in !pq state


      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b00;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[3], "!p!q", (CGuard *) 0, input, 1, 0, 1, NULL); //output 0 in !p!q state

      tmp=t;
      // (0 -> 1) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[0],  &s[1]);

      tmp = tmp->nxt;

      // (1 -> 0) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[1],  &s[0]);

      tmp = tmp->nxt;

      // (0 -> 2) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[0],  &s[2]);
      
      tmp = tmp->nxt;

      // (0 -> 3) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[0],  &s[3]);

      tmp = tmp->nxt;

      // (3 -> 0) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[3],  &s[0]);

      tmp = tmp->nxt;

      // (2 -> 3) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[2],  &s[3]);

      tmp = tmp->nxt;

      // (3 -> 2) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[3],  &s[2]);

      tmp = tmp->nxt;

      // (3 -> 1) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[3],  &s[1]);

      cCount++;

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = t;
      tA->tStates = s;
      tA->stateNum = 4;
      tOut = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      merge_bin_timed(t1,t2,tA,tOut);
      // TODO: free tA, t1, t2 (9)
      tA = tOut;
      break;

    case U_OPER: 
      t1= build_timed(p->lft);
      t2= build_timed(p->rgt);

      //create timed automata with 8 transition and 1 clock;
      t = emalloc_ttrans(8,1); 
      s = (TState *) tl_emalloc(sizeof(TState)*4);

      input = (unsigned short *) malloc(sizeof(unsigned short)*2);
      input[0] = 0b01;
      input[1] = 0b00;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[0], "!p", (CGuard *) 0, input, 2, 0, 1, NULL); //output 0 in !p state

      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b10;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[1], "!(p!q)", (CGuard *) 0, input, 1, 0, 1, NULL); //output 0 in !(p!q) state

      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b10;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[2], "p!q", (CGuard *) 0, input, 1, 1, 0, NULL); //output 1 in p!q state


      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b11;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[3], "pq", (CGuard *) 0, input, 1, 1, 1, NULL); //output 1 in pq state

      tmp=t;
      // (0 -> 1) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[0],  &s[1]);

      tmp = tmp->nxt;

      // (1 -> 0) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[1],  &s[0]);

      tmp = tmp->nxt;

      // (0 -> 2) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[0],  &s[2]);
      
      tmp = tmp->nxt;

      // (0 -> 3) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[0],  &s[3]);

      tmp = tmp->nxt;

      // (3 -> 0) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[3],  &s[0]);

      tmp = tmp->nxt;

      // (2 -> 3) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[2],  &s[3]);

      tmp = tmp->nxt;

      // (3 -> 2) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[3],  &s[2]);

      tmp = tmp->nxt;

      // (3 -> 1) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[3],  &s[1]);

      cCount++;

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = t;
      tA->tStates = s;
      tA->stateNum = 4;
      tOut = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      merge_bin_timed(t1,t2,tA,tOut);
      // TODO: free tA, t1, t2 (9)
      tA = tOut;
      break;

    case EVENTUALLY_I: {
      t1= build_timed(p->lft);

      //create prediction generator with 2m transition and 2m clock;
      // TODO: how to add the clock reset beyond b (3)
      // TODO: add initial node for eventually automata (3)
      float d = p->intvl[1] - p->intvl[0];
      short m = ceil(p->intvl[1]/d) + 1;
      tG = emalloc_ttrans(2*m,1); 
      sG = (TState *) tl_emalloc(sizeof(TState)*2*m);

      for (int i =0; i< m; i++){
        // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
        
        stateName= (char *) malloc (sizeof(char)*(strlen("Gen_"))+3);
        sprintf(stateName, "Gen_%d", 2*i+1);

        input = (unsigned short *) malloc(sizeof(unsigned short)*1);
        create_tstate(&sG[0+i*2], stateName, (CGuard *) 0, input, 1, 0, 1, p); //output 0 first stage

        stateName= (char *) malloc (sizeof(char)*(strlen("Gen_"))+3);
        sprintf(stateName, "Gen_%d", 2*i+2);
        input = (unsigned short *) malloc(sizeof(unsigned short)*1);    
        // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
        create_tstate(&sG[1+i*2], stateName, (CGuard *) 0, input, 1, 1, 1, p); //output 1 in second stage
      }
      
      tmp=tG;
      for (int i = 0; i < m; i++){
        
        // (2*i -> 2*i+1) :  * | yi (2i+1):= 0
        cguard = (CGuard*) 0;
        //reset which clock
        clockId = (int *) malloc(sizeof(int)*1);
        clockId[0] = cCount+i*2+1;
        // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
        create_ttrans(tmp, cguard, clockId, 1, &sG[2*i],  &sG[2*i+1]);

        tmp = tmp->nxt;

        // (2*i+1 -> 2*i+2) :  yi>=b-a | x_i+1 (2i+2):= 0 for i!=m-1
        // (2*m-1 -> 0) :  yi>=b-a | x_0 (0):= 0 for i = m-1
        cguard = (CGuard*) malloc(sizeof(CGuard)); 
        cguard->nType = PREDICATE;  
        cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
        cguard->cCstr->cIdx = cCount+i*2+1;
        cguard->cCstr->gType = GREATEREQUAL; 
        cguard->cCstr->bndry = d;

        if (i != m-1){
          
          //reset which clock
          clockId = (int *) malloc(sizeof(int)*1);
          clockId[0] = cCount+i*2+2;
          // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
          create_ttrans(tmp, cguard, clockId, 1, &sG[2*i+1],  &sG[2*i+2]);

          tmp = tmp->nxt;

        } else {

          //reset which clock
          clockId = (int *) malloc(sizeof(int)*1);
          clockId[0] = cCount;
          // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
          create_ttrans(tmp, cguard, clockId, 1, &sG[2*i+1],  &sG[0]);

          tmp = tmp->nxt;
        }

      }

      // prediction checker
      tC = emalloc_ttrans(4*m,1); 
      sC = (TState *) tl_emalloc(sizeof(TState)*(3*m));

      for (int i = 0; i < m; i++){
        // s1 (!p: *) -- y1 < b
        stateName= (char *) malloc (sizeof(char)*(strlen("CHK_")+3));
        sprintf(stateName, "CHK_%d", 3*i+1);
        input = (unsigned short *) malloc(sizeof(unsigned short)*1);
        input[0] = 0;
        cguard = (CGuard *) malloc(sizeof(CGuard)); 
        cguard->nType = PREDICATE;  
        cguard->cCstr = (CCstr *) malloc(sizeof(CCstr));
        cguard->cCstr->cIdx = cCount+2*i+1;
        cguard->cCstr->gType = LESS; 
        cguard->cCstr->bndry = p->intvl[1];
        // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
        create_tstate(&sC[0+3*i], stateName, cguard, input, 1, NULLOUT, 1, p); //output * in s1 state

        //s2 (p: *) -- *
        stateName= (char *) malloc (sizeof(char)*(strlen("CHK_")+3));
        sprintf(stateName, "CHK_%d", 3*i+2);
        input = (unsigned short *) malloc(sizeof(unsigned short)*1);
        input[0] = 1;
        // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
        create_tstate(&sC[1+3*i], stateName, (CGuard *) 0, input, 1, NULLOUT, 1, p); //output 0 in s2 state

        //s3 (!p: *) -- z < d
        stateName= (char *) malloc (sizeof(char)*(strlen("CHK_")+3));
        sprintf(stateName, "CHK_%d", 3*i+3);
        input = (unsigned short *) malloc(sizeof(unsigned short)*1);
        input[0] = 0;
        cguard = (CGuard *) malloc(sizeof(CGuard)); 
        cguard->nType = PREDICATE;  
        cguard->cCstr = (CCstr *) malloc(sizeof(CCstr));
        cguard->cCstr->cIdx = cCount+2*m; // z clock is 2*m
        cguard->cCstr->gType = LESS; 
        cguard->cCstr->bndry = d;
        // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
        create_tstate(&sC[2+3*i], stateName, cguard, input, 1, NULLOUT, 1, p); //output * in s3 state
      }

      tmp=tC;

      for (int i = 0; i < m; i++){
        
        // (3*i -> 3*i+1) :  yi >=b | *
        cguard = (CGuard*) malloc(sizeof(CGuard)); 
        cguard->nType = PREDICATE;  
        cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
        cguard->cCstr->cIdx = cCount+2*i+1;
        cguard->cCstr->gType = GREATEREQUAL; 
        cguard->cCstr->bndry = p->intvl[1];
        //reset which clock
        clockId = (int *) 0;
        // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
        create_ttrans(tmp, cguard, clockId, 0, &sC[3*i],  &sC[3*i+1]);

        tmp = tmp->nxt;

        if (i != m-1){
          // (3*i+1 -> 3*i+3) :  xi+1>=a | * for i!=m-1
          cguard = (CGuard*) malloc(sizeof(CGuard)); 
          cguard->nType = PREDICATE;  
          cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
          cguard->cCstr->cIdx = cCount+i*2+2;
          cguard->cCstr->gType = GREATEREQUAL; 
          cguard->cCstr->bndry = p->intvl[0];
          //reset which clock
          clockId = (int *) 0;
          // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
          create_ttrans(tmp, cguard, clockId, 0, &sC[3*i+1],  &sC[3*i+3]);

        } else {

          // (3*m-2 -> 0) :  x1>=a | * for i = m-1
          cguard = (CGuard*) malloc(sizeof(CGuard)); 
          cguard->nType = PREDICATE;  
          cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
          cguard->cCstr->cIdx = cCount;
          cguard->cCstr->gType = GREATEREQUAL; 
          cguard->cCstr->bndry = p->intvl[0];
          //reset which clock
          clockId = (int *) 0;
          // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
          create_ttrans(tmp, cguard, clockId, 0, &sC[3*i+1],  &sC[0]);

        }

        tmp = tmp->nxt;

        // (3*i+1 -> 3*i+2) :  * | z (2m):= 0 
        cguard = (CGuard*) 0;
        //reset which clock
        clockId = (int *) malloc(sizeof(int)*1);
        clockId[0] = cCount+2*m;
        // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
        create_ttrans(tmp, cguard, clockId, 1, &sC[3*i+1],  &sC[3*i+2]);

        tmp = tmp->nxt;

        // (3*i+2 -> 3*i+1) :  * | *
        cguard = (CGuard*) 0;
        //reset which clock
        clockId = (int *) 0;
        // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
        create_ttrans(tmp, cguard, clockId, 0, &sC[3*i+2],  &sC[3*i+1]);

        tmp = tmp->nxt;
      }

      cCount += 2*m + 1;

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = tG;
      tA->tStates = sG;
      tA->stateNum = 2*m;

      tB = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tB->tTrans = tC;
      tB->tStates = sC;
      tB->stateNum = 3*m;
      
      tOut = (TAutomata *) tl_emalloc(sizeof(TAutomata));

      merge_event_timed(t1,tA,tB,tOut);
      // TODO: free tA, tB, t1 (9)
      tA = tOut;
      break;
    }

    case AND:
      t1= build_timed(p->lft);
      t2= build_timed(p->rgt);

      t = emalloc_ttrans(2,1); 
      s = (TState *) tl_emalloc(sizeof(TState)*2);


      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b11;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[0], "and", (CGuard *) 0, input, 1, 1, 1, NULL); //output 1 in pq state

      input = (unsigned short *) malloc(sizeof(unsigned short)*3);
      input[0] = 0b10;
      input[1] = 0b01;
      input[2] = 0b00;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[1], "! and", (CGuard *) 0, input, 3, 0, 1, NULL); //output 0 in other state

      tmp=t;
      // (0 -> 1) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[0],  &s[1]);

      tmp = tmp->nxt;

      // (1 -> 0) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[1],  &s[0]);

      cCount++;

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = t;
      tA->tStates = s;
      tA->stateNum = 2;

      tOut = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      merge_bin_timed(t1,t2,tA,tOut);
      // TODO: free tA, t1, t2 (9)
      tA = tOut;
      break;

    case OR:
      t1= build_timed(p->lft);
      t2= build_timed(p->rgt);

      t = emalloc_ttrans(2,1); 
      s = (TState *) tl_emalloc(sizeof(TState)*2);

      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b00;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[0], "or", (CGuard *) 0, input, 1, 0, 1, NULL); //output 0 in !p!q state

      input = (unsigned short *) malloc(sizeof(unsigned short)*3);
      input[0] = 0b10;
      input[1] = 0b01;
      input[2] = 0b11;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
      create_tstate(&s[1], "! or", (CGuard *) 0, input, 3, 1, 1, NULL); //output 1 in other state
 
      tmp=t;
      // (0 -> 1) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[0],  &s[1]);

      tmp = tmp->nxt;

      // (1 -> 0) : z > 0 | z := 0
      cguard = (CGuard*) malloc(sizeof(CGuard)); 
      cguard->nType = PREDICATE;  
      cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
      cguard->cCstr->cIdx = cCount;
      cguard->cCstr->gType = GREATER; 
      cguard->cCstr->bndry = 0;
      //reset which clock
      clockId = (int *) malloc(sizeof(int)*1);
      clockId[0] = cCount;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[1],  &s[0]);

      cCount++;

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = t;
      tA->tStates = s;
      tA->stateNum = 2;

      tOut = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      merge_bin_timed(t1,t2,tA,tOut);
      // free tA
      tA = tOut;
      break;

    default:
      break;
  }

  // t_transition[ttrans_count] = t;
  // t_label[ttrans_count++] = p; 
  return(tA);
}

// TODO: simplify invariants if they are looking at same clock (4)
void merge_inv(CGuard *target, CGuard *lft, CGuard *rgt, CGuard *top){
  if (lft && rgt && top) {
    target->nType = AND;
    target->cCstr = (CCstr *)0;
    target->lft = (CGuard*) malloc(sizeof(CGuard));
    target->lft->nType = AND;
    target->lft->cCstr = (CCstr *)0;
    target->lft->lft = lft;
    target->lft->rgt = rgt;
    target->rgt = top;
  }else if (lft && rgt){
    target->nType = AND;
    target->cCstr = (CCstr *)0;
    target->lft = lft;
    target->rgt = rgt;
  }else if (lft && top){
    target->nType = AND;
    target->cCstr = (CCstr *)0;
    target->lft = lft;
    target->rgt = top;
  }else if (rgt && top){
    target->nType = AND;
    target->cCstr = (CCstr *)0;
    target->lft = rgt;
    target->rgt = top;
  }else if (lft){
    target->nType = lft->nType;
    target->cCstr = lft->cCstr;
    target->lft = lft->lft;
    target->rgt = lft->rgt;
  }else if (rgt){
    target->nType = rgt->nType;
    target->cCstr = rgt->cCstr;
    target->lft = rgt->lft;
    target->rgt = rgt->rgt;
  }else if (top){
    target->nType = top->nType;
    target->cCstr = top->cCstr;
    target->lft = top->lft;
    target->rgt = top->rgt;
  }
}

/********************************************************************\
|*             Linking the Timed Automata                           *|
\********************************************************************/

void merge_ttrans(TTrans *t1, TTrans *t2, TTrans *tt, TTrans *tOut, TState *from, TState *to){
  if (t1 && t2 && tt){
    tOut->cIdx = new_set(4);
    clear_set(tOut->cIdx, 4);
    do_merge_sets(tOut->cIdx, t1->cIdx,t2->cIdx,4);
    merge_sets(tOut->cIdx, tt->cIdx,4);
    
    if (!t1->cguard && !t2->cguard && !tt->cguard){
      tOut->cguard = (CGuard *) 0;
    }else{
      tOut->cguard = (CGuard *) malloc(sizeof(CGuard));
      merge_inv(tOut->cguard, t1->cguard, t2->cguard, tt->cguard);
    }
  }else if (t1 && tt) {
    tOut->cIdx = new_set(4);
    clear_set(tOut->cIdx, 4);
    do_merge_sets(tOut->cIdx, t1->cIdx,tt->cIdx,4);

    if (!t1->cguard && !tt->cguard){
      tOut->cguard = (CGuard *) 0;
    }else{
      tOut->cguard = (CGuard *) malloc(sizeof(CGuard));
      merge_inv(tOut->cguard, t1->cguard, NULL, tt->cguard);
    }
  }else if (t2 && tt) {
    tOut->cIdx = new_set(4);
    clear_set(tOut->cIdx, 4);
    do_merge_sets(tOut->cIdx, t2->cIdx,tt->cIdx,4);

    if (!t2->cguard && !tt->cguard){
      tOut->cguard = (CGuard *) 0;
    }else{
      tOut->cguard = (CGuard *) malloc(sizeof(CGuard));
      merge_inv(tOut->cguard, t2->cguard, NULL, tt->cguard);
    }
  }else if (t1) {
    tOut->cIdx = dup_set(t1->cIdx, 4);

    if (!t1->cguard){
      tOut->cguard = (CGuard *) 0;
    }else{
      tOut->cguard = (CGuard *) malloc(sizeof(CGuard));
      merge_inv(tOut->cguard, t1->cguard, NULL, NULL);
    }
  }else if (t2){
    tOut->cIdx = dup_set(t2->cIdx, 4);

    if (!t2->cguard){
      tOut->cguard = (CGuard *) 0;
    }else{
      tOut->cguard = (CGuard *) malloc(sizeof(CGuard));
      merge_inv(tOut->cguard, t2->cguard, NULL, NULL);
    }
  }else{
    printf("ERROR! in merge_ttrans!");
  }
  tOut->from = from;
  tOut->to = to;
}

void print_sub_formula(Node *n, char* subform) {
  if (!n) return;
  char buff[40];
  buff[0] = '\0';

  switch(n->ntyp) {
  case OR:  
    strcat(subform, "("); 
    print_sub_formula(n->lft, subform);
    strcat(subform, " || "); 
    print_sub_formula(n->rgt, subform);
    strcat(subform, ")");
    break;
  case AND:
    strcat(subform, "(");
    print_sub_formula(n->lft, subform);
    strcat(subform, " && ");
    print_sub_formula(n->rgt, subform);
    strcat(subform, ")");
    break;
  case U_OPER:
    strcat(subform, "(");
    print_sub_formula(n->lft, subform);
    strcat(subform, " U ");
    print_sub_formula(n->rgt, subform);
    strcat(subform, ")");
    break;
  case V_OPER:
    strcat(subform, "(");
    print_sub_formula(n->lft, subform);
    strcat(subform, " V ");
    print_sub_formula(n->rgt, subform);
    strcat(subform, ")");
    break;
#ifdef NXT
  case NEXT:
    strcat(subform, "X");
    strcat(subform, " (");
    print_sub_formula(n->lft, subform);
    strcat(subform, ")");
    break;
#endif
// #ifdef TIMED
  case EVENTUALLY_I:
    strcat(subform, "<>_I");
    strcat(subform, " (");
    print_sub_formula(n->lft, subform);
    strcat(subform, ")");
    break;
// #endif
  case NOT:
    strcat(subform, "!");
    strcat(subform, " (");
    print_sub_formula(n->lft, subform);
    strcat(subform, ")");
    break;
  case FALSE:
    strcat(subform, "false");
    break;
  case TRUE:
    strcat(subform, "true");
    break;
  case PREDICATE:
    sprintf(buff, "%s", n->sym->name);
    strcat(subform, buff);
    break;
  case -1:
    strcat(subform, " D ");
    break;
  default:
    printf("Unknown token: ");
    tl_explain(n->ntyp);
    break;
  }
}

void merge_event_timed(TAutomata *t1, TAutomata *tB, TAutomata *tA, TAutomata *out){
  // tB is the generator and tA is the checker. t1 is the subformula automata
  // merge the input automata with the checker and generate new output from generator
  merge_timed(t1, tA, out);

  const int numOfState = out->stateNum + tB->stateNum;

  TState *s = (TState *) tl_emalloc(sizeof(TState)*numOfState);

  // copy state in tB to tOut->state
  for (int i=0; i< tB->stateNum; i++){
    create_tstate(&s[i], tB->tStates[i].tstateId, tB->tStates[i].inv, tB->tStates[i].input, tB->tStates[i].inputNum, tB->tStates[i].output, tB->tStates[i].buchi, NULL);
    if (s[i].output != NULLOUT){
      s[i].sym = dup_set(tB->tStates[0].sym, 3);
    }
  }


  // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p)
  for (int i=0; i < out->stateNum; i++){
    create_tstate(&s[tB->stateNum+i], out->tStates[i].tstateId, out->tStates[i].inv, out->tStates[i].input, out->tStates[i].inputNum, out->tStates[i].output, out->tStates[i].buchi, NULL);
    if (s[tB->stateNum+i].output == NULLOUT && out->tStates[i].sym == NULL){
      s[tB->stateNum+i].sym = dup_set(t1->tStates[0].sym, 3);
      // s[tB->stateNum+i].sym = new_set(3);
      // clear_set(s[tB->stateNum+i].sym , 3);
      // do_merge_sets(s[tB->stateNum+i].sym , tA->tStates[0].sym, t1->tStates[0].sym, 3);
    }else if (s[tB->stateNum+i].output == NULLOUT){
       s[tB->stateNum+i].sym = dup_set(out->tStates[i].sym, 3); 
    }
  }

  TTrans *tt = tB->tTrans;
  while (tt->nxt) {
    tt->to = &s[tt->to - &tB->tStates[0]];
    tt->from = &s[tt->from - &tB->tStates[0]];
    tt = tt->nxt;
  }
  tt->to = &s[tt->to - &tB->tStates[0]];
  tt->from = &s[tt->from - &tB->tStates[0]];

  tt->nxt = out->tTrans;
  out->tEvents = tt->nxt;
  tt = tt->nxt;
  while (tt->nxt) {
    tt->to = &s[tB->stateNum + tt->to-&out->tStates[0]];
    tt->from = &s[tB->stateNum + tt->from-&out->tStates[0]];
    tt = tt->nxt;
  }
  tt->to = &s[tB->stateNum + tt->to-&out->tStates[0]];
  tt->from = &s[tB->stateNum + tt->from-&out->tStates[0]];

  out->tTrans = tB->tTrans;
  out->tStates = s;
  out->eventNum = out->stateNum;
  out->stateNum = numOfState;

}

void merge_bin_timed(TAutomata *t1, TAutomata *t2, TAutomata *t, TAutomata *out){
  int numOfState = 0;
  int maxInput = 1;
  for (int i= 0; i < t->stateNum; i++){
    maxInput = maxInput < t->tStates[i].inputNum ? t->tStates[i].inputNum : maxInput;
  }
  const int maxNumOfState = ((t1->stateNum < t2->stateNum) ? t2->stateNum : t1->stateNum)* t->stateNum * maxInput;
  // printf("%ld \n", sizeof(TState)*(maxNumOfState + t1->eventNum + t2->eventNum));
  TState *s = (TState *) tl_emalloc(sizeof(TState)*(maxNumOfState + t1->eventNum + t2->eventNum));
  int t1StateNum[maxNumOfState+1];
  int t2StateNum[maxNumOfState];
  int tStateNum[maxNumOfState];
  int tEventStateNum[t1->eventNum + t2->eventNum];

  int matches = 0;
  int events = 0;

  for (int i=0; i<t->stateNum; i++){  
    
    for (int j=0; j< t->tStates[i].inputNum; j++) {
      for (int k=0; k< t1->stateNum; k++){
        if (t1->tStates[k].output == t->tStates[i].input[j] >> 1 && t1->tStates[k].output!= NULLOUT ) {
          //make product state if the input is the same as the output
          t1StateNum[matches] = k;
          for (int l=0; l< t2->stateNum; l++){
            if (t2->tStates[l].output == (t->tStates[i].input[j] & (unsigned short) 0x01) && t2->tStates[l].output!= NULLOUT){
              tStateNum[matches]=i;
              t2StateNum[matches++] = l;
              t1StateNum[matches] = k;
            }
          }
        }else if(t1->tStates[k].output== NULLOUT && events == 0){ // scan only one time for testing NULLOUT of t2
          for (int l=0; l< t2->stateNum; l++){
            if (t2->tStates[l].output== NULLOUT){ 
              tEventStateNum[events++] = l;
            }
          }
          tEventStateNum[events++] = k;
        }else if (events == 0){
          for (int l=0; l< t2->stateNum; l++){
            if (t2->tStates[l].output== NULLOUT){ 
              tEventStateNum[events++] = l;
            }
          }
        }else if(t1->tStates[k].output== NULLOUT && events < t1->eventNum + t2->eventNum){
          tEventStateNum[events++] = k;
        }
      }
    }

    for (int k=numOfState; k< matches; k++){
      // merge their stateId name
      s[k].tstateId = (char *) malloc(sizeof(char)*(strlen(t1->tStates[t1StateNum[k]].tstateId)+strlen(t2->tStates[t2StateNum[k]].tstateId)+strlen(t->tStates[i].tstateId) +9));
      sprintf(s[k].tstateId,"(%s , %s) x %s", t1->tStates[t1StateNum[k]].tstateId, t2->tStates[t2StateNum[k]].tstateId, t->tStates[i].tstateId);
      // merge set of symbols
      s[k].sym = new_set(3);
      if (t1->tStates[t1StateNum[k]].sym!=NULL && t2->tStates[t2StateNum[k]].sym!=NULL)
        do_merge_sets(s[k].sym, t1->tStates[t1StateNum[k]].sym, t2->tStates[t2StateNum[k]].sym,3);
      else if (t1->tStates[t1StateNum[k]].sym!=NULL)
        s[k].sym = dup_set(t1->tStates[t1StateNum[k]].sym, 3);
      else if (t2->tStates[t2StateNum[k]].sym!=NULL)
        s[k].sym = dup_set(t2->tStates[t2StateNum[k]].sym, 3);

      s[k].buchi = t1->tStates[t1StateNum[k]].buchi & t2->tStates[t2StateNum[k]].buchi & t->tStates[i].buchi;
      
      // merge invariants 
      if (!t1->tStates[t1StateNum[k]].inv && !t2->tStates[t2StateNum[k]].inv && !t->tStates[i].inv){
        s[k].inv = (CGuard*) 0;
      }else{
        s[k].inv = (CGuard*) malloc(sizeof(CGuard)); 
        merge_inv(s[k].inv, t1->tStates[t1StateNum[k]].inv,t2->tStates[t2StateNum[k]].inv,t->tStates[i].inv);
      }

      // merge inputs
      s[k].inputNum=0;
      if (t1->tStates[t1StateNum[k]].inputNum>0 && t2->tStates[t2StateNum[k]].inputNum>0) {
        s[k].input= (unsigned short *) malloc(sizeof(unsigned short)*t1->tStates[t1StateNum[k]].inputNum*t2->tStates[t2StateNum[k]].inputNum);
      }else{
        s[k].input= (unsigned short *) malloc(sizeof(unsigned short)*(t1->tStates[t1StateNum[k]].inputNum + t2->tStates[t2StateNum[k]].inputNum));
      }
      if (t1->tStates[t1StateNum[k]].inputNum>0) {
        for (int l=0; l< t1->tStates[t1StateNum[k]].inputNum; l++){
          for (int n=0; n< t2->tStates[t2StateNum[k]].inputNum; n++){
            s[k].input[s[k].inputNum++] = t1->tStates[t1StateNum[k]].input[l] | t2->tStates[t2StateNum[k]].input[n];
          }
        }
      }else if (t2->tStates[t2StateNum[k]].inputNum>0 ){
        for (int n=0; n< t2->tStates[t2StateNum[k]].inputNum; n++){
          s[k].input[s[k].inputNum++] = t2->tStates[t2StateNum[k]].input[n];
        }
      }

      // merge output
      s[k].output = t->tStates[i].output;
    }
    numOfState = matches;
  }

  //add previous ended state back to the merged states
  for (int i=0; i<events; i++){
    if (i < t2->eventNum){
      int inputNum=0;
      s[numOfState+i].input= (unsigned short *) malloc(sizeof(unsigned short)*t2->tStates[tEventStateNum[i]].inputNum);
      for (int l=0; l< t2->tStates[tEventStateNum[i]].inputNum; l++){
        s[numOfState+i].input[inputNum++] = t2->tStates[tEventStateNum[i]].input[l];
      }
      create_tstate(&s[numOfState+i], t2->tStates[tEventStateNum[i]].tstateId, t2->tStates[tEventStateNum[i]].inv, s[numOfState+i].input, t2->tStates[tEventStateNum[i]].inputNum, t2->tStates[tEventStateNum[i]].output, t2->tStates[tEventStateNum[i]].buchi, NULL);
      s[numOfState+i].sym = dup_set(t2->tStates[tEventStateNum[i]].sym ,3);
    }else{
      int inputNum=0;
      s[numOfState+i].input= (unsigned short *) malloc(sizeof(unsigned short)*t1->tStates[tEventStateNum[i]].inputNum);
      for (int l=0; l< t1->tStates[tEventStateNum[i]].inputNum; l++){
        s[numOfState+i].input[inputNum++] = t1->tStates[tEventStateNum[i]].input[l];
      }
      create_tstate(&s[numOfState+i], t1->tStates[tEventStateNum[i]].tstateId, t1->tStates[tEventStateNum[i]].inv, s[numOfState+i].input, t1->tStates[tEventStateNum[i]].inputNum, t1->tStates[tEventStateNum[i]].output, t1->tStates[tEventStateNum[i]].buchi, NULL);
      s[numOfState+i].sym = dup_set(t1->tStates[tEventStateNum[i]].sym ,3);
    }
  }

  //merge transitions
  TTrans *tt = t->tTrans;
  TTrans *tOut = (TTrans *) emalloc_ttrans(1,1);
  TTrans *tmp = tOut;
  while (tt){
    // find tt->from in tStateNum then get the corresponding t1->tStates[] then find the transitions there

    // find the From and to idx for t->tStates that corresponds to tt-> from and tt->to  there should be only one,
    int tStateFrom = -1;
    int tStateTo= -1;
    int i = 0;
    while ((tStateFrom == -1 || tStateTo == -1) && i < t->stateNum) {
      if( &t->tStates[i] == tt->from) {
        tStateFrom = i;
      }
      if( &t->tStates[i] == tt->to) {
        tStateTo = i;
      }
      i++;
    }

    /**********************************************************************************************************/
    /* Find the appearance of those idx in the match table, it is possible to have multiple entries satisfies */
    /* that in the table. Merge them one by one if find match                                                 */
    /**********************************************************************************************************/

    for(i=0; i<numOfState; i++){
      if (tStateNum[i] == tStateFrom){
        for (int j=0; j<numOfState; j++){
          if (tStateNum[j] == tStateTo){
            // i, j are the indexes of one transitions

            //pointer iterate through the linked list to find the transition
            TTrans* t1Match = t1->tTrans;
            TTrans* t2Match = t2->tTrans;
            
            // find transition from t1StateNum[i] to t1StateNum[j]
            if (t1StateNum[i] == t1StateNum[j]){
              t1Match = NULL;
            }else{
              while (t1Match){
                if ( (t1Match->from == &(t1->tStates[t1StateNum[i]])) && (t1Match->to == &(t1->tStates[t1StateNum[j]])) ){
                  break;
                }
                t1Match = t1Match->nxt;
              }
            }

            // find transition from t2StateNum[i] to t2StateNum[j]
            if (t2StateNum[i] == t2StateNum[j]){
              t2Match = NULL;
            }else{
              while (t2Match){
                if ( (t2Match->from == &(t2->tStates[t2StateNum[i]])) && (t2Match->to == &(t2->tStates[t2StateNum[j]])) ){
                  break;
                }
                t2Match = t2Match->nxt;
              }
            }

            if (t1Match || t2Match) { // if both is not NULL
              // merge the transitions t1Match t2Match and tt
              tmp->nxt = (TTrans *) emalloc_ttrans(1,1);
              merge_ttrans(t1Match, t2Match, tt, tmp->nxt, &s[i], &s[j]);
              
              tmp = tmp->nxt;
            }else{
              // printf("Cannot merge transition of the following: \n t1 %s -> %s \n t2 %s -> %s \n t %s -> %s \n", t1->tStates[t1StateNum[i]].tstateId, t1->tStates[t1StateNum[j]].tstateId, t2->tStates[t2StateNum[i]].tstateId, t2->tStates[t2StateNum[j]].tstateId, t->tStates[tStateNum[i]].tstateId, t->tStates[tStateNum[j]].tstateId);
            }

          }
        }
      }
    }

    tt=tt->nxt;
  }

  //merge transition that go to itself
  for (int k=0; k < t->stateNum; k++){

    int tStateTo = k;
    int tStateFrom = k;

    for(int i=0; i<numOfState; i++){
      if (tStateNum[i] == tStateFrom){
        for (int j=0; j<numOfState; j++){
          if (tStateNum[j] == tStateTo){
            if (i==j) continue;
            // i, j are the indexes of one transitions

            //pointer iterate through the linked list to find the transition
            TTrans* t1Match = t1->tTrans;
            TTrans* t2Match = t2->tTrans;
            
            // find transition from t1StateNum[i] to t1StateNum[j]
            if (t1StateNum[i] == t1StateNum[j]){
              t1Match = NULL;
            }else{
              while (t1Match){
                if ( (t1Match->from == &(t1->tStates[t1StateNum[i]])) && (t1Match->to == &(t1->tStates[t1StateNum[j]])) ){
                  break;
                }
                t1Match = t1Match->nxt;
              }
            }

            // find transition from t2StateNum[i] to t2StateNum[j]
            if (t2StateNum[i] == t2StateNum[j]){
              t2Match = NULL;
            }else{
              while (t2Match){
                if ( (t2Match->from == &(t2->tStates[t2StateNum[i]])) && (t2Match->to == &(t2->tStates[t2StateNum[j]])) ){
                  break;
                }
                t2Match = t2Match->nxt;
              }
            }

            if (t1Match || t2Match) { // if both is not NULL
              // merge the transitions t1Match t2Match and tt
              tmp->nxt = (TTrans *) emalloc_ttrans(1,1);
              merge_ttrans(t1Match, t2Match, NULL, tmp->nxt, &s[i], &s[j]);
              
              tmp = tmp->nxt;
            }else{
              // printf("Cannot merge transition of the following: \n t1 %s -> %s \n t2 %s -> %s \n t %s -> %s \n", t1->tStates[t1StateNum[i]].tstateId, t1->tStates[t1StateNum[j]].tstateId, t2->tStates[t2StateNum[i]].tstateId, t2->tStates[t2StateNum[j]].tstateId, t->tStates[tStateNum[i]].tstateId, t->tStates[tStateNum[j]].tstateId);
            }

          }
        }
      }
    }
  }


  //add previous ended transition back to the merged automata
  tt = tOut->nxt;
  while (tt->nxt) {
    tt = tt->nxt;
  }
  if (t2->tEvents != NULL){
    tt->nxt = t2->tEvents;
    out->tEvents = tt->nxt;
    while (tt->nxt) {
      tt = tt->nxt;
      tt->to = &s[numOfState + tt->to - &t2->tStates[0] - tEventStateNum[0]];
      tt->from = &s[numOfState + tt->from - &t2->tStates[0] - tEventStateNum[0]];
    }
  }

  if (t1->tEvents != NULL){
    tt->nxt = t1->tEvents;
    out->tEvents = tt->nxt;
    while (tt->nxt) {
      tt = tt->nxt;
      tt->to = &s[numOfState + t2->eventNum + tt->to - &t1->tStates[0] - tEventStateNum[t2->eventNum]];
      tt->from = &s[numOfState + t2->eventNum + tt->from - &t1->tStates[0] - tEventStateNum[t2->eventNum]];
    }
  }
  //create return Automata out
  // out = (TAutomata *) malloc(sizeof(TAutomata));
  out->stateNum = numOfState + events;
  out->tStates = s;
  out->tTrans = tOut->nxt;
  out->eventNum = events;

}

void merge_timed(TAutomata *t1, TAutomata *t, TAutomata *out){
  int numOfState = 0;
  int maxInput = 1;
  for (int i= 0; i < t->stateNum; i++){
    maxInput = maxInput < t->tStates[i].inputNum ? t->tStates[i].inputNum : maxInput;
  }
  const int maxNumOfState = t1->stateNum* t->stateNum * maxInput;
  // printf("%d \n", maxNumOfState+t1->eventNum);
  TState *s = (TState *) tl_emalloc(sizeof(TState)*(maxNumOfState+t1->eventNum));
  int t1StateNum[maxNumOfState+1];
  int tStateNum[maxNumOfState];
  int tEventStateNum[t1->eventNum];

  int matches = 0;
  int events = 0;

  for (int i=0; i<t->stateNum; i++){  
    
    for (int j=0; j< t->tStates[i].inputNum; j++) {
      for (int k=0; k< t1->stateNum; k++){
        if (t1->tStates[k].output == t->tStates[i].input[j] && t1->tStates[k].output!= NULLOUT ) {
          //make product state if the input is the same as the output
          t1StateNum[matches] = k;
          tStateNum[matches++]=i;
        }else if(t1->tStates[k].output== NULLOUT && events < t1->eventNum){
          tEventStateNum[events++] = k;
        }
      }
    }

    for (int k=numOfState; k< matches; k++){
      // merge their stateId name
      s[k].tstateId = (char *) malloc(sizeof(char)*(strlen(t1->tStates[t1StateNum[k]].tstateId)+strlen(t->tStates[i].tstateId) +5));
      sprintf(s[k].tstateId,"%s x %s", t1->tStates[t1StateNum[k]].tstateId, t->tStates[i].tstateId);
      // merge set of symbols
      s[k].sym = dup_set(t1->tStates[t1StateNum[k]].sym,3);
      
      // merge invariants 
      if (!t1->tStates[t1StateNum[k]].inv && !t->tStates[i].inv){
        s[k].inv = (CGuard*) 0;
      }else{
        s[k].inv = (CGuard*) malloc(sizeof(CGuard)); 
        merge_inv(s[k].inv, t1->tStates[t1StateNum[k]].inv, NULL ,t->tStates[i].inv);
      }

      // merge inputs
      s[k].inputNum=0;
      s[k].input= (unsigned short *) malloc(sizeof(unsigned short)*t1->tStates[t1StateNum[k]].inputNum);
      for (int l=0; l< t1->tStates[t1StateNum[k]].inputNum; l++){
        s[k].input[s[k].inputNum++] = t1->tStates[t1StateNum[k]].input[l];
      }

      // merge output
      s[k].output = t->tStates[i].output;      

      // merge buchi
      s[k].buchi = t1->tStates[t1StateNum[k]].buchi & t->tStates[i].buchi;
    }
    numOfState = matches;
  }

  //add previous ended state back to the merged states
  for (int i=0; i<events; i++){

    int inputNum=0;
    s[numOfState+i].input= (unsigned short *) malloc(sizeof(unsigned short)*t1->tStates[tEventStateNum[i]].inputNum);
    for (int l=0; l< t1->tStates[tEventStateNum[i]].inputNum; l++){
      s[numOfState+i].input[inputNum++] = t1->tStates[tEventStateNum[i]].input[l];
    }
    create_tstate(&s[numOfState+i], t1->tStates[tEventStateNum[i]].tstateId, t1->tStates[tEventStateNum[i]].inv, s[numOfState+i].input, t1->tStates[tEventStateNum[i]].inputNum, t1->tStates[tEventStateNum[i]].output, t1->tStates[tEventStateNum[i]].buchi, NULL);
    s[numOfState+i].sym = dup_set(t1->tStates[tEventStateNum[i]].sym ,3);
  }  


  //merge transitions
  TTrans *tt = t->tTrans;
  TTrans *tOut = (TTrans *) emalloc_ttrans(1,1);
  TTrans *tmp = tOut;
  while (tt){
    // find tt->from in tStateNum then get the corresponding t1->tStates[] then find the transitions there

    // find the From and to idx for t->tStates that corresponds to tt-> from and tt->to  there should be only one,
    int tStateFrom = -1;
    int tStateTo= -1;
    int i = 0;
    while ((tStateFrom == -1 || tStateTo == -1) && i < t->stateNum) {
      if( &t->tStates[i] == tt->from) {
        tStateFrom = i;
      }
      if( &t->tStates[i] == tt->to) {
        tStateTo = i;
      }
      i++;
    }

    /**********************************************************************************************************/
    /* Find the appearance of those idx in the match table.                                                   */
    /**********************************************************************************************************/

    for(i=0; i<numOfState; i++){
      if (tStateNum[i] == tStateFrom){
        for (int j=0; j<numOfState; j++){
          if (tStateNum[j] == tStateTo){
            // i, j are the indices of one transitions

            //pointer iterate through the linked list to find the transition
            TTrans* t1Match = t1->tTrans;
            
            // find transition from t1StateNum[i] to t1StateNum[j]
            if (t1StateNum[i] == t1StateNum[j]){
              t1Match = NULL;
            }else{
              while (t1Match){
                if ( (t1Match->from == &(t1->tStates[t1StateNum[i]])) && (t1Match->to == &(t1->tStates[t1StateNum[j]])) ){
                  break;
                }
                t1Match = t1Match->nxt;
              }
            }

            if (t1Match) { // if both is not NULL
              // merge the transitions t1Match tt
              tmp->nxt = (TTrans *) emalloc_ttrans(1,1);
              merge_ttrans(t1Match, NULL, tt, tmp->nxt, &s[i], &s[j]);
              
              tmp = tmp->nxt;
            }else{
              printf("Cannot merge transition of the following: \n t1 %s -> %s \n t %s -> %s \n", t1->tStates[t1StateNum[i]].tstateId, t1->tStates[t1StateNum[j]].tstateId, t->tStates[tStateNum[i]].tstateId, t->tStates[tStateNum[j]].tstateId);
            }

          }
        }
      }
    }

    tt=tt->nxt;
  }

  //merge transition that go to itself
  for (int k=0; k < t->stateNum; k++){

    int tStateTo = k;
    int tStateFrom = k;

    for(int i=0; i<numOfState; i++){
      if (tStateNum[i] == tStateFrom){
        for (int j=0; j<numOfState; j++){
          if (tStateNum[j] == tStateTo){
            if (i==j) continue;
            // i, j are the indexes of one transitions

            //pointer iterate through the linked list to find the transition
            TTrans* t1Match = t1->tTrans;
            
            // find transition from t1StateNum[i] to t1StateNum[j]
            if (t1StateNum[i] == t1StateNum[j]){
              t1Match = NULL;
            }else{
              while (t1Match){
                if ( (t1Match->from == &(t1->tStates[t1StateNum[i]])) && (t1Match->to == &(t1->tStates[t1StateNum[j]])) ){
                  break;
                }
                t1Match = t1Match->nxt;
              }
            }

            if (t1Match) { // if both is not NULL
              // merge the transitions t1Match t2Match and tt
              tmp->nxt = (TTrans *) emalloc_ttrans(1,1);
              merge_ttrans(t1Match, NULL, NULL, tmp->nxt, &s[i], &s[j]);
              
              tmp = tmp->nxt;
            }else{
              printf("Cannot merge transition of the following: \n t1 %s -> %s \n t %s -> %s \n", t1->tStates[t1StateNum[i]].tstateId, t1->tStates[t1StateNum[j]].tstateId, t->tStates[tStateNum[i]].tstateId, t->tStates[tStateNum[j]].tstateId);
            }

          }
        }
      }
    }
  }

  //add previous ended transition back to the merged automata
  tt = tOut;
  while (tt->nxt) {
    tt = tt->nxt;
  }
  if (t1->tEvents != NULL){
    tt->nxt = t1->tEvents;
    out->tEvents = tt->nxt;
    while (tt->nxt) {
      tt = tt->nxt;
      tt->to = &s[numOfState + tt->to - &t1->tStates[0] - tEventStateNum[0]];
      tt->from = &s[numOfState + tt->from - &t1->tStates[0] - tEventStateNum[0]];
    }
  }
  //create return Automata out
  // out = (TAutomata *) malloc(sizeof(TAutomata));
  out->stateNum = numOfState + events;
  out->tStates = s;
  out->tTrans = tOut->nxt;
  out->eventNum = events;
}


/********************************************************************\
|*                Create Timed Automata of the map                  *|
\********************************************************************/
TAutomata *create_map(int nodeNum){
  TAutomata *t = (TAutomata *) tl_emalloc(sizeof(TAutomata));
  TState *s = (TState *)tl_emalloc(sizeof(TState)*nodeNum);
  CGuard *cguard;
  int *clockId;

  //share same cguard
  cguard = (CGuard *) malloc(sizeof(CGuard));
  cguard->nType = PREDICATE;
  cguard->cCstr = (CCstr *)(CCstr * )  malloc(sizeof(CCstr));
  cguard->cCstr->cIdx = cCount;
  cguard->cCstr->gType = LESSEQUAL;
  cguard->cCstr->bndry = 1;
  // void create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, unsigned short buchi, Node* p){
  for (int i=0; i<nodeNum; i++){
    s[i].tstateId = (char *)malloc(sizeof(char)*6);
    sprintf(s[i].tstateId, "loc%i",i);

    create_tstate(&s[i], s[i].tstateId, cguard, (unsigned short *) 0, 0, 0, 1, NULL);
    s[i].sym = new_set(3);
    clear_set(s[i].sym,3);
    add_set(s[i].sym, t_get_sym_id("a"));
  }
  s[nodeNum-1].output= 1;
  TTrans *tt = emalloc_ttrans(1,1);
  TTrans *tmp = tt;

  //share same cguard and clockId
  cguard = (CGuard*) malloc(sizeof(CGuard));
  cguard->nType = PREDICATE;
  cguard->cCstr = (CCstr * ) malloc(sizeof(CCstr));
  cguard->cCstr->cIdx = cCount;
  cguard->cCstr->gType = GREATEREQUAL;
  cguard->cCstr->bndry = 1;
  clockId = (int *) malloc(sizeof(int)*1);
  clockId[0] = cCount;

  for (int i=0; i<nodeNum; i++){
    for (int j=i+1; j<nodeNum; j++){
      tmp->nxt = emalloc_ttrans(1,1);
      tmp = tmp->nxt;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[i],  &s[j]);

      tmp->nxt = emalloc_ttrans(1,1);
      tmp = tmp->nxt;
      // void create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to)
      create_ttrans(tmp, cguard, clockId, 1, &s[j],  &s[i]);

    }
  }
  cCount++;

  t->tTrans = tt->nxt;
  t->tStates = s;
  t->stateNum = nodeNum;
  t->tEvents = NULL;
  t->eventNum = 0;
  return t;
}

/********************************************************************\
|*                Display of the Timed Automata                     *|
\********************************************************************/

//TODO: print clock guards (10)
void print_CGuard(CGuard *cg){
  if (!cg){
    fprintf(tl_out, "* ");
    return;
  }else{
    switch (cg->nType){
      case AND:
        print_CGuard(cg->lft);
        fprintf(tl_out, "&& ");
        print_CGuard(cg->rgt);
        break;

      case OR:
        print_CGuard(cg->lft);
        fprintf(tl_out, "|| ");
        print_CGuard(cg->rgt);
        break;

      case PREDICATE:
        fprintf(tl_out, "z%d ", cg->cCstr->cIdx);
        if(cg->cCstr->gType == GREATER)    fprintf(tl_out, "> ");
        else if(cg->cCstr->gType == GREATEREQUAL)    fprintf(tl_out, ">= ");
        else if(cg->cCstr->gType == LESS)    fprintf(tl_out, "< ");
        else if(cg->cCstr->gType == LESSEQUAL)    fprintf(tl_out, "<= ");
        fprintf(tl_out, "%d ", cg->cCstr->bndry);
        break;
    }
  }
}

void CGuard_to_xml(CGuard *cg, char* res){
  if (!cg){
    res = NULL;
    return;
  }else{
    char buffer[15];
    switch (cg->nType){
      case AND:
        strcat(res, "(");
        CGuard_to_xml(cg->lft, res);
        strcat(res, " && ");
        CGuard_to_xml(cg->rgt, res);
        strcat(res, ")");
        break;

      case OR:
        strcat(res, "(");
        CGuard_to_xml(cg->lft, res);
        strcat(res, " || ");
        CGuard_to_xml(cg->lft, res);
        strcat(res, ")");
        break;

      case PREDICATE:
        sprintf(buffer, "z[%d]", cg->cCstr->cIdx);
        strcat(res, buffer);
        if(cg->cCstr->gType == GREATER)    strcat(res, ">");
        else if(cg->cCstr->gType == GREATEREQUAL)    strcat(res, ">=");
        else if(cg->cCstr->gType == LESS)    strcat(res, "<");
        else if(cg->cCstr->gType == LESSEQUAL)    strcat(res, "<=");
        sprintf(buffer, "%d", cg->cCstr->bndry);
        strcat(res, buffer);
        break;
    }
  }
}

void print_timed(TAutomata *t) /* dumps the alternating automaton */
{
 //  int i;
 //  ATrans *t;

 //  fprintf(tl_out, "init :\n");
 //  for(t = transition[0]; t; t = t->nxt) {
 //    print_set(t->to, 0);
 //    fprintf(tl_out, "\n");
 //  }
  TTrans *tmp;
  tmp = t->tTrans;
  int j = 0;
  while (tmp != NULL) {
    fprintf(tl_out, "Transition %i : %i to %i \n", j, (int) (tmp->from - &t->tStates[0]) + 1, (int) (tmp->to - &t->tStates[0]) + 1);
    fprintf(tl_out, "Clock reseted: ");
    print_set(tmp->cIdx, 4);
    fprintf(tl_out, "\nGuards Condition: ");
    print_CGuard(tmp->cguard);
    fprintf(tl_out, "\n");
    j++;
    tmp = tmp->nxt;
  }
  for (int i=0; i< t->stateNum; i++){
    fprintf(tl_out, "State %i : %s \n   input: (", i+1, t->tStates[i].tstateId);
    for (int j=0; j< t->tStates[i].inputNum; j++){
      fprintf(tl_out,"%o, ", t->tStates[i].input[j]);
    }
    fprintf(tl_out,") output: (%i) \n", t->tStates[i].output);

    if (t->tStates[i].sym != NULL){
      fprintf(tl_out, "   symbols: ");
      print_set(t->tStates[i].sym,3);
      fprintf(tl_out, "\n");
    }
    fprintf(tl_out, "   invariants: ");
    print_CGuard(t->tStates[i].inv);
    fprintf(tl_out, "\n");
  }


 //  for(i = node_id - 1; i > 0; i--) {
 //    if(!label[i])
 //      continue;
 //    fprintf(tl_out, "state %i : ", i);
 //    dump(label[i]);
 //    fprintf(tl_out, "\n");
 //    for(t = transition[i]; t; t = t->nxt) {
 //      if (empty_set(t->pos, 1) && empty_set(t->neg, 1))
	// fprintf(tl_out, "1");
 //      print_set(t->pos, 1);
 //      if (!empty_set(t->pos,1) && !empty_set(t->neg,1)) fprintf(tl_out, " & ");
 //      print_set(t->neg, 2);
 //      fprintf(tl_out, " -> ");
 //      print_set(t->to, 0);
 //      fprintf(tl_out, "\n");
 //    }
 //  }
}


void timed_to_xml(TAutomata *t, int clockSize, FILE *xml) /* dumps the alternating automaton */
{
 //  int i;
 //  ATrans *t;

 //  fprintf(tl_out, "init :\n");
 //  for(t = transition[0]; t; t = t->nxt) {
 //    print_set(t->to, 0);
 //    fprintf(tl_out, "\n");
 //  }
  fprintf(xml, "#!/usr/bin/python\nfrom pyuppaal import *\ndef main():\n\tlocid = 0\n\tlocations = []\n\ttransitions = []\n");

  int j = 0;
  char buffer[80];
  char setBuffer[50];
  for (int i=0; i< t->stateNum; i++){
    buffer[0] = '\0';
    CGuard_to_xml(t->tStates[i].inv, buffer);
    if(t->tStates[i].buchi== 1){
      fprintf(xml,"\tlocations.append( Location(invariant='%s', urgent=False, committed=False, name='loc%i_b', id = 'id'+str(locid)) )\n", buffer, i);
    }else{
      fprintf(xml,"\tlocations.append( Location(invariant='%s', urgent=False, committed=False, name='loc%i', id = 'id'+str(locid)) )\n", buffer, i);
    }

    fprintf(xml, "\tlocid +=1\n");
  }

  TTrans *tmp;
  tmp = t->tTrans;

  while (tmp != NULL) {
    buffer[0] = '\0';
    CGuard_to_xml(tmp->cguard, buffer);
    setBuffer[0] = '\0';
    set_to_xml(tmp->cIdx, setBuffer);
    fprintf(xml, "\ttransitions.append( Transition(locations[%i], locations[%i], guard='%s', assignment='%s') )\n", (int) (tmp->from - &t->tStates[0]), (int) (tmp->to - &t->tStates[0]) , buffer, setBuffer);
    j++;
    tmp = tmp->nxt;
  }

  fprintf(xml, "\ttemplate = Template('sys', locations=locations, transitions=transitions, declaration='clock z[%i];', initlocation=locations[0])\n", clockSize);

  fprintf(xml, "\ttemplate.layout(auto_nails = True);\n\tnta = NTA(system = 'system sys;', templates=[template])\n\tprint nta.to_xml()\nif __name__ == '__main__':\n\tmain()\n");

  fclose(xml);

 //  for(i = node_id - 1; i > 0; i--) {
 //    if(!label[i])
 //      continue;
 //    fprintf(tl_out, "state %i : ", i);
 //    dump(label[i]);
 //    fprintf(tl_out, "\n");
 //    for(t = transition[i]; t; t = t->nxt) {
 //      if (empty_set(t->pos, 1) && empty_set(t->neg, 1))
  // fprintf(tl_out, "1");
 //      print_set(t->pos, 1);
 //      if (!empty_set(t->pos,1) && !empty_set(t->neg,1)) fprintf(tl_out, " & ");
 //      print_set(t->neg, 2);
 //      fprintf(tl_out, " -> ");
 //      print_set(t->to, 0);
 //      fprintf(tl_out, "\n");
 //    }
 //  }
}
/********************************************************************\
|*                       Main method                                *|
\********************************************************************/

void mk_timed(Node *p) /* generates an timed automata for p */
{
  // if(tl_stats) getrusage(RUSAGE_SELF, &tr_debut);

  t_clock_size = t_calculate_clock_size(p) + 1; /* number of states in the automaton */
  // t_label = (Node **) tl_emalloc(t_node_size * sizeof(Node *));
  // t_transition = (TTrans **) tl_emalloc(t_node_size * sizeof(TTrans *));
  // node_size = node_size / (8 * sizeof(int)) + 1;

  t_sym_size = t_calculate_sym_size(p); /* number of predicates */
  if(t_sym_size) t_sym_table = (char **) tl_emalloc(t_sym_size * sizeof(char *));
  t_sym_size = t_sym_size / (8 * sizeof(int)) + 1;
  
//   final_set = make_set(-1, 0);
  cCount = 0;
  tAutomata = build_timed(p); /* generates the alternating automaton */

  fprintf(tl_out, "%i\n",cCount);

  print_timed(tAutomata);

  TAutomata* mapAutomata = create_map(4);

  print_timed(mapAutomata);

  TAutomata *tResult = (TAutomata *) tl_emalloc(sizeof(TAutomata));
  merge_timed(mapAutomata, tAutomata, tResult);

  print_timed(tResult);

  FILE *xml;
  char outputFileName[20] = "scripts/uppaal.py";
  xml = fopen(outputFileName, "w");

  if (xml == NULL) {
    fprintf(stderr, "Can't open output file %s!\n", outputFileName);
    exit(1);
  }
  timed_to_xml(tResult, t_clock_size, xml);

//   if(tl_verbose) {
//     fprintf(tl_out, "\nAlternating automaton before simplification\n");
//     print_alternating();
//   }

//   if(tl_simp_diff) {
//     simplify_astates(); /* keeps only accessible states */
//     if(tl_verbose) {
//       fprintf(tl_out, "\nAlternating automaton after simplification\n");
//       print_alternating();
//     }
//   }
  
//   if(tl_stats) {
//     getrusage(RUSAGE_SELF, &tr_fin);
//     timeval_subtract (&t_diff, &tr_fin.ru_utime, &tr_debut.ru_utime);
//     fprintf(tl_out, "\nBuilding and simplification of the alternating automaton: %i.%06is",
// 		t_diff.tv_sec, t_diff.tv_usec);
//     fprintf(tl_out, "\n%i states, %i transitions\n", astate_count, atrans_count);
//   }

//   releasenode(1, p);
//   tfree(label);
}
// #endif