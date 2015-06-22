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
  case U_OPER:
  case V_OPER:
    return(t_calculate_clock_size(p->lft) + t_calculate_clock_size(p->rgt) + 4);
#ifdef NXT
  case NEXT:
    return(t_calculate_clock_size(p->lft) + 2);
#endif
  case NOT:
  default:
    return 1;
    break;
  }
}

// int calculate_sym_size(Node *p) /* returns the number of predicates */
// {
//   switch(p->ntyp) {
//   case AND:
//   case OR:
//   case U_OPER:
//   case V_OPER:
//     return(calculate_sym_size(p->lft) + calculate_sym_size(p->rgt));
// #ifdef NXT
//   case NEXT:
//     return(calculate_sym_size(p->lft));
// #endif
//   case NOT:
//   case PREDICATE:
//     return 1;
//   default:
//     return 0;
//   }
// }

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
  t_sym_table[t_sym_id] = s;
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
    s->sym = new_set(3); //3 is symolic set. sym_set_size is used to determine the allocation size
    clear_set(s->sym, 3);
    add_set(s->sym, t_get_sym_id(p->sym->name));
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
  
   TTrans *t = (TTrans *)0, *tmp ;
   TState *s;
   TAutomata *tA;
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
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
      create_tstate(s, "true", (CGuard *) 0, (unsigned short*) 0, 0, 1, 1, NULL); //output true

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = (TTrans *)0;
      tA->tStates = s;
      tA->stateNum = 1;
      break;
    case FALSE:
      s = (TState *) tl_emalloc(sizeof(TState)*1);
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
      create_tstate(s, "false", (CGuard *) 0, (unsigned short*) 0, 0, 0, 1, NULL); //output true

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = (TTrans *)0;
      tA->tStates = s;
      tA->stateNum = 1;
      break;

    case PREDICATE:
      t = emalloc_ttrans(2,1);  //2 states and 1 clock
      s = (TState *) tl_emalloc(sizeof(TState)*2);

      stateName= (char *) malloc (sizeof(char)*(strlen(p->sym->name))+8);
      sprintf(stateName, "pred : %s", p->sym->name);
      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 1 << t_get_sym_id(p->sym->name);
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
      create_tstate(s, stateName, (CGuard *) 0, input, 1, 1, 1, p); //output true when p is true

      stateName= (char *) malloc (sizeof(char)*(strlen(p->sym->name))+10);
      sprintf(stateName, "! pred : %s", p->sym->name);
      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
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
      break;

    case NOT:
      t1 = build_timed(p->lft);

      t = emalloc_ttrans(2,1);  //2 states 2 transitions and 1 clock
      s = (TState *) tl_emalloc(sizeof(TState)*2);

      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b1;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
      create_tstate(s, "p", (CGuard *) 0, input, 1, 0, 1, NULL); //output false when p is true

      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b0;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
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

    case U_OPER: 
      t1= build_timed(p->lft);
      t2= build_timed(p->rgt);

      //create timed automata with 8 transition and 1 clock;
      t = emalloc_ttrans(8,1); 
      s = (TState *) tl_emalloc(sizeof(TState)*4);

      input = (unsigned short *) malloc(sizeof(unsigned short)*2);
      input[0] = 0b01;
      input[1] = 0b00;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
      create_tstate(&s[0], "!p", (CGuard *) 0, input, 2, 0, 1, NULL); //output 0 in !p state

      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b10;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
      create_tstate(&s[1], "!(p!q)", (CGuard *) 0, input, 1, 0, 1, NULL); //output 0 in !(p!q) state

      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b10;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
      create_tstate(&s[2], "p!q", (CGuard *) 0, input, 1, 1, 0, NULL); //output 1 in p!q state


      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b11;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
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
      // TODO: free tA, t1, t2
      tA = tOut;
      break;

  //   case U_OPER:    /* p U q <-> q || (p && X (p U q)) */
  //     for(t2 = build_alternating(p->rgt); t2; t2 = t2->nxt) {
  //       ATrans *tmp = dup_trans(t2);  /* q */
  //       tmp->nxt = t;
  //       t = tmp;
  //     }
  //     for(t1 = build_alternating(p->lft); t1; t1 = t1->nxt) {
  //       ATrans *tmp = dup_trans(t1);  /* p */
  //       add_set(tmp->to, node_id);  /* X (p U q) */
  //       tmp->nxt = t;
  //       t = tmp;
  //     }
  //     add_set(final_set, node_id);
  //     break;
  // TOOD: add V_OPER
  //   case V_OPER:    /* p V q <-> (p && q) || (p && X (p V q)) */
  //     for(t1 = build_alternating(p->rgt); t1; t1 = t1->nxt) {
  //       ATrans *tmp;

  //       for(t2 = build_alternating(p->lft); t2; t2 = t2->nxt) {
  // 	tmp = merge_trans(t1, t2);  /* p && q */
  // 	if(tmp) {
  // 	  tmp->nxt = t;
  // 	  t = tmp;
  // 	}
  //       }

  //       tmp = dup_trans(t1);  /* p */
  //       add_set(tmp->to, node_id);  /* X (p V q) */
  //       tmp->nxt = t;
  //       t = tmp;
  //     }
  //     break;

    case AND:
      t1= build_timed(p->lft);
      t2= build_timed(p->rgt);

      t = emalloc_ttrans(2,1); 
      s = (TState *) tl_emalloc(sizeof(TState)*2);


      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b11;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
      create_tstate(&s[0], "and", (CGuard *) 0, input, 1, 1, 1, NULL); //output 1 in pq state

      input = (unsigned short *) malloc(sizeof(unsigned short)*3);
      input[0] = 0b10;
      input[1] = 0b01;
      input[2] = 0b00;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
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
      // TODO: free tA, t1, t2
      tA = tOut;
      break;

    case OR:
      t1= build_timed(p->lft);
      t2= build_timed(p->rgt);

      t = emalloc_ttrans(2,1); 
      s = (TState *) tl_emalloc(sizeof(TState)*2);

      input = (unsigned short *) malloc(sizeof(unsigned short)*1);
      input[0] = 0b00;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
      create_tstate(&s[0], "or", (CGuard *) 0, input, 1, 0, 1, NULL); //output 0 in !p!q state

      input = (unsigned short *) malloc(sizeof(unsigned short)*3);
      input[0] = 0b10;
      input[1] = 0b01;
      input[2] = 0b11;
      // create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p)
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

// TODO: simplify invariants if they are looking at same clock
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
    target= lft;
  }else if (rgt){
    target= rgt;
  }else if (top){
    target= top;
  }
}
/********************************************************************\
|*             Linking the Timed Automata                           *|
\********************************************************************/

void merge_ttrans(TTrans *t1, TTrans *t2, TTrans *tt, TTrans *tOut, TState *from, TState *to){
  if (t1 && t2){
    tOut->cIdx = new_set(4);
    clear_set(tOut->cIdx, 4);
    do_merge_sets(tOut->cIdx, t1->cIdx,t2->cIdx,4);
    merge_sets(tOut->cIdx, tt->cIdx,4);
    tOut->cguard = (CGuard *) malloc(sizeof(CGuard));
    merge_inv(tOut->cguard, t1->cguard, t2->cguard, tt->cguard);
  }else if (t1) {
    tOut->cIdx = new_set(4);
    clear_set(tOut->cIdx, 4);
    do_merge_sets(tOut->cIdx, t1->cIdx,tt->cIdx,4);

    tOut->cguard = (CGuard *) malloc(sizeof(CGuard));
    merge_inv(tOut->cguard, t1->cguard, (CGuard *) 0, tt->cguard);
  }else if (t2) {

    tOut->cIdx = new_set(4);
    clear_set(tOut->cIdx, 4);
    do_merge_sets(tOut->cIdx, t2->cIdx,tt->cIdx,4);

    tOut->cguard = (CGuard *) malloc(sizeof(CGuard));
    merge_inv(tOut->cguard, t2->cguard, (CGuard *) 0, tt->cguard);
  }else {
    printf("ERROR! in merge_ttrans!");
  }
  tOut->from = from;
  tOut->to = to;
}

// TODO: Add Eventually I and V 
void merge_bin_timed(TAutomata *t1, TAutomata *t2, TAutomata *t, TAutomata *out){
  int numOfState = 0;
  const int maxNumOfState = ((t1->stateNum < t2->stateNum) ? t2->stateNum : t1->stateNum)* t->stateNum;
  TState s[maxNumOfState];
  int t1StateNum[maxNumOfState+1];
  int t2StateNum[maxNumOfState];
  int tStateNum[maxNumOfState];

  int matches = 0;

  for (int i=0; i<t->stateNum; i++){  
    
    for (int j=0; j< t->tStates[i].inputNum; j++) {
      for (int k=0; k< t1->stateNum; k++){
        if (t1->tStates[k].output == t->tStates[i].input[j] >> 1) {
          //make product state if the input is the same as the output
          t1StateNum[matches] = k;
          for (int l=0; l< t2->stateNum; l++){
            if (t2->tStates[l].output == (t->tStates[i].input[j] & (unsigned short) 0x01)){
              tStateNum[matches]=i;
              t2StateNum[matches++] = l;
              t1StateNum[matches] = k;
            }
          }
        }
      }
    }

    for (int k=numOfState; k< matches; k++){
      // merge their stateId name
      s[k].tstateId = (char *) malloc(sizeof(char)*(strlen(t1->tStates[t1StateNum[k]].tstateId)+strlen(t2->tStates[t2StateNum[k]].tstateId)+strlen(t->tStates[i].tstateId) +9));
      sprintf(s[k].tstateId,"(%s , %s) x %s", t1->tStates[t1StateNum[k]].tstateId, t2->tStates[t2StateNum[k]].tstateId, t->tStates[i].tstateId);
      // merge set of symbols
      s[k].sym = new_set(3);
      do_merge_sets(s[k].sym, t1->tStates[t1StateNum[k]].sym, t2->tStates[t2StateNum[k]].sym,3);
      
      // merge invariants 

      s[k].inv = (CGuard*) malloc(sizeof(CGuard)); 
      merge_inv(s[k].inv, t1->tStates[t1StateNum[k]].inv,t2->tStates[t2StateNum[k]].inv,t->tStates[i].inv);


      // merge inputs
      s[k].inputNum=0;
      s[k].input= (unsigned short *) malloc(sizeof(unsigned short)*t1->tStates[t1StateNum[k]].inputNum*t2->tStates[t2StateNum[k]].inputNum);
      for (int l=0; l< t1->tStates[t1StateNum[k]].inputNum; l++){
        for (int n=0; n< t2->tStates[t2StateNum[k]].inputNum; n++){
          s[k].input[s[k].inputNum++] = t1->tStates[t1StateNum[k]].input[l] | t2->tStates[t2StateNum[k]].input[n];
        }
      }

      // merge output
      s[k].output = t->tStates[i].output;      
    }
    numOfState = matches;
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
            // i, j are the indices of one transitions

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
              merge_ttrans(t1Match, t2Match, tt, tmp, &s[i], &s[j]);
              tmp->nxt = (TTrans *) emalloc_ttrans(1,1);
              tmp = tmp->nxt;
            }else{
              printf("ERROR! Problem in merging transitions! \n");
            }

          }
        }
      }
    }

    tt=tt->nxt;
  }

  //create return Automata out
  out = (TAutomata *) malloc(sizeof(TAutomata));
  out->stateNum = numOfState;
  out->tStates = s;
  out->tTrans = tOut;

}

void merge_timed(TAutomata *t1, TAutomata *t, TAutomata *out){
  int numOfState = 0;
  const int maxNumOfState = t1->stateNum* t->stateNum;
  TState s[maxNumOfState];
  int t1StateNum[maxNumOfState+1];
  int tStateNum[maxNumOfState];

  int matches = 0;

  for (int i=0; i<t->stateNum; i++){  
    
    for (int j=0; j< t->tStates[i].inputNum; j++) {
      for (int k=0; k< t1->stateNum; k++){
        if (t1->tStates[k].output == t->tStates[i].input[j]) {
          //make product state if the input is the same as the output
          t1StateNum[matches] = k;
          tStateNum[matches++]=i;
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
      s[k].inv = (CGuard*) malloc(sizeof(CGuard)); 
      merge_inv(s[k].inv, t1->tStates[t1StateNum[k]].inv,NULL,t->tStates[i].inv);

      // merge inputs
      s[k].inputNum=0;
      s[k].input= (unsigned short *) malloc(sizeof(unsigned short)*t1->tStates[t1StateNum[k]].inputNum);
      for (int l=0; l< t1->tStates[t1StateNum[k]].inputNum; l++){
        s[k].input[s[k].inputNum++] = t1->tStates[t1StateNum[k]].input[l];
      }

      // merge output
      s[k].output = t->tStates[i].output;      
    }
    numOfState = matches;
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
              merge_ttrans(t1Match, NULL, tt, tmp, &s[i], &s[j]);
              tmp->nxt = (TTrans *) emalloc_ttrans(1,1);
              tmp = tmp->nxt;
            }else{
              printf("ERROR! Problem in merging transitions! \n");
            }

          }
        }
      }
    }

    tt=tt->nxt;
  }

  //create return Automata out
  out = (TAutomata *) malloc(sizeof(TAutomata));
  out->stateNum = numOfState;
  out->tStates = s;
  out->tTrans = tOut;
}

/********************************************************************\
|*                Display of the Timed Automata                     *|
\********************************************************************/
//TODO: display timed automata created
void print_timed(TAutomata *t) /* dumps the alternating automaton */
{
 //  int i;
 //  ATrans *t;

 //  fprintf(tl_out, "init :\n");
 //  for(t = transition[0]; t; t = t->nxt) {
 //    print_set(t->to, 0);
 //    fprintf(tl_out, "\n");
 //  }
  for (int i=0; i< t->stateNum; i++){
    fprintf(tl_out, "state %i : %s \n   input: (", i, t->tStates[i].tstateId);
    for (int j=0; j< t->tStates[i].inputNum; j++){
      fprintf(tl_out, "%o, ", t->tStates[i].input[j]);
    }
    fprintf(tl_out, ") output:( %i) \n", t->tStates[i].output);


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

  t_sym_size = calculate_sym_size(p); /* number of predicates */
  if(t_sym_size) t_sym_table = (char **) tl_emalloc(t_sym_size * sizeof(char *));
  t_sym_size = t_sym_size / (8 * sizeof(int)) + 1;
  
//   final_set = make_set(-1, 0);
  tAutomata = build_timed(p); /* generates the alternating automaton */

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