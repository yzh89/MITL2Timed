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
#ifdef TIMED
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
void merge_bin_timed(TAutomata *t1, TAutomata *t2, TAutomata *t);
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

TTrans *dup_ttrans(TTrans *trans)  /* returns the copy of a transition */
{
  TTrans *result;
  if(!trans) return trans;
  result = emalloc_ttrans(1,1);
  return result;
}

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

TState *create_tstate(TState *s, char *tstateId, CGuard *inv, unsigned short *input, unsigned short inputNum, unsigned short output, Node* p){
  s->tstateId = tstateId;
  s->inv = inv;
  
  s->input = input;
  s->inputNum = inputNum;
  s->output = output;  //output true
  if (p){
    s->sym = new_set(3); //3 is symolic set. sym_set_size is used to determine the allocation size
    clear_set(s->sym, 3);
    add_set(s->sym, t_get_sym_id(p->sym->name));
  }
  return s;
}

TTrans *create_ttrans(TTrans *t, CGuard *cguard, int *cIdxs, int clockNum, TState *from, TState *to){
  t->cguard=cguard;
  t->cIdx = new_set(4);
  for (int i=0; i<clockNum ; i++){
    
  }
      // tmp->cguard = malloc(sizeof(CGuard)); 
      // tmp->cguard->nType = PREDICATE;  
      // tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      // tmp->cguard->cCstr->cIdx = cCount;
      // tmp->cguard->cCstr->gType = GREATER; 
      // tmp->cguard->cCstr->bndry = 0;
      // tmp->cIdx[0] = cCount;
      // tmp->from = &s[0];
      // tmp->to = &s[1];
      // tmp = tmp->nxt;
  return t;
}




TAutomata *build_timed(Node *p) /* builds an timed automaton for p */
//TODO change the U_OPER to timed automata
//TODO change logic NOT ADD OR to automata
//TODO linking NOT with U_OPER
{

   TAutomata *t1, *t2;
  
   TTrans *t = (TTrans *)0, *tmp ;
   TState *s;
   TAutomata *tA;
//   int node = already_done(p);
//   if(node >= 0) return transition[node];


  switch (p->ntyp) {

    case TRUE:
      s = (TState *) tl_emalloc(sizeof(TState)*1);

      s[0].tstateId = "true";
      s[0].inv = (CGuard *) 0;
      s[0].input = (unsigned short*) 0;
      s[0].inputNum = 0;
      s[0].output = 1;  //output true

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = (TTrans *)0;
      tA->tStates = s;
      tA->stateNum = 1;
      break;
  //     t = emalloc_atrans();
  //     clear_set(t->to,  0);
  //     clear_set(t->pos, 1);
  //     clear_set(t->neg, 1);
    case FALSE:
      s = (TState *) tl_emalloc(sizeof(TState)*1);
      s[0].tstateId = "true";
      s[0].inv = (CGuard *) 0;
      s[0].input = (unsigned short*) 0;
      s[0].inputNum = 0;
      s[0].output = 1;  //output true

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = (TTrans *)0;
      tA->tStates = s;
      tA->stateNum = 1;
      break;

    case PREDICATE:
      t = emalloc_ttrans(2,1); 
      s = (TState *) tl_emalloc(sizeof(TState)*2);

      s[0].tstateId = malloc (sizeof(char)*(strlen(p->sym->name))+7);
      sprintf(s[0].tstateId, "pred : %s", p->sym->name);
      s[0].inv = (CGuard *) 0;
      s[0].input = malloc(sizeof(unsigned short)*1);
      s[0].input[0] = 1 << t_get_sym_id(p->sym->name);
      s[0].inputNum = 1;
      s[0].output = 1;  
      s[0].sym = new_set(3);
      clear_set(s[0].sym, 3);
      add_set(s[0].sym, t_get_sym_id(p->sym->name));

      s[1].tstateId = malloc (sizeof(char)*(strlen(p->sym->name))+10);
      sprintf(s[1].tstateId, "! pred : %s", p->sym->name);
      s[1].inv = (CGuard *) 0;
      s[1].input = malloc(sizeof(unsigned short)*1);
      s[1].input[0] = 0;
      s[1].inputNum = 1;
      s[1].output = 0;  
      s[1].sym = new_set(3);
      clear_set(s[0].sym, 3);
      add_set(s[0].sym, t_get_sym_id(p->sym->name));
      
      tmp=t;
      // (0 -> 1) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->from = &s[0];
      tmp->to = &s[1];
      tmp = tmp->nxt;

      // (1 -> 0) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->to = &s[0];
      tmp->from = &s[1];
      tmp = tmp->nxt;
      cCount++;

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = t;
      tA->tStates = s;
      tA->stateNum = 2;
      break;
  //   case NOT:
  //     t = emalloc_atrans();
  //     clear_set(t->to,  0);
  //     clear_set(t->pos, 1);
  //     clear_set(t->neg, 1);
  //     add_set(t->neg, get_sym_id(p->lft->sym->name));
  //     break;

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
      s[0].tstateId = "!p";
      s[0].inv = (CGuard *) 0;
      s[0].input = malloc(sizeof(unsigned short)*2);
      s[0].inputNum = 2;
      s[0].input[0] = 0b01;
      s[0].input[1] = 0b00;
      s[0].output = 0;

      s[1].tstateId = "!(p!q)";
      s[1].inv = (CGuard *) 0;
      s[1].input = malloc(sizeof(unsigned short)*1);
      s[1].input[0] = 0b10;
      s[1].output = 0;
      s[1].inputNum = 1;

      s[2].tstateId = "p!q";
      s[2].inv = (CGuard *) 0;
      s[2].input = malloc(sizeof(unsigned short)*1);
      s[2].input[0] = 0b10;
      s[2].inputNum = 1;
      s[2].output = 1;

      s[3].tstateId = "pq";
      s[3].inv = (CGuard *) 0;
      s[3].input = malloc(sizeof(unsigned short)*1);
      s[3].input[0] = 0b11;
      s[3].inputNum = 1;
      s[3].output = 1;

      tmp=t;
      // (0 -> 1) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->from = &s[0];
      tmp->to = &s[1];
      tmp = tmp->nxt;

      // (1 -> 0) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->to = &s[0];
      tmp->from = &s[1];
      tmp = tmp->nxt;

      // (0 -> 2) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->from = &s[0];
      tmp->to = &s[2];
      tmp = tmp->nxt;

      // (0 -> 3) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->from = &s[0];
      tmp->to = &s[3];
      tmp = tmp->nxt;

      // (3 -> 0) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->to = &s[0];
      tmp->from = &s[3];
      tmp = tmp->nxt;

      // (2 -> 3) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->from = &s[2];
      tmp->to = &s[3];
      tmp = tmp->nxt;

      // (3 -> 2) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->to = &s[2];
      tmp->from = &s[3];
      tmp = tmp->nxt;

      // (3 -> 1) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->from = &s[3];
      tmp->to = &s[1];

      cCount++;

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = t;
      tA->tStates = s;
      tA->stateNum = 4;
      merge_bin_timed(t1,t2,tA);
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

      s[0].tstateId = "and";
      s[0].inv = (CGuard *) 0;
      s[0].input = malloc(sizeof(unsigned short)*1);
      s[0].input[0] = 0b11;
      s[0].inputNum = 1;
      s[0].output = 1;  //output the symoblic id of the alphabat

      s[1].tstateId = "! and";
      s[1].inv = (CGuard *) 0;
      s[1].input = malloc(sizeof(unsigned short)*3);
      s[1].inputNum = 3;
      s[1].input[0] = 0b10;
      s[1].input[1] = 0b01;
      s[1].input[2] = 0b00;
      s[1].output = 0;  //output the symoblic id of the alphabat    

      tmp=t;
      // (0 -> 1) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->from = &s[0];
      tmp->to = &s[1];
      tmp = tmp->nxt;

      // (1 -> 0) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->to = &s[0];
      tmp->from = &s[1];
      tmp = tmp->nxt;
      cCount++;

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = t;
      tA->tStates = s;
      tA->stateNum = 2;
      merge_bin_timed(t1,t2,tA);
      break;

    case OR:
      t1= build_timed(p->lft);
      t2= build_timed(p->rgt);

      t = emalloc_ttrans(2,1); 
      s = (TState *) tl_emalloc(sizeof(TState)*2);

      s[0].tstateId = "! or";
      s[0].inv = (CGuard *) 0;
      s[0].input = malloc(sizeof(unsigned short)*1);
      s[0].inputNum = 1;
      s[0].input[0] = 0b00;
      s[0].output = 1;  //output the symoblic id of the alphabat

      s[1].tstateId = "or";
      s[1].inv = (CGuard *) 0;
      s[1].input = malloc(sizeof(unsigned short)*3);
      s[1].inputNum = 3;
      s[1].input[0] = 0b10;
      s[1].input[1] = 0b01;
      s[1].input[2] = 0b11;
      s[1].output = 0;  //output the symoblic id of the alphabat    

      tmp=t;
      // (0 -> 1) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->from = &s[0];
      tmp->to = &s[1];
      tmp = tmp->nxt;

      // (1 -> 0) : z > 0 | z := 0
      tmp->cguard = malloc(sizeof(CGuard)); 
      tmp->cguard->nType = PREDICATE;  
      tmp->cguard->cCstr = malloc(sizeof(CCstr));;
      tmp->cguard->cCstr->cIdx = cCount;
      tmp->cguard->cCstr->gType = GREATER; 
      tmp->cguard->cCstr->bndry = 0;
      tmp->cIdx[0] = cCount;
      tmp->to = &s[0];
      tmp->from = &s[1];
      tmp = tmp->nxt;
      cCount++;

      tA = (TAutomata *) tl_emalloc(sizeof(TAutomata));
      tA->tTrans = t;
      tA->tStates = s;
      tA->stateNum = 2;
      merge_bin_timed(t1,t2,tA);
      break;

    default:
      break;
  }

  // t_transition[ttrans_count] = t;
  // t_label[ttrans_count++] = p; 
  return(tA);
}

/********************************************************************\
|*             Linking the Timed Automata                           *|
\********************************************************************/

void merge_bin_timed(TAutomata *t1, TAutomata *t2, TAutomata *t){

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
      s[k].tstateId = malloc(sizeof(char)*(strlen(t1->tStates[t1StateNum[k]].tstateId)+strlen(t2->tStates[t2StateNum[k]].tstateId)+strlen(t->tStates[i].tstateId) +9));
      sprintf(s[k].tstateId,"(%s , %s) x %s", t1->tStates[t1StateNum[k]].tstateId, t2->tStates[t2StateNum[k]].tstateId, t->tStates[i].tstateId);
      // merge set of symbols
      s[k].sym = new_set(3);
      do_merge_sets(s[k].sym, t1->tStates[t1StateNum[k]].sym, t2->tStates[t2StateNum[k]].sym,3);
      
      // merge invariants
      s[k].inv = malloc(sizeof(CGuard)); 
      if (t1->tStates[t1StateNum[k]].inv && t2->tStates[t2StateNum[k]].inv && t->tStates[i].inv) {
        s[k].inv->nType = AND;
        s[k].inv->cCstr = (CCstr *)0;
        s[k].inv->lft = malloc(sizeof(CGuard));
        s[k].inv->lft->nType = AND;
        s[k].inv->lft->cCstr = (CCstr *)0;
        s[k].inv->lft->lft = t1->tStates[t1StateNum[k]].inv;
        s[k].inv->lft->rgt = t2->tStates[t2StateNum[k]].inv;
        s[k].inv->rgt = t->tStates[i].inv;
      }else if (t1->tStates[t1StateNum[k]].inv && t2->tStates[t2StateNum[k]].inv){
        s[k].inv->nType = AND;
        s[k].inv->cCstr = (CCstr *)0;
        s[k].inv->lft = t1->tStates[t1StateNum[k]].inv;
        s[k].inv->rgt = t2->tStates[t2StateNum[k]].inv;
      }else if (t1->tStates[t1StateNum[k]].inv && t->tStates[i].inv){
        s[k].inv->nType = AND;
        s[k].inv->cCstr = (CCstr *)0;
        s[k].inv->lft = t1->tStates[t1StateNum[k]].inv;
        s[k].inv->rgt = t->tStates[i].inv;
      }else if (t2->tStates[t2StateNum[k]].inv && t->tStates[i].inv){
        s[k].inv->nType = AND;
        s[k].inv->cCstr = (CCstr *)0;
        s[k].inv->lft = t2->tStates[t2StateNum[k]].inv;
        s[k].inv->rgt = t->tStates[i].inv;
      }else if (t1->tStates[t1StateNum[k]].inv){
        s[k].inv= t1->tStates[t1StateNum[k]].inv;
      }else if (t2->tStates[t2StateNum[k]].inv){
        s[k].inv= t2->tStates[t2StateNum[k]].inv;
      }else if (t->tStates[i].inv){
        s[k].inv= t->tStates[i].inv;
      }

      // merge inputs
      s[k].inputNum=0;
      s[k].input= malloc(sizeof(unsigned short)*t1->tStates[t1StateNum[k]].inputNum*t2->tStates[t2StateNum[k]].inputNum);
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
  TTrans *tOut = emalloc_ttrans(1,1);
  while (tt){
    // tt->from = 
    tt=tt->nxt;
  }


}

void merge_timed(){

}

/********************************************************************\
|*                Display of the Timed Automata                     *|
\********************************************************************/

void print_timed() /* dumps the alternating automaton */
{
 //  int i;
 //  ATrans *t;

 //  fprintf(tl_out, "init :\n");
 //  for(t = transition[0]; t; t = t->nxt) {
 //    print_set(t->to, 0);
 //    fprintf(tl_out, "\n");
 //  }
  
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
#endif