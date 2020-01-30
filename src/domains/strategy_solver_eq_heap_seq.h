//
// Created by vmalik on 5/3/19.
//

#ifndef CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_EQ_HEAP_SEQ_H
#define CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_EQ_HEAP_SEQ_H


#include "strategy_solver_base.h"
#include "eq_heap_seq_domain.h"
#include "strategy_solver_equality.h"
#include "strategy_solver_heap.h"
#include "strategy_solver_heap_tpolyhedra_sympath.h"

class strategy_solver_eq_heap_seqt:public strategy_solver_baset
{
public:
  strategy_solver_eq_heap_seqt(
    eq_heap_seq_domaint &_eq_heap_seq_domain,
    incremental_solvert &_solver,
    const local_SSAt &SSA,
    const exprt &precondition,
    message_handlert &message_handler,
    template_generator_baset &template_generator):
    strategy_solver_baset(_solver, SSA.ns),
    eq_heap_seq_domain(_eq_heap_seq_domain),
    equality_solver(eq_heap_seq_domain.equality_domain, _solver, SSA.ns),
    heap_solver(
      eq_heap_seq_domain.heap_domain, _solver, SSA, precondition,
      message_handler, template_generator) {}

  virtual bool iterate(invariantt &_inv) override;

  virtual void set_message_handler(message_handlert &_message_handler) override;
protected:
  eq_heap_seq_domaint &eq_heap_seq_domain;

  strategy_solver_equalityt equality_solver;
  strategy_solver_heap_tpolyhedra_sympatht heap_solver;

  bool equality_done = false;
};


#endif //CPROVER_2LS_DOMAINS_STRATEGY_SOLVER_EQ_HEAP_SEQ_H
