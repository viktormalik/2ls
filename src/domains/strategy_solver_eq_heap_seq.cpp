//
// Created by vmalik on 5/3/19.
//

#include "strategy_solver_eq_heap_seq.h"

bool strategy_solver_eq_heap_seqt::iterate(strategy_solver_baset::invariantt &_inv)
{
  eq_heap_seq_domaint::eq_heap_seq_valuet &inv=static_cast<eq_heap_seq_domaint::eq_heap_seq_valuet &>(_inv);

  if (!equality_done) {
    if (!equality_solver.iterate(inv.equality_value))
      equality_done=true;
    return true;
  } else {
    return heap_solver.iterate(inv.heap_value);
  }
}

void
strategy_solver_eq_heap_seqt::set_message_handler(message_handlert &_message_handler)
{
  equality_solver.set_message_handler(_message_handler);
  heap_solver.set_message_handler(_message_handler);
}
