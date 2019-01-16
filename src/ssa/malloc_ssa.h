/*******************************************************************\

Module: SSA for malloc()

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_2LS_SSA_MALLOC_SSA_H
#define CPROVER_2LS_SSA_MALLOC_SSA_H

#include <ssa/dynamic_object.h>
#include <util/std_code.h>
#include <goto-programs/goto_model.h>

dynamic_objectt malloc_ssa(
  exprt &,
  unsigned int loc_number,
  symbol_tablet &,
  bool is_concrete,
  bool alloc_concrete);

dynamic_objectst replace_malloc(goto_modelt &goto_model, bool alloc_concrete);

void allow_record_malloc(goto_modelt &goto_model);
void allow_record_memleak(goto_modelt &goto_model);

#endif
