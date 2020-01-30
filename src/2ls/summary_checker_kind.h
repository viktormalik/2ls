/*******************************************************************\

Module: Summary Checker for k-induction

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_2LS_SUMMARY_CHECKER_KIND_H
#define CPROVER_2LS_2LS_SUMMARY_CHECKER_KIND_H

#include "summary_checker_base.h"

class summary_checker_kindt:public summary_checker_baset
{
public:
  inline summary_checker_kindt(
      optionst &_options,
      const ssa_heap_analysist &heap_analysis,
      const dynamic_objectst &dynamic_objects):
    summary_checker_baset(_options, heap_analysis, dynamic_objects)
  {
  }

  virtual resultt operator()(const goto_modelt &);
};

#endif
