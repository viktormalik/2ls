/*******************************************************************\

Module: Summary Checker for k-induction

Author: Peter Schrammel

\*******************************************************************/

#include <goto-instrument/k_induction.h>
#include <domains/heap_tpolyhedra_domain.h>
#include <goto-instrument/unwind.h>
#include "summary_checker_kind.h"

/*******************************************************************\

Function: summary_checker_kindt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

property_checkert::resultt summary_checker_kindt::operator()(
  goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  // SSA_functions(goto_model, ns, heap_analysis);

  // ssa_unwinder.init(true, false);

  property_checkert::resultt result=property_checkert::UNKNOWN;
  unsigned max_unwind=options.get_unsigned_int_option("unwind");
  unsigned give_up_invariants=
    options.get_unsigned_int_option("give-up-invariants");
  status() << "Max-unwind is " << max_unwind << eom;
  // ssa_unwinder.init_localunwinders();

  goto_unwindt goto_unwind;

  for(unsigned unwind=0; unwind<=max_unwind; unwind++)
  {
    status() << "Unwinding (k=" << unwind << ")" << eom;

    // TODO: recompute only functions with loops
    summary_db.mark_recompute_all();

    goto_unwind(goto_model.goto_functions, unwind, goto_unwindt::CONTINUE);
    goto_model.goto_functions.compute_location_numbers();
    goto_model.goto_functions.compute_loop_numbers();
    goto_model.goto_functions.compute_target_numbers();
    goto_model.goto_functions.compute_incoming_edges();
    // ssa_unwinder.unwind_all(unwind);
//    if (unwind > 0)
//      k_induction(goto_model.goto_functions, false, true, unwind);
//    else
//    {
//      k_induction(goto_model.goto_functions, true, false, unwind);
//    }
    // Maybe should be here, don't know yet
    SSA_functions(goto_model, ns, heap_analysis);
    ssa_db.get("_start").output(std::cout);
    ssa_unwinder.init(false, false);
    // ssa_unwinder.init_localunwinders();

    result=check_properties();
    bool magic_limit_not_reached=
      unwind<give_up_invariants ||
      !options.get_bool_option("competition-mode");
    if(result==property_checkert::UNKNOWN &&
       !options.get_bool_option("havoc") &&
       magic_limit_not_reached)
    {
      summarize(goto_model);
      result=check_properties();
    }

    if(result==property_checkert::PASS)
    {
      status() << "k-induction proof found after "
         << unwind << " unwinding(s)" << eom;
      break;
    }
    else if(result==property_checkert::FAIL)
    {
      status() << "k-induction counterexample found after "
         << unwind << " unwinding(s)" << eom;
      break;
    }
  }
  report_statistics();
  return result;
}

