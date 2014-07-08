/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_SSA_ANALYZER_H
#define DELTACHECK_SSA_ANALYZER_H

#include <util/replace_expr.h>

#include "../ssa/local_ssa.h"
#include "strategy_solver_base.h"

class ssa_analyzert : public messaget
{
public:
  typedef strategy_solver_baset::constraintst constraintst;
  typedef strategy_solver_baset::var_listt var_listt;

  explicit ssa_analyzert(const namespacet &_ns, 
                         const optionst &_options)
    : ns(_ns),
      options(_options),
      inv_inout(true_exprt()),
      inv_loop(true_exprt())
  {
  }  

  void operator()(local_SSAt &SSA);

  void get_summary(exprt &result);
  void get_loop_invariants(exprt &result);

protected:
  const namespacet &ns;
  const optionst &options;
  exprt inv_inout;
  exprt inv_loop;
  unsigned iteration_number;
  
  replace_mapt renaming_map;


  // functions for extracting information for template generation

  void collect_variables(const local_SSAt &SSA,
			 domaint::var_specst &var_specs);

  domaint::var_specst filter_template_domain(const domaint::var_specst& var_specs);
  domaint::var_specst filter_equality_domain(const domaint::var_specst& var_specs);
  void add_var(const domaint::vart &var_to_add, 			    
	       const domaint::guardt &pre_guard, 
	       const domaint::guardt &post_guard,
	       const domaint::kindt &kind,
	       domaint::var_specst &var_specs);
  void add_vars(const var_listt &vars_to_add, 			    
		const domaint::guardt &pre_guard, 
		const domaint::guardt &post_guard,
		const domaint::kindt &kind,
		domaint::var_specst &var_specs);
  void add_vars(const local_SSAt::var_listt &vars_to_add,
		const domaint::guardt &pre_guard, 
		const domaint::guardt &post_guard,
		const domaint::kindt &kind,
		domaint::var_specst &var_specs);
  void add_vars(const local_SSAt::var_sett &vars_to_add,
		const domaint::guardt &pre_guard, 
		const domaint::guardt &post_guard,
		const domaint::kindt &kind,
		domaint::var_specst &var_specs);

};


#endif