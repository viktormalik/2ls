/*******************************************************************\

Module: Template Generator for Calling Contexts

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Template Generator for Calling Contexts

#include <util/find_symbols.h>

#include <ssa/ssa_inliner.h>

#include "template_generator_callingcontext.h"
#include "equality_domain.h"
#include "tpolyhedra_domain.h"

void template_generator_callingcontextt::operator()(
  unsigned _domain_number,
  const local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it,
  bool forward)
{
  domain_number=_domain_number;
  handle_special_functions(SSA); // we have to call that to prevent trouble!

  collect_variables_loop(SSA, forward);
  collect_variables_callingcontext(SSA, n_it, f_it, forward);

  // get domain from command line options
  domain_ptr=instantiate_standard_domains(all_var_specs, SSA);

#if 1
  debug() << "Template variables: " << eom;
  all_var_specs.output(debug(), SSA.ns); debug() << eom;
  debug() << "Template: " << eom;
  domain_ptr->output_domain(debug(), SSA.ns); debug() << eom;
#endif
}

void template_generator_callingcontextt::collect_variables_callingcontext(
  const local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it,
  bool forward)
{
  exprt guard=SSA.guard_symbol(n_it->location);

  assert(f_it->function().id()==ID_symbol); // no function pointers
  irep_idt fname=to_symbol_expr(f_it->function()).get_identifier();
  const local_SSAt &fSSA=ssa_db.get(fname);

  // getting globals at call site
  local_SSAt::var_sett cs_globals_in, globals_in;
  if(forward)
  {
    SSA.get_globals(n_it->location, cs_globals_in, true, false);
      // filter out return values
    globals_in=fSSA.globals_in;
  }
  else
  {
    SSA.get_globals(n_it->location, cs_globals_in, false, true, fname);
      // with return values for function call
    globals_in=fSSA.globals_out;
  }

  for(local_SSAt::var_sett::iterator v_it=cs_globals_in.begin();
      v_it!=cs_globals_in.end(); v_it++)
  {
    symbol_exprt dummy;
    if(ssa_inlinert::find_corresponding_symbol(*v_it, globals_in, dummy) ||
       id2string(v_it->get_identifier()).find("dynamic_object$")!=
       std::string::npos)
    {
      add_var(
        *v_it,
        guard,
        guard,
        guardst::OUT, // the same for both forward and backward
        {},
        all_var_specs);
    }
  }

  // TODO: actually, the context should contain both,
  //       arguments and return values
  if(!forward)
    return;

  // add function arguments
  for(exprt::operandst::const_iterator a_it=f_it->arguments().begin();
      a_it!=f_it->arguments().end(); a_it++)
  {
    std::set<symbol_exprt> args;
    find_symbols(*a_it, args);
    exprt arg=*a_it;
    add_vars(args, guard, guard, guardst::OUT, all_var_specs);
  }
}

var_sett template_generator_callingcontextt::callingcontext_vars()
{
  var_sett vars;
  for(const auto &v : all_var_specs)
  {
    if(v.guards.kind==guardst::OUT)
      vars.insert(v.var);
  }
  return vars;
}
