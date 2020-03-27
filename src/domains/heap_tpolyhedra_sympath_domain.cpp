/*******************************************************************\

Module: Abstract domain for computing invariants in heap-tpolyhedra
        domain for different symbolic paths in program.

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Abstract domain for computing invariants in heap-tpolyhedra domain for
///   different symbolic paths in program.

#include "heap_tpolyhedra_sympath_domain.h"

void heap_tpolyhedra_sympath_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  const heap_tpolyhedra_sympath_valuet &v=
    static_cast<const heap_tpolyhedra_sympath_valuet &>(value);
  for(auto &config : v)
  {
    out << from_expr(ns, "", config.first) << "==>\n";
    heap_tpolyhedra_domain.output_value(out, config.second, ns);
  }
}

void heap_tpolyhedra_sympath_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  heap_tpolyhedra_domain.output_domain(out, ns);
}

void heap_tpolyhedra_sympath_domaint::project_on_vars(
  domaint::valuet &value,
  const var_sett &vars,
  exprt &result)
{
  heap_tpolyhedra_sympath_valuet &v=
    static_cast<heap_tpolyhedra_sympath_valuet &>(value);
  exprt::operandst c;
  for(auto &config : v)
  {
    exprt config_result;
    heap_tpolyhedra_domain.project_on_vars(config.second, vars, config_result);
    c.push_back(and_exprt(config.first, config_result));
  }
  c.push_back(no_loops_path);

  result=c.empty() ? true_exprt() : disjunction(c);
}
