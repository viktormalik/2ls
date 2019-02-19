/*******************************************************************\

Module: Combination of heap and template polyhedra abstract domains

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Combination of heap and template polyhedra abstract domains

#include "heap_tpolyhedra_domain.h"

/// Initialize abstract value.
void heap_tpolyhedra_domaint::initialize(domaint::valuet &value)
{
  heap_tpolyhedra_valuet &v=static_cast<heap_tpolyhedra_valuet &>(value);

  heap_domain.initialize(v.heap_value);
  polyhedra_domain.initialize(v.tpolyhedra_value);
}

void heap_tpolyhedra_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  const heap_tpolyhedra_valuet &v=
    static_cast<const heap_tpolyhedra_valuet &>(value);

  heap_domain.output_value(out, v.heap_value, ns);
  polyhedra_domain.output_value(out, v.tpolyhedra_value, ns);
}

void heap_tpolyhedra_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  heap_domain.output_domain(out, ns);
  polyhedra_domain.output_domain(out, ns);
}

void heap_tpolyhedra_domaint::project_on_vars(
  domaint::valuet &value,
  const domaint::var_sett &vars,
  exprt &result)
{
  heap_tpolyhedra_valuet &v=static_cast<heap_tpolyhedra_valuet &>(value);

  exprt heap_result;
  heap_domain.project_on_vars(v.heap_value, vars, heap_result);
  exprt tpolyhedra_result;
  polyhedra_domain.project_on_vars(v.tpolyhedra_value, vars, tpolyhedra_result);

  result=heap_result;
  if(tpolyhedra_result!=true_exprt())
    result=and_exprt(result, tpolyhedra_result);
}

/// Restrict template to a given symbolic path.
/// \param sympath: Symbolic path
void heap_tpolyhedra_domaint::restrict_to_sympath(
  const symbolic_patht &sympath)
{
  heap_domain.restrict_to_sympath(sympath);
  polyhedra_domain.restrict_to_sympath(sympath);
}

/// Reset aux symbols to true (remove all restricitions).
void heap_tpolyhedra_domaint::clear_aux_symbols()
{
  heap_domain.clear_aux_symbols();
  polyhedra_domain.clear_aux_symbols();
}

/// Restrict template to other paths than those specified.
/// \param sympaths: Vector of symbolic paths
void heap_tpolyhedra_domaint::eliminate_sympaths(
  const std::vector<symbolic_patht> &sympaths)
{
  heap_domain.eliminate_sympaths(sympaths);
  polyhedra_domain.eliminate_sympaths(sympaths);
}

/// Undo last restriction.
void heap_tpolyhedra_domaint::undo_restriction()
{
  heap_domain.undo_restriction();
  polyhedra_domain.undo_restriction();
}

bool heap_tpolyhedra_domaint::edit_row(
  const rowt &row,
  valuet &inv,
  bool improved)
{
  return improved;
}

exprt heap_tpolyhedra_domaint::to_pre_constraints(valuet &value)
{
  return true_exprt();
}

void heap_tpolyhedra_domaint::make_not_post_constraints(
  valuet &value,
  exprt::operandst &cond_exprs)
{
}

std::vector<exprt> heap_tpolyhedra_domaint::get_required_smt_values(size_t row)
{
  std::vector<exprt> r;
  return r;
}

void heap_tpolyhedra_domaint::set_smt_values(
  std::vector<exprt> got_values,
  size_t row)
{
}

/*******************************************************************\

Function: heap_tpolyhedra_domaint::identify_invariant_imprecision

  Inputs: TODO

 Outputs: TODO

 Purpose: TODO

\*******************************************************************/
std::vector<std::string> heap_tpolyhedra_domaint::identify_invariant_imprecision(
  const domaint::valuet &value)
{
  const heap_tpolyhedra_valuet &v=
    static_cast<const heap_tpolyhedra_valuet &>(value);

  // invariant identif imprecision for both 'sub-domains'
  // heap domain variables
  std::vector<std::string> ssa_vars=heap_domain.identify_invariant_imprecision(
    v.heap_value);

  // tpolyhedra domain variables
  std::vector<std::string> tpoly_vars=
    polyhedra_domain.identify_invariant_imprecision(v.tpolyhedra_value);

  // concatenate vectors
  ssa_vars.reserve(ssa_vars.size() + tpoly_vars.size());
  ssa_vars.insert(
    ssa_vars.end(),
    std::make_move_iterator(tpoly_vars.begin()),
    std::make_move_iterator(tpoly_vars.end())
  );

  return ssa_vars;
}
