/*******************************************************************\

Module: Analysis of expressions used as array indices

Author: Viktor Malik, imalik@fit.vutbr.cz

\*******************************************************************/

/// \file
/// Analysis of expressions used as array indices

#include "array_index_analysis.h"

void array_index_domaint::transform(
  ai_domain_baset::locationt from,
  ai_domain_baset::locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  if(from->is_assign())
  {
    const code_assignt &code_assign=to_code_assign(from->code);
    collect_lhs_indices(code_assign.lhs(), from);
    collect_rhs_indices(code_assign.rhs(), from, ai);
  }
  else if(from->is_goto() || from->is_assert())
  {
    collect_rhs_indices(from->guard, from, ai);
  }
}

bool array_index_domaint::merge(
  const array_index_domaint &other,
  ai_domain_baset::locationt from,
  ai_domain_baset::locationt to)
{
  bool changed=false;
  for(auto &other_array_indices : other.written_indices)
  {
    auto array_indices=written_indices.find(other_array_indices.first);
    if(array_indices==written_indices.end())
    {
      // Array has not been assigned to before - copy all indices
      written_indices.emplace(
        other_array_indices.first, other_array_indices.second);
      changed=true;
    }
    else
    {
      // Array has been assigned to before - do union of indices
      size_t old_size=array_indices->second.size();
      array_indices->second.insert(
        other_array_indices.second.begin(), other_array_indices.second.end());
      if(array_indices->second.size()!=old_size)
        changed=true;
    }
  }
  return changed;
}

void array_index_domaint::collect_lhs_indices(const exprt &expr, locationt loc)
{
  collect_indices(expr, loc, written_indices);
}

void array_index_domaint::collect_rhs_indices(
  const exprt &expr,
  locationt loc,
  ai_baset &ai)
{
  auto &read_indices=dynamic_cast<array_index_analysist &>(ai).read_indices;
  collect_indices(expr, loc, read_indices);
}

void array_index_domaint::collect_indices(
  const exprt &expr,
  ai_domain_baset::locationt loc,
  array_index_domaint::index_mapt &dest_map)
{
  if(expr.id()==ID_index)
  {
    // Get array name
    auto &array=to_index_expr(expr).array();
    if(array.id()==ID_symbol)
    {
      const irep_idt array_id=to_symbol_expr(array).get_identifier();

      // Index may be a typecast
      exprt index=to_index_expr(expr).index();
      if(index.id()==ID_typecast)
        index=to_typecast_expr(index).op();

      // Insert index into given index map
      dest_map[array_id].emplace(index, loc);
    }
  }
  else
  {
    forall_operands(op, expr)
    {
      collect_indices(*op, loc, dest_map);
    }
  }
}

void array_index_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  for(auto &indices : written_indices)
  {
    out << indices.first << " (written) : ";
    for(auto &index_info : indices.second)
      out << " " << from_expr(ns, "", index_info.index);
    out << "\n";
  }
}

void array_index_analysist::output(
  const namespacet &ns,
  const goto_programt &goto_program,
  const irep_idt &identifier,
  std::ostream &out) const
{
  ai_baset::output(ns, goto_program, identifier, out);

  for(auto &indices : read_indices)
  {
    out << indices.first << " (read) : ";
    for(auto &index_info : indices.second)
      out << " " << from_expr(ns, "", index_info.index);
    out << "\n";
  }
}
