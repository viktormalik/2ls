/*******************************************************************\

Module: Analysis of potential relations among expressions.
        Computes which expressions (mainly symbols) occur in the same
        expression/statement and therefore there may be a relation
        between them. This information can be later used to create
        a more precise analysis template.

Author: Viktor Malik, viktor.malik@gmail.com

\*******************************************************************/

/// \file
/// Analysis of potential relations among expressions.
/// Computes which expressions (mainly symbols) occur in the same
/// expression/statement and therefore there may be a relation between them.
/// This information can be later used to create a more precise analysis
/// template.

#include "expression_dependence.h"

/// Recursively collect all expressions of interest.
void expression_dependence_domaint::collect_exprs_rec(
  const exprt &expr,
  std::set<exprt> &result)
{
  if(expr.id()==ID_symbol)
    result.insert(expr);
  else if(expr.id()==ID_index)
  {
    result.insert(expr);
    // For array access, add the array, too
    auto &arr=to_index_expr(expr).array();
    if(arr.id()==ID_symbol)
      result.insert(arr);
  }
  else
  {
    forall_operands(o_it, expr)collect_exprs_rec(*o_it, result);
  }
}

/// Put all given expressions (and their existing dependencies) into
/// the same dependence set.
void expression_dependence_domaint::make_union(std::set<exprt> &exprs)
{
  if(exprs.empty())
    return;

  auto &first=*exprs.begin();
  for(auto it=std::next(exprs.begin()); it!=exprs.end(); it=std::next(it))
    dep_sets.make_union(first, *it);
}

void expression_dependence_domaint::transform(
  ai_domain_baset::locationt from,
  ai_domain_baset::locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  if(from->is_assign())
  {
    const code_assignt &assign=to_code_assign(from->code);
    std::set<exprt> exprs;
    collect_exprs_rec(assign.lhs(), exprs);
    collect_exprs_rec(assign.rhs(), exprs);
    make_union(exprs);
  }
  else if(from->is_goto() || from->is_assume() || from->is_assert())
  {
    std::set<exprt> exprs;
    collect_exprs_rec(from->guard, exprs);
    make_union(exprs);
  }

  if (from->is_backwards_goto())
    loop_end = from->location_number;
}

bool expression_dependence_domaint::merge(
  const expression_dependence_domaint &other,
  ai_domain_baset::locationt from,
  ai_domain_baset::locationt to)
{
  bool result=false;

  if (other.loop_end)
  {
    if (!(from->is_goto() && to->location_number > other.loop_end))
      if (loop_end != other.loop_end)
      {
        loop_end = other.loop_end;
        result = true;
      }
  }

  if (!loop_end)
    return result;

  for(auto &a : other.dep_sets)
  {
    for(auto &b : other.dep_sets)
    {
      if(other.dep_sets.same_set(a, b) &&
         !dep_sets.same_set(a, b))
      {
        dep_sets.make_union(a, b);
        result=true;
      }
    }
  }
  return result;
}

void expression_dependence_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  out << "Loop: " << loop_end << "\n";
  for(const exprt &e : dep_sets)
  {
    size_t n;
    dep_sets.get_number(e, n);
    out << "    " << dep_sets.find_number(n) << ": " << from_expr(e) << "\n";
  }
}

const expression_dependence_domaint &
expression_dependencet::get_deps_for_ssa_expr(
  const exprt &expr,
  const local_SSAt &SSA)
{
  if (expr.id() == ID_symbol)
  {
    return (*this)[SSA.get_loc_with_symbol_def(to_symbol_expr(expr))];
  }
  else
    assert(false);
}
