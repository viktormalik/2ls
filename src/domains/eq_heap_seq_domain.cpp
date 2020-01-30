//
// Created by vmalik on 5/3/19.
//

#include "eq_heap_seq_domain.h"

void eq_heap_seq_domaint::initialize(domaint::valuet &value)
{
  eq_heap_seq_valuet &v=static_cast<eq_heap_seq_valuet &>(value);

  equality_domain.initialize(v.equality_value);
  heap_domain.initialize(v.heap_value);
}

void eq_heap_seq_domaint::output_value(
  std::ostream &out,
  const domaint::valuet &value,
  const namespacet &ns) const
{
  const eq_heap_seq_valuet &v=static_cast<const eq_heap_seq_valuet &>(value);

  equality_domain.output_value(out, v.equality_value, ns);
  heap_domain.output_value(out, v.heap_value, ns);
}

void eq_heap_seq_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  equality_domain.output_domain(out, ns);
  heap_domain.output_domain(out, ns);
}

void eq_heap_seq_domaint::project_on_vars(
  domaint::valuet &value,
  const domaint::var_sett &vars,
  exprt &result)
{
  eq_heap_seq_valuet &v=static_cast<eq_heap_seq_valuet &>(value);

  exprt equality_result;
  equality_domain.project_on_vars(v.equality_value, vars, equality_result);
  exprt heap_result;
  heap_domain.project_on_vars(v.heap_value, vars, heap_result);

  result = equality_result;
  if (heap_result!=true_exprt())
    result = and_exprt(result, heap_result);
}
