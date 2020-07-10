/*******************************************************************\

Module: Abstract domain for representing contents of arrays

Author: Viktor Malik <viktor.malik@gmail.com>

\*******************************************************************/
/// \file
/// Abstract domain for representing contents of arrays

#ifndef CPROVER_2LS_DOMAINS_ARRAY_DOMAIN_H
#define CPROVER_2LS_DOMAINS_ARRAY_DOMAIN_H

#include "simple_domain.h"
#include <ssa/local_ssa.h>

class array_domaint:public simple_domaint
{
public:
  array_domaint(
    unsigned int domain_number,
    replace_mapt &renaming_map,
    const var_specst &var_specs,
    const local_SSAt &SSA,
    incremental_solvert *solver):
    simple_domaint(domain_number, renaming_map, SSA.ns),
    SSA(SSA),
    solver(solver)
  {
    make_template(var_specs, SSA.ns);
  }

  // A template row is a single segment of a single array
  //   (lower <= index_var < upper) ==> P(array[index_var])
  //  where P is a predicate in a chosen value domain
  struct template_row_exprt:public simple_domaint::template_row_exprt
  {
    vart array; // array variable
    vart index_var; // index variable of this segment
    exprt lower_bound; // lower segment index
    exprt upper_bound; // upper segment index

    template_row_exprt(
      const vart &array,
      const vart &indexVar,
      const exprt &lowerBound,
      const exprt &upperBound):
      array(array), index_var(indexVar), lower_bound(lowerBound),
      upper_bound(upperBound) {}

    std::vector<exprt> get_row_exprs() override { return {array, index_var}; }

    void output(std::ostream &out, const namespacet &ns) const override;
  };

  // For now, a template row value is a single value which is one of:
  //  - single value stored in all elements of the segment
  //  - TRUE (domain top, any value)
  //  - FALSE (domain bottom, no value)
  struct row_valuet:exprt
  {
    using exprt::operator=;

    exprt get_row_expr(const template_row_exprt &templ_row_expr) const
    {
      if(is_true() || is_false())
        return *this;
      return equal_exprt(
        index_exprt(templ_row_expr.array, templ_row_expr.index_var), *this);
    }
  };

  struct array_valuet:simple_domaint::valuet, std::vector<row_valuet>
  {
    exprt get_row_expr(rowt row, const template_rowt &templ_row) const override
    {
      auto &array_row_expr=dynamic_cast<template_row_exprt &>(*templ_row.expr);
      return (*this)[row].get_row_expr(array_row_expr);
    }

    array_valuet *clone() override { return new array_valuet(*this); }
  };

  std::unique_ptr<domaint::valuet> new_value() override
  {
    return std::unique_ptr<domaint::valuet>(new array_valuet());
  }

  void initialize_value(domaint::valuet &value) override;

  // We have to override row pre- and post-constraints since segment bounds must
  // be added to precondition.
  exprt get_row_pre_constraint(
    rowt row,
    const valuet &row_value) override;
  exprt get_row_post_constraint(
    rowt row,
    const valuet &value) override;

  bool edit_row(const rowt &row, valuet &inv, bool improved) override;

  void project_on_vars(
    domaint::valuet &base_value,
    const var_sett &vars,
    exprt &result) override;

protected:
  void make_template(const var_specst &var_specs, const namespacet &ns);
  void add_segment_row(
    const var_spect &var_spec,
    const exprt &lower,
    const exprt &upper);
  bool order_indices(var_listt &indices, const exprt &array_size);
  bool ordered_indices(
    const exprt &first,
    const exprt &second,
    const exprt &array_size);

  static exprt row_segment_constraint(const template_rowt &row);
  exprt get_current_item_model();

  exprt project_row_on_index(rowt row, const valuet &value, const exprt &index);

  const local_SSAt &SSA;
  incremental_solvert *solver;
};


#endif // CPROVER_2LS_DOMAINS_ARRAY_DOMAIN_H
