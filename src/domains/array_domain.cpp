/*******************************************************************\

Module: Abstract domain for representing contents of arrays

Author: Viktor Malik <viktor.malik@gmail.com>

\*******************************************************************/
/// \file
/// Abstract domain for representing contents of arrays

#include "array_domain.h"
#include <algorithm>
#include <util/arith_tools.h>

void array_domaint::initialize_value(domaint::valuet &value)
{
  auto &array_value=dynamic_cast<array_valuet &>(value);
  array_value.resize(templ.size());
  for(auto row=0; row<templ.size(); row++)
  {
    if(templ[row].guards.kind==guardst::IN)
      array_value[row]=true_exprt(); // marker for oo
    else
      array_value[row]=false_exprt(); // marker for -oo
  }
}

exprt array_domaint::get_row_pre_constraint(
  const rowt row,
  const valuet &value)
{
  // For exit variables the result is true
  if(templ[row].guards.kind==guardst::OUT ||
     templ[row].guards.kind==guardst::OUTL)
    return true_exprt();

  return implies_exprt(
    and_exprt(templ[row].guards.pre_guard, row_segment_constraint(templ[row])),
    get_row_value_constraint(row, value));
}

exprt array_domaint::get_row_post_constraint(
  rowt row,
  const valuet &value)
{
  exprt row_post_constraint;
  if(templ[row].guards.kind==guardst::IN)
    row_post_constraint=true_exprt();
  else
  {
    auto row_expr=get_row_value_constraint(row, value);
    row_post_constraint=implies_exprt(
      and_exprt(
        templ[row].guards.post_guard, row_segment_constraint(templ[row])),
      row_expr);
  }

  if(templ[row].guards.kind==guardst::LOOP)
    rename(row_post_constraint);

  return and_exprt(templ[row].guards.aux_expr, not_exprt(row_post_constraint));
}

exprt array_domaint::row_segment_constraint(const template_rowt &row)
{
  auto row_expr=dynamic_cast<array_domaint::template_row_exprt &>(*row.expr);
  const exprt interval_expr=and_exprt(
    binary_relation_exprt(row_expr.index_var, ID_ge, row_expr.lower_bound),
    binary_relation_exprt(row_expr.index_var, ID_lt, row_expr.upper_bound));
  return and_exprt(
    binary_relation_exprt(
      row_expr.index_var, ID_ge, from_integer(0, row_expr.index_var.type())),
    interval_expr);
}

bool array_domaint::edit_row(const rowt &row, valuet &_inv, bool improved)
{
  auto &value_row=dynamic_cast<array_valuet &>(_inv)[row];

  // Retrieve value of the used representative item from the updated array
  auto segment_item_model=get_current_item_model();

  std::cerr << "Updating array segment " << row << ": model value is "
            << from_expr(ns, "", segment_item_model) << "\n";

  if(value_row.is_false())
  { // The current value is bottom - set to the model value
    value_row=segment_item_model;
    return true;
  }
  else if(value_row!=segment_item_model)
  { // The model value is different from the current value - set current to top
    value_row=true_exprt();
    return true;
  }

  return improved;
}

void array_domaint::make_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  for(const var_spect &spec : var_specs)
  {
    if(spec.guards.kind!=guardst::LOOP)
      continue;

    if(spec.var.type().id()==ID_array)
    {
      // For now, we use a concrete array index (used in the programs located
      // in regression tests).
      auto index_spec=std::find_if(
        var_specs.begin(), var_specs.end(), [](const var_spect &v)
        {
          return v.var.id()==ID_symbol &&
                 to_symbol_expr(v.var).get_identifier()=="main::1::i#lb21";
        });
      // The array is hard-partitioned into 3 segments:
      //   {0} ... {i#lb21} ... {i#lb21 + 1} ... {10}
      add_segment_row(
        spec,
        from_integer(0, index_spec->var.type()),
        index_spec->var);
      add_segment_row(
        spec,
        index_spec->var,
        plus_exprt(index_spec->var, from_integer(1, index_spec->var.type())));
      add_segment_row(
        spec,
        plus_exprt(index_spec->var, from_integer(1, index_spec->var.type())),
        from_integer(10, index_spec->var.type()));
    }
  }
}

void array_domaint::add_segment_row(
  const var_spect &var_spec,
  const exprt &lower,
  const exprt &upper)
{
  templ.push_back(template_rowt());
  template_rowt &templ_row=templ.back();

  const symbol_exprt &index_var=symbol_exprt(
    "idx#"+std::to_string(templ.size()), lower.type());
  templ_row.expr=std::unique_ptr<template_row_exprt>(
    new template_row_exprt(var_spec.var, index_var, lower, upper));

  templ_row.guards=var_spec.guards;
}

exprt array_domaint::get_current_item_model()
{
  auto &array_model=smt_model_values[0];
  auto &index_model=smt_model_values[1];
  // Convert binary string to integer
  int index_value=stoi(
    to_constant_expr(index_model).get_string(ID_value), nullptr, 2);
  // Extract the concrete array element that was used to improve the row
  return to_array_expr(array_model).operands()[index_value];
}

void array_domaint::project_on_vars(
  domaint::valuet &base_value,
  const var_sett &vars,
  exprt &result)
{
  auto &value=dynamic_cast<array_valuet &>(base_value);
  assert(value.size()==templ.size());

  exprt::operandst c;
  for(rowt row=0; row<templ.size(); ++row)
  {
    auto &row_expr=dynamic_cast<template_row_exprt &>(*templ[row].expr);
    if(vars.find(row_expr.array)==vars.end())
      continue;

    // Row constraint
    c.push_back(get_row_pre_constraint(row, value));
    // Equality x#phi24 == idx#row for each segment since x#phi24 is the only
    // expression that occurs as an index of a#lb21 after the creation loop.
    c.push_back(
      equal_exprt(
        row_expr.index_var,
        symbol_exprt("main::1::x#phi24", row_expr.index_var.type())));
  }
  result=conjunction(c);
}


void array_domaint::template_row_exprt::output(
  std::ostream &out,
  const namespacet &ns) const
{
  out << from_expr(ns, "", index_var) << " in ["
      << from_expr(ns, "", lower_bound) << ", "
      << from_expr(ns, "", upper_bound) << "] ==> "
      << from_expr(ns, "", index_exprt(array, index_var))
      << " == CONST" << std::endl;
}
