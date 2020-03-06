/*******************************************************************\

Module: Abstract domain for representing contents of arrays

Author: Viktor Malik <viktor.malik@gmail.com>

\*******************************************************************/
/// \file
/// Abstract domain for representing contents of arrays

#include "array_domain.h"
#include <algorithm>
#include <util/arith_tools.h>
#include <ssa/local_ssa.h>

/// Value initialization - LOOP rows are initialized to false (bottom)
///                          IN rows are initialized to true (top)
void array_domaint::initialize_value(domaint::valuet &value)
{
  auto &array_value=dynamic_cast<array_valuet &>(value);
  array_value.resize(templ.size());
  for(auto row=0; row<templ.size(); row++)
  {
    if(templ[row].guards.kind==guardst::IN)
      array_value[row]=true_exprt();
    else
      array_value[row]=false_exprt();
  }
}

/// Row pre-constraint:
///   (pre_guard && segment_constraint) => value_constraint
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

/// Row post-constraint:
///   (post_guard && segment_constraint) => value_constraint
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

/// Row segment constraint:
///   index >= 0 && index < size && index >= lower && index < upper
/// Index expression is type-casted to match the type of boundary expressions.
/// Boundary expressions are guaranteed to have the same type.
exprt array_domaint::row_segment_constraint(const template_rowt &row)
{
  auto row_expr=dynamic_cast<array_domaint::template_row_exprt &>(*row.expr);
  const exprt interval_expr=and_exprt(
    binary_relation_exprt(row_expr.index_var, ID_ge, row_expr.lower_bound),
    binary_relation_exprt(row_expr.index_var, ID_lt, row_expr.upper_bound));
  const exprt bounds_expr=and_exprt(
    binary_relation_exprt(
      row_expr.index_var, ID_ge, from_integer(0, row_expr.index_var.type())),
    binary_relation_exprt(
      row_expr.index_var, ID_lt, to_array_type(row_expr.array.type()).size())
  );
  return and_exprt(bounds_expr, interval_expr);
}

/// Update a row value using the model of an array element that lies in the
/// given segment obtained from the SMT solver.
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
      // For now, we assume that there is just a single written index i
      assert(spec.related_vars.size()==1);
      exprt index_var=spec.related_vars.at(0);
      // Try to find the index variable in var_specs - if found, it means that
      // it has been changed within the loop and the loop-back variant must be
      // used.
      auto index_spec=std::find_if(
        var_specs.begin(), var_specs.end(), [&index_var](const var_spect &v)
        {
          return v.var.id()==ID_symbol &&
                 get_original_name(to_symbol_expr(v.var))==
                 get_original_name(to_symbol_expr(index_var));
        });
      if(index_spec!=var_specs.end())
        index_var=index_spec->var;

      auto &array_type=to_array_type(spec.var.type());
      assert(array_type.is_complete());
      auto &array_size=array_type.size();

      // Ensure that all segment borders have the same type (array size type).
      if(index_var.type()!=array_size.type())
        index_var=typecast_exprt(index_var, array_size.type());

      // The array is hard-partitioned into 3 segments:
      //   {0} ... {i} ... {i + 1} ... {size}
      auto index_plus_one=
        plus_exprt(index_var, from_integer(1, index_var.type()));
      add_segment_row(spec, from_integer(0, array_size.type()), index_var);
      add_segment_row(spec, index_var, index_plus_one);
      add_segment_row(spec, index_plus_one, array_size);
    }
  }
}

/// Add a single segment row to the template.
/// A unique index variable for the segment is created.
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

/// Retrieve model value of the array item that was used as a representative
/// item for the current row segment.
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

/// Projection of the computed invariant on variables.
/// Each segment is projected onto all indices that are used to read from the
/// array corresponding to the given row. This projection is done by replacing
/// the segment index variable by the given read index variable.
/// This ensures that the computed array invariant is applied every time when
/// reading from the given array.
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
    // The row must be projected onto each index expression occurring on RHS
    // for the given array.
    auto array_name=get_original_name(to_symbol_expr(row_expr.array));
    auto &read_indices=SSA.array_index_analysis.read_indices.at(array_name);

    for(auto &read_index_info : read_indices)
    {
      const exprt read_index=SSA.read_rhs(
        read_index_info.index, read_index_info.loc);
      // Row constraint projected on read_index
      c.push_back(project_row_on_index(row, value, read_index));
    }
  }
  result=conjunction(c);
}

/// Get row invariant (i.e. row pre-constraint) projected onto a given index
/// expression.
exprt array_domaint::project_row_on_index(
  simple_domaint::rowt row,
  const simple_domaint::valuet &value,
  const exprt &index)
{
  auto row_expr=dynamic_cast<template_row_exprt &>(*templ[row].expr);
  // Get row pre-constraint
  exprt row_value=get_row_pre_constraint(row, value);
  // Typecast index if needed
  exprt index_expr=index;
  if(index.type()!=row_expr.index_var.type())
    index_expr=typecast_exprt(index, row_expr.index_var.type());
  // Replace row index by the index to project on
  replace_mapt repl_map;
  repl_map[row_expr.index_var]=index_expr;
  replace_expr(repl_map, row_value);
  return row_value;
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
