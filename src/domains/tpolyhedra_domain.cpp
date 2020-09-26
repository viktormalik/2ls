/*******************************************************************\

Module: Template polyhedra domain

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Template polyhedra domain

#ifdef DEBUG
#include <iostream>
#include <langapi/languages.h>
#endif

#include <util/find_symbols.h>
#include <util/i2string.h>
#include <util/simplify_expr.h>

#include "tpolyhedra_domain.h"
#include "util.h"
#include "domain.h"

#define SYMB_BOUND_VAR "symb_bound#"

#define ENABLE_HEURISTICS

void tpolyhedra_domaint::initialize(valuet &value)
{
#if 0
  if(templ.size()==0)
    return domaint::initialize(value);
#endif

  templ_valuet &v=static_cast<templ_valuet&>(value);
  v.resize(templ.size());
  for(std::size_t row=0; row<templ.size(); row++)
  {
    if(templ[row].kind==IN)
      v[row]=true_exprt(); // marker for oo
    else
      v[row]=false_exprt(); // marker for -oo
  }
}

std::vector<exprt> tpolyhedra_domaint::get_required_smt_values(size_t row)
{
  std::vector<exprt> r;
  r.push_back(strategy_value_exprs[row]);
  return r;
}

void tpolyhedra_domaint::set_smt_values(
  std::vector<exprt> got_values,
  size_t row)
{
  value=got_values[0];
}

bool tpolyhedra_domaint::edit_row(const rowt &row, valuet &_inv, bool improved)
{
    tpolyhedra_domaint::templ_valuet &inv=
        static_cast<tpolyhedra_domaint::templ_valuet &>(_inv);
    set_row_value(row, simplify_const(value), inv);
    return true;
}

void tpolyhedra_domaint::join(valuet &value1, const valuet &value2)
{
#if 0
  if(templ.size()==0)
    return domaint::join(value1, value2);
#endif

  templ_valuet &v1=static_cast<templ_valuet&>(value1);
  const templ_valuet &v2=static_cast<const templ_valuet&>(value2);
  assert(v1.size()==templ.size());
  assert(v1.size()==v2.size());
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    if(is_row_value_inf(v1[row]) || is_row_value_inf(v2[row]))
      v1[row]=true_exprt();
    else if(is_row_value_neginf(v1[row]))
      v1[row]=v2[row];
    else if(!is_row_value_neginf(v2[row]))
    {
      if(less_than(v1[row], v2[row]))
        v1[row]=v2[row];
    }
  }
}

tpolyhedra_domaint::row_valuet tpolyhedra_domaint::between(
  const row_valuet &lower, const row_valuet &upper)
{
  if(lower.type()==upper.type() &&
     (lower.type().id()==ID_signedbv || lower.type().id()==ID_unsignedbv))
  {
    typet type=lower.type();
    mp_integer vlower, vupper;
    to_integer(lower, vlower);
    to_integer(upper, vupper);
    assert(vupper>=vlower);
    if(vlower+1==vupper)
      return from_integer(vlower, lower.type()); // floor

#ifdef ENABLE_HEURISTICS
    // heuristics
    if(type.id()==ID_unsignedbv)
    {
      mp_integer vlargest=to_unsignedbv_type(type).largest();
      if(vlower==mp_integer(0) && vupper==vlargest)
        return from_integer(mp_integer(1), type);
      if(vlower==mp_integer(1) && vupper==vlargest)
        return from_integer(mp_integer(vupper-1), type);
      if(vlower==mp_integer(1) && vupper==vlargest-1)
        return from_integer(mp_integer(2), type);
      if(vlower<mp_integer(128) && vupper==vlargest)
        return from_integer(vlargest-1, type);
      if(vlower<mp_integer(128) && vupper==vlargest-1)
        return from_integer(mp_integer(255), type);
    }
    if(type.id()==ID_signedbv)
    {
      mp_integer vlargest=to_signedbv_type(type).largest();
      if(vlower==-vlargest && vupper==vlargest)
        return from_integer(mp_integer(0), type);
      if(vlower==mp_integer(1) && vupper==vlargest)
        return from_integer(mp_integer(2), type);
      if(vlower==mp_integer(-1) && vupper==vlargest)
        return from_integer(mp_integer(0), type);
      if(vlower==mp_integer(0) &&  vupper==vlargest)
        return from_integer(mp_integer(vupper-1), type);
      if(vlower==-(vlargest/2) && vupper==vlargest)
        return from_integer(mp_integer(vlargest/2+1), type);
      if(vlower==vlargest/2+1 && vupper==vlargest)
        return from_integer(mp_integer(vlargest/2+2), type);
      if(vlower==mp_integer(0) && vupper==vlargest-1)
        return from_integer(mp_integer(1), type);
      if(vlower<mp_integer(128) && vupper==vlargest)
        return from_integer(vlargest-1, type);
      if(vlower<mp_integer(128) && vupper==vlargest-1)
        return from_integer(mp_integer(255), type);
      if(vlower<mp_integer(-128) && vupper==mp_integer(255))
        return from_integer(mp_integer(-255), type);
    }
#endif

    return from_integer((vupper+vlower)/2, type);
  }
  if(lower.type().id()==ID_floatbv && upper.type().id()==ID_floatbv)
  {
    ieee_floatt vlower(to_constant_expr(lower));
    ieee_floatt vupper(to_constant_expr(upper));
    if(vlower.get_sign()==vupper.get_sign())
    {
      mp_integer plower=vlower.pack(); // compute "median" float number
      mp_integer pupper=vupper.pack();
#if 0
      assert(pupper>=plower);
#endif
      ieee_floatt res(to_floatbv_type(lower.type()));
      res.unpack((plower+pupper)/2); // ...by computing integer mean
      return res.to_expr();
    }
    ieee_floatt res(to_floatbv_type(lower.type()));
    res.make_zero();
    return res.to_expr();
  }
  assert(false); // types do not match or are not supported
}

bool tpolyhedra_domaint::less_than(const row_valuet &v1, const row_valuet &v2)
{
  if(v1.type()==v2.type() &&
     (v1.type().id()==ID_signedbv || v1.type().id()==ID_unsignedbv))
  {
    mp_integer vv1, vv2;
    to_integer(v1, vv1);
    to_integer(v2, vv2);
    return vv1<vv2;
  }
  if(v1.type().id()==ID_floatbv && v2.type().id()==ID_floatbv)
  {
    ieee_floatt vv1(to_constant_expr(v1));
    ieee_floatt vv2(to_constant_expr(v2));
    return vv1<vv2;
  }
  assert(false); // types do not match or are not supported
}

/// pre_guard==> row_expr<=row_value
exprt tpolyhedra_domaint::get_row_constraint(
  const rowt &row,
  const row_valuet &row_value)
{
  assert(row<templ.size());
  if(is_row_value_neginf(row_value))
    return false_exprt();
  if(is_row_value_inf(row_value))
    return true_exprt();
  return binary_relation_exprt(templ[row].expr, ID_le, row_value);
}

/// pre_guard==> row_expr<=row_value
exprt tpolyhedra_domaint::get_row_pre_constraint(
  const rowt &row,
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row=templ[row];
  kindt k=templ_row.kind;
  if(k==OUT || k==OUTL)
    return true_exprt();
  return implies_exprt(templ_row.pre_guard, get_row_constraint(row, row_value));
}

/// pre_guard==> row_expr<=row_value
exprt tpolyhedra_domaint::get_row_pre_constraint(
  const rowt &row,
  const templ_valuet &value)
{
  assert(value.size()==templ.size());
  return get_row_pre_constraint(row, value[row]);
}

/// row_expr<=row_value
exprt tpolyhedra_domaint::get_row_post_constraint(
  const rowt &row,
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row=templ[row];
  if(templ_row.kind==IN)
    return true_exprt();

#if 0 // TEST for disjunctive domains
  if(templ.size()==4)
  {
    exprt guard=true_exprt();
    if(row==1 || row==3)
      return guard=
        binary_relation_exprt(
          templ_row.expr,
          ID_gt,
          from_integer(mp_integer(0), templ_row.expr.type()));
    else
      return guard=
        binary_relation_exprt(
          templ_row.expr,
          ID_lt,
          from_integer(mp_integer(0), templ_row.expr.type()));
    if(is_row_value_neginf(row_value))
      return implies_exprt(
        templ_row.post_guard,
        implies_exprt(guard, false_exprt()));
    if(is_row_value_inf(row_value))
      return implies_exprt(
        templ_row.post_guard,
        implies_exprt(guard, true_exprt()));
    exprt c=implies_exprt(
      templ_row.post_guard,
      implies_exprt(
        guard,
        binary_relation_exprt(templ_row.expr, ID_le, row_value)));
  }
#endif

  exprt c=
    implies_exprt(templ_row.post_guard, get_row_constraint(row, row_value));
  if(templ_row.kind==LOOP)
    rename(c);
  return c;
}

/// row_expr<=row_value
exprt tpolyhedra_domaint::get_row_post_constraint(
  const rowt &row,
  const templ_valuet &value)
{
  assert(value.size()==templ.size());
  return get_row_post_constraint(row, value[row]);
}

/// /\_all_rows ( pre_guard==> (row_expr<=row_value) )
exprt tpolyhedra_domaint::to_pre_constraints(valuet &_value)
{
  tpolyhedra_domaint::templ_valuet &value=
    static_cast<tpolyhedra_domaint::templ_valuet &>(_value);
  assert(value.size()==templ.size());

  exprt::operandst c;
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    c.push_back(get_row_pre_constraint(row, value[row]));
  }
  return conjunction(c);
}

/// for all rows !(post_guard==> (row_expr<=row_value)) to be connected
/// disjunctively
void tpolyhedra_domaint::make_not_post_constraints(
  valuet &_value,
  exprt::operandst &cond_exprs)
{
  tpolyhedra_domaint::templ_valuet &value=
    static_cast<tpolyhedra_domaint::templ_valuet &>(_value);
  assert(value.size()==templ.size());
  cond_exprs.resize(templ.size());
  strategy_value_exprs.resize(templ.size());

  exprt::operandst c;
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    strategy_value_exprs[row]=templ[row].expr;
    rename(strategy_value_exprs[row]);
    cond_exprs[row]=
      and_exprt(
        templ[row].aux_expr,
        not_exprt(get_row_post_constraint(row, value)));
  }
}

/// generates symbolic value symbol
symbol_exprt tpolyhedra_domaint::get_row_symb_value(const rowt &row)
{
  assert(row<templ.size());
  return symbol_exprt(
    SYMB_BOUND_VAR+i2string(domain_number)+"$"+
    i2string(row), templ[row].expr.type());
}

/// pre_guard==> (row_expr<=symb_value)
exprt tpolyhedra_domaint::get_row_symb_pre_constraint(
  const rowt &row,
  const row_valuet &row_value)
{
  assert(row<templ.size());
  const template_rowt &templ_row=templ[row];
  if(templ_row.kind==OUT || templ_row.kind==OUTL)
    return true_exprt();
  return implies_exprt(
    templ_row.pre_guard,  // REMARK: and_expr==> loop15 regression
    binary_relation_exprt(templ_row.expr, ID_le, get_row_symb_value(row)));
}

/// post_guard && (row_expr >= row_symb_value)  (!!!)
exprt tpolyhedra_domaint::get_row_symb_post_constraint(const rowt &row)
{
  assert(row<templ.size());
  const template_rowt &templ_row=templ[row];
  if(templ_row.kind==IN)
    return true_exprt();
  exprt c=and_exprt(
    templ_row.post_guard,
    binary_relation_exprt(templ_row.expr, ID_ge, get_row_symb_value(row)));
  rename(c);
  c=and_exprt(
    c, not_exprt(equal_exprt(get_row_symb_value(row), templ_row.expr)));
  return and_exprt(templ_row.aux_expr, c);
}

/// pre_guard==> (row_expr<=symb_row_value)
exprt tpolyhedra_domaint::to_symb_pre_constraints(const templ_valuet &value)
{
  assert(value.size()==templ.size());
  exprt::operandst c;
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    c.push_back(get_row_symb_pre_constraint(row, value[row]));
  }
  return conjunction(c);
}

/// pre_guard==> (row_expr<=symb_row_value)
exprt tpolyhedra_domaint::to_symb_pre_constraints(
  const templ_valuet &value,
  const std::set<rowt> &symb_rows)
{
  assert(value.size()==templ.size());
  exprt::operandst c;
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    if(symb_rows.find(row)!=symb_rows.end())
      c.push_back(get_row_symb_pre_constraint(row, value[row]));
    else
      c.push_back(get_row_pre_constraint(row, value[row]));
  }
  return conjunction(c);
}

/// /\_i post_guard==> (row_expr >= symb_row_value)
exprt tpolyhedra_domaint::to_symb_post_constraints(
  const std::set<rowt> &symb_rows)
{
  exprt::operandst c;
  for(const auto &row : symb_rows)
  {
    c.push_back(get_row_symb_post_constraint(row));
  }
  return conjunction(c);
}

/// row_value_value<=symb_row
exprt tpolyhedra_domaint::get_row_symb_value_constraint(
  const rowt &row,
  const row_valuet &row_value,
  bool geq)
{
  if(is_row_value_neginf(row_value))
    return false_exprt();
  if(is_row_value_inf(row_value))
    return true_exprt();
  exprt c=binary_relation_exprt(
    get_row_symb_value(row),
    geq ? ID_ge : ID_le,
    row_value);
  return c;
}


tpolyhedra_domaint::row_valuet tpolyhedra_domaint::get_row_value(
  const rowt &row,
  const templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  return value[row];
}

void tpolyhedra_domaint::project_on_vars(
  valuet &value,
  const var_sett &vars,
  exprt &result)
{
#if 0
  if(templ.size()==0)
    return domaint::project_on_vars(value, vars, result);
#endif

  const templ_valuet &v=static_cast<const templ_valuet &>(value);

  assert(v.size()==templ.size());
  exprt::operandst c;
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    const template_rowt &templ_row=templ[row];

    std::set<symbol_exprt> symbols;
    find_symbols(templ_row.expr, symbols);

    bool pure=true;
    for(const auto &symbol : symbols)
    {
      if(!vars.empty() && vars.find(symbol)==vars.end())
      {
        pure=false;
        break;
      }
    }
    if(!pure)
      continue;

    const row_valuet &row_v=v[row];
    const exprt row_constraint=get_row_constraint(row, row_v);
    if(templ_row.kind==LOOP)
      c.push_back(implies_exprt(templ_row.pre_guard, row_constraint));
    else
      c.push_back(row_constraint);
  }
  result=conjunction(c);
}

void tpolyhedra_domaint::set_row_value(
  const rowt &row,
  const tpolyhedra_domaint::row_valuet &row_value,
  templ_valuet &value)
{
  assert(row<value.size());
  assert(value.size()==templ.size());
  value[row]=row_value;
}

tpolyhedra_domaint::row_valuet tpolyhedra_domaint::get_max_row_value(
  const tpolyhedra_domaint::rowt &row)
{
  const template_rowt &templ_row=templ[row];
  if(templ_row.expr.type().id()==ID_signedbv)
  {
    return to_signedbv_type(templ_row.expr.type()).largest_expr();
  }
  if(templ_row.expr.type().id()==ID_unsignedbv)
  {
    return to_unsignedbv_type(templ_row.expr.type()).largest_expr();
  }
  if(templ_row.expr.type().id()==ID_floatbv)
  {
    ieee_floatt max(to_floatbv_type(templ_row.expr.type()));
    max.make_fltmax();
    return max.to_expr();
  }
  assert(false); // type not supported
}

tpolyhedra_domaint::row_valuet tpolyhedra_domaint::get_min_row_value(
  const tpolyhedra_domaint::rowt &row)
{
  const template_rowt &templ_row=templ[row];
  if(templ_row.expr.type().id()==ID_signedbv)
  {
    return to_signedbv_type(templ_row.expr.type()).smallest_expr();
  }
  if(templ_row.expr.type().id()==ID_unsignedbv)
  {
    return to_unsignedbv_type(templ_row.expr.type()).smallest_expr();
  }
  if(templ_row.expr.type().id()==ID_floatbv)
  {
    ieee_floatt min(to_floatbv_type(templ_row.expr.type()));
    min.make_fltmin();
    return min.to_expr();
  }
  assert(false); // type not supported
}

void tpolyhedra_domaint::output_value(
  std::ostream &out,
  const valuet &value,
  const namespacet &ns) const
{
  const templ_valuet &v=static_cast<const templ_valuet &>(value);
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    const template_rowt &templ_row=templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns, "", templ_row.pre_guard) << " | ";
      out << from_expr(ns, "", templ_row.post_guard) << " | ";
      out << from_expr(ns, "", templ_row.aux_expr)
          << " ]===> " << std::endl << "       ";
      break;
    case IN: out << "(IN)   "; break;
    case OUT: case OUTL: out << "(OUT)  "; break;
    default: assert(false);
    }
    out << "( " << from_expr(ns, "", templ_row.expr) << "<=";
    if(is_row_value_neginf(v[row]))
      out << "-oo";
    else if(is_row_value_inf(v[row]))
      out << "oo";
    else
      out << from_expr(ns, "", v[row]);
    out << " )" << std::endl;
  }
}

void tpolyhedra_domaint::output_domain(
  std::ostream &out,
  const namespacet &ns) const
{
  for(std::size_t row=0; row<templ.size(); ++row)
  {
    const template_rowt &templ_row=templ[row];
    switch(templ_row.kind)
    {
    case LOOP:
      out << "(LOOP) [ " << from_expr(ns, "", templ_row.pre_guard) << " | ";
      out << from_expr(ns, "", templ_row.post_guard) << " | ";
      out << from_expr(ns, "", templ_row.aux_expr) << " ]===> "
          << std::endl << "      ";
      break;
    case IN:
      out << "(IN)   ";
      out << from_expr(ns, "", templ_row.pre_guard) << "===> "
          << std::endl << "      ";
      break;
    case OUT: case OUTL:
      out << "(OUT)  ";
      out << from_expr(ns, "", templ_row.post_guard) << "===> "
          << std::endl << "      ";
      break;
    default: assert(false);
    }
    out << "( " <<
      from_expr(ns, "", templ_row.expr) << "<=CONST )" << std::endl;
  }
}

unsigned tpolyhedra_domaint::template_size()
{
  return templ.size();
}

bool tpolyhedra_domaint::is_row_value_neginf(
  const row_valuet & row_value) const
{
  return row_value.get(ID_value)==ID_false;
}

bool tpolyhedra_domaint::is_row_value_inf(const row_valuet & row_value) const
{
  return row_value.get(ID_value)==ID_true;
}

/// add row suffix to non-symbolic-bound variables in expression (required for
/// strategy iteration (binsearch3))
void tpolyhedra_domaint::rename_for_row(exprt &expr, const rowt &row)
{
  if(row==0)
    return; // do not rename
  if(expr.id()==ID_symbol || expr.id()==ID_nondet_symbol)
  {
    const std::string &old_id=expr.get_string(ID_identifier);
    if(old_id.find(SYMB_BOUND_VAR)==std::string::npos)
    {
      irep_idt id=old_id+"_"+i2string(row);
      expr.set(ID_identifier, id);
    }
  }
  for(std::size_t i=0; i<expr.operands().size(); ++i)
    rename_for_row(expr.operands()[i], row);
}

tpolyhedra_domaint::template_rowt &tpolyhedra_domaint::add_template_row(
  const exprt& expr,
  const exprt& pre_guard,
  const exprt& post_guard,
  const exprt& aux_expr,
  kindt kind
  )
{
  templ.push_back(template_rowt());
  template_rowt &templ_row=templ.back();
  templ_row.expr=expr;
  extend_expr_types(templ_row.expr);
  templ_row.pre_guard=pre_guard;
  templ_row.post_guard=post_guard;
  templ_row.aux_expr=aux_expr;
  templ_row.kind=kind;
  return templ_row;
}

/// +-x<=c
void tpolyhedra_domaint::add_interval_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  unsigned size=2*var_specs.size();
  templ.reserve(templ.size()+size);

  for(const auto v : var_specs)
  {
    if(v.kind==IN)
      continue;
    if(v.var.type().id()==ID_pointer)
      continue;

    // x
    add_template_row(
      v.var,
      v.pre_guard,
      v.post_guard,
      v.aux_expr,
      v.kind);

    // -x
    add_template_row(
      unary_minus_exprt(v.var, v.var.type()),
      v.pre_guard,
      v.post_guard,
      v.aux_expr,
      v.kind);
  }
}

/// x+-y<=c
void tpolyhedra_domaint::add_difference_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  std::size_t size=var_specs.size()*(var_specs.size()-1);
  templ.reserve(templ.size()+size);

  for(var_specst::const_iterator v1=var_specs.begin();
      v1!=var_specs.end(); ++v1)
  {
    if(v1->var.type().id()==ID_pointer)
      continue;
    if(v1->var.id()==ID_and)
      continue;
    var_specst::const_iterator v2=v1;
    ++v2;
    for(; v2!=var_specs.end(); ++v2)
    {
      if(v2->var.id()==ID_and)
        continue;

      // Check if both vars are dynamic objects allocated by the same malloc.
      // In such case, do not add the template row, since only one of those is
      // always allocated and the combined guard would never hold.
      if(v1->var.id()==ID_symbol && v2->var.id()==ID_symbol)
      {
        int v1_index=get_dynobj_line(to_symbol_expr(v1->var).get_identifier());
        int v2_index=get_dynobj_line(to_symbol_expr(v2->var).get_identifier());
        if(v1_index>=0 && v2_index>=0 && v1_index==v2_index)
        {
          int v1_inst=get_dynobj_instance(
            to_symbol_expr(v1->var).get_identifier());
          int v2_inst=get_dynobj_instance(
            to_symbol_expr(v2->var).get_identifier());
          if(v1_inst>=0 && v2_inst>=0 && v1_inst!=v2_inst)
            continue;
        }
      }

      kindt k=domaint::merge_kinds(v1->kind, v2->kind);
      if(k==IN)
        continue;
      if(k==LOOP && v1->pre_guard!=v2->pre_guard)
        continue; // TEST: we need better heuristics
      if(v2->var.type().id()==ID_pointer)
        continue;

      exprt pre_g, post_g, aux_expr;
      merge_and(pre_g, v1->pre_guard, v2->pre_guard, ns);
      merge_and(post_g, v1->post_guard, v2->post_guard, ns);
      merge_and(aux_expr, v1->aux_expr, v2->aux_expr, ns);
      if(post_g.is_false())
        continue;

      // x1-x2
      add_template_row(
        minus_exprt(v1->var, v2->var), pre_g, post_g, aux_expr, k);

      // x2-x1
      add_template_row(
        minus_exprt(v2->var, v1->var), pre_g, post_g, aux_expr, k);
    }
  }
}

/// +-x^2<=c
void tpolyhedra_domaint::add_quadratic_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  unsigned size=2*var_specs.size();
  templ.reserve(templ.size()+size);

  for(const auto v : var_specs)
  {
    if(v.kind==IN)
      continue;

    // x
    add_template_row(
      mult_exprt(v.var, v.var),
      v.pre_guard,
      v.post_guard,
      v.aux_expr,
      v.kind);

    // -x
    add_template_row(
      unary_minus_exprt(mult_exprt(v.var, v.var), v.var.type()),
      v.pre_guard,
      v.post_guard,
      v.aux_expr,
      v.kind);
  }
}

/// x+y<=c, -x-y<=c
void tpolyhedra_domaint::add_sum_template(
  const var_specst &var_specs,
  const namespacet &ns)
{
  unsigned size=var_specs.size()*(var_specs.size()-1);
  templ.reserve(templ.size()+size);

  for(var_specst::const_iterator v1=var_specs.begin();
      v1!=var_specs.end(); ++v1)
  {
    var_specst::const_iterator v2=v1; ++v2;
    for(; v2!=var_specs.end(); ++v2)
    {
      kindt k=domaint::merge_kinds(v1->kind, v2->kind);
      if(k==IN)
        continue;
      if(k==LOOP && v1->pre_guard!=v2->pre_guard)
        continue; // TEST: we need better heuristics

      exprt pre_g, post_g, aux_expr;
      merge_and(pre_g, v1->pre_guard, v2->pre_guard, ns);
      merge_and(post_g, v1->post_guard, v2->post_guard, ns);
      merge_and(aux_expr, v1->aux_expr, v2->aux_expr, ns);

      // -x1-x2
      add_template_row(
        minus_exprt(unary_minus_exprt(v1->var, v1->var.type()), v2->var),
        pre_g,
        post_g,
        aux_expr,
        k);

      // x1+x2
      add_template_row(
        plus_exprt(v1->var, v2->var), pre_g, post_g, aux_expr, k);
    }
  }
}

void tpolyhedra_domaint::restrict_to_sympath(const symbolic_patht &sympath)
{
  for(auto &row : templ)
  {
    const exprt c=sympath.get_expr(row.pre_guard.op1());
    row.aux_expr=and_exprt(row.aux_expr, c);
  }
}

void tpolyhedra_domaint::clear_aux_symbols()
{
  for(auto &row : templ)
    row.aux_expr=true_exprt();
}

void tpolyhedra_domaint::undo_restriction()
{
  for(auto &row : templ)
  {
    if(row.aux_expr.id()==ID_and)
    {
      row.aux_expr=to_and_expr(row.aux_expr).op0();
    }
  }
}

void tpolyhedra_domaint::eliminate_sympaths(
  const std::vector<symbolic_patht> &sympaths)
{
  for(auto &row : templ)
  {
    exprt::operandst paths;
    for(const symbolic_patht &sympath : sympaths)
    {
      const exprt path_expr=sympath.get_expr(row.pre_guard.op1());
      paths.push_back(path_expr);
    }
    row.aux_expr=paths.empty()
                 ? true_exprt()
                 : static_cast<exprt>(not_exprt(disjunction(paths)));
  }
}

/// Identify imprecise template variables inside invariant
/// \return Vector of imprecise SSA variable names
std::vector<std::string> tpolyhedra_domaint::identify_invariant_imprecision(
  const domaint::valuet &value)
{
  const templ_valuet &templ_val=static_cast<const templ_valuet &>(value);
  assert(templ_val.size()==templ.size());

  // vector for saving ssa variable names
  std::vector<std::string> ssa_vars;

  // loop through template row pairs
  for(rowt row=0; row<templ.size(); row+=2)
  {
    // get the row values of the template row pair
    row_valuet row_val_1st=templ_val[row];
    row_valuet row_val_2nd=templ_val[row+1];

    // imprecise when the 1st row is maximum value and
    //  the 2nd row is minimum value of its corresponding type
    if(is_row_value_max(row, row_val_1st) &&
        is_row_value_min(row+1, row_val_2nd))
    {
      const exprt &templ_expr=templ[row].expr;

      // skip CPROVER variables i.e., have CPROVER prefix
      if(!is_cprover_symbol(templ_expr))
        ssa_vars.push_back(from_expr(domaint::ns, "", templ_expr));
    }
  }

  return ssa_vars;
}

/// Evaluate whether a row value at row is a maximum value
/// \param row: template row
/// \param row_val: row value to be evaluated
/// \return True if row has maximum value otherwise false
bool tpolyhedra_domaint::is_row_value_max(
  const rowt &row,
  const row_valuet &row_val)
{
  const template_rowt &templ_row=templ[row];

  // float types
  if(templ_row.expr.type().id()==ID_floatbv)
  {
    ieee_floatt row_valf(row_val);
    ieee_floatt max_valf(to_floatbv_type(templ_row.expr.type()));
    max_valf.make_fltmax();

    // is greater than max (including infinity)
    return row_valf>=max_valf;
  }
  else
  {
    // is maximum value of the row
    return row_val==get_max_row_value(row);
  }
}

/// Evaluate whether a row value at row is a minimum value
/// \param row: template row
/// \param row_val: row value to be evaluated
/// \return True if row has minimum value otherwise false
bool tpolyhedra_domaint::is_row_value_min(
  const rowt &row,
  const row_valuet &row_val)
{
  const template_rowt &templ_row=templ[row];

  // signed numeric type
  if(templ_row.expr.type().id()==ID_signedbv)
  {
    mp_integer int_row_val;

    // try converting the row value to mp_integer
    if(to_integer(row_val, int_row_val))
      return false;

    // the first row of the pair was unsigned, check if is minimum (is zero)
    if(templ[row-1].expr.type().id()==ID_unsignedbv)
      return int_row_val==0;

    // check if the signed row value is the minimum of its signed type
    //  due to implementation details, the row value must be shifted
    //  to get its comparable negative value
    return -(int_row_val << 1)==
      to_signedbv_type(templ_row.expr.type()).smallest();
  }
  // unsigned numeric type
  if(templ_row.expr.type().id()==ID_unsignedbv)
  {
    return row_val==
      to_unsignedbv_type(templ_row.expr.type()).smallest_expr();
  }
  // float type
  if(templ_row.expr.type().id()==ID_floatbv)
  {
    ieee_floatt row_valf(row_val);
    ieee_floatt max_valf(to_floatbv_type(templ_row.expr.type()));
    max_valf.make_fltmax();

    // -row_valf is greater than max (including infinity)
    return row_valf>=max_valf;
  }

  return false;
}

