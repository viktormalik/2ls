/*******************************************************************\

Module: Domain utilities

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Domain utilities

#ifndef CPROVER_2LS_DOMAINS_UTIL_H
#define CPROVER_2LS_DOMAINS_UTIL_H

#include <util/std_expr.h>
#include <util/namespace.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <langapi/language_util.h>
#include <iostream>

#define DYN_PREFIX_LEN 15

void extend_expr_types(exprt &expr);
constant_exprt simplify_const(const exprt &expr);
ieee_floatt simplify_const_float(const exprt &expr);
mp_integer simplify_const_int(const exprt &expr);
void pretty_print_termination_argument(
  std::ostream &out,
  const namespacet &ns,
  const exprt &expr);
void merge_and(
  exprt & result,
  const exprt &expr1,
  const exprt &expr2,
  const namespacet &ns);
constant_exprt make_zero(const typet &type);
constant_exprt make_one(const typet &type);
constant_exprt make_minusone(const typet &type);

irep_idt get_original_name(const symbol_exprt &);
std::string get_original_name(const std::string &s);
void clean_expr(exprt &expr);

bool is_cprover_symbol(const exprt &expr);

int get_dynobj_line(const irep_idt &id);
int get_dynobj_instance(const irep_idt &id);

bool is_dynamic_name(const std::string &name);
int is_loopback_var(const std::string &name);
std::string get_dynamic_field(const std::string &name);

#endif
