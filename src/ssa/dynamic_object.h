/*******************************************************************\

Module: Dynamically allocated objects

Author: Viktor Malik, viktor.malik@gmail.com

\*******************************************************************/

#ifndef CPROVER_2LS_SSA_DYNAMIC_OBJECT_H
#define CPROVER_2LS_SSA_DYNAMIC_OBJECT_H

#include <goto-programs/goto_model.h>
#include <util/type.h>
#include <set>
#include <string>

/*******************************************************************\

 Class representing a dynamic object - abstraction of all objects
 allocated at some program location (loc).
 It is composed of a number of instances, each representing a number
 of concrete objects.

\*******************************************************************/
class dynamic_objectt
{
public:
  dynamic_objectt(
    const exprt &malloc_call,
    unsigned int loc_number,
    symbol_tablet &symbol_table,
    bool is_concrete,
    bool alloc_concrete);

  void create_instance(
    symbol_tablet &symbol_table,
    std::string inst_suffix,
    bool concrete,
    bool nondet);

  void drop_last_instance();

  bool is_abstract() const;
  exprt get_expr() const;
  std::string get_name() const;

protected:
  unsigned loc;
  typet type;
  std::vector<std::pair<exprt, symbol_exprt>> instances;
  typet malloc_type;

  exprt create_instance_guard(
    exprt &instance_address,
    symbol_tablet &symbol_table,
    std::string inst_suffix,
    bool concrete,
    bool nondet);
};

/*******************************************************************\

 Class representing all dynamically allocated objects in the program.

\*******************************************************************/
class dynamic_objectst
{
public:
  dynamic_objectt &get(unsigned loc);
  const dynamic_objectt &get(unsigned loc) const;
  dynamic_objectt &get(symbol_exprt obj_expr);
  const dynamic_objectt &get(symbol_exprt obj_expr) const;

  bool contains(unsigned loc) const;
  bool contains(symbol_exprt obj_expr) const;
  void add(unsigned loc, dynamic_objectt &obj);
  bool have_abstract() const;

protected:
  std::map<unsigned, dynamic_objectt> objects;
};

dynamic_objectst collect_dynamic_objects(
  goto_modelt &goto_model,
  bool alloc_concrete);

int get_dynobj_line(const irep_idt &id);

#endif // CPROVER_2LS_SSA_DYNAMIC_OBJECT_H
