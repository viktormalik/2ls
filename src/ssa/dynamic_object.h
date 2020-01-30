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

  // Disable copying so that there is always a single dynamic object (we work
  // with its address).
  dynamic_objectt(const dynamic_objectt &)=delete;
  dynamic_objectt &operator=(const dynamic_objectt &)=delete;
  dynamic_objectt(dynamic_objectt &&)=default;
  dynamic_objectt &operator=(dynamic_objectt &&)=default;

  struct instancet
  {
    exprt guard;
    symbol_exprt guard_symbol;
    std::string suffix;
    symbol_exprt symbol;
    bool concrete;

    instancet(
      const exprt &guard,
      const symbol_exprt &guard_symbol,
      const std::string &suffix,
      symbol_exprt &symbol,
      const bool concrete,
      dynamic_objectt *dynobj):
      guard(guard), guard_symbol(guard_symbol), suffix(suffix), symbol(symbol), concrete(concrete),
      dynobj(dynobj)
    {
      if(concrete)
        symbol.set("#concrete", true);
    }

    const exprt select_guard() const;

  private:
    dynamic_objectt *dynobj;
  };

  void create_instance(
    symbol_tablet &symbol_table,
    std::string inst_suffix,
    bool concrete,
    bool nondet);

  void drop_last_instance();
  const instancet *get_instance(const symbol_exprt &symbol) const;

  const exprt include_instance_guard(
    const symbol_tablet &symbol_table,
    const symbol_exprt &instance) const;

  void compute_guards_concrete(symbol_tablet &symbol_table);
  void enforce_order(symbol_tablet &symbol_table);

  bool is_abstract() const;
  exprt get_expr() const;
  std::string get_name() const;

  std::vector<instancet> instances;

protected:
  unsigned loc;
  typet type;
  typet malloc_type;

  symbol_exprt create_instance_cond(
    symbol_tablet &symbol_table,
    std::string &inst_suffix
  );

  exprt create_instance_guard(
    symbol_tablet &symbol_table,
    std::string inst_suffix,
    bool nondet);

  exprt exclude_instances_guard(
    symbol_tablet &symbol_table,
    const std::vector<const symbol_exprt *> &inst_to_exclude);
  exprt include_instances_guard(
    symbol_tablet &symbol_table,
    const std::vector<const symbol_exprt *> &inst_to_include);
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
  void add(unsigned loc, dynamic_objectt &&obj);
  bool have_abstract() const;

protected:
  std::map<unsigned, dynamic_objectt> objects;
};

dynamic_objectst collect_dynamic_objects(
  goto_modelt &goto_model,
  bool alloc_concrete);

int get_dynobj_line(const irep_idt &id);
std::string get_dynobj_instance_suffix(const irep_idt &id);

#endif // CPROVER_2LS_SSA_DYNAMIC_OBJECT_H
