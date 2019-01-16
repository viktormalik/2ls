/*******************************************************************\

Module: Dynamically allocated objects

Author: Viktor Malik, viktor.malik@gmail.com

\*******************************************************************/

#ifndef CPROVER_2LS_SSA_DYNAMIC_OBJECT_H
#define CPROVER_2LS_SSA_DYNAMIC_OBJECT_H

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
  dynamic_objectt(unsigned int loc, const typet &type);

  exprt create_instance(
    symbol_tablet &symbol_table,
    std::string inst_suffix,
    bool concrete);

  bool is_abstract() const;

protected:
  unsigned loc;
  typet type;
  std::set<symbol_exprt> instances;
};

/*******************************************************************\

 Class representing all dynamically allocated objects in the program.

\*******************************************************************/
class dynamic_objectst
{
public:
  dynamic_objectt &get(unsigned loc);
  dynamic_objectt &get(symbol_exprt obj_expr);
  void add(unsigned loc, dynamic_objectt &obj);
  bool have_abstract() const;

protected:
  std::map<unsigned, dynamic_objectt> objects;
};

int get_dynobj_line(const irep_idt &id);

#endif // CPROVER_2LS_SSA_DYNAMIC_OBJECT_H
