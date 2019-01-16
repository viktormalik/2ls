/*******************************************************************\

Module: Dynamically allocated objects

Author: Viktor Malik, viktor.malik@gmail.com

\*******************************************************************/

#include <util/symbol_table.h>
#include <util/std_expr.h>
#include <util/expr_util.h>
#include <ansi-c/c_types.h>
#include <algorithm>
#include "dynamic_object.h"

dynamic_objectt::dynamic_objectt(unsigned int loc, const typet &type):
  loc(loc), type(type) {}

/*******************************************************************\

Function: dynamic_object::create_instance

  Inputs: symbol_table
          inst_suffix Suffix of the new instance
          concrete True if the instance represents a concrete object

 Outputs: Expression holding address of the newly created symbol.

 Purpose: Create a symbol representing an instance of the dynamic
          object. The new symbol is inserted into the symbol table
          and into the set of instances of 'this'.

\*******************************************************************/
exprt dynamic_objectt::create_instance(
  symbol_tablet &symbol_table,
  std::string inst_suffix,
  bool concrete)
{
  symbolt symbol;
  symbol.base_name="dynamic_object$"+std::to_string(loc)+inst_suffix;
  symbol.name="ssa::"+id2string(symbol.base_name);
  symbol.is_lvalue=true;
  symbol.type=type;
  symbol.type.set("#dynamic", true);
  symbol.mode=ID_C;

  symbol_table.add(symbol);
  instances.insert(symbol.symbol_expr());

  address_of_exprt address_of_object;

  if(type.id()==ID_array)
  {
    address_of_object.type()=pointer_typet(symbol.type.subtype());
    index_exprt index_expr(symbol.type.subtype());
    index_expr.array()=symbol.symbol_expr();
    index_expr.index()=gen_zero(index_type());
    address_of_object.op0()=index_expr;
  }
  else
  {
    address_of_object.op0()=symbol.symbol_expr();
    if(concrete)
      address_of_object.op0().set("#concrete", true);
    address_of_object.type()=pointer_typet(symbol.type);
  }

  return address_of_object;
}

/*******************************************************************\

Function: dynamic_object::is_abstract

  Inputs:

 Outputs: True if the dynamic object is abstract (contains more than
          one instance).

 Purpose:

\*******************************************************************/
bool dynamic_objectt::is_abstract() const
{
  return instances.size()>1;
}

/*******************************************************************\

Function: dynamic_objects::get

  Inputs: loc Location number

 Outputs: Dynamic object allocated at the given location.

 Purpose:

\*******************************************************************/
dynamic_objectt &dynamic_objectst::get(unsigned loc)
{
  auto obj=objects.find(loc);
  assert(obj!=objects.end());
  return obj->second;
}

/*******************************************************************\

Function: dynamic_objects::get

  Inputs: obj_expr Symbol of an instance of a dynamic object

 Outputs: Dynamic object corresponding to the given instance.

 Purpose:

\*******************************************************************/
dynamic_objectt &dynamic_objectst::get(symbol_exprt obj_expr)
{
  int loc=get_dynobj_line(obj_expr.get_identifier());
  assert(loc>=0);
  return get((unsigned) loc);
}

/*******************************************************************\

Function: dynamic_objects::add

  Inputs:

 Outputs:

 Purpose: Add a new dynamic object to the set.

\*******************************************************************/
void dynamic_objectst::add(unsigned int loc, dynamic_objectt &obj)
{
  objects.insert(std::make_pair(loc, obj));
}

/*******************************************************************\

Function: dynamic_objects::have_abstract

  Inputs:

 Outputs: True if there is some abstract dynamic object (one that is
          allocated in a loop).

 Purpose:

\*******************************************************************/
bool dynamic_objectst::have_abstract() const
{
  return std::any_of(
    objects.begin(), objects.end(),
    [](const std::pair<const unsigned, dynamic_objectt> &o)
    {
      return o.second.is_abstract();
    });
}

/*******************************************************************\

Function: get_dynobj_line

  Inputs: Symbol identifier.

 Outputs: If the symbol is a dynamic object, then the location number of the
          malloc call where the object was allocated, otherwise -1.

 Purpose:

\*******************************************************************/
int get_dynobj_line(const irep_idt &id)
{
  std::string name=id2string(id);
  size_t pos=name.find("dynamic_object$");
  if(pos==std::string::npos)
    return -1;

  size_t start=pos+15;
  size_t end=name.find_first_not_of("0123456789", pos);
  std::string number=name.substr(start, end-start);
  return std::stoi(number);
}
