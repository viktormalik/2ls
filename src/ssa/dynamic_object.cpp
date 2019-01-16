/*******************************************************************\

Module: Dynamically allocated objects

Author: Viktor Malik, viktor.malik@gmail.com

\*******************************************************************/

#include <analyses/constant_propagator.h>
#include <ansi-c/c_types.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <algorithm>

#include "dynamic_object.h"

/*******************************************************************\

Function: c_sizeof_type_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static inline typet c_sizeof_type_rec(const exprt &expr)
{
  const irept &sizeof_type=expr.find(ID_C_c_sizeof_type);

  if(!sizeof_type.is_nil())
  {
    return static_cast<const typet &>(sizeof_type);
  }
  else if(expr.id()==ID_mult)
  {
    forall_operands(it, expr)
      {
        typet t=c_sizeof_type_rec(*it);
        if(t.is_not_nil())
          return t;
      }
  }

  return nil_typet();
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose: Determine type of the object allocated by malloc from
          the sizeof() expression passed to malloc.

\*******************************************************************/
static typet determine_malloc_type(
  const exprt &size,
  symbol_tablet &symbol_table)
{
  namespacet ns(symbol_table);

  typet type=nil_typet();
  // special treatment for sizeof(T)*x
  if(size.id()==ID_mult &&
     size.operands().size()==2 &&
     size.op0().find(ID_C_c_sizeof_type).is_not_nil())
  {
    type=array_typet(
      c_sizeof_type_rec(size.op0()),
      size.op1());
  }
  else if(size.id()==ID_mult &&
          size.operands().size()==2 &&
          size.op1().find(ID_C_c_sizeof_type).is_not_nil())
  {
    type=array_typet(
      c_sizeof_type_rec(size.op1()),
      size.op0());
  }
  else
  {
    typet tmp_type=c_sizeof_type_rec(size);

    if(tmp_type.is_not_nil())
    {
      // Did the size get multiplied?
      mp_integer elem_size=pointer_offset_size(tmp_type, ns);
      mp_integer alloc_size;
      if(elem_size<0 || to_integer(size, alloc_size))
      {
      }
      else
      {
        if(alloc_size==elem_size)
          type=tmp_type;
        else
        {
          mp_integer elements=alloc_size/elem_size;

          if(elements*elem_size==alloc_size)
            type=array_typet(
              tmp_type,
              from_integer(elements, size.type()));
        }
      }
    }
  }

  // the fall-back is to produce a byte-array
  if(type.is_nil())
    type=array_typet(unsigned_char_type(), size);

#ifdef DEBUG
  std::cout << "OBJECT_TYPE: " << from_type(ns, "", object_type) << std::endl;
#endif

  return type;
}

/*******************************************************************\

Function: collect_pointer_vars

  Inputs:

 Outputs:

 Purpose: Collect all variables (symbols and their members) of pointer
          type with given pointed type.

\*******************************************************************/

static std::vector<exprt> collect_pointer_vars(
  const symbol_tablet &symbol_table,
  const typet &pointed_type)
{
  namespacet ns(symbol_table);
  std::vector<exprt> pointers;
  forall_symbols(it, symbol_table.symbols)
  {
    if(ns.follow(it->second.type).id()==ID_struct)
    {
      for(auto &component : to_struct_type(
        ns.follow(it->second.type)).components())
      {
        if(component.type().id()==ID_pointer)
        {
          if(ns.follow(component.type().subtype())==ns.follow(pointed_type))
          {
            pointers.push_back(
              member_exprt(
                it->second.symbol_expr(), component.get_name(),
                component.type()));
          }
        }
      }
    }
    if(it->second.type.id()==ID_pointer)
    {
      if(ns.follow(it->second.type.subtype())==ns.follow(pointed_type))
      {
        pointers.push_back(it->second.symbol_expr());
      }
    }
  }
  return pointers;
}


/*******************************************************************\

Function: dynamic_objectt::dynamic_objectt

  Inputs: malloc_call expression
          loc_number Program location of the malloc
          symbol_table
          is_concrete True if the allocated object should be concrete.
          alloc_concrete True if the allocated object is abstract
                         but we want to materialize a concrete object
                         within it.

 Outputs:

 Purpose: Constructor for a dynamic object from malloc call.

\*******************************************************************/
dynamic_objectt::dynamic_objectt(
  const exprt &malloc_call,
  unsigned int loc_number,
  symbol_tablet &symbol_table,
  bool is_concrete,
  bool alloc_concrete):
  loc(loc_number), type(determine_malloc_type(malloc_call.op0(), symbol_table))
{
  auto pointers=collect_pointer_vars(symbol_table, type);

  expr=create_instance(symbol_table, "", is_concrete);

  if(expr.type()!=malloc_call.type())
    expr=typecast_exprt(expr, malloc_call.type());
  if(!is_concrete && alloc_concrete)
  {
    exprt concrete_object=create_instance(symbol_table, "$co", true);
    exprt guard=create_instance_guard(
      concrete_object, symbol_table, "$co", true);

    if(concrete_object.type()!=malloc_call.type())
      concrete_object=typecast_exprt(concrete_object, malloc_call.type());
    expr=if_exprt(guard, concrete_object, expr);
  }

  expr.set("#malloc_result", true);
}

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

Function: dynamic_object::create_instance_guard

  Inputs: instance_address Address of the corresponding instance.
          symbol_table
          inst_suffix Suffix of the new instance
          concrete True if the instance represents a concrete object

 Outputs:

 Purpose: Create a guard for an instance of dynamic object. The guard
          determines when the corresponding instance is created.

\*******************************************************************/
exprt dynamic_objectt::create_instance_guard(
  exprt &instance_address,
  symbol_tablet &symbol_table,
  std::string inst_suffix,
  bool concrete)
{
  // Fresh free boolean symbol
  symbolt nondet_symbol;
  nondet_symbol.base_name="$guard#os"+std::to_string(loc)+inst_suffix;
  nondet_symbol.name=nondet_symbol.base_name;
  nondet_symbol.is_lvalue=true;
  nondet_symbol.type=bool_typet();
  nondet_symbol.mode=ID_C;
  symbol_table.add(nondet_symbol);

  exprt guard=nondet_symbol.symbol_expr();
  if(concrete)
  {
    auto pointers=collect_pointer_vars(symbol_table, type);
    exprt::operandst pointer_equs;
    for(auto &ptr : pointers)
    {
      pointer_equs.push_back(equal_exprt(ptr, instance_address));
    }
    guard=and_exprt(
      guard,
      not_exprt(disjunction(pointer_equs)));
  }

  return guard;
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

Function: dynamic_object::get_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
exprt dynamic_objectt::get_expr() const
{
  return expr;
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

Function: replace_malloc_rec

  Inputs:

 Outputs:

 Purpose: Try to replace malloc call. If expr is not a malloc call,
          call self on expr operands.

\*******************************************************************/

static void replace_malloc_rec(
  exprt &expr,
  symbol_tablet &symbol_table,
  const exprt &malloc_size,
  unsigned loc_number,
  bool is_concrete,
  bool alloc_concrete,
  dynamic_objectst &dynamic_objects)
{
  if(expr.id()==ID_side_effect &&
     to_side_effect_expr(expr).get_statement()==ID_malloc)
  {
    assert(!malloc_size.is_nil());
    expr.op0()=malloc_size;

    dynamic_objectt dynobj(
      expr,
      loc_number,
      symbol_table,
      is_concrete,
      alloc_concrete);
    expr=dynobj.get_expr();
    dynamic_objects.add(loc_number, dynobj);
  }
  else
  {
    Forall_operands(it, expr)
      {
        replace_malloc_rec(
          *it, symbol_table, malloc_size, loc_number, is_concrete,
          alloc_concrete, dynamic_objects);
      }
  }
}

/*******************************************************************\

Function: collect_dynamic_objects

  Inputs:

 Outputs:

 Purpose: Traverse all programs and replace mallocs by dynamic objects.
          Return all created objects.

\*******************************************************************/

dynamic_objectst collect_dynamic_objects(
  goto_modelt &goto_model,
  bool alloc_concrete)
{
  dynamic_objectst objects;
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    goto_programt::const_targett loop_end=f_it->second.body.instructions.end();
    exprt malloc_size=nil_exprt();
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(loop_end==f_it->second.body.instructions.end())
      {
        for(const auto &incoming : i_it->incoming_edges)
        {
          if(incoming->is_backwards_goto() &&
             incoming!=i_it)
          {
            loop_end=incoming;
          }
        }
      }
      else if(i_it==loop_end)
      {
        loop_end=f_it->second.body.instructions.end();
      }

      if(i_it->is_assign())
      {
        code_assignt &code_assign=to_code_assign(i_it->code);
        if(code_assign.lhs().id()==ID_symbol)
        {
          // we have to propagate the malloc size
          //   in order to get the object type
          // TODO: this only works with inlining,
          //       and btw, this is an ugly hack
          std::string lhs_id=
            id2string(to_symbol_expr(code_assign.lhs()).get_identifier());
          if(lhs_id=="malloc::malloc_size" ||
             lhs_id=="__builtin_alloca::alloca_size")
          {
            namespacet ns(goto_model.symbol_table);
            goto_functionst::goto_functiont function_copy=f_it->second;
            constant_propagator_ait const_propagator(function_copy, ns);
            forall_goto_program_instructions(copy_i_it, function_copy.body)
            {
              if(copy_i_it->location_number==i_it->location_number)
              {
                assert(copy_i_it->is_assign());
                malloc_size=to_code_assign(copy_i_it->code).rhs();
              }
            }
          }
        }
        replace_malloc_rec(
          code_assign.rhs(), goto_model.symbol_table, malloc_size,
          i_it->location_number,
          loop_end==f_it->second.body.instructions.end(),
          alloc_concrete, objects);
      }
    }
  }
  return objects;
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
