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
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <algorithm>
#include <iostream>

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
  loc(loc_number),
  type(determine_malloc_type(malloc_call.op0(), symbol_table)),
  malloc_type(malloc_call.type())
{
//  if(!is_concrete && alloc_concrete)
//    create_instance(symbol_table, "$co", true, false);

  create_instance(symbol_table, "", is_concrete, false);
}

/*******************************************************************\

Function: dynamic_object::create_instance

  Inputs: symbol_table
          inst_suffix Suffix of the new instance
          concrete True if the instance represents a concrete object
          nodet True if the instance is created non-deterministically

 Outputs:

 Purpose: Create a symbol representing an instance of the dynamic
          object. The new symbol is inserted into the symbol table.
          Also an allocation guard for the instance is created.

\*******************************************************************/
void dynamic_objectt::create_instance(
  symbol_tablet &symbol_table,
  std::string inst_suffix,
  bool concrete,
  bool nondet)
{
  // Create new symbol
  symbolt symbol;
  symbol.base_name=get_name()+inst_suffix;
  symbol.name="ssa::"+id2string(symbol.base_name);
  symbol.is_lvalue=true;
  symbol.type=type;
  symbol.type.set("#dynamic", true);
  symbol.mode=ID_C;

  symbol_table.add(symbol);

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

  exprt guard=create_instance_guard(symbol_table, inst_suffix, nondet);
  symbol_exprt guard_symbol=create_instance_cond(symbol_table, inst_suffix);
  symbol_exprt instance=symbol.symbol_expr();
  instances.emplace_back(guard, guard_symbol, inst_suffix, instance, concrete, this);
}

/*******************************************************************\

Function: dynamic_object::create_instance_guard

  Inputs: instance_address Address of the corresponding instance.
          symbol_table
          inst_suffix Suffix of the new instance
          concrete True if the instance represents a concrete object
          nodet True if the instance is created non-deterministically

 Outputs:

 Purpose: Create a guard for an instance of dynamic object. The guard
          determines when the corresponding instance is created.

\*******************************************************************/
exprt dynamic_objectt::create_instance_guard(
  symbol_tablet &symbol_table,
  std::string inst_suffix,
  bool nondet)
{
  if(nondet)
  {
    // Fresh free boolean symbol (non-determinism)
    symbolt nondet_symbol;
    nondet_symbol.base_name="$guard#os"+std::to_string(loc)+inst_suffix;
    nondet_symbol.name=nondet_symbol.base_name;
    nondet_symbol.is_lvalue=true;
    nondet_symbol.type=bool_typet();
    nondet_symbol.mode=ID_C;
    symbol_table.add(nondet_symbol);

    return nondet_symbol.symbol_expr();
  }
  return true_exprt();
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
  return instances.size()>1 || !instances[0].concrete;
}

/*******************************************************************\

Function: dynamic_object::get_expr

  Inputs:

 Outputs: Expression corresponding to the given abstract object.
          It is a choice from object instances based on instance
          allocation guards.

 Purpose:

\*******************************************************************/
exprt dynamic_objectt::get_expr() const
{
  assert(!instances.empty());
  auto inst_it=instances.rbegin();

  exprt expr=address_of_exprt(inst_it->symbol);
  if(expr.type()!=malloc_type)
    expr=typecast_exprt(expr, malloc_type);

  while(++inst_it!=instances.rend())
  {
    exprt obj=address_of_exprt(inst_it->symbol);
    if(obj.type()!=malloc_type)
      obj=typecast_exprt(obj, malloc_type);
    expr=if_exprt(inst_it->guard_symbol, obj, expr);
  }
  expr.set("#malloc_result", true);
  return expr;
}

std::string dynamic_objectt::get_name() const
{
  return "dynamic_object$"+std::to_string(loc);
}

/*******************************************************************\

Function: dynamic_objects::drop_last_instance

  Inputs:

 Outputs:

 Purpose: Removes the last instance from the object.
          This is called when the last instance is replaced by a set
          of instances.

\*******************************************************************/
void dynamic_objectt::drop_last_instance()
{
  instances.pop_back();
}

exprt dynamic_objectt::exclude_instances_guard(
  symbol_tablet &symbol_table,
  const std::vector<const symbol_exprt *> &inst_to_exclude)
{
  exprt::operandst instance_equs;
  for (auto *inst : inst_to_exclude)
  {
    auto addr=address_of_exprt(*inst);
    auto pointers=collect_pointer_vars(symbol_table, type);
    for(auto &p : pointers)
    {
      instance_equs.push_back(equal_exprt(p, addr));
    }
  }
  if(instance_equs.empty())
    return true_exprt();
  return not_exprt(disjunction(instance_equs));
}

exprt dynamic_objectt::include_instances_guard(
  symbol_tablet &symbol_table,
  const std::vector<const symbol_exprt *> &inst_to_include)
{
  symbolt &malloc_obj = symbol_table.lookup("__CPROVER_malloc_object");
  exprt::operandst instance_equs;
  for(auto *inst : inst_to_include)
  {
    instance_equs.push_back(
      equal_exprt(
        malloc_obj.symbol_expr(),
        typecast_exprt(address_of_exprt(*inst), malloc_obj.type)));
  }

  if(instance_equs.empty())
    return true_exprt();
  return disjunction(instance_equs);
}

const exprt dynamic_objectt::include_instance_guard(
  const symbol_tablet &symbol_table,
  const symbol_exprt &instance) const
{
  exprt::operandst equs;
  auto addr = address_of_exprt(instance);
  auto pointers=collect_pointer_vars(symbol_table, type);
  for (auto &p : pointers) {
    equs.push_back(equal_exprt(p, addr));
  }
  return disjunction(equs);
}

void dynamic_objectt::compute_guards_concrete(symbol_tablet &symbol_table)
{
  for (auto &inst : instances)
  {
    if (inst.concrete)
    {
      std::vector<const symbol_exprt *> v = {&inst.symbol};
      inst.guard=and_exprt(
        inst.guard,
        exclude_instances_guard(symbol_table, v));
    }
//    simplify_expr(inst.first, namespacet(symbol_table));
  }
}

void dynamic_objectt::enforce_order(symbol_tablet &symbol_table)
{
  for(auto inst_it=instances.begin(); inst_it!=instances.end(); inst_it++)
  {
//    std::cerr << id2string(inst_it->symbol.get_identifier()) << ":\n";
    std::vector<const symbol_exprt *> pred_instances;
    std::vector<const symbol_exprt *> succ_instances;

    auto other_inst_it = inst_it;
    if (!inst_it->concrete)
      pred_instances.push_back(&other_inst_it->symbol);

    if (other_inst_it != instances.begin())
    {
      do
      {
        other_inst_it--;
        pred_instances.push_back(&other_inst_it->symbol);
      } while(other_inst_it!=instances.begin() && !other_inst_it->concrete);
    }

    other_inst_it = inst_it;
    other_inst_it++;
    while(other_inst_it!=instances.end())
    {
      succ_instances.push_back(&other_inst_it->symbol);
      ++other_inst_it;
    }

    inst_it->guard=and_exprt(
      inst_it->guard,
      include_instances_guard(symbol_table, pred_instances));

    inst_it->guard=and_exprt(
      inst_it->guard,
      exclude_instances_guard(symbol_table, succ_instances));
  }
}

const dynamic_objectt::instancet *
dynamic_objectt::get_instance(const symbol_exprt &symbol) const
{
  std::string suffix =get_dynobj_instance_suffix(symbol.get_identifier());
  for (const auto &inst : instances)
    if (inst.suffix == suffix)
      return &inst;
  return nullptr;
}

symbol_exprt dynamic_objectt::create_instance_cond(
  symbol_tablet &symbol_table,
  std::string &inst_suffix)
{
  // Fresh free boolean symbol (non-determinism)
  symbolt cond_symbol;
  cond_symbol.base_name="$cond#os"+std::to_string(loc)+inst_suffix;
  cond_symbol.name=cond_symbol.base_name;
  cond_symbol.is_lvalue=true;
  cond_symbol.type=bool_typet();
  cond_symbol.mode=ID_C;
  symbol_table.add(cond_symbol);
  return cond_symbol.symbol_expr();
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

  Inputs: loc Location number

 Outputs: Dynamic object allocated at the given location.

 Purpose:

\*******************************************************************/
const dynamic_objectt &dynamic_objectst::get(unsigned loc) const
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

Function: dynamic_objects::get

  Inputs: obj_expr Symbol of an instance of a dynamic object

 Outputs: Dynamic object corresponding to the given instance.

 Purpose:

\*******************************************************************/
const dynamic_objectt &dynamic_objectst::get(symbol_exprt obj_expr) const
{
  int loc=get_dynobj_line(obj_expr.get_identifier());
  assert(loc>=0);
  return get((unsigned) loc);
}

/*******************************************************************\

Function: dynamic_objects::contains

  Inputs: loc Program location

 Outputs: True if there is a dynamic object allocated at the given
          location.

 Purpose:

\*******************************************************************/
bool dynamic_objectst::contains(unsigned loc) const
{
  return objects.find(loc)!=objects.end();
}

/*******************************************************************\

Function: dynamic_objects::contains

  Inputs: obj_expr Symbol of an instance of a dynamic object

 Outputs: True if there is a dynamic object corresponding to the given
          instance.

 Purpose:

\*******************************************************************/
bool dynamic_objectst::contains(symbol_exprt obj_expr) const
{
  int loc=get_dynobj_line(obj_expr.get_identifier());
  return loc>=0 && objects.find((unsigned) loc)!=objects.end();
}

/*******************************************************************\

Function: dynamic_objects::add

  Inputs:

 Outputs:

 Purpose: Add a new dynamic object to the set.

\*******************************************************************/
void dynamic_objectst::add(unsigned int loc, dynamic_objectt &&obj)
{
  objects.emplace(loc, std::move(obj));
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
    dynamic_objects.add(loc_number, std::move(dynobj));
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

std::string get_dynobj_instance_suffix(const irep_idt &id)
{
  std::string name=id2string(id);
  size_t pos=name.find("dynamic_object$");
  if(pos==std::string::npos)
    return "";
  pos=name.find_first_of("#", pos);
  if(pos==std::string::npos)
    return "";
  size_t end=name.find_first_not_of("0123456789", pos+1);
  return name.substr(pos, end-pos);
}

const exprt dynamic_objectt::instancet::select_guard() const
{
  return symbol_exprt("guard#is" + std::to_string(dynobj->loc) + suffix,
                      bool_typet());
}
