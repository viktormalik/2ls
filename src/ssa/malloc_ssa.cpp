/*******************************************************************\

Module: SSA for malloc()

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/symbol.h>
#include <util/i2string.h>
#include <util/pointer_offset_size.h>

#include <ansi-c/c_types.h>
#include <analyses/constant_propagator.h>

#include <ssa/dynamic_object.h>

#include <functional>

#include "malloc_ssa.h"

/*******************************************************************\

Function: c_sizeof_type_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static typet c_sizeof_type_rec(const exprt &expr)
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

Function: collect_pointer_vars

  Inputs:

 Outputs:

 Purpose: Collect all variables (symbols and their members) of pointer
          type with given pointed type.

\*******************************************************************/

std::vector<exprt> collect_pointer_vars(
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

Function: malloc_ssa

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

dynamic_objectt malloc_ssa(
  exprt &code,
  unsigned int loc_number,
  symbol_tablet &symbol_table,
  bool is_concrete,
  bool alloc_concrete)
{
  if(code.operands().size()!=1)
    throw "malloc expected to have one operand";

  namespacet ns(symbol_table);
  exprt size=code.op0();
  typet object_type=nil_typet();

  {
    // special treatment for sizeof(T)*x
    if(size.id()==ID_mult &&
       size.operands().size()==2 &&
       size.op0().find(ID_C_c_sizeof_type).is_not_nil())
    {
      object_type=array_typet(
        c_sizeof_type_rec(size.op0()),
        size.op1());
    }
    else if(size.id()==ID_mult &&
            size.operands().size()==2 &&
            size.op1().find(ID_C_c_sizeof_type).is_not_nil())
    {
      object_type=array_typet(
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
            object_type=tmp_type;
          else
          {
            mp_integer elements=alloc_size/elem_size;

            if(elements*elem_size==alloc_size)
              object_type=array_typet(
                tmp_type,
                from_integer(elements, size.type()));
          }
        }
      }
    }

    // the fall-back is to produce a byte-array
    if(object_type.is_nil())
      object_type=array_typet(unsigned_char_type(), size);
  }

#ifdef DEBUG
  std::cout << "OBJECT_TYPE: " << from_type(ns, "", object_type) << std::endl;
#endif

  auto pointers=collect_pointer_vars(symbol_table, object_type);

  auto dynobj=dynamic_objectt(loc_number, object_type);
  exprt object=dynobj.create_instance(symbol_table, "", is_concrete);

  if(object.type()!=code.type())
    object=typecast_exprt(object, code.type());
  exprt result;
  if(!is_concrete && alloc_concrete)
  {
    exprt concrete_object=dynobj.create_instance(symbol_table, "$co", true);

    // Create nondet symbol
    symbolt nondet_symbol;
    nondet_symbol.base_name="nondet$"+loc_number;
    nondet_symbol.name="ssa::"+id2string(nondet_symbol.base_name);
    nondet_symbol.is_lvalue=true;
    nondet_symbol.type=bool_typet();
    nondet_symbol.mode=ID_C;
    symbol_table.add(nondet_symbol);

    exprt::operandst pointer_equs;
    for(auto &ptr : pointers)
    {
      pointer_equs.push_back(equal_exprt(ptr, concrete_object));
    }
    exprt cond=and_exprt(
      nondet_symbol.symbol_expr(),
      not_exprt(disjunction(pointer_equs)));

    if(concrete_object.type()!=code.type())
      concrete_object=typecast_exprt(concrete_object, code.type());
    result=if_exprt(cond, concrete_object, object);
  }
  else
    result=object;

  result.set("#malloc_result", true);

  code=result;
  return dynobj;
}


/*******************************************************************\

Function: replace_malloc_rec

  Inputs:

 Outputs:

 Purpose:

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

    auto dynobj=malloc_ssa(
      expr,
      loc_number,
      symbol_table,
      is_concrete,
      alloc_concrete);
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

Function: replace_malloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

dynamic_objectst replace_malloc(goto_modelt &goto_model, bool alloc_concrete)
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

Function: set_var_always_to_true

  Inputs: goto_model
          name_cond Function returning true for names of variables
                    to be set.

 Outputs:

 Purpose: Set undefined boolean variable to true.
          Finds declaration of a variable whose name matches the given
          condition and adds an instruction var = TRUE after
          the declaration.

\*******************************************************************/

void set_var_always_to_true(
  goto_modelt &goto_model,
  std::function<bool(std::string &)>name_cond)
{
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_decl())
      {
        code_declt &code_decl=to_code_decl(i_it->code);
        if(code_decl.symbol().id()==ID_symbol)
        {
          std::string decl_id=
            id2string(to_symbol_expr(code_decl.symbol()).get_identifier());
          if(name_cond(decl_id))
          {
            auto assign=f_it->second.body.insert_after(i_it);
            assign->make_assignment();
            assign->code=code_assignt(code_decl.symbol(), true_exprt());
          }
        }
      }
    }
    f_it->second.body.compute_location_numbers();
    f_it->second.body.compute_target_numbers();
    f_it->second.body.compute_incoming_edges();
  }
}

/*******************************************************************\

Function: allow_record_malloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void allow_record_malloc(goto_modelt &goto_model)
{
  set_var_always_to_true(
    goto_model,
    [](std::string &name)
    {
      return name.find("malloc::")!=std::string::npos &&
             name.find("::record_malloc")!=std::string::npos;
    });
}

/*******************************************************************\

Function: allow_record_memleak

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void allow_record_memleak(goto_modelt &goto_model)
{
  set_var_always_to_true(
    goto_model,
    [](std::string &name)
    {
      return name.find("malloc::")!=std::string::npos &&
             name.find("::record_may_leak")!=std::string::npos;
    });
}
