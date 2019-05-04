/*******************************************************************\

Module: SSA Analyzer

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// SSA Analyzer

#ifdef DEBUG
#include <iostream>
#endif

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/mp_arith.h>
#include <util/options.h>
#include <util/cprover_prefix.h>

#include "strategy_solver_base.h"
#include "strategy_solver_binsearch.h"
#include "strategy_solver_binsearch2.h"
#include "strategy_solver_binsearch3.h"
#include "linrank_domain.h"
#include "equality_domain.h"
#include "lexlinrank_domain.h"
#include "predabs_domain.h"
#include "template_generator_ranking.h"
#include "ssa_analyzer.h"
#include "strategy_solver_heap_tpolyhedra.h"
#include "strategy_solver_heap_tpolyhedra_sympath.h"
#include "strategy_solver.h"

// NOLINTNEXTLINE(*)
#define BINSEARCH_SOLVER strategy_solver_binsearcht(\
  *static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns)
#if 0
// NOLINTNEXTLINE(*)
#define BINSEARCH_SOLVER strategy_solver_binsearch2t(\
  *static_cast<tpolyhedra_domaint *>(domain), solver, SSA.ns)
// NOLINTNEXTLINE(*)
#define BINSEARCH_SOLVER strategy_solver_binsearch3t(\
  *static_cast<tpolyhedra_domaint *>(domain), solver, SSA, SSA.ns)
#endif


void ssa_analyzert::operator()(
  incremental_solvert &solver,
  local_SSAt &SSA,
  const exprt &precondition,
  template_generator_baset &template_generator)
{
  if(SSA.goto_function.body.instructions.empty())
    return;

  solver << SSA;
  SSA.mark_nodes();

  solver.new_context();
  solver << SSA.get_enabling_exprs();

  // add precondition (or conjunction of asssertion in backward analysis)
  solver << precondition;

  domain=template_generator.domain();

  // get strategy solver from options
  strategy_solver_baset *s_solver;
  if(template_generator.options.get_bool_option("compute-ranking-functions"))
  {
    if(template_generator.options.get_bool_option(
         "monolithic-ranking-function"))
    {
    s_solver=new strategy_solvert(
      *static_cast<linrank_domaint *>(domain),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
      result=new linrank_domaint::templ_valuet();
    }
    else
    {
    s_solver=new strategy_solvert(
      *static_cast<lexlinrank_domaint *>(domain),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
      result=new lexlinrank_domaint::templ_valuet();
    }
  }
  else if(template_generator.options.get_bool_option("equalities"))
  {
    s_solver=new strategy_solvert(
      *static_cast<equality_domaint *>(domain),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
      result=new equality_domaint::equ_valuet();
  }
  else if(template_generator.options.get_bool_option("heap"))
  {
    s_solver=new strategy_solvert(
      *static_cast<heap_domaint *>(domain),
      solver,
      SSA,
      precondition,
      get_message_handler(),
      template_generator);
    result=new heap_domaint::heap_valuet();
  }
  else if(template_generator.options.get_bool_option("heap-interval")
          || template_generator.options.get_bool_option("heap-zones"))
  {
    if(template_generator.options.get_bool_option("sympath"))
    {
      s_solver=new strategy_solver_heap_tpolyhedra_sympatht(
        *static_cast<heap_tpolyhedra_sympath_domaint *>(domain),
        solver,
        SSA,
        precondition,
        get_message_handler(),
        template_generator);
      result=
        new heap_tpolyhedra_sympath_domaint::heap_tpolyhedra_sympath_valuet();
    }
    else
    {
      s_solver=new strategy_solver_heap_tpolyhedrat(
        *static_cast<heap_tpolyhedra_domaint *>(domain),
        solver,
        SSA,
        precondition,
        get_message_handler(),
        template_generator);
      result=new heap_tpolyhedra_domaint::heap_tpolyhedra_valuet();
    }
  }
  else
  {
    if(template_generator.options.get_bool_option("enum-solver"))
    {
      s_solver=new strategy_solvert(
        *static_cast<tpolyhedra_domaint *>(domain),
        solver,
        SSA,
        precondition,
        get_message_handler(),
        template_generator);
      result=new tpolyhedra_domaint::templ_valuet();
    }
    else if(template_generator.options.get_bool_option("predabs-solver"))
    {
      s_solver=new strategy_solvert(
        *static_cast<predabs_domaint *>(domain),
        solver,
        SSA,
        precondition,
        get_message_handler(),
        template_generator);
      result=new predabs_domaint::templ_valuet();
    }
    else if(template_generator.options.get_bool_option("binsearch-solver"))
    {
      result=new tpolyhedra_domaint::templ_valuet();
      s_solver=new BINSEARCH_SOLVER;
    }
    else
      assert(false);
  }

  s_solver->set_message_handler(get_message_handler());

  // initialize inv
  domain->initialize(*result);

  // iterate
  while(s_solver->iterate(*result)) {}

  solver.pop_context();

  // statistics
  solver_instances+=s_solver->get_number_of_solver_instances();
  solver_calls+=s_solver->get_number_of_solver_calls();
  solver_instances+=s_solver->get_number_of_solver_instances();

  // imprecision identification
  if(template_generator.options.get_bool_option("show-imprecise-vars"))
  {
    // get imprecise SSA variable names
    std::vector<std::string> ssa_vars=
      domain->identify_invariant_imprecision(*result);

    // link the variables to the exact goto instuctions
    find_goto_instrs(SSA, ssa_vars);
  }

  delete s_solver;
}

void ssa_analyzert::get_result(exprt &_result, const domaint::var_sett &vars)
{
  domain->project_on_vars(*result, vars, _result);
}

void ssa_analyzert::update_heap_out(summaryt::var_sett &out)
{
  heap_domaint &heap_domain=static_cast<heap_domaint &>(*domain);

  auto new_heap_vars=heap_domain.get_new_heap_vars();
  out.insert(new_heap_vars.begin(), new_heap_vars.end());
}

const exprt ssa_analyzert::input_heap_bindings()
{
  return static_cast<heap_domaint &>(*domain).get_iterator_bindings();
}

/// Save the source code information about the variables into
///   the summary of imprecise variables
/// \param SSA: Local SSA
/// \param ssa_vars: Vector of imprecise SSA loop back variable names
void ssa_analyzert::find_goto_instrs(
  local_SSAt &SSA,
  const std::vector<std::string> &ssa_vars)
{
  imprecise_vars_summary.resize(ssa_vars.size());
  imprecise_varst::iterator summary_it=imprecise_vars_summary.begin();

  for(auto &var : ssa_vars)
  {
    bool is_dynamic=false;

    // save the real name of variables into the summary
    if(is_dynamic_name(var))
    {
      summary_it->pretty_name=get_dynobj_name(var);
      is_dynamic=true;
    }
    else
      summary_it->pretty_name=get_original_name(var);

    int node_loc=get_name_node_loc(var);

    // Node location of loop back variables is known
    if(node_loc!=-1)
    {
      // get the actual loop back node in the local SSA
      local_SSAt::nodest::iterator lb_node=SSA.find_node(
        SSA.get_location(static_cast<unsigned>(node_loc)));

      // save the source location of the loop head node in the summary
      local_SSAt::nodest::iterator lh_node=lb_node->loophead;
      summary_it->loophead_line=lh_node->location->source_location.get_line();

      // for dynamic objects additionally we save:
      //  allocation site location
      //  if structured-typed then its structure field
      if(is_dynamic)
      {
        int node_line=get_dynobj_line(var);

        summary_it->dyn_alloc_line=node_line==-1
          ? "<UNKNOWN>"
          : (SSA.find_node(SSA.get_location(static_cast<unsigned>(node_line))))
              ->location->source_location.get_line();

        summary_it->dyn_mem_field=get_dynamic_field(var);
      }
    }

    summary_it++;
  }
}

/// Get only the dynamic object name: "dynamic_object$i#y"
/// \param name: SSA loop-back Dynamic object name
/// \return SSA dynamic object name without its field and anything after
std::string ssa_analyzert::get_dynobj_name(const std::string &name)
{
  size_t idx;

  // is structure-typed object ->
  //  get the part right before the object field
  if((idx=name.find('.', DYN_PREFIX_LEN))!=std::string::npos)
    return name.substr(0, idx);
  // remove everything after loop back part of the string
  else if((idx=is_loopback_var(name))!=std::string::npos)
    return name.substr(0, idx);
  else
    return name;
}

/// Extract the node location from its ssa name.
/// \param name: SSA loop back variable name.
/// \return Location of the node in the local SSA.
int ssa_analyzert::get_name_node_loc(const std::string &name)
{
  // is not a loop back variable -> has unknown location
  size_t idx=is_loopback_var(name);
  if(idx==std::string::npos)
    return -1;

  // get the location number after '#lb'
  std::string loc_str=name.substr(idx+3);
  assert(!loc_str.empty());
  return std::stoi(loc_str);
}

