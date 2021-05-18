/*******************************************************************\

Module: Abstract domain for computing invariants for different
        program symbolic paths

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Abstract domain for computing invariants for different program symbolic
/// paths. The invariants can be computed in arbitrary domain (called the inner
/// domain).
/// Designed to work with strategy_solver_sympatht.

#ifndef CPROVER_2LS_DOMAINS_SYMPATH_DOMAIN_H
#define CPROVER_2LS_DOMAINS_SYMPATH_DOMAIN_H

#include "domain.h"
#include <ssa/local_ssa.h>

class sympath_domaint:public domaint
{
public:
  sympath_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const local_SSAt &SSA,
    std::unique_ptr<domaint> inner_domain):
    domaint(_domain_number, _renaming_map, SSA.ns),
    inner_domain(std::move(inner_domain))
  {
    exprt::operandst false_loop_guards;
    for(auto &g : SSA.loop_guards)
      false_loop_guards.push_back(not_exprt(g.first));
    no_loops_path=conjunction(false_loop_guards);
  }

  std::unique_ptr<domaint> inner_domain;

  // Value is a map from expression (symbolic path) to an invariant in the
  // inner domain
  class sympath_valuet:
    public valuet,
    public std::map<exprt, std::unique_ptr<domaint::valuet>>
  {
  public:
    explicit sympath_valuet(
      std::unique_ptr<domaint::valuet> inner_value_template):
      inner_value_template(std::move(inner_value_template)) {}

    sympath_valuet *clone() override
    {
      // Clone the inner value template
      auto new_inner_value=std::unique_ptr<domaint::valuet>(
        inner_value_template->clone());
      auto new_value=new sympath_valuet(std::move(new_inner_value));
      // Clone the inner map
      for(auto &val : *this)
        new_value->emplace(
          val.first,
          std::unique_ptr<domaint::valuet>(val.second->clone()));
      return new_value;
    }

    // A template of the inner value (corresponding to the inner domain) that
    // will be used to create new values.
    std::unique_ptr<domaint::valuet> inner_value_template;
  };

  std::unique_ptr<valuet> new_value() override
  {
    return std::unique_ptr<valuet>(
      new sympath_valuet(inner_domain->new_value()));
  }

  void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const override;

  void output_domain(
    std::ostream &out,
    const namespacet &ns) const override;

  void project_on_vars(
    domaint::valuet &value,
    const var_sett &vars,
    exprt &result,
    bool ignore_top) override;

  // These do not need to be implemented since there is no domain above this
  // one that would use it.
  void restrict_to_sympath(const symbolic_patht &sympath) override {}
  void eliminate_sympaths(
    const std::vector<symbolic_patht> &sympaths) override {}
  void undo_sympath_restriction() override {}
  void remove_all_sympath_restrictions() override {}

  std::unique_ptr<strategy_solver_baset> new_strategy_solver(
    incremental_solvert &solver,
    const local_SSAt &SSA,
    message_handlert &message_handler) override;

  tpolyhedra_domaint *get_tpolyhedra_domain() override
  {
    return inner_domain->get_tpolyhedra_domain();
  }

protected:
  // Special path containing conjunction negations of all loop-select guards
  // This must be stored explicitly since the solver is not able to explore this
  // path even though it can be feasible
  exprt no_loops_path;

  friend class strategy_solver_sympatht;
};


#endif // CPROVER_2LS_DOMAINS_SYMPATH_DOMAIN_H
