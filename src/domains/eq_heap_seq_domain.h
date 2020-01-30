//
// Created by vmalik on 5/3/19.
//

#ifndef CPROVER_2LS_DOMAINS_EQ_HEAP_SEQ_DOMAIN_H
#define CPROVER_2LS_DOMAINS_EQ_HEAP_SEQ_DOMAIN_H


#include "domain.h"
#include "heap_domain.h"
#include "equality_domain.h"
#include "heap_tpolyhedra_sympath_domain.h"

class eq_heap_seq_domaint:public domaint
{
public:
  equality_domaint equality_domain;
  heap_tpolyhedra_sympath_domaint heap_domain;

  eq_heap_seq_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const var_specst &var_specs,
    const local_SSAt &SSA):
    domaint(_domain_number, _renaming_map, ns),
    equality_domain(_domain_number, _renaming_map, var_specs, ns),
    heap_domain(_domain_number, _renaming_map, var_specs, SSA, heap_tpolyhedra_domaint::polyhedra_kindt::INTERVAL)
  {}

  class eq_heap_seq_valuet:public valuet{
  public:
    equality_domaint::equ_valuet equality_value;
    heap_tpolyhedra_sympath_domaint::heap_tpolyhedra_sympath_valuet heap_value;
  };

  virtual void initialize(valuet &value) override;

  virtual void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const override;

  virtual void output_domain(
    std::ostream &out,
    const namespacet &ns) const override;

  virtual void project_on_vars(
    valuet &value,
    const var_sett &vars,
    exprt &result) override;
};


#endif //CPROVER_2LS_DOMAINS_EQ_HEAP_SEQ_DOMAIN_H
