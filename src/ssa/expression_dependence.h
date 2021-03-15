/*******************************************************************\

Module: Analysis of potential relations among expressions.
        Computes which expressions (mainly symbols) occur in the same
        expression/statement and therefore there may be a relation
        between them. This information can be later used to create
        a more precise analysis template.

Author: Viktor Malik, viktor.malik@gmail.com

\*******************************************************************/

/// \file
/// Analysis of potential relations among expressions.
/// Computes which expressions (mainly symbols) occur in the same
/// expression/statement and therefore there may be a relation between them.
/// This information can be later used to create a more precise analysis
/// template.

#ifndef CPROVER_2LS_SSA_EXPRESSION_DEPENDENCE_H
#define CPROVER_2LS_SSA_EXPRESSION_DEPENDENCE_H

#include <analyses/ai.h>
#include <util/union_find.h>
#include "local_ssa.h"

class expression_dependence_domaint:public ai_domain_baset
{
public:
  // Equivalence partitioning of the expressions onto dependence sets
  union_find<exprt> dep_sets;

  void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) override;

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const override;

  bool merge(
    const expression_dependence_domaint &other,
    locationt from,
    locationt to);

protected:
  void collect_exprs_rec(const exprt &expr, std::set<exprt> &result);
  void make_union(std::set<exprt> &exprs);

  unsigned loop_end = 0;
};

class expression_dependencet:public ait<expression_dependence_domaint>
{
public:
  expression_dependencet(
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    operator()(goto_function, ns);
  }

  const expression_dependence_domaint &get_deps_for_ssa_expr(
    const exprt &expr, const local_SSAt &SSA);

protected:
  friend class expression_dependence_domaint;
};

#endif //CPROVER_2LS_SSA_EXPRESSION_DEPENDENCE_H
