/*******************************************************************\

Module: Analysis of expressions used as array indices

Author: Viktor Malik, imalik@fit.vutbr.cz

\*******************************************************************/

/// \file
/// Analysis of expressions used as array indices.
/// L-expressions are captured per-location - for each location and for each
/// array, the result states which indices of the array might have been
/// assigned to.
/// R-expressions are captured globally for the whole program - for each array,
/// the result states which indices are read from somewhere in the program.

#ifndef CPROVER_2LS_SSA_ARRAY_INDEX_ANALYSIS_H
#define CPROVER_2LS_SSA_ARRAY_INDEX_ANALYSIS_H

#include <analyses/ai.h>
#include <iostream>

class array_index_domaint:public ai_domain_baset
{
public:
  void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) override;

  bool merge(const array_index_domaint &other, locationt from, locationt to);

  void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const override;

  // Information about a single array index usage
  struct index_infot
  {
    exprt index;
    locationt loc;

    index_infot(const exprt &index, const locationt &loc):
      index(index), loc(loc) {}

    bool operator<(const index_infot &rhs) const
    {
      return std::tie(index, loc)<std::tie(rhs.index, rhs.loc);
    }
  };
  typedef std::map<irep_idt, std::set<index_infot>> index_mapt;

  // Written indices are stored per-location - we'll need to know which indices
  // might have been written so far for an array.
  index_mapt written_indices;

protected:
  void collect_indices(const exprt &expr, locationt loc, index_mapt &dest_map);
  void collect_lhs_indices(const exprt &expr, locationt loc);
  void collect_rhs_indices(
    const exprt &expr,
    locationt loc,
    ai_baset &ai);
};

class array_index_analysist:public ait<array_index_domaint>
{
public:
  array_index_analysist(
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    operator()(goto_function, ns);
  }

  // Read indices are stored globally for the whole analysis - we'll need to
  // know which indices may be read anywhere in the program.
  array_index_domaint::index_mapt read_indices;

protected:
  void output(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier,
    std::ostream &out) const override;
};


#endif // CPROVER_2LS_SSA_ARRAY_INDEX_ANALYSIS_H
