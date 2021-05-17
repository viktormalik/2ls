/*******************************************************************\

Module: Abstract domain base class

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Abstract domain base class

#ifndef CPROVER_2LS_DOMAINS_DOMAIN_H
#define CPROVER_2LS_DOMAINS_DOMAIN_H

#include <iostream>
#include <set>

#include <util/std_expr.h>
#include <util/i2string.h>
#include <langapi/language_util.h>
#include <util/replace_expr.h>
#include <util/namespace.h>
#include <solvers/refinement/bv_refinement.h>
#include <goto-programs/goto_program.h>
#include <memory>
#include "symbolic_path.h"
#include "incremental_solver.h"

// Forward declaration - real is in template_generator_base.h
class template_generator_baset;
class strategy_solver_baset;

class local_SSAt;

typedef goto_programt::const_targett locationt;

/// Guards specification
struct guardst
{
  typedef exprt guardt;
  typedef enum { LOOP, IN, OUT, OUTL } kindt;

  kindt kind;
  guardt pre_guard;
  guardt post_guard;
  exprt aux_expr;

  void output(std::ostream &out, const namespacet &ns) const;
  /// Merge two guardst objects into one by conjunction of the guards
  static guardst merge_and_guards(
    const guardst &g1,
    const guardst &g2,
    const namespacet &ns);
};

typedef exprt vart;
typedef std::vector<vart> var_listt;
typedef std::set<vart> var_sett;

/// Variable specification
/// Contains a variable (exprt) and guards.
struct var_spect
{
  vart var;
  guardst guards;
  var_listt related_vars;
  locationt loc;

  void output(std::ostream &out, const namespacet &ns) const;
};

/// Vector of variable specifications.
/// Implements printing method.
struct var_specst:std::vector<var_spect>
{
  void output(std::ostream &out, const namespacet &ns) const;
};

class domaint
{
public:
  domaint(
    unsigned _domain_number,
    replace_mapt &_renaming_map,
    const namespacet &_ns):
    domain_number(_domain_number),
    renaming_map(_renaming_map),
    ns(_ns)
  {
  }

  virtual ~domaint()=default;

  /// Base class for abstract value. Contains only the basic value, the rest is
  /// defined per-domain.
  class valuet
  {
  public:
    typedef enum { TOP, BOTTOM, OTHER } basic_valuet;

    valuet():basic_value(OTHER) {}

    virtual ~valuet() {}

    /// Each abstract value needs to implement clone with covariant return type.
    /// This is needed to properly clone abstract value when only a pointer to
    /// valuet is available.
    /// Since the method returns a raw pointer, the caller is responsible for
    /// taking ownership of the created object.
    virtual valuet *clone()=0;

    basic_valuet basic_value;
  };

  /// Create a new empty abstract value for the domain
  virtual std::unique_ptr<valuet> new_value()=0;
  /// Create a new strategy solver for the domain
  virtual std::unique_ptr<strategy_solver_baset> new_strategy_solver(
    incremental_solvert &solver,
    const local_SSAt &SSA,
    message_handlert &message_handler)=0;

  // General methods for the strategy solver
  // Each generic strategy solver should implement at least these.

  /// Initialize an abstract value.
  /// The derived class is expected to override this.
  virtual void initialize_value(valuet &value)
  {
    value.basic_value=valuet::BOTTOM;
  }

  /// Initialize domain at the beginning of strategy solving
  virtual void initialize() {}

  /// Initialize value at the beginning of strategy solver iteration
  virtual void init_value_solver_iteration(valuet &value) {}

  /// Finalize the domain after a single iteration of strategy solving.
  virtual void finalize_solver_iteration() {}

  /// Abstract value join - not used by most of the domains since the join
  /// is typically done between an abstract value and a model of satisfiability
  /// in the strategy solver (see method edit_row).
  virtual void join(valuet &value1, const valuet &value2);

  /// Output the domain (its template)
  virtual void output_domain(std::ostream &out, const namespacet &ns) const=0;

  /// Output the given abstract value in this domain.
  virtual void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const=0;

  /// Project invariant (abstract value) onto a set of variables.
  /// If vars is empty, project onto all variables (get the entire invariant).
  // (not useful to make value const (e.g. union-find))
  virtual void project_on_vars(
    valuet &value,
    const var_sett &vars,
    exprt &result,
    bool ignore_top=false)=0;

  // Methods related to symbolic paths

  /// Restrict the template to the given symbolic path.
  virtual void restrict_to_sympath(const symbolic_patht &sympath)=0;
  /// Restrict template to any other paths than those specified.
  virtual void eliminate_sympaths(
    const std::vector<symbolic_patht> &sympaths)=0;
  /// Undo the last symbolic path restriction
  virtual void undo_sympath_restriction()=0;
  /// Remove all symbolic path restrictions.
  virtual void remove_all_sympath_restrictions()=0;

protected:
  unsigned domain_number; // serves as id for variables names
  replace_mapt &renaming_map;
  const namespacet &ns;

  inline void rename(exprt &expr)
  {
    replace_expr(renaming_map, expr);
  }

  inline void rename(exprt::operandst &operands)
  {
    for(unsigned i=0; i<operands.size(); ++i)
      replace_expr(renaming_map, operands[i]);
  }
};

#endif // CPROVER_2LS_DOMAINS_DOMAIN_H
