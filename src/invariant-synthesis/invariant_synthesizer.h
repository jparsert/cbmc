/*******************************************************************\

Module: Invariant Synthesizer

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Enumerative invariant synthesizer.
/// Enumerates candidate loop invariants from program variables
/// using simple predicates (equalities, inequalities, bounds).

#ifndef CPROVER_INVARIANT_SYNTHESIS_INVARIANT_SYNTHESIZER_H
#define CPROVER_INVARIANT_SYNTHESIS_INVARIANT_SYNTHESIZER_H

#include <goto-programs/goto_model.h>
#include <goto-programs/loop_ids.h>

#include <vector>

class messaget;

/// Collects all scalar (integer/boolean) program variables visible at a
/// given loop head from the symbol table.
std::vector<symbol_exprt> collect_loop_variables(
  const goto_modelt &goto_model,
  const loop_idt &loop_id);

/// Enumerates candidate invariant expressions for a single loop.
/// Returns a flat list of candidate \c exprt values.
/// Candidates are simple predicates over collected variables:
///   - var >= 0, var == 0
///   - var1 <= var2, var1 == var2
/// This list is intentionally minimal and easy to extend.
std::vector<exprt> enumerate_symbolic_comparison_from_vars(
  const goto_modelt &goto_model,
  const loop_idt &loop_id,
  messaget &log);

/// Parses \p expr_str as a C boolean expression in the variable scope of
/// \p loop_id's function and returns the typed \c exprt.
/// Returns \c nullopt if parsing or type-checking fails.
std::optional<exprt> parse_invariant_string(
  const goto_modelt &goto_model,
  const loop_idt &loop_id,
  const std::string &expr_str,
  message_handlert &message_handler);

#endif // CPROVER_INVARIANT_SYNTHESIS_INVARIANT_SYNTHESIZER_H
