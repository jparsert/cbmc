/*******************************************************************\

Module: Invariant Checker

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Checks loop invariant candidates for provability and VC sufficiency.

#ifndef CPROVER_INVARIANT_SYNTHESIS_INVARIANT_CHECKER_H
#define CPROVER_INVARIANT_SYNTHESIS_INVARIANT_CHECKER_H

#include <goto-programs/goto_model.h>
#include <goto-programs/goto_trace.h>
#include <goto-programs/loop_ids.h>

#include <util/options.h>

#include <map>
#include <optional>
#include <vector>

class messaget;
class ui_message_handlert;

/// Result of checking a single invariant candidate for provability.
struct provability_resultt
{
  bool is_provable = false;
  std::optional<goto_tracet> counterexample;
};

/// Result of checking whether a set of invariants proves all VCs.
struct vc_check_resultt
{
  bool is_sufficient = false;
  std::optional<goto_tracet> counterexample;
};

/// Checks whether \p candidate is a provable (inductive) invariant for
/// \p loop_id. Uses a copy of \p goto_model so the original is not modified.
provability_resultt check_invariant_provable(
  const goto_modelt &goto_model,
  const loop_idt &loop_id,
  const exprt &candidate,
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  messaget &log);

/// Checks whether \p invariants (one per loop) are sufficient to prove all
/// assertions in \p goto_model. Uses a copy of \p goto_model.
vc_check_resultt check_vcs_with_invariants(
  const goto_modelt &goto_model,
  const std::map<loop_idt, exprt> &invariants,
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  messaget &log);

#endif // CPROVER_INVARIANT_SYNTHESIS_INVARIANT_CHECKER_H
