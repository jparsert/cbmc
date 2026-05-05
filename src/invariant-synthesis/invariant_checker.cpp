/*******************************************************************\

Module: Invariant Checker

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Invariant checker implementation.

#include "invariant_checker.h"

#include <util/format_expr.h>
#include <util/message.h>
#include <util/std_expr.h>
#include <util/ui_message.h>

#include <ansi-c/goto-conversion/goto_convert_functions.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/process_goto_program.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/set_properties.h>

#include <goto-checker/all_properties_verifier_with_trace_storage.h>
#include <goto-checker/multi_path_symex_checker.h>
#include <goto-checker/properties.h>

#include <goto-instrument/contracts/contracts.h>
#include <goto-instrument/contracts/utils.h>

#include <pointer-analysis/add_failed_symbols.h>

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static goto_modelt copy_goto_model(const goto_modelt &src)
{
  goto_modelt dst;
  for(const auto &sym : src.symbol_table.symbols)
    dst.symbol_table.add(sym.second);
  for(const auto &f : src.goto_functions.function_map)
  {
    auto &df = dst.goto_functions.function_map[f.first];
    df.parameter_identifiers = f.second.parameter_identifiers;
    df.body.copy_from(f.second.body);
  }
  dst.goto_functions.update();
  dst.goto_functions.compute_loop_numbers();
  return dst;
}

/// Preprocesses \p model, annotates \p inv_map, applies loop contracts,
/// runs the verifier, and returns the resulting properties.
static propertiest run_verifier(
  goto_modelt &model,
  const invariant_mapt &inv_map,
  const optionst &options,
  messaget &log)
{
  // 1. Preprocess so the model is in normal form.
  add_failed_symbols(model.symbol_table);
  process_goto_program(model, options, log);
  model.goto_functions.update();
  model.goto_functions.compute_loop_numbers();

  // 2. Annotate invariants (loop numbers are now stable).
  annotate_invariants(inv_map, model);

  // 3. Apply loop contracts.
  code_contractst contracts(
    model, log, loop_contract_configt{true, true, true});
  contracts.apply_loop_contracts();

  model.goto_functions.update();
  remove_skip(model);
  label_properties(model);

  // 4. goto_convert (as in cegis_verifier).
  goto_convert(
    model.symbol_table, model.goto_functions, log.get_message_handler());

  // 5. Run the verifier.
  ui_message_handlert ui(log.get_message_handler());
  all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>
    checker(options, ui, model);
  checker();
  return checker.get_properties();
}

/// Returns true if no invariant-related property fails.
/// Skips assigns-check failures (property_class == "assigns") since those
/// are about the assigns clause, not invariant provability.
/// An invariant is provable (inductive) if only the loop invariant checks pass.
/// We ignore:
///   - assigns-check failures (property_class == "assigns")
///   - user assertion failures (property_class == "assertion") -- those test
///     sufficiency, not provability
static bool invariant_properties_pass(const propertiest &props)
{
  for(const auto &prop : props)
  {
    if(prop.second.status != property_statust::FAIL)
      continue;
    const irep_idt cls =
      prop.second.pc->source_location().get_property_class();
    if(cls == "assigns" || cls == "assertion")
      continue;
    return false;
  }
  return true;
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

provability_resultt check_invariant_provable(
  const goto_modelt &goto_model,
  const loop_idt &loop_id,
  const exprt &candidate,
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  messaget &log)
{
  provability_resultt result;

  goto_modelt model = copy_goto_model(goto_model);

  // The contracts code calls conjunction(invariant.operands()), so the stored
  // expression must have boolean operands. Wrap in and_exprt(candidate, true).
  invariant_mapt inv_map;
  inv_map[loop_id] = and_exprt(candidate, true_exprt());

  const propertiest props =
    run_verifier(model, inv_map, options, log);

  log.debug() << "Provability check for " << format(candidate) << ":" << messaget::eom;
  for(const auto &p : props)
    if(p.second.status == property_statust::FAIL)
      log.debug() << "  FAIL [" << p.second.pc->source_location().get_property_class()
                  << "] " << p.second.description << messaget::eom;

  result.is_provable = invariant_properties_pass(props);
  return result;
}

vc_check_resultt check_vcs_with_invariants(
  const goto_modelt &goto_model,
  const std::map<loop_idt, exprt> &invariants,
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  messaget &log)
{
  vc_check_resultt result;

  goto_modelt model = copy_goto_model(goto_model);

  invariant_mapt inv_map;
  for(const auto &e : invariants)
    inv_map[e.first] = and_exprt(e.second, true_exprt());

  const propertiest props =
    run_verifier(model, inv_map, options, log);

  // For sufficiency: check that all user assertions pass (ignore assigns).
  bool sufficient = true;
  for(const auto &p : props)
  {
    if(p.second.status != property_statust::FAIL)
      continue;
    if(p.second.pc->source_location().get_property_class() == "assigns")
      continue;
    sufficient = false;
    break;
  }
  result.is_sufficient = sufficient;
  return result;
}
