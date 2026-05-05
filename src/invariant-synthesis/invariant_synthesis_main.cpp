/*******************************************************************\

Module: Invariant Synthesis Main

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Main entry point for the invariant-synthesis tool.

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif

#include <util/config.h>
#include <util/cout_message.h>
#include <util/exit_codes.h>
#include <util/format_expr.h>
#include <ansi-c/expr2c.h>
#include <util/options.h>
#include <util/ui_message.h>

#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_program.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/process_goto_program.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/set_properties.h>

#include <ansi-c/ansi_c_language.h>
#include <langapi/mode.h>

#include "invariant_synthesizer.h"
#include "invariant_checker.h"

#include <cstdint>
#include <iostream>
#include <map>
#include <vector>

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static void register_languages()
{
  register_language(new_ansi_c_language);
}

/// Collects all loop IDs present in \p goto_model.
static std::vector<loop_idt> find_all_loops(const goto_modelt &goto_model)
{
  std::vector<loop_idt> loops;
  for(const auto &func_entry : goto_model.goto_functions.function_map)
  {
    const irep_idt &func_id = func_entry.first;
    for(const auto &instr : func_entry.second.body.instructions)
    {
      if(instr.is_backwards_goto())
        loops.emplace_back(func_id, instr.loop_number);
    }
  }
  return loops;
}

static optionst make_default_options()
{
  optionst options;
  options.set_option("built-in-assertions", true);
  options.set_option("assertions", true);
  options.set_option("assumptions", true);
  options.set_option("propagation", true);
  options.set_option("simplify", true);
  options.set_option("simple-slice", true);
  options.set_option("depth", UINT32_MAX);
  options.set_option("exploration-strategy", "lifo");
  options.set_option("rewrite-union", true);
  options.set_option("self-loops-to-assumptions", true);
  options.set_option("arrays-uf", "auto");
  options.set_option("trace", true);
  return options;
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  auto vec = narrow_argv(argc, argv_wide);
  auto narrow = to_c_str_array(std::begin(vec), std::end(vec));
  auto argv = narrow.data();
#else
int main(int argc, const char **argv)
{
#endif
  if(argc < 2)
  {
    std::cerr << "Usage: invariant-synthesis <file.c> [--max-iter N]\n";
    return CPROVER_EXIT_USAGE_ERROR;
  }

  unsigned max_iterations = 10;
  for(int i = 2; i < argc - 1; ++i)
  {
    if(std::string(argv[i]) == "--max-iter")
      max_iterations = static_cast<unsigned>(std::stoul(argv[i + 1]));
  }

  console_message_handlert message_handler;
  // Suppress verbose CBMC internals; show STATUS and above.
  message_handler.set_verbosity(messaget::M_STATUS);
  messaget log(message_handler);

  register_languages();

  // Set up a default native config before parsing.
  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  config.set_arch("x86_64");

  const optionst options = make_default_options();

  // 1. Parse the C file.
  log.status() << "Parsing " << argv[1] << messaget::eom;
  goto_modelt goto_model;
  try
  {
    goto_model = initialize_goto_model({argv[1]}, message_handler, options);
  }
  catch(const std::exception &e)
  {
    log.error() << "Failed to parse: " << e.what() << messaget::eom;
    return CPROVER_EXIT_PARSE_ERROR;
  }

  config.set_from_symbol_table(goto_model.symbol_table);
  goto_model.goto_functions.update();
  goto_model.goto_functions.compute_loop_numbers();

  // 2. Identify all loops.
  const std::vector<loop_idt> loops = find_all_loops(goto_model);
  if(loops.empty())
  {
    log.status() << "No loops found." << messaget::eom;
    return CPROVER_EXIT_SUCCESS;
  }
  log.status() << "Found " << loops.size() << " loop(s)." << messaget::eom;

  ui_message_handlert ui_message_handler(message_handler);

  const namespacet ns(goto_model.symbol_table);

  // Per-loop lists of provable and unprovable invariants.
  std::map<loop_idt, std::vector<exprt>> provable_invariants;
  std::map<loop_idt, std::vector<exprt>> unprovable_invariants;

  // ---------------------------------------------------------------------------
  // Main synthesis loop
  // ---------------------------------------------------------------------------
  for(unsigned iter = 0; iter < max_iterations; ++iter)
  {
    log.status() << "\n=== Iteration " << (iter + 1) << " ===" << messaget::eom;

    // 3. For each loop, enumerate and check candidates.
    for(const auto &loop_id : loops)
    {
      const std::vector<exprt> candidates =
        enumerate_symbolic_comparison_from_vars(goto_model, loop_id, log);

      log.status() << "Loop " << loop_id.function_id << "."
                   << loop_id.loop_number << ": " << candidates.size()
                   << " candidate(s)" << messaget::eom;

      for(const auto &candidate : candidates)
      {
        // Skip already-classified candidates.
        auto &prov = provable_invariants[loop_id];
        auto &unprov = unprovable_invariants[loop_id];
        if(
          std::find(prov.begin(), prov.end(), candidate) != prov.end() ||
          std::find(unprov.begin(), unprov.end(), candidate) != unprov.end())
          continue;

        // 4. Check provability.
        const provability_resultt r = check_invariant_provable(
          goto_model, loop_id, candidate, options, ui_message_handler, log);

        if(r.is_provable)
        {
          log.status() << "  PROVABLE: " << expr2c(candidate, ns) << messaget::eom;
          prov.push_back(candidate);
        }
        else
        {
          log.status() << "  not provable: " << expr2c(candidate, ns)
                       << messaget::eom;
          unprov.push_back(candidate);
        }
      }
    }

    // 5. Print summary of provable invariants.
    log.status() << "\nProvable invariants this iteration:" << messaget::eom;
    for(const auto &loop_id : loops)
    {
      const auto &prov = provable_invariants[loop_id];
      log.status() << "  Loop " << loop_id.function_id << "."
                   << loop_id.loop_number << ": " << prov.size()
                   << " provable" << messaget::eom;
    }

    // 6. Try to prove VCs using the conjunction of all provable invariants.
    // Build a single combined invariant per loop (conjunction of all provable).
    std::map<loop_idt, exprt> combined;
    bool any_provable = false;
    for(const auto &loop_id : loops)
    {
      const auto &prov = provable_invariants[loop_id];
      if(prov.empty())
        continue;
      any_provable = true;
      exprt conj = prov[0];
      for(std::size_t i = 1; i < prov.size(); ++i)
        conj = and_exprt(conj, prov[i]);
      combined[loop_id] = conj;
    }

    if(!any_provable)
    {
      log.status() << "No provable invariants yet, continuing." << messaget::eom;
      continue;
    }

    const vc_check_resultt vc = check_vcs_with_invariants(
      goto_model, combined, options, ui_message_handler, log);

    if(vc.is_sufficient)
    {
      log.status() << "\nSUCCESS: All VCs proved!" << messaget::eom;
      for(const auto &loop_id : loops)
      {
        for(const auto &inv : provable_invariants[loop_id])
          log.result() << "  Loop " << loop_id.function_id << "."
                       << loop_id.loop_number << ": " << expr2c(inv, ns)
                       << messaget::eom;
      }
      return CPROVER_EXIT_SUCCESS;
    }
    else
    {
      log.status() << "VCs not yet proved. Counterexample available: "
                   << (vc.counterexample.has_value() ? "yes" : "no")
                   << messaget::eom;
    }
  }

  log.status() << "\nFAILED: Could not prove all VCs within " << max_iterations
               << " iteration(s)." << messaget::eom;

  log.status() << "\nFinal provable invariants (not sufficient):"
               << messaget::eom;
  for(const auto &loop_id : loops)
  {
    for(const auto &inv : provable_invariants[loop_id])
      log.result() << "  Loop " << loop_id.function_id << "."
                   << loop_id.loop_number << ": " << expr2c(inv, ns)
                   << messaget::eom;
  }

  log.status() << "\nUnprovable candidates:" << messaget::eom;
  for(const auto &loop_id : loops)
  {
    for(const auto &inv : unprovable_invariants[loop_id])
      log.result() << "  Loop " << loop_id.function_id << "."
                   << loop_id.loop_number << ": " << expr2c(inv, ns)
                   << messaget::eom;
  }

  return CPROVER_EXIT_VERIFICATION_UNSAFE;
}
