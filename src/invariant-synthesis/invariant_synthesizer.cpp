/*******************************************************************\

Module: Invariant Synthesizer

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Enumerative invariant synthesizer implementation.

#include "invariant_synthesizer.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/message.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_functions.h>

#include <ansi-c/ansi_c_language.h>

std::vector<symbol_exprt> collect_loop_variables(
  const goto_modelt &goto_model,
  const loop_idt &loop_id)
{
  std::vector<symbol_exprt> vars;

  // Collect all non-auxiliary scalar symbols from the symbol table
  // that belong to the function containing the loop.
  for(const auto &sym_entry : goto_model.symbol_table.symbols)
  {
    const symbolt &sym = sym_entry.second;

    // Skip non-variable symbols (functions, types, etc.)
    if(sym.is_type || sym.is_macro)
      continue;

    // Only consider symbols from the loop's function or file-scope
    if(
      !sym.name.empty() &&
      sym.location.get_function() != loop_id.function_id &&
      !sym.is_static_lifetime)
      continue;

    // Skip CBMC-internal symbols
    const std::string name_str = id2string(sym.name);
    if(
      name_str.find("__CPROVER") != std::string::npos ||
      name_str.find("#") != std::string::npos ||
      name_str.find("$") != std::string::npos)
      continue;

    // Only scalar integer or boolean types
    const typet &t = sym.type;
    if(
      t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
      t.id() == ID_bool || t.id() == ID_c_bool)
    {
      vars.push_back(sym.symbol_expr());
    }
  }

  return vars;
}

std::vector<exprt> enumerate_symbolic_comparison_from_vars(
  const goto_modelt &goto_model,
  const loop_idt &loop_id,
  messaget &log)
{
  std::vector<exprt> candidates;

  const auto vars = collect_loop_variables(goto_model, loop_id);

  log.debug() << "Enumerating candidates for loop " << loop_id.function_id
              << "." << loop_id.loop_number << " with " << vars.size()
              << " variables" << messaget::eom;

  const exprt zero = from_integer(0, signed_int_type());

  // Unary predicates: var >= 0, var == 0
  for(const auto &v : vars)
  {
    if(v.type().id() == ID_signedbv || v.type().id() == ID_unsignedbv)
    {
      const exprt zero_typed = from_integer(0, v.type());
      const exprt one_typed = from_integer(1, v.type());

      candidates.push_back(binary_relation_exprt(v, ID_ge, zero_typed));
      candidates.push_back(binary_relation_exprt(v, ID_ge, one_typed));
      candidates.push_back(equal_exprt(v, zero_typed));
      candidates.push_back(not_exprt(equal_exprt(v, zero_typed)));

    }
  }

  // Binary predicates: var1 <= var2, var1 == var2
  for(std::size_t i = 0; i < vars.size(); ++i)
  {
    for(std::size_t j = i + 1; j < vars.size(); ++j)
    {
      const auto &v1 = vars[i];
      const auto &v2 = vars[j];

      // Only compare same-type variables
      if(v1.type() != v2.type())
        continue;

      candidates.push_back(binary_relation_exprt(v1, ID_le, v2));
      candidates.push_back(binary_relation_exprt(v2, ID_le, v1));
      candidates.push_back(equal_exprt(v1, v2));
    }
  }

  return candidates;
}

std::optional<exprt> parse_invariant_string(
  const goto_modelt &goto_model,
  const loop_idt &loop_id,
  const std::string &expr_str,
  message_handlert &message_handler)
{
  // Build a symbol table with variables under their base names so that
  // to_expr can resolve e.g. "x" even though the real symbol is "main::1::x".
  // After parsing we substitute the base-name symbols back to the real ones.
  symbol_tablet base_st;
  std::map<irep_idt, symbol_exprt> base_to_real; // base_name -> real symbol_exprt

  for(const auto &v : collect_loop_variables(goto_model, loop_id))
  {
    const std::string full = id2string(v.get_identifier());
    const auto pos = full.rfind("::");
    const irep_idt base =
      pos == std::string::npos ? full : irep_idt(full.substr(pos + 2));

    if(base_to_real.count(base))
      continue; // skip shadowed names

    symbolt sym;
    sym.name = base;
    sym.base_name = base;
    sym.type = v.type();
    sym.is_lvalue = true;
    base_st.add(sym);
    base_to_real.emplace(base, v);
  }

  const namespacet ns(base_st);
  ansi_c_languaget language;
  exprt expr;
  null_message_handlert null_message; // suppress "failed to find symbol" noise
  if(language.to_expr(expr_str, "", expr, ns, null_message))
  {
    messaget log(message_handler);
    log.warning() << "parse_invariant_string: cannot parse \"" << expr_str
                  << "\"" << messaget::eom;
    return std::nullopt;
  }

  // Substitute base-name symbol_exprt nodes with the real ones.
  std::function<void(exprt &)> substitute = [&](exprt &e) {
    if(e.id() == ID_symbol)
    {
      auto it = base_to_real.find(to_symbol_expr(e).get_identifier());
      if(it != base_to_real.end())
        e = it->second;
      return;
    }
    for(auto &op : e.operands())
      substitute(op);
  };
  substitute(expr);

  return expr;
}
