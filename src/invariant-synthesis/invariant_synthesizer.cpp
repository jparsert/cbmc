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

#include <goto-programs/goto_functions.h>

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
  // Supported syntax: "<lhs> <op> <rhs>"
  // where op is one of: <=, >=, <, >, ==, !=
  // and each side is either a variable name or an integer literal.
  static const std::array<std::pair<std::string, irep_idt>, 6> ops = {{
    {"<=", ID_le}, {">=", ID_ge}, {"!=", ID_notequal},
    {"<",  ID_lt}, {">",  ID_gt}, {"==", ID_equal},
  }};

  const auto vars = collect_loop_variables(goto_model, loop_id);

  // Build a map from bare name to exprt.
  std::map<std::string, exprt> var_map;
  for(const auto &v : vars)
  {
    const std::string full = id2string(v.get_identifier());
    const auto pos = full.rfind("::");
    var_map[pos == std::string::npos ? full : full.substr(pos + 2)] = v;
  }

  auto trim = [](const std::string &s) {
    const auto a = s.find_first_not_of(' ');
    const auto b = s.find_last_not_of(' ');
    return a == std::string::npos ? std::string{} : s.substr(a, b - a + 1);
  };

  // Resolve a token to an exprt: variable or integer literal.
  auto resolve = [&](const std::string &tok,
                     const typet &hint) -> std::optional<exprt>
  {
    const std::string t = trim(tok);
    if(t.empty())
      return std::nullopt;
    auto it = var_map.find(t);
    if(it != var_map.end())
      return it->second;
    try
    {
      const long long val = std::stoll(t);
      return from_integer(
        val,
        hint.id() == ID_signedbv || hint.id() == ID_unsignedbv
          ? hint
          : signed_int_type());
    }
    catch(...) { return std::nullopt; }
  };

  // Forward declaration for recursion.
  std::function<std::optional<exprt>(const std::string &)> parse_expr;

  // Parse a single comparison atom.
  auto parse_atom = [&](const std::string &s) -> std::optional<exprt>
  {
    for(const auto &[op_str, op_id] : ops)
    {
      const auto pos = s.find(op_str);
      if(pos == std::string::npos)
        continue;
      const std::string lhs_tok = s.substr(0, pos);
      const std::string rhs_tok = s.substr(pos + op_str.size());
      auto lhs = resolve(lhs_tok, signed_int_type());
      auto rhs = resolve(rhs_tok, lhs ? lhs->type() : signed_int_type());
      if(!lhs || !rhs)
        continue;
      lhs = resolve(lhs_tok, rhs->type());
      if(!lhs)
        continue;
      exprt l = *lhs, r = *rhs;
      if(l.type() != r.type())
      {
        if(r.type().id() == ID_signedbv || r.type().id() == ID_unsignedbv)
          l = typecast_exprt(l, r.type());
        else
          r = typecast_exprt(r, l.type());
      }
      return binary_relation_exprt(l, op_id, r);
    }
    return std::nullopt;
  };

  // Find the last occurrence of `conn` outside any parentheses.
  // We use the last (rightmost) occurrence so that left-associativity is
  // preserved when the same connective appears multiple times.
  auto find_connective = [](const std::string &s,
                            const std::string &conn) -> std::size_t
  {
    int depth = 0;
    std::size_t found = std::string::npos;
    for(std::size_t i = 0; i + conn.size() <= s.size(); ++i)
    {
      if(s[i] == '(') { ++depth; continue; }
      if(s[i] == ')') { --depth; continue; }
      if(depth == 0 && s.substr(i, conn.size()) == conn)
        found = i;
    }
    return found;
  };

  // Split on a logical connective (outside parens) and recurse.
  auto split_logical = [&](const std::string &s,
                           const std::string &conn,
                           irep_idt id) -> std::optional<exprt>
  {
    const auto pos = find_connective(s, conn);
    if(pos == std::string::npos)
      return std::nullopt;
    auto lhs = parse_expr(s.substr(0, pos));
    auto rhs = parse_expr(s.substr(pos + conn.size()));
    if(!lhs || !rhs)
      return std::nullopt;
    return binary_exprt(*lhs, id, *rhs, bool_typet{});
  };

  parse_expr = [&](const std::string &s) -> std::optional<exprt>
  {
    std::string t = trim(s);
    // Strip outer parentheses.
    while(t.size() >= 2 && t.front() == '(' && t.back() == ')')
    {
      // Make sure the opening paren actually closes at the end.
      int depth = 0;
      bool matched = true;
      for(std::size_t i = 0; i < t.size() - 1; ++i)
      {
        if(t[i] == '(') ++depth;
        else if(t[i] == ')') { --depth; if(depth == 0) { matched = false; break; } }
      }
      if(!matched) break;
      t = trim(t.substr(1, t.size() - 2));
    }
    // || has lowest precedence, then &&, then atoms.
    if(auto r = split_logical(t, "||", ID_or))
      return r;
    if(auto r = split_logical(t, "&&", ID_and))
      return r;
    return parse_atom(t);
  };

  auto result = parse_expr(expr_str);
  if(!result)
  {
    messaget log(message_handler);
    log.warning() << "parse_invariant_string: cannot parse \"" << expr_str
                  << "\"" << messaget::eom;
  }
  return result;
}
