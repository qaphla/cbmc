/*******************************************************************\

Module: Interrupt Instrumentation

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Interrupt Instrumentation

#include "interrupt.h"

#include <linking/static_lifetime_init.h>

#ifdef LOCAL_MAY
#include <analyses/local_may_alias.h>
#endif

bool potential_race_on_read(
  const rw_set_baset &code_rw_set,
  const rw_set_baset &isr_rw_set)
{
  // R/W race?
  forall_rw_set_r_entries(e_it, code_rw_set)
  {
    if(isr_rw_set.has_w_entry(e_it->first))
      return true;
  }

  return false;
}

bool potential_race_on_write(
  const rw_set_baset &code_rw_set,
  const rw_set_baset &isr_rw_set)
{
  // W/R or W/W?
  forall_rw_set_w_entries(e_it, code_rw_set)
  {
    if(isr_rw_set.has_r_entry(e_it->first))
      return true;

    if(isr_rw_set.has_w_entry(e_it->first))
      return true;
  }

  return false;
}

void interrupt(
  value_setst &value_sets,
  const symbol_tablet &symbol_table,
#ifdef LOCAL_MAY
  const goto_functionst::goto_functiont &goto_function,
#endif
  goto_programt &goto_program,
  const symbol_exprt &interrupt_handler,
  const rw_set_baset &isr_rw_set)
{
  namespacet ns(symbol_table);

  Forall_goto_program_instructions(i_it, goto_program)
  {
    goto_programt::instructiont &instruction=*i_it;

#ifdef LOCAL_MAY
  local_may_aliast local_may(goto_function);
#endif
    rw_set_loct rw_set(ns, value_sets, i_it
#ifdef LOCAL_MAY
      , local_may
#endif
    ); // NOLINT(whitespace/parens)

    // potential race?
    bool race_on_read=potential_race_on_read(rw_set, isr_rw_set);
    bool race_on_write=potential_race_on_write(rw_set, isr_rw_set);

    if(!race_on_read && !race_on_write)
      continue;

    // Insert the call to the ISR.
    // We do before for races on Read, and before and after
    // for races on Write.

    if(race_on_read || race_on_write)
    {
      goto_programt::instructiont original_instruction;
      original_instruction.swap(instruction);

      const source_locationt &source_location=
        original_instruction.source_location;

      code_function_callt isr_call;
      isr_call.add_source_location()=source_location;
      isr_call.function()=interrupt_handler;

      goto_programt::targett t_goto=i_it;
      goto_programt::targett t_call=goto_program.insert_after(t_goto);
      goto_programt::targett t_orig=goto_program.insert_after(t_call);

      t_goto->make_goto(t_orig);
      t_goto->source_location=source_location;
      t_goto->guard = side_effect_expr_nondett(bool_typet(), source_location);
      t_goto->function=original_instruction.function;

      t_call->make_function_call(isr_call);
      t_call->source_location=source_location;
      t_call->function=original_instruction.function;

      t_orig->swap(original_instruction);

      i_it=t_orig; // the for loop already counts us up
    }

    if(race_on_write)
    {
      // insert _after_ the instruction with race
      goto_programt::targett t_orig=i_it;
      t_orig++;

      goto_programt::targett t_goto=goto_program.insert_after(i_it);
      goto_programt::targett t_call=goto_program.insert_after(t_goto);

      const source_locationt &source_location=i_it->source_location;

      code_function_callt isr_call;
      isr_call.add_source_location()=source_location;
      isr_call.function()=interrupt_handler;

      t_goto->make_goto(t_orig);
      t_goto->source_location=source_location;
      t_goto->guard = side_effect_expr_nondett(bool_typet(), source_location);
      t_goto->function=i_it->function;

      t_call->make_function_call(isr_call);
      t_call->source_location=source_location;
      t_call->function=i_it->function;

      i_it=t_call; // the for loop already counts us up
    }
  }
}

symbol_exprt get_isr(
  const symbol_tablet &symbol_table,
  const irep_idt &interrupt_handler)
{
  std::list<symbol_exprt> matches;

  forall_symbol_base_map(m_it, symbol_table.symbol_base_map, interrupt_handler)
  {
    // look it up
    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(m_it->second);

    if(s_it==symbol_table.symbols.end())
      continue;

    if(s_it->second.type.id()==ID_code)
      matches.push_back(s_it->second.symbol_expr());
  }

  if(matches.empty())
    throw "interrupt handler `"+id2string(interrupt_handler)+"' not found";

  if(matches.size()>=2)
    throw "interrupt handler `"+id2string(interrupt_handler)+"' is ambiguous";

  symbol_exprt isr=matches.front();

  if(!to_code_type(isr.type()).parameters().empty())
    throw "interrupt handler `"+id2string(interrupt_handler)+
          "' must not have parameters";

  return isr;
}

void interrupt(
  value_setst &value_sets,
  goto_modelt &goto_model,
  const irep_idt &interrupt_handler)
{
  // look up the ISR
  symbol_exprt isr=
    get_isr(goto_model.symbol_table, interrupt_handler);

  // we first figure out which objects are read/written by the ISR
  rw_set_functiont isr_rw_set(
    value_sets, goto_model, isr);

  // now instrument

  Forall_goto_functions(f_it, goto_model.goto_functions)
    if(f_it->first != INITIALIZE_FUNCTION &&
       f_it->first!=goto_functionst::entry_point() &&
       f_it->first!=isr.get_identifier())
      interrupt(
        value_sets, goto_model.symbol_table,
#ifdef LOCAL_MAY
        f_it->second,
#endif
        f_it->second.body, isr, isr_rw_set);

  goto_model.goto_functions.update();
}
