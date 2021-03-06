/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "std_code.h"

#include "std_expr.h"

const irep_idt &code_declt::get_identifier() const
{
  return to_symbol_expr(symbol()).get_identifier();
}

const irep_idt &code_deadt::get_identifier() const
{
  return to_symbol_expr(symbol()).get_identifier();
}

code_blockt &codet::make_block()
{
  if(get_statement()==ID_block)
    return static_cast<code_blockt &>(*this);

  exprt tmp;
  tmp.swap(*this);

  *this = codet(ID_block);
  move_to_operands(tmp);

  return static_cast<code_blockt &>(*this);
}

codet &codet::first_statement()
{
  const irep_idt &statement=get_statement();

  if(has_operands())
  {
    if(statement==ID_block)
      return to_code(op0()).first_statement();
    else if(statement==ID_label)
      return to_code(op0()).first_statement();
  }

  return *this;
}

const codet &codet::first_statement() const
{
  const irep_idt &statement=get_statement();

  if(has_operands())
  {
    if(statement==ID_block)
      return to_code(op0()).first_statement();
    else if(statement==ID_label)
      return to_code(op0()).first_statement();
  }

  return *this;
}

codet &codet::last_statement()
{
  const irep_idt &statement=get_statement();

  if(has_operands())
  {
    if(statement==ID_block)
      return to_code(operands().back()).last_statement();
    else if(statement==ID_label)
      return to_code(operands().back()).last_statement();
  }

  return *this;
}

const codet &codet::last_statement() const
{
  const irep_idt &statement=get_statement();

  if(has_operands())
  {
    if(statement==ID_block)
      return to_code(operands().back()).last_statement();
    else if(statement==ID_label)
      return to_code(operands().back()).last_statement();
  }

  return *this;
}

/// Add all the codets from extra_block to the current code_blockt
/// \param extra_block: The input code_blockt
void code_blockt::append(const code_blockt &extra_block)
{
  operands().reserve(operands().size()+extra_block.operands().size());

  for(const auto &operand : extra_block.operands())
  {
    add(to_code(operand));
  }
}

code_blockt create_fatal_assertion(
  const exprt &condition, const source_locationt &loc)
{
  code_blockt result;
  result.copy_to_operands(code_assertt(condition));
  result.copy_to_operands(code_assumet(condition));
  for(auto &op : result.operands())
    op.add_source_location() = loc;
  result.add_source_location() = loc;
  return result;
}

side_effect_exprt::side_effect_exprt(
  const irep_idt &statement,
  const typet &_type,
  const source_locationt &loc)
  : exprt(ID_side_effect, _type)
{
  set_statement(statement);
  add_source_location() = loc;
}

side_effect_expr_nondett::side_effect_expr_nondett(
  const typet &_type,
  const source_locationt &loc)
  : side_effect_exprt(ID_nondet, _type, loc)
{
  set_nullable(true);
}

side_effect_expr_function_callt::side_effect_expr_function_callt(
  const exprt &_function,
  const exprt::operandst &_arguments,
  const typet &_type,
  const source_locationt &loc)
  : side_effect_exprt(ID_function_call, _type, loc)
{
  operands().resize(2);
  op1().id(ID_arguments);
  function() = _function;
  arguments() = _arguments;
}
