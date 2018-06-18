/*******************************************************************\

Module: Expand pointer predicates in assertions/assumptions.

Author: Klaas Pruiksma

Date: June 2018

\*******************************************************************/

/// \file
/// Replace pointer predicates (e.g. __CPROVER_points_to_valid_memory)
/// in assumptions and assertions with suitable expressions and additional
/// instructions.

#include "expand_pointer_predicates.h"

#include <util/expr_iterator.h>
#include <util/fresh_symbol.h>
#include <util/namespace.h>
#include <util/pointer_predicates.h>

#include <goto-programs/goto_model.h>

#include <iostream>

class expand_pointer_predicatest
{
public:
  expand_pointer_predicatest(
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions):
      ns(_symbol_table),
      symbol_table(_symbol_table),
      goto_functions(_goto_functions)
  {
  }

  void operator()();

protected:
  namespacet ns;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;

  void expand_pointer_predicates();

  exprt expand_assumption(
    goto_programt &program,
    goto_programt::targett target,
    exprt &assume_expr);

  exprt expand_assertion(exprt &assert_expr);

  const symbolt &new_tmp_symbol(
    const typet &type,
    const source_locationt &source_location);
};

bool is_lvalue(const exprt &expr);

void expand_pointer_predicatest::expand_pointer_predicates()
{
  Forall_goto_functions(f_it, goto_functions)
  {
    goto_functionst::goto_functiont &goto_function = f_it->second;
    Forall_goto_program_instructions(i_it, goto_function.body)
    {
      if(i_it->is_assert())
      {
        exprt assert_expr = expand_assertion(i_it->guard);
        i_it->guard = assert_expr;
      }
      else if(i_it->is_assume())
      {
        exprt assume_expr = expand_assumption(
          goto_function.body,
          i_it,
          i_it->guard);
        i_it->guard = assume_expr;
      }
      else
      {
        continue;
      }
    }
  }
}

exprt expand_pointer_predicatest::expand_assumption(
  goto_programt &program,
  goto_programt::targett target,
  exprt &assume_expr)
{
  goto_programt assume_code;
  exprt assume_copy(assume_expr);
  for(depth_iteratort it=assume_copy.depth_begin();
      it != assume_copy.depth_end();)
  {
    if(it->id() == ID_valid_pointer)
    {
      exprt &valid_pointer_expr = it.mutate();
      exprt &pointer_expr = valid_pointer_expr.op0();
     
      // This should be forced by typechecking. 
      INVARIANT(pointer_expr.type().id() == ID_pointer &&
                  is_lvalue(pointer_expr),
                "Invalid argument to valid_pointer.");
      typet &base_type = pointer_expr.type().subtype();
      
      // Decl a new variable (which is therefore unconstrained)
      goto_programt::targett d = assume_code.add_instruction(DECL);
      d->function = target->function;
      d->source_location = assume_expr.source_location();
      symbol_exprt obj =
        new_tmp_symbol(base_type, d->source_location).symbol_expr();
      d->code=code_declt(obj);

      address_of_exprt rhs(obj, to_pointer_type(pointer_expr.type()));

      // Point the relevant pointer to the new object
      goto_programt::targett a = assume_code.add_instruction(ASSIGN);
      a->function = target->function;
      a->source_location = assume_expr.source_location();
      a->code = code_assignt(pointer_expr, rhs);
      a->code.add_source_location() = assume_expr.source_location();

      // Because some uses of this occur before deallocated, dead, and malloc
      // objects are initialized, we need to make some additional assumptions
      // to clarify that our newly allocated object is not dead, deallocated,
      // or outside the bounds of a malloc region.
      
      exprt check_expr = valid_pointer_assume_def(pointer_expr, ns);
      valid_pointer_expr.swap(check_expr);
      it.next_sibling_or_parent();
    }
    else {
      ++it;
    }
  }

  program.destructive_insert(target, assume_code);

  return assume_copy;
}

exprt expand_pointer_predicatest::expand_assertion(exprt &assert_expr)
{
  exprt assert_copy(assert_expr);
  for(depth_iteratort it = assert_copy.depth_begin();
      it != assert_copy.depth_end();)
  {
    if(it->id() == ID_valid_pointer)
    {
      // Build an expression that checks validity.
      exprt &valid_pointer_expr = it.mutate();
      exprt &pointer_expr = valid_pointer_expr.op0();

      exprt check_expr = valid_pointer_assert_def(pointer_expr, ns);
      valid_pointer_expr.swap(check_expr);
      it.next_sibling_or_parent();
    }
    else
    {
      ++it;
    }
  }

  return assert_copy;
}

const symbolt &expand_pointer_predicatest::new_tmp_symbol(
  const typet &type,
  const source_locationt &source_location)
{
  return get_fresh_aux_symbol(
    type,
    id2string(source_location.get_function()),
    "tmp_cc",
    source_location,
    irep_idt(),
    symbol_table);
}

void expand_pointer_predicatest::operator()()
{
  expand_pointer_predicates();
}

void expand_pointer_predicates(goto_modelt &goto_model)
{
  expand_pointer_predicatest(goto_model.symbol_table,
                             goto_model.goto_functions)();
}
