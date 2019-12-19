#include <SWI-Stream.h>
#include <SWI-Prolog.h>
#include <stdio.h>
#include <assert.h>

#include "Solver.h"

namespace Glucose {

#define val(i) ((s->model[i] != l_Undef) ? ((s->model[i]==l_True)? i+1:-1*(i+1)):0)

Solver      *s = NULL;
int         seed=0;

vec<Solver*> cache_slvrs;

extern "C" foreign_t minisat_default_seed(term_t pl_seed)
{
  PL_get_integer(pl_seed,&seed);
  PL_succeed;
}

extern "C" foreign_t minisat_new_solver()
{
  if (s) {
    Sdprintf("%% Warning: minisat_new_solver deleted existing solver !\n");
    delete s;
    s = NULL;
  }
  s = new Solver;
  if (seed != 0) {
    s->random_seed = seed;
  }
  PL_succeed;
}

extern "C" foreign_t minisat_delete_solver()
{
    if (s) {
      delete s;
      s = NULL;
    } else {
      Sdprintf("%% Warning: minisat_delete_solver didn't had a solver to delete !\n");
    }
    PL_succeed;
}

extern "C" foreign_t minisat_cache_push_solver()
{
  if (s) {
    cache_slvrs.push(s);
    s = NULL;
    PL_succeed;
  } else {
    Sdprintf("%% Error: minisat_cache_push_solver failed since no active SAT solver !\n");
    PL_fail;
  }
}

extern "C" foreign_t minisat_cache_pop_solver()
{
  if (cache_slvrs.size() == 0) {
    Sdprintf("%% Error: minisat_cache_pop_solver failed since no cached SAT solver !\n");
    PL_fail;
  }

  if (s) {
    Sdprintf("%% Warning: minisat_cache_pop_solver deleted existing solver !\n");
    delete s;
    s = NULL;
  }
  s = cache_slvrs.last();
  cache_slvrs.pop();
  PL_succeed;
}

static inline Lit pl2lit(term_t pl_literal)
{
  int pl_lit_int, var;
  PL_get_integer(pl_literal,&pl_lit_int);
  var = abs(pl_lit_int)-1;
  while (var >= s->nVars()) s->newVar();
  return mkLit(var,!(pl_lit_int > 0));
}


extern "C" foreign_t minisat_add_clause(term_t l)
{
    term_t head = PL_new_term_ref();      /* variable for the elements */
    term_t list = PL_copy_term_ref(l);    /* copy as we need to write */
    
    vec<Lit> lits;

    while( PL_get_list(list, head, list) ) {
      lits.push( pl2lit(head) );
    }

    assert(PL_get_nil(list));
    
    if (s->addClause(lits)) PL_succeed; else PL_fail;
}


extern "C" foreign_t minisat_solve() {
    if (s->solve()) PL_succeed; else PL_fail;
}

extern "C" foreign_t minisat_solve_assumptions(term_t l) {
    term_t head = PL_new_term_ref();      /* variable for the elements */
    term_t list = PL_copy_term_ref(l);    /* copy as we need to write */
    
    vec<Lit> lits;

    while( PL_get_list(list, head, list) ) {
      lits.push( pl2lit(head) );
    }

    assert(PL_get_nil(list));

    if (s->solve(lits)) PL_succeed; else PL_fail;
}

extern "C" foreign_t minisat_get_var_assignment(term_t var, term_t res)
{
  int i;

  PL_get_integer(var,&i);
  i--;

  if (i < s->nVars()) {
    return PL_unify_integer(res,val(i));
  } else {
    PL_fail;
  }
}


extern "C" foreign_t minisat_get_model(term_t model)
{
    term_t l = PL_new_term_ref();
    term_t pl_lit = PL_new_term_ref();
    int pl_lit_int;
  
    PL_put_nil(l);

    int i=s->nVars();
    while( --i >= 0 ) {
      PL_put_integer(pl_lit,val(i));
      PL_cons_list(l, pl_lit, l);
    }

    return PL_unify(model,l);
}


extern "C" foreign_t minisat_assign_model(term_t asgnTo)
{
    term_t asgnList = PL_copy_term_ref(asgnTo);    /* copy as we need to write */
    term_t asgnVar = PL_new_term_ref();      /* variable for the elements */

	int indx=0;
	while( PL_get_list(asgnList, asgnVar, asgnList) ) {
		if(s->model[indx]==l_True) 
			PL_unify_integer(asgnVar,1);
		else
			PL_unify_integer(asgnVar,-1);
		indx++;
	}

    PL_succeed;
}


extern "C" foreign_t minisat_nvars(term_t res)
{
  return PL_unify_integer(res,s->nVars());
}

} // namespace



//=============================================================================
static const PL_extension predicates[] =
    {
        //
        //  { "name", arity, function, PL_FA_<flags> },
        //

      { "minisat_new_solver",         0, (pl_function_t)Glucose::minisat_new_solver,         0 },
      { "minisat_delete_solver",      0, (pl_function_t)Glucose::minisat_delete_solver,      0 },
      { "minisat_cache_push_solver",  0, (pl_function_t)Glucose::minisat_cache_push_solver,  0 },
      { "minisat_cache_pop_solver",   0, (pl_function_t)Glucose::minisat_cache_pop_solver,   0 },
      { "minisat_add_clause",         1, (pl_function_t)Glucose::minisat_add_clause,         0 },
      { "minisat_solve",              0, (pl_function_t)Glucose::minisat_solve,              0 },
      { "minisat_solve_assumptions",  1, (pl_function_t)Glucose::minisat_solve_assumptions,  0 },
      { "minisat_get_var_assignment", 2, (pl_function_t)Glucose::minisat_get_var_assignment, 0 },
      { "minisat_get_model",          1, (pl_function_t)Glucose::minisat_get_model,          0 },
      { "minisat_assign_model",       1, (pl_function_t)Glucose::minisat_assign_model,       0 },
      { "minisat_nvars",              1, (pl_function_t)Glucose::minisat_nvars,              0 },
      { "minisat_default_seed",       1, (pl_function_t)Glucose::minisat_default_seed,       0 },
      { NULL,                         0, NULL,                              0 }    // terminating line
    };

//-----------------------------------------------------------------------------
extern "C" install_t install()
{
    Sdprintf("%% SWI-Prolog interface to Glucose v2.2 ... ");
    PL_register_extensions(predicates);	/* This is the only PL_ call allowed */
					/* before PL_initialise().  It */
					/* ensures the foreign predicates */
					/* are available before loading */
					/* Prolog code */

    Sdprintf("OK\n");
}

//-----------------------------------------------------------------------------
// This part is for compiling into a standalone executable

#ifdef READLINE
static void install_readline(int argc, char**argv)
{
    PL_install_readline();
}
#endif

int main(int argc, char **argv)
{

#ifdef READLINE
    PL_initialise_hook(install_readline);
#endif

    install();
    if ( !PL_initialise(argc, argv) )
	PL_halt(1);
    
    PL_halt(PL_toplevel() ? 0 : 1);
    
    return 0;
}