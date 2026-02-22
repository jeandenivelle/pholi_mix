
// Helper functions that make it easy to construct terms
// in code. Probably, all of these functions can go away
// when we have a good (even a temporary) parser with which 
// the test cases can be entered. 

#ifndef LOGIC_TERMOPERATORS_ 
#define LOGIC_TERMOPERATORS_  

#include "term.h"

namespace logic
{

   inline term prop( const term& t ) 
      { return term( op_prop, t ); }

   inline term operator ! ( const term& t ) 
      { return term( op_not, t ); }

   inline term operator || ( const term& t1, const term& t2 ) 
      { return term( op_or, t1, t2 ); }

   inline term operator && ( const term& t1, const term& t2 )
      { return term( op_and, t1, t2 ); }

   inline term lazy_and( const term& t1, const term& t2 )
      { return term( op_lazy_and, t1, t2 ); }

   inline term implies( const term& t1, const term& t2 )
      { return term( op_implies, t1, t2 ); }

   inline term lazy_implies( const term& t1, const term& t2 )
      { return term( op_lazy_implies, t1, t2 ); }

   inline term equiv( const term& t1, const term& t2 )
      { return term( op_equiv, t1, t2 ); }

   inline term operator == ( const term& t1, const term& t2 )
      { return term( op_equals, t1, t2 ); }

   inline term operator != ( const term& t1, const term& t2 )
      { return ! ( t1 == t2 ); }

   inline term forall( std::initializer_list< vartype > vars, const term& t )
      { return term( op_forall, t, vars ); }

   inline term exists( std::initializer_list< vartype > vars, const term& t )
      { return term( op_exists, t, vars ); }

   inline term apply( const term& f, std::initializer_list< term > args )
      { return term( op_apply, f, args ); }

   inline term lambda( std::initializer_list< vartype > vars, const term& t )
      { return term( op_lambda, t, vars ); }

   inline term let( const vartype& var, const term& val, const term& body )
      { return term( op_let, var, val, body ); }

}


inline logic::term operator "" _db( long long unsigned int i )
   { return logic::term( logic::op_debruijn, i ); }

inline logic::term operator "" _unchecked( const char* c, size_t len )
   { return logic::term( logic::op_unchecked, identifier() + c ); }

#endif 

