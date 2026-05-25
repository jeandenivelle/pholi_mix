
// Written by Hans de Nivelle, May 2026.

#ifndef CALC_WEIGHTS_
#define CALC_WEIGHTS_

#include "logic/cmp.h"
#include "quantifiers.h"
#include "propositional.h"

namespace calc
{

   using weight_type = logic::weight_type;

   template< typename F >
   weight_type weight( const forall<F> & all )
   {
      weight_type res = 1;
      res += all. vars. size( );
      res += weight( all. body );
      return res;
   }

   template< typename F >
   weight_type weight( const exists<F> & ex )
   {
      weight_type res = 1;
      res += ex. vars. size( );
      res += weight( ex. body );
      return res;
   }

   template< typename F >
   weight_type weight( const disjunction<F> & disj )
   {
      weight_type res = 1;
      for( const auto& d : disj )
         res += weight(d);
       return res;
   }

   template< typename F >
   weight_type weight( const conjunction<F> & conj )
   {
      weight_type res = 1;
      for( const auto& c : conj )
         res += weight(c);
       return res;
   }

}

#endif

