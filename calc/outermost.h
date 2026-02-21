
// Written by Hans de Nivelle, November 2025.

#ifndef CALC_OUTERMOST_
#define CALC_OUTERMOST_

#include "logic/outermost.h"
#include "propositional.h"
#include "quantifiers.h"

namespace calc
{

   // Each function has non-const and const versions.
   // That's why there are so many. 
 
   template< logic::replacement R, typename F >
   disjunction<F> 
   outermost( R& repl, disjunction<F> disj, size_t vardepth )
   {
      for( auto& f : disj )
         f = outermost( repl, std::move(f), vardepth );
      return disj;
   }

   template< logic::replacement R, typename F >
   disjunction<F> 
   outermost( const R& repl, disjunction<F> disj, size_t vardepth )
   {
      for( auto& f : disj )
         f = outermost( repl, std::move(f), vardepth );
      return disj;
   }


   template< logic::replacement R, typename F > 
   forall<F> outermost( R& repl, forall<F> all, size_t vardepth )
   {
      all. body = outermost( repl, std::move( all. body ), 
                             vardepth + all. vars. size( ));
      return all;
   }

   template< logic::replacement R, typename F >
   forall<F> outermost( const R& repl, forall<F> all, size_t vardepth )
   {
      all. body = outermost( repl, std::move( all. body ),
                             vardepth + all. vars. size( ));
      return all;
   }


   template< logic::replacement R, typename F > 
   exists<F> 
   outermost( R& repl, exists<F> ex, size_t vardepth )
   {
      ex. body = outermost( repl, std::move( ex. body ),
                            vardepth + ex. vars. size( )); 
      return ex;
   }

   template< logic::replacement R, typename F >
   exists<F>
   outermost( const R& repl, exists<F> ex, size_t vardepth )
   {
      ex. body = outermost( repl, std::move( ex. body ),
                            vardepth + ex. vars. size( ));
      return ex;
   }
 
}

#endif

