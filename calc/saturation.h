
// Written by Hans de Nivelle, March 2026.

#ifndef CALC_SATURATION_
#define CALC_SATURATION_

#include <iostream>
#include <limits>
#include <list>

#include "logic/term.h"
#include "normalforms.h"
#include "disjunction_map.h"

namespace calc
{

   struct exists_equal_to
   {
      exists_equal_to( ) noexcept = default;

      bool operator( ) ( logic::term& t1, logic::term& t2 ) const;
   };


   struct saturation
   {
      using clause = 
         disjunction_map< exists< logic::term >, exists_equal_to > ;
  
      constexpr static size_t 
         notinsequent = std::numeric_limits< size_t > :: max( );

      // The clause sets are called after what has been done with them.
      // list makes deletion easier.
 
      std::list< std::pair< clause, size_t >> saturated;
      std::list< std::pair< clause, size_t >> simplified;
      std::list< std::pair< clause, size_t >> raw;
      std::unordered_set< size_t > removed;
         // Indices of subsumed initial clauses. They can be
         // made hidden in the sequent later.

      saturation( ) noexcept = default;

      void insert( dnf< logic::term > d, size_t ind );
         // Add an initial clause to nothing if it has the right form,
         // and is not subsumed. 

      static 
      void direct( std::pair< exists< logic::term >, truthset > & lit ); 
         // Direct equalities from bigger to smaller using KBO.
         // If the equality has form t == t, modify the truth set,
         // to make triviality obvious.

      static void equalities( clause& cls );
         // Direct equalities, and
         // remove negative equalities of form ( t = t ) -> F.
         // Replace ( A -> S1 ), ( A -> S2 ) by ( A -> S1|S2 ).
 
#if 0
      // True if it happened:
 
      bool rewrite( const clause& from, clause& into );
      bool resolve( const clause& from, clause& into );

      void simplify( conjunction< clause > & simp );
         // This is the main function that should be called. 
#endif

      void print( std::ostream& out ) const; 
   };

}

#endif

