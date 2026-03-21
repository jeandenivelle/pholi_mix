
// Written by Hans de Nivelle, March 2026.

#ifndef CALC_SATURATION_
#define CALC_SATURATION_

#include <iostream>
#include <limits>
#include <list>
#include <optional>

#include "logic/term.h"
#include "normalforms.h"
#include "disjunction_map.h"

namespace calc
{

   struct exists_equal_to
   {
      exists_equal_to( ) noexcept = default;

      bool operator( ) ( const exists< logic::term > & lit1, 
                         const exists< logic::term > & lit2  ) const;
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

      void insert( dnf< logic::term > disj, size_t ind );
         // Add dnf to raw if it has the right form
         // if it is not subsumed.

      static 
      void direct( std::pair< exists< logic::term >, truthset > & lit ); 
         // Direct equalities from bigger to smaller using KBO.
         // If the equality has form t == t, modify the truth set,
         // to make triviality obvious.

      static void equalities( clause& cls );
         // Direct equalities, and
         // remove negative equalities of form ( t = t ) -> F.
         // Replace ( A -> S1 ), ( A -> S2 ) by ( A -> S1|S2 ).

      struct demodulator
      {
         uint64_t used;
         std::optional< logic::rewriterule > rewr; 

         demodulator( const std::pair< exists< logic::term >, truthset > & lit );

         bool usable( ) const { return rewr. has_value( ); }
         std::pair< exists< logic::term >, truthset >
         operator( ) 
             ( std::pair< exists< logic::term >, truthset > lit );
      };
 
#if 0
      // True if it happened:
 
      bool resolve( const clause& from, clause& into );

      void y( conjunction< clause > & simp );
         // This is the main function that should be called. 
#endif

      void print( std::ostream& out ) const; 
   };

   bool 
   ressimp( const saturation::clause& from, saturation::clause& into );
      // From should not be identical to into. 
}

#endif

