
// Written by Hans de Nivelle, March 2026.

#ifndef CALC_ATP_
#define CALC_ATP_

#include <iostream>

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


   struct proofstate 
   {
      using clause = 
         disjunction_map< exists< logic::term >, exists_equal_to > ;

      // The clause sets are called after what has been done with them.
     
      std::vector< std::pair< clause, size_t >> saturated;
      std::vector< std::pair< clause, size_t >> simplified;
      std::vector< std::pair< clause, size_t >> nothing;
      std::unordered_set< size_t > removed;
         // Indices of subsumed initial clauses. They can be
         // made hidden in the sequent later.

      void initial( dnf< logic::term > d, size_t ind );
         // Add an initial clause to nothing if it has the right form,
         // and is not subsumed. 
 
#if 0
      void simplify( clause& cls );
         // Remove redundant literals, and direct equalities using
         // KBO.
 
      bool subsumes( const literal& lit, const clause& cls,
                     clause::const_iterator skip );

      bool subsumes( const clause& cls1, clause::const_iterator skip1,
                     const clause& cls2, clause::const_iterator skip2 );

         // True if cls1 \ skip1 is a subset of cls2 \ skip2.
         // If you want the full clause, use end( ).

      // True if it happened:
 
      bool rewrite( const clause& from, clause& into );
      bool resolve( const clause& from, clause& into );

      void simplify( conjunction< clause > & simp );
         // This is the main function that should be called. 
#endif

   };

}

#endif

