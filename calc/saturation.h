
// Written by Hans de Nivelle, March 2026.

#ifndef CALC_SATURATION_
#define CALC_SATURATION_

#include <iostream>
#include <cstdint>
#include <list>
#include <optional>

#include "logic/term.h"
#include "normalforms.h"
#include "disjunction_map.h"

namespace calc
{

   struct saturation
   {
      using littype = truthform< exists< logic::term >> ;

      struct clause
      {
         disjunction_map< exists< logic::term >> disj;
         uint64_t nr;
         std::optional< size_t > seqind;  // Index in sequent, if initial.

         clause( uint64_t nr )
            : nr( nr )
         { }

         clause( uint64_t nr, size_t seqind )
            : nr( nr ),
              seqind( seqind )
         { }

         void print( std::ostream& out ) const; 
      };
      
      uint64_t notsaturated = 0;
      uint64_t notsubsumed = 0;
      uint64_t notnormalized = 0;
      uint64_t notcreated = 0;

      std::list< clause > clauses;

      std::unordered_set< size_t > removed;
         // Indices of subsumed initial clauses. They can be
         // made hidden in the sequent later.

      saturation( ) noexcept = default;

      void initial( dnf< logic::term > disj, size_t index );
         // Add an initial clause. It will be lifted over liftdist,
         // and its index will be index.

      littype makeliteral( const exists< logic::term > & lit );

      static void direct( littype& lit ); 
         // Direct equalities from bigger to smaller using KBO.
         // If the equality has form t == t, modify the truth set,
         // in order to make triviality obvious.

      static void normalize( clause& cls );

      struct resolver
      {
         std::optional< littype > from; 
         uint64_t fld_used;

         resolver( const littype& from );  
         bool usable( ) const { return from. has_value( ); }
         littype operator( ) ( littype lit );
         uint64_t used( ) const { return fld_used; }
      };

      struct demodulator
      {
         std::optional< logic::rewriterule > rewr; 

         demodulator( const littype& lit );
         bool usable( ) const { return rewr. has_value( ); }
         littype operator( ) ( littype lit );
         uint64_t used( ) const { return rewr. value( ). used; }
      };

      void saturate( );

      bool simplify( const clause& from, clause& into ); 

      void print( std::ostream& out ) const; 
   };

}

#endif

