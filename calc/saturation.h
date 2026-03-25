
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
         std::optional< size_t > seqind;  // Index in sequent, if initial.

         clause( ) = default;

         explicit clause( size_t seqind )
            : seqind( seqind )
         { }

         void print( std::ostream& out ) const; 
      };
      
      std::list< clause > checked;
      std::list< clause > unchecked; 
      std::list< clause > notnormalized; 

      std::unordered_set< size_t > removed;
         // Indices of removed initial clauses. They can be
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

      // A cheap equivalence relation:
 
      static bool 
      cheapequiv( const exists< logic::term > & lit1,
                  const exists< logic::term > & lit2 );
      
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

      std::list< clause > :: iterator pick( );
         // Picks a clause from unchecked.
         // unchecked must be non-empty.
     
      void saturate( );

      void print( std::ostream& out ) const; 
   };

}

#endif

