
// Written by Hans de Nivelle, December 2024.

#ifndef LOGIC_EXACT_
#define LOGIC_EXACT_

#include <unordered_set>
#include <unordered_map>
#include <compare>

#include "util/print.h"

namespace logic 
{ 
   struct exact
   {
      size_t nr;

      exact( ) = delete; 
      explicit exact( size_t nr )
         : nr( nr ) 
      { }

      void print( std::ostream& out ) const
         { out << '$' << nr; } 

      struct equal_to
      {
         equal_to( ) = default;
         bool operator( ) ( exact e1, exact e2 ) const
            { return e1. nr == e2. nr; }
      };

      struct hash 
      {
         hash( ) = default;
         size_t operator( ) ( const exact e ) const
            { return e. nr; }
      };

      using unordered_set =
      std::unordered_set< exact, exact::hash, exact::equal_to > ;

      template< typename V > using unordered_map = 
      std::unordered_map< exact, V, exact::hash, exact::equal_to > ;

   };

   // exact must be an ordered type, because of KBO.
   // We assume that e1 < e2 if e1 was defined before e2,
   // which is a natural order I think. 

   inline std::strong_ordering operator <=> ( exact e1, exact e2 ) 
      { return ( e1. nr <=> e2. nr ); }

   inline bool operator == ( exact e1, exact e2 )
      { return is_eq( e1 <=> e2 ); }

   inline bool operator != ( exact e1, exact e2 )
      { return is_neq( e1 <=> e2 ); }

}

#endif

