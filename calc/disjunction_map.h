
#ifndef CALC_DISJUNCTION_MAP_
#define CALC_DISJUNCTION_MAP_

#include <iostream>
#include <vector>

#include "truthset.h"

// We finally understood that a clause is not a set of literals.
// It is a mapping from atoms to sets of truth values.
// We represent the truth values by bits, and sets of truth values
// by their bitwise ors.

namespace calc
{

   template< typename F, typename E = std::equal_to<F>> 
   class disjunction_map
   {
      std::vector< std::pair< F, truthset >> map;

      F f;
      E eq;

   public:
      disjunction_map( ) noexcept = default;

      bool isempty( ) const { return map. empty( ); }
      size_t size( ) const { return map. size( ); }

      void append( F f, truthset s = tttt ) 
         { map. push_back( std::pair( std::move(f), s )); }

      void print( std::ostream& out ) const
      {
         out << "Disjunction Map:\n";
         for( auto& p : map )
            out << p. first << " -> " << p. second << "\n";
      }

   };
#if 0
   inline prefix operator & ( prefix p1, prefix p2 ) 
      { return p1 &= p2; }

   inline prefix operator | ( prefix p1, prefix p2 ) 
      { return p1 |= p2; }
 
   inline std::ostream& operator << ( std::ostream& out, prefix p )
   {
      p. print( out );
      return out;
   }
#endif

}

#endif

