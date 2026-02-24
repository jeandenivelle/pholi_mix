
#ifndef NATDED_INTERPRETATION_
#define NATDED_INTERPRETATION_

// An interpretation is always propositional.
// Since we are only interpreting De Bruijn indices, 
// we behave like a stack.

#include <iostream>
#include <vector>

#include "truthval.h"

namespace natded
{

   struct interpretation
   {
      std::vector< truthval > values;

      interpretation( ) noexcept = default;

      size_t size( ) const { return values. size( ); }
      truthval gettruth( size_t index ) const
         { return values[ values. size( ) - index - 1 ]; }

      void append( truthval tv ) { values. push_back( tv ); }
      void restore( size_t ss );

      void print( std::ostream& out ) const; 
   };


}

#endif

