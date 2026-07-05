
// A position in a term. 
// These are needed, so that one can specify where to expand
// definitions, and the proof editor keeps a set of 
// unfinished points. Currently not used.

#ifndef LOGIC_POSITION_
#define LOGIC_POSITION_   

#include <vector>
#include <compare>
#include "util/print.h"

namespace logic
{
   // Is it an object or value?
   // We chose for object, so that it can be analogous
   // to context and localnamestack.

   class position
   {
      std::vector< unsigned int > vect;
 
   public:  
      position( ) = default;

      void extend( unsigned int p );
      void restore( size_t s );

      size_t firstdifference( const position& other ) const;
         // Finds the index of the first difference with pos. 
         // If there is no difference, it will be the size
         // of the smaller.

      void print( std::ostream& out ) const;  

      unsigned int operator[] ( size_t i ) const { return vect. at(i); }

      size_t size( ) const { return vect. size( ); }

   };

   std::strong_ordering 
   operator <=> ( const position& pos1, const position& pos2 ); 

   inline bool operator < ( const position& pos1, const position& pos2 )
   {
      return is_lt( pos1 <=> pos2 );
   }

   inline bool operator == ( const position& pos1, const position& pos2 )
   {
      return is_eq( pos1 <=> pos2 );
   }

}

#endif

