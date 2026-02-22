
#ifndef CALC_PREFIX_
#define CALC_PREFIX_

#include <iostream>

#include "logic/term.h"

namespace calc
{

   class prefix
   {
      uint8_t val;

      explicit prefix( uint8_t val ) 
         : val( val )
      { }

   public:
      static prefix F( ) { return prefix(4); }
      static prefix E( ) { return prefix(2); }
      static prefix T( ) { return prefix(1); }
      static prefix empty( ) { return prefix(0); }

      bool isempty( ) const { return val == 0; }

      bool subset( prefix p ) const
         { return ! ( val & ~p. val ); }

      prefix& operator |= ( const prefix& p ) 
         { val |= p. val; return *this; }

      prefix& operator &= ( const prefix& p ) 
         { val &= p. val; return *this; }

      prefix operator ~ ( ) const
         { return prefix( 7 ^ val ); }
        
      void print( std::ostream& out ) const;
   };

   inline prefix operator & ( prefix p1, prefix p2 ) 
      { return p1 &= p2; }

   inline prefix operator | ( prefix p1, prefix p2 ) 
      { return p1 |= p2; }
 
   inline std::ostream& operator << ( std::ostream& out, prefix p )
   {
      p. print( out );
      return out;
   }
}

#endif

