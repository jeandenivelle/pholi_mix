
#ifndef CALC_LITERAL_VIEW_
#define CALC_LITERAL_VIEW_

#include <iostream>

#include "logic/term.h"

namespace calc
{

   // We are a VIEW, which means that we do not own
   // the terms.

   template< typename F, typename E = std::equal_to<F>> 
   class disjunction_view 
   {
      enum truthset { ffff = 1, eeee = 2, tttt = 4 };

      std::vector< std::pair< F, uint8_t >> disj;

      const logic::term* body;
      truthset truth;

      disjunction_view( ) noexcept = default;

   public:

      bool isempty( ) const { return disj. size( ) == 0; }

#if 0
      bool subset( prefix p ) const
         { return ! ( val & ~p. val ); }

      prefix& operator |= ( const prefix& p ) 
         { val |= p. val; return *this; }

      prefix& operator &= ( const prefix& p ) 
         { val &= p. val; return *this; }

      prefix operator ~ ( ) const
         { return prefix( 7 ^ val ); }
        
      void print( std::ostream& out ) const;
#endif 
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

