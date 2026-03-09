
#ifndef CALC_TRUTHSET_
#define CALC_TRUTHSET_

#include <iostream>
#include <vector>

// We finally understood that a clause is not a set of literals.
// It is a mapping from atoms to sets of truth values.
// We represent the truth values by bits, and sets of truth values
// by their bitwise ors.

namespace calc
{

   enum truthset { empty = 0,
                   ffff = 1, eeee = 2, tttt = 4, 
                   ffee = 3, fftt = 5, eett = 6,
                   all = 7 };

   const char* getcstring( truthset );

#if 0
      bool subset( prefix p ) const
         { return ! ( val & ~p. val ); }

      prefix& operator |= ( const prefix& p ) 
         { val |= p. val; return *this; }

      prefix& operator &= ( const prefix& p ) 
         { val &= p. val; return *this; }

      prefix operator ~ ( ) const
         { return prefix( 7 ^ val ); }
        
#endif 

#if 0
   inline prefix operator & ( prefix p1, prefix p2 ) 
      { return p1 &= p2; }

   inline prefix operator | ( prefix p1, prefix p2 ) 
      { return p1 |= p2; }
#endif

   inline std::ostream& operator << ( std::ostream& out, truthset s )
      { out << getcstring(s); return out; }

}

#endif

