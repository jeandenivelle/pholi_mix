
#include "truthset.h"

const char* calc::getcstring( truthset set )
{

   switch( set )
   {
   case empty: return "{}";
   case ffff: return "{F}";
   case eeee: return "{E}";
   case tttt: return "{T}";
   case ffee: return "{F,E}";
   case fftt: return "{F,T}";
   case all:  return "{F,E,T}";
   }

   return "???"; 
}


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


