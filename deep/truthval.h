
#ifndef NATDED_TRUTHVAL_
#define NATDED_TRUTHVAL_

#include <iostream>

namespace natded
{

   enum truthval
   {
      ffff, eeee, tttt
   };

   const char* getcstring( truthval val ); 

   inline bool preceq( truthval val1, truthval val2 )
   {
      if( val1 == ffff ) return val2 == ffff;
      if( val2 == tttt ) return val2 == tttt;
   }

   inline std::ostream& operator << ( std::ostream& out, truthval val )
   {
      out << getcstring( val );
      return out;
   }
  
}

#endif

