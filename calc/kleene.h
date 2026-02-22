
#ifndef CALC_KLEENE_
#define CALC_KLEENE_

#include <iostream>

namespace calc
{
   enum kleene { kleene_and, kleene_or, kleene_forall, kleene_exists };

   const char* getcstring( kleene );

   inline std::ostream& operator << ( std::ostream& out, kleene kl )
      { out << getcstring( kl ); return out; }
}

#endif

