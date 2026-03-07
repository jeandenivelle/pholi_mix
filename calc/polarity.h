
#ifndef CALC_POLARITY_
#define CALC_POLARITY_

#include <iostream>
#include "logic/selector.h"

namespace calc
{
   enum polarity { pol_pos, pol_neg };

   const char* getcstring( polarity pol );

   inline std::ostream& operator << ( std::ostream& out, polarity pol )
      { out << getcstring( pol ); return out; }

   polarity operator - ( polarity );  

}

#endif

