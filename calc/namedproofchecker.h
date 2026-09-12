
// Written by Hans de Nivelle, August 2026.

#ifndef CALC_NAMEDPROOFCHECKER_
#define CALC_NAMEDPROOFCHECKER_

#include "identifier.h"
#include "proofchecker.h"

namespace calc
{
   // One can use this class if one knows the exact name of
   // the formula being proven.

   struct namedproofchecker : public proofchecker
   {
      logic::exact name; 

      namedproofchecker( const logic::beliefstate* blfs, 
                         logic::exact name, const logic::term& goal )
         : proofchecker( blfs, goal ),
           name( name ) 
      { }
   };

}

#endif
 
