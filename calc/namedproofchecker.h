
// Written by Hans de Nivelle, August 2026.

#ifndef CALC_NAMEDPROOFCHECKER_
#define CALC_NAMEDPROOFCHECKER_

#include <optional>
#include <vector>

#include "identifier.h"
#include "proofchecker.h"

namespace calc
{
   // One can use this class if there is a change that one knows 
   // name of the formula being proven, and its universal types.  
   // We assume that the universal types have been checked and resolved.

   struct namedproofchecker : public proofchecker
   {
      logic::exact name; 

      std::vector< logic::type > types; 
         // In principle resolved.

      namedproofchecker( const logic::beliefstate* blfs, 
                         logic::exact name, const logic::term& goal,
                         std::vector< logic::type > types )
         : proofchecker( blfs, goal ),
           name( name ),
           types( std::move( types ))
      { }

   };

}

#endif
 
