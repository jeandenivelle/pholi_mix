
#ifndef CALC_NAMEDPROOFCHECKER_
#define CALC_NAMEDPROOFCHECKER_

#include <optional>
#include <vector>

#include "identifier.h"
#include "proofchecker.h"

namespace calc
{
   // One can use this class if one knows the 
   // name of the formula being proven, and its universal types.  
   // We assume that the universal types have been checked and resolved.

   struct namedproofchecker : public proofchecker
   {
      std::optional< logic::exact > name; 
         // We cannot put an exact name, because the parser may not find
         // the name, but we have to continue.

      std::vector< logic::type > types; 

      namedproofchecker( const logic::beliefstate* blfs,
                         std::vector< logic::type > types )
         : proofchecker( blfs, logic::term( logic::op_true ))
      { }

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
 
