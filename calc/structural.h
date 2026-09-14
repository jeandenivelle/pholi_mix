
#ifndef CALC_STRUCTURAL_
#define CALC_STRUCTURAL_

#include <optional>
#include "logic/beliefstate.h"
#include "errortree.h"

namespace calc 
{

   bool 
   fits( const logic::belief& bl, const logic::typesequence& univtypes );
      // True if bl fits to univtypes

   bool
   fitsbetter( const logic::belief& bl1, const logic::belief& bl2, 
               const logic::typesequence& univtypes );

   std::optional< logic::exact > 
   findformula( const logic::beliefstate& blfs, errorvector& errs, 
                const identifier& ident,
                const logic::typesequence& univtypes ); 
      // Types in univtypes must be resolved.

   logic::term getgoal( const logic::belief& blf ); 
      // get the goal belonging to blf. 
}

#endif

