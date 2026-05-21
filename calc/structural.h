
#ifndef CALC_STRUCTURAL_
#define CALC_STRUCTURAL_

#include <optional>
#include "errorstack.h"
#include "logic/beliefstate.h"

namespace calc 
{

   bool
   applicable( const logic::belief& blf,
               const std::vector< logic::type > & tps );

   std::optional< logic::exact > 
   checkandresolve( const logic::beliefstate& blfs, errorstack& errors, 
                    const identifier& ident,
                    std::vector< logic::type > & argtypes ); 
}

#endif

