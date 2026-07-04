
#ifndef CALC_STRUCTURAL_
#define CALC_STRUCTURAL_

#include <optional>
#include "logic/beliefstate.h"
#include "errorstack.h"

namespace calc 
{

   bool
   applicable( const logic::belief& blf,
               const std::vector< logic::type > & tps );

   std::optional< logic::exact > 
   findformula( const logic::beliefstate& blfs, errorstack& err, 
                const identifier& ident,
                const std::vector< logic::type > & argtypes ); 
}

#endif

