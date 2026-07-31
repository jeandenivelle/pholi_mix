
#ifndef CALC_STRUCTURAL_
#define CALC_STRUCTURAL_

#include <optional>
#include "logic/beliefstate.h"
#include "errortree.h"

namespace calc 
{

   bool
   applicable( const logic::belief& blf,
               const std::vector< logic::type > & types );

   std::optional< logic::exact > 
   findformula( const logic::beliefstate& blfs, errorvector& errs, 
                const identifier& ident,
                const std::vector< logic::type > & argtypes ); 

   logic::term proofobligation( const logic::belief& blf );    
}

#endif

