
#ifndef CALC_STRUCTURAL_
#define CALC_STRUCTURAL_

#include <optional>
#include "logic/beliefstate.h"
#include "errorstack.h"
#include "proofterm.h"

namespace calc 
{

   bool
   applicable( const logic::belief& blf,
               const std::vector< logic::type > & tps );

   std::optional< logic::exact > 
   findformula( const logic::beliefstate& blfs, errorstack& err, 
                const identifier& ident,
                const std::vector< logic::type > & argtypes ); 

   void checkproof( const logic::beliefstate& blfs, errorstack& err,
                    logic::exact fname, proofterm prf );
      // We may spoil the proof term in the process.

   proofterm
   replace_debruijn( indexedstack< std::string, size_t > & db, proofterm prf );

   proofterm replace_debruijn( proofterm prf );
      // We always assume "goal"/0.
}

#endif

